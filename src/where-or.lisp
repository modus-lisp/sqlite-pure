;;;; where-or.lisp — the OR optimizations of SQLite's where.c.
;;;;
;;;; An OR term of the WHERE clause is analyzed into its disjuncts
;;;; (exprAnalyzeOrTerm): when every disjunct is x = <value> on one column
;;;; it gains a virtual x IN (...) term, a two-way x = A OR x > A gains a
;;;; virtual x >= A, and when every disjunct can use an index on a table
;;;; the planner may read that table as a "MULTI-INDEX OR" loop
;;;; (whereLoopAddOr): one index lookup per disjunct, each planned as its
;;;; own single-table sub-WHERE, with rows already delivered by an earlier
;;;; disjunct skipped.

(in-package #:sqlite-pure)

(defun root-wc (wc)
  (loop while (wc-outer wc) do (setf wc (wc-outer wc)))
  wc)

(defun split-disjuncts (e)
  (let ((x (skip-collate e)))
    (if (and (consp x) (eq (car x) :binary) (eq (second x) :or))
        (append (split-disjuncts (third x)) (split-disjuncts (fourth x)))
        (list e))))

(defun term-lhs (term)
  "The column side of TERM's comparison (pExpr->pLeft once commuted)."
  (let ((e (wt-expr term)))
    (case (car e)
      (:binary (if (eq (wt-rhs term) (third e)) (fourth e) (third e)))
      ((:in :isnull :between) (second e))
      (t nil))))

(defun allowed-op-p (e)
  "allowedOp: the operators an index can use."
  (case (car e)
    (:binary (member (second e) '(:eq :lt :le :gt :ge :is)))
    (:in (not (fourth e)))
    (:isnull (not (third e)))
    (t nil)))

(defun analyze-clause (conjuncts scope nsrc &optional outer (op :and))
  "A sub-WHERE clause (sqlite3WhereSplit + sqlite3WhereExprAnalyze) of
CONJUNCTS, each (ast outer-on inner-on); OP :OR for disjuncts."
  (let ((wc (make-wclause :scope scope :nsrc nsrc :outer outer :op op)))
    (dolist (c conjuncts)
      (destructuring-bind (e outer-on inner-on) c
        (add-wterm wc (make-wterm :expr e :origin e :outer-on outer-on :inner-on inner-on :base t))))
    (loop for i from (1- (length conjuncts)) downto 0
          do (analyze-term wc (aref (wc-terms wc) i)))
    wc))

(defun analyze-or-term (wc term)
  "exprAnalyzeOrTerm."
  (let* ((scope (wc-scope wc)) (n (wc-nsrc wc))
         (outer-on (wt-outer-on term)) (inner-on (wt-inner-on term))
         (or-wc (analyze-clause (mapcar (lambda (d) (list d outer-on inner-on))
                                        (split-disjuncts (wt-expr term)))
                                scope n nil :or))
         (indexable -1) (chng -1))
    ;; which tables every disjunct can index; could it be x IN (...)?
    (loop for ot across (wc-terms or-wc)
          while (/= indexable 0)
          do (cond ((null (wt-op ot))
                    ;; several ANDed terms (or one no index can use)
                    (setf chng 0)
                    (let ((awc (analyze-clause (mapcar (lambda (c) (list c outer-on inner-on))
                                                       (split-conjuncts (wt-expr ot)))
                                               scope n))
                          (b 0))
                      (setf (wc-outer awc) wc
                            (wt-and-wc ot) awc)
                      (loop for at across (wc-terms awc)
                            do (when (and (allowed-op-p (wt-expr at)) (wt-src at))
                                 (setf b (logior b (ash 1 (wt-src at))))))
                      (setf indexable (logand indexable b))))
                   ((wt-copied ot))       ; its virtual copy stands for it
                   (t
                    (let ((b (ash 1 (wt-src ot))))
                      (when (and (wt-virtual ot) (wt-parent ot) (wt-src (wt-parent ot)))
                        (setf b (logior b (ash 1 (wt-src (wt-parent ot))))))
                      (setf indexable (logand indexable b))
                      (if (eq (wt-op ot) :eq)
                          (setf chng (logand chng b))
                          (setf chng 0))))))
    (setf (wt-or-wc term) or-wc
          (wt-indexable term) indexable)
    ;; a two-way OR: x = A OR x > A is x >= A
    (when (and (/= indexable 0) (= (length (wc-terms or-wc)) 2))
      (dolist (one (disjunct-subterms (aref (wc-terms or-wc) 0)))
        (dolist (two (disjunct-subterms (aref (wc-terms or-wc) 1)))
          (combine-disjuncts wc term one two))))
    ;; every disjunct x = <value> on one column: x IN (...)
    (when (/= chng 0)
      (or-to-in wc term or-wc chng))))

(defun disjunct-subterms (ot)
  "whereNthSubterm: the terms of an ANDed disjunct, or the disjunct."
  (if (wt-and-wc ot) (coerce (wc-terms (wt-and-wc ot)) 'list) (list ot)))

(defun combine-disjuncts (wc term one two)
  "whereCombineDisjuncts."
  (let ((ops (list (wt-op one) (wt-op two))))
    (when (or (wt-vnull one) (wt-vnull two)) (return-from combine-disjuncts))
    (unless (every (lambda (o) (member o '(:eq :lt :le :gt :ge))) ops) (return-from combine-disjuncts))
    (unless (or (subsetp ops '(:eq :lt :le)) (subsetp ops '(:eq :gt :ge))) (return-from combine-disjuncts))
    (unless (and (equal (term-lhs one) (term-lhs two)) (equal (wt-rhs one) (wt-rhs two)))
      (return-from combine-disjuncts))
    (let* ((op (cond ((eq (first ops) (second ops)) (first ops))
                     ((intersection ops '(:lt :le)) :le)
                     (t :ge)))
           (new (make-wterm :expr (list :binary op (copy-tree (term-lhs one)) (copy-tree (wt-rhs one)))
                            :virtual t :outer-on (wt-outer-on term) :inner-on (wt-inner-on term))))
      (add-wterm wc new)
      (analyze-term wc new))))

(defun or-to-in (wc term or-wc chng)
  "exprAnalyzeOrTerm, case 1: the disjuncts all x = <value> on one column
of one table become a virtual x IN (...) child of the OR term."
  (let* ((scope (wc-scope wc))
         (terms (coerce (wc-terms or-wc) 'list))
         (ok nil) (oks '()) (i-cursor -1) (i-col nil))
    (loop for j below 2
          until ok
          do (setf oks '())
             (let ((start (position-if (lambda (ot) (and (not (eql (wt-src ot) i-cursor))
                                                        (wt-src ot)
                                                        (logtest chng (ash 1 (wt-src ot)))))
                                       terms)))
               (unless start (return))
               (setf i-col (wt-col (nth start terms)) i-cursor (wt-src (nth start terms)) ok t)
               (loop for ot in (nthcdr start terms)
                     while ok
                     do (cond ((not (eql (wt-src ot) i-cursor)))
                              ((not (equal (wt-col ot) i-col)) (setf ok nil))
                              (t (let ((aff-r (expr-affinity (wt-rhs ot) scope))
                                       (aff-l (expr-affinity (term-lhs ot) scope)))
                                   (if (and aff-r (not (eq aff-r aff-l)))
                                       (setf ok nil)
                                       (push ot oks))))))))
    (when ok
      (let* ((oks (reverse oks))
             (new (make-wterm :expr (list :in (copy-tree (term-lhs (car (last oks))))
                                          (list :list (mapcar (lambda (ot) (copy-tree (wt-rhs ot))) oks))
                                          nil)
                              :virtual t :parent term
                              :outer-on (wt-outer-on term) :inner-on (wt-inner-on term))))
        (add-wterm wc new)
        (analyze-term wc new)))))

;;; ------------------------------------------------------------------
;;; The multi-index OR loop (whereLoopAddOr)

(defconstant +n-or-cost+ 3)

(defun or-set-insert (b prereq r-run n-out)
  "whereOrInsert into B's cost set."
  (let ((set (wb-or-set b)))
    (block ins
      (let ((p nil))
        (loop for e across set
              do (when (and (<= r-run (second e)) (= (logand prereq (first e)) prereq))
                   (setf p e) (return))
                 (when (and (<= (second e) r-run) (= (logand (first e) prereq) (first e)))
                   (return-from ins nil)))
        (unless p
          (if (< (length set) +n-or-cost+)
              (progn (setf p (list prereq r-run n-out)) (vector-push-extend p set))
              (progn
                (setf p (reduce (lambda (a c) (if (> (second a) (second c)) c a)) set))
                (when (<= (second p) r-run) (return-from ins nil)))))
        (setf (first p) prereq (second p) r-run)
        (when (> (third p) n-out) (setf (third p) n-out))
        t))))

(defun add-or-loops (b ws m-prereq)
  "whereLoopAddOr: for each OR term every disjunct of which can use an
index on WS, a MULTI-INDEX OR loop costed as the sum of the disjuncts'
best index lookups."
  (when (member (ws-join ws) '(:right :full)) (return-from add-or-loops))
  (loop for term across (wc-terms *wc*)
        do (when (and (wt-or-wc term) (logtest (wt-indexable term) (ws-mask ws)))
             (let ((sum nil) (once t))
               (block disjuncts
                 (loop for ot across (wc-terms (wt-or-wc term))
                       do (let ((sub (cond ((wt-and-wc ot))
                                           ((eql (wt-src ot) (ws-i ws))
                                            (let ((w (make-wclause :scope (wc-scope *wc*) :nsrc (wc-nsrc *wc*)
                                                                   :outer *wc*)))
                                              (add-wterm w ot)
                                              w))
                                           (t nil))))
                            (when sub
                              (let* ((cur (make-array 0 :adjustable t :fill-pointer t))
                                     (sb (copy-wbuilder b)))
                                (setf (wb-or-set sb) cur (wb-main sb) (or (wb-main b) b))
                                (let ((*wc* sub))
                                  (add-btree-loops sb ws m-prereq)
                                  (add-or-loops sb ws m-prereq))
                                ;; the sub-build shares SQLite's one template loop
                                (setf (wb-sort-idx b) (wb-sort-idx sb))
                                (when *where-trace*
                                  (format *error-output* "~&  -- disjunct of ~a: ~s~%" (ws-i ws)
                                          (coerce cur 'list)))
                                (cond ((zerop (length cur)) (setf sum nil) (return-from disjuncts))
                                      (once (setf sum cur once nil))
                                      (t (let ((prev sum)
                                               (acc (make-wbuilder :or-set (make-array 0 :adjustable t
                                                                                         :fill-pointer t))))
                                           (loop for p across prev
                                                 do (loop for c across cur
                                                          do (or-set-insert acc (logior (first p) (first c))
                                                                            (log-est-add (second p) (second c))
                                                                            (log-est-add (third p) (third c)))))
                                           (setf sum (wb-or-set acc))))))))))
               (when *where-trace*
                 (format *error-output* "~&  -- OR sum for ~a: ~s~%" (ws-i ws) (and sum (coerce sum 'list))))
               (setf (wb-sort-idx b) 0)          ; pNew->iSortIdx = 0
               (when sum
                 (loop for s across sum
                       do (loop-insert b (make-wloop :src (ws-i ws) :mask (ws-mask ws)
                                                     :prereq (first s) :flags +where-multi-or+
                                                     :lterms (list term)
                                                     :r-setup 0 :r-run (1+ (second s)) :n-out (third s)
                                                     :sort-idx 0))))))))

;;; ------------------------------------------------------------------
;;; Running it: each disjunct as its own single-table sub-WHERE

(defun or-branch-plans (lp ws bound)
  "For the MULTI-INDEX OR loop LP on WS (BOUND: the tables of the outer
loops): (index loop wc) per disjunct that reads WS, as the codegen plans
them -- the disjunct AND the WHERE clause's other usable terms, planned
for WS alone with the outer tables' values known."
  (let* ((term (first (wl-lterms lp)))
         (main (root-wc *wc*))
         (scope (wc-scope main)) (n (wc-nsrc main))
         (and-terms
           (loop for x across (wc-terms main)
                 when (and (not (eq x term)) (not (wt-virtual x))
                           (or (wt-op x) (wt-or-wc x))
                           (not (expr-has-subquery-p (wt-expr x)))
                           ;; coded by an outer loop already
                           (logtest (wt-prereq-all x) (ws-mask ws)))
                   collect (list (or (wt-origin x) (wt-expr x)) (wt-outer-on x) (wt-inner-on x)))))
    (loop for ot across (wc-terms (wt-or-wc term))
          for ii from 0
          when (or (wt-and-wc ot) (eql (wt-src ot) (ws-i ws)))
            collect (let* ((conjuncts (append (mapcar (lambda (c) (list c (wt-outer-on term) (wt-inner-on term)))
                                                      (split-conjuncts (or (wt-origin ot) (wt-expr ot))))
                                              and-terms))
                           (sub (analyze-clause conjuncts scope n))
                           (best (let ((*wc* sub) (*or-branch-plan* t))
                                   (plan-or-branch ws bound))))
                      (list (1+ ii) best sub (mapcar #'first conjuncts))))))

(defun plan-or-branch (ws bound)
  "The best loop for WS alone under *WC*, the outer tables BOUND."
  ;; (no whereShortCut: it declines WHERE_OR_SUBCLAUSE)
  (let ((b (make-wbuilder)))
    (add-btree-loops b ws 0)
    (add-or-loops b ws 0)
    (when *where-trace*
      (format *error-output* "~&  -- OR branch:~%")
      (trace-loops b))
    (let ((best nil) (best-cost nil))
      (dolist (lp (wb-loops b) best)
        (when (zerop (logandc2 (wl-prereq lp) bound))
          (let ((cost (log-est-add (wl-r-setup lp) (wl-r-run lp))))
            (when (or (null best) (< cost best-cost)
                      (and (= cost best-cost) (< (wl-n-out lp) (wl-n-out best))))
              (setf best lp best-cost cost))))))))

(defun multi-or-iterate (lp ws scope bound)
  "The rows of each disjunct's loop in turn, each row once."
  (let* ((branches (or-branch-plans lp ws bound))
         (table (ws-table ws))
         (si (ws-i ws))
         (iters (loop for (nil blp sub) in branches
                      collect (let ((*wc* sub))
                                (if (flag-p (wl-flags blp) +where-multi-or+)
                                    (multi-or-iterate blp ws scope bound)
                                    (loop-iterate blp ws scope nil)))))
         ;; each sub-WHERE's own terms, which its loop evaluates
         ;; (only terms on tables that are ready: the rest wait for a later loop)
         (ready (logior bound (ws-mask ws)))
         (filters (loop for br in branches
                        collect (loop for c in (fourth br)
                                      when (zerop (logandc2 (expr-usage c scope (wc-nsrc (root-wc *wc*)))
                                                            ready))
                                        collect (compile-expr (substitute-fixed c) scope)))))
    (flet ((key (row)
             (if (and table (table-without-rowid table))
                 (mapcar (lambda (p) (svref row p)) (table-pk table))
                 (svref row (1- (length row))))))
      (lambda (env fn)
        (let ((seen (make-hash-table :test #'equal)))
          (loop for it in iters
                for fs in filters
                do (funcall it env (lambda (row)
                                     (let ((saved (svref (env-rows env) si)))
                                       (setf (svref (env-rows env) si) row)
                                       (let ((pass (every (lambda (f) (eq (truth (funcall f env)) t)) fs)))
                                         (setf (svref (env-rows env) si) saved)
                                         (when pass
                                           (let ((k (key row)))
                                             (unless (gethash k seen)
                                               (setf (gethash k seen) t)
                                               (funcall fn row))))))))))))))

(defun explain-multi-or (lp ws name bound)
  "MULTI-INDEX OR, then INDEX n and its sub-plan's scan per disjunct."
  (with-eqp-node ("MULTI-INDEX OR")
    (dolist (br (or-branch-plans lp ws bound))
      (destructuring-bind (ii blp sub &rest conjuncts) br
        (declare (ignore conjuncts))
        (with-eqp-node ((format nil "INDEX ~d" ii))
          (let ((*wc* sub) (*eqp-left* nil))
            (if (flag-p (wl-flags blp) +where-multi-or+)
                (explain-multi-or blp ws name bound)
                (eqp-table-note (explain-loop blp ws name)))))))))
