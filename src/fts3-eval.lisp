;;;; fts3-eval.lisp — evaluating an FTS3/4 query (the evaluation half of
;;;; fts3.c): phrase doclists loaded whole or read incrementally, the
;;;; docid iteration over AND/OR/NOT/NEAR, NEAR trimming of position lists,
;;;; deferred tokens, and the per-phrase statistics and position lists the
;;;; auxiliary functions use.
;;;;
;;;; This follows SQLite's code closely, including its byte-level edits of
;;;; the doclists it holds: which phrase instances offsets(), snippet() and
;;;; matchinfo() see in a row depends on them.

(in-package #:sqlite-pure)

(defconstant +f3-poslist-end+ (1- (expt 2 63)))

(defstruct (f3cursor (:conc-name cs-))
  fts expr (langid 0)
  deferred                     ; list of deferred-token records
  (prev-id 0) desc eof
  (min-docid +fts3-smallest-int64+) (max-docid +fts3-largest-int64+)
  (ndoc 0) (nrowavg 0)
  row                          ; current row: (docid values langid), or NIL
  (nphrase 0)
  mi-format mi-global          ; cached matchinfo format and global values
  (id 0))

(defstruct (f3deferred (:conc-name df-)) token (col 0) list)

;;; ------------------------------------------------------------------
;;; Position lists (byte level)

(defun f3-read-next-pos (buf p pos)
  "fts3ReadNextPos: (values p pos); POS is position+2 form."
  (if (/= 0 (logand (aref buf p) #xfe))
      (multiple-value-bind (v o) (f3-get-varint32 buf p)
        (values o (- (+ pos v) 2)))
      (values p +f3-poslist-end+)))

(defun f3-get-delta-varint (buf p val)
  (multiple-value-bind (v o) (f3-get-varint buf p) (values o (+ val v))))

(defun f3-put-col-number (out col)
  (if (/= col 0)
      (let ((start (fill-pointer out)))
        (vector-push-extend 1 out)
        (f3-buf-varint out col)
        (- (fill-pointer out) start))
      0))

(defun f3-columnlist-copy (out buf p)
  "Copy the column list at P (not its terminator) to OUT; returns the
offset of the terminator."
  (let ((e (f3-columnlist-skip buf p)))
    (when out (f3-buf-append out buf p e))
    e))

(defun f3-poslist-copy (out buf p)
  (let ((e (f3-poslist-skip buf p)))
    (when out (f3-buf-append out buf p e))
    e))

(defun f3-poslist-merge (out b1 p1 b2 p2)
  "fts3PoslistMerge: the union of the position lists at P1 and P2 appended
to OUT (with its terminator).  Returns (values p1 p2) just past each."
  (loop while (or (/= 0 (aref b1 p1)) (/= 0 (aref b2 p2)))
        do (let ((c1 (cond ((= (aref b1 p1) 1)
                            (let ((c (f3-get-varint32 b1 (1+ p1))))
                              (when (zerop c) (corrupt "database disk image is malformed"))
                              c))
                           ((= (aref b1 p1) 0) #x7fffffff)
                           (t 0)))
                 (c2 (cond ((= (aref b2 p2) 1)
                            (let ((c (f3-get-varint32 b2 (1+ p2))))
                              (when (zerop c) (corrupt "database disk image is malformed"))
                              c))
                           ((= (aref b2 p2) 0) #x7fffffff)
                           (t 0))))
             (cond
               ((= c1 c2)
                (let* ((n (f3-put-col-number out c1)) (i1 0) (i2 0) (prev 0))
                  (incf p1 n) (incf p2 n)
                  (multiple-value-setq (p1 i1) (f3-get-delta-varint b1 p1 0))
                  (multiple-value-setq (p2 i2) (f3-get-delta-varint b2 p2 0))
                  (when (or (< i1 2) (< i2 2)) (return))
                  (loop
                    (let ((v (min i1 i2)))
                      (f3-buf-varint out (- v prev))
                      (setf prev (- v 2)))
                    (cond ((= i1 i2)
                           (multiple-value-setq (p1 i1) (f3-read-next-pos b1 p1 i1))
                           (multiple-value-setq (p2 i2) (f3-read-next-pos b2 p2 i2)))
                          ((< i1 i2) (multiple-value-setq (p1 i1) (f3-read-next-pos b1 p1 i1)))
                          (t (multiple-value-setq (p2 i2) (f3-read-next-pos b2 p2 i2))))
                    (when (and (= i1 +f3-poslist-end+) (= i2 +f3-poslist-end+)) (return)))))
               ((< c1 c2)
                (incf p1 (f3-put-col-number out c1))
                (setf p1 (f3-columnlist-copy out b1 p1)))
               (t
                (incf p2 (f3-put-col-number out c2))
                (setf p2 (f3-columnlist-copy out b2 p2))))))
  (vector-push-extend 0 out)
  (values (1+ p1) (1+ p2)))

(defun f3-poslist-phrase-merge (out ntoken save-left exact b1 p1 b2 p2)
  "fts3PoslistPhraseMerge: append to OUT the positions of list 2 (or of list
1, with SAVE-LEFT) that follow a position of list 1 by at most NTOKEN
(exactly NTOKEN, with EXACT).  Returns (values wrote-something p1 p2)."
  (let ((start (fill-pointer out)) (c1 0) (c2 0))
    (when (= (aref b1 p1) 1) (incf p1) (multiple-value-setq (c1 p1) (f3-get-varint32 b1 p1)))
    (when (= (aref b2 p2) 1) (incf p2) (multiple-value-setq (c2 p2) (f3-get-varint32 b2 p2)))
    (loop
      (cond
        ((= c1 c2)
         (let ((save (fill-pointer out)) (saved t) (prev 0) (pos1 0) (pos2 0))
           (when (/= c1 0)
             (vector-push-extend 1 out)
             (f3-buf-varint out c1))
           (multiple-value-setq (p1 pos1) (f3-get-delta-varint b1 p1 0)) (decf pos1 2)
           (multiple-value-setq (p2 pos2) (f3-get-delta-varint b2 p2 0)) (decf pos2 2)
           (when (or (< pos1 0) (< pos2 0))
             (return))
           (loop
             (when (or (= pos2 (+ pos1 ntoken))
                       (and (not exact) (> pos2 pos1) (<= pos2 (+ pos1 ntoken))))
               (let ((s (if save-left pos1 pos2)))
                 (f3-buf-varint out (- (+ s 2) prev))
                 (setf prev s)
                 (setf saved nil)))
             (if (or (and (not save-left) (<= pos2 (+ pos1 ntoken))) (<= pos2 pos1))
                 (progn (when (zerop (logand (aref b2 p2) #xfe)) (return))
                        (multiple-value-setq (p2 pos2) (f3-get-delta-varint b2 p2 pos2)) (decf pos2 2))
                 (progn (when (zerop (logand (aref b1 p1) #xfe)) (return))
                        (multiple-value-setq (p1 pos1) (f3-get-delta-varint b1 p1 pos1)) (decf pos1 2))))
           (when saved (setf (fill-pointer out) save))
           (setf p1 (f3-columnlist-skip b1 p1) p2 (f3-columnlist-skip b2 p2))
           (when (or (zerop (aref b1 p1)) (zerop (aref b2 p2))) (return))
           (incf p1) (multiple-value-setq (c1 p1) (f3-get-varint32 b1 p1))
           (incf p2) (multiple-value-setq (c2 p2) (f3-get-varint32 b2 p2))))
        ((< c1 c2)
         (setf p1 (f3-columnlist-skip b1 p1))
         (when (zerop (aref b1 p1)) (return))
         (incf p1) (multiple-value-setq (c1 p1) (f3-get-varint32 b1 p1)))
        (t
         (setf p2 (f3-columnlist-skip b2 p2))
         (when (zerop (aref b2 p2)) (return))
         (incf p2) (multiple-value-setq (c2 p2) (f3-get-varint32 b2 p2)))))
    (setf p2 (f3-poslist-skip b2 p2) p1 (f3-poslist-skip b1 p1))
    (if (= (fill-pointer out) start)
        (values nil p1 p2)
        (progn (vector-push-extend 0 out) (values t p1 p2)))))

(defun f3-poslist-near-merge (out nright nleft b1 p1 b2 p2)
  "fts3PoslistNearMerge: the positions of list 2 within NRIGHT after or
NLEFT before a position of list 1, appended to OUT.  Returns true if any."
  (let ((t1 (f3-buf 32)) (t2 (f3-buf 32)))
    (f3-poslist-phrase-merge t1 nright nil nil b1 p1 b2 p2)
    (f3-poslist-phrase-merge t2 nleft t nil b2 p2 b1 p1)
    (let ((a (plusp (fill-pointer t1))) (b (plusp (fill-pointer t2))))
      (cond ((and a b)
             (let ((x (f3-padded t1)) (y (f3-padded t2)))
               (f3-poslist-merge out x 0 y 0)))
            (a (f3-buf-append out t1))
            (b (f3-buf-append out t2)))
      (or a b))))

;;; Doclists

(defun f3-get-delta-varint3 (buf p end desc val)
  "fts3GetDeltaVarint3: (values p-or-NIL val)."
  (if (>= p end)
      (values nil val)
      (multiple-value-bind (u o) (f3-get-varint-u buf p)
        (values o (f3-signed (ldb (byte 64 0) (if desc (- val u) (+ val u))))))))

(defun f3-put-delta-varint3 (out desc prev firstp val)
  "fts3PutDeltaVarint3: returns the new prev."
  (f3-buf-varint out (if (or (not desc) (not firstp)) (- val prev) (- prev val)))
  val)

(defun f3-docid-cmp (desc a b)
  (let ((c (cond ((> a b) 1) ((= a b) 0) (t -1)))) (if desc (- c) c)))

(defun f3-doclist-or-merge (desc a1 n1 a2 n2)
  "fts3DoclistOrMerge: a padded octet vector and its size."
  (let ((out (f3-buf (+ n1 n2 16))) (i1 0) (i2 0) (prev 0) (firstp nil)
        (p1 0) (p2 0))
    (multiple-value-setq (p1 i1) (f3-get-delta-varint3 a1 0 n1 nil 0))
    (multiple-value-setq (p2 i2) (f3-get-delta-varint3 a2 0 n2 nil 0))
    (loop while (or p1 p2)
          do (let ((diff (f3-docid-cmp desc i1 i2)))
               (cond ((and p1 p2 (= diff 0))
                      (setf prev (f3-put-delta-varint3 out desc prev firstp i1) firstp t)
                      (multiple-value-setq (p1 p2) (f3-poslist-merge out a1 p1 a2 p2))
                      (multiple-value-setq (p1 i1) (f3-get-delta-varint3 a1 p1 n1 desc i1))
                      (multiple-value-setq (p2 i2) (f3-get-delta-varint3 a2 p2 n2 desc i2)))
                     ((or (null p2) (and p1 (< diff 0)))
                      (setf prev (f3-put-delta-varint3 out desc prev firstp i1) firstp t)
                      (setf p1 (f3-poslist-copy out a1 p1))
                      (multiple-value-setq (p1 i1) (f3-get-delta-varint3 a1 p1 n1 desc i1)))
                     (t
                      (setf prev (f3-put-delta-varint3 out desc prev firstp i2) firstp t)
                      (setf p2 (f3-poslist-copy out a2 p2))
                      (multiple-value-setq (p2 i2) (f3-get-delta-varint3 a2 p2 n2 desc i2))))))
    (values (f3-padded out) (fill-pointer out))))

(defun f3-doclist-phrase-merge (desc ndist left nleft right nright)
  "fts3DoclistPhraseMerge: (values doclist size)."
  (let ((out (f3-buf (+ nright 16))) (i1 0) (i2 0) (prev 0) (firstp nil) (p1 0) (p2 0))
    (multiple-value-setq (p1 i1) (f3-get-delta-varint3 left 0 nleft nil 0))
    (multiple-value-setq (p2 i2) (f3-get-delta-varint3 right 0 nright nil 0))
    (loop while (and p1 p2)
          do (let ((diff (f3-docid-cmp desc i1 i2)))
               (cond ((= diff 0)
                      (let ((save (fill-pointer out)) (psave prev) (fsave firstp))
                        (setf prev (f3-put-delta-varint3 out desc prev firstp i1) firstp t)
                        (multiple-value-bind (wrote np1 np2) (f3-poslist-phrase-merge out ndist nil t left p1 right p2)
                          (setf p1 np1 p2 np2)
                          (unless wrote (setf (fill-pointer out) save prev psave firstp fsave))))
                      (multiple-value-setq (p1 i1) (f3-get-delta-varint3 left p1 nleft desc i1))
                      (multiple-value-setq (p2 i2) (f3-get-delta-varint3 right p2 nright desc i2)))
                     ((< diff 0)
                      (setf p1 (f3-poslist-skip left p1))
                      (multiple-value-setq (p1 i1) (f3-get-delta-varint3 left p1 nleft desc i1)))
                     (t
                      (setf p2 (f3-poslist-skip right p2))
                      (multiple-value-setq (p2 i2) (f3-get-delta-varint3 right p2 nright desc i2))))))
    (values (f3-padded out) (fill-pointer out))))

(defun f3-doclist-count-docids (buf n)
  (let ((p 0) (count 0))
    (when buf
      (loop while (< p n)
            do (incf count)
               (loop while (logtest (aref buf p) #x80) do (incf p))
               (incf p)
               (setf p (f3-poslist-skip buf p))))
    count))

(defun f3-doclist-next (desc buf n iter docid)
  "sqlite3Fts3DoclistNext: (values iter docid eof)."
  (if (null iter)
      (multiple-value-bind (d o) (f3-get-varint buf 0) (values o d nil))
      (let ((p (f3-poslist-skip buf iter)))
        (loop while (and (< p n) (zerop (aref buf p))) do (incf p))
        (if (>= p n)
            (values p docid t)
            (multiple-value-bind (v o) (f3-get-varint buf p)
              (values o (f3-signed (ldb (byte 64 0) (+ docid (* (if desc -1 1) v)))) nil))))))

;;; ------------------------------------------------------------------
;;; Term doclists

(defun f3-term-seg-reader-cursor (cs term prefix-p)
  "fts3TermSegReaderCursor."
  (let* ((f (cs-fts cs)) (found nil) (m nil) (n (length term)))
    (when prefix-p
      (loop for i from 1 below (f3-nindex f)
            do (when (= (aref (f3-prefixes f) i) n)
                 (setf found t
                       m (f3-seg-reader-cursor f (cs-langid cs) i :all term nil nil))
                 (setf (msr-lookup m) t)
                 (return)))
      (unless found
        (loop for i from 1 below (f3-nindex f)
              do (when (= (aref (f3-prefixes f) i) (1+ n))
                   (setf found t
                         m (f3-seg-reader-cursor f (cs-langid cs) i :all term t nil))
                   (f3-seg-reader-cursor f (cs-langid cs) 0 :all term nil nil m)
                   (return)))))
    (unless found
      (setf m (f3-seg-reader-cursor f (cs-langid cs) 0 :all term prefix-p nil))
      (setf (msr-lookup m) (not prefix-p)))
    m))

(defun f3-term-select (cs tok col)
  "fts3TermSelect: the token's doclist (all matching terms OR-ed), as
(values buffer size); frees the token's reader."
  (let* ((f (cs-fts cs)) (m (tk-segcsr tok))
         (flags (logior +f3f-ignore-empty+ +f3f-require-pos+
                        (if (tk-prefix-p tok) +f3f-prefix+ 0)
                        (if (tk-first-p tok) +f3f-first+ 0)
                        (if (< col (f3-ncol f)) +f3f-column-filter+ 0)))
         (acc nil) (nacc 0))
    (f3-msr-start-filter f m flags (tk-term tok) col)
    (loop while (f3-msr-step f m)
          do (let ((d (f3-msr-doclist m)) (n (msr-ndoclist m)))
               (if acc
                   (multiple-value-setq (acc nacc) (f3-doclist-or-merge (f3-desc-p f) d n acc nacc))
                   (setf acc d nacc n))))
    (setf (tk-segcsr tok) nil)
    (values acc nacc)))

;;; ------------------------------------------------------------------
;;; Phrases

(defun f3-phrase-merge-token (f ph itoken list nlist)
  "fts3EvalPhraseMergeToken."
  (cond ((null list) (setf (ph-all ph) nil (ph-nall ph) 0))
        ((< (ph-doclist-token ph) 0) (setf (ph-all ph) list (ph-nall ph) nlist))
        ((null (ph-all ph)) nil)
        (t (multiple-value-bind (left nleft right nright diff)
               (if (< (ph-doclist-token ph) itoken)
                   (values (ph-all ph) (ph-nall ph) list nlist (- itoken (ph-doclist-token ph)))
                   (values list nlist (ph-all ph) (ph-nall ph) (- (ph-doclist-token ph) itoken)))
             (multiple-value-bind (d n) (f3-doclist-phrase-merge (f3-desc-p f) diff left nleft right nright)
               (setf (ph-all ph) d (ph-nall ph) n)))))
  (when (> itoken (ph-doclist-token ph)) (setf (ph-doclist-token ph) itoken)))

(defun f3-phrase-load (cs ph)
  (loop for tok across (ph-tokens ph)
        for i from 0
        do (when (tk-segcsr tok)
             (multiple-value-bind (list n) (f3-term-select cs tok (ph-column ph))
               (f3-phrase-merge-token (cs-fts cs) ph i list n)))))

(defun f3-invalidate-poslist (ph)
  (setf (ph-list-buf ph) nil (ph-list-off ph) 0 (ph-nlist ph) 0 (ph-free-list ph) nil))

(defun f3-phrase-start (cs opt-ok ph)
  "fts3EvalPhraseStart."
  (let* ((f (cs-fts cs))
         (ntok (length (ph-tokens ph)))
         (incr-ok (and opt-ok (eq (and (cs-desc cs) t) (and (f3-desc-p f) t)) (<= 1 ntok 4)))
         (have-incr nil))
    (loop for tok across (ph-tokens ph)
          while incr-ok
          do (when (or (tk-first-p tok) (and (tk-segcsr tok) (not (msr-lookup (tk-segcsr tok)))))
               (setf incr-ok nil))
             (when (tk-segcsr tok) (setf have-incr t)))
    (if (and incr-ok have-incr)
        (let ((col (if (>= (ph-column ph) (f3-ncol f)) -1 (ph-column ph))))
          (loop for tok across (ph-tokens ph)
                do (when (tk-segcsr tok)
                     (f3-msr-incr-start f (tk-segcsr tok) col (tk-term tok))))
          (setf (ph-incr ph) t))
        (progn (f3-phrase-load cs ph)
               (setf (ph-incr ph) nil)))))

(defun f3-dl-phrase-next (f ph)
  "fts3EvalDlPhraseNext: returns EOF."
  (let* ((all (ph-all ph))
         (iter (or (ph-next-docid ph) (and all 0))))
    (if (or (null iter) (null all) (>= iter (ph-nall ph)))
        t
        (multiple-value-bind (delta o) (f3-get-varint all iter)
          (setf (ph-docid ph)
                (f3-signed (ldb (byte 64 0) (if (or (not (f3-desc-p f)) (null (ph-next-docid ph)))
                                                (+ (ph-docid ph) delta)
                                                (- (ph-docid ph) delta)))))
          (let ((e (f3-poslist-skip all o)))
            (setf (ph-list-buf ph) all (ph-list-off ph) o (ph-nlist ph) (- e o))
            (loop while (and (< e (ph-nall ph)) (zerop (aref all e))) do (incf e))
            (setf (ph-next-docid ph) e)
            nil)))))

(defstruct (f3tdl) ignore (docid 0) buf (off 0) (n 0))

(defun f3-incr-token-next (f ph itoken a)
  "incrPhraseTokenNext: returns EOF."
  (if (= (ph-doclist-token ph) itoken)
      (let ((eof (f3-dl-phrase-next f ph)))
        (setf (f3tdl-buf a) (ph-list-buf ph) (f3tdl-off a) (ph-list-off ph)
              (f3tdl-n a) (ph-nlist ph) (f3tdl-docid a) (ph-docid ph))
        eof)
      (let ((tok (aref (ph-tokens ph) itoken)))
        (if (tk-segcsr tok)
            (multiple-value-bind (docid buf off n) (f3-msr-incr-next f (tk-segcsr tok))
              (if docid
                  (progn (setf (f3tdl-docid a) docid (f3tdl-buf a) buf (f3tdl-off a) off (f3tdl-n a) n) nil)
                  (progn (setf (f3tdl-buf a) nil) t)))
            (progn (setf (f3tdl-ignore a) t) nil)))))

(defun f3-incr-phrase-next (cs ph)
  "fts3EvalIncrPhraseNext: returns EOF."
  (let* ((f (cs-fts cs)) (ntok (length (ph-tokens ph))) (eof nil))
    (if (= ntok 1)
        (multiple-value-bind (docid buf off n) (f3-msr-incr-next f (tk-segcsr (aref (ph-tokens ph) 0)))
          (if docid
              (setf (ph-docid ph) docid (ph-list-buf ph) buf (ph-list-off ph) off (ph-nlist ph) n)
              (setf (ph-list-buf ph) nil eof t)))
        (let ((desc (cs-desc cs))
              (a (coerce (loop repeat ntok collect (make-f3tdl)) 'vector)))
          (loop until eof
                do (let ((max-set nil) (imax 0))
                     (loop for i below ntok
                           until eof
                           do (setf eof (f3-incr-token-next f ph i (aref a i)))
                              (when (and (not (f3tdl-ignore (aref a i)))
                                         (or (not max-set) (< (f3-docid-cmp desc imax (f3tdl-docid (aref a i))) 0)))
                                (setf imax (f3tdl-docid (aref a i)) max-set t)))
                     (let ((i 0))
                       (loop while (< i ntok)
                             do (loop while (and (not eof) (not (f3tdl-ignore (aref a i)))
                                                 (< (f3-docid-cmp desc (f3tdl-docid (aref a i)) imax) 0))
                                      do (setf eof (f3-incr-token-next f ph i (aref a i)))
                                         (when (> (f3-docid-cmp desc (f3tdl-docid (aref a i)) imax) 0)
                                           (setf imax (f3tdl-docid (aref a i)) i 0)))
                                (incf i)))
                     (unless eof
                       (let* ((last (aref a (1- ntok)))
                              (doc (f3-padded (f3tdl-buf last) (f3tdl-off last) (+ (f3tdl-off last) (f3tdl-n last) 1)))
                              (nlist 0) (i 0))
                         (loop while (< i (1- ntok))
                               do (let ((ai (aref a i)))
                                    (unless (f3tdl-ignore ai)
                                      (let ((out (f3-buf 32)))
                                        (multiple-value-bind (res) (f3-poslist-phrase-merge out (- ntok 1 i) nil t
                                                                                            (f3tdl-buf ai) (f3tdl-off ai) doc 0)
                                          (unless res (return))
                                          (replace doc out)
                                          (setf nlist (fill-pointer out))))))
                                  (incf i))
                         (when (= i (1- ntok))
                           (setf (ph-docid ph) imax (ph-list-buf ph) doc (ph-list-off ph) 0
                                 (ph-nlist ph) nlist (ph-free-list ph) t)
                           (return))))))))
    eof))

(defun f3-phrase-next (cs ph)
  "fts3EvalPhraseNext: returns EOF."
  (let ((f (cs-fts cs)))
    (cond ((ph-incr ph) (f3-incr-phrase-next cs ph))
          ((and (not (eq (and (cs-desc cs) t) (and (f3-desc-p f) t))) (plusp (ph-nall ph)))
           (multiple-value-bind (iter docid nlist eof)
               (f3-doclist-prev (f3-desc-p f) (ph-all ph) 0 (ph-nall ph) (ph-next-docid ph) (ph-docid ph))
             (setf (ph-next-docid ph) iter (ph-docid ph) docid)
             (unless eof (setf (ph-nlist ph) nlist))
             (setf (ph-list-buf ph) (ph-all ph) (ph-list-off ph) iter)
             eof))
          (t (f3-dl-phrase-next f ph)))))

;;; ------------------------------------------------------------------
;;; Deferred tokens

(defun f3-defer-token (cs tok col)
  (let ((d (make-f3deferred :token tok :col col)))
    (push d (cs-deferred cs))
    (setf (tk-deferred tok) d)))

(defun f3-cache-deferred-doclists (cs)
  "sqlite3Fts3CacheDeferredDoclists: tokenize the current row for the
deferred tokens."
  (let* ((f (cs-fts cs)) (row (cs-row cs)) (docid (first row)))
    (loop for v in (second row)
          for i from 0
          for notidx in (f3-notindexed f)
          do (unless notidx
               (let ((bytes (fts3-text-bytes v)))
                 (when bytes
                   (loop for (term nil nil pos) across (fts3-tokenize (f3-tokenizer f) bytes)
                         do (dolist (d (cs-deferred cs))
                              (let ((tok (df-token d)))
                                (when (and (or (>= (df-col d) (f3-ncol f)) (= (df-col d) i))
                                           (or (not (tk-first-p tok)) (= pos 0))
                                           (let ((n (length (tk-term tok))))
                                             (and (or (= n (length term)) (and (tk-prefix-p tok) (< n (length term))))
                                                  (string= (tk-term tok) term :end2 n))))
                                  (setf (df-list d) (f3-pending-list-append (df-list d) docid i pos))))))))))
    (dolist (d (cs-deferred cs))
      (when (df-list d) (f3-buf-varint (pl-data (df-list d)) 0)))))

(defun f3-free-deferred-doclists (cs)
  (dolist (d (cs-deferred cs)) (setf (df-list d) nil)))

(defun f3-deferred-token-list (d)
  "(values buffer size) of the position list after the docid, or NIL."
  (let ((pl (df-list d)))
    (when pl
      (let* ((data (pl-data pl))
             (skip (nth-value 1 (f3-get-varint (f3-padded data) 0))))
        (values (f3-padded data skip (fill-pointer data)) (- (fill-pointer data) skip))))))

(defun f3-deferred-phrase (cs ph)
  "fts3EvalDeferredPhrase."
  (let ((aposlist nil) (nposlist 0) (iprev -1))
    (loop for tok across (ph-tokens ph)
          for itoken from 0
          do (let ((d (tk-deferred tok)))
               (when d
                 (multiple-value-bind (list nlist) (f3-deferred-token-list d)
                   (cond ((null list)
                          (setf (ph-list-buf ph) nil (ph-nlist ph) 0 (ph-free-list ph) nil)
                          (return-from f3-deferred-phrase nil))
                         ((null aposlist) (setf aposlist list nposlist nlist))
                         (t (let ((out (f3-buf 32)))
                              (f3-poslist-phrase-merge out (- itoken iprev) nil t aposlist 0 list 0)
                              (setf nposlist (fill-pointer out))
                              (when (zerop nposlist)
                                (setf (ph-list-buf ph) nil (ph-nlist ph) 0 (ph-free-list ph) nil)
                                (return-from f3-deferred-phrase nil))
                              (setf aposlist (f3-padded out)))))
                   (setf iprev itoken)))))
    (when (>= iprev 0)
      (let ((max-undeferred (ph-doclist-token ph)))
        (if (< max-undeferred 0)
            (setf (ph-list-buf ph) aposlist (ph-list-off ph) 0 (ph-nlist ph) nposlist
                  (ph-docid ph) (cs-prev-id cs) (ph-free-list ph) t)
            (let ((out (f3-buf 32)) b1 o1 b2 o2 dist)
              (if (> max-undeferred iprev)
                  (setf b1 aposlist o1 0 b2 (ph-list-buf ph) o2 (ph-list-off ph) dist (- max-undeferred iprev))
                  (setf b1 (ph-list-buf ph) o1 (ph-list-off ph) b2 aposlist o2 0 dist (- iprev max-undeferred)))
              (if (and b1 b2 (f3-poslist-phrase-merge out dist nil t b1 o1 b2 o2))
                  (setf (ph-list-buf ph) (f3-padded out) (ph-list-off ph) 0
                        (ph-nlist ph) (fill-pointer out) (ph-free-list ph) t)
                  (setf (ph-list-buf ph) nil (ph-nlist ph) 0))))))))

;;; ------------------------------------------------------------------
;;; Starting a query

(defun f3-leaf-overflow-pages (cs m)
  "sqlite3Fts3MsrOvfl."
  (let* ((f (cs-fts cs)) (pgsz (f3-pgsz f)) (n 0))
    (loop for r across (msr-segments m)
          do (unless (or (rd-pending-p r) (rd-root-only r))
               (loop for jj from (rd-start-block r) to (rd-leaves-end-block r)
                     do (let ((nb (f3-block-size f jj)))
                          (when (> (+ nb 35) pgsz)
                            (incf n (floor (+ nb 34) pgsz)))))))
    n))

(defstruct (f3tc) phrase itoken token root (novfl 0) (col 0))

(defun f3-token-costs (cs root x)
  "fts3EvalTokenCosts: (values token-costs or-roots) in tree order."
  (let ((tcs '()) (ors '()))
    (labels ((walk (root x)
               (case (fx-type x)
                 (:phrase
                  (let ((ph (fx-phrase x)))
                    (loop for tok across (ph-tokens ph)
                          for i from 0
                          do (push (make-f3tc :phrase ph :itoken i :token tok :root root :col (ph-column ph)
                                              :novfl (f3-leaf-overflow-pages cs (tk-segcsr tok)))
                                   tcs))))
                 (:not nil)
                 (t (if (eq (fx-type x) :or)
                        (progn (push (fx-left x) ors) (walk (fx-left x) (fx-left x))
                               (push (fx-right x) ors) (walk (fx-right x) (fx-right x)))
                        (progn (walk root (fx-left x)) (walk root (fx-right x))))))))
      (walk root x))
    (values (nreverse tcs) (nreverse ors))))

(defun f3-average-docsize (cs)
  (when (zerop (cs-nrowavg cs))
    (let* ((f (cs-fts cs)) (r (f3-stat-get f 0)) (ndoc 0) (nbyte 0))
      (let ((a (and r (first r))))
        (when (and (blobp a) (plusp (length a)))
          (let ((p (f3-padded a)) (i 0) (end (length a)))
            (multiple-value-setq (ndoc i) (f3-get-varint-bounded p i end))
            (loop while (< i end) do (multiple-value-setq (nbyte i) (f3-get-varint-bounded p i end))))))
      (when (or (zerop ndoc) (zerop nbyte)) (corrupt "database disk image is malformed"))
      (setf (cs-ndoc cs) ndoc
            (cs-nrowavg cs) (floor (+ (truncate nbyte ndoc) (f3-pgsz f)) (f3-pgsz f)))))
  (cs-nrowavg cs))

(defun f3-select-deferred (cs root tcs)
  "fts3EvalSelectDeferred."
  (let* ((f (cs-fts cs)) (nmin-est 0) (nload4 1) (novfl 0) (ntoken 0) (ndocsize 0)
         (mine (remove-if-not (lambda (tc) (eq (f3tc-root tc) root)) tcs)))
    (when (f3-content f) (return-from f3-select-deferred nil))
    (dolist (tc mine) (incf novfl (f3tc-novfl tc)) (incf ntoken))
    (when (or (zerop novfl) (< ntoken 2)) (return-from f3-select-deferred nil))
    (setf ndocsize (f3-average-docsize cs))
    (dotimes (ii ntoken)
      (let ((tc nil))
        (dolist (c mine)
          (when (and (f3tc-token c) (or (null tc) (< (f3tc-novfl c) (f3tc-novfl tc))))
            (setf tc c)))
        (if (and (plusp ii)
                 (>= (f3tc-novfl tc) (* (floor (+ nmin-est (floor nload4 4) -1) (floor nload4 4)) ndocsize)))
            (let ((tok (f3tc-token tc)))
              (f3-defer-token cs tok (f3tc-col tc))
              (setf (tk-segcsr tok) nil))
            (progn
              (when (< ii 12) (setf nload4 (* nload4 4)))
              (when (or (zerop ii) (and (> (length (ph-tokens (f3tc-phrase tc))) 1) (/= ii (1- ntoken))))
                (let ((tok (f3tc-token tc)))
                  (multiple-value-bind (list n) (f3-term-select cs tok (f3tc-col tc))
                    (f3-phrase-merge-token f (f3tc-phrase tc) (f3tc-itoken tc) list n))
                  (let ((count (f3-doclist-count-docids (ph-all (f3tc-phrase tc)) (ph-nall (f3tc-phrase tc)))))
                    (when (or (zerop ii) (< count nmin-est)) (setf nmin-est count)))))))
        (setf (f3tc-token tc) nil)))))

(defun f3-eval-start (cs)
  "fts3EvalStart."
  (let ((ntoken 0) (f (cs-fts cs)))
    (labels ((alloc (x)
               (when x
                 (if (eq (fx-type x) :phrase)
                     (let ((ph (fx-phrase x)))
                       (loop for tok across (ph-tokens ph)
                             do (incf ntoken)
                                (setf (tk-segcsr tok) (f3-term-seg-reader-cursor cs (tk-term tok) (tk-prefix-p tok))))
                       (setf (ph-doclist-token ph) -1))
                     (progn (alloc (fx-left x)) (alloc (fx-right x))))))
             (start (x)
               (when x
                 (if (eq (fx-type x) :phrase)
                     (let* ((ph (fx-phrase x)) (n (length (ph-tokens ph))))
                       (when (plusp n)
                         (setf (fx-deferred x) (every #'tk-deferred (ph-tokens ph))))
                       (f3-phrase-start cs t ph))
                     (progn (start (fx-left x)) (start (fx-right x))
                            (setf (fx-deferred x) (and (fx-deferred (fx-left x)) (fx-deferred (fx-right x)))))))))
      (alloc (cs-expr cs))
      (when (and (> ntoken 1) (f3-fts4-p f))
        (multiple-value-bind (tcs ors) (f3-token-costs cs nil (cs-expr cs))
          (f3-select-deferred cs nil tcs)
          (dolist (r ors) (f3-select-deferred cs r tcs))))
      (start (cs-expr cs)))))

;;; ------------------------------------------------------------------
;;; Iterating

(defun f3-near-trim (nnear ph aposlist ntoken)
  "fts3EvalNearTrim: trim PH's current position list (in place) to the
positions near APOSLIST (a (buf . off)).  Returns (values ok new-aposlist new-ntoken)."
  (let* ((p1 (+ nnear (length (ph-tokens ph))))
         (p2 (+ nnear ntoken))
         (out (f3-buf 32)))
    (if (f3-poslist-near-merge out p1 p2 (car aposlist) (cdr aposlist) (ph-list-buf ph) (ph-list-off ph))
        (let* ((nnew (1- (fill-pointer out)))
               (buf (ph-list-buf ph)) (off (ph-list-off ph)))
          (when (and (>= nnew 0) (<= nnew (ph-nlist ph)))
            (replace buf out :start1 off :end2 (1+ nnew))
            (fill buf 0 :start (+ off nnew) :end (+ off (ph-nlist ph)))
            (setf (ph-nlist ph) nnew))
          (values t (cons buf off) (length (ph-tokens ph))))
        (values nil aposlist ntoken))))

(defun f3-eval-next-row (cs x)
  "fts3EvalNextRow.  (SQLite 3.40 does not skip an expression already at
its end; later versions do.)"
  (progn
    (let ((desc (cs-desc cs)))
      (setf (fx-start x) t)
      (case (fx-type x)
        ((:near :and)
         (let ((l (fx-left x)) (r (fx-right x)))
           (cond ((fx-deferred l)
                  (f3-eval-next-row cs r)
                  (setf (fx-docid x) (fx-docid r) (fx-eof x) (fx-eof r)))
                 ((fx-deferred r)
                  (f3-eval-next-row cs l)
                  (setf (fx-docid x) (fx-docid l) (fx-eof x) (fx-eof l)))
                 (t
                  (f3-eval-next-row cs l)
                  (f3-eval-next-row cs r)
                  (loop while (and (not (fx-eof l)) (not (fx-eof r)))
                        do (let ((diff (f3-docid-cmp desc (fx-docid l) (fx-docid r))))
                             (when (zerop diff) (return))
                             (if (< diff 0) (f3-eval-next-row cs l) (f3-eval-next-row cs r))))
                  (setf (fx-docid x) (fx-docid l) (fx-eof x) (or (fx-eof l) (fx-eof r)))
                  (when (and (eq (fx-type x) :near) (fx-eof x))
                    (when (ph-all (fx-phrase r))
                      (loop until (fx-eof r)
                            do (let ((ph (fx-phrase r)))
                                 (when (ph-list-buf ph)
                                   (fill (ph-list-buf ph) 0 :start (ph-list-off ph) :end (+ (ph-list-off ph) (ph-nlist ph)))))
                               (f3-eval-next-row cs r)))
                    (when (and (fx-phrase l) (ph-all (fx-phrase l)))
                      (loop until (fx-eof l)
                            do (let ((ph (fx-phrase l)))
                                 (when (ph-list-buf ph)
                                   (fill (ph-list-buf ph) 0 :start (ph-list-off ph) :end (+ (ph-list-off ph) (ph-nlist ph)))))
                               (f3-eval-next-row cs l)))
                    (setf (fx-eof r) t (fx-eof l) t))))))
        (:or
         (let* ((l (fx-left x)) (r (fx-right x))
                (cmp (f3-docid-cmp desc (fx-docid l) (fx-docid r))))
           (cond ((or (fx-eof r) (and (not (fx-eof l)) (< cmp 0))) (f3-eval-next-row cs l))
                 ((or (fx-eof l) (> cmp 0)) (f3-eval-next-row cs r))
                 (t (f3-eval-next-row cs l) (f3-eval-next-row cs r)))
           (setf (fx-eof x) (and (fx-eof l) (fx-eof r)))
           (setf cmp (f3-docid-cmp desc (fx-docid l) (fx-docid r)))
           (setf (fx-docid x) (if (or (fx-eof r) (and (not (fx-eof l)) (< cmp 0))) (fx-docid l) (fx-docid r)))))
        (:not
         (let ((l (fx-left x)) (r (fx-right x)))
           (unless (fx-start r) (f3-eval-next-row cs r))
           (f3-eval-next-row cs l)
           (unless (fx-eof l)
             (loop while (and (not (fx-eof r)) (> (f3-docid-cmp desc (fx-docid l) (fx-docid r)) 0))
                   do (f3-eval-next-row cs r)))
           (setf (fx-docid x) (fx-docid l) (fx-eof x) (fx-eof l))))
        (t
         (let ((ph (fx-phrase x)))
           (f3-invalidate-poslist ph)
           (setf (fx-eof x) (f3-phrase-next cs ph))
           (setf (fx-docid x) (ph-docid ph))))))))

(defun f3-eval-near-test (x)
  "fts3EvalNearTest."
  (let ((res t))
    (when (and (eq (fx-type x) :near)
               (or (null (fx-parent x)) (not (eq (fx-type (fx-parent x)) :near))))
      (let ((p x))
        (loop while (fx-left p) do (setf p (fx-left p)))
        (let ((apos (cons (ph-list-buf (fx-phrase p)) (ph-list-off (fx-phrase p))))
              (ntok (length (ph-tokens (fx-phrase p)))))
          (loop for q = (fx-parent p) then (fx-parent q)
                while (and res q (eq (fx-type q) :near))
                do (multiple-value-setq (res apos ntok)
                     (f3-near-trim (fx-near q) (fx-phrase (fx-right q)) apos ntok)))
          (setf apos (cons (ph-list-buf (fx-phrase (fx-right x))) (ph-list-off (fx-phrase (fx-right x))))
                ntok (length (ph-tokens (fx-phrase (fx-right x)))))
          (loop for q = (fx-left x) then (fx-left q)
                while (and q res)
                do (let ((ph (if (eq (fx-type q) :near) (fx-phrase (fx-right q)) (fx-phrase q))))
                     (multiple-value-setq (res apos ntok)
                       (f3-near-trim (fx-near (fx-parent q)) ph apos ntok)))))))
    res))

(defun f3-eval-test-expr (cs x)
  "fts3EvalTestExpr."
  (case (fx-type x)
    ((:near :and)
     (let ((hit (and (f3-eval-test-expr cs (fx-left x))
                     (f3-eval-test-expr cs (fx-right x))
                     (f3-eval-near-test x))))
       (when (and (not hit) (eq (fx-type x) :near)
                  (or (null (fx-parent x)) (not (eq (fx-type (fx-parent x)) :near))))
         (let ((p x))
           (loop while (null (fx-phrase p))
                 do (when (= (fx-docid (fx-right p)) (cs-prev-id cs))
                      (f3-invalidate-poslist (fx-phrase (fx-right p))))
                    (setf p (fx-left p)))
           (when (= (fx-docid p) (cs-prev-id cs))
             (f3-invalidate-poslist (fx-phrase p)))))
       hit))
    (:or (let ((h1 (f3-eval-test-expr cs (fx-left x)))
               (h2 (f3-eval-test-expr cs (fx-right x))))
           (or h1 h2)))
    (:not (and (f3-eval-test-expr cs (fx-left x))
               (not (f3-eval-test-expr cs (fx-right x)))))
    (t (let ((ph (fx-phrase x)))
         (if (and (cs-deferred cs)
                  (or (fx-deferred x)
                      (and (= (fx-docid x) (cs-prev-id cs)) (ph-list-buf ph))))
             (progn
               (when (fx-deferred x) (f3-invalidate-poslist ph))
               (f3-deferred-phrase cs ph)
               (setf (fx-docid x) (cs-prev-id cs))
               (and (ph-list-buf ph) t))
             (and (not (fx-eof x)) (= (fx-docid x) (cs-prev-id cs)) (> (ph-nlist ph) 0)))))))

(defun f3-eval-test-deferred (cs)
  "sqlite3Fts3EvalTestDeferred: true if the current row does NOT match."
  (when (cs-deferred cs)
    (f3-cursor-load-row cs)
    (f3-cache-deferred-doclists cs))
  (prog1 (not (f3-eval-test-expr cs (cs-expr cs)))
    (f3-free-deferred-doclists cs)))

(defun f3-eval-next (cs)
  "fts3EvalNext: advance to the next matching row (CS-EOF at the end)."
  (let ((x (cs-expr cs)))
    (if (null x)
        (setf (cs-eof cs) t)
        (loop
          (f3-eval-next-row cs x)
          (setf (cs-eof cs) (fx-eof x)
                (cs-prev-id cs) (fx-docid x)
                (cs-row cs) nil)
          (when (or (cs-eof cs) (not (f3-eval-test-deferred cs))) (return))))
    (when (if (cs-desc cs)
              (< (cs-prev-id cs) (cs-min-docid cs))
              (> (cs-prev-id cs) (cs-max-docid cs)))
      (setf (cs-eof cs) t))))

(defun f3-eval-restart (cs x)
  (when x
    (let ((ph (fx-phrase x)))
      (when ph
        (f3-invalidate-poslist ph)
        (when (ph-incr ph)
          (loop for tok across (ph-tokens ph)
                do (when (tk-segcsr tok) (f3-msr-incr-restart (tk-segcsr tok))))
          (f3-phrase-start cs nil ph))
        (setf (ph-next-docid ph) nil (ph-docid ph) 0 (ph-or-poslist ph) nil)))
    (setf (fx-docid x) 0 (fx-eof x) nil (fx-start x) nil)
    (f3-eval-restart cs (fx-left x))
    (f3-eval-restart cs (fx-right x))))

;;; ------------------------------------------------------------------
;;; Statistics and position lists for the auxiliary functions

(defun f3-eval-update-counts (x ncol)
  (when x
    (let ((ph (fx-phrase x)))
      (when (and ph (ph-list-buf ph) (fx-mi x))
        (let ((buf (ph-list-buf ph)) (p (ph-list-off ph)) (col 0))
          (loop
            (let ((c 0) (cnt 0))
              (loop while (/= 0 (logand #xfe (logior (aref buf p) c)))
                    do (when (zerop (logand c #x80)) (incf cnt))
                       (setf c (logand (aref buf p) #x80))
                       (incf p))
              (when (< col ncol)
                (incf (aref (fx-mi x) (+ (* col 3) 1)) cnt)
                (when (plusp cnt) (incf (aref (fx-mi x) (+ (* col 3) 2)))))
              (when (zerop (aref buf p)) (return))
              (incf p)
              (multiple-value-setq (col p) (f3-get-varint32 buf p))
              (unless (< col ncol) (return)))))))
    (f3-eval-update-counts (fx-left x) ncol)
    (f3-eval-update-counts (fx-right x) ncol)))

(defun f3-eval-gather-stats (cs x)
  "fts3EvalGatherStats."
  (unless (fx-mi x)
    (let* ((f (cs-fts cs)) (ncol (f3-ncol f)) (root x)
           (prev-id (cs-prev-id cs)) (saved-row (cs-row cs)))
      ;; (3.40: the root is the top of the NEAR group; later versions also
      ;; climb past deferred nodes)
      (loop while (and (fx-parent root) (eq (fx-type (fx-parent root)) :near))
            do (setf root (fx-parent root)))
      (let ((docid (fx-docid root)) (eof (fx-eof root)))
        (loop for p = root then (fx-left p)
              while p
              do (let ((pe (if (eq (fx-type p) :phrase) p (fx-right p))))
                   (setf (fx-mi pe) (make-array (* ncol 3) :initial-element 0))))
        (f3-eval-restart cs root)
        (loop until (cs-eof cs)
              do (loop
                   (f3-eval-next-row cs root)
                   (setf (cs-eof cs) (fx-eof root) (cs-prev-id cs) (fx-docid root) (cs-row cs) nil)
                   (unless (and (not (cs-eof cs)) (eq (fx-type root) :near) (f3-eval-test-deferred cs))
                     (return)))
                 (unless (cs-eof cs)
                   (f3-eval-update-counts root ncol)))
        (setf (cs-eof cs) nil (cs-prev-id cs) prev-id (cs-row cs) saved-row)
        (if eof
            (setf (fx-eof root) t)
            (progn
              (f3-eval-restart cs root)
              (loop (f3-eval-next-row cs root)
                    (when (fx-eof root) (corrupt "database disk image is malformed"))
                    (when (= (fx-docid root) docid) (return)))))))))

(defun f3-expr-phrases-all (x)
  "Every phrase node under X (sqlite3Fts3ExprIterate: NOT's right side excluded)."
  (f3-expr-phrases x))

(defun f3-eval-phrase-stats (cs x)
  "sqlite3Fts3EvalPhraseStats: vector of (hits-all-rows docs-with-hits) per column."
  (let* ((f (cs-fts cs)) (ncol (f3-ncol f)) (out (make-array (* 2 ncol) :initial-element 0)))
    (if (and (fx-deferred x) (fx-parent x) (not (eq (fx-type (fx-parent x)) :near)))
        (dotimes (i ncol)
          (setf (aref out (* 2 i)) (logand (cs-ndoc cs) #xffffffff)
                (aref out (1+ (* 2 i))) (logand (cs-ndoc cs) #xffffffff)))
        (progn
          (f3-eval-gather-stats cs x)
          (dotimes (i ncol)
            (setf (aref out (* 2 i)) (aref (fx-mi x) (+ (* i 3) 1))
                  (aref out (1+ (* 2 i))) (aref (fx-mi x) (+ (* i 3) 2))))))
    out))

(defun f3-eval-phrase-poslist (cs x col)
  "sqlite3Fts3EvalPhrasePoslist: (values buf off) of the phrase's column
list for COL in the current row, or NIL."
  (let* ((f (cs-fts cs)) (ph (fx-phrase x)) (ncol (f3-ncol f))
         (buf (ph-list-buf ph)) (iter (ph-list-off ph)))
    (when (and (< (ph-column ph) ncol) (/= (ph-column ph) col))
      (return-from f3-eval-phrase-poslist nil))
    (when (or (/= (fx-docid x) (cs-prev-id cs)) (fx-eof x))
      (let ((desc-dl (f3-desc-p f)) (or-p nil) (tree-eof nil) (near x) (run nil))
        (loop for p = (fx-parent x) then (fx-parent p)
              while p
              do (when (eq (fx-type p) :or) (setf or-p t))
                 (when (eq (fx-type p) :near) (setf near p))
                 (when (fx-eof p) (setf tree-eof t)))
        (unless or-p (return-from f3-eval-phrase-poslist nil))
        (setf run near)                 ; (3.40; later versions skip deferred nodes)
        (when (ph-incr ph)
          (let ((eof-save (fx-eof run)) (docid (fx-docid x)))
            (f3-eval-restart cs run)
            (loop until (fx-eof run)
                  do (f3-eval-next-row cs run)
                     (when (and (not eof-save) (= (fx-docid run) docid)) (return)))
            (unless (eq (and (fx-eof run) t) (and eof-save t))
              (corrupt "database disk image is malformed"))))
        (when tree-eof
          (loop until (fx-eof run) do (f3-eval-next-row cs run)))
        (let ((match t))
          (loop for p = near then (fx-left p)
                while p
                do (let* ((test (if (eq (fx-type p) :near) (fx-right p) p))
                          (pph (fx-phrase test))
                          (it (ph-or-poslist pph)) (docid (ph-or-docid pph)) (eof nil))
                     (if (eq (and (cs-desc cs) t) (and desc-dl t))
                         (progn
                           (setf eof (or (zerop (ph-nall pph)) (and it (>= it (ph-nall pph)))))
                           (loop while (and (or (null it) (< (f3-docid-cmp desc-dl docid (cs-prev-id cs)) 0)) (not eof))
                                 do (multiple-value-setq (it docid eof)
                                      (f3-doclist-next desc-dl (ph-all pph) (ph-nall pph) it docid))))
                         (progn
                           (setf eof (or (zerop (ph-nall pph)) (and it (<= it 0))))
                           (loop while (and (or (null it) (> (f3-docid-cmp desc-dl docid (cs-prev-id cs)) 0)) (not eof))
                                 do (multiple-value-bind (i2 d2 n2 e2)
                                        (f3-doclist-prev desc-dl (ph-all pph) 0 (ph-nall pph) it docid)
                                      (declare (ignore n2))
                                      (setf it i2 docid d2 eof e2)))))
                     (setf (ph-or-poslist pph) it (ph-or-docid pph) docid)
                     (when (or eof (/= docid (cs-prev-id cs))) (setf match nil))))
          (if match
              (setf buf (ph-all ph) iter (ph-or-poslist ph))
              (setf buf nil)))))
    (unless buf (return-from f3-eval-phrase-poslist nil))
    (let ((this 0))
      (if (= (aref buf iter) 1)
          (progn (incf iter) (multiple-value-setq (this iter) (f3-get-varint32 buf iter)))
          (setf this 0))
      (loop while (< this col)
            do (setf iter (f3-columnlist-skip buf iter))
               (when (zerop (aref buf iter)) (return-from f3-eval-phrase-poslist nil))
               (incf iter)
               (multiple-value-setq (this iter) (f3-get-varint32 buf iter)))
      (when (zerop (aref buf iter)) (return-from f3-eval-phrase-poslist nil))
      (if (= col this) (values buf iter) nil))))
