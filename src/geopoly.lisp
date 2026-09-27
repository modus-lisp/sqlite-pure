;;;; geopoly.lisp — the Geopoly module (geopoly.c): polygons in an r-tree.
;;;;
;;;; CREATE VIRTUAL TABLE t USING geopoly(a, b, ...) declares
;;;; t(_shape, a, b, ...) and is stored exactly as a 2-dimensional float
;;;; r-tree whose auxiliary columns are _shape and the user's columns: each
;;;; entry's coordinates are the bounding box of its _shape, and a0 of the
;;;; <t>_rowid shadow table holds the polygon itself.
;;;;
;;;; A polygon is a blob: a 4-byte header (byte 0: 1 = little-endian
;;;; coordinates, 0 = big-endian; bytes 1-3: the vertex count, big-endian)
;;;; then x,y float32 pairs.  JSON text '[[x,y],...,[x,y]]' is accepted
;;;; wherever a polygon is (at least 4 vertices, the last repeating the
;;;; first).  Coordinates are float32 throughout and every computation that
;;;; C does in float is done in float here too: a double holding a float32
;;;; value, rounded with F32 after each float operation (for + - * / of two
;;;; floats, rounding the double result again gives the float result).

(in-package #:sqlite-pure)

(defun geo-p (v) (and (rtree-p v) (equal (rtree-module v) "geopoly")))

;;; ------------------------------------------------------------------
;;; Polygons

(defstruct (gpoly (:constructor make-gpoly (n xy &optional (hdr (list 0 (ldb (byte 8 8) n) (ldb (byte 8 0) n))))))
  n                      ; vertex count
  xy                     ; simple-vector of 2n float32 values (as doubles)
  hdr)                   ; header bytes 1-3, as given

(defun gx (p i) (svref (gpoly-xy p) (* 2 i)))
(defun gy (p i) (svref (gpoly-xy p) (1+ (* 2 i))))

(defun gpoly-blob (p)
  (let* ((n (gpoly-n p)) (b (make-octets (+ 4 (* 8 n)))))
    (setf (aref b 0) 1)
    (loop for h in (gpoly-hdr p) for k from 1 do (setf (aref b k) h))
    (loop for i below (* 2 n)
          for u = (f32-bits (svref (gpoly-xy p) i))
          for off = (+ 4 (* 4 i))
          do (dotimes (k 4) (setf (aref b (+ off k)) (ldb (byte 8 (* 8 k)) u))))
    b))

(defun geo-json-space-p (c) (member c '(9 10 13 32)))

(defun geo-parse-json (s)
  "geopolyParseJson: (values GPOLY-or-NIL status).  Text that does not
start with '[' is no polygon but no error either (status :OK), as in C."
  (let ((pos 0) (len (length s)) (xy (make-array 16 :adjustable t :fill-pointer 0)) (nv 0))
    (labels ((at (i) (if (and (>= i 0) (< i len)) (char-code (char s i)) 0))
             (ch (i) (let ((c (at i))) (if (zerop c) 0 c)))
             (skip () (loop while (geo-json-space-p (ch pos)) do (incf pos)) (ch pos))
             (digitp (c) (<= 48 c 57))
             (number ()
               ;; geopolyParseNumber: 1 and the value, 0 if not a number, -1
               (let* ((c (skip)) (z pos) (j 0) (seen-dp nil) (seen-e nil))
                 (flet ((z (k) (ch (+ z k))))
                   (when (= c (char-code #\-)) (setf j 1 c (z j)))
                   (when (and (= c (char-code #\0)) (digitp (z (1+ j)))) (return-from number 0))
                   (loop
                     (setf c (z j))
                     (cond ((digitp c))
                           ((= c (char-code #\.))
                            (when (= (z (1- j)) (char-code #\-)) (return-from number 0))
                            (when seen-dp (return-from number 0))
                            (setf seen-dp t))
                           ((member c '(101 69))
                            (when (< (z (1- j)) 48) (return-from number 0))
                            (when seen-e (return-from number -1))
                            (setf seen-dp t seen-e t)
                            (setf c (z (1+ j)))
                            (when (member c '(43 45)) (incf j) (setf c (z (1+ j))))
                            (unless (digitp c) (return-from number 0)))
                           (t (return)))
                     (incf j))
                   (when (< (z (1- j)) 48) (return-from number 0))
                   (let ((v (if (zerop j) 0d0 (let ((r (value-to-real (subseq s z (+ z j))))) (if (floatp r) r 0d0)))))
                     (setf pos (+ z j))
                     (values 1 (f32 v)))))))
      (unless (= (skip) (char-code #\[))
        (return-from geo-parse-json (values nil :ok)))
      (incf pos)
      (progn
        (loop while (= (skip) (char-code #\[))
              do (incf pos)
                 (let ((ii 0))
                   (loop
                     (multiple-value-bind (r v) (number)
                       (when (eql r 0) (return))
                       (when (eql r -1) (return-from geo-parse-json (values nil :error)))
                       (when (<= ii 1) (vector-push-extend v xy))
                       (incf ii)
                       (when (= ii 2) (incf nv))
                       (let ((c (skip)))
                         (incf pos)
                         (cond ((= c (char-code #\,)))
                               ((and (= c (char-code #\])) (>= ii 2)) (return))
                               (t (return-from geo-parse-json (values nil :error)))))))
                   ;; a vertex with only one number stays half-stored, as in C
                   (when (/= (length xy) (* 2 nv)) (setf (fill-pointer xy) (* 2 nv))))
                 (if (= (skip) (char-code #\,))
                     (incf pos)
                     (return)))
        (when (and (= (skip) (char-code #\]))
                   (>= nv 4)
                   (= (aref xy 0) (aref xy (- (* 2 nv) 2)))
                   (= (aref xy 1) (aref xy (- (* 2 nv) 1)))
                   (progn (incf pos) (zerop (skip))))
          (decf nv)
          (return-from geo-parse-json
            (values (make-gpoly nv (subseq (coerce xy 'simple-vector) 0 (* 2 nv))) :ok))))
      (values nil :error))))

(defun geo-param (v)
  "geopolyFuncParam: (values GPOLY-or-NIL status), status :OK or :ERROR.
A blob of the right size with a bad header is NIL but :OK, as in C."
  (cond ((and (blobp v) (>= (length v) 28))
         (let ((nv (+ (ash (aref v 1) 16) (ash (aref v 2) 8) (aref v 3))))
           (if (and (<= (aref v 0) 1) (= (+ 4 (* 8 nv)) (length v)))
               (let ((xy (make-array (* 2 nv))) (le (= (aref v 0) 1)))
                 (dotimes (i (* 2 nv))
                   (let ((off (+ 4 (* 4 i))))
                     (setf (svref xy i)
                           (f32-from-bits (if le
                                              (logior (aref v off) (ash (aref v (+ off 1)) 8)
                                                      (ash (aref v (+ off 2)) 16) (ash (aref v (+ off 3)) 24))
                                              (get-u32 v off))))))
                 (values (make-gpoly nv xy (list (aref v 1) (aref v 2) (aref v 3))) :ok))
               (values nil :ok))))
        ((stringp v) (geo-parse-json v))
        (t (values nil :error))))

(defun geo-poly (v) (values (geo-param v)))

(defun geo-area (p)
  (let ((a 0d0) (n (gpoly-n p)))
    (flet ((term (i j) (* (f32 (* (f32 (- (gx p i) (gx p j))) (f32 (+ (gy p i) (gy p j))))) 0.5d0)))
      (loop for i below (1- n) do (incf a (term i (1+ i))))
      (incf a (term (1- n) 0)))
    a))

(defun geo-bbox-coords (v)
  "geopolyBBox into coordinates: (values #(minx maxx miny maxy) status)."
  (multiple-value-bind (p st) (geo-param v)
    (cond (p (let ((mnx (gx p 0)) (mxx (gx p 0)) (mny (gy p 0)) (mxy (gy p 0)))
               (loop for i from 1 below (gpoly-n p)
                     do (let ((r (gx p i)))
                          (cond ((< r mnx) (setf mnx r)) ((> r mxx) (setf mxx r))))
                        (let ((r (gy p i)))
                          (cond ((< r mny) (setf mny r)) ((> r mxy) (setf mxy r)))))
               (values (vector mnx mxx mny mxy) :ok)))
          ((eq st :ok) (values (vector 0d0 0d0 0d0 0d0) :ok))
          (t (values nil :error)))))

(defun geo-box-poly (c)
  (make-gpoly 4 (vector (svref c 0) (svref c 2) (svref c 1) (svref c 2)
                        (svref c 1) (svref c 3) (svref c 0) (svref c 3))))

;;; ------------------------------------------------------------------
;;; Overlap (a sweep line over the segments of both polygons)

(defstruct (gseg (:conc-name gs-)) (c 0d0) (b 0d0) (y 0d0) (y0 0d0) side idx next)
(defstruct (gevent (:conc-name ge-)) x type seg next)

(defun geo-merge (left right take-right-p next set-next)
  "Merge two linked lists, taking from RIGHT when TAKE-RIGHT-P says so."
  (let ((first nil) (last nil))
    (flet ((append1 (x) (if last (funcall set-next last x) (setf first x)) (setf last x)))
      (loop while (and right left)
            do (if (funcall take-right-p left right)
                   (let ((r right)) (setf right (funcall next right)) (append1 r))
                   (let ((l left)) (setf left (funcall next left)) (append1 l))))
      (let ((rest (or right left)))
        (if last (funcall set-next last rest) (setf first rest))))
    first))

(defun geo-event-merge (left right)
  (geo-merge left right (lambda (l r) (<= (ge-x r) (ge-x l)))
             #'ge-next (lambda (x v) (setf (ge-next x) v))))

(defun geo-seg-merge (left right)
  (geo-merge left right (lambda (l r) (let ((d (- (gs-y r) (gs-y l))))
                                        (when (= d 0) (setf d (- (gs-c r) (gs-c l))))
                                        (< d 0)))
             #'gs-next (lambda (x v) (setf (gs-next x) v))))

(defun geo-sort-list (items merge set-next)
  "The bottom-up merge sort geopoly uses (so ties fall exactly as in C)."
  (let ((a (make-array 50 :initial-element nil)) (mx 0))
    (dolist (p items)
      (funcall set-next p nil)
      (let ((j 0))
        (loop while (and (< j mx) (aref a j))
              do (setf p (funcall merge (aref a j) p) (aref a j) nil)
                 (incf j))
        (setf (aref a j) p)
        (when (>= j mx) (setf mx (1+ j)))))
    (let ((p nil))
      (dotimes (i mx) (setf p (funcall merge (aref a i) p)))
      p)))

(defun geo-overlap (p1 p2)
  "geopolyOverlap: 0 disjoint, 1 overlap, 2 P1 inside P2, 3 P2 inside P1, 4 same."
  (let ((events '()))
    (flet ((add (x0 y0 x1 y1 side idx)
             (unless (= x0 x1)
               (when (> x0 x1) (rotatef x0 x1) (rotatef y0 y1))
               (let* ((c (f32 (/ (f32 (- y1 y0)) (f32 (- x1 x0)))))
                      (s (make-gseg :c c :b (- y1 (* x1 c)) :y0 y0 :side side :idx idx)))
                 (push (make-gevent :x x0 :type 0 :seg s) events)
                 (push (make-gevent :x x1 :type 1 :seg s) events)))))
      (dolist (pp (list (cons p1 1) (cons p2 2)))
        (let* ((p (car pp)) (n (gpoly-n p)))
          (loop for i below (1- n) do (add (gx p i) (gy p i) (gx p (1+ i)) (gy p (1+ i)) (cdr pp) i))
          (add (gx p (1- n)) (gy p (1- n)) (gx p 0) (gy p 0) (cdr pp) (1- n)))))
    (let* ((ev (geo-sort-list (nreverse events) #'geo-event-merge (lambda (x v) (setf (ge-next x) v))))
           (rx (if (and ev (= (ge-x ev) 0)) -1d0 0d0))
           (active nil) (need-sort nil)
           (ov (make-array 4 :initial-element 0)))
      (loop while ev
            do (unless (= (ge-x ev) rx)
                 (setf rx (ge-x ev))
                 (when need-sort
                   (let ((items (loop for s = active then (gs-next s) while s collect s)))
                     (setf active (geo-sort-list items #'geo-seg-merge (lambda (x v) (setf (gs-next x) v)))))
                   (setf need-sort nil))
                 (let ((prev nil) (mask 0))
                   (loop for s = active then (gs-next s) while s
                         do (when (and prev (/= (gs-y prev) (gs-y s))) (setf (aref ov mask) 1))
                            (setf mask (logxor mask (gs-side s)) prev s)))
                 (let ((prev nil) (mask 0))
                   (loop for s = active then (gs-next s) while s
                         do (setf (gs-y s) (+ (* (gs-c s) rx) (gs-b s)))
                            (when prev
                              (cond ((and (> (gs-y prev) (gs-y s)) (/= (gs-side prev) (gs-side s)))
                                     (return-from geo-overlap 1))
                                    ((/= (gs-y prev) (gs-y s)) (setf (aref ov mask) 1))))
                            (setf mask (logxor mask (gs-side s)) prev s))))
               (let ((seg (ge-seg ev)))
                 (if (= (ge-type ev) 0)
                     (setf (gs-y seg) (gs-y0 seg) (gs-next seg) active active seg need-sort t)
                     (if (eq active seg)
                         (setf active (gs-next active))
                         (loop for s = active then (gs-next s) while s
                               do (when (eq (gs-next s) seg)
                                    (setf (gs-next s) (gs-next seg))
                                    (return))))))
               (setf ev (ge-next ev)))
      (cond ((zerop (aref ov 3)) 0)
            ((and (/= (aref ov 1) 0) (zerop (aref ov 2))) 3)
            ((and (zerop (aref ov 1)) (/= (aref ov 2) 0)) 2)
            ((and (zerop (aref ov 1)) (zerop (aref ov 2))) 4)
            (t 1)))))

(defun point-beneath-line (x0 y0 x1 y1 x2 y2)
  (cond ((and (= x0 x1) (= y0 y1)) 2)
        ((< x1 x2) (if (or (<= x0 x1) (> x0 x2)) 0 (pbl-at x0 y0 x1 y1 x2 y2)))
        ((> x1 x2) (if (or (<= x0 x2) (> x0 x1)) 0 (pbl-at x0 y0 x1 y1 x2 y2)))
        ((/= x0 x1) 0)
        ((and (< y0 y1) (< y0 y2)) 0)
        ((and (> y0 y1) (> y0 y2)) 0)
        (t 2)))

(defun pbl-at (x0 y0 x1 y1 x2 y2)
  (let ((y (+ y1 (/ (* (- y2 y1) (- x0 x1)) (- x2 x1)))))
    (cond ((= y0 y) 2) ((< y0 y) 1) (t 0))))

(defun geopoly-sine (r)
  (let ((pi* 3.1415926535897932385d0))
    (when (>= r (* 1.5d0 pi*)) (decf r (* 2d0 pi*)))
    (if (>= r (* 0.5d0 pi*))
        (- (geopoly-sine (- r pi*)))
        (let* ((r2 (* r r)) (r3 (* r2 r)) (r5 (* r3 r2)))
          (+ (- (* 0.9996949d0 r) (* 0.1656700d0 r3)) (* 0.0075134d0 r5))))))

;;; ------------------------------------------------------------------
;;; SQL functions

(defun geo-result (p) (if p (gpoly-blob p) :null))

(defsqlfun "geopoly_area" (1 1) (args)
  (let ((p (geo-poly (first args)))) (if p (geo-area p) :null)))

(defsqlfun "geopoly_blob" (1 1) (args) (geo-result (geo-poly (first args))))

(defsqlfun "geopoly_json" (1 1) (args)
  (let ((p (geo-poly (first args))))
    (if (null p)
        :null
        (with-output-to-string (s)
          (write-string "[" s)
          (dotimes (i (gpoly-n p))
            (write-string (sql-printf "[%!g,%!g]," (list (gx p i) (gy p i))) s))
          (write-string (sql-printf "[%!g,%!g]]" (list (gx p 0) (gy p 0))) s)))))

(defsqlfun "geopoly_svg" (0 nil) (args)
  (let ((p (and args (geo-poly (first args)))))
    (if (null p)
        :null
        (with-output-to-string (s)
          (write-string "<polyline points=" s)
          (dotimes (i (gpoly-n p))
            (write-string (sql-printf "%c%g,%g" (list (if (zerop i) "'" " ") (gx p i) (gy p i))) s))
          (write-string (sql-printf " %g,%g'" (list (gx p 0) (gy p 0))) s)
          (dolist (a (rest args))
            (unless (eq a :null)
              (let ((z (value-to-text a)))
                (when (plusp (length z)) (format s " ~a" z)))))
          (write-string "></polyline>" s)))))

(defsqlfun "geopoly_xform" (7 7) (args)
  (let ((p (geo-poly (first args))))
    (destructuring-bind (a b c d e f) (mapcar #'rt-double (rest args))
      (if (null p)
          :null
          (let ((xy (gpoly-xy p)))
            (dotimes (i (gpoly-n p))
              (let ((x0 (gx p i)) (y0 (gy p i)))
                (setf (svref xy (* 2 i)) (f32 (+ (+ (* a x0) (* b y0)) e))
                      (svref xy (1+ (* 2 i))) (f32 (+ (+ (* c x0) (* d y0)) f)))))
            (gpoly-blob p))))))

(defsqlfun "geopoly_ccw" (1 1) (args)
  (let ((p (geo-poly (first args))))
    (when (and p (< (geo-area p) 0))
      (let ((xy (gpoly-xy p)))
        (loop for i from 1 for j downfrom (1- (gpoly-n p)) while (< i j)
              do (rotatef (svref xy (* 2 i)) (svref xy (* 2 j)))
                 (rotatef (svref xy (1+ (* 2 i))) (svref xy (1+ (* 2 j)))))))
    (geo-result p)))

(defsqlfun "geopoly_regular" (4 4) (args)
  (let ((x (rt-double (first args))) (y (rt-double (second args)))
        (r (rt-double (third args))) (n (rt-int32 (fourth args))))
    (if (or (< n 3) (<= r 0d0))
        :null
        (let* ((n (min n 1000)) (xy (make-array (* 2 n))) (pi* 3.1415926535897932385d0))
          (dotimes (i n)
            (let ((angle (/ (* (* 2d0 pi*) i) n)))
              (setf (svref xy (* 2 i)) (f32 (- x (* r (geopoly-sine (- angle (* 0.5d0 pi*))))))
                    (svref xy (1+ (* 2 i))) (f32 (+ y (* r (geopoly-sine angle)))))))
          (gpoly-blob (make-gpoly n xy))))))

(defsqlfun "geopoly_bbox" (1 1) (args)
  (if (geo-poly (first args))
      (gpoly-blob (geo-box-poly (geo-bbox-coords (first args))))
      :null))

(defsqlfun "geopoly_contains_point" (3 3) (args)
  (let ((p (geo-poly (first args))) (x0 (rt-double (second args))) (y0 (rt-double (third args))))
    (if (null p)
        :null
        (let ((v 0) (cnt 0) (n (gpoly-n p)) (i 0))
          (loop while (< i (1- n))
                do (setf v (point-beneath-line x0 y0 (gx p i) (gy p i) (gx p (1+ i)) (gy p (1+ i))))
                   (when (= v 2) (return))
                   (incf cnt v)
                   (incf i))
          (unless (= v 2)
            (setf v (point-beneath-line x0 y0 (gx p i) (gy p i) (gx p 0) (gy p 0))))
          (cond ((= v 2) 1) ((zerop (logand (+ v cnt) 1)) 0) (t 2))))))

(defsqlfun "geopoly_within" (2 2) (args)
  (let ((p1 (geo-poly (first args))) (p2 (geo-poly (second args))))
    (if (and p1 p2)
        (case (geo-overlap p1 p2) (2 1) (4 2) (t 0))
        :null)))

(defsqlfun "geopoly_overlap" (2 2) (args)
  (let ((p1 (geo-poly (first args))) (p2 (geo-poly (second args))))
    (if (and p1 p2) (geo-overlap p1 p2) :null)))

(defsqlfun "geopoly_debug" (1 1) (args)
  (declare (ignore args))
  :null)

(defaggregate "geopoly_group_bbox" (1 1)
  (let ((box nil))
    (values (lambda (args)
              (multiple-value-bind (a st) (geo-bbox-coords (first args))
                (when (eq st :ok)
                  (if (null box)
                      (setf box a)
                      (progn (when (< (svref a 0) (svref box 0)) (setf (svref box 0) (svref a 0)))
                             (when (> (svref a 1) (svref box 1)) (setf (svref box 1) (svref a 1)))
                             (when (< (svref a 2) (svref box 2)) (setf (svref box 2) (svref a 2)))
                             (when (> (svref a 3) (svref box 3)) (setf (svref box 3) (svref a 3)))))))
              nil)
            (lambda () (if box (gpoly-blob (geo-box-poly box)) :null)))))

;;; ------------------------------------------------------------------
;;; The virtual table

(defun geopoly-spec (args)
  (make-rtree :module "geopoly" :ndim2 4 :int-p nil :naux (1+ (length args))
              :names (cons "_shape" (mapcar #'rtree-arg-name args))))

(defun geopoly-declaration (args)
  (format nil "CREATE TABLE x(_shape~{,~a~});" args))

(defun geopoly-table-from-ast (name args sql)
  (let ((tb (table-from-ast name (car (first (parse-sql (geopoly-declaration args)))) 0 sql)))
    (setf (table-vtab tb) (geopoly-spec args))
    tb))

(defun geopoly-write (ctx old new)
  "geopolyUpdate: delete OLD (if OLD and no NEW), else insert or update.
Returns the new rowid, T, or :IGNORE."
  (let* ((rt (rt-spec)) (tb (rt-table)) (naux (rtree-naux rt))
         (nochange (and old new (listp *update-columns*) (not (member 0 *update-columns*))))
         (old-id (and old (rt-int64 (svref old naux))))
         (new-valid (and new (not (eq (svref new naux) :null))))
         (id (if new-valid (rt-int64 (svref new naux)) 0))
         (coords nil))
    (when (and new (or (null old) (not nochange) (/= old-id id)))
      (multiple-value-bind (c st) (geo-bbox-coords (if nochange :null (svref new 0)))
        (unless (eq st :ok) (sql-error "_shape does not contain a valid polygon"))
        (setf coords c))
      (when (and new-valid (or (null old) (/= old-id id)) (shadow-get (rt-rowid-table) id))
        (let ((action (resolve-action ctx nil)))
          (case action
            (:replace (rtree-delete-id id))
            (:ignore (return-from geopoly-write :ignore))
            (t (conflict-fail action "UNIQUE constraint failed: ~a._shape" (table-name tb)))))))
    (when (or (null new) (and coords old))
      (rtree-delete-id old-id))
    (when (and new coords)
      (unless new-valid
        (setf id (rtree-new-rowid)))
      (insert-at-height (cons id coords) 0))
    (when new
      (let ((r (shadow-get (rt-rowid-table) id)))
        (when r
          (let* ((v (svref new 0))
                 (shape (cond (nochange (or (second r) :null))
                              ((and (stringp v) (geo-poly v)) (gpoly-blob (geo-poly v)))
                              (t v))))
            (shadow-put (rt-rowid-table) id
                        (list* (first r) shape (loop for i from 1 below naux collect (svref new i))))))))
    (flush-rnodes)
    (unless (= (rtree-depth) *rt-depth*)
      (let ((root (load-rnode 1))) (setf (rn-dirty root) t) (flush-rnodes)))
    (if new id t)))

(defun geopoly-vtab-insert (ctx row)
  (with-rtree ((wc-table ctx))
    (let* ((*rt-depth* (rtree-depth))
           (id (geopoly-write ctx nil row)))
      (unless (eq id :ignore)
        (setf (db-last-insert-rowid (conn *db*)) id)
        (incf (wc-changes ctx))
        (setf (svref row (1- (length row))) -1)
        (collect-returning ctx row)
        t))))

(defun geopoly-vtab-update (ctx old new)
  (with-rtree ((wc-table ctx))
    (let ((*rt-depth* (rtree-depth)))
      (unless (eq (geopoly-write ctx old new) :ignore)
        (incf (wc-changes ctx))
        t))))

(defun geopoly-vtab-delete (table row)
  (with-rtree (table)
    (let ((*rt-depth* (rtree-depth)))
      (geopoly-write nil row nil))))

(defun geopoly-row (id)
  (let* ((aux (rtree-aux id)) (row (make-array (1+ (length aux)))))
    (replace row aux)
    (setf (svref row (length aux)) id)
    row))

(defun geopoly-func-term (conjuncts li scope)
  "The last geopoly_overlap(_shape, X) / geopoly_within(_shape, X) conjunct:
(values 2-or-3 X)."
  (let ((found nil) (arg nil))
    (dolist (c conjuncts)
      (when (and (eq (car c) :fn) (member (second c) '("geopoly_overlap" "geopoly_within") :test #'string-equal)
                 (= (length (third c)) 2) (not (fourth c)) (not (fifth c)) (not (sixth c)))
        (let ((a (first (third c))) (b (second (third c))))
          (multiple-value-bind (depth si ci)
              (case (car a)
                (:col (resolve-column scope (second a) (third a)))
                (:srccol (values 0 (second a) (third a))))
            (when (and depth (= depth 0) (= si li) (eql ci 0))
              (let ((refs (expr-refs b scope)))
                (when (and (listp refs) (every (lambda (r) (< r li)) refs))
                  (setf found (if (string-equal (second c) "geopoly_overlap") 2 3) arg b))))))))
    (values found arg)))

(defun geopoly-plan-access (fs li conjuncts scope)
  (let* ((table (fsrc-table fs))
         (rowid-eq (find-if (lambda (c) (and (eq (first c) :rowid) (eq (fourth c) :eq)))
                            (equality-candidates conjuncts li scope)))
         (id-fn (and rowid-eq (compile-expr (second rowid-eq) scope))))
    (multiple-value-bind (idx arg) (if id-fn (values 1 nil) (geopoly-func-term conjuncts li scope))
      (let ((idx (or idx 4))
            (arg-fn (and arg (compile-expr arg scope))))
        (eqp-table-note (format nil "SCAN ~a VIRTUAL TABLE INDEX ~d:~a" (src-name (fsrc-src fs)) idx
                                (case idx (1 "rowid") (4 "fullscan") (t "rtree"))))
        (lambda (env fn)
          (with-rtree (table)
            (if id-fn
                (let* ((id (rowid-probe (funcall id-fn env)))
                       (leafno (and id (first (shadow-get (rt-rowid-table) id))))
                       (cell (and (integerp leafno) (assoc id (rn-cells (load-rnode leafno))))))
                  (when cell (funcall fn (geopoly-row id))))
                (let ((tests (when arg-fn
                               (multiple-value-bind (b st) (geo-bbox-coords (funcall arg-fn env))
                                 (unless (eq st :ok) (sql-error "SQL logic error"))
                                 (if (= idx 2)
                                     (list (list 0 :le (svref b 1)) (list 1 :ge (svref b 0))
                                           (list 2 :le (svref b 3)) (list 3 :ge (svref b 2)))
                                     (list (list 0 :ge (svref b 0)) (list 1 :le (svref b 1))
                                           (list 2 :ge (svref b 2)) (list 3 :le (svref b 3)))))))
                      (depth (rtree-depth)))
                  (labels ((leaf-ok (c)
                             (loop for (k op v) in tests
                                   always (if (eq op :le) (<= (svref c k) v) (>= (svref c k) v))))
                           (walk (node height)
                             (dolist (c (rn-cells node))
                               (if (zerop height)
                                   (when (leaf-ok (cdr c)) (funcall fn (geopoly-row (car c))))
                                   (when (box-may-match (cdr c) tests)
                                     (walk (load-rnode (car c) (rn-no node)) (1- height)))))))
                    (walk (load-rnode 1) depth))))))))))
