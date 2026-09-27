;;;; btree.lisp — table and index b-trees.
;;;;
;;;; Reads walk page bytes in place; writes are btree-edit.lisp's port of
;;;; SQLite's.

(in-package #:sqlite-pure)

(declaim (inline hdr-off leaf-type-p table-type-p page-hdr-size))
(defun hdr-off (pgno) (if (= pgno 1) 100 0))
(defun leaf-type-p (type) (>= type 10))
(defun table-type-p (type) (or (= type +interior-table+) (= type +leaf-table+)))
(defun page-hdr-size (type) (if (leaf-type-p type) 8 12))

(defun check-page-type (type pgno)
  (unless (member type '(2 5 10 13))
    (corrupt "page ~d has invalid b-tree page type ~d" pgno type))
  type)


;;; ------------------------------------------------------------------
;;; Payload geometry

(defun max-local (db table-leaf-p)
  (let ((u (db-usable-size db)))
    (if table-leaf-p (- u 35) (- (floor (* (- u 12) 64) 255) 23))))

(defun min-local (db)
  (- (floor (* (- (db-usable-size db) 12) 32) 255) 23))

(defun local-size (db psize table-leaf-p)
  (let ((x (max-local db table-leaf-p)))
    (if (<= psize x)
        psize
        (let* ((m (min-local db))
               (k (+ m (mod (- psize m) (- (db-usable-size db) 4)))))
          (if (<= k x) k m)))))

(defun read-overflow (db first out start)
  "Fill OUT from START with the overflow chain beginning at page FIRST."
  (let ((pos start) (pg first) (cap (- (db-usable-size db) 4)) (seen 0))
    (loop while (< pos (length out))
          do (when (or (zerop pg) (> (incf seen) (db-page-count db)))
               (corrupt "overflow chain truncated"))
             (let* ((b (read-page db pg))
                    (n (min cap (- (length out) pos))))
               (replace out b :start1 pos :start2 4 :end2 (+ 4 n))
               (incf pos n)
               (setf pg (get-u32 b 0))))
    out))

(defun read-payload (db b p psize local)
  "Full payload of a cell whose local part starts at B[P]."
  (if (= local psize)
      (octets-subseq b p (+ p psize))
      (let ((out (make-octets psize)))
        (replace out b :start2 p :end2 (+ p local))
        (read-overflow db (get-u32 b (+ p local)) out local))))

;;; ------------------------------------------------------------------
;;; Cells on a raw page

(defun cell-ptr (b off type i)
  (get-u16 b (+ off (page-hdr-size type) (* 2 i))))

(defun page-ncells (b off) (get-u16 b (+ off 3)))

(defun raw-cell-rowid (b off type i)
  (let ((p (cell-ptr b off type i)))
    (if (= type +leaf-table+)
        (get-varint-signed b (+ p (nth-value 1 (get-varint b p))))
        (get-varint-signed b (+ p 4)))))

(defun raw-index-entry (db b off type i)
  (let* ((p (cell-ptr b off type i))
         (q (if (= type +interior-index+) (+ p 4) p)))
    (multiple-value-bind (psize n1) (get-varint b q)
      (decode-record (read-payload db b (+ q n1) psize (local-size db psize nil))))))

(defun lower-bound (n pred)
  "Smallest I in [0,N) with (PRED I) true, assuming PRED is monotone; else N."
  (let ((lo 0) (hi n))
    (loop while (< lo hi)
          do (let ((mid (floor (+ lo hi) 2)))
               (if (funcall pred mid) (setf hi mid) (setf lo (1+ mid)))))
    lo))

(defun cell-length (db b p type)
  "Bytes occupied by the cell at P, child pointer included."
  (ecase type
    (#.+leaf-table+
     (multiple-value-bind (psize n1) (get-varint b p)
       (let* ((n2 (nth-value 1 (get-varint b (+ p n1))))
              (local (local-size db psize t)))
         (+ n1 n2 local (if (< local psize) 4 0)))))
    (#.+interior-table+ (+ 4 (nth-value 1 (get-varint b (+ p 4)))))
    ((#.+leaf-index+ #.+interior-index+)
     (let ((q (if (= type +interior-index+) (+ p 4) p)))
       (multiple-value-bind (psize n1) (get-varint b q)
         (let ((local (local-size db psize nil)))
           (+ (- q p) n1 local (if (< local psize) 4 0))))))))

(defun map-table (db root fn &key start)
  "Call (FN rowid payload) for every row with rowid >= START, in order."
  (labels ((visit (pgno depth)
             (when (> depth 64) (corrupt "b-tree too deep"))
             (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off)))
               (cond ((= type +leaf-table+)
                      (dotimes (i n)
                        (let ((p (cell-ptr b off type i)))
                          (multiple-value-bind (psize n1) (get-varint b p)
                            (multiple-value-bind (rowid n2) (get-varint-signed b (+ p n1))
                              (when (or (null start) (>= rowid start))
                                (funcall fn rowid
                                         (read-payload db b (+ p n1 n2) psize
                                                       (local-size db psize t)))))))))
                     ((= type +interior-table+)
                      (let ((right (get-u32 b (+ off 8)))
                            (entries (loop for i below n
                                           for p = (cell-ptr b off type i)
                                           collect (cons (get-u32 b p)
                                                         (get-varint-signed b (+ p 4))))))
                        (loop for (child . key) in entries
                              do (when (or (null start) (>= key start))
                                   (visit child (1+ depth))))
                        (visit right (1+ depth))))
                     (t (corrupt "index page ~d inside a table b-tree" pgno))))))
    (visit root 0)))

(defun map-table-reverse (db root fn)
  "Call (FN rowid payload) for every row, in descending rowid order."
  (labels ((visit (pgno depth)
             (when (> depth 64) (corrupt "b-tree too deep"))
             (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off)))
               (cond ((= type +leaf-table+)
                      (loop for i from (1- n) downto 0
                            do (let ((p (cell-ptr b off type i)))
                                 (multiple-value-bind (psize n1) (get-varint b p)
                                   (multiple-value-bind (rowid n2) (get-varint-signed b (+ p n1))
                                     (funcall fn rowid (read-payload db b (+ p n1 n2) psize
                                                                     (local-size db psize t))))))))
                     ((= type +interior-table+)
                      (let ((children (loop for i below n collect (get-u32 b (cell-ptr b off type i)))))
                        (visit (get-u32 b (+ off 8)) (1+ depth))
                        (dolist (c (reverse children)) (visit c (1+ depth)))))
                     (t (corrupt "index page ~d inside a table b-tree" pgno))))))
    (visit root 0)))

(defun map-index-reverse (db root fn)
  "Call (FN values) for every index entry, in descending order."
  (labels ((visit (pgno depth)
             (when (> depth 64) (corrupt "b-tree too deep"))
             (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off)))
               (cond ((= type +leaf-index+)
                      (loop for i from (1- n) downto 0
                            do (funcall fn (raw-index-entry db b off type i))))
                     ((= type +interior-index+)
                      (visit (get-u32 b (+ off 8)) (1+ depth))
                      (loop for i from (1- n) downto 0
                            do (funcall fn (raw-index-entry db b off type i))
                               (visit (get-u32 b (cell-ptr b off type i)) (1+ depth))))
                     (t (corrupt "table page ~d inside an index b-tree" pgno))))))
    (visit root 0)))

(defun table-lookup (db root rowid)
  "Payload of ROWID, or NIL."
  (let ((pgno root))
    (loop repeat 64
          do (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off)))
               (cond ((= type +leaf-table+)
                      (dotimes (i n)
                        (let ((p (cell-ptr b off type i)))
                          (multiple-value-bind (psize n1) (get-varint b p)
                            (multiple-value-bind (r n2) (get-varint-signed b (+ p n1))
                              (when (= r rowid)
                                (return-from table-lookup
                                  (read-payload db b (+ p n1 n2) psize
                                                (local-size db psize t))))))))
                      (return-from table-lookup nil))
                     ((= type +interior-table+)
                      ;; binary search for the first key >= rowid
                      (let ((lo 0) (hi n))
                        (loop while (< lo hi)
                              do (let ((mid (floor (+ lo hi) 2)))
                                   (if (< (get-varint-signed b (+ (cell-ptr b off type mid) 4)) rowid)
                                       (setf lo (1+ mid))
                                       (setf hi mid))))
                        (setf pgno (if (< lo n)
                                       (get-u32 b (cell-ptr b off type lo))
                                       (get-u32 b (+ off 8))))))
                     (t (corrupt "index page in table b-tree")))))
    (corrupt "b-tree too deep")))

(defun table-max-rowid (db root)
  (let ((pgno root))
    (loop repeat 64
          do (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off)))
               (if (= type +leaf-table+)
                   (return-from table-max-rowid
                     (when (plusp n)
                       (let ((p (cell-ptr b off type (1- n))))
                         (get-varint-signed b (+ p (nth-value 1 (get-varint b p)))))))
                   (setf pgno (get-u32 b (+ off 8))))))
    (corrupt "b-tree too deep")))

(defun map-index (db root fn &key probe cmp)
  "Call (FN values) for every index entry in order.  With PROBE, start at
the first entry E for which (CMP E PROBE) >= 0."
  (labels ((start-pos (b off type n)
             (if probe
                 (lower-bound n (lambda (i) (>= (funcall cmp (raw-index-entry db b off type i) probe) 0)))
                 0))
           (visit (pgno depth)
             (when (> depth 64) (corrupt "b-tree too deep"))
             (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off))
                    (start (start-pos b off type n)))
               (cond ((= type +leaf-index+)
                      (loop for i from start below n
                            do (let ((vals (raw-index-entry db b off type i)))
                                 (setf probe nil)
                                 (funcall fn vals))))
                     ((= type +interior-index+)
                      (let ((right (get-u32 b (+ off 8))))
                        (loop for i from start below n
                              do (let ((child (get-u32 b (cell-ptr b off type i))))
                                   (visit child (1+ depth))
                                   (setf probe nil)
                                   (funcall fn (raw-index-entry db b off type i))))
                        (visit right (1+ depth))))
                     (t (corrupt "table page ~d inside an index b-tree" pgno))))))
    (visit root 0)))

(defun btree-count (db root)
  "Number of entries in a b-tree, from cell counts alone."
  (labels ((visit (pgno depth)
             (when (> depth 64) (corrupt "b-tree too deep"))
             (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off)))
               (case type
                 (#.+leaf-table+ n)
                 (#.+leaf-index+ n)
                 (t (+ (if (= type +interior-index+) n 0)
                       (loop for i below n
                             sum (visit (get-u32 b (cell-ptr b off type i)) (1+ depth)))
                       (visit (get-u32 b (+ off 8)) (1+ depth))))))))
    (visit root 0)))

;;; *INDEX-CMP* compares two decoded index entries (records whose last
;;; column is the rowid) for the index being modified.

(defvar *index-cmp* nil "Comparator (a b) -> -1/0/1 for the index being modified.")
