;;;; rtree.lisp — the R*Tree module: CREATE VIRTUAL TABLE t USING rtree(...)
;;;; and rtree_i32(...), in SQLite 3.40's on-disk form, so each side can
;;;; read and modify the other's trees.
;;;;
;;;; An r-tree table stores nothing itself (its sqlite_schema row has root
;;;; page 0).  Its data lives in three ordinary "shadow" tables:
;;;;   <t>_node(nodeno INTEGER PRIMARY KEY, data)   one blob per tree node
;;;;   <t>_rowid(rowid INTEGER PRIMARY KEY, nodeno, a0, a1, ...)
;;;;                                  entry -> its leaf, plus +auxiliary columns
;;;;   <t>_parent(nodeno INTEGER PRIMARY KEY, parentnode)   node -> its parent
;;;; A node blob is a fixed size: 2 bytes tree depth (root, node 1, only),
;;;; 2 bytes cell count, then cells of an 8-byte id (entry rowid, or child
;;;; node) and 2*D coordinates, big-endian float32 (rtree) or int32
;;;; (rtree_i32).  Float coordinates are rounded outward, as SQLite does:
;;;; lower bounds down and upper bounds up.
;;;;
;;;; Insertion descends by least enlargement and splits R*-style (best axis
;;;; by margin, then least overlap); deletion removes underfull nodes and
;;;; reinserts their contents, and shrinks the root when it has one child.
;;;; Queries walk the tree, pruning subtrees whose bounding boxes cannot
;;;; satisfy the WHERE clause's constraints on coordinate columns.

(in-package #:sqlite-pure)

(defstruct rtree
  module                 ; "rtree" or "rtree_i32"
  ndim2                  ; number of coordinate columns (2 per dimension)
  int-p                  ; rtree_i32
  (naux 0)
  names                  ; all column names
  (node-size nil))       ; octets per node blob (read from node 1)

(defconstant +rtree-max-cells+ 51)
(defconstant +rtree-max-depth+ 40)
(defparameter *rnd-towards* (- 1d0 (/ 1d0 8388608d0)))
(defparameter *rnd-away* (+ 1d0 (/ 1d0 8388608d0)))

;;; ------------------------------------------------------------------
;;; Declaring an r-tree

(defun rtree-arg-name (arg)
  "The column name an rtree argument declares: its first token."
  (let ((tk (aref (tokenize arg) 0)))
    (if (eq (tok-kind tk) :eof) "" (princ-to-string (tok-value tk)))))

(defun rtree-spec (module args)
  "Validate an r-tree's arguments as rtreeInit does; return an RTREE."
  (let ((int-p (name= module "rtree_i32")) (ndim2 0) (naux 0) (names '()) (bad nil))
    (when (< (length args) 3) (sql-error "Too few columns for an rtree table"))
    (when (> (length args) (+ 100 3)) (sql-error "Too many columns for an rtree table"))
    (push (rtree-arg-name (first args)) names)
    (dolist (a (rest args))
      (cond ((and (plusp (length a)) (char= (char a 0) #\+))
             (incf naux)
             (push (rtree-arg-name (subseq a 1)) names))
            ((plusp naux) (setf bad t) (return))
            (t (incf ndim2) (push (rtree-arg-name a) names))))
    (when bad (sql-error "Auxiliary rtree columns must be last"))
    (cond ((< (floor ndim2 2) 1) (sql-error "Too few columns for an rtree table"))
          ((> ndim2 10) (sql-error "Too many columns for an rtree table"))
          ((oddp ndim2) (sql-error "Wrong number of columns for an rtree table")))
    (make-rtree :module (string-downcase-ascii module) :ndim2 ndim2 :int-p int-p :naux naux
                :names (nreverse names))))

(defun rtree-declaration (rt)
  "The table SQLite declares for the r-tree: CREATE TABLE x(id INT, c REAL, ..., aux)."
  (format nil "CREATE TABLE x(~{~a~^,~})"
          (loop for n in (rtree-names rt)
                for i from 0
                collect (format nil "~a~a" (quote-ident n)
                                (cond ((zerop i) " INT")
                                      ((<= i (rtree-ndim2 rt)) (if (rtree-int-p rt) " INT" " REAL"))
                                      (t ""))))))

(defun virtual-table-from-ast (name ast sql &optional (db *db*))
  "The TABLE for a CREATE VIRTUAL TABLE row.  An unknown module still loads
(as SQLite does); using the table then fails."
  (destructuring-bind (&key module args &allow-other-keys) (cdr ast)
    (flet ((unknown () (make-table :name name :root 0 :sql sql :columns #() :vtab (list :unknown module))))
      (cond ((fts3-module-p module)
             (return-from virtual-table-from-ast
               (handler-case (fts3-table-from-ast name ast sql db) (sqlite-error () (unknown)))))
            ((name= module "fts4aux")
             (return-from virtual-table-from-ast
               (handler-case (fts4aux-table-from-ast name ast sql) (sqlite-error () (unknown)))))
            ((name= module "fts3tokenize")
             (return-from virtual-table-from-ast
               (handler-case (fts3tok-table-from-ast name ast sql) (sqlite-error () (unknown)))))))
    (when (name= module "fts5vocab")
      (return-from virtual-table-from-ast
        (handler-case (fts5vocab-table-from-ast name ast sql)
          (sqlite-error () (make-table :name name :root 0 :sql sql :columns #()
                                       :vtab (list :unknown module))))))
    (when (name= module "fts5")
      (return-from virtual-table-from-ast
        (handler-case (fts5-table-from-ast name ast sql)
          (sqlite-error () (make-table :name name :root 0 :sql sql :columns #()
                                       :vtab (list :unknown module))))))
    (let ((rt (and (member module '("rtree" "rtree_i32") :test #'name=)
                   (ignore-errors (rtree-spec module args)))))
      (if rt
          (let ((tb (table-from-ast name (car (first (parse-sql (rtree-declaration rt)))) 0 sql)))
            (setf (table-vtab tb) rt)
            tb)
          (make-table :name name :root 0 :sql sql :columns #()
                      :vtab (list :unknown module))))))

(defun vtab-rtree (table)
  "TABLE's r-tree, or an error for a module this library does not have."
  (let ((v (table-vtab table)))
    (if (rtree-p v) v (sql-error "no such module: ~a" (second v)))))

(defun shadow-name (table suffix) (format nil "~a_~a" (table-name table) suffix))

(defun shadow-table (table suffix)
  (or (find-table-in (table-owner table) (shadow-name table suffix))
      (corrupt "database disk image is malformed")))

(defun rtree-shadow-p (db name)
  "Is NAME one of a virtual table's shadow tables in DB?"
  (let ((p (position #\_ name :from-end t)))
    (and p
         (let ((tb (find-table-in db (subseq name 0 p))))
           (and tb (table-vtab tb)
                (member (subseq name (1+ p)) (vtab-shadow-suffixes tb) :test #'name=))))))

(defun exec-create-virtual (st)
  (destructuring-bind (&key name schema if-not-exists module args sql &allow-other-keys) (cdr st)
    (let ((*db* (ddl-target schema nil)))
      (when (find-table-in *db* name)
        (if if-not-exists
            (return-from exec-create-virtual nil)
            (sql-error "table ~a already exists" name)))
      (check-new-name name :table)
      (when (name= module "fts5")
        (return-from exec-create-virtual (exec-create-fts5 st)))
      (when (fts3-module-p module)
        (return-from exec-create-virtual (exec-create-fts3 st)))
      (when (member module '("fts4aux" "fts3tokenize") :test #'name=)
        (if (name= module "fts4aux") (fts4aux-spec args) (fts3tok-spec args))
        (ensure-write-txn *db*)
        (add-schema-row "table" name name 0 (concatenate 'string "CREATE VIRTUAL TABLE " sql))
        (bump-schema-cookie)
        (return-from exec-create-virtual nil))
      (when (name= module "fts5vocab")
        (return-from exec-create-virtual (exec-create-fts5vocab st)))
      (unless (member module '("rtree" "rtree_i32") :test #'name=)
        (sql-error "no such module: ~a" module))
      (let* ((rt (rtree-spec module args))
             (q (substitute-string "\"" "\"\"" name)))
        (ensure-write-txn *db*)
        (add-schema-row "table" name name 0 (concatenate 'string "CREATE VIRTUAL TABLE " sql))
        (dolist (ddl (list (format nil "CREATE TABLE \"~a_rowid\"(rowid INTEGER PRIMARY KEY,nodeno~{,a~d~})"
                                   q (loop for i below (rtree-naux rt) collect i))
                           (format nil "CREATE TABLE \"~a_node\"(nodeno INTEGER PRIMARY KEY,data)" q)
                           (format nil "CREATE TABLE \"~a_parent\"(nodeno INTEGER PRIMARY KEY,parentnode)" q)))
          (create-table-from-ast (car (first (parse-sql ddl))) ddl))
        (let* ((bpc (+ 8 (* 4 (rtree-ndim2 rt))))
               (size (min (- (db-page-size *db*) 64) (+ 4 (* bpc +rtree-max-cells+))))
               (tb (find-table-in *db* name)))
          (shadow-put (shadow-table tb "node") 1 (list (make-octets size))))
        (bump-schema-cookie)
        nil))))

;;; ------------------------------------------------------------------
;;; Shadow-table rows (each has an INTEGER PRIMARY KEY first column)

(defun shadow-get (table rowid)
  "The values after the key column, or NIL."
  (let ((payload (table-lookup (table-owner table) (table-root table) rowid)))
    (when payload (rest (decode-record payload)))))

(defun shadow-put (table rowid values)
  (table-insert (table-owner table) (table-root table) rowid (encode-record (cons :null values))))

(defun shadow-del (table rowid)
  (table-delete (table-owner table) (table-root table) rowid))

;;; ------------------------------------------------------------------
;;; Coordinates

(defun rt-double (v)
  (let ((x (if (eq v :null) :null (value-to-real v))))
    (if (floatp x) x 0d0)))

(defun rt-int64 (v)
  (let ((x (if (eq v :null) :null (value-to-integer v))))
    (if (integerp x) x 0)))

(defun rt-int32 (v)
  (let ((x (ldb (byte 32 0) (rt-int64 v))))
    (if (>= x #x80000000) (- x #x100000000) x)))

(defun floor-log2 (a)
  "floor(log2 A) for a positive rational A."
  (let ((e (- (integer-length (numerator a)) (integer-length (denominator a)))))
    (if (>= a (expt 2 e)) e (1- e))))

(defparameter *f32-overflow* (* (- 2 (expt 2 -24)) (expt 2 127)))

(defun round-f32 (d)
  "The double D rounded to the nearest float32 (ties to even), as a double."
  (cond ((or (float-nan-p d) (float-infinity-p d) (zerop d)) d)
        (t (let* ((r (rational d)) (a (abs r)))
             (if (>= a *f32-overflow*)
                 (if (plusp r) (double-positive-infinity) (double-negative-infinity))
                 (let* ((ulp (expt 2 (- (max -126 (floor-log2 a)) 23)))
                        (m (* (round a ulp) ulp)))
                   (coerce (if (minusp r) (- m) m) 'double-float)))))))

(defun rtree-value-down (v)
  (let* ((d (rt-double v)) (f (round-f32 d)))
    (if (> f d) (round-f32 (* d (if (< d 0) *rnd-away* *rnd-towards*))) f)))

(defun rtree-value-up (v)
  (let* ((d (rt-double v)) (f (round-f32 d)))
    (if (< f d) (round-f32 (* d (if (< d 0) *rnd-towards* *rnd-away*))) f)))

(defun f32-bits (v)
  (cond ((float-nan-p v) #x7fc00000)
        ((float-infinity-p v) (if (plusp v) #x7f800000 #xff800000))
        ((zerop v) (if (minusp (float-sign v)) #x80000000 0))
        (t (let* ((sign (if (minusp v) #x80000000 0))
                  (a (abs (rational v))))
             (if (< a (expt 2 -126))
                 (logior sign (* a (expt 2 149)))
                 (let ((e (floor-log2 a)))
                   (logior sign (ash (+ e 127) 23) (- (* a (expt 2 (- 23 e))) (expt 2 23)))))))))

(defun f32-from-bits (u)
  (let ((neg (logbitp 31 u)) (ex (ldb (byte 8 23) u)) (m (ldb (byte 23 0) u)))
    (cond ((= ex 255)
           (if (zerop m)
               (if neg (double-negative-infinity) (double-positive-infinity))
               (let ((inf (double-positive-infinity))) (- inf inf))))
          (t (let ((mag (if (zerop ex) (* m (expt 2 -149)) (* (+ m (expt 2 23)) (expt 2 (- ex 150))))))
               (cond ((and (zerop mag) neg) -0d0)
                     (t (coerce (if neg (- mag) mag) 'double-float))))))))

;;; ------------------------------------------------------------------
;;; Nodes

(defstruct (rnode (:conc-name rn-))
  no                     ; node number
  cells                  ; list of (id . coords-vector)
  parent                 ; parent node number, or NIL if not yet known
  dirty)

(defvar *rt* nil "The r-tree being operated on: (table rtree node-table rowid-table parent-table).")
(defvar *rt-nodes* nil "Nodes loaded by this operation: nodeno -> RNODE.")
(defvar *rt-next-node* nil)

(defun rt-table () (first *rt*))
(defun rt-spec () (second *rt*))
(defun rt-node-table () (third *rt*))
(defun rt-rowid-table () (fourth *rt*))
(defun rt-parent-table () (fifth *rt*))

(defmacro with-rtree ((table) &body body)
  `(let* ((*rt* (let ((tb ,table))
                  (list tb (vtab-rtree tb) (shadow-table tb "node")
                        (shadow-table tb "rowid") (shadow-table tb "parent"))))
          (*rt-nodes* (make-hash-table))
          (*rt-next-node* nil))
     (rt-node-size)
     ,@body))

(defun rtree-bytes-per-cell () (+ 8 (* 4 (rtree-ndim2 (rt-spec)))))

(defun rt-node-size ()
  (let ((rt (rt-spec)))
    (or (rtree-node-size rt)
        (let ((blob (first (shadow-get (rt-node-table) 1))))
          (unless (and (blobp blob) (>= (length blob) 4))
            (corrupt "database disk image is malformed"))
          (setf (rtree-node-size rt) (length blob))))))

(defun rtree-max-cells () (floor (- (rt-node-size) 4) (rtree-bytes-per-cell)))
(defun rtree-min-cells () (floor (rtree-max-cells) 3))

(defun decode-rnode (no blob)
  (let* ((rt (rt-spec)) (nd (rtree-ndim2 rt)) (bpc (rtree-bytes-per-cell))
         (n (get-u16 blob 2)))
    (unless (and (blobp blob) (= (length blob) (rt-node-size)) (<= n (rtree-max-cells)))
      (corrupt "database disk image is malformed"))
    (make-rnode :no no
                :cells (loop for i below n
                             for off = (+ 4 (* i bpc))
                             collect (cons (let ((u (logior (ash (get-u32 blob off) 32) (get-u32 blob (+ off 4)))))
                                             (if (logbitp 63 u) (- u (expt 2 64)) u))
                                           (let ((c (make-array nd)))
                                             (dotimes (k nd c)
                                               (let ((u (get-u32 blob (+ off 8 (* 4 k)))))
                                                 (setf (svref c k)
                                                       (if (rtree-int-p rt)
                                                           (if (logbitp 31 u) (- u #x100000000) u)
                                                           (f32-from-bits u)))))))))))

(defun encode-rnode (node depth)
  (let* ((rt (rt-spec)) (bpc (rtree-bytes-per-cell))
         (blob (make-octets (rt-node-size))))
    (put-u16 blob 0 (if (= (rn-no node) 1) depth 0))
    (put-u16 blob 2 (length (rn-cells node)))
    (loop for (id . c) in (rn-cells node)
          for off from 4 by bpc
          do (let ((u (ldb (byte 64 0) id)))
               (put-u32 blob off (ldb (byte 32 32) u))
               (put-u32 blob (+ off 4) (ldb (byte 32 0) u)))
             (dotimes (k (length c))
               (put-u32 blob (+ off 8 (* 4 k))
                        (if (rtree-int-p rt) (ldb (byte 32 0) (svref c k)) (f32-bits (svref c k))))))
    blob))

(defun rtree-depth ()
  (let ((blob (first (shadow-get (rt-node-table) 1))))
    (let ((d (get-u16 blob 0)))
      (when (> d +rtree-max-depth+) (corrupt "database disk image is malformed"))
      d)))

(defvar *rt-depth* nil)

(defun load-rnode (no &optional parent)
  (or (let ((n (gethash no *rt-nodes*)))
        (when (and n parent (null (rn-parent n))) (setf (rn-parent n) parent))
        n)
      (let ((blob (first (shadow-get (rt-node-table) no))))
        (unless blob (corrupt "database disk image is malformed"))
        (let ((n (decode-rnode no blob)))
          (setf (rn-parent n) parent)
          (setf (gethash no *rt-nodes*) n)))))

(defun rnode-parent (node)
  (or (rn-parent node)
      (unless (= (rn-no node) 1)
        (setf (rn-parent node)
              (or (first (shadow-get (rt-parent-table) (rn-no node)))
                  (corrupt "database disk image is malformed"))))))

(defun new-rnode ()
  (let ((no (or *rt-next-node*
                (1+ (or (table-max-rowid (table-owner (rt-node-table)) (table-root (rt-node-table))) 0)))))
    (setf *rt-next-node* (1+ no))
    (setf (gethash no *rt-nodes*) (make-rnode :no no :dirty t))))

(defun flush-rnodes ()
  (maphash (lambda (no n)
             (when (rn-dirty n)
               (shadow-put (rt-node-table) no (list (encode-rnode n *rt-depth*)))
               (setf (rn-dirty n) nil)))
           *rt-nodes*))

(defun set-mapping (cell node height)
  "Record where CELL now lives: an entry's leaf, or a child node's parent."
  (if (zerop height)
      (let ((old (shadow-get (rt-rowid-table) (car cell))))
        (shadow-put (rt-rowid-table) (car cell)
                    (cons (rn-no node)
                          (if old (rest old) (make-list (rtree-naux (rt-spec)) :initial-element :null)))))
      (progn
        (shadow-put (rt-parent-table) (car cell) (list (rn-no node)))
        (let ((child (gethash (car cell) *rt-nodes*)))
          (when child (setf (rn-parent child) (rn-no node)))))))

;;; ------------------------------------------------------------------
;;; Geometry (on coordinate vectors: min0 max0 min1 max1 ...)

(defun box-union (a b)
  (let ((c (copy-seq a)))
    (loop for k from 0 below (length a) by 2
          do (setf (svref c k) (min (svref a k) (svref b k))
                   (svref c (1+ k)) (max (svref a (1+ k)) (svref b (1+ k)))))
    c))

(defun cells-box (cells)
  (reduce #'box-union (mapcar #'cdr cells)))

(defun box-area (a)
  (loop with p = 1d0
        for k from 0 below (length a) by 2
        do (setf p (* p (float (- (svref a (1+ k)) (svref a k)) 1d0)))
        finally (return p)))

(defun box-margin (a)
  (loop for k from 0 below (length a) by 2
        sum (float (- (svref a (1+ k)) (svref a k)) 1d0)))

(defun box-overlap (a b)
  (loop with p = 1d0
        for k from 0 below (length a) by 2
        do (let ((lo (max (svref a k) (svref b k))) (hi (min (svref a (1+ k)) (svref b (1+ k)))))
             (if (< hi lo) (return 0d0) (setf p (* p (float (- hi lo) 1d0)))))
        finally (return p)))

(defun box-contains-p (outer inner)
  (loop for k from 0 below (length outer) by 2
        always (and (<= (svref outer k) (svref inner k))
                    (>= (svref outer (1+ k)) (svref inner (1+ k))))))

;;; ------------------------------------------------------------------
;;; Insertion

(defun choose-node (box height)
  "Descend from the root to the node at HEIGHT that least needs enlarging."
  (let ((node (load-rnode 1)))
    (loop for h downfrom *rt-depth* above height
          do (let ((best nil) (best-growth 0d0) (best-area 0d0))
               (dolist (c (rn-cells node))
                 (let* ((area (box-area (cdr c)))
                        (growth (- (box-area (box-union (cdr c) box)) area)))
                   (when (or (null best) (< growth best-growth)
                             (and (= growth best-growth) (< area best-area)))
                     (setf best c best-growth growth best-area area))))
               (unless best (corrupt "database disk image is malformed"))
               (setf node (load-rnode (car best) (rn-no node)))))
    node))

(defun fix-boxes (node)
  "Make every ancestor's cell for NODE the exact bounding box of its cells."
  (loop until (= (rn-no node) 1)
        do (let* ((parent (load-rnode (rnode-parent node)))
                  (cell (or (assoc (rn-no node) (rn-cells parent))
                            (corrupt "database disk image is malformed")))
                  (box (and (rn-cells node) (cells-box (rn-cells node)))))
             (when (or (null box) (equalp box (cdr cell))) (return))
             (setf (cdr cell) box (rn-dirty parent) t node parent))))

(defun insert-cell (node cell height)
  "Add CELL to NODE (at HEIGHT), splitting as needed."
  (setf (rn-cells node) (append (rn-cells node) (list cell))
        (rn-dirty node) t)
  (if (<= (length (rn-cells node)) (rtree-max-cells))
      (progn (set-mapping cell node height)
             (fix-boxes node))
      (rtree-split-node node height)))

(defun split-cells (cells)
  "R*-tree split: the axis with the least total margin, then the division
with the least overlap (then least area).  Returns (values left right)."
  (let* ((n (length cells))
         (m (max 1 (min (rtree-min-cells) (floor n 2))))
         (v (coerce cells 'vector))
         (nd (length (cdr (first cells))))
         (best-axis nil) (best-margin nil))
    (flet ((sorted (k)
             (sort (copy-seq v) (lambda (a b)
                                  (let ((a0 (svref (cdr a) (* 2 k))) (b0 (svref (cdr b) (* 2 k))))
                                    (or (< a0 b0)
                                        (and (= a0 b0) (< (svref (cdr a) (1+ (* 2 k)))
                                                          (svref (cdr b) (1+ (* 2 k)))))))))))
      (dotimes (k (floor nd 2))
        (let ((s (sorted k)) (margin 0d0))
          (loop for i from m to (- n m)
                do (incf margin (+ (box-margin (cells-box (coerce (subseq s 0 i) 'list)))
                                   (box-margin (cells-box (coerce (subseq s i) 'list))))))
          (when (or (null best-margin) (< margin best-margin))
            (setf best-margin margin best-axis s))))
      (let ((best-i nil) (best-overlap 0d0) (best-area 0d0))
        (loop for i from m to (- n m)
              do (let* ((l (cells-box (coerce (subseq best-axis 0 i) 'list)))
                        (r (cells-box (coerce (subseq best-axis i) 'list)))
                        (overlap (box-overlap l r))
                        (area (+ (box-area l) (box-area r))))
                   (when (or (null best-i) (< overlap best-overlap)
                             (and (= overlap best-overlap) (< area best-area)))
                     (setf best-i i best-overlap overlap best-area area))))
        (values (coerce (subseq best-axis 0 best-i) 'list)
                (coerce (subseq best-axis best-i) 'list))))))

(defun rtree-split-node (node height)
  (multiple-value-bind (left right) (split-cells (rn-cells node))
    (if (= (rn-no node) 1)
        ;; the root stays node 1: its contents move down into two new nodes
        (let ((l (new-rnode)) (r (new-rnode)))
          (setf (rn-cells l) left (rn-cells r) right
                (rn-parent l) 1 (rn-parent r) 1
                (rn-cells node) (list (cons (rn-no l) (cells-box left))
                                      (cons (rn-no r) (cells-box right)))
                (rn-dirty node) t)
          (incf *rt-depth*)
          (dolist (c left) (set-mapping c l height))
          (dolist (c right) (set-mapping c r height))
          (set-mapping (first (rn-cells node)) node (1+ height))
          (set-mapping (second (rn-cells node)) node (1+ height)))
        (let ((r (new-rnode))
              (parent (load-rnode (rnode-parent node))))
          (setf (rn-cells node) left (rn-cells r) right)
          (dolist (c left) (set-mapping c node height))
          (dolist (c right) (set-mapping c r height))
          (fix-boxes node)
          (insert-cell parent (cons (rn-no r) (cells-box right)) (1+ height))))))

(defun insert-at-height (cell height)
  (insert-cell (choose-node (cdr cell) height) cell height))

;;; ------------------------------------------------------------------
;;; Deletion

(defvar *rt-reinsert* nil "(cells . height) of nodes removed as underfull.")

(defun delete-cell (node cell height)
  (setf (rn-cells node) (remove cell (rn-cells node)) (rn-dirty node) t)
  (unless (= (rn-no node) 1)
    (if (< (length (rn-cells node)) (rtree-min-cells))
        (remove-rnode node height)
        (fix-boxes node))))

(defun remove-rnode (node height)
  "Unlink NODE from the tree; its cells are queued for reinsertion."
  (let* ((parent (load-rnode (rnode-parent node)))
         (cell (or (assoc (rn-no node) (rn-cells parent))
                   (corrupt "database disk image is malformed"))))
    (delete-cell parent cell (1+ height))
    (shadow-del (rt-node-table) (rn-no node))
    (shadow-del (rt-parent-table) (rn-no node))
    (remhash (rn-no node) *rt-nodes*)
    (push (cons (rn-cells node) height) *rt-reinsert*)))

(defun rtree-delete-id (id)
  "Remove entry ID; true if it existed."
  (let ((leafno (first (shadow-get (rt-rowid-table) id))))
    (when (integerp leafno)
      (let* ((*rt-reinsert* '())
             (leaf (load-rnode leafno))
             (cell (or (assoc id (rn-cells leaf)) (corrupt "database disk image is malformed"))))
        (shadow-del (rt-rowid-table) id)
        (delete-cell leaf cell 0)
        ;; a root with one child: bring the child's contents up
        (let ((root (load-rnode 1)))
          (when (and (plusp *rt-depth*) (= (length (rn-cells root)) 1))
            (let ((child (load-rnode (car (first (rn-cells root))) 1)))
              (remove-rnode child (1- *rt-depth*))
              (decf *rt-depth*)
              (setf (rn-dirty root) t))))
        (loop while *rt-reinsert*
              do (destructuring-bind (cells . height) (pop *rt-reinsert*)
                   (dolist (c cells) (insert-at-height c height))))
        t))))

;;; ------------------------------------------------------------------
;;; Writing rows

(defun rtree-row-cell (row)
  "The (id . coords) of ROW, or signals the coordinate constraint."
  (let* ((rt (rt-spec)) (nd (rtree-ndim2 rt)) (c (make-array nd)))
    (loop for k from 0 below nd by 2
          do (if (rtree-int-p rt)
                 (setf (svref c k) (rt-int32 (svref row (+ 1 k)))
                       (svref c (1+ k)) (rt-int32 (svref row (+ 2 k))))
                 (setf (svref c k) (rtree-value-down (svref row (+ 1 k)))
                       (svref c (1+ k)) (rtree-value-up (svref row (+ 2 k)))))
             (when (> (svref c k) (svref c (1+ k)))
               (return-from rtree-row-cell
                 (values nil (format nil "rtree constraint failed: ~a.(~a<=~a)"
                                     (table-name (rt-table))
                                     (nth (+ 1 k) (rtree-names rt)) (nth (+ 2 k) (rtree-names rt)))))))
    (cons (if (eq (svref row 0) :null) nil (rt-int64 (svref row 0))) c)))

(defun rtree-write (ctx old new)
  "The r-tree's xUpdate: delete OLD's entry (if OLD), insert NEW (if NEW).
Returns T, or :IGNORE if a constraint skipped the row."
  (let* ((rt (rt-spec)) (tb (rt-table)) (cell nil))
    (flet ((fail (msg)
             (let ((action (resolve-action ctx nil)))
               (when (eq action :ignore) (return-from rtree-write :ignore))
               (conflict-fail (if (eq action :replace) :abort action) "~a" msg))))
      (when new
        (multiple-value-bind (c msg) (rtree-row-cell new)
          (unless c (fail msg))
          (setf cell c))
        (let ((id (car cell)))
          (when (and id (or (null old) (/= id (rt-int64 (svref old 0))))
                     (shadow-get (rt-rowid-table) id))
            (if (eq (resolve-action ctx nil) :replace)
                (rtree-delete-id id)
                (fail (format nil "UNIQUE constraint failed: ~a.~a"
                              (table-name tb) (first (rtree-names rt))))))))
      (when old (rtree-delete-id (rt-int64 (svref old 0))))
      (when new
        (unless (car cell)
          (setf (car cell) (1+ (or (table-max-rowid (table-owner (rt-rowid-table))
                                                    (table-root (rt-rowid-table)))
                                   0))))
        (insert-at-height cell 0)
        (let ((aux (loop for i from (1+ (rtree-ndim2 rt)) below (length (rtree-names rt))
                         collect (svref new i))))
          (shadow-put (rt-rowid-table) (car cell)
                      (cons (first (shadow-get (rt-rowid-table) (car cell))) aux))))
      (flush-rnodes)
      (unless (= (rtree-depth) *rt-depth*)
        (let ((root (load-rnode 1))) (setf (rn-dirty root) t) (flush-rnodes)))
      (if cell (car cell) t))))

(defun vtab-read-only-check (table)
  (unless (or (fts5-p (table-vtab table)) (rtree-p (table-vtab table)) (fts3-p (table-vtab table)))
    (sql-error "table ~a may not be modified" (table-name table))))

(defun vtab-insert (ctx row)
  (vtab-read-only-check (wc-table ctx))
  (cond ((fts5-p (table-vtab (wc-table ctx))) (fts5-vtab-insert ctx row))
        ((fts3-p (table-vtab (wc-table ctx))) (fts3-vtab-insert ctx row))
        (t (rtree-vtab-insert ctx row))))

(defun vtab-update (ctx old new)
  (vtab-read-only-check (wc-table ctx))
  (cond ((fts5-p (table-vtab (wc-table ctx))) (fts5-vtab-update ctx old new))
        ((fts3-p (table-vtab (wc-table ctx))) (fts3-vtab-update ctx old new))
        (t (rtree-vtab-update ctx old new))))

(defun vtab-delete (table row)
  (vtab-read-only-check table)
  (cond ((fts5-p (table-vtab table)) (fts5-vtab-delete table row))
        ((fts3-p (table-vtab table)) (fts3-vtab-delete table row))
        (t (rtree-vtab-delete table row))))

(defun vtab-plan-access (fs li conjuncts scope)
  (let ((v (table-vtab (fsrc-table fs))))
    (cond ((fts5-p v) (fts5-plan-access fs li conjuncts scope))
          ((fts3-p v) (fts3-plan-access fs li conjuncts scope))
          ((fts4aux-p v) (fts4aux-plan-access fs li conjuncts scope))
          ((fts3tok-p v) (fts3tok-plan-access fs li conjuncts scope))
          ((fts5vocab-p v) (fts5vocab-plan-access fs li conjuncts scope))
          ((rtree-p v) (rtree-plan-access fs li conjuncts scope))
          (t (sql-error "no such module: ~a" (second v))))))

(defun rtree-vtab-insert (ctx row)
  (with-rtree ((wc-table ctx))
    (let* ((*rt-depth* (rtree-depth))
           (id (rtree-write ctx nil row)))
      (unless (eq id :ignore)
        (setf (db-last-insert-rowid (conn *db*)) id)
        (incf (wc-changes ctx))
        ;; RETURNING sees the values as given (and rowid -1), as in SQLite
        (setf (svref row (1- (length row))) -1)
        (collect-returning ctx row)
        t))))

(defun rtree-vtab-update (ctx old new)
  (with-rtree ((wc-table ctx))
    (let ((*rt-depth* (rtree-depth)))
      (unless (eq (rtree-write ctx old new) :ignore)
        (incf (wc-changes ctx))
        t))))

(defun rtree-vtab-delete (table row)
  (with-rtree (table)
    (let ((*rt-depth* (rtree-depth)))
      (rtree-delete-id (rt-int64 (svref row 0)))
      (flush-rnodes)
      (unless (= (rtree-depth) *rt-depth*)
        (setf (rn-dirty (load-rnode 1)) t)
        (flush-rnodes)))))

;;; ------------------------------------------------------------------
;;; Reading

(defun rtree-row (id coords aux)
  (let* ((n (+ 1 (length coords) (length aux)))
         (row (make-array (1+ n))))
    (setf (svref row 0) id (svref row n) id)
    (replace row coords :start1 1)
    (replace row aux :start1 (1+ (length coords)))
    row))

(defun rtree-aux (id)
  (let ((naux (rtree-naux (rt-spec))))
    (when (plusp naux)
      (let ((r (shadow-get (rt-rowid-table) id)))
        (if r (subseq (append (rest r) (make-list naux :initial-element :null)) 0 naux)
            (make-list naux :initial-element :null))))))

(defun box-may-match (box tests)
  "Could a coordinate inside BOX satisfy every (k op value) test?"
  (loop for (k op v) in tests
        for lo = (svref box (* 2 (floor k 2)))
        for hi = (svref box (1+ (* 2 (floor k 2))))
        always (case op
                 (:eq (and (<= lo v) (<= v hi)))
                 (:gt (> hi v)) (:ge (>= hi v))
                 (:lt (< lo v)) (:le (<= lo v))
                 (t t))))

(defun rtree-constraints (conjuncts li scope)
  "Conjuncts <column of source LI> <op> <expr of earlier sources>: list of
(column-index op expr)."
  (let ((out '()))
    (dolist (c conjuncts out)
      (when (and (eq (car c) :binary) (member (second c) '(:eq :lt :le :gt :ge)))
        (flet ((try (a b op)
                 (multiple-value-bind (depth si ci)
                     (case (car a)
                       (:col (resolve-column scope (second a) (third a)))
                       (:srccol (values 0 (second a) (third a))))
                   (when (and depth (= depth 0) (= si li))
                     (let ((refs (expr-refs b scope)))
                       (when (and (listp refs) (every (lambda (r) (< r li)) refs))
                         (push (list (if (eq ci :rowid) 0 ci) op b) out)))))))
          (try (third c) (fourth c) (second c))
          (try (fourth c) (third c)
               (ecase (second c) (:eq :eq) (:lt :gt) (:le :ge) (:gt :lt) (:ge :le))))))))

(defun rtree-plan-access (fs li conjuncts scope)
  "Iterate an r-tree's rows: by id when the WHERE clause names one, else by
walking the tree past subtrees the coordinate constraints rule out."
  (let* ((table (fsrc-table fs))
         (rt (vtab-rtree table))
         (cons* (rtree-constraints conjuncts li scope))
         (id-eq (find-if (lambda (c) (and (eql (first c) 0) (eq (second c) :eq))) cons*))
         (coord (remove-if-not (lambda (c) (<= 1 (first c) (rtree-ndim2 rt))) cons*))
         (id-fn (and id-eq (compile-expr (third id-eq) scope)))
         (_ (eqp-table-note
             (format nil "SCAN ~a VIRTUAL TABLE INDEX ~:[2:~{~a~}~;1:~]" (src-name (fsrc-src fs)) id-eq
                     (loop for (ci op) in (reverse coord)
                           collect (format nil "~a~d" (ecase op (:eq "A") (:le "B") (:lt "C") (:ge "D") (:gt "E"))
                                           (1- ci))))))
         (coord-fns (mapcar (lambda (c) (list (1- (first c)) (second c) (compile-expr (third c) scope)))
                            coord)))
    (declare (ignore _))
    (lambda (env fn)
      (with-rtree (table)
        (if id-fn
            (let* ((id (rowid-probe (funcall id-fn env)))
                   (leafno (and id (first (shadow-get (rt-rowid-table) id))))
                   (cell (and (integerp leafno) (assoc id (rn-cells (load-rnode leafno))))))
              (when cell
                (funcall fn (rtree-row id (coerce (cdr cell) 'list) (rtree-aux id)))))
            (let ((tests (loop for (k op f) in coord-fns
                               for v = (apply-comparison-affinity (funcall f env) :numeric)
                               when (or (integerp v) (floatp v)) collect (list k op v)))
                  (depth (rtree-depth)))
              (labels ((walk (node height)
                         (dolist (c (rn-cells node))
                           (if (zerop height)
                               (funcall fn (rtree-row (car c) (coerce (cdr c) 'list) (rtree-aux (car c))))
                               (when (box-may-match (cdr c) tests)
                                 (walk (load-rnode (car c) (rn-no node)) (1- height)))))))
                (walk (load-rnode 1) depth))))))))

;;; ------------------------------------------------------------------
;;; DROP and RENAME

(defun vtab-shadow-suffixes (table)
  (let ((v (table-vtab table)))
    (cond ((rtree-p v) '("rowid" "node" "parent"))
          ((fts5-p v) (fts5-shadow-suffixes v))
          ((fts3-p v) (progn (fts3-of table) (fts3-shadow-suffixes v)))
          (t '()))))

(defun vtab-drop (table)
  "Drop a virtual table's shadow tables (all roots at once: in an auto-vacuum
database dropping one moves another)."
  (progn
    (let ((shadows (loop for suffix in (vtab-shadow-suffixes table)
                         for sh = (find-table-in *db* (shadow-name table suffix))
                         when sh collect sh)))
      (drop-btrees (mapcar #'table-root shadows))
      (dolist (sh shadows)
        (delete-schema-rows (lambda (r) (and (stringp (fourth r)) (name= (fourth r) (table-name sh)))))))))

(defun vtab-rename (table new)
  "Rename the shadow tables along with the virtual table."
  (progn
    (dolist (suffix (vtab-shadow-suffixes table))
      (let* ((old (shadow-name table suffix))
             (nn (format nil "~a_~a" new suffix))
             (r (find-if (lambda (r) (and (equal (second r) "table") (name= (third r) old)))
                         (schema-rows (db-schema* *db*)))))
        (when r
          (let* ((sql (sixth r))
                 (tk (find-if (lambda (tk) (and (member (tok-kind tk) '(:id :string))
                                                (equal (princ-to-string (tok-value tk)) old)))
                              (tokenize sql))))
            (rewrite-schema-row r :name nn :tbl nn
                                  :sql (if tk
                                           (concatenate 'string (subseq sql 0 (tok-pos tk))
                                                        (format nil "\"~a\"" (substitute-string "\"" "\"\"" nn))
                                                        (subseq sql (tok-end tk)))
                                           sql))))
        ;; and the shadow table's automatic indexes
        (dolist (r (schema-rows (db-schema* *db*)))
          (when (and (equal (second r) "index") (stringp (fourth r)) (name= (fourth r) old))
            (let* ((nm (third r))
                   (pre (format nil "sqlite_autoindex_~a_" old)))
              (rewrite-schema-row r :tbl nn
                                    :name (if (and (> (length nm) (length pre)) (name= (subseq nm 0 (length pre)) pre))
                                              (format nil "sqlite_autoindex_~a_~a" nn (subseq nm (length pre)))
                                              nm)))))))))

;;; ------------------------------------------------------------------
;;; SQL functions: rtreenode(ndim, blob) and rtreecheck([schema,] table)

(defun rtreenode-text (ndim blob)
  "SQLite's debugging rendering of a node blob."
  (if (not (and (blobp blob) (>= (length blob) 4)))
      :null
      (let* ((n (get-u16 blob 2)) (bpc (+ 8 (* 8 ndim))))
        (format nil "~{~a~^ ~}"
                (loop for i below n
                      for off = (+ 4 (* i bpc))
                      while (<= (+ off bpc) (length blob))
                      collect (format nil "{~d~{ ~a~}}"
                                      (let ((u (logior (ash (get-u32 blob off) 32) (get-u32 blob (+ off 4)))))
                                        (if (logbitp 63 u) (- u (expt 2 64)) u))
                                      (loop for k below (* 2 ndim)
                                            collect (sql-printf "%g" (list (f32-from-bits (get-u32 blob (+ off 8 (* 4 k)))))))))))))

(defun rtreecheck (schema name)
  "The r-tree's structural invariants, as rtreecheck() reports them."
  (let* ((d (if schema (schema-db *db* schema) *db*))
         (tb (lookup-table d name t))
         (problems '()))
    (flet ((note (fmt &rest args) (push (apply #'format nil fmt args) problems)))
      (with-rtree (tb)
        (let ((depth (rtree-depth)) (entries 0) (nodes 0))
          (labels ((walk (no box height parent)
                     (let ((node (ignore-errors (load-rnode no))))
                       (if (null node)
                           (note "Node ~d missing from database" no)
                           (progn
                             (when parent
                               (incf nodes)
                               (let ((p (first (shadow-get (rt-parent-table) no))))
                                 (cond ((null p) (note "Mapping (~d -> ~d) missing from %_parent table" no parent))
                                       ((/= p parent) (note "Found (~d -> ~d) in %_parent table, expected (~d -> ~d)" no p no parent)))))
                             (loop for (id . c) in (rn-cells node)
                                   for i from 0
                                   do (loop for k from 0 below (length c) by 2
                                            do (cond ((> (svref c k) (svref c (1+ k)))
                                                      (note "Dimension ~d of cell ~d on node ~d is corrupt" (floor k 2) i no))
                                                     ((and box (or (< (svref c k) (svref box k))
                                                                   (> (svref c (1+ k)) (svref box (1+ k)))))
                                                      (note "Dimension ~d of cell ~d on node ~d is corrupt relative to parent"
                                                            (floor k 2) i no))))
                                      (if (zerop height)
                                          (let ((m (first (shadow-get (rt-rowid-table) id))))
                                            (incf entries)
                                            (cond ((null m) (note "Mapping (~d -> ~d) missing from %_rowid table" id no))
                                                  ((/= m no) (note "Found (~d -> ~d) in %_rowid table, expected (~d -> ~d)" id m id no))))
                                          (walk id c (1- height) no))))))))
            (walk 1 nil depth nil))
          (flet ((count-of (tbl) (let ((n 0)) (map-table (table-owner tbl) (table-root tbl) (lambda (r p) (declare (ignore r p)) (incf n))) n)))
            (let ((a (count-of (rt-rowid-table))))
              (unless (= a entries) (note "Wrong number of entries in %_rowid table - expected ~d, actual ~d" entries a)))
            (let ((a (count-of (rt-parent-table))))
              (unless (= a nodes) (note "Wrong number of entries in %_parent table - expected ~d, actual ~d" nodes a)))))))
    (if problems (format nil "~{~a~^~%~}" (nreverse problems)) "ok")))

(defsqlfun "rtreenode" (2 2) (args)
  (let ((nd (value-to-integer (first args))))
    (rtreenode-text (if (integerp nd) nd 0) (second args))))

(defsqlfun "rtreecheck" (1 2) (args)
  (if (cdr args)
      (rtreecheck (value-to-text (first args)) (value-to-text (second args)))
      (rtreecheck nil (value-to-text (first args)))))
