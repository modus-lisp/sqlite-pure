;;;; dbstat.lisp — the DBSTAT virtual table (dbstat.c): one row per page of
;;;; every b-tree (and overflow page), or with aggregate=1 one row per
;;;; b-tree, giving cells, payload and unused bytes.  Usable eponymously
;;;; (FROM dbstat, FROM dbstat('main', 1)) or by CREATE VIRTUAL TABLE x
;;;; USING dbstat([schema]).

(in-package #:sqlite-pure)

(defstruct (dbstat (:conc-name dbs-)) schema)

(defparameter +dbstat-declaration+
  "CREATE TABLE x(name TEXT, path TEXT, pageno INTEGER, pagetype TEXT, ncell INTEGER, payload INTEGER, unused INTEGER, mx_payload INTEGER, pgoffset INTEGER, pgsize INTEGER, schema TEXT, aggregate BOOLEAN)")

(defun dbstat-table (name sql schema)
  (let ((tb (table-from-ast name (car (first (parse-sql +dbstat-declaration+))) 0 sql)))
    (setf (column-hidden (aref (table-columns tb) 10)) t
          (column-hidden (aref (table-columns tb) 11)) t
          (table-vtab tb) (make-dbstat :schema schema))
    tb))

(defun dbstat-spec (args)
  (when (> (length args) 1) (sql-error "wrong number of arguments to dbstat"))
  (when args
    (let ((s (fts3-dequote (first args))))
      (unless (schema-db *db* s nil) (sql-error "no such database: ~a" (first args)))
      s)))

(defun dbstat-fsrc (alias args)
  "An FSRC for the eponymous dbstat table (ARGS: the table-valued arguments)."
  (when (> (length args) 2) (sql-error "too many arguments on dbstat() - max 2"))
  (let ((tb (dbstat-table "dbstat" nil nil)))
    (make-fsrc :src (make-table-src tb alias) :table tb :vtab-args args)))

;;; Page decoding (statDecodePage)

(defun dbstat-local-payload (usable flags total)
  (let ((min (- (floor (* (- usable 12) 32) 255) 23))
        (max (if (= flags #x0d) (- usable 35) (- (floor (* (- usable 12) 64) 255) 23))))
    (let ((local (+ min (rem (- total min) (- usable 4)))))   ; (C's %)
      (if (> local max) min local))))

(defstruct (dbstat-page (:conc-name dsp-))
  (flags 0) (ncell 0) (unused 0) (right 0) (mx 0) cells)   ; cell: (nlocal child overflow-pages nlastovfl)

(defun dbstat-decode (db pgno)
  (let* ((b (read-page db pgno))
         (psz (db-page-size db))
         (h (if (= pgno 1) 100 0))
         (p (make-dbstat-page :flags (aref b h))))
    (block decode
      (flet ((corrupt () (setf (dsp-flags p) 0 (dsp-cells p) nil (dsp-ncell p) 0) (return-from decode)))
        (let* ((flags (dsp-flags p))
               (leaf (member flags '(#x0a #x0d)))
               (nhdr (cond (leaf 8) ((member flags '(#x05 #x02)) 12) (t (corrupt)))))
          (when (= pgno 1) (incf nhdr 100))
          (setf (dsp-ncell p) (get-u16 b (+ h 3)))
          (let ((unused (+ (- (get-u16 b (+ h 5)) nhdr (* 2 (dsp-ncell p))) (aref b (+ h 7))))
                (off (get-u16 b (+ h 1))))
            (loop while (/= off 0)
                  do (when (>= off psz) (corrupt))
                     (incf unused (get-u16 b (+ off 2)))
                     (let ((next (get-u16 b off)))
                       (when (and (< next (+ off 4)) (> next 0)) (corrupt))
                       (setf off next)))
            (setf (dsp-unused p) unused))
          (setf (dsp-right p) (if leaf 0 (get-u32 b (+ h 8))))
          (let ((usable (db-usable-size db)) (cells '()))
            (dotimes (i (dsp-ncell p))
              (let ((off (get-u16 b (+ nhdr (* 2 i)))) (child 0) (nlocal 0) (ovfl '()) (nlast 0))
                (when (or (< off nhdr) (>= off psz)) (corrupt))
                (unless leaf (setf child (get-u32 b off)) (incf off 4))
                (unless (= flags #x05)
                  (multiple-value-bind (npayload n) (get-varint b off)
                    (incf off n)
                    (when (= flags #x0d) (incf off (nth-value 1 (get-varint b off))))
                    (when (> npayload (dsp-mx p)) (setf (dsp-mx p) npayload))
                    (setf nlocal (dbstat-local-payload usable flags npayload))
                    (when (< nlocal 0) (corrupt))
                    (when (> npayload nlocal)
                      (let ((novfl (floor (+ (- npayload nlocal) usable -4 -1) (- usable 4))))
                        (when (or (> (+ off nlocal 4) usable) (> npayload #x7fffffff)) (corrupt))
                        (setf nlast (- (- npayload nlocal) (* (1- novfl) (- usable 4))))
                        (let ((pg (get-u32 b (+ off nlocal))))
                          (push pg ovfl)
                          (loop repeat (1- novfl)
                                do (setf pg (get-u32 (read-page db pg) 0))
                                   (push pg ovfl)))))))
                (push (list nlocal child (nreverse ovfl) nlast) cells)))
            (setf (dsp-cells p) (nreverse cells))))))
    p))

;;; Walking the b-trees (statNext)

(defun dbstat-rows (db btrees agg schema-name)
  "Row vectors (12 columns + rowid) for BTREES, a list of (name root)."
  (let* ((psz (db-page-size db)) (usable (db-usable-size db))
         (rows '()) (last-pageno 0))
    (when (zerop (db-page-count db)) (return-from dbstat-rows nil))
    (dolist (bt btrees)
      (destructuring-bind (name root) bt
        (let ((npage 0) (ncell 0) (payload 0) (unused 0) (mx 0) (size 0))
          (labels ((emit (path pageno pagetype offset)
                     (unless agg
                       (push (vector name path pageno pagetype ncell payload unused mx offset size
                                     schema-name 0 pageno)
                             rows)
                       (setf ncell 0 payload 0 unused 0 mx 0 size 0)))
                   (visit (pgno path)
                     (let ((p (dbstat-decode db pgno)))
                       (incf npage)
                       (incf size psz)
                       (incf ncell (dsp-ncell p))
                       (incf unused (dsp-unused p))
                       (setf mx (max mx (dsp-mx p)))
                       (incf payload (reduce #'+ (dsp-cells p) :key #'first))
                       (emit path pgno (case (dsp-flags p) ((#x05 #x02) "internal") ((#x0d #x0a) "leaf") (t "corrupted"))
                             (* psz (1- pgno)))
                       (setf last-pageno pgno)
                       (loop for (nil child ovfl nlast) in (dsp-cells p)
                             for i from 0
                             do (loop for pg in ovfl
                                      for j from 0
                                      do (incf npage)
                                         (incf size psz)
                                         (if (< j (1- (length ovfl)))
                                             (incf payload (- usable 4))
                                             (progn (incf payload nlast) (incf unused (- usable 4 nlast))))
                                         ;; (SQLite computes the offset before moving to the page)
                                         (emit (and path (format nil "~a~(~3,'0x~)+~(~6,'0x~)" path i j))
                                               pg "overflow" (* psz (1- last-pageno)))
                                         (setf last-pageno pg))
                                (unless (zerop (dsp-right p))
                                  (visit child (and path (format nil "~a~(~3,'0x~)/" path i)))))
                       (unless (zerop (dsp-right p))
                         (visit (dsp-right p) (and path (format nil "~a~(~3,'0x~)/" path (dsp-ncell p))))))))
            (visit root (if agg nil "/"))
            (when agg
              (push (vector name :null npage :null ncell payload unused mx :null size schema-name 1 last-pageno)
                    rows))))))
    (nreverse rows)))

(defun dbstat-btrees (db name)
  (let ((out (list (list "sqlite_schema" 1))))
    (dolist (r (schema-rows (db-schema* db)))
      (destructuring-bind (rowid type nm tbl root &rest ignore) r
        (declare (ignore rowid type tbl ignore))
        (when (and (integerp root) (/= root 0))
          (push (list nm root) out))))
    (setf out (nreverse out))
    (if name (remove-if-not (lambda (b) (equal (first b) name)) out) out)))

(defun dbstat-plan-access (fs li conjuncts scope)
  (let* ((table (fsrc-table fs)) (v (table-vtab table))
         (args (fsrc-vtab-args fs))
         (eqs (equality-candidates conjuncts li scope))
         (find-eq (lambda (ci) (find-if (lambda (c) (and (eql (first c) ci) (eq (fourth c) :eq))) eqs)))
         (schema-fn (let ((c (or (and args (first args)) (second (funcall find-eq 10)))))
                      (and c (compile-expr c scope))))
         (name-fn (let ((c (second (funcall find-eq 0)))) (and c (compile-expr c scope))))
         (agg-fn (let ((c (or (and (cdr args) (second args)) (second (funcall find-eq 11)))))
                   (and c (compile-expr c scope))))
         (order (let ((h (and (= li 0) *order-hint*)))
                  (when (and h (eq (first h) :dbstat)) (setf *order-satisfied* t) t)))
         (idxnum (+ (if schema-fn 1 0) (if name-fn 2 0) (if agg-fn 4 0) (if order 8 0))))
    (eqp-table-note (format nil "SCAN ~a VIRTUAL TABLE INDEX ~d:" (src-name (fsrc-src fs)) idxnum))
    (lambda (env fn)
      (let* ((sname (if schema-fn
                        (let ((x (funcall schema-fn env))) (if (eq x :null) nil (value-to-text x)))
                        (or (dbs-schema v) "main")))
             (db (and sname (schema-db (table-owner* table) sname nil))))
        (when db
          (let* ((name (and name-fn (let ((x (funcall name-fn env))) (if (eq x :null) nil (value-to-text x)))))
                 (agg (and agg-fn (let ((x (funcall agg-fn env))) (/= 0 (value-to-real x)))))
                 (btrees (dbstat-btrees db name)))
            (when (and name-fn (null name)) (setf btrees (dbstat-btrees db nil)))
            (when order (setf btrees (stable-sort btrees #'string< :key #'first)))
            (dolist (r (dbstat-rows db btrees agg (db-name db)))
              (funcall fn r))))))))

(defun table-owner* (table)
  (or (table-owner table) *db*))
