;;;; autovacuum.lisp — auto_vacuum databases: pointer maps and page moves.
;;;;
;;;; An auto-vacuum database (header offset 52 non-zero) keeps a pointer
;;;; map: every page after page 1 has a 5-byte entry, on a map page, giving
;;;; its role and its parent, so that any page can be moved and its one
;;;; referrer fixed.  Three rules follow, all kept here:
;;;;   * table roots are packed at the front: a new root goes at
;;;;     largest-root + 1, moving whatever lived there;
;;;;   * dropping a root moves the largest root into its slot (and the
;;;;     schema's rootpage with it);
;;;;   * in FULL mode (offset 64 zero) every commit moves pages down from
;;;;     the end into free slots and truncates the file; INCREMENTAL mode
;;;;     does so on PRAGMA incremental_vacuum.

(in-package #:sqlite-pure)

(defconstant +ptrmap-root+ 1)
(defconstant +ptrmap-free+ 2)
(defconstant +ptrmap-overflow1+ 3)
(defconstant +ptrmap-overflow2+ 4)
(defconstant +ptrmap-btree+ 5)
(defconstant +hdr-largest-root+ 52)
(defconstant +hdr-incremental+ 64)

(defun autovacuum-p (db)
  (and (plusp (db-page-count db)) (plusp (get-u32 (read-page db 1) +hdr-largest-root+))))

(defun incremental-p (db) (plusp (get-u32 (read-page db 1) +hdr-incremental+)))

(defun ptrmap-page-of (db pgno)
  "The pointer-map page holding PGNO's entry (sqlite3's PTRMAP_PAGENO)."
  (let* ((per (1+ (floor (db-usable-size db) 5)))
         (ret (+ 2 (* per (floor (- pgno 2) per)))))
    (if (= ret (pending-byte-page db)) (1+ ret) ret)))

(defun ptrmap-page-p (db pgno)
  (and (>= pgno 2) (= pgno (ptrmap-page-of db pgno))))

(defun skipped-page-p (db pgno)
  "Pages that are never b-tree, overflow or free pages."
  (or (ptrmap-page-p db pgno) (= pgno (pending-byte-page db))))

(defun ptrmap-put (db pgno type parent)
  (when (and (autovacuum-p db) (>= pgno 3) (not (ptrmap-page-p db pgno)))
    (let* ((mp (ptrmap-page-of db pgno))
           (off (* 5 (- pgno mp 1))))
      (let ((cur (read-page db mp)))
        (unless (and (= (aref cur off) type) (= (get-u32 cur (1+ off)) parent))
          (let ((b (page-for-write db mp)))
            (setf (aref b off) type)
            (put-u32 b (1+ off) parent)))))))

(defun ptrmap-get (db pgno)
  "(values type parent) of PGNO."
  (let* ((mp (ptrmap-page-of db pgno))
         (off (* 5 (- pgno mp 1)))
         (b (read-page db mp)))
    (values (aref b off) (get-u32 b (1+ off)))))

;;; ------------------------------------------------------------------
;;; Keeping entries current (called from the b-tree layer)

(defun cell-overflow-at (db b off type i)
  "(values first-overflow-page offset-of-its-pointer) for cell I, or NIL."
  (let ((p (cell-ptr b off type i)))
    (ecase type
      (#.+leaf-table+
       (multiple-value-bind (psize n1) (get-varint b p)
         (let* ((n2 (nth-value 1 (get-varint b (+ p n1))))
                (local (local-size db psize t)))
           (when (< local psize)
             (let ((at (+ p n1 n2 local))) (values (get-u32 b at) at))))))
      (#.+interior-table+ nil)
      ((#.+leaf-index+ #.+interior-index+)
       (let ((q (if (= type +interior-index+) (+ p 4) p)))
         (multiple-value-bind (psize n1) (get-varint b q)
           (let ((local (local-size db psize nil)))
             (when (< local psize)
               (let ((at (+ q n1 local))) (values (get-u32 b at) at))))))))))

(defun ptrmap-note-page (db pgno)
  "Record b-tree page PGNO as parent of its children and overflow chains."
  (when (autovacuum-p db)
    (let* ((b (read-page db pgno))
           (off (hdr-off pgno))
           (type (aref b off))
           (n (page-ncells b off)))
      (dotimes (i n)
        (unless (leaf-type-p type)
          (ptrmap-put db (get-u32 b (cell-ptr b off type i)) +ptrmap-btree+ pgno))
        (let ((ov (cell-overflow-at db b off type i)))
          (when ov (ptrmap-put db ov +ptrmap-overflow1+ pgno))))
      (unless (leaf-type-p type)
        (ptrmap-put db (get-u32 b (+ off 8)) +ptrmap-btree+ pgno)))))

(defun ptrmap-note-chain (db pages)
  "An overflow chain: each page's parent is the one before it."
  (loop for (a b) on pages
        while b do (ptrmap-put db b +ptrmap-overflow2+ a)))

;;; ------------------------------------------------------------------
;;; Moving a page (relocatePage)

(defun relocate-page (db src dst &optional type parent)
  "Move page SRC's content to DST (already allocated) and fix its referrer
and the entries of the pages it refers to."
  (unless type (multiple-value-setq (type parent) (ptrmap-get db src)))
  (let ((content (copy-seq (read-page db src))))
    (replace (page-for-write db dst) content))
  (cond ((member type (list +ptrmap-root+ +ptrmap-btree+))
         (ptrmap-note-page db dst))
        (t (let ((next (get-u32 (read-page db dst) 0)))
             (when (plusp next) (ptrmap-put db next +ptrmap-overflow2+ dst)))))
  (unless (= type +ptrmap-root+)
    ;; modifyPagePointer: the first pointer to SRC in the referrer
    (cond ((= type +ptrmap-btree+)
           (let* ((b (page-for-write db parent)) (off (hdr-off parent))
                  (ptype (aref b off)) (n (page-ncells b off)))
             (unless (loop for i below n
                           for p = (cell-ptr b off ptype i)
                           thereis (when (= (get-u32 b p) src) (put-u32 b p dst) t))
               (if (= (get-u32 b (+ off 8)) src)
                   (put-u32 b (+ off 8) dst)
                   (corrupt "page ~d not referred to by ~d" src parent)))))
          ((= type +ptrmap-overflow1+)
           (let* ((b (read-page db parent)) (off (hdr-off parent))
                  (ptype (aref b off)) (n (page-ncells b off)))
             (dotimes (i n (corrupt "overflow page ~d not referred to by ~d" src parent))
               (multiple-value-bind (ov at) (cell-overflow-at db b off ptype i)
                 (when (eql ov src)
                   (put-u32 (page-for-write db parent) at dst)
                   (return))))))
          ((= type +ptrmap-overflow2+)
           (put-u32 (page-for-write db parent) 0 dst)))
    (ptrmap-put db dst type parent))
  type)

;;; ------------------------------------------------------------------
;;; Roots (btreeCreateTable / btreeDropTable)

(defun next-root-slot (db n)
  (loop do (incf n) while (skipped-page-p db n))
  n)

(defun allocate-root (db)
  "The page for a new b-tree root: the slot after the largest root, its
occupant (if any) moved out of the way."
  (let* ((root (next-root-slot db (header-u32 db +hdr-largest-root+)))
         (move (allocate-page db root :exact)))
    (when (/= move root)
      (multiple-value-bind (type parent) (ptrmap-get db root)
        (when (member type (list +ptrmap-root+ +ptrmap-free+))
          (corrupt "root slot ~d already a root" root))
        (relocate-page db root move type parent)))
    (ptrmap-put db root +ptrmap-root+ 0)
    (set-header-u32 db +hdr-largest-root+ root)
    root))

(defun release-root (db root)
  "After ROOT's tree was cleared (ROOT itself left an empty leaf): keep the
roots packed.  Returns the root page moved into ROOT's slot (whose schema
entry must change), or NIL."
  (let ((largest (header-u32 db +hdr-largest-root+)) (moved nil))
    (if (= root largest)
        (free-page db root)
        (progn
          (relocate-page db largest root +ptrmap-root+ 0)
          (free-page db largest)
          (setf moved largest)))
    (let ((n (1- largest)))
      (loop while (skipped-page-p db n) do (decf n))
      (set-header-u32 db +hdr-largest-root+ n))
    moved))

;;; ------------------------------------------------------------------
;;; Vacuuming (incrVacuumStep, autoVacuumCommit)

(defun final-db-size (db norig nfree)
  (let* ((nentry (floor (db-usable-size db) 5))
         (nptrmap (floor (+ (- nfree norig) (ptrmap-page-of db norig) nentry) nentry))
         (nfin (- norig nfree nptrmap)))
    (when (and (> norig (pending-byte-page db)) (< nfin (pending-byte-page db)))
      (decf nfin))
    (loop while (skipped-page-p db nfin) do (decf nfin))
    nfin))

(defun incr-vacuum-step (db nfin last commit)
  "Empty page LAST into a free page at or below NFIN.  :DONE if the
freelist is empty."
  (unless (skipped-page-p db last)
    (when (zerop (header-u32 db +hdr-freelist-count+))
      (return-from incr-vacuum-step :done))
    (multiple-value-bind (type parent) (ptrmap-get db last)
      (cond ((= type +ptrmap-root+) (corrupt "root page ~d above the vacuum limit" last))
            ((= type +ptrmap-free+)
             (unless commit (allocate-page db last :exact)))
            (t (let ((dst nil))
                 (loop do (setf dst (if commit (allocate-page db 0 :any) (allocate-page db nfin :le)))
                       while (and commit (> dst nfin)))
                 (relocate-page db last dst type parent))))))
  (unless commit
    (loop do (decf last) while (skipped-page-p db last))
    (shrink-to db last))
  :ok)

(defun autovacuum-commit (db)
  "FULL auto-vacuum: before committing, move pages down and shrink."
  (let ((nfree (header-u32 db +hdr-freelist-count+))
        (norig (db-page-count db)))
    (when (plusp nfree)
      (let ((nfin (final-db-size db norig nfree)))
        (loop for last from norig above nfin
              until (eq (incr-vacuum-step db nfin last t) :done))
        (set-header-u32 db +hdr-freelist-trunk+ 0)
        (set-header-u32 db +hdr-freelist-count+ 0)
        (set-header-u32 db +hdr-page-count+ nfin)
        (shrink-to db nfin)))))

(defun incremental-vacuum (db n)
  "PRAGMA incremental_vacuum(N): N steps (all if N <= 0), each moving the
last page of the file into a free page, as sqlite3BtreeIncrVacuum does."
  (loop repeat (if (plusp n) n most-positive-fixnum)
        do (let ((nfree (header-u32 db +hdr-freelist-count+))
                 (norig (db-page-count db)))
             (when (zerop nfree) (return))
             (when (eq (incr-vacuum-step db (final-db-size db norig nfree) norig nil) :done)
               (return))
             (set-header-u32 db +hdr-page-count+ (db-page-count db)))))

(defun ptrmap-problems (db)
  "Pointer-map entries that disagree with the b-trees and the freelist."
  (let ((problems '()))
    (labels ((expect (pg type parent)
               (when (and (>= pg 3) (<= pg (db-page-count db)) (not (ptrmap-page-p db pg)))
                 (multiple-value-bind (ty pa) (ptrmap-get db pg)
                   (unless (and (= ty type) (= pa parent))
                     (push (format nil "Bad ptr map entry key=~d expected=(~d,~d) got=(~d,~d)"
                                   pg type parent ty pa)
                           problems)))))
             (chain (first parent)
               (expect first +ptrmap-overflow1+ parent)
               (loop with prev = first
                     for next = (get-u32 (read-page db prev) 0)
                     for guard from 0
                     while (and (plusp next) (< guard (db-page-count db)))
                     do (expect next +ptrmap-overflow2+ prev)
                        (setf prev next)))
             (tree (pg depth)
               (when (< depth 64)
                 (let* ((b (read-page db pg)) (off (hdr-off pg)) (type (aref b off))
                        (n (page-ncells b off)))
                   (when (member type '(2 5 10 13))
                     (dotimes (i n)
                       (let ((ov (cell-overflow-at db b off type i)))
                         (when ov (chain ov pg)))
                       (unless (leaf-type-p type)
                         (let ((c (get-u32 b (cell-ptr b off type i))))
                           (expect c +ptrmap-btree+ pg)
                           (tree c (1+ depth)))))
                     (unless (leaf-type-p type)
                       (let ((c (get-u32 b (+ off 8))))
                         (expect c +ptrmap-btree+ pg)
                         (tree c (1+ depth)))))))))
      (dolist (r (schema-rows (load-schema db)))
        (let ((root (fifth r)))
          (when (and (integerp root) (plusp root))
            (expect root +ptrmap-root+ 0)
            (tree root 0))))
      (tree 1 0)
      (let ((trunk (header-u32 db +hdr-freelist-trunk+)) (guard 0))
        (loop while (and (plusp trunk) (< (incf guard) (db-page-count db)))
              do (expect trunk +ptrmap-free+ 0)
                 (let ((tb (read-page db trunk)))
                   (dotimes (i (min (get-u32 tb 4) (floor (db-usable-size db) 4)))
                     (expect (get-u32 tb (+ 8 (* 4 i))) +ptrmap-free+ 0))
                   (setf trunk (get-u32 tb 0))))))
    (nreverse problems)))

(defun shrink-to (db n)
  (loop for p from (1+ n) to (db-page-count db)
        do (remhash p (db-dirty db))
           (remhash p (db-cache db)))
  (setf (db-page-count db) n))
