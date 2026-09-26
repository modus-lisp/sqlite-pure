;;;; btree.lisp — table and index b-trees.
;;;;
;;;; Reads walk page bytes in place.  Writes decode a page into a NODE (a
;;;; list of CELLs), edit the list, and re-serialise the whole page; a node
;;;; that no longer fits is split into as many siblings as it needs and the
;;;; dividers are pushed into the parent, recursively.  The root page never
;;;; moves: an overflowing root moves its content to a new child first.
;;;;
;;;; Deletion keeps every non-root page non-empty (an empty page is unlinked
;;;; from its parent and freed; a parent left with no cells is collapsed
;;;; into its only child) but does not otherwise rebalance, so pages may be
;;;; under-full.  SQLite accepts that; PRAGMA integrity_check does too.

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

(defstruct node type cells right)
(defstruct cell child key body)         ; KEY: rowid, for table cells

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

(defun write-overflow (db data start)
  "Store DATA[START..] in a fresh overflow chain; return its first page."
  (let ((cap (- (db-usable-size db) 4))
        (pages '()))
    (loop for pos from start below (length data) by cap
          do (push (allocate-page db) pages))
    (setf pages (nreverse pages))
    (ptrmap-note-chain db pages)
    (loop for (pg next) on pages
          for pos from start by cap
          do (let ((b (page-for-write db pg)))
               (put-u32 b 0 (or next 0))
               (replace b data :start1 4 :start2 pos
                               :end2 (min (length data) (+ pos cap)))))
    (first pages)))

(defun free-overflow-chain (db first)
  (loop with pg = first
        with seen = 0
        while (plusp pg)
        do (when (> (incf seen) (db-page-count db)) (corrupt "overflow loop"))
           (let ((next (get-u32 (read-page db pg) 0)))
             (free-page db pg)
             (setf pg next))))

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

(defun insert-cell-in-place (db pgno pos body child)
  "Insert a cell at POS on page PGNO if the unallocated gap between the
cell-pointer array and the cell content area can take it."
  (let* ((b (read-page db pgno))
         (off (hdr-off pgno))
         (type (aref b off))
         (hs (page-hdr-size type))
         (n (page-ncells b off))
         (cs (let ((v (get-u16 b (+ off 5)))) (if (zerop v) 65536 v)))
         (ptr-end (+ off hs (* 2 n)))
         (len (max 4 (+ (length body) (if child 4 0)))))
    (when (>= (- cs ptr-end) (+ len 2))
      (let* ((b (page-for-write db pgno))
             (new-cs (- cs len)))
        (if child
            (progn (put-u32 b new-cs child) (replace b body :start1 (+ new-cs 4)))
            (replace b body :start1 new-cs))
        (let ((at (+ off hs (* 2 pos))))
          (replace b b :start1 (+ at 2) :start2 at :end2 ptr-end)
          (put-u16 b at new-cs))
        (put-u16 b (+ off 3) (1+ n))
        (put-u16 b (+ off 5) new-cs)
        (ptrmap-note-page db pgno)
        t))))

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

(defun decode-node (db pgno)
  (let* ((b (read-page db pgno))
         (off (hdr-off pgno))
         (type (check-page-type (aref b off) pgno))
         (n (page-ncells b off))
         (cells '()))
    (dotimes (i n)
      (let* ((p (cell-ptr b off type i))
             (len (cell-length db b p type)))
        (push (if (leaf-type-p type)
                  (make-cell :body (octets-subseq b p (+ p len))
                             :key (when (= type +leaf-table+)
                                    (get-varint-signed b (+ p (nth-value 1 (get-varint b p))))))
                  (make-cell :child (get-u32 b p)
                             :body (octets-subseq b (+ p 4) (+ p len))
                             :key (when (= type +interior-table+)
                                    (get-varint-signed b (+ p 4)))))
              cells)))
    (make-node :type type :cells (nreverse cells)
               :right (unless (leaf-type-p type) (get-u32 b (+ off 8))))))

(defun cell-space (c)
  (+ 2 (max 4 (+ (length (cell-body c)) (if (cell-child c) 4 0)))))

(defun node-fits-p (db pgno node)
  (<= (+ (hdr-off pgno) (page-hdr-size (node-type node))
         (reduce #'+ (node-cells node) :key #'cell-space))
      (db-usable-size db)))

(defun serialize-node (db pgno node)
  "Write NODE to page PGNO if it fits; return true on success."
  (when (node-fits-p db pgno node)
    (let* ((b (page-for-write db pgno))
           (off (hdr-off pgno))
           (type (node-type node))
           (hs (page-hdr-size type))
           (usable (db-usable-size db))
           (content usable)
           (cells (node-cells node)))
      (fill b 0 :start off)
      (setf (aref b off) type)
      (put-u16 b (+ off 3) (length cells))
      (unless (leaf-type-p type) (put-u32 b (+ off 8) (node-right node)))
      (loop for c in cells
            for i from 0
            for body = (cell-body c)
            for len = (max 4 (+ (length body) (if (cell-child c) 4 0)))
            do (decf content len)
               (let ((p content))
                 (when (cell-child c) (put-u32 b p (cell-child c)) (incf p 4))
                 (replace b body :start1 p))
               (put-u16 b (+ off hs (* 2 i)) content))
      (put-u16 b (+ off 5) (if (= content 65536) 0 content))
      (ptrmap-note-page db pgno)
      t)))

;;; ------------------------------------------------------------------
;;; Building cells

(defun make-table-leaf-cell (db rowid payload)
  (let* ((psize (length payload))
         (local (local-size db psize t))
         (n1 (varint-length psize))
         (n2 (varint-length rowid))
         (body (make-octets (+ n1 n2 local (if (< local psize) 4 0)))))
    (put-varint body 0 psize)
    (put-varint body n1 rowid)
    (replace body payload :start1 (+ n1 n2) :end2 local)
    (when (< local psize)
      (put-u32 body (+ n1 n2 local) (write-overflow db payload local)))
    (make-cell :key rowid :body body)))

(defun make-index-cell (db payload &optional child)
  (let* ((psize (length payload))
         (local (local-size db psize nil))
         (n1 (varint-length psize))
         (body (make-octets (+ n1 local (if (< local psize) 4 0)))))
    (put-varint body 0 psize)
    (replace body payload :start1 n1 :end2 local)
    (when (< local psize)
      (put-u32 body (+ n1 local) (write-overflow db payload local)))
    (make-cell :child child :body body)))

(defun cell-overflow-page (db type c)
  (let ((b (cell-body c)))
    (ecase type
      (#.+leaf-table+
       (multiple-value-bind (psize n1) (get-varint b 0)
         (let ((n2 (nth-value 1 (get-varint b n1)))
               (local (local-size db psize t)))
           (when (< local psize) (get-u32 b (+ n1 n2 local))))))
      (#.+interior-table+ nil)
      ((#.+leaf-index+ #.+interior-index+)
       (multiple-value-bind (psize n1) (get-varint b 0)
         (let ((local (local-size db psize nil)))
           (when (< local psize) (get-u32 b (+ n1 local)))))))))

(defun index-cell-payload (db c)
  (let ((b (cell-body c)))
    (multiple-value-bind (psize n1) (get-varint b 0)
      (read-payload db b n1 psize (local-size db psize nil)))))

(defun free-cell-overflow (db type c)
  (let ((pg (cell-overflow-page db type c)))
    (when pg (free-overflow-chain db pg))))

;;; ------------------------------------------------------------------
;;; Read-side traversal

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

(defun map-btree-pages (db root fn)
  "Call FN on every page number of the b-tree rooted at ROOT, overflow
pages included (children before parents)."
  (labels ((visit (pgno depth)
             (when (> depth 64) (corrupt "b-tree too deep"))
             (let* ((node (decode-node db pgno))
                    (type (node-type node)))
               (dolist (c (node-cells node))
                 (when (cell-child c) (visit (cell-child c) (1+ depth)))
                 (let ((ov (cell-overflow-page db type c)))
                   (loop while (and ov (plusp ov))
                         do (let ((next (get-u32 (read-page db ov) 0)))
                              (funcall fn ov)
                              (setf ov next)))))
               (when (node-right node) (visit (node-right node) (1+ depth)))
               (funcall fn pgno))))
    (visit root 0)))

;;; ------------------------------------------------------------------
;;; Splitting

(defun partition-cells (cells cap consumes k)
  "Split CELLS into K runs each fitting in CAP bytes.  When CONSUMES, the
cell between two runs becomes a divider.  Return (values runs dividers)
or NIL."
  (let* ((v (coerce cells 'vector))
         (n (length v))
         (sz (map 'vector #'cell-space v))
         (total (reduce #'+ sz))
         (target (/ total k))
         (i 0) (runs '()) (dividers '()))
    (dotimes (j k)
      (let ((start i) (sum 0))
        (if (= j (1- k))
            (progn
              (loop while (< i n) do (incf sum (aref sz i)) (incf i))
              (when (or (= start i) (> sum cap)) (return-from partition-cells nil)))
            (let ((reserve (* (- k j 1) (if consumes 2 1))))
              ;; Leave room for the divider after this run (if consumed) and
              ;; for at least one cell in each later run.
              (loop while (and (< i (- n reserve))
                               (<= (+ sum (aref sz i)) cap)
                               (or (= i start) (< sum target)))
                    do (incf sum (aref sz i)) (incf i))
              (when (= i start) (return-from partition-cells nil))))
        (push (coerce (subseq v start i) 'list) runs)
        (when (and consumes (< j (1- k)))
          (when (>= i n) (return-from partition-cells nil))
          (push (aref v i) dividers)
          (incf i))))
    (values (nreverse runs) (nreverse dividers))))

(defun interior-type (type)
  (if (table-type-p type) +interior-table+ +interior-index+))

(defun write-node (db pgno node path &optional append)
  "Store NODE at PGNO, splitting as needed.  PATH is ((parent . index) ...)
from the immediate parent up to the root."
  (cond ((serialize-node db pgno node))
        ((null path)
         ;; The root overflowed: move its content to a new child.
         (let ((child (allocate-page db)))
           (serialize-node db pgno (make-node :type (interior-type (node-type node))
                                              :cells '() :right child))
           (split-node db child node (list (cons pgno 0)) append)))
        (t (split-node db pgno node path append))))

(defun split-node (db pgno node path append)
  (let* ((type (node-type node))
         (cells (node-cells node))
         (cap (- (db-usable-size db) (page-hdr-size type)))
         (consumes (/= type +leaf-table+))
         runs dividers)
    ;; Appending to a table leaf: leave the old cells packed and start a
    ;; new page with just the new one (SQLite's "quick balance").
    (when (and append (not consumes) (> (length cells) 1))
      (let ((old (butlast cells)) (new (last cells)))
        (when (and (<= (reduce #'+ old :key #'cell-space) cap)
                   (<= (reduce #'+ new :key #'cell-space) cap))
          (setf runs (list old new)))))
    (unless runs
      (loop for k from 2 to (max 2 (length cells))
            do (multiple-value-bind (r d) (partition-cells cells cap consumes k)
                 (when r (setf runs r dividers d) (return))))
      (unless runs (corrupt "cannot split page ~d" pgno)))
    (let* ((k (length runs))
           (pages (append (loop repeat (1- k) collect (allocate-page db)) (list pgno)))
           (leaf (leaf-type-p type))
           (new-parent-cells '()))
      (loop for run in runs
            for pg in pages
            for j from 0
            for div = (nth j dividers)
            do (unless (serialize-node db pg (make-node :type type :cells run
                                                        :right (unless leaf
                                                                 (if (< j (1- k))
                                                                     (cell-child div)
                                                                     (node-right node)))))
                 (corrupt "split produced an oversized page"))
               (when (< j (1- k))
                 (push (cond ((= type +leaf-table+)
                              (let ((key (cell-key (car (last run)))))
                                (make-cell :child pg :key key :body (varint-octets key))))
                             (t (make-cell :child pg :key (cell-key div)
                                           :body (cell-body div))))
                       new-parent-cells)))
      (setf new-parent-cells (nreverse new-parent-cells))
      (destructuring-bind ((ppg . idx) . rest) path
        (let* ((parent (decode-node db ppg))
               (pcells (node-cells parent)))
          (setf (node-cells parent)
                (append (subseq pcells 0 idx) new-parent-cells (nthcdr idx pcells)))
          (write-node db ppg parent rest))))))

;;; ------------------------------------------------------------------
;;; Table b-tree mutation

(defun table-seek-path (db root rowid)
  "Return (values leaf-pgno path)."
  (let ((pgno root) (path '()))
    (loop repeat 64
          do (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off)))
               (when (= type +leaf-table+) (return-from table-seek-path (values pgno path)))
               (let ((lo 0) (hi n))
                 (loop while (< lo hi)
                       do (let ((mid (floor (+ lo hi) 2)))
                            (if (< (get-varint-signed b (+ (cell-ptr b off type mid) 4)) rowid)
                                (setf lo (1+ mid))
                                (setf hi mid))))
                 (push (cons pgno lo) path)
                 (setf pgno (if (< lo n)
                                (get-u32 b (cell-ptr b off type lo))
                                (get-u32 b (+ off 8)))))))
    (corrupt "b-tree too deep")))

(defun table-insert (db root rowid payload)
  "Insert or replace the row ROWID."
  (multiple-value-bind (leaf path) (table-seek-path db root rowid)
    (let* ((b (read-page db leaf))
           (off (hdr-off leaf))
           (n (page-ncells b off))
           (pos (lower-bound n (lambda (i) (>= (raw-cell-rowid b off +leaf-table+ i) rowid)))))
      (unless (and (< pos n) (= (raw-cell-rowid b off +leaf-table+ pos) rowid))
        ;; fast path: a new rowid, and room on the page
        (let ((cell (make-table-leaf-cell db rowid payload)))
          (unless (insert-cell-in-place db leaf pos (cell-body cell) nil)
            (let* ((node (decode-node db leaf))
                   (cells (node-cells node)))
              (setf (node-cells node) (append (subseq cells 0 pos) (list cell) (nthcdr pos cells)))
              (write-node db leaf node path (= pos (length cells)))))
          (return-from table-insert nil))))
    (let* ((node (decode-node db leaf))
           (cells (node-cells node))
           (pos (or (position-if (lambda (c) (>= (cell-key c) rowid)) cells)
                    (length cells)))
           (existing (and (< pos (length cells)) (= (cell-key (nth pos cells)) rowid)))
           (cell (make-table-leaf-cell db rowid payload)))
      (when existing
        (free-cell-overflow db +leaf-table+ (nth pos cells)))
      (setf (node-cells node)
            (append (subseq cells 0 pos) (list cell)
                    (nthcdr (if existing (1+ pos) pos) cells)))
      (write-node db leaf node path (= pos (length cells))))))

(defun table-delete (db root rowid)
  "Delete ROWID; return true if it existed."
  (multiple-value-bind (leaf path) (table-seek-path db root rowid)
    (let* ((node (decode-node db leaf))
           (cell (find rowid (node-cells node) :key #'cell-key)))
      (when cell
        (free-cell-overflow db +leaf-table+ cell)
        (setf (node-cells node) (remove cell (node-cells node)))
        (if (or (node-cells node) (null path))
            (serialize-node db leaf node)
            (remove-empty-page db root leaf path))
        t))))

(defun remove-empty-page (db root pgno path)
  "PGNO is an empty non-root leaf: unlink it and free it."
  (free-page db pgno)
  (destructuring-bind ((ppg . idx) . rest) path
    (let* ((parent (decode-node db ppg))
           (cells (node-cells parent))
           (n (length cells))
           (orphan nil))
      (if (< idx n)
          (progn (setf orphan (nth idx cells))
                 (setf (node-cells parent) (remove orphan cells)))
          (progn (setf orphan (car (last cells)))
                 (setf (node-right parent) (cell-child orphan)
                       (node-cells parent) (butlast cells))))
      (if (node-cells parent)
          (serialize-node db ppg parent)
          (collapse-page db ppg parent rest))
      ;; An index divider carries a real entry: put it back.
      (when (= (node-type parent) +interior-index+)
        (let ((payload (index-cell-payload db orphan)))
          (free-cell-overflow db +interior-index+ orphan)
          (index-insert-payload db root payload))))))

(defun collapse-page (db pgno node path)
  "NODE (at PGNO) is an interior page left with no cells, only a right
child.  At the root, pull the child up (every leaf gets one level
shallower).  Elsewhere, merge it with a sibling through the parent's
divider, which keeps every leaf at the same depth."
  (let ((child (node-right node)))
    (if (null path)
        (let ((cnode (decode-node db child)))
          (free-page db child)
          (write-node db pgno cnode nil))
        (destructuring-bind ((gpg . gidx) . rest) path
          (let* ((g (decode-node db gpg))
                 (gcells (node-cells g))
                 (n (length gcells)))
            (flet ((child-at (i) (if (< i n) (cell-child (nth i gcells)) (node-right g))))
              (if (plusp gidx)
                  ;; merge into the left sibling Q = child (gidx-1)
                  (let* ((div (nth (1- gidx) gcells))
                         (q-pg (cell-child div))
                         (q (decode-node db q-pg)))
                    (setf (node-cells q)
                          (append (node-cells q)
                                  (list (make-cell :child (node-right q) :key (cell-key div)
                                                   :body (cell-body div))))
                          (node-right q) child)
                    ;; drop the divider; the pointer that named PGNO now names Q
                    (setf gcells (remove div gcells))
                    (if (< gidx n)
                        (setf (cell-child (nth (1- gidx) gcells)) q-pg)
                        (setf (node-right g) q-pg))
                    (setf (node-cells g) gcells)
                    (free-page db pgno)
                    (finish-merge db gpg g rest q-pg q (1- gidx)))
                  ;; leftmost child: merge into the right sibling Q
                  (let* ((div (first gcells))
                         (q-pg (child-at 1))
                         (q (decode-node db q-pg)))
                    (setf (node-cells q)
                          (cons (make-cell :child child :key (cell-key div) :body (cell-body div))
                                (node-cells q)))
                    (setf (node-cells g) (rest gcells))
                    (free-page db pgno)
                    (finish-merge db gpg g rest q-pg q 0)))))))))

(defun finish-merge (db gpg g gpath q-pg q q-idx)
  "Store the parent G (one cell shorter) and the merged sibling Q, which
sits at index Q-IDX of G."
  (if (node-cells g)
      (progn
        (serialize-node db gpg g)
        (write-node db q-pg q (cons (cons gpg q-idx) gpath)))
      (progn
        ;; G is now empty too.  Store Q first (a split would give G a cell
        ;; back), then deal with G.
        (serialize-node db gpg g)
        (write-node db q-pg q (cons (cons gpg q-idx) gpath))
        (let ((g2 (decode-node db gpg)))
          (unless (node-cells g2)
            (collapse-page db gpg g2 gpath))))))

;;; ------------------------------------------------------------------
;;; Index b-tree mutation.  Entries are records whose last column is the
;;; rowid, so every entry is unique.  *INDEX-CMP* compares two decoded
;;; entries.

(defvar *index-cmp* nil "Comparator (a b) -> -1/0/1 for the index being modified.")

(defun cell-values (db c)
  (decode-record (index-cell-payload db c)))

(defun index-seek-path (db root vals)
  "Descend toward VALS.  Return (values pgno path position found-p node)
where POSITION is the first cell >= VALS on the page where the search
stopped (a leaf, or the interior page holding an equal entry)."
  (let ((pgno root) (path '()))
    (loop repeat 64
          do (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off))
                    (cmp-at (make-hash-table))
                    (pos (lower-bound n (lambda (i)
                                          (let ((c (funcall *index-cmp* (raw-index-entry db b off type i) vals)))
                                            (setf (gethash i cmp-at) c)
                                            (>= c 0)))))
                    (found (and (< pos n)
                                (= 0 (or (gethash pos cmp-at)
                                         (funcall *index-cmp* (raw-index-entry db b off type pos) vals))))))
               (when (or found (leaf-type-p type))
                 (return-from index-seek-path (values pgno path pos found (decode-node db pgno))))
               (push (cons pgno pos) path)
               (setf pgno (if (< pos n)
                              (get-u32 b (cell-ptr b off type pos))
                              (get-u32 b (+ off 8))))))
    (corrupt "b-tree too deep")))

(defun index-insert-payload (db root payload)
  (let ((vals (decode-record payload))
        (pgno root) (path '()))
    ;; Entries are unique (the rowid is part of the key), so the new entry
    ;; always goes into a leaf.
    (loop repeat 64
          do (let* ((b (read-page db pgno))
                    (off (hdr-off pgno))
                    (type (check-page-type (aref b off) pgno))
                    (n (page-ncells b off))
                    (pos (lower-bound n (lambda (i)
                                          (>= (funcall *index-cmp* (raw-index-entry db b off type i) vals) 0)))))
               (if (leaf-type-p type)
                   (let ((cell (make-index-cell db payload)))
                     (unless (insert-cell-in-place db pgno pos (cell-body cell) nil)
                       (let* ((node (decode-node db pgno))
                              (cells (node-cells node)))
                         (setf (node-cells node) (append (subseq cells 0 pos) (list cell) (nthcdr pos cells)))
                         (write-node db pgno node path (= pos (length cells)))))
                     (return-from index-insert-payload nil))
                   (progn
                     (push (cons pgno pos) path)
                     (setf pgno (if (< pos n)
                                    (get-u32 b (cell-ptr b off type pos))
                                    (get-u32 b (+ off 8))))))))
    (corrupt "b-tree too deep")))

(defun index-insert (db root vals)
  (index-insert-payload db root (encode-record vals)))

(defun index-delete (db root vals)
  "Delete the entry equal to VALS; return true if found."
  (multiple-value-bind (pgno path pos found node) (index-seek-path db root vals)
    (unless found (return-from index-delete nil))
    (let ((type (node-type node))
          (victim (nth pos (node-cells node))))
      (if (leaf-type-p type)
          (progn
            (free-cell-overflow db type victim)
            (setf (node-cells node) (remove victim (node-cells node)))
            (if (or (node-cells node) (null path))
                (serialize-node db pgno node)
                (remove-empty-page db root pgno path)))
          ;; Interior: replace by the in-order predecessor, then remove the
          ;; predecessor's leaf copy.  The predecessor's cell (with its
          ;; overflow chain) moves up, so its chain is not freed.
          (let* ((pred-leaf (loop with pg = (cell-child victim)
                                  for nd = (decode-node db pg)
                                  until (leaf-type-p (node-type nd))
                                  do (setf pg (node-right nd))
                                  finally (return nd)))
                 (pred (car (last (node-cells pred-leaf))))
                 (pred-vals (cell-values db pred)))
            (free-cell-overflow db type victim)
            (setf (cell-body victim) (cell-body pred))
            (write-node db pgno node path)
            (index-delete-leaf-copy db root pred-vals))))
    t))

(defun index-delete-leaf-copy (db root vals)
  "Remove the leaf occurrence of VALS, which also appears in an interior
page: descend, and on meeting the interior copy go left and then rightmost."
  (let ((pgno root) (path '()) (rightmost nil))
    (loop
      (let* ((node (decode-node db pgno))
             (cells (node-cells node)))
        (when (leaf-type-p (node-type node))
          (let ((victim (car (last cells))))
            (unless (and rightmost victim)
              (corrupt "index predecessor not found"))
            (setf (node-cells node) (butlast cells))
            (if (or (node-cells node) (null path))
                (serialize-node db pgno node)
                (remove-empty-page db root pgno path))
            (return t)))
        (let ((pos (if rightmost
                       (length cells)
                       (or (position-if (lambda (c)
                                          (>= (funcall *index-cmp* (cell-values db c) vals) 0))
                                        cells)
                           (length cells)))))
          (when (and (not rightmost) (< pos (length cells))
                     (= 0 (funcall *index-cmp* (cell-values db (nth pos cells)) vals)))
            (setf rightmost t))
          (push (cons pgno pos) path)
          (setf pgno (if (< pos (length cells))
                         (cell-child (nth pos cells))
                         (node-right node))))))))

;;; ------------------------------------------------------------------
;;; Whole trees

(defun create-btree (db type)
  (ensure-write-txn db)                  ; page 1 (and its auto_vacuum flag) first
  (let ((pg (if (autovacuum-p db) (allocate-root db) (allocate-page db))))
    (serialize-node db pg (make-node :type type :cells '()
                                     :right (unless (leaf-type-p type) 0)))
    pg))

(defun clear-btree (db root &key keep-root)
  "Free every page of the tree; with KEEP-ROOT leave an empty root."
  (let* ((type (node-type (decode-node db root)))
         (leaf (if (table-type-p type) +leaf-table+ +leaf-index+))
         (pages '()))
    (map-btree-pages db root (lambda (pg) (push pg pages)))
    (dolist (pg pages)
      (unless (and keep-root (= pg root)) (free-page db pg)))
    (when keep-root
      (serialize-node db root (make-node :type leaf :cells '())))))
