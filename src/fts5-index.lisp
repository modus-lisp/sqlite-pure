;;;; fts5-index.lisp — the FTS5 full-text index, in SQLite 3.40's format.
;;;;
;;;; The index lives in <t>_data (blobs by id) and <t>_idx (a b-tree over
;;;; each segment's leaves):
;;;;   id 1           averages: varints nRow, then total tokens per column
;;;;   id 10          structure: cookie (4 bytes), nLevel, nSegment,
;;;;                  write-counter, then per level nMerge, nSeg and each
;;;;                  segment's (id first-page last-page)
;;;;   segid<<37|pg   leaf pages of a segment
;;;; A leaf page: u16 offset of the first rowid not preceded by a term on the
;;;; page (0: none), u16 size of the data, the data, then a footer of varint
;;;; term offsets (the first absolute, then deltas).  Terms are prefix-
;;;; compressed (a page's first term is written whole) and carry a leading
;;;; index byte: '0' for the main index, '1'.. for prefix indexes.  After each
;;;; term comes its doclist: rowids (the first on a doclist or on a page
;;;; absolute, then deltas), each followed (detail full/column) by a varint
;;;; nBytes*2+deleted and a position list, or (detail none) by 0x00 if the
;;;; row was deleted (0x00 0x00: deleted and re-inserted).  Positions are
;;;; varint (offset - previous + 2) with 0x01 col introducing a column;
;;;; detail=column lists columns the same way.
;;;;
;;;; Writes collect in a pending buffer that is flushed as a new level-0
;;;; segment at the end of each statement (and whenever rowids would repeat
;;;; or go backwards, as SQLite does).  A newer segment's entry for a
;;;; (term, rowid) replaces older ones, and an entry with no positions marks
;;;; a deletion.  Segments are merged level by level (automerge, crisis-
;;;; merge), and delete markers disappear when the merge output is the
;;;; oldest data in the index.  The leaf writer follows SQLite's
;;;; (fts5WriteAppendTerm & co.), so a flushed segment is byte-identical to
;;;; the one SQLite would write; doclist indexes are not written (they only
;;;; speed up seeks, and SQLite does not require them).

(in-package #:sqlite-pure)

(defconstant +fts5-averages-id+ 1)
(defconstant +fts5-structure-id+ 10)
(defconstant +fts5-max-token-size+ 32768)

(defstruct (fts5 (:conc-name fts-))
  name db
  columns                ; user column names
  unindexed              ; list of booleans, per column
  prefixes               ; prefix index lengths (characters)
  (detail :full)         ; :full :column :none
  (content :normal)      ; :normal, :none (content=''), or the external table name
  (content-rowid "rowid")
  (columnsize t)
  tokenizer tokenize-spec
  ;; %_config
  (pgsz 4050) (automerge 4) (crisismerge 16) (usermerge 4) (hashsize 1048576)
  rank (cookie 0) config-loaded
  ;; pending writes
  (pending (make-hash-table :test #'equal))
  (pending-rowid nil) (pending-delete nil) (pending-bytes 0)
  totals)                ; (nrow . vector of per-column totals) while writing

;;; ------------------------------------------------------------------
;;; Varints (SQLite's) on byte vectors and byte strings

(defun fts-varint-bytes (v)
  "The SQLite varint of V (as an unsigned 64-bit value), as a byte vector."
  (varint-octets v))

(defun buf-varint (buf v)
  (loop for b across (fts-varint-bytes v) do (vector-push-extend b buf)))

(defun buf-bytes (buf bytes &optional (start 0) (end (length bytes)))
  (loop for i from start below end do (vector-push-extend (aref bytes i) buf)))

(defun read-fts-varint (b off)
  "(values value next-offset) of the varint at OFF of byte vector B."
  (let ((v 0))
    (dotimes (i 8)
      (let ((x (aref b (+ off i))))
        (setf v (logior (ash v 7) (logand x #x7f)))
        (when (< x #x80) (return-from read-fts-varint (values v (+ off i 1))))))
    (values (logior (ash v 8) (aref b (+ off 8))) (+ off 9))))

(defun varint-size (b off)
  (nth-value 1 (read-fts-varint b off)))

(defun new-buf () (make-array 64 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))

(defun signed64 (u) (if (logbitp 63 u) (- u (expt 2 64)) u))

;;; ------------------------------------------------------------------
;;; Term keys: byte strings (characters 0..255), compared as memcmp

(defun fts-term-key (index-char token)
  (let* ((b (utf8-encode token))
         (b (if (> (length b) +fts5-max-token-size+) (subseq b 0 +fts5-max-token-size+) b))
         (s (make-string (1+ (length b)))))
    (setf (char s 0) index-char)
    (dotimes (i (length b) s) (setf (char s (1+ i)) (code-char (aref b i))))))

(defun key-bytes (key) (map '(vector (unsigned-byte 8)) #'char-code key))

(defun prefix-key (i token nchars)
  "The prefix index I's key for TOKEN, or NIL if it has fewer than NCHARS characters."
  (when (>= (length token) nchars)
    (fts-term-key (code-char (+ 48 i)) (subseq token 0 nchars))))

;;; ------------------------------------------------------------------
;;; Shadow tables

(defun fts-shadow (fts suffix)
  (or (find-table-in (fts-db fts) (format nil "~a_~a" (fts-name fts) suffix))
      (corrupt "database disk image is malformed")))

(defun fts-data-get (fts id)
  (let ((r (shadow-get (fts-shadow fts "data") id)))
    (and r (let ((b (first r))) (if (blobp b) b (make-octets 0))))))

(defun fts-data-put (fts id bytes)
  (shadow-put (fts-shadow fts "data") id (list (coerce bytes '(simple-array (unsigned-byte 8) (*))))))

(defun fts-data-delete-range (fts lo hi)
  (let ((tb (fts-shadow fts "data")) (ids '()))
    (catch :range-done
      (map-table (table-owner tb) (table-root tb)
                 (lambda (rowid payload) (declare (ignore payload))
                   (when (> rowid hi) (throw :range-done nil))
                   (when (>= rowid lo) (push rowid ids)))
                 :start lo))
    (dolist (id ids) (shadow-del tb id))))

(defun segment-rowid (segid pgno) (+ (ash segid 37) pgno))

;;; %_idx (segid, term, pgno), WITHOUT ROWID: key (segid term)
(defun fts-idx-table (fts) (fts-shadow fts "idx"))

(defun fts-idx-entries (fts segid)
  "((term-bytes . pgno-field) ...) of segment SEGID, in key order."
  (let* ((tb (fts-idx-table fts)) (out '()))
    (catch :idx-done
      (map-index (table-owner tb) (table-root tb)
                 (lambda (vals)
                   (unless (eql (first vals) segid) (throw :idx-done nil))
                   (push (cons (let ((tm (second vals)))
                                 (cond ((blobp tm) tm)
                                       ((stringp tm) (utf8-encode tm))
                                       (t (make-octets 0))))
                               (third vals))
                         out))
                 :probe (list segid)
                 :cmp (lambda (vals probe) (compare-values (first vals) (first probe)))))
    (nreverse out)))

(defun fts-idx-put (fts segid term-bytes pgno)
  (let* ((tb (fts-idx-table fts))
         (*index-cmp* (index-full-cmp tb (find-if #'index-pk-index (table-indexes tb)))))
    (index-insert (table-owner tb) (table-root tb) (list segid (coerce term-bytes '(simple-array (unsigned-byte 8) (*))) pgno))))

(defun fts-idx-delete-segment (fts segid)
  (let* ((tb (fts-idx-table fts))
         (*index-cmp* (index-full-cmp tb (find-if #'index-pk-index (table-indexes tb)))))
    (dolist (e (fts-idx-entries fts segid))
      (index-delete (table-owner tb) (table-root tb) (list segid (car e) (cdr e))))))

;;; ------------------------------------------------------------------
;;; %_config

(defun fts-load-config (fts)
  (unless (fts-config-loaded fts)
    (setf (fts-config-loaded fts) t)
    (let ((tb (fts-shadow fts "config")))
      (map-index (table-owner tb) (table-root tb)
                 (lambda (vals)
                   (let ((k (first vals)) (v (second vals)))
                     (when (stringp k)
                       (fts-apply-config fts k v nil))))))
    (let ((s (fts-data-get fts +fts5-structure-id+)))
      (when (and s (>= (length s) 4)) (setf (fts-cookie fts) (get-u32 s 0))))))

(defun fts-apply-config (fts k v strict)
  "Set config K to V in FTS; with STRICT, reject bad values."
  (flet ((int (lo &optional hi)
           (if (and (integerp v) (>= v lo) (or (null hi) (<= v hi)))
               v
               (if strict (sql-error "SQL logic error") nil))))
    (let ((k (string-downcase-ascii k)))
      (cond ((string= k "pgsz") (let ((x (int 32 65536))) (when x (setf (fts-pgsz fts) x))))
            ((string= k "automerge") (let ((x (int 0 64))) (when x (setf (fts-automerge fts) (if (= x 1) 4 x)))))
            ((string= k "crisismerge") (let ((x (int 0))) (when x (setf (fts-crisismerge fts) (if (<= x 1) 16 x)))))
            ((string= k "usermerge") (let ((x (int 2 16))) (when x (setf (fts-usermerge fts) x))))
            ((string= k "hashsize") (let ((x (int 1))) (when x (setf (fts-hashsize fts) x))))
            ((string= k "rank") (if (and (stringp v) (parse-rank-spec v))
                                    (setf (fts-rank fts) v)
                                    (when strict (sql-error "SQL logic error"))))
            ((string= k "version") (unless (eql v 4) (sql-error "invalid fts5 file format (found ~a, expected 4) - run 'rebuild'" v)))
            (t (when strict (sql-error "SQL logic error")))))))

(defun fts-set-config (fts k v)
  (fts-load-config fts)
  (fts-apply-config fts k v t)
  (let* ((tb (fts-shadow fts "config"))
         (*index-cmp* (index-full-cmp tb (find-if #'index-pk-index (table-indexes tb)))))
    ;; replace the (k v) row
    (let ((old nil))
      (map-index (table-owner tb) (table-root tb)
                 (lambda (vals) (when (equal (first vals) k) (setf old vals))))
      (when old (index-delete (table-owner tb) (table-root tb) old))
      (index-insert (table-owner tb) (table-root tb) (list k v))))
  ;; as SQLite: a config change bumps the cookie in the structure record
  (let ((s (fts-read-structure fts)))
    (setf (fts-cookie fts) (ldb (byte 32 0) (1+ (fts-cookie fts))))
    (fts-write-structure fts s)))

;;; ------------------------------------------------------------------
;;; The structure record

(defstruct (fseg (:constructor make-fseg (id first last))) id first last)

(defstruct (fstruct (:conc-name fst-))
  (write-counter 0)
  (levels (make-array 0 :adjustable t :fill-pointer 0)))   ; of (nmerge . list-of-fseg)

(defun fst-level (s i) (aref (fst-levels s) i))
(defun fst-nlevel (s) (length (fst-levels s)))
(defun fst-segments (s) (loop for l across (fst-levels s) append (cdr l)))

(defun fts-read-structure (fts)
  (let ((b (fts-data-get fts +fts5-structure-id+))
        (s (make-fstruct)))
    (when (and b (> (length b) 4))
      (let ((off 4) nlevel nseg)
        (multiple-value-setq (nlevel off) (read-fts-varint b off))
        (multiple-value-setq (nseg off) (read-fts-varint b off))
        (when (< off (length b))
          (multiple-value-bind (wc o) (read-fts-varint b off)
            (setf (fst-write-counter s) wc off o)))
        (dotimes (i nlevel)
          (let (nmerge n segs)
            (multiple-value-setq (nmerge off) (read-fts-varint b off))
            (multiple-value-setq (n off) (read-fts-varint b off))
            (dotimes (j n)
              (let (id first last)
                (multiple-value-setq (id off) (read-fts-varint b off))
                (multiple-value-setq (first off) (read-fts-varint b off))
                (multiple-value-setq (last off) (read-fts-varint b off))
                (push (make-fseg id first last) segs)))
            (vector-push-extend (cons nmerge (nreverse segs)) (fst-levels s))))
        nseg))
    s))

(defun fts-write-structure (fts s)
  ;; trailing empty levels go (fts5StructureWrite writes nLevel as it is,
  ;; but a level count never shrinks in SQLite; keep them)
  (let ((buf (new-buf)))
    (let ((c (fts-cookie fts)))
      (dolist (sh '(24 16 8 0)) (vector-push-extend (ldb (byte 8 sh) c) buf)))
    (buf-varint buf (fst-nlevel s))
    (buf-varint buf (length (fst-segments s)))
    (buf-varint buf (fst-write-counter s))
    (loop for (nmerge . segs) across (fst-levels s)
          do (buf-varint buf nmerge)
             (buf-varint buf (length segs))
             (dolist (g segs)
               (buf-varint buf (fseg-id g)) (buf-varint buf (fseg-first g)) (buf-varint buf (fseg-last g))))
    (fts-data-put fts +fts5-structure-id+ buf)))

(defun fts-alloc-segid (s &optional also-used)
  (let ((used (append (mapcar #'fseg-id also-used) (mapcar #'fseg-id (fst-segments s)))))
    (loop for i from 1 unless (member i used) return i)))

(defun fts-ensure-level (s i)
  (loop while (<= (fst-nlevel s) i) do (vector-push-extend (cons 0 '()) (fst-levels s))))

(defun fseg-size (g) (1+ (- (fseg-last g) (fseg-first g))))

(defun fts-promote (s ilvl)
  "fts5StructurePromote: after writing the newest segment of level ILVL."
  (let ((segs (cdr (fst-level s ilvl))))
    (when segs
      (let* ((new (car (last segs)))
             (szseg (fseg-size new))
             (itst (loop for i downfrom (1- ilvl) to 0
                         unless (null (cdr (fst-level s i))) return i))
             (ipromote ilvl) (szpromote szseg))
        (when itst
          (let ((szmax (reduce #'max (mapcar #'fseg-size (cdr (fst-level s itst))) :initial-value 0)))
            (when (>= szmax szseg) (setf ipromote itst szpromote szmax))))
        ;; fts5StructurePromoteTo
        (when (zerop (car (fst-level s ipromote)))
          (loop for il from (1+ ipromote) below (fst-nlevel s)
                do (let ((lvl (fst-level s il)))
                     (unless (zerop (car lvl)) (return))
                     (loop while (cdr lvl)
                           do (let ((g (car (last (cdr lvl)))))
                                (when (> (fseg-size g) szpromote) (return-from fts-promote nil))
                                (setf (cdr lvl) (butlast (cdr lvl)))
                                (push g (cdr (fst-level s ipromote))))))))))))

;;; ------------------------------------------------------------------
;;; Averages: nRow and per-column token totals

(defun fts-read-totals (fts)
  (let ((b (fts-data-get fts +fts5-averages-id+))
        (n (length (fts-columns fts))))
    (let ((totals (make-array n :initial-element 0)) (nrow 0))
      (when (and b (plusp (length b)))
        (let ((off 0))
          (multiple-value-setq (nrow off) (read-fts-varint b off))
          (dotimes (i n)
            (when (< off (length b))
              (multiple-value-bind (v o) (read-fts-varint b off)
                (setf (aref totals i) v off o))))))
      (cons nrow totals))))

(defun fts-ensure-totals (fts)
  (or (fts-totals fts)
      (setf (fts-totals fts) (fts-read-totals fts))))

(defun fts-write-totals (fts)
  (let ((tt (fts-totals fts)) (buf (new-buf)))
    (when tt
      (buf-varint buf (car tt))
      (loop for v across (cdr tt) do (buf-varint buf v))
      (fts-data-put fts +fts5-averages-id+ buf))))

;;; ------------------------------------------------------------------
;;; Pending writes

(defstruct (pentry (:constructor make-pentry ())) (del nil) (pos '()) (present nil))

(defun fts-begin-write (fts delete-p rowid)
  "sqlite3Fts5IndexBeginWrite: flush when rowids would repeat or go back."
  (let ((last (fts-pending-rowid fts)))
    (when (and last (or (< rowid last)
                        (and (= rowid last) (not (fts-pending-delete fts)))
                        (> (fts-pending-bytes fts) (fts-hashsize fts))))
      (fts-flush fts)))
  (setf (fts-pending-rowid fts) rowid (fts-pending-delete fts) delete-p))

(defun fts-pending-entry (fts key rowid)
  (let ((h (or (gethash key (fts-pending fts))
               (setf (gethash key (fts-pending fts)) (make-hash-table)))))
    (or (gethash rowid h) (setf (gethash rowid h) (make-pentry)))))

(defun fts-pending-write (fts rowid col pos token delete-p)
  "Record TOKEN at (COL, POS) of ROWID, or its deletion."
  (flet ((note (key)
           (let ((e (fts-pending-entry fts key rowid)))
             (incf (fts-pending-bytes fts) (+ 8 (length key)))
             (if delete-p
                 (setf (pentry-del e) t)
                 (progn (setf (pentry-present e) t)
                        (push (+ (ash col 32) pos) (pentry-pos e)))))))
    (note (fts-term-key #\0 token))
    (loop for n in (fts-prefixes fts)
          for i from 1
          do (let ((k (prefix-key i token n))) (when k (note k))))))

(defun encode-poslist (fts positions)
  "The position list bytes for POSITIONS (col<<32|off, ascending, may repeat)."
  (let ((buf (new-buf)) (prev 0))
    (ecase (fts-detail fts)
      (:full
       (dolist (p (remove-duplicates positions))
         (unless (= (logand p (ash #x7fffffff 32)) (logand prev (ash #x7fffffff 32)))
           (vector-push-extend 1 buf)
           (buf-varint buf (ash p -32))
           (setf prev (logand p (ash #x7fffffff 32))))
         (buf-varint buf (+ (- p prev) 2))
         (setf prev p)))
      (:column
       (dolist (c (remove-duplicates (mapcar (lambda (p) (ash p -32)) positions)))
         (buf-varint buf (+ (- c prev) 2))
         (setf prev c))))
    buf))

(defun fts-pending-doclists (fts)
  "Sorted list of (key . doclist-bytes) from the pending buffer."
  (let ((out '()))
    (maphash (lambda (key h)
               (let ((buf (new-buf)) (prev nil))
                 (dolist (rowid (sort (loop for r being the hash-keys of h collect r) #'<))
                   (let ((e (gethash rowid h)))
                     (buf-varint buf (if prev (- rowid prev) rowid))
                     (setf prev rowid)
                     (if (eq (fts-detail fts) :none)
                         (when (pentry-del e)
                           (vector-push-extend 0 buf)
                           (when (pentry-present e) (vector-push-extend 0 buf)))
                         (let ((pl (if (pentry-present e) (encode-poslist fts (reverse (pentry-pos e))) (new-buf))))
                           (buf-varint buf (+ (* 2 (length pl)) (if (pentry-del e) 1 0)))
                           (buf-bytes buf pl)))))
                 (push (cons key buf) out)))
             (fts-pending fts))
    (sort out #'string< :key #'car)))

;;; ------------------------------------------------------------------
;;; The leaf writer (fts5SegWriter)

(defstruct (segw (:conc-name sw-))
  fts segid
  (pgno 1)
  (buf (let ((b (new-buf))) (dotimes (i 4) (vector-push-extend 0 b)) b))
  (pgidx (new-buf))
  (prev-pgidx 0)
  (term "")                  ; last term written (byte string)
  (first-term-in-page t) (first-rowid-in-page t) (first-rowid-in-doclist t)
  (prev-rowid 0)
  (bt-page 1) (bt-term "")   ; the pending %_idx entry
  (leaves 0))

(defun sw-flush-leaf (w)
  (let ((buf (sw-buf w)))
    (setf (aref buf 2) (ldb (byte 8 8) (length buf)) (aref buf 3) (ldb (byte 8 0) (length buf)))
    (unless (sw-first-term-in-page w) (buf-bytes buf (sw-pgidx w)))
    (fts-data-put (sw-fts w) (segment-rowid (sw-segid w) (sw-pgno w)) buf)
    (setf (sw-buf w) (let ((b (new-buf))) (dotimes (i 4) (vector-push-extend 0 b)) b)
          (sw-pgidx w) (new-buf)
          (sw-prev-pgidx w) 0)
    (incf (sw-pgno w))
    (incf (sw-leaves w))
    (setf (sw-first-term-in-page w) t (sw-first-rowid-in-page w) t)))

(defun sw-flush-btree (w)
  (when (plusp (sw-bt-page w))
    (fts-idx-put (sw-fts w) (sw-segid w) (key-bytes (sw-bt-term w)) (ash (sw-bt-page w) 1))
    (setf (sw-bt-page w) 0)))

(defun common-prefix (a b)
  (let ((n (min (length a) (length b))))
    (or (mismatch a b :end1 n :end2 n) n)))

(defun sw-append-term (w key)
  (let* ((pgsz (fts-pgsz (sw-fts w)))
         (nterm (length key)))
    (when (>= (+ (length (sw-buf w)) (length (sw-pgidx w)) nterm 2) pgsz)
      (when (> (length (sw-buf w)) 4) (sw-flush-leaf w)))
    (buf-varint (sw-pgidx w) (- (length (sw-buf w)) (sw-prev-pgidx w)))
    (setf (sw-prev-pgidx w) (length (sw-buf w)))
    (let ((nprefix 0))
      (if (sw-first-term-in-page w)
          (unless (= (sw-pgno w) 1)
            ;; a b-tree key for this leaf: the shortest prefix of the term
            ;; greater than the previous one
            (let ((n (if (plusp (length (sw-term w)))
                         (1+ (common-prefix (sw-term w) key))
                         nterm)))
              (sw-flush-btree w)
              (setf (sw-bt-term w) (subseq key 0 (min n nterm)) (sw-bt-page w) (sw-pgno w))))
          (progn (setf nprefix (common-prefix (sw-term w) key))
                 (buf-varint (sw-buf w) nprefix)))
      (buf-varint (sw-buf w) (- nterm nprefix))
      (loop for i from nprefix below nterm do (vector-push-extend (char-code (char key i)) (sw-buf w))))
    (setf (sw-term w) key
          (sw-first-term-in-page w) nil
          (sw-first-rowid-in-page w) nil
          (sw-first-rowid-in-doclist w) t)))

(defun sw-append-rowid (w rowid)
  (when (>= (+ (length (sw-buf w)) (length (sw-pgidx w))) (fts-pgsz (sw-fts w)))
    (sw-flush-leaf w))
  (when (sw-first-rowid-in-page w)
    (let ((n (length (sw-buf w))))
      (setf (aref (sw-buf w) 0) (ldb (byte 8 8) n) (aref (sw-buf w) 1) (ldb (byte 8 0) n))))
  (buf-varint (sw-buf w) (if (or (sw-first-rowid-in-doclist w) (sw-first-rowid-in-page w))
                             rowid
                             (- rowid (sw-prev-rowid w))))
  (setf (sw-prev-rowid w) rowid (sw-first-rowid-in-doclist w) nil (sw-first-rowid-in-page w) nil))

(defun sw-append-poslist-data (w data)
  "fts5WriteAppendPoslistData: spill DATA across leaves, whole varints only."
  (let ((pgsz (fts-pgsz (sw-fts w))) (a 0) (n (length data)))
    (loop while (>= (+ (length (sw-buf w)) (length (sw-pgidx w)) n) pgsz)
          do (let ((nreq (- pgsz (length (sw-buf w)) (length (sw-pgidx w)))) (ncopy 0))
               (loop while (< ncopy nreq) do (setf ncopy (- (varint-size data (+ a ncopy)) a)))
               (buf-bytes (sw-buf w) data a (+ a ncopy))
               (incf a ncopy) (decf n ncopy)
               (sw-flush-leaf w)))
    (when (plusp n) (buf-bytes (sw-buf w) data a (+ a n)))))

(defun poslist-prefix (data start nmax)
  "fts5PoslistPrefix: bytes of whole varints from START fitting in NMAX (at least one)."
  (let ((ret (- (varint-size data start) start)))
    (when (< ret nmax)
      (loop (let ((i (- (varint-size data (+ start ret)) (+ start ret))))
              (when (> (+ ret i) nmax) (return))
              (incf ret i)
              (when (>= (+ start ret) (length data)) (return)))))
    ret))

(defun sw-flush-doclist (w doclist)
  "Write a whole pending doclist (fts5FlushOneHash's copy loop)."
  (let* ((fts (sw-fts w)) (pgsz (fts-pgsz fts)) (none (eq (fts-detail fts) :none)))
    (if (>= pgsz (+ (length (sw-buf w)) (length (sw-pgidx w)) (length doclist) 1))
        (buf-bytes (sw-buf w) doclist)
        (let ((off 0) (rowid 0) (n (length doclist)))
          (loop while (< off n)
                do (multiple-value-bind (delta o) (read-fts-varint doclist off)
                     (setf off o rowid (+ rowid delta))
                     (if (sw-first-rowid-in-page w)
                         (let ((m (length (sw-buf w))))
                           (setf (aref (sw-buf w) 0) (ldb (byte 8 8) m) (aref (sw-buf w) 1) (ldb (byte 8 0) m))
                           (buf-varint (sw-buf w) rowid)
                           (setf (sw-first-rowid-in-page w) nil))
                         (buf-varint (sw-buf w) delta))
                     (if none
                         (progn
                           (when (and (< off n) (zerop (aref doclist off)))
                             (vector-push-extend 0 (sw-buf w)) (incf off)
                             (when (and (< off n) (zerop (aref doclist off)))
                               (vector-push-extend 0 (sw-buf w)) (incf off)))
                           (when (>= (+ (length (sw-buf w)) (length (sw-pgidx w))) pgsz)
                             (sw-flush-leaf w)))
                         (multiple-value-bind (sz o2) (read-fts-varint doclist off)
                           (let ((ncopy (+ (- o2 off) (ash sz -1))))
                             (if (<= (+ (length (sw-buf w)) (length (sw-pgidx w)) ncopy) pgsz)
                                 (buf-bytes (sw-buf w) doclist off (+ off ncopy))
                                 (let ((ipos 0))
                                   (loop
                                     (let* ((nspace (- pgsz (length (sw-buf w)) (length (sw-pgidx w))))
                                            (k (if (<= (- ncopy ipos) nspace)
                                                   (- ncopy ipos)
                                                   (poslist-prefix doclist (+ off ipos) nspace))))
                                       (buf-bytes (sw-buf w) doclist (+ off ipos) (+ off ipos k))
                                       (incf ipos k)
                                       (when (>= (+ (length (sw-buf w)) (length (sw-pgidx w))) pgsz)
                                         (sw-flush-leaf w))
                                       (when (>= ipos ncopy) (return))))))
                             (incf off ncopy))))))))))

(defun sw-finish (w)
  "Write the last leaf and %_idx entry; returns the last page number (0: empty)."
  (if (and (sw-first-term-in-page w) (= (length (sw-buf w)) 4) (= (sw-pgno w) 1))
      0
      (progn
        (when (> (length (sw-buf w)) 4) (sw-flush-leaf w))
        (sw-flush-btree w)
        (1- (sw-pgno w)))))

;;; ------------------------------------------------------------------
;;; Flushing the pending buffer as a new segment

(defun fts-flush (fts)
  "Write pending terms as a new level-0 segment; then promote and merge."
  (when (plusp (hash-table-count (fts-pending fts)))
    (let* ((s (fts-read-structure fts))
           (segid (fts-alloc-segid s))
           (w (make-segw :fts fts :segid segid)))
      (dolist (kd (fts-pending-doclists fts))
        (sw-append-term w (car kd))
        (sw-flush-doclist w (cdr kd)))
      (let ((last (sw-finish w)))
        (clrhash (fts-pending fts))
        (setf (fts-pending-rowid fts) nil (fts-pending-bytes fts) 0)
        (when (plusp last)
          (fts-ensure-level s 0)
          (setf (cdr (fst-level s 0)) (append (cdr (fst-level s 0)) (list (make-fseg segid 1 last))))
          (fts-promote s 0)
          (fts-run-merges fts s (sw-leaves w)))
        (fts-write-structure fts s))))
  (when (fts-totals fts) (fts-write-totals fts)))


;;; ------------------------------------------------------------------
;;; Reading segments

(defstruct (segr (:conc-name sr-))
  fts seg
  (pages (make-hash-table))   ; pgno -> leaf bytes
  idx)                        ; ((term-bytes . pgno-field) ...)

(defun sr-page (r pgno)
  (or (gethash pgno (sr-pages r))
      (setf (gethash pgno (sr-pages r))
            (or (fts-data-get (sr-fts r) (segment-rowid (fseg-id (sr-seg r)) pgno))
                (corrupt "database disk image is malformed")))))

(defun leaf-szleaf (b) (logior (ash (aref b 2) 8) (aref b 3)))
(defun leaf-rowid-off (b) (logior (ash (aref b 0) 8) (aref b 1)))

(defun leaf-term-offsets (b)
  "Offsets of the terms that begin on leaf B."
  (let ((off (leaf-szleaf b)) (acc 0) (out '()))
    (loop while (< off (length b))
          do (multiple-value-bind (v o) (read-fts-varint b off)
               (incf acc v) (push acc out) (setf off o)))
    (nreverse out)))

(defstruct (dlpart (:constructor make-dlpart (bytes start end abs))) bytes start end abs)

(defun sr-scan (r fn &key from-key)
  "Call FN with (key parts) for each term of the segment in order (from the
leaf holding FROM-KEY, if given).  PARTS are the doclist's byte ranges, one
per page, with the offset of an absolute rowid on each (or NIL).  FN
returns :stop to end the scan."
  (let* ((seg (sr-seg r))
         (first (fseg-first seg)) (last (fseg-last seg))
         (start first))
    (when from-key
      (unless (sr-idx r) (setf (sr-idx r) (fts-idx-entries (sr-fts r) (fseg-id seg))))
      (let ((kb (key-bytes from-key)))
        (dolist (e (sr-idx r))
          (when (not (plusp (compare-blobs (car e) kb)))
            (setf start (max first (ash (cdr e) -1)))))))
    ;; find the first term at or after START
    (let ((pg start))
      (loop while (and (<= pg last) (null (leaf-term-offsets (sr-page r pg)))) do (incf pg))
      (when (> pg last) (return-from sr-scan nil))
      (let* ((b (sr-page r pg))
             (offs (leaf-term-offsets b))
             (term "") (first-on-page t))
        (loop
          (let ((off (pop offs)))
            ;; the term
            (multiple-value-bind (nprefix o)
                (if first-on-page (values 0 off) (read-fts-varint b off))
              (multiple-value-bind (nsuffix o2) (read-fts-varint b o)
                (setf term (concatenate 'string (subseq term 0 nprefix)
                                        (map 'string #'code-char (subseq b o2 (+ o2 nsuffix)))))
                (setf first-on-page nil)
                ;; its doclist: to the next term, or across pages to the next term start
                (let ((parts '()) (dstart (+ o2 nsuffix)))
                  (if offs
                      (push (make-dlpart b dstart (first offs) nil) parts)
                      (progn
                        (push (make-dlpart b dstart (leaf-szleaf b) nil) parts)
                        (loop
                          (incf pg)
                          (when (> pg last) (return))
                          (setf b (sr-page r pg) offs (leaf-term-offsets b) first-on-page t)
                          (let ((ro (leaf-rowid-off b)))
                            (push (make-dlpart b 4 (if offs (first offs) (leaf-szleaf b))
                                               (and (plusp ro) ro))
                                  parts))
                          (when offs (return)))))
                  (when (eq (funcall fn term (nreverse parts)) :stop)
                    (return-from sr-scan nil))
                  (when (null offs) (return-from sr-scan nil))))))
          (when (and first-on-page (null offs)) (return-from sr-scan nil)))))))

(defun compare-blobs (a b)
  (let ((m (mismatch a b)))
    (cond ((null m) 0)
          ((>= m (length a)) -1)
          ((>= m (length b)) 1)
          ((< (aref a m) (aref b m)) -1)
          (t 1))))

(defun decode-doclist (fts parts)
  "List of (rowid del positions-bytes-or-nil) from a doclist's PARTS."
  (let ((out '()) (rowid 0) (first t) (none (eq (fts-detail fts) :none))
        (carry nil))                     ; a poslist continuing onto the next part
    (dolist (p parts)
      (let ((b (dlpart-bytes p)) (off (dlpart-start p)) (end (dlpart-end p)))
        (when carry
          ;; the rest of the previous poslist
          (destructuring-bind (need . acc) carry
            (let ((take (min need (- end off))))
              (buf-bytes acc b off (+ off take))
              (incf off take)
              (decf need take)
              (if (plusp need)
                  (setf carry (cons need acc))
                  (progn (setf (third (first out)) acc) (setf carry nil))))))
        (loop while (< off end)
              do (multiple-value-bind (v o) (read-fts-varint b off)
                   (setf rowid (if (or first (eql off (dlpart-abs p))) v (+ rowid v))
                         first nil off o))
                 (if none
                     (let ((del nil) (present t))
                       (when (and (< off end) (zerop (aref b off)))
                         (setf del t present nil) (incf off)
                         (when (and (< off end) (zerop (aref b off)))
                           (setf present t) (incf off)))
                       (push (list rowid del (and present :present)) out))
                     (multiple-value-bind (sz o) (read-fts-varint b off)
                       (setf off o)
                       (let* ((n (ash sz -1)) (del (logbitp 0 sz))
                              (take (min n (- end off)))
                              (acc (new-buf)))
                         (buf-bytes acc b off (+ off take))
                         (incf off take)
                         (push (list rowid del (if (zerop n) nil acc)) out)
                         (when (< take n) (setf carry (cons (- n take) acc)))))))))
    (nreverse out)))

(defun decode-positions (fts bytes)
  "Positions (col<<32|off), or for detail=column the columns, of a poslist."
  (let ((out '()) (off 0) (col 0) (prev 0) (n (length bytes)))
    (loop while (< off n)
          do (multiple-value-bind (v o) (read-fts-varint bytes off)
               (setf off o)
               (if (and (eq (fts-detail fts) :full) (= v 1))
                   (multiple-value-bind (c o2) (read-fts-varint bytes off)
                     (setf col c prev 0 off o2))
                   (progn (setf prev (+ prev (- v 2)))
                          (push (if (eq (fts-detail fts) :full) (+ (ash col 32) prev) prev) out)))))
    (nreverse out)))

;;; ------------------------------------------------------------------
;;; Merged views over all segments (newest entry wins)

(defun fts-segments-newest-first (s)
  (loop for i from 0 below (fst-nlevel s)
        append (reverse (cdr (fst-level s i)))))

(defun fts-term-entries (fts key &optional (s (fts-read-structure fts)))
  "rowid -> (del positions-bytes) for KEY, newest segment first, merged:
list of (rowid . poslist-bytes-or-:present) for rows that have the term."
  (let ((seen (make-hash-table)) (out '()))
    (dolist (seg (fts-segments-newest-first s))
      (let ((r (make-segr :fts fts :seg seg)))
        (sr-scan r (lambda (term parts)
                     (cond ((string= term key)
                            (dolist (e (decode-doclist fts parts))
                              (destructuring-bind (rowid del pl) e
                                (declare (ignore del))
                                (unless (nth-value 1 (gethash rowid seen))
                                  (setf (gethash rowid seen) t)
                                  (when pl (push (cons rowid pl) out)))))
                            :stop)
                           ((string> term key) :stop)))
                 :from-key key)))
    (sort out #'< :key #'car)))

(defun fts-prefix-terms (fts prefix-key &optional (s (fts-read-structure fts)))
  "All keys (across segments) beginning with PREFIX-KEY."
  (let ((keys (make-hash-table :test #'equal)))
    (dolist (seg (fts-segments-newest-first s))
      (let ((r (make-segr :fts fts :seg seg)) (n (length prefix-key)))
        (sr-scan r (lambda (term parts)
                     (declare (ignore parts))
                     (cond ((and (>= (length term) n) (string= prefix-key term :end2 n))
                            (setf (gethash term keys) t) nil)
                           ((string> term prefix-key) :stop)))
                 :from-key prefix-key)))
    (sort (loop for k being the hash-keys of keys collect k) #'string<)))

;;; ------------------------------------------------------------------
;;; Merging

(defun fts-merge-segments (fts s inputs out-level)
  "Merge INPUTS (fsegs, oldest first) into one new segment appended to
OUT-LEVEL of structure S.  Returns the new fseg (or NIL if empty)."
  (let* ((segid (fts-alloc-segid s inputs))
         (_ (fts-ensure-level s out-level))
         (oldest (and (null (cdr (fst-level s out-level)))
                      (= (fst-nlevel s) (1+ out-level))))
         (w (make-segw :fts fts :segid segid))
         (terms (make-hash-table :test #'equal))
         (none (eq (fts-detail fts) :none)))
    (declare (ignore _))
    ;; gather every term's doclist from every input, newest first
    (loop for seg in (reverse inputs)
          for age from 0
          do (let ((r (make-segr :fts fts :seg seg)))
               (sr-scan r (lambda (term parts)
                            (push (cons age (decode-doclist fts parts)) (gethash term terms))
                            nil))))
    (dolist (term (sort (loop for k being the hash-keys of terms collect k) #'string<))
      (let ((rows (make-hash-table)) (written nil))
        (dolist (src (sort (gethash term terms) #'< :key #'car))   ; newest first
          (dolist (e (cdr src))
            (unless (nth-value 1 (gethash (first e) rows))
              (setf (gethash (first e) rows) e))))
        (dolist (rowid (sort (loop for k being the hash-keys of rows collect k) #'<))
          (destructuring-bind (rid del pl) (gethash rowid rows)
            (unless (and (null pl) (or oldest (not del)))
              (unless written (sw-append-term w term) (setf written t))
              (sw-append-rowid w rid)
              ;; the oldest data has nothing older to mask: no delete flags
              (let ((del (and del (not oldest))))
                (if none
                    (when del
                      (vector-push-extend 0 (sw-buf w))
                      (when pl (vector-push-extend 0 (sw-buf w))))
                    (let ((bytes (if (and pl (not (eq pl :present))) pl (new-buf))))
                      (buf-varint (sw-buf w) (+ (* 2 (length bytes)) (if del 1 0)))
                      (sw-append-poslist-data w bytes)))))))))
    (let ((last (sw-finish w)))
      (dolist (seg inputs) (fts-remove-segment fts (fseg-id seg)))
      (when (plusp last)
        (let ((g (make-fseg segid 1 last)))
          (setf (cdr (fst-level s out-level)) (append (cdr (fst-level s out-level)) (list g)))
          g)))))

(defun fts-remove-segment (fts segid)
  (fts-data-delete-range fts (segment-rowid segid 0) (1- (segment-rowid (1+ segid) 0)))
  (fts-idx-delete-segment fts segid))

(defun fts-merge-level (fts s lvl)
  "Merge every segment of level LVL (and an unfinished merge's output) into LVL+1."
  (let* ((level (fst-level s lvl))
         (inputs (cdr level)))
    (fts-ensure-level s (1+ lvl))
    (when (plusp (car level))
      ;; SQLite left an incremental merge half done: its output segment (the
      ;; last on the next level) holds what it has merged so far
      (let ((out (car (last (cdr (fst-level s (1+ lvl)))))))
        (setf inputs (append (subseq inputs 0 (car level)) (list out))
              (cdr (fst-level s (1+ lvl))) (butlast (cdr (fst-level s (1+ lvl)))))
        (setf (cdr level) (nthcdr (car level) (cdr level)))))
    (setf (cdr level) (remove-if (lambda (g) (member g inputs)) (cdr level)) (car level) 0)
    ;; inputs oldest first: within a level, earlier segments are older
    (fts-merge-segments fts s inputs (1+ lvl))))

(defun fts-run-merges (fts s nleaf)
  "After a flush of NLEAF leaves: fts5IndexAutomerge, then fts5IndexCrisismerge.
Work is scheduled as SQLite schedules it (in 64-page units of the write
counter); a merge, once chosen, is done whole rather than incrementally."
  (when (plusp (fts-automerge fts))
    (let* ((wc (fst-write-counter s))
           (nwork (- (floor (+ wc nleaf) 64) (floor wc 64)))
           (nrem (* 64 nwork (fst-nlevel s))))
      (setf (fst-write-counter s) (+ wc nleaf))
      (fts-index-merge fts s nrem (fts-automerge fts))))
  (let ((lvl 0))
    (loop while (and (< lvl (fst-nlevel s)) (>= (length (cdr (fst-level s lvl))) (fts-crisismerge fts)))
          do (fts-merge-level fts s lvl)
             (fts-promote s (1+ lvl))
             (incf lvl))))

(defun fts-index-merge (fts s nrem nmin)
  "fts5IndexMerge: merge the fullest level while work remains."
  (loop while (plusp nrem)
        do (let ((best 0) (nbest 0))
             (loop for i below (fst-nlevel s)
                   do (let ((l (fst-level s i)))
                        (when (plusp (car l))
                          (when (> (car l) nbest) (setf best i nbest (car l)))
                          (return))
                        (when (> (length (cdr l)) nbest) (setf nbest (length (cdr l)) best i))))
             (when (and (< nbest nmin) (zerop (car (fst-level s best)))) (return))
             (let ((g (fts-merge-level fts s best)))
               (decf nrem (if g (fseg-size g) 1)))
             (fts-promote s (1+ best)))))

(defun fts-optimize (fts)
  "fts5 'optimize': merge every segment into one (sqlite3Fts5IndexOptimize)."
  (fts-flush fts)
  (let* ((s (fts-read-structure fts))
         (all (fst-segments s)))
    (when (>= (length all) 2)
      (let ((lvl (position-if (lambda (l) (= (length (cdr l)) (length all))) (fst-levels s))))
        (unless lvl
          ;; gather every segment, oldest first, on a new last level
          (let ((oldest-first (loop for i downfrom (1- (fst-nlevel s)) to 0 append (cdr (fst-level s i))))
                (new (make-fstruct :write-counter (fst-write-counter s))))
            (dotimes (i (min (1+ (fst-nlevel s)) 64)) (vector-push-extend (cons 0 '()) (fst-levels new)))
            (setf lvl (1- (fst-nlevel new))
                  (cdr (fst-level new lvl)) oldest-first
                  s new)))
        (fts-merge-level fts s lvl)
        (fts-write-structure fts s)))))
