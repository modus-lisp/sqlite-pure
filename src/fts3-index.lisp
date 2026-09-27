;;;; fts3-index.lisp — the FTS3/4 full-text index, in SQLite's format
;;;; (a port of fts3_write.c).
;;;;
;;;; The index is a set of segments, each a b-tree of terms: leaves in
;;;; <t>_segments (blockid -> block), described by a <t>_segdir row (level,
;;;; idx, start_block, leaves_end_block, end_block, root).  A segment small
;;;; enough to fit in its root has no leaves.  A leaf is a run of terms,
;;;; each "varint prefix, varint suffix-length, suffix, varint doclist-size,
;;;; doclist"; an interior node is "height, varint leftmost-child" then
;;;; terms, each separating consecutive children.  A doclist is "varint
;;;; docid-delta, position list" repeated; a position list is varints
;;;; position+2 (deltas), 0x01 col to change column, 0x00 at the end.  An
;;;; empty position list marks a deletion.  Varints here are little-endian
;;;; base-128 (not SQLite's record varints).
;;;;
;;;; Absolute level = (langid * nIndex + index) * 1024 + level, index 0
;;;; being the terms and 1.. the prefix indexes.  Writes collect in pending
;;;; term lists, flushed to a new level-0 segment at the end of each
;;;; statement (or when docids would go backwards, or the pending data
;;;; passes 1MB); a level with 16 segments is merged into one on the next
;;;; level; 'merge=' and 'automerge=' run SQLite's incremental merge.
;;;;
;;;; Byte-level structures are ported closely because the query evaluator
;;;; (fts3-eval.lisp) works on the same buffers the readers return, and
;;;; SQLite's results depend on some in-place edits of those buffers.

(in-package #:sqlite-pure)

(defconstant +fts3-merge-count+ 16)
(defconstant +fts3-segdir-maxlevel+ 1024)
(defconstant +fts3-node-padding+ 20)
(defconstant +fts3-buffer-padding+ 8)
(defconstant +fts3-max-appendable-height+ 16)
(defconstant +fts3-largest-int64+ (1- (expt 2 63)))
(defconstant +fts3-smallest-int64+ (- (expt 2 63)))

(deftype octets () '(simple-array (unsigned-byte 8) (*)))

(defstruct (fts3 (:conc-name f3-))
  name db module fts4-p
  columns notindexed              ; lists
  tokenizer
  content                         ; NIL: <t>_content; a string: content=
  languageid                      ; the languageid= column name, or NIL
  compress uncompress             ; function names, or NIL
  desc-p                          ; order=desc
  prefixes                        ; vector: 0 for the main index, then prefix lengths
  has-stat has-docsize
  (pgsz 4096) (node-size 4061)
  (autoincrmerge #xff) (leaf-add 0)
  pending                         ; vector of EQUAL hash tables, one per index
  (pending-data 0) (prev-docid 0) (prev-langid 0) (prev-delete nil)
  (max-pending (* 1024 1024))
  (txn-mark nil)
  read-fn)                        ; cached content query

(defun f3-ncol (f) (length (f3-columns f)))
(defun f3-nindex (f) (length (f3-prefixes f)))

;;; ------------------------------------------------------------------
;;; Varints (little-endian base 128)

(declaim (inline f3-varint-len))
(defun f3-varint-len (v)
  (let ((v (ldb (byte 64 0) v)) (n 0))
    (loop do (incf n) (setf v (ash v -7)) while (/= v 0))
    n))

(defun f3-put-varint (buf off v)
  "Write V at OFF of BUF; returns the new offset."
  (let ((v (ldb (byte 64 0) v)))
    (loop (let ((b (logand v #x7f)))
            (setf v (ash v -7))
            (if (zerop v)
                (progn (setf (aref buf off) b) (return (1+ off)))
                (progn (setf (aref buf off) (logior b #x80)) (incf off)))))))

(defun f3-get-varint-u (buf off)
  "(values unsigned-value next-offset), reading at most 10 bytes."
  (let ((v 0) (shift 0))
    (loop (let ((c (aref buf off)))
            (incf off)
            (setf v (logior v (ash (logand c #x7f) shift)))
            (when (or (zerop (logand c #x80)) (>= shift 63)) (return))
            (incf shift 7)))
    (values (ldb (byte 64 0) v) off)))

(declaim (inline f3-signed))
(defun f3-signed (u) (if (logbitp 63 u) (- u (expt 2 64)) u))

(defun f3-get-varint (buf off)
  (multiple-value-bind (u o) (f3-get-varint-u buf off) (values (f3-signed u) o)))

(defun f3-get-varint32 (buf off)
  "fts3GetVarint32: at most 5 bytes, into a non-negative int."
  (let ((c (aref buf off)))
    (if (< c #x80)
        (values c (1+ off))
        (let ((a (logand c #x7f)) (shift 7))
          (loop for i from 1 below 4
                do (let ((c (aref buf (+ off i))))
                     (setf a (logior a (ash (logand c #x7f) shift)))
                     (when (< c #x80) (return-from f3-get-varint32 (values a (+ off i 1))))
                     (incf shift 7)))
          (values (logior (logand a #x0fffffff) (ash (logand (aref buf (+ off 4)) 7) 28))
                  (+ off 5))))))

(defun f3-get-varint-bounded (buf off end)
  (let ((v 0) (shift 0))
    (loop (let ((c (if (< off end) (aref buf off) 0)))
            (incf off)
            (setf v (logior v (ash (logand c #x7f) shift)))
            (when (or (zerop (logand c #x80)) (>= shift 63)) (return))
            (incf shift 7)))
    (values (f3-signed (ldb (byte 64 0) v)) off)))

;;; Growable byte buffers

(defun f3-buf (&optional (n 64))
  (make-array n :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))

(defun f3-buf-varint (buf v)
  (let ((v (ldb (byte 64 0) v)))
    (loop (let ((b (logand v #x7f)))
            (setf v (ash v -7))
            (if (zerop v)
                (progn (vector-push-extend b buf) (return))
                (vector-push-extend (logior b #x80) buf))))))

(defun f3-buf-append (buf src &optional (start 0) (end (length src)))
  (loop for i from start below end do (vector-push-extend (aref src i) buf)))

(defun f3-padded (src &optional (start 0) (end (length src)) (pad +fts3-node-padding+))
  "A fresh simple octet vector holding SRC[START,END) followed by PAD zeros."
  (let ((b (make-array (+ (- end start) pad) :element-type '(unsigned-byte 8) :initial-element 0)))
    (replace b src :start2 start :end2 end)
    b))

(defun f3-memcmp (a aoff b boff n)
  (loop for i below n
        do (let ((x (aref a (+ aoff i))) (y (aref b (+ boff i))))
             (cond ((< x y) (return-from f3-memcmp -1))
                   ((> x y) (return-from f3-memcmp 1)))))
  0)

;;; Terms are byte strings (characters 0..255).
(defun f3-term-cmp (a b)
  "memcmp over the shorter length, then the length difference."
  (let* ((na (length a)) (nb (length b)) (n (min na nb)))
    (dotimes (i n (- na nb))
      (let ((x (char-code (char a i))) (y (char-code (char b i))))
        (cond ((< x y) (return -1))
              ((> x y) (return 1)))))))

(defun f3-prefix-compress (prev next)
  (let ((n 0))
    (loop while (and (< n (length prev)) (< n (length next)) (char= (char prev n) (char next n)))
          do (incf n))
    n))

;;; ------------------------------------------------------------------
;;; Shadow tables

(defun f3-shadow (f suffix &optional (must t))
  (or (find-table-in (f3-db f) (format nil "~a_~a" (f3-name f) suffix))
      (and must (corrupt "database disk image is malformed"))))

(defun f3-abs-level (f langid index level)
  (+ (* (+ (* langid (f3-nindex f)) index) +fts3-segdir-maxlevel+) level))

(defstruct (f3seg (:conc-name sd-)) level idx start leaves-end end root row)

(defun f3-segdir-row-to-seg (row)
  (make-f3seg :level (svref row 0) :idx (svref row 1)
              :start (let ((v (svref row 2))) (if (integerp v) v (f3-int-of v)))
              :leaves-end (let ((v (svref row 3))) (if (integerp v) v (f3-int-of v)))
              :end (svref row 4)
              :root (let ((v (svref row 5))) (cond ((blobp v) v) ((eq v :null) nil) (t (utf8-encode (value-to-text v)))))
              :row row))

(defun f3-int-of (v)
  "sqlite3_column_int64: integers as they are, text by its leading integer."
  (cond ((integerp v) v)
        ((eq v :null) 0)
        ((floatp v) (let ((x (value-to-integer v))) (if (integerp x) x 0)))
        (t (let* ((s (if (blobp v) (map 'string #'code-char v) (value-to-text v)))
                  (i 0) (n (length s)) (neg nil) (val 0))
             (loop while (and (< i n) (member (char s i) '(#\Space #\Tab #\Newline #\Return))) do (incf i))
             (when (and (< i n) (member (char s i) '(#\+ #\-)))
               (setf neg (char= (char s i) #\-)) (incf i))
             (loop while (and (< i n) (digit-char-p (char s i)))
                   do (setf val (+ (* val 10) (digit-char-p (char s i)))) (incf i))
             (let ((x (if neg (- val) val)))
               (max +fts3-smallest-int64+ (min +fts3-largest-int64+ x)))))))

(defun f3-segdirs (f &key level lo hi)
  "Segments (F3SEG) at absolute LEVEL (ordered by idx) or with level in
[LO,HI] (ordered by level DESC, idx ASC)."
  (let ((tb (f3-shadow f "segdir")) (out '()))
    (map-table-rows tb (lambda (row)
                         (let ((l (svref row 0)))
                           (when (and (integerp l)
                                      (if level (= l level) (<= lo l hi)))
                             (push (f3-segdir-row-to-seg (copy-seq row)) out)))))
    (if level
        (sort out #'< :key (lambda (s) (f3-int-of (sd-idx s))))
        (sort out (lambda (a b) (or (> (sd-level a) (sd-level b))
                                    (and (= (sd-level a) (sd-level b))
                                         (< (f3-int-of (sd-idx a)) (f3-int-of (sd-idx b))))))))))

(defun f3-all-segdir-rows (f)
  (let ((tb (f3-shadow f "segdir")) (out '()))
    (map-table-rows tb (lambda (row) (push (copy-seq row) out)))
    (nreverse out)))

(defun f3-segdir-write (f level idx start leaves-end end nleafdata root)
  "REPLACE INTO %_segdir VALUES(...)."
  (let* ((tb (f3-shadow f "segdir"))
         (rowid (1+ (or (table-max-rowid (table-owner tb) (table-root tb)) 0)))
         (endv (if (zerop nleafdata) end (format nil "~d ~d" end nleafdata))))
    (dolist (r (f3-all-segdir-rows f))
      (when (and (eql (svref r 0) level) (eql (svref r 1) idx))
        (delete-row tb r)))
    (let ((row (vector level idx start leaves-end endv
                       (coerce (or root (make-octets 0)) 'octets) rowid)))
      (write-row tb row))))

(defun f3-segdir-delete-if (f pred)
  (let ((tb (f3-shadow f "segdir")))
    (dolist (r (f3-all-segdir-rows f))
      (when (funcall pred r) (delete-row tb r)))))

(defun f3-segdir-update (f row &key (level (svref row 0)) (idx (svref row 1))
                                    (start (svref row 2)) (root (svref row 5)))
  (let ((tb (f3-shadow f "segdir"))
        (new (copy-seq row)))
    (setf (svref new 0) level (svref new 1) idx (svref new 2) start (svref new 5) root)
    (delete-row tb row)
    (write-row tb new)
    new))

(defun f3-segdir-max-level (f lo hi)
  "SELECT max(level) FROM %_segdir WHERE level BETWEEN LO AND HI (NIL if none)."
  (let ((m nil))
    (dolist (r (f3-all-segdir-rows f) m)
      (let ((l (svref r 0)))
        (when (and (integerp l) (<= lo l hi) (or (null m) (> l m))) (setf m l))))))

(defun f3-next-segment-index (f level)
  "(SELECT max(idx) FROM %_segdir WHERE level = ?) + 1, as an int (0 if none)."
  (let ((m nil))
    (dolist (r (f3-all-segdir-rows f))
      (when (eql (svref r 0) level)
        (let ((i (svref r 1)))
          (when (and (numberp i) (or (null m) (> i m))) (setf m i)))))
    (if m (f3-int-of (+ m 1)) 0)))

(defun f3-read-block (f blockid)
  "The block's bytes, padded; corrupt if missing."
  (let ((r (shadow-get (f3-shadow f "segments") blockid)))
    (unless r (corrupt "database disk image is malformed"))
    (let ((b (first r)))
      (cond ((blobp b) (values (f3-padded b) (length b)))
            ((stringp b) (let ((x (utf8-encode b))) (values (f3-padded x) (length x))))
            ((eq b :null) (corrupt "database disk image is malformed"))
            (t (let ((x (utf8-encode (value-to-text b)))) (values (f3-padded x) (length x))))))))

(defun f3-block-size (f blockid)
  (let ((r (shadow-get (f3-shadow f "segments") blockid)))
    (unless r (corrupt "database disk image is malformed"))
    (let ((b (first r)))
      (cond ((blobp b) (length b))
            ((eq b :null) 0)
            (t (length (utf8-encode (value-to-text b))))))))

(defun f3-write-block (f blockid bytes &optional (n (and bytes (length bytes))))
  "REPLACE INTO %_segments(blockid, block) VALUES(?, ?); BYTES NIL writes NULL."
  (shadow-put (f3-shadow f "segments") blockid
              (list (if bytes (coerce (subseq bytes 0 n) 'octets) :null))))

(defun f3-delete-blocks (f lo hi)
  (let ((tb (f3-shadow f "segments")) (ids '()))
    (catch :range-done
      (map-table (table-owner tb) (table-root tb)
                 (lambda (rowid payload) (declare (ignore payload))
                   (when (> rowid hi) (throw :range-done nil))
                   (when (>= rowid lo) (push rowid ids)))
                 :start lo))
    (dolist (id ids) (shadow-del tb id))))

(defun f3-next-block-id (f)
  (let ((tb (f3-shadow f "segments")))
    (1+ (or (table-max-rowid (table-owner tb) (table-root tb)) 0))))

(defun f3-stat-get (f id)
  (let ((tb (f3-shadow f "stat" nil)))
    (and tb (shadow-get tb id))))

(defun f3-stat-put (f id value)
  (shadow-put (f3-shadow f "stat") id (list value)))

(defun f3-clear-table (tb)
  (let ((ids '()))
    (map-table (table-owner tb) (table-root tb) (lambda (r p) (declare (ignore p)) (push r ids)))
    (dolist (r ids) (shadow-del tb r))))

;;; ------------------------------------------------------------------
;;; Pending terms

(defstruct (f3pending (:conc-name pl-))
  (data (f3-buf 100)) (last-docid 0) (last-col -1) (last-pos 0))

(defconstant +f3-hash-elem-size+ 40)

(defun f3-pending-list-append (p docid col pos)
  "fts3PendingListAppend: P may be NIL (a new list is made).  Returns P."
  (let ((p (or p (make-f3pending))))
    (when (or (zerop (fill-pointer (pl-data p))) (/= (pl-last-docid p) docid))
      (let ((delta (- docid (if (zerop (fill-pointer (pl-data p))) 0 (pl-last-docid p)))))
        (when (plusp (fill-pointer (pl-data p)))
          (vector-push-extend 0 (pl-data p)))
        (f3-buf-varint (pl-data p) delta)
        (setf (pl-last-col p) -1 (pl-last-pos p) 0 (pl-last-docid p) docid)))
    (when (and (> col 0) (/= (pl-last-col p) col))
      (f3-buf-varint (pl-data p) 1)
      (f3-buf-varint (pl-data p) col)
      (setf (pl-last-col p) col (pl-last-pos p) 0))
    (when (>= col 0)
      (f3-buf-varint (pl-data p) (+ 2 (- pos (pl-last-pos p))))
      (setf (pl-last-pos p) pos))
    p))

(defun f3-pending-add-one (f col pos hash key)
  (let ((pl (gethash key hash)))
    (when pl
      (decf (f3-pending-data f) (+ (fill-pointer (pl-data pl)) (length key) +f3-hash-elem-size+)))
    (setf pl (f3-pending-list-append pl (f3-prev-docid f) col pos))
    (setf (gethash key hash) pl)
    (incf (f3-pending-data f) (+ (fill-pointer (pl-data pl)) (length key) +f3-hash-elem-size+))))

(defun f3-pending-terms-add (f langid bytes col)
  "Tokenize BYTES (or NIL) into the pending terms; COL -1 records a deletion.
Returns the number of token positions (nWord)."
  (declare (ignore langid))
  (if (null bytes)
      0
      (let ((nword 0))
        (loop for (term nil nil pos) across (fts3-tokenize (f3-tokenizer f) bytes)
              do (when (>= pos nword) (setf nword (1+ pos)))
                 (when (or (< pos 0) (zerop (length term)))
                   (sql-error "SQL logic error"))
                 (f3-pending-add-one f col pos (aref (f3-pending f) 0) term)
                 (loop for i from 1 below (f3-nindex f)
                       for np = (aref (f3-prefixes f) i)
                       do (unless (< (length term) np)
                            (f3-pending-add-one f col pos (aref (f3-pending f) i) (subseq term 0 np)))))
        nword)))

(defun f3-pending-terms-docid (f delete-p langid docid)
  (when (or (< docid (f3-prev-docid f))
            (and (= docid (f3-prev-docid f)) (not (f3-prev-delete f)))
            (/= (f3-prev-langid f) langid)
            (> (f3-pending-data f) (f3-max-pending f)))
    (f3-pending-flush f))
  (setf (f3-prev-docid f) docid (f3-prev-langid f) langid (f3-prev-delete f) delete-p))

(defun f3-pending-clear (f)
  (loop for h across (f3-pending f) do (clrhash h))
  (setf (f3-pending-data f) 0))

(defun f3-pending-empty-p (f)
  (every (lambda (h) (zerop (hash-table-count h))) (f3-pending f)))

;;; ------------------------------------------------------------------
;;; Segment readers (Fts3SegReader)

(defstruct (f3reader (:conc-name rd-))
  (idx 0)                 ; age: larger is newer; the pending reader is the newest
  lookup root-only
  (start-block 0) (leaves-end-block 0) (end-block 0) (current-block 0)
  node (nnode 0)          ; aNode (NIL at EOF)
  (term (make-array 16 :element-type 'character :adjustable t :fill-pointer 0))
  doclist (ndoclist 0)    ; aDoclist offset into NODE (NIL before the first term)
  offset-list (noffset-list 0) (docid 0)
  pending-elems pending-p)

(defun f3-reader-new (age lookup start leaves-end end root)
  (when (and (zerop start) (/= leaves-end 0)) (corrupt "database disk image is malformed"))
  (let ((r (make-f3reader :idx age :lookup lookup :start-block start
                          :leaves-end-block leaves-end :end-block end)))
    (if (zerop start)
        (setf (rd-root-only r) t
              (rd-node r) (f3-padded (or root (make-octets 0)))
              (rd-nnode r) (length (or root #())))
        (setf (rd-current-block r) (1- start)))
    r))

(defun f3-reader-pending (f index term prefix-p)
  "sqlite3Fts3SegReaderPending: a reader over the pending terms of INDEX
matching TERM (a prefix when PREFIX-P), or NIL."
  (let* ((h (aref (f3-pending f) index))
         (elems (if prefix-p
                    (sort (loop for k being the hash-keys of h using (hash-value v)
                                when (or (zerop (length term))
                                         (and (>= (length k) (length term))
                                              (string= k term :end1 (length term))))
                                  collect (cons k v))
                          (lambda (a b) (minusp (f3-term-cmp (car a) (car b)))))
                    (let ((v (gethash term h))) (and v (list (cons term v)))))))
    (when elems
      (make-f3reader :idx #x7fffffff :pending-p t :pending-elems elems))))

(defun f3-reader-set-eof (r)
  (setf (rd-node r) nil))

(defun f3-reader-term (r) (rd-term r))

(defun f3-reader-next (f r)
  "fts3SegReaderNext: advance R to its next term (NODE NIL at EOF)."
  (let ((next (if (rd-doclist r) (+ (rd-doclist r) (rd-ndoclist r)) 0)))
    (when (or (null (rd-node r)) (>= next (rd-nnode r)))
      (when (rd-pending-p r)
        (let ((e (pop (rd-pending-elems r))))
          (setf (rd-node r) nil)
          (when e
            (let* ((data (pl-data (cdr e)))
                   (n (1+ (fill-pointer data)))
                   (copy (make-array (+ n +fts3-node-padding+) :element-type '(unsigned-byte 8) :initial-element 0)))
              (replace copy data)
              (setf (fill-pointer (rd-term r)) 0)
              (loop for c across (car e) do (vector-push-extend c (rd-term r)))
              (setf (rd-node r) copy (rd-nnode r) n (rd-doclist r) 0 (rd-ndoclist r) n
                    (rd-offset-list r) nil)))
          (return-from f3-reader-next nil)))
      (f3-reader-set-eof r)
      (when (rd-root-only r) (return-from f3-reader-next nil))
      (when (>= (rd-current-block r) (rd-leaves-end-block r)) (return-from f3-reader-next nil))
      (multiple-value-bind (b n) (f3-read-block f (incf (rd-current-block r)))
        (setf (rd-node r) b (rd-nnode r) n (rd-doclist r) nil next 0)))
    (let ((node (rd-node r)) nprefix nsuffix)
      (multiple-value-setq (nprefix next) (f3-get-varint32 node next))
      (multiple-value-setq (nsuffix next) (f3-get-varint32 node next))
      (when (or (<= nsuffix 0) (< (- (rd-nnode r) next) nsuffix) (> nprefix (fill-pointer (rd-term r))))
        (corrupt "database disk image is malformed"))
      (setf (fill-pointer (rd-term r)) nprefix)
      (loop for i from next below (+ next nsuffix)
            do (vector-push-extend (code-char (aref node i)) (rd-term r)))
      (incf next nsuffix)
      (multiple-value-bind (nd o) (f3-get-varint32 node next)
        (setf (rd-ndoclist r) nd (rd-doclist r) o (rd-offset-list r) nil))
      (when (or (> (rd-ndoclist r) (- (rd-nnode r) (rd-doclist r)))
                (zerop (rd-ndoclist r))
                (/= 0 (aref node (+ (rd-doclist r) (rd-ndoclist r) -1))))
        (corrupt "database disk image is malformed"))
      nil)))

(defun f3-doclist-prev (desc-idx buf start n iter docid)
  "sqlite3Fts3DoclistPrev over BUF[START, START+N): ITER is NIL or the offset
of the current entry's docid-varint end.  Returns (values iter docid nlist eof)."
  (if (null iter)
      (let ((i start) (end (+ start n)) (d 0) (next nil) (mul 1))
        (loop while (< i end)
              do (multiple-value-bind (delta o) (f3-get-varint buf i)
                   (setf d (+ d (* mul delta)) i o next o)
                   (setf i (f3-poslist-skip buf i))
                   (loop while (and (< i end) (zerop (aref buf i))) do (incf i))
                   (setf mul (if desc-idx -1 1))))
        (values next (f3-signed (ldb (byte 64 0) d)) (- end next) nil))
      (let ((mul (if desc-idx -1 1)))
        (multiple-value-bind (p delta) (f3-reverse-varint buf iter start)
          (let ((d (f3-signed (ldb (byte 64 0) (- docid (* mul delta))))))
            (if (= p start)
                (values p d 0 t)
                (let ((save p))
                  (let ((np (f3-reverse-poslist buf start p)))
                    (values np d (- save np) nil)))))))))

(defun f3-reverse-varint (buf pp start)
  "fts3GetReverseVarint: PP is just past a varint; returns (values start-of-varint value)."
  (let ((p (- pp 2)))
    (loop while (and (>= p start) (logtest (aref buf p) #x80)) do (decf p))
    (incf p)
    (values p (f3-get-varint buf p))))

(defun f3-reverse-poslist (buf start pp)
  "fts3ReversePoslist: PP points at a docid varint; returns the offset of the
start of the preceding position list."
  (let ((p (- pp 2)) (c 0))
    (loop while (and (> p start) (progn (setf c (aref buf p)) (decf p) (zerop c))))
    (loop while (and (> p start) (or (logtest (aref buf p) #x80) (/= c 0)))
          do (setf c (aref buf p)) (decf p))
    (when (or (> p start) (and (zerop c) (> pp (+ p 2))))
      (setf p (+ p 2)))
    (loop while (logtest (aref buf p) #x80) do (incf p))
    (1+ p)))

(defun f3-poslist-skip (buf p)
  "fts3PoslistCopy without output: the offset just past the 0x00 ending the
position list at P."
  (let ((c 0))
    (loop while (/= 0 (logior (aref buf p) c))
          do (setf c (logand (aref buf p) #x80)) (incf p))
    (1+ p)))

(defun f3-columnlist-skip (buf p)
  "fts3ColumnlistCopy without output: the offset of the 0x00/0x01 ending the
column list at P."
  (let ((c 0))
    (loop while (/= 0 (logand #xfe (logior (aref buf p) c)))
          do (setf c (logand (aref buf p) #x80)) (incf p))
    p))

(defun f3-reader-first-docid (f r)
  (if (and (f3-desc-p f) (rd-pending-p r))
      (multiple-value-bind (iter docid nlist) (f3-doclist-prev nil (rd-node r) (rd-doclist r) (rd-ndoclist r) nil 0)
        (setf (rd-offset-list r) iter (rd-docid r) docid (rd-noffset-list r) nlist))
      (multiple-value-bind (d o) (f3-get-varint (rd-node r) (rd-doclist r))
        (setf (rd-docid r) d (rd-offset-list r) o))))

(defun f3-reader-next-docid (f r)
  "fts3SegReaderNextDocid: returns (values poslist-offset poslist-length)
for the current entry and advances."
  (let ((node (rd-node r)))
    (if (and (f3-desc-p f) (rd-pending-p r))
        (let ((pl (rd-offset-list r)) (npl (1- (rd-noffset-list r))))
          (multiple-value-bind (iter docid nlist eof)
              (f3-doclist-prev nil node (rd-doclist r) (rd-ndoclist r) (rd-offset-list r) (rd-docid r))
            (setf (rd-docid r) docid (rd-noffset-list r) nlist
                  (rd-offset-list r) (if eof nil iter)))
          (values pl npl))
        (let* ((pl (rd-offset-list r))
               (p (1- (f3-poslist-skip node pl)))
               (end (+ (rd-doclist r) (rd-ndoclist r))))
          (incf p)
          (let ((npl (- p pl 1)))
            (loop while (and (< p end) (zerop (aref node p))) do (incf p))
            (if (>= p end)
                (setf (rd-offset-list r) nil)
                (multiple-value-bind (delta o) (f3-get-varint-u node p)
                  (setf (rd-offset-list r) o
                        (rd-docid r) (f3-signed (ldb (byte 64 0) (if (f3-desc-p f)
                                                                     (- (rd-docid r) delta)
                                                                     (+ (rd-docid r) delta)))))))
            (values pl npl))))))

;;; Comparisons (fts3SegReaderCmp & co.)

(defun f3-reader-cmp (a b)
  (let ((rc (if (and (rd-node a) (rd-node b))
                (let ((c (f3-term-cmp (rd-term a) (rd-term b))))
                  c)
                (- (if (rd-node a) 0 1) (if (rd-node b) 0 1)))))
    (if (zerop rc) (- (rd-idx b) (rd-idx a)) rc)))

(defun f3-reader-doclist-cmp (a b)
  (let ((rc (- (if (rd-offset-list a) 0 1) (if (rd-offset-list b) 0 1))))
    (if (zerop rc)
        (if (= (rd-docid a) (rd-docid b))
            (- (rd-idx b) (rd-idx a))
            (if (> (rd-docid a) (rd-docid b)) 1 -1))
        rc)))

(defun f3-reader-doclist-cmp-rev (a b)
  (let ((rc (- (if (rd-offset-list a) 0 1) (if (rd-offset-list b) 0 1))))
    (if (zerop rc)
        (if (= (rd-docid a) (rd-docid b))
            (- (rd-idx b) (rd-idx a))
            (if (< (rd-docid a) (rd-docid b)) 1 -1))
        rc)))

(defun f3-reader-term-cmp (r term)
  (if (rd-node r) (f3-term-cmp (rd-term r) term) 0))

(defun f3-reader-sort (v n nsuspect cmp)
  (when (= nsuspect n) (decf nsuspect))
  (loop for i from (1- nsuspect) downto 0
        do (loop for j from i below (1- n)
                 do (when (minusp (funcall cmp (aref v j) (aref v (1+ j)))) (return))
                    (rotatef (aref v j) (aref v (1+ j))))))

;;; ------------------------------------------------------------------
;;; Multi-segment readers (Fts3MultiSegReader)

(defconstant +f3f-require-pos+ 1)
(defconstant +f3f-ignore-empty+ 2)
(defconstant +f3f-column-filter+ 4)
(defconstant +f3f-prefix+ 8)
(defconstant +f3f-scan+ 16)
(defconstant +f3f-first+ 32)

(defstruct (f3msr (:conc-name msr-))
  (segments (make-array 0 :adjustable t :fill-pointer 0))
  (nadvance 0) restart lookup
  (flags 0) filter-term (filter-col 0) filter-set
  term                                   ; current term (a byte string)
  doclist-buf (doclist-off 0) (ndoclist 0)
  (buffer (make-octets 0))
  (col-filter -1))

(defun msr-nsegment (m) (fill-pointer (msr-segments m)))

(defun f3-msr-add (m r) (vector-push-extend r (msr-segments m)))

(defun f3-seg-reader-cursor (f langid index level term prefix-p scan-p &optional (m (make-f3msr)))
  "fts3SegReaderCursor: LEVEL is :all, :pending or a relative level.  Adds
readers to M (a new one by default) and returns it."
  (progn
    (when (and (member level '(:all :pending)) (= (f3-prev-langid f) langid))
      (let ((r (f3-reader-pending f index (or term "") (or prefix-p scan-p))))
        (when r (f3-msr-add m r))))
    (unless (eq level :pending)
      (dolist (s (if (eq level :all)
                     (f3-segdirs f :lo (f3-abs-level f langid index 0)
                                   :hi (f3-abs-level f langid index (1- +fts3-segdir-maxlevel+)))
                     (f3-segdirs f :level (f3-abs-level f langid index level))))
        (let ((start (sd-start s)) (leaves-end (sd-leaves-end s))
              (end (f3-int-of (sd-end s))) (root (sd-root s)))
          (when (and (/= start 0) term root)
            (multiple-value-bind (first last) (f3-select-leaf f term (f3-padded root) (length root) t prefix-p)
              (setf start first)
              (when prefix-p (setf leaves-end last))
              (unless (or prefix-p scan-p) (setf leaves-end start))))
          (f3-msr-add m (f3-reader-new (1+ (msr-nsegment m)) (and (not prefix-p) (not scan-p))
                                       start leaves-end end root)))))
    m))

(defun f3-scan-interior-node (term node nnode want-first want-last)
  "fts3ScanInteriorNode: (values first-child last-child)."
  (let ((p 0) (first nil) (last nil) (buf (make-array 16 :element-type 'character :adjustable t :fill-pointer 0))
        (is-first t) child nterm)
    (multiple-value-setq (child p) (f3-get-varint-u node p))
    (multiple-value-setq (child p) (f3-get-varint-u node p))
    (when (> p nnode) (corrupt "database disk image is malformed"))
    (setf nterm (length term))
    (loop while (and (< p nnode) (or (and want-first (null first)) (and want-last (null last))))
          do (let ((nprefix 0) nsuffix)
               (unless is-first
                 (multiple-value-setq (nprefix p) (f3-get-varint32 node p))
                 (when (> nprefix (fill-pointer buf)) (corrupt "database disk image is malformed")))
               (setf is-first nil)
               (multiple-value-setq (nsuffix p) (f3-get-varint32 node p))
               (when (or (> nprefix p) (> nsuffix (- nnode p)) (zerop nsuffix))
                 (corrupt "database disk image is malformed"))
               (setf (fill-pointer buf) nprefix)
               (loop for i from p below (+ p nsuffix) do (vector-push-extend (code-char (aref node i)) buf))
               (incf p nsuffix)
               (let* ((nb (fill-pointer buf))
                      (n (min nb nterm))
                      (cmp (let ((c 0))
                             (dotimes (i n)
                               (let ((x (char-code (char term i))) (y (char-code (char buf i))))
                                 (when (/= x y) (setf c (if (< x y) -1 1)) (return))))
                             c)))
                 (when (and want-first (null first) (or (< cmp 0) (and (= cmp 0) (> nb nterm))))
                   (setf first child))
                 (when (and want-last (null last) (< cmp 0))
                   (setf last child)))
               (incf child)))
    (values (or first (and want-first child)) (or last (and want-last child)))))

(defun f3-select-leaf (f term node nnode want-first want-last)
  "fts3SelectLeaf: (values first-leaf last-leaf)."
  (let ((height (f3-get-varint32 node 0)))
    (multiple-value-bind (first last) (f3-scan-interior-node term node nnode want-first want-last)
      (when (> height 1)
        (when (and want-first want-last (/= first last))
          (multiple-value-bind (b n) (f3-read-block f first)
            (setf first (f3-select-leaf f term b n t nil)))
          (setf want-first nil))
        (multiple-value-bind (b n) (f3-read-block f (if want-first first last))
          (let ((h2 (f3-get-varint32 b 0)))
            (when (>= h2 height) (corrupt "database disk image is malformed"))
            (multiple-value-bind (a2 b2) (f3-select-leaf f term b n want-first want-last)
              (when want-first (setf first a2))
              (when want-last (setf last b2))))))
      (values first last))))

(defun f3-msr-start (f m term)
  "fts3SegReaderStart."
  (let ((v (msr-segments m)) (n (msr-nsegment m)))
    (unless (msr-restart m)
      (dotimes (i n)
        (let ((r (aref v i)) (res 0))
          (loop (f3-reader-next f r)
                (unless (and term (minusp (setf res (f3-reader-term-cmp r term)))) (return)))
          (when (and (rd-lookup r) (/= res 0))
            (f3-reader-set-eof r)))))
    (f3-reader-sort v n n #'f3-reader-cmp)))

(defun f3-msr-start-filter (f m flags term col)
  (setf (msr-flags m) flags (msr-filter-term m) term (msr-filter-col m) col (msr-filter-set m) t)
  (f3-msr-start f m term))

(defun f3-column-filter (col zero buf off n)
  "fts3ColumnFilter: (values new-off new-n)."
  (let ((end (+ off n)) (current 0) (p off) (list off) (nlist n))
    (loop
      (let ((c 0))
        (loop while (and (< p end) (/= 0 (logand (logior c (aref buf p)) #xfe)))
              do (setf c (logand (aref buf p) #x80)) (incf p)))
      (when (= col current)
        (setf nlist (- p list))
        (return))
      (decf nlist (- p list))
      (setf list p)
      (when (<= nlist 0) (return))
      (setf p (1+ list))
      (multiple-value-setq (current p) (f3-get-varint32 buf p)))
    (when (and zero (> (- end (+ list nlist)) 0))
      (fill buf 0 :start (+ list nlist) :end end))
    (values list nlist)))

(defun f3-msr-buffer-data (m buf off n)
  (let ((b (make-array (+ n +fts3-node-padding+) :element-type '(unsigned-byte 8) :initial-element 0)))
    (replace b buf :start2 off :end2 (+ off n))
    (setf (msr-buffer m) b)
    b))

(defun f3-msr-incr-next (f m)
  "sqlite3Fts3MsrIncrNext: (values docid buf off n), or NIL at the end."
  (let ((nmerge (msr-nadvance m)) (v (msr-segments m))
        (cmp (if (f3-desc-p f) #'f3-reader-doclist-cmp-rev #'f3-reader-doclist-cmp)))
    (when (zerop nmerge) (return-from f3-msr-incr-next nil))
    (loop
      (let ((seg (aref v 0)))
        (unless (rd-offset-list seg) (return nil))
        (let ((docid (rd-docid seg)) (buf (rd-node seg)))
          (multiple-value-bind (off n) (f3-reader-next-docid f seg)
            (let ((j 1))
              (loop while (and (< j nmerge) (rd-offset-list (aref v j)) (= (rd-docid (aref v j)) docid))
                    do (f3-reader-next-docid f (aref v j)) (incf j))
              (f3-reader-sort v nmerge j cmp)
              ;; (SQLite tests the reader now first in line, not the one read)
              (when (and (plusp n) (rd-pending-p (aref v 0)))
                (setf buf (f3-msr-buffer-data m buf off (1+ n)) off 0))
              (when (>= (msr-col-filter m) 0)
                (multiple-value-setq (off n) (f3-column-filter (msr-col-filter m) t buf off n)))
              (when (plusp n)
                (return (values docid buf off n))))))))))

(defun f3-msr-incr-start (f m col term)
  "sqlite3Fts3MsrIncrStart."
  (f3-msr-start f m term)
  (let ((v (msr-segments m)) (i 0))
    (loop while (and (< i (msr-nsegment m))
                     (rd-node (aref v i))
                     (zerop (f3-reader-term-cmp (aref v i) term)))
          do (incf i))
    (setf (msr-nadvance m) i)
    (dotimes (k i) (f3-reader-first-docid f (aref v k)))
    (f3-reader-sort v i i (if (f3-desc-p f) #'f3-reader-doclist-cmp-rev #'f3-reader-doclist-cmp))
    (setf (msr-col-filter m) col)))

(defun f3-msr-incr-restart (m)
  (setf (msr-nadvance m) 0 (msr-restart m) t)
  (loop for r across (msr-segments m)
        do (setf (rd-offset-list r) nil (rd-noffset-list r) 0 (rd-docid r) 0)))

(defun f3-first-filter (delta buf off n out)
  "sqlite3Fts3FirstFilter: append to OUT (a growable buffer) the entry for
the first-token positions of the position list BUF[OFF, OFF+N); returns the
number of bytes written."
  (let ((start (fill-pointer out)) (written nil) (p off) (end (+ off n)))
    (unless (= (aref buf p) 1)
      (when (= (aref buf p) 2)
        (f3-buf-varint out delta)
        (vector-push-extend 2 out)
        (setf written t))
      (setf p (f3-columnlist-skip buf p)))
    (loop while (< p end)
          do (incf p)
             (multiple-value-bind (col o) (f3-get-varint buf p)
               (setf p o)
               (when (= (aref buf p) 2)
                 (unless written (f3-buf-varint out delta) (setf written t))
                 (vector-push-extend 1 out)
                 (f3-buf-varint out col)
                 (vector-push-extend 2 out))
               (setf p (f3-columnlist-skip buf p))))
    (when written (vector-push-extend 0 out))
    (- (fill-pointer out) start)))

(defun f3-msr-step (f m)
  "sqlite3Fts3SegReaderStep: T when positioned on a term (MSR-TERM,
MSR-DOCLIST-*), NIL at the end."
  (let* ((flags (msr-flags m))
         (ignore-empty (logtest flags +f3f-ignore-empty+))
         (require-pos (logtest flags +f3f-require-pos+))
         (col-filter (logtest flags +f3f-column-filter+))
         (prefix (logtest flags +f3f-prefix+))
         (scan (logtest flags +f3f-scan+))
         (first-p (logtest flags +f3f-first+))
         (v (msr-segments m))
         (nseg (msr-nsegment m))
         (fterm (msr-filter-term m))
         (cmp (if (f3-desc-p f) #'f3-reader-doclist-cmp-rev #'f3-reader-doclist-cmp)))
    (when (zerop nseg) (return-from f3-msr-step nil))
    (loop
      (dotimes (i (msr-nadvance m))
        (let ((r (aref v i)))
          (if (rd-lookup r) (f3-reader-set-eof r) (f3-reader-next f r))))
      (f3-reader-sort v nseg (msr-nadvance m) #'f3-reader-cmp)
      (setf (msr-nadvance m) 0)
      (unless (rd-node (aref v 0)) (return nil))
      (let ((term (copy-seq (rd-term (aref v 0)))))
        (setf (msr-term m) term)
        (when (and fterm (not scan))
          (when (or (< (length term) (length fterm))
                    (and (not prefix) (> (length term) (length fterm)))
                    (string/= term fterm :end1 (length fterm)))
            (return nil)))
        (let ((nmerge 1))
          (loop while (and (< nmerge nseg) (rd-node (aref v nmerge))
                           (string= (rd-term (aref v nmerge)) term))
                do (incf nmerge))
          (cond
            ((and (= nmerge 1) (not ignore-empty) (not first-p)
                  (or (not (f3-desc-p f)) (not (rd-pending-p (aref v 0)))))
             (let ((r (aref v 0)))
               (setf (msr-ndoclist m) (rd-ndoclist r))
               (if (rd-pending-p r)
                   (setf (msr-doclist-buf m) (f3-msr-buffer-data m (rd-node r) (rd-doclist r) (rd-ndoclist r))
                         (msr-doclist-off m) 0)
                   (setf (msr-doclist-buf m) (rd-node r) (msr-doclist-off m) (rd-doclist r)))
               (setf (msr-nadvance m) nmerge)
               (return t)))
            (t
             (let ((out (f3-buf 128)) (prev 0))
               (dotimes (i nmerge) (f3-reader-first-docid f (aref v i)))
               (f3-reader-sort v nmerge nmerge cmp)
               (loop while (rd-offset-list (aref v 0))
                     do (let* ((r0 (aref v 0)) (docid (rd-docid r0)) (buf (rd-node r0)))
                          (multiple-value-bind (pl npl) (f3-reader-next-docid f r0)
                            (let ((j 1))
                              (loop while (and (< j nmerge) (rd-offset-list (aref v j))
                                               (= (rd-docid (aref v j)) docid))
                                    do (f3-reader-next-docid f (aref v j)) (incf j))
                              (when col-filter
                                (multiple-value-setq (pl npl) (f3-column-filter (msr-filter-col m) nil buf pl npl)))
                              (when (or (not ignore-empty) (> npl 0))
                                (let ((delta (if (and (f3-desc-p f) (plusp (fill-pointer out)))
                                                 (progn (when (<= prev docid) (corrupt "database disk image is malformed"))
                                                        (- prev docid))
                                                 (progn (when (and (plusp (fill-pointer out)) (>= prev docid))
                                                          (corrupt "database disk image is malformed"))
                                                        (- docid prev)))))
                                  (if first-p
                                      (when (plusp (f3-first-filter delta buf pl npl out))
                                        (setf prev docid))
                                      (progn
                                        (f3-buf-varint out delta)
                                        (setf prev docid)
                                        (when require-pos
                                          (f3-buf-append out buf pl (+ pl npl))
                                          (vector-push-extend 0 out))))))
                              (f3-reader-sort v nmerge j cmp)))))
               (setf (msr-nadvance m) nmerge)
               (when (plusp (fill-pointer out))
                 (setf (msr-doclist-buf m) (f3-padded out)
                       (msr-doclist-off m) 0
                       (msr-ndoclist m) (fill-pointer out)
                       (msr-buffer m) (msr-doclist-buf m))
                 (return t))))))))))

(defun f3-msr-doclist (m)
  "The current doclist as a fresh padded octet vector."
  (f3-padded (msr-doclist-buf m) (msr-doclist-off m) (+ (msr-doclist-off m) (msr-ndoclist m))))

;;; ------------------------------------------------------------------
;;; Segment writer (SegmentWriter / SegmentNode)

(defstruct (f3node (:conc-name nd-))
  parent right leftmost (nentry 0)
  (term "") has-term
  (data (f3-buf 64)))                  ; starts with 11 bytes reserved for the header

(defstruct (f3writer (:conc-name wr-))
  tree (first 0) (free 0)
  (term "") (data (f3-buf 256)) (nleafdata 0))

(defun f3-node-new ()
  (let ((n (make-f3node)))
    (dotimes (i 11) (vector-push-extend 0 (nd-data n)))
    n))

(defun f3-node-add-term (f tree term)
  "fts3NodeAddTerm: returns the (possibly new) node."
  (when tree
    (let* ((nprefix (f3-prefix-compress (nd-term tree) term))
           (nsuffix (- (length term) nprefix)))
      (when (<= nsuffix 0) (corrupt "database disk image is malformed"))
      (let ((nreq (+ (fill-pointer (nd-data tree)) (f3-varint-len nprefix) (f3-varint-len nsuffix) nsuffix)))
        (when (or (<= nreq (f3-node-size f)) (not (nd-has-term tree)))
          (when (nd-has-term tree) (f3-buf-varint (nd-data tree) nprefix))
          (f3-buf-varint (nd-data tree) nsuffix)
          (loop for i from nprefix below (length term)
                do (vector-push-extend (char-code (char term i)) (nd-data tree)))
          (incf (nd-nentry tree))
          (setf (nd-term tree) term (nd-has-term tree) t)
          (return-from f3-node-add-term tree)))))
  (let ((new (f3-node-new)))
    (if tree
        (let ((parent (f3-node-add-term f (nd-parent tree) term)))
          (unless (nd-parent tree) (setf (nd-parent tree) parent))
          (setf (nd-right tree) new
                (nd-leftmost new) (nd-leftmost tree)
                (nd-parent new) parent))
        (progn (setf (nd-leftmost new) new)
               (setf new (f3-node-add-term f new term))))
    new))

(defun f3-tree-finish-node (node height left-child)
  "Write the header before offset 11; returns the start offset."
  (let* ((start (- 10 (f3-varint-len left-child)))
         (d (nd-data node)))
    (setf (aref d start) height)
    (f3-put-varint d (1+ start) left-child)
    start))

(defun f3-node-write (f tree height leaf free)
  "fts3NodeWrite: (values last-block root-bytes)."
  (if (null (nd-parent tree))
      (let ((start (f3-tree-finish-node tree height leaf)))
        (values (1- free) (subseq (nd-data tree) start)))
      (let ((next-free free) (next-leaf leaf))
        (loop for it = (nd-leftmost tree) then (nd-right it)
              while it
              do (let ((start (f3-tree-finish-node it height next-leaf)))
                   (f3-write-block f next-free (subseq (nd-data it) start))
                   (incf next-free)
                   (incf next-leaf (1+ (nd-nentry it)))))
        (f3-node-write f (nd-parent tree) (1+ height) free next-free))))

(defun f3-writer-add (f w term doclist &optional (dstart 0) (dend (length doclist)))
  "fts3SegWriterAdd: W may be NIL; returns the writer."
  (let ((w (or w (let ((nw (make-f3writer))) (setf (wr-free nw) (f3-next-block-id f) (wr-first nw) (wr-free nw)) nw)))
        (ndoc (- dend dstart)))
    (let* ((nprefix (f3-prefix-compress (wr-term w) term))
           (nsuffix (- (length term) nprefix))
           (nreq (+ (f3-varint-len nprefix) (f3-varint-len nsuffix) nsuffix (f3-varint-len ndoc) ndoc)))
      (when (<= nsuffix 0) (corrupt "database disk image is malformed"))
      (when (and (plusp (fill-pointer (wr-data w))) (> (+ (fill-pointer (wr-data w)) nreq) (f3-node-size f)))
        (f3-write-block f (wr-free w) (wr-data w))
        (incf (wr-free w))
        (incf (f3-leaf-add f))
        (setf (wr-tree w) (f3-node-add-term f (wr-tree w) (subseq term 0 (1+ nprefix))))
        (setf (fill-pointer (wr-data w)) 0 (wr-term w) "")
        (setf nprefix 0 nsuffix (length term)
              nreq (+ 1 (f3-varint-len (length term)) (length term) (f3-varint-len ndoc) ndoc)))
      (incf (wr-nleafdata w) nreq)
      (let ((d (wr-data w)))
        (f3-buf-varint d nprefix)
        (f3-buf-varint d nsuffix)
        (loop for i from nprefix below (length term) do (vector-push-extend (char-code (char term i)) d))
        (f3-buf-varint d ndoc)
        (f3-buf-append d doclist dstart dend))
      (setf (wr-term w) term))
    w))

(defun f3-writer-flush (f w level idx)
  (if (wr-tree w)
      (let ((last-leaf (wr-free w)))
        (f3-write-block f (wr-free w) (wr-data w))
        (incf (wr-free w))
        (multiple-value-bind (last root) (f3-node-write f (wr-tree w) 1 (wr-first w) (wr-free w))
          (f3-segdir-write f level idx (wr-first w) last-leaf last (wr-nleafdata w) root)))
      (f3-segdir-write f level idx 0 0 0 (wr-nleafdata w) (coerce (wr-data w) 'octets)))
  (incf (f3-leaf-add f)))

;;; ------------------------------------------------------------------
;;; Merging

(defun f3-read-end-block-field (v)
  "fts3ReadEndBlockField: (values end-block nbytes)."
  (let ((s (cond ((stringp v) v) ((eq v :null) nil) ((integerp v) (format nil "~d" v))
                 ((blobp v) (map 'string #'code-char v)) (t (value-to-text v)))))
    (if (null s)
        (values 0 0)
        (let ((i 0) (val 0) (mul 1) (n (length s)))
          (loop while (and (< i n) (digit-char-p (char s i)))
                do (setf val (+ (* val 10) (digit-char-p (char s i)))) (incf i))
          (let ((end (f3-signed (ldb (byte 64 0) val))))
            (loop while (and (< i n) (char= (char s i) #\Space)) do (incf i))
            (setf val 0)
            (when (and (< i n) (char= (char s i) #\-)) (incf i) (setf mul -1))
            (loop while (and (< i n) (digit-char-p (char s i)))
                  do (setf val (+ (* val 10) (digit-char-p (char s i)))) (incf i))
            (values end (* val mul)))))))

(defun f3-promote-segments (f abs-level nbyte)
  "fts3PromoteSegments."
  (let* ((last (1- (* (1+ (floor abs-level +fts3-segdir-maxlevel+)) +fts3-segdir-maxlevel+)))
         (limit (floor (* nbyte 3) 2))
         (ok nil))
    (dolist (s (f3-segdirs f :lo (1+ abs-level) :hi last))
      (let ((size (nth-value 1 (f3-read-end-block-field (sd-end s)))))
        (when (or (<= size 0) (> size limit)) (setf ok nil) (return))
        (setf ok t)))
    (when ok
      (let ((i 0))
        (dolist (s (f3-segdirs f :lo abs-level :hi last))
          (f3-segdir-update f (sd-row s) :level -1 :idx i)
          (incf i)))
      (dolist (s (f3-segdirs f :level -1))
        (f3-segdir-update f (sd-row s) :level abs-level)))))

(defun f3-allocate-segdir-idx (f langid index level)
  (let ((next (f3-next-segment-index f (f3-abs-level f langid index level))))
    (if (>= next +fts3-merge-count+)
        (progn (f3-segment-merge f langid index level) 0)
        next)))

(defun f3-delete-segment (f r)
  (unless (zerop (rd-start-block r))
    (f3-delete-blocks f (rd-start-block r) (rd-end-block r))))

(defun f3-delete-segdir (f langid index level readers)
  (loop for r across readers do (f3-delete-segment f r))
  (if (eq level :all)
      (let ((lo (f3-abs-level f langid index 0)) (hi (f3-abs-level f langid index (1- +fts3-segdir-maxlevel+))))
        (f3-segdir-delete-if f (lambda (r) (and (integerp (svref r 0)) (<= lo (svref r 0) hi)))))
      (let ((l (f3-abs-level f langid index level)))
        (f3-segdir-delete-if f (lambda (r) (eql (svref r 0) l))))))

(defun f3-segment-merge (f langid index level)
  "fts3SegmentMerge: LEVEL :all, :pending or a relative level.  Returns
:done when there was nothing to do for :all."
  (let* ((m (f3-seg-reader-cursor f langid index level nil t nil))
         (idx 0) (new-level 0) (ignore-empty nil) (max-level 0) (w nil))
    (when (zerop (msr-nsegment m)) (return-from f3-segment-merge nil))
    (unless (eq level :pending)
      (setf max-level (or (f3-segdir-max-level f (f3-abs-level f langid index 0)
                                               (f3-abs-level f langid index (1- +fts3-segdir-maxlevel+)))
                          0)))
    (if (eq level :all)
        (progn
          (when (and (= (msr-nsegment m) 1) (not (rd-pending-p (aref (msr-segments m) 0))))
            (return-from f3-segment-merge :done))
          (setf new-level max-level ignore-empty t))
        (let ((rel (if (eq level :pending) -1 level)))
          (setf new-level (f3-abs-level f langid index (1+ rel)))
          (setf idx (f3-allocate-segdir-idx f langid index (1+ rel)))
          (setf ignore-empty (and (not (eq level :pending)) (> new-level max-level)))))
    (f3-msr-start-filter f m (logior +f3f-require-pos+ (if ignore-empty +f3f-ignore-empty+ 0)) nil 0)
    (loop while (f3-msr-step f m)
          do (setf w (f3-writer-add f w (msr-term m) (msr-doclist-buf m)
                                    (msr-doclist-off m) (+ (msr-doclist-off m) (msr-ndoclist m)))))
    (unless (eq level :pending)
      (f3-delete-segdir f langid index level (msr-segments m)))
    (when w
      (f3-writer-flush f w new-level idx)
      (when (or (eq level :pending) (< new-level max-level))
        (f3-promote-segments f new-level (wr-nleafdata w))))
    nil))

(defun f3-pending-flush (f)
  "sqlite3Fts3PendingTermsFlush."
  (dotimes (i (f3-nindex f))
    (f3-segment-merge f (f3-prev-langid f) i :pending))
  (when (and (f3-has-stat f) (= (f3-autoincrmerge f) #xff) (plusp (f3-leaf-add f)))
    (let ((r (f3-stat-get f 2)))
      (setf (f3-autoincrmerge f)
            (if r (let ((v (value-to-integer (first r)))) (if (eql v 1) 8 (if (integerp v) v 0))) 0))))
  (f3-pending-clear f))

(defun f3-all-langids (f)
  "SELECT ? UNION SELECT level / (1024 * nIndex) FROM %_segdir (sorted, distinct)."
  (let ((ids (list (f3-prev-langid f))))
    (dolist (r (f3-all-segdir-rows f))
      (let ((l (svref r 0)))
        (pushnew (if (integerp l) (truncate l (* 1024 (f3-nindex f))) l) ids :test #'equal)))
    (sort ids (lambda (a b) (if (and (integerp a) (integerp b)) (< a b) (integerp a))))))

(defun f3-optimize (f return-done)
  "fts3DoOptimize: T if everything was already optimal (with RETURN-DONE)."
  (f3-pending-flush f)
  (let ((seen-done nil))
    (dolist (langid (f3-all-langids f))
      (when (integerp langid)
        (dotimes (i (f3-nindex f))
          (when (eq (f3-segment-merge f langid i :all) :done) (setf seen-done t)))))
    (and return-done seen-done)))

;;; ------------------------------------------------------------------
;;; Incremental merge (merge=X,Y and automerge=N)

(defstruct (f3nw (:conc-name nw-))                 ; NodeWriter
  (block 0)
  (key (make-array 16 :element-type 'character :adjustable t :fill-pointer 0))
  (data (f3-buf 64)))

(defstruct (f3iw (:conc-name iw-))                 ; IncrmergeWriter
  (leaf-est 0) (work 0) (abs-level 0) (idx 0) (start 0) (end 0)
  (leaf-data 0) no-leaf-data
  (nodes (let ((v (make-array +fts3-max-appendable-height+)))
           (dotimes (i +fts3-max-appendable-height+ v) (setf (aref v i) (make-f3nw))))))

(defstruct (f3nr (:conc-name nr-))                 ; NodeReader
  node (nnode 0) (off 0) (child 0)
  (term (make-array 16 :element-type 'character :adjustable t :fill-pointer 0))
  (doclist 0) (ndoclist 0))

(defun f3-nr-next (r)
  (let ((first-p (zerop (fill-pointer (nr-term r)))) (nprefix 0) nsuffix (node (nr-node r)))
    (when (and (/= 0 (nr-child r)) (not first-p)) (incf (nr-child r)))
    (if (>= (nr-off r) (nr-nnode r))
        (setf (nr-node r) nil)
        (progn
          (unless first-p (setf (values nprefix (nr-off r)) (f3-get-varint32 node (nr-off r))))
          (setf (values nsuffix (nr-off r)) (f3-get-varint32 node (nr-off r)))
          (when (or (> nprefix (fill-pointer (nr-term r))) (> nsuffix (- (nr-nnode r) (nr-off r))) (zerop nsuffix))
            (corrupt "database disk image is malformed"))
          (setf (fill-pointer (nr-term r)) nprefix)
          (loop for i from (nr-off r) below (+ (nr-off r) nsuffix)
                do (vector-push-extend (code-char (aref node i)) (nr-term r)))
          (incf (nr-off r) nsuffix)
          (when (zerop (nr-child r))
            (multiple-value-bind (nd o) (f3-get-varint32 node (nr-off r))
              (when (< (- (nr-nnode r) o) nd) (corrupt "database disk image is malformed"))
              (setf (nr-ndoclist r) nd (nr-doclist r) o (nr-off r) (+ o nd))))))))

(defun f3-nr-init (node nnode)
  (let ((r (make-f3nr :node node :nnode nnode)))
    (if (and node (plusp nnode) (/= 0 (aref node 0)))
        (multiple-value-bind (c o) (f3-get-varint node 1)
          (setf (nr-child r) c (nr-off r) o))
        (setf (nr-off r) 1))
    (when node (f3-nr-next r))
    r))

(defun f3-append-to-node (block prev term doclist dstart dend)
  "fts3AppendToNode: BLOCK and PREV (the previous term) are growable."
  (let* ((first-p (zerop (fill-pointer prev)))
         (nprefix (f3-prefix-compress prev term))
         (nsuffix (- (length term) nprefix)))
    (when (<= nsuffix 0) (corrupt "database disk image is malformed"))
    (setf (fill-pointer prev) 0)
    (loop for c across term do (vector-push-extend c prev))
    (unless first-p (f3-buf-varint block nprefix))
    (f3-buf-varint block nsuffix)
    (loop for i from nprefix below (length term) do (vector-push-extend (char-code (char term i)) block))
    (when doclist
      (f3-buf-varint block (- dend dstart))
      (f3-buf-append block doclist dstart dend))))

(defun f3-incrmerge-push (f w term)
  (let ((ptr (nw-block (aref (iw-nodes w) 0))))
    (loop for layer from 1 below +fts3-max-appendable-height+
          do (let* ((node (aref (iw-nodes w) layer))
                    (next-ptr 0)
                    (nprefix (f3-prefix-compress (nw-key node) term))
                    (nsuffix (- (length term) nprefix))
                    (space (+ (f3-varint-len nprefix) (f3-varint-len nsuffix) nsuffix)))
               (when (<= nsuffix 0) (corrupt "database disk image is malformed"))
               (if (or (zerop (fill-pointer (nw-key node)))
                       (<= (+ (fill-pointer (nw-data node)) space) (f3-node-size f)))
                   (let ((blk (nw-data node)))
                     (when (zerop (fill-pointer blk))
                       (vector-push-extend layer blk)
                       (f3-buf-varint blk ptr))
                     (when (plusp (fill-pointer (nw-key node))) (f3-buf-varint blk nprefix))
                     (f3-buf-varint blk nsuffix)
                     (loop for i from nprefix below (length term) do (vector-push-extend (char-code (char term i)) blk))
                     (setf (fill-pointer (nw-key node)) 0)
                     (loop for c across term do (vector-push-extend c (nw-key node))))
                   (progn
                     (f3-write-block f (nw-block node) (nw-data node))
                     (setf (fill-pointer (nw-data node)) 0)
                     (vector-push-extend layer (nw-data node))
                     (f3-buf-varint (nw-data node) (1+ ptr))
                     (setf next-ptr (nw-block node))
                     (incf (nw-block node))
                     (setf (fill-pointer (nw-key node)) 0)))
               (when (zerop next-ptr) (return))
               (setf ptr next-ptr)))))

(defun f3-incrmerge-append (f w m)
  (let* ((term (msr-term m)) (buf (msr-doclist-buf m))
         (ds (msr-doclist-off m)) (nd (msr-ndoclist m)) (de (+ ds nd))
         (leaf (aref (iw-nodes w) 0))
         (nprefix (f3-prefix-compress (nw-key leaf) term))
         (nsuffix (- (length term) nprefix))
         (space (+ (f3-varint-len nprefix) (f3-varint-len nsuffix) nsuffix (f3-varint-len nd) nd)))
    (when (<= nsuffix 0) (corrupt "database disk image is malformed"))
    ;; (3.40 writes the leaf whether or not the estimated leaf area is full)
    (when (and (plusp (fill-pointer (nw-data leaf)))
               (> (+ (fill-pointer (nw-data leaf)) space) (f3-node-size f)))
      (f3-write-block f (nw-block leaf) (nw-data leaf))
      (incf (iw-work w))
      (f3-incrmerge-push f w (subseq term 0 (1+ nprefix)))
      (incf (nw-block leaf))
      (setf (fill-pointer (nw-key leaf)) 0 (fill-pointer (nw-data leaf)) 0)
      (setf nsuffix (length term)
            space (+ 1 (f3-varint-len nsuffix) nsuffix (f3-varint-len nd) nd)))
    (incf (iw-leaf-data w) space)
    (when (zerop (fill-pointer (nw-data leaf))) (vector-push-extend 0 (nw-data leaf)))
    (f3-append-to-node (nw-data leaf) (nw-key leaf) term buf ds de)))

(defun f3-incrmerge-release (f w)
  (let ((root-i (loop for i from (1- +fts3-max-appendable-height+) downto 0
                      when (plusp (fill-pointer (nw-data (aref (iw-nodes w) i)))) return i)))
    (when root-i
      (when (zerop root-i)
        (let ((b (nw-data (aref (iw-nodes w) 1))))
          (setf (fill-pointer b) 0)
          (vector-push-extend 1 b)
          (f3-buf-varint b (nw-block (aref (iw-nodes w) 0))))
        (setf root-i 1))
      (dotimes (i root-i)
        (let ((node (aref (iw-nodes w) i)))
          (when (plusp (fill-pointer (nw-data node)))
            (f3-write-block f (nw-block node) (nw-data node)))))
      (f3-segdir-write f (1+ (iw-abs-level w)) (iw-idx w) (iw-start w)
                       (nw-block (aref (iw-nodes w) 0)) (iw-end w)
                       (if (iw-no-leaf-data w) 0 (iw-leaf-data w))
                       (coerce (nw-data (aref (iw-nodes w) root-i)) 'octets)))))

(defun f3-appendable-p (f end)
  "SELECT 1 FROM %_segments WHERE blockid=? AND block IS NULL"
  (let ((r (shadow-get (f3-shadow f "segments") end)))
    (and r (eq (first r) :null))))

(defun f3-incrmerge-load (f abs-level idx key w)
  (let ((s (find (f3-int-of idx) (f3-segdirs f :level (1+ abs-level)) :key (lambda (s) (f3-int-of (sd-idx s))))))
    (when s
      (let ((start (sd-start s)) (leaf-end (sd-leaves-end s)) (root (sd-root s)))
        (multiple-value-bind (end nleaf) (f3-read-end-block-field (sd-end s))
          (setf (iw-leaf-data w) (abs nleaf) (iw-no-leaf-data w) (zerop nleaf))
          (unless root (corrupt "database disk image is malformed"))
          (let ((appendable (f3-appendable-p f end)))
            (when appendable
              (multiple-value-bind (b n) (f3-read-block f leaf-end)
                (let ((r (f3-nr-init b n)))
                  (loop while (nr-node r) do (f3-nr-next r))
                  (when (<= (f3-term-cmp key (coerce (nr-term r) 'simple-string)) 0)
                    (setf appendable nil)))))
            (when appendable
              (let ((height (if (plusp (length root)) (aref root 0) 0)))
                (unless (and (>= height 1) (< height +fts3-max-appendable-height+))
                  (corrupt "database disk image is malformed"))
                (setf (iw-leaf-est w) (floor (1+ (- end start)) +fts3-max-appendable-height+)
                      (iw-start w) start (iw-end w) end (iw-abs-level w) abs-level (iw-idx w) idx)
                (loop for i from (1+ height) below +fts3-max-appendable-height+
                      do (setf (nw-block (aref (iw-nodes w) i)) (+ start (* i (iw-leaf-est w)))))
                (let ((node (aref (iw-nodes w) height)))
                  (setf (nw-block node) (+ start (* (iw-leaf-est w) height)))
                  (setf (fill-pointer (nw-data node)) 0)
                  (f3-buf-append (nw-data node) root))
                (loop for i from height downto 0
                      do (let* ((node (aref (iw-nodes w) i))
                                (r (f3-nr-init (f3-padded (nw-data node)) (fill-pointer (nw-data node)))))
                           (loop while (nr-node r) do (f3-nr-next r))
                           (setf (fill-pointer (nw-key node)) 0)
                           (loop for c across (nr-term r) do (vector-push-extend c (nw-key node)))
                           (when (> i 0)
                             (let ((below (aref (iw-nodes w) (1- i))))
                               (setf (nw-block below) (nr-child r))
                               (multiple-value-bind (b n) (f3-read-block f (nr-child r))
                                 (setf (fill-pointer (nw-data below)) 0)
                                 (f3-buf-append (nw-data below) b 0 n))))))))))))))

(defun f3-incrmerge-writer (f abs-level idx nseg w)
  (let* ((rows (subseq (f3-segdirs f :level abs-level) 0 (min nseg (length (f3-segdirs f :level abs-level)))))
         (leaf-est (truncate (* 2 (loop for s in rows
                                         sum (float (+ 1 (- (sd-leaves-end s) (sd-start s))) 1d0))))))
    (setf (iw-start w) (f3-next-block-id f)
          (iw-end w) (+ (iw-start w) -1 (* leaf-est +fts3-max-appendable-height+)))
    (f3-write-block f (iw-end w) nil)
    (setf (iw-abs-level w) abs-level (iw-leaf-est w) leaf-est (iw-idx w) idx)
    (dotimes (i +fts3-max-appendable-height+)
      (setf (nw-block (aref (iw-nodes w) i)) (+ (iw-start w) (* i leaf-est))))))

(defun f3-truncate-node (node nnode term)
  "fts3TruncateNode: (values new-node-bytes child-block)."
  (when (< nnode 1) (corrupt "database disk image is malformed"))
  (let* ((leaf-p (zerop (aref node 0)))
         (new (f3-buf 64))
         (prev (make-array 16 :element-type 'character :adjustable t :fill-pointer 0))
         (block 0)
         (r (f3-nr-init node nnode)))
    (loop while (nr-node r)
          do (block this
               (when (zerop (fill-pointer new))
                 (let ((res (f3-term-cmp (coerce (nr-term r) 'simple-string) term)))
                   (when (or (< res 0) (and (not leaf-p) (= res 0))) (return-from this)))
                 (vector-push-extend (aref node 0) new)
                 (unless (zerop (nr-child r)) (f3-buf-varint new (nr-child r)))
                 (setf block (nr-child r)))
               (f3-append-to-node new prev (coerce (nr-term r) 'simple-string)
                                  (and (zerop (nr-child r)) node) (nr-doclist r) (+ (nr-doclist r) (nr-ndoclist r))))
             (f3-nr-next r))
    (when (zerop (fill-pointer new))
      (vector-push-extend (aref node 0) new)
      (unless (zerop (nr-child r)) (f3-buf-varint new (nr-child r)))
      (setf block (nr-child r)))
    (values (coerce new 'octets) block)))

(defun f3-truncate-segment (f abs-level idx term)
  (let ((s (find idx (f3-segdirs f :level abs-level) :key (lambda (s) (f3-int-of (sd-idx s)))))
        (new-start 0) (old-start 0) (root nil) (block 0))
    (when s
      (setf old-start (sd-start s))
      (let ((r (sd-root s)))
        (multiple-value-setq (root block) (f3-truncate-node (f3-padded r) (length r) term))))
    (loop while (/= block 0)
          do (setf new-start block)
             (multiple-value-bind (b n) (f3-read-block f block)
               (multiple-value-bind (nb nblock) (f3-truncate-node b n term)
                 (f3-write-block f new-start nb)
                 (setf block nblock))))
    (when (/= new-start 0)
      (f3-delete-blocks f old-start (1- new-start)))
    (when s
      (f3-segdir-update f (sd-row s) :start new-start :root (or root (make-octets 0))))))

(defun f3-repack-level (f abs-level)
  (let ((i 0))
    (dolist (s (f3-segdirs f :level abs-level))
      (unless (eql (sd-idx s) i)
        (f3-segdir-update f (sd-row s) :idx i))
      (incf i))))

(defun f3-incrmerge-chomp (f abs-level m)
  "Returns the number of input segments left (truncated)."
  (let ((nrem 0) (n (msr-nsegment m)))
    (loop for i from (1- n) downto 0
          do (let ((seg (find i (msr-segments m) :key #'rd-idx)))
               (if (null (rd-node seg))
                   (progn (f3-delete-segment f seg)
                          (f3-segdir-delete-if f (lambda (r) (and (eql (svref r 0) abs-level) (eql (svref r 1) i)))))
                   (progn (f3-truncate-segment f abs-level i (coerce (rd-term seg) 'simple-string))
                          (incf nrem)))))
    (when (/= nrem n) (f3-repack-level f abs-level))
    nrem))

(defun f3-hint-pop (hint)
  "(values rest-of-hint abs-level ninput) from the last pair of HINT."
  (let* ((n (length hint)) (i (1- n)))
    (when (logtest (aref hint i) #x80) (corrupt "database disk image is malformed"))
    (loop while (and (> i 0) (logtest (aref hint (1- i)) #x80)) do (decf i))
    (when (zerop i) (corrupt "database disk image is malformed"))
    (decf i)
    (loop while (and (> i 0) (logtest (aref hint (1- i)) #x80)) do (decf i))
    (let ((p (f3-padded hint)))
      (multiple-value-bind (lvl o) (f3-get-varint p i)
        (multiple-value-bind (nin o2) (f3-get-varint32 p o)
          (unless (= o2 n) (corrupt "database disk image is malformed"))
          (values (subseq hint 0 i) lvl nin))))))

(defun f3-find-merge-level (f nmin)
  "SELECT level, count(*) AS cnt FROM %_segdir GROUP BY level HAVING cnt>=?
ORDER BY (level % 1024) ASC, 2 DESC LIMIT 1: (values level count) or NIL."
  (let ((counts (make-hash-table)))
    (dolist (r (f3-all-segdir-rows f))
      (when (integerp (svref r 0)) (incf (gethash (svref r 0) counts 0))))
    (let ((best nil))
      (loop for l in (sort (loop for k being the hash-keys of counts collect k) #'<)
            for c = (gethash l counts)
            do (when (>= c nmin)
                 (when (or (null best)
                           (< (rem l 1024) (rem (car best) 1024))
                           (and (= (rem l 1024) (rem (car best) 1024)) (> c (cdr best))))
                   (setf best (cons l c)))))
      (and best (values (car best) (cdr best))))))

(defun f3-incrmerge (f nmerge nmin)
  "sqlite3Fts3Incrmerge: do about NMERGE leaves of merging, of levels with
at least NMIN segments."
  (let ((hint (let ((r (f3-stat-get f 1))) (if (and r (blobp (first r))) (copy-seq (first r)) (make-octets 0))))
        (dirty nil) (nrem nmerge)
        (nmod (* +fts3-segdir-maxlevel+ (f3-nindex f))))
    (loop while (> nrem 0)
          do (let ((use-hint nil) (abs-level 0) (nseg -1) (idx 0))
               (multiple-value-bind (l c) (f3-find-merge-level f (max 2 nmin))
                 (when l (setf abs-level l nseg c)))
               (when (plusp (length hint))
                 (multiple-value-bind (rest hlevel hseg) (f3-hint-pop hint)
                   (when (or (< nseg 0) (>= (mod abs-level nmod) (mod hlevel nmod)))
                     (setf abs-level hlevel nseg (min (max nmin nseg) hseg) use-hint t dirty t hint rest))))
               (when (<= nseg 0) (return))
               (when (or (< abs-level 0) (> abs-level (ash nmod 32))) (corrupt "database disk image is malformed"))
               (let ((flags +f3f-require-pos+) (w (make-f3iw)))
                 (setf idx (f3-next-segment-index f (1+ abs-level)))
                 (when (or (zerop idx) (and use-hint (= idx 1)))
                   (unless (f3-segdir-max-level f (+ abs-level 2)
                                                (* (1+ (floor (1+ abs-level) +fts3-segdir-maxlevel+)) +fts3-segdir-maxlevel+))
                     (setf flags (logior flags +f3f-ignore-empty+))))
                 (let ((m (make-f3msr))
                       (segs (f3-segdirs f :level abs-level)))
                   (loop for s in segs for i from 0 below nseg
                         do (f3-msr-add m (f3-reader-new i nil (sd-start s) (sd-leaves-end s)
                                                         (f3-int-of (sd-end s)) (sd-root s))))
                   (when (= (msr-nsegment m) nseg)
                     (f3-msr-start-filter f m flags nil 0)
                     (let* ((row (f3-msr-step f m)) (empty (not row)))
                       (if (and use-hint (> idx 0))
                           (f3-incrmerge-load f abs-level (1- idx) (msr-term m) w)
                           (f3-incrmerge-writer f abs-level idx (msr-nsegment m) w))
                       (when (plusp (iw-leaf-est w))
                         (unless empty
                           (loop (f3-incrmerge-append f w m)
                                 (let ((more (f3-msr-step f m)))
                                   (when (or (not more) (>= (iw-work w) nrem)) (return)))))
                         (decf nrem (1+ (iw-work w)))
                         (setf nseg (f3-incrmerge-chomp f abs-level m))
                         (when (/= nseg 0)
                           (setf dirty t)
                           (let ((b (f3-buf)))
                             (f3-buf-append b hint)
                             (f3-buf-varint b abs-level)
                             (f3-buf-varint b nseg)
                             (setf hint (coerce b 'octets)))))
                       (when (/= nseg 0) (setf (iw-leaf-data w) (- (iw-leaf-data w))))
                       (f3-incrmerge-release f w)
                       (when (and (zerop nseg) (not (iw-no-leaf-data w)))
                         (f3-promote-segments f (1+ abs-level) (iw-leaf-data w)))))))))
    (when dirty (f3-stat-put f 1 hint))))

(defun f3-parse-getint (s i)
  (let ((v 0))
    (loop while (and (< i (length s)) (digit-char-p (char s i)) (< v 214748363))
          do (setf v (+ (* 10 v) (digit-char-p (char s i)))) (incf i))
    (values v i)))

;;; ------------------------------------------------------------------
;;; Document sizes and totals (FTS4)

(defun f3-encode-ints (ints)
  (let ((b (f3-buf)))
    (loop for x across ints do (f3-buf-varint b (logand x #xffffffff)))
    (coerce b 'octets)))

(defun f3-decode-ints (n blob)
  (let ((a (make-array n :initial-element 0)))
    (when (and (blobp blob) (plusp (length blob)) (zerop (logand (aref blob (1- (length blob))) #x80)))
      (let ((p (f3-padded blob)) (j 0) (i 0))
        (loop while (and (< i n) (< j (length blob)))
              do (multiple-value-bind (x o) (f3-get-varint p j)
                   (setf (aref a i) (logand x #xffffffff) j o)
                   (incf i)))))
    a))

(defun f3-insert-docsize (f docid sizes)
  (shadow-put (f3-shadow f "docsize") docid (list (f3-encode-ints (subseq sizes 0 (f3-ncol f))))))

(defun f3-update-doc-totals (f ins del nchng)
  (let* ((nstat (+ (f3-ncol f) 2))
         (r (f3-stat-get f 0))
         (a (if r (f3-decode-ints nstat (first r)) (make-array nstat :initial-element 0))))
    (if (and (< nchng 0) (< (aref a 0) (- nchng)))
        (setf (aref a 0) 0)
        (setf (aref a 0) (logand (+ (aref a 0) nchng) #xffffffff)))
    (dotimes (i (1+ (f3-ncol f)))
      (let ((x (aref a (1+ i))))
        (setf (aref a (1+ i))
              (if (< (logand (+ x (aref ins i)) #xffffffff) (aref del i))
                  0
                  (logand (- (+ x (aref ins i)) (aref del i)) #xffffffff)))))
    (f3-stat-put f 0 (f3-encode-ints a))))

;;; ------------------------------------------------------------------
;;; Integrity check (checksums of the index against the content)

(defun f3-checksum-entry (term langid index docid col pos)
  (let ((ret (ldb (byte 64 0) docid)))
    (flet ((add (x) (setf ret (ldb (byte 64 0) (+ ret (ash ret 3) x)))))
      (add langid) (add index) (add col) (add pos)
      (loop for ch across term
            do (let ((b (char-code ch))) (add (if (>= b 128) (- b 256) b)))))
    ret))

(defun f3-checksum-index (f langid index)
  (let ((m (f3-seg-reader-cursor f langid index :all nil nil t)) (ck 0))
    (f3-msr-start-filter f m (logior +f3f-require-pos+ +f3f-ignore-empty+ +f3f-scan+) nil 0)
    (loop while (f3-msr-step f m)
          do (let* ((buf (msr-doclist-buf m)) (p (msr-doclist-off m)) (end (+ p (msr-ndoclist m)))
                    (term (msr-term m)) (docid 0) (col 0) (pos 0))
               (multiple-value-setq (docid p) (f3-get-varint buf p))
               (loop while (< p end)
                     do (multiple-value-bind (v o) (f3-get-varint-u buf p)
                          (setf p o)
                          (when (< p end)
                            (if (or (= v 0) (= v 1))
                                (progn (setf col 0 pos 0)
                                       (if (= v 1)
                                           (multiple-value-setq (col p) (f3-get-varint buf p))
                                           (multiple-value-bind (d o2) (f3-get-varint-u buf p)
                                             (setf p o2
                                                   docid (f3-signed (ldb (byte 64 0) (if (f3-desc-p f) (- docid d) (+ docid d))))))))
                                (progn (setf pos (ldb (byte 64 0) (+ pos (- v 2))))
                                       (setf ck (logxor ck (f3-checksum-entry term langid index docid col pos))))))))))
    ck))
