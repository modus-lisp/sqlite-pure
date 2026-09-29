;;;; wal.lisp — write-ahead-log databases, shared with SQLite processes.
;;;;
;;;; SQLite's WAL connections coordinate through "<db>-shm", the wal-index:
;;;; a header (two copies, checksummed) naming the last committed frame, a
;;;; checkpoint record with five reader "marks", and hash tables mapping
;;;; page numbers to frames.  Byte-range locks on the -shm file (offsets
;;;; 120..127: WRITE, CKPT, RECOVER, READ0..READ4; 128 the "dead-man switch"
;;;; every attached connection read-locks) replace the rollback journal's
;;;; locks, and every connection keeps a SHARED lock on the database file.
;;;;
;;;; This file speaks that protocol as SQLite 3.40 does:
;;;;  - a read transaction snapshots the header and holds a read mark no
;;;;    checkpoint may pass;
;;;;  - a write transaction takes WRITE, appends frames to -wal and entries
;;;;    to the hash tables, then publishes a new header;
;;;;  - when the log is wholly checkpointed and no reader needs it, the next
;;;;    writer restarts it from the beginning with fresh salts;
;;;;  - a missing or damaged index is rebuilt from the log (recovery);
;;;;  - PRAGMA wal_checkpoint copies what no reader still needs into the
;;;;    database file, and the last connection to close checkpoints fully and
;;;;    removes -wal and -shm.
;;;; So SQLite processes may read and write the database at the same time.
;;;; (Locks are fcntl(2) locks, which belong to a process: two connections
;;;; inside one Lisp do not exclude each other.)
;;;;
;;;; A read-only connection does not touch -shm: each read transaction
;;;; rescans the log for its committed frames.

(in-package #:sqlite-pure)

(defconstant +wal-magic+ #x377f0682)             ; | 1 = big-endian checksums
(defconstant +wal-version+ 3007000)
(defconstant +shm-hdr-size+ 136)
(defconstant +shm-block+ 32768)
(defconstant +shm-npage+ 4096)                   ; frames per hash block
(defconstant +shm-nslot+ 8192)
(defconstant +shm-npage-one+ (- 4096 34))        ; block 0 also holds the header
(defconstant +shm-lock-base+ 120)
(defconstant +wal-shm-dms+ 128)
(defconstant +readmark-not-used+ #xffffffff)
;; lock slots, relative to +shm-lock-base+
(defconstant +lk-write+ 0)
(defconstant +lk-ckpt+ 1)
(defun lk-read (i) (+ 3 i))

(defparameter *native-big* (not (member :little-endian *features*))
  "The -shm file is in the host's byte order (it is shared memory).")

(defstruct (wal (:conc-name wal-))
  path stream            ; the -wal file (opened on demand)
  shm                    ; the -shm stream (NIL: read-only, no shared index)
  node                   ; its SHM-NODE, shared with this process's other connections
  hdr                    ; our snapshot: the 48-octet index header
  read-lock              ; NIL, a read-mark slot 0..4, or :legacy
  write-lock
  fresh                  ; nothing has been read under this snapshot yet
  (frames (make-hash-table))   ; pgno -> newest frame number <= MAPPED
  (mapped 0)
  map-salt)

(defun wal-file-path (db) (concatenate 'string (db-path db) "-wal"))
(defun shm-file-path (db) (concatenate 'string (db-path db) "-shm"))

(defun wal-checksum (big b start end s1 s2)
  (loop for i from start below end by 8
        do (flet ((w (k) (if big (get-u32 b k)
                             (logior (aref b k) (ash (aref b (+ k 1)) 8)
                                     (ash (aref b (+ k 2)) 16) (ash (aref b (+ k 3)) 24)))))
             (setf s1 (ldb (byte 32 0) (+ s1 (w i) s2))
                   s2 (ldb (byte 32 0) (+ s2 (w (+ i 4)) s1)))))
  (values s1 s2))

;;; native-order fields of -shm
(defun nget-u32 (b off)
  (if *native-big* (get-u32 b off)
      (logior (aref b off) (ash (aref b (+ off 1)) 8)
              (ash (aref b (+ off 2)) 16) (ash (aref b (+ off 3)) 24))))
(defun nput-u32 (b off v)
  (if *native-big* (put-u32 b off v)
      (dotimes (i 4) (setf (aref b (+ off i)) (ldb (byte 8 (* 8 i)) v)))))
(defun nget-u16 (b off)
  (if *native-big* (get-u16 b off) (logior (aref b off) (ash (aref b (1+ off)) 8))))
(defun nput-u16 (b off v)
  (if *native-big* (put-u16 b off v)
      (setf (aref b off) (ldb (byte 8 0) v) (aref b (1+ off)) (ldb (byte 8 8) v))))

(defun hdr-change (h) (nget-u32 h 8))
(defun hdr-mx (h) (nget-u32 h 16))
(defun hdr-npage (h) (nget-u32 h 20))
(defun hdr-big (h) (= 1 (aref h 13)))
(defun hdr-salt (h) (subseq h 32 40))

;;; ------------------------------------------------------------------
;;; Files and locks

#+sbcl
(defun fd-lock (stream type start len)
  (handler-case
      (progn (sb-posix:fcntl (sb-sys:fd-stream-fd stream) sb-posix:f-setlk
                             (make-instance 'sb-posix:flock :type type :whence sb-posix:seek-set
                                                            :start start :len len))
             t)
    (sb-posix:syscall-error (e)
      (if (member (sb-posix:syscall-errno e) (list sb-posix:eagain sb-posix:eacces))
          nil
          (error e)))))

#-sbcl
(defun fd-lock (stream type start len)
  (declare (ignore stream type start len))
  t)

(defun stream-truncate (stream len)
  #+sbcl (progn (finish-output stream)
                (sb-posix:ftruncate (sb-sys:fd-stream-fd stream) len))
  #-sbcl (declare (ignore stream len)))

;;; The -shm file's locks, like the database file's, belong to the process:
;;; its connections share one SHM-NODE -- one descriptor, and for each lock
;;; slot the connections holding it shared or exclusive -- and fcntl is
;;; called only when the process's own hold changes (unixShmLock).

(defstruct (shm-node (:constructor make-shm-node (key stream)) (:include lock-queue))
  key stream     ; (its queue: connections waiting for the WRITE lock)
  (refs 0)
  (shared (make-array 8 :initial-element '()))   ; slot -> the WALs holding it SHARED
  (excl (make-array 8 :initial-element nil)))    ; slot -> the WAL holding it EXCLUSIVE

(defvar *shm-nodes* (make-hash-table :test 'equal))

(defun shm-lock (w type slot &optional (n 1))
  "Take (TYPE +RD+ or +WR+) or release (+UN+) lock slots SLOT..SLOT+N-1 of
the index for W's connection; true on success, NIL if another connection
of this process or another holds them."
  (with-lock-mutex
    (let* ((node (wal-node w))
           (shared (shm-node-shared node))
           (excl (shm-node-excl node))
           (slots (loop for i from slot below (+ slot n) collect i))
           (stream (shm-node-stream node))
           (start (+ +shm-lock-base+ slot)))
      (cond
        ((eql type +un+)
         ;; the process lets go unless another connection still reads them
         (unless (some (lambda (i) (remove w (aref shared i))) slots)
           (fd-lock stream +un+ start n))
         (when (and (= slot +lk-write+) (eq (aref excl slot) w))
           (hand-off node))
         (dolist (i slots)
           (setf (aref shared i) (remove w (aref shared i)))
           (when (eq (aref excl i) w) (setf (aref excl i) nil)))
         t)
        ((eql type +rd+)
         (cond ((some (lambda (i) (aref excl i)) slots) nil)
               ((and (notany (lambda (i) (aref shared i)) slots)
                     (not (fd-lock stream +rd+ start n)))
                nil)
               (t (dolist (i slots) (pushnew w (aref shared i))) t)))
        (t
         (cond ((some (lambda (i) (or (aref excl i) (aref shared i))) slots) nil)
               ((and (= slot +lk-write+) (turned-away-p node)) nil)
               ((fd-lock stream +wr+ start n)
                (dolist (i slots) (setf (aref excl i) w))
                (when (= slot +lk-write+) (setf (shm-node-handoff node) nil))
                t)
               (t nil)))))))

(defun shm-read (w off len)
  "LEN octets of -shm at OFF (zeros past its end).  (The stream is the
process's, shared by its connections: one at a time.)"
  (with-lock-mutex
    (let* ((s (wal-shm w)) (b (make-octets len)) (flen (file-length s)))
      (when (< off flen)
        (file-position s off)
        (read-sequence b s :end (min len (- flen off))))
      b)))

(defun shm-write (w off octets)
  (with-lock-mutex
    (let ((s (wal-shm w)))
      (file-position s off)
      (write-sequence octets s)
      (finish-output s))))

(defun shm-write-u32 (w off v)
  (let ((b (make-octets 4))) (nput-u32 b 0 v) (shm-write w off b)))

(defun shm-info (w)
  "The checkpoint record: 40 octets at offset 96."
  (shm-read w 96 40))
(defun info-backfill (i) (nget-u32 i 0))
(defun info-mark (i k) (nget-u32 i (+ 4 (* 4 k))))

(defun wal-ensure-stream (db)
  (let ((w (db-wal db)))
    (or (wal-stream w)
        (setf (wal-stream w)
              (open (wal-path w) :element-type '(unsigned-byte 8) :direction :io
                                 :if-exists :overwrite :if-does-not-exist :create)))))

(defun wal-input-stream (db)
  "The -wal stream, if the file exists."
  (let ((w (db-wal db)))
    (or (wal-stream w)
        (when (probe-file (wal-path w))
          (if (db-readonly db)
              (setf (wal-stream w)
                    (open (wal-path w) :element-type '(unsigned-byte 8) :direction :input
                                       :if-does-not-exist nil))
              (wal-ensure-stream db))))))

(defun frame-offset (db f) (+ 32 (* (1- f) (+ 24 (db-page-size db)))))

;;; ------------------------------------------------------------------
;;; The index header

(defun shm-try-header (w)
  "(values header status): status :OK, :TORN (the two copies differ: a
writer is mid-update) or :INVALID (never initialised, or damaged)."
  (let* ((b (shm-read w 0 96))
         (h1 (subseq b 0 48)))
    (cond ((not (equalp h1 (subseq b 48 96))) (values nil :torn))
          ((zerop (aref h1 12)) (values nil :invalid))
          (t (multiple-value-bind (s1 s2) (wal-checksum *native-big* h1 0 40 0 0)
               (cond ((not (and (= s1 (nget-u32 h1 40)) (= s2 (nget-u32 h1 44))))
                      (values nil :invalid))
                     ((/= (nget-u32 h1 0) +wal-version+)
                      (error 'sqlite-error :code :cantopen :message "unable to open database file"))
                     (t (values h1 :ok))))))))

(defun write-shm-header (w hdr)
  "Seal and publish HDR: second copy first, as SQLite does."
  (nput-u32 hdr 0 +wal-version+)
  (setf (aref hdr 12) 1)
  (multiple-value-bind (s1 s2) (wal-checksum *native-big* hdr 0 40 0 0)
    (nput-u32 hdr 40 s1) (nput-u32 hdr 44 s2))
  (shm-write w 48 hdr)
  (shm-write w 0 hdr))

(defun szpage-field (ps) (logior (logand ps #xff00) (ash ps -16)))

;;; ------------------------------------------------------------------
;;; Hash tables: frame F's page number lives in block K's page array; a
;;; page number's frames are found by linear probing from pgno*383.

(defun frame-block (f)
  (if (<= f +shm-npage-one+) 0 (1+ (floor (- f +shm-npage-one+ 1) +shm-npage+))))
(defun block-zero (k) (if (zerop k) 0 (+ +shm-npage-one+ (* (1- k) +shm-npage+))))
(defun block-pgno-offset (k) (+ (* k +shm-block+) (if (zerop k) +shm-hdr-size+ 0)))
(defun block-end (k) (* (1+ k) +shm-block+))

(defun shm-frame-pgnos (w from to)
  "Page numbers of frames FROM..TO (inclusive), in order."
  (let ((out '()) (f from))
    (loop while (<= f to)
          do (let* ((k (frame-block f))
                    (zero (block-zero k))
                    (last (min to (+ zero (if (zerop k) +shm-npage-one+ +shm-npage+))))
                    (b (shm-read w (+ (block-pgno-offset k) (* 4 (- f zero 1)))
                                 (* 4 (1+ (- last f))))))
               (loop for j from 0 to (- last f) do (push (nget-u32 b (* 4 j)) out))
               (setf f (1+ last))))
    (nreverse out)))

(defun shm-append-frames (w first pgnos mx-before)
  "Index frames FIRST, FIRST+1, ... holding PGNOS.  MX-BEFORE is the last
committed frame; entries past it are leftovers of a rolled-back writer."
  (let ((f first))
    (loop while pgnos
          do (let* ((k (frame-block f))
                    (zero (block-zero k))
                    (base (block-pgno-offset k))
                    (hash (- (+ (* k +shm-block+) (* 4 +shm-npage+)) base))
                    (b (shm-read w base (- (block-end k) base)))
                    (cleaned nil))
               (flet ((slot (i) (nget-u16 b (+ hash (* 2 i))))
                      (set-slot (i v) (nput-u16 b (+ hash (* 2 i)) v)))
                 (loop while (and pgnos (= (frame-block f) k))
                       do (let ((idx (- f zero)) (pgno (pop pgnos)))
                            (when (= idx 1) (fill b 0) (setf cleaned t))
                            (unless (or cleaned (zerop (nget-u32 b (* 4 (1- idx)))))
                              ;; walCleanupHash: forget entries past MX-BEFORE
                              (let ((limit (max 0 (- mx-before zero))))
                                (dotimes (i +shm-nslot+)
                                  (when (> (slot i) limit) (set-slot i 0)))
                                (fill b 0 :start (* 4 limit) :end hash))
                              (setf cleaned t))
                            (nput-u32 b (* 4 (1- idx)) pgno)
                            (let ((key (logand (* pgno 383) (1- +shm-nslot+))))
                              (loop until (zerop (slot key))
                                    do (setf key (logand (1+ key) (1- +shm-nslot+))))
                              (set-slot key idx))
                            (incf f))))
               (shm-write w base b)))))

;;; ------------------------------------------------------------------
;;; Reading the log itself (recovery, and read-only connections)

(defun wal-scan (db)
  "Parse the log.  Returns a plist: :valid :big :seq :salt :hs1 :hs2 (the
header's checksum) :pgnos (committed frames, in order) :mx :npage :s1 :s2
(the checksum chain at the last commit)."
  (let ((s (wal-input-stream db)) (ps (db-page-size db)))
    (if (not (and s (>= (file-length s) 32)))
        (list :valid nil :mx 0)
        (let ((hdr (make-octets 32)))
          (file-position s 0)
          (read-sequence hdr s)
          (let ((magic (get-u32 hdr 0)))
            (if (not (and (member magic (list +wal-magic+ (1+ +wal-magic+)))
                          (= (get-u32 hdr 4) +wal-version+)
                          (= (get-u32 hdr 8) ps)))
                (list :valid nil :mx 0)
                (let ((big (= magic (1+ +wal-magic+))))
                  (multiple-value-bind (s1 s2) (wal-checksum big hdr 0 24 0 0)
                    (if (not (and (= s1 (get-u32 hdr 24)) (= s2 (get-u32 hdr 28))))
                        (list :valid nil :mx 0)
                        (let ((fh (make-octets 24)) (page (make-octets ps))
                              (pending '()) (committed '()) (mx 0) (npage 0)
                              (cs1 s1) (cs2 s2) (hs1 s1) (hs2 s2))
                          (loop for f from 1
                                for pos = (+ 32 (* (1- f) (+ 24 ps)))
                                while (<= (+ pos 24 ps) (file-length s))
                                do (file-position s pos)
                                   (read-sequence fh s)
                                   (read-sequence page s)
                                   (unless (equalp (subseq fh 8 16) (subseq hdr 16 24)) (return))
                                   (multiple-value-setq (s1 s2) (wal-checksum big fh 0 8 s1 s2))
                                   (multiple-value-setq (s1 s2) (wal-checksum big page 0 ps s1 s2))
                                   (unless (and (= s1 (get-u32 fh 16)) (= s2 (get-u32 fh 20))) (return))
                                   (push (get-u32 fh 0) pending)
                                   (when (plusp (get-u32 fh 4))
                                     (setf committed (append pending committed)
                                           pending '() mx f npage (get-u32 fh 4)
                                           cs1 s1 cs2 s2)))
                          (list :valid t :big big :seq (get-u32 hdr 12) :salt (subseq hdr 16 24)
                                :hs1 hs1 :hs2 hs2 :pgnos (reverse committed) :mx mx :npage npage
                                :s1 cs1 :s2 cs2)))))))))))

(defun wal-rebuild-index (db)
  "Recovery: rebuild -shm from the log.  Caller holds WRITE, CKPT, RECOVER."
  (let* ((w (db-wal db))
         (scan (wal-scan db))
         (hdr (make-octets 48))
         (mx (getf scan :mx)))
    (when (getf scan :valid)
      (setf (aref hdr 13) (if (getf scan :big) 1 0))
      (nput-u16 hdr 14 (szpage-field (db-page-size db)))
      (replace hdr (getf scan :salt) :start1 32)
      (nput-u32 hdr 16 mx)
      (nput-u32 hdr 20 (getf scan :npage))
      (nput-u32 hdr 24 (if (plusp mx) (getf scan :s1) (getf scan :hs1)))
      (nput-u32 hdr 28 (if (plusp mx) (getf scan :s2) (getf scan :hs2))))
    (when (plusp mx) (shm-append-frames w 1 (getf scan :pgnos) 0))
    (write-shm-header w hdr)
    (shm-write-u32 w 96 0)                      ; nBackfill
    (shm-write-u32 w 128 mx)                    ; nBackfillAttempted
    (shm-write-u32 w 100 0)                     ; mark 0
    (loop for i from 1 below 5
          do (when (shm-lock w +wr+ (lk-read i))
               (shm-write-u32 w (+ 100 (* 4 i)) (if (and (= i 1) (plusp mx)) mx +readmark-not-used+))
               (shm-lock w +un+ (lk-read i))))))

(defun wal-recover (db)
  "Rebuild a damaged index.  True if the index is valid afterwards (NIL:
another connection is busy; retry)."
  (let* ((w (db-wal db)) (had (wal-write-lock w)))
    (when (or had (shm-lock w +wr+ +lk-write+))
      (unwind-protect
           (multiple-value-bind (hdr status) (shm-try-header w)
             (declare (ignore hdr))
             (or (eq status :ok)
                 (when (shm-lock w +wr+ +lk-ckpt+ 2)   ; CKPT and RECOVER
                   (unwind-protect (progn (wal-rebuild-index db) t)
                     (shm-lock w +un+ +lk-ckpt+ 2)))))
        (unless had (shm-lock w +un+ +lk-write+))))))

;;; ------------------------------------------------------------------
;;; Opening and closing

(defun wal-open (db)
  "DB is in WAL mode: attach to the shared index (read-write connections)."
  (let ((w (make-wal :path (wal-file-path db))))
    (setf (db-wal db) w)
    (unless (db-readonly db)
      (with-lock-mutex
        (let* ((key (inode-key (db-inode db)))
               (node (gethash key *shm-nodes*)))
          (unless node
            ;; the first connection of this process opens the index
            (let ((shm (open (shm-file-path db) :element-type '(unsigned-byte 8) :direction :io
                                                :if-exists :overwrite :if-does-not-exist :create)))
              (handler-bind ((error (lambda (c) (declare (ignore c)) (close shm))))
                ;; the dead-man switch: alone, we reset the index; then read-lock it
                (busy-wait (lambda ()
                             (or (and (fd-lock shm +wr+ +wal-shm-dms+ 1)
                                      (progn (stream-truncate shm 0) t)
                                      (fd-lock shm +rd+ +wal-shm-dms+ 1))
                                 (fd-lock shm +rd+ +wal-shm-dms+ 1)))))
              (setf node (make-shm-node key shm)
                    (gethash key *shm-nodes*) node)))
          (incf (shm-node-refs node))
          (setf (wal-node w) node (wal-shm w) (shm-node-stream node))))
      ;; and a SHARED lock on the database for as long as we are open
      (busy-wait (lambda () (%lock db :shared))))
    w))

(defun release-shm-node (w)
  "W's connection leaves the index: the process's last closes it."
  (with-lock-mutex
    (let ((node (wal-node w)))
      (when (zerop (decf (shm-node-refs node)))
        (close (shm-node-stream node))
        (remhash (shm-node-key node) *shm-nodes*))
      (setf (wal-node w) nil (wal-shm w) nil))))

(defun wal-close (db)
  "Leave the index.  The last connection out checkpoints and removes the
log and the index."
  (let ((w (db-wal db)))
    (when w
      (when (wal-shm w)
        (wal-unlock db :none)
        (when (%lock db :exclusive)
          ;; nobody else, in this process or another, has the database open
          (multiple-value-bind (busy log done) (wal-checkpoint db)
            (when (and (eql busy 0) (eql log done))
              (when (wal-stream w) (close (wal-stream w)) (setf (wal-stream w) nil))
              (let ((p (probe-file (wal-path w)))) (when p (delete-file p)))
              (let ((p (probe-file (shm-file-path db)))) (when p (delete-file p))))))
        (release-shm-node w)
        (%unlock db :none))
      (setf (wal-read-lock w) nil)
      (when (wal-stream w) (close (wal-stream w)) (setf (wal-stream w) nil)))))

;;; ------------------------------------------------------------------
;;; Read transactions

(defun db-file-page-count (db)
  (let* ((s (db-stream db)) (len (file-length s)))
    (if (< len 100)
        0
        (let ((h (make-octets 100)))
          (file-position s 0)
          (read-sequence h s)
          (let ((n (get-u32 h +hdr-page-count+)))
            (if (and (plusp n) (= (get-u32 h +hdr-change-counter+) (get-u32 h +hdr-version-valid-for+)))
                n
                (ceiling len (db-page-size db))))))))

(defun wal-begin-read (db)
  (let ((w (db-wal db)))
    (unless (wal-read-lock w)
      (if (wal-shm w)
          ;; A few immediate attempts before the busy handler, as
          ;; walBeginReadTransaction's retry loop does: an attempt that
          ;; finds the wal-index header :INVALID recovers it and asks to be
          ;; retried, which is not contention.  Under a busy timeout of 0
          ;; (cl-sqlite's default) BUSY-WAIT gives that retry only when the
          ;; clock has not yet ticked past its zero-length deadline -- so
          ;; the first PRAGMA journal_mode=WAL on a fresh database reported
          ;; "database is locked" on a slower implementation (modus).
          (or (loop repeat 5 thereis (wal-try-begin-read db))
              (busy-wait (lambda () (wal-try-begin-read db))))
          (wal-legacy-begin-read db)))))

(defun wal-try-begin-read (db)
  "One attempt at walTryBeginRead; NIL means retry."
  (let ((w (db-wal db)))
    (multiple-value-bind (hdr status) (shm-try-header w)
      (case status
        (:torn (return-from wal-try-begin-read nil))
        (:invalid (wal-recover db) (return-from wal-try-begin-read nil)))
      (flet ((unchanged-p () (equalp (shm-try-header w) hdr)))
        (let* ((info (shm-info w)) (mx (hdr-mx hdr)))
          ;; everything is in the database file: read it alone (mark 0)
          (when (= (info-backfill info) mx)
            (when (shm-lock w +rd+ (lk-read 0))
              (if (unchanged-p)
                  (progn (wal-install-snapshot db hdr 0) (return-from wal-try-begin-read t))
                  (progn (shm-lock w +un+ (lk-read 0)) (return-from wal-try-begin-read nil)))))
          (let ((mx-mark 0) (mx-i 0))
            (loop for i from 1 below 5
                  for m = (info-mark info i)
                  do (when (and (<= mx-mark m) (<= m mx)) (setf mx-mark m mx-i i)))
            (when (or (< mx-mark mx) (zerop mx-i))
              (loop for i from 1 below 5
                    do (when (shm-lock w +wr+ (lk-read i))
                         (shm-write-u32 w (+ 100 (* 4 i)) mx)
                         (setf mx-mark mx mx-i i)
                         (shm-lock w +un+ (lk-read i))
                         (return))))
            (when (zerop mx-i) (return-from wal-try-begin-read nil))
            (unless (shm-lock w +rd+ (lk-read mx-i)) (return-from wal-try-begin-read nil))
            (if (and (= (info-mark (shm-info w) mx-i) mx-mark) (unchanged-p))
                (progn (wal-install-snapshot db hdr mx-i) t)
                (progn (shm-lock w +un+ (lk-read mx-i)) nil))))))))

(defun wal-install-snapshot (db hdr lock)
  "Adopt HDR as this connection's view: drop cached pages it changed."
  (let* ((w (db-wal db))
         (old (wal-hdr w))
         (cache (db-cache db))
         (old-page1 (gethash 1 cache)))
    (setf (wal-read-lock w) lock)
    (unless (equalp old hdr)
      (let ((same-log (and old (equalp (hdr-salt old) (hdr-salt hdr)) (<= (hdr-mx old) (hdr-mx hdr)))))
        (if (and same-log (/= lock 0))
            (dolist (p (shm-frame-pgnos w (1+ (hdr-mx old)) (hdr-mx hdr)))
              (remhash p cache))
            (clrhash cache)))
      (setf (wal-hdr w) hdr))
    ;; the frame map, for reading pages out of the log
    (unless (and (equalp (wal-map-salt w) (hdr-salt hdr)) (<= (wal-mapped w) (hdr-mx hdr)))
      (clrhash (wal-frames w))
      (setf (wal-mapped w) 0 (wal-map-salt w) (hdr-salt hdr)))
    (when (/= lock 0)
      (loop for p in (shm-frame-pgnos w (1+ (wal-mapped w)) (hdr-mx hdr))
            for f from (1+ (wal-mapped w))
            do (setf (gethash p (wal-frames w)) f))
      (setf (wal-mapped w) (hdr-mx hdr)))
    (setf (db-page-count db) (if (plusp (hdr-mx hdr)) (hdr-npage hdr) (db-file-page-count db)))
    (when (and old-page1 (not (gethash 1 cache)) (plusp (db-page-count db)))
      (let ((new (read-page db 1)))
        (unless (equalp (subseq old-page1 40 44) (subseq new 40 44))
          (setf (db-schema db) nil))))
    (setf (wal-fresh w) t)))

(defun wal-legacy-begin-read (db)
  "Read-only connections: take the log's committed frames as they are."
  (let* ((w (db-wal db))
         (scan (wal-scan db))
         (key (list (getf scan :salt) (getf scan :mx))))
    (unless (equalp key (wal-map-salt w))
      (clrhash (db-cache db))
      (setf (db-schema db) nil)
      (clrhash (wal-frames w))
      (loop for p in (getf scan :pgnos) for f from 1 do (setf (gethash p (wal-frames w)) f))
      (setf (wal-mapped w) (getf scan :mx) (wal-map-salt w) key))
    (setf (db-page-count db) (if (plusp (getf scan :mx)) (getf scan :npage) (db-file-page-count db))
          (wal-read-lock w) :legacy)))

(defun wal-end-read (db)
  (let* ((w (db-wal db)) (lk (wal-read-lock w)))
    (when (and (integerp lk) (wal-shm w)) (shm-lock w +un+ (lk-read lk)))
    (setf (wal-read-lock w) nil)))

(defun wal-read-page (db pgno buffer)
  "Fill BUFFER with PGNO's image from the log if our snapshot has one."
  (let* ((w (db-wal db))
         (lk (wal-read-lock w))
         (f (and lk (not (eql lk 0)) (gethash pgno (wal-frames w)))))
    (when f
      (let ((s (wal-input-stream db)))
        (file-position s (+ (frame-offset db f) 24))
        (read-sequence buffer s)
        t))))

;;; ------------------------------------------------------------------
;;; Write transactions

(defun wal-begin-write (db)
  (let ((w (db-wal db)))
    (unless (wal-shm w)
      (error 'sqlite-error :code :readonly :message "attempt to write a readonly database"))
    (wal-begin-read db)
    (unless (wal-write-lock w)
      (busy-wait (lambda () (shm-lock w +wr+ +lk-write+)) (wal-node w))
      (setf (wal-write-lock w) t)
      (multiple-value-bind (hdr status) (shm-try-header w)
        (unless (eq status :ok)
          (busy-wait (lambda () (shm-lock w +wr+ +lk-ckpt+ 2)))
          (unwind-protect (wal-rebuild-index db)
            (shm-lock w +un+ +lk-ckpt+ 2))
          (setf hdr (shm-try-header w)))
        (unless (equalp hdr (wal-hdr w))
          ;; someone committed since our snapshot was taken
          (if (wal-fresh w)
              (progn (wal-end-read db) (wal-begin-read db))
              (progn (shm-lock w +un+ +lk-write+)
                     (setf (wal-write-lock w) nil)
                     (error 'sqlite-error :code :busy :message "database is locked"))))))))

(defun wal-unlock (db level)
  "Drop to LEVEL: :SHARED ends the write transaction, :NONE the read one too."
  (let ((w (db-wal db)))
    (when (wal-write-lock w)
      (shm-lock w +un+ +lk-write+)
      (setf (wal-write-lock w) nil))
    (ecase level
      (:shared
       ;; mark 0 reads only the database file, which lacks what we just wrote
       (when (and (eql (wal-read-lock w) 0) (plusp (hdr-mx (wal-hdr w))))
         (wal-end-read db)
         (wal-begin-read db)))
      (:none (wal-end-read db)))))

(defun wal-restart-log (db)
  "Before appending: if the log is wholly checkpointed and nobody reads
from it, start it over with new salts (walRestartLog)."
  (let ((w (db-wal db)))
    (when (eql (wal-read-lock w) 0)
      (let ((info (shm-info w)))
        (when (and (plusp (info-backfill info)) (shm-lock w +wr+ (lk-read 1) 4))
          (let ((hdr (copy-seq (wal-hdr w))))
            (put-u32 hdr 32 (ldb (byte 32 0) (1+ (get-u32 hdr 32))))
            (put-u32 hdr 36 (random #x100000000 (sql-random-state)))
            (nput-u32 hdr 16 0)
            (write-shm-header w hdr)
            (shm-write-u32 w 96 0)
            (shm-write-u32 w 128 0)
            (shm-write-u32 w 104 0)
            (loop for i from 2 below 5 do (shm-write-u32 w (+ 100 (* 4 i)) +readmark-not-used+))
            (shm-lock w +un+ (lk-read 1) 4)
            (setf (wal-hdr w) hdr)
            (wal-end-read db)
            (wal-begin-read db)
            t))))))

(defun wal-commit (db pages)
  "Append PAGES (dirty page numbers, sorted) as one committed transaction."
  (wal-begin-write db)
  (let* ((w (db-wal db))
         (restarted (wal-restart-log db))
         (hdr (copy-seq (wal-hdr w)))
         (mx (hdr-mx hdr))
         (ps (db-page-size db))
         (s (wal-ensure-stream db))
         (s1 (nget-u32 hdr 24)) (s2 (nget-u32 hdr 28)))
    (when (zerop mx)
      ;; a fresh log: its header carries this generation's salts
      (let ((seq (let ((old (wal-scan db))) (if (getf old :valid) (getf old :seq) 0)))
            (h (make-octets 32)))
        (if restarted
            (incf seq)
            (dotimes (i 8) (setf (aref hdr (+ 32 i)) (random 256 (sql-random-state)))))
        (setf (aref hdr 13) (if *native-big* 1 0))
        (put-u32 h 0 (if *native-big* (1+ +wal-magic+) +wal-magic+))
        (put-u32 h 4 +wal-version+)
        (put-u32 h 8 ps)
        (put-u32 h 12 (ldb (byte 32 0) seq))
        (replace h hdr :start1 16 :start2 32 :end2 40)
        (multiple-value-setq (s1 s2) (wal-checksum (hdr-big hdr) h 0 24 0 0))
        (put-u32 h 24 s1) (put-u32 h 28 s2)
        (file-position s 0)
        (write-sequence h s)))
    (let ((fh (make-octets 24)) (big (hdr-big hdr)) (f mx))
      (loop for (p . more) on pages
            for img = (gethash p (db-cache db))
            do (incf f)
               (fill fh 0)
               (put-u32 fh 0 p)
               (put-u32 fh 4 (if more 0 (db-page-count db)))
               (replace fh hdr :start1 8 :start2 32 :end2 40)
               (multiple-value-setq (s1 s2) (wal-checksum big fh 0 8 s1 s2))
               (multiple-value-setq (s1 s2) (wal-checksum big img 0 ps s1 s2))
               (put-u32 fh 16 s1)
               (put-u32 fh 20 s2)
               (file-position s (frame-offset db f))
               (write-sequence fh s)
               (write-sequence img s))
      (sync-stream s db 3)                 ; synchronous=FULL syncs the log per commit
      ;; index the frames, then publish: only now is the transaction in
      (shm-append-frames w (1+ mx) pages mx)
      (nput-u32 hdr 8 (ldb (byte 32 0) (1+ (hdr-change hdr))))
      (nput-u16 hdr 14 (szpage-field ps))
      (nput-u32 hdr 16 f)
      (nput-u32 hdr 20 (db-page-count db))
      (nput-u32 hdr 24 s1)
      (nput-u32 hdr 28 s2)
      (write-shm-header w hdr)
      (setf (wal-hdr w) hdr)
      (if (and (equalp (wal-map-salt w) (hdr-salt hdr)) (= (wal-mapped w) mx))
          (progn
            (loop for p in pages for g from (1+ mx) do (setf (gethash p (wal-frames w)) g))
            (setf (wal-mapped w) f))
          (progn (clrhash (wal-frames w)) (setf (wal-mapped w) 0 (wal-map-salt w) nil))))))

;;; ------------------------------------------------------------------
;;; Checkpoint

(defun wal-current-header (db)
  "A valid index header, recovering the index if need be."
  (let ((w (db-wal db)))
    (busy-wait (lambda ()
                 (multiple-value-bind (h status) (shm-try-header w)
                   (case status
                     (:ok h)
                     (:invalid (wal-recover db) nil)
                     (t nil)))))
    (shm-try-header w)))

(defun wal-checkpoint (db)
  "A passive checkpoint: copy into the database every frame no reader still
needs.  Returns (values busy log-frames checkpointed-frames)."
  (let ((w (db-wal db)))
    (if (not (and w (wal-shm w) (shm-lock w +wr+ +lk-ckpt+)))
        (values 1 -1 -1)
        (unwind-protect
             (let* ((hdr (wal-current-header db))
                    (mx (hdr-mx hdr))
                    (info (shm-info w))
                    (backfill (info-backfill info))
                    (safe mx))
               (when (< backfill mx)
                 ;; no further than the oldest reader still using the log
                 (loop for i from 1 below 5
                       for m = (info-mark info i)
                       do (when (> safe m)
                            (if (shm-lock w +wr+ (lk-read i))
                                (progn (shm-write-u32 w (+ 100 (* 4 i))
                                                      (if (= i 1) safe +readmark-not-used+))
                                       (shm-lock w +un+ (lk-read i)))
                                (setf safe m))))
                 (when (and (< backfill safe) (shm-lock w +wr+ (lk-read 0)))
                   (unwind-protect
                        (let ((latest (make-hash-table))
                              (ps (db-page-size db))
                              (npage (hdr-npage hdr))
                              (ws (wal-input-stream db))
                              (s (db-stream db))
                              (buf (make-octets (db-page-size db))))
                          (shm-write-u32 w 128 safe)
                          (fsync-only ws db)          ; the log is durable before we copy out of it
                          (loop for p in (shm-frame-pgnos w (1+ backfill) safe)
                                for f from (1+ backfill)
                                do (setf (gethash p latest) f))
                          (dolist (p (sort (loop for k being the hash-keys of latest collect k) #'<))
                            (when (<= p npage)
                              (file-position ws (+ (frame-offset db (gethash p latest)) 24))
                              (read-sequence buf ws)
                              (file-position s (* (1- p) ps))
                              (write-sequence buf s)))
                          (sync-stream s db)
                          (when (and (= safe mx) (> (file-length s) (* npage ps)))
                            (stream-truncate s (* npage ps)))
                          (shm-write-u32 w 96 safe)
                          (setf backfill safe))
                     (shm-lock w +un+ (lk-read 0)))))
               (values 0 mx backfill))
          (shm-lock w +un+ +lk-ckpt+)))))

;;; ------------------------------------------------------------------
;;; PRAGMA journal_mode

(defun set-journal-mode (db mode)
  "Switch between WAL and rollback-journal modes; returns the mode name."
  (cond
    ((memory-db-p db) "memory")
    ((string= mode "wal")
     (unless (db-wal db)
       (when (db-explicit (conn db)) (sql-error "cannot change into wal mode from within a transaction"))
       (let ((*db* db))
         (run-in-write-txn db (lambda ()
                                (let ((h (page-for-write db 1)))
                                  (setf (aref h 18) 2 (aref h 19) 2)))))
       (unlock-to db :none)
       (wal-open db)
       (wal-begin-read db))
     "wal")
    (t
     (when (db-wal db)
       (when (db-explicit (conn db)) (sql-error "cannot change out of wal mode from within a transaction"))
       (when (db-readonly db)
         (error 'sqlite-error :code :readonly :message "attempt to write a readonly database"))
       ;; only a connection alone with the database may leave WAL mode
       (wal-unlock db :none)
       (unless (%lock db :exclusive)
         (%unlock db :shared)
         (error 'sqlite-error :code :busy :message "database is locked"))
       (wal-close db)
       (setf (db-wal db) nil (db-lock db) :none)
       (clrhash (db-cache db))
       (setf (db-page-count db) (db-file-page-count db))
       (lock-shared db)
       (let ((*db* db))
         (run-in-write-txn db (lambda ()
                                (let ((h (page-for-write db 1)))
                                  (setf (aref h 18) 1 (aref h 19) 1))))))
     "delete")))
