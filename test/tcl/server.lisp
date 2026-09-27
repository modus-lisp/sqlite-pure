;;;; test/tcl/server.lisp — one database connection, driven over stdin/stdout
;;;; by test/tcl/sqlite3.tcl, so that SQLite's own TCL test suite
;;;; (tester.tcl and the *.test files, unmodified) can run against this
;;;; library.  Each Tcl database handle is its own server process, so two
;;;; handles on one file lock against each other exactly as two SQLite
;;;; connections do.
;;;;
;;;; Frames, both directions: "<count>\n" then COUNT items, each a type
;;;; character, a byte length, ":" and the bytes.  Types: n null, i integer,
;;;; f double (shortest round-trip decimal), s text (UTF-8), b blob.
;;;;
;;;; Requests (item 0 names the request) are answered by an "ok" or "error"
;;;; frame; while answering "eval", the server may send "vars" (the values
;;;; of named parameters, asked for as each statement is prepared), "call"
;;;; (a Tcl SQL function) and "coll" (a Tcl collation), each answered by Tcl
;;;; with "ret" or "err".

(defpackage #:sqlite-pure.tclserver
  (:use #:cl)
  (:export #:main))

(in-package #:sqlite-pure.tclserver)

(defvar *in*)
(defvar *out*)
(defvar *db* nil)
(defvar *last-code* 0)

;;; framing

(defun read-frame ()
  (let ((count (let ((n 0))
                 (loop for c = (read-byte *in* nil nil)
                       do (cond ((null c) (return-from read-frame nil))
                                ((= c 10) (return n))
                                (t (setf n (+ (* 10 n) (- c 48)))))))))
    (loop repeat count collect (read-item))))

(defun read-item ()
  (let ((type (code-char (read-byte *in*))) (len 0))
    (loop for c = (read-byte *in*) until (= c 58) do (setf len (+ (* 10 len) (- c 48))))
    (let ((bytes (make-array len :element-type '(unsigned-byte 8))))
      (read-sequence bytes *in*)
      (ecase type
        (#\n :null)
        (#\i (parse-integer (map 'string #'code-char bytes)))
        (#\f (let ((s (map 'string #'code-char bytes)))
               (cond ((string-equal s "inf") sb-ext:double-float-positive-infinity)
                     ((string-equal s "-inf") sb-ext:double-float-negative-infinity)
                     (t (let ((*read-default-float-format* 'double-float))
                          (coerce (let ((*read-eval* nil)) (read-from-string s)) 'double-float))))))
        (#\s (sqlite-pure::utf8-decode-lenient bytes))
        (#\b bytes)))))

(defun double-text (d)
  (cond ((sqlite-pure::float-infinity-p d) (if (plusp d) "Inf" "-Inf"))
        (t (let ((*read-default-float-format* 'double-float))
             (let ((s (prin1-to-string d)))
               ;; SBCL writes 1.0d20 style only for other formats; with the
               ;; default format it writes 1.0e20 or 1.0
               (substitute #\e #\d s))))))

(defun write-item (v)
  (multiple-value-bind (type bytes)
      (cond ((eq v :null) (values #\n #()))
            ((integerp v) (values #\i (sqlite-pure::utf8-encode (princ-to-string v))))
            ((floatp v) (values #\f (sqlite-pure::utf8-encode (double-text v))))
            ((stringp v) (values #\s (sqlite-pure::utf8-encode v)))
            ((symbolp v) (values #\s (sqlite-pure::utf8-encode (string-downcase v))))
            (t (values #\b v)))
    (write-byte (char-code type) *out*)
    (loop for c across (princ-to-string (length bytes)) do (write-byte (char-code c) *out*))
    (write-byte 58 *out*)
    (write-sequence bytes *out*)))

(defun send (&rest items)
  (loop for c across (princ-to-string (length items)) do (write-byte (char-code c) *out*))
  (write-byte 10 *out*)
  (dolist (v items) (write-item v))
  (force-output *out*))

(defun send-list (items) (apply #'send items))

(defun ask (&rest items)
  "Send a callback frame and wait for Tcl's answer: (values value errorp)."
  (send-list items)
  (let ((reply (read-frame)))
    (if (equal (first reply) "ret")
        (values (second reply) nil)
        (values (second reply) t))))

;;; results

(defun error-code (c)
  "SQLite's primary result code for a condition."
  (case (sqlp:sqlite-error-code c)
    (:busy 5) (:locked 6) (:readonly 8) (:interrupt 9) (:corrupt 11) (:full 13) (:cantopen 14)
    (:toobig 18) (:constraint 19) (:mismatch 20) (:range 25) (:notadb 26) (:abort 4) (:auth 23)
    (:schema 17) (:ioerr 10) (:nomem 7) (:misuse 21) (:perm 3)
    (t 1)))

(defun statement-texts (sql)
  "SQL split into statements, as successive sqlite3_prepare calls see it;
signals the parse error of the first bad statement (after the good ones
before it have been returned by a first pass)."
  (mapcar #'cdr (sqlite-pure::parse-sql sql)))

(defun param-names (text)
  "The named parameters of TEXT, in order of first appearance."
  (let ((names '()))
    (loop for tk across (sqlite-pure::tokenize text)
          do (when (and (eq (sqlite-pure::tok-kind tk) :param)
                        (stringp (sqlite-pure::tok-value tk)))
               (pushnew (sqlite-pure::tok-value tk) names :test #'string=)))
    (nreverse names)))

(defun bind-values (text)
  "Positional parameter values for TEXT: named ones from Tcl variables."
  (multiple-value-bind (stmts nparam names) (sqlite-pure::parse-sql text)
    (declare (ignore stmts))
    (when (and nparam (plusp nparam))
      (let* ((wanted (param-names text))
             (vals (if wanted
                       (let ((reply (progn (send-list (cons "vars" wanted)) (read-frame))))
                         (rest reply))
                       '()))
             (table (mapcar #'cons wanted vals)))
        (loop for i from 1 to nparam
              collect (let ((name (car (rassoc i names))))
                        (or (and name (cdr (assoc name table :test #'string=))) :null)))))))

(defun do-eval (sql)
  "Run every statement of SQL in turn; answer with each statement's
columns and rows, and the error that stopped it, if any."
  (let ((results '()) (err nil))
    (handler-case
        (dolist (text (sqlite-pure.shell::split-statements sql))
          (let ((params (bind-values text)))
            (multiple-value-bind (rows cols) (apply #'sqlp:query *db* text params)
              (push (cons cols rows) results))))
      (sqlp:sqlite-error (c) (setf err c))
      (error (c) (setf err (make-condition 'sqlp:sqlite-error :message (format nil "LISP ERROR: ~a" c)))))
    (setf *last-code* (if err (error-code err) 0))
    (let ((items (list (if err "error" "ok")
                       (if err (sqlp:sqlite-error-message err) "")
                       (if err (error-code err) 0)
                       (length results))))
      (dolist (r (reverse results))
        (destructuring-bind (cols . rows) r
          (setf items (append items (list (length cols)) cols (list (length rows))))
          (dolist (row rows) (setf items (append items row)))))
      (send-list items))))

;;; testfixture's SQL functions (test_md5.c, test_func.c)

(defun md5-hex (octets)
  (format nil "~(~{~2,'0x~}~)" (coerce (sb-md5:md5sum-sequence octets) 'list)))

(defun value-text-octets (v)
  "sqlite3_value_text as a C string: NIL for NULL, and up to the first NUL."
  (unless (eq v :null)
    (let* ((o (if (stringp v) (sqlite-pure::utf8-encode v)
                  (sqlite-pure::value-to-blob v)))
           (z (position 0 o)))
      (if z (subseq o 0 z) o))))

(defun install-test-functions (db)
  ;; md5sum(...): the MD5 of every non-NULL argument's text, over all rows
  (sqlp:define-aggregate db "md5sum"
    (lambda (state &rest args)
      (dolist (a args state)
        (let ((o (value-text-octets a))) (when o (push o state)))))
    :initial nil
    :final (lambda (state)
             (md5-hex (let ((all (reverse state)))
                        (apply #'concatenate '(vector (unsigned-byte 8)) all)))))
  ;; randstr(MIN, MAX): a random string of MIN..MAX characters
  (sqlp:define-function db "randstr"
    (lambda (lo hi)
      (let* ((src ".-!,:*^+=_|?/<> abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")
             (lo (min 999 (max 0 (sqlite-pure::value-to-integer lo))))
             (hi (min 999 (max lo (sqlite-pure::value-to-integer hi))))
             (n (+ lo (if (> hi lo) (random (1+ (- hi lo))) 0))))
        (let ((s (make-string n)))
          (dotimes (i n s) (setf (char s i) (char src (random (length src))))))))
    :arity 2))

;;; requests

(defun tcl-function (id)
  (lambda (&rest args)
    (multiple-value-bind (v errp) (apply #'ask "call" id args)
      (if errp
          (error 'sqlp:sqlite-error :message (if (stringp v) v "error"))
          v))))

(defun handle (req)
  (let ((op (first req)) (args (rest req)))
    (cond
      ((equal op "open")
       (destructuring-bind (path readonly) args
         (handler-case
             (progn (setf *db* (sqlp:open-database (if (equal path "") ":memory:" path)
                                                   :readonly (eql readonly 1)))
                  (install-test-functions *db*)
                  (send "ok"))
           (sqlp:sqlite-error (c) (send "error" (sqlp:sqlite-error-message c)))
           (error (c) (send "error" (format nil "~a" c))))))
      ((equal op "eval") (do-eval (first args)))
      ((equal op "md5") (send "ok" (md5-hex (sqlite-pure::utf8-encode (first args)))))
      ((equal op "close")
       (ignore-errors (sqlp:close-database *db*))
       (send "ok")
       (sb-ext:exit :code 0 :abort t))
      ((equal op "changes") (send "ok" (sqlp:changes *db*)))
      ((equal op "total_changes") (send "ok" (sqlite-pure::db-total-changes (sqlite-pure::conn *db*))))
      ((equal op "last_insert_rowid") (send "ok" (sqlp:last-insert-rowid *db*)))
      ((equal op "autocommit") (send "ok" (if (sqlp:in-transaction-p *db*) 0 1)))
      ((equal op "errorcode") (send "ok" *last-code*))
      ((equal op "complete") (send "ok" (if (sqlite-pure.shell::sql-complete-p (first args)) 1 0)))
      ((equal op "func")
       (destructuring-bind (name nargs id) args
         (sqlp:define-function *db* name (tcl-function id) :arity nargs)
         (send "ok")))
      ((equal op "collate")
       (destructuring-bind (name id) args
         (sqlp:define-collation *db* name
           (lambda (a b)
             (multiple-value-bind (v errp) (ask "coll" id a b)
               (if (or errp (not (integerp v))) 0 v))))
         (send "ok")))
      (t (send "error" (format nil "unknown request ~a" op))))))

(defun main ()
  (let ((*in* (sb-sys:make-fd-stream 0 :input t :element-type '(unsigned-byte 8) :buffering :full))
        (*out* (sb-sys:make-fd-stream 1 :output t :element-type '(unsigned-byte 8) :buffering :full)))
    (loop for req = (read-frame)
          while req
          do (handle req))
    (sb-ext:exit :code 0 :abort t)))
