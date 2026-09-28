;;;; shell/shell.lisp — sqlp, a command-line shell for sqlite-pure that
;;;; behaves like SQLite's own sqlite3 (3.40): the same options, prompts,
;;;; statement completion, output modes (list, csv, column, table, box,
;;;; markdown, line, json, html, insert, quote, tabs, tcl, ascii), error
;;;; reports, and the everyday dot-commands.  Output is produced byte for
;;;; byte as shell.c produces it, so scripts written against sqlite3 read the
;;;; same text.  SBCL only (file descriptors, isatty, chdir, run-program).

(defpackage #:sqlite-pure.shell
  (:use #:cl)
  (:export #:main #:toplevel))

(in-package #:sqlite-pure.shell)

(defparameter *version* "3.40.1")
(defparameter *source-id* "2022-12-28 14:03:47 sqlite-pure")

;;; ------------------------------------------------------------------
;;; Bytes.  Cell text is UTF-8 octets, as shell.c's char* is.

(deftype octets () '(simple-array (unsigned-byte 8) (*)))

(defun b (x)
  "X as UTF-8 octets."
  (etypecase x
    ((simple-array (unsigned-byte 8) (*)) x)
    (string (sqlite-pure::utf8-encode x))
    (vector (coerce x 'octets))))

(defun s (octs)
  "Octets as a Lisp string (lenient)."
  (if (stringp octs) octs (sqlite-pure::utf8-decode-lenient octs)))

(defun bcat (&rest parts)
  (let* ((bs (mapcar #'b parts)) (out (make-array (reduce #'+ bs :key #'length) :element-type '(unsigned-byte 8))))
    (loop with i = 0 for x in bs do (replace out x :start1 i) (incf i (length x)))
    out))

(defun starts-with-p (s prefix)
  (and (stringp s) (>= (length s) (length prefix)) (string= s prefix :end1 (length prefix))))

(defun string-prefix-ci-p (prefix s)
  (and (>= (length s) (length prefix)) (string-equal s prefix :end1 (length prefix))))

(defun char-count (octs)
  "strlenChar: characters in UTF-8 octets."
  (count-if (lambda (c) (/= (logand c #xc0) #x80)) octs))

;;; ------------------------------------------------------------------
;;; State

(defstruct (shell (:conc-name sh-))
  db filename (open-flags nil) readonly
  (mode :list) (c-mode :list)
  (col-sep "|") (row-sep (string #\Newline)) (null-value "")
  show-header header-set
  (widths '()) actual
  (wrap 60) wordwrap quote
  (dest-table "\"table\"")
  out out-name once
  echo bail count-changes timer auto-eqp
  (main-prompt "sqlite> ") (cont-prompt "   ...> ")
  in (lineno 0) (nesting 0) interactive
  (cnt 0) (nerr 0) writable-schema)

(defvar *stdout*)
(defvar *stderr*)
(defvar *stdin*)
(defvar *newlines* nil "SHFLG_Newlines: .dump --newlines.")

(defun out (sh x)
  (let ((o (sh-out sh)))
    (write-sequence (b x) o)))

(defun err (fmt &rest args)
  (write-sequence (b (apply #'format nil fmt args)) *stderr*)
  (force-output *stderr*))

(defun flush (sh) (force-output (sh-out sh)))

;;; ------------------------------------------------------------------
;;; Values as shell.c sees them (sqlite3_column_text / _type)

(defun col-type (v)
  (cond ((eq v :null) :null) ((integerp v) :integer) ((floatp v) :float)
        ((stringp v) :text) (t :blob)))

(defun c-str (octs)
  "OCTS up to the first NUL, as a char* reads them."
  (let ((z (position 0 octs))) (if z (subseq octs 0 z) octs)))

(defun col-text (v)
  "sqlite3_column_text: octets, or NIL for NULL."
  (cond ((eq v :null) nil)
        ((integerp v) (b (princ-to-string v)))
        ((floatp v) (b (sqlite-pure::format-real v)))
        (t (c-str (b v)))))

(defun printf (fmt &rest args) (sqlite-pure::sql-printf fmt args))

;;; ------------------------------------------------------------------
;;; Quoting helpers (output_quoted_string & co.)

(defun quote-char (name)
  "quoteChar: #\\\" if NAME needs quoting as an identifier, else NIL."
  (let ((n (s name)))
    (if (or (zerop (length n))
            (not (or (alpha-char-p (char n 0)) (char= (char n 0) #\_)))
            (notevery (lambda (c) (or (and (< (char-code c) 128) (alphanumericp c)) (char= c #\_))) n)
            (sqlite-pure::reserved-p n))
        #\" nil)))

(defun ident (name &optional (q (quote-char name)))
  (if q (format nil "\"~a\"" (sqlite-pure::substitute-string "\"" "\"\"" (s name))) (s name)))

(defun quoted-string (octs)
  "output_quoted_string."
  (let ((o (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0)))
    (vector-push-extend 39 o)
    (loop for c across octs do (vector-push-extend c o) (when (= c 39) (vector-push-extend 39 o)))
    (vector-push-extend 39 o)
    (coerce o 'octets)))

(defun unused-string (z a bb)
  (let ((zs (s z)))
    (cond ((not (search a zs)) a)
          ((not (search bb zs)) bb)
          (t (loop for i from 0
                   for cand = (format nil "(~a~d)" a i)
                   unless (search cand zs) return cand)))))

(defun quoted-escaped-string (octs)
  "output_quoted_escaped_string: newlines and CRs as replace(...)."
  (if (not (find-if (lambda (c) (member c '(39 10 13))) octs))
      (bcat "'" octs "'")
      (let* ((nnl (count 10 octs)) (ncr (count 13 octs))
             (znl (and (plusp nnl) (unused-string octs "\\n" "\\012")))
             (zcr (and (plusp ncr) (unused-string octs "\\r" "\\015")))
             (o (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0)))
        (flet ((put (x) (loop for c across (b x) do (vector-push-extend c o))))
          (when (plusp nnl) (put "replace("))
          (when (plusp ncr) (put "replace("))
          (put "'")
          (loop for c across octs
                do (cond ((= c 39) (put "''"))
                         ((= c 10) (put znl))
                         ((= c 13) (put zcr))
                         (t (vector-push-extend c o))))
          (put "'")
          (when (plusp ncr) (put (format nil ",'~a',char(13))" zcr)))
          (when (plusp nnl) (put (format nil ",'~a',char(10))" znl))))
        (coerce o 'octets))))

(defun c-string (x)
  "output_c_string."
  (with-output-to-string (o)
    (write-char #\" o)
    (loop for c across (b x)
          do (case c
               (92 (write-string "\\\\" o))
               (34 (write-string "\\\"" o))
               (9 (write-string "\\t" o))
               (10 (write-string "\\n" o))
               (13 (write-string "\\r" o))
               (t (if (or (< c 32) (> c 126))
                      (format o "\\~3,'0o" c)
                      (write-char (code-char c) o)))))
    (write-char #\" o)))

(defun json-string (octs)
  "output_json_string."
  (let ((o (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0)))
    (flet ((put (x) (loop for c across (b x) do (vector-push-extend c o))))
      (put "\"")
      (loop for c across octs
            do (cond ((or (= c 92) (= c 34)) (vector-push-extend 92 o) (vector-push-extend c o))
                     ((<= c 31) (put (case c (8 "\\b") (12 "\\f") (10 "\\n") (13 "\\r") (9 "\\t")
                                       (t (format nil "\\u~(~4,'0x~)" c)))))
                     (t (vector-push-extend c o))))
      (put "\""))
    (coerce o 'octets)))

(defun html-string (octs)
  (let ((o (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0)))
    (loop for c across octs
          do (let ((rep (case c (60 "&lt;") (38 "&amp;") (62 "&gt;") (34 "&quot;") (39 "&#39;"))))
               (if rep (loop for x across (b rep) do (vector-push-extend x o)) (vector-push-extend c o))))
    (coerce o 'octets)))

(defun hex-blob (octs)
  (format nil "X'~(~{~2,'0x~}~)'" (coerce octs 'list)))

(defun csv-field (sh octs)
  "output_csv (without the separator)."
  (if (null octs)
      (b (sh-null-value sh))
      (if (or (zerop (length octs))
              (find-if (lambda (c) (or (<= c 32) (> c 126) (member c '(34 39)))) octs)
              (search (b (sh-col-sep sh)) octs))
          (let ((o (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0)))
            (vector-push-extend 34 o)
            (loop for c across octs do (vector-push-extend c o) (when (= c 34) (vector-push-extend 34 o)))
            (vector-push-extend 34 o)
            (coerce o 'octets))
          octs)))

(defun real-20g (v)
  (cond ((and (sqlite-pure::float-infinity-p v) (plusp v)) "1e999")
        ((sqlite-pure::float-infinity-p v) "-1e999")
        (t (printf "%!.20g" v))))

;;; ------------------------------------------------------------------
;;; Row output (shell_callback)

(defun print-dashes (sh n) (out sh (make-string (max 0 n) :initial-element #\-)))

(defun width-print (sh w octs)
  "utf8_width_print."
  (let* ((aw (abs w)) (octs (or octs (b ""))) (n 0) (i 0) (len (length octs)))
    (loop while (< i len)
          do (when (/= (logand (aref octs i) #xc0) #x80)
               (incf n)
               (when (= n aw)
                 (incf i)
                 (loop while (and (< i len) (= (logand (aref octs i) #xc0) #x80)) do (incf i))
                 (return)))
             (incf i))
    (cond ((>= n aw) (out sh (subseq octs 0 (min i len))))
          ((< w 0) (out sh (make-string (- aw n) :initial-element #\Space)) (out sh octs))
          (t (out sh octs) (out sh (make-string (- aw n) :initial-element #\Space))))))

(defun row-out (sh cols vals)
  "One row (shell_callback) in the current mode."
  (let* ((n (length cols)) (rs (sh-row-sep sh)) (cs (sh-col-sep sh))
         (texts (mapcar #'col-text vals))
         (first (= (sh-cnt sh) 0)))
    (flet ((txt (i) (nth i texts)) (col (i) (b (nth i cols))))
      (ecase (sh-c-mode sh)
        ((:off :count) (incf (sh-cnt sh)))
        (:line
         (let ((w (max 5 (reduce #'max cols :key (lambda (c) (length (b c))) :initial-value 0))))
           (when (plusp (sh-cnt sh)) (out sh rs))
           (incf (sh-cnt sh))
           (dotimes (i n)
             (out sh (make-string (max 0 (- w (length (col i)))) :initial-element #\Space))
             (out sh (col i)) (out sh " = ") (out sh (or (txt i) (sh-null-value sh))) (out sh rs))))
        (:list
         (when (and first (sh-show-header sh))
           (dotimes (i n) (out sh (col i)) (out sh (if (= i (1- n)) rs cs))))
         (incf (sh-cnt sh))
         (dotimes (i n) (out sh (or (txt i) (sh-null-value sh))) (out sh (if (= i (1- n)) rs cs))))
        (:html
         (when (and first (sh-show-header sh))
           (out sh "<TR>")
           (dotimes (i n) (out sh "<TH>") (out sh (html-string (col i))) (out sh (format nil "</TH>~%")))
           (out sh (format nil "</TR>~%")))
         (incf (sh-cnt sh))
         (out sh "<TR>")
         (dotimes (i n) (out sh "<TD>") (out sh (html-string (or (txt i) (b (sh-null-value sh))))) (out sh (format nil "</TD>~%")))
         (out sh (format nil "</TR>~%")))
        (:tcl
         (when (and first (sh-show-header sh))
           (dotimes (i n) (out sh (c-string (col i))) (when (< i (1- n)) (out sh cs)))
           (out sh rs))
         (incf (sh-cnt sh))
         (dotimes (i n) (out sh (c-string (or (txt i) (sh-null-value sh)))) (when (< i (1- n)) (out sh cs)))
         (out sh rs))
        (:csv
         (when (and first (sh-show-header sh))
           (dotimes (i n) (out sh (csv-field sh (col i))) (when (< i (1- n)) (out sh cs)))
           (out sh rs))
         (incf (sh-cnt sh))
         (when (plusp n)
           (dotimes (i n) (out sh (csv-field sh (txt i))) (when (< i (1- n)) (out sh cs)))
           (out sh rs)))
        (:insert
         (out sh (format nil "INSERT INTO ~a" (sh-dest-table sh)))
         (when (sh-show-header sh)
           (out sh "(")
           (dotimes (i n) (when (plusp i) (out sh ",")) (out sh (ident (nth i cols))))
           (out sh ")"))
         (incf (sh-cnt sh))
         (dotimes (i n)
           (out sh (if (plusp i) "," " VALUES("))
           (let ((v (nth i vals)))
             (ecase (col-type v)
               (:null (out sh "NULL"))
               (:text (out sh (if *newlines* (quoted-string (txt i)) (quoted-escaped-string (txt i)))))
               (:integer (out sh (txt i)))
               (:float (out sh (if (and (not (sqlite-pure::float-infinity-p v)) (= v (ftruncate v))
                                        (< (abs v) 9.2d18))
                                   (format nil "~d.0" (truncate v))
                                   (real-20g v))))
               (:blob (out sh (hex-blob v))))))
         (out sh (format nil ");~%")))
        (:json
         (out sh (if (zerop (sh-cnt sh)) "[{" (format nil ",~%{")))
         (incf (sh-cnt sh))
         (dotimes (i n)
           (out sh (json-string (col i))) (out sh ":")
           (let ((v (nth i vals)))
             (ecase (col-type v)
               (:null (out sh "null"))
               (:float (out sh (real-20g v)))
               (:blob (out sh (json-string v)))
               (:text (out sh (json-string (txt i))))
               (:integer (out sh (txt i)))))
           (when (< i (1- n)) (out sh ",")))
         (out sh "}"))
        (:quote
         (when (and first (sh-show-header sh))
           (dotimes (i n) (when (plusp i) (out sh cs)) (out sh (quoted-string (col i))))
           (out sh rs))
         (incf (sh-cnt sh))
         (dotimes (i n)
           (when (plusp i) (out sh cs))
           (let ((v (nth i vals)))
             (ecase (col-type v)
               (:null (out sh "NULL"))
               (:text (out sh (quoted-string (txt i))))
               (:integer (out sh (txt i)))
               (:float (out sh (printf "%!.20g" v)))
               (:blob (out sh (hex-blob v))))))
         (out sh rs))
        (:ascii
         (when (and first (sh-show-header sh))
           (dotimes (i n) (when (plusp i) (out sh cs)) (out sh (col i)))
           (out sh rs))
         (incf (sh-cnt sh))
         (dotimes (i n) (when (plusp i) (out sh cs)) (out sh (or (txt i) (sh-null-value sh))))
         (out sh rs))))))

;;; Columnar modes (exec_prepared_stmt_columnar)

(defun translate-for-display (z mx wordwrap)
  "translateForDisplayAndDup: (values display-octets tail-octets-or-nil)."
  (if (null z)
      (values nil nil)
      (let* ((mx (if (zerop mx) 1000000 (abs mx)))
             (len (length z)) (i 0) (j 0) (n 0) k)
        (flet ((at (x) (if (< x len) (aref z x) 0)))
          (loop while (< n mx)
                do (cond ((>= (at i) 32)
                          (incf n)
                          (loop do (incf i) (incf j) while (= (logand (at i) #xc0) #x80)))
                         ((= (at i) 9)
                          (loop do (incf n) (incf j) while (and (/= (logand n 7) 0) (< n mx)))
                          (incf i))
                         (t (return))))
          (if (and (>= n mx) wordwrap)
              (progn
                (setf k i)
                (loop while (> k (floor i 2))
                      do (when (member (at (1- k)) '(32 9 10 11 12 13)) (return))
                         (decf k))
                (when (<= k (floor i 2))
                  (setf k i)
                  (loop while (> k (floor i 2))
                        do (when (and (not (eq (alnum-p (at (1- k))) (alnum-p (at k))))
                                      (/= (logand (at k) #xc0) #x80))
                             (return))
                           (decf k)))
                (if (<= k (floor i 2))
                    (setf k i)
                    (progn (setf i k) (loop while (= (at i) 32) do (incf i)))))
              (setf k i))
          (let ((tail (cond ((and (>= n mx) (>= (at i) 32)) (subseq z i))
                            ((and (= (at i) 13) (= (at (1+ i)) 10)) (if (> len (+ i 2)) (subseq z (+ i 2)) nil))
                            ((or (>= i len) (>= (1+ i) len)) nil)
                            (t (subseq z (1+ i)))))
                (o (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0)))
            (setf i 0 n 0)
            (loop while (< i k)
                  do (cond ((>= (at i) 32)
                            (incf n)
                            (loop do (vector-push-extend (at i) o) (incf i) while (= (logand (at i) #xc0) #x80)))
                           ((= (at i) 9)
                            (loop do (incf n) (vector-push-extend 32 o) while (and (/= (logand n 7) 0) (< n mx)))
                            (incf i))
                           (t (return))))
            (values (coerce o 'octets) tail))))))

(defun alnum-p (c) (and (< c 128) (alphanumericp (code-char c))))

(defun quoted-column (v)
  (ecase (col-type v)
    (:null (b "NULL"))
    ((:integer :float) (col-text v))
    (:text (b (printf "%Q" v)))
    (:blob (b (format nil "x'~(~{~2,'0x~}~)'" (coerce v 'list))))))

(defun box-line (sh n) (dotimes (i n) (out sh (string (code-char #x2500)))))

(defun columnar-out (sh cols rows)
  (when (null rows) (return-from columnar-out))
  (let* ((ncol (length cols)) (mode (sh-c-mode sh))
         (widths (let ((w (sh-widths sh))) (loop for i below ncol collect (or (nth i w) 0))))
         (actual (mapcar #'abs widths))
         (data '()) (row-div '()) (multiline nil))
    (flet ((wrapw (i) (let ((w (nth i widths))) (abs (if (zerop w) (sh-wrap sh) w)))))
      ;; headers
      (let ((hdr (loop for c in cols for i from 0
                       collect (translate-for-display (b c) (wrapw i) (sh-wordwrap sh)))))
        (push hdr data))
      (dolist (r rows)
        (let ((next (loop for v in r collect (if (sh-quote sh) (quoted-column v)
                                                 (or (col-text v) (b (sh-null-value sh)))))))
          (loop
            (let ((line '()) (tails '()) (more nil))
              (loop for z in next for i from 0
                    do (multiple-value-bind (d tail) (translate-for-display (or z (b "")) (wrapw i) (sh-wordwrap sh))
                         (push d line) (push tail tails)
                         (when tail (setf more t))))
              (push (nreverse line) data)
              (push (not more) row-div)
              (when more (setf multiline t))
              (unless more (return))
              (setf next (mapcar (lambda (x) (or x (b ""))) (nreverse tails)))))))
      (setf data (nreverse data) row-div (nreverse row-div))
      (dolist (r data)
        (loop for d in r for i from 0
              do (setf (nth i actual) (max (nth i actual) (char-count (or d (b ""))))))))
    (setf (sh-actual sh) actual)
    (let* ((hdr (first data)) (body (rest data))
           (cs (case mode (:column "  ") (:box (format nil " ~a " (code-char #x2502))) (t " | ")))
           (rs (case mode (:column (string #\Newline)) (:box (format nil " ~a~%" (code-char #x2502)))
                 (t (format nil " |~%")))))
      (labels ((sep-row (ch)
                 (out sh ch)
                 (loop for w in actual for i from 0
                       do (print-dashes sh (+ w 2)) (out sh ch))
                 (out sh (string #\Newline)))
               (box-sep (a mid z)
                 (out sh (string (code-char a)))
                 (loop for w in actual for i from 0
                       do (box-line sh (+ w 2))
                          (out sh (string (code-char (if (= i (1- ncol)) z mid)))))
                 (out sh (string #\Newline)))
               (centered (i)
                 (let* ((w (nth i actual)) (d (nth i hdr)) (n (char-count d)))
                   (out sh (make-string (floor (- w n) 2) :initial-element #\Space))
                   (out sh d)
                   (out sh (make-string (floor (+ (- w n) 1) 2) :initial-element #\Space)))))
        (case mode
          (:column
           (when (sh-show-header sh)
             (dotimes (i ncol)
               (width-print sh (if (minusp (nth i widths)) (- (nth i actual)) (nth i actual)) (nth i hdr))
               (out sh (if (= i (1- ncol)) (string #\Newline) "  ")))
             (dotimes (i ncol)
               (print-dashes sh (nth i actual))
               (out sh (if (= i (1- ncol)) (string #\Newline) "  ")))))
          (:table
           (sep-row "+")
           (out sh "| ")
           (dotimes (i ncol) (centered i) (out sh (if (= i (1- ncol)) (format nil " |~%") " | ")))
           (sep-row "+"))
          (:markdown
           (out sh "| ")
           (dotimes (i ncol) (centered i) (out sh (if (= i (1- ncol)) (format nil " |~%") " | ")))
           (sep-row "|"))
          (:box
           (box-sep #x250c #x252c #x2510)
           (out sh (format nil "~a " (code-char #x2502)))
           (dotimes (i ncol)
             (centered i)
             (out sh (if (= i (1- ncol)) (format nil " ~a~%" (code-char #x2502)) (format nil " ~a " (code-char #x2502)))))
           (box-sep #x251c #x253c #x2524)))
        (loop for r in body for div in row-div for k from 0
              do (unless (eq mode :column) (out sh (if (eq mode :box) (format nil "~a " (code-char #x2502)) "| ")))
                 (loop for d in r for i from 0
                       do (width-print sh (if (minusp (nth i widths)) (- (nth i actual)) (nth i actual))
                                       (or d (b (sh-null-value sh))))
                          (out sh (if (= i (1- ncol)) rs cs)))
                 (when (and multiline div (< (1+ k) (length body)))
                   (case mode
                     (:table (sep-row "+"))
                     (:box (box-sep #x251c #x253c #x2524))
                     (:column (out sh (string #\Newline))))))
        (case mode
          (:table (sep-row "+"))
          (:box (box-sep #x2514 #x2534 #x2518)))))))

;;; EXPLAIN QUERY PLAN as a tree (eqp_render)

(defun eqp-render (sh rows)
  "ROWS: (id parent notused detail)."
  (when rows
    (let ((rows (copy-list rows)))
      (if (and (stringp (fourth (first rows))) (plusp (length (fourth (first rows))))
               (char= (char (fourth (first rows)) 0) #\-))
          (progn
            (when (null (rest rows)) (return-from eqp-render))
            (out sh (format nil "~a~%" (subseq (fourth (first rows)) 3)))
            (pop rows))
          (out sh (format nil "QUERY PLAN~%")))
      (labels ((level (id prefix)
                 (let ((kids (remove-if-not (lambda (r) (eql (second r) id)) rows)))
                   (loop for (r . more) on kids
                         do (out sh (format nil "~a~a~a~%" prefix (if more "|--" "`--") (fourth r)))
                            (level (first r) (concatenate 'string prefix (if more "|  " "   ")))))))
        (level 0 "")))))

;;; ------------------------------------------------------------------
;;; Statements

(defun complete-state (sql)
  "sqlite3_complete's state after SQL (1 = complete)."
  (let ((state 0) (i 0) (n (length sql)))
    (flet ((trans (tok)
             (setf state
                   (aref #2A((1 0 2 3 4 2 2 2) (1 1 2 3 4 2 2 2) (1 2 2 2 2 2 2 2) (1 3 3 2 4 2 2 2)
                             (1 4 2 2 2 4 5 2) (6 5 5 5 5 5 5 5) (6 6 5 5 5 5 5 7) (1 7 5 5 5 5 5 5))
                         state tok))))
      (loop while (< i n)
            do (let ((c (char sql i)))
                 (cond
                   ((char= c #\;) (trans 0) (incf i))
                   ((member c '(#\Space #\Tab #\Newline #\Return #\Page)) (trans 1) (incf i))
                   ((and (char= c #\/) (< (1+ i) n) (char= (char sql (1+ i)) #\*))
                    (let ((e (search "*/" sql :start2 (+ i 2))))
                      (unless e (return-from complete-state 0))
                      (setf i (+ e 2)) (trans 1)))
                   ((and (char= c #\-) (< (1+ i) n) (char= (char sql (1+ i)) #\-))
                    (let ((e (position #\Newline sql :start i)))
                      (unless e (return-from complete-state state))
                      (setf i (1+ e)) (trans 1)))
                   ((char= c #\[)
                    (let ((e (position #\] sql :start (1+ i))))
                      (unless e (return-from complete-state 0))
                      (setf i (1+ e)) (trans 2)))
                   ((member c '(#\` #\" #\'))
                    (let ((e (position c sql :start (1+ i))))
                      (unless e (return-from complete-state 0))
                      (setf i (1+ e)) (trans 2)))
                   ((or (alpha-char-p c) (char= c #\_) (> (char-code c) 127))
                    (let* ((e (or (position-if-not (lambda (x) (or (alphanumericp x) (char= x #\_) (char= x #\$)
                                                                    (> (char-code x) 127)))
                                                   sql :start i)
                                  n))
                           (w (string-downcase (subseq sql i e))))
                      (setf i e)
                      (trans (cond ((string= w "create") 4)
                                   ((string= w "trigger") 6)
                                   ((or (string= w "temp") (string= w "temporary")) 5)
                                   ((string= w "end") 7)
                                   ((string= w "explain") 3)
                                   (t 2)))))
                   (t (trans 2) (incf i)))))
      state)))

(defun sql-complete-p (sql) (= (complete-state sql) 1))

(defun split-statements (sql)
  "The statements of SQL, each with its trailing text trimmed, as
sqlite3_prepare would take them one after another."
  (let ((out '()) (start 0) (n (length sql)))
    ;; cut after each ';' that completes a statement
    (loop for i from 0 below n
          do (when (and (char= (char sql i) #\;) (sql-complete-p (subseq sql start (1+ i))))
               (push (subseq sql start (1+ i)) out)
               (setf start (1+ i))))
    (when (< start n) (push (subseq sql start) out))
    (remove-if (lambda (x) (every (lambda (c) (member c '(#\Space #\Tab #\Newline #\Return #\Page #\;))) (strip-comments x)))
               (nreverse out))))

(defun strip-comments (sql)
  (let ((o (make-string-output-stream)) (i 0) (n (length sql)))
    (loop while (< i n)
          do (let ((c (char sql i)))
               (cond ((and (char= c #\-) (< (1+ i) n) (char= (char sql (1+ i)) #\-))
                      (setf i (or (position #\Newline sql :start i) n)))
                     ((and (char= c #\/) (< (1+ i) n) (char= (char sql (1+ i)) #\*))
                      (setf i (let ((e (search "*/" sql :start2 (+ i 2)))) (if e (+ e 2) n))))
                     ((member c '(#\' #\" #\` #\[))
                      (let ((e (position (if (char= c #\[) #\] c) sql :start (1+ i))))
                        (write-string (subseq sql i (if e (1+ e) n)) o)
                        (setf i (if e (1+ e) n))))
                     (t (write-char c o) (incf i)))))
    (get-output-stream-string o)))

(defun error-code-number (c)
  (case (sqlite-pure:sqlite-error-code c)
    (:busy 5) (:locked 6) (:readonly 8) (:interrupt 9) (:corrupt 11) (:full 13) (:cantopen 14)
    (:toobig 18) (:constraint 19) (:mismatch 20) (:range 25) (:notadb 26) (:abort 4)
    (t 1)))

(defparameter *prepare-errors*
  '("near \"" "incomplete input" "unrecognized token" "unterminated" "no such table" "no such column"
    "no such function" "wrong number of arguments" "ambiguous column name" "no such index"
    "no such view" "no such trigger" "misuse of" "aggregate functions are not allowed"
    "already exists" "has no column named" "values for" "columns but" "cannot UPDATE generated"
    "cannot INSERT into generated" "ORDER BY term out of" "GROUP BY term out of" "1st ORDER BY"
    "2nd ORDER BY" "3rd ORDER BY" "ORDER BY clause should come after" "LIMIT clause should come after"
    "SELECTs to the left and right" "sub-select returns" "row value misused" "circular reference"
    "DISTINCT aggregates must have exactly one argument" "no such collation sequence"
    "use DROP" "may not be" "cannot modify" "is not a function" "no such savepoint" "hex literal too big"
    "malformed blob literal" "bad parameter name" "unknown database" "no such module"
    "duplicate column name" "more than one primary key" "no such window"
    "may only be used within a trigger-program" "there is already"
    "recursive references" "references to recursive table"
    "unable to identify the object to be reindexed"
    "table" "index" "view" "trigger"))

(defun prepare-error-p (msg)
  (let ((m (string-downcase msg)))
    (some (lambda (p) (let ((pl (string-downcase p)))
                        (and (search pl m) (not (member p '("table" "index" "view" "trigger") :test #'string=)))))
          *prepare-errors*)))

(defun error-offset (c sql)
  "Where in SQL the error points (sqlite3_error_offset), or NIL."
  (or (sqlite-pure:sqlite-error-offset c)
      (let ((msg (sqlite-pure:sqlite-error-message c)))
        (flet ((find-qualified (qual col)
                 ;; QUAL . COL as three tokens: the position of QUAL
                 (let ((toks (ignore-errors (sqlite-pure::tokenize sql))))
                   (when toks
                     (flet ((tok= (k name)
                              (and (< k (length toks))
                                   (member (sqlite-pure::tok-kind (aref toks k)) '(:id :string))
                                   (string-equal (princ-to-string (sqlite-pure::tok-value (aref toks k))) name))))
                       (loop for k below (- (length toks) 2)
                             when (and (tok= k qual)
                                       (equal (sqlite-pure::tok-value (aref toks (1+ k))) ".")
                                       (tok= (+ k 2) col))
                               return (sqlite-pure::tok-pos (aref toks k)))))))
               (find-bare (name)
                 ;; NAME as a token of its own: not qualifying, not qualified
                 (let ((toks (ignore-errors (sqlite-pure::tokenize sql))))
                   (when toks
                     (flet ((dot-p (k) (and (< -1 k (length toks))
                                            (equal (sqlite-pure::tok-value (aref toks k)) "."))))
                       (loop for k below (length toks)
                             for tk = (aref toks k)
                             when (and (member (sqlite-pure::tok-kind tk) '(:id :string))
                                       (string-equal (princ-to-string (sqlite-pure::tok-value tk)) name)
                                       (not (dot-p (1- k))) (not (dot-p (1+ k))))
                               return (sqlite-pure::tok-pos tk))))))
               (find-ident (name &optional before-paren (update-p (string-prefix-ci-p "UPDATE" (string-left-trim " " sql))))
                 (let ((toks (ignore-errors (sqlite-pure::tokenize sql))))
                   (when toks
                     (loop for k below (length toks)
                           for tk = (aref toks k)
                           when (and (member (sqlite-pure::tok-kind tk) '(:id :string))
                                     (stringp (princ-to-string (sqlite-pure::tok-value tk)))
                                     (string-equal (princ-to-string (sqlite-pure::tok-value tk)) name)
                                     (or (not before-paren)
                                         (and (< (1+ k) (length toks))
                                              (equal (sqlite-pure::tok-value (aref toks (1+ k))) "(")))
                                     ;; an UPDATE's SET target is reported without a position
                                     (not (and update-p (< (1+ k) (length toks))
                                               (equal (sqlite-pure::tok-value (aref toks (1+ k))) "="))))
                             return (sqlite-pure::tok-pos tk))))))
          (cond ((starts-with-p msg "no such column: ")
                 (let* ((name (subseq msg 16)) (dot (position #\. name :from-end t)))
                   (let ((pos (find-ident (if dot (subseq name (1+ dot)) name))))
                     (if (and pos dot)
                         (or (find-qualified (subseq name 0 dot) (subseq name (1+ dot)))
                             (find-ident (subseq name 0 dot)) pos)
                         pos))))
                ((and (search " already exists" msg)
                      (some (lambda (k) (starts-with-p msg k)) '("table " "view " "trigger ")))
                 (find-ident (subseq msg (1+ (position #\Space msg)) (search " already exists" msg))))
                ((starts-with-p msg "unknown database ")
                 (find-ident (subseq msg 17)))
                ((starts-with-p msg "ambiguous column name: ")
                 (let* ((name (subseq msg 23)) (dot (position #\. name :from-end t)))
                   (if dot
                       (or (find-qualified (subseq name 0 dot) (subseq name (1+ dot)))
                           (find-ident (subseq name (1+ dot))))
                       (or (find-bare name) (find-ident name)))))
                ((starts-with-p msg "no such function: ")
                 (find-ident (subseq msg 18) t))
                ((starts-with-p msg "wrong number of arguments to function ")
                 (find-ident (string-right-trim "()" (subseq msg 38)) t)))))))

(defun error-context (sql offset)
  "shell_error_context."
  (if (null offset)
      ""
      (let ((sql sql) (off offset))
        (loop while (> off 50) do (setf sql (subseq sql 1)) (decf off))
        (let* ((code (substitute-if #\Space (lambda (c) (member c '(#\Newline #\Tab #\Return #\Page)))
                                    (subseq sql 0 (min 78 (length sql))))))
          (if (< off 25)
              (format nil "~%  ~a~%  ~a^--- error here" code (make-string off :initial-element #\Space))
              (format nil "~%  ~a~%  ~aerror here ---^" code (make-string (- off 14) :initial-element #\Space)))))))

(defun statement-params (sh sql)
  "Values for SQL's parameters from temp.sqlite_parameters (.parameter)."
  (multiple-value-bind (stmts nparam names) (ignore-errors (sqlite-pure::parse-sql sql))
    (declare (ignore stmts))
    (when (and nparam (plusp nparam))
      (let ((table (ignore-errors
                    (sqlp:query (sh-db sh) "SELECT key, value FROM temp.sqlite_parameters"))))
        (loop for i from 1 to nparam
              collect (let* ((name (car (rassoc i names)))
                             (hit (and name (assoc name table :test #'string=))))
                        (if hit (second hit) :null)))))))

(defun open-db (sh)
  (unless (sh-db sh)
    (handler-case
        (setf (sh-db sh) (sqlp:open-database (or (sh-filename sh) ":memory:") :readonly (sh-readonly sh)))
      (error (e)
        (err "Error: unable to open database \"~a\": ~a~%" (sh-filename sh)
             (if (typep e 'sqlp:sqlite-error) (sqlp:sqlite-error-message e) e))
        (sb-ext:exit :code 1 :abort t)))
    (install-shell-functions sh))
  (sh-db sh))

(defun run-one-statement (sh sql)
  "Prepare and run one statement; signal SHELL-SQL-ERROR on failure."
  (let ((db (open-db sh)) (trimmed (string-left-trim '(#\Space #\Tab #\Newline #\Return) sql)))
    (setf (sh-cnt sh) 0 (sh-c-mode sh) (sh-mode sh))
    ;; syntax first: a statement that does not parse is a "Parse error"
    (handler-case (sqlite-pure::parse-sql sql)
      (sqlp:sqlite-error (c) (error 'shell-sql-error :phase "in prepare" :condition c :sql trimmed)))
    (when (and (sh-auto-eqp sh) (not (explain-p trimmed)))
      (let ((rows (ignore-errors (sqlp:query db (concatenate 'string "EXPLAIN QUERY PLAN " trimmed)))))
        (eqp-render sh rows)))
    (multiple-value-bind (rows cols)
        (handler-case (apply #'sqlp:query db sql (statement-params sh sql))
          (sqlp:sqlite-error (c)
            (error 'shell-sql-error :phase (if (prepare-error-p (sqlp:sqlite-error-message c)) "in prepare" "stepping")
                                    :condition c :sql trimmed)))
      (cond ((explain-qp-p trimmed) (eqp-render sh rows))
            ((null cols))
            ((member (sh-c-mode sh) '(:column :table :box :markdown)) (columnar-out sh cols rows))
            (t (dolist (r rows) (row-out sh cols r))
               (when rows
                 (case (sh-c-mode sh)
                   (:json (out sh (format nil "]~%")))
                   (:count (out sh (format nil "~d row~:p~%" (length rows)))))))))))

(defun explain-p (sql) (and (>= (length sql) 7) (string-equal (subseq sql 0 7) "explain")))
(defun explain-qp-p (sql)
  (let ((toks (ignore-errors (sqlite-pure::tokenize sql))))
    (and toks (> (length toks) 3)
         (loop for k below 3 for w in '("explain" "query" "plan")
               always (string-equal (princ-to-string (sqlite-pure::tok-value (aref toks k))) w)))))

(define-condition shell-sql-error (error)
  ((phase :initarg :phase :reader err-phase)
   (condition :initarg :condition :reader inner)
   (sql :initarg :sql :reader err-sql)))

(defun shell-exec (sh sql)
  "shell_exec: run every statement of SQL; NIL, or the error text (with
its phase prefix and context, as save_err_msg builds it)."
  (handler-case
      (progn (dolist (st (split-statements sql)) (run-one-statement sh st)) nil)
    (shell-sql-error (e)
      (let* ((c (inner e)) (code (error-code-number c)))
        (format nil "~a, ~a~@[ (~d)~]~a" (err-phase e) (sqlp:sqlite-error-message c) (and (> code 1) code)
                (error-context (err-sql e) (error-offset c (err-sql e))))))))

(defun run-sql-line (sh sql startline)
  "runOneSqlLine."
  (open-db sh)
  (let* ((t0 (get-internal-real-time)) (r0 (get-internal-run-time))
         (e (shell-exec sh sql)))
    (when (sh-timer sh)
      (let ((real (/ (- (get-internal-real-time) t0) internal-time-units-per-second))
            (user (/ (- (get-internal-run-time) r0) internal-time-units-per-second)))
        (out sh (format nil "Run Time: real ~,3f user ~,6f sys ~,6f~%" real user 0))))
    (cond (e
           (let* ((type (cond ((starts-with-p e "in prepare, ") "Parse error")
                              ((starts-with-p e "stepping, ") "Runtime error")
                              (t "Error")))
                  (tail (subseq e (cond ((string= type "Parse error") 12) ((string= type "Runtime error") 10) (t 0)))))
             (flush sh)
             (if (or (sh-in sh) (not (sh-interactive sh)))
                 (err "~a near line ~d: ~a~%" type startline tail)
                 (err "~a: ~a~%" type tail))
             1))
          (t (when (sh-count-changes sh)
               (out sh (format nil "changes: ~d   total_changes: ~d~%"
                               (sqlp:changes (sh-db sh)) (sqlite-pure::db-total-changes (sqlite-pure::conn (sh-db sh))))))
             0))))

;;; SQL functions the dot-commands use

(defun install-shell-functions (sh)
  (sqlp:define-function (sh-db sh) "shell_add_schema"
    (lambda (sql schema name)
      (add-schema-name sh sql schema name))
    :arity 3))

(defun add-schema-name (sh sql schema name)
  "shellAddSchemaName."
  (if (and (stringp sql) (starts-with-p sql "CREATE "))
      (dolist (prefix '("TABLE" "INDEX" "UNIQUE INDEX" "VIEW" "TRIGGER" "VIRTUAL TABLE") sql)
        (let ((n (length prefix)))
          (when (and (> (length sql) (+ 7 n)) (string= (subseq sql 7 (+ 7 n)) prefix)
                     (char= (char sql (+ 7 n)) #\Space))
            (let ((z nil) (fake nil))
              (when (stringp schema)
                (setf z (if (and (quote-char schema) (string-not-equal schema "temp"))
                            (format nil "~a \"~a\".~a" (subseq sql 0 (+ 7 n))
                                    (sqlite-pure::substitute-string "\"" "\"\"" schema) (subseq sql (+ n 8)))
                            (format nil "~a ~a.~a" (subseq sql 0 (+ 7 n)) schema (subseq sql (+ n 8))))))
              (when (and (stringp name) (char= (char prefix 0) #\V)
                         (setf fake (fake-schema sh schema name)))
                (setf z (format nil "~a~%/* ~a */" (or z sql) fake)))
              (return (or z sql))))))
      (if (stringp sql) sql :null)))

(defun fake-schema (sh schema name)
  (let ((cols (ignore-errors (sqlp:query (sh-db sh) (format nil "PRAGMA \"~a\".table_info(~a)"
                                                             (sqlite-pure::substitute-string "\"" "\"\"" (if (stringp schema) schema "main"))
                                                             (printf "%Q" name))))))
    (when cols
      (format nil "~@[~a.~]~a(~{~a~^,~})"
              (and (stringp schema) (if (string-equal schema "temp") schema (ident schema)))
              (ident name)
              (mapcar (lambda (r) (ident (second r))) cols)))))

;;; ------------------------------------------------------------------
;;; Dot-commands

(defun resolve-backslashes (z)
  (let ((o (make-string-output-stream)) (i 0) (n (length z)))
    (loop while (< i n)
          do (let ((c (char z i)))
               (if (and (char= c #\\) (< (1+ i) n))
                   (let ((d (char z (incf i))))
                     (incf i)
                     (case d
                       (#\a (write-char (code-char 7) o)) (#\b (write-char (code-char 8) o))
                       (#\t (write-char #\Tab o)) (#\n (write-char #\Newline o))
                       (#\v (write-char (code-char 11) o)) (#\f (write-char (code-char 12) o))
                       (#\r (write-char #\Return o)) (#\" (write-char #\" o)) (#\' (write-char #\' o))
                       (#\\ (write-char #\\ o))
                       (#\x (let ((v 0) (k 0))
                              (loop while (and (< i n) (< k 2) (digit-char-p (char z i) 16))
                                    do (setf v (+ (* 16 v) (digit-char-p (char z i) 16))) (incf i) (incf k))
                              (write-char (code-char v) o)))
                       (t (if (digit-char-p d 8)
                              (let ((v (digit-char-p d 8)) (k 1))
                                (loop while (and (< i n) (< k 3) (digit-char-p (char z i) 8))
                                      do (setf v (+ (* 8 v) (digit-char-p (char z i) 8))) (incf i) (incf k))
                                (write-char (code-char v) o))
                              (progn (write-char #\\ o) (write-char d o))))))
                   (progn (write-char c o) (incf i)))))
    (get-output-stream-string o)))

(defun split-dot-args (line)
  (let ((args '()) (h 1) (n (length line)))
    (loop
      (loop while (and (< h n) (member (char line h) '(#\Space #\Tab #\Newline #\Return))) do (incf h))
      (when (>= h n) (return))
      (let ((c (char line h)))
        (if (member c '(#\' #\"))
            (let ((start (incf h)))
              (loop while (and (< h n) (char/= (char line h) c))
                    do (when (and (char= (char line h) #\\) (char= c #\") (< (1+ h) n)) (incf h))
                       (incf h))
              (let ((a (subseq line start (min h n))))
                (push (if (char= c #\") (resolve-backslashes a) a) args))
              (when (< h n) (incf h)))
            (let ((start h))
              (loop while (and (< h n) (not (member (char line h) '(#\Space #\Tab #\Newline #\Return)))) do (incf h))
              (push (resolve-backslashes (subseq line start h)) args)))))
    (nreverse args)))

(defun boolean-value (z)
  (cond ((and (plusp (length z)) (every #'digit-char-p z)) (/= 0 (parse-integer z)))
        ((or (string-equal z "on") (string-equal z "yes")) t)
        ((or (string-equal z "off") (string-equal z "no")) nil)
        (t (err "ERROR: Not a boolean value: \"~a\". Assuming \"no\".~%" z) nil)))

(defun cmd-match (arg name &optional (min 1))
  "cli_strncmp(azArg[0], NAME, n)==0 with n>=MIN: ARG abbreviates NAME."
  (and (>= (length arg) min) (<= (length arg) (length name)) (string= arg name :end2 (length arg))))

(defun option-match (z name)
  (let ((z (string-left-trim "-" z))) (string= z name)))

(defparameter *mode-names*
  '((:line . "line") (:column . "column") (:list . "list") (:html . "html") (:insert . "insert")
    (:quote . "quote") (:tcl . "tcl") (:csv . "csv") (:explain . "explain") (:ascii . "ascii")
    (:pretty . "prettyprint") (:semi . "semi") (:eqp . "eqp") (:json . "json") (:markdown . "markdown")
    (:table . "table") (:box . "box") (:count . "count") (:off . "off")))

(defun mode-name (m) (cdr (assoc m *mode-names*)))

(defun columnar-mode-p (m) (member m '(:column :markdown :table :box)))

(defparameter *help*
  '(".backup ?DB? FILE        Backup DB (default \"main\") to FILE"
    ".bail on|off             Stop after hitting an error.  Default OFF"
    ".cd DIRECTORY            Change the working directory to DIRECTORY"
    ".changes on|off          Show number of rows changed by SQL"
    ".databases               List names and files of attached databases"
    ".dump ?OBJECTS?          Render database content as SQL"
    "   Options:"
    "     --data-only            Output only INSERT statements"
    "     --newlines             Allow unescaped newline characters in output"
    "     --nosys                Omit system tables (ex: \"sqlite_stat1\")"
    "     --preserve-rowids      Include ROWID values in the output"
    "   OBJECTS is a LIKE pattern for tables, indexes, triggers or views to dump"
    "   Additional LIKE patterns can be given in subsequent arguments"
    ".echo on|off             Turn command echo on or off"
    ".eqp on|off              Enable or disable automatic EXPLAIN QUERY PLAN"
    ".exit ?CODE?             Exit this program with return-code CODE"
    ".fullschema ?--indent?   Show schema and the content of sqlite_stat tables"
    ".headers on|off          Turn display of headers on or off"
    ".help ?-all? ?PATTERN?   Show help text for PATTERN"
    ".import FILE TABLE       Import data from FILE into TABLE"
    "   Options:"
    "     --ascii               Use \\037 and \\036 as column and row separators"
    "     --csv                 Use , and \\n as column and row separators"
    "     --skip N              Skip the first N rows of input"
    "     --schema S            Target table to be S.TABLE"
    "     -v                    \"Verbose\" - increase auxiliary output"
    "   Notes:"
    "     *  If TABLE does not exist, it is created.  The first row of input"
    "        determines the column names."
    "     *  If neither --csv or --ascii are used, the input mode is derived"
    "        from the \".mode\" output mode"
    "     *  If FILE begins with \"|\" then it is a command that generates the"
    "        input text."
    ".indexes ?TABLE?         Show names of indexes"
    "                           If TABLE is specified, only show indexes for"
    "                           tables matching TABLE using the LIKE operator."
    ".mode MODE ?OPTIONS?     Set output mode"
    "   MODE is one of:"
    "     ascii       Columns/rows delimited by 0x1F and 0x1E"
    "     box         Tables using unicode box-drawing characters"
    "     csv         Comma-separated values"
    "     column      Output in columns.  (See .width)"
    "     html        HTML <table> code"
    "     insert      SQL insert statements for TABLE"
    "     json        Results in a JSON array"
    "     line        One value per line"
    "     list        Values delimited by \"|\""
    "     markdown    Markdown table format"
    "     qbox        Shorthand for \"box --wrap 60 --quote\""
    "     quote       Escape answers as for SQL"
    "     table       ASCII-art table"
    "     tabs        Tab-separated values"
    "     tcl         TCL list elements"
    "   OPTIONS: (for columnar modes or insert mode):"
    "     --wrap N       Wrap output lines to no longer than N characters"
    "     --wordwrap B   Wrap or not at word boundaries per B (on/off)"
    "     --ww           Shorthand for \"--wordwrap 1\""
    "     --quote        Quote output text as SQL literals"
    "     --noquote      Do not quote output text"
    "     TABLE          The name of SQL table used for \"insert\" mode"
    ".nullvalue STRING        Use STRING in place of NULL values"
    ".once ?FILE?             Output for the next SQL command only to FILE"
    "     If FILE begins with '|' then open as a pipe"
    ".open ?OPTIONS? ?FILE?   Close existing database and reopen FILE"
    "     Options:"
    "        --new           Initialize FILE to an empty database"
    "        --readonly      Open FILE readonly"
    ".output ?FILE?           Send output to FILE or stdout if FILE is omitted"
    "   If FILE begins with '|' then open it as a pipe."
    ".parameter CMD ...       Manage SQL parameter bindings"
    "   clear                   Erase all bindings"
    "   init                    Initialize the TEMP table that holds bindings"
    "   list                    List the current parameter bindings"
    "   set PARAMETER VALUE     Given SQL parameter PARAMETER a value of VALUE"
    "                           PARAMETER should start with one of: $ : @ ?"
    "   unset PARAMETER         Remove PARAMETER from the binding table"
    ".print STRING...         Print literal STRING"
    ".prompt MAIN CONTINUE    Replace the standard prompts"
    ".quit                    Exit this program"
    ".read FILE               Read input from FILE or command output"
    "    If FILE begins with \"|\", it is a command that generates the input."
    ".save FILE               Write database to FILE (an alias for .backup ...)"
    ".schema ?PATTERN?        Show the CREATE statements matching PATTERN"
    "   Options:"
    "      --indent             Try to pretty-print the schema"
    "      --nosys              Omit objects whose names start with \"sqlite_\""
    ".separator COL ?ROW?     Change the column and row separators"
    ".shell CMD ARGS...       Run CMD ARGS... in a system shell"
    ".show                    Show the current values for various settings"
    ".system CMD ARGS...      Run CMD ARGS... in a system shell"
    ".tables ?TABLE?          List names of tables matching LIKE pattern TABLE"
    ".timeout MS              Try opening locked tables for MS milliseconds"
    ".timer on|off            Turn SQL timer on or off"
    ".width NUM1 NUM2 ...     Set minimum column widths for columnar output"
    "     Negative values right-justify"))

(defun show-help (sh pattern)
  "showHelp: the one-line summaries, or every line of the commands matching PATTERN."
  (cond ((or (null pattern) (string= pattern "-a") (string= pattern "-all") (string= pattern "--all"))
         (dolist (l *help*)
           (when (or pattern (char= (char l 0) #\.)) (out sh l) (out sh (string #\Newline)))))
        (t (let ((n 0) (in nil))
             (dolist (l *help*)
               (if (char= (char l 0) #\.)
                   (setf in (starts-with-p l (concatenate 'string "." pattern)))
                   nil)
               (when in (incf n) (out sh l) (out sh (string #\Newline))))
             (when (zerop n)
               (out sh (format nil "Nothing matches '~a'~%" pattern)))))))

(defun query-texts (sh sql &rest params)
  (apply #'sqlp:query (open-db sh) sql params))

(defun dot-tables (sh args indexes)
  (let* ((dbs (query-texts sh "PRAGMA database_list"))
         (parts (loop for (nil name) in dbs
                      collect (format nil "~a~a.sqlite_schema ~a"
                                      (if (string-equal name "main") "SELECT name FROM "
                                          (format nil "SELECT '~a'||'.'||name FROM " (sqlite-pure::substitute-string "'" "''" name)))
                                      (format nil "\"~a\"" name)
                                      (if indexes
                                          " WHERE type='index'   AND tbl_name LIKE ?1"
                                          " WHERE type IN ('table','view')   AND name NOT LIKE 'sqlite_%'   AND name LIKE ?1"))))
         (rows (mapcar #'first (query-texts sh (format nil "~{~a~^ UNION ALL ~} ORDER BY 1" parts)
                                            (if (second args) (second args) "%")))))
    (when rows
      (let* ((maxlen (reduce #'max rows :key #'length))
             (ncol (max 1 (floor 80 (+ maxlen 2))))
             (nrow (ceiling (length rows) ncol)))
        (dotimes (i nrow)
          (loop for j from i below (length rows) by nrow
                do (out sh (format nil "~a~va" (if (< j nrow) "" "  ") maxlen (nth j rows))))
          (out sh (string #\Newline)))))))

(defun print-schema-line (sh z tail)
  "printSchemaLine."
  (when z
    (when (and (char= (char tail 0) #\;) (or (search "/*" z) (search "--" z)))
      (dolist (term (list "" "*/" (string #\Newline)))
        (let ((new (concatenate 'string z term ";")))
          (when (sql-complete-p new)
            (setf z (subseq new 0 (1- (length new))))
            (return)))))
    (if (and (starts-with-p z "CREATE TABLE ") (> (length z) 13) (member (char z 13) '(#\' #\")))
        (out sh (format nil "CREATE TABLE IF NOT EXISTS ~a~a" (subseq z 13) tail))
        (out sh (format nil "~a~a" z tail)))))

(defun pretty-schema (sh z)
  "MODE_Pretty."
  (when (or (string-prefix-ci-p "CREATE VIEW" z) (string-prefix-ci-p "CREATE TRIG" z))
    (out sh (format nil "~a;~%" z))
    (return-from pretty-schema))
  (let* ((spacep (lambda (c) (member c '(#\Space #\Tab #\Newline #\Return #\Page (code-char 11)))))
         (buf (make-array (length z) :element-type 'character :fill-pointer 0)))
    (let ((i (or (position-if-not spacep z) (length z))))
      (loop for k from i below (length z)
            for c = (char z k)
            do (cond ((funcall spacep c)
                      (when (and (plusp (fill-pointer buf)) (char= (aref buf (1- (fill-pointer buf))) #\Return))
                        (setf (aref buf (1- (fill-pointer buf))) #\Newline))
                      (unless (or (zerop (fill-pointer buf))
                                  (funcall spacep (aref buf (1- (fill-pointer buf))))
                                  (char= (aref buf (1- (fill-pointer buf))) #\())
                        (vector-push c buf)))
                     (t (when (and (member c '(#\( #\))) (plusp (fill-pointer buf))
                                   (funcall spacep (aref buf (1- (fill-pointer buf)))))
                          (decf (fill-pointer buf)))
                        (vector-push c buf)))))
    (loop while (and (plusp (fill-pointer buf)) (funcall spacep (aref buf (1- (fill-pointer buf)))))
          do (decf (fill-pointer buf)))
    (let ((z (coerce buf 'string)))
      (if (>= (length z) 79)
          (let ((line (make-string-output-stream)) (nparen 0) (cend nil) (nline 0) (i 0) (n (length z)))
            (flet ((emit (tail) (print-schema-line sh (get-output-stream-string line) tail)))
              (loop while (< i n)
                    do (let ((c (char z i)))
                         (cond ((and cend (char= c cend)) (setf cend nil))
                               (cend)
                               ((member c '(#\" #\' #\`)) (setf cend c))
                               ((char= c #\[) (setf cend #\]))
                               ((and (char= c #\-) (< (1+ i) n) (char= (char z (1+ i)) #\-)) (setf cend #\Newline))
                               ((char= c #\() (incf nparen))
                               ((char= c #\))
                                (decf nparen)
                                (when (and (plusp nline) (zerop nparen))
                                  (let ((pending (get-output-stream-string line)))
                                    (when (plusp (length pending))
                                      (print-schema-line sh pending (string #\Newline)))))))
                         (write-char c line)
                         (when (and (= nparen 1) (null cend)
                                    (or (char= c #\() (char= c #\Newline)
                                        (and (char= c #\,) (not (ws-to-eol z (1+ i))))))
                           (let ((txt (get-output-stream-string line)))
                             (when (char= c #\Newline) (setf txt (subseq txt 0 (1- (length txt)))))
                             (print-schema-line sh txt (format nil "~%  ")))
                           (incf nline)
                           (loop while (and (< (1+ i) n) (funcall spacep (char z (1+ i)))) do (incf i)))
                         (incf i)))
              (emit (format nil ";~%"))))
          (print-schema-line sh z (format nil ";~%"))))))

(defun ws-to-eol (z i)
  (loop for k from i below (length z)
        for c = (char z k)
        do (cond ((char= c #\Newline) (return t))
                 ((member c '(#\Space #\Tab #\Return)) nil)
                 ((and (char= c #\-) (< (1+ k) (length z)) (char= (char z (1+ k)) #\-)) (return t))
                 (t (return nil)))
        finally (return t)))

(defun dot-schema (sh args)
  (let ((pretty nil) (nosys nil) (name nil))
    (dolist (a (rest args))
      (cond ((option-match a "indent") (setf pretty t))
            ((option-match a "nosys") (setf nosys t))
            ((char= (char a 0) #\-) (err "Unknown option: \"~a\"~%" a) (return-from dot-schema 1))
            ((null name) (setf name a))
            (t (err "Usage: .schema ?--indent? ?--nosys? ?LIKE-PATTERN?~%") (return-from dot-schema 1))))
    (flet ((emit (sql) (if pretty (pretty-schema sh sql) (print-schema-line sh sql (format nil ";~%")))))
      (when (and name (member name '("sqlite_master" "sqlite_schema" "sqlite_temp_master" "sqlite_temp_schema")
                              :test #'string-equal))
        (emit (format nil "CREATE TABLE ~a (~%  type text,~%  name text,~%  tbl_name text,~%  rootpage integer,~%  sql text~%)" name)))
      (let* ((dbs (query-texts sh "SELECT name FROM pragma_database_list"))
             (parts (loop for (db) in dbs for k from 1
                          collect (format nil "SELECT shell_add_schema(sql,~a,name) AS sql, type, tbl_name, name, rowid,~d AS snum, '~a' AS sname FROM ~a.sqlite_schema"
                                          (if (string-equal db "main") "NULL" (format nil "'~a'" db))
                                          k db (ident db))))
             (where (with-output-to-string (o)
                      (when name
                        (let ((glob (find-if (lambda (c) (member c '(#\* #\? #\[))) name)))
                          (format o "~a ~a ~a~a AND "
                                  (if (find #\. name) "lower(printf('%s.%s',sname,tbl_name))" "lower(tbl_name)")
                                  (if glob "GLOB" "LIKE")
                                  (printf "%Q" name)
                                  (if glob "" " ESCAPE '\\' "))))
                      (when nosys (write-string "name NOT LIKE 'sqlite_%' AND " o))))
             (rows (handler-case
                       (query-texts sh (format nil "SELECT sql FROM(~{~a~^ UNION ALL ~}) WHERE ~asql IS NOT NULL ORDER BY snum, rowid"
                                               parts where))
                     (sqlp:sqlite-error (c) (err "Error: ~a~%" (sqlp:sqlite-error-message c)) (return-from dot-schema 1)))))
        (dolist (r rows) (emit (first r)))
        0))))

(defun table-columns-for-dump (sh table preserve-rowid)
  "tableColumnList: (rowid-name-or-nil . column names)."
  (let* ((info (query-texts sh (format nil "PRAGMA table_info=~a" (printf "%Q" table))))
         (cols (mapcar #'second info))
         (npk (count-if (lambda (r) (/= 0 (sixth r))) info))
         (ipk (and (= npk 1) (let ((r (find-if (lambda (r) (/= 0 (sixth r))) info)))
                               (string-equal (third r) "INTEGER"))))
         (rowid nil))
    (when (and preserve-rowid ipk)
      (setf preserve-rowid (query-texts sh (format nil "SELECT 1 FROM pragma_index_list(~a) WHERE origin='pk'" (printf "%Q" table)))))
    (when preserve-rowid
      (dolist (r '("rowid" "_rowid_" "oid"))
        (unless (member r cols :test #'string-equal)
          (when (ignore-errors (query-texts sh (format nil "SELECT ~a FROM ~a LIMIT 0" r (ident table))) t)
            (setf rowid r))
          (return))))
    (cons rowid cols)))

(defun dot-dump (sh args)
  (let ((like nil) (preserve nil) (newlines nil) (data-only nil) (nosys nil)
        (saved-header (sh-show-header sh)))
    (dolist (a (rest args))
      (if (char= (char a 0) #\-)
          (let ((z (string-left-trim "-" a)))
            (cond ((string= z "preserve-rowids") (setf preserve t))
                  ((string= z "newlines") (setf newlines t))
                  ((string= z "data-only") (setf data-only t))
                  ((string= z "nosys") (setf nosys t))
                  (t (err "Unknown option \"~a\" on \".dump\"~%" a) (return-from dot-dump 1))))
          (let ((e (format nil "name LIKE ~a ESCAPE '\\' OR EXISTS (  SELECT 1 FROM sqlite_schema WHERE     name LIKE ~a ESCAPE '\\' AND    sql LIKE 'CREATE VIRTUAL TABLE%' AND    substr(o.name, 1, length(name)+1) == (name||'_'))"
                           (printf "%Q" a) (printf "%Q" a))))
            (setf like (if like (format nil "~a OR ~a" like e) e)))))
    (open-db sh)
    (unless data-only
      (out sh (format nil "PRAGMA foreign_keys=OFF;~%BEGIN TRANSACTION;~%")))
    (setf (sh-writable-schema sh) nil (sh-show-header sh) nil (sh-nerr sh) 0)
    (dolist (r (query-texts sh (format nil "SELECT name, type, sql FROM sqlite_schema AS o WHERE (~a) AND type=='table'  AND sql NOT NULL ORDER BY tbl_name='sqlite_sequence', rowid"
                                       (or like "true"))))
      (destructuring-bind (table type sql) r
        (block one
          (cond ((string= table "sqlite_sequence")
                 (unless nosys (unless data-only (out sh (format nil "DELETE FROM sqlite_sequence;~%")))))
                ((and (starts-with-p table "sqlite_stat") (= (length table) 12))
                 (unless nosys (unless data-only (out sh (format nil "ANALYZE sqlite_schema;~%")))))
                ((starts-with-p table "sqlite_") (return-from one))
                (data-only)
                ((starts-with-p sql "CREATE VIRTUAL TABLE")
                 (unless (sh-writable-schema sh)
                   (out sh (format nil "PRAGMA writable_schema=ON;~%"))
                   (setf (sh-writable-schema sh) t))
                 (out sh (format nil "INSERT INTO sqlite_schema(type,name,tbl_name,rootpage,sql)VALUES('table',~a,~a,0,~a);~%"
                                 (printf "%Q" table) (printf "%Q" table) (printf "%Q" sql)))
                 (return-from one))
                (t (print-schema-line sh sql (format nil ";~%"))))
          (when (string= type "table")
            (let* ((cl (table-columns-for-dump sh table preserve))
                   (rowid (car cl)) (cols (cdr cl))
                   (dest (format nil "~a~@[(~a~{,~a~})~]" (ident table) rowid (and rowid (mapcar #'ident cols))))
                   (select (format nil "SELECT ~@[~a,~]~{~a~^,~} FROM ~a" rowid (mapcar #'ident cols) (ident table)))
                   (saved-dest (sh-dest-table sh)) (saved-mode (sh-mode sh)))
              (setf (sh-dest-table sh) dest (sh-mode sh) :insert)
              (let ((e (let ((*newlines* newlines)) (shell-exec sh select))))
                (when e (incf (sh-nerr sh))))
              (setf (sh-dest-table sh) saved-dest (sh-mode sh) saved-mode))))))
    (unless data-only
      (dolist (r (query-texts sh (format nil "SELECT sql FROM sqlite_schema AS o WHERE (~a) AND sql NOT NULL  AND type IN ('index','trigger','view')"
                                         (or like "true"))))
        (let ((z (first r)))
          (out sh z)
          (out sh (if (search "--" z) (format nil "~%;~%") (format nil ";~%"))))))
    (when (sh-writable-schema sh)
      (out sh (format nil "PRAGMA writable_schema=OFF;~%"))
      (setf (sh-writable-schema sh) nil))
    (unless data-only
      (out sh (if (plusp (sh-nerr sh)) (format nil "ROLLBACK; -- due to errors~%") (format nil "COMMIT;~%"))))
    (setf (sh-show-header sh) saved-header)
    0))


;;; .import

(defstruct (import-ctx (:conc-name ic-)) in file (line 1) col-sep row-sep term (nrow 0) (nerr 0) not-first)

(defun ic-getc (ic) (read-byte (ic-in ic) nil :eof))

(defun csv-read-field (ic)
  "csv_read_one_field: octets, or NIL at end of input."
  (let ((z (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
        (csep (ic-col-sep ic)) (rsep (ic-row-sep ic))
        (c (ic-getc ic)))
    (when (eq c :eof) (setf (ic-term ic) :eof) (return-from csv-read-field nil))
    (if (eql c 34)
        (let ((pc 0) (ppc 0) (start (ic-line ic)))
          (loop
            (setf c (ic-getc ic))
            (when (eql c rsep) (incf (ic-line ic)))
            (cond
              ((and (eql c 34) (eql pc 34)) (setf pc 0))
              ((or (and (eql c csep) (eql pc 34)) (and (eql c rsep) (eql pc 34))
                   (and (eql c rsep) (eql pc 13) (eql ppc 34)) (and (eq c :eof) (eql pc 34)))
               (loop do (decf (fill-pointer z)) until (= (aref z (fill-pointer z)) 34))
               (setf (ic-term ic) c)
               (return))
              (t
               (when (and (eql pc 34) (not (eql c 13)))
                 (err "~a:~d: unescaped \" character~%" (ic-file ic) (ic-line ic)))
               (when (eq c :eof)
                 (err "~a:~d: unterminated \"-quoted field~%" (ic-file ic) start)
                 (setf (ic-term ic) c)
                 (return))
               (vector-push-extend c z)
               (setf ppc pc pc c)))))
        (progn
          (when (and (eql c #xef) (not (ic-not-first ic)))
            (let ((c2 (ic-getc ic)) (c3 nil))
              (if (and (eql c2 #xbb) (eql (setf c3 (ic-getc ic)) #xbf))
                  (progn (setf (ic-not-first ic) t) (return-from csv-read-field (csv-read-field ic)))
                  (progn (vector-push-extend c z) (setf c c2)
                         (when c3 (unless (eq c2 :eof) (vector-push-extend c2 z)) (setf c c3))))))
          (loop while (not (or (eq c :eof) (eql c csep) (eql c rsep)))
                do (vector-push-extend c z) (setf c (ic-getc ic)))
          (when (eql c rsep)
            (incf (ic-line ic))
            (when (and (plusp (fill-pointer z)) (= (aref z (1- (fill-pointer z))) 13))
              (decf (fill-pointer z))))
          (setf (ic-term ic) c)))
    (setf (ic-not-first ic) t)
    (coerce z 'octets)))


(defun ascii-read-field (ic)
  (let ((z (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
        (c (ic-getc ic)))
    (when (eq c :eof) (setf (ic-term ic) :eof) (return-from ascii-read-field nil))
    (loop while (not (or (eq c :eof) (eql c (ic-col-sep ic)) (eql c (ic-row-sep ic))))
          do (vector-push-extend c z) (setf c (ic-getc ic)))
    (when (eql c (ic-row-sep ic)) (incf (ic-line ic)))
    (setf (ic-term ic) c)
    (coerce z 'octets)))

(defun dot-import (sh args)
  (let ((file nil) (table nil) (schema nil) (skip 0) (verbose 0) (use-output t)
        (reader (if (eq (sh-mode sh) :ascii) #'ascii-read-field #'csv-read-field))
        (csep nil) (rsep nil))
    (loop for rest on (rest args)
          do (let ((z (first rest)))
               (when (and (> (length z) 1) (char= (char z 0) #\-) (char= (char z 1) #\-)) (setf z (subseq z 1)))
               (cond ((char/= (char z 0) #\-)
                      (cond ((null file) (setf file z))
                            ((null table) (setf table z))
                            (t (out sh (format nil "ERROR: extra argument: \"~a\".  Usage:~%" z))
                               (show-help sh "import") (return-from dot-import 1))))
                     ((string= z "-v") (incf verbose))
                     ((and (string= z "-schema") (rest rest)) (setf schema (pop (cdr rest))))
                     ((and (string= z "-skip") (rest rest)) (setf skip (parse-integer (pop (cdr rest)) :junk-allowed t)))
                     ((string= z "-ascii") (setf csep 31 rsep 30 reader #'ascii-read-field use-output nil))
                     ((string= z "-csv") (setf csep 44 rsep 10 reader #'csv-read-field use-output nil))
                     (t (out sh (format nil "ERROR: unknown option: \"~a\".  Usage:~%" z))
                        (show-help sh "import") (return-from dot-import 1)))))
    (unless table
      (out sh (format nil "ERROR: missing ~a argument. Usage:~%" (if file "TABLE" "FILE")))
      (show-help sh "import")
      (return-from dot-import 1))
    (open-db sh)
    (when use-output
      (let ((cs (b (sh-col-sep sh))) (rs (b (sh-row-sep sh))))
        (cond ((zerop (length cs)) (err "Error: non-null column separator required for import~%") (return-from dot-import 1))
              ((> (length cs) 1) (err "Error: multi-character column separators not allowed for import~%") (return-from dot-import 1)))
        (when (and (eq (sh-mode sh) :csv) (equalp rs (b (format nil "~c~c" #\Return #\Newline))))
          (setf rs (b (string #\Newline))))
        (cond ((zerop (length rs)) (err "Error: non-null row separator required for import~%") (return-from dot-import 1))
              ((> (length rs) 1) (err "Error: multi-character row separators not allowed for import~%") (return-from dot-import 1)))
        (setf csep (aref cs 0) rsep (aref rs 0))))
    (let ((in (handler-case (if (char= (char file 0) #\|)
                                (sb-ext:process-output (sb-ext:run-program "/bin/sh" (list "-c" (subseq file 1))
                                                                           :output :stream :wait nil))
                                (open file :element-type '(unsigned-byte 8)))
                (error () nil))))
      (unless in (err "Error: cannot open \"~a\"~%" file) (return-from dot-import 1))
      (unwind-protect
           (let* ((ic (make-import-ctx :in in :file (if (char= (char file 0) #\|) "<pipe>" file)
                                       :col-sep csep :row-sep rsep))
                  (full (if schema (format nil "\"~a\".\"~a\"" schema table)
                            (format nil "\"~a\"" (sqlite-pure::substitute-string "\"" "\"\"" table)))))
             (when (or (>= verbose 2) (and (>= verbose 1) use-output))
               (out sh (format nil "Column separator ~a, row separator ~a~%"
                               (c-string (b (vector csep))) (c-string (b (vector rsep))))))
             (loop repeat skip
                   do (loop while (and (funcall reader ic) (eql (ic-term ic) csep))))
             (let ((ncol (handler-case (length (nth-value 1 (sqlp:query (sh-db sh) (format nil "SELECT * FROM ~a LIMIT 0" full))))
                           (sqlp:sqlite-error (c)
                             (unless (starts-with-p (sqlp:sqlite-error-message c) "no such table: ")
                               (err "Error: ~a~%" (sqlp:sqlite-error-message c)) (return-from dot-import 1))
                             nil))))
               (unless ncol
                 ;; the first row names the columns of a new table
                 (let ((names '()))
                   (loop (let ((z (funcall reader ic)))
                           (unless z (return))
                           (push (s z) names)
                           (unless (eql (ic-term ic) csep) (return))))
                   (setf names (nreverse names))
                   (when (null names) (err "~a: empty file~%" (ic-file ic)) (return-from dot-import 1))
                   (let ((create (format nil "CREATE TABLE ~a(~%~{~a~^, ~})~%" full
                                         (mapcar (lambda (n) (format nil "\"~a\" TEXT" (sqlite-pure::substitute-string "\"" "\"\"" n)))
                                                 (dedupe-names names)))))
                     (when (>= verbose 1) (out sh (format nil "~a~%" create)))
                     (handler-case (sqlp:execute (sh-db sh) create)
                       (sqlp:sqlite-error (c)
                         (err "~a failed:~%~a~%" create (sqlp:sqlite-error-message c))
                         (return-from dot-import 1)))
                     (setf ncol (length names)))))
               (let* ((insert (format nil "INSERT INTO ~a VALUES(~{~a~^,~})" full (make-list ncol :initial-element "?")))
                      (need-commit (not (sqlp:in-transaction-p (sh-db sh)))))
                 (when (>= verbose 2) (out sh (format nil "Insert using: ~a~%" insert)))
                 (when need-commit (sqlp:execute (sh-db sh) "BEGIN"))
                 (loop
                   (let ((start (ic-line ic)) (vals '()) (i 0) (stop nil))
                     (loop while (< i ncol)
                           do (let ((z (funcall reader ic)))
                                (when (and (null z) (= i 0)) (setf stop t) (return))
                                (when (and (eq (sh-mode sh) :ascii) (or (null z) (zerop (length z))) (= i 0))
                                  (setf stop t) (return))
                                (push (if z (s z) :null) vals)
                                (when (and (< i (1- ncol)) (not (eql (ic-term ic) csep)))
                                  (err "~a:~d: expected ~d columns but found ~d - filling the rest with NULL~%"
                                       (ic-file ic) start ncol (1+ i))
                                  (loop repeat (- ncol i 1) do (push :null vals))
                                  (setf i (+ i 2)) (return))
                                (incf i)))
                     (when (eql (ic-term ic) csep)
                       (loop do (funcall reader ic) (incf i) while (eql (ic-term ic) csep))
                       (err "~a:~d: expected ~d columns but found ~d - extras ignored~%" (ic-file ic) start ncol i))
                     (when (and (not stop) (>= i ncol))
                       (handler-case (progn (apply #'sqlp:execute (sh-db sh) insert (subseq (nreverse vals) 0 ncol))
                                            (incf (ic-nrow ic)))
                         (sqlp:sqlite-error (c)
                           (err "~a:~d: INSERT failed: ~a~%" (ic-file ic) start (sqlp:sqlite-error-message c))
                           (incf (ic-nerr ic)))))
                     (when (eq (ic-term ic) :eof) (return))))
                 (when need-commit (sqlp:execute (sh-db sh) "COMMIT"))
                 (when (plusp verbose)
                   (out sh (format nil "Added ~d rows with ~d errors using ~d lines of input~%"
                                   (ic-nrow ic) (ic-nerr ic) (1- (ic-line ic)))))
                 0)))
        (close in)))))

(defun dedupe-names (names)
  (let ((seen (make-hash-table :test #'equalp)))
    (loop for n in names
          collect (let ((k (gethash n seen 0)))
                    (setf (gethash n seen) (1+ k))
                    (if (plusp k) (format nil "~a_~d" n k) n)))))

;;; .parameter

(defun bind-table-init (sh)
  "bind_table_init: made with the schema writable, as shell.c does."
  (let* ((db (open-db sh)) (was (sqlp:query-value db "PRAGMA writable_schema")))
    (sqlp:execute db "PRAGMA writable_schema=ON")
    (unwind-protect
         (sqlp:execute db "CREATE TABLE IF NOT EXISTS temp.sqlite_parameters(  key TEXT PRIMARY KEY,  value) WITHOUT ROWID;")
      (sqlp:execute db (format nil "PRAGMA writable_schema=~d" was)))))

(defun dot-parameter (sh args)
  (open-db sh)
  (let ((n (length args)))
    (cond ((and (= n 2) (string= (second args) "clear"))
           (ignore-errors (sqlp:execute (sh-db sh) "DROP TABLE IF EXISTS temp.sqlite_parameters;")))
          ((and (= n 2) (string= (second args) "list"))
           (let ((rows (ignore-errors (query-texts sh "SELECT key, quote(value) FROM temp.sqlite_parameters;"))))
             (when rows
               (let ((len (min 40 (reduce #'max rows :key (lambda (r) (length (first r)))))))
                 (dolist (r rows) (out sh (format nil "~va ~a~%" len (first r) (second r))))))))
          ((and (= n 2) (string= (second args) "init")) (bind-table-init sh))
          ((and (= n 4) (string= (second args) "set"))
           (bind-table-init sh)
           (handler-case
               (sqlp:execute (sh-db sh) (format nil "REPLACE INTO temp.sqlite_parameters(key,value)VALUES(~a,~a);"
                                                (printf "%Q" (third args)) (fourth args)))
             (sqlp:sqlite-error ()
               (handler-case
                   (sqlp:execute (sh-db sh) (format nil "REPLACE INTO temp.sqlite_parameters(key,value)VALUES(~a,~a);"
                                                    (printf "%Q" (third args)) (printf "%Q" (fourth args))))
                 (sqlp:sqlite-error (c) (out sh (format nil "Error: ~a~%" (sqlp:sqlite-error-message c))) (return-from dot-parameter 1))))))
          ((and (= n 3) (string= (second args) "unset"))
           (ignore-errors (sqlp:execute (sh-db sh) (format nil "DELETE FROM temp.sqlite_parameters WHERE key=~a" (printf "%Q" (third args))))))
          (t (show-help sh "parameter")))
    0))

;;; .backup / .save

(defun dot-backup (sh args)
  (let ((dest nil) (dbname nil))
    (dolist (a (rest args))
      (cond ((char= (char a 0) #\-) (err "unknown option: ~a~%" a) (return-from dot-backup 1))
            ((null dest) (setf dest a))
            ((null dbname) (setf dbname dest dest a))
            (t (err "Usage: .backup ?DB? ?OPTIONS? FILENAME~%") (return-from dot-backup 1))))
    (unless dest (err "missing FILENAME argument on .backup~%") (return-from dot-backup 1))
    (let* ((main (open-db sh))
           (db (if dbname (sqlite-pure::schema-db main dbname) main)))
      (handler-case
          (progn
            (when (probe-file dest) (delete-file dest))
            (with-open-file (o dest :direction :output :element-type '(unsigned-byte 8) :if-exists :supersede)
              (loop for pg from 1 to (sqlite-pure::db-page-count db)
                    do (write-sequence (sqlite-pure::read-page db pg) o)))
            0)
        (error (e) (err "Error: ~a~%" (if (typep e 'sqlp:sqlite-error) (sqlp:sqlite-error-message e) e)) 1)))))

;;; .output / .once

(defun set-output (sh target once)
  (close-output sh)
  (cond ((null target) (setf (sh-out sh) *stdout* (sh-out-name sh) nil))
        ((char= (char target 0) #\|)
         (let ((p (sb-ext:run-program "/bin/sh" (list "-c" (subseq target 1)) :input :stream :output t :error t :wait nil)))
           (setf (sh-out sh) (sb-ext:process-input p) (sh-out-name sh) target)))
        ((member target '("stdout" "-") :test #'string=) (setf (sh-out sh) *stdout* (sh-out-name sh) nil))
        (t (handler-case
               (setf (sh-out sh) (open target :direction :output :element-type '(unsigned-byte 8)
                                              :if-exists :supersede :if-does-not-exist :create)
                     (sh-out-name sh) target)
             (error () (err "Error: cannot write to \"~a\"~%" target) (setf (sh-out sh) *stdout*)
               (return-from set-output 1)))))
  (setf (sh-once sh) once)
  0)

(defun close-output (sh)
  (unless (eq (sh-out sh) *stdout*)
    (ignore-errors (close (sh-out sh))))
  (setf (sh-out sh) *stdout* (sh-out-name sh) nil (sh-once sh) nil))

;;; the dispatcher

(defun do-meta-command (sh line)
  "Returns 0, 1 (error) or 2 (quit)."
  (let* ((args (split-dot-args line)))
    (when (null args) (return-from do-meta-command 0))
    (let* ((cmd (first args)) (n (length args)) (c (char cmd 0)))
      (declare (ignorable c))
      (macrolet ((usage (text) `(progn (err "~a~%" ,text) 1)))
        (cond
          ((or (cmd-match cmd "backup" 3) (cmd-match cmd "save" 3)) (dot-backup sh args))
          ((cmd-match cmd "bail" 3)
           (if (= n 2) (progn (setf (sh-bail sh) (boolean-value (second args))) 0) (usage "Usage: .bail on|off")))
          ((cmd-match cmd "binary" 3) 0)
          ((string= cmd "cd")
           (if (= n 2)
               (handler-case (progn (setf *default-pathname-defaults* (truename (concatenate 'string (string-right-trim "/" (second args)) "/")))
                                    (sb-posix:chdir (second args)) 0)
                 (error () (err "Cannot change to directory \"~a\"~%" (second args)) 1))
               (usage "Usage: .cd DIRECTORY")))
          ((cmd-match cmd "changes" 3)
           (if (= n 2) (progn (setf (sh-count-changes sh) (boolean-value (second args))) 0) (usage "Usage: .changes on|off")))
          ((and (> (length cmd) 1) (cmd-match cmd "databases"))
           (dolist (r (query-texts sh "PRAGMA database_list"))
             (let ((d (sqlite-pure::schema-db (sh-db sh) (second r) nil)))
               (out sh (format nil "~a: ~a ~a~a~%" (second r)
                               (if (plusp (length (third r))) (absolute-path (third r)) "\"\"")
                               (if (and d (sqlite-pure::db-readonly d)) "r/o" "r/w")
                               (cond ((null d) "") ((sqlite-pure::db-txn d) " write-txn") (t ""))))))
           0)
          ((cmd-match cmd "dump") (dot-dump sh args))
          ((cmd-match cmd "echo")
           (if (= n 2) (progn (setf (sh-echo sh) (boolean-value (second args))) 0) (usage "Usage: .echo on|off")))
          ((cmd-match cmd "eqp")
           (if (= n 2) (progn (setf (sh-auto-eqp sh) (and (not (string-equal (second args) "off")) (boolean-or-full (second args)))) 0)
               (usage "Usage: .eqp off|on|trace|trigger|full")))
          ((cmd-match cmd "exit")
           (when (and (> n 1) (/= 0 (or (parse-integer (second args) :junk-allowed t) 0)))
             (finish sh) (sb-ext:exit :code (parse-integer (second args) :junk-allowed t) :abort t))
           2)
          ((cmd-match cmd "explain") 0)
          ((cmd-match cmd "fullschema")
           (let ((pretty (and (= n 2) (option-match (second args) "indent"))))
             (if (> n (if pretty 2 1))
                 (usage "Usage: .fullschema ?--indent?")
                 (progn
                   (dolist (r (query-texts sh "SELECT sql FROM  (SELECT sql sql, type type, tbl_name tbl_name, name name, rowid x     FROM sqlite_schema UNION ALL   SELECT sql, type, tbl_name, name, rowid FROM sqlite_temp_schema) WHERE type!='meta' AND sql NOTNULL AND name NOT LIKE 'sqlite_%' ORDER BY x"))
                     (if pretty (pretty-schema sh (first r)) (print-schema-line sh (first r) (format nil ";~%"))))
                   (if (query-texts sh "SELECT rowid FROM sqlite_schema WHERE name GLOB 'sqlite_stat[134]'")
                       (let ((saved-mode (sh-mode sh)) (saved-dest (sh-dest-table sh)) (saved-hdr (sh-show-header sh)))
                         (out sh (format nil "ANALYZE sqlite_schema;~%"))
                         (setf (sh-mode sh) :insert (sh-show-header sh) nil (sh-dest-table sh) "sqlite_stat1")
                         (shell-exec sh "SELECT * FROM sqlite_stat1")
                         (setf (sh-mode sh) saved-mode (sh-dest-table sh) saved-dest (sh-show-header sh) saved-hdr)
                         (out sh (format nil "ANALYZE sqlite_schema;~%")))
                       (out sh (format nil "/* No STAT tables available */~%")))
                   0))))
          ((cmd-match cmd "headers")
           (if (= n 2) (progn (setf (sh-show-header sh) (boolean-value (second args)) (sh-header-set sh) t) 0)
               (usage "Usage: .headers on|off")))
          ((cmd-match cmd "help")
           (show-help sh (second args)) 0)
          ((cmd-match cmd "import") (dot-import sh args))
          ((or (cmd-match cmd "indexes") (cmd-match cmd "indices"))
           (if (> n 2) (usage "Usage: .indexes ?LIKE-PATTERN?") (progn (dot-tables sh args t) 0)))
          ((cmd-match cmd "load") (err "Error: extension loading is not supported~%") 1)
          ((cmd-match cmd "mode") (dot-mode sh args))
          ((cmd-match cmd "nullvalue")
           (if (= n 2) (progn (setf (sh-null-value sh) (second args)) 0) (usage "Usage: .nullvalue STRING")))
          ((and (>= (length cmd) 2) (cmd-match cmd "once"))
           (set-output sh (loop for a in (rest args) unless (char= (char a 0) #\-) return a) t))
          ((and (>= (length cmd) 2) (cmd-match cmd "open")) (dot-open sh args))
          ((and (>= (length cmd) 2) (cmd-match cmd "output"))
           (set-output sh (loop for a in (rest args) unless (char= (char a 0) #\-) return a) nil))
          ((and (>= (length cmd) 3) (cmd-match cmd "parameter")) (dot-parameter sh args))
          ((and (>= (length cmd) 3) (cmd-match cmd "print"))
           (out sh (format nil "~{~a~^ ~}~%" (rest args))) 0)
          ((cmd-match cmd "prompt")
           (when (>= n 2) (setf (sh-main-prompt sh) (second args)))
           (when (>= n 3) (setf (sh-cont-prompt sh) (third args)))
           0)
          ((cmd-match cmd "quit") 2)
          ((and (>= (length cmd) 3) (cmd-match cmd "read"))
           (if (/= n 2)
               (usage "Usage: .read FILE")
               (let ((f (second args)))
                 (handler-case
                     (let ((stream (if (char= (char f 0) #\|)
                                       (sb-ext:process-output (sb-ext:run-program "/bin/sh" (list "-c" (subseq f 1)) :output :stream :wait nil))
                                       (open f :external-format '(:utf-8 :replacement #\?)))))
                       (let ((saved-in (sh-in sh)) (saved-line (sh-lineno sh)))
                         (setf (sh-in sh) stream)
                         (prog1 (process-input sh)
                           (close stream)
                           (setf (sh-in sh) saved-in (sh-lineno sh) saved-line))))
                   (file-error () (err "Error: cannot open \"~a\"~%" f) 1)))))
          ((cmd-match cmd "schema") (dot-schema sh args))
          ((cmd-match cmd "separator")
           (if (or (< n 2) (> n 3))
               (usage "Usage: .separator COL ?ROW?")
               (progn (setf (sh-col-sep sh) (second args))
                      (when (= n 3) (setf (sh-row-sep sh) (third args)))
                      0)))
          ((or (and (>= (length cmd) 2) (cmd-match cmd "shell")) (cmd-match cmd "system"))
           (if (< n 2)
               (usage (format nil "Usage: .~a COMMAND" cmd))
               (progn (flush sh)
                      (sb-ext:run-program "/bin/sh" (list "-c" (format nil "~{~a~^ ~}" (rest args)))
                                          :input t :output t :error t)
                      0)))
          ((and (>= (length cmd) 2) (cmd-match cmd "show"))
           (if (/= n 1) (usage "Usage: .show") (progn (dot-show sh) 0)))
          ((and (> (length cmd) 1) (cmd-match cmd "tables")) (dot-tables sh args nil) 0)
          ((and (> (length cmd) 4) (cmd-match cmd "timeout"))
           (setf sqlite-pure::*busy-timeout* (/ (if (>= n 2) (or (parse-integer (second args) :junk-allowed t) 0) 0) 1000))
           0)
          ((and (>= (length cmd) 5) (cmd-match cmd "timer"))
           (if (= n 2) (progn (setf (sh-timer sh) (boolean-value (second args))) 0) (usage "Usage: .timer on|off")))
          ((cmd-match cmd "width")
           (setf (sh-widths sh) (loop for a in (rest args) collect (or (parse-integer a :junk-allowed t) 0)))
           0)
          (t (err "Error: unknown command or invalid arguments:  \"~a\". Enter \".help\" for help~%" cmd) 1))))))

(defun absolute-path (file)
  "sqlite3_db_filename: the full path name."
  (let ((p (probe-file file)))
    (if p (namestring p) (namestring (merge-pathnames file)))))

(defun boolean-or-full (z) (declare (ignore z)) t)

(defun dot-mode (sh args)
  (let ((mode nil) (tab nil) (wrap 60) (ww nil) (quote nil))
    (loop for rest on (rest args)
          do (let ((z (first rest)))
               (cond ((and (option-match z "wrap") (char= (char z 0) #\-) (rest rest))
                      (setf wrap (or (parse-integer (pop (cdr rest)) :junk-allowed t) 0)))
                     ((and (char= (char z 0) #\-) (option-match z "ww")) (setf ww t))
                     ((and (char= (char z 0) #\-) (option-match z "wordwrap") (rest rest))
                      (setf ww (boolean-value (pop (cdr rest)))))
                     ((and (char= (char z 0) #\-) (option-match z "quote")) (setf quote t))
                     ((and (char= (char z 0) #\-) (option-match z "noquote")) (setf quote nil))
                     ((null mode) (setf mode z)
                      (when (string= z "qbox") (setf mode "box" wrap 60 ww nil quote t)))
                     ((null tab) (setf tab z))
                     ((char= (char z 0) #\-)
                      (err "unknown option: ~a~%options:~%  --noquote~%  --quote~%  --wordwrap on/off~%  --wrap N~%  --ww~%" z)
                      (return-from dot-mode 1))
                     (t (err "extra argument: \"~a\"~%" z) (return-from dot-mode 1)))))
    (unless mode
      (if (columnar-mode-p (sh-mode sh))
          (out sh (format nil "current output mode: ~a --wrap ~d --wordwrap ~a --~aquote~%"
                          (mode-name (sh-mode sh)) (sh-wrap sh) (if (sh-wordwrap sh) "on" "off") (if (sh-quote sh) "" "no")))
          (out sh (format nil "current output mode: ~a~%" (mode-name (sh-mode sh)))))
      (setf mode (mode-name (sh-mode sh))))
    (flet ((is (name) (and (plusp (length mode)) (<= (length mode) (length name)) (string= mode name :end2 (length mode))))
           (cm () (setf (sh-wrap sh) wrap (sh-wordwrap sh) ww (sh-quote sh) quote)))
      (cond ((is "lines") (setf (sh-mode sh) :line (sh-row-sep sh) (string #\Newline)))
            ((is "columns") (setf (sh-mode sh) :column (sh-row-sep sh) (string #\Newline))
             (unless (sh-header-set sh) (setf (sh-show-header sh) t))
             (cm))
            ((is "list") (setf (sh-mode sh) :list (sh-col-sep sh) "|" (sh-row-sep sh) (string #\Newline)))
            ((is "html") (setf (sh-mode sh) :html))
            ((is "tcl") (setf (sh-mode sh) :tcl (sh-col-sep sh) " " (sh-row-sep sh) (string #\Newline)))
            ((is "csv") (setf (sh-mode sh) :csv (sh-col-sep sh) "," (sh-row-sep sh) (format nil "~c~c" #\Return #\Newline)))
            ((is "tabs") (setf (sh-mode sh) :list (sh-col-sep sh) (string #\Tab)))
            ((is "insert") (setf (sh-mode sh) :insert (sh-dest-table sh) (ident (or tab "table"))))
            ((is "quote") (setf (sh-mode sh) :quote (sh-col-sep sh) "," (sh-row-sep sh) (string #\Newline)))
            ((is "ascii") (setf (sh-mode sh) :ascii (sh-col-sep sh) (string (code-char 31)) (sh-row-sep sh) (string (code-char 30))))
            ((is "markdown") (setf (sh-mode sh) :markdown) (cm))
            ((is "table") (setf (sh-mode sh) :table) (cm))
            ((is "box") (setf (sh-mode sh) :box) (cm))
            ((is "count") (setf (sh-mode sh) :count))
            ((is "off") (setf (sh-mode sh) :off))
            ((is "json") (setf (sh-mode sh) :json))
            (t (err "Error: mode should be one of: ascii box column csv html insert json line list markdown qbox quote table tabs tcl~%")
               (return-from dot-mode 1))))
    (setf (sh-c-mode sh) (sh-mode sh))
    0))

(defun dot-show (sh)
  (flet ((line (name value) (out sh (format nil "~12@a: ~a~%" name value))))
    (line "echo" (if (sh-echo sh) "on" "off"))
    (line "eqp" (if (sh-auto-eqp sh) "on" "off"))
    (line "explain" "auto")
    (line "headers" (if (sh-show-header sh) "on" "off"))
    (if (columnar-mode-p (sh-mode sh))
        (line "mode" (format nil "~a --wrap ~d --wordwrap ~a --~aquote" (mode-name (sh-mode sh)) (sh-wrap sh)
                             (if (sh-wordwrap sh) "on" "off") (if (sh-quote sh) "" "no")))
        (line "mode" (mode-name (sh-mode sh))))
    (line "nullvalue" (c-string (sh-null-value sh)))
    (line "output" (or (sh-out-name sh) "stdout"))
    (line "colseparator" (c-string (sh-col-sep sh)))
    (line "rowseparator" (c-string (sh-row-sep sh)))
    (line "stats" "off")
    (out sh (format nil "~12@a: ~{~d ~}~%" "width" (sh-widths sh)))
    (line "filename" (or (sh-filename sh) ""))))

(defun dot-open (sh args)
  (let ((file nil) (new nil) (readonly nil))
    (dolist (a (rest args))
      (cond ((option-match a "new") (setf new t))
            ((option-match a "readonly") (setf readonly t))
            ((option-match a "nofollow"))
            ((char= (char a 0) #\-) (err "unknown option: ~a~%" a) (return-from dot-open 1))
            (file (err "extra argument: \"~a\"~%" a) (return-from dot-open 1))
            (t (setf file a))))
    (when (sh-db sh) (ignore-errors (sqlp:close-database (sh-db sh))))
    (setf (sh-db sh) nil (sh-filename sh) file (sh-readonly sh) readonly)
    (when (and new file (probe-file file)) (delete-file file))
    (open-db sh)
    0))

;;; ------------------------------------------------------------------
;;; Input

(defun read-input-line (sh continuation)
  (let ((in (or (sh-in sh) *stdin*)))
    (when (and (null (sh-in sh)) (sh-interactive sh))
      (out sh (if continuation (sh-cont-prompt sh) (sh-main-prompt sh))))
    (flush sh)
    (let ((line (read-line in nil nil)))
      (when (and line (plusp (length line)) (char= (char line (1- (length line))) #\Return))
        (setf line (subseq line 0 (1- (length line)))))
      line)))

(defun whitespace-or-comment-p (sql)
  (every (lambda (c) (member c '(#\Space #\Tab #\Newline #\Return #\Page))) (strip-comments sql)))

(defun command-terminator-p (line)
  (let ((z (string-trim '(#\Space #\Tab) line)))
    (or (string= z "/") (string-equal z "go"))))

(defun process-input (sh)
  "process_input: returns 1 if any error, else 0 (2 propagates quit)."
  (when (>= (sh-nesting sh) 25)
    (err "Input nesting limit (25) reached at line ~d. Check recursion.~%" (sh-lineno sh))
    (return-from process-input 1))
  (incf (sh-nesting sh))
  (setf (sh-lineno sh) 0)
  (let ((sql nil) (startline 0) (errors 0) (quit nil))
    (loop while (or (zerop errors) (not (sh-bail sh)) (and (null (sh-in sh)) (sh-interactive sh)))
          do (let ((line (handler-case (read-input-line sh (and sql t))
                           (sb-sys:interactive-interrupt () (out sh (string #\Newline)) (setf sql nil) ""))))
               (unless line
                 (when (and (null (sh-in sh)) (sh-interactive sh)) (out sh (string #\Newline)))
                 (return))
               (incf (sh-lineno sh))
               (when (and sql (command-terminator-p line) (sql-complete-p (concatenate 'string sql ";")))
                 (setf line ";"))
               (cond
                 ((and (null sql) (whitespace-or-comment-p line))
                  (when (sh-echo sh) (out sh (format nil "~a~%" line))))
                 ((and (null sql) (plusp (length line)) (member (char line 0) '(#\. #\#)))
                  (when (sh-echo sh) (out sh (format nil "~a~%" line)))
                  (when (char= (char line 0) #\.)
                    (let ((rc (handler-case (do-meta-command sh line)
                                (sqlp:sqlite-error (c) (err "Error: ~a~%" (sqlp:sqlite-error-message c)) 1))))
                      (cond ((eql rc 2) (setf quit t) (return))
                            ((and rc (/= rc 0)) (incf errors))))))
                 (t
                  (if (null sql)
                      (setf sql (string-left-trim '(#\Space #\Tab #\Newline #\Return #\Page) line)
                            startline (sh-lineno sh))
                      (setf sql (concatenate 'string sql (string #\Newline) line)))
                  (cond ((sql-complete-p sql)
                         (when (sh-echo sh) (out sh (format nil "~a~%" sql)))
                         (incf errors (run-sql-line sh sql startline))
                         (setf sql nil)
                         (when (sh-once sh) (close-output sh)))
                        ((whitespace-or-comment-p sql)
                         (when (sh-echo sh) (out sh (format nil "~a~%" sql)))
                         (setf sql nil)))))))
    (when (and sql (not quit))
      (when (sh-echo sh) (out sh (format nil "~a~%" sql)))
      (incf errors (run-sql-line sh sql startline)))
    (decf (sh-nesting sh))
    (flush sh)
    (if quit 2 (if (plusp errors) 1 0))))

;;; ------------------------------------------------------------------
;;; main

(defparameter *options*
  "   -ascii               set output mode to 'ascii'
   -bail                stop after hitting an error
   -batch               force batch I/O
   -box                 set output mode to 'box'
   -column              set output mode to 'column'
   -cmd COMMAND         run \"COMMAND\" before reading stdin
   -csv                 set output mode to 'csv'
   -echo                print inputs before execution
   -init FILENAME       read/process named file
   -[no]header          turn headers on or off
   -help                show this message
   -html                set output mode to HTML
   -interactive         force interactive I/O
   -json                set output mode to 'json'
   -line                set output mode to 'line'
   -list                set output mode to 'list'
   -markdown            set output mode to 'markdown'
   -newline SEP         set output row separator. Default: '\\n'
   -nullvalue TEXT      set text string for NULL values. Default ''
   -quote               set output mode to 'quote'
   -readonly            open the database read-only
   -separator SEP       set output column separator. Default: '|'
   -table               set output mode to 'table'
   -tabs                set output mode to 'tabs'
   -version             show SQLite version
")

(defun usage (argv0 detail)
  (err "Usage: ~a [OPTIONS] FILENAME [SQL]~%FILENAME is the name of an SQLite database. A new database is created~%if the file does not previously exist.~%" argv0)
  (if detail
      (err "OPTIONS include:~%~a" *options*)
      (err "Use the -help option for additional information~%"))
  (sb-ext:exit :code 1 :abort t))

(defun finish (sh)
  (ignore-errors (flush sh))
  (unless (eq (sh-out sh) *stdout*) (ignore-errors (close (sh-out sh))))
  (ignore-errors (force-output *stdout*))
  (when (sh-db sh) (ignore-errors (sqlp:close-database (sh-db sh)))))

(defun isatty (fd) (= 1 (sb-unix:unix-isatty fd)))

(defun main (argv)
  "Run the shell on ARGV (program name first); returns the exit code."
  (let* ((*stdout* (sb-sys:make-fd-stream 1 :output t :element-type '(unsigned-byte 8) :buffering :full))
         (*stderr* (sb-sys:make-fd-stream 2 :output t :element-type '(unsigned-byte 8) :buffering :full))
         (*stdin* (sb-sys:make-fd-stream 0 :input t :external-format '(:utf-8 :replacement #\?) :buffering :full))
         (argv0 (or (first argv) "sqlp"))
         (sh (make-shell :out *stdout* :interactive (isatty 0)))
         (cmds '()) (init-file nil) (read-stdin t) (rc 0))
    ;; pass 1: the file name, commands, and options that must come first
    (loop with args = (rest argv)
          while args
          do (let ((z (pop args)))
               (cond ((or (zerop (length z)) (char/= (char z 0) #\-))
                      (if (sh-filename sh) (progn (setf read-stdin nil) (push z cmds)) (setf (sh-filename sh) z)))
                     (t (let ((o (if (and (> (length z) 1) (char= (char z 1) #\-)) (subseq z 1) z)))
                          (cond ((member o '("-separator" "-nullvalue" "-newline" "-cmd") :test #'string=)
                                 (unless args (err "~a: Error: missing argument to ~a~%" argv0 z) (sb-ext:exit :code 1 :abort t))
                                 (pop args))
                                ((string= o "-init") (setf init-file (pop args)))
                                ((string= o "-batch") (setf (sh-interactive sh) nil))
                                ((string= o "-bail") (setf (sh-bail sh) t))
                                ((string= o "-readonly") (setf (sh-readonly sh) t))))))))
    (setf cmds (nreverse cmds))
    (let ((warn-memory (null (rest argv))))
      (unless (sh-filename sh) (setf (sh-filename sh) ":memory:"))
      (when (and (string/= (sh-filename sh) ":memory:") (probe-file (sh-filename sh))) (open-db sh))
      ;; ~/.sqliterc or -init
      (let ((rcfile (or init-file (let ((home (sb-posix:getenv "HOME"))) (and home (format nil "~a/.sqliterc" home))))))
        (when rcfile
          (let ((stream (ignore-errors (open rcfile :external-format '(:utf-8 :replacement #\?)))))
            (cond (stream
                   (when (sh-interactive sh) (err "-- Loading resources from ~a~%" rcfile))
                   (setf (sh-in sh) stream)
                   (when (and (plusp (process-input sh)) (sh-bail sh)) (finish sh) (return-from main 1))
                   (close stream)
                   (setf (sh-in sh) nil))
                  (init-file (err "cannot open: \"~a\"~%" init-file)
                             (when (sh-bail sh) (return-from main 1)))))))
      ;; pass 2: the rest of the options, in order
      (loop with args = (rest argv)
            while args
            do (let ((z (pop args)))
                 (when (and (plusp (length z)) (char= (char z 0) #\-))
                   (let ((o (if (and (> (length z) 1) (char= (char z 1) #\-)) (subseq z 1) z)))
                     (flet ((val () (pop args)))
                       (cond ((string= o "-init") (val))
                             ((string= o "-html") (setf (sh-mode sh) :html))
                             ((string= o "-list") (setf (sh-mode sh) :list))
                             ((string= o "-quote") (setf (sh-mode sh) :quote (sh-col-sep sh) "," (sh-row-sep sh) (string #\Newline)))
                             ((string= o "-line") (setf (sh-mode sh) :line))
                             ((string= o "-column") (setf (sh-mode sh) :column))
                             ((string= o "-json") (setf (sh-mode sh) :json))
                             ((string= o "-markdown") (setf (sh-mode sh) :markdown))
                             ((string= o "-table") (setf (sh-mode sh) :table))
                             ((string= o "-box") (setf (sh-mode sh) :box))
                             ((string= o "-csv") (setf (sh-mode sh) :csv (sh-col-sep sh) ","))
                             ((string= o "-readonly"))
                             ((string= o "-nofollow"))
                             ((string= o "-ascii") (setf (sh-mode sh) :ascii (sh-col-sep sh) (string (code-char 31))
                                                         (sh-row-sep sh) (string (code-char 30))))
                             ((string= o "-tabs") (setf (sh-mode sh) :list (sh-col-sep sh) (string #\Tab) (sh-row-sep sh) (string #\Newline)))
                             ((string= o "-separator") (setf (sh-col-sep sh) (val)))
                             ((string= o "-newline") (setf (sh-row-sep sh) (val)))
                             ((string= o "-nullvalue") (setf (sh-null-value sh) (val)))
                             ((string= o "-header") (setf (sh-show-header sh) t (sh-header-set sh) t))
                             ((string= o "-noheader") (setf (sh-show-header sh) nil (sh-header-set sh) t))
                             ((string= o "-echo") (setf (sh-echo sh) t))
                             ((string= o "-eqp") (setf (sh-auto-eqp sh) t))
                             ((string= o "-bail"))
                             ((string= o "-version")
                              (out sh (format nil "~a ~a~%" *version* *source-id*)) (finish sh) (return-from main 0))
                             ((string= o "-interactive") (setf (sh-interactive sh) t))
                             ((string= o "-batch") (setf (sh-interactive sh) nil))
                             ((member o '("-mmap" "-vfs" "-heap" "-maxsize" "-memtrace" "-sorterref") :test #'string=) (val))
                             ((member o '("-lookaside" "-pagecache" "-nonce" "-threadsafe") :test #'string=) (val) (val))
                             ((member o '("-stats" "-scanstats" "-safe" "-append" "-deserialize" "-backslash" "-multiplex" "-vfstrace")
                                      :test #'string=))
                             ((string= o "-help") (usage argv0 t))
                             ((string= o "-cmd")
                              (let ((c (val)))
                                (when c
                                  (if (char= (char c 0) #\.)
                                      (let ((r (do-meta-command sh c)))
                                        (when (and (/= r 0) (sh-bail sh)) (finish sh) (return-from main (if (= r 2) 0 r))))
                                      (let ((e (progn (open-db sh) (shell-exec sh c))))
                                        (when e
                                          (flush sh) (err "Error: ~a~%" e)
                                          (when (sh-bail sh) (finish sh) (return-from main 1))))))))
                             (t (err "~a: Error: unknown option: ~a~%Use -help for a list of options.~%" argv0 z)
                                (finish sh) (return-from main 1))))
                     (setf (sh-c-mode sh) (sh-mode sh))))))
      (cond
        ((not read-stdin)
         (dolist (c cmds)
           (if (char= (char c 0) #\.)
               (let ((r (do-meta-command sh c)))
                 (when (/= r 0) (finish sh) (return-from main (if (= r 2) 0 r))))
               (let ((e (progn (open-db sh) (shell-exec sh c))))
                 (when e
                   (flush sh) (err "Error: ~a~%" e)
                   (finish sh) (return-from main 1))))))
        ((sh-interactive sh)
         (out sh (format nil "SQLite version ~a ~a~%Enter \".help\" for usage hints.~%" *version*
                         (subseq *source-id* 0 (min 19 (length *source-id*)))))
         (when warn-memory
           (out sh (format nil "Connected to a ~c[1mtransient in-memory database~c[0m.~%Use \".open FILENAME\" to reopen on a persistent database.~%"
                           #\Esc #\Esc)))
         (setf rc (process-input sh)))
        (t (setf rc (process-input sh))))
      (finish sh)
      (if (= rc 2) 0 rc))))

(defun toplevel ()
  "Entry point for a saved image or a script: arguments from the command line."
  (setf sqlite-pure::*where-trace* (sb-ext:posix-getenv "SQLP_WHERETRACE")
        sqlite-pure::*flatten* (not (sb-ext:posix-getenv "SQLP_NO_FLATTEN")))
  (let* ((argv sb-ext:*posix-argv*)
         (pos (position "--end-toplevel-options" argv :test #'string=))
         (name (or (sb-ext:posix-getenv "SQLP_ARGV0") (first argv) "sqlp"))
         (args (cons name (if pos (nthcdr (1+ pos) argv) (rest argv)))))
    (sb-ext:exit :code (handler-case (main args)
                         (sb-sys:interactive-interrupt () 130))
                 :abort t)))
