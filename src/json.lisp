;;;; json.lisp — SQLite's JSON1 functions (as built into SQLite 3.40).
;;;;
;;;; Parsed JSON is a tree of lists:
;;;;   (:null) (:true) (:false) (:num "text") (:str "raw text between quotes")
;;;;   (:arr node...) (:obj (raw-key . node)...)
;;;; Numbers and strings keep their source text, because SQLite re-renders
;;;; them verbatim (json('1.0') is '1.0', escapes are preserved).
;;;;
;;;; SQLite tags values produced by JSON functions with a "JSON subtype" so
;;;; that json_array(json('[1]')) nests an array instead of a string.  The
;;;; strings produced here are recorded in *JSON-VALUES* (by identity) for
;;;; the duration of a statement, which is all the subtype ever lives for.

(in-package #:sqlite-pure)

(defvar *json-values* (make-hash-table :test #'eq))

(defun json-result (s)
  (setf (gethash s *json-values*) t)
  s)

(defun json-subtype-p (v) (and (stringp v) (gethash v *json-values*)))

(defun json-error () (sql-error "malformed JSON"))

;;; ------------------------------------------------------------------
;;; Parsing

(defun json-ws-p (c) (member c '(#\Space #\Tab #\Newline #\Return)))

(defun json-parse (s &optional (errorp t))
  "Parse the whole of string S; signal (or return NIL) if malformed."
  (let ((i 0) (n (length s)))
    (labels ((fail () (if errorp (json-error) (return-from json-parse nil)))
             (skip () (loop while (and (< i n) (json-ws-p (char s i))) do (incf i)))
             (expect-lit (lit node)
               (if (and (<= (+ i (length lit)) n) (string= lit s :start2 i :end2 (+ i (length lit))))
                   (progn (incf i (length lit)) node)
                   (fail)))
             (value (depth)
               (when (> depth 2000) (fail))
               (skip)
               (when (>= i n) (fail))
               (let ((c (char s i)))
                 (case c
                   (#\{ (incf i) (skip)
                    (if (and (< i n) (char= (char s i) #\}))
                        (progn (incf i) (list :obj))
                        (let ((members '()))
                          (loop
                            (skip)
                            (unless (and (< i n) (char= (char s i) #\")) (fail))
                            (let ((key (json-string-raw)))
                              (skip)
                              (unless (and (< i n) (char= (char s i) #\:)) (fail))
                              (incf i)
                              (push (cons key (value (1+ depth))) members))
                            (skip)
                            (cond ((and (< i n) (char= (char s i) #\,)) (incf i))
                                  ((and (< i n) (char= (char s i) #\})) (incf i) (return))
                                  (t (fail))))
                          (cons :obj (nreverse members)))))
                   (#\[ (incf i) (skip)
                    (if (and (< i n) (char= (char s i) #\]))
                        (progn (incf i) (list :arr))
                        (let ((items '()))
                          (loop
                            (push (value (1+ depth)) items)
                            (skip)
                            (cond ((and (< i n) (char= (char s i) #\,)) (incf i))
                                  ((and (< i n) (char= (char s i) #\])) (incf i) (return))
                                  (t (fail))))
                          (cons :arr (nreverse items)))))
                   (#\" (list :str (json-string-raw)))
                   (#\t (expect-lit "true" (list :true)))
                   (#\f (expect-lit "false" (list :false)))
                   (#\n (expect-lit "null" (list :null)))
                   (t (if (or (digit-char-p c) (char= c #\-)) (json-number) (fail))))))
             (json-string-raw ()
               ;; I is at the opening quote
               (let ((start (1+ i)))
                 (incf i)
                 (loop
                   (when (>= i n) (fail))
                   (let ((c (char s i)))
                     (cond ((char= c #\") (incf i) (return (subseq s start (1- i))))
                           ((char= c #\\)
                            (when (>= (1+ i) n) (fail))
                            (let ((e (char s (1+ i))))
                              (cond ((find e "\"\\/bfnrt") (incf i 2))
                                    ((char= e #\u)
                                     (unless (and (<= (+ i 6) n)
                                                  (loop for k from (+ i 2) below (+ i 6)
                                                        always (digit-char-p (char s k) 16)))
                                       (fail))
                                     (incf i 6))
                                    (t (fail)))))
                           ((< (char-code c) #x20) (fail))
                           (t (incf i)))))))
             (json-number ()
               (let ((start i))
                 (when (char= (char s i) #\-) (incf i))
                 (cond ((and (< i n) (char= (char s i) #\0)) (incf i))
                       ((and (< i n) (digit-char-p (char s i)))
                        (loop while (and (< i n) (digit-char-p (char s i))) do (incf i)))
                       (t (fail)))
                 (when (and (< i n) (char= (char s i) #\.))
                   (incf i)
                   (unless (and (< i n) (digit-char-p (char s i))) (fail))
                   (loop while (and (< i n) (digit-char-p (char s i))) do (incf i)))
                 (when (and (< i n) (char-equal (char s i) #\e))
                   (incf i)
                   (when (and (< i n) (member (char s i) '(#\+ #\-))) (incf i))
                   (unless (and (< i n) (digit-char-p (char s i))) (fail))
                   (loop while (and (< i n) (digit-char-p (char s i))) do (incf i)))
                 (list :num (subseq s start i)))))
      (let ((v (value 0)))
        (skip)
        (if (< i n) (fail) v)))))

(defun json-unescape (raw)
  "Decode the escapes of a JSON string body."
  (if (not (find #\\ raw))
      raw
      (with-output-to-string (out)
        (let ((i 0) (n (length raw)))
          (loop while (< i n)
                do (let ((c (char raw i)))
                     (if (char/= c #\\)
                         (progn (write-char c out) (incf i))
                         (let ((e (char raw (1+ i))))
                           (incf i 2)
                           (case e
                             (#\b (write-char (code-char 8) out))
                             (#\f (write-char (code-char 12) out))
                             (#\n (write-char #\Newline out))
                             (#\r (write-char (code-char 13) out))
                             (#\t (write-char #\Tab out))
                             (#\u (let ((u (parse-integer raw :start i :end (+ i 4) :radix 16)))
                                    (incf i 4)
                                    (if (and (<= #xd800 u #xdbff) (< (+ i 5) n)
                                             (char= (char raw i) #\\) (char= (char raw (1+ i)) #\u))
                                        (let ((lo (parse-integer raw :start (+ i 2) :end (+ i 6) :radix 16)))
                                          (if (<= #xdc00 lo #xdfff)
                                              (progn (incf i 6)
                                                     (write-char (safe-code-char
                                                                  (+ #x10000 (ash (- u #xd800) 10) (- lo #xdc00)))
                                                                 out))
                                              (write-char (safe-code-char u) out)))
                                        (write-char (safe-code-char u) out))))
                             (t (write-char e out)))))))))))

(defun json-escape (s)
  "Body of a JSON string holding the text S."
  (with-output-to-string (out)
    (loop for c across s
          for code = (char-code c)
          do (case c
               (#\" (write-string "\\\"" out))
               (#\\ (write-string "\\\\" out))
               (t (cond ((= code 8) (write-string "\\b" out))
                        ((= code 12) (write-string "\\f" out))
                        ((= code 10) (write-string "\\n" out))
                        ((= code 13) (write-string "\\r" out))
                        ((= code 9) (write-string "\\t" out))
                        ((< code #x20) (format out "\\u~4,'0x" code))
                        (t (write-char c out))))))))

;;; ------------------------------------------------------------------
;;; Rendering

(defun json-render (node)
  (with-output-to-string (out) (json-render-to node out)))

(defun json-render-to (node out)
  (ecase (car node)
    (:null (write-string "null" out))
    (:true (write-string "true" out))
    (:false (write-string "false" out))
    (:num (write-string (second node) out))
    (:str (write-char #\" out) (write-string (second node) out) (write-char #\" out))
    (:arr (write-char #\[ out)
     (loop for (x . more) on (cdr node)
           do (json-render-to x out) (when more (write-char #\, out)))
     (write-char #\] out))
    (:obj (write-char #\{ out)
     (loop for ((k . v) . more) on (cdr node)
           do (write-char #\" out) (write-string k out) (write-string "\":" out)
              (json-render-to v out)
              (when more (write-char #\, out)))
     (write-char #\} out))))

;;; ------------------------------------------------------------------
;;; SQL values <-> JSON

(defun json-number-value (text)
  (multiple-value-bind (r end int-syntax dbl) (scan-number text)
    (declare (ignore end))
    (rational-to-sql-number r int-syntax dbl)))

(defun json-node-sql-value (node)
  "The SQL value json_extract / ->> return for NODE."
  (ecase (car node)
    (:null :null)
    (:true 1)
    (:false 0)
    (:num (json-number-value (second node)))
    (:str (json-unescape (second node)))
    ((:arr :obj) (json-result (json-render node)))))

(defun sql-value-json-node (v)
  "JSON for an SQL value (a JSON-subtype string is embedded as JSON)."
  (cond ((eq v :null) (list :null))
        ((integerp v) (list :num (format nil "~d" v)))
        ((floatp v) (list :num (cond ((float-infinity-p v) (if (plusp v) "9e999" "-9e999"))
                                     (t (format-real v)))))
        ((json-subtype-p v) (json-parse v))
        ((stringp v) (list :str (json-escape v)))
        (t (sql-error "JSON cannot hold BLOB values"))))

(defun json-type-name (node)
  (ecase (car node)
    (:null "null") (:true "true") (:false "false")
    (:num (if (and (not (find #\. (second node))) (not (find #\e (second node) :test #'char-equal)))
              "integer" "real"))
    (:str "text") (:arr "array") (:obj "object")))

(defun json-arg (v)
  "Parse an SQL argument that should hold JSON text."
  (cond ((eq v :null) nil)
        ((blobp v) (json-error))
        (t (json-parse (value-to-text v)))))

;;; ------------------------------------------------------------------
;;; Paths

(defun json-parse-path (path)
  "'$.a[2].\"b c\"' -> list of steps: (:key \"a\") (:index 2) (:from-end 1) (:append)."
  (let ((i 1) (n (length path)) (steps '()))
    (flet ((fail () (sql-error "JSON path error near '~a'" (subseq path (min i n)))))
      (unless (and (plusp n) (char= (char path 0) #\$))
        (setf i 0) (fail))
      (loop while (< i n)
            do (let ((c (char path i)))
                 (cond
                   ((char= c #\.)
                    (incf i)
                    (if (and (< i n) (char= (char path i) #\"))
                        (let ((end (position #\" path :start (1+ i))))
                          (unless end (fail))
                          (push (list :key (subseq path (1+ i) end)) steps)
                          (setf i (1+ end)))
                        (let ((start i))
                          (loop while (and (< i n) (not (member (char path i) '(#\. #\[)))) do (incf i))
                          (when (= start i) (fail))
                          (push (list :key (subseq path start i)) steps))))
                   ((char= c #\[)
                    (incf i)
                    (cond ((and (< i n) (char= (char path i) #\#))
                           (incf i)
                           (cond ((and (< i n) (char= (char path i) #\]))
                                  (push (list :append) steps) (incf i))
                                 ((and (< i n) (char= (char path i) #\-))
                                  (let ((start (1+ i)))
                                    (setf i start)
                                    (loop while (and (< i n) (digit-char-p (char path i))) do (incf i))
                                    (unless (and (> i start) (< i n) (char= (char path i) #\])) (fail))
                                    (push (list :from-end (parse-integer path :start start :end i)) steps)
                                    (incf i)))
                                 (t (fail))))
                          (t (let ((start i))
                               (loop while (and (< i n) (digit-char-p (char path i))) do (incf i))
                               (unless (and (> i start) (< i n) (char= (char path i) #\])) (fail))
                               (push (list :index (parse-integer path :start start :end i)) steps)
                               (incf i)))))
                   (t (fail))))))
    (nreverse steps)))

(defun json-step-lookup (node step)
  (case (first step)
    (:key (when (eq (car node) :obj)
            (cdr (find (second step) (cdr node) :key (lambda (m) (json-unescape (car m)))
                                                :test #'string=))))
    (:index (when (eq (car node) :arr) (nth (second step) (cdr node))))
    (:from-end (when (eq (car node) :arr)
                 (let ((k (- (length (cdr node)) (second step))))
                   (when (>= k 0) (nth k (cdr node))))))
    (t nil)))

(defun json-lookup (node steps)
  (dolist (st steps node)
    (setf node (json-step-lookup node st))
    (unless node (return nil))))

(defun json-edit (node steps value mode)
  "Return NODE with VALUE put at STEPS.  MODE is :set, :insert, :replace or
:remove (VALUE ignored).  Missing containers are created for :set/:insert."
  (if (null steps)
      (ecase mode
        ((:set :replace) value)
        (:insert node)
        (:remove nil))
      (let ((step (first steps)) (rest (rest steps)))
        (flet ((fresh () (if rest
                             (json-edit (if (member (first (first rest)) '(:key)) (list :obj) (list :arr))
                                        rest value mode)
                             value)))
          (ecase (car node)
            (:obj
             (if (eq (first step) :key)
                 (let ((member (find (second step) (cdr node) :key (lambda (m) (json-unescape (car m)))
                                                             :test #'string=)))
                   (cond (member
                          (let ((new (json-edit (cdr member) rest value mode)))
                            (if new
                                (cons :obj (substitute (cons (car member) new) member (cdr node)))
                                (cons :obj (remove member (cdr node))))))
                         ((member mode '(:set :insert))
                          (append node (list (cons (json-escape (second step)) (fresh)))))
                         (t node)))
                 node))
            (:arr
             (let* ((items (cdr node))
                    (k (case (first step)
                         (:index (second step))
                         (:from-end (- (length items) (second step)))
                         (:append (length items))
                         (t nil))))
               (cond ((or (null k) (minusp k)) node)
                     ((< k (length items))
                      (let ((new (json-edit (nth k items) rest value mode)))
                        (cons :arr (if new
                                       (append (subseq items 0 k) (list new) (nthcdr (1+ k) items))
                                       (append (subseq items 0 k) (nthcdr (1+ k) items))))))
                     ((and (= k (length items)) (member mode '(:set :insert))
                           (or (eq (first step) :append) (eq (first step) :index)))
                      (append node (list (fresh))))
                     (t node))))
            (t node))))))

(defun arrow-path (p)
  "Right operand of -> / ->>: a path, a label, or an array index."
  (cond ((integerp p) (format nil "$[~d]" p))
        ((and (stringp p) (plusp (length p)) (char= (char p 0) #\$)) p)
        ((and (stringp p) (plusp (length p)) (char= (char p 0) #\[)) (concatenate 'string "$" p))
        (t (format nil "$.~a" (value-to-text p)))))

;;; ------------------------------------------------------------------
;;; Functions

(defsqlfun "json" (1 1) (args)
  (let ((node (json-arg (first args))))
    (if node (json-result (json-render node)) :null)))

(defsqlfun "json_valid" (1 1) (args)
  (let ((v (first args)))
    (cond ((eq v :null) 0)
          ((blobp v) 0)
          (t (if (json-parse (value-to-text v) nil) 1 0)))))

(defsqlfun "json_quote" (1 1) (args)
  (json-result (json-render (sql-value-json-node (first args)))))

(defsqlfun "json_array" (0 nil) (args)
  (json-result (json-render (cons :arr (mapcar #'sql-value-json-node args)))))

(defsqlfun "json_object" (0 nil) (args)
  (when (oddp (length args))
    (sql-error "json_object() requires an even number of arguments"))
  (json-result
   (json-render (cons :obj (loop for (k v) on args by #'cddr
                                 collect (progn
                                           (unless (stringp k)
                                             (sql-error "json_object() labels must be TEXT"))
                                           (cons (json-escape k) (sql-value-json-node v))))))))

(defsqlfun "json_extract" (1 nil) (args)
  (let ((node (json-arg (first args))))
    (cond ((null node) :null)
          ((null (cddr args))
           (let ((hit (json-lookup node (json-parse-path (value-to-text (second args))))))
             (if hit (json-node-sql-value hit) :null)))
          (t (json-result
              (json-render (cons :arr (mapcar (lambda (p)
                                                (or (json-lookup node (json-parse-path (value-to-text p)))
                                                    (list :null)))
                                              (rest args)))))))))

(defsqlfun "json_extract_arrow" (2 2) (args)
  (let ((node (json-arg (first args))))
    (if (null node)
        :null
        (let ((hit (json-lookup node (json-parse-path (arrow-path (second args))))))
          (if hit (json-result (json-render hit)) :null)))))

(defsqlfun "json_extract_arrow2" (2 2) (args)
  (let ((node (json-arg (first args))))
    (if (null node)
        :null
        (let ((hit (json-lookup node (json-parse-path (arrow-path (second args))))))
          (if hit (json-node-sql-value hit) :null)))))

(defsqlfun "json_type" (1 2) (args)
  (let ((node (json-arg (first args))))
    (if (null node)
        :null
        (let ((hit (if (cdr args) (json-lookup node (json-parse-path (value-to-text (second args)))) node)))
          (if hit (json-type-name hit) :null)))))

(defsqlfun "json_array_length" (1 2) (args)
  (let ((node (json-arg (first args))))
    (if (null node)
        :null
        (let ((hit (if (cdr args) (json-lookup node (json-parse-path (value-to-text (second args)))) node)))
          (cond ((null hit) :null)
                ((eq (car hit) :arr) (length (cdr hit)))
                (t 0))))))

(defun json-edit-fn (args mode)
  (let ((node (json-arg (first args))))
    (when (and (member mode '(:set :insert :replace)) (evenp (length args)))
      (sql-error "json_~(~a~)() needs an odd number of arguments" mode))
    (if (null node)
        :null
        (progn
          (if (eq mode :remove)
              (dolist (p (rest args))
                (when (eq p :null) (return-from json-edit-fn :null))
                (setf node (or (json-edit node (json-parse-path (value-to-text p)) nil :remove)
                               (return-from json-edit-fn :null))))
              (loop for (p v) on (rest args) by #'cddr
                    do (when (eq p :null) (return-from json-edit-fn :null))
                       (setf node (json-edit node (json-parse-path (value-to-text p))
                                             (sql-value-json-node v) mode))))
          (json-result (json-render node))))))

(defsqlfun "json_set" (1 nil) (args) (json-edit-fn args :set))
(defsqlfun "json_insert" (1 nil) (args) (json-edit-fn args :insert))
(defsqlfun "json_replace" (1 nil) (args) (json-edit-fn args :replace))
(defsqlfun "json_remove" (1 nil) (args) (json-edit-fn args :remove))

(defun json-merge-patch (target patch)
  (if (not (eq (car patch) :obj))
      patch
      (let ((result (if (eq (car target) :obj) (copy-list (cdr target)) '())))
        (dolist (m (cdr patch))
          (let* ((key (json-unescape (car m)))
                 (existing (find key result :key (lambda (x) (json-unescape (car x))) :test #'string=)))
            (cond ((eq (car (cdr m)) :null)
                   (setf result (remove existing result)))
                  (existing
                   (setf result (substitute (cons (car existing) (json-merge-patch (cdr existing) (cdr m)))
                                            existing result)))
                  (t (setf result (append result (list (cons (car m) (json-merge-patch (list :null) (cdr m))))))))))
        (cons :obj result))))

(defsqlfun "json_patch" (2 2) (args)
  (let ((target (json-arg (first args))) (patch (json-arg (second args))))
    (if (or (null target) (null patch))
        :null
        (json-result (json-render (json-merge-patch target patch))))))

(defaggregate "json_group_array" (1 1)
  (let ((items '()))
    (values (lambda (args) (push (sql-value-json-node (first args)) items) nil)
            (lambda () (json-result (json-render (cons :arr (reverse items))))))))

(defaggregate "json_group_object" (2 2)
  (let ((members '()))
    (values (lambda (args)
              (let ((k (first args)))
                (unless (eq k :null)
                  (push (cons (json-escape (value-to-text k)) (sql-value-json-node (second args)))
                        members)))
              nil)
            (lambda () (json-result (json-render (cons :obj (reverse members))))))))

;;; ------------------------------------------------------------------
;;; json_each / json_tree

(defparameter +json-each-columns+
  '("key" "value" "type" "atom" "id" "parent" "fullkey" "path" "json" "root"))

(defun json-table-rows (json-text path recursive)
  "Rows (lists) of json_each / json_tree."
  (let* ((root (json-parse json-text))
         (path (or path "$"))
         (steps (json-parse-path path))
         (counter 0)
         (ids (make-hash-table :test #'eq))
         (rows '()))
    ;; SQLite's ids are positions in its flat parse array, where every
    ;; object key also occupies a slot.
    (labels ((number-nodes (node)
               (setf (gethash node ids) counter)
               (incf counter)
               (case (car node)
                 (:arr (dolist (x (cdr node)) (number-nodes x)))
                 (:obj (dolist (m (cdr node)) (incf counter) (number-nodes (cdr m))))))
             (atom-of (node) (if (member (car node) '(:arr :obj)) :null (json-node-sql-value node)))
             (value-of (node) (if (member (car node) '(:arr :obj))
                                  (json-result (json-render node))
                                  (json-node-sql-value node)))
             (emit (node key parent fullkey parentpath)
               (push (list key (value-of node) (json-type-name node) (atom-of node)
                           (gethash node ids) parent fullkey parentpath json-text path)
                     rows))
             (child-key (fullkey m-or-i)
               (if (integerp m-or-i)
                   (format nil "~a[~d]" fullkey m-or-i)
                   (let ((k (json-unescape m-or-i)))
                     (if (every (lambda (c) (or (alphanumericp c) (char= c #\_))) k)
                         (format nil "~a.~a" fullkey k)
                         (format nil "~a.\"~a\"" fullkey k)))))
             (walk (node key parent fullkey parentpath)
               (emit node key parent fullkey parentpath)
               (when recursive
                 (walk-children node fullkey)))
             (walk-children (node fullkey)
               (case (car node)
                 (:arr (loop for x in (cdr node) for i from 0
                             do (walk x i (gethash node ids) (child-key fullkey i) fullkey)))
                 (:obj (loop for (k . v) in (cdr node)
                             do (walk v (json-unescape k) (gethash node ids) (child-key fullkey k) fullkey))))))
      (number-nodes root)
      (let ((start (json-lookup root steps)))
        (when start
          (if recursive
              (walk start (if (null steps) :null (json-path-last-key steps)) :null path
                    (json-path-parent path))
              (if (member (car start) '(:arr :obj))
                  (case (car start)
                    (:arr (loop for x in (cdr start) for i from 0
                                do (emit x i :null (child-key path i) path)))
                    (:obj (loop for (k . v) in (cdr start)
                                do (emit v (json-unescape k) :null (child-key path k) path))))
                  (emit start :null :null path (json-path-parent path)))))))
    (nreverse rows)))

(defun json-path-last-key (steps)
  (let ((s (car (last steps))))
    (case (first s) (:key (second s)) (:index (second s)) (t :null))))

(defun json-path-parent (path)
  (let ((p (max (or (position #\. path :from-end t) 0) (or (position #\[ path :from-end t) 0))))
    (if (zerop p) "$" (subseq path 0 p))))

(defun json-table-source (name arg-fns alias)
  "An FSRC for json_each / json_tree with argument closures ARG-FNS."
  (let* ((recursive (name= name "json_tree"))
         (src (derived-src (or alias name) +json-each-columns+
                           (make-list 10 :initial-element nil)
                           (make-list 10 :initial-element :binary))))
    (setf (src-hidden src) '(8 9))
    (make-fsrc :src src
               :rows-fn (lambda (env)
                          (let* ((vals (mapcar (lambda (f) (funcall f env)) arg-fns))
                                 (j (first vals)))
                            (if (or (null vals) (eq j :null))
                                '()
                                (rows-to-vectors
                                 (json-table-rows (value-to-text j)
                                                  (and (second vals) (not (eq (second vals) :null))
                                                       (value-to-text (second vals)))
                                                  recursive))))))))
