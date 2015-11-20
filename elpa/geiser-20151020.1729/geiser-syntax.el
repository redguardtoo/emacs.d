;;; geiser-syntax.el -- utilities for parsing scheme syntax

;; Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014, 2015 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sun Feb 08, 2009 15:03



(require 'geiser-impl)
(require 'geiser-popup)
(require 'geiser-base)

(require 'scheme)

(eval-when-compile (require 'cl))


;;; Indentation:

(defmacro geiser-syntax--scheme-indent (&rest pairs)
  `(progn ,@(mapcar (lambda (p)
                      `(put ',(car p) 'scheme-indent-function ',(cadr p)))
                    pairs)))

(geiser-syntax--scheme-indent
 (and-let* 1)
 (case-lambda 0)
 (catch defun)
 (class defun)
 (dynamic-wind 0)
 (guard 1)
 (let*-values 1)
 (let-values 1)
 (let/ec 1)
 (letrec* 1)
 (match 1)
 (match-lambda 0)
 (match-lambda* 0)
 (match-let 1)
 (match-let* 1)
 (match-letrec 1)
 (opt-lambda 1)
 (parameterize 1)
 (parameterize* 1)
 (receive 2)
 (require-extension 0)
 (syntax-case 2)
 (test-approximate 1)
 (test-assert 1)
 (test-eq 1)
 (test-equal 1)
 (test-eqv 1)
 (test-group-with-cleanup 1)
 (test-runner-on-bad-count! 1)
 (test-runner-on-bad-end-name! 1)
 (test-runner-on-final! 1)
 (test-runner-on-group-begin! 1)
 (test-runner-on-group-end! 1)
 (test-runner-on-test-begin! 1)
 (test-runner-on-test-end! 1)
 (test-with-runner 1)
 (unless 1)
 (when 1)
 (while 1)
 (with-exception-handler 1)
 (with-syntax 1))


;;; Extra syntax keywords

(defconst geiser-syntax--builtin-keywords
  '("and-let*"
    "cut"
    "cute"
    "define-condition-type"
    "define-immutable-record-type"
    "define-record-type"
    "define-values"
    "letrec*"
    "match"
    "match-lambda"
    "match-lambda*"
    "match-let"
    "match-let*"
    "match-letrec"
    "parameterize"
    "receive"
    "require-extension"
    "set!"
    "syntax-case"
    "test-approximate"
    "test-assert"
    "test-begin"
    "test-end"
    "test-eq"
    "test-equal"
    "test-eqv"
    "test-error"
    "test-group"
    "test-group-with-cleanup"
    "test-with-runner"
    "unless"
    "when"
    "with-exception-handler"
    "with-input-from-file"
    "with-output-to-file"))

(defun geiser-syntax--simple-keywords (keywords)
  "Return `font-lock-keywords' to highlight scheme KEYWORDS.
KEYWORDS should be a list of strings."
  (when keywords
    `((,(format "[[(]%s\\>" (regexp-opt keywords 1)) . 1))))

(defun geiser-syntax--keywords ()
  (append
   (geiser-syntax--simple-keywords geiser-syntax--builtin-keywords)
   `(("\\[\\(else\\)\\>" . 1)
     (,(rx "(" (group "define-syntax-rule") eow (* space)
           (? "(") (? (group (1+ word))))
      (1 font-lock-keyword-face)
      (2 font-lock-function-name-face nil t)))))

(font-lock-add-keywords 'scheme-mode (geiser-syntax--keywords))

(geiser-impl--define-caller geiser-syntax--impl-kws keywords ()
  "A variable (or thunk returning a value) giving additional,
implementation-specific entries for font-lock-keywords.")

(geiser-impl--define-caller geiser-syntax--case-sensitive case-sensitive ()
  "A flag saying whether keywords are case sensitive.")

(defun geiser-syntax--add-kws ()
  (when (not (and (boundp 'quack-mode) quack-mode))
    (let ((kw (geiser-syntax--impl-kws geiser-impl--implementation))
          (cs (geiser-syntax--case-sensitive geiser-impl--implementation)))
      (when kw (font-lock-add-keywords nil kw))
      (setq font-lock-keywords-case-fold-search (not cs)))))


;;; A simple scheme reader

(defvar geiser-syntax--read/buffer-limit nil)

(defsubst geiser-syntax--read/eos ()
  (or (eobp)
      (and geiser-syntax--read/buffer-limit
           (<= geiser-syntax--read/buffer-limit (point)))))

(defsubst geiser-syntax--read/next-char ()
  (unless (geiser-syntax--read/eos)
    (forward-char)
    (char-after)))

(defsubst geiser-syntax--read/token (token)
  (geiser-syntax--read/next-char)
  (if (listp token) token (list token)))

(defsubst geiser-syntax--read/elisp ()
  (ignore-errors (read (current-buffer))))

(defun geiser-syntax--read/symbol ()
  (with-syntax-table scheme-mode-syntax-table
    (when (re-search-forward "\\(\\sw\\|\\s_\\)+" nil t)
      (make-symbol (match-string-no-properties 0)))))

(defun geiser-syntax--read/matching (open close)
  (let ((count 1)
        (p (1+ (point))))
    (while (and (> count 0)
                (geiser-syntax--read/next-char))
      (cond ((looking-at-p open) (setq count (1+ count)))
            ((looking-at-p close) (setq count (1- count)))))
    (buffer-substring-no-properties p (point))))

(defsubst geiser-syntax--read/unprintable ()
  (geiser-syntax--read/token
   (cons 'unprintable (geiser-syntax--read/matching "<" ">"))))

(defun geiser-syntax--read/skip-comment ()
  (while (and (geiser-syntax--read/next-char)
              (nth 8 (syntax-ppss))))
  (geiser-syntax--read/next-token))

(defun geiser-syntax--read/next-token ()
  (skip-syntax-forward "->")
  (if (geiser-syntax--read/eos) '(eob)
    (case (char-after)
      (?\; (geiser-syntax--read/skip-comment))
      ((?\( ?\[) (geiser-syntax--read/token 'lparen))
      ((?\) ?\]) (geiser-syntax--read/token 'rparen))
      (?. (if (memq (car (syntax-after (1+ (point)))) '(0 11 12))
              (geiser-syntax--read/token 'dot)
            (cons 'atom (geiser-syntax--read/elisp))))
      (?\# (case (geiser-syntax--read/next-char)
             ('nil '(eob))
             (?| (geiser-syntax--read/skip-comment))
             (?: (if (geiser-syntax--read/next-char)
                     (cons 'kwd (geiser-syntax--read/symbol))
                   '(eob)))
             (?\\ (cons 'char (geiser-syntax--read/elisp)))
             (?\( (geiser-syntax--read/token 'vectorb))
             (?\< (geiser-syntax--read/unprintable))
             ((?' ?` ?,) (geiser-syntax--read/next-token))
             (t (let ((tok (geiser-syntax--read/symbol)))
                  (cond ((equal (symbol-name tok) "t") '(boolean . :t))
                        ((equal (symbol-name tok) "f") '(boolean . :f))
                        (tok (cons 'atom tok))
                        (t (geiser-syntax--read/next-token)))))))
      (?\' (geiser-syntax--read/token '(quote . quote)))
      (?\` (geiser-syntax--read/token
            `(backquote . ,backquote-backquote-symbol)))
      (?, (if (eq (geiser-syntax--read/next-char) ?@)
              (geiser-syntax--read/token
               `(splice . ,backquote-splice-symbol))
            `(unquote . ,backquote-unquote-symbol)))
      (?\" (cons 'string (geiser-syntax--read/elisp)))
      (t (cons 'atom (geiser-syntax--read/symbol))))))

(defsubst geiser-syntax--read/match (&rest tks)
  (let ((token (geiser-syntax--read/next-token)))
    (if (memq (car token) tks) token
      (error "Unexpected token: %s" token))))

(defsubst geiser-syntax--read/skip-until (&rest tks)
  (let (token)
    (while (and (not (memq (car token) tks))
                (not (eq (car token) 'eob)))
      (setq token (geiser-syntax--read/next-token)))
    token))

(defsubst geiser-syntax--read/try (&rest tks)
  (let ((p (point))
        (tk (ignore-errors (apply 'geiser-syntax--read/match tks))))
    (unless tk (goto-char p))
    tk))

(defun geiser-syntax--read/list ()
  (cond ((geiser-syntax--read/try 'dot)
         (let ((tail (geiser-syntax--read)))
           (geiser-syntax--read/skip-until 'eob 'rparen)
           tail))
        ((geiser-syntax--read/try 'rparen 'eob) nil)
        (t (cons (geiser-syntax--read)
                 (geiser-syntax--read/list)))))

(defun geiser-syntax--read ()
  (let ((token (geiser-syntax--read/next-token))
        (max-lisp-eval-depth (max max-lisp-eval-depth 3000)))
    (case (car token)
      (eob nil)
      (lparen (geiser-syntax--read/list))
      (vectorb (apply 'vector (geiser-syntax--read/list)))
      ((quote backquote unquote splice) (list (cdr token)
                                              (geiser-syntax--read)))
      (kwd (make-symbol (format ":%s" (cdr token))))
      (unprintable (format "#<%s>" (cdr token)))
      ((char string atom) (cdr token))
      (boolean (cdr token))
      (t (error "Reading scheme syntax: unexpected token: %s" token)))))

(defun geiser-syntax--read-from-string (string &optional start end)
  (when (stringp string)
    (let* ((start (or start 0))
           (end (or end (length string)))
           (max-lisp-eval-depth (min 20000
                                     (max max-lisp-eval-depth (- end start)))))
      (with-temp-buffer
        (save-excursion (insert string))
        (cons (ignore-errors (geiser-syntax--read)) (point))))))

(defun geiser-syntax--form-from-string (s)
  (car (geiser-syntax--read-from-string s)))

(defsubst geiser-syntax--form-after-point (&optional boundary)
  (let ((geiser-syntax--read/buffer-limit (and (numberp boundary) boundary)))
    (save-excursion (values (geiser-syntax--read) (point)))))

(defun geiser-syntax--mapconcat (fun lst sep)
  (cond ((null lst) "")
        ((not (listp lst)) (format ".%s%s" sep (funcall fun lst)))
        ((null (cdr lst)) (format "%s" (funcall fun (car lst))))
        (t (format "%s%s%s"
                   (funcall fun (car lst))
                   sep
                   (geiser-syntax--mapconcat fun (cdr lst) sep)))))


;;; Code parsing:

(defsubst geiser-syntax--symbol-at-point ()
  (and (not (nth 8 (syntax-ppss)))
       (car (geiser-syntax--read-from-string (thing-at-point 'symbol)))))

(defsubst geiser-syntax--skip-comment/string ()
  (let ((pos (nth 8 (syntax-ppss))))
    (goto-char (or pos (point)))
    pos))

(defsubst geiser-syntax--nesting-level ()
  (or (nth 0 (syntax-ppss)) 0))

(defun geiser-syntax--pop-to-top ()
  (ignore-errors
    (while (> (geiser-syntax--nesting-level) 0) (backward-up-list))))

(defsubst geiser-syntax--in-string-p ()
  (nth 3 (syntax-ppss)))

(defsubst geiser-syntax--pair-length (p)
  (if (cdr (last p)) (1+ (safe-length p)) (length p)))

(defun geiser-syntax--shallow-form (boundary)
  (when (looking-at-p "\\s(")
    (save-excursion
      (forward-char)
      (let ((elems))
        (ignore-errors
          (while (< (point) boundary)
            (skip-syntax-forward "-<>")
            (when (<= (point) boundary)
              (forward-sexp)
              (let ((s (thing-at-point 'symbol)))
                (unless (equal "." s)
                  (push (car (geiser-syntax--read-from-string s)) elems))))))
        (nreverse elems)))))

(defsubst geiser-syntax--keywordp (s)
  (and s (symbolp s) (string-match "^:.+" (symbol-name s))))

(defsubst geiser-syntax--symbol-eq (s0 s1)
  (and (symbolp s0) (symbolp s1) (equal (symbol-name s0) (symbol-name s1))))

(defun geiser-syntax--scan-sexps (&optional begin)
  (let* ((fst (geiser-syntax--symbol-at-point))
         (smth (or fst (not (looking-at-p "[\s \s)\s>\s<\n]"))))
         (path (and fst `((,fst 0)))))
    (save-excursion
      (while (> (or (geiser-syntax--nesting-level) 0) 0)
        (let ((boundary (point)))
          (geiser-syntax--skip-comment/string)
          (backward-up-list)
          (let ((form (geiser-syntax--shallow-form boundary)))
            (when (and (listp form) (car form) (symbolp (car form)))
              (let* ((len (geiser-syntax--pair-length form))
                     (pos (if smth (1- len) (progn (setq smth t) len)))
                     (prev (and (> pos 1) (nth (1- pos) form)))
                     (prev (and (geiser-syntax--keywordp prev)
                                (list prev))))
                (push `(,(car form) ,pos ,@prev) path)))))))
    (mapcar (lambda (e)
              (cons (substring-no-properties (format "%s" (car e))) (cdr e)))
            (nreverse path))))

(defsubst geiser-syntax--binding-form-p (bfs sbfs f)
  (and (symbolp f)
       (let ((f (symbol-name f)))
         (or (member f '("define" "define*" "define-syntax"
                         "syntax-rules" "lambda" "case-lambda"
                         "let" "let*" "let-values" "let*-values"
                         "letrec" "letrec*" "parameterize"))
             (member f bfs)
             (member f sbfs)))))

(defsubst geiser-syntax--binding-form*-p (sbfs f)
  (and (symbolp f)
       (let ((f (symbol-name f)))
         (or (member f '("let*" "let*-values" "letrec" "letrec*"))
             (member f sbfs)))))

(defsubst geiser-syntax--if-symbol (x) (and (symbolp x) x))
(defsubst geiser-syntax--if-list (x) (and (listp x) x))

(defsubst geiser-syntax--normalize (vars)
  (mapcar (lambda (i)
            (let ((i (if (listp i) (car i) i)))
              (and (symbolp i) (symbol-name i))))
          vars))

(defun geiser-syntax--linearize (form)
  (cond ((not (listp form)) (list form))
	((null form) nil)
	(t (cons (car form) (geiser-syntax--linearize (cdr form))))))

(defun geiser-syntax--scan-locals (bfs sbfs form nesting locals)
  (if (or (null form) (not (listp form)))
      (geiser-syntax--normalize locals)
    (if (not (geiser-syntax--binding-form-p bfs sbfs (car form)))
	(geiser-syntax--scan-locals bfs sbfs
				    (car (last form))
                                    (1- nesting) locals)
      (let* ((head (car form))
	     (name (geiser-syntax--if-symbol (cadr form)))
	     (names (if name (geiser-syntax--if-list (caddr form))
		      (geiser-syntax--if-list (cadr form))))
             (bns (and name
                       (geiser-syntax--binding-form-p bfs sbfs (car names))))
	     (rest (if (and name (not bns)) (cdddr form) (cddr form)))
	     (use-names (and (or rest
                                 (< nesting 1)
                                 (geiser-syntax--binding-form*-p sbfs head))
                             (not bns))))
	(when name (push name locals))
        (when (geiser-syntax--symbol-eq head 'case-lambda)
          (dolist (n (and (> nesting 0) (caar (last form))))
            (when n (push n locals)))
          (setq rest (and (> nesting 0) (cdr form)))
          (setq use-names nil))
        (when (geiser-syntax--symbol-eq head 'syntax-rules)
          (dolist (n (and (> nesting 0) (cdaar (last form))))
            (when n (push n locals)))
          (setq rest (and (> nesting 0) (cdr form))))
	(when use-names
	  (dolist (n (geiser-syntax--linearize names))
            (let ((xs (if (and (listp n) (listp (car n))) (car n) (list n))))
              (dolist (x xs) (when x (push x locals))))))
	(dolist (f (butlast rest))
	  (when (and (listp f)
                     (geiser-syntax--symbol-eq (car f) 'define)
                     (cadr f))
	    (push (cadr f) locals)))
	(geiser-syntax--scan-locals bfs sbfs
				    (car (last (or rest names)))
                                    (1- nesting)
				    locals)))))

(defun geiser-syntax--locals-around-point (bfs sbfs)
  (when (eq major-mode 'scheme-mode)
    (save-excursion
      (let ((sym (unless (geiser-syntax--skip-comment/string)
                   (thing-at-point 'symbol))))
        (skip-syntax-forward "->")
        (let ((boundary (point))
              (nesting (geiser-syntax--nesting-level)))
          (geiser-syntax--pop-to-top)
          (multiple-value-bind (form end)
              (geiser-syntax--form-after-point boundary)
            (delete sym
                    (geiser-syntax--scan-locals bfs
                                                sbfs
                                                form
                                                (1- nesting)
                                                '()))))))))


;;; Display and fontify strings as Scheme code:

(defun geiser-syntax--display (a)
  (cond ((null a) "()")
        ((eq a :t) "#t")
        ((eq a :f) "#f")
        ((geiser-syntax--keywordp a) (format "#%s" a))
        ((symbolp a) (format "%s" a))
        ((equal a "...") "...")
        ((stringp a) (format "%S" a))
        ((and (listp a) (symbolp (car a))
              (equal (symbol-name (car a)) "quote"))
         (format "'%s" (geiser-syntax--display (cadr a))))
        ((listp a)
         (format "(%s)"
                 (geiser-syntax--mapconcat 'geiser-syntax--display a " ")))
        (t (format "%s" a))))

(defun geiser-syntax--font-lock-buffer ()
  (let ((name " *geiser font lock*"))
    (or (get-buffer name)
        (let ((buffer (get-buffer-create name)))
          (set-buffer buffer)
          (let ((geiser-default-implementation
                 (or geiser-default-implementation
                     (car geiser-active-implementations))))
            (scheme-mode))
          buffer))))

(defun geiser-syntax--scheme-str (str)
  (save-current-buffer
    (set-buffer (geiser-syntax--font-lock-buffer))
    (erase-buffer)
    (insert str)
    (let ((font-lock-verbose nil))
      (if (fboundp 'font-lock-ensure)
          (font-lock-ensure)
        (with-no-warnings
          (font-lock-fontify-buffer))))
    (buffer-string)))


(provide 'geiser-syntax)
