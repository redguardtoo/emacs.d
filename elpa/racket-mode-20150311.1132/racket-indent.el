;;; racket-indent.el

;; Copyright (c) 2013-2015 by Greg Hendershott.
;; Portions Copyright (C) 1985-1986, 1999-2013 Free Software Foundation, Inc.

;; Author: Greg Hendershott
;; URL: https://github.com/greghendershott/racket-mode

;; License:
;; This is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version. This is distributed in the hope that it will be
;; useful, but without any warranty; without even the implied warranty
;; of merchantability or fitness for a particular purpose. See the GNU
;; General Public License for more details. See
;; http://www.gnu.org/licenses/ for details.

(require 'racket-custom)

;; The two top-level commands we care about are:
;;   1. `indent-region' C-M-\
;;   2. `indent-pp-sexp' C-M-q
;;
;; 1. `indent-region' is in indent.el. Normally it calls
;; `indent-according-to-mode', which in turn calls the mode-specific
;; `indent-line-function'. In lisp-mode that's `lisp-indent-line', in
;; racket-mode that's `racket-indent-line'. These in turn call
;; `calculate-lisp-indent'. That in turn calls the mode-specific
;; `indent-function' -- in our case `racket-indent-function'.
;;
;; 2. `indent-pp-sexp' is lisp-specific, in lisp-mode.el. This is
;; a wrapper for `indent-sexp', which also uses
;; `calculate-lisp-indent', and therefore `racket-indent-function'.
;; (AFAICT `indent-line' is not involved with this).
;;
;; The status quo Emacs design seems to support (a) indentation
;; customization per mode, while also (b) allowing some lisp
;; indentation logic to be factored out for "DRY" as
;; `calculate-lisp-indent'. On the other hand, while tracing through
;; with edebug there seems to be a lot of complexity, as well as some
;; duplication of work, among `calculate-lisp-indent' and
;; `lisp-indent-function'. Yet I'm not quite brave enough to take out
;; a clean sheet of paper and rewrite from scratch.

(defun racket-indent-line (&optional whole-exp)
  "Indent current line as Racket code.

This behaves like `lisp-indent-line', except that whole-line
comments are treated the same regardless of whether they start
with single or double semicolons.

- Automatically indents forms that start with `begin` in the usual
  way that `begin` is indented.

- Automatically indents forms that start with `def` or `with-` in the
  usual way that `define` is indented.

- Has rules for many specific standard Racket forms.

To extend, use your Emacs init file to

    (put SYMBOL 'racket-indent-function INDENT)

where `SYMBOL` is the name of the Racket form (e.g. `'test-case`)
and `INDENT` is an integer or the symbol `'defun`. When `INDENT`
is an integer, the meaning is the same as for
`lisp-indent-function` and `scheme-indent-function`: Indent the
first `n` arguments specially and then indent any further
arguments like a body.

For example in your `.emacs` file you could use:

    (put 'test-case 'racket-indent-function 1)

to change the indent of `test-case` from this:

    (test-case foo
               blah
               blah)

to this:

    (test-case foo
      blah
      blah)
"
  (interactive)
  (let ((indent (calculate-lisp-indent))
	(pos (- (point-max) (point)))
	(beg (progn (beginning-of-line) (point))))
    (skip-chars-forward " \t")
    (if (or (null indent) (looking-at "\\s<\\s<\\s<"))
	;; Don't alter indentation of a ;;; comment line
	;; or a line that starts in a string.
        ;; FIXME: inconsistency: comment-indent moves ;;; to column 0.
	(goto-char (- (point-max) pos))
      (when (listp indent)
        (setq indent (car indent)))
      (unless (zerop (- indent (current-column)))
        (delete-region beg (point))
        (indent-to indent))
      ;; If initial point was within line's indentation,
      ;; position after the indentation.  Else stay at same point in text.
      (when (> (- (point-max) pos) (point))
        (goto-char (- (point-max) pos))))))

(defvar calculate-lisp-indent-last-sexp)

;; Copied from lisp-mode but heavily modified
(defun racket-indent-function (indent-point state)
  "Racket mode function for the value of the variable `lisp-indent-function'.
This behaves like the function `lisp-indent-function', except that:

i) it checks for a non-nil value of the property `racket-indent-function'
rather than `lisp-indent-function'.

ii) if that property specifies a function, it is called with three
arguments (not two), the third argument being the default (i.e., current)
indentation.

iii) there is special handling for:
  - forms that begin with a #:keyword
  - sequence literals when `racket-indent-sequence-depth' is > 0
  - {} forms when `racket-indent-curly-as-sequence'

The function `calculate-lisp-indent' calls this to determine
if the arguments of a Lisp function call should be indented specially.

INDENT-POINT is the position at which the line being indented begins.
Point is located at the point to indent under (for default indentation);
STATE is the `parse-partial-sexp' state for that position.

If the current line is in a call to a Lisp form that has a non-nil
property `racket-indent-function' it specifies how to indent.  The property
value can be:

* `defun', meaning indent `defun'-style
  \(this is also the case if there is no property and the form
  has a name that begins with \"def\" or \"with-\");

* an integer N, meaning indent the first N arguments specially
  \(like ordinary function arguments), and then indent any further
  arguments like a body
  \(a value of 0 is used if there is no property and the form
  has a name that begins with \"begin\");

* a function to call that returns the indentation (or nil).
  `lisp-indent-function' calls this function with the same two arguments
  that it itself received.

This function returns either the indentation to use, or nil if the
Lisp function does not specify a special indentation."
  (let ((normal-indent (current-column))
        (open-pos      (elt state 1))   ;start of innermost containing list
        (last-sexp-pos (elt state 2)))  ;start of last complete sexp terminated
    (goto-char (1+ open-pos))
    (parse-partial-sexp (point) calculate-lisp-indent-last-sexp 0 t)
    (if (and last-sexp-pos
             (or (not (looking-at (rx (or (syntax word) (syntax symbol)))))
                 (looking-at (rx "#:" (or (syntax word) (syntax symbol))))))
        (progn
          (backward-prefix-chars)
          (current-column))
      (let* ((head (buffer-substring (point) (progn (forward-sexp 1) (point))))
             (method (get (intern-soft head) 'racket-indent-function)))
        (cond ((racket--align-sequence-with-head)
               (goto-char open-pos)
               (1+ (current-column)))
              ((and (null method)
                    (string-match (rx bos "begin") head))
               (racket--indent-specform 0 state indent-point normal-indent))
              ((or (eq method 'defun)
                   (and (null method)
                        (string-match (rx bos (or "def" "with-")) head)))
               (lisp-indent-defform state indent-point))
              ((integerp method)
               (racket--indent-specform method state indent-point normal-indent))
              (method
               (funcall method state indent-point normal-indent)))))))

(defun racket--align-sequence-with-head ()
  "Indent items with the head item for certain sequences?

These include '() `() #() -- and {} if `racket-indent-curly-as-sequence'
is t -- but not #'() #`() ,() ,@().

To handle nested items, search `backward-up-list' up to
`racket-indent-sequence-depth' times."
  (and (>= racket-indent-sequence-depth 1)
       (save-excursion
         (condition-case ()
             (let ((answer 'unknown)
                   (depth racket-indent-sequence-depth))
               (while (and (eq answer 'unknown)
                           (> depth 0))
                 (backward-up-list)
                 (setq depth (1- depth))
                 (cond ((or
                         ;; a quoted '( ) or quasiquoted `( ) list --
                         ;; but NOT syntax #'( ) or quasisyntax #`( )
                         (and (memq (char-before (point)) '(?\' ?\`))
                              (eq (char-after (point)) ?\()
                              (not (eq (char-before (1- (point))) ?#)))
                         ;; a vector literal: #( )
                         (and (eq (char-before (point)) ?#)
                              (eq (char-after  (point)) ?\())
                         ;; { }
                         (and racket-indent-curly-as-sequence
                              (eq (char-after (point)) ?{)))
                        (setq answer t))
                       (;; unquote or unquote-splicing
                        (and (or (eq (char-before (point)) ?,)
                                 (and (eq (char-before (1- (point))) ?,)
                                      (eq (char-before (point))      ?@)))
                             (eq (char-after (point)) ?\())
                        (setq answer nil))))
               (eq answer t))
           (error nil)))))

(defun racket--indent-specform (count state indent-point normal-indent)
  "This is like `lisp-indent-specform' but fixes bug #50."
  (let ((containing-form-start (elt state 1))
        (orig-count count))
    ;; Move to the start of containing form, calculate indentation to
    ;; use for non-distinguished forms (> count), and move past the
    ;; function symbol. `lisp-indent-function' guarantees that there
    ;; is at least one word or symbol character following open paren
    ;; of containing form.
    (goto-char containing-form-start)
    (let* ((containing-form-column (current-column))
           (body-indent (+ lisp-body-indent containing-form-column))
           non-distinguished-column)
      (forward-char 1)
      (forward-sexp 1)
      (parse-partial-sexp (point) indent-point 1 t)
      ;; Now find the start of the last form.
      (while (and (< (point) indent-point)
                  (condition-case ()
                      (progn
                        (setq count (1- count))
                        (forward-sexp 1)
                        (parse-partial-sexp (point) indent-point 1 t)
                        ;; Remember column of first non-distinguished
                        ;; form -- provided it's the first form on
                        ;; the line.
                        (when (and (zerop count)
                                   (looking-back (rx bol (* (syntax whitespace)))))
                          (setq non-distinguished-column (current-column)))
                        t)
                    (error nil))))
      (cond ((> count 0) ;; A distinguished form
             (list (+ containing-form-column (* 2 lisp-body-indent))
                   containing-form-start))
            ((or (and (= orig-count 0) (= count 0))
                 (and (= count 0) (<= body-indent normal-indent)))
             body-indent)
            (non-distinguished-column non-distinguished-column)
            (t normal-indent)))))

(defun racket--conditional-indent (state indent-point normal-indent
                                   looking-at-regexp true false)
  (skip-chars-forward " \t")
  (let ((n (if (looking-at looking-at-regexp) true false)))
    (lisp-indent-specform n state indent-point normal-indent)))

(defun racket--indent-let (state indent-point normal-indent)
  ;; check for named let
  (racket--conditional-indent state indent-point normal-indent
                              "[-a-zA-Z0-9+*/?!@$%^&_:~]" 2 1))

(defun racket--indent-for (state indent-point normal-indent)
  "Indent function for all for/ and for*/ forms EXCEPT
for/fold and for*/fold."
  ;; check for either of:
  ;; - maybe-type-ann e.g. (for/list : T ([x xs]) x)
  ;; - for/vector optional length, (for/vector #:length ([x xs]) x)
  (racket--conditional-indent state indent-point normal-indent
                              "[:#]" 3 1))

(defun racket--indent-for/fold (state indent-point normal-indent)
  "Indent function for for/fold and for*/fold."
  ;; check for maybe-type-ann e.g. (for/fold : T ([n 0]) ([x xs]) x)
  (skip-chars-forward " \t")
  (if (looking-at ":")
      (lisp-indent-specform 4 state indent-point normal-indent)
    (racket--indent-for/fold-untyped state indent-point normal-indent)))

(defun racket--indent-for/fold-untyped (state indent-point normal-indent)
  ;; see http://community.schemewiki.org/?emacs-indentation
  (let ((containing-sexp-start (elt state 1))
        containing-sexp-point
        containing-sexp-column
        body-indent
        clause-indent)
    ;; Move to the start of containing sexp, calculate its
    ;; indentation, store its point and move past the function symbol
    ;; so that we can use 'parse-partial-sexp'.
    ;;
    ;; 'lisp-indent-function' guarantees that there is at least one
    ;; word or symbol character following open paren of containing
    ;; sexp.
    (forward-char 1)
    (goto-char containing-sexp-start)
    (setq containing-sexp-point (point))
    (setq containing-sexp-column (current-column))
    (setq body-indent (+ lisp-body-indent containing-sexp-column))
    (forward-char 1)    ;Move past the open paren.
    (forward-sexp 2)    ;Move to the next sexp, past its close paren
    (backward-sexp 1)   ;Move to its start paren
    (setq clause-indent (current-column))
    (forward-sexp 1)    ;Move back past close paren
    ;; Now go back to the beginning of the line holding
    ;; the indentation point. Count the sexps on the way.
    (parse-partial-sexp (point) indent-point 1 t)
    (let ((n 1))
      (while (and (< (point) indent-point)
                  (condition-case ()
                      (progn
                        (setq n (+ 1 n))
                        (forward-sexp 1)
                        (parse-partial-sexp (point) indent-point 1 t))
                    (error nil))))
      (list (cond ((= 1 n) clause-indent)
                  (t body-indent))
            containing-sexp-point))))

(defun racket--set-indentation ()
  "Set indentation for various Racket forms.

Note that `beg*`, `def*` and `with-*` aren't listed here because
`racket-indent-function' handles those.

Note that indentation is set for the symbol alone, and also with
a : suffix for legacy Typed Racket. For example both `let` and
`let:`. Although this is overzealous in the sense that Typed
Racket does not define its own variant of all of these, it
doesn't hurt to do so."
  (mapc (lambda (x)
          (put (car x) 'racket-indent-function (cadr x))
          (let ((typed (intern (format "%s:" (car x)))))
            (put typed 'racket-indent-function (cadr x))))
        '(;; begin* forms default to 0 unless otherwise specified here
          (begin0 1)
          (c-declare 0)
          (c-lambda 2)
          (call-with-input-file defun)
          (call-with-output-file defun)
          (call-with-output-file* defun)
          (case 1)
          (case-lambda 0)
          (catch 1)
          (class defun)
          (class* defun)
          (compound-unit/sig 0)
          (cond 0)
          ;; def* forms default to 'defun unless otherwise specified here
          (delay 0)
          (do 2)
          (dynamic-wind 0)
          (fn 1) ;alias for lambda (although not officially in Racket)
          (for 1)
          (for/list racket--indent-for)
          (for/vector racket--indent-for)
          (for/hash racket--indent-for)
          (for/hasheq racket--indent-for)
          (for/hasheqv racket--indent-for)
          (for/and racket--indent-for)
          (for/or racket--indent-for)
          (for/lists racket--indent-for/fold)
          (for/first racket--indent-for)
          (for/last racket--indent-for)
          (for/fold racket--indent-for/fold)
          (for/flvector racket--indent-for)
          (for/set racket--indent-for)
          (for/sum racket--indent-for)
          (for/product racket--indent-for)
          (for* 1)
          (for*/list racket--indent-for)
          (for*/vector racket--indent-for)
          (for*/hash racket--indent-for)
          (for*/hasheq racket--indent-for)
          (for*/hasheqv racket--indent-for)
          (for*/and racket--indent-for)
          (for*/or racket--indent-for)
          (for*/lists racket--indent-for/fold)
          (for*/first racket--indent-for)
          (for*/last racket--indent-for)
          (for*/fold racket--indent-for/fold)
          (for*/flvector racket--indent-for)
          (for*/set racket--indent-for)
          (for*/sum racket--indent-for)
          (for*/product racket--indent-for)
          (instantiate 2)
          (interface 1)
          (λ 1)
          (lambda 1)
          (lambda/kw 1)
          (let racket--indent-let)
          (let* 1)
          (letrec 1)
          (let-values 1)
          (let*-values 1)
          (let+ 1)
          (let-values 1)
          (let-syntax 1)
          (letrec-syntax 1)
          (let/ec 1)
          (match 1)
          (match* 1)
          (match-define defun)
          (match-let 1)
          (match-let* 1)
          (match-lambda 0)
          (match-lambda* 0)
          (mixin 2)
          (module 2)
          (module+ 1)
          (module* 2)
          (opt-lambda 1)
          (parameterize 1)
          (parameterize-break 1)
          (parameterize* 1)
          (quasisyntax/loc 1)
          (receive 2)
          (require/typed 1)
          (send* 1)
          (sigaction 1)
          (splicing-syntax-parameterize 1)
          (struct defun)
          (syntax-case 2)
          (syntax-case* 3)
          (syntax-rules 1)
          (syntax-parse 1)
          (syntax-parser 0)
          (syntax-parameterize 1)
          (syntax/loc 1)
          (syntax-parse 1)
          (unit defun)
          (unit/sig 2)
          (unless 1)
          (when 1)
          (while 1)
          ;; with- forms default to 1 unless otherwise specified here
          )))

(provide 'racket-indent)

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:

;; racket-indent.el ends here
