;; texi-docstring-magic.el --- munge internal docstrings into texi
;;
;; Keywords: lisp, docs, tex
;; Author:     David Aspinall <David.Aspinall@ed.ac.uk>
;; Copyright   (C) 1998 David Aspinall
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; texi-docstring-magic.el,v 12.1 2012/08/30 14:30:23 monnier Exp
;;
;; This file is distributed under the terms of the GNU General Public
;; License, Version 2.  Find a copy of the GPL with your version of
;; GNU Emacs or Texinfo.
;;
;;
;; This package generates Texinfo source fragments from Emacs
;; docstrings.  This avoids documenting functions and variables in
;; more than one place, and automatically adds Texinfo markup to
;; docstrings.
;;
;; It relies heavily on you following the Elisp documentation
;; conventions to produce sensible output, check the Elisp manual
;; for details.  In brief:
;;
;;  * The first line of a docstring should be a complete sentence.
;;  * Arguments to functions should be written in upper case: ARG1..ARGN
;;  * User options (variables users may want to set) should have docstrings
;;    beginning with an asterisk.
;;
;; Usage:
;;
;;  Write comments of the form:
;;
;;    @c TEXI DOCSTRING MAGIC: my-package-function-or-variable-name
;;
;;  In your texi source, mypackage.texi.  From within an Emacs session
;;  where my-package is loaded, visit mypackage.texi and run
;;  M-x texi-docstring-magic to update all of the documentation strings.
;;
;;  This will insert @defopt, @deffn and the like underneath the
;;  magic comment strings.
;;
;;  The default value for user options will be printed.
;;
;;  Symbols are recognized if they are defined for faces, functions,
;;  or variables (in that order).
;;
;; Automatic markup rules:
;;
;; 1. Indented lines are gathered into a @lisp environment.
;; 2. Pieces of text `stuff' or surrounded in quotes marked up with @samp.
;; 3. Words *emphasized* are made @strong{emphasized}
;; 4. Words sym-bol which are symbols become @code{sym-bol}.
;; 5. Upper cased words ARG corresponding to arguments become @var{arg}.
;;    In fact, you can use any word longer than three letters, so that
;;    metavariables can be used easily.
;;    FIXME: to escape this, use `ARG'
;; 6. Words 'sym which are lisp-quoted are marked with @code{'sym}.
;;
;; -----
;;
;; Useful key binding when writing Texinfo:
;;
;;  (define-key TeXinfo-mode-map "C-cC-d" 'texi-docstring-magic-insert-magic)
;;
;; -----
;;
;; Useful enhancements to do:
;;
;;  * Tweak replacement: at the moment it skips blank lines
;;    under magic comment.
;;  * Use customize properties (e.g. group, simple types)
;;  * Look for a "texi-docstring" property for symbols
;;    so TeXInfo can be defined directly in case automatic markup
;;    goes badly wrong.
;;  * Add tags to special comments so that user can specify face,
;;    function, or variable binding for a symbol in case more than
;;    one binding exists.
;;
;; ------
;;
;; Thanks to: Christoph Conrad for an Emacs compatibility fix.
;;
;;

(eval-when-compile
  (require 'cl))

(defun texi-docstring-magic-find-face (face)
  ;; Compatibility between FSF Emacs and XEmacs
  (or (facep face)
      (and (fboundp 'find-face) (find-face face))))

(defun texi-docstring-magic-splice-sep (strings sep)
  "Return concatenation of STRINGS spliced together with separator SEP."
  (let (str)
    (while strings
      (setq str (concat str (car strings)))
      (if (cdr strings)
	  (setq str (concat str sep)))
      (setq strings (cdr strings)))
    str))

(defconst texi-docstring-magic-munge-table
  '(;; 0. Escape @, { and } characters
    ("\\(@\\)" t "@@")
    ("\\({\\)" t "@{")
    ("\\(}\\)" t "@}")
    ;; 1. Indented lines are gathered into @lisp environment.
    ("^\\(\n\\|.+\\)$"
     t
     (let
	 ((line (match-string 0 docstring)))
       (if (save-match-data (string-match "^[ \t]" line))
	   ;; whitespace
	   (if in-quoted-region
	       line
	     (setq in-quoted-region t)
	     (concat "@lisp\n" line))
	 ;; non-white space/carriage return
	 (if (and in-quoted-region (not (equal line "\n")))
	     (progn
	       (setq in-quoted-region nil)
	       (concat "@end lisp\n" line))
	   line))))
    ;; 2. Pieces of text `stuff' or surrounded in quotes
    ;; are marked up with @samp.  NB: Must be backquote
    ;; followed by forward quote for this to work.
    ;; Can't use two forward quotes else problems with
    ;; symbols.
    ;; Odd hack: because ' is a word constituent in text/texinfo
    ;; mode, putting this first enables the recognition of args
    ;; and symbols put inside quotes.
    ("\\(`\\([^']+\\)'\\)"
     t
     (concat "@samp{" (match-string 2 docstring) "}"))
    ;; 3. Words *emphasized* are made @strong{emphasized}
    ("\\(\\*\\(\\w+\\)\\*\\)"
     t
     (concat "@strong{" (match-string 2 docstring) "}"))
    ;; 4. Words sym-bol which are symbols become @code{sym-bol}.
    ;; Must have at least one hyphen to be recognized,
    ;; terminated in whitespace, end of line, or punctuation.
    ;; Only consider symbols made from word constituents
    ;; and hyphen.
    ("\\(\\(\\w+\\-\\(\\w\\|\\-\\)+\\)\\)\\(\\s\)\\|\\s-\\|\\s.\\|$\\)"
     (or (boundp (intern (match-string 2 docstring)))
	 (fboundp (intern (match-string 2 docstring))))
     (concat "@code{" (match-string 2 docstring) "}"
	     (match-string 4 docstring)))
    ;; 5. Upper cased words ARG corresponding to arguments become
    ;; @var{arg}
    ;; In fact, include any word so long as it is more than 3 characters
    ;; long.  (Comes after symbols to avoid recognizing the
    ;; lowercased form of an argument as a symbol)
    ;; FIXME: maybe we don't want to downcase stuff already
    ;; inside @samp
    ;; FIXME: should - terminate?  should _ be included?
    ("\\([A-Z0-9_\\-]+\\)\\(/\\|\)\\|}\\|\\s-\\|\\s.\\|$\\)"
     (or (> (length (match-string 1 docstring)) 3)
	 (member (downcase (match-string 1 docstring)) args))
     (concat "@var{" (downcase (match-string 1 docstring)) "}"
	     (match-string 2 docstring)))

    ;; 6. Words 'sym which are lisp quoted are
    ;; marked with @code.
    ("\\(\\(\\s-\\|^\\)'\\(\\(\\w\\|\\-\\)+\\)\\)\\(\\s\)\\|\\s-\\|\\s.\\|$\\)"
     t
     (concat (match-string 2 docstring)
	     "@code{'" (match-string 3 docstring) "}"
	     (match-string 5 docstring)))
    ;; 7,8. Clean up for @lisp environments left with spurious newlines
    ;; after 1.
    ("\\(\\(^\\s-*$\\)\n@lisp\\)" t "@lisp")
    ("\\(\\(^\\s-*$\\)\n@end lisp\\)" t "@end lisp")
    ;; 9. Hack to remove @samp{@var{...}} sequences.
    ;; Changed to just @samp of uppercase.
    ("\\(@samp{@var{\\([^}]+\\)}}\\)"
     t
     (concat "@samp{" (upcase (match-string 2 docstring)) "}")))
    "Table of regexp matches and replacements used to markup docstrings.
Format of table is a list of elements of the form
   (regexp predicate replacement-form)
If regexp matches and predicate holds, then replacement-form is
evaluated to get the replacement for the match.
predicate and replacement-form can use variables arg,
and forms such as (match-string 1 docstring)
Match string 1 is assumed to determine the
length of the matched item, hence where parsing restarts from.
The replacement must cover the whole match (match string 0),
including any whitespace included to delimit matches.")


(defun texi-docstring-magic-untabify (string)
  "Convert tabs in STRING into multiple spaces."
  (with-temp-buffer 
    (insert string)
    (untabify (point-min) (point-max))
    (buffer-string)))

(defun texi-docstring-magic-munge-docstring (docstring args)
  "Markup DOCSTRING for texi according to regexp matches."
  (let ((case-fold-search nil))
    (setq docstring (texi-docstring-magic-untabify docstring))
    (dolist (test texi-docstring-magic-munge-table)
      (let ((regexp	(nth 0 test))
	    (predicate  (nth 1 test))
	    (replace    (nth 2 test))
	    (i		0)
	    in-quoted-region)

	(while (and
		(< i (length docstring))
		(string-match regexp docstring i))
	  (setq i (match-end 1))
	  (if (eval predicate)
	      (let* ((origlength  (- (match-end 0) (match-beginning 0)))
		     (replacement (eval replace))
		     (newlength   (length replacement)))
		(setq docstring
		      (replace-match replacement t t docstring))
		(setq i (+ i (- newlength origlength))))))
	(if in-quoted-region
	    (setq docstring (concat docstring "\n@end lisp"))))))
  ;; Force a new line after (what should be) the first sentence,
  ;; if not already a new paragraph.
  (let*
      ((pos      (string-match "\n" docstring))
       (needscr  (and pos
		      (not (string= "\n"
				    (substring docstring
					       (1+ pos)
					       (+ pos 2)))))))
    (if (and pos needscr)
	(concat (substring docstring 0 pos)
		"@*\n"
		(substring docstring (1+ pos)))
      docstring)))

(defun texi-docstring-magic-texi (env grp name docstring args &optional endtext)
  "Make a texi def environment ENV for entity NAME with DOCSTRING."
  (concat "@def" env (if grp (concat " " grp) "") " " name
	  " "
	  (texi-docstring-magic-splice-sep args " ")
	  ;; " "
	  ;; (texi-docstring-magic-splice-sep extras " ")
	  "\n"
	  (texi-docstring-magic-munge-docstring docstring args)
	  "\n"
	  (or endtext "")
	  "@end def" env "\n"))

(defun texi-docstring-magic-format-default (default)
  "Make a default value string for the value DEFAULT.
Markup as @code{stuff} or @lisp stuff @end lisp."
  ;; NB: might be nice to use a 'default-value-description
  ;; property here, in case the default value is computed.
  (let ((text       (format "%S" default)))
    (concat
     "\nThe default value is "
     (if (string-match "\n" text)
	 ;; Carriage return will break @code, use @lisp
	 (if (stringp default)
	     (concat "the string: \n@lisp\n" default "\n@end lisp\n")
	   (concat "the value: \n@lisp\n" text "\n@end lisp\n"))
       (concat "@code{" text "}.\n")))))


(defun texi-docstring-magic-texi-for (symbol &optional noerror)
  (cond
   ;; Faces
   ((texi-docstring-magic-find-face symbol)
    (let*
	((face	    symbol)
	 (name      (symbol-name face))
	 (docstring (or (face-doc-string face)
			"Not documented."))
	 (useropt   (eq ?* (string-to-char docstring))))
      ;; Chop off user option setting
      (if useropt
	  (setq docstring (substring docstring 1)))
      (texi-docstring-magic-texi "fn" "Face" name docstring nil)))
   ((boundp symbol)
    ;; Variables.
    (let*
	((variable  symbol)
	 (name      (symbol-name variable))
	 (docstring (or (documentation-property variable
						'variable-documentation)
			"Not documented."))
	 (useropt   (eq ?* (string-to-char docstring)))
	 (default   (if useropt
			(texi-docstring-magic-format-default
			 (default-value symbol)))))
      ;; Chop off user option setting
      (if useropt
	  (setq docstring (substring docstring 1)))
      (texi-docstring-magic-texi
       (if useropt "opt" "var") nil name docstring nil default)))
   ((fboundp symbol)
    ;; Functions.  Functions with same name as variables are documented
    ;; as variables.
    ;; We don't handle macros,  aliases, or compiled fns properly.
    (let*
	((function  symbol)
	 (name	    (symbol-name function))
	 (docstring (or (documentation function)
			"Not documented."))
	 (def	    (symbol-function function))
	 (macrop    (eq 'macro (car-safe def)))
	 (argsyms   (cond ((eq (car-safe def) 'lambda)
			   (nth 1 def))))
	 (args	    (mapcar 'symbol-name argsyms)))
      (cond
       ((commandp function)
	(texi-docstring-magic-texi "fn" "Command" name docstring args))
       (macrop
	(texi-docstring-magic-texi "fn" "Macro" name docstring args))
       (t
	(texi-docstring-magic-texi "un" nil name docstring args)))))
   (noerror
    (message "Warning: symbol `%s' not defined" (symbol-name symbol))
    "")
   (t
    (error "Don't know anything about symbol %s" (symbol-name symbol)))))

(defconst texi-docstring-magic-comment
  "@c TEXI DOCSTRING MAGIC:"
  "Magic string in a texi buffer expanded into @defopt, or @deffn.")


;;;###autoload
(defun texi-docstring-magic (&optional noerror)
  "Update all texi docstring magic annotations in buffer.
With prefix arg, no errors on unknown symbols.  (This results in
@def .. @end being deleted if not known)."
  (interactive "P")
  (save-excursion
    (goto-char (point-min))
    (let ((magic (concat "^"
			 (regexp-quote texi-docstring-magic-comment)
			 "\\s-*\\(\\(\\w\\|\\-\\)+\\)[ \t]*$"))
	  p
	  symbol
	  deleted)
      (while (re-search-forward magic nil t)
	(setq symbol (intern (match-string 1)))
	(forward-line)
	(setq p (point))
	;; delete any whitespace following magic comment
	(skip-chars-forward " \n\t")
	(delete-region p (point))
	;; If comment already followed by an environment, delete it.
	(if (and
	     (looking-at "@def\\(\\w+\\)\\s-")
	     (search-forward (concat "@end def" (match-string 1)) nil t))
	    (progn
	      (forward-line)
	      (delete-region p (point))
	      (setq deleted t)))
	(insert
	 (texi-docstring-magic-texi-for symbol noerror))
	(unless deleted
	  ;; Follow newly inserted @def with a single blank.
	  (insert "\n"))))))

(defun texi-docstring-magic-face-at-point ()
  (ignore-errors
    (let ((stab (syntax-table)))
      (unwind-protect
	  (save-excursion
	    (set-syntax-table emacs-lisp-mode-syntax-table)
	    (or (not (zerop (skip-syntax-backward "_w")))
		(eq (char-syntax (char-after (point))) ?w)
		(eq (char-syntax (char-after (point))) ?_)
		(forward-sexp -1))
	    (skip-chars-forward "'")
	    (let ((obj (read (current-buffer))))
	      (and (symbolp obj) (texi-docstring-magic-find-face obj) obj)))
	(set-syntax-table stab)))))

(defun texi-docstring-magic-insert-magic (symbol)
  (interactive
   (let* ((v (or (variable-at-point)
		 (and (fboundp 'function-at-point) (function-at-point))
		 (and (fboundp 'function-called-at-point) (function-called-at-point))
		 (texi-docstring-magic-face-at-point)))
	  (val (let ((enable-recursive-minibuffers t))
		 (completing-read
		  (if v
		      (format "Magic docstring for symbol (default %s): " v)
		     "Magic docstring for symbol: ")
		   obarray (lambda (sym)
                             (or (boundp sym)
                                 (fboundp sym)
                                 (texi-docstring-magic-find-face sym)))
		   t nil 'variable-history))))
     (list (if (equal val "") v (intern val)))))
  (insert "\n" texi-docstring-magic-comment " " (symbol-name symbol)))


(provide 'texi-docstring-magic)
