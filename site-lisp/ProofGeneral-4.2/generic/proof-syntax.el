;; proof-syntax.el --- Functions for dealing with syntax
;;
;; Copyright (C) 1997-2001, 2010 LFCS Edinburgh.
;; Authors:   David Aspinall, Healfdene Goguen,
;;	      Thomas Kleymann, Dilip Sequiera
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; proof-syntax.el,v 12.0 2011/10/13 10:54:49 da Exp
;;

(require 'font-lock)
(require 'proof-config)			; proof-case-fold-search
(require 'proof-compat)			; proof-buffer-syntactic-context
(require 'pg-pamacs)			; proof-ass-sym


;;; Commentary:
;; 

;;; Code:

(defsubst proof-ids-to-regexp (l)
  "Maps a non-empty list of tokens L to a regexp matching any element.
Uses a regexp of the form \\_<...\\_>."
  (concat "\\_<\\(?:"
	  (regexp-opt l) ; was: (mapconcat 'identity l "\\|")
	  "\\)\\_>"))

(defsubst proof-anchor-regexp (e)
  "Anchor (\\`) and group the regexp E."
  (concat "\\`\\(" e "\\)"))

(defconst proof-no-regexp "\\<\\>"
  "A regular expression that never matches anything.")

(defsubst proof-regexp-alt (&rest args)
  "Return the regexp which matches any of the regexps ARGS."
  ;; see regexp-opt (NB: but that is for strings, not regexps)
  (let ((res ""))
    (dolist (regexp args)
      (setq res (concat res (if (string-equal res "") "\\(?:" "\\|\\(?:")
			regexp "\\)")))
    res))

(defsubst proof-regexp-alt-list (args)
  "Return the regexp which matches any of the regexps ARGS."
  (apply 'proof-regexp-alt args))

(defsubst proof-re-search-forward-region (startre endre)
  "Search for a region delimited by regexps STARTRE and ENDRE.
Return the start position of the match for STARTRE, or
nil if a region cannot be found."
  (if (re-search-forward startre nil t)
      (let ((start (match-beginning 0)))
	(if (re-search-forward endre nil t)
	    start))))

;; Functions for string matching and searching that take into account
;; value of proof-case-fold-search.  Last arg to string-match is not
;; applicable.

(defsubst proof-search-forward (string &optional bound noerror count)
  "Like search-forward, but set case-fold-search to proof-case-fold-search."
  (let
      ((case-fold-search proof-case-fold-search))
    (search-forward string bound noerror count)))

;;;###autoload
(defsubst proof-replace-regexp-in-string (regexp rep string)
  "Like replace-regexp-in-string, but set case-fold-search to proof-case-fold-search."
  (let ((case-fold-search proof-case-fold-search))
    (replace-regexp-in-string regexp rep string)))

(defsubst proof-re-search-forward (regexp &optional bound noerror count)
  "Like re-search-forward, but set case-fold-search to proof-case-fold-search."
  (let ((case-fold-search proof-case-fold-search))
    (re-search-forward regexp bound noerror count)))

(defsubst proof-re-search-backward (regexp &optional bound noerror count)
  "Like re-search-backward, but set case-fold-search to proof-case-fold-search."
  (let ((case-fold-search proof-case-fold-search))
    (re-search-backward regexp bound noerror count)))

(defsubst proof-re-search-forward-safe (regexp &optional bound noerror count)
  "Like re-search-forward, but set case-fold-search to proof-case-fold-search."
  (and regexp
       (let ((case-fold-search proof-case-fold-search))
	 (re-search-forward regexp bound noerror count))))

(defsubst proof-string-match (regexp string &optional start)
  "Like string-match, but set case-fold-search to proof-case-fold-search."
  (let ((case-fold-search proof-case-fold-search))
    (string-match regexp string start)))

(defsubst proof-string-match-safe (regexp string &optional start)
  "Like `string-match', but return nil if REGEXP or STRING is nil."
  (if (and regexp string) (proof-string-match regexp string start)))

(defsubst proof-stringfn-match (regexp-or-fn string)
  "Like proof-string-match if first arg is regexp, otherwise call it."
  (cond ((stringp regexp-or-fn)
	 (proof-string-match regexp-or-fn string))
	((functionp regexp-or-fn)
	 (funcall regexp-or-fn string))))

(defsubst proof-looking-at (regexp)
  "Like looking-at, but set case-fold-search to proof-case-fold-search."
  (let ((case-fold-search proof-case-fold-search))
    (looking-at regexp)))

(defsubst proof-looking-at-safe (regexp)
  "Like `proof-looking-at', but return nil if REGEXP is nil."
  (if regexp (proof-looking-at regexp)))

;;
;; Syntactic context
;;

;; A function named after one in XEmacs
(defun proof-buffer-syntactic-context (&optional buffer)
  "Return the syntactic context of BUFFER at point.
If BUFFER is nil or omitted, the current buffer is assumed.
The returned value is one of the following symbols:

	nil		; meaning no special interpretation
	string		; meaning point is within a string
	comment		; meaning point is within a line comment"
  (save-excursion
    (if buffer (set-buffer buffer))
    (let ((pp (syntax-ppss)))
	   ;;(parse-partial-sexp (point-min) (point))))
      (cond
       ((nth 3 pp) 'string)
       ;; ((nth 7 pp) 'block-comment)
       ;; "Stefan Monnier" <monnier+misc/news@rum.cs.yale.edu> suggests
       ;; distinguishing between block comments and ordinary comments
       ;; is problematic: not what XEmacs claims and different to what
       ;; (nth 7 pp) tells us in GNU Emacs.
       ((nth 4 pp) 'comment)))))

(defsubst proof-looking-at-syntactic-context-default ()
  "Default function for `proof-looking-at-syntactic-context'."
  (or
   (proof-buffer-syntactic-context)
   (save-match-data
     (when (proof-looking-at-safe proof-script-comment-start-regexp) 'comment))
   (save-match-data
     (when (proof-looking-at-safe proof-string-start-regexp) 'string))))

(defun proof-looking-at-syntactic-context ()
  "Determine if current point is at beginning or within comment/string context.
If so, return a symbol indicating this ('comment or 'string).
This function invokes <PA-syntactic-context> if that is defined, otherwise
it calls `proof-looking-at-syntactic-context'."
  (if (fboundp (proof-ass-sym syntactic-context))
      (funcall (proof-ass-sym syntactic-context))
    (proof-looking-at-syntactic-context-default)))

(defun proof-inside-comment (pos)
  "Return non-nil if POS is inside a comment."
  (save-excursion
    (goto-char pos)
    (eq (proof-buffer-syntactic-context) 'comment)))

(defun proof-inside-string (pos)
  "Return non-nil if POS is inside a comment."
  (save-excursion
    (goto-char pos)
    (eq (proof-buffer-syntactic-context) 'string)))

;;
;; Replacing matches
;;

(defsubst proof-replace-string (string to-string)
  "Non-interactive `replace-string', using `proof-case-fold-search'."
  (while (proof-search-forward string nil t)
    (replace-match to-string nil t)))

(defsubst proof-replace-regexp (regexp to-string)
  "Non-interactive `replace-regexp', using `proof-case-fold-search'."
  (while (proof-re-search-forward regexp nil t)
    (replace-match to-string nil nil)))

(defsubst proof-replace-regexp-nocasefold (regexp to-string)
  "Non-interactive `replace-regexp', forcing `case-fold-search' to nil."
  (let ((case-fold-search nil))
    (while (proof-re-search-forward regexp nil t)
      (replace-match to-string nil nil))))

;;
;; Generic font-lock
;;

(defvar proof-id "\\(\\w\\(\\w\\|\\s_\\)*\\)"
  "A regular expression for parsing identifiers.")

;; For font-lock, we treat ,-separated identifiers as one identifier
;; and refontify commata using \{proof-zap-commas}.

(defsubst proof-ids (proof-id &optional sepregexp)
  "Generate a regular expression for separated lists of identifiers.
Default is comma separated, or SEPREGEXP if set."
  (concat proof-id "\\(\\s-*"   (or sepregexp ",") "\\s-*"
	  proof-id "\\)*"))


(defun proof-zap-commas (limit)
  "Remove the face of all `,' from point to LIMIT.
Meant to be used from `font-lock-keywords' as a way
to unfontify commas in declarations and definitions.
Useful for provers which have declarations of the form x,y,z:Ty
All that can be said for it is that the previous ways of doing
this were even more bogus...."
(while (proof-search-forward "," limit t)
    (if (memq (get-text-property (1- (point)) 'face)
	      '(proof-declaration-name-face
		font-lock-variable-name-face
		font-lock-function-name-face))
	(put-text-property (1- (point)) (point) 'face nil))))


;;
;; Font lock: providing an alternative syntactic fontify
;; region function.
;; 
;; The hook font-lock-fontify-region-function is tempting but not
;; really a convenient place.  We just want to replace the syntactic
;; fontification function.
;;

(eval-after-load "font-lock"
'(progn
(defadvice font-lock-fontify-keywords-region
  (before font-lock-fontify-keywords-advice (beg end loudly))
  "Call proof assistant specific syntactic region fontify.
If it's bound, we call <PA>-font-lock-fontify-syntactically-region."
  (when (and proof-buffer-type
	     (fboundp (proof-ass-sym font-lock-fontify-syntactically-region)))
    (funcall (proof-ass-sym font-lock-fontify-syntactically-region)
	     beg end loudly)))
(ad-activate 'font-lock-fontify-keywords-region)))

;;
;; Functions for doing something like "format" but with customizable
;; control characters.
;;

;;;###autoload
(defun proof-format (alist string)
  "Format a string by matching regexps in ALIST against STRING.
ALIST contains (REGEXP . REPLACEMENT) pairs where REPLACEMENT
may be a string or sexp evaluated to get a string."
  (while alist
    (let ((idx 0))
      (while (string-match (car (car alist)) string idx)
	(setq string
	      (concat (substring string 0 (match-beginning 0))
		      (cond
		       ((stringp (cdr (car alist)))
			(cdr (car alist)))
		       (t
			(eval (cdr (car alist)))))
		      (substring string (match-end 0))))
	(setq idx (+ (match-beginning 0) (length (cdr (car alist)))))))
    (setq alist (cdr alist)))
  string)

(defun proof-format-filename (string filename)
  "Format STRING by replacing quoted chars by escaped version of FILENAME.

%e uses the canonicalized expanded version of filename (including
directory, using `default-directory' -- see `expand-file-name').

%r uses the unadjusted (possibly relative) version of FILENAME.

%m ('module') uses the basename of the file, without directory
or extension.

%s means the same as %e.

Using %e can avoid problems with dumb proof assistants who don't
understand ~, for example.

For all these cases, the escapes in `proof-shell-filename-escapes'
are processed.

If STRING is in fact a function, instead invoke it on FILENAME and
return the resulting (string) value."
  (cond
   ((functionp string)
    (funcall string filename))
   (t
    (proof-format
     (list (cons "%s" (proof-format proof-shell-filename-escapes
				    (expand-file-name filename)))
	   (cons "%e" (proof-format proof-shell-filename-escapes
				    (expand-file-name filename)))
	   (cons "%r" (proof-format proof-shell-filename-escapes
				    filename))
	   (cons "%m" (proof-format proof-shell-filename-escapes
				    (file-name-nondirectory
				     (file-name-sans-extension filename)))))
     string))))


;;
;; Functions for inserting text into buffer.
;;

; Taken from Isamode
;
;  %l  - insert the value of isa-logic-name
;  %s  - insert the value returned by isa-current-subgoal

(defun proof-insert (text)
  "Insert TEXT into the current buffer.
TEXT may include these special characters:
  %p  - place the point here after input
Any other %-prefixed character inserts itself."
  ; would be quite nice to have this function:
  ;(isa-delete-pending-input)
  (let ((i 0) pos acc)
    (while (< i (length text))
      (let ((ch (elt text i)))
	(if (not (eq ch ?%))
	    (setq acc (concat acc (char-to-string ch)))
	  (setq i (1+ i))
	  (setq ch (elt text i))
	  (cond ;((eq ch ?l)
		; (setq acc (concat acc isa-logic-name)))
		;((eq ch ?s)
		; (setq acc
		;       (concat acc
		;	       (int-to-string
		;		(if (boundp 'isa-denoted-subgoal)
		;		    isa-denoted-subgoal
		;		  1)))))
		;((eq ch ?n)
		; (if acc (insert acc))
		; (setq acc nil)
		; (scomint-send-input))
		((eq ch ?p)
		 (if acc (insert acc))
		 (setq acc nil)
		 (setq pos (point)))
		(t (setq acc (concat acc (char-to-string ch)))))))
      (setq i (1+ i)))
    (if acc (insert acc))
    (if pos (goto-char pos))))

(provide 'proof-syntax)

;;; proof-syntax.el ends here
