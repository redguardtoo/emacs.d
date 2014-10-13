;;; unicode-tokens.el --- Support for control and symbol tokens
;;
;; Copyright(C) 2008-2010 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; unicode-tokens.el,v 12.3 2012/09/04 20:57:54 da Exp
;;
;; This is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;;
;; This is a replacement for X-Symbol for Proof General.
;;
;; Functions to display tokens that represent Unicode characters and
;; control code sequences for changing the layout.  Tokens are useful
;; for programs that do not understand a Unicode encoding.
;;

;; Desirable improvements/enhancements
;;
;; -- insert tokens via numeric code (extra format string), cf HTML
;; -- simplify: unify region and control settings?
;; -- simplify/optimise property handling
;; -- support multiple modes with mode-local configs at once

;;
;;; Code:
;;

(require 'cl)
(require 'quail)

(eval-when-compile
  (require 'maths-menu)		; nuke compile warnings
  ;; Emacs <24 compatibility
  (when (and (fboundp 'flet)
	     (not (get 'flet 'byte-obsolete-info)))
    (defalias 'cl-flet 'flet)))

;;
;; Customizable user options
;;

(defgroup unicode-tokens-options nil
  "User options for Unicode Tokens mode."
  :group 'faces
  :prefix "unicode-tokens-")

(defcustom unicode-tokens-add-help-echo t
  "If non-nil, add mouse hover (or minibuffer messages) to show tokens."
  :type 'boolean
  :group 'unicode-tokens-options)

(defun unicode-tokens-toggle-add-help-echo ()
  (interactive)
  (customize-set-variable 'unicode-tokens-add-help-echo
			  (not unicode-tokens-add-help-echo))
  ;; NB: approximate, should refontify all...
  (font-lock-fontify-buffer))

;;
;; Variables that should be set by client modes
;;
;; Each variable may be set directly or indirectly; see
;; `unicode-tokens-copy-configuration-variables' below.
;;

(defvar unicode-tokens-token-symbol-map nil
  "Mapping of token names to compositions.
A list, each element of which is a list

  (TOKNAME COMPOSITION FONTSYMB ...)

A composition is typically a single Unicode character string, but
can be more complex: see documentation of `compose-region'.

TOKNAMEs may be repeated.  The first one with a usable
composition according to `unicode-tokens-usable-composition',
if any.

The sequence of FONTSYMB are optional.  Each FONTSYMB is a symbol
indicating a set of additional text properties, looked up in
`unicode-tokens-fontsymb-properties'.

By default, tokens are displayed in `unicode-tokens-symbol-font-face'.")

(defvar unicode-tokens-token-format "%s"
  "Format string for formatting token a name into a token.
Will be regexp quoted for matching.  Not used for matching if
`unicode-tokens-token-variant-format-regexp' is set.
Also used to format shortcuts.")

(defvar unicode-tokens-token-variant-format-regexp nil
  "A regular expression which matches a token variant.
Will not be regexp quoted, and will be formatted with
a nested regexp that matches any token.

An example would be: \\\\(%s\\\\)\\\\(:?\\w+\\\\)

which matches plain token strings optionally followed by a colon
and variant name.  Once set, (match-string 1) should be
the name of the token whereas (match-string 0) matches
the longer text, if any.

If set, this variable is used instead of `unicode-tokens-token-format'.")

(defvar unicode-tokens-shortcut-alist nil
  "An alist of keyboard shortcuts to unicode strings.
The alist is added to the input mode for tokens.
The shortcuts are only used for input convenience; no reverse
mapping back to shortucts is performed.  Behaviour is like abbrev.")

(defvar unicode-tokens-shortcut-replacement-alist nil
  "Overrides `unicode-tokens-shortcut-alist' for `unicode-tokens-replace-shortcuts'.")


;;
;; Variables that may optionally be set in client modes
;;

(defvar unicode-tokens-control-region-format-regexp nil
  "A regexp for control regions, with up to two %s placeholders.
When fomatted with arguments START END, results in a regexp
that matches a control region.  There should be three delimited
subexpressions: (match-string 1) and (match-string 3) are hidden,
and (match-string 2) has the display control applied.")

(defvar unicode-tokens-control-char-format-regexp nil
  "A format string for control characters, possibly with a %s placeholder.
When fomatted with arguments STRING, results in a regexp
that matches a control character sequence.   There should be two
delimited subexpressions: (match-string 1) is hidden
and (match-string 2) has the display control applied.")

(defvar unicode-tokens-control-regions nil
  "A list of control regions.")

(defvar unicode-tokens-control-characters nil
  "A list of control characters.")

(defvar unicode-tokens-control-char-format nil
  "A format string for inserting a control character sequence.")

(defvar unicode-tokens-control-region-format-start nil
  "A format string for begining a control region sequence.")

(defvar unicode-tokens-control-region-format-end nil
  "A format string for ending a control region sequence.")

(defvar unicode-tokens-tokens-customizable-variables nil
  "A list of lists (NAME VAR) of variables for a customize submenu.")

;;
;; A list of the above variables
;;

(defconst unicode-tokens-configuration-variables
  '(token-symbol-map
    token-format
    token-variant-format-regexp
    shortcut-alist
    shortcut-replacement-alist
    control-region-format-regexp
    control-region-format-start
    control-region-format-end
    control-char-format-regexp
    control-char-format
    control-regions
    control-characters
    tokens-customizable-variables))

(defun unicode-tokens-config (sym)
  "Construct the symbol name `unicode-tokens-SYM'."
  (intern (concat "unicode-tokens-" (symbol-name sym))))

(defun unicode-tokens-config-var (sym)
  "Construct the symbol name `unicode-tokens-SYM-variable'."
  (intern (concat "unicode-tokens-" (symbol-name sym) "-variable")))

(dolist (sym unicode-tokens-configuration-variables)
 (lambda (sym)
   (eval `(defvar ,(unicode-tokens-config-var sym)
	   nil
	   ,(format
	     "Name of a variable used to configure %s.\nValue should be a symbol."
	     (symbol-name (unicode-tokens-config sym)))))))

(defun unicode-tokens-copy-configuration-variables ()
  "Initialise the configuration variables by copying from variable names.
Each configuration variable may be set directly or indirectly by client;
modes an indirect setting is made by this function from a variable named
<setting>-variable, e.g., `unicode-tokens-token-symbol-map'
will be initialised from `unicode-tokens-token-symbol-map-variable',
if it is bound; it should be the name of a variable."
  (dolist (sym unicode-tokens-configuration-variables)
    (let ((var (unicode-tokens-config-var sym)))
      (if (and (boundp var) (not (null (symbol-value var))))
	  (set (unicode-tokens-config sym)
	       (symbol-value (symbol-value
			      (unicode-tokens-config-var sym)))))))
  (unless unicode-tokens-shortcut-replacement-alist
    (setq unicode-tokens-shortcut-replacement-alist
	  unicode-tokens-shortcut-alist))
  (unless unicode-tokens-tokens-customizable-variables
    (setq unicode-tokens-tokens-customizable-variables
	  (list
	   (list "Token Map"
		 (symbol-value (unicode-tokens-config-var 'token-symbol-map)))
	   (list "Shortcut List"
		 (symbol-value (unicode-tokens-config-var 'shortcut-alist)))))))

;;
;; Variables set in the mode
;;

(defvar unicode-tokens-token-list nil
  "List of usable token names in order from `unicode-tokens-token-symbol-map'.")

(defvar unicode-tokens-hash-table nil
  "Hash table mapping token names (strings) to composition and properties.")

(defvar unicode-tokens-token-match-regexp nil
  "Regular expression used by font-lock to match known tokens.
The match should span the whole token; (match-string 1) should
span the token name, if that is shorter.
The value is calculated by `unicode-tokens-calculate-token-match'.")

(defvar unicode-tokens-uchar-hash-table nil
  "Hash table mapping unicode strings to symbolic token names.
This is used for an approximate reverse mapping, see `unicode-tokens-paste'.")

(defvar unicode-tokens-uchar-regexp nil
  "Regular expression matching converted tokens.
This is used for an approximate reverse mapping, see `unicode-tokens-paste'.")

;;
;; Faces
;;

(defgroup unicode-tokens-faces nil
  "The faces used in Unicode Tokens mode."
  :group 'faces)

;;
;; This is a fallback for when fontconfig is not used/available.
;;
;; NB: even with fontconfig, name aliasing has undesirable effects
;; (e.g., can end up with version of font without anti-aliasing)
;;
(defconst unicode-tokens-font-family-alternatives
  '(("STIXGeneral"
     "DejaVu Sans Mono" "DejaVuLGC Sans Mono" 
     "Lucida Grande" "Lucida Sans Unicode" "Apple Symbols")
    ("Script"
     "Lucida Calligraphy" "URW Chancery L" "Zapf Chancery")
    ("Fraktur"
     "Lucida Blackletter" "Isabella" "URW Bookman L")))

(if (boundp 'face-font-family-alternatives)
    (custom-set-default
     'face-font-family-alternatives
     (append face-font-family-alternatives
	     unicode-tokens-font-family-alternatives)))

(defface unicode-tokens-symbol-font-face
 '((t :family "STIXGeneral"))      ;; best, but needs installation/config
;  '((t :family "DejaVu Sans Mono")) ;; more reliable default on Ubuntu
  "The default font used for symbols.  Only :family and :slant attributes are used."
  :group 'unicode-tokens-faces)

;; (defface unicode-tokens-large-symbol-font-face
;;    '((t :family "STIXSizeThreeSym"))
;;    "The font used for large symbols."
;;    :group 'unicode-tokens-faces)

(defface unicode-tokens-script-font-face
  '((t :family "URW Chancery L" :slant italic))
  "Script font face."
  :group 'unicode-tokens-faces)

(defface unicode-tokens-fraktur-font-face
  '((t :family "Fraktur"))
  "Fraktur font face."
  :group 'unicode-tokens-faces)

(defface unicode-tokens-serif-font-face
  '((t :family "Times New Roman"))
  "Serif (roman) font face."
  :group 'unicode-tokens-faces)

(defface unicode-tokens-sans-font-face
  '((t :family "Sans"))
  "Sans serif font face."
  :group 'unicode-tokens-faces)

(defface unicode-tokens-highlight-face
  '((((min-colors 88) (background dark))
     (:background "yellow1" :foreground "black"))
    (((background dark)) (:background "yellow" :foreground "black"))
    (((min-colors 88)) (:background "yellow1"))
    (t (:background "yellow")))
  "Face used for highlighting in Unicode tokens."
  :group 'unicode-tokens-faces)

(defconst unicode-tokens-fonts
  '(symbol script fraktur serif sans) ; large-symbol
  "A list of the faces used for setting fonts for Unicode Tokens.")


;;
;; Standard text properties used to build fontification
;;

(defconst unicode-tokens-fontsymb-properties
  '((sub	  "Lower"	  (display (raise -0.4)))
    (sup	  "Raise"	  (display (raise 0.4)))
    (bold	  "Bold"	  (face (:weight bold)))
    (italic	  "Italic"	  (face (:slant italic)))
    (big	  "Bigger"	  (face (:height 1.5)))
    (small	  "Smaller"	  (face (:height 0.75)))
    (underline	  "Underline"	  (face (:underline t)))
    (overline	  "Overline"	  (face (:overline t)))
    ;; NB: symbols for fonts need to be as in unicode-tokens-fonts
    (script	  "Script font"   (face unicode-tokens-script-font-face))
    (frakt	  "Frakt font"    (face unicode-tokens-fraktur-font-face))
    (serif	  "Serif font"    (face unicode-tokens-serif-font-face))
    (sans	  "Sans font"     (face unicode-tokens-sans-font-face))
;    (large-symbol "Large Symbol font"
;		  (face unicode-tokens-large-symbol-font-face))
    (keyword      "Keyword face"       (face font-lock-keyword-face))
    (function	  "Function name face" (face font-lock-function-name-face))
    (type         "Type face"          (face font-lock-type-face))
    (preprocessor "Preprocessor face"  (face font-lock-preprocessor-face))
    (doc	  "Documentation face" (face font-lock-preprocessor-face))
    (builtin	  "Builtin face"       (face font-lock-builtin-face))
    (tacticals    "Tacticals face"     (face proof-tacticals-name-face)))
 "Association list mapping a symbol to a name and list of text properties.
Used in `unicode-tokens-token-symbol-map', `unicode-tokens-control-regions',
and `unicode-tokens-control-characters'.
Several symbols can be used at once, in `unicode-tokens-token-symbol-map'.")

(define-widget 'unicode-tokens-token-symbol-map 'lazy
  "Type for customize variables used to set `unicode-tokens-token-symbol-map'."
  :offset 4
  :tag "Token symbol map"
  :type
  ;; TODO: improve this so customize editing is more pleasant.
  (list 'repeat :tag "Map entries"
	(append
	 '(list :tag "Mapping"
		(string :tag "Token name")
		(sexp :tag "Composition"))
	 (list (append
		'(set :tag "Text property styles"  :inline t)
		(mapcar (lambda (fsp)
			  (list 'const :tag
				(cadr fsp) (car fsp)))
			unicode-tokens-fontsymb-properties))))))

(define-widget 'unicode-tokens-shortcut-alist 'lazy
  "Type for customize variables used to set `unicode-tokens-shortcut-alist'."
  :offset 4
  :tag "Shortcut list"
  :type '(repeat :tag "Shortcut list"
		 (cons (string :tag "Shortcut sequence")
		       (string :tag "Buffer string"))))


;;
;; Calculating font-lock-keywords
;;

(defconst unicode-tokens-font-lock-extra-managed-props
  '(composition help-echo display invisible)
  "Value for `font-lock-extra-managed-props' here.")

(defun unicode-tokens-font-lock-keywords ()
  "Calculate and return value for `font-lock-keywords'.
This function also initialises the important tables for the mode."
  ;; Credit to Stefan Monnier for much slimmer original version
  (let ((hash       (make-hash-table :test 'equal))
	(ucharhash  (make-hash-table :test 'equal))
	toks uchars)
     (dolist (x   unicode-tokens-token-symbol-map)
       (let ((tok  (car x))
	     (comp (cadr x)))
	 (when (unicode-tokens-usable-composition comp)
	   (unless (gethash tok hash)
	     (puthash tok (cdr x) hash)
	     (push tok toks)
	     (if (stringp comp) ;; reverse map only for string comps
		 (unless (or (gethash comp ucharhash)
			     ;; ignore plain chars for reverse map
			     (string-match "[a-zA-Z0-9]+" comp))
		   (push comp uchars)
		   (puthash comp tok ucharhash)))))))
     (when toks
       (setq unicode-tokens-hash-table hash)
       (setq unicode-tokens-uchar-hash-table ucharhash)
       (setq unicode-tokens-uchar-regexp (regexp-opt uchars))
       (setq unicode-tokens-token-match-regexp
	     (unicode-tokens-calculate-token-match toks))
       (setq unicode-tokens-token-list (nreverse toks))
       (cons
	`(,unicode-tokens-token-match-regexp
	  (0 (unicode-tokens-help-echo) prepend)
	  (0 (unicode-tokens-font-lock-compose-symbol 1) prepend))
	(unicode-tokens-control-font-lock-keywords)))))

(defun unicode-tokens-calculate-token-match (toks)
  "Calculate value for `unicode-tokens-token-match-regexp'."
;  (with-syntax-table (standard-syntax-table)
    ;; hairy logic based on Coq-style vs Isabelle-style configs
    (if (string= "" (format unicode-tokens-token-format ""))
	;; no special token format, parse separate words/symbols
	(let* ((optoks
		(remove* "^\\(?:\\sw\\|\\s_\\)+$"
			 toks :test 'string-match))
	       (idtoks
		(set-difference toks optoks))
	       (idorop
		(concat "\\(\\_<"
			(regexp-opt idtoks)
			"\\_>\\|\\(?:\\B"
			(regexp-opt optoks)
			"\\B\\)\\)")))
	  (if unicode-tokens-token-variant-format-regexp
	      (format unicode-tokens-token-variant-format-regexp
		      idorop)
	    idorop))
      ;; otherwise, assumption is that token syntax delimits tokens
      (if unicode-tokens-token-variant-format-regexp
	  (format unicode-tokens-token-variant-format-regexp
		  (regexp-opt toks))
	(regexp-opt (mapcar (lambda (tok)
			      (format unicode-tokens-token-format tok))
			    toks)))));)


(defun unicode-tokens-usable-composition (comp)
  "Return non-nil if the composition COMP seems to be usable.
The check is with `char-displayable-p'."
  (cond
   ((stringp comp)
    (reduce (lambda (x y) (and x (char-displayable-p y)))
 	    comp
 	    :initial-value t))
   ((characterp comp)
    (char-displayable-p comp))
   (comp ;; assume any other non-null is OK
    t)))

(defun unicode-tokens-help-echo ()
  "Return a help-echo text property to display the contents of match string."
  (if unicode-tokens-add-help-echo
      (list 'face nil 'help-echo (match-string 0))))

(defvar unicode-tokens-show-symbols nil
  "Non-nil to reveal symbol (composed) tokens instead of compositions.")

(defun unicode-tokens-interpret-composition (comp)
  "Turn the composition string COMP into an argument for `compose-region'."
  (cond
   ((and (stringp comp) (= 1 (length comp)))
    comp)
   ((stringp comp)
    ;; change a longer string into a sequence placing glyphs left-to-right.
    (let ((chars (nreverse (string-to-list comp)))
	  (sep   '(5 . 3))
	  res)
      (while chars
	(setq res (cons (car chars) res))
	(if (setq chars (cdr chars))
	    (setq res (cons sep res))))
      res))
   (t
    comp)))

(defun unicode-tokens-font-lock-compose-symbol (match)
  "Compose a sequence of chars into a symbol.
Regexp match data number MATCH selects the token name, while match
number 1 matches the text to be replaced.
Token name from MATCH is searched for in `unicode-tokens-hash-table'.
The face property is set to the :family and :slant attriubutes taken from
`unicode-tokens-symbol-font-face'."
  (let* ((start     (match-beginning 0))
	 (end       (match-end 0))
	 (compps    (gethash (match-string match)
			   unicode-tokens-hash-table))
	 (propsyms  (cdr-safe compps))
	 (comp      (car-safe compps)))
    (if (and comp (not unicode-tokens-show-symbols))
	(compose-region start end
			(unicode-tokens-interpret-composition comp)))
    (if propsyms
	(let ((props (unicode-tokens-symbs-to-props propsyms)))
	  (while props
	    (font-lock-append-text-property start end
					    (car props) (cadr props))
	    (setq props (cddr props)))))
    (unless (or unicode-tokens-show-symbols
		(intersection unicode-tokens-fonts propsyms))
      (font-lock-append-text-property
       start end 'face
       ;; just use family and slant to enhance merging with other faces
       (list :family
	     (face-attribute 'unicode-tokens-symbol-font-face :family)))
      (if (face-attribute 'unicode-tokens-symbol-font-face :slant)
	  (font-lock-append-text-property
	   start end 'face
	   (list :slant
		 (face-attribute 'unicode-tokens-symbol-font-face :slant))))
      )
    ;; [returning face property here seems to have no effect?]
    nil))

(defun unicode-tokens-prepend-text-properties-in-match (props matchno)
  (let ((start     (match-beginning matchno))
	(end       (match-end matchno)))
    (while props
      (unicode-tokens-prepend-text-property start end
					    (car props) (cadr props))
      (setq props (cddr props)))
    nil))

;; this is adapted from font-lock-prepend-text-property, which
;; currently fails to merge property values for 'face property properly.
;; e.g., it makes (:slant italic (:weight bold font-lock-string-face))
;; rather than  (:slant italic :weight bold font-lock-string-face)
;;
(defun unicode-tokens-prepend-text-property (start end prop value &optional object)
  "Prepend to one property of the text from START to END.
Arguments PROP and VALUE specify the property and value to append to the value
already in place.  The resulting property values are always lists.
Optional argument OBJECT is the string or buffer containing the text."
  (let ((val (if (listp value) value (list value))) next prev)
    (while (/= start end)
      (setq next (next-single-property-change start prop object end)
	    prev (get-text-property start prop object))
      ;; Canonicalize old forms of face property.
      (and (memq prop '(face font-lock-face))
	   (listp prev)
	   (or (keywordp (car prev))
	       (memq (car prev) '(foreground-color background-color)))
	   (setq prev (list prev)))
      (setq prev (if (listp prev) prev (list prev)))
      ;; hack to flatten erroneously nested face property lists
      (if (and (memq prop '(face font-lock-face))
	       (listp (car prev)) (null (cdr prev)))
	  (setq prev (car prev)))
      (put-text-property start next prop
			 (append prev val)
			 object)
      (setq start next))))

(defun unicode-tokens-show-symbols (&optional arg)
  "Toggle variable `unicode-tokens-show-symbols'.  With ARG, turn on iff positive."
  (interactive "P")
  (setq unicode-tokens-show-symbols
	(if (null arg) (not unicode-tokens-show-symbols)
	  (> (prefix-numeric-value arg) 0)))
  (font-lock-fontify-buffer))

(defun unicode-tokens-symbs-to-props (symbs &optional facenil)
  "Turn the property name list SYMBS into a list of text properties.
Symbols are looked up in `unicode-tokens-fontsymb-properties'.
Optional argument FACENIL means set the face property to nil, unless 'face is in the property list."
  (let (props ps)
    (dolist (s symbs)
      (setq ps (cdr-safe
		(cdr-safe (assoc s unicode-tokens-fontsymb-properties))))
      (dolist (p ps)
	(setq props (append p props))))
    (if (and facenil
	     (not (memq 'face props)))
	(setq props (append '(face nil) props)))
    props))

;;
;; Control tokens: as "characters" CTRL <stuff>
;;                 and regions     BEGINCTRL <stuff> ENDCTRL
;;

(defvar unicode-tokens-show-controls nil
  "Non-nil supresses hiding of control tokens.")

(defun unicode-tokens-show-controls (&optional arg)
  "Toggle variable `unicode-tokens-show-controls'.  With ARG, turn on iff positive."
  (interactive "P")
  (setq unicode-tokens-show-controls
	(if (null arg) (not unicode-tokens-show-controls)
	  (> (prefix-numeric-value arg) 0)))
  (when unicode-tokens-show-controls
    (remove-from-invisibility-spec 'unicode-tokens-show-controls))
  (when (not unicode-tokens-show-controls)
    (add-to-invisibility-spec 'unicode-tokens-show-controls))
  (redraw-display))

(defun unicode-tokens-control-char (name s &rest props)
  `(,(format unicode-tokens-control-char-format-regexp (regexp-quote s))
    (1 '(face nil invisible unicode-tokens-show-controls) prepend)
    ;; simpler but buggy with font-lock-prepend-text-property:
    ;; (2 ',(unicode-tokens-symbs-to-props props t) prepend)
    (2 (unicode-tokens-prepend-text-properties-in-match
	',(unicode-tokens-symbs-to-props props t) 2) prepend)
    ))

(defun unicode-tokens-control-region (name start end &rest props)
  `(,(format unicode-tokens-control-region-format-regexp
	     (regexp-quote start) (regexp-quote end))
    (1 '(face nil invisible unicode-tokens-show-controls) prepend)
    ;; simpler but buggy with font-lock-prepend-text-property:
    ;; (2 ',(unicode-tokens-symbs-to-props props t) prepend)
    (2 (unicode-tokens-prepend-text-properties-in-match
	',(unicode-tokens-symbs-to-props props t) 2) prepend)
    (3 '(face nil invisible unicode-tokens-show-controls) prepend)
    ))

(defun unicode-tokens-control-font-lock-keywords ()
  (append
   (mapcar (lambda (args) (apply 'unicode-tokens-control-char args))
	   unicode-tokens-control-characters)
   (mapcar (lambda (args) (apply 'unicode-tokens-control-region args))
	   unicode-tokens-control-regions)))

;;
;; Shortcuts for typing, using quail
;;

(defvar unicode-tokens-use-shortcuts t
  "Non-nil means use `unicode-tokens-shortcut-alist' if set.")

(defun unicode-tokens-use-shortcuts (&optional arg)
  "Toggle variable `unicode-tokens-use-shortcuts'.  With ARG, turn on iff positive."
  (interactive "P")
  (setq unicode-tokens-use-shortcuts
	(if (null arg) (not unicode-tokens-use-shortcuts)
	  (> (prefix-numeric-value arg) 0)))
  (if unicode-tokens-use-shortcuts
    (set-input-method "Unicode tokens")
    (set-input-method nil)))

(quail-define-package
 "Unicode tokens" "UTF-8" "u" t
 "Input method for tokens or unicode characters, application specific short-cuts"
 nil t nil nil nil nil nil ; max shortest, could try t
 nil nil nil t)

(defun unicode-tokens-map-ordering (s1 s2)
  "Ordering on (car S1, car S2): order longer strings first."
  (>= (length (car s1)) (length (car s2))))

; core dump caused when quail active, but not by quail.
;(defun unicode-tokens-shortcut-will-crash-emacs (ustring)
;  "Work around a nasty Emacs bug that causes a core dump."
;  (> 1 (length ustring)))

(defun unicode-tokens-quail-define-rules ()
  "Define the token and shortcut input rules.
Calculated from `unicode-tokens-token-name-alist' and
`unicode-tokens-shortcut-alist'."
  (let ((unicode-tokens-quail-define-rules
	 (list 'quail-define-rules)))
    (let ((ulist (copy-list unicode-tokens-shortcut-alist))
	  ustring shortcut)
      (setq ulist (sort ulist 'unicode-tokens-map-ordering))
      (while ulist
	(setq shortcut (caar ulist))
	(setq ustring (cdar ulist))
	(nconc unicode-tokens-quail-define-rules
	       (list (list shortcut
			   (vector ustring))))
	(setq ulist (cdr ulist))))
    (eval unicode-tokens-quail-define-rules)))


;;
;; User-level functions
;;

(defun unicode-tokens-insert-token (tok)
  "Insert symbolic token named TOK, giving a message."
  (interactive (list (completing-read
		      "Insert token: "
		      unicode-tokens-hash-table)))
  (let ((ins (format unicode-tokens-token-format tok)))
    (insert ins)
    (message "Inserted %s" ins)))

(defun unicode-tokens-annotate-region (name)
  "Annotate region with region markup tokens for scheme NAME.
Available annotations chosen from `unicode-tokens-control-regions'."
  (interactive (let ((completion-ignore-case t))
		 (list (completing-read
			"Annotate region with: "
			unicode-tokens-control-regions nil
			'requirematch))))
  (assert (assoc name unicode-tokens-control-regions))
  (let* ((entry (assoc name unicode-tokens-control-regions))
	 (beg   (region-beginning))
	 (end   (region-end))
	 (begtok
	  (format unicode-tokens-control-region-format-start (nth 1 entry)))
	 (endtok
	  (format unicode-tokens-control-region-format-end (nth 2 entry))))
    (when (> beg end)
	(setq beg end)
	(setq end (region-beginning)))
    (goto-char beg)
    (insert begtok)
    (goto-char (+ end (- (point) beg)))
    (insert endtok)))

(defun unicode-tokens-insert-control (name)
  "Insert a control symbol sequence.  NAME is from `unicode-tokens-control-characters'."
  (interactive (list (completing-read
		      "Insert control symbol: "
		      unicode-tokens-control-characters
		      nil 'requirematch)))
  (assert (assoc name unicode-tokens-control-characters))
  (insert (format unicode-tokens-control-char-format
		  (cadr (assoc name unicode-tokens-control-characters)))))

(defun unicode-tokens-insert-uchar-as-token (char)
  "Insert CHAR as a symbolic token, if possible."
  (let ((tok (gethash char unicode-tokens-uchar-hash-table)))
    (when tok
      (unicode-tokens-insert-token tok))))

(defun unicode-tokens-delete-token-near-point ()
  "Delete the token near point; try first before point, then after."
  (interactive)
  (if (or
       (re-search-backward unicode-tokens-token-match-regexp
			   (save-excursion
			     (beginning-of-line) (point)) t)
       (re-search-forward unicode-tokens-token-match-regexp
			   (save-excursion
			     (end-of-line) (point)) t))
      (kill-region (match-beginning 0) (match-end 0))))

(defun unicode-tokens-delete-backward-char (&optional arg)
  "Delete the last ARG visually presented characters.
This accounts for tokens having a single character presentation
but multiple characters in the underlying buffer."
  (interactive "p")
  (if arg
      (while (> arg 0)
	(unicode-tokens-delete-backward-1)
	(setq arg (1- arg)))
    (unicode-tokens-delete-backward-1)))

(defun unicode-tokens-delete-char (&optional arg)
  "Delete the next ARG visually presented characters.
This accounts for tokens having a single character presentation
but multiple characters in the underlying buffer."
  (interactive "p")
  (if arg
      (while (> arg 0)
	(unicode-tokens-delete-1)
	(setq arg (1- arg)))
    (unicode-tokens-delete-1)))

(defun unicode-tokens-delete-backward-1 ()
  "Delete the last visually presented character.
This accounts for tokens having a single character presentation
but multiple characters in the underlying buffer."
  (let (tokst tokend)
    (save-match-data
      (save-excursion
	(setq tokst
	      (re-search-backward unicode-tokens-token-match-regexp
				  (save-excursion
				    (beginning-of-line) (point)) t))
	(setq tokend (match-end 0))))
    ;(message "End is: %d and point is: %d" tokend (point))
    (if (and tokst (= (point) tokend))
	(delete-region tokst tokend)
      (delete-char -1))))

(defun unicode-tokens-delete-1 ()
  "Delete the following visually presented character.
This accounts for tokens having a single character presentation
but multiple characters in the underlying buffer."
  (let (tokend)
    (save-match-data
      (save-excursion
	(if (looking-at unicode-tokens-token-match-regexp)
	    (setq tokend (match-end 0)))))
    (if tokend
	(delete-region (point) tokend)
      (delete-char 1))))


;; TODO: behaviour with unknown tokens not good.  Should
;; use separate regexp for matching tokens known or not known.
(defun unicode-tokens-prev-token ()
  "Return the token before point, matching with `unicode-tokens-token-match-regexp'."
  (let ((match (re-search-backward unicode-tokens-token-match-regexp
				    (save-excursion
				      (beginning-of-line 0) (point)) t)))
    (if match
	(match-string 1))))

(defun unicode-tokens-rotate-token-forward (&optional n)
  "Rotate the token before point by N steps in the table."
  (interactive "p")
  (if (> (point) (point-min))
      (save-match-data
	(let ((pos    (point))
	      (token  (unicode-tokens-prev-token)))
	  (when (not token)
	    (goto-char (point))
	    (error "Cannot find token before point"))
	  (when token
	    (let* ((tokennumber
		    (search (list token) unicode-tokens-token-list :test 'equal))
		   (numtoks
		    (hash-table-count unicode-tokens-hash-table))
		   (newtok
		    (if tokennumber
			(nth (mod (+ tokennumber (or n 1)) numtoks)
			     unicode-tokens-token-list))))
	      (when newtok
		(delete-region (match-beginning 0) (match-end 0))
		(insert (format unicode-tokens-token-format newtok)))
	      (when (not newtok)
		;; FIXME: currently impossible case
		(message "Token not in tables: %s" token))))))))


(defun unicode-tokens-rotate-token-backward (&optional n)
  "Rotate the token before point, by -N steps in the token list."
  (interactive "p")
  (unicode-tokens-rotate-token-forward (if n (- n) -1)))

(defun unicode-tokens-replace-shortcut-match (&rest ignore)
  "Subroutine for `unicode-tokens-replace-shortcuts'."
  (let* ((match (match-string-no-properties 0))
	 (repl  (if match
		    (cdr-safe
		     (assoc match unicode-tokens-shortcut-replacement-alist)))))
    (if repl (regexp-quote repl))))

;; handy for legacy Isabelle files, probably not useful in general.
(defun unicode-tokens-replace-shortcuts ()
  "Query-replace shortcuts in the buffer with compositions they expand to.
Starts from point."
  (interactive)
  (let ((shortcut-regexp
	 (regexp-opt (mapcar 'car unicode-tokens-shortcut-replacement-alist))))
    ;; override the display of the regexp because it's huge!
    ;; (doesn't help with C-h: need way to programmatically show string)
    (cl-flet ((query-replace-descr (str) 
				(if (eq str shortcut-regexp) "shortcut" str)))
      (perform-replace shortcut-regexp
		       (cons 'unicode-tokens-replace-shortcut-match nil)
		       t t nil))))

(defun unicode-tokens-replace-unicode-match (&rest ignore)
  "Subroutine for `unicode-tokens-replace-unicode'."
  (let* ((useq	(match-string-no-properties 0))
	 (token (gethash useq unicode-tokens-uchar-hash-table)))
    (if token (regexp-quote
	       (format unicode-tokens-token-format token)))))

(defun unicode-tokens-replace-unicode ()
  "Query-replace unicode sequences in the buffer with tokens having same appearance.
Starts from point."
  (interactive)
  (let ((uchar-regexp unicode-tokens-uchar-regexp))
    ;; override the display of the regexp because it's huge!
    ;; (doesn't help with C-h: need way to programmatically show string)
    (cl-flet ((query-replace-descr (str) (if (eq str uchar-regexp)
					  "unicode presentation" str)))
      (perform-replace uchar-regexp
		       (cons 'unicode-tokens-replace-unicode-match nil)
       t t nil))))

;;
;; Token and shortcut tables
;;

(defun unicode-tokens-copy-token (tokname)
  "Copy the token TOKNAME into the kill ring."
  (interactive "s")
  (kill-new
   (format unicode-tokens-token-format tokname)
   (eq last-command 'unicode-tokens-copy-token)))

(define-button-type 'unicode-tokens-list
  'help-echo "mouse-2, RET: copy this character"
  'face nil
  'action #'(lambda (button)
	      (unicode-tokens-copy-token (button-get button 'unicode-token))))

(defun unicode-tokens-list-tokens ()
  "Show a buffer of all tokens."
  (interactive)
  (with-output-to-temp-buffer "*Unicode Tokens List*"
    (with-current-buffer standard-output
      (make-local-variable 'unicode-tokens-show-symbols)
      (setq unicode-tokens-show-symbols nil)
      (unicode-tokens-mode)
      (setq tab-width 7)
      (insert "Hover to see token.  Mouse-2 or RET to copy into kill ring.\n")
      (let ((count 10)
	    (toks unicode-tokens-token-list)
	    tok)
	;; display in originally given order
	(while (or (/= 1 (mod count 10)) toks)
	  (unless (null toks)
	    (setq tok (car toks)))
	  (if (/= 0 (mod count 10))
	      (insert "\t")
	    (insert "\n")
	    (unless (null toks)
	      (insert (format "%4d. " (/ count 10))))
	    (if (= 0 (mod count 20))
		(overlay-put (make-overlay
			      (save-excursion
				(forward-line -1) (point))
			      (point))
			     'face
			     '(background-color . "gray90")))
	    (insert " "))
	  (incf count)
	  (if (null toks)
	      (insert " ")
	    (insert-text-button
	     (format unicode-tokens-token-format tok)
	     :type 'unicode-tokens-list
	     'unicode-token tok)
	    (setq toks (cdr toks))))))))

(defun unicode-tokens-list-shortcuts ()
  "Show a buffer of all the shortcuts available."
  (interactive)
  (with-output-to-temp-buffer "*Unicode Tokens Shortcuts*"
    (with-current-buffer standard-output
      (make-local-variable 'unicode-tokens-show-symbols)
      (setq unicode-tokens-show-symbols nil)
      (unicode-tokens-mode)
      (let (grey start)
	(dolist (short unicode-tokens-shortcut-alist)
	  (setq start (point))
	  (insert "Typing  " (car short) "\tinserts \t"
		  (cdr short) "\n")
	  (if (setq grey (not grey))
	      (overlay-put (make-overlay start (point))
			   'face
			   '(background-color . "gray90"))))))))

(defalias 'unicode-tokens-list-unicode-chars 'unicode-chars-list-chars)

(defun unicode-tokens-encode-in-temp-buffer (str fn)
  "Call FN on encoded version of STR."
  (with-temp-buffer
    (insert str)
    (goto-char (point-min))
    (while (re-search-forward unicode-tokens-token-match-regexp nil t)
      ;; TODO: interpret more exotic compositions here
      (let* ((tstart    (match-beginning 0))
	     (tend      (match-end 0))
	     (comp      (car-safe
			 (gethash (match-string 1)
				  unicode-tokens-hash-table))))
	(when comp
	  (delete-region tstart tend)
	  ;; TODO: improve this: interpret vector, strip tabs
	  (insert comp)))) ;; gross approximation to compose-region
    (funcall fn (point-min) (point-max))))

(defun unicode-tokens-encode (beg end)
  "Return a unicode encoded version of the presentation in region BEG..END."
  (unicode-tokens-encode-in-temp-buffer
   (buffer-substring-no-properties beg end) 'buffer-substring))

;;;###autoload
(defun unicode-tokens-encode-str (str)
  "Return a unicode encoded version presentation of STR."
  (unicode-tokens-encode-in-temp-buffer str 'buffer-substring))

(defun unicode-tokens-copy (beg end)
  "Copy presentation of region between BEG and END.
This is an approximation; it makes assumptions about the behaviour
of symbol compositions, and will lose layout information."
  (interactive "r")
  ;; cf kill-ring-save, uncode-tokens-font-lock-compose-symbol
  (unicode-tokens-encode-in-temp-buffer
   (buffer-substring-no-properties beg end) 'copy-region-as-kill))

(defun unicode-tokens-paste ()
  "Paste text from clipboard, converting Unicode to tokens where possible."
  (interactive)
  (let ((start (point)) end)
    ;; da: notice bug in Emacs 23 snapshot (at least) on Ubuntu 9.04
    ;; that gives wrong default to x-select-enable-clipboard
    ;; need: (setq x-select-enable-clipboard t)
    (clipboard-yank)
    (setq end (point-marker))
    (while (re-search-backward unicode-tokens-uchar-regexp start t)
      (let* ((useq	(match-string 0))
	     (token     (gethash useq unicode-tokens-uchar-hash-table))
	     (pos	(point)))
	(when token
	  (replace-match (format unicode-tokens-token-format token) t t)
	  (goto-char pos))))
    (goto-char end)
    (set-marker end nil)))

(defvar unicode-tokens-highlight-unicode nil
  "Non-nil to highlight Unicode characters.")

(defconst unicode-tokens-unicode-highlight-patterns
  '(("[^\000-\177]" (0 'unicode-tokens-highlight-face t)))
  "Font lock patterns for highlighting Unicode tokens.")

(defun unicode-tokens-highlight-unicode ()
  "Hilight Unicode characters in the buffer.
Toggles highlighting of Unicode characters used in the
buffer beyond the legacy 8-bit character set codes.  This is
useful to manually determine if a buffer contains Unicode or
tokenised symbols."
  (interactive)
  (setq unicode-tokens-highlight-unicode
	(not unicode-tokens-highlight-unicode))
  (unicode-tokens-highlight-unicode-setkeywords)
  (font-lock-fontify-buffer))

(defun unicode-tokens-highlight-unicode-setkeywords ()
  "Adjust font lock keywords according to variable `unicode-tokens-highlight-unicode'."
  (if unicode-tokens-highlight-unicode
    (font-lock-add-keywords
     nil unicode-tokens-unicode-highlight-patterns)
    (font-lock-remove-keywords
     nil unicode-tokens-unicode-highlight-patterns)))

;;
;; Minor mode
;;

(defun unicode-tokens-initialise ()
  "Perform initialisation for Unicode Tokens minor mode.
This function calculates `font-lock-keywords' and other configuration
variables."
  (interactive)
  (unicode-tokens-copy-configuration-variables)
  (let ((flks (unicode-tokens-font-lock-keywords)))
    (put 'unicode-tokens-font-lock-keywords major-mode flks)
    (unicode-tokens-quail-define-rules)
    (unicode-tokens-define-menu)
    flks))

;; not as expected
;; (defun unicode-tokens-restart ()
;;   (interactive)
;;   (unicode-tokens-mode 0)
;;   (put 'unicode-tokens-font-lock-keywords major-mode nil)
;;   (setq font-lock-set-defaults nil)
;;   (unicode-tokens-mode 1))

(defvar unicode-tokens-mode-map (make-sparse-keymap)
  "Key map used for Unicode Tokens mode.")

(defvar unicode-tokens-display-table
  (let ((disptab (make-display-table)))
    (set-display-table-slot disptab 'selective-display
			    (vector ?\ #x0022ef ?\ ))
    disptab)
  "Display table for Unicode Tokens mode.  Alters ellipsis character.")

(define-minor-mode unicode-tokens-mode
  "Toggle Tokens mode for current buffer.
With optional argument ARG, turn Tokens mode on if ARG is
positive, otherwise turn it off.

In Unicode Tokens mode (Utoks appears in the modeline), a
sequence of characters in the buffer (a token) may be presented
instead as a Unicode character. The underlying buffer contents is
not changed, only what is presented on the display.  Other tokens
may be used to control layout, for example, enabling sub/super
scripts, bold and italic fonts, etc.  Keyboard shortcut sequences
for entering tokens quickly can be defined.

Tokens mode needs configuration with a set of tokens, their
presentation forms, and keyboard shortcuts.  See documentation in
`unicode-tokens.el' for more information.

Commands available are:

\\{unicode-tokens-mode-map}"
  :keymap unicode-tokens-mode-map
  :init-value nil
  :lighter " Utoks"
  :group 'unicode-tokens
  (let ((flks (get 'unicode-tokens-font-lock-keywords major-mode)))
    (when unicode-tokens-mode
      (unless flks
	(setq flks (unicode-tokens-initialise)))
      ;; make sure buffer can display 16 bit chars
      (if (and
	   (fboundp 'set-buffer-multibyte)
	   (not (buffer-base-buffer)))
	  (set-buffer-multibyte t))

      (make-local-variable 'font-lock-extra-managed-props)

      (when (not unicode-tokens-show-controls)
	(add-to-invisibility-spec 'unicode-tokens-show-controls))

      (make-local-variable 'unicode-tokens-highlight-unicode)

      ;; a convention:
      ;; - set default for font-lock-extra-managed-props
      ;;   as property on major mode symbol (ordinarily nil).
      (font-lock-add-keywords nil flks)

      (setq font-lock-extra-managed-props
	    (get 'font-lock-extra-managed-props major-mode))
      (mapc
       (lambda (p) (add-to-list 'font-lock-extra-managed-props p))
       unicode-tokens-font-lock-extra-managed-props)

      (unicode-tokens-highlight-unicode-setkeywords)

      (font-lock-fontify-buffer)

      ;; experimental: this may be rude for non-nil standard tables
      (setq buffer-display-table unicode-tokens-display-table)

      (if unicode-tokens-use-shortcuts
	  (set-input-method "Unicode tokens"))

      ;; adjust maths menu to insert tokens
      (set (make-local-variable 'maths-menu-filter-predicate)
	   (lambda (uchar) (gethash (char-to-string uchar)
				    unicode-tokens-uchar-hash-table)))
      (set (make-local-variable 'maths-menu-tokenise-insert)
	   (lambda (uchar)
	     (unicode-tokens-insert-token
	      (gethash (char-to-string uchar)
		       unicode-tokens-uchar-hash-table)))))

    (when (not unicode-tokens-mode)

      (remove-from-invisibility-spec 'unicode-tokens-show-controls)

      (when flks
	(font-lock-unfontify-buffer)
	(setq font-lock-extra-managed-props
	      (get 'font-lock-extra-managed-props major-mode))
	(setq font-lock-set-defaults nil) ; force font-lock-set-defaults to reinit
	(font-lock-fontify-buffer)
	(set-input-method nil))

      ;; experimental: this may be rude for non-nil standard tables
      (setq buffer-display-table nil)

      ;; Remove hooks from maths menu
      (kill-local-variable 'maths-menu-filter-predicate)
      (kill-local-variable 'maths-menu-tokenise-insert))))


;;
;; Font selection
;;

(when (fboundp 'ns-respond-to-change-font)
  ;; A nasty hack to ns-win.el for Mac OS X support

  ;; Tricky because we get a callback on font changes, but not when
  ;; the window is closed.  How do we know when user is finished?

  (when (not (fboundp 'old-ns-respond-to-change-font))
    (fset 'old-ns-respond-to-change-font
	  (symbol-function 'ns-respond-to-change-font)))

  (when (not (fboundp 'old-ns-popup-font-panel))
    (fset 'old-ns-popup-font-panel
	  (symbol-function 'ns-popup-font-panel)))

  (defvar unicode-tokens-respond-to-change-font nil)

  (defun ns-respond-to-change-font (&rest args)
    (interactive)
    (cond
     (unicode-tokens-respond-to-change-font
	(unicode-tokens-set-font-var-aux
	 unicode-tokens-respond-to-change-font
	 (with-no-warnings
	   ns-input-font)))
     (t
      (apply 'old-ns-respond-to-change-font args))))

  (defun ns-popup-font-panel (&rest args)
    (setq unicode-tokens-respond-to-change-font nil)
    (with-no-warnings
      (apply 'old-ns-popup-font-panel args)))

  (defun unicode-tokens-popup-font-panel (fontvar)
    (setq unicode-tokens-respond-to-change-font fontvar)
    (with-no-warnings
      (old-ns-popup-font-panel)))
)

;; parameterised version of function from menu-bar.el (Emacs 23.1)
;; this now copes with Emacs 23.1, Emacs 22, Mac OS X Emacs 23.1.
(defun unicode-tokens-set-font-var (fontvar)
  "Interactively select a font for FONTVAR."
  (interactive)
  (let (font spec)
    (if (fboundp 'ns-popup-font-panel)
	(with-no-warnings
	  (unicode-tokens-popup-font-panel fontvar))
      (cond
       ((fboundp 'x-select-font)
	(setq font (x-select-font)))
       ((fboundp 'mouse-select-font)
	(setq font (mouse-select-font)))
       (t
	(setq font (unicode-tokens-mouse-set-font))))
      (unicode-tokens-set-font-var-aux fontvar font))))

(defun unicode-tokens-set-font-var-aux (fontvar font)
  "A subroutine of `unicode-tokens-set-font-var'."
  (when font
    ;; Trac #311 - sometimes (on Linux/xft) :font doesn't work but
    ;; :family does.
    (condition-case nil
	(set-face-attribute fontvar (selected-frame)
			    ;; da: don't try to reset these for token fonts.
			    ;; :weight 'normal :slant 'normal
			    :width 'normal
			    :font font)
      (error
       (set-face-attribute fontvar (selected-frame)
			   :width 'normal
			   :family font)))
    (let ((font-object (face-attribute fontvar :font))
	  spec)

 	(set-face-attribute fontvar t :font font-object)
        (setq spec (list (list t (face-attr-construct fontvar))))
	(put fontvar 'customized-face spec)
	(custom-push-theme 'theme-face fontvar 'user 'set spec)
	(put fontvar 'face-modified nil))
    ;; da: add this to make sure fonts set by font lock are altered
    (dolist (f (frame-list))
      (and (display-graphic-p f)
	   (dolist (w (window-list f))
	     (with-current-buffer (window-buffer w)
	       (when font-lock-mode (font-lock-fontify-buffer))))))))

;; based on mouse-set-font from mouse.el in Emacs 22.2.1
(defun unicode-tokens-mouse-set-font ()
  "Select an Emacs font from a list of known good fonts and fontsets."
  (unless (display-multi-font-p)
    (error "Cannot change fonts on this display"))
  (car-safe ; just choose first
	    ; (original cycles through trying set-default-font
   (x-popup-menu
    (if (listp last-nonmenu-event)
       last-nonmenu-event
     (list '(0 0) (selected-window)))
   ;; Append list of fontsets currently defined.
   (append x-fixed-font-alist (list (generate-fontset-menu))))))

(defsubst unicode-tokens-face-font-sym (fontsym)
  "Return the symbol unicode-tokens-FONTSYM-font-face."
  (intern (concat "unicode-tokens-" (symbol-name fontsym) "-font-face")))

(defun unicode-tokens-set-font-restart (fontsym)
  "Open a dialog to set the font for FONTSYM, and reinitialise."
  (let ((facevar (unicode-tokens-face-font-sym fontsym)))
    (unicode-tokens-set-font-var facevar)
    (unicode-tokens-initialise)
    (font-lock-fontify-buffer)))

;;
;; interface to custom
;;

(defun unicode-tokens-save-fonts ()
  "Save the customized font variables."
  ;; save all customized faces (tricky to do less)
  (interactive)
  (apply 'unicode-tokens-custom-save-faces
   (mapcar 'unicode-tokens-face-font-sym
	   unicode-tokens-fonts)))

(defun unicode-tokens-custom-save-faces (&rest faces)
  "Save custom faces FACES."
  (dolist (symbol faces)
    (let ((face (get symbol 'customized-face)))
      ;; See customize-save-customized; adjust properties so
      ;; that custom-save-all will save the face.
      (when face
	(put symbol 'saved-face face)
	(custom-push-theme 'theme-value symbol 'user 'set face)
	(put symbol 'customized-face nil))))
  (custom-save-all))


;;
;; Key bindings
;;

(define-key unicode-tokens-mode-map
  [remap delete-backward-char]
  'unicode-tokens-delete-backward-char)
(define-key unicode-tokens-mode-map
  [remap delete-char]
  'unicode-tokens-delete-char)

;; support delete selection mode
(put 'unicode-tokens-delete-backward-char 'delete-selection 'supersede)
(put 'unicode-tokens-delete-char 'delete-selection 'supersede)

(defvar unicode-tokens-quail-translation-keymap
  (let ((quail-current-package
	 (assoc "Unicode tokens"
		quail-package-alist)))
    (quail-translation-keymap)))

;; FIXME: does this work?
(define-key unicode-tokens-quail-translation-keymap
     [remap quail-delete-last-char]
     'unicode-tokens-quail-delete-last-char)

(defun unicode-tokens-quail-delete-last-char ()
  (interactive)
  (if unicode-tokens-mode
      (if (= (length quail-current-key) 1)
	  (progn
	    (quail-abort-translation)
	    (unicode-tokens-delete-backward-char))
	(quail-delete-last-char))
    (quail-delete-last-char)))

;    (setq quail-current-key (substring quail-current-key 0 -1))
;    (quail-delete-region)
 ;   (quail-update-translation (quail-translate-key))))


(define-key unicode-tokens-mode-map [(control ?,)]
  'unicode-tokens-rotate-token-backward)
(define-key unicode-tokens-mode-map [(control ?.)]
  'unicode-tokens-rotate-token-forward)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control t)] 'unicode-tokens-insert-token)
(define-key unicode-tokens-mode-map
  [(control c) (control backspace)]
  'unicode-tokens-delete-token-near-point)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control r)] 'unicode-tokens-annotate-region)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control e)] 'unicode-tokens-insert-control)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control z)] 'unicode-tokens-show-symbols)
(define-key unicode-tokens-mode-map
  [(control c) (control t) (control t)] 'unicode-tokens-show-controls)


;;
;; Menu
;;

(defun unicode-tokens-customize-submenu ()
  (mapcar (lambda (cv)
	    (vector (car cv)
		    `(lambda () (interactive)
		       (customize-variable (quote ,(cadr cv))))))
	  unicode-tokens-tokens-customizable-variables))

(defun unicode-tokens-define-menu ()
  "Define Tokens menu."
  (easy-menu-define unicode-tokens-menu unicode-tokens-mode-map
   "Tokens menu"
    (cons "Tokens"
     (list
      ["Insert Token..." unicode-tokens-insert-token]
      ["Next Token"      unicode-tokens-rotate-token-forward]
      ["Prev Token"      unicode-tokens-rotate-token-backward]
      ["Delete Token"    unicode-tokens-delete-token-near-point]
       (cons "Format Char"
	     (mapcar
	     (lambda (fmt)
	       (vector (car fmt)
		       `(lambda () (interactive)
			  (funcall 'unicode-tokens-insert-control ',(car fmt)))
		       :help (concat "Format next item as "
				     (downcase (car fmt)))))
	     unicode-tokens-control-characters))
       (cons "Format Region"
	    (mapcar
	     (lambda (fmt)
	       (vector (car fmt)
		       `(lambda () (interactive)
			 (funcall 'unicode-tokens-annotate-region ',(car fmt)))
		       :help (concat "Format region as "
				     (downcase (car fmt)))
		       :active 'mark-active))
	     unicode-tokens-control-regions))
       "---"
      ["List Tokens"     unicode-tokens-list-tokens]
      ["List Shortcuts"  unicode-tokens-list-shortcuts]
      ["List Unicode Characters"  unicode-tokens-list-unicode-chars]
      "---"
      ["Copy As Unicode" unicode-tokens-copy
       :active 'mark-active
       :help "Copy presentation form of text from buffer, converting tokens to Unicode"]
      ["Paste From Unicode" unicode-tokens-paste
       :active (and kill-ring (not buffer-read-only))
       :help
       "Paste from clipboard, converting Unicode to tokens where possible"]
      ["Replace Shortcuts" unicode-tokens-replace-shortcuts
       :help "Query-replace shortcut sequences with compositions they stand for, starting from point"]
      ["Replace Unicode" unicode-tokens-replace-unicode
       :help "Query-replace Unicode characters with tokens where possible, starting from point"]
       "---"
      ["Reveal Control Tokens" unicode-tokens-show-controls
       :style toggle
       :selected unicode-tokens-show-controls
       :active (or
		unicode-tokens-control-region-format-regexp
		unicode-tokens-control-char-format-regexp)
       :help "Prevent hiding of control tokens"]
      ["Reveal Symbol Tokens" unicode-tokens-show-symbols
       :style toggle
       :selected unicode-tokens-show-symbols
       :help "Show tokens for symbols"]
      ["Highlight Real Unicode Chars" unicode-tokens-highlight-unicode
       :style toggle
       :selected unicode-tokens-highlight-unicode
       :help "Hightlight non-8bit characters in buffer which are saved as Unicode"]
      ["Enable Shortcuts" unicode-tokens-use-shortcuts
       :style toggle
       :selected unicode-tokens-use-shortcuts
       :active unicode-tokens-shortcut-alist
       :help "Use short cuts for typing tokens"]
      ["Add Token Hovers" unicode-tokens-toggle-add-help-echo
       :style toggle
       :selected unicode-tokens-add-help-echo
       :help "Use hover popups (or minibuffer messages) to show underlying tokens"]
      "---"
      (cons "Customize"
	    (unicode-tokens-customize-submenu))
      (cons "Set Font"
       (append
	(mapcar
	 (lambda (var)
	   (vector
	    (upcase-initials (symbol-name var))
	    `(lambda () (interactive)
		(funcall 'unicode-tokens-set-font-restart ',var))
	     :help (concat "Set the " (symbol-name var) " font")))
	 unicode-tokens-fonts)
	 (list "----"
	["Save Fonts" unicode-tokens-save-fonts
	 :help "Save the customized font choices"]
	["Make Fontsets"
	 (lambda () (interactive) (require 'pg-fontsets))
	 :active (not (featurep 'pg-fontsets))
	 :help "Define fontsets (for Options->Set fontsets)"
	 :visible (< emacs-major-version 23) ; not useful on 23,
	 ;; at least when font menu provided.  Drawback: this
	 ;; is done too late: displayable tokens have already been
	 ;; chosen now, before fontsets generated.
	 ;; Never mind: non-issue with platform fonts menu.
	 ])))))))



(provide 'unicode-tokens)

;;; unicode-tokens.el ends here
