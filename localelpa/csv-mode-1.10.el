;;; csv-mode.el --- Major mode for editing comma/char separated values  -*- lexical-binding: t -*-

;; Copyright (C) 2003, 2004, 2012-2019  Free Software Foundation, Inc

;; Author: "Francis J. Wright" <F.J.Wright@qmul.ac.uk>
;; Maintainer: emacs-devel@gnu.org
;; Version: 1.10
;; Package-Requires: ((emacs "24.1") (cl-lib "0.5"))
;; Keywords: convenience

;; This package is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This package is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This package implements CSV mode, a major mode for editing records
;; in a generalized CSV (character-separated values) format.  It binds
;; files with prefix ".csv" to `csv-mode' (and ".tsv" to `tsv-mode') in
;; `auto-mode-alist'.

;; In CSV mode, the following commands are available:

;; - C-c C-s (`csv-sort-fields') and C-c C-n (`csv-sort-numeric-fields')
;;   respectively sort lexicographically and numerically on a
;;   specified field or column.

;; - C-c C-r (`csv-reverse-region') reverses the order.  (These
;;   commands are based closely on, and use, code in `sort.el'.)

;; - C-c C-k (`csv-kill-fields') and C-c C-y (`csv-yank-fields') kill
;;   and yank fields or columns, although they do not use the normal
;;   kill ring.  C-c C-k can kill more than one field at once, but
;;   multiple killed fields can be yanked only as a fixed group
;;   equivalent to a single field.

;; - `csv-align-mode' keeps fields visually aligned, on-the-fly.
;;   It truncates fields to a maximum width that can be changed per-column
;;   with `csv-align-set-column-width'.
;;   Alternatively, C-c C-a (`csv-align-fields') aligns fields into columns
;;   and C-c C-u (`csv-unalign-fields') undoes such alignment;
;;   separators can be hidden within aligned records (controlled by
;;   `csv-invisibility-default' and `csv-toggle-invisibility').

;; - C-c C-t (`csv-transpose') interchanges rows and columns.  For
;;   details, see the documentation for the individual commands.

;; CSV mode can recognize fields separated by any of several single
;; characters, specified by the value of the customizable user option
;; `csv-separators'.  CSV data fields can be delimited by quote
;; characters (and must if they contain separator characters).  This
;; implementation supports quoted fields, where the quote characters
;; allowed are specified by the value of the customizable user option
;; `csv-field-quotes'.  By default, the both commas and tabs are considered
;; as separators and the only field quote is a double quote.
;; These user options can be changed ONLY by customizing them, e.g. via M-x
;; customize-variable.

;; CSV mode commands ignore blank lines and comment lines beginning
;; with the value of the buffer local variable `csv-comment-start',
;; which by default is #.  The user interface is similar to that of
;; the standard commands `sort-fields' and `sort-numeric-fields', but
;; see the major mode documentation below.

;; The global minor mode `csv-field-index-mode' provides display of
;; the current field index in the mode line, cf. `line-number-mode'
;; and `column-number-mode'.  It is on by default.

;;; Installation:

;; Put this file somewhere that Emacs can find it (i.e. in one of the
;; directories in your `load-path' such as `site-lisp'), optionally
;; byte-compile it (recommended), and put this in your .emacs file:
;;
;; (add-to-list 'auto-mode-alist '("\\.[Cc][Ss][Vv]\\'" . csv-mode))
;; (autoload 'csv-mode "csv-mode"
;;   "Major mode for editing comma-separated value files." t)

;;; History:

;; Begun on 15 November 2003 to provide lexicographic sorting of
;; simple CSV data by field and released as csv.el.  Facilities to
;; kill multiple fields and customize separator added on 9 April 2004.
;; Converted to a major mode and renamed csv-mode.el on 10 April 2004,
;; partly at the suggestion of Stefan Monnier <monnier at
;; IRO.UMontreal.CA> to avoid conflict with csv.el by Ulf Jasper.
;; Field alignment, comment support and CSV mode customization group
;; added on 1 May 2004.  Support for index ranges added on 6 June
;; 2004.  Multiple field separators added on 12 June 2004.
;; Transposition added on 22 June 2004.  Separator invisibility added
;; on 23 June 2004.

;;; See also:

;; the standard GNU Emacs 21 packages align.el, which will align
;; columns within a region, and delim-col.el, which helps to prettify
;; columns in a text region or rectangle;

;; csv.el by Ulf Jasper <ulf.jasper at web.de>, which provides
;; functions for reading/parsing comma-separated value files and is
;; available at http://de.geocities.com/ulf_jasper/emacs.html (and in
;; the gnu.emacs.sources archives).

;;; To do (maybe):

;; Make separators and quotes buffer-local and locally settable.
;; Support (La)TeX tables: set separator and comment; support record
;; end string.
;; Convert comma-separated to space- or tab-separated.

;;; Code:

(eval-when-compile (require 'cl-lib))

(defgroup CSV nil
  "Major mode for editing files of comma-separated value type."
  :group 'convenience)

(defvar csv-separator-chars nil
  "Field separators as a list of character.
Set by customizing `csv-separators' -- do not set directly!")

(defvar csv-separator-regexp nil
  "Regexp to match a field separator.
Set by customizing `csv-separators' -- do not set directly!")

(defvar csv--skip-chars nil
  "Char set used by `skip-chars-forward' etc. to skip fields.
Set by customizing `csv-separators' -- do not set directly!")

(defvar csv-font-lock-keywords nil
  "Font lock keywords to highlight the field separators in CSV mode.
Set by customizing `csv-separators' -- do not set directly!")

(defcustom csv-separators '("," "\t")
  "Field separators: a list of *single-character* strings.
For example: (\",\"), the default, or (\",\" \";\" \":\").
Neighbouring fields may be separated by any one of these characters.
The first is used when inserting a field separator into the buffer.
All must be different from the field quote characters, `csv-field-quotes'."
  ;; Suggested by Eckhard Neber <neber@mwt.e-technik.uni-ulm.de>
  :type '(repeat string)
  ;; FIXME: Character would be better, but in Emacs 21.3 does not display
  ;; correctly in a customization buffer.
  :set (lambda (variable value)
	 (mapc (lambda (x)
		 (if (/= (length x) 1)
		     (error "Non-single-char string %S" x))
                 (if (and (boundp 'csv-field-quotes)
                          (member x csv-field-quotes))
                     (error "%S is already a quote" x)))
	       value)
	 (custom-set-default variable value)
	 (setq csv-separator-chars (mapcar #'string-to-char value)
	       csv--skip-chars (apply #'concat "^\n" csv-separators)
	       csv-separator-regexp (apply #'concat `("[" ,@value "]"))
	       csv-font-lock-keywords
	       ;; NB: csv-separator-face variable evaluates to itself.
	       `((,csv-separator-regexp (0 'csv-separator-face))))))

(defcustom csv-field-quotes '("\"")
  "Field quotes: a list of *single-character* strings.
For example: (\"\\\"\"), the default, or (\"\\\"\" \"\\='\" \"\\=`\").
A field can be delimited by a pair of any of these characters.
All must be different from the field separators, `csv-separators'."
  :type '(repeat string)
  ;; Character would be better, but in Emacs 21 does not display
  ;; correctly in a customization buffer.
  :set (lambda (variable value)
	 (mapc (lambda (x)
		 (if (/= (length x) 1)
		     (error "Non-single-char string %S" x))
		 (if (member x csv-separators)
		     (error "%S is already a separator" x)))
	       value)
	 (when (boundp 'csv-mode-syntax-table)
	   ;; FIRST remove old quote syntax:
	   (with-syntax-table text-mode-syntax-table
	     (mapc (lambda (x)
		     (modify-syntax-entry
		      (string-to-char x)
		      (string (char-syntax (string-to-char x)))
		      ;; symbol-value to avoid compiler warning:
		      (symbol-value 'csv-mode-syntax-table)))
		   csv-field-quotes))
	   ;; THEN set new quote syntax:
	   (csv-set-quote-syntax value))
	 ;; BEFORE setting new value of `csv-field-quotes':
	 (custom-set-default variable value)))

(defun csv-set-quote-syntax (field-quotes)
  "Set syntax for field quote characters FIELD-QUOTES to be \"string\".
FIELD-QUOTES should be a list of single-character strings."
  (mapc (lambda (x)
	  (modify-syntax-entry
	   (string-to-char x) "\""
	   ;; symbol-value to avoid compiler warning:
	   (symbol-value 'csv-mode-syntax-table)))
	field-quotes))

(defvar csv-comment-start nil
  "String that starts a comment line, or nil if no comment syntax.
Such comment lines are ignored by CSV mode commands.
This variable is buffer local\; its default value is that of
`csv-comment-start-default'.  It is set by the function
`csv-set-comment-start' -- do not set it directly!")

(make-variable-buffer-local 'csv-comment-start)

(defcustom csv-comment-start-default "#"
  "String that starts a comment line, or nil if no comment syntax.
Such comment lines are ignored by CSV mode commands.
Default value of buffer-local variable `csv-comment-start'.
Changing this variable does not affect any existing CSV mode buffer."
  :type '(choice (const :tag "None" nil) string)
  :set (lambda (variable value)
	 (custom-set-default variable value)
	 (setq-default csv-comment-start value)))

(defcustom csv-align-style 'left
  "Aligned field style: one of `left', `centre', `right' or `auto'.
Alignment style used by `csv-align-mode' and `csv-align-fields'.
Auto-alignment means left align text and right align numbers."
  :type '(choice (const left) (const centre)
		 (const right) (const auto)))

(defcustom csv-align-padding 1
  "Aligned field spacing: must be a positive integer.
Number of spaces used by `csv-align-mode' and `csv-align-fields' after separators."
  :type 'integer)

(defcustom csv-header-lines 0
  "Header lines to skip when setting region automatically."
  :type 'integer)

(defcustom csv-invisibility-default t
  "If non-nil, make separators in aligned records invisible."
  :type 'boolean)

(defface csv-separator-face
  '((t :inherit escape-glyph))
  "CSV mode face used to highlight separators.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Mode definition, key bindings and menu
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defconst csv-mode-line-format
  '(csv-field-index-string ("" csv-field-index-string))
  "Mode line format string for CSV mode.")

(defvar csv-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(control ?c) (control ?v)] 'csv-toggle-invisibility)
    (define-key map [(control ?c) (control ?t)] 'csv-transpose)
    (define-key map [(control ?c) (control ?c)] 'csv-set-comment-start)
    (define-key map [(control ?c) (control ?u)] 'csv-unalign-fields)
    (define-key map [(control ?c) (control ?a)] 'csv-align-fields)
    (define-key map [(control ?c) (control ?z)] 'csv-yank-as-new-table)
    (define-key map [(control ?c) (control ?y)] 'csv-yank-fields)
    (define-key map [(control ?c) (control ?k)] 'csv-kill-fields)
    (define-key map [(control ?c) (control ?d)] 'csv-toggle-descending)
    (define-key map [(control ?c) (control ?r)] 'csv-reverse-region)
    (define-key map [(control ?c) (control ?n)] 'csv-sort-numeric-fields)
    (define-key map [(control ?c) (control ?s)] 'csv-sort-fields)
    map))

;;;###autoload
(define-derived-mode csv-mode text-mode "CSV"
  "Major mode for editing files of comma-separated value type.

CSV mode is derived from `text-mode', and runs `text-mode-hook' before
running `csv-mode-hook'.  It turns `auto-fill-mode' off by default.
CSV mode can be customized by user options in the CSV customization
group.  The separators are specified by the value of `csv-separators'.

CSV mode commands ignore blank lines and comment lines beginning with
the value of `csv-comment-start', which delimit \"paragraphs\".
\"Sexp\" is re-interpreted to mean \"field\", so that `forward-sexp'
\(\\[forward-sexp]), `kill-sexp' (\\[kill-sexp]), etc. all apply to fields.
Standard comment commands apply, such as `comment-dwim' (\\[comment-dwim]).

If `font-lock-mode' is enabled then separators, quoted values and
comment lines are highlighted using respectively `csv-separator-face',
`font-lock-string-face' and `font-lock-comment-face'.

The user interface (UI) for CSV mode commands is similar to that of
the standard commands `sort-fields' and `sort-numeric-fields', except
that if there is no prefix argument then the UI prompts for the field
index or indices.  In `transient-mark-mode' only: if the region is not
set then the UI attempts to set it to include all consecutive CSV
records around point, and prompts for confirmation; if there is no
prefix argument then the UI prompts for it, offering as a default the
index of the field containing point if the region was not set
explicitly.  The region set automatically is delimited by blank lines
and comment lines, and the number of header lines at the beginning of
the region given by the value of `csv-header-lines' are skipped.

Sort order is controlled by `csv-descending'.

CSV mode provides the following specific keyboard key bindings:

\\{csv-mode-map}"
  :group 'CSV
  ;; We used to `turn-off-auto-fill' here instead, but that's not very
  ;; effective since text-mode-hook is run afterwards anyway!
  (setq-local normal-auto-fill-function nil)
  ;; Set syntax for field quotes:
  (csv-set-quote-syntax csv-field-quotes)
  ;; Make sexp functions apply to fields:
  (set (make-local-variable 'forward-sexp-function) #'csv-forward-field)
  (csv-set-comment-start csv-comment-start)
  ;; Font locking -- separator plus syntactic:
  (setq font-lock-defaults '(csv-font-lock-keywords))
  (setq-local jit-lock-contextually nil) ;Each line should be independent.
  (if csv-invisibility-default (add-to-invisibility-spec 'csv))
  ;; Mode line to support `csv-field-index-mode':
  (set (make-local-variable 'mode-line-position)
       (pcase mode-line-position
         (`(,(or (pred consp) (pred stringp)) . ,_)
          `(,@mode-line-position ,csv-mode-line-format))
         (_ `("" ,mode-line-position ,csv-mode-line-format))))
  (set (make-local-variable 'truncate-lines) t)
  ;; Enable or disable `csv-field-index-mode' (could probably do this
  ;; a bit more efficiently):
  (csv-field-index-mode (symbol-value 'csv-field-index-mode)))

(defun csv-set-comment-start (string)
  "Set comment start for this CSV mode buffer to STRING.
It must be either a string or nil."
  (interactive
   (list (edit-and-eval-command
	  "Comment start (string or nil): " csv-comment-start)))
  ;; Paragraph means a group of contiguous records:
  (set (make-local-variable 'paragraph-separate) "[:space:]*$") ; White space.
  (set (make-local-variable 'paragraph-start) "\n");Must include \n explicitly!
  ;; Remove old comment-start/end if available
  (with-syntax-table text-mode-syntax-table
    (when comment-start
      (modify-syntax-entry (string-to-char comment-start)
			   (string (char-syntax (string-to-char comment-start)))
			   csv-mode-syntax-table))
    (modify-syntax-entry ?\n
			 (string (char-syntax ?\n))
			 csv-mode-syntax-table))
  (when string
    (setq paragraph-separate (concat paragraph-separate "\\|" string)
	  paragraph-start (concat paragraph-start "\\|" string))
    (set (make-local-variable 'comment-start) string)
    (modify-syntax-entry
     (string-to-char string) "<" csv-mode-syntax-table)
    (modify-syntax-entry ?\n ">" csv-mode-syntax-table))
  (setq csv-comment-start string))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.[Cc][Ss][Vv]\\'" . csv-mode))

(defvar csv-descending nil
  "If non-nil, CSV mode sort functions sort in order of descending sort key.
Usually they sort in order of ascending sort key.")

(defun csv-toggle-descending ()
  "Toggle `csv-descending'."
  (interactive)
  (setq csv-descending (not csv-descending))
  (message "Sort order is %sscending" (if csv-descending "de" "a")))

(defun csv-toggle-invisibility ()
  ;; FIXME: Make it into a proper minor mode?
  "Toggle `buffer-invisibility-spec'."
  (interactive)
  (if (memq 'csv buffer-invisibility-spec)
      (remove-from-invisibility-spec 'csv)
    (add-to-invisibility-spec 'csv))
  (message "Separators in aligned records will be %svisible \
\(after re-aligning if soft\)"
	   (if (memq 'csv buffer-invisibility-spec) "in" ""))
  (redraw-frame (selected-frame)))

(easy-menu-define
  csv-menu
  csv-mode-map
  "CSV major mode menu keymap"
  '("CSV"
    ["Sort By Field Lexicographically" csv-sort-fields :active t
     :help "Sort lines in region lexicographically by the specified field"]
    ["Sort By Field Numerically" csv-sort-numeric-fields :active t
     :help "Sort lines in region numerically by the specified field"]
    ["Reverse Order of Lines" csv-reverse-region :active t
     :help "Reverse the order of the lines in the region"]
    ["Use Descending Sort Order" csv-toggle-descending :active t
     :style toggle :selected csv-descending
     :help "If selected, use descending order when sorting"]
    "--"
    ["Kill Fields (Columns)" csv-kill-fields :active t
     :help "Kill specified fields of each line in the region"]
    ["Yank Fields (Columns)" csv-yank-fields :active t
     :help "Yank killed fields as specified field of each line in region"]
    ["Yank As New Table" csv-yank-as-new-table :active t
     :help "Yank killed fields as a new table at point"]
    ["Align Fields into Columns" csv-align-fields :active t
     :help "Align the start of every field of each line in the region"]
    ["Unalign Columns into Fields" csv-unalign-fields :active t
     :help "Undo soft alignment and optionally remove redundant white space"]
    ["Transpose Rows and Columns" csv-transpose :active t
     :help "Rewrite rows (which may have different lengths) as columns"]
    "--"
    ["Forward Field" forward-sexp :active t
     :help "Move forward across one field; with ARG, do it that many times"]
    ["Backward Field" backward-sexp :active t
     :help "Move backward across one field; with ARG, do it that many times"]
    ["Kill Field Forward" kill-sexp :active t
     :help "Kill field following cursor; with ARG, do it that many times"]
    ["Kill Field Backward" backward-kill-sexp :active t
     :help "Kill field preceding cursor; with ARG, do it that many times"]
    "--"
    ("Alignment Style"
     ["Left" (setq csv-align-style 'left) :active t
      :style radio :selected (eq csv-align-style 'left)
      :help "If selected, `csv-align' left aligns fields"]
     ["Centre" (setq csv-align-style 'centre) :active t
      :style radio :selected (eq csv-align-style 'centre)
      :help "If selected, `csv-align' centres fields"]
     ["Right" (setq csv-align-style 'right) :active t
      :style radio :selected (eq csv-align-style 'right)
      :help "If selected, `csv-align' right aligns fields"]
     ["Auto" (setq csv-align-style 'auto) :active t
      :style radio :selected (eq csv-align-style 'auto)
      :help "\
If selected, `csv-align' left aligns text and right aligns numbers"]
     )
    ["Set header line" csv-header-line :active t]
    ["Auto-(re)align fields" csv-align-mode
     :style toggle :selected csv-align-mode]
    ["Show Current Field Index" csv-field-index-mode :active t
     :style toggle :selected csv-field-index-mode
     :help "If selected, display current field index in mode line"]
    ["Make Separators Invisible" csv-toggle-invisibility :active t
     :style toggle :selected (memq 'csv buffer-invisibility-spec)
     :visible (not (tsv--mode-p))
     :help "If selected, separators in aligned records are invisible"]
    ["Set Buffer's Comment Start" csv-set-comment-start :active t
     :help "Set comment start string for this buffer"]
    ["Customize CSV Mode" (customize-group 'CSV) :active t
     :help "Open a customization buffer to change CSV mode options"]
    ))

(require 'sort)

(defsubst csv-not-looking-at-record ()
  "Return t if looking at blank or comment line, nil otherwise.
Assumes point is at beginning of line."
  (looking-at paragraph-separate))

(defun csv-interactive-args (&optional type)
  "Get arg or field(s) and region interactively, offering sensible defaults.
Signal an error if the buffer is read-only.
If TYPE is noarg then return a list (beg end).
Otherwise, return a list (arg beg end), where arg is:
  the raw prefix argument by default\;
  a single field index if TYPE is single\;
  a list of field indices or index ranges if TYPE is multiple.
Field defaults to the current prefix arg\; if not set, prompt user.

A field index list consists of positive or negative integers or ranges,
separated by any non-integer characters.  A range has the form m-n,
where m and n are positive or negative integers, m < n, and n defaults
to the last field index if omitted.

In transient mark mode, if the mark is not active then automatically
select and highlight CSV records around point, and query user.
The default field when read interactively is the current field."
  ;; Must be run interactively to activate mark!
  (let* ((arg current-prefix-arg) (default-field 1)
	 (region
	  (if (not (use-region-p))
	      ;; Set region automatically:
	      (save-excursion
                (if arg
                    (beginning-of-line)
                  (let ((lbp (line-beginning-position)))
                    (while (re-search-backward csv-separator-regexp lbp 1)
                      ;; Move as far as possible, i.e. to beginning of line.
                      (setq default-field (1+ default-field)))))
                (if (csv-not-looking-at-record)
                    (error "Point must be within CSV records"))
		(let ((startline (point)))
		  ;; Set mark at beginning of region:
		  (while (not (or (bobp) (csv-not-looking-at-record)))
		    (forward-line -1))
		  (if (csv-not-looking-at-record) (forward-line 1))
		  ;; Skip header lines:
		  (forward-line csv-header-lines)
		  (set-mark (point))	; OK since in save-excursion
		  ;; Move point to end of region:
		  (goto-char startline)
		  (beginning-of-line)
		  (while (not (or (eobp) (csv-not-looking-at-record)))
		    (forward-line 1))
		  ;; Show mark briefly if necessary:
		  (unless (and (pos-visible-in-window-p)
			       (pos-visible-in-window-p (mark)))
		    (exchange-point-and-mark)
		    (sit-for 1)
		    (exchange-point-and-mark))
		  (or (y-or-n-p "Region OK? ")
		      (error "Action aborted by user"))
		  (message nil)		; clear y-or-n-p message
		  (list (region-beginning) (region-end))))
	    ;; Use region set by user:
	    (list (region-beginning) (region-end)))))
    (setq default-field (number-to-string default-field))
    (cond
     ((eq type 'multiple)
      (if arg
	  ;; Ensure that field is a list:
	  (or (consp arg)
	      (setq arg (list (prefix-numeric-value arg))))
	;; Read field interactively, ignoring non-integers:
	(setq arg
	      (mapcar
	       (lambda (x)
		 (if (string-match "-" x 1) ; not first character
		     ;; Return a range as a pair - the cdr may be nil:
		     (let ((m (substring x 0 (match-beginning 0)))
			   (n (substring x (match-end 0))))
		       (cons (car (read-from-string m))
			     (and (not (string= n ""))
				  (car (read-from-string n)))))
		   ;; Return a number as a number:
		   (car (read-from-string x))))
	       (split-string
		(read-string
		 "Fields (sequence of integers or ranges): " default-field)
		"[^-+0-9]+")))))
     ((eq type 'single)
      (if arg
	  (setq arg (prefix-numeric-value arg))
	(while (not (integerp arg))
	  (setq arg (eval-minibuffer "Field (integer): " default-field))))))
    (if (eq type 'noarg) region (cons arg region))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Sorting by field
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun csv-nextrecfun ()
  "Called by `csv-sort-fields-1' with point at end of previous record.
It moves point to the start of the next record.
It should move point to the end of the buffer if there are no more records."
  (forward-line)
  (while (and (not (eobp)) (csv-not-looking-at-record))
    (forward-line)))

(defun csv-sort-fields-1 (field beg end startkeyfun endkeyfun)
  "Modified version of `sort-fields-1' that skips blank or comment lines.

FIELD is a single field index, and BEG and END specify the region to
sort.

STARTKEYFUN moves from the start of the record to the start of the key.
It may return either a non-nil value to be used as the key, or
else the key is the substring between the values of point after
STARTKEYFUN and ENDKEYFUN are called.  If STARTKEYFUN is nil, the key
starts at the beginning of the record.

ENDKEYFUN moves from the start of the sort key to the end of the sort key.
ENDKEYFUN may be nil if STARTKEYFUN returns a value or if it would be the
same as ENDRECFUN."
  (let ((tbl (syntax-table)))
    (if (zerop field) (setq field 1))
    (unwind-protect
	(save-excursion
	  (save-restriction
	    (narrow-to-region beg end)
	    (goto-char (point-min))
	    (set-syntax-table sort-fields-syntax-table)
	    (sort-subr csv-descending
		       'csv-nextrecfun 'end-of-line
		       startkeyfun endkeyfun)))
      (set-syntax-table tbl))))

(defun csv-sort-fields (field beg end)
  "Sort lines in region lexicographically by the ARGth field of each line.
If not set, the region defaults to the CSV records around point.
Fields are separated by `csv-separators' and null fields are allowed anywhere.
Field indices increase from 1 on the left or decrease from -1 on the right.
A prefix argument specifies a single field, otherwise prompt for field index.
Ignore blank and comment lines.  The variable `sort-fold-case'
determines whether alphabetic case affects the sort order.
When called non-interactively, FIELD is a single field index\;
BEG and END specify the region to sort."
  ;; (interactive "*P\nr")
  (interactive (csv-interactive-args 'single))
  (barf-if-buffer-read-only)
  (csv-sort-fields-1 field beg end
		     (lambda () (csv-sort-skip-fields field) nil)
		     (lambda () (skip-chars-forward csv--skip-chars))))

(defun csv-sort-numeric-fields (field beg end)
  "Sort lines in region numerically by the ARGth field of each line.
If not set, the region defaults to the CSV records around point.
Fields are separated by `csv-separators'.
Null fields are allowed anywhere and sort as zeros.
Field indices increase from 1 on the left or decrease from -1 on the right.
A prefix argument specifies a single field, otherwise prompt for field index.
Specified non-null field must contain a number in each line of the region,
which may begin with \"0x\" or \"0\" for hexadecimal and octal values.
Otherwise, the number is interpreted according to sort-numeric-base.
Ignore blank and comment lines.
When called non-interactively, FIELD is a single field index\;
BEG and END specify the region to sort."
  ;; (interactive "*P\nr")
  (interactive (csv-interactive-args 'single))
  (barf-if-buffer-read-only)
  (csv-sort-fields-1 field beg end
		 (lambda ()
		   (csv-sort-skip-fields field)
		   (let* ((case-fold-search t)
			  (base
			   (if (looking-at "\\(0x\\)[0-9a-f]\\|\\(0\\)[0-7]")
			       (cond ((match-beginning 1)
				      (goto-char (match-end 1))
				      16)
				     ((match-beginning 2)
				      (goto-char (match-end 2))
				      8)
				     (t nil)))))
		     (string-to-number (buffer-substring (point)
							 (save-excursion
							   (forward-sexp 1)
							   (point)))
				       (or base sort-numeric-base))))
		 nil))

(defun csv-reverse-region (beg end)
  "Reverse the order of the lines in the region.
This is just a CSV-mode style interface to `reverse-region', which is
the function that should be used non-interactively.  It takes two
point or marker arguments, BEG and END, delimiting the region."
  ;; (interactive "*P\nr")
  (interactive (csv-interactive-args 'noarg))
  (barf-if-buffer-read-only)
  (reverse-region beg end))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Moving by field
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsubst csv-end-of-field ()
  "Skip forward over one field."
  (skip-chars-forward " ")
  (if (eq (char-syntax (following-char)) ?\")
      (goto-char (scan-sexps (point) 1)))
  (skip-chars-forward csv--skip-chars))

(defsubst csv-beginning-of-field ()
  "Skip backward over one field."
  (skip-syntax-backward " ")
  (if (eq (char-syntax (preceding-char)) ?\")
      (goto-char (scan-sexps (point) -1)))
  (skip-chars-backward csv--skip-chars))

(defun csv-forward-field (arg)
  "Move forward across one field, cf. `forward-sexp'.
With ARG, do it that many times.  Negative arg -N means
move backward across N fields."
  (interactive "p")
  (if (< arg 0)
      (csv-backward-field (- arg))
    (while (>= (setq arg (1- arg)) 0)
      (if (or (bolp)
	      (when (and (not (eobp)) (eolp)) (forward-char) t))
	  (while (and (not (eobp)) (csv-not-looking-at-record))
	    (forward-line 1)))
      (if (memq (following-char) csv-separator-chars) (forward-char))
      (csv-end-of-field))))

(defun csv-backward-field (arg)
  "Move backward across one field, cf. `backward-sexp'.
With ARG, do it that many times.  Negative arg -N means
move forward across N fields."
  (interactive "p")
  (if (< arg 0)
      (csv-forward-field (- arg))
    (while (>= (setq arg (1- arg)) 0)
      (when (or (eolp)
		(when (and (not (bobp)) (bolp)) (backward-char) t))
	(while (progn
		 (beginning-of-line)
		 (csv-not-looking-at-record))
	  (backward-char))
	(end-of-line))
      (if (memq (preceding-char) csv-separator-chars) (backward-char))
      (csv-beginning-of-field))))

(defun csv-sort-skip-fields (n &optional yank)
  "Position point at the beginning of field N on the current line.
Fields are separated by `csv-separators'\; null terminal field allowed.
Assumes point is initially at the beginning of the line.
YANK non-nil allows N to be greater than the number of fields, in
which case extend the record as necessary."
  (if (> n 0)
      ;; Skip across N - 1 fields.
      (let ((i (1- n)))
	(while (> i 0)
	  (csv-end-of-field)
	  (if (eolp)
	      (if yank
		  (if (> i 1) (insert (car csv-separators)))
		(error "Line has too few fields: %s"
		       (buffer-substring
			(save-excursion (beginning-of-line) (point))
			(save-excursion (end-of-line) (point)))))
	    (forward-char))		; skip separator
	  (setq i (1- i))))
    (end-of-line)
    ;; Skip back across -N - 1 fields.
    (let ((i (1- (- n))))
      (while (> i 0)
	(csv-beginning-of-field)
	(if (bolp)
	    (error "Line has too few fields: %s"
		   (buffer-substring
		    (save-excursion (beginning-of-line) (point))
		    (save-excursion (end-of-line) (point)))))
	(backward-char)			; skip separator
	(setq i (1- i)))
      ;; Position at the front of the field
      ;; even if moving backwards.
      (csv-beginning-of-field))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Field index mode
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Based partly on paren.el

(defcustom csv-field-index-delay 0.125
  "Time in seconds to delay before updating field index display."
  :type '(number :tag "seconds"))

(defvar csv-field-index-idle-timer nil)

(defvar csv-field-index-string nil)
(make-variable-buffer-local 'csv-field-index-string)

(defvar csv-field-index-old nil)
(make-variable-buffer-local 'csv-field-index-old)

(define-minor-mode csv-field-index-mode
  "Toggle CSV-Field-Index mode.
With prefix ARG, turn CSV-Field-Index mode on if and only if ARG is positive.
Returns the new status of CSV-Field-Index mode (non-nil means on).
When CSV-Field-Index mode is enabled, the current field index appears in
the mode line after `csv-field-index-delay' seconds of Emacs idle time."
  :global t
  :init-value t		       ; for documentation, since default is t
  ;; This macro generates a function that first sets the mode
  ;; variable, then runs the following code, runs the mode hooks,
  ;; displays a message if interactive, updates the mode line and
  ;; finally returns the variable value.

  ;; First, always disable the mechanism (to avoid having two timers):
  (when csv-field-index-idle-timer
    (cancel-timer csv-field-index-idle-timer)
    (setq csv-field-index-idle-timer nil))
  ;; Now, if the mode is on and any buffer is in CSV mode then
  ;; re-initialize and enable the mechanism by setting up a new timer:
  (if csv-field-index-mode
      (if (memq t (mapcar (lambda (buffer)
			    (with-current-buffer buffer
			      (when (derived-mode-p 'csv-mode)
				(setq csv-field-index-string nil
				      csv-field-index-old nil)
				t)))
			  (buffer-list)))
	  (setq csv-field-index-idle-timer
		(run-with-idle-timer csv-field-index-delay t
				     #'csv-field-index)))
    ;; but if the mode is off then remove the display from the mode
    ;; lines of all CSV buffers:
    (mapc (lambda (buffer)
	    (with-current-buffer buffer
	      (when (derived-mode-p 'csv-mode)
		(setq csv-field-index-string nil
		      csv-field-index-old nil)
		(force-mode-line-update))))
	    (buffer-list))))

(defun csv--field-index ()
  (save-excursion
    (let ((lbp (line-beginning-position)) (field 1))
      (while (re-search-backward csv-separator-regexp lbp 'move)
	;; Move as far as possible, i.e. to beginning of line.
	(setq field (1+ field)))
      (unless (csv-not-looking-at-record) field))))

(defun csv-field-index ()
  "Construct `csv-field-index-string' to display in mode line.
Called by `csv-field-index-idle-timer'."
  (if (derived-mode-p 'csv-mode)
      (let ((field (csv--field-index)))
	(when (not (eq field csv-field-index-old))
	  (setq csv-field-index-old field
		csv-field-index-string
		(and field (format "F%d" field)))
	  (force-mode-line-update)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Killing and yanking fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar csv-killed-fields nil
  "A list of the fields or sub-records last killed by `csv-kill-fields'.")

(defun csv-kill-fields (fields beg end)
  "Kill specified fields of each line in the region.
If not set, the region defaults to the CSV records around point.
Fields are separated by `csv-separators' and null fields are allowed anywhere.
Field indices increase from 1 on the left or decrease from -1 on the right.
The fields are stored for use by `csv-yank-fields'.  Fields can be
specified in any order but are saved in increasing index order.
Ignore blank and comment lines.

When called interactively, a prefix argument specifies a single field,
otherwise prompt for a field list, which may include ranges in the form
m-n, where m < n and n defaults to the last field index if omitted.

When called non-interactively, FIELDS is a single field index or a
list of field indices, with ranges specified as (m.n) or (m), and BEG
and END specify the region to process."
  ;; (interactive "*P\nr")
  (interactive (csv-interactive-args 'multiple))
  (barf-if-buffer-read-only)
  ;; Kill the field(s):
  (setq csv-killed-fields nil)
  (save-excursion
    (save-restriction
      (narrow-to-region beg end)
      (goto-char (point-min))
      (if (or (cdr fields) (consp (car fields)))
	  (csv-kill-many-columns fields)
	(csv-kill-one-column (car fields)))))
  (setq csv-killed-fields (nreverse csv-killed-fields)))

(defun csv-kill-one-field (field)
  "Kill field with index FIELD in current line.
Return killed text.  Assumes point is at beginning of line."
  ;; Move to start of field to kill:
  (csv-sort-skip-fields field)
  ;; Kill to end of field (cf. `kill-region'):
  (prog1 (delete-and-extract-region
          (point)
          (progn (csv-end-of-field) (point)))
    (if (eolp)
        (unless (bolp) (delete-char -1)) ; Delete trailing separator at eol
      (delete-char 1))))                 ; or following separator otherwise.

(defun csv-kill-one-column (field)
  "Kill field with index FIELD in all lines in (narrowed) buffer.
Save killed fields in `csv-killed-fields'.
Assumes point is at `point-min'.  Called by `csv-kill-fields'.
Ignore blank and comment lines."
  (while (not (eobp))
    (or (csv-not-looking-at-record)
	(push (csv-kill-one-field field) csv-killed-fields))
    (forward-line)))

(defun csv-kill-many-columns (fields)
  "Kill several fields in all lines in (narrowed) buffer.
FIELDS is an unordered list of field indices.
Save killed fields in increasing index order in `csv-killed-fields'.
Assumes point is at `point-min'.  Called by `csv-kill-fields'.
Ignore blank and comment lines."
  (if (eolp) (error "First record is empty"))
  ;; Convert non-positive to positive field numbers:
  (let ((last 1) (f fields))
    (csv-end-of-field)
    (while (not (eolp))
      (forward-char)			; skip separator
      (csv-end-of-field)
      (setq last (1+ last)))	     ; last = # fields in first record
    (while f
      (cond ((consp (car f))
	     ;; Expand a field range: (m.n) -> m m+1 ... n-1 n.
	     ;; If n is nil then it defaults to the number of fields.
	     (let* ((range (car f)) (cdrf (cdr f))
		    (m (car range)) (n (cdr range)))
	       (if (< m 0) (setq m (+ m last 1)))
	       (if n
		   (if (< n 0) (setq n (+ n last 1)))
		 (setq n last))
	       (setq range (list n))
	       (while (> n m) (push (setq n (1- n)) range))
	       (setcar f (car range))
	       (setcdr f (cdr range))
	       (setcdr (setq f (last range)) cdrf)))
	    ((zerop (car f)) (setcar f 1))
	    ((< (car f) 0) (setcar f (+ f last 1))))
      (setq f (cdr f))))
  (goto-char (point-min))
  ;; Kill from right to avoid miscounting:
  (setq fields (sort fields '>))
  (while (not (eobp))
    (or (csv-not-looking-at-record)
	(let ((fields fields) killed-fields field)
	  (while fields
	    (setq field (car fields)
		  fields (cdr fields))
	    (beginning-of-line)
	    (push (csv-kill-one-field field) killed-fields))
	  (push (mapconcat #'identity killed-fields (car csv-separators))
		csv-killed-fields)))
    (forward-line)))

(defun csv-yank-fields (field beg end)
  "Yank fields as the ARGth field of each line in the region.
ARG may be arbitrarily large and records are extended as necessary.
If not set, the region defaults to the CSV records around point\;
if point is not in a CSV record then offer to yank as a new table.
The fields yanked are those last killed by `csv-kill-fields'.
Fields are separated by `csv-separators' and null fields are allowed anywhere.
Field indices increase from 1 on the left or decrease from -1 on the right.
A prefix argument specifies a single field, otherwise prompt for field index.
Ignore blank and comment lines.  When called non-interactively, FIELD
is a single field index\; BEG and END specify the region to process."
  ;; (interactive "*P\nr")
  (interactive (condition-case err
		   (csv-interactive-args 'single)
		 (error (list nil nil err))))
  (barf-if-buffer-read-only)
  (if (null beg)
      (if (y-or-n-p (concat (error-message-string end)
			    ".  Yank as a new table? "))
	  (csv-yank-as-new-table)
	(error (error-message-string end)))
    (if (<= field 0) (setq field (1+ field)))
    (save-excursion
      (save-restriction
	(narrow-to-region beg end)
	(goto-char (point-min))
	(let ((fields csv-killed-fields))
	  (while (not (eobp))
	    (unless (csv-not-looking-at-record)
	      ;; Yank at start of specified field if possible,
	      ;; otherwise yank at end of record:
	      (if (zerop field)
		  (end-of-line)
		(csv-sort-skip-fields field 'yank))
	      (and (eolp) (insert (car csv-separators)))
	      (when fields
		(insert (car fields))
		(setq fields (cdr fields)))
	      (or (eolp) (insert (car csv-separators))))
	    (forward-line)))))))

(defun csv-yank-as-new-table ()
  "Yank fields as a new table starting at point.
The fields yanked are those last killed by `csv-kill-fields'."
  (interactive "*")
  (let ((fields csv-killed-fields))
    (while fields
      (insert (car fields) ?\n)
      (setq fields (cdr fields)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Aligning fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun csv--make-overlay (beg end &optional buffer front-advance rear-advance props)
  (let ((o (make-overlay beg end buffer front-advance rear-advance)))
    (overlay-put o 'csv t)
    (while props
      (overlay-put o (pop props) (pop props)))
    o))

(defun csv--delete-overlay (o)
  (and (overlay-get o 'csv) (delete-overlay o)))

(defun csv--column-widths (beg end)
  "Return a list of two lists (COLUMN-WIDTHS FIELD-WIDTHS).
COLUMN-WIDTHS is a list of elements (WIDTH START END)
indicating the widths of the columns after point (and the position of the
widest field that determined the overall width).
FIELD-WIDTHS contains the widths of each individual field after
point."
  (let ((column-widths '())
        (field-widths '()))
    (goto-char beg)
    ;; Construct list of column widths:
    (while (< (point) end)              ; for each record...
      (or (csv-not-looking-at-record)
          (let ((w column-widths)
                (col (current-column))
                (beg (point))
                field-width)
            (while (not (eolp))
              (csv-end-of-field)
              (setq field-width (- (current-column) col))
              (push field-width field-widths)
              (if w
                  (if (> field-width (caar w))
                      (setcar w (list field-width beg (point))))
                (setq w (list (list field-width beg (point)))
                      column-widths (nconc column-widths w)))
              (or (eolp) (forward-char)) ; Skip separator.
              (setq w (cdr w) col (current-column) beg (point)))))
      (forward-line))
    (list column-widths (nreverse field-widths))))

(defun csv-align-fields (hard beg end)
  "Align all the fields in the region to form columns.
The alignment style is specified by `csv-align-style'.  The number of
spaces specified by `csv-align-padding' appears after each separator.
Use soft alignment done by displaying virtual white space after the
separators unless invoked with an argument, in which case insert real
space characters into the buffer after the separators.
Unalign first (see `csv-unalign-fields').  Ignore blank and comment lines.

In hard-aligned records, separators become invisible whenever
`buffer-invisibility-spec' is non-nil.  In soft-aligned records, make
separators invisible if and only if `buffer-invisibility-spec' is
non-nil when the records are aligned\; this can be changed only by
re-aligning.  \(Unaligning always makes separators visible.)

When called non-interactively, use hard alignment if HARD is non-nil\;
BEG and END specify the region to align.
If there is no selected region, default to the whole buffer."
  (interactive (cons current-prefix-arg
                     (if (use-region-p)
                         (list (region-beginning) (region-end))
                       (list (point-min) (point-max)))))
  ;; FIXME: Use csv--jit-align when applicable!
  (setq end (copy-marker end))
  (csv-unalign-fields hard beg end) ; If hard then barfs if buffer read only.
  (save-excursion
    (pcase-let ((`(,column-widths ,field-widths) (csv--column-widths beg end)))
      (save-restriction
        (narrow-to-region beg end)
        (set-marker end nil)

	;; Align fields:
	(goto-char (point-min))
	(while (not (eobp))		; for each record...
	  (unless (csv-not-looking-at-record)
            (let ((w column-widths)
                  (column 0))    ;Desired position of left-side of this column.
              (while (and w (not (eolp)))
                (let* ((beg (point))
                       (align-padding (if (bolp) 0 csv-align-padding))
                       (left-padding 0) (right-padding 0)
                       (field-width (pop field-widths))
                       (column-width (car (pop w)))
                       (x (- column-width field-width))) ; Required padding.
                  (csv-end-of-field)
                  (set-marker end (point)) ; End of current field.
                  ;; beg = beginning of current field
                  ;; end = (point) = end of current field

                  ;; Compute required padding:
                  (cond
                   ((eq csv-align-style 'left)
                    ;; Left align -- pad on the right:
                    (setq left-padding align-padding
                          right-padding x))
                   ((eq csv-align-style 'right)
                    ;; Right align -- pad on the left:
                    (setq left-padding (+ align-padding x)))
                   ((eq csv-align-style 'auto)
                    ;; Auto align -- left align text, right align numbers:
                    (if (string-match "\\`[-+.[:digit:]]+\\'"
                                      (buffer-substring beg (point)))
                        ;; Right align -- pad on the left:
                        (setq left-padding (+ align-padding x))
                      ;; Left align -- pad on the right:
                      (setq left-padding align-padding
                            right-padding x)))
                   ((eq csv-align-style 'centre)
                    ;; Centre -- pad on both left and right:
                    (let ((y (/ x 2)))  ; truncated integer quotient
                      (setq left-padding (+ align-padding y)
                            right-padding (- x y)))))

                  (cond
                   (hard ;; Hard alignment...
                    (when (> left-padding 0) ; Pad on the left.
                      ;; Insert spaces before field:
                      (if (= beg end)   ; null field
                          (insert (make-string left-padding ?\ ))
                        (goto-char beg) ; beginning of current field
                        (insert (make-string left-padding ?\ ))
                        (goto-char end))) ; end of current field
                    (unless (eolp)
                      (if (> right-padding 0) ; pad on the right
                          ;; Insert spaces after field:
                          (insert (make-string right-padding ?\ )))
                      ;; Make separator (potentially) invisible;
                      ;; in Emacs 21.3, neighbouring overlays
                      ;; conflict, so use the following only
                      ;; with hard alignment:
		      (csv--make-overlay (point) (1+ (point)) nil t nil
					 '(invisible csv evaporate t))
                      (forward-char)))  ; skip separator

                   ;; Soft alignment...
                   ((or (memq 'csv buffer-invisibility-spec)
                        ;; For TSV, hidden or not doesn't make much difference,
                        ;; but the behavior is slightly better when we "hide"
                        ;; the TABs with a `display' property than if we add
                        ;; before/after-strings.
                        (tsv--mode-p))

                    ;; Hide separators...
                    ;; Merge right-padding from previous field
                    ;; with left-padding from this field:
                    (if (zerop column)
                        (when (> left-padding 0)
                          ;; Display spaces before first field
                          ;; by overlaying first character:
			  (csv--make-overlay
			   beg (1+ beg) nil nil nil
			   `(before-string ,(make-string left-padding ?\ ))))
                      ;; Display separator as spaces:
                      (with-silent-modifications
                        (put-text-property
                         (1- beg) beg
                         'display `(space :align-to
                                          ,(+ left-padding column)))))
                    (unless (eolp) (forward-char)) ; Skip separator.
                    (setq column (+ column column-width align-padding)))

                   (t ;; Do not hide separators...
                    (let ((overlay (csv--make-overlay beg (point) nil nil t)))
                      (when (> left-padding 0) ; Pad on the left.
                        ;; Display spaces before field:
                        (overlay-put overlay 'before-string
                                     (make-string left-padding ?\ )))
                      (unless (eolp)
                        (if (> right-padding 0) ; Pad on the right.
                            ;; Display spaces after field:
                            (overlay-put
                             overlay
                             'after-string (make-string right-padding ?\ )))
                        (forward-char)))) ; Skip separator.

                   )))))
	  (forward-line)))))
  (set-marker end nil))

(defun csv-unalign-fields (hard beg end)
  "Undo soft alignment and optionally remove redundant white space.
Undo soft alignment introduced by `csv-align-fields'.  If invoked with
an argument then also remove all spaces and tabs around separators.
Also make all invisible separators visible again.
Ignore blank and comment lines.  When called non-interactively, remove
spaces and tabs if HARD non-nil\; BEG and END specify region to unalign.
If there is no selected region, default to the whole buffer."
  (interactive (cons current-prefix-arg
                     (if (use-region-p)
                         (list (region-beginning) (region-end))
                       (list (point-min) (point-max)))))
  ;; Remove any soft alignment:
  (mapc #'csv--delete-overlay (overlays-in beg end))
  (with-silent-modifications
    (remove-list-of-text-properties beg end '(display invisible)))
  (when hard
    (barf-if-buffer-read-only)
    ;; Remove any white-space padding around separators:
    (save-excursion
      (save-restriction
	(narrow-to-region beg end)
	(goto-char (point-min))
	(while (not (eobp))
	  (or (csv-not-looking-at-record)
	      (while (not (eolp))
		;; Delete horizontal white space forward:
		;; (delete-horizontal-space)
		;; This relies on left-to-right argument evaluation;
		;; see info node (elisp) Function Forms.
		(delete-region (point)
			       (+ (point) (skip-chars-forward " \t")))
		(csv-end-of-field)
		;; Delete horizontal white space backward:
		;; (delete-horizontal-space t)
		(delete-region (point)
			       (+ (point) (skip-chars-backward " \t")))
		(or (eolp) (forward-char))))
	  (forward-line))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Transposing rows and columns
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun csv-transpose (beg end)
  "Rewrite rows (which may have different lengths) as columns.
Null fields are introduced as necessary within records but are
stripped from the ends of records.  Preserve soft alignment.
This function is its own inverse.  Ignore blank and comment lines.
When called non-interactively, BEG and END specify region to process."
  ;; (interactive "*P\nr")
  (interactive (csv-interactive-args 'noarg))
  (barf-if-buffer-read-only)
  (save-excursion
    (save-restriction
      (narrow-to-region beg end)
      (goto-char (point-min))
      ;; Delete rows and collect them as a reversed list of lists of
      ;; fields, skipping comment and blank lines:
      (let ((sep (car csv-separators))
	    (align (overlays-in beg end))
	    rows columns)
	;; Remove soft alignment if necessary:
	(when align
	  (mapc #'csv--delete-overlay align)
	  (setq align t))
	(while (not (eobp))
	  (if (csv-not-looking-at-record)
	      ;; Skip blank and comment lines:
	      (forward-line)
	    (let ((lep (line-end-position)))
	      (push
	       (split-string
		(buffer-substring-no-properties (point) lep)
		csv-separator-regexp)
	       rows)
	      (delete-region (point) lep)
	      (or (eobp) (delete-char 1)))))
	;; Rows must have monotonic decreasing lengths to be
	;; transposable, so ensure this by padding with null fields.
	;; rows is currently a reversed list of field lists, which
	;; must therefore have monotonic increasing lengths.
	(let ((oldlen (length (car rows))) newlen
	      (r (cdr rows)))
	  (while r
	    (setq newlen (length (car r)))
	    (if (< newlen oldlen)
		(nconc (car r) (make-list (- oldlen newlen) nil))
	      (setq oldlen newlen))
	    (setq r (cdr r))))
	;; Collect columns as a reversed list of lists of fields:
	(while rows
	  (let (column (r rows) row)
	    (while r
	      (setq row (car r))
	      ;; Provided it would not be a trailing null field, push
	      ;; field onto column:
	      (if (or column (string< "" (car row)))
		  (push (car row) column))
	      ;; Pop field off row:
	      (setcar r (cdr row))
	      ;; If row is now empty then remove it:
	      (or (car r) (setq rows (cdr rows)))
	      (setq r (cdr r)))
	    (push column columns)))
	;; Insert columns into buffer as rows:
	(setq columns (nreverse columns))
	(while columns
	  (insert (mapconcat #'identity (car columns) sep) ?\n)
	  (setq columns (cdr columns)))
	;; Re-do soft alignment if necessary:
	(if align (csv-align-fields nil (point-min) (point-max)))))))

(defvar-local csv--header-line nil)
(defvar-local csv--header-hscroll nil)
(defvar-local csv--header-string nil)

(defun csv-header-line (&optional use-current-line)
  "Set/unset the header line.
If the optional prefix arg USE-CURRENT-LINE is nil, use the first line
as the header line.
If there is already a header line, then unset the header line."
  (interactive "P")
  (if csv--header-line
      (progn
        (delete-overlay csv--header-line)
        (setq csv--header-line nil)
        (kill-local-variable 'header-line-format))
    (save-excursion
      (unless use-current-line (goto-char (point-min)))
      (setq csv--header-line (make-overlay (line-beginning-position)
                                           (line-end-position)
                                           nil nil t))
      (overlay-put csv--header-line 'modification-hooks
                   '(csv--header-flush)))
    (csv--header-flush)
    (setq header-line-format
          '(:eval (csv--header-string)))))

(defun csv--header-flush (&rest _)
  ;; Force re-computation of the header-line.
  (setq csv--header-hscroll nil))

(defun csv--header-string ()
  ;; FIXME: Won't work with multiple windows showing that same buffer.
  (if (eql (window-hscroll) csv--header-hscroll)
      csv--header-string
    (setq csv--header-hscroll (window-hscroll))
    (setq csv--header-string
          (csv--compute-header-string))))

(defun csv--compute-header-string ()
  (with-demoted-errors "csv--compute-header-string %S"
    (save-excursion
      (goto-char (overlay-start csv--header-line))
      ;; Re-set the line-end-position, just in case.
      (move-overlay csv--header-line (point) (line-end-position))
      (jit-lock-fontify-now (point) (line-end-position))
      ;; Not sure why it is sometimes nil!
      (move-to-column (or csv--header-hscroll 0))
      (let ((str (buffer-substring (point) (line-end-position)))
            (i 0))
        (while (and i (< i (length str)))
          (let ((prop (get-text-property i 'display str)))
            (and (eq (car-safe prop) 'space)
                 (eq (car-safe (cdr prop)) :align-to)
                 (let* ((x (nth 2 prop))
                        (nexti (next-single-property-change i 'display str))
                        (newprop
                         `(space :align-to
                                 ,(if (numberp x)
                                      (- x (or csv--header-hscroll 0))
                                    `(- ,x csv--header-hscroll)))))
                   (put-text-property i (or nexti (length str))
                                      'display newprop str)
                   (setq i nexti))))
          (setq i (next-single-property-change i 'display str)))
        (concat (propertize " " 'display '((space :align-to 0))) str)))))

;;; Auto-alignment

(defcustom csv-align-max-width 40
  "Maximum width of a column in `csv-align-mode'.
This does not apply to the last column (for which the usual `truncate-lines'
setting works better)."
  :type 'integer)

(defvar-local csv--config-column-widths nil
  "Settings per column, stored as a list indexed by the column.")

(defun csv-align--set-column (column value)
  (let ((len (length csv--config-column-widths)))
    (if (< len column)
        (setq csv--config-column-widths
              (nconc csv--config-column-widths (make-list (- column len) nil))))
    (setf (nth (1- column) csv--config-column-widths) value)))

(defun csv-align-set-column-width (column width)
  "Set the max WIDTH to use for COLUMN."
  (interactive
   (let* ((field (or (csv--field-index) 1))
          (curwidth (nth (1- field) csv--config-column-widths)))
     (list field
           (cond
            ((numberp current-prefix-arg)
             current-prefix-arg)
            (current-prefix-arg
             (read-number (format "Column width (for field %d): " field)
                          curwidth))
            (t (if curwidth nil (csv--ellipsis-width)))))))
  (when (eql width csv-align-max-width)
    (setq width nil))
  (csv-align--set-column column width)
  (jit-lock-refontify))

(defvar-local csv--jit-columns nil)

(defun csv--jit-merge-columns (column-widths)
  ;; FIXME: The incremental update (delayed by jit-lock-context-time) of column
  ;; width is a bit jarring at times.  It's OK while scrolling or when
  ;; extending a column, but not right when enabling the csv-align-mode or
  ;; when shortening the longest field (or deleting the line containing it),
  ;; because in that case we have *several* cascaded updates, e.g.:
  ;; - Remove the line with the longest field of column N.
  ;; - Edit some line: this line is updated as if its field was the widest,
  ;;   hence its subsequent fields are too much to the left.
  ;; - The rest is updated starting from the first few lines (according
  ;;   to jit-lock-chunk-size).
  ;; - After the first few lines, come the next set of few lines,
  ;;   which may cause the previous few lines to need refresh again.
  ;; - etc.. until arriving again at the edited line which is re-aligned
  ;;   again.
  ;; - etc.. until the end of the windows, potentially causing yet more
  ;;   refreshes as we discover yet-wider fields for this column.
  (let ((old-columns csv--jit-columns)
        (changed nil))
    (while (and old-columns column-widths)
      (when (or (> (caar column-widths) (caar old-columns))
                ;; Apparently modification-hooks aren't run when the
                ;; whole text containing the overlay is deleted (e.g.
                ;; the whole line), so detect this case here.
                ;; It's a bit too late, but better than never.
                (null (overlay-buffer (cdar old-columns))))
        (setq changed t) ;; Return non-nil if some existing column changed.
        (pcase-let ((`(,width ,beg ,end) (car column-widths)))
          (setf (caar old-columns) width)
          (move-overlay (cdar old-columns) beg end)))
      (setq old-columns (cdr old-columns))
      (setq column-widths (cdr column-widths)))
    (when column-widths
      ;; New columns appeared.
      (setq csv--jit-columns
            (nconc csv--jit-columns
                   (mapcar (lambda (x)
                             (pcase-let*
                                 ((`(,width ,beg ,end) x)
                                  (ol (make-overlay beg end)))
                               (overlay-put ol 'csv-width t)
                               (overlay-put ol 'evaporate t)
                               (overlay-put ol 'modification-hooks
                                            (list #'csv--jit-width-change))
                               (cons width ol)))
                           column-widths))))
    changed))

(defun csv--jit-width-change (ol after _beg _end &optional len)
  (when (and after (> len 0))
    ;; (let ((x (rassq ol csv--jit-columns)))
    ;;   (when x (setf (car x) -1)))
    (delete-overlay ol)))

(defun csv--jit-unalign (beg end)
  (remove-text-properties beg end
                          '(display nil csv--jit nil invisible nil
                            cursor-sensor-functions nil csv--revealed nil))
  (remove-overlays beg end 'csv--jit t))

(defun csv--jit-flush (beg end)
  "Cause all the buffer (except for the BEG...END region) to be re-aligned."
  (cl-assert (>= end beg))
  ;; The buffer shouldn't have changed since beg/end were computed,
  ;; but just in case, let's make sure they're still sane.
  (when (< beg (point-min))
    (setq beg (point-min) end (max end beg)))
  (when (< (point-max) end)
    (setq end (point-max) beg (min end beg)))
  (let ((pos (point-min)))
    (while (and (< pos beg)
                (setq pos (text-property-any pos beg 'csv--jit t)))
      (jit-lock-refontify
       pos (setq pos (or (text-property-any pos beg 'csv--jit nil) beg))))
    (setq pos end)
    (while (and (< pos (point-max))
                (setq pos (text-property-any pos (point-max) 'csv--jit t)))
      (jit-lock-refontify
       pos (setq pos (or (text-property-any pos (point-max) 'csv--jit nil)
                         (point-max))))))
  (csv--header-flush))

(defun csv--ellipsis-width ()
  (let ((ellipsis
         (when standard-display-table
           (display-table-slot standard-display-table
                               'selective-display))))
    (if ellipsis (length ellipsis) 3)))

(defun csv-align--cursor-truncated (window oldpos dir)
  ;; FIXME: Neither the `entered' nor the `left' event are guaranteed
  ;; to be sent, and for the `left' case, even when we do get called,
  ;; it may be unclear where the revealed text was (it's somewhere around
  ;; `oldpos', but that position can be stale).
  ;; Worse, if we have several windows displaying the buffer, when one
  ;; cursor leaves we may need to keep the text revealed because of
  ;; another window's cursor.
  (let* ((prop (if (eq dir 'entered) 'invisible 'csv--revealed))
         (pos (cond
               ((eq dir 'entered) (window-point window))
               (t (max (point-min)
                       (min (point-max)
                            (or oldpos (window-point window)))))))
         (start (cond
                 ((and (> pos (point-min))
                       (eq (get-text-property (1- pos) prop) 'csv-truncate))
                  (or (previous-single-property-change pos prop) (point-min)))
                 (t pos)))
         (end (if (eq (get-text-property pos prop) 'csv-truncate)
                  (or (next-single-property-change pos prop) (point-max))
                pos)))
    (unless (eql start end)
      (with-silent-modifications
        (put-text-property start end
                           (if (eq dir 'entered) 'csv--revealed 'invisible)
                           'csv-truncate)
        (remove-text-properties start end (list prop))))))

(defun csv--jit-align (beg end)
  (save-excursion
    ;; This is run with inhibit-modification-hooks set, so the overlays'
    ;; modification-hook doesn't work :-(
    (and csv--header-line
         (<= beg (overlay-end csv--header-line))
         (>= end (overlay-start csv--header-line))
         (csv--header-flush))
    ;; First, round up to a whole number of lines.
    (goto-char end)
    (unless (bolp) (forward-line 1) (setq end (point)))
    (goto-char beg)
    (unless (bolp) (forward-line 1) (setq beg (point)))
    (csv--jit-unalign beg end)
    (put-text-property beg end 'csv--jit t)

    (pcase-let* ((`(,column-widths ,field-widths) (csv--column-widths beg end))
                 (changed (csv--jit-merge-columns column-widths))
                 (ellipsis-width (csv--ellipsis-width)))
      (when changed
        ;; Do it after the current redisplay is over.
        (run-with-timer jit-lock-context-time nil #'csv--jit-flush beg end))

      ;; Align fields:
      (goto-char beg)
      (while (< (point) end)
	(unless (csv-not-looking-at-record)
          (let ((w csv--jit-columns)
                (widths-config csv--config-column-widths)
                (column 0))      ;Desired position of left-side of this column.
            (while (and w (not (eolp)))
              (let* ((field-beg (point))
                     (width-config (pop widths-config))
                     (align-padding (if (bolp) 0 csv-align-padding))
                     (left-padding 0) (right-padding 0)
                     (field-width (pop field-widths))
                     (column-width
                      (min (car (pop w))
                           (or width-config
                               ;; Don't apply csv-align-max-width
                               ;; to the last field!
                               (if w csv-align-max-width
                                 most-positive-fixnum))))
                     (x (- column-width field-width)) ; Required padding.
                     (truncate nil))
                (csv-end-of-field)
                ;; beg = beginning of current field
                ;; end = (point) = end of current field
                (when (< x 0)
                  (setq truncate (max column
                                      (+ column column-width
                                         align-padding (- ellipsis-width))))
                  (setq x 0))
                ;; Compute required padding:
                (pcase csv-align-style
                  ('left
                   ;; Left align -- pad on the right:
                   (setq left-padding align-padding
                         right-padding x))
                  ('right
                   ;; Right align -- pad on the left:
                   (setq left-padding (+ align-padding x)))
                  ('auto
                   ;; Auto align -- left align text, right align numbers:
                   (if (string-match "\\`[-+.[:digit:]]+\\'"
                                     (buffer-substring field-beg (point)))
                       ;; Right align -- pad on the left:
                       (setq left-padding (+ align-padding x))
                     ;; Left align -- pad on the right:
                     (setq left-padding align-padding
                           right-padding x)))
                  ('centre
                   ;; Centre -- pad on both left and right:
                   (let ((y (/ x 2)))   ; truncated integer quotient
                     (setq left-padding (+ align-padding y)
                           right-padding (- x y)))))

                (cond

                 ((or (memq 'csv buffer-invisibility-spec)
                      ;; For TSV, hidden or not doesn't make much difference,
                      ;; but the behavior is slightly better when we "hide"
                      ;; the TABs with a `display' property than if we add
                      ;; before/after-strings.
                      (tsv--mode-p))

                  ;; Hide separators...
                  ;; Merge right-padding from previous field
                  ;; with left-padding from this field:
                  (if (zerop column)
                      (when (> left-padding 0)
                        ;; Display spaces before first field
                        ;; by overlaying first character:
			(csv--make-overlay
			 field-beg (1+ field-beg) nil nil nil
			 `(before-string ,(make-string left-padding ?\ )
			                 csv--jit t)))
                    ;; Display separator as spaces:
                    (with-silent-modifications
                      (put-text-property
                       (1- field-beg) field-beg
                       'display `(space :align-to
                                        ,(+ left-padding column))))))

                 (t ;; Do not hide separators...
                  (let ((overlay (csv--make-overlay field-beg (point)
                                                    nil nil t
                                                    '(csv--jit t))))
                    (when (> left-padding 0) ; Pad on the left.
                      ;; Display spaces before field:
                      (overlay-put overlay 'before-string
                                   (make-string left-padding ?\ )))
                    (unless (eolp)
                      (if (> right-padding 0) ; Pad on the right.
                          ;; Display spaces after field:
                          (overlay-put
                           overlay
                           'after-string (make-string right-padding ?\ )))))))
                (setq column (+ column column-width align-padding))
                ;; Do it after applying the property, so `move-to-column' can
                ;; take it into account.
                (when truncate
                  (let ((trunc-pos
                         (save-excursion
                           ;; ¡¡ BIG UGLY HACK !!
                           ;; `current-column' and `move-to-column' count
                           ;; text hidden with an ellipsis "as if" it were
                           ;; fully visible, which is completely wrong here,
                           ;; so circumvent this by temporarily pretending
                           ;; that `csv-truncate' is fully invisible (which
                           ;; isn't quite right either, but should work
                           ;; just well enough for us here).
                           (let ((buffer-invisibility-spec
                                  buffer-invisibility-spec))
                             (add-to-invisibility-spec 'csv-truncate)
                             (move-to-column truncate))
                           (point))))
                    (put-text-property trunc-pos (point)
                                       'invisible 'csv-truncate)
                    (when (> (- (point) trunc-pos) 1)
                      ;; Arrange to temporarily untruncate the string when
                      ;; cursor moves into it.
                      ;; FIXME: This only works if
                      ;; `global-disable-point-adjustment' is non-nil!
                      ;; Arguably this should be fixed by making
                      ;; point-adjustment code pay attention to
                      ;; cursor-sensor-functions!
                      (put-text-property
                       (1+ trunc-pos) (point)
                       'cursor-sensor-functions
                       (list #'csv-align--cursor-truncated)))))
                (unless (eolp) (forward-char)) ; Skip separator.
                ))))
	(forward-line)))
    `(jit-lock-bounds ,beg . ,end)))

(define-minor-mode csv-align-mode
  "Align columns on the fly."
  :global nil
  (csv-unalign-fields nil (point-min) (point-max)) ;Just in case.
  (cond
   (csv-align-mode
    (add-to-invisibility-spec '(csv-truncate . t))
    (kill-local-variable 'csv--jit-columns)
    (cursor-sensor-mode 1)
    (jit-lock-register #'csv--jit-align)
    (jit-lock-refontify))
   (t
    (remove-from-invisibility-spec '(csv-truncate . t))
    (jit-lock-unregister #'csv--jit-align)
    (csv--jit-unalign (point-min) (point-max))))
  (csv--header-flush))

;;; TSV support

;; Since "the" CSV format is really a bunch of different formats, it includes
;; TSV as a subcase, but this subcase is sufficiently interesting that it has
;; its own mime-type and mostly standard file extension, also it suffers
;; less from the usual quoting problems of CSV (because the only problematic
;; chars are LF and TAB, really, which are much less common inside fields than
;; commas, space, and semi-colons) so it's "better behaved".

(defvar tsv-mode-syntax-table
  ;; Inherit from `text-mode-syntax-table' rather than from
  ;; `csv-mode-syntax-table' so as not to inherit the
  ;; `csv-field-quotes' settings.
  (let ((st (make-syntax-table text-mode-syntax-table)))
    st))

(defvar tsv-mode-map
  (let ((map (make-sparse-keymap)))
    ;; In `tsv-mode', the `csv-invisibility-default/csv-toggle-invisibility'
    ;; business doesn't make much sense.
    (define-key map [remap csv-toggle-invisibility] #'undefined)
    map))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.tsv\\'" . tsv-mode))

(defun tsv--mode-p ()
  (equal csv-separator-chars '(?\t)))

;;;###autoload
(define-derived-mode tsv-mode csv-mode "TSV"
  "Major mode for editing files of tab-separated value type."
  :group 'CSV
  ;; In TSV we know TAB is the only possible separator.
  (setq-local csv-separators '("\t"))
  ;; FIXME: Copy&pasted from the `:set'ter of csv-separators!
  (setq-local csv-separator-chars '(?\t))
  (setq-local csv--skip-chars "^\n\t")
  (setq-local csv-separator-regexp "\t")
  (setq-local csv-font-lock-keywords
	      ;; NB: csv-separator-face variable evaluates to itself.
	      `((,csv-separator-regexp (0 'csv-separator-face))))

  ;; According to wikipedia, TSV doesn't use quotes but uses backslash escapes
  ;; of the form \n, \t, \r, and \\ instead.
  (setq-local csv-field-quotes nil))

;;;; ChangeLog:

;; 2019-10-22  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el (csv-align--cursor-truncated): Fix C-e
;; 	case
;; 
;; 2019-10-22  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el: Auto-shorten columns as well
;; 
;; 	(csv--column-widths): Also return the position of the widest field in 
;; 	each column.
;; 	(csv-align-fields, csv--jit-align): Update accordingly.
;; 	(csv--jit-width-change): New function.
;; 	(csv--jit-merge-columns): Use it on overlays placed on the widest field 
;; 	of each column, to detect when they're shortened.
;; 
;; 2019-10-19  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el: More cvs-align-mode improvements
;; 
;; 	Rename csv-align-fields-* to cvs-align-*.
;; 	(csv-transpose): Use split-string.
;; 	(csv-split-string): Delete function.
;; 	(csv--config-column-widths): New var.
;; 	(csv-align--set-column): New function.
;; 	(csv-align-set-column-width): New command.
;; 	(csv--jit-align): Use them to obey the per-column width settings. Delay
;; 	context refresh by jit-lock-context-time. Set cursor-sensor-functions to
;; 	untruncate fields on-the-fly.
;; 	(csv-align--cursor-truncated): New function.
;; 	(csv-align-mode): Activate cursor-sensor-mode.
;; 
;; 2019-10-19  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el: Fix incorrect truncation
;; 
;; 	(csv--field-index): New function, extracted from csv-field-index.
;; 	(csv--jit-align): Don't apply csv-align-fields-max-width to the last
;; 	column.	 Fix move-to-column call.
;; 
;; 2019-10-10  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el: Fix header-line's alignment
;; 
;; 	(csv-header-line): Change csv--header-line into an overlay. Add a
;; 	modification-hooks to auto-refresh the header-line.
;; 	(csv--header-flush, csv--header-string): New functions.
;; 	(csv--compute-header-string): Make sure jit-lock was applied. 
;; 	csv--header-hscroll can be nil sometimes somehow!
;; 	(csv--jit-flush, csv-align-fields-mode): Flush header-line as well.
;; 	(csv--jit-align): Flush header-line when applicable.  Fix typo.
;; 
;; 2019-10-09  Filipp Gunbin  <fgunbin@fastmail.fm>
;; 
;; 	packages/csv-mode/csv-mode.el: Fix csv-align-fields doc
;; 
;; 	(csv-align-fields): docstring mentioned csv-align-fields instead of 
;; 	csv-align-padding
;; 
;; 2019-09-29  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el: Remove Francis as maintainer
;; 
;; 	(csv-unalign-fields): Also remove the `invisible` property since we use
;; 	it to truncate fields in csv--jit-align.
;; 	(csv-align-fields-max-width): Rename from csv-align-field-max-width to 
;; 	match the "csv-align-fields" prefix.
;; 	(csv--ellipsis-width): New function.
;; 	(csv--jit-align): Use it to truncate more correctly.
;; 
;; 2019-09-27  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el (csv-align-field-max-width): New var
;; 
;; 	(csv--jit-unalign): Erase invisible property as well.
;; 	(csv--jit-align): Truncate field to fit within csv-align-field-max-width 
;; 	when needed.
;; 	(csv-align-fields-mode): Add/remove `csv-truncate` to invisibility spec.
;; 
;; 2019-09-27  Francis Wright  <f.j.wright@qmul.ac.uk>
;; 
;; 	* packages/csv-mode/csv-mode.el: Fix for customize-mode
;; 
;; 	(csv-mode, tsv-mode): Specify :group explicitly for `customize-mode`s
;; 	benefit
;; 
;; 2019-09-24  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el: Add tsv-mode and csv-align-fields-mode
;; 
;; 	Require cl-lib. Don't set buffer-invisibility-spec directly.
;; 	(csv--skip-chars): Rename from misleading csv--skip-regexp.
;; 	(csv-mode): Set normal-auto-fill-function to really disable
;; 	auto-fill-mode.
;; 	(csv--column-widths): Only operate over new args beg..end.
;; 	(csv-align-fields): No need to narrow before csv--column-widths any
;; 	more.
;; 	(csv-align-fields-mode): New minor mode.
;; 	(tsv-mode): New major mode.
;; 
;; 2019-09-18  Simen Heggestøyl  <simenheg@gmail.com>
;; 
;; 	Speed up 'csv-align-fields'
;; 
;; 	* packages/csv-mode/csv-mode.el: Bump version number and make the 
;; 	dependency on Emacs 24.1 or higher explicit.
;; 	(csv--column-widths): Return the field widths as well.
;; 	(csv-align-fields): Speed up by using the field widths already computed 
;; 	by 'csv--column-widths' (bug#37393).
;; 
;; 2017-12-05  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* csv-mode/csv-mode.el (csv-header-line): New command
;; 
;; 	(csv-menu): Add an entry for it.
;; 	(csv--header-line, csv--header-hscroll, csv--header-string): New vars.
;; 	(csv--compute-header-string): New function.
;; 
;; 2016-07-11  Paul Eggert	 <eggert@cs.ucla.edu>
;; 
;; 	Fix some quoting problems in doc strings
;; 
;; 	Most of these are minor issues involving, e.g., quoting `like this' 
;; 	instead of 'like this'.	 A few involve escaping ` and ' with a preceding
;; 	\= when the characters should not be turned into curved single quotes.
;; 
;; 2016-04-21  Leo Liu  <sdl.web@gmail.com>
;; 
;; 	Fix csv-mode to delete its own overlays only
;; 
;; 	* csv-mode/csv-mode.el (csv--make-overlay, csv--delete-overlay): New
;; 	 functions.
;; 	 (csv-align-fields, csv-unalign-fields, csv-transpose): Use them.
;; 
;; 2016-03-04  Francis Wright  <f.j.wright@qmul.ac.uk>
;; 
;; 	* csv-mode/csv-mode.el: Remove out-of-date "URL:" header.
;; 
;; 2016-03-03  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* csv-mode, landmark: Fix maintainer's email
;; 
;; 2015-07-09  Leo Liu  <sdl.web@gmail.com>
;; 
;; 	Fix column width calculation in cvs-mode.el
;; 
;; 	* csv-mode/cvs-mode.el (csv--column-widths, csv-align-fields): Fix
;; 	 column width calculation.
;; 
;; 2015-05-24  Leo Liu  <sdl.web@gmail.com>
;; 
;; 	* csv-mode/cvs-mode.el (csv-set-comment-start): Handle nil.
;; 
;; 	See also http://debbugs.gnu.org/20564.
;; 
;; 2015-04-15  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	(csv-mode): Set mode-line-position rather than mode-line-format.
;; 
;; 	Fixes: debbugs:20343
;; 
;; 	* csv-mode/csv-mode.el (csv-mode-line-format): Only keep the CSV part of
;; 	the mode line.
;; 
;; 2014-01-15  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* csv-mode (csv-mode-line-help-echo): Remove.
;; 
;; 2013-04-24  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* csv-mode.el (csv-kill-one-field): Check for presence before deleting
;; 	trailing separator.  Remove last arg and turn into a function.
;; 	(csv-kill-one-column, csv-kill-many-columns): Adjust callers.
;; 
;; 2012-10-22  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el (csv-end-of-field): Don't skip TABs.
;; 	(csv--skip-regexp): Rename from csv-skip-regexp.
;; 
;; 2012-10-10  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* csv-mode.el: Bump version number.
;; 
;; 2012-10-10  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* csv-mode.el: Use lexical-binding.  Remove redundant :group args.
;; 	(csv-separators): Add TAB to the default.
;; 	(csv-invisibility-default): Change default to t.
;; 	(csv-separator-face): Inherit from escape-glyph.  Remove variable.
;; 	(csv-mode-line-format): Remove trailing "--".  Move next to line-number.
;; 	(csv-interactive-args): Use use-region-p.
;; 	(csv--column-widths): New function, extracted from csv-align-fields.
;; 	(csv-align-fields): Use it.  Use whole buffer by default. Use :align-to
;; 	and text-properties when possible.
;; 	(csv-unalign-fields): Also remove properties.
;; 	(csv-mode): Truncate lines.
;; 
;; 2012-03-24  Chong Yidong  <cyd@gnu.org>
;; 
;; 	Commentary fix for quarter-plane.el.
;; 
;; 2012-03-24  Chong Yidong  <cyd@gnu.org>
;; 
;; 	Commentary tweaks for csv-mode, ioccur, and nhexl-mode packages.
;; 
;; 2012-03-24  Chong Yidong  <cyd@gnu.org>
;; 
;; 	csv-mode.el: Improve commentary.
;; 
;; 2012-03-12  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* packages/csv-mode/csv-mode.el: Minor installation cleanups. Fix up
;; 	copyright notice.  Set version.
;; 	(csv-separators, csv-field-quotes): Fix calls to `error'.
;; 	(csv-mode-line-help-echo, csv-mode-line-format): Replace
;; 	mode-line-format for default-mode-line-format.
;; 	(csv-mode-map): Declare and initialize.
;; 	(csv-mode): Add autoload cookie.
;; 	(csv-set-comment-start): Make sure vars are made buffer-local.
;; 	(csv-field-index-mode, csv-field-index): Use derived-mode-p.
;; 	(csv-align-fields): Improve insertion types of overlay's markers.
;; 
;; 2012-03-12  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	Add csv-mode.el.
;; 



(provide 'csv-mode)

;;; csv-mode.el ends here
