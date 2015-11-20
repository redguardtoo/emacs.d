;;; bbdb-print.el -- for printing BBDB databases using TeX.

;; Copyright (C) 1993 Boris Goldowsky
;; Copyright (C) 2010-2014 Roland Winkler <winkler@gnu.org>

;; Authors: Boris Goldowsky <boris@cs.rochester.edu>
;;          Dirk Grunwald <grunwald@cs.colorado.edu>
;;          Luigi Semenzato <luigi@paris.cs.berkeley.edu>

;; This file is part of the Insidious Big Brother Database (aka BBDB),

;; BBDB is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; BBDB is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with BBDB.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; This file lets you print the BBDB using TeX.
;;; See the BBDB info manual for documentation.
;;;
;;; In the *BBDB* buffer, type P to convert the listing to TeX
;;; format. It will prompt you for a filename.  Then run TeX on that
;;; file and print it out.
;;;
;;; `bbdb-print' understands one new bbdb field: tex-name.  If it
;;; exists, this will be used for the printed listing instead of the
;;; name field of that record.  This is designed for entering names
;;; with lots of accents that would mess up mailers, or when for any
;;; reason you want the printed version of the name to be different
;;; from the version that appears on outgoing mail and in the *BBDB*
;;; buffer.  You may want to add tex-name to a omit list of the variable
;;; `bbdb-layout-alist' so you only see it in the printout.
;;; tex-name is exempted from the usual special-character quoting done by
;;; `bbdb-print'; it is used verbatim.
;;;
;;; Not all fields or records need to be printed.  To not print a certain
;;; field, add it to `bbdb-print-omit-fields'.  If after eliding fields
;;; a record contains no interesting information, it will not be printed
;;; at all; the variable `bbdb-print-require' determines what is meant
;;; by "interesting" information.  You can also restrict printing to just
;;; the records currently in the *BBDB* buffer by using *P instead of P.
;;;
;;; There are various options for the way the formatting is done; most
;;; are controlled by the variable `bbdb-print-alist'. See its
;;; documentation for the allowed options.

;;; This program was adapted for BBDB by Boris Goldowsky
;;; <boris@cs.rochester.edu> and Dirk Grunwald
;;; <grunwald@cs.colorado.edu> using a TeX format designed by Luigi
;;; Semenzato <luigi@paris.cs.berkeley.edu>.
;;; We are also grateful to numerous people on the bbdb-info
;;; mailing list for suggestions and bug reports.

;;; Code:

(require 'bbdb)
(require 'bbdb-com)

;;; Variables:

(defcustom bbdb-print-file "~/bbdb.tex"
  "Default file name for printouts of BBDB database."
  :group 'bbdb-utilities-print
  :type 'file)

(defcustom bbdb-print-omit-fields
  '(tex-name aka mail-alias creation-date timestamp vm-folder)
  "List of fields NOT to print in address list.
See also `bbdb-print-require'."
  :group 'bbdb-utilities-print
  :type '(repeat (symbol :tag "Field to exclude")))

(defcustom bbdb-print-require '(or address phone)
  "What fields are required for printing a record.
This is a lisp expression and a record will be printed only if the evaluation
of this expression yields a non-nil value for this records.
The symbols name, organization, mail, phone, address, and notes will be set
to appropriate values when this is evaluated; they will be nil if the field
does not exist or is elided.

The value of this variable can be any lisp expression, but typically
it will be a boolean combination of the field variables, as in
the following examples:

  Print only people whose phone numbers are known:
    (setq bbdb-print-require 'phone)
  Print people whose names and organizations are known:
    (setq bbdb-print-require '(and name organization))
  Print people whose names, and either addresses or phone numbers are known:
    (setq bbdb-print-require '(and name (or address phone)))."
  :group 'bbdb-utilities-print
  :type '(choice (const :tag "Print all records" t)
                 (symbol :tag "Print all records with this field" phone)
                 (sexp :tag "Print only when this evaluates to non-nil"
                       '(or phone address phone))))

(define-widget 'bbdb-print-alist-widget 'repeat
  "For use in Customize"
  :args `((choice
           (cons :tag "Column specification" :value (column . 1)
                 (const :tag "Column mode" column)
                 (radio-button-choice (const :tag "One column" 1)
                                      (const :tag "Two columns" 2)
                                      (const :tag "Three columns" 3)
                                      (const :tag "Four columns" 4)
                                      (const :tag "Quad" quad)
                                      (const :tag "Grid" grid)))
           (cons :tag "Separator specification" :value (separator . 0)
                 (const :tag "Separator" separator)
                 (radio-button-choice (const :tag "None" 0)
                                      (const :tag "Line" 1)
                                      (const :tag "Boxed letters" 2)
                                      (const :tag "Large boxed letters" 3)
                                      (const :tag "Large letters" 4)
                                      (const :tag "Letters with lines" 5)
                                      (const :tag "Letters with suits" 6)
                                      (const :tag "Boxed letters with suits" 7)))
           (cons :tag "Omit certain area codes"
                 :value (omit-area-code . ,(concat "^("
                                                   (if (integerp bbdb-default-area-code)
                                                       (int-to-string bbdb-default-area-code)
                                                     "000")  ") "))
                 (const :tag "Omit certain area codes" omit-area-code)
                 (regexp :tag "Regexp to omit"))
           (cons :tag "Phone number label" :value (phone-on-first-line . t)
                 (const :tag "Phone number label" phone-on-first-line)
                 (choice (const :tag "First home number on same line as name" t)
                         (const :tag "Do not put the phone number on the name line" nil)
                         (regexp :tag "Use phone number whose label matches" "^work$")))
           (cons :tag "Limit included phone numbers" :value (n-phones . 3)
                 (const :tag "Limit included phone numbers" n-phones)
                 (integer :tag "Maximum number to include" 3))
           (cons :tag "Limit included addresses" :value (n-addresses . 3)
                 (const :tag "Limit included addresses" n-addresses)
                 (integer :tag "Maximum number to include" 3))
           (cons :tag "Include additional TeX input files" :value (include-files . nil)
                 (const :tag "Additional TeX input files to include" include-files)
                 (repeat (file :tag "TeX file to include")))
           (cons :tag "Font type selection" :value (ps-fonts . nil)
                 (const :tag "Select font type" ps-fonts)
                 (choice (const :tag "Use standard TeX fonts" nil)
                         (const :tag "Use Postscript fonts" t)))
           (cons :tag "Font size selection" :value (font-size . 10)
                 (const :tag "Select font size" font-size)
                 (integer :tag "Font size in points" 10))
           (cons :tag "Page height selection" :value (v-size . nil)
                 (const :tag "Select page height" v-size)
                 (choice (const :tag "Use TeX default" nil)
                         (string :tag "Height (must be valid TeX dimension)" "9in")))
           (cons :tag "Page width selection" :value (h-size . nil)
                 (const :tag "Select page width" h-size)
                 (choice (const :tag "Use TeX default" nil)
                         (string :tag "Width (must be valid TeX dimension)" "6in")))
           (cons :tag "Vertical offset (top margin)" :value (voffset . nil)
                 (const :tag "Select vertical offset (top margin)" voffset)
                 (choice (const :tag "Use TeX default" nil)
                         (string :tag "Vertical offset (must be valid TeX dimension)" "1in")))
           (cons :tag "Horizontal offset (left margin)" :value (hoffset . nil)
                 (const :tag "Select horizontal offset (left margin)" hoffset)
                 (choice (const :tag "Use TeX default" nil)
                         (string :tag "Horizontal offset (must be valid TeX dimension)" "1in")))
           (cons :tag "Quad format height" :value (quad-vsize . "")
                 (const :tag "Select height for quad format pages" quad-vsize)
                 (string :tag "Height (must be valid TeX dimension)"))
           (cons :tag "Quad format width" :value (quad-hsize . "")
                 (const :tag "Select width for quad format pages" quad-hsize)
                 (string :tag "Width (must be valid TeX dimension)")))))

(defcustom bbdb-print-alist
  `((omit-area-code . ,(concat "^(" (if (integerp bbdb-default-area-code)
                                        (int-to-string bbdb-default-area-code)
                                      "000") ") "))
    (phone-on-first-line . "^[ \t]*$")
    (ps-fonts . nil)
    (font-size . 6)
    (quad-hsize . "3.15in")
    (quad-vsize . "4.5in"))
  "Formatting options for `bbdb-print', all formats.
This is an alist of the form ((option1 . value1) (option2 . value2) ...)

You can have separate settings for brief and non-brief printouts;
see the variables `bbdb-print-brief-alist' and `bbdb-print-full-alist'.
Settings there will override the common settings in this variable.

The possible options and legal values are:
 - columns: 1, 2, 3, 4 or 'quad (4 little 2-column pages per sheet)
     or 'grid (12 credit-card-sized pages per sheet).
 - separator: 0-7, the style of heading for each letter.
     0=none, 1=line, 2=boxed letters, 3=large boxed letters, 4=large letters,
     5=letters with lines, 6=letters with suits, 7=boxed letters with suits.
 - omit-area-code: a regular expression matching area codes to omit.
 - phone-on-first-line: t means to put first phone number on the same
     line with the name, nil means just the name.  A string means to
     use the first phone number whose \"label\" matches that string,
     which should be a valid regular expression.
 - n-phones: maximum number of phone numbers to include.
 - n-addresses: maximum number of addresses to include.
 - include-files: list of TeX files to \\input.  If these filenames are not
   absolute, the files must be located somewhere that TeX will find them.
 - ps-fonts: nonnil means to use them, nil to use standard TeX fonts.
 - font-size: in points, any integer (assuming fonts in that size exist).
 - hsize, vsize: horizontal dimension of pages.  String value can be any valid
   TeX dimension, or nil to use TeX's default.
 - hoffset, voffset: shift TeX's output rightward (downward) by this distance
   (any TeX dimension).  Nil or 0 uses TeX's default positioning.
 - quad-hsize, quad-vsize: for the quad format, horizontal and
     vertical size of the little pages.  These must be strings which
     are valid TeX dimensions, eg \"10cm\"."
  :group 'bbdb-utilities-print
  :type 'bbdb-print-alist-widget)

(defcustom bbdb-print-full-alist
  '((columns . 3)
    (separator . 2)
    (include-files "bbdb-print" "bbdb-cols"))
  "Extra options for `bbdb-print' non-brief format.
These supplement or override entries in `bbdb-print-alist'; see description
of possible contents there."
  :group 'bbdb-utilities-print
  :type 'bbdb-print-alist-widget)

(defcustom bbdb-print-brief-alist
  '((columns . 1)
    (separator . 1)
    (n-phones . 2)
    (n-addresses . 1)
    (include-files "bbdb-print-brief" "bbdb-cols"))
  "Extra Options for `bbdb-print', brief format.
These supplement or override entries in `bbdb-print-alist'; see description
of possible contents there."
  :group 'bbdb-utilities-print
  :type 'bbdb-print-alist-widget)

(defcustom bbdb-print-prolog
  (concat "%%%% ====== Phone/Address list in -*-TeX-*- Format =====\n"
          "%%%%        produced by bbdb-print, version 3.0\n\n")
  "TeX statements to include at the beginning of the `bbdb-print' file."
  :group 'bbdb-utilities-print
  :type '(text :format "%t:\n%v"))

(defcustom bbdb-print-epilog "\\endaddresses\n\\bye\n"
  "TeX statements to include at the end of the `bbdb-print' file."
  :group 'bbdb-utilities-print
  :type '(text :format "%t:\n%v"))

(defcustom bbdb-print-mail 'primary
  "Whether only the primary or all mail addresses are printed.
Value `primary' means print the primary mail address only.
Value `all' means print all mail addresses."
  :group 'bbdb-utilities-print
  :type '(choice (const primary)
         (const all)))

(defcustom bbdb-print-tex-quote-alist
  '(("[#$%&_]" . "\\\\\\&")
    ("[<>=]+" . "$\\&$")
    ("[{}]" . "$\\\\\\&$")
    ("~" . "\\\\~{}"))
  "Replacement alist for quoting TeX's special characters.
Each element is of the form (REGEXP . REPLACE)."
  :group 'bbdb-utilities-print)

(defcustom bbdb-print-address-format-list bbdb-address-format-list
  "List of address formatting rules for printing.
Each element may take the same values as in `bbdb-address-format-list'.
The EDIT elements of `bbdb-address-format-list' are ignored."
  :group 'bbdb-utilities-print)

(defcustom bbdb-print-name-format 'first-last
  "Format for names when printing BBDB.
If first-last format names as \"Firstname Lastname\".
If last-first format names as \"Lastname, Firstname\".
If `bbdb-print-name' returns the full name as a single, preformatted string,
this takes precedence over `bbdb-print-name-format'."
  :group 'bbdb-utilities-print
  :type '(choice (const :tag "Firstname Lastname" first-last)
                 (const :tag "Lastname, Firstname" last-first)))

(defcustom bbdb-print-name 'tex-name
  "Xfield holding the full print name for a record.
This may also be a function taking one argument, a record.
If it returns the full print name as a single string, this is used \"as is\".
If it returns a cons pair (FIRST . LAST) with the first and last name
for this record, these are formatted obeying `bbdb-print-name-format'.
In any case, this function should call `bbdb-print-tex-quote' as needed."
  :group 'bbdb-utilities-print
  :type '(choice (symbol :tag "xfield")
                 (function :tag "print name function")))

;;; Functions:

(defsubst bbdb-print-field-p (field)
  (not (memq field bbdb-print-omit-fields)))

(defun bbdb-print-front-if (func list)
  "Move first elt of LIST satisfying predicate FUNC to front of LIST.
The car of the returned list is the first element that returned nonnil;
The cdr are all other elements of LIST.
If FUNC returns nil for all elements of LIST, return nil."
  (cond ((null list) nil)
        ((funcall func (car list))
         list)
        ((let ((rest (bbdb-print-front-if func (cdr list))))
           (if rest
               (cons (car rest)
                     (cons (car list) (cdr rest))))))))

(defun bbdb-print-firstn (n list force)
  "Return the first N elements of LIST.  If N is nil, just return LIST.
If FORCE is nonnil and LIST is shorter than N, extend the list to length N
by adding nil's."
  ;; FORCE is needed by the `brief' format that is really a big table.
  ;; So we want to create output for the relevant fields of a record
  ;; even if these fields are empty.
  (cond ((null n) list)
        ((null list) (if force (make-list n nil) nil))
        ((<= n 0) nil)
        (t (cons (car list) (bbdb-print-firstn (1- n) (cdr list) force)))))

(defun bbdb-print-tex-quote (string)
  "Quote any unquoted TeX special characters that appear in STRING.
The replacement rules are defined in `bbdb-print-tex-quote-alist'."
  (if string
      (dolist (quote bbdb-print-tex-quote-alist string)
        (setq string (replace-regexp-in-string (car quote) (cdr quote) string)))
    ""))

;;;###autoload
(defun bbdb-print (records file brief)
  "Make a TeX FILE for printing RECORDS.
Interactively, use BBDB prefix \
\\<bbdb-mode-map>\\[bbdb-do-all-records], see `bbdb-do-all-records'.
With prefix BRIEF non-nil, make a brief (one line per record) printout.
There are various variables for customizing the content and format
of the printout, notably the variables `bbdb-print-alist' and
`bbdb-print-require'."
  (interactive
   (list (bbdb-do-records)
         (read-file-name
          (format "TeX file: (default %s) "
                  (abbreviate-file-name bbdb-print-file))
          (file-name-directory bbdb-print-file)
          bbdb-print-file)
         current-prefix-arg))
  ;; Remember our choice for `bbdb-print-file'.
  (setq bbdb-print-file (expand-file-name file))
  (let* ((alist (append (if brief bbdb-print-brief-alist bbdb-print-full-alist)
                        bbdb-print-alist))
         (psstring (if (cdr (assoc 'ps-fonts alist))
                       "ps" ""))
         (columns (cdr (assoc 'columns alist)))
         (current-letter t)
         (pofl (cdr (assoc 'phone-on-first-line alist)))
         (n-phones (cdr (assoc 'n-phones alist)))
         (n-addresses (cdr (assoc 'n-addresses alist))))
    (find-file bbdb-print-file)
    (widen)
    (erase-buffer)
    (insert bbdb-print-prolog)
    (let (tmp)
      (dolist (dim '(hsize vsize hoffset voffset))
        (if (setq tmp (cdr (assoc dim alist)))
            (insert (format "\\%s=%s\n" dim tmp))))
      (dolist (file (cdr (assoc 'include-files alist)))
        (if (setq tmp (locate-file file bbdb-print-tex-path '(".tex" "")))
            (progn
              ;; We use lisp `insert-file-contents' instead of TeX `\input'
              ;; because installing the respective files in the proper place
              ;; of a TeX installation can be tricky...
              (insert-file-contents tmp)
              (goto-char (point-max)))
          (error "File `%s' not found, check bbdb-print-tex-path" file))))
    (insert (format "\n\\set%ssize{%d}\n"
                    psstring (cdr (assoc 'font-size alist)))
            (format "\\setseparator{%d}\n"
                    (cdr (assoc 'separator alist)))
            (cond ((eq 'quad columns)
                   (format "\\quadformat{%s}{%s}"
                           (cdr (assoc 'quad-hsize alist))
                           (cdr (assoc 'quad-vsize alist))))
                  ((eq 'grid columns) "\\grid")
                  ((= 4 columns) "\\fourcol")
                  ((= 3 columns) "\\threecol")
                  ((= 2 columns) "\\twocol")
                  ((= 1 columns) "\\onecol"))
            "\n\n\\beginaddresses\n")
    (dolist (record (bbdb-record-list records))
      (setq current-letter
            (bbdb-print-record record current-letter
                                      brief pofl n-phones n-addresses)))
    (insert bbdb-print-epilog)
    (goto-char (point-min)))
  (message "Process this file with TeX (not LaTeX)"))

(defun bbdb-print-record (record current-letter
                                 brief pofl n-phones n-addresses)
  "Insert the bbdb RECORD in TeX format in the current buffer.
CURRENT-LETTER is the first letter of the sortkey of the previous record.
If this is non-nil and RECORD begins differently, a section heading is output.
If CURRENT-LETTER is t always produce a heading.
BRIEF is non-nil for 1-line-per-record printouts.
PHONE-ON-FIRST-LINE, N-PHONES, and N-ADDRESSES are the respective values
from `bbdb-print-alist'.

The return value is the new CURRENT-LETTER."

  (let ((first-letter
         (substring (concat (bbdb-record-sortkey record) "?") 0 1))
        (name (cond ((functionp bbdb-print-name)
                     (let ((value (funcall bbdb-print-name record)))
                       (cond ((stringp value) value)
                             ((eq bbdb-print-name-format 'first-last)
                              (bbdb-concat 'name-first-last
                                           (car value) (cdr value)))
                             (t
                              (bbdb-concat 'name-last-first
                                           (cdr value) (car value))))))
                    ((bbdb-record-xfield record bbdb-print-name))
                    ((eq bbdb-print-name-format 'first-last)
                     (bbdb-print-tex-quote (bbdb-record-name record)))
                    (t
                     (bbdb-print-tex-quote (bbdb-record-name-lf record)))))
        (organization (bbdb-record-organization record))
        (affix   (bbdb-record-affix record))
        (mail    (bbdb-record-mail record))
        (phone   (bbdb-record-phone record))
        (address (bbdb-record-address record))
        (xfields (bbdb-record-xfields record))
        (bbdb-address-format-list bbdb-print-address-format-list))

    (when (eval bbdb-print-require)
      ;; Insert section header, if neccessary.
      (if (or (eq current-letter t)
              (not (string-equal first-letter current-letter)))
          (insert (format "%s\\separator{%s}\n%%\n"
                          (if brief "" "\\goodbreak\n")
                          (bbdb-print-tex-quote (upcase first-letter)))))

      (insert "\\beginrecord\n"
              (format "\\firstline{%s}{%s}\n"
                      (cond (name)
                            ;; if there is no name, use organization instead
                            (organization
                             (prog1 (bbdb-print-tex-quote (bbdb-concat 'organization organization))
                               (setq organization nil)))
                            (t ""))
                      ;; Possibly put one phone number next to name
                      (cond ((null phone) "")
                            ((eq t pofl)
                             (prog1 (bbdb-print-phone (car phone))
                               (setq phone (cdr phone))))
                            ((stringp pofl)
                             (let ((p (bbdb-print-front-if
                                       (lambda (ph) (string-match pofl (aref ph 0)))
                                       phone)))
                               (if p (prog1 (bbdb-print-phone (car p))
                                       (setq phone (cdr p))) "")))
                            (t ""))))

      (if (and organization (bbdb-print-field-p 'organization))
          (insert (format "\\comp{%s}\n" (bbdb-print-tex-quote
                                          (bbdb-concat 'organization organization)))))

      ;; Phone numbers
      (if n-phones
          (setq phone (bbdb-print-firstn (- n-phones (if pofl 1 0))
                                         phone brief)))
      (dolist (ph phone)
        (if (and ph (bbdb-print-field-p 'phone))
            (insert (format "\\phone{%s%s}\n"
                            (bbdb-print-tex-quote
                             (if (or (not (aref ph 0)) (equal "" (aref ph 0))) ""
                               (concat (aref ph 0) ": ")))
                            (bbdb-print-phone ph)))
          (insert "\\phone{}\n"))) ;; needed for brief format

      ;; Mail address
      (when (and mail (bbdb-print-field-p 'mail))
        (insert
         (format
          "\\email{%s}\n"
          (mapconcat
           (lambda (mail)
             ;; Make all dots legal line-breaks.
             (replace-regexp-in-string "\\." ".\\\\-"
                                       (bbdb-print-tex-quote mail)))
           (cond ((eq bbdb-print-mail 'primary)
                  (list (car mail)))
                 ((eq bbdb-print-mail 'all)
                  mail))
           ", "))))

      ;; Addresses.  FUTURE: If none left, should use phones instead.
      (if n-addresses
          (setq address
                (bbdb-print-firstn n-addresses address nil)))
      (if (and address (bbdb-print-field-p 'address))
          (dolist (a address)
            (insert
             "\\address{"
             (replace-regexp-in-string
              "\n" (if brief ", " "\\\\\\\\\n")
              (bbdb-print-tex-quote (bbdb-format-address a 2)))
             "}\n"))
        (insert "\\address{}\n")) ;; needed for brief format

      ;; xfields
      (dolist (xfield xfields)
        (when (bbdb-print-field-p (car xfield))
          ;; The value of the xfield may be a sexp.  Ideally, a sexp
          ;; should be formatted by `pp-to-string' then printed verbatim.
          (let ((value (bbdb-print-tex-quote (format "%s" (cdr xfield)))))
            (insert (if (eq 'notes (car xfield))
                        (format "\\notes{%s}\n" value)
                      (format "\\note{%s}{%s}\n"
                              (bbdb-print-tex-quote (symbol-name (car xfield)))
                              value))))))
      ;; Mark end of the record.
      (insert "\\endrecord\n%\n")
      (setq current-letter first-letter)))
  current-letter)

(defun bbdb-print-phone (phone)
  "Format PHONE as a string, obeying omit-area-code setting.
Omit-area-code is one of the allowed symbols in `bbdb-print-alist'."
  (let ((str (bbdb-phone-string phone))
        (omit (cdr (assoc 'omit-area-code bbdb-print-alist))))
    (bbdb-print-tex-quote
     (if (and omit (string-match omit str))
         (substring str (match-end 0))
       str))))

(provide 'bbdb-print)

;;; bbdb-print ends here.
