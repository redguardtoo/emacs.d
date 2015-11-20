;;; bbdb-anniv.el --- get anniversaries from BBDB

;; Copyright (C) 2011-2014 Roland Winkler <winkler@gnu.org>

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
;; Anniversaries are stored in xfields as defined via `bbdb-anniv-alist'.
;; Each such field may contain multiple anniversaries entries with separators
;; defined via `bbdb-separator-alist' (newlines by default).
;; Each anniversary entry is a string DATE followed by optional TEXT.
;; DATE may take the same format as the date of ordinary diary entries.
;; In particular, `calendar-date-style' is obeyed via `diary-date-forms'.
;; If `bbdb-anniv-alist' has a non-nil FORM for this type of anniversary,
;; FORM is used to display the anniversary entry in the diary buffer.
;; If FORM is nil, TEXT is used instead to display the anniversary entry
;; in the diary buffer.
;;
;; To display BBDB anniversaries in the Emacs diary,
;; call `bbdb-initialize' with arg `anniv'.
;;
;; See the BBDB info manual for documentation.

(require 'bbdb)
(require 'bbdb-com)
(require 'diary-lib)

(defcustom bbdb-anniv-alist
  '((birthday . "%n's %d%s birthday")
    (wedding  . "%n's %d%s wedding anniversary")
    (anniversary))
  "Alist of rules for formatting anniversaries in the diary buffer.
Each element is of the form (LABEL . FORM).
LABEL is the xfield where this type of anniversaries is stored.
FORM is a format string with the following substitutions:
  %n  name of the record
  %d  number of years
  %s  ordinal suffix (st, nd, rd, th) for the year.
  %t  the optional text following the date string in field LABEL.
If FORM is nil, use the text following the date string in field LABEL
as format string."
  :type '(repeat (cons :tag "Rule"
                       (symbol :tag "Label")
                       (choice (regexp)
                               (const nil))))
  :group 'bbdb-utilities-anniv)

;; `bbdb-anniv-diary-entries' becomes a member of  `diary-list-entries-hook'.
;; When this hook is run by `diary-list-entries', the variable `original-date'
;; is bound to the value of arg DATE of `diary-list-entries'.
;; Also, `number' is arg NUMBER of `diary-list-entries'.
;; `diary-list-entries' selects the entries for NUMBER days starting with DATE.

(defvar original-date) ; defined in diary-lib
(with-no-warnings (defvar number)) ; defined in diary-lib

;;;###autoload
(defun bbdb-anniv-diary-entries ()
  "Add anniversaries from BBDB records to `diary-list-entries'.
This obeys `calendar-date-style' via `diary-date-forms'.
To enable this feature, put the following into your .emacs:

 \(add-hook 'diary-list-entries-hook 'bbdb-anniv-diary-entries)"
  ;; Loop over NUMBER dates starting from ORGINAL-DATE.
  (let* ((num-date (1- (calendar-absolute-from-gregorian original-date)))
         (end-date (+ num-date number)))
    (while (<= (setq num-date (1+ num-date)) end-date)
      (let* ((date (calendar-gregorian-from-absolute num-date))
             ;; The following variables may be used by `diary-date-forms'.
             (day (calendar-extract-day date))
             (month (calendar-extract-month date))
             (current-year (calendar-extract-year date))
             (non-leap (and (= month 3) (= day 1)
                            (not (calendar-leap-year-p current-year))))
             (dayname (format "%s\\|%s\\.?" (calendar-day-name date)
                              (calendar-day-name date 'abbrev)))
             (monthname (format "%s\\|%s" (calendar-month-name month)
                                (calendar-month-name month 'abbrev)))
             (day (format "0*%d" day))
             (month (format "0*%d" month))
             ;; We could use an explicitly numbered group to match the year.
             ;; This requires emacs 23.
             (year "\\([0-9]+\\)\\|\\*")
             date-forms)

        (dolist (date-form diary-date-forms)
          ;; Require that the matched date is at the beginning of the string.
          ;; Use shy groups so that we can grab the year more easily.
          (push (cons (format "\\`%s?\\(?:%s\\)"
                              (regexp-quote diary-nonmarking-symbol)
                              (mapconcat 'eval (if (eq (car date-form) 'backup)
                                                   (cdr date-form) date-form)
                                         "\\)\\(?:"))
                      (eq (car date-form) 'backup))
                date-forms))

        ;; The anniversary of February 29 is considered to be March 1
        ;; in non-leap years.  So we search for February 29, too.
        (when non-leap
          (let* ((day "0*29") (month "0*2")
                 (monthname (format "%s\\|%s" (calendar-month-name 2)
                                    (calendar-month-name 2 'abbrev))))
            (dolist (date-form diary-date-forms)
              (push (cons (format "\\`%s?\\(?:%s\\)"
                                  (regexp-quote diary-nonmarking-symbol)
                                  (mapconcat 'eval (if (eq (car date-form) 'backup)
                                                       (cdr date-form) date-form)
                                             "\\)\\(?:"))
                          (eq (car date-form) 'backup))
                    date-forms))))

        (dolist (record (bbdb-records))
          (dolist (rule bbdb-anniv-alist)
            (dolist (anniv (bbdb-record-xfield-split record (car rule)))
              (let ((date-forms date-forms)
                    (anniv-string (concat anniv " X")) ; for backup forms
                    (case-fold-search t)
                    form yy text)
                (while (setq form (pop date-forms))
                  (when (string-match (car form) anniv-string)
                    (setq date-forms nil
                          yy (match-string 1 anniv-string)
                          yy (if (and yy (string-match-p "[0-9]+" yy))
                                 (- current-year (string-to-number yy))
                               100) ; as in `diary-anniversary'
                          ;; For backup forms we should search backward in
                          ;; anniv-string from (match-end 0) for "\\<".
                          ;; That gets too complicated here!
                          ;; Yet for the default value of `diary-date-forms'
                          ;; this would matter only if anniv-string started
                          ;; with a time. That is rather rare for anniversaries.
                          ;; Then we may simply step backward by one character.
                          text (substring anniv-string (if (cdr form) ; backup
                                                           (1- (match-end 0))
                                                         (match-end 0)) -1)
                          text (replace-regexp-in-string "\\`[ \t]+" "" text)
                          text (replace-regexp-in-string "[ \t]+\\'" "" text))
                    (if (cdr rule)
                        (setq text (replace-regexp-in-string "%t" text (cdr rule))))))
                ;; Add the anniversaries to `diary-entries-list'.
                (if (and yy (> yy 0) (< 0 (length text)))
                    (diary-add-to-list
                     date
                     (format
                      ;; Text substitution similar to `diary-anniversary'.
                      (replace-regexp-in-string "%n" (bbdb-record-name record) text)
                      yy (diary-ordinal-suffix yy))
                     ;; It would be nice to have a SPECIFIER that allowed us to jump
                     ;; from the diary display buffer to the respective BBDB record.
                     ;; Yet it seems that diary-lib does not support this for us.
                     ;; So we use instead an empty string.  When clicking on the
                     ;; anniversary entry in the diary display buffer, this give us
                     ;; the message "Unable to locate this diary entry".
                     ""))))))))))

(provide 'bbdb-anniv)
