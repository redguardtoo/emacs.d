;;; bbdb-migrate.el --- migration functions for BBDB

;; Copyright (C) 1991, 1992, 1993, 1994 Jamie Zawinski <jwz@netscape.com>.
;; Copyright (C) 2010-2014 Roland Winkler <winkler@gnu.org>

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
;;; This file contains the migration functions for BBDB.
;;; See the BBDB info manual for documentation.

(require 'bbdb)

;;; Migrating the BBDB

;; Unused
(defconst bbdb-migration-features
  '((3 . "* Date format for `creation-date' and `timestamp' has changed,
  from \"dd mmm yy\" (ex: 25 Sep 97) to \"yyyy-mm-dd\" (ex: 1997-09-25).")
    (4 . "* Country field added.")
    (5 . "* More flexible street address.")
    (6 . "* postcodes are stored as plain strings.")
    (7 . "* Xfields is always a list.  Organizations are stored as list.
  New field `affix'."))
  "BBDB Features that have changed in various database revisions.
Format ((VERSION . DIFFERENCES) ... ).")

(defun bbdb-peel-the-onion (lis)
  "Remove outer layers of parens around singleton lists.
This is done until we get a list which is either not a singleton list
or does not contain a list.  This is a utility function used in recovering
slightly munged old BBDB files."
  (while (and (consp lis)
	      (null (cdr lis))
	      (listp (car lis)))
    (setq lis (car lis)))
  lis)

;;;###autoload
(defun bbdb-migrate (records old-format)
  "Migrate the BBDB from the version on disk to the current version
\(in `bbdb-file-format')."
  ;; Some BBDB files were corrupted by random outer layers of
  ;; parentheses surrounding the actual correct data.  We attempt to
  ;; compensate for this.
  (setq records (bbdb-peel-the-onion records))

  ;; Add new field `affix'.
  (if (< old-format 7)
      (let ((temp records) record)
        (while (setq record (car temp))
          (setcar temp (vector (elt record 0) (elt record 1) nil
                               (elt record 2) (elt record 3) (elt record 4)
                               (elt record 5) (elt record 6) (elt record 7)
                               (elt record 8)))
          (setq temp (cdr temp)))))
  (mapc (bbdb-migrate-versions-lambda old-format) records)
  records)

(defconst bbdb-migration-spec
  '((2 (bbdb-record-xfields bbdb-record-set-xfields
        bbdb-migrate-change-dates))
    (3 (bbdb-record-address bbdb-record-set-address
        bbdb-migrate-add-country-field))
    (4 (bbdb-record-address bbdb-record-set-address
        bbdb-migrate-streets-to-list))
    (5 (bbdb-record-address bbdb-record-set-address
        bbdb-migrate-postcodes-to-strings))
    (6 (bbdb-record-xfields bbdb-record-set-xfields
        bbdb-migrate-xfields-to-list)
       (bbdb-record-organization bbdb-record-set-organization
        bbdb-migrate-organization-to-list)))
  "The alist of (version . migration-spec-list).
See `bbdb-migrate-record-lambda' for details.")

(defun bbdb-migrate-record-lambda (changes)
  "Return a function which will migrate a single record.
CHANGES is a `migration-spec-list' containing entries of the form

        (GET SET FUNCTION)

where GET is the function to be used to retrieve the field to be
modified, and SET is the function to be used to set the field to be
modified.  FUNCTION will be applied to the result of GET, and its
results will be saved with SET."
  (byte-compile `(lambda (record)
                  ,@(mapcar (lambda (ch)
                              `(,(cadr ch) record
                                (,(car (cddr ch))
                                 (,(car ch) record))))
                            changes)
                  record)))

(defun bbdb-migrate-versions-lambda (v0)
  "Return the function to migrate from V0 to `bbdb-file-format'."
  (let (spec)
    (while (< v0 bbdb-file-format)
      (setq spec (append spec (cdr (assoc v0 bbdb-migration-spec)))
            v0 (1+ v0)))
    (bbdb-migrate-record-lambda spec)))

(defun bbdb-migrate-postcodes-to-strings (addresses)
  "Make all postcodes plain strings.
This uses the code that used to be in `bbdb-address-postcode'."
  ;; apply the function to all addresses in the list and return a
  ;; modified list of addresses
  (mapcar (lambda (address)
            (let ((postcode (if (stringp (bbdb-address-postcode address))
                                (bbdb-address-postcode address)
                              ;; if not a string, make it a string...
                              (if (consp (bbdb-address-postcode address))
                                  ;; if a cons cell with two strings
                                  (if (and (stringp (car (bbdb-address-postcode address)))
                                           (stringp (car (cdr (bbdb-address-postcode address)))))
                                      ;; if the second string starts with 4 digits
                                      (if (string-match "^[0-9][0-9][0-9][0-9]"
                                                        (car (cdr (bbdb-address-postcode address))))
                                          (concat (car (bbdb-address-postcode address))
                                                  "-"
                                                  (car (cdr (bbdb-address-postcode address))))
                                        ;; if ("abc" "efg")
                                        (concat (car (bbdb-address-postcode address))
                                                " "
                                                (car (cdr (bbdb-address-postcode address)))))
                                    ;; if ("SE" (123 45))
                                    (if (and (stringp (nth 0 (bbdb-address-postcode address)))
                                             (consp (nth 1 (bbdb-address-postcode address)))
                                             (integerp (nth 0 (nth 1 (bbdb-address-postcode address))))
                                             (integerp (nth 1 (nth 1 (bbdb-address-postcode address)))))
                                        (format "%s-%d %d"
                                                (nth 0 (bbdb-address-postcode address))
                                                (nth 0 (nth 1 (bbdb-address-postcode address)))
                                                (nth 1 (nth 1 (bbdb-address-postcode address))))
                                      ;; if a cons cell with two numbers
                                      (if (and (integerp (car (bbdb-address-postcode address)))
                                               (integerp (car (cdr (bbdb-address-postcode address)))))
                                          (format "%05d-%04d" (car (bbdb-address-postcode address))
                                                  (car (cdr (bbdb-address-postcode address))))
                                        ;; else a cons cell with a string an a number (possible error
                                        ;; if a cons cell with a number and a string -- note the
                                        ;; order!)
                                        (format "%s-%d" (car (bbdb-address-postcode address))
                                                (car (cdr (bbdb-address-postcode address)))))))
                                ;; if nil or zero
                                (if (or (zerop (bbdb-address-postcode address))
                                        (null (bbdb-address-postcode address)))
                                    ""
                                  ;; else a number, could be 3 to 5 digits (possible error: assuming
                                  ;; no leading zeroes in postcodes)
                                  (format "%d" (bbdb-address-postcode address)))))))
              (bbdb-address-set-postcode address postcode))
            address)
          addresses))

(defun bbdb-migrate-change-dates (record)
  "Change date formats.
Formats are changed in timestamp and creation-date fields from
\"dd mmm yy\" to \"yyyy-mm-dd\"."
  (unless (stringp record)
    (mapc (lambda (rr)
                 (when (memq (car rr) '(creation-date timestamp))
                   (bbdb-migrate-change-dates-change-field rr)))
               record)
    record))

(defun bbdb-migrate-change-dates-change-field (field)
  "Migrate the date field (the cdr of FIELD) from \"dd mmm yy\" to
\"yyyy-mm-dd\"."
  (let ((date (cdr field))
    parsed)
    ;; Verify and extract - this is fairly hideous
    (and (equal (setq parsed (timezone-parse-date (concat date " 00:00:00")))
        ["0" "0" "0" "0" nil])
     (equal (setq parsed (timezone-parse-date date))
        ["0" "0" "0" "0" nil])
     (cond ((string-match
         "^\\([0-9]\\{4\\}\\)[-/]\\([ 0-9]?[0-9]\\)[-/]\\([ 0-9]?[0-9]\\)" date)
        (setq parsed (vector (string-to-number (match-string 1 date))
                     (string-to-number (match-string 2 date))
                     (string-to-number (match-string 3 date))))
        ;; This should be fairly loud for GNU Emacs users
        (bbdb-warn "BBDB is treating %s field value %s as %s %d %d"
               (car field) (cdr field)
               (upcase-initials
                (downcase (car (rassoc (aref parsed 1)
                           timezone-months-assoc))))
               (aref parsed 2) (aref parsed 0)))
           ((string-match
         "^\\([ 0-9]?[0-9]\\)[-/]\\([ 0-9]?[0-9]\\)[-/]\\([0-9]\\{4\\}\\)" date)
        (setq parsed (vector (string-to-number (match-string 3 date))
                     (string-to-number (match-string 1 date))
                     (string-to-number (match-string 2 date))))
        ;; This should be fairly loud for GNU Emacs users
        (bbdb-warn "BBDB is treating %s field value %s as %s %d %d"
               (car field) (cdr field)
               (upcase-initials
                (downcase (car (rassoc (aref parsed 1)
                           timezone-months-assoc))))
               (aref parsed 2) (aref parsed 0)))
           (t ["0" "0" "0" "0" nil])))

    ;; I like numbers
    (and (stringp (aref parsed 0))
     (aset parsed 0 (string-to-number (aref parsed 0))))
    (and (stringp (aref parsed 1))
     (aset parsed 1 (string-to-number (aref parsed 1))))
    (and (stringp (aref parsed 2))
     (aset parsed 2 (string-to-number (aref parsed 2))))

    ;; Sanity check
    (cond ((and (< 0 (aref parsed 0))
        (< 0 (aref parsed 1)) (>= 12 (aref parsed 1))
        (< 0 (aref parsed 2))
        (>= (timezone-last-day-of-month (aref parsed 1)
                        (aref parsed 0))
            (aref parsed 2)))
       (setcdr field (format "%04d-%02d-%02d" (aref parsed 0)
                 (aref parsed 1) (aref parsed 2)))
       field)
      (t
       (error "BBDB cannot parse %s header value %S for upgrade"
          field date)))))

(defun bbdb-migrate-add-country-field (addrl)
  "Add a country field to each address in the address list."
  (mapcar (lambda (address) (vconcat address [""])) addrl))

(defun bbdb-migrate-streets-to-list (addrl)
  "Convert the streets to a list."
  (mapcar (lambda (address)
            (vector (aref address 0) ; tag
                    (delq nil (delete "" ; nuke empties
                                      (list (aref address 1) ; street1
                                            (aref address 2) ; street2
                                            (aref address 3))));street3
                    (aref address 4) ; city
                    (aref address 5) ; state
                    (aref address 6) ; postcode
                    (aref address 7))) ; country
          addrl))

(defun bbdb-migrate-xfields-to-list (xfields)
  "Migrate XFIELDS to list."
  (if (stringp xfields)
      (list (cons 'notes xfields))
    xfields))

(defun bbdb-migrate-organization-to-list (organization)
  "Migrate ORGANIZATION to list."
  (if (stringp organization)
      (bbdb-split 'organization organization)
    organization))

;;;###autoload
(defun bbdb-undocumented-variables (&optional name-space message)
  "Return list of undocumented variables in NAME-SPACE.
NAME-SPACE defaults to \"bbdb-\".  Use a prefix arg to specify NAME-SPACE
interactively.  If MESSAGE is non-nil (as in interactive calls) display
the list in the message area.

This command may come handy to identify BBDB variables in your init file
that are not used anymore by the current version of BBDB.  Yet this fails
for outdated BBDB variables that are set via your personal `custom-file'."
  (interactive (list (if current-prefix-arg
                         (read-string "Name space: ")) t))
  (let ((re (concat "\\`" (or name-space "bbdb-"))) list)
    (mapatoms (lambda (vv)
                (if (and (boundp vv)
                         (string-match re (symbol-name vv))
                         (not (get vv 'variable-documentation)))
                    (push vv list))))
    (if message
        (if list
            (apply 'message (concat "Undocumented variables: "
                                    (mapconcat (lambda (m) "%s") list " ")) list)
          (message "No undocumented variables `%s...'" name-space)))
    list))

(provide 'bbdb-migrate)
