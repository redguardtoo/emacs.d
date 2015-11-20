;;; bbdb-sc.el --- BBDB interface to Supercite

;; Copyright (C) 1991, 1992 Jamie Zawinski <jwz@netscape.com>.
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
;; This file contains the BBDB interface to Supercite (sc)

;; This file was written by Martin Sjolin <marsj@ida.liu.se>
;; based on the original code by Tom Tromey <tromey@busco.lanl.gov>.
;; Thanks to Richard Stanton <stanton@haas.berkeley.edu> for ideas
;; for improvements and to Michael D. Carney  <carney@ltx-tr.com>
;; for testing and feedback.

;; This file adds the ability to define attributions for Supercite in BBDB
;; and it enables you to retrieve your standard attribution from BBDB.
;; If the From header in the mail message to which you are replying only
;; contains the mail address, the sender's name is looked up in BBDB.
;; The attribution is stored in the xfield `attribution' (unless you
;; have changed `bbdb-sc-attribution-field').

;; To enable supercite support for BBDB, call `bbdb-initialize' with arg `sc'.
;; Also customize supercite as follows:
;; (1) Add element "sc-consult" to `sc-preferred-attribution-list'
;;     (note that order matters!), e.g.,
;;
;;   (setq sc-preferred-attribution-list
;;         '("sc-lastchoice" "x-attribution" "sc-consult"
;;           "initials" "firstname" "lastname"))
;;
;; (2) The variable `sc-attrib-selection-list' should include an element
;;
;;   (add-to-list 'sc-attrib-selection-list
;;                '("from" ((".*" . (bbdb-sc-get-attrib
;;                                   (sc-mail-field "from"))))))
;;
;; (3) Set `sc-mail-glom-frame' as follows to fetch the sender's name from BBDB
;;     if there is only a plain mail address in the From field of the mail message,
;;     e.g.,
;;
;;  (setq sc-mail-glom-frame
;;        '((begin                        (setq sc-mail-headers-start (point)))
;;          ("^From "                     (sc-mail-check-from) nil nil)
;;          ("^x-attribution:[ \t]+.*$"   (sc-mail-fetch-field t) nil t)
;;          ("^\\S +:.*$"                 (sc-mail-fetch-field) nil t)
;;          ("^$"                         (list 'abort '(step . 0)))
;;          ("^[ \t]+"                    (sc-mail-append-field))
;;          (sc-mail-warn-if-non-rfc822-p (sc-mail-error-in-mail-field))
;;          (end                          (progn
;;                                          (bbdb-sc-update-from)
;;                                          (setq sc-mail-headers-end (point))))))

(require 'bbdb-com)
(require 'bbdb-mua)
(require 'supercite)

(defcustom bbdb-sc-attribution-field 'attribution
  "The BBDB xfield used for Supercite attribution."
  :group 'bbdb-utilities-sc
  :type '(symbol :tag "Field name"))
(define-obsolete-variable-alias 'bbdb/sc-attribution-field
  'bbdb-sc-attribution-field)

(defcustom bbdb-sc-update-records-p 'search
  "How `bbdb-sc-set-attrib' updates BBDB records automatically.
This may take the same values as arg UPDATE-P of `bbdb-update-records'."
  :group 'bbdb-utilities-sc
  :type '(choice (const :tag "do nothing" nil)
                 (const :tag "search for existing records" search)
                 (const :tag "update existing records" update)
                 (const :tag "query annotation of all messages" query)
                 (const :tag "annotate all messages" create)
                 (function :tag "User-defined function")))

(defcustom bbdb-sc-update-attrib-p 'query
 "How `bbdb-sc-set-attrib' updates the attribution field.
Allowed values include
 nil    Do not create or modify the attribution field
 query  Query before creating or modifying the attribution field.
 t      Create or modify the attribution field."
 :group 'bbdb-utilities-sc
 :type '(choice (const "Do nothing" nil)
                (const "Query before updating the attribution field" query)
                (const "Update the attribution field" t)))

;;; Internal variables
(defvar bbdb-sc-last-attrib ""
 "Last attribution used by Supercite.
Used to compare against citation selected by the user.")

(defun bbdb-sc-get-attrib (mail)
  "Get the Supercite attribution from BBDB.
MAIL is the mail address to look for in BBDB."
  ;; We could store in `sc-mail-info' from which record we grabbed
  ;; this attribution.  Yet we do not know whether `bbdb-sc-set-attrib'
  ;; will want to use the same record.
  (let* ((address (bbdb-extract-address-components mail))
         (record (bbdb-message-search (car address)
                                      (cadr address))))
    ;; FIXME: What to do if we have multiple matching records?
    (when (cdr record)
      (message "Multiple records match %s" mail)
      (sit-for 1))
    (if record
        (bbdb-record-field (car record) bbdb-sc-attribution-field))))
(define-obsolete-function-alias 'bbdb/sc-consult-attr 'bbdb-sc-get-attrib)

(defun bbdb-sc-set-attrib ()
  "Store attribution in BBDB."
  (let ((from (bbdb-extract-address-components (sc-mail-field "from")))
        (attrib (sc-mail-field "sc-attribution"))
        bbdb-notice-mail-hook record)
    (when (and from attrib bbdb-sc-update-attrib-p
               (not (string-equal attrib bbdb-sc-last-attrib))
               (setq record (bbdb-update-records (list from)
                                                 bbdb-sc-update-records-p)))
      ;; FIXME: What to do if we have multiple matching records?
      (when (cdr record)
        (message "Multiple records match %s" from)
        (sit-for 1))
      (setq record (car record))
      (let ((old (bbdb-record-field record bbdb-sc-attribution-field)))
        ;; Do nothing if the new value equals the old value
        (when (and (not (and old (string-equal old attrib)))
                   (or (not (eq bbdb-sc-update-attrib-p 'query))
                       (y-or-n-p (format (if (bbdb-record-field
                                              record bbdb-sc-attribution-field)
                                             "Change attribution for %s to %s?"
                                           "For %s add attribution %s?")
                                         (bbdb-record-name record) attrib))))
          (bbdb-record-set-field record bbdb-sc-attribution-field attrib)
          (bbdb-change-record record))))))
(define-obsolete-function-alias 'bbdb/sc-set-attr 'bbdb-sc-set-attrib)

;;;###autoload
(defun bbdb-sc-update-from ()
  "Update the \"from\" field in `sc-mail-info'.
If the \"from\" field in `sc-mail-info' contains only a plain mail address,
complement the \"from\" field in `sc-mail-info' with the sender's name in BBDB."
  (let* ((from (sc-mail-field "from"))
         ;; Do not use `bbdb-extract-address-components' that can "invent" names.
         (address (and from (bbdb-decompose-bbdb-address from)))
         ;; FIXME: Should we always update the sender's name in `sc-mail-info'
         ;; if it does not agree with what BBDB says?
         (record (if (and (cadr address) (not (car address)))
                     (bbdb-message-search nil (cadr address))))
         ;; FIXME: What to do if we have multiple matching records?
         (_ (when (cdr record)
              (message "Multiple records match %s" from)
              (sit-for 1)))
         (name (and record (bbdb-record-name (car record)))))
    (if name
        (setcdr (assoc-string "from" sc-mail-info t)
                (format "%s <%s>" name (cadr address))))))
(define-obsolete-function-alias 'bbdb/sc-default 'bbdb-sc-update-from)

;; Insert our hooks

;; Dammit, supercite!  It runs `sc-attribs-postselect-hook' in an
;; environment with the local variable `attribution' that we rely on.
(with-no-warnings (defvar attribution))

;;;###autoload
(defun bbdb-insinuate-sc ()
  "Hook BBDB into Supercite.
Do not call this in your init file.  Use `bbdb-initialize'.
However, this is not the full story.  See bbdb-sc.el for how to fully hook
BBDB into Supercite."
  (add-hook 'sc-post-hook 'bbdb-sc-set-attrib)
  (add-hook 'sc-attribs-postselect-hook
            (lambda ()
              (setq bbdb-sc-last-attrib
                    (if sc-downcase-p
                        (downcase attribution)
                      attribution)))))

(provide 'bbdb-sc)

;;; end of bbdb-sc.el
