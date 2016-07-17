;;; gmail2bbdb.el --- import email and name into bbdb from vcard.

;; Copyright (C) 2014, 2015 Chen Bin
;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/gmail2bbdb
;; Keywords: vcard bbdb email contact gmail
;; Version: 0.0.4

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program ; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; To setup, insert below code into ~/.emacs:
;;   (add-to-list 'load-path "~/.emacs.d/lisp/")
;;   (autoload 'gmail2bbdb-import-file "gmail2bbdb" nil t nil)
;;
;; Usage:
;;   - At https://www.google.com/contacts, click "More->Export->vCard format->Export".
;;     The file "contacts.vcf" will be downloaded.
;;   - Run command "M-x gmail2bbdb-import-file" and select contacts.vcf.
;;     ~/.bbdb will be created.
;;

;;; Code:

(defvar gmail2bbdb-bbdb-file "~/.bbdb"
  "The full path of exported BBDB file.")

(defvar gmail2bbdb-excluded-email-regex-list '("^noreply.*"
                                               "notify.*@disqus.net"
                                               ".*@noreply.github.com$"
                                               "reply.*@reply.github.com"
                                               "do-not-reply@stackoverflow.com")
  "Email matching any regex from the list will NOT be exported")

(defun gmail2bbdb--is-valid-email (eml)
  (let ((i 0) excluded re)
    (while (and (not excluded)
                (< i (length gmail2bbdb-excluded-email-regex-list)))
      (setq re (nth i gmail2bbdb-excluded-email-regex-list))
      (if (string-match re eml)
        (setq excluded t))
      (setq i (1+ i))
      )
    (not excluded)))

;; ["Spolsky" "Joel" nil ("Spolsky Joel") nil nil nil ("spolsky@fogcreek.com") nil nil]
(defun gmail2bbdb--extract-item (str)
  (let (lines fullname firstname lastname emails rlt eml)
    (setq lines (split-string str "[\r\n]+"))
    (dolist (l lines)
      (cond
       ((string-match "^FN:\\(.*\\)" l)
        (setq fullname (match-string 1 l)))

       ((string-match "^N:\\([^;]*\\);\\([^;]*\\);.*" l)
        (setq firstname (match-string 1 l))
        (setq lastname (match-string 2 l)))

       ((string-match "TYPE=[A-Z]+:\\([^ @]+@[^ @]+\\)" l)
        (setq eml (match-string 1 l))
        (if (gmail2bbdb--is-valid-email eml)
            (add-to-list 'emails eml)
          ))
       ))
    (when emails
      (setq rlt (vector firstname lastname nil (list fullname) nil nil nil emails nil nil))
      (format "%S" rlt))
    ))

;;;###autoload
(defun gmail2bbdb-import-file (vcard-file)
  "Import vCards from VCARD-FILE into BBDB.
If VCARD-FILE is a wildcard, import each matching file.  Existing BBDB
records will be REMOVED."
  (interactive "FvCard file (or wildcard): ")
  (let (dst-file rlt)
    (setq dst-file (file-truename gmail2bbdb-bbdb-file))
    (with-temp-buffer
      (insert-file-contents vcard-file)
      (goto-char (point-min))
      ;; Change CRLF into CR if necessary
      ;; (with-temp-file
      ;;     )
      (while (re-search-forward "\r\n" nil t)
        (replace-match "\n" nil nil nil 1))
      (goto-char (point-min))
      (while (re-search-forward
              "^\\([[:alnum:]-]*\\.\\)?*BEGIN:VCARD[\n[:print:][:cntrl:]]*?\\(^\\([[:alnum:]-]*\\.\\)?END:VCARD\\)"
              nil t)
        (let ((vcard (match-string 0)) item)
          (setq item (gmail2bbdb--extract-item vcard))
          (if item (setq rlt (concat rlt "\n" item)))
          ))
      )
    (if rlt
        (with-temp-buffer
          (insert ";; -*- mode: Emacs-Lisp; coding: utf-8; -*-\n")
          (insert ";;; file-format: 7\n")
          (insert rlt)
          (write-file (file-truename gmail2bbdb-bbdb-file)))
      (message "No email found"))
    ))

(provide 'gmail2bbdb)

;;; gmail2bbdb.el ends here
