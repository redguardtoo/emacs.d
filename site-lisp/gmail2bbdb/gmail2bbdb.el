;;; gmail2bbdb.el --- import email and name into bbdb from vcard

;; Copyright (C) 2014 Chen Bin
;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/gmail2bbdb
;; Keywords: vcard bbdb email contact gmail
;; Version: 0.0.1

;; This file is not part of GNU Emacs.

;; This file is free software (GPLv3 License)

;; How to set it up:
;; See README.org which is distributed with this file

;;; Code:

(defvar gmail2bbdb-bbdb-file "~/.bbdb.el")

;; ["Spolsky" "Joel" nil ("Spolsky Joel") nil nil nil ("spolsky@fogcreek.com") nil nil]
;; ["捷英" "沈" nil ("沈捷英") nil nil nil ("jieyingsh@gmail.com" "140113204@sohu.com" "jieyingsh@hotmail.com" "jieyingshen@gmail.com") nil nil]
(defun gmail2bbdb--extract-item (str)
  (let (lines fullname firstname lastname emails rlt)
    (setq lines (split-string str "[\r\n]+"))
    (dolist (l lines)
      (cond
       ((string-match "^FN:\\(.*\\)" l)
        (setq fullname (match-string 1 l)))
       ((string-match "^N:\\([^;]*\\);\\([^;]*\\);.*" l)
        (setq firstname (match-string 1 l))
        (setq lastname (match-string 2 l)))
       ((string-match "TYPE=[A-Z]+:\\([^ @]+@[^ @]+\\)" l)
        (add-to-list 'emails (match-string 1 l)))
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
          (write-file gmail2bbdb-bbdb-file))
      (message "No email found"))
    ))

(provide 'gmail2bbdb)

;;; gmail2bbdb.el ends here
