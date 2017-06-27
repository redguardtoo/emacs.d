;;; vc-msg-p4.el --- extract Perforce(p4) commit message

;; Copyright (C) 2017  Free Software Foundation, Inc.

;; Author: Chen Bin

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:
;;

;;; Code:
(require 'vc-msg-sdk)

(defvar vc-msg-p4-program "p4")

(defvar vc-msg-p4-file-to-url nil
  "(car p4-file-to-url) is the original file prefix.
(cadr p4-file-to-url) is the url prefix.
Please note it supports regular expression.
It's used to convert a local file path to peforce URL.
If you use Windows version p4 in Cygwin Emacs, or Cygwin
version p4 in Window Emacs. You need to convert the path
to URL.")

(defun vc-msg-p4-generate-cmd (opts)
  (format "%s %s" vc-msg-p4-program opts))

(defun vc-msg-p4-anonate-output (cmd)
  (shell-command-to-string cmd))

(defun vc-msg-p4-changelist-output (id)
  (let* ((cmd (vc-msg-p4-generate-cmd (format "change -o %s" id))))
    (shell-command-to-string cmd)))

;;;###autoload
(defun vc-msg-p4-execute (file line-num &optional extra)
  "Use FILE and LINE-NUM to produce p4 command.
Parse the command execution output and return a plist:
'(:id str :author str :date str :message str)."
  ;; convert file to perforce url
  (if (and vc-msg-p4-file-to-url (listp vc-msg-p4-file-to-url))
      (setq file (replace-regexp-in-string (car vc-msg-p4-file-to-url)
                                           (cadr vc-msg-p4-file-to-url)
                                           (file-truename file))))
  ;; there is no one comamnd to get the commit information for current line
  (let* ((cmd (vc-msg-p4-generate-cmd (format "annotate -c -q %s" file)))
         (output (vc-msg-p4-anonate-output cmd))
         id)
    ;; I prefer simpler code:
    ;; if output doesn't match certain text pattern
    ;; we assume the command fail
    (cond
     ((setq id (vc-msg-sdk-extract-id-from-output line-num "^\\([0-9]+\\): " output))
      (when id
        ;; this command should always be successful
        (setq output (vc-msg-p4-changelist-output id))
        (let* (author
               author-time)
          (if (string-match "^User:[ \t]+\\([^ ].*\\)" output)
              (setq author (match-string 1 output)))
          (if (string-match "^Date:[ \t]+\\([^ ].*\\)" output)
              (setq author-time (match-string 1 output)))

          ;; no time zone in output
          (list :id id
                :author author
                :author-time author-time
                :summary (vc-msg-sdk-extract-summary "^Description:" output)))))
     (t
      ;; failed, send back the cmd
      (format "`%s` failed. Do you forget `p4 login`?" cmd)))))

;;;###autoload
(defun vc-msg-p4-format (info)
  (let* ((author (plist-get info :author)))
    (cond
     ((string-match-p "Not Committed Yet" author)
      "*Not Commited Yet*")
     (t
      (format "Commit: %s\nAuthor: %s\nDate: %s\n\n%s"
              (plist-get info :id)
              author
              (plist-get info :author-time)
              (plist-get info :summary))))))

(provide 'vc-msg-p4)
;;; vc-msg-p4.el ends here

