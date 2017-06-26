;;; vc-msg-p4.el --- extract perforce(p4) commit message

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
(defvar vc-msg-p4-program "p4")

;;;###autoload
(defun vc-msg-p4-program-arguments (file line)
  (format "--no-pager blame -w -L %d,+1 --porcelain %s" line file))

(defun vc-msg-p4-generate-cmd (opts)
  (format "%s %s" vc-msg-p4-program opts))

;;;###autoload
(defun vc-msg-p4-execute (file line &optional extra)
  "Use FILE and LINE to produce p4 command.
Parse the command execution output and return a plist:
'(:id str :author str :date str :message str)."
  ;; there is no one comamnd to get the commit information for current line
  (let* ((cmd (vc-msg-p4-generate-cmd (format "annotate -c -q %s" file)))
         (output (shell-command-to-string cmd))
         cur-line
         changelist)
    ;; I prefer simpler code:
    ;; if output doesn't match certain text pattern
    ;; we assum the command fail
    (cond
     ((string-match-p "^[0-9]+: " output)
      (with-temp-buffer
        (insert output)
        (goto-line line)
        (setq cur-line (buffer-substring-no-properties (line-beginning-position)
                                                       (line-end-position)))
        (if (string-match "^\\([0-9]+\\): " cur-line)
            (setq changelist (match-string 1 cur-line))))
      (when changelist
        ;; this command should always be successful
        (setq output (shell-command-to-string (vc-msg-p4-generate-cmd (format "change -o %s" changelist))))
        (let* (id
               author
               author-time
               summary-beg
               summary)
          (if (string-match "^Change:[ \t]+\\([0-9]+\\)" output)
              (setq id (match-string 1 output)))
          (if (string-match "^User:[ \t]+\\([^ ].*\\)" output)
              (setq author (match-string 1 output)))
          (if (string-match "^Date:[ \t]+\\([^ ].*\\)" output)
              (setq author-time (match-string 1 output)))
          ;; no time zone in output

          ;; last paragraph is description
          (setq summary-beg (+ (string-match "^Description:" output)
                              (length "Description:")))
          (setq summary (substring-no-properties output
                                                 summary-beg))
          ;; remove leading white space
          (setq summary (replace-regexp-in-string "^[ \t]+\\|[ \t]+$" "" summary))
          ;; strip summary
          (setq summary
                (replace-regexp-in-string "\\`[ \t\n]*" "" (replace-regexp-in-string "[ \t\n]*\\'" "" summary)))
          (list :id id
                :author author
                :author-time author-time
                :summary summary))))
     (t
      ;; failed, send back the cmd
      cmd))))

;;;###autoload
(defun vc-msg-p4-format (info)
  (let* ((author (plist-get info :author)))
    (cond
     ((string-match-p "Not Committed Yet" author)
      "* Not Commited Yet*")
     (t
      (format "Commit: %s\nAuthor: %s\nDate: %s\n\n%s"
              (plist-get info :id)
              author
              (plist-get info :author-time)
              (plist-get info :summary))))))

(provide 'vc-msg-p4)
;;; vc-msg-p4.el ends here

