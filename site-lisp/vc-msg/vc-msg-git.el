;;; vc-msg-git.el --- extract git commit message

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
(defvar vc-msg-git-program "git")

;;;###autoload
(defun vc-msg-git-program-arguments (file line)
  (format "--no-pager blame -w -L %d,+1 --porcelain %s" line file))

;;;###autoload
(defun vc-msg-git-execute (file line &optional extra)
  "Use FILE and LINE to produce git command.
Parse the command execution output and return a plist:
'(:id str :author str :date str :message str)."
  (let* ((cmd (format "%s %s"
                      vc-msg-git-program
                      (vc-msg-git-program-arguments file line)))
         (output (shell-command-to-string cmd))
         ;; (output "9999 \nauthor cb\nauthor-time 292993\nauthor-tz 0900\nsummary abcde")
         )
    ;; I prefer simpler code:
    ;; if output doesn't match certain text pattern
    ;; we assum the command fail
    (cond
     ((string-match-p "^author " output)
      (let* (id
             author
             author-time
             author-tz
             summary
             (first-line (nth 0 (split-string output "[\n\r]+"))))
        (if (string-match "^\\([a-z0-9A-Z]+\\) " output)
            (setq id (match-string 1 output)))
        (if (string-match "^author +\\([^ ].*\\)" output)
            (setq author (match-string 1 output)))
        (if (string-match "^author-time +\\([^ ].*\\)" output)
            (setq author-time (match-string 1 output)))
        (if (string-match "^author-time +\\([^ ].*\\)" output)
            (setq author-time (match-string 1 output)))
        (if (string-match "^author-tz +\\([^ ].*\\)" output)
            (setq author-tz (match-string 1 output)))
        (if (string-match "^summary +\\([^ ].*\\)" output)
            (setq summary (match-string 1 output)))
        (list :id id
              :author author
              :author-time author-time
              :author-tz author-tz
              :summary summary)))
     (t
      cmd))))

(defun vc-msg-git-format-timezone (zone)
  (concat zone
          " "
          (cond
           ((string= zone "-1200")
            "Eniwetok")
           ((string= zone "-1100")
            "Midway Island")
           ((string= zone "-1000")
            "Hawaii")
           ((string= zone "-0900")
            "Alaska")
           ((string= zone "-0800")
            "Los Angeles")
           ((string= zone "-0700")
            "Salt Lake City")
           ((string= zone "-0600")
            "Chicago")
           ((string= zone "-0500")
            "Boston")
           ((string= zone "-0400")
            "Caracas")
           ((string= zone "-0300")
            "Rio")
           ((string= zone "-0200")
            "Mid-Atlantic")
           ((string= zone "-0100")
            "Azores")
           ((string= zone "+0100")
            "Berlin")
           ((string= zone "+0200")
            "Cario")
           ((string= zone "+0300")
            "Moscow")
           ((string= zone "+0400")
            "Baku")
           ((string= zone "+0500")
            "New Dehli")
           ((string= zone "+0600")
            "Kathmandu")
           ((string= zone "+0700")
            "Bangkok")
           ((string= zone "+0800")
            "Shanghai")
           ((string= zone "+0900")
            "Tokyo")
           ((string= zone "+1000")
            "Sydney")
           ((string= zone "+1100")
            "Solomon Island")
           ((string= zone "+1200")
            "Auckland")
           (t
            ""))))

;;;###autoload
(defun vc-msg-git-format (info)
  (let* ((author (plist-get info :author)))
    (cond
     ((string-match-p "Not Committed Yet" author)
      "* Not Commited Yet*")
     (t
      (format "Commit: %s\nAuthor: %s\nDate: %s\nTimezone: %s\n\n%s"
              (substring (plist-get info :id) 0 8)
              author
              (current-time-string (seconds-to-time (string-to-number (plist-get info :author-time))))
              (vc-msg-git-format-timezone (plist-get info :author-tz))
              (plist-get info :summary))
      ))))

(provide 'vc-msg-git)
;;; vc-msg-git.el ends here

