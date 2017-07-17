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
(require 'vc-msg-sdk)

(defcustom vc-msg-git-program "git"
  "Git program."
  :type 'string
  :group 'vc-msg)

(defun vc-msg-git-blame-output (cmd)
  "Generate blame output by running CMD in shell."
  (shell-command-to-string cmd))

(defun vc-msg-git-generate-cmd (opts)
  "Generate Git command from OPTS."
  (format "%s --no-pager %s" vc-msg-git-program opts))

;;;###autoload
(defun vc-msg-git-blame-arguments (file line-num)
  "Git blame FILE at LINE-NUM.
Note git option `-C' track text copied elsewhere,
`-M' tracked moved content inside file.
See https://www.kernel.org/pub/software/scm/git/docs/git-blame.html"
  (format "blame -C -M -w -L %d,+1 --porcelain %s" line-num file))

;;;###autoload
(defun vc-msg-git-execute (file line-num)
  "Use FILE and LINE-NUM to produce git command.
Parse the command execution output and return a plist:
'(:id str :author str :author-time str :summary str)."
  (let* ((cmd (vc-msg-git-generate-cmd (vc-msg-git-blame-arguments file line-num)))
         (output (vc-msg-git-blame-output cmd)))
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
      (format "`%s` failed." cmd)))))

;;;###autoload
(defun vc-msg-git-format (info)
  "Format the message for popup from INFO."
  (let* ((author (plist-get info :author)))
    (cond
     ((string-match-p "Not Committed Yet" author)
      "* Not Commited Yet*")
     (t
      (format "Commit: %s\nAuthor: %s\nDate: %s\nTimezone: %s\n\n%s"
              (vc-msg-sdk-short-id (plist-get info :id))
              author
              (vc-msg-sdk-format-datetime (plist-get info :author-time))
              (vc-msg-sdk-format-timezone (plist-get info :author-tz))
              (plist-get info :summary))))))

(defun vc-msg-git-show-code ()
  "Show code."
  (let* ((info vc-msg-previous-commit-info)
         (cmd (vc-msg-git-generate-cmd (format "show %s" (plist-get info :id)))))
    (vc-msg-sdk-get-or-create-buffer
     "vs-msg"
     (shell-command-to-string cmd))))

(defcustom vc-msg-git-extra
  '(("c" "[c]ode" vc-msg-git-show-code))
  "Extra keybindings/commands used by `vc-msg-map'.
An example:
'((\"c\" \"[c]ode\" (lambda (message info))
  (\"d\" \"[d]iff\" (lambda (message info))))"
  :type '(repeat sexp)
  :group 'vc-msg)

(provide 'vc-msg-git)
;;; vc-msg-git.el ends here

