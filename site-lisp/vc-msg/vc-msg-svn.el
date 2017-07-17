;;; vc-msg-svn.el --- extract Perforce(svn) commit message

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

(defcustom vc-msg-svn-program "svn"
  "Subversion program."
  :type 'string
  :group 'vc-msg)

(defun vc-msg-svn-generate-cmd (opts)
  "Generate Subversion CLI from OPTS."
  (format "LANG=C %s %s" vc-msg-svn-program opts))

(defun vc-msg-svn-blame-output (cmd)
  "Generate blame output by running CMD in shell."
  (shell-command-to-string cmd))

(defun vc-msg-svn-changelist-output (id)
  "Generate commit information from ID."
  (let* ((cmd (vc-msg-svn-generate-cmd (format "log -r %s" id))))
    (shell-command-to-string cmd)))

;;;###autoload
(defun vc-msg-svn-execute (file line-num)
  "Use FILE and LINE-NUM to produce svn command.
Parse the command execution output and return a plist:
'(:id str :author str :date str :message str)."
  ;; there is no one comamnd to get the commit information for current line
  (let* ((cmd (vc-msg-svn-generate-cmd (format "blame %s" file)))
         (output (vc-msg-svn-blame-output cmd))
         id)
    ;; I prefer simpler code:
    ;; if output doesn't match certain text pattern
    ;; we assum the command fail
    (cond
     ((setq id (vc-msg-sdk-extract-id-from-output line-num
                                                  "^[ \t]+\\\([0-9]+\\)[ \t]+"
                                                  output))
      (when id
        ;; this command should always be successful
        (setq output (vc-msg-svn-changelist-output id))
        ;; clean output
        (setq output (replace-regexp-in-string "^-+[\r\n]*" "" output))
        (let* ((first-line (nth 0 (split-string output "[\r\n]+")))
               (grids (split-string first-line "[ \t]*|[ \t]*"))
               author
               author-time
               author-tz
               summary)
          (setq author (nth 1 grids))
          (setq author-time (nth 2 grids))
          (when (string-match "\\(.*\\)[ \t]+\\([+-][0-9]\\{4\\}\\).*"
                              author-time)
            (setq author-tz (match-string 2 author-time))
            (setq author-time (match-string 1 author-time)))
          (setq summary (vc-msg-sdk-trim (substring-no-properties output
                                                                  (length first-line))))
          (list :id id
                :author author
                :author-time author-time
                :author-tz author-tz
                :summary summary))))
     (t
      ;; failed, send back the cmd
      (format "`%s` failed." cmd)))))

;;;###autoload
(defun vc-msg-svn-format (info)
  "Format the message to display from INFO."
  (format "Commit: %s\nAuthor: %s\nDate: %s\nTimezone: %s\n\n%s"
          (plist-get info :id)
          (plist-get info :author)
          (plist-get info :author-time)
          (vc-msg-sdk-format-timezone (plist-get info :author-tz))
          (plist-get info :summary)))

(defun vc-msg-svn-show-code ()
  "Show code."
  (let* ((info vc-msg-previous-commit-info)
         (cmd (vc-msg-svn-generate-cmd (format "diff --internal-diff -c %s" (plist-get info :id)))))
    (vc-msg-sdk-get-or-create-buffer
     "vs-msg"
     (shell-command-to-string cmd))))

(defcustom vc-msg-svn-extra
  '(("c" "[c]ode" vc-msg-svn-show-code))
  "Extra keybindings/commands used by `vc-msg-map'.
An example:
'((\"c\" \"[c]ode\" (lambda (message info))
  (\"d\" \"[d]iff\" (lambda (message info))))"
  :type '(repeat sexp)
  :group 'vc-msg)

(provide 'vc-msg-svn)
;;; vc-msg-svn.el ends here

