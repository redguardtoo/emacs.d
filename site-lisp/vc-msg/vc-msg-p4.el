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

(defcustom vc-msg-p4-program "p4"
  "Perforce program."
  :type 'string
  :group 'vc-msg)

(defcustom vc-msg-p4-file-to-url nil
  "Please note (car vc-msg-p4-file-to-url) is the original file prefix.
And (cadr vc-msg-p4-file-to-url) is the url prefix.
Please note it supports regular expression.
It's used to convert a local file path to Perforce URL.
If you use Windows version p4 in Cygwin Emacs, or Cygwin
version p4 in Windows Emacs, you need convert the path
to URL."
  :type '(repeat string)
  :group 'vc-msg)

(defun vc-msg-p4-generate-cmd (opts)
  "Generate Perforce CLI from OPTS."
  (format "%s %s" vc-msg-p4-program opts))

(defun vc-msg-p4-anonate-output (cmd)
  "Run CMD in shell."
  (shell-command-to-string cmd))

(defun vc-msg-p4-changelist-output (id)
  "Get the information about ID."
  (let* ((cmd (vc-msg-p4-generate-cmd (format "change -o %s" id))))
    (shell-command-to-string cmd)))

;;;###autoload
(defun vc-msg-p4-execute (file line-num)
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
  "Format the INFO into a string."
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

(defun vc-msg-p4-show-code ()
  "Show code."
  (let* ((info vc-msg-previous-commit-info)
         (cmd (vc-msg-p4-generate-cmd (format "describe -du %s" (plist-get info :id))))
         (rlt (shell-command-to-string cmd)))
    ;; remove p4 verbose bullshit and create a standard diff output
    ;; Don't be too greedy, or else regex will overflow
    (setq rlt (replace-regexp-in-string "^\\(Affected\\|Moved\\) files \.\.\.[\r\n]+"
                                        ""
                                        rlt))
    (setq rlt (replace-regexp-in-string "Differences \.\.\.[\r\n]+" "" rlt))
    ;; one line short description of change list
    (setq rlt (replace-regexp-in-string "Change \\([0-9]+\\) by \\([^ @]+\\)@[^ @]+ on \\([^ \r\n]*\\).*[\r\n \t]+\\([^ \t].*\\)" "\\1 by \\2@\\3 \\4" rlt))
    ;; `diff-mode' friendly format
    (setq rlt (replace-regexp-in-string "^==== \\(.*\\)#[0-9]+ (text) ====[\r\n]+" "--- \\1\n+++ \\1\n" rlt))
    (vc-msg-sdk-get-or-create-buffer
     "vs-msg"
     rlt)))

(defcustom vc-msg-p4-extra
  '(("c" "[c]ode" vc-msg-p4-show-code))
  "Extra keybindings/commands used by `vc-msg-map'.
An example:
'((\"c\" \"[c]ode\" (lambda (message info))
  (\"d\" \"[d]iff\" (lambda (message info))))"
  :type '(repeat sexp)
  :group 'vc-msg)

(provide 'vc-msg-p4)
;;; vc-msg-p4.el ends here

