;;; vc-msg-git.el --- extract git commit message

;; Copyright (C) 2017  Free Software Foundation, Inc.

;; Author: Chen Bin

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
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

(defcustom vc-msg-git-show-commit-function nil
  "The function to show git commit.  Revision is the parameter of the function.
It can be set the value like `magit-show-commit'."
  :type 'function
  :group 'vc-msg)

(defun vc-msg-git-shell-output (cmd)
  "Generate clean output by running CMD in shell."
  (let* ((default-directory (vc-msg-sdk-git-rootdir)))
    (string-trim (shell-command-to-string cmd))))

(defun vc-msg-git-generate-cmd (opts)
  "Generate Git command from OPTS."
  (format "%s --no-pager %s" vc-msg-git-program opts))

(defun vc-msg-git-parse-blame-output (output)
  "Parse git blame OUTPUT."
  (let* (id
         author
         author-time
         author-tz
         filename
         summary
         (lines (split-string output "[\n\r]+"))
         (first-line (nth 0 lines))
         (prev-commit-line-num (nth 1 (split-string first-line " ")))
         (code (string-trim (nth (1- (length lines)) lines))))
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
    (if (string-match "^filename +\\([^ ].*\\)" output)
        (setq filename (match-string 1 output)))
    (list :id id
          :author author
          :author-time author-time
          :author-tz author-tz
          :line_num prev-commit-line-num
          :code code
          :filename filename
          :summary summary)))

;;;###autoload
(defun vc-msg-git-blame-arguments (line-num)
  "Git blame at LINE-NUM.
Note git option `-C' track text copied elsewhere,
`-M' tracked moved content inside file.
See https://www.kernel.org/pub/software/scm/git/docs/git-blame.html"
  ;; @see https://stackoverflow.com/questions/15769298/git-blame-correct-author-after-merge
  (format "blame -C -M -w -L %s,+1 --no-merges --porcelain" line-num))

(defmacro vc-msg-git-valid-p (output)
  "OUTPUT is valid."
  `(string-match-p "^author " ,output))

(defun vc-msg-git-find-blame-cmd-recursively (command info str common-opts)
  "Git blame COMMAND is executed and output is extracted into INFO.
Find commit id from the blame, blame again with the parent commit id.
If the new blame output does not contain STR, return the original command.
COMMON-OPTS is used to build new blame command."
  (let* ((id (plist-get info :id))
         ;; file is a relative path to git root
         (file (plist-get info :filename))
         (line-num (plist-get info :line-num))
         (next-cmd (vc-msg-git-generate-cmd (format "%s %s^ -- %s"
                                                    common-opts
                                                    id
                                                    file)))

         (next-output (vc-msg-git-shell-output next-cmd))
         next-info)
    (cond
     ((not (and (vc-msg-git-valid-p next-output)
                (setq next-info (vc-msg-git-parse-blame-output next-output))
                (string-match-p (regexp-quote str)
                                (plist-get next-info :code))))
      command)
     (t
      (vc-msg-git-find-blame-cmd-recursively next-cmd
                                             next-info
                                             str
                                             common-opts)))))

(defun vc-msg-git-generate-blame-cmd (file line-num version)
  "Generate git blame command from FILE, LINE-NUM and VERSION."
  (let* ((str (vc-msg-sdk-selected-string))
         output
         info
         (common-opts (vc-msg-git-blame-arguments line-num))
         (cmd (vc-msg-git-generate-cmd (format "%s %s -- %s"
                                               common-opts
                                               version
                                               file))))
    (cond
     ((not str)
      cmd)
     ((vc-msg-git-valid-p (setq output (vc-msg-git-shell-output cmd)))
      (setq info (vc-msg-git-parse-blame-output output))
      (vc-msg-git-find-blame-cmd-recursively cmd
                                             info
                                             (string-trim str)
                                             common-opts)))))

;;;###autoload
(defun vc-msg-git-execute (file line-num version)
  "Use FILE, LINE-NUM and VERSION to produce git command.
Parse the command execution output and return a plist:
'(:id str :author str :author-time str :summary str)."
  ;; convert full file path to path relative to git directory
  ;; because the command should always be executed in git root.
  (setq file (file-relative-name file (vc-msg-sdk-git-rootdir)))
  (let* ((cmd (vc-msg-git-generate-blame-cmd file line-num version))
         (output (vc-msg-git-shell-output cmd)))

    ;; I prefer simpler code:
    ;; if output doesn't match certain text pattern, the command fails
    (cond
     ((vc-msg-git-valid-p output)
      (vc-msg-git-parse-blame-output output))
     (t
      (format "`%s` failed." cmd)))))

;;;###autoload
(defun vc-msg-git-format (info)
  "Format the message for popup from INFO."
  (let* ((author (plist-get info :author)))
    (cond
     ((string-match-p "Not Committed Yet" author)
      "* Not Committed Yet*")
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
         (id (plist-get info :id)))
    (cond
     (vc-msg-git-show-commit-function
      (funcall vc-msg-git-show-commit-function id))
     (t
      ;; show one commit information
      (vc-msg-sdk-get-or-create-buffer
       "vs-msg"
       (vc-msg-git-shell-output (vc-msg-git-generate-cmd (format "show %s" id))))))))

(defcustom vc-msg-git-extra
  '(("c" "[c]ode" vc-msg-git-show-code))
  "Extra keybindings/commands used by `vc-msg-map'.
An example:
'((\"c\" \"[c]ode\" (lambda () (message \"%s\" vc-msg-previous-commit-info))
  (\"d\" \"[d]iff\" (lambda () (message \"%s\" vc-msg-previous-commit-info))))"
  :type '(repeat sexp)
  :group 'vc-msg)

(provide 'vc-msg-git)
;;; vc-msg-git.el ends here

