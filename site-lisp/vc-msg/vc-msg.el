;;; vc-msg.el --- Show commit information of current line

;; Copyright (C) 2017 Chen Bin
;;
;; Version: 0.0.4
;; Keywords: git vc svn hg messenger
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: http://github.com/redguardtoo/vc-msg
;; Package-Requires: ((emacs "24.3") (popup "0.5.0"))

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
;; You only need run "M-x vc-msg-show" and follow the hint.

;; The current Version Control Software (VCS) is detected automatically.
;; If you need force the VCS type (Peforce, for example),
;; it's only one liner setup:
;;   (setq vc-msg-force-vcs "p4")
;;
;; You can add hook to `vc-msg-hook',
;;   (defun vc-msg-hook-setup (vcs-type commit-info)
;;     ;; copy commit id to clipboard
;;     (message (format "%s\n%s\n%s\n%s"
;;                      (plist-get commit-info :id)
;;                      (plist-get commit-info :author)
;;                      (plist-get commit-info :author-time)
;;                      (plist-get commit-info :author-summary))))
;;   (add-hook 'vc-msg-hook 'vc-msg-hook-setup)
;;
;; Hook `vc-msg-show-code-hook' is hook after code of certain commit
;; is displayed. Here is sample code:
;;   (defun vc-msg-show-code-setup ()
;;     ;; use `ffip-diff-mode' from package find-file-in-project instead of `diff-mode'
;;     (ffip-diff-mode))
;;   (add-hook 'vc-msg-show-code-hook 'vc-msg-show-code-setup)
;;
;; Perforce is detected automatically.  You don't need any manual setup.
;; But if you use Windows version of perforce CLI in Cygwin Emacs, we
;; provide the variable `vc-msg-p4-file-to-url' to convert file path to
;; ULR so Emacs and Perforce CLI could communicate the file location
;; correctly:
;;   (setq vc-msg-p4-file-to-url '(".*/proj1" "//depot/development/proj1"))
;;
;; The program provides a plugin framework so you can easily write a
;; plugin to support any alien VCS.  Please use "vc-msg-git.el" as a sample.

;;; Code:

(require 'cl-lib)
(require 'popup)
(require 'vc-msg-sdk)

(defgroup vc-msg nil
  "vc-msg"
  :group 'vc)

(defcustom vc-msg-force-vcs nil
  "Extra VCS overrides result of `vc-msg-detect-vcs-type'.
A string like 'git' or 'svn' to lookup `vc-msg-plugins'."
  :type 'string)

(defcustom vc-msg-copy-id-to-kill-ring t
  "Copy commit id/hash/changelist into `kill-ring' when `vc-msg-show'."
  :type 'boolean)

(defcustom vc-msg-known-vcs
  '(("p4" . (let* ((output (shell-command-to-string "p4 client -o"))
                   (root-dir (if (string-match "^Root:[ \t]+\\(.*\\)" output)
                                 (match-string 1 output))))
              ;; 'p4 client -o' has the parent directory of `buffer-file-name'
              (and root-dir
                   (string-match-p (format "^%s" root-dir) buffer-file-name))))
    ("svn" . ".svn")
    ("hg" . ".hg")
    ("git" . ".git"))
  "List of known VCS.
In VCS, the key like 'git' or 'svn' is used to locate plugin
in `vc-msg-plugins'.  The directory name like '.git' or '.svn'
is used to locate VCS root directory."
  :type '(repeat sexp))

(defcustom vc-msg-show-at-line-beginning-p t
  "Show the mesesage at beginning of line."
  :type 'boolean)

(defcustom vc-msg-plugins
  '((:type "svn" :execute vc-msg-svn-execute :format vc-msg-svn-format :extra vc-msg-svn-extra)
    (:type "hg" :execute vc-msg-hg-execute :format vc-msg-hg-format :extra vc-msg-hg-extra)
    (:type "p4" :execute vc-msg-p4-execute :format vc-msg-p4-format :extra vc-msg-p4-extra)
    (:type "git" :execute vc-msg-git-execute :format vc-msg-git-format :extra vc-msg-git-extra))
  "List of VCS plugins.
A plugin is a `plist'.  Sample to add a new plugin:

  (defun my-execute (file line &optional extra))
  (defun my-format (info))
  (add-to-list 'vc-msg-plugins
               '(:type \"git\"
                 :execute my-execute
                 :format my-format)

`vc-msg-show' finds correct VCS plugin and show commit message:

  (popup-tip (my-format (my-execute buffer-file-name (line-number-at-pos)))).

The result of `my-execute' is blackbox outside of plugin.
But if result is string, `my-execute' fails and returns error message.
If result is nil, `my-execute' fails silently.
Please check `vc-msg-git-execute' and `vc-msg-git-format' for sample."
  :type '(repeat sexp))

(defcustom vc-msg-newbie-friendly-msg "Press q to quit"
  "Extra friendly hint for newbies."
  :type 'string)

(defcustom vc-msg-hook nil
  "Hook for `vc-msg-show'.
The first parameter of hook is VCS type (\"git\", fore example).
The second parameter is the `plist' of extrated information,
- `(plist-get param :id)`
- `(plist-get param :author)`
- `(plist-get param :author-time)`
- `(plist-get param :author-summary)`
Other extra fields of param may exists which is produced by plugin
and is a blackbox to 'vc-msg.el'."
  :type 'hook)

(defcustom vc-msg-show-code-hook nil
  "Hook after showing the code in a new buffer."
  :type 'hook)

(defcustom vc-msg-previous-commit-info nil
  "Store the data extracted by (plist-get :execute plugin)."
  :type 'sexp)

(defun vc-msg-match-plugin (plugin)
  "Try match PLUGIN.  Return string keyword or nil."
  (let* ((type (car plugin))
         (algorithm (cdr plugin)))
    (cond
     ((stringp algorithm)
      ;; shell command
      (if (locate-dominating-file default-directory algorithm)
          type))
     ((functionp algorithm)
      ;; execute function
      (if (funcall plugin)
          type))
     ((consp plugin)
      ;; execute lisp expression
      (if (funcall `(lambda () ,algorithm))
          type)))))

(defun vc-msg-detect-vcs-type ()
  "Return VCS type or nil."
  (cond
   ;; use `vc-msg-force-vcs' if it's not nil
   (vc-msg-force-vcs
    vc-msg-force-vcs)
   (t
    ;; or some "smart" algorithm will figure out the correct VCS
    (if (listp vc-msg-known-vcs)
        (cl-some #'vc-msg-match-plugin
                 vc-msg-known-vcs)))))

(defun vc-msg-find-plugin ()
  "Find plugin automatically using `vc-msg-plugins'."
  (let* ((plugin (cl-some (lambda (e)
                            (if (string= (plist-get e :type) current-vcs-type) e))
                          vc-msg-plugins)))
    (if plugin
        ;; load the plugin in run time
        (let* ((plugin-file (intern (concat "vc-msg-" (plist-get plugin :type)))))
          (unless (featurep plugin-file)
            (require plugin-file))))
    plugin))

(defun vc-msg-close ()
  "Close the popup."
  (interactive)
  (throw 'vc-msg-loop t))

(defun vc-msg-get-friendly-id (plugin commit-info)
  "Show user the short id if PLUGIN and COMMIT-INFO is correct."
  (let* ((vcs-type (plist-get plugin :type))
         (id (plist-get commit-info :id)))
    (if (member vcs-type '("git" "hg"))
        (vc-msg-sdk-short-id id)
      id)))

(defun vc-msg-copy-all ()
  "Copy the content of popup into `kill-ring'."
  (interactive)
  (let* ((plugin (vc-msg-find-plugin))
         formatter)
    (when plugin
      (setq formatter (plist-get plugin :format))
      (kill-new (funcall formatter vc-msg-previous-commit-info))
      (message "Copy all from commit %s"
               (vc-msg-get-friendly-id plugin
                                       vc-msg-previous-commit-info)))
    (vc-msg-close)))

(defvar vc-msg-map
  (let ((map (make-sparse-keymap)))
    ;; key bindings
    (define-key map (kbd "q") 'vc-msg-close)
    (define-key map (kbd "w") 'vc-msg-copy-all)
    map)
  "Keymap of vc-msg popup.")

(defun vc-msg-show-position ()
  "Where to show the popup."
  (if vc-msg-show-at-line-beginning-p
      (line-beginning-position)
    (point)))

(defun vc-msg-prompt (extra-commands)
  "Show popup prompt for built in commands and EXTRA-COMMANDS."
  (concat "[q]uit [w]Copy all "
          (mapconcat #'cadr extra-commands " ")))

(defun vc-msg-clean (str)
  "Clean the STR carriage return, for example)."
  (setq str (replace-regexp-in-string "\r\n" "\n" str))
  (replace-regexp-in-string "\r" "\n" str))

(defun vc-msg-update-keymap (extra-commands)
  "EXTRA-COMMANDS is like:
'((\"d\" \"details\" (lambda (message \"%s\" info))
  (\"a\" \"diff\" (lambda (message \"%s\" info))))"
  (if extra-commands
      (dolist (c extra-commands)
        (let* ((key (car c))
               (fn (nth 2 c)))
          (define-key vc-msg-map (kbd key)
            `(lambda ()
               (interactive)
               (funcall (quote ,fn))
               ;; have to happend after `funcall'
               (vc-msg-close))))))
  vc-msg-map)

;;;###autoload
(defun vc-msg-show ()
  "Show commit message of current line."
  (interactive)
  (let* (finish
         (current-vcs-type (vc-msg-detect-vcs-type))
         (plugin (vc-msg-find-plugin)))
    (if plugin
      (let* ((executer (plist-get plugin :execute))
             (formatter (plist-get plugin :format))
             (commit-info (funcall executer
                                   (file-name-nondirectory buffer-file-name)
                                   (line-number-at-pos)))
             message
             (extra-commands (symbol-value (plist-get plugin :extra))))

        (vc-msg-update-keymap extra-commands)

        (cond
         ((listp commit-info)
          ;; the message to display
          (setq message (funcall formatter commit-info))

          ;; Hint in minibuffer might be not visible enough
          (if vc-msg-newbie-friendly-msg
              (setq message (format "%s\n\n%s"
                                    message
                                    vc-msg-newbie-friendly-msg)))

          (setq vc-msg-previous-commit-info commit-info)

          ;; copy the commit it/hash/changelist
          (when vc-msg-copy-id-to-kill-ring
            (let* ((id (vc-msg-get-friendly-id plugin commit-info)))
              (kill-new id)
              (message "%s => kill-ring" id)))

          ;; show the message in popup
          (while (not finish)
            (let* ((menu (popup-tip (vc-msg-clean message) :point (vc-msg-show-position) :nowait t)))
              (unwind-protect
                  (setq finish (catch 'vc-msg-loop
                                 (popup-menu-event-loop menu
                                                        ;; update `vc-msg-map' with extra keybindgs&commands
                                                        vc-msg-map
                                                        'popup-menu-fallback
                                                        :prompt (vc-msg-prompt extra-commands))
                                 t))
                (popup-delete menu))))

          (run-hook-with-args 'vc-msg-hook current-vcs-type commit-info))

         ((stringp commit-info)
          ;; Failed. Show the reason.
          (kill-new commit-info)
          (message commit-info))
         (t
          ;; Failed for unknown reason
          (message "Shell command failed.")))))))

(provide 'vc-msg)
;;; vc-msg.el ends here
