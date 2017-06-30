;;; vc-msg.el --- Show Version Control Software (VCS) commit message of current line

;; Copyright (C) 2017 Chen Bin
;;
;; Version: 0.0.1
;; Keywords: git vcs svn hg messenger
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: http://github.com/redguardtoo/vc-msg
;; Package-Requires: ((emacs "24.1"))

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

(require 'cl-lib)
(require 'popup)

(defvar vc-msg-force-vcs nil
  "Extra VCS overrides result of `vc-msg-detect-vcs-type'.
A string like 'git' or 'svn' to lookup `vc-msg-plugins'.")

(defvar vc-msg-known-vcs
  '(("p4" . (let* ((output (shell-command-to-string "p4 client -o"))
                   (root-dir (if (string-match "^Root:[ \t]+\\(.*\\)" output)
                                 (match-string 1 output))))
              ;; 'p4 client -o' has the parent directory of `buffer-file-name'
              (and root-dir
                   (string-match-p (format "^%s" root-dir) buffer-file-name))))
    ("svn" . ".svn")
    ("hg" . ".hg")
    ("git" . ".git"))
  "List of know VCS.
In VCS, the key like 'git' or 'svn' is used to locate plugin
in `vc-msg-plugins'.  The directory name like '.git' or '.svn'
is used to locate VCS root directory.")

(defvar vc-msg-show-at-line-beginning-p t
  "Show the mesesage at beginning of line.")

(defvar vc-msg-plugins
  '((:type "svn" :execute vc-msg-svn-execute :format vc-msg-svn-format)
    (:type "hg" :execute vc-msg-hg-execute :format vc-msg-hg-format)
    (:type "p4" :execute vc-msg-p4-execute :format vc-msg-p4-format)
    (:type "git" :execute vc-msg-git-execute :format vc-msg-git-format))
  "List of VCS plugins.
A plugin is a `plist'. Sample to add a new plugin:

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
If result is `nil', `my-execute' fails silently.
Please check `vc-msg-git-execute' and `vc-msg-git-format' for sample.")

(defvar vc-msg-newbie-friendly-msg "Press q to quit"
  "Extra friendly hint for newbies.")

(defun vc-msg-match-plugin (plugin)
  "Try match plugin.
Return string keyword or `nil'."
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

;;;###autoload
(defun vc-msg-close ()
  (interactive)
  (throw 'vc-msg-loop t))

(defvar vc-msg-map
  (let ((map (make-sparse-keymap)))
    ;; key bindings
    (define-key map (kbd "q") 'vc-msg-close)
    map)
  "Keymap of vc-msg popup.")

(defun vc-msg-show-position ()
  (if vc-msg-show-at-line-beginning-p
      (line-beginning-position)
    (point)))

(defun vc-msg-prompt ()
  "[q]uit")

(defun vc-msg-clean (str)
  "Clean the string (carriage return, for example)."
  (setq str (replace-regexp-in-string "\r\n" "\n" str))
  (replace-regexp-in-string "\r" "\n" str))

;;;###autoload
(defun vc-msg-show ()
  "Show commit messeage of current line"
  (interactive)
  (let* (finish
         (current-vcs-type (vc-msg-detect-vcs-type))
         (plugin (cl-some (lambda (e)
                            (if (string= (plist-get e :type) current-vcs-type) e))
                          vc-msg-plugins)))
    (when plugin
      ;; load the plugin in run time
      (let* ((plugin-file (intern (concat "vc-msg-" (plist-get plugin :type)))))
        (unless (featurep plugin-file)
          (require plugin-file)))

      (let* ((executer (plist-get plugin :execute))
             (formatter (plist-get plugin :format))
             (commit-info (funcall executer
                                   (file-name-nondirectory buffer-file-name)
                                   (line-number-at-pos)))

             message)
        (cond
         ((listp commit-info)
          ;; the message to display
          (setq message (funcall formatter commit-info))

          ;; Hint in minibuffer might be not visible enough
          (if vc-msg-newbie-friendly-msg
              (setq message (format "%s\n\n%s"
                                    message
                                    vc-msg-newbie-friendly-msg)))
          ;; show the message in popup
          (while (not finish)
            (let* ((menu (popup-tip (vc-msg-clean message) :point (vc-msg-show-position) :nowait t)))
              (unwind-protect
                  (setq finish (catch 'vc-msg-loop
                                 (popup-menu-event-loop menu
                                                        vc-msg-map
                                                        'popup-menu-fallback
                                                        :prompt (vc-msg-prompt))
                                 t))
                (popup-delete menu)))))

         ((stringp commit-info)
          ;; Failed. Show the reason.
          (kill-new commit-info)
          (message commit-info))
         (t
          ;; Failed for unknown reason
          (message "Shell command failed.")))))))

(provide 'vc-msg)
;;; vc-msg.el ends here
