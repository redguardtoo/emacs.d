;;; js-comint.el --- Run a JavaScript interpreter in an inferior process window.

;;; Copyright (C) 2008 Paul Huff
;;; Copyright (C) 2015 Stefano Mazzucco
;;; Copyright (C) 2016 Chen Bin

;;; Author: Paul Huff <paul.huff@gmail.com>, Stefano Mazzucco <MY FIRST NAME - AT - CURSO - DOT - RE>
;;; Maintainer: Chen Bin <chenbin.sh AT gmail DOT com>
;;; Created: 15 Feb 2014
;;; Version: 1.0.0
;;; URL: https://github.com/redguardtoo/js-comint
;;; Package-Requires: ()
;;; Keywords: javascript, node, inferior-mode, convenience

;; This file is NOT part of GNU Emacs.

;;; License:

;; js-comint.el is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or
;; at your option any later version.

;; js-comint.el is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING, or type `C-h C-c'. If
;; not, write to the Free Software Foundation at this address:

;;   Free Software Foundation
;;   51 Franklin Street, Fifth Floor
;;   Boston, MA 02110-1301
;;   USA

;;; Commentary:

;; js-comint.el is a comint mode for Emacs which allows you to run a
;; compatible javascript repl like Node.js/Spidermonkey/Rhino inside Emacs.
;; It also defines a few functions for sending javascript input to it
;; quickly.

;; Usage:
;;  Put js-comint.el in your load path
;;  Add (require 'js-comint) to your .emacs or ~/.emacs.d/init.el
;;
;;  Optionally, set the `inferior-js-program-command' string
;;  and the `inferior-js-program-arguments' list to the executable that runs
;;  the JS interpreter and the arguments to pass to it respectively.
;;  E.g., the default is:
;;  (setq inferior-js-program-command "node")
;;  (setq inferior-js-program-arguments '("--interactive"))

;;  E.g. Set up the Rhino JAR downloaded from
;;  https://github.com/mozilla/rhino
;;  (setq inferior-js-program-command "java")
;;  (setq inferior-js-program-arguments '("-jar" "/absolute/path/to/rhino/js.jar"))

;;  Do: `M-x run-js'
;;  Away you go.
;;  `node_modules' is *automatically* searched and appended into environment
;;  variable `NODE_PATH'. So 3rd party javascript is usable out of box.

;;  If you have nvm, you can select the versions of node.js installed and run
;;  them.  This is done thanks to nvm.el.
;;  Please note nvm.el is optional. So you need *manually* install it.
;;  To enable nvm support, run `js-do-use-nvm'.
;;  The first time you start the JS interpreter with run-js, you will be asked
;;  to select a version of node.js
;;  If you want to change version of node js, run `js-select-node-version'
;;
;;  `js-clear' clears the content of REPL.
;;
;; You may get cleaner output by following setup (highly recommended):
;;
;;   (defun inferior-js-mode-hook-setup ()
;;     (add-hook 'comint-output-filter-functions 'js-comint-process-output))
;;   (add-hook 'inferior-js-mode-hook 'inferior-js-mode-hook-setup t)
;;
;;  `js-comint-process-output' uses `js-comint-drop-regexp' which could be
;;  customized by users.
;;
;;  You can add the following lines to your .emacs to take advantage of
;;  cool keybindings for sending things to the javascript interpreter inside
;;  of Steve Yegge's most excellent js2-mode.
;;
;;   (add-hook 'js2-mode-hook
;;             (lambda ()
;;               (local-set-key (kbd "C-x C-e") 'js-send-last-sexp)
;;               (local-set-key (kbd "C-M-x") 'js-send-last-sexp-and-go)
;;               (local-set-key (kbd "C-c b") 'js-send-buffer)
;;               (local-set-key (kbd "C-c C-b") 'js-send-buffer-and-go)
;;               (local-set-key (kbd "C-c l") 'js-load-file-and-go)))

;;; Code:

(require 'comint)

(defgroup inferior-js nil
  "Run a javascript process in a buffer."
  :group 'inferior-js)

(defcustom inferior-js-program-command "node"
  "JavaScript interpreter."
  :group 'inferior-js)

(defcustom inferior-js-program-arguments '("--interactive")
  "List of command line arguments to pass to the JavaScript interpreter."
  :group 'inferior-js)

(defcustom inferior-js-mode-hook nil
  "*Hook for customizing inferior-js mode."
  :type 'hook
  :group 'inferior-js)

(defcustom js-use-nvm nil
  "When t, use NVM.  Requires nvm.el."
  :type 'boolean
  :group 'inferior-js)

(defvar inferior-js-buffer nil
  "Name of the inferior JavaScript buffer.")

(defvar js-prompt-regexp "^\\(?:> \\)"
  "Prompt for `run-js'.")

(defvar js-comint-drop-regexp
  "^[ \t]*undefined[\r\n]+"
  "Regexp that matches text to silently drop.")

(defvar js-nvm-current-version nil
  "Current version of node.")

(defun js-list-nvm-versions (prompt)
  "List all available node versions from nvm prompting the user with PROMPT.
Return a string representing the node version."
  (let ((candidates (sort (mapcar 'car (nvm--installed-versions)) 'string<)))
    (completing-read prompt
                     candidates nil t nil
                     nil
                     (car candidates))))
;;;###autoload
(defun js-do-use-nvm ()
  "Enable nvm."
  (setq js-use-nvm t))

;;;###autoload
(defun js-select-node-version (&optional version)
  "Use a given VERSION of node from nvm."
  (interactive)
  (if version
      (setq js-nvm-current-version (nvm--find-exact-version-for version))
    (let ((old-js-nvm js-nvm-current-version))
      (setq js-nvm-current-version
            (nvm--find-exact-version-for
             (js-list-nvm-versions
              (if old-js-nvm
                  (format "Node version (current %s): " (car old-js-nvm))
                "Node version: "))))))
  (progn
    (setq inferior-js-program-command
          (concat
           (car (last js-nvm-current-version))
           "/bin"
           "/node"))))

(defun js--is-nodejs ()
  (string-match-p "node$" inferior-js-program-command))

(defun js--guess-load-file-cmd (filename)
  (let ((cmd (concat "require(\"" filename "\")\n")))
    (when (not (js--is-nodejs))
      (setq cmd (concat "load(\"" filename "\")\n")))
    cmd))

;;;###autoload
(defun js-clear ()
  "Clear the *js* buffer."
  (interactive)
  (let* ((buf (get-buffer inferior-js-buffer))
         (old-buf (current-buffer)))
    (save-excursion
      (cond
       ((buffer-live-p buf)
        (switch-to-buffer buf)
        (erase-buffer)
        (switch-to-buffer old-buf)
        (message "*js* buffer cleared."))
       (t
        (error "*js* buffer doesn't exist!"))))))

;;;###autoload
(defun run-js (cmd &optional dont-switch-p)
  "Run an inferior Javascript process, input and output via buffer `*js*'.
If there is a process already running in `*js*', switch to that buffer.
With argument, allows you to edit the command line (default is value
of `inferior-js-program-command').
Runs the hook `inferior-js-mode-hook' \(after the `comint-mode-hook'
is run).
\(Type \\[describe-mode] in the process buffer for a list of commands.)"
  (interactive
   (list
    (when current-prefix-arg
      (setq cmd
            (read-string "Run js: "
                         (mapconcat
                          'identity
                          (cons
                           inferior-js-program-command
                           inferior-js-program-arguments)
                          " ")))
      (when js-use-nvm
        (unless (featurep 'nvm)
          (require 'nvm))
        (unless js-nvm-current-version
          (js-select-node-version)))
      (setq inferior-js-program-arguments (split-string cmd))
      (setq inferior-js-program-command (pop inferior-js-program-arguments)))))

  (setenv "NODE_NO_READLINE" "1")

  ;; add "node_modules/" into $NODE_PATH
  (let* ((node-modules (locate-dominating-file default-directory "node_modules"))
         (node-path (getenv "NODE_PATH")))
    (cond
     (node-modules
      (setq node-modules (concat (file-name-as-directory node-modules) "node_modules"))
      (cond
       ((or (not node-path)
            (string= "" node-path))
        ;; set
        (setenv "NODE_PATH" node-modules))
       ((not (string-match-p node-modules node-path))
        ;; append
        (setenv "NODE_PATH" (concat node-path ":" node-modules))))
      (message "%s added into \$NODE_PATH" node-modules))
     (t
      (message "Can't find node_modules/"))))

  (if (not (comint-check-proc "*js*"))
      (with-current-buffer
          (apply 'make-comint "js" inferior-js-program-command
                 nil inferior-js-program-arguments)
        (inferior-js-mode)))
  (setq inferior-js-buffer "*js*")
  (if dont-switch-p
      (display-buffer "*js*")
    (pop-to-buffer "*js*")))

;;;###autoload
(defun js-send-region (start end)
  "Send the current region to the inferior Javascript process."
  (interactive "r")
  (run-js inferior-js-program-command t)
  (comint-send-region inferior-js-buffer start end)
  (comint-send-string inferior-js-buffer "\n"))

;;;###autoload
(defun js-send-region-and-go (start end)
  "Send the current region to the inferior Javascript process."
  (interactive "r")
  (run-js inferior-js-program-command t)
  (comint-send-region inferior-js-buffer start end)
  ;; (comint-send-string inferior-js-buffer "\n")
  (switch-to-js inferior-js-buffer))

;;;###autoload
(defun js-send-last-sexp-and-go ()
  "Send the previous sexp to the inferior Js process."
  (interactive)
  (js-send-region-and-go
   (save-excursion
     (backward-sexp)
     (move-beginning-of-line nil)
     (point))
   (point)))

;;;###autoload
(defun js-send-last-sexp ()
  "Send the previous sexp to the inferior Javascript process."
  (interactive)
  (js-send-region
   (save-excursion
     (backward-sexp)
     (move-beginning-of-line nil)
     (point))
   (point)))

(defun js-get-buffer-point-min ()
  (let* ((rlt (point-min)))
    (save-excursion
      (goto-char rlt)
      (when (= (following-char) ?#)
        (forward-line)
        (setq rlt (line-beginning-position))))
    rlt))

;;;###autoload
(defun js-send-buffer ()
  "Send the buffer to the inferior Javascript process."
  (interactive)
  (js-send-region (js-get-buffer-point-min) (point-max)))


;;;###autoload
(defun js-send-buffer-and-go ()
  "Send the buffer to the inferior Javascript process."
  (interactive)
  (js-send-region-and-go (js-get-buffer-point-min) (point-max)))

;;;###autoload
(defun js-load-file (filename)
  "Load a file in the javascript interpreter."
  (interactive "f")
  (let ((filename (expand-file-name filename)))
    (run-js inferior-js-program-command t)
    (comint-send-string inferior-js-buffer (js--guess-load-file-cmd filename))))

;;;###autoload
(defun js-load-file-and-go (filename)
  "Load a file in the javascript interpreter."
  (interactive "f")
  (let ((filename (expand-file-name filename)))
    (run-js inferior-js-program-command t)
    (comint-send-string inferior-js-buffer (js--guess-load-file-cmd filename))
    (switch-to-js inferior-js-buffer)))

;;;###autoload
(defun js-comint-process-output (string)
  "Cleaner output."
  (let* ((start-marker (or comint-last-output-start
                            (point-min-marker)))
          (end-marker (process-mark (get-buffer-process (current-buffer)))))
    ;; shamelessly copied from `ansi-color-process-output'
    (save-excursion
      (goto-char start-marker)
      (while (re-search-forward js-comint-drop-regexp end-marker t)
        (replace-match "")))))

;;;###autoload
(defun switch-to-js (eob-p)
  "Switch to the javascript process buffer.
With argument, position cursor at end of buffer."
  (interactive "P")
  (if (and inferior-js-buffer (get-buffer inferior-js-buffer))
      (pop-to-buffer inferior-js-buffer)
    (error "No current process buffer.  See variable `inferior-js-buffer'"))
  (when eob-p
    (push-mark)
    (goto-char (point-max))))

(defvar inferior-js-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m "\C-x\C-e" 'js-send-last-sexp)
    (define-key m "\C-cl" 'js-load-file)
    m))

;;;###autoload
(define-derived-mode inferior-js-mode comint-mode "Inferior Javascript"
  "Major mode for interacting with an inferior javascript process.

The following commands are available:
\\{inferior-js-mode-map}

A javascript process can be fired up with M-x run-js.

Customization: Entry to this mode runs the hooks on comint-mode-hook and
inferior-js-mode-hook (in that order).

You can send text to the inferior Javascript process from other buffers containing
Javascript source.
    switch-to-js switches the current buffer to the Javascript process buffer.
    js-send-region sends the current region to the Javascript process.
"
  :group 'inferior-js
  (use-local-map inferior-js-mode-map))

(provide 'js-comint)
;;; js-comint.el ends here
