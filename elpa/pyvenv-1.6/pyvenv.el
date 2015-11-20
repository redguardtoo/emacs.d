;;; pyvenv.el --- Python virtual environment interface -*- lexical-binding: t -*-

;; Copyright (C) 2013-2015  Jorgen Schaefer <contact@jorgenschaefer.de>

;; Author: Jorgen Schaefer <contact@jorgenschaefer.de>
;; URL: http://github.com/jorgenschaefer/pyvenv
;; Package-Version: 1.6
;; Version: 1.6
;; Keywords: Python, Virtualenv, Tools

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is a simple global minor mode which will replicate the changes
;; done by virtualenv activation inside Emacs.

;; The main entry points are `pyvenv-activate', which queries the user
;; for a virtual environment directory to activate, and
;; `pyvenv-workon', which queries for a virtual environment in
;; $WORKON_HOME (from virtualenvwrapper.sh).

;; If you want your inferior Python processes to be restarted
;; automatically when you switch your virtual environment, add
;; `pyvenv-restart-python' to `pyvenv-post-activate-hooks'.

;;; Code:

(require 'json)

;; User customization

(defgroup pyvenv nil
  "Python Virtual Environment Interface."
  :prefix "pyvenv-"
  :group 'languages)

(defcustom pyvenv-workon nil
  "The intended virtualenv in the virtualenvwrapper directory.

This is rarely useful to set globally. Rather, set this in file-
or directory-local variables using \\[add-file-local-variable] or
\\[add-dir-local-variable].

When `pyvenv-mode' is enabled, pyvenv will switch to this
virtualenv. If a virtualenv is already enabled, it will ask first."
  :type 'pyvenv-workon
  :safe #'stringp
  :group 'pyvenv)

(defcustom pyvenv-activate nil
  "The intended virtualenv directory.

This is rarely useful to set globally. Rather, set this in file-
or directory-local variables using \\[add-file-local-variable] or
\\[add-dir-local-variable].

When `pyvenv-mode' is enabled, pyvenv will switch to this
virtualenv. If a virtualenv is already enabled, it will ask first."
  :type 'directory
  :safe #'stringp
  :group 'pyvenv)

(defcustom pyvenv-tracking-ask-before-change nil
  "Non-nil means pyvenv will ask before automatically changing a virtualenv.

This can happen when a new file is opened with a buffer-local
value (from file-local or directory-local variables) for
`pyvenv-workon' or `pyvenv-workon', or if `pyvenv-tracking-mode'
is active, after every command."
  :type 'boolean
  :group 'pyvenv)

(defcustom pyvenv-virtualenvwrapper-python
  (or (getenv "VIRTUALENVWRAPPER_PYTHON")
      (executable-find "python"))
  "The python process which has access to the virtualenvwrapper module.

This should be $VIRTUALENVWRAPPER_PYTHON outside of Emacs, but
virtualenvwrapper.sh does not export that variable. We make an
educated guess, but that can be off."
  :type '(file :must-match t)
  :safe #'file-directory-p
  :group 'pyvenv)

;; API for other libraries

(defvar pyvenv-virtual-env nil
  "The current virtual environment.

Do not set this variable directly; use `pyvenv-activate' or
`pyvenv-workon'.")

(defvar pyvenv-virtual-env-name nil
  "The name of the current virtual environment.

This is usually the base name of `pyvenv-virtual-env'.")

(defvar pyvenv-pre-activate-hooks nil
  "Hooks run before a virtual environment is activated.

`pyvenv-virtual-env' is already set.")

(defvar pyvenv-post-activate-hooks nil
  "Hooks run after a virtual environment is activated.

`pyvenv-virtual-env' is set.")

(defvar pyvenv-pre-deactivate-hooks nil
  "Hooks run before a virtual environment is deactivated.

`pyvenv-virtual-env' is set.")

(defvar pyvenv-post-deactivate-hooks nil
  "Hooks run after a virtual environment is deactivated.

`pyvenv-virtual-env' is still set.")

(defvar pyvenv-mode-line-indicator '(pyvenv-virtual-env-name
                                     ("[" pyvenv-virtual-env-name "] "))
  "How `pyvenv-mode' will indicate the current environment in the mode line.")

;; Internal code.

(defvar pyvenv-old-process-environment nil
  "The old process environment before the last activate.")

(defvar pyvenv-old-exec-path nil
  "The old exec path before the last activate.")

;;;###autoload
(defun pyvenv-activate (directory)
  "Activate the virtual environment in DIRECTORY."
  (interactive "DActivate venv: ")
  (setq directory (expand-file-name directory))
  (pyvenv-deactivate)
  (setq pyvenv-virtual-env directory
        pyvenv-virtual-env-name (file-name-nondirectory directory))
  ;; Preserve variables from being overwritten.
  (let ((old-exec-path exec-path)
        (old-process-environment process-environment))
    (unwind-protect
        (pyvenv-run-virtualenvwrapper-hook "pre_activate" pyvenv-virtual-env)
      (setq exec-path old-exec-path
            process-environment old-process-environment)))
  (run-hooks 'pyvenv-pre-activate-hooks)
  (setq pyvenv-old-exec-path exec-path
        pyvenv-old-process-environment process-environment
        ;; For some reason, Emacs adds some directories to `exec-path'
        ;; but not to `process-environment'?
        exec-path (if (file-exists-p (format "%s/Scripts" directory))
                      (cons (format "%s/Scripts" directory) exec-path)
                    (cons (format "%s/bin" directory) exec-path))
        process-environment (append
                             (list
                              (format "VIRTUAL_ENV=%s" directory)
                              (format "PATH=%s" (mapconcat (lambda (x)
                                                             (or x "."))
                                                           exec-path
                                                           path-separator))
                              ;; No "=" means to unset
                              "PYTHONHOME")
                             process-environment)
        )
  (pyvenv-run-virtualenvwrapper-hook "post_activate")
  (run-hooks 'pyvenv-post-activate-hooks))

;;;###autoload
(defun pyvenv-deactivate ()
  "Deactivate any current virtual environment."
  (interactive)
  (when pyvenv-virtual-env
    (pyvenv-run-virtualenvwrapper-hook "pre_deactivate")
    (run-hooks 'pyvenv-pre-deactivate-hooks))
  (when pyvenv-old-process-environment
    (setq process-environment pyvenv-old-process-environment
          pyvenv-old-process-environment nil))
  (when pyvenv-old-exec-path
    (setq exec-path pyvenv-old-exec-path
          pyvenv-old-exec-path nil))
  (when pyvenv-virtual-env
    ;; Make sure this does not change `exec-path', as $PATH is
    ;; different
    (let ((old-exec-path exec-path)
          (old-process-environment process-environment))
      (unwind-protect
          (pyvenv-run-virtualenvwrapper-hook "post_deactivate"
                                             pyvenv-virtual-env)
        (setq exec-path old-exec-path
              process-environment old-process-environment)))
    (run-hooks 'pyvenv-post-deactivate-hooks))
  (setq pyvenv-virtual-env nil
        pyvenv-virtual-env-name nil))

(defvar pyvenv-workon-history nil
  "Prompt history for `pyvenv-workon'.")

;;;###autoload
(defun pyvenv-workon (name)
  "Activate a virtual environment from $WORKON_HOME."
  (interactive
   (list
    (completing-read "Work on: " (pyvenv-virtualenv-list)
                     nil t nil 'pyvenv-workon-history nil nil)))
  (when (not (or (equal name "")
                 ;; Some completion frameworks can return nil for the
                 ;; default, see
                 ;; https://github.com/jorgenschaefer/elpy/issues/144
                 (equal name nil)))
    (pyvenv-activate (format "%s/%s"
                             (pyvenv-workon-home)
                             name))))

(defun pyvenv-virtualenv-list (&optional noerror)
  "Prompt the user for a name in $WORKON_HOME.

If NOERROR is set, do not raise an error if WORKON_HOME is not
configured."
  (let ((workon-home (pyvenv-workon-home))
        (result nil))
    (if (not (file-directory-p workon-home))
        (when (not noerror)
          (error "Can't find a workon home directory, set $WORKON_HOME"))
      (dolist (name (directory-files workon-home))
        (when (or (file-exists-p (format "%s/%s/bin/activate"
                                         workon-home name))
                  (file-exists-p (format "%s/%s/Scripts/activate.bat"
                                         workon-home name)))
          (setq result (cons name result))))
      (sort result (lambda (a b)
                     (string-lessp (downcase a)
                                   (downcase b)))))))

(define-widget 'pyvenv-workon 'choice
  "Select an available virtualenv from virtualenvwrapper."
  :convert-widget
  (lambda (widget)
    (setq widget (widget-copy widget))
    (widget-put widget
                :args (cons '(const :tag "None" nil)
                            (mapcar (lambda (env)
                                      (list 'const env))
                                    (pyvenv-virtualenv-list t))))
    (widget-types-convert-widget widget))

  :prompt-value (lambda (widget prompt value unbound)
                  (let ((name (completing-read
                               prompt
                               (cons "None"
                                     (pyvenv-virtualenv-list t))
                               nil t)))
                    (if (equal name "None")
                        nil
                      name))))

(defvar pyvenv-mode-map (make-sparse-keymap)
  "The mode keymap for `pyvenv-mode'.")

(easy-menu-define pyvenv-menu pyvenv-mode-map
  "Pyvenv Menu"
  '("Virtual Envs"
    :visible pyvenv-mode
    ("Workon"
     :help "Activate a virtualenvwrapper environment"
     :filter (lambda (&optional ignored)
               (mapcar (lambda (venv)
                         (vector venv `(pyvenv-workon ,venv)
                                 :style 'radio
                                 :selected `(equal pyvenv-virtual-env-name
                                                   ,venv)))
                       (pyvenv-virtualenv-list t))))
    ["Activate" pyvenv-activate
     :help "Activate a virtual environment by directory"]
    ["Deactivate" pyvenv-deactivate
     :help "Deactivate the current virtual environment"
     :active pyvenv-virtual-env
     :suffix pyvenv-virtual-env-name]
    ["Restart Python Processes" pyvenv-restart-python
     :help "Restart all Python processes to use the current environment"]))

;;;###autoload
(define-minor-mode pyvenv-mode
  "Global minor mode for pyvenv.

Will show the current virtualenv in the mode line, and respect a
`pyvenv-workon' setting in files."
  :global t
  (cond
   (pyvenv-mode
    (add-to-list 'mode-line-misc-info '(pyvenv-mode pyvenv-mode-line-indicator))
    (add-hook 'hack-local-variables-hook #'pyvenv-track-virtualenv))
   ((not pyvenv-mode)
    (setq mode-line-misc-info (delete '(pyvenv-mode pyvenv-mode-line-indicator)
                                      mode-line-misc-info))
    (remove-hook 'hack-local-variables-hook #'pyvenv-track-virtualenv))))

;;;###autoload
(define-minor-mode pyvenv-tracking-mode
  "Global minor mode to track the current virtualenv.

When this mode is active, pyvenv will activate a buffer-specific
virtualenv whenever the user switches to a buffer with a
buffer-local `pyvenv-workon' or `pyvenv-activate' variable."
  :global t
  (if pyvenv-tracking-mode
      (add-hook 'post-command-hook 'pyvenv-track-virtualenv)
    (remove-hook 'post-command-hook 'pyvenv-track-virtualenv)))

(defun pyvenv-track-virtualenv ()
  "Set a virtualenv as specified for the current buffer.

If either `pyvenv-activate' or `pyvenv-workon' are specified, and
they specify a virtualenv different from the current one, switch
to that virtualenv."
  (cond
   (pyvenv-activate
    (when (and (not (equal pyvenv-activate pyvenv-virtual-env))
               (or (not pyvenv-tracking-ask-before-change)
                   (y-or-n-p (format "Switch to virtualenv %s (currently %s)"
                                     pyvenv-activate pyvenv-virtual-env))))
      (pyvenv-activate pyvenv-activate)))
   (pyvenv-workon
    (when (and (not (equal pyvenv-workon pyvenv-virtual-env-name))
               (or (not pyvenv-tracking-ask-before-change)
                   (y-or-n-p (format "Switch to virtualenv %s (currently %s)"
                                     pyvenv-workon pyvenv-virtual-env-name))))
      (pyvenv-workon pyvenv-workon)))))

(defun pyvenv-run-virtualenvwrapper-hook (hook &rest args)
  "Run a virtualenvwrapper hook, and update the environment.

This will run a virtualenvwrapper hook and update the local
environment accordingly.

CAREFUL! This will modify your `process-environment' and
`exec-path'."
  (when (pyvenv-hook-dir)
    (with-temp-buffer
      (let ((tmpfile (make-temp-file "pyvenv-virtualenvwrapper-")))
        (unwind-protect
            (progn
              (apply #'call-process
                     pyvenv-virtualenvwrapper-python
                     nil t nil
                     "-c"
                     "from virtualenvwrapper.hook_loader import main; main()"
                     "--script" tmpfile
                     (if (getenv "HOOK_VERBOSE_OPTION")
                         (cons (getenv "HOOK_VERBOSE_OPTION")
                               (cons hook args))
                       (cons hook args)))
              (call-process-shell-command
               (format ". '%s' ; echo ; echo =-=-= ; python -c \"import os, json ; print(json.dumps(dict(os.environ)))\""
                       tmpfile)
               nil t nil))
          (delete-file tmpfile)))
      (goto-char (point-min))
      (when (and (not (re-search-forward "ImportError: No module named virtualenvwrapper" nil t))
                 (re-search-forward "\n=-=-=\n" nil t))
        (let ((output (buffer-substring (point-min)
                                        (match-beginning 0))))
          (when (> (length output) 0)
            (with-help-window "*Virtualenvwrapper Hook Output*"
              (with-current-buffer "*Virtualenvwrapper Hook Output*"
                (let ((inhibit-read-only t))
                  (erase-buffer)
                  (insert
                   (format
                    "Output from the virtualenvwrapper hook %s:\n\n"
                    hook)
                   output))))))
        (dolist (binding (json-read))
          (let ((env (format "%s=%s" (car binding) (cdr binding))))
            (when (not (member env process-environment))
              (setq process-environment (cons env process-environment))))
          (when (eq (car binding) 'PATH)
            (setq exec-path (split-string (cdr binding) ":"))))))))

;;;###autoload
(defun pyvenv-restart-python ()
  "Restart Python inferior processes."
  (interactive)
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (and (eq major-mode 'inferior-python-mode)
                 (get-buffer-process buf))
        (let ((cmd (combine-and-quote-strings (process-command
                                               (get-buffer-process buf))))
              (dedicated (if (string-match "\\[.*\\]$" (buffer-name buf))
                             t
                           nil))
              (show nil))
          (delete-process (get-buffer-process buf))
          (goto-char (point-max))
          (insert "\n\n"
                  "###\n"
                  (format "### Restarting in virtualenv %s (%s)\n"
                          pyvenv-virtual-env-name pyvenv-virtual-env)
                  "###\n"
                  "\n\n")
          (run-python cmd dedicated show)
          (goto-char (point-max)))))))

(defun pyvenv-hook-dir ()
  "Return the current hook directory.

This is usually the value of $VIRTUALENVWRAPPER_HOOK_DIR, but
virtualenvwrapper has stopped exporting that variable, so we go
back to the default of $WORKON_HOME or even just ~/.virtualenvs/."
  (or (getenv "VIRTUALENVWRAPPER_HOOK_DIR")
      (pyvenv-workon-home)))

(defun pyvenv-workon-home ()
  "Return the current workon home.

This is the value of $WORKON_HOME or ~/.virtualenvs."
  (or (getenv "WORKON_HOME")
      (expand-file-name "~/.virtualenvs")))

;;; Compatibility

(when (not (fboundp 'file-name-base))
  ;; Emacs 24.3
  (defun file-name-base (&optional filename)
    "Return the base name of the FILENAME: no directory, no extension.
FILENAME defaults to `buffer-file-name'."
    (file-name-sans-extension
     (file-name-nondirectory (or filename (buffer-file-name)))))
  )

(when (not (boundp 'mode-line-misc-info))
  (defvar mode-line-misc-info nil
    "Compatibility variable for 24.3+")
  (let ((line mode-line-format))
    (while line
      (when (eq 'which-func-mode
                (car-safe (car-safe (cdr line))))
        (setcdr line (cons 'mode-line-misc-format
                           (cdr line)))
        (setq line (cdr line)))
      (setq line (cdr line)))))

(provide 'pyvenv)
;;; pyvenv.el ends here
