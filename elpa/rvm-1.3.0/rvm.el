;;; rvm.el --- Emacs integration for rvm

;; Copyright (C) 2010-2011 Yves Senn

;; Author: Yves Senn <yves.senn@gmx.ch>
;; URL: http://www.emacswiki.org/emacs/RvmEl
;; Package-Version: 1.3.0
;; Version: 1.3.0
;; Created: 5 April 2010
;; Keywords: ruby rvm
;; EmacsWiki: RvmEl

;; This file is NOT part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; M-x rvm-use-default prepares the current Emacs session to use
;; the default ruby configured with rvm.

;; M-x rvm-use allows you to switch the current session to the ruby
;; implementation of your choice. You can also change the active gemset.

;;; Compiler support:

(eval-when-compile (require 'cl))
(defvar eshell-path-env)
(defvar persp-mode)
(defvar perspectives-hash)
(declare-function persp-switch "perspective" (name))

;;; Code:

(defcustom rvm-executable
  (or (executable-find "rvm")
      (and (file-readable-p "~/.rvm/bin/rvm") "~/.rvm/bin/rvm")
      (and (file-readable-p "/usr/local/rvm/bin/rvm") "/usr/local/rvm/bin/rvm"))
  "Location of RVM executable."
  :group 'rvm
  :type 'file)

(defcustom rvm-configuration-file-name
  ".rvmrc"
  "RVM configuration file name"
  :group 'rvm
  :type 'string)

(defcustom rvm-interactive-completion-function
  (if ido-mode 'ido-completing-read 'completing-read)
  "The function which is used by rvm.el to interactivly complete user input"
  :group 'rvm
  :type 'function)

(defcustom rvm-interactive-find-file-function
  (if ido-mode 'ido-find-file 'find-file)
  "The function which is used by rvm.el to interactivly open files"
  :group 'rvm
  :type 'function)

(defvar rvm--gemset-default "global"
  "the default gemset per ruby interpreter")

(defvar rvm--gemset-separator "@"
  "character that separates the ruby version from the gemset.")

(defvar rvm--current-ruby-binary-path nil
  "reflects the path to the current 'ruby' executable.
This path gets added to the PATH variable and the exec-path list.")

(defvar rvm--current-gem-binary-path nil
  "reflects the path to the current 'rubygems' executables.
This path gets added to the PATH variable and the exec-path list.")

(defvar rvm--info-option-regexp "\s+\\(.+\\):\s+\"\\(.+\\)\""
  "regular expression to parse the options from rvm info")

(defvar rvm--list-ruby-regexp "\s*\\(=?[>\*]\\)?\s*\\(.+?\\)\s*\\[\\(.+\\)\\]\s*$"
  "regular expression to parse the ruby version from the 'rvm list' output")

(defvar rvm--gemset-list-filter-regexp "^\\(gemsets for\\|Gemset '\\)"
  "regular expression to filter the output of rvm gemset list")

(defvar rvm--gemset-list-regexp "\s*\\(=>\\)?\s*\\(.+?\\)\s*$"
  "regular expression to parse the gemset from the 'rvm gemset list' output")

(defvar rvm--rvmrc-parse-regexp (concat "\\(?:^rvm\s+\\(?:use\s+\\|\\)\\|environment_id=\"\\)\s*"
                                        "\\(?:--.+\s\\)*" ;; Flags
                                        "\\([^"
                                        rvm--gemset-separator
                                        "\n]+\\)\\(?:"
                                        rvm--gemset-separator
                                        "\\([^\"\s\n]+\\)\\)?\\(?:\"\\|\\)")
  "regular expression to parse the .rvmrc files inside project directories.
the first group matches the ruby-version and the second group is the gemset.
when no gemset is set, the second group is nil")

;; Support Code

;; Put with other utils
;; From http://www.emacswiki.org/emacs/ElispCookbook
(defun chomp (str)
  "Chomp leading and tailing whitespace from STR."
  (let ((s (if (symbolp str) (symbol-name str) str)))
    (replace-regexp-in-string "\\(^[[:space:]\n]*\\|[[:space:]\n]*$\\)" "" s)))

;; Application Code

;;;###autoload
(defun rvm-use-default ()
  "use the rvm-default ruby as the current ruby version"
  (interactive)
  (when (rvm-working-p)
    (rvm-use (rvm--ruby-default) rvm--gemset-default)))

;;;###autoload
(defun rvm-activate-corresponding-ruby ()
  "activate the corresponding ruby version for the file in the current buffer.
This function searches for an .rvmrc file and activates the configured ruby.
If no .rvmrc file is found, the default ruby is used insted."
  (interactive)

  (when (rvm-working-p)
   (let* ((rvmrc-path (rvm--rvmrc-locate))
          (rvmrc-info (if rvmrc-path (rvm--rvmrc-read-version rvmrc-path) nil)))
     (if rvmrc-info (rvm-use (first rvmrc-info) (second rvmrc-info))
       (rvm-use-default)))))

;;;###autoload
(defun rvm-use (new-ruby new-gemset)
  "switch the current ruby version to any ruby, which is installed with rvm"
  (interactive
   (let* ((picked-ruby (rvm--completing-read "Ruby Version: "
                                             (rvm/list)))
          (picked-gemset (rvm--completing-read "Gemset: "
                                               (rvm/gemset-list picked-ruby))))
     (list picked-ruby picked-gemset)))
  (when (rvm-working-p)
   (let* ((new-ruby-with-gemset (rvm--ruby-gemset-string new-ruby new-gemset))
          (ruby-info (rvm/info new-ruby-with-gemset))
          (new-ruby-binary (cdr (assoc "ruby" ruby-info)))
          (new-ruby-gemhome (cdr (assoc "GEM_HOME" ruby-info)))
          (new-ruby-gempath (cdr (assoc "GEM_PATH" ruby-info))))
     (rvm--set-ruby (file-name-directory new-ruby-binary))
     (rvm--set-gemhome new-ruby-gemhome new-ruby-gempath new-gemset))
   (message (concat "Ruby: " new-ruby " Gemset: " new-gemset))))

;;;###autoload
(defun rvm-open-gem (gemhome)
  (interactive (list (rvm--emacs-gemhome)))
  (when (rvm-working-p)
    (let* ((gems-dir (concat gemhome "/gems/"))
           (gem-name (rvm--completing-read "Gem: "
                                           (directory-files gems-dir nil "^[^.]")))
           (gem-dir (concat gems-dir gem-name)))
      (when (and (featurep 'perspective) persp-mode)
        (let ((initialize (not (gethash gem-name perspectives-hash))))
          (persp-switch gem-name)))
      (rvm--find-file gem-dir))))

(defun rvm-run-tests ()
  "run the complete test suite for rvm.el"
  (interactive)
  (let* ((test-directory (concat (file-name-directory
                                  (symbol-file 'rvm-run-tests)) "tests/"))
         (current-dir default-directory))
    (mapcar (lambda (f)
              (when (string-match-p "-tests.el$" f) (load f)))
            (directory-files (file-name-directory test-directory) t))
    (ert-run-tests-interactively "rvm-.*")))

;;;; TODO: take buffer switching into account
(defun rvm-autodetect-ruby ()
  (interactive)
  (when (rvm-working-p)
    (add-hook 'ruby-mode-hook 'rvm-activate-corresponding-ruby)
    (message "rvm.el is now autodetecting the ruby version")))

(defun rvm-autodetect-ruby-stop ()
  (interactive)
  (when (rvm-working-p)
    (remove-hook 'ruby-mode-hook 'rvm-activate-corresponding-ruby)
    (message "stopped rvm.el from autodetecting ruby versions")))

(defun rvm/list (&optional default-ruby)
  (let ((rubies (rvm--call-process "list" (when default-ruby "default")))
        (start 0)
        (parsed-rubies '())
        (current-ruby '()))
    (while (string-match rvm--list-ruby-regexp rubies start)
      (let ((ruby-version (match-string 2 rubies))
            (ruby-platform (match-string 3 rubies))
            (ruby-current-version (match-string 1 rubies)))
        (add-to-list 'current-ruby ruby-current-version)
        (if ruby-current-version (add-to-list 'parsed-rubies ruby-version)
          (add-to-list 'parsed-rubies ruby-version t))
        (setq start (match-end 0))))
    parsed-rubies))

(defun rvm/gemset-list (ruby-version)
  (let* ((gemset-result (rvm--call-process "gemset" "list_all"))
         (gemset-lines (split-string gemset-result "\n"))
         (parsed-gemsets (list))
         (ruby-current-version nil))
    (loop for gemset in gemset-lines do
          (let ((filtered-gemset (string-match rvm--gemset-list-filter-regexp gemset)))
            (if filtered-gemset
                (if (string-match ruby-version gemset)
                    (setq ruby-current-version ruby-version)
                  (setq ruby-current-version nil)))
            (if (and (> (length gemset) 0)
                     ruby-current-version
                     (not filtered-gemset)
                     (string-match rvm--gemset-list-regexp gemset))
                (add-to-list 'parsed-gemsets (match-string 2 gemset) t))))
    parsed-gemsets))

(defun rvm/info (&optional ruby-version)
  (let ((info (rvm--call-process "info" ruby-version))
        (start 0)
        (parsed-info '()))
    (when (not info) (error "The ruby version: %s is not installed" ruby-version))
    (while (string-match rvm--info-option-regexp info start)
      (let ((info-key (match-string 1 info))
            (info-value (match-string 2 info)))
        (add-to-list 'parsed-info (cons info-key info-value))
        (setq start (match-end 0))))
    parsed-info))

(defun rvm--string-trim (string)
  (replace-regexp-in-string "^\\s-*\\|\\s-*$" "" string))

(defun rvm--ruby-gemset-string (ruby-version gemset)
  (if (rvm--default-gemset-p gemset) ruby-version
    (concat ruby-version rvm--gemset-separator gemset)))

(defun rvm--completing-read (prompt options)
  (let ((selected (funcall rvm-interactive-completion-function prompt options)))
    (rvm--string-trim selected)))

(defun rvm--find-file (directory)
  (let ((default-directory directory))
    (call-interactively rvm-interactive-find-file-function)))

(defun rvm--emacs-ruby-binary ()
  rvm--current-ruby-binary-path)

(defun rvm--emacs-gemhome ()
  (getenv "GEM_HOME"))

(defun rvm--emacs-gempath ()
  (getenv "GEM_PATH"))

(defun rvm--change-path (current-binary-var new-binaries)
  (let ((current-binaries-for-path
         (mapconcat 'identity (eval current-binary-var) ":"))
        (new-binaries-for-path (mapconcat 'identity new-binaries ":")))
    (if (and (eval current-binary-var)
             (not (string= (first (eval current-binary-var)) "/bin")))
        (progn
          (setenv "PATH" (replace-regexp-in-string
                          (regexp-quote current-binaries-for-path)
                          new-binaries-for-path
                          (getenv "PATH")))
          (dolist (binary (eval current-binary-var))
            (setq exec-path (remove binary exec-path))))
      (setenv "PATH" (concat new-binaries-for-path ":" (getenv "PATH"))))
    (dolist (binary new-binaries)
      (add-to-list 'exec-path binary))
    (setq eshell-path-env (getenv "PATH"))
    (set current-binary-var new-binaries)))

(defun rvm--set-ruby (ruby-binary)
  (rvm--change-path 'rvm--current-ruby-binary-path (list ruby-binary)))

(defun rvm--rvmrc-locate (&optional path)
  "searches the directory tree for an .rvmrc configuration file"
  (when (null path) (setq path default-directory))
  (cond
   ((equal (expand-file-name path) (expand-file-name "~")) nil)
   ((equal (expand-file-name path) "/") nil)
   ((member rvm-configuration-file-name (directory-files path))
    (concat (expand-file-name path) "/" rvm-configuration-file-name))
   (t (rvm--rvmrc-locate (concat (file-name-as-directory path) "..")))))

(defun rvm--rvmrc-read-version (path-to-rvmrc)
  (with-temp-buffer
    (insert-file-contents path-to-rvmrc)
    (rvm--rvmrc-parse-version (buffer-string))))

(defun rvm--rvmrc-parse-version (rvmrc-line)
  (when (string-match rvm--rvmrc-parse-regexp rvmrc-line)
    (list (rvm--string-trim (match-string 1 rvmrc-line))
          (rvm--string-trim (or (match-string 2 rvmrc-line) rvm--gemset-default)))))

(defun rvm--gem-binary-path-from-gem-path (gempath)
  (let ((gem-paths (split-string gempath ":")))
    (mapcar (lambda (path) (concat path "/bin")) gem-paths)))

(defun rvm--set-gemhome (gemhome gempath gemset)
  (if (and gemhome gempath gemset)
      (progn
        (setenv "GEM_HOME" gemhome)
        (setenv "GEM_PATH" gempath)
        (setenv "BUNDLE_PATH" gemhome)
        (rvm--change-path 'rvm--current-gem-binary-path (rvm--gem-binary-path-from-gem-path gempath)))
    (setenv "GEM_HOME" "")
    (setenv "GEM_PATH" "")
    (setenv "BUNDLE_PATH" "")))

(defun rvm--ruby-default ()
  (car (rvm/list t)))

(defun rvm-working-p ()
  (and rvm-executable (file-exists-p rvm-executable)))

(defun rvm--default-gemset-p (gemset)
  (string= gemset rvm--gemset-default))

(defun rvm--call-process (&rest args)
  (with-temp-buffer
    (let* ((success (apply 'call-process rvm-executable nil t nil
                           (delete nil args)))
           (output (buffer-substring-no-properties
                    (point-min) (point-max))))
      (if (= 0 success)
          output
        (message output)))))

(defun rvm-gem-install (gem)
  "Install GEM into the currently active RVM Gemset."
  (interactive "SGem Install: ")
  (shell-command (format "%s install %s&" ; & executes async
                         (concat (first rvm--current-ruby-binary-path) "/gem") gem))
  (pop-to-buffer "*Async Shell Command*"))

(provide 'rvm)
;;; rvm.el ends here
