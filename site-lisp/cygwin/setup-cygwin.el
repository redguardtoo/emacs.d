;;; setup-cygwin.el --- Set up Emacs for using Cygwin
;;
;; Filename: setup-cygwin.el
;; Description:
;; Author: Markus Hoenika
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2004-2015, Drew Adams, all rights reserved.
;; Created: Thu Jan 15 11:13:38 2004
;; Version: 0
;; Package-Requires: ((cygwin-mount "0"))
;; Last-Updated: Thu Jan  1 11:13:26 2015 (-0800)
;;           By: dradams
;;     Update #: 158
;; URL: http://www.emacswiki.org/setup-cygwin.el
;; Doc URL: http://www.emacswiki.org/NTEmacsWithCygwin
;; Keywords: os, unix, cygwin
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `ange-ftp', `backquote', `comint', `cygwin-mount', `ring'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;   Set up Emacs for using Cygwin.  From Markus Hoenika's paper "SGML
;;   for Windows NT" <hoenika_markus@compuserve.com>
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change Log:
;;
;; 2014/01/30 dadams
;;     Added: setcyg-dir-p.
;;     cygwin-root-directory: Look for "C:/cygwin64/" first, then "C:/cygwin/".
;; 2014/01/14 dadams
;;     Added: add-to-list definition with APPEND, for Emacs 20.
;; 2013/06/02 dadams
;;     Set env var CYGWIN to nodosfilewarning, to workaround ediff-buffers problem with names of temp files.
;;     Set null-device to /dev/null.
;; 2013/04/27 dadams
;;     Put Cygwin path stuff before the stuff from getenv.
;; 2013/03/08 dadams
;;     Added: defgroup setup-cygwin, option cygwin-root-directory.
;;     Use cygwin-root-directory instead of hardcoding root dir.  Thx to Gabor Vida.
;; 2011/08/11 dadams
;;     Made settings that are based on Cygwin install directory conditional, per input from Tom Popovich.
;; 2011/01/04 dadams
;;     Added autoload cookies for commands.
;; 2009/10-15 dadams
;;     Set ediff-shell to shell-file-name.
;; 2007/12/08 dadams
;;     Use absolute file name for shell-file-name.
;; 2006/11/16 dadams
;;     Replace add-to-list by setq, for Emacs -q prior to Emacs 21.
;; 2006/08/14 dadams
;;     Append, not prepend "c:/cygwin/usr/info/" to Info-default-directory-list.
;; 2004/10/01 dadams
;;     Changed Info-directory-list to Info-default-directory-list
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(require 'cygwin-mount)

(when (< emacs-major-version 21)
  (defun add-to-list (list-var element &optional append)
    "Add to the value of LIST-VAR the element ELEMENT if it isn't there yet.
The test for presence of ELEMENT is done with `equal'.
If ELEMENT is added, it is added at the beginning of the list,
unless the optional argument APPEND is non-nil, in which case
ELEMENT is added at the end.

If you want to use `add-to-list' on a variable that is not defined
until a certain package is loaded, you should put the call to `add-to-list'
into a hook function that will be run only after loading the package.
`eval-after-load' provides one way to do this.  In some cases
other hooks, such as major mode hooks, can do the job."
    (if (member element (symbol-value list-var))
        (symbol-value list-var)
      (set list-var
           (if append
               (append (symbol-value list-var) (list element))
             (cons element (symbol-value list-var)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgroup setup-cygwin nil
  "Set up Emacs to use Cygwin.")

(defun setcyg-dir-p (directory)
  "Return DIRECTORY if DIRECTORY is a readable directory, nil otherwise."
  (and (file-directory-p directory)  (file-readable-p directory)  directory))

(defcustom cygwin-root-directory (or (setcyg-dir-p "C:/cygwin64/")  (setcyg-dir-p "C:/cygwin/"))
  "Root directory of Cygwin installation.
It should have subdirectories `bin' and `usr/info'.
Subdirectory `bin' should have file `bin/bash.exe'."
  :group 'setup-cygwin :type 'directory)

(unless (setcyg-dir-p cygwin-root-directory)
  (error "Cannot find Cygwin.  Please customize option `cygwin-root-directory'"))


;;; Make Cygwin paths accessible
(cygwin-mount-activate)

;;; Follow Cygwin symlinks.
;;; Handles old-style (text file) symlinks and new-style (.lnk file) symlinks.
;;; (Non-Cygwin-symlink .lnk files, such as desktop shortcuts, are still loaded as such.)
(defun follow-cygwin-symlink ()
  "Follow Cygwin symlinks.
Handles old-style (text file) and new-style (.lnk file) symlinks.
\(Non-Cygwin-symlink .lnk files, such as desktop shortcuts, are still
loaded as such.)"
  (save-excursion
    (goto-char 0)
    (if (looking-at
         "L\x000\x000\x000\x001\x014\x002\x000\x000\x000\x000\x000\x0C0\x000\x000\x000\x000\x000\x000\x046\x00C")
        (progn
          (re-search-forward
           "\x000\\([-A-Za-z0-9_\\.\\\\\\$%@(){}~!#^'`][-A-Za-z0-9_\\.\\\\\\$%@(){}~!#^'`]+\\)")
          (find-alternate-file (match-string 1)))
      (when (looking-at "!<symlink>")
        (re-search-forward "!<symlink>\\(.*\\)\0")
        (find-alternate-file (match-string 1))))))
(add-hook 'find-file-hooks 'follow-cygwin-symlink)

;;; Use Unix-style line endings.
(setq-default buffer-file-coding-system 'undecided-unix)

;;; Use /dev/null, not NUL.
(setq null-device  "/dev/null")

;;; Without this env var setting, Cygwin causes `ediff-buffers', at least, to raise an error.
;;; Making this setting here might have no effect, as the env var is checked only by the first Cygwin process
;;; invoked during your Windows session.  For best results, set this env var globally, in Windows itself.
;;; An alternative might be to use `cygpath' to change from MS Windows file names to POSIX.
(setenv "CYGWIN" "nodosfilewarning")

;;; Add Cygwin Info pages
(add-to-list 'Info-default-directory-list (expand-file-name "usr/info" cygwin-root-directory) 'APPEND)

;;; Use `bash' as the default shell in Emacs.
(add-to-list 'exec-path (expand-file-name "bin" cygwin-root-directory))
(setq shell-file-name  (expand-file-name "bin/bash.exe" cygwin-root-directory)) ; Subprocesses invoked by shell.
(setenv "SHELL" shell-file-name)
;; (setenv "PATH" (concat (getenv "PATH") ";" (expand-file-name "bin" cygwin-root-directory)))
(setenv "PATH" (concat (expand-file-name "bin" cygwin-root-directory) ";" (getenv "PATH")))
(setq explicit-shell-file-name  shell-file-name) ; Interactive shell
(setq ediff-shell               shell-file-name)    ; Ediff shell
(setq explicit-shell-args       '("--login" "-i"))

;;;;; (setq shell-command-switch "-ic") ; SHOULD THIS BE "-c" or "-ic"?
(setq w32-quote-process-args ?\") ;; " @@@ IS THIS BETTER? ;@@@ WAS THIS BEFORE: (setq w32-quote-process-args t)

;; These don't seem to be needed.
;; They were recommended by http://www.khngai.com/emacs/cygwin.php
;;;;; (add-hook 'comint-output-filter-functions
;;;;;     'shell-strip-ctrl-m nil t)
;;;;; ;; Removes unsightly ^M characters that would otherwise appear in output of java applications.
;;;;; (add-hook 'comint-output-filter-functions
;;;;;     'comint-watch-for-password-prompt nil t)
;;;;; (setq explicit-shell-file-name "bash.exe")
;;;;; ;; For subprocesses invoked via the shell
;;;;; ;; (e.g., "shell -c command")
;;;;; (setq shell-file-name explicit-shell-file-name)


;;;###autoload
(defun bash ()
  "Start `bash' shell."
  (interactive)
  (let ((binary-process-input t)
        (binary-process-output nil))
    (shell)))

(setq process-coding-system-alist
      (cons '("bash" . (raw-text-dos . raw-text-unix)) process-coding-system-alist))


;; From: http://www.dotfiles.com/files/6/235_.emacs
;;;###autoload
(defun set-shell-bash()
  "Enable on-the-fly switching between the bash shell and DOS."
  (interactive)
  ;; (setq binary-process-input t)
  (setq shell-file-name "bash")
  (setq shell-command-switch "-c")      ; SHOULD IT BE (setq shell-command-switch "-ic")?
  (setq explicit-shell-file-name "bash")
  (setenv "SHELL" explicit-shell-file-name)
  ;;;;;(setq explicit-sh-args '("-login" "-i")) ; Undefined?
  (setq w32-quote-process-args ?\") ;; "
  ;;;;;(setq mswindows-quote-process-args t)) ; Undefined?
  )

;;;###autoload
(defun set-shell-cmdproxy()
  "Set shell to `cmdproxy'."
  (interactive)
  (setq shell-file-name "cmdproxy")
  (setq explicit-shell-file-name "cmdproxy")
  (setenv "SHELL" explicit-shell-file-name)
  ;;;;;(setq explicit-sh-args nil)           ; Undefined?
  (setq w32-quote-process-args nil))

;;;;;;;;;;;;;;;;;;;;;;;

(provide 'setup-cygwin)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; setup-cygwin.el ends here
