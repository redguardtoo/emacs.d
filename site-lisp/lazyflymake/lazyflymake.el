;;; lazyflymake.el --- Lightweight syntax checker for Emacs, alternative of `flymake-mode' -*- lexical-binding: t -*-

;; Copyright (C) 2020 Chen Bin
;;
;; Version: 0.0.3
;; Keywords: convenience, languages, tools
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: https://github.com/redguardtoo/lazyflymake
;; Package-Requires: ((emacs "25.1"))

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, see <https://www.gnu.org/licenses/>.

;;; Commentary:
;;  Remove "(flymake-mode 1)" from ~/.emacs and insert below line instead,
;;
;;    (add-hook 'prog-mode-hook #'lazyflymake-start)
;;
;; Errors are reported after saving current file.
;; Use `flymake-goto-next-error', `flymake-goto-prev-error' to locate errors.
;;
;; Please note this program also set up flymake for Shell script, Emacs Lisp,
;; and Lua automatically.
;;
;; Shellcheck (https://github.com/koalaman/shellcheck) is required to check
;; shell script.
;;
;; Lua executable is required to check Lua code.
;;

;;; Code:
(require 'cl-lib)
(require 'flymake)
(require 'lazyflymake-sdk)

(defcustom lazyflymake-shell-script-modes '(sh-mode)
  "Major modes for shell script."
  :group 'lazyflymake
  :type '(repeat 'sexp))

(defvar flymake-err-line-patterns)
(defvar flymake-allowed-file-name-masks)

;;;###autoload
(defun lazyflymake-new-flymake-p ()
  "Test the flymake version."
  (fboundp 'flymake-start))

;;;###autoload
(defun lazyflymake-load(file-name-regexp mask &optional force)
  "Load flymake MASK for files matching FILE-NAME-REGEXP.
If FORCE is t, the existing set up in `flymake-allowed-file-name-masks' is replaced."
  (let* ((lib (intern (concat "lazyflymake-" (symbol-name mask))))
         (prefix (concat "lazyflymake-" (symbol-name mask)))
         (init-fn (intern (format "%s-%s" prefix "init")))
         (pattern-fn (intern (format "%s-%s" prefix "err-line-pattern")))
         filtered-masks)

    (when lazyflymake-debug
      (message "lazyflymake-load: mask=%s regexp=%s code-file=%s"
               mask
               file-name-regexp
               buffer-file-name))

    ;; load the library
    (when (and buffer-file-name
               (string-match file-name-regexp buffer-file-name)
               ;; respect existing set up in `flymake-allowed-file-name-masks'
               (or (eq (length (setq filtered-masks (cl-remove-if
                                                `(lambda (e)
                                                   (string= (car e) ,file-name-regexp))
                                                flymake-allowed-file-name-masks)))
                       (length flymake-allowed-file-name-masks))
                   force))

      ;; delete existing set up first
      (when (and filtered-masks force)
        (setq flymake-allowed-file-name-masks filtered-masks))

      ;; library is loaded or functions inside the library are defined
      (unless (or (and (fboundp 'init-fn) (fboundp 'pattern-fn))
                  (featurep lib))
        (require lib))

      (let* ((pattern (funcall pattern-fn)))
        (if lazyflymake-debug (message "pattern=%s" pattern))
        (when pattern
          (cond
           ((stringp (car pattern))
            (push pattern flymake-err-line-patterns))
           ((listp pattern)
            (setq-local flymake-err-line-patterns pattern)))))
      (push (list file-name-regexp init-fn) flymake-allowed-file-name-masks))))

(defun lazyflymake-guess-shell-script-regexp ()
  "Guess shell script file name regex."
  (let* ((ext (file-name-extension buffer-file-name)))
    (cond
     (ext
      (format "\\.%s$" ext))
     (t
      (format "\\%s$" (file-name-base buffer-file-name))))))

(defun lazyflymake--extract-err (output idx)
  "Extract error information from OUTPUT using IDX."
  (cond
   (idx
    (match-string idx output))
   (t
    "nil")))

(defun lazyflymake--legacy-info-at-point ()
  "Get info of errors at point.  Only used by old version of flymake."
  (let* ((line-no (line-number-at-pos))
         (errors (or (car (flymake-find-err-info flymake-err-info line-no))
                     (user-error "No errors for current line")))
         (menu (mapcar (lambda (x)
                         (if (flymake-ler-file x)
                             (cons (format "%s - %s(%d)"
                                           (flymake-ler-text x)
                                           (flymake-ler-file x)
                                           (flymake-ler-line x))
                                   x)
                           (list (flymake-ler-text x))))
                       errors)))
         (format "Line %s: %s" line-no (caar menu))))

;;;###autoload
(defun lazyflymake-test-err-line-pattern ()
  "Test one line of command line program output by `flymake-err-line-patterns'."
  (interactive)
  (let* ((output (read-string "One line of CLI output: "))
         (i 0)
         pattern
         len)
    (when (and output flymake-err-line-patterns)
      (setq len (length flymake-err-line-patterns))
      (while (< i len)
        (setq pattern (nth i flymake-err-line-patterns))
        (when (string-match (car pattern) output)
          (message "%d/%d matched: re=%s file=%s line=%s error=%s"
                   (1+ i)
                   len
                   (car pattern)
                   (lazyflymake--extract-err output (nth 1 pattern))
                   (lazyflymake--extract-err output (nth 2 pattern))
                   (lazyflymake--extract-err output (nth 4 pattern))))
        (setq i (1+ i))))))

(defun lazyflymake-echo-error (&optional arg)
  "Echo error at point.  ARG is ignored."
  (ignore arg)
  (message (lazyflymake--legacy-info-at-point)))

;;;###autoload
(defun lazyflymake-start ()
  "Turn on lazyflymake to syntax check code."
  (interactive)

  ;; set up `flymake-allowed-file-name-masks'
  ;; Emacs 26 has its own elisp syntax init
  (unless (lazyflymake-new-flymake-p) (lazyflymake-load "\\.el$" 'elisp))

  ;; set log level to WARNING, so we could see error message in echo area
  (unless (lazyflymake-new-flymake-p)
    (advice-add 'flymake-goto-next-error :after #'lazyflymake-echo-error)
    (advice-add 'flymake-goto-prev-error :after #'lazyflymake-echo-error))

  (lazyflymake-load "\\.lua$" 'lua)
  ;; a bit hard to get regex matching all shell script files
  (when (and (memq major-mode lazyflymake-shell-script-modes)
             (lazyflymake-sdk-file-exist-p))
    ;; File with `sh-mode' is shell script
    (lazyflymake-load (lazyflymake-guess-shell-script-regexp) 'shell))

  (if lazyflymake-debug (message "flymake-allowed-file-name-masks=%s" flymake-allowed-file-name-masks))

  ;; js-mode has its own linter
  (unless (derived-mode-p 'js2-mode)
    (lazyflymake-load "\\.[jt]s$" 'eslint))

  (unless flymake-mode (flymake-mode 1)))

;;;###autoload
(defun lazyflymake-stop ()
  "Turn on lazyflymake to syntax check code."
  (interactive)

  (unless (lazyflymake-new-flymake-p)
    (advice-remove 'flymake-goto-next-error #'lazyflymake-echo-error)
    (advice-remove 'flymake-goto-prev-error #'lazyflymake-echo-error)))

(provide 'lazyflymake)
;;; lazyflymake.el ends here
