;;; shellcop.el --- analyze errors reported in Emacs builtin shell  -*- lexical-binding: t -*-

;; Copyright (C) 2020 Chen Bin
;;
;; Version: 0.0.3
;; Keywords: unix tools
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: https://github.com/redguardtoo/shellcop
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

;;  Open the file from command line error report,
;;   - Insert "(add-hook 'shell-mode-hook 'shellcop-start)" into ~/.emacs
;;   - Start shell by "M-x shell"
;;   - Run any command line program in shell
;;   - Press ENTER in the program's output which contains file and line number
;;
;; `shellcop-reset-with-new-command' will,
;;   - kill current running process
;;   - erase the content in shell buffer
;;   - If `shellcop-sub-window-has-error-function' return nil in all sub-windows, run `shellcop-insert-shell-command-function'.
;;
;; `shellcop-erase-buffer' erases the content buffer with below names,
;;   - "*Messages*" (default)
;;   - "*shell*" (if parameter 1 is passed)
;;   - "*Javascript REPL*" (if parameter 2 is passed)
;;   - "*eshell*" (if parameter 3 is passed)
;;

;;; Code:

;;;

(require 'cl-lib)

(defgroup shellcop nil
  "Analyze errors reported in Emacs builtin shell."
  :group 'tools)

(defcustom shellcop-insert-shell-command-function
  nil
  "Function to insert command when calling `shellcop-reset-with-new-command'."
  :type 'function
  :group 'shellcop)

(defcustom shellcop-sub-window-has-error-function
  nil
  "Get errors of sub-window when calling `shellcop-reset-with-new-command'.
If there is error, it returns t."
  :type 'function
  :group 'shellcop)

(defcustom shellcop-excluded-file-patterns
  '("\\.\\(bundle\\|min\\)\\.[tj]sx?$"
    "/node_modules/"
    "/\\.svn/"
    "/\\.hg/"
    "/\\.git/")
  "File patterns to be excluded from analysis."
  :type '(repeat sexp)
  :group 'shellcop)

(defcustom shellcop-terminal-primary-prompt "^\\$ "
  "The primary prompt of terminal."
  :type 'string
  :group 'shellcop)

(defcustom shellcop-wait-time-after-kill-running-job 2
  "Seconds to wait after kill running job in shell."
  :type 'number
  :group 'shellcop)

(defun shellcop-location-detail (str)
  "Get file, line and column from STR."
  (when (string-match "^\\([^:]+\\):\\([0-9]+\\)+\\(:[0-9]+\\)?$" str)
    (let* ((file (match-string 1 str))
           (line (match-string 2 str))
           (col (match-string 3 str)))
      ;; clean the column format
      (when col
        (setq col (replace-regexp-in-string ":" "" col)))
      (list file line col))))

(defun shellcop-extract-location ()
  "Extract location from current line."
  (let* (file
         (end (line-end-position))
         rlt)
    (save-excursion
      (goto-char (line-beginning-position))

      ;; return the first found
      (while (and (< (point) end) (not rlt))
        ;; searching
        (when (setq file (thing-at-point 'filename))
          (when (setq rlt (shellcop-location-detail file))
            (setq rlt (cons (string-trim (shellcop-current-line)) rlt))))
        (forward-word)))
    rlt))

(defmacro shellcop-push-location (location result)
  "Push LOCATION into RESULT."
  `(unless (cl-some (lambda (pattern)
                      (let* ((file (nth 1 ,location)))
                        (or (string-match pattern file)
                            (not (file-exists-p file)))))
                    shellcop-excluded-file-patterns)
     (push ,location ,result)))

(defun shellcop-extract-locations-at-point (&optional above)
  "Extract locations in one direction into RLT.
If ABOVE is t, extract locations above current point; or else below current point."
  (let* (rlt
         (line (if above -1 1))
         location)
    (save-excursion
      (while (and (eq (forward-line line) 0)
                  (setq location (shellcop-extract-location)))
        (shellcop-push-location location rlt)))
    rlt))

(defun shellcop-extract-all-locations ()
  "Extract all locations near current point."
  (let* ((location (shellcop-extract-location))
         rlt)
    ;; at least current line should contain file path
    (when location
      (shellcop-push-location location rlt)
      (setq rlt (append rlt
                        (shellcop-extract-locations-at-point t)
                        (shellcop-extract-locations-at-point))))
    rlt))

(defun shellcop-forward-line (n)
  "Forward N lines."
  (when (and n (> n 0))
    (goto-char (point-min))
    (forward-line (1- n))))

(defun shellcop-comint-send-input-hack (orig-func &rest args)
  "Advice `comint-send-input' with ORIG-FUNC and ARGS.
Extract file paths when user presses enter key shell."
  (let* ((artifical (nth 1 args))
         locations)
    (cond
     ((or artifical (not (eq major-mode 'shell-mode)))
      ;; do nothing
      (apply orig-func args))

     ((setq locations (shellcop-extract-all-locations))
      (let* (location-detail
             location)
        (when (and (> (length locations) 0)
                   (setq location (completing-read "Go to: " locations))
                   (setq location-detail (assoc location locations)))
          (find-file-other-window (nth 1 location-detail))
          (goto-char (point-min))
          ;; forward N lines
          (shellcop-forward-line (string-to-number (nth 2 location-detail)))
          ;; move to specific column
          (when (nth 3 location-detail)
            (goto-char (line-beginning-position))
            (forward-char (string-to-number (nth 3 location-detail)))))))
     (t
      (apply orig-func args)))))

;;;###autoload
(defun shellcop-start ()
  "Start this program."
  (interactive)
  (advice-add 'comint-send-input :around #'shellcop-comint-send-input-hack))

;;;###autoload
(defun shellcop-all-windows ()
  "Return all windows."
  (cl-mapcan (lambda (f)
               (window-list f 0 (frame-first-window f)))
             (visible-frame-list)))

;;;###autoload
(defun shellcop-current-line ()
  "Get current line text."
  (let* ((inhibit-field-text-motion t))
    (buffer-substring-no-properties (line-beginning-position)
                                    (line-end-position))))

;;;###autoload
(defun shellcop-prompt-line-p (&optional position)
  "If line at POSITION has prompt at the beginning."
  (let* (rlt)
    ;; user can't move the cursor to the first column in prompt line
    (save-excursion
      (goto-char (or position (point)))
      (goto-char (line-beginning-position))
      (setq rlt (> (current-column) 1)))

    ;; another round if we can't decide cursor movement
    (unless rlt
      (setq rlt (string-match-p shellcop-terminal-primary-prompt
                                (shellcop-current-line))))
    rlt))

(defun shellcop-search-backward-prompt (n)
  "Search backward for N prompt.
Return the line beginning of prompt line."
  (let* (rlt
         (first-line-end-pos (save-excursion
                               (goto-char (point-min))
                               (line-end-position))))
    (save-excursion
      (while (and (> (line-beginning-position) first-line-end-pos)
                  (> n 0))
        (when (shellcop-prompt-line-p)
          (setq n (1- n))
          (setq rlt (line-beginning-position)))
        (forward-line -1)))
    rlt))

;;;###autoload
(defun shellcop-erase-one-visible-buffer (buf-name &optional n)
  "Erase the content of visible buffer with BUF-NAME.
Keep latest N cli program output if it's not nil."
  (let* ((original-window (get-buffer-window))
         (target-window (get-buffer-window buf-name))
         beg)
    (cond
     ((not target-window)
      (message "Buffer %s is not visible!" buf-name))
     (t
      (select-window target-window)
      (let* ((inhibit-read-only t))
        (when (and n (> n 0))
          ;; skip current prompt line
          (forward-line -2)
          (setq beg (shellcop-search-backward-prompt n)))
        (cond
         (beg
          (delete-region (point-min) beg))
         (t
          (erase-buffer))))
      (select-window original-window)))))

;;;###autoload
(defun shellcop-reset-with-new-command ()
  "Kill running sub-process, erase shell, insert new command."
  (interactive)
  (cond
   ;; erase buffer, check errors in other window and insert certain command
   ((derived-mode-p 'comint-mode)
    ;; loop all sub-windows.
    ;; if no error, run `shellcop-check-errors-of-other-windows-function'
    (let* ((orig-w (get-buffer-window))
           (wins (shellcop-all-windows))
           err-wins)
      (dolist (w wins)
        (select-window w)
        (when (and shellcop-sub-window-has-error-function
                   (funcall shellcop-sub-window-has-error-function))
          (push (buffer-name) err-wins)))
      ;; back to original window
      (select-window orig-w)

      ;; kill current running process
      (comint-interrupt-subjob)

      ;; wait
      (sit-for shellcop-wait-time-after-kill-running-job)

      (shellcop-erase-one-visible-buffer (buffer-name (current-buffer)))
      (goto-char (point-max))

      (cond
       (err-wins
        (message "Code syntax error in windows %s"
                 (mapconcat 'identity err-wins " ")))
       (shellcop-insert-shell-command-function
        (funcall shellcop-insert-shell-command-function)))))

   (t
    (message "Can't erase buffer in %s" major-mode))))

;;;###autoload
(defun shellcop-erase-buffer ()
  "Erase *Messages* buffer if not in `shell-mode' or `messages-buffer-mode'.
Or else erase current buffer."
  (interactive)
  (cond
   ((memq major-mode '(shell-mode message-buffer-mode))
    (shellcop-erase-one-visible-buffer (buffer-name (current-buffer)))
    (when (eq major-mode 'shell-mode)
      (comint-send-input)))

   (t
    (shellcop-erase-one-visible-buffer "*Messages*"))))

(provide 'shellcop)
;;; shellcop.el ends here
