;;; shellcop.el --- Analyze info&error in shell-mode  -*- lexical-binding: t -*-

;; Copyright (C) 2020-2021 Chen Bin
;;
;; Version: 0.1.0
;; Keywords: unix tools
;; Author: Chen Bin <chenbin.sh@gmail.com>
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
;;   - Start shell-mode by "M-x shell"
;;   - Run any command line program in shell
;;   - Press ENTER in the program's output containing file and line number.
;;     Or run `shellcop-goto-location-near-point'.
;;   - Cursor is NOT required to be on the same line containing file path.
;;
;; `shellcop-reset-with-new-command' will,
;;   - kill current running process
;;   - erase the content in shell buffer
;;   - If `shellcop-sub-window-has-error-function' return nil in all sub-windows,
;;     run `shellcop-insert-shell-command-function'.
;;
;; `shellcop-erase-buffer' erases the content buffer with below names,
;;   - "*Messages*" (default)
;;   - "*shell*" (if parameter 1 is passed)
;;   - "*Javascript REPL*" (if parameter 2 is passed)
;;   - "*eshell*" (if parameter 3 is passed)
;;
;; `shellcop-jump-around' jumps to directories recorded by https://github.com/rupa/z,
;;   - If shell is visible, \"cd destination-dir\" is inserted into shell
;;   - Or else, the directory is opened in `dired-mode'
;;
;; `shellcop-search-in-shell-buffer-of-other-window' uses current word or selected text
;; to search in *shell* buffer of the other window.
;;

;;; Code:

;;;

(require 'cl-lib)
(require 'comint)
(require 'subr-x)

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

(defcustom shellcop-string-search-function 'search-backward
  "String search function for `shellcop-search-in-shell-buffer-of-other-window'."
  :type 'function
  :group 'shellcop)

(defcustom shellcop-shell-buffer-name "*shell*"
  "The name of buffer in `shell-mode'."
  :type 'string
  :group 'shellcop)

(defcustom shellcop-jump-around-data-file "~/.z"
  "The data file created by z (see https://github.com/rupa/z)."
  :type 'string
  :group 'shellcop)

(defvar shellcop-debug nil "Enable debug output if not nil.")

(defun shellcop-next-line ()
  "Content of next line."
  (save-excursion
    (forward-line 1)
    (string-trim (buffer-substring (line-beginning-position)
                                   (line-end-position)))))

(defun shellcop-location-detail ()
  "Get file, line and column from at point."
  (let* (rlt
         (str (thing-at-point 'filename))
         file
         line
         col
         next-line)

    (cond
     ((not str))

     ((string-match "^\\([^:]+\\):\\([0-9]+\\)+\\(:[0-9]+\\)?" str)
      (setq file (match-string 1 str))
      (setq line (match-string 2 str))
      (setq col (match-string 3 str)))

     ((and (setq next-line (shellcop-next-line))
           (file-exists-p str)
           (string-match "^\\([0-9]+\\)+\\(:[0-9]+\\)?" next-line))

      (setq file str)
      (setq line (match-string 1 next-line))
      ;; clean the column format
      (when (setq col (match-string 2 next-line))
        (setq col (replace-regexp-in-string ":" "" col)))))

    (when (and file line)
      (setq rlt (list file line col)))

    (when shellcop-debug
      (message "shellcop-location-details str=%s file=%s line=%s col=%s"
               str file line col))
    rlt))

(defun shellcop-extract-location ()
  "Extract location from current line."
  (let* ((end (line-end-position))
         rlt)
    (save-excursion
      (goto-char (line-beginning-position))

      ;; return the first found
      (while (and (< (point) end) (not rlt))
        ;; searching
        (when (setq rlt (shellcop-location-detail))
          (setq rlt (cons (string-trim (shellcop-current-line)) rlt))
          (forward-line))
        (forward-word)))
    (when shellcop-debug
      (message "shellcop-extract-location called. rlt=%s" rlt))
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
If ABOVE is t, extract locations above current point,
If ABOVE is nil, extract locations below current point."
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

    (when shellcop-debug
      (message "shellcop-extract-all-locations called. location=%s" location))

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

(defun shellcop-goto-location-near-point ()
  "Goto location (file, line, column) near current point."
  (interactive)
  (let* ((locations (shellcop-extract-all-locations))
         location-detail
         location)

    (when shellcop-debug
      (message "shellcop-goto-location-near-point (%s)" locations))

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
        (forward-char (string-to-number (nth 3 location-detail)))))
    locations))

(defun shellcop-comint-send-input-hack (orig-func &rest args)
  "Advice `comint-send-input' with ORIG-FUNC and ARGS.
Extract file paths when user presses enter key shell."
  (let* ((artifical (nth 1 args)))
    (when shellcop-debug
      (message "shellcop-comint-send-input-hack (%s)" artifical))
    (cond
     ((or artifical (not (eq major-mode 'shell-mode)))
      ;; do nothing
      (apply orig-func args))

     ((shellcop-goto-location-near-point))

     (t
      (apply orig-func args)))))

;;;###autoload
(defun shellcop-start ()
  "Start this program."
  (interactive)
  (advice-add 'comint-send-input :around #'shellcop-comint-send-input-hack))

(defun shellcop-all-windows ()
  "Return all windows."
  (cl-mapcan (lambda (f)
               (window-list f 0 (frame-first-window f)))
             (visible-frame-list)))

(defun shellcop-current-line ()
  "Get current line text."
  (let* ((inhibit-field-text-motion t))
    (buffer-substring-no-properties (line-beginning-position)
                                    (line-end-position))))

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
                 (mapconcat #'identity err-wins " ")))
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
   ((memq major-mode '(shell-mode message-buffer-mode inferior-python-mode))
    (shellcop-erase-one-visible-buffer (buffer-name (current-buffer)))
    (unless (eq major-mode 'message-buffer-mode)
      (comint-send-input)))

   (t
    (shellcop-erase-one-visible-buffer "*Messages*"))))

(defun shellcop-visible-window-list ()
  "Visible window list."
  (cl-mapcan (lambda (frame)
               (window-list frame 0 (frame-first-window frame)))
             (visible-frame-list)))

;;;###autoload
(defun shellcop-get-window (buffer-name)
  "Get window of buffer with BUFFER-NAME."
  (let* ((sub-window (cl-find-if `(lambda (w)
                                    (string= (buffer-name (window-buffer w)) ,buffer-name))
                                 (shellcop-visible-window-list))))
    sub-window))

;;;###autoload
(defun shellcop-focus-window (buffer-name fn)
  "Focus on window with BUFFER-NAME and run function FN."
  (let* ((sub-window (shellcop-get-window buffer-name))
         (keyword (cond
                   ((region-active-p)
                    (buffer-substring (region-beginning) (region-end)))
                   (t
                    (thing-at-point 'word)))))
    (when shellcop-debug
      (message "shellcop-focus-window called. sub-window=%s keyword=%s" sub-window keyword))
    (when sub-window
      ;; select sub-window
      (select-window sub-window)
      ;; do something
      (funcall fn keyword))))

;;;###autoload
(defun shellcop-search-in-shell-buffer-of-other-window ()
  "Search symbol or selected text in *shell* buffer of the other window."
  (interactive)
  (shellcop-focus-window
   shellcop-shell-buffer-name
   (lambda (keyword)
     (when keyword
       (funcall shellcop-string-search-function keyword)))))

;;;###autoload
(defun shellcop-directories-from-z ()
  "Get directories from z's data file."
  (when (file-exists-p shellcop-jump-around-data-file)
    ;; Emacs use gzip to extract plain text file "~/.z"
    (let* ((content (shell-command-to-string (format "cat %s" shellcop-jump-around-data-file)))
           (dirs (mapcar (lambda (line)
                           ;; line's format: "dir | score | timestamp"
                           (let* ((a (split-string line "|")))
                             (cons (nth 0 a) (string-to-number (nth 2 a)))))
                         (split-string (string-trim content) "[\n\r]+"))))

      ;; sort by timestamp in descending order
      (setq dirs (sort dirs (lambda (a b) (> (cdr a) (cdr b)))))
      dirs)))

;;;###autoload
(defun shellcop-jump-around ()
  "Jump to directories recorded by https://github.com/rupa/z.
If shell is visible, \"cd destination-dir\" is inserted into shell.
Or else, the directory is opened in `dired-mode'."
  (interactive)
  (when (file-exists-p shellcop-jump-around-data-file)
    ;; Emacs use gzip to extract plain text file "~/.z"
    (let* ((dirs (shellcop-directories-from-z))
           dest
           pattern)

      (when (> (length dirs) 0)
        (setq pattern
              (read-string "pattern to filter directory (or leave it empty): "))
        (unless (string= pattern "")
          (setq dirs
                (cl-remove-if-not (lambda (d) (string-match pattern (car d)))
                                  dirs)))
        ;; only directory candidate, select it
        (cond
         ((eq (length dirs) 1)
          (setq dest (car (nth 0 dirs))))
         (t
          (setq dest (completing-read "Select directory: " dirs))))

        (when dest
          (cond
           ((derived-mode-p 'comint-mode)
            (insert "cd " dest))

           ;; jump to the shell
           ((shellcop-get-window shellcop-shell-buffer-name)
            (shellcop-focus-window shellcop-shell-buffer-name
                                   (lambda (keyword)
                                     (ignore keyword)
                                     (insert "cd " dest))))

           (t
            (dired dest))))))))

(provide 'shellcop)
;;; shellcop.el ends here
