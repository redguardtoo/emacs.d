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
(require 'lazyflymake-sdk)

;; fixing syntax error costs more time
(defcustom lazyflymake-update-interval 3
  "Interval (seconds) for `lazyflymake-check-buffer'."
  :group 'lazyflymake
  :type 'integer)

(defcustom lazyflymake-flymake-mode-on t
  "If t, the \"flymake-mode\" is turned on by `lazyflymake-start' automatically.
If nil, the \"flymake-mode\" is not turned on and smart checking algorithm
is used when current file is saved."
  :group 'lazyflymake
  :type 'boolean)

(defcustom lazyflymake-shell-script-modes '(sh-mode)
  "Major modes for shell script."
  :group 'lazyflymake
  :type '(repeat 'sexp))

(defcustom lazyflymake-file-match-algorithm "strict"
  "The algorithm to match file name.
If it's \"string\", the full path of file should be same as current code file.
If it's nil, do not check file at all."
  :group 'lazyflymake
  :type 'string)

(defcustom lazyflymake-check-buffer-max (* 128 1024 1024)
  "Max size of buffer to run `lazyflymake-check-buffer'."
  :type 'integer
  :group 'lazyflymake)

(defvar lazyflymake-overlays nil "The overlays for syntax errors.")

;; Timer to run auto-update tags file
(defvar lazyflymake-timer nil "Internal timer.")

(defvar lazyflymake-start-check-now nil
  "If it's t, `lazyflymake-start' starts buffer syntax check immediately.
This variable is for debug and unit test only.")

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

(defun lazyflymake-proc-buffer (&optional force-erase-p)
  "Get process buffer.  Erase its content if FORCE-ERASE-P is t."
  (let* ((buf (or (get-buffer "lazyflymake-stdout")
                  (generate-new-buffer "lazyflymake-stdout"))))
    (when force-erase-p
      (with-current-buffer buf
        (erase-buffer)))
    buf))

(defun lazyflymake-parse-err-line (text)
  "Extract error information from TEXT."
  (let* (rlt (i 0) )
    (while (and (not rlt)
                flymake-err-line-patterns
                (< i (length flymake-err-line-patterns)))
      (let* ((pattern (nth i flymake-err-line-patterns))
             (regexp (nth 0 pattern))
             (file-idx (nth 1 pattern))
             (line-idx (nth 2 pattern))
             (col-idx (nth 3 pattern))
             (err-text-idx (nth 4 pattern))
             file
             line
             col
             err-text)
        (when (string-match regexp text)
          (setq file (and file-idx (match-string file-idx text)))
          (setq line (and line-idx (match-string line-idx text)))
          (setq col (and col-idx (match-string col-idx text)))
          (setq err-text (and err-text-idx (match-string err-text-idx text)))
          (when (and file line err-text)
            (setq col (if col (1- (string-to-number col)) 0))
            (save-excursion
              (goto-char (point-min))
              (forward-line (1- (string-to-number line)))
              ;; push error start and end of error
              (setq rlt (list file
                              (+ (line-beginning-position) col)
                              (line-end-position)
                              err-text))))))
      (setq i (1+ i)))
    rlt))

(defun lazyflymake-clear-errors ()
  "Remove error overlays being displayed."
  (interactive)
  (save-excursion
    (widen)
    (dolist (ov lazyflymake-overlays)
      (delete-overlay ov))
    (setq lazyflymake-overlays nil)))

(defun lazyflymake-make-overlay (err)
  "Create overlay from ERR."
  (let* ((err-text (nth 3 err))
         (ov (make-overlay (nth 1 err) (nth 2 err))))
    (overlay-put ov 'category 'flymake-error)
    (overlay-put ov 'face 'flymake-error)
    (overlay-put ov 'help-echo err-text)
    (overlay-put ov 'evaporate t)
    ov))

(defun lazyflymake-current-file-p (file)
  "FILE does match `buffer-file-name'."

  ;; algorithms to match file
  ;; - exactly same as full path name or at least file name is same
  ;; - don't worry about file name at all
  (let* ((algorithm lazyflymake-file-match-algorithm)
         rlt)
    (cond
     ((or (not buffer-file-name) (not file))
      (when (not algorithm)
        (setq rlt t)))

     ((and (string= algorithm "strict")
           (string= (file-truename buffer-file-name) (file-truename file)))
      (setq rlt t))

     ((not algorithm)
      (setq rlt t)))

    rlt))

(defun lazyflymake-extract-errors (output)
  "Extract errors from command line OUTPUT."
  (let* (errors)
    (cond
     ((and (version< "25" emacs-version) (eq major-mode 'emacs-lisp-mode))
      (setq output (replace-regexp-in-string "^:elisp-flymake-output-start[\r\n]*" "" output))
      (unless (string= "" output)
        (let* ((original-errors (read output)))
          (setq errors (mapcar (lambda (e)
                                 (list buffer-file-name
                                       (nth 1 e)
                                       (save-excursion
                                         (goto-char (nth 1 e))
                                         (line-end-position))
                                       (nth 0 e)))
                               original-errors)))))
     (t
      ;; extract syntax errors
      (dolist (l (split-string output "[\r\n]+"  t "[ \t]+"))
        (let* ((err (lazyflymake-parse-err-line l)))
          (when err (push err errors))))))
    errors))

(defun lazyflymake-show-errors (errors)
  "Show ERRORS with overlays."
  (if lazyflymake-debug (message "lazyflymake-show-errors called"))
  (let* ((ovs lazyflymake-overlays))
    ;; render overlays
    (save-restriction
      (widen)
      ;; make new overlays
      (dolist (err errors)
        (let* ((file (nth 0 err)))
          (when (or (lazyflymake-current-file-p file)
                    (eq major-mode 'emacs-lisp-mode))
            (push (lazyflymake-make-overlay err) ovs))))
      ;; remove overlay without binding buffer
      (setq ovs (cl-remove-if (lambda (ov) (not (overlay-start ov))) ovs))
      (setq lazyflymake-overlays
            (sort ovs (lambda (a b) (< (overlay-start a) (overlay-start b))))))))

(defun lazyflymake-proc-output (process)
  "The output of PROCESS."
  (with-current-buffer (process-buffer process)
    (buffer-string)))

(defun lazyflymake-proc-report (process event)
  "Handle PROCESS and its EVENT."
  (ignore event)
  (let* ((status (process-status process)))
    (when (memq status '(exit signal))
      (let* ((errors (lazyflymake-extract-errors (lazyflymake-proc-output process))))
        (lazyflymake-show-errors errors)))))

(defun lazyflymake-start-buffer-checking-process ()
  "Check current buffer right now."
  (let* ((backend (cl-find-if (lambda (m)
                                (string-match (car m) buffer-file-name))
                              flymake-allowed-file-name-masks)))
    (when (and backend
               ;; only when syntax checking process should be running
               (memq (process-status "lazyflymake-proc") '(nil exit signal)))
      (unwind-protect
          (let* ((flymake-proc--temp-source-file-name nil)
                 (init-fn (nth 1 backend))
                 (cmd-and-args (funcall init-fn))
                 (program (car cmd-and-args))
                 (args (nth 1 cmd-and-args))
                 (buf (lazyflymake-proc-buffer t))
                 (proc (apply 'start-file-process "lazyflymake-proc" buf program args)))
            (lazyflymake-clear-errors)
            (when flymake-proc--temp-source-file-name
              (process-put proc 'flymake-proc--temp-source-file-name flymake-proc--temp-source-file-name))
            (set-process-sentinel proc #'lazyflymake-proc-report)

            (when (and (eq major-mode 'emacs-lisp-mode)
                       (fboundp 'elisp-flymake-checkdoc))
              (elisp-flymake-checkdoc (lambda (diags)
                                        (let* (errs beg end)
                                          (dolist (d diags)
                                            (setq beg (or (flymake--diag-beg d) 0))
                                            (setq end (or (flymake--diag-end d)
                                                          (save-excursion
                                                            (goto-char beg)
                                                            (line-end-position))))
                                            (push (list buffer-file-name beg end (flymake--diag-text d))
                                                  errs))
                                          (when errs
                                            (lazyflymake-show-errors (nreverse errs))))))))))))

(defun lazyflymake-check-buffer ()
  "Spell check current buffer."
  (if lazyflymake-debug (message "lazyflymake-check-buffer called."))
  (cond
   ((not lazyflymake-timer)
    ;; start timer if not started yet
    (setq lazyflymake-timer (current-time)))

   ((< (- (float-time (current-time)) (float-time lazyflymake-timer))
       lazyflymake-update-interval)
    ;; do nothing, avoid `flyspell-buffer' too often
    (if lazyflymake-debug "Flymake syntax check skipped."))

   (t
    ;; check
    (setq lazyflymake-timer (current-time))
    (when (and (< (buffer-size) lazyflymake-check-buffer-max))
      (lazyflymake-start-buffer-checking-process)
      (if lazyflymake-debug (message "Flymake syntax checking ..."))))))

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
  (cond
   ;; Emacs 25, 26
   ((boundp 'flymake-err-info)
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
   (t
    (let* ((ov (lazyflymake-overlay-at-point)))
      (when ov
        (flymake--diag-text (overlay-get ov 'flymake-diagnostic)))))))

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

(defun lazyflymake-overlay-at-point (&optional position)
  "Find overlay at POSITION."
  (unless position (setq position (point)))
  (save-excursion
    (goto-char position)
    (cl-find-if (lambda (ov)
                  (and (< (overlay-start ov) (overlay-end ov))
                       (memq (overlay-get ov 'category) '(flymake-note flymake-error flymake-warning))))
                (overlays-in (line-beginning-position) (line-end-position)))))

(defun lazyflymake-echo-error (&optional arg)
  "Echo error at point.  ARG is ignored."
  (ignore arg)
  (cond
   (flymake-mode
    (message (lazyflymake--legacy-info-at-point)))
   (t
    (let* ((ov (lazyflymake-overlay-at-point)))
      (when ov
        (message "%s" (overlay-get ov 'help-echo)))))))

(defun lazyflymake-goto-overlay-center (overlay)
  "Go to center of OVERLAY."
  (goto-char (/ (+ (overlay-start overlay) (overlay-end overlay)) 2)))

(defun lazyflymake-goto-next-error ()
  "Got to next syntax error."
  (interactive)
  (cond
   (flymake-mode
    (flymake-goto-next-error)
    (lazyflymake-echo-error))
   (t
    (let* ((start (line-end-position))
           (ov (cl-find-if `(lambda (ov) (< ,start (overlay-start ov)))
                           lazyflymake-overlays)))
      (when ov
        (lazyflymake-goto-overlay-center ov)
        (lazyflymake-echo-error))))))

(defun lazyflymake-goto-prev-error ()
  "Got to previous syntax error."
  (interactive)
  (cond
   (flymake-mode
    (flymake-goto-prev-error)
    (lazyflymake-echo-error))
   (t
    (let* ((start (line-beginning-position))
           (ov (cl-find-if `(lambda (ov) (> ,start (overlay-end ov)))
                           (nreverse lazyflymake-overlays))))
      (when ov
        (lazyflymake-goto-overlay-center ov)
        (lazyflymake-echo-error))))))

;;;###autoload
(defun lazyflymake-start ()
  "Turn on lazyflymake to syntax check code."
  (interactive)

  ;; set up `flymake-allowed-file-name-masks'

  ;; Since Emacs 26, `flymake-mode' uses `elisp-flymake-byte-compile'
  ;; and `elisp-flymake-checkdoc'.
  (unless lazyflymake-flymake-mode-on
    (lazyflymake-load "\\.el$" 'elisp))

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

  (when lazyflymake-debug
    (message "flymake-allowed-file-name-masks=%s" flymake-allowed-file-name-masks))

  ;; js-mode has its own linter
  (unless (derived-mode-p 'js2-mode)
    (lazyflymake-load "\\.[jt]s$" 'eslint))

  ;; initialize some internal variables of `flymake-mode'
  (flymake-mode 1)
  (unless lazyflymake-flymake-mode-on
    (flymake-mode -1))

  (cond
   ;; for debug, unit test, and CI
   (lazyflymake-start-check-now
    (lazyflymake-start-buffer-checking-process)
    (if lazyflymake-debug (message "Flymake syntax checking now ...")))

   ((not lazyflymake-flymake-mode-on)
    ;; local hook will override global hook. So have to use local hook
    ;; here.
    (add-hook 'after-save-hook #'lazyflymake-check-buffer nil t))))

;;;###autoload
(defun lazyflymake-stop ()
  "Turn on lazyflymake to syntax check code."
  (interactive)
  (unless lazyflymake-flymake-mode-on
    (remove-hook 'after-save-hook #'lazyflymake-check-buffer t))

  (unless (lazyflymake-new-flymake-p)
    (advice-remove 'flymake-goto-next-error #'lazyflymake-echo-error)
    (advice-remove 'flymake-goto-prev-error #'lazyflymake-echo-error)))

(provide 'lazyflymake)
;;; lazyflymake.el ends here
