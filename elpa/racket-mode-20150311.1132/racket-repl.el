;;; racket-repl.el

;; Copyright (c) 2013-2015 by Greg Hendershott.
;; Portions Copyright (C) 1985-1986, 1999-2013 Free Software Foundation, Inc.
;; Image portions Copyright (C) 2012 Jose Antonio Ortega Ruiz.

;; Author: Greg Hendershott
;; URL: https://github.com/greghendershott/racket-mode

;; License:
;; This is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version. This is distributed in the hope that it will be
;; useful, but without any warranty; without even the implied warranty
;; of merchantability or fitness for a particular purpose. See the GNU
;; General Public License for more details. See
;; http://www.gnu.org/licenses/ for details.

(require 'racket-custom)
(require 'racket-common)
(require 'racket-util)
(require 'comint)
(require 'compile)
(require 'easymenu)

(defconst racket--repl-buffer-name/raw
  "Racket REPL"
  "The base buffer name, NOT surrounded in *stars*")
(defconst racket--repl-buffer-name
  (concat "*" racket--repl-buffer-name/raw "*")
  "The actual buffer name as created by comint-mode")
(defun racket--get-repl-buffer-process ()
  (get-buffer-process racket--repl-buffer-name))

(defun racket-repl--input-filter (str)
  "Don't save anything matching `racket-history-filter-regexp'."
  (not (string-match racket-history-filter-regexp str)))

(defun racket--get-old-input ()
  "Snarf the sexp ending at point."
  (if (looking-back comint-prompt-regexp (line-beginning-position))
      ""
    (save-excursion
      (let ((end (point)))
        (backward-sexp)
        (buffer-substring (point) end)))))

;; I don't want comint-mode clobbering our font-lock with
;; comint-highlight-input face. Changing that _face_ to be non-bold
;; isn't sufficient, it simply clobbers everything non-bold.
;;
;; So far, the least-pukey way I can figure out how to do this is to
;; copy-pasta much of comint-send-input, and modify the one tiny
;; offending bit.  Blech. If anyone reading this knows a better way,
;; please let me know!
;;
;; Update: I went on to slim down the copy -- deleted the `no-newline`
;; and `artificial` args we don't use, and the code that could only
;; execute if they were non-nil.
(defun racket--comint-send-input ()
  "Like `comint-send-input` but doesn't use face `comint-highlight-input'."
  ;; Note that the input string does not include its terminal newline.
  (let ((proc (get-buffer-process (current-buffer))))
    (if (not proc) (user-error "Current buffer has no process")
      (widen)
      (let* ((pmark (process-mark proc))
             (intxt (if (>= (point) (marker-position pmark))
                        (progn (if comint-eol-on-send (end-of-line))
                               (buffer-substring pmark (point)))
                      (let ((copy (racket--get-old-input)))
                        (goto-char pmark)
                        (insert copy)
                        copy)))
             (input (if (not (eq comint-input-autoexpand 'input))
                        ;; Just whatever's already there.
                        intxt
                      ;; Expand and leave it visible in buffer.
                      (comint-replace-by-expanded-history t pmark)
                      (buffer-substring pmark (point))))
             (history (if (not (eq comint-input-autoexpand 'history))
                          input
                        ;; This is messy 'cos ultimately the original
                        ;; functions used do insertion, rather than return
                        ;; strings.  We have to expand, then insert back.
                        (comint-replace-by-expanded-history t pmark)
                        (let ((copy (buffer-substring pmark (point)))
                              (start (point)))
                          (insert input)
                          (delete-region pmark start)
                          copy))))
        (insert ?\n)
        (comint-add-to-input-history history)
        (run-hook-with-args 'comint-input-filter-functions
                            (concat input "\n"))
        (let ((beg (marker-position pmark))
              (end (1- (point)))
              (inhibit-modification-hooks t))
          (when (> end beg)
            ;;;; The bit from comint-send-input that we DON'T want:
            ;; (add-text-properties beg end
            ;;                      '(front-sticky t
            ;;                        font-lock-face comint-highlight-input))
            (unless comint-use-prompt-regexp
              ;; Give old user input a field property of `input', to
              ;; distinguish it from both process output and unsent
              ;; input.  The terminating newline is put into a special
              ;; `boundary' field to make cursor movement between input
              ;; and output fields smoother.
              (add-text-properties
               beg end
               '(mouse-face highlight
                 help-echo "mouse-2: insert after prompt as new input"))))
          (unless comint-use-prompt-regexp
            ;; Cover the terminating newline
            (add-text-properties end (1+ end)
                                 '(rear-nonsticky t
                                   field boundary
                                   inhibit-line-move-field-capture t))))
        (comint-snapshot-last-prompt)
        (setq comint-save-input-ring-index comint-input-ring-index)
        (setq comint-input-ring-index nil)
        ;; Update the markers before we send the input
        ;; in case we get output amidst sending the input.
        (set-marker comint-last-input-start pmark)
        (set-marker comint-last-input-end (point))
        (set-marker (process-mark proc) (point))
        ;; clear the "accumulation" marker
        (set-marker comint-accum-marker nil)
        (funcall comint-input-sender proc input)
        ;; This used to call comint-output-filter-functions,
        ;; but that scrolled the buffer in undesirable ways.
        (run-hook-with-args 'comint-output-filter-functions "")))))

(defun racket-repl-eval-or-newline-and-indent ()
  "If complete sexpr, eval in Racket. Else do `racket-newline-and-indent'."
  (interactive)
  (let ((proc (get-buffer-process (current-buffer))))
    (cond ((not proc) (user-error "Current buffer has no process"))
          ((not (eq "" (racket--get-old-input)))
           (condition-case nil
               (progn
                 (save-excursion
                   (goto-char (process-mark proc))
                   (forward-list)) ;will error unless complete sexpr
                 (racket--comint-send-input))
             (error (newline-and-indent)))))))

;;;###autoload
(defun racket-repl (&optional noselect)
  "Run the Racket REPL and display its buffer in some window.

If the Racket process is not already running, it is started.

If NOSELECT is not nil, does not select the REPL
window (preserves the originally selected window).

Commands that don't want the REPL to be displayed can instead use
`racket--repl-ensure-buffer-and-process'."
  (interactive "P")
  (racket--repl-ensure-buffer-and-process t)
  (unless noselect
    (select-window (get-buffer-window racket--repl-buffer-name))))

(defvar racket--run.rkt
  (expand-file-name "run.rkt"
                    (file-name-directory (or load-file-name (buffer-file-name))))
  "Path to run.rkt")

(defvar racket--repl-command-output-file
  (make-temp-file "racket-mode-command-ouput-file")
  "File used to collect output from commands used by racket-mode.")

(defun racket--repl-ensure-buffer-and-process (&optional display)
  "Ensure Racket REPL buffer exists and has live Racket process.

If the Racket process is not already running, it is started and
the buffer is put in `racket-repl-mode'.

Non-nil DISPLAY means `display-buffer'.

Never changes selected window."
  (if (comint-check-proc racket--repl-buffer-name)
      (when display
        (display-buffer racket--repl-buffer-name))
    (with-current-buffer
        (make-comint racket--repl-buffer-name/raw ;w/o *stars*
                     racket-racket-program
                     nil
                     racket--run.rkt
                     racket--repl-command-output-file)
      ;; Display now so users see startup and banner sooner.
      (when display
        (display-buffer (current-buffer)))
      ;; The following is needed to make e.g. λ work when pasted
      ;; into the comint-buffer, both directly by the user and via
      ;; the racket--repl-eval functions.
      (set-process-coding-system (get-buffer-process racket--repl-buffer-name)
                                 'utf-8 'utf-8)
      (racket-repl-mode))))

(defun racket-repl-file-name ()
  "Return the file running in the buffer, or nil.

The result can be nil if the REPL is not started, or if it is
running no particular file as with the `,top` command."
  (when (comint-check-proc racket--repl-buffer-name)
    (racket--repl-cmd/sexpr ",path")))

(defun racket-repl-switch-to-edit ()
  "Switch to the window for the buffer of the file running in the REPL.

If no buffer is visting the file, `find-file' it in `other-window'.

If the REPL is running no file (if the prompt is `>`), do nothing."
  (interactive)
  (let ((path (racket-repl-file-name)))
    (unless path
      (user-error "The REPL is not running any file"))
    (let ((buffer (find-buffer-visiting path)))
      (if buffer
          (pop-to-buffer buffer t)
        (other-window 1)
        (find-file path)))))

(defun racket--repl-eval (expression)
  "Eval EXPRESSION in the *Racket REPL* buffer.
Allow Racket process output to be displayed, and show the window.
Intended for use by things like ,run command."
  (racket-repl t)
  (racket--repl-forget-errors)
  (comint-send-string (racket--get-repl-buffer-process) expression)
  (racket--repl-show-and-move-to-end))

(defconst racket--repl-command-timeout 10
  "Default timeout when none supplied to `racket--repl-cmd/buffer' and friends.")

(defun racket--repl-cmd/buffer (command &optional timeout)
  "Send COMMAND capturing its input in the returned buffer.

Expects COMMAND to already include the comma/unquote prefix: `,command`.

Prepends a `#` to make it `#,command`. This causes output to be
redirected to `racket--repl-command-output-file'. When that file
comes into existence, the command has completed and we read its
contents into a buffer."
  (racket--repl-ensure-buffer-and-process)
  (when (file-exists-p racket--repl-command-output-file)
    (delete-file racket--repl-command-output-file))
  (comint-send-string (racket--get-repl-buffer-process)
                      (concat "#" command "\n")) ;e.g. #,command
  (let ((deadline (+ (float-time) (or timeout racket--repl-command-timeout))))
    (while (and (not (file-exists-p racket--repl-command-output-file))
                (< (float-time) deadline))
      (accept-process-output (get-buffer-process racket--repl-buffer-name)
                             (- deadline (float-time)))
      (sit-for 0))) ;let REPL output be drawn
  (unless (file-exists-p racket--repl-command-output-file)
    (error "Command timed out"))
  (let ((buf (get-buffer-create " *Racket Command Output*")))
    (with-current-buffer buf
      (erase-buffer)
      (insert-file-contents racket--repl-command-output-file)
      (delete-file racket--repl-command-output-file))
    buf))

(defun racket--repl-cmd/string (command &optional timeout)
  (with-current-buffer (racket--repl-cmd/buffer command timeout)
    (buffer-substring (point-min) (point-max))))

(defun racket--repl-cmd/sexpr (command &optional timeout)
  (eval (read (racket--repl-cmd/string command timeout))))

;;;

(defun racket--send-region-to-repl (start end)
  "Internal function to send the region to the Racket REPL.
Before sending the region, calls `racket-repl' and
`racket--repl-forget-errors'. Afterwards calls
`racket--repl-show-and-move-to-end'."
  (when (and start end)
    (racket-repl t)
    (racket--repl-forget-errors)
    (comint-send-region (racket--get-repl-buffer-process) start end)
    (comint-send-string (racket--get-repl-buffer-process) "\n")
    (racket--repl-show-and-move-to-end)))

(defun racket-send-region (start end)
  "Send the current region (if any) to the Racket REPL."
  (interactive "r")
  (if (region-active-p)
      (racket--send-region-to-repl start end)
    (beep)
    (message "No region.")))

(defun racket-send-definition ()
  "Send the current definition to the Racket REPL."
  (interactive)
  (save-excursion
   (end-of-defun)
   (let ((end (point)))
     (beginning-of-defun)
     (racket--send-region-to-repl (point) end))))

(defun racket-send-last-sexp ()
  "Send the previous sexp to the Racket REPL."
  (interactive)
  (racket--send-region-to-repl (save-excursion (backward-sexp) (point))
                               (point)))

(defun racket--repl-forget-errors ()
  "Forget existing compilation mode errors in the REPL.
Although they remain clickable, `next-error' and `previous-error'
will ignore them."
  (with-current-buffer racket--repl-buffer-name
    (compilation-forget-errors)))

(defun racket--repl-show-and-move-to-end ()
  "Make the Racket REPL visible, and move point to end.
Keep original window selected."
  (display-buffer racket--repl-buffer-name)
  (save-selected-window
    (select-window (get-buffer-window racket--repl-buffer-name))
    (comint-show-maximum-output)))

;;; Inline images in REPL

(defvar racket-image-cache-dir nil)

(defun racket-repl--list-image-cache ()
  "List all the images in the image cache."
  (and racket-image-cache-dir
       (file-directory-p racket-image-cache-dir)
       (let ((files (directory-files-and-attributes
                     racket-image-cache-dir t "racket-image-[0-9]*.png")))
         (mapcar 'car
                 (sort files (lambda (a b)
                               (< (float-time (nth 6 a))
                                  (float-time (nth 6 b)))))))))

(defun racket-repl--clean-image-cache ()
  "Clean all except for the last `racket-images-keep-last'
images in 'racket-image-cache-dir'."
  (interactive)
  (dolist (file (butlast (racket-repl--list-image-cache)
                         racket-images-keep-last))
    (delete-file file)))

(defun racket-repl--replace-images ()
  "Replace all image patterns with actual images"
  (with-silent-modifications
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward "\"#<Image: \\([-+./_0-9a-zA-Z]+\\)>\"" nil t)
        ;; can't pass a filename to create-image because emacs might
        ;; not display it before it gets deleted (race condition)
        (let* ((file (match-string 1))
               (begin (match-beginning 0))
               (end (match-end 0)))
          (delete-region begin end)
          (goto-char begin)
          (if (and racket-images-inline (display-images-p))
              (insert-image (create-image file) "[image]")
            (goto-char begin)
            (insert "[image] ; use M-x racket-view-last-image to view"))
          (setq racket-image-cache-dir (file-name-directory file))
          (racket-repl--clean-image-cache))))))

(defun racket-view-last-image (n)
  "Open the last displayed image using `racket-images-system-viewer'.

With prefix arg, open the N-th last shown image."
  (interactive "p")
  (let ((images (reverse (racket-repl--list-image-cache))))
    (if (>= (length images) n)
        (start-process "Racket image view"
                       nil
                       racket-images-system-viewer
                       (nth (- n 1) images))
      (error "There aren't %d recent images" n))))

(defun racket-repl--output-filter (txt)
  (racket-repl--replace-images))

;;; racket-repl-mode

(defvar racket-repl-mode-map
  (racket--easy-keymap-define
   '(("RET"             racket-repl-eval-or-newline-and-indent)
     ("TAB"             indent-for-tab-command)
     ("M-C-u"           racket-backward-up-list)
     ("C-a"             comint-bol)
     ("C-w"             comint-kill-region)
     ("[C-S-backspace]" comint-kill-whole-line)
     ("["               racket-smart-open-bracket)
     (")"               racket-insert-closing-paren)
     ("]"               racket-insert-closing-bracket)
     ("}"               racket-insert-closing-brace)
     ("M-C-y"           racket-insert-lambda)
     ("C-c C-d"         racket-doc)
     ("C-c C-."         racket-describe)
     ("M-."             racket-visit-definition)
     ("C-M-."           racket-visit-module)
     ("C-c C-z"         racket-repl-switch-to-edit)))
  "Keymap for Racket REPL mode.")

(easy-menu-define racket-repl-mode-menu racket-repl-mode-map
  "Menu for Racket REPL mode."
  '("Racket"
    ["Insert λ" racket-insert-lambda]
    ["Indent Region" indent-region]
    ["Cycle Paren Shapes" racket-cycle-paren-shapes]
    "---"
    ["Visit Definition" racket-visit-definition]
    ["Visit Module" racket-visit-module]
    ["Return from Visit" racket-unvisit]
    "---"
    ["Racket Documentation" racket-doc]
    ["Describe" racket-describe]
    "---"
    ["Switch to Edit Buffer" racket-repl-switch-to-edit]))

(define-derived-mode racket-repl-mode comint-mode "Racket-REPL"
  "Major mode for Racket REPL.
\\{racket-repl-mode-map}"
  (racket--variables-for-both-modes)
  (setq-local comint-prompt-regexp ".*?> +")
  (setq-local comint-use-prompt-regexp t)
  (setq-local comint-prompt-read-only t) ;rebind C-w to `comint-kill-region'!
  (setq-local mode-line-process nil)
  (setq-local comint-input-filter #'racket-repl--input-filter)
  (add-hook 'comint-output-filter-functions #'racket-repl--output-filter nil t)
  (compilation-setup t)
  (setq-local
   compilation-error-regexp-alist
   '(("^;?[ ]*\\([^ :]+\\):\\([0-9]+\\)[:.]\\([0-9]+\\)" 1 2 3) ;errs, defns
     ("^;?[ ]*at:[ ]+\\([^ :]+\\):\\([0-9]+\\)[.]\\([0-9]+\\)$" 1 2 3) ;contract
     ("#<path:\\([^>]+\\)> \\([0-9]+\\) \\([0-9]+\\)" 1 2 3)   ;rackunit
     ("#<path:\\([^>]+\\)>" 1 nil nil 0)                       ;path struct
     ))
  (setq-local comint-get-old-input #'racket--get-old-input))

(provide 'racket-repl)

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:

;; racket-repl.el ends here
