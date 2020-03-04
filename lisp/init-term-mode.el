;; -*- coding: utf-8; lexical-binding: t; -*-

(defun my-kill-process-buffer-when-exit (proc)
  "Kill buffer of process PROC when it's terminated."
  (when (memq (process-status proc) '(signal exit))
    (kill-buffer (process-buffer proc))))

;; {{ @see https://coredumped.dev/2020/01/04/native-shell-completion-in-emacs/
;; enable auto-completion in `shell'.
;; Since we already got a dropdown for auto-completion, so don't bother with
;; `company-mode' backend set up
(eval-after-load 'shell
  '(progn
     (setq explicit-bash-args
           (delete "--noediting" explicit-bash-args))))

(advice-add 'comint-term-environment
            :filter-return (lambda (env) (cons "INSIDE_EMACS" env)))


(defun my-exit-shell-process (process event)
  "Called when the shell PROCESS is stopped.  EVENT is ignored."
  (my-kill-process-buffer-when-exit process))

(defun shell-mode-hook-setup ()
  "Set up `shell-mode'."
  ;; try to kill buffer when exit shell
  (let* ((proc (get-buffer-process (current-buffer)))
         (shell (file-name-nondirectory (car (process-command proc)))))
    ;; Don't waste time on dumb shell which `shell-write-history-on-exit' is binding
    (unless (string-match shell-dumb-shell-regexp shell)
      (set-process-sentinel proc #'my-exit-shell-process)))

  ;; look up shell command history
  (local-set-key (kbd "M-n") 'counsel-shell-history))
(add-hook 'shell-mode-hook 'shell-mode-hook-setup)
;; }}

;; {{ @see http://emacs-journey.blogspot.com.au/2012/06/improving-ansi-term.html
(defadvice term-sentinel (after term-sentinel-after-hack activate)
  (my-kill-process-buffer-when-exit (nth 0 (ad-get-args 0))))

;; always use bash
(defvar my-term-program "/bin/bash")
(defadvice ansi-term (before force-bash)
  (interactive (list my-term-program)))
(ad-activate 'ansi-term)

;; utf8
(defun my-term-use-utf8 ()
  (set-buffer-process-coding-system 'utf-8-unix 'utf-8-unix))
(add-hook 'term-exec-hook 'my-term-use-utf8)
;; }}

;; {{ multi-term
(defun last-term-buffer (l)
  "Return most recently used term buffer."
  (when l
    (if (eq 'term-mode (with-current-buffer (car l) major-mode))
        (car l) (last-term-buffer (cdr l)))))

(defun get-term ()
  "Switch to the term buffer last used, or create a new one if
    none exists, or if the current buffer is already a term."
  (interactive)
  (let* ((b (last-term-buffer (buffer-list))))
    (if (or (not b) (eq 'term-mode major-mode))
        (multi-term)
      (switch-to-buffer b))))

(defun term-send-kill-whole-line ()
  "Kill whole line in term mode."
  (interactive)
  (term-send-raw-string "\C-a")
  (term-send-raw-string "\C-k"))

(defun term-send-kill-line ()
  "Kill line in term mode."
  (interactive)
  (term-send-raw-string "\C-k"))

(setq multi-term-program my-term-program)
;; check `term-bind-key-alist' for key bindings
(eval-after-load 'multi-term
  '(progn
     (dolist (p '(("C-p" . term-send-up)
                  ("C-n" . term-send-down)
                  ("C-s" . swiper)
                  ("C-r" . term-send-reverse-search-history)
                  ("C-m" . term-send-raw)
                  ("C-k" . term-send-kill-whole-line)
                  ("C-y" . yank)
                  ("C-_" . term-send-raw)
                  ("M-f" . term-send-forward-word)
                  ("M-b" . term-send-backward-word)
                  ("M-K" . term-send-kill-line)
                  ("M-p" . previous-line)
                  ("M-n" . next-line)
                  ("M-y" . yank-pop)
                  ("M-." . term-send-raw-meta)))
       (setq term-bind-key-alist (delq (assoc (car p) term-bind-key-alist) term-bind-key-alist))
       (add-to-list 'term-bind-key-alist p))))
;; }}

(provide 'init-term-mode)
