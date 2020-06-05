;; -*- coding: utf-8; lexical-binding: t; -*-

(defun my-kill-process-buffer-when-exit (proc)
  "Kill buffer of process PROC when it's terminated."
  (when (memq (process-status proc) '(signal exit))
    (kill-buffer (process-buffer proc))))

;; {{ @see https://coredumped.dev/2020/01/04/native-shell-completion-in-emacs/
;; Enable auto-completion in `shell'.
(with-eval-after-load 'shell
  ;; `comint-terminfo-terminal' is invented in Emacs 26
  (unless (and (boundp 'comint-terminfo-terminal)
               comint-terminfo-terminal)
    (setq comint-terminfo-terminal "dumb"))
  (native-complete-setup-bash))

;; `bash-completion-tokenize' can handle garbage output of "complete -p"
(defun my-bash-completion-tokenize-hack (orig-fun &rest args)
  "Original code extracts tokens line by line of output of \"complete -p\"."
  (let* ((beg (nth 0 args))
         (end (nth 1 args)))
    (cond
     ((not (string-match-p "^complete " (buffer-substring beg end)))
      ;; filter out some weird lines
      nil)
     (t
      (apply orig-fun args)))))
(advice-add 'bash-completion-tokenize :around #'my-bash-completion-tokenize-hack)

(defun shell-mode-hook-setup ()
  "Set up `shell-mode'."
  ;; hook `completion-at-point', optional
  (add-hook 'completion-at-point-functions #'native-complete-at-point nil t)
  (setq-local company-backends '((company-files company-native-complete)))
  ;; `company-native-complete' is better than `completion-at-point'
  (local-set-key (kbd "TAB") 'company-complete)
  ;; try to kill buffer when exit shell
  (let* ((proc (get-buffer-process (current-buffer)))
         (shell (file-name-nondirectory (car (process-command proc)))))
    ;; Don't waste time on dumb shell which `shell-write-history-on-exit' is binding
    (unless (string-match shell-dumb-shell-regexp shell)
      (set-process-sentinel proc
                            (lambda (process event)
                              (my-kill-process-buffer-when-exit process))))))
(add-hook 'shell-mode-hook 'shell-mode-hook-setup)
;; }}


(defun eshell-mode-hook-setup ()
  "Set up `eshell-mode'."
  (local-set-key (kbd "C-c C-y") 'hydra-launcher/body)
  (local-set-key (kbd "M-n") 'counsel-esh-history))
(add-hook 'eshell-mode-hook 'eshell-mode-hook-setup)

;; {{ @see http://emacs-journey.blogspot.com.au/2012/06/improving-ansi-term.html
(defun my-term-sentinel-hack (proc)
  (my-kill-process-buffer-when-exit proc))
(advice-add 'term-sentinel :after #'my-term-sentinel-hack)

;; always use bash
(defvar my-term-program "/bin/bash")

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
(with-eval-after-load 'multi-term
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
    (add-to-list 'term-bind-key-alist p)))
;; }}

(provide 'init-term-mode)
