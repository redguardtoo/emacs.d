;; -*- coding: utf-8; lexical-binding: t; -*-

(defun my-kill-process-buffer-when-exit (process event)
  "Kill buffer of PROCESS when it's terminated.
EVENT is ignored."
  (ignore event)
  (when (memq (process-status process) '(signal exit))
    (kill-buffer (process-buffer process))))

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
    ;; Don't waste time on dumb shell which `shell-write-history-on-exit' is binding to
    (unless (string-match shell-dumb-shell-regexp shell)
      (set-process-sentinel proc #'my-kill-process-buffer-when-exit))))
(add-hook 'shell-mode-hook 'shell-mode-hook-setup)
;; }}

(defun eshell-mode-hook-setup ()
  "Set up `eshell-mode'."
  (local-set-key (kbd "C-c C-y") 'hydra-launcher/body)
  (local-set-key (kbd "M-n") 'counsel-esh-history))
(add-hook 'eshell-mode-hook 'eshell-mode-hook-setup)

;; {{ @see http://emacs-journey.blogspot.com.au/2012/06/improving-ansi-term.html
(advice-add 'term-sentinel :after #'my-kill-process-buffer-when-exit)

;; always use bash
(defvar my-term-program "/bin/bash")

;; utf8
(defun my-term-use-utf8 ()
  (set-buffer-process-coding-system 'utf-8-unix 'utf-8-unix))
(add-hook 'term-exec-hook 'my-term-use-utf8)
;; }}

;; {{ comint-mode
(with-eval-after-load 'comint
  ;; Don't echo passwords when communicating with interactive programs:
  ;; Github prompt is like "Password for 'https://user@github.com/':"
  (setq comint-password-prompt-regexp
        (format "%s\\|^ *Password for .*: *$" comint-password-prompt-regexp))
  (add-hook 'comint-output-filter-functions 'comint-watch-for-password-prompt))
(defun comint-mode-hook-setup ()
  ;; look up shell command history
  (local-set-key (kbd "M-n") 'counsel-shell-history)
  ;; Don't show trailing whitespace in REPL.
  (local-set-key (kbd "M-;") 'comment-dwim))
(add-hook 'comint-mode-hook 'comint-mode-hook-setup)
;; }}

(provide 'init-term-mode)
