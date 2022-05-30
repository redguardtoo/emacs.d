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
  (unless comint-terminfo-terminal (setq comint-terminfo-terminal "dumb"))
  (native-complete-setup-bash))

;; `bash-completion-tokenize' can handle garbage output of "complete -p"
(defun my-bash-completion-tokenize-hack (orig-fun &rest args)
  "Original code extracts tokens line by line of output of \"complete -p\"."
  (let* ((beg (nth 0 args))
         (end (nth 1 args)))
    (cond
     ((not (string-match "^complete " (buffer-substring beg end)))
      ;; filter out some weird lines
      nil)
     (t
      (apply orig-fun args)))))
(advice-add 'bash-completion-tokenize :around #'my-bash-completion-tokenize-hack)

(defun shell-mode-hook-setup ()
  "Set up `shell-mode'."

  ;; analyze error output in shell
  (shellcop-start)

  (setq shellcop-sub-window-has-error-function
        (lambda ()
          (and (eq major-mode 'js2-mode)
               (> (length (js2-errors)) 0))))

  ;; hook `completion-at-point', optional
  (add-hook 'completion-at-point-functions #'native-complete-at-point nil t)
  (setq-local company-backends '((company-files company-native-complete)))
  ;; `company-native-complete' is better than `completion-at-point'
  (local-set-key (kbd "TAB") 'company-complete)

  ;; @see https://github.com/redguardtoo/emacs.d/issues/882
  (setq-local company-idle-delay 1)

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
  (local-set-key (kbd "C-c C-y") 'my-hydra-launcher/body)
  (local-set-key (kbd "M-n") 'counsel-esh-history))
(add-hook 'eshell-mode-hook 'eshell-mode-hook-setup)

;; {{ @see http://emacs-journey.blogspot.com.au/2012/06/improving-ansi-term.html
(advice-add 'term-sentinel :after #'my-kill-process-buffer-when-exit)

;; always use bash
(defvar my-term-program "/bin/bash")
;; }}

;; {{ hack counsel-browser-history
(defvar my-comint-full-input nil)
(defun my-counsel-shell-history-hack (orig-func &rest args)
  (setq my-comint-full-input (my-comint-current-input))
  (my-comint-kill-current-input)
  (apply orig-func args)
  (setq my-comint-full-input nil))
(advice-add 'counsel-shell-history :around #'my-counsel-shell-history-hack)
(defun my-ivy-history-contents-hack (orig-func &rest args)
  "Make sure `ivy-history-contents' returns items matching `my-comint-full-input'."
  (let* ((rlt (apply orig-func args))
         (input my-comint-full-input))
    (when (and input (not (string= input "")))
      ;; filter shell history with current input
      (setq rlt
            (delq nil (mapcar
                       `(lambda (item)
                          (let* ((cli (if (stringp item) item (car item))))
                            (and (string-match (regexp-quote ,input) cli) item)))
                       rlt))))
    rlt))
(advice-add 'ivy-history-contents :around #'my-ivy-history-contents-hack)
;; }}

;; {{ comint-mode
(with-eval-after-load 'comint
  ;; Don't echo passwords when communicating with interactive programs:
  ;; Github prompt is like "Password for 'https://user@github.com/':"
  (setq comint-password-prompt-regexp
        (format "%s\\|^ *Password for .*: *$" comint-password-prompt-regexp))
  (add-hook 'comint-output-filter-functions 'comint-watch-for-password-prompt))

(defun my-comint-mode-hook-setup ()
  "Set up embedded shells."
  (local-set-key (kbd "C-c C-l") 'eacl-complete-line-from-buffer)
  ;; look up shell command history
  (local-set-key (kbd "M-n") 'counsel-shell-history)
  ;; Don't show trailing whitespace in REPL.
  (local-set-key (kbd "M-;") 'comment-dwim))
(add-hook 'comint-mode-hook 'my-comint-mode-hook-setup)
;; }}

(provide 'init-term-mode)
