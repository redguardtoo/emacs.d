;; -*- coding: utf-8; lexical-binding: t; -*-

(defun my-kill-process-buffer-when-exit (process event)
  "Kill buffer of PROCESS when it's terminated.  EVENT is ignored."
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

;; {{ @see http://emacs-journey.blogspot.com.au/2012/06/improving-ansi-term.html
(advice-add 'term-sentinel :after #'my-kill-process-buffer-when-exit)

;; always use bash
(defvar my-term-program "/bin/bash")
;; }}

(defun my-shell-history ()
  "Browse shell history with current input as initial filter."
  (interactive)
  (let* ((current-input (my-comint-current-input))
         (history-list (ring-elements comint-input-ring))
         ;; use current non-empty input as filter
         (initial-filter (when (and current-input
                                    (not (string= current-input "")))
                           current-input))
         ;; filter history
         (filtered-history (if initial-filter
                               (seq-filter (lambda (cmd)
                                             (string-match-p
                                              (regexp-quote initial-filter)
                                              cmd))
                                           history-list)
                             history-list))
         selected)

    ;; clear current input
    (when current-input
      (my-comint-kill-current-input))

    ;; use completing-read to select
    (setq selected
          (completing-read
           (format "Shell history%s: "
                   (if initial-filter
                       (format " (filter: %s)" initial-filter)
                     ""))
           filtered-history
           nil                    ; predicate
           t                      ; require-match
           nil                    ; initial-input
           'shell-history-ring    ; history variable (built-in)
           (car filtered-history))) ; default value

    ;; insert selected command
    (when (and selected (not (string= selected "")))
      (insert selected))))

;; {{ comint-mode
(with-eval-after-load 'comint
  ;; Don't echo passwords when communicating with interactive programs:
  ;; Github prompt is like "Password for 'https://user@github.com/':"
  (setq comint-password-prompt-regexp
        (format "%s\\|^ *Password for .*: *$" comint-password-prompt-regexp))
  (add-hook 'comint-output-filter-functions 'comint-watch-for-password-prompt))

(defun my-comint-mode-hook-setup ()
  "Set up embedded shells."
  (local-set-key (kbd "C-c C-l") #'eacl-complete-line-from-buffer)
  ;; look up shell command history
  (local-set-key (kbd "M-n") #'my-shell-history)
  ;; Don't show trailing whitespace in REPL.
  (local-set-key (kbd "M-;") #'comment-dwim))
(add-hook 'comint-mode-hook #'my-comint-mode-hook-setup)
;; }}

(provide 'init-term-mode)
