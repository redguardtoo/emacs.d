;; -*- coding: utf-8; lexical-binding: t; -*-

(add-hook 'after-init-hook 'global-company-mode)

(when (fboundp 'evil-declare-change-repeat)
  (mapc #'evil-declare-change-repeat
        '(company-complete-common
          company-select-next
          company-select-previous
          company-complete-selection
          company-complete-number)))

(eval-after-load 'company
  '(progn
     ;; @see https://github.com/company-mode/company-mode/issues/348
     (company-statistics-mode)
     (push 'company-cmake company-backends)
     (push 'company-c-headers company-backends)
     ;; can't work with TRAMP
     (setq company-backends (delete 'company-ropemacs company-backends))

     ;; company-ctags is faster than company-etags
     (require 'company-ctags)
     (company-ctags-auto-setup)

     ;; (setq company-backends (delete 'company-capf company-backends))

     ;; I don't like the downcase word in company-dabbrev!
     (setq company-dabbrev-downcase nil
           ;; make previous/next selection in the popup cycles
           company-selection-wrap-around t
           ;; Some languages use camel case naming convention,
           ;; so company should be case sensitive.
           company-dabbrev-ignore-case nil
           ;; press M-number to choose candidate
           company-show-numbers t
           company-idle-delay 0.2
           company-clang-insert-arguments nil
           company-require-match nil
           company-etags-ignore-case t
           ;; @see https://github.com/company-mode/company-mode/issues/146
           company-tooltip-align-annotations t)

     ;; @see https://github.com/redguardtoo/emacs.d/commit/2ff305c1ddd7faff6dc9fa0869e39f1e9ed1182d
     (defadvice company-in-string-or-comment (around company-in-string-or-comment-hack activate)
       ;; you can use (ad-get-arg 0) and (ad-set-arg 0) to tweak the arguments
       (if (memq major-mode '(php-mode html-mode web-mode nxml-mode))
           (setq ad-return-value nil)
         ad-do-it))

     ;; press SPACE will accept the highlighted candidate and insert a space
     ;; `M-x describe-variable company-auto-complete-chars` for details
     ;; That's BAD idea.
     (setq company-auto-complete nil)

     ;; NOT to load company-mode for certain major modes.
     ;; Ironic that I suggested this feature but I totally forgot it
     ;; until two years later.
     ;; https://github.com/company-mode/company-mode/issues/29
     (setq company-global-modes
           '(not
             eshell-mode comint-mode erc-mode gud-mode rcirc-mode
             minibuffer-inactive-mode))))

(eval-after-load 'company-ispell
  '(progn
     ;; use company-ispell in comment and string when programming
     (defadvice company-ispell-available (around company-ispell-available-hack activate)
       (cond
        ((and (derived-mode-p 'prog-mode)
              (not (company-in-string-or-comment)))
         (setq ad-return-value nil))
        (t
         ad-do-it)))))


(defun my-add-ispell-to-company-backends ()
  "Add ispell to the last of `company-backends'."
  (setq company-backends
        (add-to-list 'company-backends 'company-ispell)))

;; {{ setup company-ispell
(defun toggle-company-ispell ()
  "Toggle company-ispell."
  (interactive)
  (cond
   ((memq 'company-ispell company-backends)
    (setq company-backends (delete 'company-ispell company-backends))
    (message "company-ispell disabled"))
   (t
    (my-add-ispell-to-company-backends)
    (message "company-ispell enabled!"))))

(defun company-ispell-setup ()
  ;; @see https://github.com/company-mode/company-mode/issues/50
  (when (boundp 'company-backends)
    (make-local-variable 'company-backends)
    (my-add-ispell-to-company-backends)
    ;; @see https://github.com/redguardtoo/emacs.d/issues/473
    (cond
     ((and (boundp 'ispell-alternate-dictionary)
           ispell-alternate-dictionary)
      (setq company-ispell-dictionary ispell-alternate-dictionary))
     (t
       (setq company-ispell-dictionary (file-truename "~/.emacs.d/misc/english-words.txt"))))))

;; message-mode use company-bbdb.
;; So we should NOT turn on company-ispell
(add-hook 'org-mode-hook 'company-ispell-setup)
;; }}

;; Wait 30  minutes to update cache from tags file
;; assume `company-dabbrev-code' or `company-dabbrev' in the same group provides candidates
;; @see https://github.com/company-mode/company-mode/pull/877 for tech details
;; The purpose is to avoid rebuilding candidate too frequently because rebuilding could take
;; too much time.
(defvar company-etags-update-interval 1800
  "The interval (seconds) to update candidate cache.
Function `tags-completion-table' sets up variable `tags-completion-table'
by parsing tags files.
The interval stops the function being called too frequently.")

(defvar company-etags-timer nil
  "Timer to avoid calling function `tags-completion-table' too frequently.")

(provide 'init-company)
