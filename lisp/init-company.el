;; -*- coding: utf-8; lexical-binding: t; -*-

(add-hook 'after-init-hook 'global-company-mode)

;; evil has already integrated company-mode, see evil-integration.el

(defvar my-company-select-by-number-p t
  "User can press number key to select company candidate.")

(defvar my-company-zero-key-for-filter nil
  "If t, pressing 0 calls `company-filter-candidates' per company's status.
If `my-company-select-by-number-p' is nil, this flag is ignored. ")

(with-eval-after-load 'company

  ;; company changed the default key bindings, un-comment below code to restore original key bindings
  ;; @see https://github.com/company-mode/company-mode/wiki/Tips-%26-tricks/_compare/5ea840d^...5ea840d

  ;; (define-key company-active-map (kbd "C-n") nil)
  ;; (define-key company-active-map (kbd "C-p") nil)
  ;; (define-key company-active-map (kbd "M-n") #'company-select-next)
  ;; (define-key company-active-map (kbd "M-p") #'company-select-previous)

  (defun my-company-number ()
    "Forward to `company-complete-number'.
Unless the number is potentially part of the candidate.
In that case, insert the number."
    (interactive)
    (let* ((k (this-command-keys))
           (re (concat "^" company-prefix k))
           (n (if (equal k "0") 10 (string-to-number k))))
      (cond
       ((or (cl-find-if (lambda (s) (string-match re s)) company-candidates)
            (> n (length company-candidates))
            (looking-back "[0-9]" (line-beginning-position)))
        (self-insert-command 1))

       ((and (eq n 10) my-company-zero-key-for-filter)
        (company-filter-candidates))

       (t
        (company-complete-number n)))))
  (with-eval-after-load 'evil
    (mapc #'evil-declare-change-repeat
          '(my-company-number)))

  ;; @see https://github.com/company-mode/company-mode/issues/348
  (company-statistics-mode)
  (push 'company-cmake company-backends)
  (push 'company-c-headers company-backends)
  ;; can't work with TRAMP
  (setq company-backends (delete 'company-ropemacs company-backends))

  ;; @see https://oremacs.com/2017/12/27/company-numbers/
  ;; Using digits to select company-mode candidates
  (when my-company-select-by-number-p
    (let ((map company-active-map))
      (mapc
       (lambda (x)
         (define-key map (format "%d" x) 'my-company-number))
       (number-sequence 0 9))))

  (setq company-auto-commit t)
  ;; characters "/ ) . , ;"to trigger auto commit
  (setq company-auto-commit-chars '(92  41 46 44 59))

  ;; company-ctags is much faster out of box. No further optimiation needed
  (unless (featurep 'company-ctags) (local-require 'company-ctags))
  (company-ctags-auto-setup)

  ;; (setq company-backends (delete 'company-capf company-backends))

  ;; I don't like the downcase word in company-dabbrev
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
        company-ctags-ignore-case t ; I use company-ctags instead
        ;; @see https://github.com/company-mode/company-mode/issues/146
        company-tooltip-align-annotations t)

  ;; Press SPACE will accept the highlighted candidate and insert a space
  ;; "M-x describe-variable company-auto-complete-chars" for details.
  ;; So that's BAD idea.
  (setq company-auto-complete nil)

  ;; NOT to load company-mode for certain major modes.
  ;; Ironic that I suggested this feature but I totally forgot it
  ;; until two years later.
  ;; https://github.com/company-mode/company-mode/issues/29
  (setq company-global-modes
        '(not
          eshell-mode
          comint-mode
          erc-mode
          gud-mode
          rcirc-mode
          minibuffer-inactive-mode)))

(defun my-company-ispell-available-hack (orig-func &rest args)
    ;; in case evil is disabled
    (my-ensure 'evil-nerd-commenter)
    (cond
     ((and (derived-mode-p 'prog-mode)
           (or (not (company-in-string-or-comment)) ; respect advice in `company-in-string-or-comment'
               ;; I renamed the api in new version of evil-nerd-commenter
               (not  (evilnc-pure-comment-p (point))))) ; auto-complete in comment only
      ;; only use company-ispell in comment when coding
      nil)
     (t
      (apply orig-func args))))
(with-eval-after-load 'company-ispell
  (advice-add 'company-ispell-available :around #'my-company-ispell-available-hack))

(with-eval-after-load 'ispell
  ;; `ispell-alternate-dictionary' is a plain text dictionary if it exists
  (let* ((dict (concat my-emacs-d "misc/english-words.txt")))
    (when (and (null ispell-alternate-dictionary)
               (file-exists-p dict))
      ;; @see https://github.com/redguardtoo/emacs.d/issues/977
      ;; fallback to built in dictionary
      (setq ispell-alternate-dictionary dict))))

;; {{ setup company-ispell
(defun toggle-company-ispell ()
  "Toggle company ispell backend."
  (interactive)
  (cond
   ((memq 'company-ispell company-backends)
    (setq company-backends (delete 'company-ispell company-backends))
    (message "company-ispell disabled"))
   (t
    (push 'company-ispell company-backends)
    (message "company-ispell enabled!"))))

(with-eval-after-load 'ispell
  ;; "look" is not reliable, use "grep" instead.
  ;; For example, Linux CLI "/usr/bin/look -df Monday /usr/share/dict/words"
  ;; returns nothing on my Debian Linux testing version.
  (setq ispell-look-p nil))

(defun my-company-ispell-setup ()
  ;; @see https://github.com/company-mode/company-mode/issues/50
  (when (boundp 'company-backends)
    (make-local-variable 'company-backends)
    (push 'company-ispell company-backends)

    (cond
     ;; @see https://github.com/redguardtoo/emacs.d/issues/473
     ;; Windows users never load ispell module
     ((and (boundp 'ispell-alternate-dictionary)
           ispell-alternate-dictionary)
      (setq company-ispell-dictionary ispell-alternate-dictionary))

     (t
      (setq company-ispell-dictionary
            (concat my-emacs-d "misc/english-words.txt"))))))

;; message-mode use company-bbdb.
;; So we should NOT turn on company-ispell
(add-hook 'org-mode-hook 'my-company-ispell-setup)
;; }}

(provide 'init-company)
