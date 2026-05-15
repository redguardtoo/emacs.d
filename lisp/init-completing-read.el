;;; -*- lexical-binding: t -*-

(use-package vertico
  :ensure t
  :init
  (vertico-mode 1)

  :bind
  (:map vertico-map
        ("C-j" . vertico-next)           ;; next candidate
        ("C-k" . vertico-previous)       ;; previous candidate
        ("C-l" . vertico-insert)         ;; insert candidate
        ("C-M-j" . vertico-next-group)   ;; next group
        ("C-M-k" . vertico-previous-group) ;; previous group
        ("C-c C-r" . vertico-repeat)         ;; resume last session
        ("C-c C-s" . vertico-repeat-select)  ;; select from session history
        ;; navigate within same command's session history
        ("C-c C-p" . vertico-repeat-previous)
        ("C-c C-n" . vertico-repeat-next))

  :config
  (add-hook 'minibuffer-setup-hook #'vertico-repeat-save)
  (setq vertico-cycle t))
(global-set-key (kbd "C-c C-a") #'vertico-suspend)

(use-package savehist
  :init
  (savehist-mode))

(use-package orderless
  :ensure t
  :custom
  (completion-styles '(orderless basic))
  (completion-category-defaults nil)
  (completion-category-overrides '((file (styles partial-completion)))))

(use-package consult
  :ensure t
  :bind (("C-s" . consult-line)
         ;; outline
         ("M-g o" . consult-outline))
  :custom
  ;; disable live preview
  (consult-preview-key nil)
  ;; use "<" to narrow
  (consult-narrow-key "<"))

(use-package embark
  :ensure t
  :bind
  ("C-." . embark-act)         ;; M-o equivalent
  ("C-;" . embark-dwim)
  ("C-c C-o" . embark-export)
  ("C-h b" . embark-bindings)
  :config
  (require 'embark-consult)
  ;; press C-c C-p to edit in wgrep buffer
  (setf (alist-get 'fastctags-grep embark-exporters-alist) 'embark-consult-export-grep))

(setq completions-format 'one-column)
(setq completion-auto-help 'visible)
(setq completions-max-height 20)
(setq completions-detailed t)

(provide 'init-completing-read)
;;; init-completing-read.el ends here
