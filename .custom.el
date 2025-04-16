;; add unstable pakcages to list if want to install unstable packages and can not find the pakcage in package list
(add-to-list 'melpa-include-packages 'clang-format)

(require-package 'go-mode)
(add-hook 'c-mode-common-hook
          (lambda ()
            (c-set-offset 'case-label '+)))

;; Clang stuff
(require-package 'clang-format)
(setq clang-format-style "file")

;; Mac Only
(defvar my-term-program "/bin/zsh")

(require-package 'unicad)

;; Linux Only
;;(setq counsel-etags-extra-tags-files '("/usr/include/TAGS"))

;; customize mode line
(require-package 'keycast)
(setq keycast-insert-after "   ")
(setq-default my-extra-mode-line-info '("" mode-line-keycast))
(customize-set-variable 'keycast-mode t)

;;(desktop-save-mode)
;;(setq desktop-path '("~/emacs-auto-save"))

;; indent
(setq-default c-basic-offset 4)

;; org mode
(global-set-key (kbd "C-c a") 'org-agenda)
(global-set-key (kbd "C-c C-r") 'org-store-link)
(setq vc-follow-symlinks nil)
(setq org-agenda-files  '("~/GTD"))
(setq org-M-RET-may-split-line nil)
(setq org-image-actual-width 300)

(require-package 'org-bullets)
;; (setq org-hide-emphasis-markers t
;;       org-fontify-done-headline t
;;       org-hide-leading-stars t
;;       org-pretty-entities t
;;       org-odd-levels-only t)
;; (setq org-bullets-bullet-list '( "⦿" "○" "✸" "✿" "◆"))
;; (add-hook 'org-mode-hook (lambda () (org-bullets-mode 1)))
(when (member "Symbola" (font-family-list))
  (set-fontset-font "fontset-default" nil
                    (font-spec :size 20 :name "Symbola")))

(when (member "Symbola" (font-family-list))
  (set-fontset-font t 'unicode "Symbola" nil 'prepend))

(prefer-coding-system       'utf-8)
(set-default-coding-systems 'utf-8)
(set-terminal-coding-system 'utf-8)
(set-keyboard-coding-system 'utf-8)
(setq default-buffer-file-coding-system 'utf-8)

(setq org-bullets-bullet-list '("◉" "☯" "○" "☯" "✸" "☯" "✿" "☯" "✜" "☯" "◆" "☯" "▶"))
(setq org-ellipsis "▼")

(setq org-startup-indented t
      org-src-tab-acts-natively t)

(add-hook 'org-mode-hook (lambda () (org-bullets-mode 1)))
;; (add-hook 'org-mode-hook (lambda ()
;;                            (variable-pitch-mode 1)
;;                            visual-line-mode))

;; (setq org-hide-emphasis-markers t)
(defun org-toggle-emphasis ()
  "Toggle hiding/showing of org emphasize markers."
  (interactive)
  (if org-hide-emphasis-markers
      (set-variable 'org-hide-emphasis-markers nil)
    (set-variable 'org-hide-emphasis-markers t)))
(with-eval-after-load "org-bullets"
		      (define-key org-mode-map (kbd "C-c e") 'org-toggle-emphasis))

(setq org-fontify-done-headline t)
(setq org-hide-leading-stars t)
;; (setq org-pretty-entities t)
;; (setq org-odd-levels-only t)

(setq org-list-demote-modify-bullet
      (quote (("+" . "-")
              ("-" . "+")
              ("*" . "-")
              ("1." . "-")
              ("1)" . "-")
              ("A)" . "-")
              ("B)" . "-")
              ("a)" . "-")
              ("b)" . "-")
              ("A." . "-")
              ("B." . "-")
              ("a." . "-")
              ("b." . "-"))))

(font-lock-add-keywords 'org-mode
                        '(("^ *\\([-]\\) "
                           (0 (prog1 () (compose-region (match-beginning 1) (match-end 1) "•"))))))
(font-lock-add-keywords 'org-mode
                        '(("^ *\\([+]\\) "
                           (0 (prog1 () (compose-region (match-beginning 1) (match-end 1) "◦"))))))


;; org roam
(require-package 'org-roam)
(setq org-roam-directory (file-truename "~/notes"))
(org-roam-db-autosync-mode)
(setq org-roam-v2-ack t)
(setq org-roam-complete-everywhere t)

(global-set-key (kbd "C-c n l") 'org-roam-buffer-toggle)
(global-set-key (kbd "C-c n f") 'org-roam-node-find)
(global-set-key (kbd "C-c n i") 'org-roam-node-insert)

(setq org-roam-capture-templates
      '(("m" "main" plain
         "%?"
         :if-new (file+head "main/%<%Y%m%d%H%M%S>-${slug}.org"
                            "#+title: ${title}\n")
         :immediate-finish t
         :unnarrowed t)
        ("r" "reference" plain "%?"
         :if-new
         (file+head "reference/%<%Y%m%d%H%M%S>-${slug}.org" "#+title: ${title}\n")
         :immediate-finish t
         :unnarrowed t)
        ("b" "taiji reference" plain
         "%?"
         :if-new
         (file+head "reference/%<%Y%m%d%H%M%S>-${slug}.org" "#+title: ${title}\n#+filetags: 太极\n* 原文\n\n\n* 个人理解\n\n\n* 来源\n\n")
         :immediate-finish t
         :unnarrowed t)
        ("t" "taiji" plain "%?"
         :if-new
         (file+head "main/%<%Y%m%d%H%M%S>-${slug}.org" "#+title: ${title}\n#+filetags: 太极")
         :immediate-finish t
         :unnarrowed t)
        ("q" "雀魂 reference" plain
         "%?"
         :if-new
         (file+head "reference/%<%Y%m%d%H%M%S>-${slug}.org" "#+title: ${title}\n#+filetags: 雀魂\n* 原文\n\n\n* 个人理解\n\n\n* 来源\n\n")
         :immediate-finish t
         :unnarrowed t)
        ("a" "article" plain "%?"
         :if-new
         (file+head "articles/%<%Y%m%d%H%M%S>-${slug}.org" "#+title: ${title}\n#+filetags: :article:\n")
         :immediate-finish t
         :unnarrowed t)))

(setq org-capture-templates
      '(("s" "Slipbox" entry  (file "~/notes/inbox.org")
         "* %?\n")
        ("t" "Todo" entry (file+headline "~/gtd.org" "Tasks")
         "* TODO %?\n  %i\n  %a")))

(defun qucheng/org-capture-slipbox()
  (interactive)
  (org-capture nil "s"))

(defun qucheng/org-capture-todo()
  (interactive)
  (org-capture nil "t"))

(cl-defmethod org-roam-node-type ((node org-roam-node))
  "Return the TYPE of NODE."
  (condition-case nil
      (file-name-nondirectory
       (directory-file-name
        (file-name-directory
         (file-relative-name (org-roam-node-file node) org-roam-directory))))
    (error "")))

(setq org-roam-node-display-template
      (concat "${type:15} ${title:*} " (propertize "${tags:10}" 'face 'org-tag)))


;; theme
(load-theme 'twilight-bright t)

(setq cmake-tab-width 4)
(setq find-file-visit-truename nil)
;;(setq find-file-existing-other-name t)

(defun my-setup-indent (n)
  ;; java/c/c++
  (setq-local c-basic-offset n)
  ;; web development
  (setq-local coffee-tab-width n) ; coffeescript
  (setq-local javascript-indent-level n) ; javascript-mode
  (setq-local js-indent-level n) ; js-mode
  (setq-local js2-basic-offset n) ; js2-mode, in latest js2-mode, it's alias of js-indent-level
  (setq-local web-mode-markup-indent-offset n) ; web-mode, html tag in html file
  (setq-local web-mode-css-indent-offset n) ; web-mode, css in html file
  (setq-local web-mode-code-indent-offset n) ; web-mode, js code in html file
  (setq-local css-indent-offset n) ; css-mode
  )

;; Don't ask before rereading the TAGS files if they have changed
(setq tags-revert-without-query t)
;; Don't warn when TAGS files are large
(setq large-file-warning-threshold nil)
;; Setup auto update now
(add-hook 'prog-mode-hook
  (lambda ()
    (add-hook 'after-save-hook
              'counsel-etags-virtual-update-tags 'append 'local)))


;; auto update tags
(local-require 'counsel-etags)
(defun my-setup-develop-environment ()
  "Set up my develop environment."
  (interactive)
  (setq indent-tabs-mode nil)
  (my-setup-indent 4)
  (unless (my-buffer-file-temp-p)
	(add-hook 'after-save-hook 'counsel-etags-virtual-update-tags 'append 'local)))
(add-hook 'prog-mode-hook 'my-setup-develop-environment)
(add-hook 'c-mode-hook 'my-setup-develop-environment)
(add-hook 'c++-mode-hook 'my-setup-develop-environment)

(require-package 'jenkinsfile-mode)


;; setup plantuml and mermaid
;; (require-package 'plantuml-mode)
;; (add-to-list 'org-src-lang-modes '("plantuml" . plantuml))
(setq org-plantuml-jar-path (expand-file-name "~/plantuml.jar"))
(require-package 'ob-mermaid)
(setq ob-mermaid-cli-path (expand-file-name "~/node_modules/.bin/mmdc"))
(org-babel-do-load-languages 'org-babel-load-languages '((plantuml . t)
                                                         (mermaid . t)
                                                         (scheme . t)))

;; setup plantuml napkin
;; (with-eval-after-load 'ob
;;   ;; Optional for syntax highlight of napkin-puml src block.
;;   ;; (require 'plantuml)
;;   (require 'ob-napkin))

(require-package 'powershell)

;; setup lsp-mode
(with-eval-after-load 'lsp-mode
  ;; enable log only for debug
  (setq lsp-log-io nil)
  ;; use `evil-matchit' instead
  (setq lsp-enable-folding nil)
  ;; no real time syntax check
  (setq lsp-diagnostic-package :none)
  ;; handle yasnippet by myself
  (setq lsp-enable-snippet nil)
  ;; turn off for better performance
  (setq lsp-enable-symbol-highlighting nil)
  ;; use find-fine-in-project instead
  (setq lsp-enable-links nil)
  ;; auto restart lsp
  (setq lsp-restart 'auto-restart)
  ;; don't watch 3rd party javascript libraries
  (push "[/\\\\][^/\\\\]*\\.\\(json\\|html\\|jade\\)$" lsp-file-watch-ignored)
  ;; don't ping LSP language server too frequently
  (defvar lsp-on-touch-time 0)
  (defun my-lsp-on-change-hack (orig-fun &rest args)
    ;; do NOT run `lsp-on-change' too frequently
    (when (> (- (float-time (current-time))
                lsp-on-touch-time) 120) ;; 2 mins
      (setq lsp-on-touch-time (float-time (current-time)))
      (apply orig-fun args)))
  (advice-add 'lsp-on-change :around #'my-lsp-on-change-hack))

;; jsx tsx mode support
(require-package 'jtsx)
(add-to-list 'auto-mode-alist '("\\.tsx\\'" . jtsx-tsx-mode))