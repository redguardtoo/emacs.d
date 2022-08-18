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

;; Linux Only
;;(setq counsel-etags-extra-tags-files '("/usr/include/TAGS"))

;; org mode
(global-set-key (kbd "C-c a") 'org-agenda)
(global-set-key (kbd "C-c C-r") 'org-store-link)
(setq vc-follow-symlinks nil)
(setq org-agenda-files  '("~/GTD"))
(setq org-M-RET-may-split-line nil)

;; theme
(load-theme 'twilight-bright t)

(setq cmake-tab-width 4)
(setq find-file-visit-truename nil)
;;(setq find-file-existing-other-name t)

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
  (unless (my-buffer-file-temp-p)
	(add-hook 'after-save-hook 'counsel-etags-virtual-update-tags 'append 'local)))
(add-hook 'prog-mode-hook 'my-setup-develop-environment)

(require-package 'jenkinsfile-mode)

;; setup plantuml
;;(require-package 'plantuml-mode)
;;(setq org-plantuml-jar-path (expand-file-name "~/plantuml.jar"))
;;;;(add-to-list 'org-src-lang-modes '("plantuml" . plantuml))
;;(org-babel-do-load-languages 'org-babel-load-languages '((plantuml . t)))

;; setup plantuml napkin
;; (with-eval-after-load 'ob
;;   ;; Optional for syntax highlight of napkin-puml src block.
;;   ;; (require 'plantuml)
;;   (require 'ob-napkin))

(require-package 'powershell)
