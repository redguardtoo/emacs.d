(require-package 'use-package)
(require 'package)
(package-initialize)
(unless (package-installed-p 'use-package)
  (package-refresh-contents)
  (package-install 'use-package))
(eval-and-compile
  (setq use-package-always-ensure t
        use-package-expand-minimally t))
(require-package 'emacsql)
(require-package 'emacsql-sqlite)
(require-package 'org-roam)

(with-eval-after-load 'emacsql)
(with-eval-after-load 'emacsql-sqlite)
(setq org-roam-directory (file-truename "~/notes"))
(setq org-roam-complete-everywhere t)

(use-package org-roam
  ;; :after org
  :ensure t
  :custom
  (org-roam-directory (file-truename "~/notes"))
  (setq org-roam-v2-ack t)
  ;; (org-roam-database-connector 'sqlite-builtin)
  ;; '(define-key map (kbd "C-c n l") 'org-roam-buffer-toggle)
  ;; :config
  ;; If you're using a vertical completion framework, you might want a more informative completion interface
  (setq org-roam-node-display-template (concat "${title:*} " (propertize "${tags:10}" 'face 'org-tag)))
  (org-roam-db-autosync-mode)
  ;; If using org-roam-protocol
  (require 'org-roam-protocol)
  (org-roam-setup)
  :bind (("C-c n l" . org-roam-buffer-toggle)
         ("C-c n f" . org-roam-node-find)
         ("C-c n g" . org-roam-graph)
         ("C-c n i" . org-roam-node-insert)
         ("C-c n c" . org-roam-capture)
         ;; Dailies
         ("C-c n j" . org-roam-dailies-capture-today))
  )
