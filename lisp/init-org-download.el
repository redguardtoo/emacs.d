;; @see https://github.com/abo-abo/org-download

(push 'org-download melpa-include-packages)
(require-package 'org-download)
(require 'org-download)

(setq org-download-method 'attach)

(provide 'init-org-download)
