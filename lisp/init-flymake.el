;; -*- coding: utf-8; lexical-binding: t; -*-
(local-require 'lazyflymake)

(with-eval-after-load 'flymake
  (setq flymake-gui-warnings-enabled nil))

(add-hook 'prog-mode-hook #'lazyflymake-start)

(provide 'init-flymake)
