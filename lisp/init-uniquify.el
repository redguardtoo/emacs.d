;; -*- coding: utf-8; lexical-binding: t; -*-

;; Nicer naming of buffers for files with identical names
(setq uniquify-buffer-name-style 'reverse)
(setq uniquify-separator " • ")
(setq uniquify-after-kill-buffer-p t)
(setq uniquify-ignore-buffers-re "^\\*")

(provide 'init-uniquify)