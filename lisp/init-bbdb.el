;; -*- coding: utf-8; lexical-binding: t; -*-

(defun message-mode-hook-setup ()
  (bbdb-initialize 'message)
  (bbdb-initialize 'gnus)
  (local-set-key (kbd "TAB") 'bbdb-complete-name))
(add-hook 'message-mode-hook 'message-mode-hook-setup)

;; import Gmail contacts in vcard format into bbdb
(setq gmail2bbdb-bbdb-file "~/.bbdb")

(with-eval-after-load 'gmail2bbdb
  (setq gmail2bbdb-exclude-people-without-name t))

(provide 'init-bbdb)
