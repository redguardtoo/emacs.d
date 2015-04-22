;;----------------------------------------------------------------------------
;; Restore removed var alias, used by ruby-electric-brace and others
;;----------------------------------------------------------------------------
(unless (boundp 'last-command-char)
  (defvaralias 'last-command-char 'last-command-event))

(provide 'init-compat)
