;; -*- coding: utf-8; lexical-binding: t; -*-

(with-eval-after-load 'exec-path-from-shell
  (dolist (var '("SSH_AUTH_SOCK" "SSH_AGENT_PID" "GPG_AGENT_INFO"))
    (add-to-list 'exec-path-from-shell-variables var)))

(when (and window-system
           (memq window-system '(mac ns)))
  (exec-path-from-shell-initialize))

(provide 'init-exec-path)
