;; -*- coding: utf-8; lexical-binding: t; -*-

(when (boundp 'evil-mode)
  (general-imap ","
    (general-key-dispatch 'self-insert-command
      :timeout 0.5
      "/" 'my-toggle-input-method)))

(provide 'init-no-byte-compile)
;;; init-no-byte-compile.el ends here

;; Local Variables:
;; no-byte-compile: t
;; End:
