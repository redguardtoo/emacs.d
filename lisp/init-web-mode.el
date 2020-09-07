;; -*- coding: utf-8; lexical-binding: t; -*-

;; See `flymake-xml-program' for html flymake check
;; No extra setup is required.

(defun web-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (setq-local wucuo-flyspell-check-doublon nil)
    (remove-hook 'yas-after-exit-snippet-hook
                 'web-mode-yasnippet-exit-hook t)
    (remove-hook 'yas/after-exit-snippet-hook
                 'web-mode-yasnippet-exit-hook t)))

(add-hook 'web-mode-hook 'web-mode-hook-setup)

(with-eval-after-load 'web-mode
  ;; make org-mode export fail, I use evil and evil-matchit
  ;; to select text, so expand-region.el is not used
  (remove-hook 'web-mode-hook 'er/add-web-mode-expansions)
  (setq web-mode-enable-auto-closing t) ; enable auto close tag in text-mode
  (setq web-mode-enable-auto-pairing t)
  (setq web-mode-enable-css-colorization t)
  (setq web-mode-imenu-regexp-list
        '(("<\\(h[1-9]\\)\\([^>]*\\)>\\([^<]*\\)" 1 3 ">" nil)
          ("^[ \t]*<\\([@a-z]+\\)[^>]*>? *$" 1 " id=\"\\([a-zA-Z0-9_]+\\)\"" "#" ">")
          ("^[ \t]*<\\(@[a-z.]+\\)[^>]*>? *$" 1 " contentId=\"\\([a-zA-Z0-9_]+\\)\"" "=" ">")
          ;; angular imenu
          (" \\(ng-[a-z]*\\)=\"\\([^\"]+\\)" 1 2 "="))))

(provide 'init-web-mode)
