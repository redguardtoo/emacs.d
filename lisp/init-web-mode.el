(autoload 'web-mode "web-mode")
(add-to-list 'auto-mode-alist '("\\.phtml\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.cmp\\'" . web-mode)) ; salesforce
(add-to-list 'auto-mode-alist '("\\.app\\'" . web-mode)) ; salesforce
(add-to-list 'auto-mode-alist '("\\.page\\'" . web-mode)) ; salesforce
(add-to-list 'auto-mode-alist '("\\.component\\'" . web-mode)) ; salesforce
(add-to-list 'auto-mode-alist '("\\.wp\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.tmpl\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.php\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.module\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.inc\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.hbs\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.tpl\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.[gj]sp\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.as[cp]x\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.erb\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.mustache\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.djhtml\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.ftl\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.html?\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.xul?\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.eex?\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.xml?\\'" . web-mode))

(defun flymake-html-init ()
       (let* ((temp-file (flymake-init-create-temp-buffer-copy
                          'flymake-create-temp-inplace))
              (local-file (file-relative-name
                           temp-file
                           (file-name-directory buffer-file-name))))
         (list "tidy" (list local-file))))

(defun flymake-html-load ()
  (interactive)
  (when (and (not (null buffer-file-name)) (file-writable-p buffer-file-name))
    (set (make-local-variable 'flymake-allowed-file-name-masks)
         '(("\\.html\\|\\.ctp\\|\\.ftl\\|\\.jsp\\|\\.php\\|\\.erb\\|\\.rhtml" flymake-html-init))
         )
    (set (make-local-variable 'flymake-err-line-patterns)
         ;; only validate missing html tags
         '(("line \\([0-9]+\\) column \\([0-9]+\\) - \\(Warning\\|Error\\): \\(missing <\/[a-z0-9A-Z]+>.*\\)" nil 1 2 4)))
    (flymake-mode 1)))

(defun web-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (flymake-html-load)
    (enable-flyspell-mode-conditionally)
    (setq flyspell-check-doublon nil)
    (remove-hook 'yas-after-exit-snippet-hook
                 'web-mode-yasnippet-exit-hook t)
    (remove-hook 'yas/after-exit-snippet-hook
                 'web-mode-yasnippet-exit-hook t)))

(add-hook 'web-mode-hook 'web-mode-hook-setup)

(eval-after-load 'web-mode
  '(progn
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
             (" \\(ng-[a-z]*\\)=\"\\([^\"]+\\)" 1 2 "=")))
     ))

(provide 'init-web-mode)
