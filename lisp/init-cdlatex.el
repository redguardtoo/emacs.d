(require-package 'cdlatex)

;; turn on cdlatex-mode automatically
(autoload 'turn-on-cdlatex "cdlatex" "CDLaTeX Mode" nil)

;; Turn on CDLaTeX Minor Mode for all LaTeX files
(add-hook 'LaTeX-mode-hook 'turn-on-cdlatex)   ; with AUCTeX LaTeX mode

(setq cdlatex-math-symbol-alist '(
( ?I ("\\iota" "\\Im"))
))

(setq cdlatex-math-modify-alist '(
( ?B "\\mathbb" nil t nil nil )
( ?f "\\mathfrak" nil t nil nil )
( ?s "\\mathscr" nil t nil nil)
))

(setq cdlatex-paired-parens "${[(")

(setq cdlatex-simplify-sub-super-scripts nil)

(provide 'init-cdlatex)