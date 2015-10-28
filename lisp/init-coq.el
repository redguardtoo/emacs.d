(let* ((src-dir "~/.emacs.d/site-lisp")
       (proof-file (expand-file-name "ProofGeneral-4.2/generic/proof-site.el"
                                     src-dir)))
  (load-file proof-file))

;; I can't find coq-mode-hook, so specific yasnippet can't run.
;; I have to turn on global.
(yas-global-mode 1)

(provide 'init-coq)

