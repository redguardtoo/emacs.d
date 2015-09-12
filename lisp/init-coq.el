(let* ((src-dir "~/.emacs.d/site-lisp")
       (proof-file (expand-file-name "ProofGeneral-4.2/generic/proof-site.el"
                                     src-dir)))
  (load-file proof-file))

(provide 'init-coq)

