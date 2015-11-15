;; org-babel support language

(org-babel-do-load-languages
 'org-babel-load-languages
 '((python . t)
   (perl . t)
   (ruby . t)
   (haskell . t)
   (dot . t)
   (R . t)
   (emacs-lisp . t)))

(provide 'init-personal-misc)