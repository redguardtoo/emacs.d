(defun my-aspell-args ()
  "Customize aspell args."
  (let* ((args (wucuo-aspell-cli-args t)))
    (push (format "--personal=%s" (file-truename "tools/.aspell.en.pws")) args)
    args))

(let* ((ispell-program-name "aspell")
       (ispell-extra-args (my-aspell-args)))
  ;; (wucuo-spell-check-directory "lisp" t)
  (wucuo-spell-check-file "init.el" t)
  (wucuo-spell-check-file "README.org" t))
