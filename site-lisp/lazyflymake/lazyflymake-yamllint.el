;;; lazyflymake-yamllint.el --- flymake yaml syntax checker  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'lazyflymake-sdk)

(defcustom lazyflymake-yamllint-program "yamllint"
  "The path of the yaml linter."
  :group 'lazyflymake
  :type 'string)

(defun lazyflymake-yamllint-err-line-pattern ()
  "Return error line pattern.
If return a list containing patterns, `flymake-proc-err-line-patterns' uses the
list and is also converted into a buffer local variable.
If return the pattern, it's is pushed to `flymake-proc-err-line-patterns'.
If return nil, nothing need be done."
  '("^\\([^:]+\\):\\([0-9]+\\):\\([0-9]+\\): \\([^:]+\\)$" 1 2 3 4))

(defun lazyflymake-yamllint-init ()
  "Yamllint syntax check init."
  (let (file)
    (when (and (executable-find lazyflymake-yamllint-program)
               (setq file (lazyflymake-sdk-code-file)))
      (lazyflymake-sdk-generate-flymake-init
       lazyflymake-yamllint-program
       '("-f" "parsable")
       file))))

(provide 'lazyflymake-yamllint)
;;; lazyflymake-yamllint.el ends here
