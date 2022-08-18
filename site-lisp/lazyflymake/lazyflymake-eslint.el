;;; lazyflymake-eslint.el --- flymake eslint syntax checker  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'lazyflymake-sdk)

(defun lazyflymake-eslint-err-line-pattern ()
  "Return error line pattern.
If return a list containing patterns, `flymake-proc-err-line-patterns' uses the
list and is also converted into a buffer local variable.
If return the pattern, it's is pushed to `flymake-proc-err-line-patterns'.
If return nil, nothing need be done."
  nil)

(defun lazyflymake-eslint-init ()
  "Eslint syntax check init."
  (let* ((dir (locate-dominating-file default-directory "node_modules"))
         (local-eslint (concat dir "node_modules/.bin/eslint"))
         (program (if (file-exists-p local-eslint) local-eslint "eslint"))
         file)
    (when (and (executable-find program)
               (setq file (lazyflymake-sdk-code-file)))
      (lazyflymake-sdk-generate-flymake-init
       program
       '("--format" "unix")
       file))))

(provide 'lazyflymake-eslint)
;;; lazyflymake-eslint.el ends here
