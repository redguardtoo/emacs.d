;;; lazyflymake-eslint.el --- flymake eslint syntax checker  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'lazyflymake-sdk)

(defcustom lazyflymake-eslint-args '("--format" "unix")
  "Arguments of eslint cli."
  :group 'lazyflymake
  :type '(repeat string))

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
         file
         ;; use babel?
         (babelrc (lazyflymake-sdk-find-dominating-file '("babel.config.json" ".babelrc.json" "babel.config.js"))))

    (when (and (executable-find program)
               (setq file (lazyflymake-sdk-code-file)))

      ;; use locale babel configuration file
      (when babelrc
        (push (format "{babelOptions:{configFile:'%s'}}" (file-truename babelrc))
              lazyflymake-eslint-args)
        (push "--parser-options" lazyflymake-eslint-args))

      (lazyflymake-sdk-generate-flymake-init
       program
       lazyflymake-eslint-args
       file))))

(provide 'lazyflymake-eslint)
;;; lazyflymake-eslint.el ends here
