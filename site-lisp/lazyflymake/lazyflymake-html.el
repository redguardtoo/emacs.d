;;; lazyflymake-html.el --- flymake html/matlab syntax checker  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'lazyflymake-sdk)

(defvar lazyflymake-html-program "tidy"
  "The path of html linter.")

(defun lazyflymake-html-err-line-pattern ()
  "Return error line pattern.
If return a list containing patterns, `flymake-proc-err-line-patterns' uses the
list and is also converted into a buffer local variable.
If return the pattern, it's is pushed to `flymake-proc-err-line-patterns'.
If return nil, nothing need be done."
  '(("line \\([0-9]+\\) column \\([0-9]+\\) - \\(Warning\\|Error\\): \\(.*\\)" nil 1 2 4)))

(defun lazyflymake-html-init ()
  "Html syntax check init."
  (let (file)
    (when (and (executable-find lazyflymake-html-program)
               (setq file (lazyflymake-sdk-code-file)))
      (if lazyflymake-debug (message "lazyflymake-html-init called"))
      (lazyflymake-sdk-generate-flymake-init
       lazyflymake-html-program
       '("-language" "en" "-utf8" "-errors" "-quiet")
       file))))

(provide 'lazyflymake-html)
;;; lazyflymake-html.el ends here
