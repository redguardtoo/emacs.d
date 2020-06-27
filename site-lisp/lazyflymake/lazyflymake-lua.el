;;; lazyflymake-lua.el --- flymake lua syntax checker  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'lazyflymake-sdk)

(defcustom lazyflymake-lua-program "luac"
  "The path to the check program."
  :group 'lazyflymake
  :type 'string)

(defun lazyflymake-lua-err-line-pattern ()
  "Return error line pattern.
If return a list containing the pattern, `flymake-err-line-patterns' use the
list and is also converted into a buffer local variable.
If return the pattern, it's is pushed to `flymake-err-line-patterns'.
If return nil, nothing need be done."
  '("^.*luac[0-9.]*\\(.exe\\)?: *\\(.*\\):\\([0-9]+\\): \\(.*\\)$" 2 3 nil 4))

(defun lazyflymake-lua-init ()
  "Lua syntax check init."
  (when (executable-find lazyflymake-lua-program)
    (if lazyflymake-debug (message "lazyflymake-lua-init called"))
    (list lazyflymake-lua-program
          (list "-p" (lazyflymake-sdk-code-file)))))

(provide 'lazyflymake-lua)
;;; lazyflymake-lua.el ends here
