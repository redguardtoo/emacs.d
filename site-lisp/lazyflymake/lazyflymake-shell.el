;;; lazyflymake-shell.el --- flymake shell script syntax checker  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'lazyflymake-sdk)

(defcustom lazyflymake-shell-program "shellcheck"
  "The path of the shellcheck linter."
  :group 'lazyflymake
  :type 'string)

(defcustom lazyflymake-shell-args '("--format=gcc" "-x")
  "Arguments of shellcheck cli."
  :group 'lazyflymake
  :type '(repeat string))

(defun lazyflymake-shell-err-line-pattern ()
  "Return error line pattern.
If return a list of patterns, `flymake-proc-err-line-patterns' uses the
list and is also converted into a buffer local variable.
If return the pattern, it's is pushed to `flymake-proc-err-line-patterns'.
If return nil, nothing need be done."
;; /home/cb/.bashrc:30:7: note: Not following: /etc/bash/bashrc was not specified as input (see shellcheck -x). [SC1091]
  '("\\(^[^:]+\\):\\([0-9]+\\):\\([0-9]+\\): +\\([^:]*\\): +\\(.*\\)$"  1 2 3 5))

(defun lazyflymake-shell-init ()
  "Shell script syntax linter for flymake."
  (let (file)
    (when (and (executable-find lazyflymake-shell-program)
               (setq file (lazyflymake-sdk-code-file)))
      (if lazyflymake-debug (message "lazyflymake-shell-init called"))
      (lazyflymake-sdk-generate-flymake-init
       lazyflymake-shell-program
       lazyflymake-shell-args
       file))))

(provide 'lazyflymake-shell)
;;; lazyflymake-shell.el ends here
