;;; lazyflymake-shell.el --- flymake shell script syntax checker  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'lazyflymake-sdk)

(defcustom lazyflymake-shell-program "shellcheck"
  "The path to the shellcheck executable."
  :group 'lazyflymake
  :type 'string)

(defcustom lazyflymake-shell-program-opts '("--format=gcc")
  "The options of shellcheck executable."
  :group 'lazyflymake
  :type 'string)

(defun lazyflymake-shell-err-line-pattern ()
  "Return error line pattern.
If return a list containing the pattern, `flymake-err-line-patterns' use the
list and is also converted into a buffer local variable.
If return the pattern, it's is pushed to `flymake-err-line-patterns'.
If return nil, nothing need be done."
;; /home/cb/.bashrc:30:7: note: Not following: /etc/bash/bashrc was not specified as input (see shellcheck -x). [SC1091]
  '("\\(^[^:]+\\):\\([0-9]+\\):\\([0-9]+\\): +\\([^:]*\\): +\\(.*\\)$"  1 2 3 5))

(defun lazyflymake-shell-init ()
  "Shell script syntax linter for flymake."
  (when (executable-find lazyflymake-shell-program)
    (if lazyflymake-debug (message "lazyflymake-shell-init called"))
    (let* ((opts lazyflymake-shell-program-opts))
      (setq opts (add-to-list 'opts (lazyflymake-sdk-code-file) t))
      (list lazyflymake-shell-program opts))))

(provide 'lazyflymake-shell)
;;; lazyflymake-shell.el ends here
