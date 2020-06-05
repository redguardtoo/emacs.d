;;; lazyflymake-elisp.el --- flymake elisp syntax checker  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'lazyflymake-sdk)

(defun lazyflymake-elisp-err-line-pattern ()
  "Return error line pattern.
If return a list containing the pattern, `flymake-err-line-patterns' use the
list and is also converted into a buffer local variable.
If return the pattern, it's is pushed to `flymake-err-line-patterns'.
If return nil, nothing need be done."
  nil)

(defun lazyflymake-elisp-init ()
  "Emacs Lisp syntax linter for flymake."
  (let* ((program-name (expand-file-name invocation-name invocation-directory)))
    (if lazyflymake-debug (message "lazyflymake-elisp-init called."))
    (list program-name
          (list "-Q"
                "--batch"
                "--eval"
                (prin1-to-string
                 (quote
                  (dolist (file command-line-args-left)
                    (with-temp-buffer
                      (insert-file-contents file)
                      (condition-case data
                          (scan-sexps (point-min) (point-max))
                        (scan-error
                         (goto-char(nth 2 data))
                         (princ (format "%s:%s: error: Unmatched bracket or quote\n"
                                        file (line-number-at-pos)))))))))
                (lazyflymake-sdk-code-file)))))

(provide 'lazyflymake-elisp)
;;; lazyflymake-elisp.el ends here
