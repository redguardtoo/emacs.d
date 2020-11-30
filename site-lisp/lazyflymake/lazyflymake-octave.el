;;; lazyflymake-octave.el --- flymake octave/matlab syntax checker  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'lazyflymake-sdk)

(defvar lazyflymake-octave-program "mh_style"
  "The path of octave/matlab linter.")

(defun lazyflymake-octave-err-line-pattern ()
  "Return error line pattern.
If return a list containing the pattern, `flymake-err-line-patterns' uses the
list and is also converted into a buffer local variable.
If return the pattern, it's is pushed to `flymake-err-line-patterns'.
If return nil, nothing need be done."
  nil)

(defun lazyflymake-octave-init ()
  "Octave syntax check init."
  (let* ((file (lazyflymake-sdk-code-file)))
    (when (and (executable-find lazyflymake-octave-program) (file-exists-p file))
      (list lazyflymake-octave-program
            (list "--brief" "--tab_width=2" "--line_length=512" file)))))

(provide 'lazyflymake-octave)
;;; lazyflymake-octave.el ends here
