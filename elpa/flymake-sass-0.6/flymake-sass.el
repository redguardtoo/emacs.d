;;; flymake-sass.el --- Flymake handler for sass files
;;
;;; Author: Steve Purcell <steve@sanityinc.com>
;;; URL: https://github.com/purcell/flymake-sass
;; Package-Version: 0.6
;;; Version: DEV
;;; Package-Requires: ((flymake-easy "0.1"))
;;
;;; Commentary:
;;
;; Usage:
;;   (require 'flymake-sass)
;;   (add-hook 'sass-mode-hook 'flymake-sass-load)
;;   (add-hook 'scss-mode-hook 'flymake-sass-load)
;;
;; Uses flymake-easy, from https://github.com/purcell/flymake-easy

;;; Code:

(require 'flymake-easy)

(defconst flymake-sass-err-line-patterns
  '(("^Syntax error on line \\([0-9]+\\): \\(.*\\)$" nil 1 nil 2)
    ("^WARNING on line \\([0-9]+\\) of .*?:\r?\n\\(.*\\)$" nil 1 nil 2)
    ("^Syntax error: \\(.*\\)\r?\n        on line \\([0-9]+\\) of .*?$" nil 2 nil 1) ;; Older sass versions
    ))

;; Invoke utilities with '-c' to get syntax checking
(defun flymake-sass-command (filename)
  "Construct a command that flymake can use to check sass source."
  (append '("sass" "-c")
          (when (eq 'scss-mode major-mode)
            (list "--scss"))
          (list filename)))

;;;###autoload
(defun flymake-sass-load ()
  "Configure flymake mode to check the current buffer's sass syntax."
  (interactive)
  (flymake-easy-load 'flymake-sass-command
                     flymake-sass-err-line-patterns
                     'tempdir
                     "rb"))


(provide 'flymake-sass)
;;; flymake-sass.el ends here
