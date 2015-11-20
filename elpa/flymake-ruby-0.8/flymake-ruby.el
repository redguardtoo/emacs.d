;;; flymake-ruby.el --- A flymake handler for ruby-mode files
;;
;;; Author: Steve Purcell <steve@sanityinc.com>
;;; URL: https://github.com/purcell/flymake-ruby
;; Package-Version: 0.8
;;; Version: DEV
;;; Package-Requires: ((flymake-easy "0.1"))
;;;
;;; Commentary:
;; Usage:
;;   (require 'flymake-ruby)
;;   (add-hook 'ruby-mode-hook 'flymake-ruby-load)
;;
;; Uses flymake-easy, from https://github.com/purcell/flymake-easy

;;; Code:

(require 'flymake-easy)

(defconst flymake-ruby-err-line-patterns
  '(("^\\(.*\.rb\\):\\([0-9]+\\): \\(.*\\)$" 1 2 nil 3)))

(defvar flymake-ruby-executable "ruby"
  "The ruby executable to use for syntax checking.")

;; Invoke ruby with '-c' to get syntax checking
(defun flymake-ruby-command (filename)
  "Construct a command that flymake can use to check ruby source."
  (list flymake-ruby-executable "-w" "-c" filename))

;;;###autoload
(defun flymake-ruby-load ()
  "Configure flymake mode to check the current buffer's ruby syntax."
  (interactive)
  (flymake-easy-load 'flymake-ruby-command
                     flymake-ruby-err-line-patterns
                     'tempdir
                     "rb"))

(provide 'flymake-ruby)
;;; flymake-ruby.el ends here
