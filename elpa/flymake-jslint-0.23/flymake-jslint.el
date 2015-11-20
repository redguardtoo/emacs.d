;;; flymake-jslint.el --- Flymake support for javascript using jslint
;;
;;; Author: Steve Purcell <steve@sanityinc.com>
;;; Homepage: https://github.com/purcell/flymake-jslint
;;; Version: DEV
;; Package-Version: 0.23
;;
;;; Commentary:
;;
;; References:
;;   http://www.emacswiki.org/cgi-bin/wiki/FlymakeJavaScript
;;   http://d.hatena.ne.jp/kazu-yamamoto/mobile?date=20071029
;;
;; Usage: (add-hook 'js-mode-hook 'flymake-jslint-load)
(require 'flymake)

;;; Code:

(defgroup flymake-jslint nil
  "Flymake checking of Javascript using jslint"
  :group 'programming
  :prefix "flymake-jslint-")

;;;###autoload
(defcustom flymake-jslint-detect-trailing-comma t
  "Whether or not to report warnings about trailing commas."
  :type 'boolean :group :flymake-jslint)

;;;###autoload
(defcustom flymake-jslint-command "jsl"
  "Whether or not to report warnings about trailing commas."
  :type 'string :group 'flymake-jslint)

(defvar flymake-jslint-err-line-patterns
  '(("^\\(.+\\)\:\\([0-9]+\\)\: \\(SyntaxError\:.+\\)\:$" nil 2 nil 3)
    ("^\\(.+\\)(\\([0-9]+\\)): \\(SyntaxError:.+\\)$" nil 2 nil 3)
    ("^\\(.+\\)(\\([0-9]+\\)): \\(lint \\)?\\(warning:.+\\)$" nil 2 nil 4)))
(defvar flymake-jslint-trailing-comma-err-line-pattern
  '("^\\(.+\\)\:\\([0-9]+\\)\: strict \\(warning: trailing comma.+\\)\:$" nil 2 nil 3))


(defun flymake-jslint-init ()
  "Construct a command that flymake can use to check javascript source."
  (list flymake-jslint-command (list "-process" (flymake-init-create-temp-buffer-copy
                                                 'flymake-create-temp-inplace))))


;;;###autoload
(defun flymake-jslint-load ()
  "Configure flymake mode to check the current buffer's javascript syntax.

This function is designed to be called in `js-mode-hook' or
equivalent; it does not alter flymake's global configuration, so
function `flymake-mode' alone will not suffice."
  (interactive)
  (set (make-local-variable 'flymake-allowed-file-name-masks) '(("." flymake-jslint-init)))
  (set (make-local-variable 'flymake-err-line-patterns) flymake-jslint-err-line-patterns)
  (when flymake-jslint-detect-trailing-comma
    (add-to-list 'flymake-err-line-patterns
                 flymake-jslint-trailing-comma-err-line-pattern
                 t))
  (if (executable-find "jsl")
      (flymake-mode t)
    (message "Not enabling flymake: jsl command not found")))


(provide 'flymake-js)
;;; flymake-jslint.el ends here
