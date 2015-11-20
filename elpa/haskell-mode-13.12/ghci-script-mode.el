;;; ghci-script-mode.el --- GHCi scripts major mode

;; Copyright (c) 2014 Chris Done. All rights reserved.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:

(require 'haskell)

(defvar ghci-script-mode-keywords
  ;; The comment syntax can't be described simply in syntax-table.
  ;; We could use font-lock-syntactic-keywords, but is it worth it?
  '(("^[ \t]*--.*" . font-lock-comment-face)
    ("^ *\\([^ \t:]+\\):" (1 font-lock-keyword-face))
    ("^:[a-z{]+ *\\+" . font-lock-keyword-face)
    ("^:[a-z{]+ " . font-lock-keyword-face)))

;;;###autoload
(define-derived-mode ghci-script-mode text-mode "GHCi-Script"
  "Major mode for working with .ghci files."
  (set (make-local-variable 'adaptive-fill-mode) nil)
  (set (make-local-variable 'comment-start) "-- ")
  (set (make-local-variable 'comment-padding) 0)
  (set (make-local-variable 'comment-start-skip) "[-{]-[ \t]*")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-end-skip) "[ \t]*\\(-}\\|\\s>\\)")
  (set (make-local-variable 'indent-line-function) 'haskell-mode-suggest-indent-choice)
  (set (make-local-variable 'font-lock-defaults)
       '(ghci-script-mode-keywords t t nil nil))
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set (make-local-variable 'tab-width) 8)
  (when (boundp 'electric-indent-inhibit)
    (setq electric-indent-inhibit t))
  (set (make-local-variable 'dabbrev-case-fold-search) nil)
  (set (make-local-variable 'dabbrev-case-distinction) nil)
  (set (make-local-variable 'dabbrev-case-replace) nil)
  (set (make-local-variable 'dabbrev-abbrev-char-regexp) "\\sw\\|[.]")
  (setq haskell-literate nil))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.ghci\\'" . ghci-script-mode))

(define-key ghci-script-mode-map (kbd "C-c C-l") 'ghci-script-mode-load)

(defun ghci-script-mode-load ()
  (interactive)
  "Load the current script file into the GHCi session."
  (let ((buffer (haskell-session-interactive-buffer (haskell-session)))
        (filename (buffer-file-name)))
    (save-buffer)
    (with-current-buffer buffer
      (set-marker haskell-interactive-mode-prompt-start (point-max))
      (haskell-interactive-mode-run-expr
       (concat ":script " filename)))))

(provide 'ghci-script-mode)
