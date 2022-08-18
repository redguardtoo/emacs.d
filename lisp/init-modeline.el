;; -*- coding: utf-8; lexical-binding: t; -*-

;; @see http://emacs-fu.blogspot.com/2011/08/customizing-mode-line.html
;; @see http://www.delorie.com/gnu/docs/elisp-manual-21/elisp_360.html
;; use setq-default to set it for /all/ modes
(defvar my-extra-mode-line-info '()
  "Extra info displayed at the end of the mode line.")

(setq-default mode-line-format
  (list
    ;; the buffer name
   "%b"

    ;; line and column
   ;; '%02' to set to 2 chars at least; prevents flickering
    "(%02l,%01c)"

    "["

    "%m " ; major mode name

    ;; buffer file encoding
    '(:eval (let ((sys (coding-system-plist buffer-file-coding-system)))
              (if (memq (plist-get sys :category)
                        '(coding-category-undecided coding-category-utf-8))
                  "UTF-8"
                (upcase (symbol-name (plist-get sys :name))))))
    " "

    ;; insert vs overwrite mode
    '(:eval (propertize (if overwrite-mode "O" "I")
              'face nil
              'help-echo (concat "Buffer is in "
                           (if overwrite-mode "overwrite" "insert") " mode")))

    ;; was this buffer modified since the last save?
    '(:eval (and (buffer-modified-p)
                 (propertize "M"
                             'face nil
                             'help-echo "Buffer has been modified")))

    ;; is this buffer read-only?
    '(:eval (and buffer-read-only
                 (propertize "R" 'face nil 'help-echo "Buffer is read-only")))
    "] "

    ;; `global-mode-string' is useful because `org-timer-set-timer' uses it
    "%M"

    '(:eval my-extra-mode-line-info)

    " %-" ;; fill with '-'
    ))

(with-eval-after-load 'time
  ;; Donot show system load in mode line
  (setq display-time-default-load-average nil)
  ;; By default, the file in environment variable MAIL is checked
  ;; It's "/var/mail/my-username"
  ;; I set `display-time-mail-function' to display NO mail notification in mode line
  (setq display-time-mail-function (lambda () nil)))

(provide 'init-modeline)
