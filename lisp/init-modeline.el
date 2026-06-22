;; -*- coding: utf-8; lexical-binding: t; -*-

;; @see http://emacs-fu.blogspot.com/2011/08/customizing-mode-line.html
;; @see http://www.delorie.com/gnu/docs/elisp-manual-21/elisp_360.html
;; use setq-default to set it for /all/ modes
(defvar my-extra-mode-line-info '()
  "Extra info displayed at the end of the mode line.")

(setq-default
 mode-line-format
 '("%b" ;; the buffer name

   (:eval " (%l,%C) ")

   "["

   ;; major mode, please note "%m" is legacy format since emacs 28
   (:eval (if (stringp mode-name)
              mode-name
            (format "%s" (if (consp mode-name) (car mode-name) mode-name))))

   ;; buffer file encoding
   (:eval (let ((sys (coding-system-plist buffer-file-coding-system)))
            (format " %s "
                    (if (memq (plist-get sys :category)
                              '(coding-category-undecided coding-category-utf-8))
                        "UTF-8"
                      (upcase (symbol-name (plist-get sys :name)))))))

   (:eval (propertize (concat (if overwrite-mode "O" "I")
                              (and (buffer-modified-p) "M")
                              (and buffer-read-only "R"))
                      'face
                      'font-lock-keyword-face))

   "] "

   ;; `org-timer-set-timer' uses it
   (:eval mode-line-misc-info)

   (:eval my-extra-mode-line-info)

   mode-line-end-spaces
   ))

(with-eval-after-load 'time
  ;; Donot show system load in mode line
  (setq display-time-default-load-average nil)
  ;; By default, the file in environment variable MAIL is checked
  ;; It's "/var/mail/my-username"
  ;; I set `display-time-mail-function' to display NO mail notification in mode line
  (setq display-time-mail-function (lambda () nil)))

(provide 'init-modeline)
