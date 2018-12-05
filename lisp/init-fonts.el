;;; Changing font sizes

;(require-package 'default-text-scale)
;(add-hook 'after-init-hook 'default-text-scale-mode)


;; (defun sanityinc/maybe-adjust-visual-fill-column ()
;;   "Readjust visual fill column when the global font size is modified.
;; This is helpful for writeroom-mode, in particular."
;;   (if visual-fill-column-mode
;;       (add-hook 'after-setting-font-hook 'visual-fill-column--adjust-window nil t)
;;     (remove-hook 'after-setting-font-hook 'visual-fill-column--adjust-window t)))

;; (add-hook 'visual-fill-column-mode-hook
;;           'sanityinc/maybe-adjust-visual-fill-column)

;;; Default font setting for different OS
(when *is-a-mac*
  (set-frame-font "-*-Monaco-normal-normal-normal-*-12.5-*-*-*-m-0-iso10646-1" )
  ;; configure Chinese characters to align tables
  (dolist (charset '(kana han symbol cjk-misc bopomofo))
    (set-fontset-font (frame-parameter nil 'font)
		      charset
		      (font-spec :name "-*-HanziPen TC-normal-normal-normal-*-*-*-*-*-p-0-iso10646-1"
				 :weight 'normal
				 :slant 'normal
				 :size 14.0))))
(when *linux*
  (set-frame-font "-unkonwn-Ubuntu Mono-normal-normal-normal-*-16-*-*-*-m-0-iso10646-1")
  ;; configure Chinese characters to align tables
  (dolist (charset '(kana han symbol cjk-misc bopomofo))
    (set-fontset-font (frame-parameter nil 'font)
                      charset (font-spec :family "Noto Sans CJK JP" :size 16))))
(when *win64*
  (set-frame-font "-outline-Courier New-normal-normal-normal-mono-14-*-*-*-c-*-iso8859-1")
  ;; configure Chinese characters to align tables
  (dolist (charset '(kana han symbol cjk-misc bopomofo))
    (set-fontset-font (frame-parameter nil 'font)
                      charset (font-spec :family "NSimsun" :size 15))))



(provide 'init-fonts)
