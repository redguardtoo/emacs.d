;; EIM Input Method. Use C-\ to toggle input method.
(autoload 'eim-use-package "eim" "Another emacs input method")
(setq eim-use-tooltip nil)              ; don't use tooltip
(setq eim-punc-translate-p nil)         ; use English punctuation
(register-input-method
 "eim-py" "euc-cn" 'eim-use-package
 "pinyin" "EIM Chinese Pinyin Input Method" (file-truename "~/.eim/py.txt")
 'my-eim-py-activate-function)
(setq default-input-method "eim-py")
;; (toggle-input-method nil)               ; default is turn off
(defun my-eim-py-activate-function ()
  (add-hook 'eim-active-hook
            (lambda ()
              (let ((map (eim-mode-map)))
                (define-key eim-mode-map "-" 'eim-previous-page)
                (define-key eim-mode-map "=" 'eim-next-page)))))

;; make ime compatible with evil-mode
(defun evil-toggle-input-method ()
  "when toggle on input method, switch to evil-insert-state if possible.
when toggle off input method, switch to evil-normal-state if current state is evil-insert-state"
  (interactive)
  ;; some guy donot use evil-mode at all
  (if (fboundp 'evil-insert-state)
      (if (not current-input-method)
          (if (not (string= evil-state "insert"))
              (evil-insert-state))
        (if (string= evil-state "insert")
            (evil-normal-state)
          )))
  (toggle-input-method))

(global-set-key (kbd "C-\\") 'evil-toggle-input-method)


(provide 'init-eim)
