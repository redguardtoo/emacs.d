(require 'chinese-pyim)
(setq default-input-method "chinese-pyim")
(setq pyim-use-tooltip nil)              ; don't use tooltip
(setq pyim-dicts '((:name "pinyin1" :file "~/.eim/py.txt" :coding utf-8-unix)))

;; {{ fuzzy pinyin setup
(defun pyim-fuzzy-pinyin-adjust-shanghai ()
  (interactive)
  "As Shanghai guy, I cannot tell difference for a few pinyins"
  (cond
   ((string-match-p "eng" pyim-current-key)
    (setq pyim-current-key
          (replace-regexp-in-string "eng" "en" pyim-current-key)))
   ((string-match-p "en[^g]*" pyim-current-key)
    (setq pyim-current-key
          (replace-regexp-in-string "en" "eng" pyim-current-key)))
   ((string-match-p "ing" pyim-current-key)
    (setq pyim-current-key
          (replace-regexp-in-string "ing" "in" pyim-current-key)))
   ((string-match-p "in[^g]*" pyim-current-key)
    (setq pyim-current-key
          (replace-regexp-in-string "in" "ing" pyim-current-key))))
  (pyim-handle-string))

(setq pyim-fuzzy-pinyin-adjust-function 'pyim-fuzzy-pinyin-adjust-shanghai)
;; }}

;; {{ make IME compatible with evil-mode
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
  ;; my way to toggle-input-method, the original implementation has some weird bug
  (if current-input-method
      (progn
        (deactivate-input-method)
        (setq current-input-method nil))
    (activate-input-method default-input-method)
    (setq current-input-method default-input-method)))

(global-set-key (kbd "C-\\") 'evil-toggle-input-method)
;; }}

(provide 'init-chinese-pyim)