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
    (unless (bound-and-true-p chinese-pyim)
      (require 'chinese-pyim))
    (activate-input-method default-input-method)
    (setq current-input-method default-input-method)))

(global-set-key (kbd "C-\\") 'evil-toggle-input-method)
;; }}

;; (setq pyim-punctuation-translate-p nil) ;; use western punctuation (ban jiao fu hao)

(eval-after-load 'chinese-pyim
  '(progn
     (setq default-input-method "chinese-pyim")
     ;; (setq pyim-enable-words-predict nil)
     (setq pyim-use-tooltip nil) ; don't use tooltip
     ;; personal dictionary should be out of ~/.emacs.d if possible
     (setq pyim-personal-file "~/ownCloud/backup/pyim-personal.txt")
     (setq pyim-property-file "~/ownCloud/backup/pyim-words-property.txt")
     ;; another official dictionary
     (setq pyim-dicts '((:name "pinyin1" :file "~/ownCloud/backup/pyim-bigdict.txt" :coding utf-8-unix)))

     ;; {{ fuzzy pinyin setup
     (defun pyim-fuzzy-pinyin-adjust-shanghai ()
       "As Shanghai guy, I can't tell difference between:
  - 'en' and 'eng'
  - 'in' and 'ing'"
       (interactive)
       (cond
        ((string-match-p "[a-z][ei]ng?-.*[a-z][ei]ng?" pyim-current-key)
         ;; for two fuzzy pinyin characters, just use its SHENMU as key
         (setq pyim-current-key (replace-regexp-in-string "\\([a-z]\\)[ie]ng" "\\1" pyim-current-key)))
        (t
         ;; single fuzzy pinyin character
         (cond
          ((string-match-p "[ei]ng" pyim-current-key)
           (setq pyim-current-key (replace-regexp-in-string "\\([ei]\\)ng" "\\1n" pyim-current-key)))
          ((string-match-p "[ie]n[^g]*" pyim-current-key)
           (setq pyim-current-key (replace-regexp-in-string "\\([ie]\\)n" "\\1ng" pyim-current-key))))))
       (pyim-handle-string))

     ;; Comment out below line for default fuzzy algorithm,
     ;; or just `(setq pyim-fuzzy-pinyin-adjust-function nil)`
     ;; (setq pyim-fuzzy-pinyin-adjust-function 'pyim-fuzzy-pinyin-adjust-shanghai)
     ;; }}

     ))

(provide 'init-chinese-pyim)
