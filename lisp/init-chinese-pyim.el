;; {{ make IME compatible with evil-mode
(defun evil-toggle-input-method ()
  "when toggle on input method, goto evil-insert-state. "
  (interactive)

  ;; load IME when needed, less memory footprint
  (unless (featurep 'chinese-pyim)
    (require 'chinese-pyim))

  ;; some guy don't use evil-mode at all
  (cond
   ((and (boundp 'evil-mode) evil-mode)
    ;; evil-mode
    (cond
     ((eq evil-state 'insert)
      (toggle-input-method))
     (t
      (evil-insert-state)
      (unless current-input-method
        (toggle-input-method))
      ))
    (if current-input-method (message "IME on!")))
   (t
    ;; NOT evil-mode
    (toggle-input-method)))
  )

(defadvice evil-insert-state (around evil-insert-state-hack activate)
  ad-do-it
  (if current-input-method (message "IME on!")))

(global-set-key (kbd "C-\\") 'evil-toggle-input-method)
;; }}

(setq pyim-punctuation-translate-p nil) ;; use western punctuation (ban jiao fu hao)

(eval-after-load 'chinese-pyim
  '(progn
     (setq default-input-method "chinese-pyim")
     (setq pyim-use-tooltip 'popup) ; don't use tooltip
     ;; personal dictionary should be out of ~/.emacs.d if possible
     (if (file-exists-p (file-truename "~/.eim/pyim-personal.txt"))
       (setq pyim-personal-file "~/.eim/pyim-personal.txt"))
     ;; another official dictionary
     (setq pyim-dicts '((:name "pinyin1" :file "~/.emacs.d/pyim/py.txt" :coding utf-8-unix :dict-type pinyin-dict)))

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
     (setq pyim-fuzzy-pinyin-adjust-function 'pyim-fuzzy-pinyin-adjust-shanghai)
     ;; }}

     ))

(provide 'init-chinese-pyim)
