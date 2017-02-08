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
        (toggle-input-method))))
    (if current-input-method (message "IME on!")))
   (t
    ;; NOT evil-mode
    (toggle-input-method))))

(defadvice evil-insert-state (around evil-insert-state-hack activate)
  ad-do-it
  (if current-input-method (message "IME on!")))

(global-set-key (kbd "C-\\") 'evil-toggle-input-method)
;; }}

(eval-after-load 'chinese-pyim
  '(progn
     (setq pyim-punctuation-translate-p nil) ;; use western punctuation (ban jiao fu hao)
     (setq default-input-method "chinese-pyim")
     (setq pyim-use-tooltip 'popup) ; don't use tooltip
     ;; personal dictionary should be out of ~/.emacs.d if possible
     (if (file-exists-p (file-truename "~/.eim/pyim-personal.txt"))
         (setq pyim-personal-file "~/.eim/pyim-personal.txt"))
     ;; another official dictionary
     (setq pyim-dicts '((:name "pinyin1" :file "~/.emacs.d/pyim/py.txt" :coding utf-8-unix :dict-type pinyin-dict)))))

(provide 'init-chinese-pyim)
