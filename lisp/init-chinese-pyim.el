;; {{ make IME compatible with evil-mode
(defun evil-toggle-input-method ()
  "when toggle on input method, goto evil-insert-state. "
  (interactive)

  ;; load IME when needed, less memory footprint
  (unless (featurep 'pyim)
    (require 'pyim))

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

(defvar my-pyim-directory
  "~/.eim"
  "There directory of peronsal dictionaries for pyim.")

(add-to-list 'auto-mode-alist '("\\.pyim\\'" . text-mode))

(defun my-pyim-personal-dict (&optional dict-name)
  (file-truename (concat (file-name-as-directory my-pyim-directory)
                         (or dict-name "personal.pyim"))))

(defun my-pyim-export-dictionary ()
  "Export words you use in pyim into personal dictionary."
  (interactive)
  (with-temp-buffer
    (maphash
     #'(lambda (key value)
         ;; only export two character word
         (if (string-match "-" key)
             (insert (concat key
                             " "
                             (mapconcat #'identity value ""))
                     "\n")))
     pyim-dcache-icode2word)
    (unless (and my-pyim-directory
                 (file-directory-p my-pyim-directory))
      (setq my-pyim-directory
            (read-directory-name "Personal Chinese dictionary directory:")))
    (if my-pyim-directory
        (write-file (my-pyim-personal-dict)))))

(eval-after-load 'pyim
  '(progn
     ;; I'm OK with a smaller dictionary
     (pyim-basedict-enable)
     ;; use western punctuation (ban jiao fu hao)
     (setq pyim-punctuation-dict nil)
     ;; always input English when isearch
     (setq pyim-isearch-enable-pinyin-search t)
     (setq default-input-method "pyim")
     ;; use personal dictionary
     (if (and my-pyim-directory
              (file-exists-p (my-pyim-personal-dict)))
         (add-to-list 'pyim-dicts (list :name "personal" :file (my-pyim-personal-dict))))

     ;; You can also set up the great dictionary (80M) the same way as peronsal dictionary
     ;; great dictionary can be downloaded this way:
     ;; `curl -L https://github.com/tumashu/pyim-greatdict/raw/master/pyim-greatdict.pyim.gz | zcat > ~/.eim/pyim-greatdict.pyim`

     ;; don't use tooltip
     (setq pyim-use-tooltip 'popup)))

(provide 'init-chinese-pyim)
