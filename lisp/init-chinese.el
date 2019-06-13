;; -*- coding: utf-8; lexical-binding: t; -*-

;; use memory efficient pyim engine
(setq pyim-mapping-file-engine-p t)

;; {{ make IME compatible with evil-mode
(defun evil-toggle-input-method ()
  "When input method is on, goto `evil-insert-state'."
  (interactive)

  ;; load IME when needed, less memory footprint
  (unless (featurep 'pyim) (local-require 'pyim))

  ;; some guys don't use evil-mode at all
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
    (cond
     (current-input-method
      ;; evil-escape and pyim may conflict
      ;; @see https://github.com/redguardtoo/emacs.d/issues/629
      (evil-escape-mode -1)
      (message "IME on!"))
     (t
      (evil-escape-mode 1)
      (message "IME off!"))))
   (t
    ;; NOT evil-mode
    (toggle-input-method))))

(defadvice evil-insert-state (around evil-insert-state-hack activate)
  ad-do-it
  (if current-input-method (message "IME on!")))

(global-set-key (kbd "C-\\") 'evil-toggle-input-method)
;; }}

;; {{ pyim
(defvar my-pyim-directory "~/.eim"
  "The directory containing pyim dictionaries.
Bigger (>2M) dictionaries in this directory will replace basedict.")

(add-auto-mode 'text-mode "\\.pyim\\'")

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
     ;; use western punctuation (ban jiao fu hao)
     (setq pyim-punctuation-dict nil)
     ;; always input English when isearch
     (setq pyim-isearch-enable-pinyin-search t)
     (setq default-input-method "pyim")

     ;; I'm OK with a smaller dictionary
     (let* ((files (directory-files-and-attributes my-pyim-directory t "\.pyim$") )
            bigdict-p)
       (cond
        ((> (length files) 0)
         (setq pyim-dicts
               (mapcar (lambda (f)
                         (when (> (file-attribute-size (cdr f)) (* 2 1024 1024))
                           (setq bigdict-p t))
                         (list :name (file-name-base (car f))
                               :file (car f)))
                       files)))
        ((not bigdict-p)
         (pyim-basedict-enable))))

     ;; You can also set up the great dictionary (80M) the same way as peronsal dictionary
     ;; great dictionary can be downloaded this way:
     ;; `curl -L https://github.com/tumashu/pyim-greatdict/raw/master/pyim-greatdict.pyim.gz | zcat > ~/.eim/pyim-greatdict.pyim`

     ;; don't use tooltip
     (setq pyim-use-tooltip 'popup)))
;; }}

;; {{ cal-china-x setup
(defun chinese-calender (&optional args)
  "Open Chinese Lunar calenadar."
  (interactive "P")
  (local-require 'cal-china-x)
  (let* ((calendar-date-display-form
          '((cal-china-x-calendar-display-form
             (mapcar (lambda (el) (string-to-number el))
                     (list month day year)))))
         (diary-date-forms chinese-date-diary-pattern)

         ;; chinese month and year
         (calendar-font-lock-keywords
          (append calendar-font-lock-keywords
                  '(("[0-9]+年\\ *[0-9]+月" . font-lock-function-name-face))))

         (calendar-chinese-celestial-stem cal-china-x-celestial-stem)
         (calendar-chinese-terrestrial-branch cal-china-x-terrestrial-branch)
         (calendar-month-header '(propertize (format "%d年%2d月" year month)
                                             'font-lock-face
                                             'calendar-month-header))

         ;; if chinese font width equals to twice of ascii font
         (calendar-day-header-array cal-china-x-days)

         (calendar-mode-line-format
          (list
           (calendar-mode-line-entry 'calendar-scroll-right "previous month" "<")
           "Calendar"

           '(cal-china-x-get-holiday date)

           '(concat " " (calendar-date-string date t)
                    (format " 第%d周"
                            (funcall (if cal-china-x-custom-week-start-date
                                         'cal-china-x-custom-week-of-date
                                       'cal-china-x-week-of-date)
                                     date)))

           '(cal-china-x-chinese-date-string date)

           ;; (concat
           ;;  (calendar-mode-line-entry 'calendar-goto-info-node "read Info on Calendar"
           ;;                            nil "info")
           ;;  " / "
           ;;  (calendar-mode-line-entry 'calendar-other-month "choose another month"
           ;;                            nil "other")
           ;;  " / "
           ;;  (calendar-mode-line-entry 'calendar-goto-today "go to today's date"
           ;;                            nil "today"))

           (calendar-mode-line-entry 'calendar-scroll-left "next month" ">")))

         other-holidays
         (mark-holidays-in-calendar t)
         (cal-china-x-important-holidays cal-china-x-chinese-holidays)
         (cal-china-x-general-holidays '((holiday-lunar 1 15 "元宵节")))
         (calendar-holidays
          (append cal-china-x-important-holidays
                  cal-china-x-general-holidays
                  other-holidays)))
    (advice-add 'calendar-mark-holidays :around #'cal-china-x-mark-holidays)
    (calendar args)))

(defadvice calendar-exit (before calendar-exit-before-hack activate)
  "Clean the cal-chinese-x setup."
  (advice-remove 'calendar-mark-holidays #'cal-china-x-mark-holidays))
;; }}

(provide 'init-chinese)
