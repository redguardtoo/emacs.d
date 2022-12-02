;; -*- coding: utf-8; lexical-binding: t; -*-

(defvar my-toggle-ime-init-function
  (lambda () (my-ensure 'pyim))
  "Function to execute at the beginning of `my-toggle-input-method'.")

;; {{ make IME compatible with evil-mode
(defun my-toggle-input-method ()
  "When input method is on, goto `evil-insert-state'."
  (interactive)

  ;; load IME when needed, less memory footprint
  (when my-toggle-ime-init-function
    (funcall my-toggle-ime-init-function))

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

(defun my-evil-insert-state-hack (orig-func &rest args)
  "Notify user IME status."
  (apply orig-func args)
  (if current-input-method (message "IME on!")))
(advice-add 'evil-insert-state :around #'my-evil-insert-state-hack)

(global-set-key (kbd "C-\\") 'my-toggle-input-method)
;; }}

;; {{ pyim
(defvar my-pyim-directory "~/.eim"
  "The directory containing pyim dictionaries.")

(defvar my-pyim-enable-wubi-dict nil
  "Use wubi IME.  Its value is t or pyim-wbdict's enable function.
See pyim-wbdict's website for the full list of enable functions.")

(with-eval-after-load 'pyim
  (defun my-pyim-clear-and-off ()
    "Clear and off."
    (interactive)
    (pyim-quit-clear)
    (my-toggle-input-method))

  ;; ;; select second word
  ;; (define-key pyim-mode-map ";" (lambda ()
  ;;                                 (interactive)
  ;;                                 (pyim-page-select-word-by-number 2)))
  ;; ;;next/previous page
  ;; (define-key pyim-mode-map "." 'pyim-page-next-page)
  ;; (define-key pyim-mode-map "," 'pyim-page-previous-page)

  ;; press "/" to turn off pyim
  (define-key pyim-mode-map (kbd "/") 'my-pyim-clear-and-off)

  ;; use western punctuation
  (setq pyim-punctuation-dict nil)

  (setq default-input-method "pyim")

  (cond
   (my-pyim-enable-wubi-dict
    ;; @see https://github.com/tumashu/pyim-wbdict
    (setq pyim-default-scheme 'wubi)
    (unless (member my-pyim-enable-wubi-dict
                    '(pyim-wbdict-v86-enable
                      pyim-wbdict-v98-enable
                      pyim-wbdict-v98-morphe-enable
                      pyim-wbdict-v86-single-enable))
      (setq my-pyim-enable-wubi-dict 'pyim-wbdict-v86-enable))
    ;; load wubi dictionary
    (funcall my-pyim-enable-wubi-dict))
   (t
    (setq pyim-pinyin-fuzzy-alist
          '(("en" "eng")
            ("in" "ing")))

    ;; Dictionaries:
    ;;   pyim-greatdict is not recommended. It has too many useless words and slows down pyim.
    ;;
    ;;   Download pyim-bigdict,
    ;;   curl -L http://tumashu.github.io/pyim-bigdict/pyim-bigdict.pyim.gz | zcat > ~/.eim/pyim-bigdict.pyim
    ;;
    ;;   Download pyim-tsinghua (recommended),
    ;;   curl -L https://raw.githubusercontent.com/redguardtoo/pyim-tsinghua-dict/master/pyim-tsinghua-dict.pyim > ~/.eim/pyim-tsinghua-dict.pyim

    ;; don's use shortcode2word
    (setq pyim-enable-shortcode nil)

    ;; use memory efficient pyim engine for pinyin IME
    (my-ensure 'pyim-dregcache)
    (setq pyim-dcache-backend 'pyim-dregcache)

    ;; automatically load pinyin dictionaries "*.pyim" under "~/.eim/"
    (let* ((files (and (file-exists-p my-pyim-directory)
                       (directory-files-recursively my-pyim-directory "\.pyim$")))
           disable-basedict)
      (when (and files (> (length files) 0))
        (setq pyim-dicts
              (mapcar (lambda (f)
                        (list :name (file-name-base f) :file f))
                      files))
        (dolist (f files)
          (when (member (file-name-base f) '("pyim-another-dict"
                                             "pyim-tsinghua-dict.pyim"
                                             "pyim-bigdict"
                                             "pyim-greatdict"))
            (setq disable-basedict t))))
      (unless disable-basedict (pyim-basedict-enable)))))

  ;; don't use tooltip
  (setq pyim-use-tooltip 'popup))
;; }}

(provide 'init-chinese)
