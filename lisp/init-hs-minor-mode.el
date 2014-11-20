(dolist (hook '(c-mode-common-hook
                emacs-lisp-mode-hook
                java-mode-hook
                lisp-mode-hook
                perl-mode-hook
                sh-mode-hook
                js-mode-hook
                js2-mode-hook))
      (add-hook hook (lambda ()
                       (unless (is-buffer-file-temp)
                         (hs-minor-mode)))))

(setq hs-minor-mode-map
      (let ((map (make-sparse-keymap)))
        (define-key map (kbd "C-c @ h") 'hs-hide-block)
        (define-key map (kbd "C-c @ H") 'hs-show-block)
        (define-key map (kbd "C-c @ s") 'hs-hide-all)
        (define-key map (kbd "C-c @ S") 'hs-show-all)
        (define-key map (kbd "C-c @ l") 'hs-hide-level)
        (define-key map (kbd "C-c @ c") 'hs-toggle-hiding)
        (define-key map [(shift mouse-2)] 'hs-mouse-toggle-hiding)
        map))

(defvar hs-headline-max-len 30 "*Maximum length of `hs-headline' to display.")
(defvar hs-overlay-map (make-sparse-keymap) "Keymap for hs minor mode overlay.")
(defvar hs-hide-all nil "Current state of hideshow for toggling all.")
(defvar fold-all-fun nil "Function to fold all.")
(defvar fold-fun nil "Function to fold.")

(defun hs-display-headline ()
  (let* ((len (length hs-headline))
         (headline hs-headline)
         (postfix ""))
    (when (>= len hs-headline-max-len)
      (setq postfix "...")
      (setq headline (substring hs-headline 0 hs-headline-max-len)))
    (if hs-headline (concat headline postfix " ") "")))

(defun hs-abstract-overlay (ov)
  (let* ((start (overlay-start ov))
         (end (overlay-end ov))
         (str (format "<%d lines>" (count-lines start end))) text)
    (setq text (propertize str 'face 'hs-block-flag-face 'help-echo (buffer-substring (1+ start) end)))
    (overlay-put ov 'display text)
    (overlay-put ov 'pointer 'hand)
    (overlay-put ov 'keymap hs-overlay-map)))

(defun hs-toggle-hiding-all ()
  "Toggle hideshow all."
  (interactive)
  (setq hs-hide-all (not hs-hide-all))
  (if hs-hide-all
      (hs-hide-all)
    (hs-show-all)))

(defun hs-toggle-fold-all ()
  "Toggle fold all."
  (interactive)
  (if fold-all-fun
      (call-interactively fold-all-fun)
    (hs-toggle-hiding-all)))

(defun hs-toggle-fold ()
  "Toggle fold."
  (interactive)
  (if fold-fun
      (call-interactively fold-fun)
    (hs-toggle-hiding)))

(eval-after-load "hideshow"
  '(progn
     (setq hs-isearch-open t)
     (setq-default mode-line-format
                   (append '((:eval (hs-display-headline))) mode-line-format))
     (setq hs-set-up-overlay 'hs-abstract-overlay)
     (make-local-variable 'hs-hide-all)
     (make-variable-buffer-local 'fold-all-fun)
     (make-variable-buffer-local 'fold-fun)

     (defadvice goto-line (after expand-after-goto-line activate compile)
       (save-excursion (hs-show-block)))

     (defadvice find-tag (after expand-after-find-tag activate compile)
       (save-excursion (hs-show-block)))
     ))

(provide 'init-hs-minor-mode)
