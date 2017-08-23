;; {{ @see http://emacs-journey.blogspot.com.au/2012/06/improving-ansi-term.html
;; kill the buffer when terminal is exited
(defadvice term-sentinel (around my-advice-term-sentinel (proc msg))
  (if (memq (process-status proc) '(signal exit))
      (let ((buffer (process-buffer proc)))
        ad-do-it
        (kill-buffer buffer))
    ad-do-it))
(ad-activate 'term-sentinel)

;; always use bash
(defvar my-term-shell "/bin/bash")
(defadvice ansi-term (before force-bash)
  (interactive (list my-term-shell)))
(ad-activate 'ansi-term)

;; utf8
(defun my-term-use-utf8 ()
  (set-buffer-process-coding-system 'utf-8-unix 'utf-8-unix))
(add-hook 'term-exec-hook 'my-term-use-utf8)

;; }}

;; {{ multi-term
(defun last-term-buffer (l)
  "Return most recently used term buffer."
  (when l
    (if (eq 'term-mode (with-current-buffer (car l) major-mode))
        (car l) (last-term-buffer (cdr l)))))

(defun get-term ()
  "Switch to the term buffer last used, or create a new one if
    none exists, or if the current buffer is already a term."
  (interactive)
  (let ((b (last-term-buffer (buffer-list))))
    (if (or (not b) (eq 'term-mode major-mode))
        (multi-term)
      (switch-to-buffer b))))

(defun term-send-kill-whole-line ()
  "Kill whole line in term mode."
  (interactive)
  (term-send-raw-string "\C-a")
  (term-send-raw-string "\C-k"))

(defun term-send-kill-line ()
  "Kill line in term mode."
  (interactive)
  (term-send-raw-string "\C-k"))

(setq multi-term-program "/bin/bash")
;; check `term-bind-key-alist' for key bindings
(eval-after-load 'multi-term
  '(progn
     (dolist (p '(("C-p" . term-send-up)
                  ("C-n" . term-send-down)
                  ("C-s" . swiper)
                  ("C-r" . term-send-reverse-search-history)
                  ("C-m" . term-send-raw)
                  ("C-k" . term-send-kill-whole-line)
                  ("C-y" . yank)
                  ("C-_" . term-send-raw)
                  ("M-f" . term-send-forward-word)
                  ("M-b" . term-send-backward-word)
                  ("M-K" . term-send-kill-line)
                  ("M-p" . previous-line)
                  ("M-n" . next-line)
                  ("M-y" . yank-pop)
                  ("M-." . term-send-raw-meta)))
       (setq term-bind-key-alist (delq (assoc (car p) term-bind-key-alist) term-bind-key-alist))
       (add-to-list 'term-bind-key-alist p))))
;; }}

(provide 'init-term-mode)
