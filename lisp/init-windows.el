;; -*- coding: utf-8; lexical-binding: t; -*-

;; Navigate window layouts with "C-c <left>" and "C-c <right>"
(my-run-with-idle-timer 2 #'winner-mode)

;; @see https://emacs-china.org/t/emacs-builtin-mode/11937/63
;; press u undo and r to redo
(defun my-transient-winner-undo ()
  "Transient version of `winner-undo'."
  (interactive)
  (my-setup-extra-keymap '(("u" winner-undo)
                           ("r" winner-redo))
                         "Winner: [u]ndo [r]edo [q]uit"
                         'winner-undo))

(global-set-key (kbd "C-x 4 u") 'my-transient-winner-undo)

(global-set-key (kbd "C-x 2") 'split-window-vertically)
(global-set-key (kbd "C-x 3") 'split-window-horizontally)

(defun scroll-other-window-up ()
  "Scroll window up."
  (interactive)
  (scroll-other-window '-))

(defun my-toggle-two-split-window ()
  "Toggle two window layout vertically or horizontally."
  (interactive)
  (when (= (count-windows) 2)
    (let* ((this-win-buffer (window-buffer))
           (next-win-buffer (window-buffer (next-window)))
           (this-win-edges (window-edges (selected-window)))
           (next-win-edges (window-edges (next-window)))
           (this-win-2nd (not (and (<= (car this-win-edges)
                                       (car next-win-edges))
                                   (<= (cadr this-win-edges)
                                       (cadr next-win-edges)))))
           (splitter
            (if (= (car this-win-edges)
                   (car (window-edges (next-window))))
                'split-window-horizontally
              'split-window-vertically)))
      (delete-other-windows)
      (let* ((first-win (selected-window)))
        (funcall splitter)
        (if this-win-2nd (other-window 1))
        (set-window-buffer (selected-window) this-win-buffer)
        (set-window-buffer (next-window) next-win-buffer)
        (select-window first-win)
        (if this-win-2nd (other-window 1))))))

(defun my-rotate-windows ()
  "Rotate windows in clock-wise direction."
  (interactive)
  (cond
   ((not (> (count-windows)1))
    (message "You can't rotate a single window!"))
   (t
    (let* ((i 1)
           (num-windows (count-windows)))
      (while (< i num-windows)
        (let* ((w1 (elt (window-list) i))
               (w2 (elt (window-list) (+ (% i num-windows) 1)))

               (b1 (window-buffer w1))
               (b2 (window-buffer w2))

               (s1 (window-start w1))
               (s2 (window-start w2)))
          (set-window-buffer w1 b2)
          (set-window-buffer w2 b1)
          (set-window-start w1 s2)
          (set-window-start w2 s1)
          (setq i (1+ i))))))))

;; https://github.com/abo-abo/ace-window
;; `M-x ace-window ENTER m` to swap window
(global-set-key (kbd "C-x o") 'ace-window)

;; {{ move focus between sub-windows
(setq winum-keymap
    (let ((map (make-sparse-keymap)))
      (define-key map (kbd "M-0") 'winum-select-window-0-or-10)
      (define-key map (kbd "M-1") 'winum-select-window-1)
      (define-key map (kbd "M-2") 'winum-select-window-2)
      (define-key map (kbd "M-3") 'winum-select-window-3)
      (define-key map (kbd "M-4") 'winum-select-window-4)
      (define-key map (kbd "M-5") 'winum-select-window-5)
      (define-key map (kbd "M-6") 'winum-select-window-6)
      (define-key map (kbd "M-7") 'winum-select-window-7)
      (define-key map (kbd "M-8") 'winum-select-window-8)
      map))

(with-eval-after-load 'winum
  (setq winum-format "%s")
  (setq winum-mode-line-position 0)
  (set-face-attribute 'winum-face nil :foreground "DeepPink" :underline "DeepPink" :weight 'bold))
;; }}
(winum-mode 1)

(defun my-toggle-full-window()
  "Toggle full view of selected window."
  (interactive)
  ;; @see http://www.gnu.org/software/emacs/manual/html_node/elisp/Splitting-Windows.html
  (if (window-parent)
      (delete-other-windows)
    (winner-undo)))

(defun my-subwindow-setup ()
  "Setup subwindow"
  (interactive)
  (my-setup-extra-keymap '(("i" evil-window-increase-height)
                           ("d" evil-window-decrease-height)
                           ("b" balance-windows)
                           ("t" my-toggle-two-split-window)
                           ("k" (lambda () (interactive) (kill-buffer (current-buffer))))
                           ("r" my-rotate-windows))
                         "Window: [r]oate [t]oggle-split [i]ncrease [d]crease [b]alance [k]ill [q]uit"
                         nil))
(provide 'init-windows)
