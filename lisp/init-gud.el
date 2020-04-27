;; -*- coding: utf-8; lexical-binding: t; -*-

(defvar gud-overlay
  (let* ((ov (make-overlay (point-min) (point-min))))
    (overlay-put ov 'face 'secondary-selection)
    ov)
  "Overlay variable for GUD highlighting.")

(defadvice gud-display-line (after my-gud-highlight activate)
  "Highlight current line."
  (let* ((ov gud-overlay)
         (bf (gud-find-file true-file)))
    (with-current-buffer bf
      (move-overlay ov (line-beginning-position) (line-beginning-position 2)
                    (current-buffer)))))

(defun gud-kill-buffer ()
  (if (derived-mode-p 'gud-mode)
      (delete-overlay gud-overlay)))

(add-hook 'kill-buffer-hook 'gud-kill-buffer)

;; {{ hack buffer
;; move the cursor to the end of last line if it's gud-mode
(defun hack-gud-mode ()
  (when (string= major-mode "gud-mode")
    (goto-char (point-max))))

(defadvice switch-to-buffer (after switch-to-buffer-after activate)
  (hack-gud-mode))

(defadvice select-window-by-number (after select-window-by-number-after activate)
  (hack-gud-mode))

;; windmove-do-window-select is from windmove.el
(defadvice windmove-do-window-select (after windmove-do-window-select-after activate)
  (hack-gud-mode))
;; }}

(with-eval-after-load 'gud
  (gud-def gud-kill "kill" "\C-k" "Kill the debugee"))

(defun gud-kill-yes ()
  "gud-kill and confirm with y."
  (interactive)
  (let ((old-window (selected-window)))
    (save-excursion
      (cond
       ((buffer-live-p (get-buffer "*gud-main*"))
        (gud-kill nil)
        (select-window (get-buffer-window "*gud-main*"))
        (insert "y")
        (comint-send-input)
        (recenter-top-bottom)
        (select-window old-window))
       (t (error "GUD buffer doesn't exist!"))))))

(provide 'init-gud)
