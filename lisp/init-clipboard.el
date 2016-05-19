;; Use the system clipboard
(setq x-select-enable-clipboard t
      x-select-enable-primary t)

;; kill-ring and clipboard are same? No, it's annoying!
;; (setq save-interprogram-paste-before-kill t)

(autoload 'simpleclip-get-contents "simpleclip" "" t)
(autoload 'simpleclip-set-contents "simpleclip" "" t)

;; you need install xsel under Linux
;; xclip has some problem when copying under Linux
(defun copy-yank-str (msg &optional clipboard-only)
  (unless clipboard-only (kill-new msg))
  (simpleclip-set-contents msg))

(defun cp-filename-of-current-buffer ()
  "Copy file name (NOT full path) into the yank ring and OS clipboard"
  (interactive)
  (let (filename)
    (when buffer-file-name
      (setq filename (file-name-nondirectory buffer-file-name))
      (copy-yank-str filename)
      (message "filename %s => clipboard & yank ring" filename))))

(defun cp-filename-line-number-of-current-buffer ()
  "Copy file:line into the yank ring and clipboard"
  (interactive)
  (let (filename linenum rlt)
    (when buffer-file-name
      (setq filename (file-name-nondirectory buffer-file-name))
      (setq linenum (save-restriction
                      (widen)
                      (save-excursion
                        (beginning-of-line)
                        (1+ (count-lines 1 (point))))))
      (setq rlt (format "%s:%d" filename linenum))
      (copy-yank-str rlt)
      (message "%s => clipboard & yank ring" rlt))))

(defun cp-fullpath-of-current-buffer ()
  "Copy full path into the yank ring and OS clipboard"
  (interactive)
  (when buffer-file-name
    (copy-yank-str (file-truename buffer-file-name))
    (message "file full path => clipboard & yank ring")))

(defun copy-to-x-clipboard (&optional num)
  "If NUM equals 1, copy the downcased string.
If NUM equals 2, copy the captalized string.
If NUM equals 3, copy the upcased string."
  (interactive "P")
  (let ((thing (if (region-active-p)
                   (buffer-substring-no-properties (region-beginning) (region-end))
                 (thing-at-point 'symbol))))
    (cond
     ((not num))
     ((= num 1)
      (setq thing (downcase thing)))
     ((= num 2)
      (setq thing (capitalize thing)))
     ((= num 3)
      (setq thing (upcase thing)))
     (t
      (message "C-h f copy-to-x-clipboard to find right usage")))

    (simpleclip-set-contents thing)
    (message "thing => clipboard!")))

(defun paste-from-x-clipboard()
  "Paste string clipboard"
  (interactive)
  ;; paste after the cursor in evil normal state
  (when (and (functionp 'evil-normal-state-p)
             (functionp 'evil-move-cursor-back)
             (evil-normal-state-p)
             (not (eolp))
             (not (eobp)))
      (forward-char))
  (insert (simpleclip-get-contents)))

(defun paste-from-clipboard-and-cc-kill-ring ()
  "Paste from clipboard and cc the content into kill ring"
  (interactive)
  (let ((str (simpleclip-get-contents)))
    (insert str)
    ;; cc the content into kill ring at the same time
    (kill-new str)))

(defun latest-kill-to-clipboard ()
  (interactive)
  (copy-yank-str (current-kill 1) t))

(provide 'init-clipboard)