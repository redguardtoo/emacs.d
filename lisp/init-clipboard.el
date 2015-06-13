;; Use the system clipboard
(setq x-select-enable-clipboard t
      x-select-enable-primary t)

;; kill-ring and clipboard are same. It's annoying!
;; (setq save-interprogram-paste-before-kill t)

(autoload 'simpleclip-get-contents "simpleclip" "" t)
(autoload 'simpleclip-set-contents "simpleclip" "" t)

;; you need install xsel under Linux
;; xclip has some problem when copying under Linux
(defun copy-yank-str (msg &optional clipboard-only)
  (unless clipboard-only (kill-new msg))
  (simpleclip-set-contents msg))

(defun cp-filename-of-current-buffer ()
  "copy file name (NOT full path) into the yank ring and OS clipboard"
  (interactive)
  (let (filename)
    (when buffer-file-name
      (setq filename (file-name-nondirectory buffer-file-name))
      (copy-yank-str filename)
      (message "filename %s => clipboard & yank ring" filename))))

(defun cp-filename-line-number-of-current-buffer ()
  "copy file:line into the yank ring and clipboard"
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
  "copy full path into the yank ring and OS clipboard"
  (interactive)
  (when buffer-file-name
    (copy-yank-str (file-truename buffer-file-name))
    (message "file full path => clipboard & yank ring")))

(defun copy-to-x-clipboard ()
  (interactive)
  (let ((thing (if (region-active-p)
                   (buffer-substring-no-properties (region-beginning) (region-end))
                 (thing-at-point 'symbol))))
    (simpleclip-set-contents thing)
    (message "thing => clipboard!")))

(defun paste-from-x-clipboard()
  "Paste string clipboard"
  (interactive)
  (insert (simpleclip-get-contents)))

(defun my/paste-in-minibuffer ()
  (local-set-key (kbd "M-y") 'paste-from-x-clipboard))
(add-hook 'minibuffer-setup-hook 'my/paste-in-minibuffer)

(defun paste-from-clipboard-and-cc-kill-ring ()
  "paste from clipboard and cc the content into kill ring"
  (interactive)
  (let ((str (simpleclip-get-contents)))
    (insert str)
    ;; cc the content into kill ring at the same time
    (kill-new str)))

(defun latest-kill-to-clipboard ()
  (interactive)
  (copy-yank-str (current-kill 1) t))

(provide 'init-clipboard)
