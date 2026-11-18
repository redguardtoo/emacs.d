;; -*- coding: utf-8; lexical-binding: t; -*-

;;; Code:

(defun my-copy-yank-str (msg &optional clipboard-only)
  "Copy and yank MSG with CLIPBOARD-ONLY."
  (unless clipboard-only (kill-new msg))
  (my-pclip msg)
  msg)

(defvar my-short-introduction-of-file
  "Full source of \"%s\" is as below,\n\n%s\n\n")

(defun cp-filename-and-content-of-current-buffer (&optional n)
  "Copy file name and its content into yank ring and clipboard.
If N is not nil, copy file path and its content instead."
  (interactive "P")
  (when buffer-file-name
    (let* ((filename (if n buffer-file-name
                       (file-name-nondirectory buffer-file-name))) )
      (my-copy-yank-str (format my-short-introduction-of-file
                             filename
                             (buffer-string)))
      (message "%s and its content => clipboard&kill-ring" filename))))

(defun cp-filename-of-current-buffer (&optional n)
  "Copy file name (NOT full path) into yank ring and clipboard.
If N is not nil, copy file name and line number."
  (interactive "P")
  (when buffer-file-name
    (let* ((filename (file-name-nondirectory buffer-file-name))
           (s (if n (format "%s:%s" filename (line-number-at-pos)) filename)))
      (my-copy-yank-str s)
      (message "%s => clipboard&kill-ring" s))))

(defun cp-fullpath-of-current-buffer ()
  "Copy full path into the yank ring and OS clipboard."
  (interactive)
  (when buffer-file-name
    (my-copy-yank-str (file-truename buffer-file-name))
    (message "file full path => clipboard & yank ring")))

(defun cp-root-relative-path-of-current-buffer ()
  "Copy path relative to the project root into yank ring and clipboard."
  (interactive)
  (when buffer-file-name
    ;; require ffip to get project root
    (my-ensure 'find-file-in-project)
    (my-ensure 'project)
    (let* ((root (ffip-project-root))
           (file-path (file-truename buffer-file-name))
           relative-path)
      (cond
       ((not root)
        (message "Can't find project root."))

       (t
        (setq relative-path (file-relative-name file-path root))
        (my-copy-yank-str relative-path)
        (message "%s => clipboard & yank ring" relative-path))))))

(defun my-kill-ring-to-clipboard ()
  "Copy from `kill-ring' to clipboard."
  (interactive)
  (my-select-from-kill-ring (lambda (s)
                              (let* ((summary (car s))
                                     (hint " => clipboard" )
                                     (msg (if (string-match "\\.\\.\\.$" summary)
                                              (substring summary 0 (- (length summary) (length hint)))
                                            s)))
                                ;; cc actual string
                                (my-pclip (cdr s))
                                ;; echo
                                (message "%s%s" msg hint)))))

(defun copy-to-x-clipboard ()
  "Copy text to clipboard."
  (interactive)
  (let* ((thing (my-use-selected-string-or-ask "")))
    (if (region-active-p) (deactivate-mark))
    (my-pclip thing)
    (message "thing => clipboard!")))

(defun paste-from-x-clipboard()
  "Remove selected text and paste string clipboard."
  (interactive)
  (when (and (functionp 'evil-normal-state-p)
             (functionp 'evil-move-cursor-back)
             (evil-normal-state-p)
             (not (eolp))
             (not (eobp)))
    (forward-char))
  (let* ((str (my-gclip))
         (fn 'insert))

    (when (> (length str) (* 256 1024))
      ;; use light weight `major-mode' like `js-mode'
      (when (derived-mode-p 'js2-mode) (js-mode))
      ;; turn off syntax highlight
      (font-lock-mode -1))

    (my-delete-selected-region)
    (funcall fn str)))

(provide 'init-clipboard)
;;; init-clipboard.el ends here
