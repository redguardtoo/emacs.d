;; -*- coding: utf-8; lexical-binding: t; -*-

(defun copy-yank-str (msg &optional clipboard-only)
  (unless clipboard-only (kill-new msg))
  (my-pclip msg)
  msg)

(defun cp-filename-of-current-buffer (&optional n)
  "Copy file name (NOT full path) into the yank ring and OS clipboard.
If N is not nil, copy file name and line number."
  (interactive "P")
  (when buffer-file-name
    (let* ((filename (file-name-nondirectory buffer-file-name))
           (s (if n (format "%s:%s" filename (line-number-at-pos)) filename)))
      (copy-yank-str s)
      (message "%s => clipboard&kill-ring" s))))

(defun cp-fullpath-of-current-buffer ()
  "Copy full path into the yank ring and OS clipboard."
  (interactive)
  (when buffer-file-name
    (copy-yank-str (file-truename buffer-file-name))
    (message "file full path => clipboard & yank ring")))

(defun cp-root-relative-path-of-current-buffer ()
  "Copy path relative to the project root into the yank ring and OS clipboard"
  (interactive)
  (when buffer-file-name
    ;; require ffip to get project root
    (my-ensure 'find-file-in-project)
    (let* ((root (ffip-project-root))
           (file-path (file-truename buffer-file-name))
           relative-path)
      (cond
       ((not root)
        (message "Can't find project root."))

       ((not file-path)
        (message "File path of current buffer is empty."))

       (t
        (setq relative-path (file-relative-name file-path root))
        (copy-yank-str relative-path)
        (message "%s => clipboard & yank ring" relative-path))))))

(defun clipboard-to-kill-ring ()
  "Copy from clipboard to `kill-ring'."
  (interactive)
  (let* ((warning-minimum-level :emergency))
    (kill-new (my-gclip)))
  (message "clipboard => kill-ring"))

(defun kill-ring-to-clipboard ()
  "Copy from `kill-ring' to clipboard."
  (interactive)
  (my-select-from-kill-ring (lambda (s)
                              (let* ((summary (car s))
                                     (hint " => clipboard" )
                                     (msg (if (string-match "\.\.\.$" summary)
                                              (substring summary 0 (- (length summary) (length hint)))
                                            s)))
                                ;; cc actual string
                                (my-pclip (cdr s))
                                ;; echo
                                (message "%s%s" msg hint)))))

(defun copy-to-x-clipboard (&optional num)
  "If NUM equals 1, copy the down-cased string.
If NUM equals 2, copy the capitalized string.
If NUM equals 3, copy the up-cased string.
If NUM equals 4, indent 4 spaces."
  (interactive "P")
  (let* ((thing (my-use-selected-string-or-ask "")))
    (if (region-active-p) (deactivate-mark))
    (cond
     ((not num))
     ((= num 1)
      (setq thing (downcase thing)))
     ((= num 2)
      (setq thing (capitalize thing)))
     ((= num 3)
      (setq thing (upcase thing)))
     ((= num 4)
      (setq thing (string-trim-right (concat "    "
                                             (mapconcat 'identity (split-string thing "\n") "\n    ")))))
     (t
      (message "C-h f copy-to-x-clipboard to find right usage")))

    (my-pclip thing)
    (if (not (and num (= 4 num))) (message "kill-ring => clipboard")
      (message "thing => clipboard!"))))

(defun paste-from-x-clipboard(&optional n)
  "Remove selected text and paste string clipboard.
If N is 1, we paste diff hunk whose leading char should be removed.
If N is 2, paste into `kill-ring' too.
If N is 3, converted dashed to camel-cased then paste.
If N is 4, rectangle paste."
  (interactive "P")
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

    ;; past a big string, stop lsp temporarily
    (when (and (> (length str) 1024)
               (boundp 'lsp-mode)
               lsp-mode)
      (lsp-disconnect)
      (run-at-time 300 nil  #'lsp-deferred))

    (my-delete-selected-region)

    ;; paste after the cursor in evil normal state
    (cond
     ((not n)) ; do nothing
     ((= 1 n)
      (setq str (replace-regexp-in-string "^\\(+\\|-\\|@@ $\\)" "" str)))
     ((= 2 n)
      (kill-new str))
     ((= 3 n)
      (setq str (mapconcat (lambda (s) (capitalize s)) (split-string str "-") "")))
     ((= 4 n)
      (setq fn 'insert-rectangle)
      (setq str (split-string str "[\r]?\n"))))
    (funcall fn str)))

(provide 'init-clipboard)
