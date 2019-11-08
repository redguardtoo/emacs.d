;; -*- coding: utf-8; lexical-binding: t; -*-

;; Use the system clipboard
;; @see https://www.emacswiki.org/emacs/CopyAndPaste
;; So `C-y' could paste from clipbord if you are NOT using emacs-nox
;; I only use `paste-from-x-clipboard', not `C-y'.
(setq x-select-enable-clipboard t
      x-select-enable-primary t)

;; kill-ring and clipboard are same? No, it's annoying!
(setq save-interprogram-paste-before-kill nil)

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

(defun cp-ffip-ivy-last ()
  "Copy visible keys of `ivy-last' into `kill-ring' and clipboard."
  (interactive)
  (unless (featurep 'find-file-in-project)
    (require 'find-file-in-project))
  (when ffip-ivy-last-saved
    (copy-yank-str
     (mapconcat (lambda (e)
                  (format "%S" (if (consp e) (car e) e)))
                (ivy-state-collection ffip-ivy-last-saved)
                "\n"))
    (message "%d items from ivy-last => clipboard & yank ring" (length ivy-last))))

(defun cp-fullpath-of-current-buffer ()
  "Copy full path into the yank ring and OS clipboard"
  (interactive)
  (when buffer-file-name
    (copy-yank-str (file-truename buffer-file-name))
    (message "file full path => clipboard & yank ring")))

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
                                     (msg (if (string-match-p "\.\.\.$" summary)
                                              (substring summary 0 (- (length summary) (length hint)))
                                            msg)))
                                ;; cc actual string
                                (my-pclip (cdr s))
                                ;; echo
                                (message "%s%s" msg hint)))))

(defun copy-to-x-clipboard (&optional num)
  "If NUM equals 1, copy the downcased string.
If NUM equals 2, copy the captalized string.
If NUM equals 3, copy the upcased string.
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
  "Paste string clipboard.
If N is 1, we paste diff hunk whose leading char should be removed.
If N is 2, paste into `kill-ring' too.
If N is 3, converted dashed to camelcased then paste.
If N is 4, rectangle paste. "
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
      (when (derived-mode-p 'js2-mode)
        (js-mode 1))
      ;; turn off syntax highlight
      (font-lock-mode -1))

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
