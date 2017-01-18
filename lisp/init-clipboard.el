;; Use the system clipboard
(setq x-select-enable-clipboard t
      x-select-enable-primary t)

;; kill-ring and clipboard are same? No, it's annoying!
;; (setq save-interprogram-paste-before-kill t)

(defun test-simpleclip ()
  (simpleclip-set-contents "testsimpleclip!")
  (string= "testsimpleclip!" (simpleclip-get-contents)))

(setq simpleclip-works (test-simpleclip))

;; you need install xsel under Linux
;; xclip has some problem when copying under Linux
(defun copy-yank-str (msg &optional clipboard-only)
  (unless clipboard-only (kill-new msg))
  (if simpleclip-works (simpleclip-set-contents msg)
    (my-pclip-fallback msg)))

(defun cp-filename-of-current-buffer () "Copy file name (NOT full path) into the yank ring and OS clipboard."
  (interactive)
  (when buffer-file-name
    (let* ((filename (file-name-nondirectory buffer-file-name)))
      (copy-yank-str filename)
      (message "filename %s => clipboard & yank ring" filename))))

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

(defun cp-filename-line-number-of-current-buffer ()
  "Copy file:line into the yank ring and clipboard"
  (interactive)
  (when buffer-file-name
    (let* ((filename (file-name-nondirectory buffer-file-name))
           (linenum (save-restriction
                      (widen)
                      (save-excursion
                        (beginning-of-line)
                        (1+ (count-lines 1 (point))))))
           (rlt (format "%s:%d" filename linenum)))
      (copy-yank-str rlt)
      (message "%s => clipboard & yank ring" rlt))))

(defun cp-fullpath-of-current-buffer ()
  "Copy full path into the yank ring and OS clipboard"
  (interactive)
  (when buffer-file-name
    (copy-yank-str (file-truename buffer-file-name))
    (message "file full path => clipboard & yank ring")))

(defun my-gclip-fallback ()
  (cond
   ((eq system-type 'darwin)
    (with-output-to-string
      (with-current-buffer standard-output
        (call-process "/usr/bin/pbpaste" nil t nil "-Prefer" "txt"))))
   ((eq system-type 'cygwin)
    (with-output-to-string
      (with-current-buffer standard-output
        (call-process "getclip" nil t nil))))
   ((memq system-type '(gnu gnu/linux gnu/kfreebsd))
    (with-output-to-string
      (with-current-buffer standard-output
        (call-process "xsel" nil t nil "--clipboard" "--output"))))
   (t
    (error "Clipboard support not available"))))

(defun my-pclip-fallback (str-val)
  (cond
   ((eq system-type 'darwin)
    (with-temp-buffer
      (insert str-val)
      (call-process-region (point-min) (point-max) "/usr/bin/pbcopy")))
   ((eq system-type 'cygwin)
    (with-temp-buffer
      (insert str-val)
      (call-process-region (point-min) (point-max) "putclip")))
   ((memq system-type '(gnu gnu/linux gnu/kfreebsd))
    (with-temp-buffer
      (insert str-val)
      (call-process-region (point-min) (point-max) "xsel" nil nil nil "--clipboard" "--input")))
   (t
    (error "Clipboard support not available"))))

(defun copy-to-x-clipboard (&optional num)
  "If NUM equals 1, copy the downcased string.
If NUM equals 2, copy the captalized string.
If NUM equals 3, copy the upcased string.
If NUM equals 4, kill-ring => clipboard."
  (interactive "P")
  (let* ((thing (my-use-selected-string-or-ask "")))
    (if (region-active-p) (push-mark))
    (cond
     ((not num))
     ((= num 1)
      (setq thing (downcase thing)))
     ((= num 2)
      (setq thing (capitalize thing)))
     ((= num 3)
      (setq thing (upcase thing)))
     ((= num 4)
      (setq thing (car kill-ring)))
     (t
      (message "C-h f copy-to-x-clipboard to find right usage")))

    (if simpleclip-works (simpleclip-set-contents thing)
      (my-pclip-fallback thing))
    (if (not (and num (= 4 num))) (message "kill-ring => clipboard")
      (message "thing => clipboard!"))))

(defun paste-from-x-clipboard(&optional n)
  "Paste string clipboard.
If N is 1, we paste diff hunk whose leading char should be removed.
If N is 2, paste into kill-ring too.
If N is 3, converted dashed to camelcased then paste."
  (interactive "P")
  ;; paste after the cursor in evil normal state
  (when (and (functionp 'evil-normal-state-p)
             (functionp 'evil-move-cursor-back)
             (evil-normal-state-p)
             (not (eolp))
             (not (eobp)))
    (forward-char))
  (let* ((str (if simpleclip-works (simpleclip-get-contents) (my-gclip-fallback))))
    (cond
     ((not n)
      ;; do nothing
      )
     ((= 1 n)
      (setq str (replace-regexp-in-string "^\\(+\\|-.*\\|@@ .*$\\)" "" str)))
     ((= 2 n)
      (kill-new str))
     ((= 3 n)
      (setq str (mapconcat (lambda (s) (capitalize s)) (split-string str "-") ""))))
    (insert str)))

(provide 'init-clipboard)