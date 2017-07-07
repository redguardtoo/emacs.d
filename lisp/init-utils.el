;; elisp version of try...catch...finally
(defmacro safe-wrap (fn &rest clean-up)
  `(unwind-protect
       (let (retval)
         (condition-case ex
             (setq retval (progn ,fn))
           ('error
            (message (format "Caught exception: [%s]" ex))
            (setq retval (cons 'exception (list ex)))))
         retval)
     ,@clean-up))

;; {{ copied from http://ergoemacs.org/emacs/elisp_read_file_content.html
(defun get-string-from-file (filePath)
  "Return filePath's file content."
  (with-temp-buffer
    (insert-file-contents filePath)
    (buffer-string)))

(defun read-lines (filePath)
  "Return a list of lines of a file at filePath."
  (with-temp-buffer
    (insert-file-contents filePath)
    (split-string (buffer-string) "\n" t)))
;; }}

;; Handier way to add modes to auto-mode-alist
(defun add-auto-mode (mode &rest patterns)
  "Add entries to `auto-mode-alist' to use `MODE' for all given file `PATTERNS'."
  (dolist (pattern patterns)
    (add-to-list 'auto-mode-alist (cons pattern mode))))


;;----------------------------------------------------------------------------
;; String utilities missing from core emacs
;;----------------------------------------------------------------------------
(defun string-all-matches (regex str &optional group)
  "Find all matches for `REGEX' within `STR', returning the full match string or group `GROUP'."
  (let ((result nil)
        (pos 0)
        (group (or group 0)))
    (while (string-match regex str pos)
      (push (match-string group str) result)
      (setq pos (match-end group)))
    result))

(defun string-rtrim (str)
  "Remove trailing whitespace from `STR'."
  (replace-regexp-in-string "[ \t\n]*$" "" str))

;; Find the directory containing a given library
(defun directory-of-library (library-name)
  "Return the directory in which the `LIBRARY-NAME' load file is found."
  (file-name-as-directory (file-name-directory (find-library-name library-name))))

(defmacro my-select-from-kill-ring (fn &optional n)
  "Use `browse-kill-ring' if it exists and N is 1.
If N > 1, assume just yank the Nth item in `kill-ring'.
If N is nil, use `ivy-mode' to browse the `kill-ring'."
  (interactive "P")
  `(cond
    ((or (not ,n) (and (= ,n 1) (not (fboundp 'browse-kill-ring))))
     ;; remove duplicates in `kill-ring'
     (let* ((candidates (cl-remove-if
                         (lambda (s)
                           (or (< (length s) 5)
                               (string-match "\\`[\n[:blank:]]+\\'" s)))
                         (delete-dups kill-ring))))
       (let* ((ivy-height (/ (frame-height) 2)))
         (ivy-read "Browse `kill-ring':"
                   (mapcar
                    (lambda (s)
                      (let* ((w (frame-width))
                             ;; display kill ring item in one line
                             (key (replace-regexp-in-string "[ \t]*[\n\r]+[ \t]*" "\\\\n" s)))
                        ;; strip the whitespace
                        (setq key (replace-regexp-in-string "^[ \t]+" "" key))
                        ;; fit to the minibuffer width
                        (if (> (length key) w)
                            (setq key (concat (substring key 0 (- w 4)) "...")))
                        (cons key s)))
                    candidates)
                   :action #',fn))))
    ((= ,n 1)
     (browse-kill-ring))))

(defun my-insert-str (str)
  ;; ivy8 or ivy9
  (if (consp str) (setq str (cdr str)))
  ;; evil-mode?
  (if (and (functionp 'evil-normal-state-p)
           (boundp 'evil-move-cursor-back)
           (evil-normal-state-p)
           (not (eolp))
           (not (eobp)))
      (forward-char))
  ;; insert now
  (insert str))

(defun my-line-str (&optional line-end)
  (buffer-substring-no-properties (line-beginning-position)
                                  (if line-end line-end (line-end-position))))

(defun my-buffer-str ()
  (buffer-substring-no-properties (point-min) (point-max)))

(defun my-selected-str ()
  (buffer-substring-no-properties (region-beginning) (region-end)))

(defun my-use-selected-string-or-ask (hint)
  "Use selected region or ask user input for string."
  (if (region-active-p) (my-selected-str)
    (if (string= "" hint) (thing-at-point 'symbol)
      (read-string hint))))

;; Delete the current file
(defun delete-this-file ()
  "Delete the current file, and kill the buffer."
  (interactive)
  (or (buffer-file-name) (error "No file is currently being edited"))
  (when (yes-or-no-p (format "Really delete '%s'?"
                             (file-name-nondirectory buffer-file-name)))
    (delete-file (buffer-file-name))
    (kill-this-buffer)))


;;----------------------------------------------------------------------------
;; Rename the current file
;;----------------------------------------------------------------------------
(defun rename-this-file-and-buffer (new-name)
  "Renames both current buffer and file it's visiting to NEW-NAME."
  (interactive "sNew name: ")
  (let ((name (buffer-name))
        (filename (buffer-file-name)))
    (unless filename
      (error "Buffer '%s' is not visiting a file!" name))
    (if (get-buffer new-name)
        (message "A buffer named '%s' already exists!" new-name)
      (progn
        (rename-file filename new-name 1)
        (rename-buffer new-name)
        (set-visited-file-name new-name)
        (set-buffer-modified-p nil)))))

;;----------------------------------------------------------------------------
;; Browse current HTML file
;;----------------------------------------------------------------------------
(defun browse-current-file ()
  "Open the current file as a URL using `browse-url'."
  (interactive)
  (browse-url-generic (concat "file://" (buffer-file-name))))


(require 'cl)

(defmacro with-selected-frame (frame &rest forms)
  (let ((prev-frame (gensym))
        (new-frame (gensym)))
    `(progn
       (let* ((,new-frame (or ,frame (selected-frame)))
              (,prev-frame (selected-frame)))
         (select-frame ,new-frame)
         (unwind-protect
             (progn ,@forms)
           (select-frame ,prev-frame))))))

(defvar load-user-customized-major-mode-hook t)
(defvar cached-normal-file-full-path nil)

(defun buffer-too-big-p ()
  (or (> (buffer-size) (* 5000 64))
      (> (line-number-at-pos (point-max)) 5000)))

(defun is-buffer-file-temp ()
  (interactive)
  "If (buffer-file-name) is nil or a temp file or HTML file converted from org file"
  (let ((f (buffer-file-name))
        org
        (rlt t))
    (cond
     ((not load-user-customized-major-mode-hook) t)
     ((not f)
      ;; file does not exist at all
      (setq rlt t))
     ((string= f cached-normal-file-full-path)
      (setq rlt nil))
     ((string-match (concat "^" temporary-file-directory) f)
      ;; file is create from temp directory
      (setq rlt t))
     ((and (string-match "\.html$" f)
           (file-exists-p (setq org (replace-regexp-in-string "\.html$" ".org" f))))
      ;; file is a html file exported from org-mode
      (setq rlt t))
     (t
      (setq cached-normal-file-full-path f)
      (setq rlt nil)))
    rlt))

(defun my-guess-mplayer-path ()
  (let* ((rlt "mplayer"))
    (cond
     (*is-a-mac* (setq rlt "mplayer -quiet"))
     (*linux* (setq rlt "mplayer -quiet -stop-xscreensaver"))
     (*cygwin*
      (if (file-executable-p "/cygdrive/c/mplayer/mplayer.exe")
          (setq rlt "/cygdrive/c/mplayer/mplayer.exe -quiet")
        (setq rlt "/cygdrive/d/mplayer/mplayer.exe -quiet")))
     (t ; windows
      (if (file-executable-p "c:\\\\mplayer\\\\mplayer.exe")
          (setq rlt "c:\\\\mplayer\\\\mplayer.exe -quiet")
        (setq rlt "d:\\\\mplayer\\\\mplayer.exe -quiet"))))
    rlt))

(defun my-guess-image-viewer-path (file &optional is-stream)
  (let ((rlt "mplayer"))
    (cond
     (*is-a-mac*
      (setq rlt
            (format "open %s &" file)))
     (*linux*
      (setq rlt
            (if is-stream (format "curl -L %s | feh -F - &" file) (format "feh -F %s &" file))))
     (*cygwin* (setq rlt "feh -F"))
     (t ; windows
      (setq rlt
            (format "rundll32.exe %SystemRoot%\\\\System32\\\\\shimgvw.dll, ImageView_Fullscreen %s &" file))))
    rlt))

;; {{ simpleclip has problem on Emacs 25.1
(defun test-simpleclip ()
  (unwind-protect
      (let (retval)
        (condition-case ex
            (progn
              (simpleclip-set-contents "testsimpleclip!")
              (setq retval
                    (string= "testsimpleclip!"
                             (simpleclip-get-contents))))
          ('error
           (message (format "Please install %s to support clipboard from terminal."
                            (cond
                             (*unix*
                              "xsel or xclip")
                             ((or *cygwin* *wind64*)
                              "cygutils-extra from Cygwin")
                             (t
                              "CLI clipboard tools"))))
           (setq retval nil)))
        retval)))

(setq simpleclip-works (test-simpleclip) )

(defun my-gclip ()
  (if simpleclip-works (simpleclip-get-contents)
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
          (call-process "xsel" nil t nil "--clipboard" "--output")))))))

(defun my-pclip (str-val)
  (if simpleclip-works (simpleclip-set-contents str-val)
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
        (call-process-region (point-min) (point-max) "xsel" nil nil nil "--clipboard" "--input"))))))
;; }}

(defun make-concated-string-from-clipboard (concat-char)
  (let* ((str (replace-regexp-in-string "'" "" (upcase (my-gclip))))
         (rlt (replace-regexp-in-string "[ ,-:]+" concat-char str)))
    rlt))

;; {{ diff region SDK
(defun diff-region-exit-from-certain-buffer (buffer-name)
  (bury-buffer buffer-name)
  (winner-undo))

(defmacro diff-region-open-diff-output (content buffer-name)
  `(let ((rlt-buf (get-buffer-create ,buffer-name)))
    (save-current-buffer
      (switch-to-buffer-other-window rlt-buf)
      (set-buffer rlt-buf)
      (erase-buffer)
      (insert ,content)
      ;; `ffip-diff-mode' is more powerful than `diff-mode'
      (ffip-diff-mode)
      (goto-char (point-min))
      ;; Evil keybinding
      (if (fboundp 'evil-local-set-key)
          (evil-local-set-key 'normal "q"
                              (lambda ()
                                (interactive)
                                (diff-region-exit-from-certain-buffer ,buffer-name))))
      ;; Emacs key binding
      (local-set-key (kbd "C-c C-c")
                     (lambda ()
                       (interactive)
                       (diff-region-exit-from-certain-buffer ,buffer-name)))
      )))

;; }}
(provide 'init-utils)
