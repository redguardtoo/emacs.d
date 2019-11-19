;; -*- coding: utf-8; lexical-binding: t; -*-

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

(defun run-cmd-and-replace-region (cmd)
  "Run CMD in shell on selected region or whole buffer and replace it with cli output."
  (let* ((orig-point (point))
         (b (if (region-active-p) (region-beginning) (point-min)))
         (e (if (region-active-p) (region-end) (point-max))))
    (shell-command-on-region b e cmd nil t)
    (goto-char orig-point)))

(defun my-add-subdirs-to-load-path (my-lisp-dir)
  "Add sub-directories under MY-LISP-DIR into `load-path'."
  (let* ((default-directory my-lisp-dir))
    (setq load-path
          (append
           (delq nil
                 (mapcar (lambda (dir)
                           (unless (string-match-p "^\\." dir)
                             (expand-file-name dir)))
                         (directory-files "~/.emacs.d/site-lisp/")))
           load-path))))

;; {{ copied from http://ergoemacs.org/emacs/elisp_read_file_content.html
(defun get-string-from-file (file)
  "Return FILE's content."
  (with-temp-buffer
    (insert-file-contents file)
    (buffer-string)))

(defun read-lines (file)
  "Return a list of lines of FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (split-string (buffer-string) "\n" t)))
;; }}

(defun nonempty-lines (s)
  (split-string s "[\r\n]+" t))

;; Handier way to add modes to auto-mode-alist
(defun add-auto-mode (mode &rest patterns)
  "Add entries to `auto-mode-alist' to use `MODE' for all given file `PATTERNS'."
  (dolist (pattern patterns)
    (add-to-list 'auto-mode-alist (cons pattern mode))))


(defun font-belongs-to (pos fonts)
  "Current font at POS belongs to FONTS."
  (let* ((fontfaces (get-text-property pos 'face)))
    (when (not (listp fontfaces))
      (setf fontfaces (list fontfaces)))
    (delq nil
          (mapcar (lambda (f)
                    (member f fonts))
                  fontfaces))))

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

;; Find the directory containing a given library
(defun directory-of-library (library-name)
  "Return the directory in which the `LIBRARY-NAME' load file is found."
  (file-name-as-directory (file-name-directory (find-library-name library-name))))

(defun path-in-directory-p (file directory)
  "FILE is in DIRECTORY."
  (let* ((pattern (concat "^" (file-name-as-directory directory))))
    (if (string-match-p pattern file) file)))

(defun my-prepare-candidate-fit-into-screen (s)
  (let* ((w (frame-width))
         ;; display kill ring item in one line
         (key (replace-regexp-in-string "[ \t]*[\n\r]+[ \t]*" "\\\\n" s)))
    ;; strip the whitespace
    (setq key (replace-regexp-in-string "^[ \t]+" "" key))
    ;; fit to the minibuffer width
    (if (> (length key) w)
        (setq key (concat (substring key 0 (- w 4)) "...")))
    (cons key s)))

(defmacro my-select-from-kill-ring (fn)
  "If N > 1, yank the Nth item in `kill-ring'.
If N is nil, use `ivy-mode' to browse `kill-ring'."
  (interactive "P")
  `(let* ((candidates (cl-remove-if
                       (lambda (s)
                         (or (< (length s) 5)
                             (string-match-p "\\`[\n[:blank:]]+\\'" s)))
                       (delete-dups kill-ring)))
          (ivy-height (/ (frame-height) 2)))
     (ivy-read "Browse `kill-ring':"
               (mapcar #'my-prepare-candidate-fit-into-screen candidates)
               :action #',fn)))

(defun my-insert-str (str)
  "Insert STR into current buffer."
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
  (insert str)
  str)

(defun my-line-str (&optional line-end)
  (buffer-substring-no-properties (line-beginning-position)
                                  (if line-end line-end (line-end-position))))

(defun my-is-in-one-line (b e)
  (save-excursion
    (goto-char b)
    (and (<= (line-beginning-position) b)
         (<= e (line-end-position)))))

(defun my-buffer-str ()
  (buffer-substring-no-properties (point-min) (point-max)))

(defun my-selected-str ()
  (buffer-substring-no-properties (region-beginning) (region-end)))

(defun my-use-selected-string-or-ask (&optional hint)
  "Use selected region or ask user input for string."
  (if (region-active-p) (my-selected-str)
    (if (or (not hint) (string= "" hint)) (thing-at-point 'symbol)
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
  ;; 5000 lines
  (> (buffer-size) (* 5000 80)))

(defun file-too-big-p (file)
  (> (nth 7 (file-attributes file))
     (* 5000 64)))

(defvar force-buffer-file-temp-p nil)
(defun is-buffer-file-temp ()
  "If (buffer-file-name) is nil or a temp file or HTML file converted from org file."
  (interactive)
  (let* ((f (buffer-file-name)) (rlt t))
    (cond
     ((not load-user-customized-major-mode-hook)
      (setq rlt t))
     ((not f)
      ;; file does not exist at all
      ;; org-babel edit inline code block need calling hook
      (setq rlt nil))
     ((string= f cached-normal-file-full-path)
      (setq rlt nil))
     ((string-match (concat "^" temporary-file-directory) f)
      ;; file is create from temp directory
      (setq rlt t))
     ((and (string-match "\.html$" f)
           (file-exists-p (replace-regexp-in-string "\.html$" ".org" f)))
      ;; file is a html file exported from org-mode
      (setq rlt t))
     (force-buffer-file-temp-p
      (setq rlt t))
     (t
      (setq cached-normal-file-full-path f)
      (setq rlt nil)))
    rlt))

(defvar my-mplayer-extra-opts ""
  "Extra options for mplayer (ao or vo setup).  For example,
you can '(setq my-mplayer-extra-opts \"-ao alsa -vo vdpau\")'.")

(defun my-guess-mplayer-path ()
  (let* ((rlt "mplayer"))
    (cond
     (*is-a-mac* (setq rlt "mplayer -quiet"))
     (*linux*
      (setq rlt (format "mplayer -quiet -stop-xscreensaver %s" my-mplayer-extra-opts)))
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
  (let* ((rlt "mplayer"))
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
            (format "rundll32.exe %s\\\\System32\\\\\shimgvw.dll, ImageView_Fullscreen %s &"
                    (getenv "SystemRoot")
                    file))))
    rlt))

(defun my-gclip ()
  (let* ((powershell-program (executable-find "powershell.exe")))
    (cond
     ((and (memq system-type '(gnu gnu/linux gnu/kfreebsd))
           powershell-program)
      (string-trim-right
       (with-output-to-string
         (with-current-buffer standard-output
           (call-process powershell-program nil t nil "-command" "Get-Clipboard")))))
     (t
      (xclip-get-selection 'clipboard)))))

(defun my-pclip (str-val)
  (let* ((win64-clip-program (executable-find "clip.exe")))
    (cond
     ((and win64-clip-program (memq system-type '(gnu gnu/linux gnu/kfreebsd)))
      (with-temp-buffer
        (insert str-val)
        (call-process-region (point-min) (point-max) win64-clip-program)))
     (t
      (xclip-set-selection 'clipboard str-val)))))
;; }}

(defun should-use-minimum-resource ()
  (and buffer-file-name
       (string-match-p "\.\\(mock\\|min\\)\.js" buffer-file-name)))

(defun my-async-shell-command (command)
  "Execute string COMMAND asynchronously."
  (let* ((proc (start-process "Shell"
                              nil
                              shell-file-name
                              shell-command-switch command)))
    (set-process-sentinel proc `(lambda (process signal)
                                  (let* ((status (process-status process)))
                                    (when (memq status '(exit signal))
                                      (unless (string= (substring signal 0 -1) "finished")
                                        (message "Failed to run \"%s\"." ,command))))))))

;; {{ narrow region
(defun narrow-to-region-indirect-buffer-maybe (start end use-indirect-buffer)
  "Indirect buffer could multiple widen on same file."
  (if (region-active-p) (deactivate-mark))
  (if use-indirect-buffer
      (with-current-buffer (clone-indirect-buffer
                            (generate-new-buffer-name
                             (format "%s-indirect-:%s-:%s"
                                     (buffer-name)
                                     (line-number-at-pos start)
                                     (line-number-at-pos end)))
                            'display)
        (narrow-to-region start end)
        (goto-char (point-min)))
      (narrow-to-region start end)))

;; @see https://gist.github.com/mwfogleman/95cc60c87a9323876c6c
(defun narrow-or-widen-dwim (&optional use-indirect-buffer)
  "If the buffer is narrowed, it widens.
 Otherwise, it narrows to region, or Org subtree.
If use-indirect-buffer is not nil, use `indirect-buffer' to hold the widen content."
  (interactive "P")
  (cond ((buffer-narrowed-p) (widen))
        ((region-active-p)
         (narrow-to-region-indirect-buffer-maybe (region-beginning)
                                                 (region-end)
                                                 use-indirect-buffer))
        ((equal major-mode 'org-mode)
         (org-narrow-to-subtree))
        ((derived-mode-p 'diff-mode)
         (let* (b e)
           (save-excursion
             ;; If the (point) is already beginning or end of file diff,
             ;; the `diff-beginning-of-file' and `diff-end-of-file' return nil
             (setq b (progn (diff-beginning-of-file) (point)))
             (setq e (progn (diff-end-of-file) (point))))
           (when (and b e (< b e))
             (narrow-to-region-indirect-buffer-maybe b e use-indirect-buffer))))
        ((derived-mode-p 'prog-mode)
         (mark-defun)
         (narrow-to-region-indirect-buffer-maybe (region-beginning)
                                                 (region-end)
                                                 use-indirect-buffer))
        (t (error "Please select a region to narrow to"))))
;; }}

(defun my-multi-purpose-grep (n)
  "Run different grep from N."
  (interactive "P")
  (cond
   ((not n)
    (counsel-etags-grep))
   ((= n 1)
    ;; grep references of current web component
    ;; component could be inside styled-component like `const c = styled(Comp1)`
    (let* ((fb (file-name-base buffer-file-name)))
      (when (string= "index" fb)
        (setq fb (file-name-base (directory-file-name (file-name-directory (directory-file-name buffer-file-name))))))
        (counsel-etags-grep (format "(<%s( *$| [^ ])|styled\\\(%s\\))" fb fb))))
   ((= n 2)
    ;; grep web component attribute name
    (counsel-etags-grep (format "^ *%s[=:]" (or (thing-at-point 'symbol)
                                                (read-string "Component attribute name?")))))
   ((= n 3)
    ;; grep current file name
    (counsel-etags-grep (format ".*%s" (file-name-nondirectory buffer-file-name))))
   ((= n 4)
    ;; grep js files which is imported
    (counsel-etags-grep (format "from .*%s('|\\\.js');?"
                                (file-name-base (file-name-nondirectory buffer-file-name)))))
   ((= n 5)
    ;; grep Chinese using pinyinlib.
    ;; In ivy filter, trigger key must be pressed before filter chinese
    (unless (featurep 'pinyinlib) (require 'pinyinlib))
    (let* ((counsel-etags-convert-grep-keyword
            (lambda (keyword)
              (if (and keyword (> (length keyword) 0))
                  (pinyinlib-build-regexp-string keyword t)
                keyword))))
      (counsel-etags-grep)))))

;; {{ message buffer things
(defun erase-specific-buffer (num buf-name)
  (let* ((message-buffer (get-buffer buf-name))
         (old-buffer (current-buffer)))
    (save-excursion
      (if (buffer-live-p message-buffer)
          (progn
            (switch-to-buffer message-buffer)
            (if (not (null num))
                (progn
                  (end-of-buffer)
                  (dotimes (i num)
                    (previous-line))
                  (set-register t (buffer-substring (point) (point-max)))
                  (erase-buffer)
                  (insert (get-register t))
                  (switch-to-buffer old-buffer))
              (progn
                (erase-buffer)
                (switch-to-buffer old-buffer))))
        (error "Message buffer doesn't exists!")))))

(defun erase-message-buffer (&optional num)
  "Erase the content of the *Messages* buffer in emacs.
Keep the last num lines if argument num if given."
  (interactive "p")
  (erase-specific-buffer num "*Messages*"))

;; turn off read-only-mode in *Message* buffer, a "feature" in v24.4
(when (fboundp 'messages-buffer-mode)
  (defun messages-buffer-mode-hook-setup ()
    (message "messages-buffer-mode-hook-setup called")
    (read-only-mode -1))
  (add-hook 'messages-buffer-mode-hook 'messages-buffer-mode-hook-setup))
;; }}

;; reply y/n instead of yes/no
(fset 'yes-or-no-p 'y-or-n-p)

(provide 'init-utils)
