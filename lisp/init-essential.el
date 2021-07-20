;; -*- coding: utf-8; lexical-binding: t; -*-

;; Like "init-misc.el", the difference is this file is always loaded

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
    (let* ((counsel-etags-convert-grep-keyword
            (lambda (keyword)
              (if (and keyword (> (length keyword) 0))
                  (my-pinyinlib-build-regexp-string keyword)
                keyword))))
      (counsel-etags-grep)))))

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

;; @see https://www.reddit.com/r/emacs/comments/988paa/emacs_on_windows_seems_lagging/
(unless *no-memory*
  ;; speed up font rendering for special characters
  (setq inhibit-compacting-font-caches t))

;; @see https://gist.github.com/mwfogleman/95cc60c87a9323876c6c
;; fixed to behave correctly in org-src buffers; taken from:
;; https://lists.gnu.org/archive/html/emacs-orgmode/2019-09/msg00094.html
(defun narrow-or-widen-dwim (&optional use-indirect-buffer)
  "If the buffer is narrowed, it widens.
 Otherwise, it narrows to region, or Org subtree.
If USE-INDIRECT-BUFFER is not nil, use `indirect-buffer' to hold the widen content."
  (interactive "P")
  (cond
   ((and (not use-indirect-buffer) (buffer-narrowed-p))
    (widen))

   ((and (not use-indirect-buffer)
         (eq major-mode 'org-mode)
         (fboundp 'org-src-edit-buffer-p)
         (org-src-edit-buffer-p))
    (org-edit-src-exit))

   ;; narrow to region
   ((region-active-p)
    (narrow-to-region-indirect-buffer-maybe (region-beginning)
                                            (region-end)
                                            use-indirect-buffer))

   ;; narrow to specific org element
   ((derived-mode-p 'org-mode)
    (cond
     ((ignore-errors (org-edit-src-code)) t)
     ((ignore-errors (org-narrow-to-block) t))
     ((ignore-errors (org-narrow-to-element) t))
     (t (org-narrow-to-subtree))))

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

(defun my-swiper (&optional other-source)
  "Search current file.
If OTHER-SOURCE is 1, get keyword from clipboard.
If OTHER-SOURCE is 2, get keyword from `kill-ring'."
  (interactive "P")
  (let* ((keyword (cond
                   ((eq 1 other-source)
                    (cliphist-select-item))
                   ((eq 2 other-source)
                    (my-select-from-kill-ring 'identity))
                   ((region-active-p)
                    (my-selected-str)))))
    ;; `swiper--re-builder' read from `ivy-re-builders-alist'
    ;; more flexible
    (swiper keyword)))

(defun my-swiper-hack (&optional arg)
  "Undo region selection before swiper.  ARG is ingored."
  (ignore arg)
  (if (region-active-p) (deactivate-mark)))
(advice-add 'swiper :before #'my-swiper-hack)

(with-eval-after-load 'shellcop
  (setq shellcop-string-search-function 'swiper))

(with-eval-after-load 'cliphist
  (defun cliphist-routine-before-insert-hack (&optional arg)
    (ignore arg)
    (my-delete-selected-region))
  (advice-add 'cliphist-routine-before-insert :before #'cliphist-routine-before-insert-hack))

;; {{ Write backup files to its own directory
;; @see https://www.gnu.org/software/emacs/manual/html_node/tramp/Auto_002dsave-and-Backup.html
(defvar my-binary-file-name-regexp
  "\\.\\(avi\\|wav\\|pdf\\|mp[34g]\\|mkv\\|exe\\|3gp\\|rmvb\\|rm\\|pyim\\|\\.recentf\\)$"
  "Is binary file name?")

(setq backup-enable-predicate
      (lambda (name)
        (and (normal-backup-enable-predicate name)
             (not (string-match-p my-binary-file-name-regexp name)))))

(let* ((backup-dir (expand-file-name "~/.backups")))
  (unless (file-exists-p backup-dir) (make-directory backup-dir))
  (setq backup-by-copying t ; don't clobber symlinks
        backup-directory-alist (list (cons "." backup-dir))
        delete-old-versions t
        version-control t  ;use versioned backups
        kept-new-versions 8
        kept-old-versions 4))

;; Donot make backups of files, not safe
;; @see https://github.com/joedicastro/dotfiles/tree/master/emacs
(setq vc-make-backup-files nil)
;; }}

(with-eval-after-load 'tramp
  (push (cons tramp-file-name-regexp nil) backup-directory-alist)

;; @see https://github.com/syl20bnr/spacemacs/issues/1921
;; If you tramp is hanging, you can uncomment below line.
;; (setq tramp-ssh-controlmaster-options "-o ControlMaster=auto -o ControlPath='tramp.%%C' -o ControlPersist=no")

  (setq tramp-chunksize 8192))


;; {{ GUI frames
;; Suppress GUI features
(setq use-file-dialog nil)
(setq use-dialog-box nil)
(setq inhibit-startup-screen t)
(setq inhibit-startup-echo-area-message t)

;; Show a marker in the left fringe for lines not in the buffer
(setq indicate-empty-lines t)

(defun my-mini-ui ()
  "Minimum ui."
  ;; NO tool bar, scroll-bar
  (when window-system
    (scroll-bar-mode -1)
    (tool-bar-mode -1)
    (horizontal-scroll-bar-mode -1)))
(my-run-with-idle-timer 2 #'my-mini-ui)
;; }}

;; no menu bar
(menu-bar-mode -1)

;; Nicer naming of buffers for files with identical names
(setq uniquify-buffer-name-style 'reverse)
(setq uniquify-separator " • ")
(setq uniquify-after-kill-buffer-p t)
(setq uniquify-ignore-buffers-re "^\\*")

(setq hippie-expand-try-functions-list
      '(try-complete-file-name-partially
        try-complete-file-name
        try-expand-dabbrev
        try-expand-dabbrev-all-buffers
        try-expand-dabbrev-from-kill))
(global-set-key (kbd "M-/") 'hippie-expand)

(defun my-compile (&optional arg)
  "Call `compile' command with ARG."
  (interactive "P")
  (when arg
    ;; prepare extra option and cc it to `kill-ring'
    (my-ensure 'which-func)
    (let* ((extra-opt (which-function)))
      (setq extra-opt (replace-regexp-in-string "tdd\\.it\\." "" extra-opt))

      (cond
       ;; jest unit test
       ((and buffer-file-name (string-match-p "\\.[tj]s$" buffer-file-name))
        (setq extra-opt (format " -t \"%s\" " extra-opt)))

       ;; do nothing
       (t
        (setq extra-opt (format "\"%s\" " extra-opt))))
      (if extra-opt (kill-new extra-opt))))
  (call-interactively 'compile))

;; {{ Diff two regions
;; Step 1: Select a region and `M-x diff-region-tag-selected-as-a'
;; Step 2: Select another region and `M-x diff-region-compare-with-b'
;; Press "q" in evil-mode or "C-c C-c" to exit the diff output buffer
(defun diff-region-format-region-boundary (b e)
  "Make sure lines are selected and B is less than E."
  (if (> b e) (cl-rotatef b e))

  ;; select lines
  (save-excursion
    ;; Another workaround for evil-visual-line bug:
    ;; In evil-mode, if we use hotkey V or `M-x evil-visual-line` to select line,
    ;; the (line-beginning-position) of the line which is after the last selected
    ;; line is always (region-end)! Don't know why.
    (when (and (> e b)
               (save-excursion (goto-char e) (= e (line-beginning-position)))
               (boundp 'evil-state) (eq evil-state 'visual))
      (setq e (1- e)))
    (goto-char b)
    (setq b (line-beginning-position))
    (goto-char e)
    (setq e (line-end-position)))
  (list b e))

(defmacro diff-region-open-diff-output (content buffer-name)
  "Insert CONTENT into a buffer named BUFFER-NAME."
  `(let ((rlt-buf (get-buffer-create ,buffer-name)))
    (save-current-buffer
      (switch-to-buffer-other-window rlt-buf)
      (set-buffer rlt-buf)
      (erase-buffer)
      (insert ,content)
      ;; `ffip-diff-mode' is more powerful than `diff-mode'
      (if (fboundp 'ffip-diff-mode) (ffip-diff-mode) (diff-mode))
      (goto-char (point-min)))))

(defun diff-region-tag-selected-as-a ()
  "Select a region to compare."
  (interactive)
  (cond
   ((region-active-p)
    (let* ((tmp (diff-region-format-region-boundary (region-beginning) (region-end)))
           (buf (get-buffer-create "*Diff-regionA*")))
      ;; select lines
      (save-current-buffer
        (set-buffer buf)
        (erase-buffer))
      (append-to-buffer buf (car tmp) (cadr tmp)))
    (message "Now select the other text to compare and run `diff-region-compare-with-b'"))

   (t
    (message "Please select the text first."))))

(defun diff-region-compare-with-b ()
  "Compare current region with region from `diff-region-tag-selected-as-a'.
If no region is selected, `kill-ring' or clipboard is used instead."
  (interactive)
  (let* (rlt-buf
         cmd
         diff-output
         tmp
         ;; file A
         (fa (make-temp-file (expand-file-name "diff-region"
                                               (or small-temporary-file-directory
                                                   temporary-file-directory))))
         ;; file B
         (fb (make-temp-file (expand-file-name "diff-region"
                                               (or small-temporary-file-directory
                                                   temporary-file-directory)))))
    (when (and fa (file-exists-p fa) fb (file-exists-p fb))
      (cond
       ((region-active-p)
        ;; text from selected region
        (setq tmp (diff-region-format-region-boundary (region-beginning) (region-end)))
        (write-region (car tmp) (cadr tmp) fb))

       (t
        ;; text from `kill-ring' or clipboard
        (let* ((choice (completing-read "Since no region selected, compare text in:"
                                        '("kill-ring" "clipboard")))
               (txt (cond
                     ((string= choice "kill-ring")
                      (car kill-ring))
                     ((string= choice "clipboard")
                      (my-gclip)))))
          (with-temp-file fb
            (insert txt)))))

      ;; save region A as file A
      (save-current-buffer
        (set-buffer (get-buffer-create "*Diff-regionA*"))
        (write-region (point-min) (point-max) fa))


      ;; diff NOW!
      ;; prepare diff command, I prefer "git diff" because it has more features
      (cond
       ((executable-find "git")
        (setq cmd (format "git diff --no-index --histogram --ignore-cr-at-eol -b -w -B \"%s\" \"%s\"" fa fb)))

       ((executable-find diff-command)
        (setq cmd (format "%s -u -b -w -B \"%s\" \"%s\"" diff-command fa fb))))

      (cond
       ((not cmd)
        (message "Please add git or diff into environment variable PATH first!"))

       ((string= (setq diff-output (shell-command-to-string cmd)) "")
        (message "Two regions are SAME!"))

       (t
        ;; show the diff output
        (diff-region-open-diff-output diff-output "*Diff-region-output*")))

      ;; clean the temporary files
      (if (and fa (file-exists-p fa)) (delete-file fa))
      (if (and fb (file-exists-p fb)) (delete-file fb)))))
;; }}

(provide 'init-essential)
