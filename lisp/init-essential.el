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
                                (file-name-base (file-name-nondirectory buffer-file-name)))))))

(defun my-grep-pinyin-in-current-directory ()
  "Grep pinyin in current directory."
  (interactive)
  ;; grep Chinese using pinyinlib.
  ;; In ivy filter, trigger key must be pressed before filter chinese
  (my-ensure 'counsel-etags)
  (let* ((counsel-etags-convert-grep-keyword
          (lambda (keyword)
            (cond
             ((> (length keyword) 0)
              (my-ensure 'pinyinlib)
              ;; only grep simplified Chinese
              (pinyinlib-build-regexp-string keyword t nil t))
             (t
              keyword)))))
    (counsel-etags-grep-current-directory)))

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
(defun my-narrow-or-widen-dwim (&optional use-indirect-buffer)
  "If the buffer is narrowed, it widens.
Otherwise, it narrows to region or Org subtree.
If USE-INDIRECT-BUFFER is t, use `indirect-buffer' to hold widen content."
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
  "Undo region selection before swiper.  ARG is ignored."
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
(setq backup-enable-predicate
      (lambda (file-name)
        (and (normal-backup-enable-predicate file-name)
             (not (my-binary-file-p file-name)))))

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
;; }}


;; Nicer naming of buffers for files with identical names
(with-eval-after-load 'uniquify
  (setq uniquify-buffer-name-style 'reverse)
  (setq uniquify-separator " • ")
  (setq uniquify-after-kill-buffer-p t)
  (setq uniquify-ignore-buffers-re "^\\*"))

(setq-default hippie-expand-try-functions-list
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
       ((and buffer-file-name (string-match "\\.[tj]s$" buffer-file-name))
        (setq extra-opt (format " -t \"%s\" " extra-opt)))

       ;; do nothing
       (t
        (setq extra-opt (format "\"%s\" " extra-opt))))
      (if extra-opt (kill-new extra-opt))))
  (call-interactively 'compile))

;; {{ eacl - emacs auto complete line(s)
(global-set-key (kbd "C-x C-l") 'eacl-complete-line-from-buffer-or-project)
(global-set-key (kbd "C-c C-l") 'eacl-complete-line-from-buffer)
(global-set-key (kbd "C-c C-;") 'eacl-complete-multiline)
(with-eval-after-load 'eacl
  ;; not interested in untracked files in git repository
  (setq eacl-git-grep-untracked nil))
;; }}

(defun my-switch-to-previous-buffer ()
  "Switch to previous buffer."
  (interactive)
  (switch-to-buffer nil))

(defun my-current-string-beginning ()
  "Goto current string's beginning."
  (interactive)
  (goto-char (car (my-create-range t))))

(defun my-current-string-end ()
  "Goto current string's end."
  (interactive)
  (goto-char (1- (cdr (my-create-range t)))))

(defun my-switch-to-shell ()
  "Switch to built in or 3rd party shell."
  (interactive)
  (cond
   ((or (display-graphic-p) (daemonp))
    (my-switch-to-builtin-shell))
   (t
    (suspend-frame))))

(global-set-key (kbd "C-x C-z") #'my-switch-to-shell)
(global-set-key (kbd "C-x C-m") 'execute-extended-command)

(defun my-save-current-buffer ()
  "Save current buffer (Dired, Grep, ...) to re-use in the future."
  (interactive)
  (let* ((file (read-file-name "Save buffer to file (its extension must be \"el\"): "))
         (content (buffer-string))
         (can-save-p t)
         (header (format "-*- mode:%s; default-directory: \"%s\" -*-\n"
                         (replace-regexp-in-string "-mode" "" (format "%s" major-mode))
                         default-directory)))
    (when file
      ;; double check file name extension
      (unless (equal (file-name-extension file) "el")
        (setq file (concat (file-name-base file) ".el")))

      (when (file-exists-p file)
        (setq can-save-p
              (yes-or-no-p (format "File %s exists.  Override it?" file))))
      (when can-save-p
        (with-temp-buffer
          (insert header)
          (insert content)
          ;; write buffer content into file
          (write-region (point-min) (point-max) file))))))

(with-eval-after-load 'flymake
  ;; if `flymake-no-changes-timeout' is nil, linting code ONLY after saving buffer.
  ;; This might speeds up Emacs if some some kind of auto-save package is used
  (setq flymake-no-changes-timeout 1))

(with-eval-after-load 'paren
  ;; better performance
  (setq show-paren-delay 0.5))

;; {{ Make emacs know ssh-agent
(unless *win64*
  ;; package exec-path-from-shell uses some Linux only cli tool
  (my-run-with-idle-timer 2
                          (lambda ()
                            (my-ensure 'exec-path-from-shell)
                            (setq exec-path-from-shell-check-startup-files nil)
                            (setq exec-path-from-shell-arguments nil)
                            (dolist (var '("SSH_AUTH_SOCK" "SSH_AGENT_PID" "GPG_AGENT_INFO" "LANG" "LC_CTYPE" "NIX_SSL_CERT_FILE" "NIX_PATH"))
                              (add-to-list 'exec-path-from-shell-variables var))
                            (exec-path-from-shell-initialize))))

;; }}

;; workaround gnupg 2.4 bug
;; @see https://emacs-china.org/t/gnupg-2-4-1-easypg/25264/7
(fset 'epg-wait-for-status 'ignore)

(with-eval-after-load 'ffap
  ;; @see https://www.reddit.com/r/emacs/comments/1gjlv1z/why_is_emacs_grep_command_pinging_external_servers/
  ;; better performance and security
  (setq ffap-machine-p-known 'reject))

(provide 'init-essential)

;; Local Variables:
;; byte-compile-warnings: (not free-vars)
;; End:

;;; init-essential.el ends here
