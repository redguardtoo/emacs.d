;; -*- coding: utf-8; lexical-binding: t; -*-

(eval-after-load 'counsel
  '(progn
     ;; automatically pick up cygwin cli tools for counse
     (when *win64*
       (let* ((path (getenv "path"))
              (cygpath (or (and (file-exists-p "c:/cygwin64/bin") "c:/cygwin64/bin")
                           (and (file-exists-p "d:/cygwin64/bin") "d:/cygwin64/bin")
                           (and (file-exists-p "e:/cygwin64/bin") "e:/cygwin64/bin"))))
         ;; `cygpath' could be nil on Windows
         (when cygpath
           (unless (string-match-p cygpath counsel-git-cmd)

             (setq counsel-git-cmd (concat cygpath "/" counsel-git-cmd)))
           (unless (string-match-p cygpath counsel-git-grep-cmd-default)
             (setq counsel-git-grep-cmd-default (concat cygpath "/" counsel-git-grep-cmd-default)))
           ;; ;; git-log does not work
           ;; (unless (string-match-p cygpath counsel-git-log-cmd)
           ;;   (setq counsel-git-log-cmd (concat "GIT_PAGER="
           ;;                                     cygpath
           ;;                                     "/cat "
           ;;                                     cygpath
           ;;                                     "/git log --grep '%s'")))
           (unless (string-match-p cygpath counsel-grep-base-command)
             (setq counsel-grep-base-command (concat cygpath "/" counsel-grep-base-command))))))

     ;; @see https://oremacs.com/2015/07/23/ivy-multiaction/
     ;; press "M-o" to choose ivy action
     (ivy-set-actions
      'counsel-find-file
      '(("j" find-file-other-frame "other frame")
        ("b" counsel-find-file-cd-bookmark-action "cd bookmark")
        ("x" counsel-find-file-extern "open externally")
        ("d" delete-file "delete")
        ("r" counsel-find-file-as-root "open as root")))))

;; not good experience
;; (setq ivy-use-virtual-buffers t)
(global-set-key (kbd "C-c C-r") 'ivy-resume)
(global-set-key (kbd "C-x b") 'ivy-switch-buffer)

(define-key read-expression-map (kbd "C-r") 'counsel-expression-history)

;; {{ @see http://oremacs.com/2015/04/19/git-grep-ivy/
(defun counsel-read-keyword (hint &optional default-when-no-active-region)
  (let* (keyword)
    (cond
     ((region-active-p)
      (setq keyword (counsel-unquote-regex-parens (my-selected-str)))
      ;; de-select region
      (set-mark-command nil))
     (t
      (setq keyword (if default-when-no-active-region
                        default-when-no-active-region
                      (read-string hint)))))
    keyword))

(defun my-counsel-recentf (&optional n)
  "Find a file on `recentf-list'.
If N is not nil, only list files in current project."
  (interactive "P")
  (unless (featurep 'recentf) (require 'recentf))
  (recentf-mode 1)
  (let* ((files (mapcar #'substring-no-properties recentf-list))
         (root-dir (if (ffip-project-root) (file-truename (ffip-project-root)))))
    (when (and n root-dir)
      (setq files (delq nil (mapcar (lambda (f) (path-in-directory-p f root-dir)) files))))
    (ivy-read "Recentf: "
              files
              :initial-input (if (region-active-p) (my-selected-str))
              :action (lambda (f)
                        (with-ivy-window
                          (find-file f)))
              :caller 'counsel-recentf)))

(defmacro counsel-git-grep-or-find-api (fn git-cmd hint no-keyword)
  "Apply FN on the output lines of GIT-CMD.  HINT is hint when user input.
Yank the file name at the same time.  FILTER is function to filter the collection."
  `(let* ((str (if (buffer-file-name) (file-name-base (buffer-file-name)) ""))
          (default-directory (locate-dominating-file
                              default-directory ".git"))
          (keyword (unless ,no-keyword
                     ;; selected region contains no regular expression
                     (counsel-read-keyword (concat "Enter " ,hint " pattern:" ))))
          (collection (split-string (shell-command-to-string (if ,no-keyword ,git-cmd
                                                               (format ,git-cmd keyword)))
                                    "\n"
                                    t)))
     (cond
      ((and collection (= (length collection) 1))
       (funcall ,fn (car collection)))
      (t
       (ivy-read (if ,no-keyword ,hint (format "matching \"%s\":" keyword))
                 collection
                 :action ,fn)))))

(defun counsel--open-file (val)
  (let* ((lst (split-string val ":"))
         (linenum (string-to-number (cadr lst))))
    ;; open file
    (find-file (car lst))
    ;; goto line if line number exists
    (when (and linenum (> linenum 0))
      (goto-char (point-min))
      (forward-line (1- linenum)))))

;; grep by author is bad idea because it's too slow

(defun counsel-git-show-file ()
  "Find file in HEAD commit or whose commit hash is selected region."
  (interactive)
  (counsel-git-grep-or-find-api 'find-file
                                (format "git --no-pager diff-tree --no-commit-id --name-only -r %s"
                                        (counsel-read-keyword nil "HEAD"))
                                "files from `git-show' "
                                t))

(defun counsel-git-diff-file ()
  "Find file in `git diff'."
  (interactive)
  (counsel-git-grep-or-find-api 'find-file
                                "git --no-pager diff --name-only"
                                "files from `git-diff' "
                                t))

(defun counsel-insert-grepped-line (val)
  (let ((lst (split-string val ":")) text-line)
    ;; the actual text line could contain ":"
    (setq text-line (replace-regexp-in-string (format "^%s:%s:" (car lst) (nth 1 lst)) "" val))
    ;; trim the text line
    (setq text-line (replace-regexp-in-string (rx (* (any " \t\n")) eos) "" text-line))
    (kill-new text-line)
    (if insert-line (insert text-line))
    (message "line from %s:%s => kill-ring" (car lst) (nth 1 lst))))

(defun counsel--replace-current-line (leading-spaces content)
  (beginning-of-line)
  (kill-line)
  (insert (concat leading-spaces content))
  (end-of-line))

(defvar counsel-complete-line-use-git t)

(defun counsel-has-quick-grep ()
  (executable-find "rg"))

(defun counsel-find-quick-grep (&optional for-swiper)
  ;; ripgrep says that "-n" is enabled actually not,
  ;; so we manually add it
  (concat (executable-find "rg")
          " -n -M 128 --no-heading --color never "
          (if for-swiper "-i '%s' %s" "-s")))

(if (counsel-has-quick-grep)
    (setq counsel-grep-base-command (counsel-find-quick-grep t)))

(defvar counsel-my-name-regex ""
  "My name used by `counsel-git-find-my-file', support regex like '[Tt]om [Cc]hen'.")

(defun counsel-git-find-my-file (&optional num)
  "Find my files in the current git repository.
If NUM is not nil, find files since NUM weeks ago.
Or else, find files since 24 weeks (6 months) ago."
  (interactive"P")
  (unless (and num (> num 0))
    (setq num 24))
  (let* ((cmd (concat "git log --pretty=format: --name-only --since=\""
                      (number-to-string num)
                      " weeks ago\" --author=\""
                      counsel-my-name-regex
                      "\" | grep \"%s\" | sort | uniq")))
    ;; (message "cmd=%s" cmd)
    (counsel-git-grep-or-find-api 'find-file cmd "file" nil)))
;; }}

(defun counsel--build-bookmark-candidate (bookmark)
  (let (key)
    ;; build key which will be displayed
    (cond
     ((and (assoc 'filename bookmark) (cdr (assoc 'filename bookmark)))
      (setq key (format "%s (%s)" (car bookmark) (cdr (assoc 'filename bookmark)))))
     ((and (assoc 'location bookmark) (cdr (assoc 'location bookmark)))
      ;; bmkp-jump-w3m is from bookmark+
      (setq key (format "%s (%s)" (car bookmark) (cdr (assoc 'location bookmark)))))
     (t
      (setq key (car bookmark))))
    ;; re-shape the data so full bookmark be passed to ivy-read:action
    (cons key bookmark)))

(defun counsel-bookmark-goto ()
  "Open ANY bookmark.  Requires bookmark+"
  (interactive)
  (unless (featurep 'bookmark) (require 'bookmark))
  (bookmark-maybe-load-default-file)

  (let* ((bookmarks (and (boundp 'bookmark-alist) bookmark-alist))
         (collection (delq nil (mapcar #'counsel--build-bookmark-candidate
                                       bookmarks))))
    ;; do the real thing
    (ivy-read "bookmarks:"
              collection
              :action (lambda (bookmark)
                        (local-require 'bookmark+)
                        (bookmark-jump bookmark)))))

(defun counsel-yank-bash-history ()
  "Yank the bash history."
  (interactive)
  (shell-command "history -r") ; reload history
  (let* ((collection
          (nreverse
           (split-string (with-temp-buffer
                           (insert-file-contents (file-truename "~/.bash_history"))
                           (buffer-string))
                         "\n"
                         t))))
    (ivy-read (format "Bash history:") collection
              :action (lambda (val)
                        (kill-new val)
                        (message "%s => kill-ring" val)))))

(defun counsel-recent-directory (&optional n)
  "Goto recent directories.
If N is not nil, only list directories in current project."
  (interactive "P")
  (unless recentf-mode (recentf-mode 1))
  (let* ((cands (delete-dups
                 (append my-dired-directory-history
                         (mapcar 'file-name-directory recentf-list)
                         ;; fasd history
                         (if (executable-find "fasd")
                             (nonempty-lines (shell-command-to-string "fasd -ld"))))))
         (root-dir (if (ffip-project-root) (file-truename (ffip-project-root)))))
    (when (and n root-dir)
      (setq cands (delq nil (mapcar (lambda (f) (path-in-directory-p f root-dir)) cands))))
    (ivy-read "directories:" cands :action 'dired)))

(defun ivy-occur-grep-mode-hook-setup ()
  ;; no syntax highlight, I only care performance when searching/replacing
  (font-lock-mode -1)
  ;; @see https://emacs.stackexchange.com/questions/598/how-do-i-prevent-extremely-long-lines-making-emacs-slow
  (column-number-mode -1)
  ;; turn on wgrep right now
  ;; (ivy-wgrep-change-to-wgrep-mode) ; doesn't work, don't know why
  (local-set-key (kbd "RET") #'ivy-occur-press-and-switch))
(add-hook 'ivy-occur-grep-mode-hook 'ivy-occur-grep-mode-hook-setup)

(defun counsel-git-grep-by-selected ()
  (interactive)
  (cond
   ((region-active-p)
    (counsel-git-grep counsel-git-grep-cmd-default (my-selected-str)))
   (t
    (counsel-git-grep))))

(defun counsel-browse-kill-ring (&optional n)
  "If N > 1, assume just yank the Nth item in `kill-ring'.
If N is nil, use `ivy-mode' to browse `kill-ring'."
  (interactive "P")
  (my-select-from-kill-ring (lambda (s)
                              (let* ((plain-str (my-insert-str s))
                                     (trimmed (s-trim plain-str)))
                                (setq kill-ring (cl-delete-if
                                                 `(lambda (e) (string= ,trimmed (s-trim e)))
                                                 kill-ring))
                                (kill-new plain-str)))
                            n))

(defun ivy-switch-buffer-matcher-pinyin (regexp candidates)
  (unless (featurep 'pinyinlib) (require 'pinyinlib))
  (let* ((pys (split-string regexp "[ \t]+"))
         (regexp (format ".*%s.*"
                         (mapconcat 'pinyinlib-build-regexp-string pys ".*"))))
    (ivy--switch-buffer-matcher regexp candidates)))

(defun ivy-switch-buffer-by-pinyin ()
  "Switch to another buffer."
  (interactive)
  (unless (featurep 'ivy) (require 'ivy))
  (let ((this-command 'ivy-switch-buffer))
    (ivy-read "Switch to buffer: " 'internal-complete-buffer
              :matcher #'ivy-switch-buffer-matcher-pinyin
              :preselect (buffer-name (other-buffer (current-buffer)))
              :action #'ivy--switch-buffer-action
              :keymap ivy-switch-buffer-map
              :caller 'ivy-switch-buffer)))

(eval-after-load 'ivy
  '(progn
     ;; work around ivy issue.
     ;; @see https://github.com/abo-abo/swiper/issues/828
     (setq ivy-display-style 'fancy)))

;; {{ swiper&ivy-mode
(defun swiper-the-thing ()
  (interactive)
  ;; better performance on large files than swiper
  (counsel-grep-or-swiper (my-use-selected-string-or-ask "")))

(global-set-key (kbd "C-s") 'swiper)
;; }}

(global-set-key (kbd "C-h v") 'counsel-describe-variable)
(global-set-key (kbd "C-h f") 'counsel-describe-function)

;; better performance on everything (especially windows), ivy-0.10.0 required
;; @see https://github.com/abo-abo/swiper/issues/1218
(setq ivy-dynamic-exhibit-delay-ms 250)

;; Press C-p and Enter to select current input as candidate
;; https://oremacs.com/2017/11/30/ivy-0.10.0/
(setq ivy-use-selectable-prompt t)

;; {{ input ":" at first to start pinyin search in any ivy-related packages
(defvar ivy-pinyin-search-trigger-key ":")
;; @see https://emacs-china.org/t/topic/2432/3
(defun my-pinyinlib-build-regexp-string (str)
  (cond
   ((string= str ".*")
    ".*")
   (t
    (pinyinlib-build-regexp-string str t))))

(defun my-pinyin-regexp-helper (str)
  (cond
   ((string= str " ")
    ".*")
   ((string= str "")
    nil)
   (;; t
    str)))

(defun pinyin-to-utf8 (str)
  (when (and (> (length str) 0)
             (string= (substring str 0 1) ":"))
    (let* ((collection (split-string (replace-regexp-in-string ivy-pinyin-search-trigger-key
                                                               ""
                                                               str) "")))
      (unless (featurep 'pinyinlib) (require 'pinyinlib))
      (mapconcat 'my-pinyinlib-build-regexp-string
                 (delq nil (mapcar 'my-pinyin-regexp-helper
                                   collection))
                 ""))))

(defun re-builder-pinyin (str)
  (or (pinyin-to-utf8 str)
      (ivy--regex-plus str)))

(setq ivy-re-builders-alist
      '((t . re-builder-pinyin)))
;; }}

(eval-after-load 'ivy
  '(progn
     ;; set actions when running C-x b
     ;; replace "frame" with window to open in new window
     (ivy-set-actions
      'ivy-switch-buffer-by-pinyin
      '(("j" switch-to-buffer-other-frame "other frame")
        ("k" kill-buffer "kill")
        ("r" ivy--rename-buffer-action "rename")))))

(provide 'init-ivy)
