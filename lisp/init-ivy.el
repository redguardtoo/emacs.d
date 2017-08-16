(require 'counsel)
;; (ivy-mode 1)
;; not good experience
;; (setq ivy-use-virtual-buffers t)
(global-set-key (kbd "C-c C-r") 'ivy-resume)
(global-set-key (kbd "C-x b") 'ivy-switch-buffer)

(define-key read-expression-map (kbd "C-r") 'counsel-expression-history)

;; {{ @see http://oremacs.com/2015/04/19/git-grep-ivy/
(defun counsel-read-keyword (hint &optional default-when-no-active-region)
  (let (keyword)
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

(defmacro counsel-git-grep-or-find-api (fn git-cmd hint no-keyword)
  "Apply FN on the output lines of GIT-CMD.  HINT is hint when user input.
Yank the file name at the same time.  FILTER is function to filter the collection"
  `(let* ((str (if (buffer-file-name) (file-name-base (buffer-file-name)) ""))
          (default-directory (locate-dominating-file
                              default-directory ".git"))
          collection)

     (unless ,no-keyword
       ;; selected region contains no regular expression
       (setq keyword (counsel-read-keyword (concat "Enter " ,hint " pattern:" ))))

     (setq collection
           (split-string (shell-command-to-string (if ,no-keyword ,git-cmd
                                                    (format ,git-cmd keyword)))
                         "\n"
                         t))
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
          " -n -M 256 --no-heading --color never "
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

  (unless (featurep 'bookmark)
    (require 'bookmark))
  (bookmark-maybe-load-default-file)

  (let* ((bookmarks (and (boundp 'bookmark-alist) bookmark-alist))
         (collection (delq nil (mapcar #'counsel--build-bookmark-candidate
                                       bookmarks))))
    ;; do the real thing
    (ivy-read "bookmarks:"
              collection
              :action (lambda (bookmark)
                        (unless (featurep 'bookmark+)
                          (require 'bookmark+))
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

(defun counsel-goto-recent-directory ()
  "Goto recent directories."
  (interactive)
  (unless recentf-mode (recentf-mode 1))
  (let* ((collection (delete-dups
                      (append (mapcar 'file-name-directory recentf-list)
                              ;; fasd history
                              (if (executable-find "fasd")
                                  (split-string (shell-command-to-string "fasd -ld") "\n" t))))))
    (ivy-read "directories:" collection :action 'dired)))


;; {{ ag/grep
(defvar my-grep-ignore-dirs
  '(".git"
    ".bzr"
    ".svn"
    "bower_components"
    "node_modules"
    ".sass-cache"
    ".cache"
    "test"
    "tests"
    ".metadata"
    "logs")
  "Directories to ignore when grepping.")
(defvar my-grep-ignore-file-exts
  '("log"
    "properties"
    "session"
    "swp")
  "File extensions to ignore when grepping.")
(defvar my-grep-ignore-file-names
  '("TAGS"
    "tags"
    "GTAGS"
    "GPATH"
    ".bookmarks.el"
    "*.svg"
    "history"
    "#*#"
    "*.min.js"
    "*bundle*.js"
    "*vendor*.js"
    "*.min.css"
    "*~")
  "File names to ignore when grepping.")

(defvar my-grep-opts-cache '())

(defun my-grep-exclude-opts (use-cache)
  ;; (message "my-grep-exclude-opts called => %s" use-cache)
  (let* ((ignore-dirs (if use-cache (plist-get my-grep-opts-cache :ignore-dirs)
                        my-grep-ignore-dirs))
         (ignore-file-exts (if use-cache (plist-get my-grep-opts-cache :ignore-file-exts)
                             my-grep-ignore-file-exts))
         (ignore-file-names (if use-cache (plist-get my-grep-opts-cache :ignore-file-names)
                              my-grep-ignore-file-names)))
    (cond
     ((counsel-has-quick-grep)
      (concat (mapconcat (lambda (e) (format "-g='!%s/*'" e))
                         ignore-dirs " ")
              " "
              (mapconcat (lambda (e) (format "-g='!*.%s'" e))
                         ignore-file-exts " ")
              " "
              (mapconcat (lambda (e) (format "-g='!%s'" e))
                         ignore-file-names " ")))
     (t
      (concat (mapconcat (lambda (e) (format "--exclude-dir='%s'" e))
                         ignore-dirs " ")
              " "
              (mapconcat (lambda (e) (format "--exclude='*.%s'" e))
                         ignore-file-exts " ")
              " "
              (mapconcat (lambda (e) (format "--exclude='%s'" e))
                         ignore-file-names " "))))))

(defun my-grep-cli (keyword use-cache &optional extra-opts)
  "Extended regex is used, like (pattern1|pattern2)."
  (let* (opts cmd)
    (unless extra-opts (setq extra-opts ""))
    (cond
     ((counsel-has-quick-grep)
      (setq cmd (format "%s %s %s \"%s\" --"
                        (counsel-find-quick-grep)
                        (my-grep-exclude-opts use-cache)
                        extra-opts
                        keyword)))
     (t
      ;; use extended regex always
      (setq cmd (format "grep -rsnE %s %s \"%s\" *"
                        (my-grep-exclude-opts use-cache)
                        extra-opts
                        keyword))))
    ;; (message "cmd=%s" cmd)
    cmd))

(defun my-root-dir ()
  "If ffip is not installed, use `default-directory'."
  (file-name-as-directory (or (and (fboundp 'ffip-get-project-root-directory)
                                   (ffip-get-project-root-directory))
                              default-directory)))

;; TIP: after `M-x my-grep', you can:
;; - then `C-c C-o' or `M-x ivy-occur'
;; - `C-c C-c' or `M-x wgrep-finish-edit'
(defun my-grep-occur ()
  "Generate a custom occur buffer for `my-grep'."
  (unless (eq major-mode 'ivy-occur-grep-mode)
    (ivy-occur-grep-mode))
  ;; useless to set `default-directory', it's already correct
  ;; (message "default-directory=%s" default-directory)
  ;; we use regex in elisp, don't unquote regex
  (let* ((regex (setq ivy--old-re
                      (ivy--regex
                       (progn (string-match "\"\\(.*\\)\"" (buffer-name))
                              (match-string 1 (buffer-name))))))
         (cands (remove nil (mapcar (lambda (s) (if (string-match-p regex s) s))
                                    (split-string (shell-command-to-string (my-grep-cli keyword t))
                                                  "[\r\n]+" t)))))

    ;; Need precise number of header lines for `wgrep' to work.
    (insert (format "-*- mode:grep; default-directory: %S -*-\n\n\n"
                    default-directory))
    (insert (format "%d candidates:\n" (length cands)))
    (ivy--occur-insert-lines
     (mapcar
      (lambda (cand) (concat "./" cand))
      cands))))
;; goto `wgrep-mode' automatically after `C-c C-o', (why press extra `C-x C-q'?)
(defun ivy-occur-grep-mode-hook-setup ()
  ;; no syntax highlight, I only care performance when searching/replacing
  (font-lock-mode -1)
  ;; @see https://emacs.stackexchange.com/questions/598/how-do-i-prevent-extremely-long-lines-making-emacs-slow
  (column-number-mode -1)
  ;; turn on wgrep right now
  ;; (ivy-wgrep-change-to-wgrep-mode) ; doesn't work, don't know why
  )
(add-hook 'ivy-occur-grep-mode-hook 'ivy-occur-grep-mode-hook-setup)

(defvar my-grep-show-full-directory t)
(defvar my-grep-debug nil)
(defun my-grep ()
  "Grep at project root directory or current directory.
Try to find best grep program (ripgrep, grep...) automatically.
Extended regex like (pattern1|pattern2) is used."
  (interactive)
  (let* ((keyword (counsel-read-keyword "Enter grep pattern: "))
         (default-directory (my-root-dir))
         (collection (split-string (shell-command-to-string (my-grep-cli keyword nil)) "[\r\n]+" t))
         (dir (if my-grep-show-full-directory (my-root-dir)
                (file-name-as-directory (file-name-base (directory-file-name (my-root-dir)))))))

    (setq my-grep-opts-cache (plist-put my-grep-opts-cache :ignore-dirs my-grep-ignore-dirs))
    (setq my-grep-opts-cache (plist-put my-grep-opts-cache :ignore-file-exts my-grep-ignore-file-exts))
    (setq my-grep-opts-cache (plist-put my-grep-opts-cache :ignore-file-names my-grep-ignore-file-names))
    ;; (message "my-grep-opts-cache=%s" my-grep-opts-cache)

    (ivy-read (format "matching \"%s\" at %s:" keyword dir)
              collection
              :history 'counsel-git-grep-history
              :action `(lambda (line)
                         (let* ((default-directory (my-root-dir)))
                           (counsel--open-file line)))
              :unwind (lambda ()
                        (counsel-delete-process)
                        (swiper--cleanup))
              :caller 'my-grep)))
(ivy-set-occur 'my-grep 'my-grep-occur)
(ivy-set-display-transformer 'my-grep 'counsel-git-grep-transformer)
;; }}

(defun counsel-git-grep-by-selected ()
  (interactive)
  (cond
   ((region-active-p)
    (counsel-git-grep counsel-git-grep-cmd-default (my-selected-str)))
   (t
    (counsel-git-grep))))

(defun counsel-browse-kill-ring (&optional n)
  "Use `browse-kill-ring' if it exists and N is 1.
If N > 1, assume just yank the Nth item in `kill-ring'.
If N is nil, use `ivy-mode' to browse the `kill-ring'."
  (interactive "P")
  (my-select-from-kill-ring my-insert-str n))

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
  (swiper (my-use-selected-string-or-ask "")))

(global-set-key (kbd "C-s") 'swiper)
;; }}

(provide 'init-ivy)
