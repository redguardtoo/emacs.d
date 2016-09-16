;; {{ @see http://oremacs.com/2015/04/19/git-grep-ivy/
(defun counsel-escape (keyword)
  (setq keyword (replace-regexp-in-string "\"" "\\\\\"" keyword))
  (setq keyword (replace-regexp-in-string "\\?" "\\\\\?" keyword))
  (setq keyword (replace-regexp-in-string "\\$" "\\\\\$" keyword))
  (setq keyword (replace-regexp-in-string "\\*" "\\\\\*" keyword))
  (setq keyword (replace-regexp-in-string "\\." "\\\\\." keyword))
  (setq keyword (replace-regexp-in-string "\\[" "\\\\\[" keyword))
  (setq keyword (replace-regexp-in-string "\\]" "\\\\\]" keyword))
  (setq keyword (replace-regexp-in-string "{" "\\\\\{" keyword))
  (setq keyword (replace-regexp-in-string "}" "\\\\\}" keyword))
  (setq keyword (replace-regexp-in-string "(" "\\\\\(" keyword))
  (setq keyword (replace-regexp-in-string ")" "\\\\\)" keyword))
  keyword)

(defun counsel-read-keyword (hint &optional default-when-no-active-region)
  (if (region-active-p)
      (counsel-escape (my-selected-str))
    (if default-when-no-active-region
        default-when-no-active-region
      (read-string hint))))

(defmacro counsel-git-grep-or-find-api (fn git-cmd hint &optional no-keyword filter)
  "Apply FN on the output lines of GIT-CMD.  HINT is hint when user input.
Yank the file name at the same time.  FILTER is function to filter the collection"
  `(let* ((str (if (buffer-file-name) (file-name-base (buffer-file-name)) ""))
          (default-directory (locate-dominating-file
                              default-directory ".git"))
          keyword
          collection)

     (unless ,no-keyword
       ;; selected region contains no regular expression
       (setq keyword (counsel-read-keyword (concat "Enter " ,hint " pattern:" ))))

     (setq collection
           (split-string (shell-command-to-string (if ,no-keyword ,git-cmd
                                                    (format ,git-cmd keyword)))
                         "\n"
                         t))
     (if ,filter (setq collection (funcall ,filter collection)))
     (cond
      ((and collection (= (length collection) 1))
       (funcall ,fn (car collection)))
      (t
       (ivy-read (if ,no-keyword ,hint (format "matching \"%s\":" keyword))
                 collection
                 :action ,fn)))))

(defun counsel--open-grepped-file (val)
  (let* ((lst (split-string val ":"))
         (linenum (string-to-number (cadr lst))))
    ;; open file
    (find-file (car lst))
    ;; goto line if line number exists
    (when (and linenum (> linenum 0))
      (goto-char (point-min))
      (forward-line (1- linenum)))))

(defun counsel-git-grep-in-project ()
  "Grep in the current git repository.
Extended regex is used, like (pattern1|pattern2)."
  (interactive)
  (counsel-git-grep-or-find-api 'counsel--open-grepped-file
                                "git --no-pager grep -I --full-name -n --no-color -E -e \"%s\""
                                "grep"))

(defvar counsel-git-grep-author-regex nil)

;; `git --no-pager blame -w -L 397,+1 --porcelain lisp/init-evil.el'
(defun counsel--filter-grepped-by-author (collection)
  (if counsel-git-grep-author-regex
      (delq nil
            (mapcar
             (lambda (v)
               (let (blame-cmd (arr (split-string v ":" t)))
                 (setq blame-cmd
                       (format "git --no-pager blame -w -L %s,+1 --porcelain %s"
                               (cadr arr) ; line number
                               (car arr))) ; file
                 (if (string-match-p (format "\\(author %s\\|author Not Committed\\)"
                                               counsel-git-grep-author-regex)
                                       (shell-command-to-string blame-cmd))
                   v)))
             collection))
    collection))

(defun counsel-git-grep-by-author ()
  "Grep in the current git repository.
It's SLOW when more than 20 git blame process start."
  (interactive)
  (counsel-git-grep-or-find-api 'counsel--open-grepped-file
                                "git --no-pager grep --full-name -n --no-color -i -e \"%s\""
                                "grep by author"
                                nil
                                'counsel--filter-grepped-by-author))

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

(defun counsel-git-find-file ()
  "Find file in the current git repository."
  (interactive)
  (counsel-git-grep-or-find-api 'find-file
                                "git ls-tree -r HEAD --name-status | grep \"%s\""
                                "file"))

(defun counsel-replace-current-line (leading-spaces content)
  (beginning-of-line)
  (kill-line)
  (insert (concat leading-spaces content))
  (end-of-line))

(defun counsel-git-grep-complete-line ()
  "Complete line by use text from (line-beginning-position) to (point)."
  (interactive)
  (let* ((cur-line (my-line-str (point)))
         (default-directory (locate-dominating-file
                             default-directory ".git"))
         (keyword (counsel-escape (replace-regexp-in-string "^[ \t]*" "" cur-line)))
         (cmd (format "git --no-pager grep -I -h --no-color -i -e \"^[ \\t]*%s\" | sed s\"\/^[ \\t]*\/\/\" | sed s\"\/[ \\t]*$\/\/\" | sort | uniq"
                      keyword))
         (leading-spaces "")
         (collection (split-string (shell-command-to-string cmd) "\n" t)))

    ;; grep lines without leading/trailing spaces
    (when collection
      (if (string-match "^\\([ \t]*\\)" cur-line)
          (setq leading-spaces (match-string 1 cur-line)))
      (cond
       ((= 1 (length collection))
        (counsel-replace-current-line leading-spaces (car collection)))
       ((> (length collection) 1)
        (ivy-read "lines:"
                  collection
                  :action (lambda (l)
                            (counsel-replace-current-line leading-spaces l))))))))
(global-set-key (kbd "C-x C-l") 'counsel-git-grep-complete-line)

(defun counsel-git-grep-yank-line (&optional insert-line)
  "Grep in the current git repository and yank the line.
If INSERT-LINE is not nil, insert the line grepped"
  (interactive "P")
  (let* ((fn (lambda (val)
               (let ((lst (split-string val ":")) text-line)
                 ;; the actual text line could contain ":"
                 (setq text-line (replace-regexp-in-string (format "^%s:%s:" (car lst) (nth 1 lst)) "" val))
                 ;; trim the text line
                 (setq text-line (replace-regexp-in-string (rx (* (any " \t\n")) eos) "" text-line))
                 (kill-new text-line)
                 (if insert-line (insert text-line))
                 (message "line from %s:%s => kill-ring" (car lst) (nth 1 lst))))))

    (counsel-git-grep-or-find-api fn
                                  "git --no-pager grep -I --full-name -n --no-color -i -e \"%s\""
                                  "grep"
                                  nil)))

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

(defun ivy-imenu-get-candidates-from (alist &optional prefix)
  (cl-loop for elm in alist
           nconc (if (imenu--subalist-p elm)
                       (ivy-imenu-get-candidates-from
                        (cl-loop for (e . v) in (cdr elm) collect
                                 (cons e (if (integerp v) (copy-marker v) v)))
                        ;; pass the prefix to next recursive call
                        (concat prefix (if prefix ".") (car elm)))
                   (and (cdr elm) ; bug in imenu, should not be needed.
                        (setcdr elm (copy-marker (cdr elm))) ; Same as [1].
                        (let ((key (concat prefix (if prefix ".") (car elm))) )
                          (list (cons key (cons key (copy-marker (cdr elm)))))
                          )))))

(defun counsel-imenu-goto ()
  "Imenu based on ivy-mode."
  (interactive)
  (unless (featurep 'imenu)
    (require 'imenu nil t))
  (let* ((imenu-auto-rescan t)
         (items (imenu--make-index-alist t)))
    (ivy-read "imenu items:"
              (ivy-imenu-get-candidates-from (delete (assoc "*Rescan*" items) items))
              :action (lambda (k)
                        ;; minor error handling
                        (if (listp (cdr k)) (setq k (cdr k)))
                        ;; copied from ido-imenu, don't know the purpose
                        (push-mark (point))
                        ;; better way to imenu
                        (imenu k)
                        (if (memq major-mode '(org-mode))
                            (org-show-subtree))))))

(defun counsel-bookmark-goto ()
  "Open ANY bookmark.  Requires bookmark+"
  (interactive)

  (unless (featurep 'bookmark)
    (require 'bookmark))
  (bookmark-maybe-load-default-file)

  (let* ((bookmarks (and (boundp 'bookmark-alist) bookmark-alist))
         (collection (delq nil (mapcar (lambda (bookmark)
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
                                       bookmarks))))
    ;; do the real thing
    (ivy-read "bookmarks:"
              collection
              :action (lambda (bookmark)
                        (unless (featurep 'bookmark+)
                          (require 'bookmark+))
                        (bookmark-jump bookmark)))))

(defun counsel-git-find-file-committed-with-line-at-point ()
  (interactive)
  (let* ((default-directory (locate-dominating-file
                            default-directory ".git"))
        (filename (file-truename buffer-file-name))
        (linenum (save-restriction
                   (widen)
                   (save-excursion
                     (beginning-of-line)
                     (1+ (count-lines 1 (point))))))
        (git-cmd (format "git --no-pager blame -w -L %d,+1 --porcelain %s"
                         linenum
                         filename))
        (str (shell-command-to-string git-cmd))
        hash)

    (cond
     ((and (string-match "^\\([0-9a-z]\\{40\\}\\) " str)
           (not (string= (setq hash (match-string 1 str)) "0000000000000000000000000000000000000000")))
      ;; (message "hash=%s" hash)
      (counsel-git-grep-or-find-api 'counsel--open-grepped-file
                                    (format "git --no-pager show --pretty=\"format:\" --name-only \"%s\"" hash)
                                    (format "files in commit %s:" (substring hash 0 7))
                                    nil
                                    t))
     (t
      (message "Current line is NOT committed yet!")))))

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

(defun counsel-git-show-hash-diff-mode (hash)
  (let ((show-cmd (format "git --no-pager show --no-color %s" hash)))
    (diff-region-open-diff-output (shell-command-to-string show-cmd)
                                  "*Git-show")))

(defun counsel-recentf-goto ()
  "Recent files."
  (interactive)
  (unless recentf-mode (recentf-mode 1))
  (if (fboundp 'counsel-recentf)
      (counsel-recentf)
    (ivy-recentf)))

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
(defvar my-grep-ingore-dirs
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
(defvar my-grep-ingore-file-exts
  '("log"
    "properties"
    "session"
    "swp")
  "File extensions to ignore when grepping.")
(defvar my-grep-ingore-file-names
  '("TAGS"
    "tags"
    "GTAGS"
    "GPATH"
    ".bookmarks.el"
    "*.svg"
    "history"
    "#*#"
    "*.min.js"
    "*.min.css"
    "*~")
  "File names to ignore when grepping.")
(defun my-grep-cli (keyword)
  "Extended regex is used, like (pattern1|pattern2)."
  (let* (opts)
    (cond
     ((executable-find "ag")
      (setq opts (concat (mapconcat (lambda (e) (format "--ignore-dir='%s'" e))
                                    my-grep-ingore-dirs " ")
                         " "
                         (mapconcat (lambda (e) (format "--ignore='*.%s'" e))
                                    my-grep-ingore-file-exts " ")
                         " "
                         (mapconcat (lambda (e) (format "--ignore='%s'" e))
                                    my-grep-ingore-file-names " ")))
      (format "ag -s --nocolor --nogroup --silent %s \"%s\" -- ." opts keyword))
     (t
      (setq opts (concat (mapconcat (lambda (e) (format "--exclude-dir='%s'" e))
                                    my-grep-ingore-dirs " ")
                         " "
                         (mapconcat (lambda (e) (format "--exclude='*.%s'" e))
                                    my-grep-ingore-file-exts " ")
                         " "
                         (mapconcat (lambda (e) (format "--exclude='%s'" e))
                                    my-grep-ingore-file-names " ")))
      ;; use extended regex always
      (format "grep -rsnE %s \"%s\" * ." opts keyword)))))

(defun my-grep ()
  "Grep at project root directory or current directory.
If ag (the_silver_searcher) exists, use ag.
Extended regex is used, like (pattern1|pattern2)."
  (interactive)
  (let* ((keyword (counsel-read-keyword "Enter grep pattern: "))
         (default-directory (or (and (fboundp 'ffip-get-project-root-directory)
                                     (ffip-get-project-root-directory))
                                default-directory))
         (collection (split-string (shell-command-to-string (my-grep-cli keyword)) "\n" t)))
    (ivy-read (format "matching \"%s\" at %s:" keyword default-directory)
              collection
              :action 'counsel--open-grepped-file)))
;; }}

(defun counsel-browse-kill-ring (&optional n)
  "Use `browse-kill-ring' if it exists and N is 1.
If N > 1, assume just yank the Nth item in `kill-ring'.
If N is nil, use `ivy-mode' to browse the `kill-ring'."
  (interactive "P")
  (cond
   ((or (not n) (and (= n 1) (not (fboundp 'browse-kill-ring))))
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
                  :action 'my-insert-str))))
   ((= n 1)
    (browse-kill-ring))
   ((> n 1)
    (setq n (1- n))
    (if (< n 0) (setq n 0))
    (my-insert-str (nth n kill-ring)))))

(provide 'init-ivy)
