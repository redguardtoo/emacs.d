(defvar counsel-process-filename-string nil
  "Give you a chance to change file name string for other counsel-* functions")
;; {{ @see http://oremacs.com/2015/04/19/git-grep-ivy/
(defun counsel-git-grep-or-find-api (fn git-cmd hint open-another-window &optional no-keyword filter)
  "Apply FN on the output lines of GIT-CMD.  HINT is hint when user input.
IF OPEN-ANOTHER-WINDOW is true, open the file in another window.
Yank the file name at the same time.  FILTER is function to filter the collection"
  (let ((str (if (buffer-file-name) (file-name-base (buffer-file-name)) ""))
        (default-directory (locate-dominating-file
                            default-directory ".git"))
        keyword
        collection val lst)

    ;; insert base file name into kill ring is possible
    (kill-new (if counsel-process-filename-string
                  (funcall counsel-process-filename-string str)
                str))

    (unless no-keyword
      ;; selected region contains no regular expression
      (setq keyword (if (region-active-p)
                        (counsel-escape (buffer-substring-no-properties (region-beginning) (region-end)))
                      (read-string (concat "Enter " hint " pattern:" )))))

    ;; (message "git-cmd=%s keyword=%s" (if no-keyword git-cmd (format git-cmd keyword)) keyword)
    (setq collection (split-string (shell-command-to-string (if no-keyword
                                                                git-cmd
                                                              (format git-cmd keyword)))
                                   "\n"
                                   t))
    (if filter (setq collection (funcall filter collection)))

    (when (and collection (> (length collection) 0))
      (setq val (if (= 1 (length collection)) (car collection)
                    (ivy-read (if no-keyword hint (format "matching \"%s\":" keyword)) collection)))
      (funcall fn open-another-window val))))

(defun counsel--open-grepped-file (open-another-window val)
  (let ((lst (split-string val ":")))
    (funcall (if open-another-window 'find-file-other-window 'find-file)
             (car lst))
    (let ((linenum (string-to-number (cadr lst))))
      (when (and linenum (> linenum 0))
        (goto-char (point-min))
        (forward-line (1- linenum))))))

(defun counsel-git-grep (&optional open-another-window)
  "Grep in the current git repository.
If OPEN-ANOTHER-WINDOW is not nil, results are displayed in new window."
  (interactive "P")
  (counsel-git-grep-or-find-api 'counsel--open-grepped-file
                                "git --no-pager grep -I --full-name -n --no-color -i -e \"%s\""
                                "grep"
                                open-another-window))

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

(defun counsel-git-grep-by-author (&optional open-another-window)
  "Grep in the current git repository.
If OPEN-ANOTHER-WINDOW is not nil, results are displayed in new window.
SLOW when more than 20 git blame process start."
  (interactive "P")
  (counsel-git-grep-or-find-api 'counsel--open-grepped-file
                                "git --no-pager grep --full-name -n --no-color -i -e \"%s\""
                                "grep by author"
                                open-another-window
                                nil
                                'counsel--filter-grepped-by-author))

(defun counsel-git-show-file (&optional open-another-window)
  "Find file in HEAD commit or whose commit hash is selected region.
If OPEN-ANOTHER-WINDOW is not nil, results are displayed in new window."
  (interactive "P")
  (let (fn)
    (setq fn (lambda (open-another-window val)
               (funcall (if open-another-window 'find-file-other-window 'find-file) val)))
    (counsel-git-grep-or-find-api fn
                                  (format "git --no-pager diff-tree --no-commit-id --name-only -r %s"
                                          (if (region-active-p)
                                              (buffer-substring-no-properties (region-beginning) (region-end))
                                            "HEAD"))
                                  "files from `git-show' "
                                  open-another-window
                                  t)))


(defun counsel-git-diff-file (&optional open-another-window)
  "Find file in `git diff'.
If OPEN-ANOTHER-WINDOW is not nil, results are displayed in new window."
  (interactive "P")
  (let (fn)
    (setq fn (lambda (open-another-window val)
               (funcall (if open-another-window 'find-file-other-window 'find-file) val)))
    (counsel-git-grep-or-find-api fn
                                  "git --no-pager diff --name-only"
                                  "files from `git-diff' "
                                  open-another-window
                                  t)))

(defun counsel-git-find-file (&optional open-another-window)
  "Find file in the current git repository.
If OPEN-ANOTHER-WINDOW is not nil, results are displayed in new window."
  (interactive "P")
  (let (fn)
    (setq fn (lambda (open-another-window val)
               (funcall (if open-another-window 'find-file-other-window 'find-file) val)))
    (counsel-git-grep-or-find-api fn
                                  "git ls-tree -r HEAD --name-status | grep \"%s\""
                                  "file"
                                  open-another-window)))

(defun counsel-escape (keyword)
  (setq keyword (replace-regexp-in-string "\"" "\\\\\"" keyword))
  (setq keyword (replace-regexp-in-string "\\?" "\\\\\?" keyword))
  (setq keyword (replace-regexp-in-string "\\$" "\\\\\$" keyword))
  (setq keyword (replace-regexp-in-string "\\*" "\\\\\*" keyword))
  (setq keyword (replace-regexp-in-string "\\." "\\\\\." keyword))
  (setq keyword (replace-regexp-in-string "\\[" "\\\\\[" keyword))
  (setq keyword (replace-regexp-in-string "\\]" "\\\\\]" keyword))
  keyword)

(defun counsel-replace-current-line (leading-spaces content)
  (beginning-of-line)
  (kill-line)
  (insert (concat leading-spaces content))
  (end-of-line))

(defun counsel-git-grep-complete-line ()
  (interactive)
  (let* (cmd
        (cur-line (buffer-substring-no-properties (line-beginning-position)
                                                  (line-end-position)))
        (default-directory (locate-dominating-file
                            default-directory ".git"))
        keyword
        (leading-spaces "")
        collection)
    (setq keyword (counsel-escape (if (region-active-p)
                                      (buffer-substring-no-properties (region-beginning)
                                                                      (region-end))
                                    (replace-regexp-in-string "^[ \t]*" "" cur-line))))
    ;; grep lines without leading/trailing spaces
    (setq cmd (format "git --no-pager grep -I -h --no-color -i -e \"^[ \\t]*%s\" | sed s\"\/^[ \\t]*\/\/\" | sed s\"\/[ \\t]*$\/\/\" | sort | uniq" keyword))
    (when (setq collection (split-string (shell-command-to-string cmd) "\n" t))
      (if (string-match "^\\([ \t]*\\)" cur-line)
          (setq leading-spaces (match-string 1 cur-line)))
      (cond
       ((= 1 (length collection))
        (counsel-replace-current-line leading-spaces (car collection)))
       ((> (length collection) 1)
        (ivy-read "lines:"
                  collection
                  :action (lambda (l)
                            (counsel-replace-current-line leading-spaces l))))))
    ))
(global-set-key (kbd "C-x C-l") 'counsel-git-grep-complete-line)

(defun counsel-git-grep-yank-line (&optional insert-line)
  "Grep in the current git repository and yank the line.
If INSERT-LINE is not nil, insert the line grepped"
  (interactive "P")
  (let (fn)
    (setq fn (lambda (unused-param val)
               (let ((lst (split-string val ":")) text-line)
                 ;; the actual text line could contain ":"
                 (setq text-line (replace-regexp-in-string (format "^%s:%s:" (car lst) (nth 1 lst)) "" val))
                 ;; trim the text line
                 (setq text-line (replace-regexp-in-string (rx (* (any " \t\n")) eos) "" text-line))
                 (kill-new text-line)
                 (if insert-line (insert text-line))
                 (message "line from %s:%s => kill-ring" (car lst) (nth 1 lst)))))

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
  (interactive "P")
  (let (fn cmd)
    (setq fn (lambda (open-another-window val)
               (find-file val)))
    (unless (and num (> num 0))
      (setq num 24))
    (setq cmd (concat "git log --pretty=format: --name-only --since=\""
                                          (number-to-string num)
                                          " weeks ago\" --author=\""
                                          counsel-my-name-regex
                                          "\" | grep \"%s\" | sort | uniq"))
    ;; (message "cmd=%s" cmd)
    (counsel-git-grep-or-find-api fn cmd "file" nil)))
;; }}

(defun ivy-imenu-get-candidates-from (alist  &optional prefix)
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
  "Go to buffer position"
  (interactive)
  (let ((imenu-auto-rescan t) items)
    (unless (featurep 'imenu)
      (require 'imenu nil t))
    (setq items (imenu--make-index-alist t))
    (ivy-read "imenu items:"
              (ivy-imenu-get-candidates-from (delete (assoc "*Rescan*" items) items))
              :action (lambda (k) (imenu k)))))

(defun counsel-bookmark-goto ()
  "Open ANY bookmark"
  (interactive)
  (let (bookmarks filename)
    ;; load bookmarks
    (unless (featurep 'bookmark)
      (require 'bookmark))
    (bookmark-maybe-load-default-file)
    (setq bookmarks (and (boundp 'bookmark-alist) bookmark-alist))

    ;; do the real thing
    (ivy-read "bookmarks:"
              (delq nil (mapcar (lambda (bookmark)
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
                                bookmarks))
              :action (lambda (bookmark)
                        (unless (featurep 'bookmark+)
                          (require 'bookmark+))
                        (bookmark-jump bookmark)))
    ))

(defun counsel-git-find-file-committed-with-line-at-point ()
  (interactive)
  (let ((default-directory (locate-dominating-file
                            default-directory ".git"))
        (filename (file-truename buffer-file-name))
        (linenum (save-restriction
                   (widen)
                   (save-excursion
                     (beginning-of-line)
                     (1+ (count-lines 1 (point))))))
        git-cmd
        str
        hash)
    (setq git-cmd
          (format "git --no-pager blame -w -L %d,+1 --porcelain %s"
                  linenum
                  filename))
    (setq str (shell-command-to-string git-cmd))
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
      (message "Current line is NOT committed yet!")))
    ))

(defun counsel-yank-bash-history ()
  "Yank the bash history"
  (interactive)
  (let (hist-cmd collection val)
    (shell-command "history -r") ; reload history
    (setq collection
          (nreverse
           (split-string (with-temp-buffer (insert-file-contents (file-truename "~/.bash_history"))
                                           (buffer-string))
                         "\n"
                         t)))
    (when (and collection (> (length collection) 0)
               (setq val (if (= 1 (length collection)) (car collection)
                           (ivy-read (format "Bash history:") collection))))
        (kill-new val)
        (message "%s => kill-ring" val))))

(defun counsel-git-show-hash-diff-mode (hash)
  (let ((show-cmd (format "git --no-pager show --no-color %s" hash)))
    (diff-region-open-diff-output (shell-command-to-string show-cmd)
                                  "*Git-show")))

(defun counsel-recentf-goto ()
  "Recent files"
  (interactive)
  (unless recentf-mode (recentf-mode 1))
  (ivy-recentf))

(defun counsel-goto-recent-directory ()
  "Recent directories"
  (interactive)
  (unless recentf-mode (recentf-mode 1))
  (let ((collection
         (delete-dups
          (append (mapcar 'file-name-directory recentf-list)
                  ;; fasd history
                  (if (executable-find "fasd")
                      (split-string (shell-command-to-string "fasd -ld") "\n" t))))))
    (ivy-read "directories:" collection :action 'dired)))

(provide 'init-ivy)
