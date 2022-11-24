;; -*- coding: utf-8; lexical-binding: t; -*-

;; ;; {{ Solution 1: disable all vc backends
;; @see http://stackoverflow.com/questions/5748814/how-does-one-disable-vc-git-in-emacs
;; (setq vc-handled-backends nil)
;; }}

;; {{ Solution 2: if NO network mounted drive involved
(setq vc-handled-backends '(Git SVN Hg))
;; @see https://www.reddit.com/r/emacs/comments/4c0mi3/the_biggest_performance_improvement_to_emacs_ive/
;; open files faster but you can't check if file is version
;; controlled. other VCS functionality still works.
(remove-hook 'find-file-hook 'vc-find-file-hook)
;; }}

;; ;; {{ Solution 3: setup `vc-handled-backends' per project
;; (setq vc-handled-backends nil)
;; (defun my-setup-develop-environment ()
;;   "Default setup for project under vcs."
;;   (interactive)
;;   (cond
;;     ((string-match (file-truename user-emacs-directory)
;;                      (file-name-directory (buffer-file-name)))
;;       (setq vc-handled-backends '(Git)))
;;     (t
;;       (setq vc-handled-backends nil))))
;; (dolist (hook '(java-mode-hook emacs-lisp-mode-hook org-mode-hook
;;                 js-mode-hook javascript-mode-hook web-mode-hook
;;                 c++-mode-hook c-mode-hook))
;;   (add-hook hook #'my-setup-develop-environment))
;; ;; }}

;; {{ git-gutter
(with-eval-after-load 'git-gutter
  (unless (fboundp 'global-display-line-numbers-mode)
    ;; git-gutter's workaround for linum-mode bug.
    ;; should not be used in `display-line-number-mode'
    (git-gutter:linum-setup))

  (setq git-gutter:update-interval 2)
  ;; nobody use bzr
  ;; I could be forced to use subversion or hg which has higher priority
  ;; Please note my $HOME directory is under git control
  (setq git-gutter:handled-backends '(svn hg git))
  (setq git-gutter:disabled-modes
        '(asm-mode
          org-mode
          outline-mode
          markdown-mode
          image-mode)))

(defun my-git-gutter-reset-to-head-parent()
  "Reset gutter to HEAD^.  Support Subversion and Git."
  (interactive)
  (let* ((filename (buffer-file-name))
         (cmd (concat "git --no-pager log --oneline -n1 --pretty=\"format:%H\" "
                      filename))
         (parent (cond
                  ((eq git-gutter:vcs-type 'svn)
                   "PREV")
                  (filename
                   (concat (shell-command-to-string cmd) "^"))
                  (t
                   "HEAD^"))))
    (git-gutter:set-start-revision parent)
    (message "git-gutter:set-start-revision HEAD^")))

(defvar my-prefer-lightweight-magit t)
(defun my-hint-untracked-files ()
  "If untracked files and committed files share same extension, warn users."

  ;; don't scan whole home directory
  (unless (string= (file-truename default-directory) (file-truename "~/"))
    (let* ((exts (mapcar 'file-name-extension (my-lines-from-command-output "git diff-tree --no-commit-id --name-only -r HEAD")))
           (untracked-files (my-lines-from-command-output "git --no-pager ls-files --others --exclude-standard"))
           (lookup-ext (make-hash-table :test #'equal))
           rlt)
      ;; file extensions of files in HEAD commit
      (dolist (ext exts)
        (puthash ext t lookup-ext))
      ;; If untracked file has same file extension as committed files
      ;; maybe they should be staged too?
      (dolist (file untracked-files)
        (when (gethash (file-name-extension file) lookup-ext)
          (push (file-name-nondirectory file) rlt)))
      (when rlt
        (message "Stage files? %s" (mapconcat 'identity rlt " "))))))

(with-eval-after-load 'magit
  ;; {{speed up magit, @see https://jakemccrary.com/blog/2020/11/14/speeding-up-magit/
  (when my-prefer-lightweight-magit
    (remove-hook 'magit-status-sections-hook 'magit-insert-tags-header)
    (remove-hook 'magit-status-sections-hook 'magit-insert-status-headers)
    (remove-hook 'magit-status-sections-hook 'magit-insert-unpushed-to-pushremote)
    (remove-hook 'magit-status-sections-hook 'magit-insert-unpulled-from-pushremote)
    (remove-hook 'magit-status-sections-hook 'magit-insert-unpulled-from-upstream)
    (remove-hook 'magit-status-sections-hook 'magit-insert-unpushed-to-upstream-or-recent))
  ;; }}

  ;; "Continue listing the history of a file beyond renames (works only for a single file)."
  ;; - quoted from "git help log"
  (setq-default magit-buffer-log-args '("--follow"))

  ;; extra check&report after commit
  (defun my-git-check-status ()
    "Check git repo status."
    ;; use timer here to wait magit cool down
    (my-run-with-idle-timer 1 #'my-hint-untracked-files))
  (add-hook 'magit-post-commit-hook #'my-git-check-status)
  (add-hook 'git-commit-post-finish-hook #'my-git-check-status))

(defun my-git-gutter-toggle ()
  "Toggle git gutter."
  (interactive)
  (git-gutter-mode -1)
  ;; git-gutter-fringe doesn't seem to
  ;; clear the markup right away
  (sit-for 0.1)
  (git-gutter:clear))

(defun my-git-gutter-reset-to-default ()
  "Restore git gutter to its original status.
Show the diff between current working code and git head."
  (interactive)
  (git-gutter:set-start-revision nil)
  (message "git-gutter reset"))

(my-run-with-idle-timer 2 #'global-git-gutter-mode)

(global-set-key (kbd "C-x C-g") 'git-gutter:toggle)
(global-set-key (kbd "C-x v =") 'git-gutter:popup-hunk)
;; Stage current hunk
(global-set-key (kbd "C-x v s") 'git-gutter:stage-hunk)
;; Revert current hunk
(global-set-key (kbd "C-x v r") 'git-gutter:revert-hunk)

;; }}

(defun my-git-commit-id ()
  "Select commit id from current branch."
  (let* ((git-cmd "git --no-pager log --date=short --pretty=format:'%h|%ad|%s|%an'")
         (collection (my-nonempty-lines (shell-command-to-string git-cmd)))
         (item (completing-read "git log:" collection)))
    (when item
      (car (split-string item "|" t)))))

(defun my-git-show-commit-internal ()
  "Show git commit."
  (let* ((id (my-git-commit-id)))
    (when id
      (shell-command-to-string (format "git show %s" id)))))

(defun my-git-show-commit ()
  "Show commit using ffip."
  (interactive)
  (let* ((ffip-diff-backends '(("Show git commit" . my-git-show-commit-internal))))
    (ffip-show-diff 0)))

;; {{ git-timemachine
(defun my-git-timemachine-show-selected-revision ()
  "Show last (current) revision of file."
  (interactive)
  (let* ((collection (mapcar (lambda (rev)
                    ;; re-shape list for the ivy-read
                    (cons (concat (substring-no-properties (nth 0 rev) 0 7) "|" (nth 5 rev) "|" (nth 6 rev)) rev))
                  (git-timemachine--revisions))))
    (ivy-read "commits:"
              collection
              :action (lambda (rev)
                        ;; compatible with ivy 8+ and later ivy version
                        (unless (string-match "^[a-z0-9]*$" (car rev))
                          (setq rev (cdr rev)))
                        (git-timemachine-show-revision rev)))))

(defun my-git-timemachine ()
  "Open git snapshot with the selected version."
  (interactive)
  (my-ensure 'git-timemachine)
  (git-timemachine--start #'my-git-timemachine-show-selected-revision))
;; }}

(defun git-get-current-file-relative-path ()
  "Get relative path of current file for Git."
  (replace-regexp-in-string (concat "^" (file-name-as-directory default-directory))
                            ""
                            buffer-file-name))

(defun git-checkout-current-file ()
  "Git checkout current file."
  (interactive)
  (when (and (buffer-file-name)
             (yes-or-no-p (format "git checkout %s?"
                                  (file-name-nondirectory (buffer-file-name)))))
    (let* ((filename (git-get-current-file-relative-path)))
      (shell-command (concat "git checkout " filename))
      (message "DONE! git checkout %s" filename))))

(defvar git-commit-message-history nil)
(defun git-commit-tracked ()
  "Run 'git add -u' and commit."
  (interactive)
  (let* ((hint "Commit tracked files. Please input commit message (Enter to abort):")
         (msg (read-from-minibuffer hint
                                    nil
                                    nil
                                    nil
                                    'git-commit-message-history)))
    (cond
     ((and msg (> (length msg) 3))
      (shell-command "git add -u")
      (shell-command (format "git commit -m \"%s\"" msg))
      (message "Tracked files is committed."))
     (t
      (message "Do nothing!")))))

(defun git-add-current-file ()
  "Git add file of current buffer."
  (interactive)
  (when buffer-file-name
    (let* ((filename (git-get-current-file-relative-path))
           (head-info (shell-command-to-string
                       "git log --pretty=format:'%h %s (%an)' --date=short -n1
")))
      (shell-command (concat "git add " filename))
      (message "%s added. HEAD: %s" filename head-info))))

;; {{ look up merge conflict
(defvar my-goto-merge-conflict-fns
  '(("n" my-next-merge-conflict)
    ("p" my-prev-merge-conflict)))

(defun my-goto-merge-conflict-internal (forward-p)
  "Goto specific hunk.  If FORWARD-P is t, go in forward direction."
  ;; @see https://emacs.stackexchange.com/questions/63413/finding-git-conflict-in-the-same-buffer-if-cursor-is-at-end-of-the-buffer#63414
  (my-ensure 'smerge-mode)
  (let ((buffer (current-buffer))
        (hunk-fn (if forward-p 'smerge-next 'smerge-prev)))
    (unless (funcall hunk-fn)
      (vc-find-conflicted-file)
      (when (eq buffer (current-buffer))
        (let ((prev-pos (point)))
          (goto-char (if forward-p (point-min) (1- (point-max))))
          (unless (funcall hunk-fn)
            (goto-char prev-pos)
            (message "No conflicts found")))))))

(defun my-next-merge-conflict ()
  "Go to next merge conflict."
  (interactive)
  (my-goto-merge-conflict-internal t))

(defun my-prev-merge-conflict ()
  "Go to previous merge conflict."
  (interactive)
  (my-goto-merge-conflict-internal nil))

(defun my-search-next-merge-conflict ()
  "Search next merge conflict."
  (interactive)
  (my-setup-extra-keymap my-goto-merge-conflict-fns
                         "Goto merge conflict: [n]ext [p]revious [q]uit"
                         'my-goto-merge-conflict-internal
                         t))

(defun my-search-prev-merge-conflict ()
  "Search previous merge conflict."
  (interactive)
  (my-setup-extra-keymap my-goto-merge-conflict-fns
                         "Goto merge conflict: [n]ext [p]revious [q]uit"
                         'my-goto-merge-conflict-internal
                         nil))
;; }}

;; {{ look up diff hunk
(defvar my-goto-diff-hunk-fns
  '(("n" diff-hunk-next)
    ("p" diff-hunk-prev)))

(defun my-search-next-diff-hunk ()
  "Search next diff hunk."
  (interactive)
  (my-setup-extra-keymap my-goto-diff-hunk-fns
                         "Goto diff hunk: [n]ext [p]revious [q]uit"
                         'diff-hunk-next))

(defun my-search-prev-diff-hunk ()
  "Search previous diff hunk."
  (interactive)
  (my-setup-extra-keymap my-goto-diff-hunk-fns
                         "Goto diff hunk: [n]ext [p]revious [q]uit"
                         'diff-hunk-prev))
;; }}

;; {{
(defun my-git-extract-based (target lines)
  "Extract based version from TARGET and LINES."
  (let* (based (i 0) break)
    (while (and (not break) (< i (length lines)))
      (cond
       ((string-match (regexp-quote target) (nth i lines))
        (setq break t))
       (t
        (setq i (1+ i)))))
    ;; find child of target commit
    (when (and (< 0 i)
               (< i (length lines)))
      (setq based
            (replace-regexp-in-string "^tag: +"
                                      ""
                                      (car (split-string (nth (1- i) lines)
                                                         " +")))))
    based))

(defun my-git-rebase-interactive (&optional user-select-branch)
  "Rebase interactively on the closest branch or tag in git log output.
If USER-SELECT-BRANCH is not nil, rebase on the tag or branch selected by user."
  (interactive "P")
  (let* ((cmd "git --no-pager log --decorate --oneline -n 1024")
         (lines (my-lines-from-command-output cmd))
         (targets (delq nil
                        (mapcar (lambda (e)
                                  (when (and (string-match "^[a-z0-9]+ (\\([^()]+\\)) " e)
                                             (not (string-match "^[a-z0-9]+ (HEAD " e)))
                                    (match-string 1 e)))
                                lines)))
         based)
    (cond
     ((or (not targets) (null targets))
      (message "No tag or branch is found to base on."))
     ((or (not user-select-branch) (eq (length targets) 1))
      ;; select the closest/only tag or branch
      (setq based (my-git-extract-based (nth 0 targets) lines)))
     (t
      ;; select the one tag or branch
      (setq based (my-git-extract-based (completing-read "Select based: " targets)
                                        lines))))

    ;; start git rebase
    (when based
      (magit-rebase-interactive based nil))))
;; }}

(defun my-git-cherry-pick-from-reflog ()
  "Cherry pick a commit from git reflog."
  (interactive)
  (let* ((cmd "git --no-pager reflog --date=short")
         (lines (my-lines-from-command-output cmd))
         (selected (completing-read "Commit to cherry pick:" lines))
         (commit-id (and selected (car (split-string selected)))))
    (when commit-id
      (my-ensure 'magit)
      (magit-cherry-copy commit-id))))

;; {{ git-gutter use ivy
(defun my-git-reshape-gutter (gutter)
  "Re-shape GUTTER for `ivy-read'."
  (let* ((linenum-start (aref gutter 3))
         (linenum-end (aref gutter 4))
         (target-line "")
         (target-linenum 1)
         (tmp-line "")
         (max-line-length 0))
    (save-excursion
      (while (<= linenum-start linenum-end)
        (my-goto-line linenum-start)
        (setq tmp-line (replace-regexp-in-string "^[ \t]*" ""
                                                 (buffer-substring (line-beginning-position)
                                                                   (line-end-position))))
        (when (> (length tmp-line) max-line-length)
          (setq target-linenum linenum-start)
          (setq target-line tmp-line)
          (setq max-line-length (length tmp-line)))

        (setq linenum-start (1+ linenum-start))))
    ;; build (key . linenum-start)
    (cons (format "%s %d: %s"
                  (if (eq 'deleted (aref gutter 1)) "-" "+")
                  target-linenum target-line)
          target-linenum)))

(defun my-git-goto-gutter ()
  "Go to specific git gutter."
  (interactive)
  (if git-gutter:diffinfos
      (ivy-read "git-gutters:"
                (mapcar 'my-git-reshape-gutter git-gutter:diffinfos)
                :action (lambda (e)
                          (unless (numberp e) (setq e (cdr e)))
                          (my-goto-line e)))
    (message "NO git-gutters!")))

;; }}

(defun my-git-find-file-in-commit (&optional level)
  "Find file in previous commit with LEVEL.
If LEVEL > 0, find file in previous LEVEL commit."
  (interactive "P")
  (my-ensure 'magit)
  (let* ((rev (concat "HEAD" (if (and level (> level 0)) (make-string level ?^))))
         (pretty (string-trim (shell-command-to-string (format "git --no-pager log %s --oneline --no-walk" rev))))
         (prompt (format "Find file from commit [%s]: " pretty))
         (cmd (my-git-files-in-rev-command rev level))
         (default-directory (my-git-root-dir))
         (file (completing-read prompt (my-lines-from-command-output cmd))))
    (when file
      (find-file file))))

(defun my-git-commit-create ()
  "Git commit."
  (interactive)
  (let ((msg (read-string "Git commit message: ")))
    (when (> (length msg) 0)
      (shell-command (format "git commit --no-verify -m \"%s\"" msg)))))

(defun my-git-commit-amend (&optional reuse-p)
  "Git amend.  If REUSE-P is t, commit by reusing original message."
  (interactive)
  (let* ((original-msg  (shell-command-to-string "git log --pretty=format:'%s' -n1"))
         msg
         (extra-args (if reuse-p "--reuse-message=HEAD" ""))
         cmd)

    (setq msg (unless reuse-p
                (read-string "Git amend message: " original-msg)))
    (when (or reuse-p (> (length msg) 0))
      (setq cmd (format "git commit --no-verify --amend %s" extra-args))
      (unless reuse-p
        (setq cmd (format "%s -m \"%s\"" cmd msg)))
      (shell-command cmd))))

(defun my-git-current-branch ()
  "Show current branch name."
  (interactive)
  (message "Git current branch: %s"
           (string-trim (shell-command-to-string "git branch --show-current"))))

(provide 'init-git)
;;; init-git.el ends here
