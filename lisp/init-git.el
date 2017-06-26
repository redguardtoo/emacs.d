;; Solution 1: disable all vc backends
;; @see http://stackoverflow.com/questions/5748814/how-does-one-disable-vc-git-in-emacs
;; (setq vc-handled-backends ())

;; ;; Solution 2: if NO network mounted drive involved
(setq vc-handled-backends '(Git SVN Hg))

;; @see https://www.reddit.com/r/emacs/comments/4c0mi3/the_biggest_performance_improvement_to_emacs_ive/
;; open files faster but you can't check if file is version
;; controlled. other vcs functionality still works.
(remove-hook 'find-file-hooks 'vc-find-file-hook)

;; ;; Solution 3: setup vc-handled-backends per project
;; (setq vc-handled-backends ())
;; (defun my-setup-develop-environment ()
;;   (interactive)
;;   (cond
;;    ((string-match-p (file-truename "~/.emacs.d") (file-name-directory (buffer-file-name))
;;     (setq vc-handled-backends '(Git)))
;;    (t (setq vc-handled-backends nil)))))
;; (add-hook 'java-mode-hook 'my-setup-develop-environment)
;; (add-hook 'emacs-lisp-mode-hook 'my-setup-develop-environment)
;; (add-hook 'org-mode-hook 'my-setup-develop-environment)
;; (add-hook 'js2-mode-hook 'my-setup-develop-environment)
;; (add-hook 'js-mode-hook 'my-setup-develop-environment)
;; (add-hook 'javascript-mode-hook 'my-setup-develop-environment)
;; (add-hook 'web-mode-hook 'my-setup-develop-environment)
;; (add-hook 'c++-mode-hook 'my-setup-develop-environment)
;; (add-hook 'c-mode-hook 'my-setup-develop-environment)

;; {{ git-gutter
(require 'git-gutter)

(defun git-gutter-reset-to-head-parent()
  (interactive)
  (let (parent (filename (buffer-file-name)))
    (if (eq git-gutter:vcs-type 'svn)
        (setq parent "PREV")
      (setq parent (if filename (concat (shell-command-to-string (concat "git --no-pager log --oneline -n1 --pretty='format:%H' " filename)) "^") "HEAD^")))
    (git-gutter:set-start-revision parent)
    (message "git-gutter:set-start-revision HEAD^")))

(defun git-gutter-reset-to-default ()
  (interactive)
  (git-gutter:set-start-revision nil)
  (message "git-gutter reset"))


;; If you enable global minor mode
(global-git-gutter-mode t)

;; nobody use bzr
;; people are forced use subversion or hg, so they take priority
(custom-set-variables '(git-gutter:handled-backends '(svn hg git)))

(git-gutter:linum-setup)

(global-set-key (kbd "C-x C-g") 'git-gutter:toggle)
(global-set-key (kbd "C-x v =") 'git-gutter:popup-hunk)
;; Stage current hunk
(global-set-key (kbd "C-x v s") 'git-gutter:stage-hunk)
;; Revert current hunk
(global-set-key (kbd "C-x v r") 'git-gutter:revert-hunk)
;; }}

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
                        (unless (string-match-p "^[a-z0-9]*$" (car rev))
                          (setq rev (cdr rev)))
                        (git-timemachine-show-revision rev)))))

(defun my-git-timemachine ()
  "Open git snapshot with the selected version.  Based on ivy-mode."
  (interactive)
  (unless (featurep 'git-timemachine)
    (require 'git-timemachine))
  (git-timemachine--start #'my-git-timemachine-show-selected-revision))
;; }}

;;----------------------------------------------------------------------------
;; git-svn conveniences
;;----------------------------------------------------------------------------
(eval-after-load 'compile
  '(progn
     (dolist (defn (list '(git-svn-updated "^\t[A-Z]\t\\(.*\\)$" 1 nil nil 0 1)
                         '(git-svn-needs-update "^\\(.*\\): needs update$" 1 nil nil 2 1)))
       (add-to-list 'compilation-error-regexp-alist-alist defn))
     (dolist (defn '(git-svn-updated git-svn-needs-update))
       (add-to-list 'compilation-error-regexp-alist defn))))

(defvar git-svn--available-commands nil "Cached list of git svn subcommands")

(defun git-svn (dir)
  "Run git svn"
  (interactive "DSelect directory: ")
  (unless git-svn--available-commands
    (setq git-svn--available-commands
          (string-all-matches "^  \\([a-z\\-]+\\) +" (shell-command-to-string "git svn help") 1)))
  (let* ((default-directory (vc-git-root dir))
         (compilation-buffer-name-function (lambda (major-mode-name) "*git-svn*")))
    (compile (concat "git svn "
                     (ido-completing-read "git-svn command: " git-svn--available-commands nil t)))))

(defun git-get-current-file-relative-path ()
  (replace-regexp-in-string (concat "^" (file-name-as-directory default-directory))
                            ""
                            buffer-file-name))

(defun git-checkout-current-file ()
  "git checkout urrent file"
  (interactive)
  (when (and (buffer-file-name)
             (yes-or-no-p (format "git checkout %s?"
                                  (file-name-nondirectory (buffer-file-name)))))
    (let* ((filename (git-get-current-file-relative-path)))
      (shell-command (concat "git checkout " filename))
      (message "DONE! git checkout %s" filename))))

(defun git-add-current-file ()
  "git add file of current buffer"
  (interactive)
  (let ((filename))
    (when buffer-file-name
      (setq filename (git-get-current-file-relative-path))
      (shell-command (concat "git add " filename))
      (message "DONE! git add %s" filename))))

;; {{ goto next/previous hunk
(defun my-goto-next-hunk (arg)
  (interactive "p")
  (if (memq major-mode '(diff-mode))
      (diff-hunk-next)
    (forward-line)
    (if (re-search-forward "\\(^<<<<<<<\\|^=======\\|^>>>>>>>\\)" (point-max) t)
        (goto-char (line-beginning-position))
      (forward-line -1)
      (git-gutter:next-hunk arg))))

(defun my-goto-previous-hunk (arg)
  (interactive "p")
  (if (memq major-mode '(diff-mode))
      (diff-hunk-prev)
    (forward-line -1)
    (if (re-search-backward "\\(^>>>>>>>\\|^=======\\|^<<<<<<<\\)" (point-min) t)
        (goto-char (line-beginning-position))
      (forward-line -1)
      (git-gutter:previous-hunk arg))))
;; }}

;; {{ git-gutter use ivy
(defun my-reshape-git-gutter (gutter)
  "Re-shape gutter for `ivy-read'."
  (let* ((linenum-start (aref gutter 3))
         (linenum-end (aref gutter 4))
         (target-line "")
         (target-linenum 1)
         (tmp-line "")
         (max-line-length 0))
    (save-excursion
      (while (<= linenum-start linenum-end)
        (goto-line linenum-start)
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

(defun my-goto-git-gutter ()
  (interactive)
  (if git-gutter:diffinfos
      (ivy-read "git-gutters:"
                (mapcar 'my-reshape-git-gutter git-gutter:diffinfos)
                :action (lambda (e)
                          (unless (numberp e) (setq e (cdr e)))
                          (goto-line e)))
    (message "NO git-gutters!")))

;; }}

(provide 'init-git)

