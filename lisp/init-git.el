;; -*- coding: utf-8; lexical-binding: t; -*-

;; ;; {{ Solution 1: disable all vc backends
;; @see http://stackoverflow.com/questions/5748814/how-does-one-disable-vc-git-in-emacs
;; (setq vc-handled-backends ())
;; }}


;; {{ Solution 2: if NO network mounted drive involved
(setq vc-handled-backends '(Git SVN Hg))
;; @see https://www.reddit.com/r/emacs/comments/4c0mi3/the_biggest_performance_improvement_to_emacs_ive/
;; open files faster but you can't check if file is version
;; controlled. other VCS functionality still works.
(remove-hook 'find-file-hooks 'vc-find-file-hook)
;; }}

;; ;; {{ Solution 3: setup vc-handled-backends per project
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
;; ;; }}

;; {{ git-gutter
(local-require 'git-gutter)

(defun git-gutter-reset-to-head-parent()
  (interactive)
  (let (parent (filename (buffer-file-name)))
    (if (eq git-gutter:vcs-type 'svn)
        (setq parent "PREV")
      (setq parent (if filename (concat (shell-command-to-string (concat "git --no-pager log --oneline -n1 --pretty=\"format:%H\" " filename)) "^") "HEAD^")))
    (git-gutter:set-start-revision parent)
    (message "git-gutter:set-start-revision HEAD^")))

(defun git-gutter-reset-to-default ()
  (interactive)
  (git-gutter:set-start-revision nil)
  (message "git-gutter reset"))

(global-git-gutter-mode t)

;; nobody use bzr
;; I could be forced to use subversion or hg which has higher priority
(custom-set-variables '(git-gutter:handled-backends '(svn hg git)))

(unless (fboundp 'global-display-line-numbers-mode)
 ;; git-gutter's workaround for linum-mode bug.
 ;; should not be used in `display-line-number-mode`
 (git-gutter:linum-setup))

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
  "Open git snapshot with the selected version."
  (interactive)
  (unless (featurep 'git-timemachine)
    (require 'git-timemachine))
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
      (message "Tracked files is commited."))
     (t
      (message "Do nothing!")))))

(defun git-add-current-file ()
  "Git add file of current buffer."
  (interactive)
  (when buffer-file-name
    (let* ((filename (git-get-current-file-relative-path)))
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

(defun my-git-log-trace-definition ()
  "Similar to `magit-log-trace-definition' but UI is simpler.
If multi-lines are selected, trace the defintion of line range.
If only one line is selected, use current selection as function name to look up.
If nothing is selected, use the word under cursor as function name to look up."
  (interactive)
  (when buffer-file-name
    (let* ((range-or-func (cond
                           ((region-active-p)
                            (cond
                             ((my-is-one-line (region-beginning) (region-end))
                              (format ":%s" (my-selected-str)))
                             (t
                              (format "%s,%s"
                                      (line-number-at-pos (region-beginning))
                                      (line-number-at-pos (region-end))))))
                           (t
                            (format ":%s" (thing-at-point 'symbol)))))
           (cmd (format "git log -L%s:%s" range-or-func (file-truename buffer-file-name)))
           (content (shell-command-to-string cmd)))
      (when (string-match-p "no match" content)
        ;; mark current function and try again
        (mark-defun)
        (setq range-or-func (format "%s,%s"
                                    (line-number-at-pos (region-beginning))
                                    (line-number-at-pos (region-end))))
        (setq cmd (format "git log -L%s:%s" range-or-func (file-truename buffer-file-name))))
      (message cmd)
      (unless (featurep 'find-file-in-project) (require 'find-file-in-project))
      (ffip-show-content-in-diff-mode (shell-command-to-string cmd)))))

(eval-after-load 'magit
  '(progn
    (ivy-mode 1)))

(provide 'init-git)
