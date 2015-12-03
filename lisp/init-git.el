;; Solution 1: disable all vc backends
;; @see http://stackoverflow.com/questions/5748814/how-does-one-disable-vc-git-in-emacs
;; (setq vc-handled-backends ())

;; ;; Solution 2: if NO network mounted drive involved
(setq vc-handled-backends '(Git SVN Hg))

;; ;; Solution 3: setup vc-handled-backends per project
;; (setq vc-handled-backends ())
;; (defun my-setup-develop-environment ()
;;   (interactive)
;;   (cond
;;    ((string-match-p (file-truename "~/.emacs.d") (file-name-directory (buffer-file-name))
;;     (setq vc-handled-backends '(Git)))
;;    (t (setq vc-handled-backends nil))))
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
  (let (parent)
    (if (eq git-gutter:vcs-type 'svn)
        (setq parent "PREV")
      (setq parent "HEAD^"))
    (git-gutter:set-start-revision parent)
    (message "git-gutter:set-start-revision parent of HEAD")
    ))

(defun git-gutter-reset-to-default ()
  (interactive)
  (git-gutter:set-start-revision nil)
  (message "git-gutter reset"))

                                        ; If you enable global minor mode
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
  (let (rlt)
    (setq rlt
          (replace-regexp-in-string
           (concat "^" (file-name-as-directory default-directory))
           ""
           buffer-file-name))
    ;; (message "rlt=%s" rlt)
    rlt))

(defun git-reset-current-file ()
  "git reset file of current buffer"
  (interactive)
  (let ((filename))
    (when buffer-file-name
      (setq filename (git-get-current-file-relative-path))
      (shell-command (concat "git reset " filename))
      (message "DONE! git reset %s" filename)
      )))

(defun git-add-current-file ()
  "git add file of current buffer"
  (interactive)
  (let ((filename))
    (when buffer-file-name
      (setq filename (git-get-current-file-relative-path))
      (shell-command (concat "git add " filename))
      (message "DONE! git add %s" filename)
      )))

(defun git-push-remote-origin ()
  "run `git push'"
  (interactive)
  (when buffer-file-name
    (shell-command "git push")
    (message "DONE! git push at %s" default-directory)
    ))

(defun git-add-option-update ()
  "git add only tracked files of default directory"
  (interactive)
  (when buffer-file-name
    (shell-command "git add -u")
    (message "DONE! git add -u %s" default-directory)
    ))


;; {{ goto next/previous hunk
(defun my-goto-next-hunk (arg)
  (interactive "p")
  (forward-line)
  (if (re-search-forward "\\(^<<<<<<<\\|^=======\\|^>>>>>>>\\)" (point-max) t)
      (goto-char (line-beginning-position))
    (forward-line -1)
    (git-gutter:next-hunk arg)))

(defun my-goto-previous-hunk (arg)
  (interactive "p")
  (forward-line -1)
  (if (re-search-backward "\\(^>>>>>>>\\|^=======\\|^<<<<<<<\\)" (point-min) t)
      (goto-char (line-beginning-position))
    (forward-line -1)
    (git-gutter:previous-hunk arg)))

;; {{ git-messenger
;; show details to play `git blame' game
(setq git-messenger:show-detail t)
(add-hook 'git-messenger:after-popup-hook
          (lambda (msg)
            ;; extract commit id and put into the kill ring
            (when (string-match "\\(commit *: *\\)\\([0-9a-z]+\\)" msg)
              (copy-yank-str (match-string 2 msg))
              (message "commit hash %s => clipboard & kill-ring" (match-string 2 msg))
              )))
(global-set-key (kbd "C-x v p") 'git-messenger:popup-message)
;; }}

;; {{ @see http://oremacs.com/2015/04/19/git-grep-ivy/
(defun counsel-git-grep-function (string &optional is-find-file)
  "Grep in the current git repository for STRING."
  (let (cmd)
    (setq cmd (format
               (if is-find-file "git ls-tree -r HEAD --name-status | grep \"%s\""
                 "git --no-pager grep --full-name -n --no-color -i -e \"%s\"")
               string))
    (split-string
     (shell-command-to-string cmd)
     "\n"
     t)))

(defun counsel-git-grep-or-find-api (open-another-window &optional is-find-file)
  "Grep a string or fine a file in the current git repository."
  (let ((default-directory (locate-dominating-file
                            default-directory ".git"))
        (keyword (if (region-active-p)
                     (buffer-substring-no-properties (region-beginning) (region-end))
                   (read-string (concat "Enter " (if is-find-file "file" "grep") " pattern:" ))))
        collection val lst)

    (when (and (setq collection (counsel-git-grep-function keyword is-find-file))
               (> (length collection) 0))
      (setq val (if (= 1 (length collection)) (car collection)
                    (ivy-read (format " matching \"%s\":" keyword) collection)))
      (setq lst (split-string val ":"))
      (funcall (if open-another-window 'find-file-other-window 'find-file)
               (if (listp lst) (car lst) lst))
        (let ((linenum (string-to-number (cadr lst))))
          (when (and linenum (> linenum 0))
            (goto-char (point-min))
            (forward-line (1- linenum))
            )))))

(defun counsel-git-grep (&optional open-another-window)
  "Grep for a string in the current git repository.
If OPEN-ANOTHER-WINDOW is not nil, results are displayed in new window."
  (interactive "P")
  (counsel-git-grep-or-find-api open-another-window))

(defun counsel-git-find-file (&optional open-another-window)
  "Find file  in the current git repository.
If OPEN-ANOTHER-WINDOW is not nil, results are displayed in new window."
  (interactive "P")
  (counsel-git-grep-or-find-api open-another-window t))
;; }}

(provide 'init-git)

