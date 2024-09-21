;;; git-gutter.el --- Port of Sublime Text plugin GitGutter -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2020 Syohei YOSHIDA <syohex@gmail.com>
;; Copyright (C) 2020-2022 Neil Okamoto <neil.okamoto+melpa@gmail.com>
;; Copyright (C) 2020-2024 Shen, Jen-Chieh <jcs090218@gmail.com>

;; Author: Syohei YOSHIDA <syohex@gmail.com>
;; Maintainer: Neil Okamoto <neil.okamoto+melpa@gmail.com>
;;             Shen, Jen-Chieh <jcs090218@gmail.com>
;; URL: https://github.com/emacsorphanage/git-gutter
;; Version: 0.94
;; Package-Requires: ((emacs "25.1"))

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; Port of GitGutter which is a plugin of Sublime Text

;;; Code:

(require 'cl-lib)

(defgroup git-gutter nil
  "Port GitGutter"
  :prefix "git-gutter:"
  :group 'vc)

(defvar git-gutter-mode nil)

(defcustom git-gutter:window-width nil
  "Character width of gutter window.  Emacs mistakes width of some characters.
It is better to explicitly assign width to this variable, if you use full-width
character for signs of changes"
  :type 'integer
  :group 'git-gutter)

(defcustom git-gutter:diff-option ""
  "Option of 'git diff'."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:subversion-diff-option ""
  "Option of 'svn diff'."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:mercurial-diff-option ""
  "Option of 'hg diff'."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:bazaar-diff-option ""
  "Option of 'bzr diff'."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:update-commands
  '(ido-switch-buffer helm-buffers-list)
  "Each command of this list is executed, gutter information is updated."
  :type '(list (function :tag "Update command")
               (repeat :inline t (function :tag "Update command")))
  :group 'git-gutter)

(defcustom git-gutter:update-windows-commands
  '(kill-buffer ido-kill-buffer)
  "Each command of this list is executed, gutter information is
updated and gutter information of other windows."
  :type '(list (function :tag "Update command")
               (repeat :inline t (function :tag "Update command")))
  :group 'git-gutter)

(defcustom git-gutter:update-hooks
  '(after-save-hook
    after-revert-hook
    find-file-hook
    after-change-major-mode-hook
    text-scale-mode-hook)
  "Hook points of updating gutter."
  :type '(list (hook :tag "HookPoint")
               (repeat :inline t (hook :tag "HookPoint")))
  :group 'git-gutter)

(defcustom git-gutter:always-show-separator nil
  "Show separator even if there are no changes."
  :type 'boolean
  :group 'git-gutter)

(defcustom git-gutter:separator-sign nil
  "Separator sign."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:modified-sign "="
  "Modified sign."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:added-sign "+"
  "Added sign."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:deleted-sign "-"
  "Deleted sign."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:unchanged-sign nil
  "Unchanged sign."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:hide-gutter nil
  "Hide gutter if there are no changes."
  :type 'boolean
  :group 'git-gutter)

(defcustom git-gutter:lighter " GitGutter"
  "Minor mode lighter in mode-line."
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:verbosity 0
  "Log/message level.  4 means all, 0 nothing."
  :type 'integer
  :group 'git-gutter)

(defcustom git-gutter:visual-line nil
  "Show sign at gutter by visual line."
  :type 'boolean
  :group 'git-gutter)

(defface git-gutter:separator
  '((t (:foreground "cyan" :weight bold :inherit default)))
  "Face of separator")

(defface git-gutter:modified
  '((t (:foreground "magenta" :weight bold :inherit default)))
  "Face of modified")

(defface git-gutter:added
  '((t (:foreground "green" :weight bold :inherit default)))
  "Face of added")

(defface git-gutter:deleted
  '((t (:foreground "red" :weight bold :inherit default)))
  "Face of deleted")

(defface git-gutter:unchanged
  '((t (:background "yellow" :inherit default)))
  "Face of unchanged")

(defcustom git-gutter:disabled-modes nil
  "A list of modes which `global-git-gutter-mode' should be disabled."
  :type '(repeat symbol)
  :group 'git-gutter)

(defcustom git-gutter:handled-backends '(git)
  "List of version control backends for which `git-gutter.el` will be used.
`git', `svn', `hg', and `bzr' are supported."
  :type '(repeat symbol)
  :group 'git-gutter)

(defvar git-gutter:view-diff-function #'git-gutter:view-diff-infos
  "Function of viewing changes.")

(defvar git-gutter:clear-function #'git-gutter:clear-diff-infos
  "Function of clear changes.")

(defvar git-gutter:init-function 'nil
  "Function of initialize.")

(defcustom git-gutter-mode-on-hook nil
  "Hook run when git-gutter mode enable."
  :type 'hook
  :group 'git-gutter)

(defcustom git-gutter-mode-off-hook nil
  "Hook run when git-gutter mode disable."
  :type 'hook
  :group 'git-gutter)

(defcustom git-gutter:update-interval 0
  "Time interval in seconds for updating diff information."
  :type 'integer
  :group 'git-gutter)

(defcustom git-gutter:ask-p t
  "Ask whether commit/revert or not."
  :type 'boolean
  :group 'git-gutter)

(defcustom git-gutter:display-p t
  "Display diff information or not."
  :type 'boolean
  :group 'git-gutter)

(defvar git-gutter:start-revision nil
  "Starting revision for vc diffs.
Can be a directory-local variable in your project.")

(make-variable-buffer-local 'git-gutter:start-revision)
(put 'git-gutter:start-revision 'safe-local-variable
     (lambda (x) (or (booleanp x) (stringp x))))

(cl-defstruct git-gutter-hunk
  type content start-line end-line)

(defvar-local git-gutter:enabled nil)
(defvar git-gutter:diffinfos nil)
(defvar git-gutter:has-indirect-buffers nil)
(defvar git-gutter:real-this-command nil)
(defvar git-gutter:linum-enabled nil)
(defvar git-gutter:linum-prev-window-margin nil)
(defvar git-gutter:vcs-type nil)
(defvar git-gutter:revision-history nil)
(defvar git-gutter:update-timer nil)
(defvar-local git-gutter:last-chars-modified-tick nil)

(defvar git-gutter:popup-buffer "*git-gutter:diff*")
(defvar git-gutter:ignore-commands
  '(minibuffer-complete-and-exit
    exit-minibuffer
    ido-exit-minibuffer
    helm-maybe-exit-minibuffer
    helm-confirm-and-exit-minibuffer))

(defmacro git-gutter:awhen (test &rest body)
  "Anaphoric when.
Argument TEST is the case before BODY execution."
  (declare (indent 1))
  `(let ((it ,test))
     (when it ,@body)))

(defsubst git-gutter:execute-command (cmd output &rest args)
  (apply #'process-file cmd nil output nil args))

(defun git-gutter:in-git-repository-p ()
  (when (executable-find "git" t)
    (with-temp-buffer
      (when-let ((exec-result (git-gutter:execute-command
                               "git" t "rev-parse" "--is-inside-work-tree")))
        (when (zerop exec-result)
          (goto-char (point-min))
          (looking-at-p "true"))))))

(defun git-gutter:in-repository-common-p (cmd check-subcmd repodir)
  (and (executable-find cmd t)
       (locate-dominating-file default-directory repodir)
       (zerop (apply #'git-gutter:execute-command cmd nil check-subcmd))
       (not (string-match-p (regexp-quote (concat "/" repodir "/"))
                            default-directory))))

(defun git-gutter:vcs-check-function (vcs)
  (cl-case vcs
    (git (git-gutter:in-git-repository-p))
    (svn (git-gutter:in-repository-common-p "svn" '("info") ".svn"))
    (hg (git-gutter:in-repository-common-p "hg" '("root") ".hg"))
    (bzr (git-gutter:in-repository-common-p "bzr" '("root") ".bzr"))))

(defun git-gutter:in-repository-p ()
  (cl-loop for vcs in git-gutter:handled-backends
           when (git-gutter:vcs-check-function vcs)
           return (setq-local git-gutter:vcs-type vcs)))

(defsubst git-gutter:changes-to-number (str)
  (if (string= str "")
      1
    (string-to-number str)))

(defsubst git-gutter:base-file ()
  (buffer-file-name (buffer-base-buffer)))

(defun git-gutter:diff-content ()
  (save-excursion
    (goto-char (line-beginning-position))
    (let ((curpoint (point)))
      (forward-line 1)
      (if (re-search-forward "^@@" nil t)
          (backward-char 3) ;; for '@@'
        (goto-char (point-max)))
      (buffer-substring curpoint (point)))))

(defvar git-gutter:diff-output-regexp
  "^@@ -\\(?:[0-9]+\\),?\\([0-9]*\\) \\+\\([0-9]+\\),?\\([0-9]*\\) @@"
  "Parse diff output.")

(defun git-gutter:process-diff-output (buf)
  (when (buffer-live-p buf)
    (with-current-buffer buf
      (goto-char (point-min))
      (cl-loop while (re-search-forward git-gutter:diff-output-regexp nil t)
               for new-line  = (string-to-number (match-string 2))
               for orig-changes = (git-gutter:changes-to-number (match-string 1))
               for new-changes = (git-gutter:changes-to-number (match-string 3))
               for type = (cond ((zerop orig-changes) 'added)
                                ((zerop new-changes) 'deleted)
                                (t 'modified))
               for end-line = (if (eq type 'deleted)
                                  new-line
                                (1- (+ new-line new-changes)))
               for content = (git-gutter:diff-content)
               collect
               (let ((start (if (zerop new-line) 1 new-line))
                     (end (if (zerop end-line) 1 end-line)))
                 (make-git-gutter-hunk
                  :type type :content content :start-line start :end-line end))))))

(defsubst git-gutter:window-margin ()
  (or git-gutter:window-width (git-gutter:longest-sign-width)))

(defun git-gutter:set-window-margin (width)
  (when (and (not git-gutter:linum-enabled) (>= width 0))
    (let ((curwin (get-buffer-window)))
      (set-window-margins curwin width (cdr (window-margins curwin))))))

(defsubst git-gutter:revision-set-p ()
  (and git-gutter:start-revision (not (string= git-gutter:start-revision ""))))

(defun git-gutter:git-diff-arguments (file)
  (let (args)
    (unless (string= git-gutter:diff-option "")
      (setq args (nreverse (split-string git-gutter:diff-option))))
    (when (git-gutter:revision-set-p)
      (push git-gutter:start-revision args))
    (push "--" args)
    (nreverse (cons file args))))

(defun git-gutter:start-git-diff-process (file proc-buf)
  (let ((arg (git-gutter:git-diff-arguments file)))
    (apply #'start-file-process "git-gutter" proc-buf
           "git" "--no-pager" "-c" "diff.autorefreshindex=0"
           "diff" "--no-color" "--no-ext-diff" "--relative" "-U0"
           arg)))

(defun git-gutter:svn-diff-arguments (file)
  (let (args)
    (unless (string= git-gutter:subversion-diff-option "")
      (setq args (nreverse (split-string git-gutter:subversion-diff-option))))
    (when (git-gutter:revision-set-p)
      (push "-r" args)
      (push git-gutter:start-revision args))
    (nreverse (cons file args))))

(defsubst git-gutter:start-svn-diff-process (file proc-buf)
  (let ((args (git-gutter:svn-diff-arguments file)))
    (apply #'start-file-process "git-gutter" proc-buf "svn" "diff" "--diff-cmd"
           "diff" "-x" "-U0" args)))

(defun git-gutter:hg-diff-arguments (file)
  (let (args)
    (unless (string= git-gutter:mercurial-diff-option "")
      (setq args (nreverse (split-string git-gutter:mercurial-diff-option))))
    (when (git-gutter:revision-set-p)
      (push "-r" args)
      (push git-gutter:start-revision args))
    (nreverse (cons file args))))

(defsubst git-gutter:start-hg-diff-process (file proc-buf)
  (let ((args (git-gutter:hg-diff-arguments file))
        (process-environment (cons "HGPLAIN=1" process-environment)))
    (apply #'start-file-process "git-gutter" proc-buf "hg" "diff" "-U0" args)))

(defun git-gutter:bzr-diff-arguments (file)
  (let (args)
    (unless (string= git-gutter:bazaar-diff-option "")
      (setq args (nreverse (split-string git-gutter:bazaar-diff-option))))
    (when (git-gutter:revision-set-p)
      (push "-r" args)
      (push git-gutter:start-revision args))
    (nreverse (cons file args))))

(defsubst git-gutter:start-bzr-diff-process (file proc-buf)
  (let ((args (git-gutter:bzr-diff-arguments file)))
    (apply #'start-file-process "git-gutter" proc-buf
           "bzr" "diff" "--context=0" args)))

(defun git-gutter:start-diff-process1 (file proc-buf)
  (cl-case git-gutter:vcs-type
    (git (git-gutter:start-git-diff-process file proc-buf))
    (svn (git-gutter:start-svn-diff-process file proc-buf))
    (hg (git-gutter:start-hg-diff-process file proc-buf))
    (bzr (git-gutter:start-bzr-diff-process file proc-buf))))

(defun git-gutter:start-diff-process (curfile proc-buf)
  (let ((file (git-gutter:base-file)) ;; for tramp
        (curbuf (current-buffer))
        (process (git-gutter:start-diff-process1 curfile proc-buf)))
    (set-process-query-on-exit-flag process nil)
    (set-process-sentinel
     process
     (lambda (proc _event)
       (when (eq (process-status proc) 'exit)
         (setq git-gutter:enabled nil)
         (let ((diffinfos (git-gutter:process-diff-output (process-buffer proc))))
           (when (buffer-live-p curbuf)
             (with-current-buffer curbuf
               (git-gutter:update-diffinfo diffinfos)
               (when git-gutter:has-indirect-buffers
                 (git-gutter:update-indirect-buffers file))
               (setq git-gutter:enabled t)))
           (kill-buffer proc-buf)))))))

(defsubst git-gutter:gutter-seperator ()
  (when git-gutter:separator-sign
    (propertize git-gutter:separator-sign 'face 'git-gutter:separator)))

(defun git-gutter:before-string (sign)
  (let ((gutter-sep (concat sign (git-gutter:gutter-seperator))))
    (propertize " " 'display `((margin left-margin) ,gutter-sep))))

(defun git-gutter:propertized-sign (type)
  (let (sign face)
    (cl-case type
      (added (setq sign git-gutter:added-sign
                   face 'git-gutter:added))
      (modified (setq sign git-gutter:modified-sign
                      face 'git-gutter:modified))
      (deleted (setq sign git-gutter:deleted-sign
                     face 'git-gutter:deleted)))
    (when (get-text-property 0 'face sign)
      (setq face (append
                  (get-text-property 0 'face sign)
                  `(:inherit ,face))))
    (propertize sign 'face face)))

(defsubst git-gutter:linum-get-overlay (pos)
  (cl-loop for ov in (overlays-in pos pos)
           when (overlay-get ov 'linum-str)
           return ov))

(defun git-gutter:put-signs-linum (sign points)
  (dolist (pos points)
    (git-gutter:awhen (git-gutter:linum-get-overlay pos)
      (overlay-put it 'before-string
                   (propertize " "
                               'display
                               `((margin left-margin)
                                 ,(concat sign (overlay-get it 'linum-str))))))))

(defun git-gutter:put-signs (sign points)
  (if git-gutter:linum-enabled
      (git-gutter:put-signs-linum sign points)
    (dolist (pos points)
      (let ((ov (make-overlay pos pos))
            (gutter-sign (git-gutter:before-string sign)))
        (overlay-put ov 'before-string gutter-sign)
        (overlay-put ov 'git-gutter t)))))

(defsubst git-gutter:sign-width (sign)
  (cl-loop for s across sign
           sum (char-width s)))

(defun git-gutter:longest-sign-width ()
  (let ((signs (list git-gutter:modified-sign
                     git-gutter:added-sign
                     git-gutter:deleted-sign)))
    (when git-gutter:unchanged-sign
      (push git-gutter:unchanged-sign signs))
    (+ (apply #'max (mapcar 'git-gutter:sign-width signs))
       (git-gutter:sign-width git-gutter:separator-sign))))

(defun git-gutter:next-visual-line (arg)
  (let ((line-move-visual t))
    (or (ignore-errors
          ;; next-line raises exception at end of buffer
          (with-no-warnings
            (next-line arg))
          t)
        (goto-char (point-max)))))

(defun git-gutter:unchanged-line-p (line diffinfos)
  (cl-loop for info in diffinfos
           for start = (git-gutter-hunk-start-line info)
           for end = (git-gutter-hunk-end-line info)
           never (and (>= line start) (<= line end))))

(defun git-gutter:view-for-unchanged (diffinfos)
  (save-excursion
    (let ((sign (if git-gutter:unchanged-sign
                    (propertize git-gutter:unchanged-sign
                                'face 'git-gutter:unchanged)
                  " "))
          (move-fn (if git-gutter:visual-line
                       #'git-gutter:next-visual-line
                     #'forward-line))
          points)
      (goto-char (point-min))
      (while (not (eobp))
        (when (git-gutter:unchanged-line-p (line-number-at-pos) diffinfos)
          (push (point) points))
        (funcall move-fn 1))
      (git-gutter:put-signs sign points))))

(defsubst git-gutter:check-file-and-directory ()
  (and (git-gutter:base-file)
       default-directory (file-directory-p default-directory)))

(defun git-gutter:pre-command-hook ()
  (unless (memq this-command git-gutter:ignore-commands)
    (setq git-gutter:real-this-command this-command)))

(defun git-gutter:update-other-window-buffers (curwin curbuf)
  (save-selected-window
    (cl-loop for win in (window-list)
             unless (eq win curwin)
             do
             (progn
               (select-window win)
               (let ((win-width (window-margins win)))
                 (unless (car win-width)
                   (if (eq (current-buffer) curbuf)
                       (git-gutter:set-window-margin (git-gutter:window-margin))
                     (git-gutter:update-diffinfo git-gutter:diffinfos))))))))

(defun git-gutter:post-command-hook ()
  (cond ((memq git-gutter:real-this-command git-gutter:update-commands)
         (git-gutter))
        ((memq git-gutter:real-this-command git-gutter:update-windows-commands)
         (git-gutter)
         (unless (bound-and-true-p global-linum-mode)
           (git-gutter:update-other-window-buffers (selected-window)
                                                   (current-buffer))))))

(defsubst git-gutter:diff-process-buffer (curfile)
  (concat " *git-gutter-" curfile "-*"))

(defun git-gutter:kill-buffer-hook ()
  (let ((buf (git-gutter:diff-process-buffer (git-gutter:base-file))))
    (git-gutter:awhen (get-buffer buf)
      (kill-buffer it))))

(defsubst git-gutter:linum-padding ()
  (cl-loop repeat (git-gutter:window-margin)
           collect " " into paddings
           finally return (apply #'concat paddings)))

(defun git-gutter:linum-prepend-spaces ()
  (save-excursion
    (goto-char (point-min))
    (let ((padding (git-gutter:linum-padding))
          points)
      (while (not (eobp))
        (push (point) points)
        (forward-line 1))
      (git-gutter:put-signs-linum padding points))))

(defun git-gutter:linum-update (diffinfos)
  (let ((linum-width (car (window-margins))))
    (when linum-width
      (git-gutter:linum-prepend-spaces)
      (git-gutter:view-set-overlays diffinfos)
      (let ((curwin (get-buffer-window))
            (margin (+ linum-width (git-gutter:window-margin))))
        (setq git-gutter:linum-prev-window-margin margin)
        (set-window-margins curwin margin (cdr (window-margins curwin)))))))

(defun git-gutter:linum-init ()
  (setq-local git-gutter:linum-enabled t)
  (make-local-variable 'git-gutter:linum-prev-window-margin))

(defun git-gutter:linum-update-window (&rest _args)
  (when git-gutter:display-p
    (if (and git-gutter-mode git-gutter:diffinfos)
        (git-gutter:linum-update git-gutter:diffinfos)
      (let ((curwin (get-buffer-window))
            (margin (or git-gutter:linum-prev-window-margin
                        (car (window-margins)))))
        (set-window-margins curwin margin (cdr (window-margins curwin)))))))

;;;###autoload
(defun git-gutter:linum-setup ()
  "Setup for linum-mode."
  (setq git-gutter:init-function 'git-gutter:linum-init
        git-gutter:view-diff-function nil)
  (advice-add 'linum-update-window :after #'git-gutter:linum-update-window))

(defun git-gutter:show-backends ()
  (mapconcat (lambda (backend)
               (capitalize (symbol-name backend)))
             git-gutter:handled-backends "/"))

;;;###autoload
(define-minor-mode git-gutter-mode
  "Git-Gutter mode"
  :init-value nil
  :global     nil
  :lighter    git-gutter:lighter
  (if git-gutter-mode
      (if (and (git-gutter:check-file-and-directory)
               (git-gutter:in-repository-p))
          (progn
            (when git-gutter:init-function
              (funcall git-gutter:init-function))
            (make-local-variable 'git-gutter:diffinfos)
            ;;(setq-local git-gutter:start-revision nil)
            (add-hook 'kill-buffer-hook 'git-gutter:kill-buffer-hook nil t)
            (add-hook 'pre-command-hook 'git-gutter:pre-command-hook t)
            (add-hook 'post-command-hook 'git-gutter:post-command-hook nil t)
            (dolist (hook git-gutter:update-hooks)
              (add-hook hook 'git-gutter nil t))
            (git-gutter)
            (when (and (not git-gutter:update-timer)
                       (> git-gutter:update-interval 0))
              (setq git-gutter:update-timer
                    (run-with-idle-timer
                     git-gutter:update-interval t 'git-gutter:live-update))))
        (when (> git-gutter:verbosity 2)
          (message "Here is not %s work tree" (git-gutter:show-backends)))
        (git-gutter-mode -1))
    (remove-hook 'kill-buffer-hook 'git-gutter:kill-buffer-hook t)
    (remove-hook 'pre-command-hook 'git-gutter:pre-command-hook t)
    (remove-hook 'post-command-hook 'git-gutter:post-command-hook t)
    (dolist (hook git-gutter:update-hooks)
      (remove-hook hook 'git-gutter t))
    (git-gutter:clear-gutter)))

(defun git-gutter--turn-on ()
  (when (and (buffer-file-name)
             (not (memq major-mode git-gutter:disabled-modes)))
    (git-gutter-mode +1)))

;;;###autoload
(define-global-minor-mode global-git-gutter-mode git-gutter-mode git-gutter--turn-on)

(defsubst git-gutter:show-gutter-p (diffinfos)
  (if git-gutter:hide-gutter
      (or diffinfos git-gutter:unchanged-sign)
    (or global-git-gutter-mode git-gutter:unchanged-sign diffinfos)))

(defun git-gutter:show-gutter (diffinfos)
  (when (git-gutter:show-gutter-p diffinfos)
    (git-gutter:set-window-margin (git-gutter:window-margin))))

(defun git-gutter:view-set-overlays (diffinfos)
  (when (or git-gutter:unchanged-sign git-gutter:separator-sign)
    (git-gutter:view-for-unchanged diffinfos))
  (save-excursion
    (goto-char (point-min))
    (cl-loop with curline = 1
             with move-fn = (if git-gutter:visual-line
                                #'git-gutter:next-visual-line
                              #'forward-line)

             for info in diffinfos
             for start-line = (git-gutter-hunk-start-line info)
             for end-line = (git-gutter-hunk-end-line info)
             for type = (git-gutter-hunk-type info)
             for sign = (git-gutter:propertized-sign type)
             for points = nil
             do
             (let ((bound (progn
                            (forward-line (- end-line curline))
                            (point))))
               (forward-line (- start-line end-line))
               (cl-case type
                 ((modified added)
                  (while (and (<= (point) bound) (not (eobp)))
                    (push (point) points)
                    (funcall move-fn 1))
                  (git-gutter:put-signs sign points))
                 (deleted
                  (git-gutter:put-signs sign (list (point)))
                  (forward-line 1)))
               (setq curline (1+ end-line))))))

(defun git-gutter:view-diff-infos (diffinfos)
  (when (or diffinfos git-gutter:always-show-separator)
    (git-gutter:view-set-overlays diffinfos))
  (git-gutter:show-gutter diffinfos))

(defsubst git-gutter:reset-window-margin-p ()
  (or git-gutter:hide-gutter (not global-git-gutter-mode)))

(defun git-gutter:clear-diff-infos ()
  (when (git-gutter:reset-window-margin-p)
    (git-gutter:set-window-margin 0))
  (remove-overlays (point-min) (point-max) 'git-gutter t))

(defun git-gutter:clear-gutter ()
  (save-restriction
    (widen)
    (when git-gutter:clear-function
      (funcall git-gutter:clear-function)))
  (setq git-gutter:enabled nil
        git-gutter:last-chars-modified-tick nil
        git-gutter:diffinfos nil))

(defun git-gutter:update-diffinfo (diffinfos)
  (save-restriction
    (widen)
    (git-gutter:clear-gutter)
    (setq git-gutter:diffinfos diffinfos)
    (when (and git-gutter:display-p git-gutter:view-diff-function)
      (funcall git-gutter:view-diff-function diffinfos))))

(defun git-gutter:search-near-diff-index (diffinfos is-reverse)
  (cl-loop with current-line = (line-number-at-pos)
           with cmp-fn = (if is-reverse #'> #'<)
           for diffinfo in (if is-reverse (reverse diffinfos) diffinfos)
           for index = 0 then (1+ index)
           for start-line = (git-gutter-hunk-start-line diffinfo)
           when (funcall cmp-fn current-line start-line)
           return (if is-reverse
                      (1- (- (length diffinfos) index))
                    index)))

(defun git-gutter:search-here-diffinfo (diffinfos)
  (save-restriction
    (widen)
    (cl-loop with current-line = (line-number-at-pos)
             for diffinfo in diffinfos
             for start = (git-gutter-hunk-start-line diffinfo)
             for end   = (or (git-gutter-hunk-end-line diffinfo) (1+ start))
             when (and (>= current-line start) (<= current-line end))
             return diffinfo
             finally do (error "Here is not changed!!"))))

(defun git-gutter:collect-deleted-line (str)
  (with-temp-buffer
    (insert str)
    (goto-char (point-min))
    (cl-loop while (re-search-forward "^-\\(.*?\\)$" nil t)
             collect (match-string 1) into deleted-lines
             finally return deleted-lines)))

(defun git-gutter:delete-added-lines (start-line end-line)
  (forward-line (1- start-line))
  (let ((start-point (point)))
    (forward-line (1+ (- end-line start-line)))
    (delete-region start-point (point))))

(defun git-gutter:insert-deleted-lines (content)
  (dolist (line (git-gutter:collect-deleted-line content))
    (insert (concat line "\n"))))

(defsubst git-gutter:delete-from-first-line-p (start-line end-line)
  (and (not (= start-line 1)) (not (= end-line 1))))

(defun git-gutter:do-revert-hunk (diffinfo)
  (save-excursion
    (goto-char (point-min))
    (let ((start-line (git-gutter-hunk-start-line diffinfo))
          (end-line (git-gutter-hunk-end-line diffinfo))
          (content (git-gutter-hunk-content diffinfo)))
      (cl-case (git-gutter-hunk-type diffinfo)
        (added (git-gutter:delete-added-lines start-line end-line))
        (deleted (when (git-gutter:delete-from-first-line-p start-line end-line)
                   (forward-line start-line))
                 (git-gutter:insert-deleted-lines content))
        (modified (git-gutter:delete-added-lines start-line end-line)
                  (git-gutter:insert-deleted-lines content))))))

(defsubst git-gutter:popup-buffer-window ()
  (get-buffer-window (get-buffer git-gutter:popup-buffer)))

(defun git-gutter:query-action (action action-fn update-fn)
  (git-gutter:awhen (git-gutter:search-here-diffinfo git-gutter:diffinfos)
    (save-window-excursion
      (when git-gutter:ask-p
        (git-gutter:popup-hunk it))
      (when (or (not git-gutter:ask-p)
                (yes-or-no-p (format "%s current hunk ? " action)))
        (funcall action-fn it)
        (funcall update-fn))
      (if git-gutter:ask-p
          (delete-window (git-gutter:popup-buffer-window))
        (message "%s current hunk." action)))))

(defun git-gutter:revert-hunk ()
  "Revert current hunk."
  (interactive)
  (git-gutter:query-action "Revert" #'git-gutter:do-revert-hunk #'save-buffer))

(defun git-gutter:extract-hunk-header ()
  (git-gutter:awhen (git-gutter:base-file)
    (with-temp-buffer
      (when (zerop (git-gutter:execute-command
                    "git" t "--no-pager" "-c" "diff.autorefreshindex=0"
                    "diff" "--no-color" "--no-ext-diff"
                    "--relative" (file-name-nondirectory it)))
        (goto-char (point-min))
        (forward-line 4)
        (buffer-substring-no-properties (point-min) (point))))))

(defvar git-gutter:git-hunk-header-regexp
  "^@@ -\\([0-9]+\\),?\\([0-9]*\\) \\+\\([0-9]+\\),?\\([0-9]*\\) @@"
  "Parse git hunk header.")

(defun git-gutter:read-hunk-header (header)
  (when (string-match git-gutter:git-hunk-header-regexp header)
    (list (string-to-number (match-string 1 header))
          (git-gutter:changes-to-number (match-string 2 header))
          (string-to-number (match-string 3 header))
          (git-gutter:changes-to-number (match-string 4 header)))))

(defun git-gutter:convert-hunk-header (type)
  (let ((header (buffer-substring-no-properties (point) (line-end-position))))
    (delete-region (point) (line-end-position))
    (cl-destructuring-bind
        (orig-line orig-changes new-line new-changes)
        (git-gutter:read-hunk-header header)
      (cl-case type
        (added (setq new-line (1+ orig-line)))
        (t (setq new-line orig-line)))
      (let ((new-header (format "@@ -%d,%d +%d,%d @@"
                                orig-line orig-changes new-line new-changes)))
        (insert new-header)))))

(defun git-gutter:insert-staging-hunk (hunk type)
  (save-excursion
    (insert hunk "\n"))
  (git-gutter:convert-hunk-header type))

(defun git-gutter:apply-directory-option ()
  (let ((root (locate-dominating-file default-directory ".git")))
    (file-name-directory (file-relative-name (git-gutter:base-file) root))))

(defun git-gutter:do-stage-hunk (diff-info)
  (let ((content (git-gutter-hunk-content diff-info))
        (type (git-gutter-hunk-type diff-info))
        (header (git-gutter:extract-hunk-header))
        (patch (make-temp-name "git-gutter")))
    (when header
      (with-temp-file patch
        (insert header)
        (git-gutter:insert-staging-hunk content type))
      (let ((dir-option (git-gutter:apply-directory-option))
            (options (list "--cached" patch)))
        (when dir-option
          (setq options (cons "--directory" (cons dir-option options))))
        (unless (zerop (apply #'git-gutter:execute-command
                              "git" nil "apply" "--unidiff-zero"
                              options))
          (message "Failed: stating this hunk"))
        (delete-file patch)))))

(defun git-gutter:stage-hunk ()
  "Stage this hunk like 'git add -p'."
  (interactive)
  (git-gutter:query-action "Stage" #'git-gutter:do-stage-hunk #'git-gutter))

(defsubst git-gutter:line-point (line)
  (save-excursion
    (goto-char (point-min))
    (forward-line (1- line))
    (point)))

(defun git-gutter:mark-hunk ()
  (interactive)
  (git-gutter:awhen (git-gutter:search-here-diffinfo git-gutter:diffinfos)
    (let ((start (git-gutter:line-point (git-gutter-hunk-start-line it)))
          (end (git-gutter:line-point (1+ (git-gutter-hunk-end-line it)))))
      (goto-char start)
      (push-mark end nil t))))

(defun git-gutter:update-popuped-buffer (diffinfo)
  (with-current-buffer (get-buffer-create git-gutter:popup-buffer)
    (view-mode -1)
    (setq buffer-read-only nil)
    (erase-buffer)
    (insert (git-gutter-hunk-content diffinfo))
    (insert "\n")
    (goto-char (point-min))
    (diff-mode)
    (view-mode +1)
    (current-buffer)))

(defun git-gutter:popup-hunk (&optional diffinfo)
  "Popup current diff hunk."
  (interactive)
  (git-gutter:awhen (or diffinfo
                        (git-gutter:search-here-diffinfo git-gutter:diffinfos))
    (save-selected-window
      (display-buffer (git-gutter:update-popuped-buffer it)))))

(defun git-gutter:next-hunk (arg)
  "Move to next diff hunk"
  (interactive "p")
  (if (not git-gutter:diffinfos)
      (when (> git-gutter:verbosity 3)
        (message "There are no changes!!"))
    (save-restriction
      (widen)
      (let* ((is-reverse (< arg 0))
             (diffinfos git-gutter:diffinfos)
             (len (length diffinfos))
             (index (git-gutter:search-near-diff-index diffinfos is-reverse))
             (real-index (if index
                             (let ((next (if is-reverse (1+ index) (1- index))))
                               (mod (+ arg next) len))
                           (if is-reverse (1- len) 0)))
             (diffinfo (nth real-index diffinfos)))
        (goto-char (point-min))
        (forward-line (1- (git-gutter-hunk-start-line diffinfo)))
        (when (> git-gutter:verbosity 0)
          (message "Move to %d/%d hunk" (1+ real-index) len))
        (when (buffer-live-p (get-buffer git-gutter:popup-buffer))
          (git-gutter:update-popuped-buffer diffinfo))))))

(defun git-gutter:previous-hunk (arg)
  "Move to previous diff hunk"
  (interactive "p")
  (git-gutter:next-hunk (- arg)))

(defun git-gutter:end-of-hunk ()
  "Move to end of current diff hunk"
  (interactive)
  (git-gutter:awhen (git-gutter:search-here-diffinfo git-gutter:diffinfos)
    (let ((lines (- (git-gutter-hunk-end-line it) (line-number-at-pos))))
      (forward-line lines))))

(defalias 'git-gutter:next-diff 'git-gutter:next-hunk)
(make-obsolete 'git-gutter:next-diff 'git-gutter:next-hunk "0.60")
(defalias 'git-gutter:previous-diff 'git-gutter:previous-hunk)
(make-obsolete 'git-gutter:previous-diff 'git-gutter:previous-hunk "0.60")
(defalias 'git-gutter:popup-diff 'git-gutter:popup-hunk)
(make-obsolete 'git-gutter:popup-diff 'git-gutter:popup-hunk "0.60")

(defun git-gutter:update-indirect-buffers (orig-file)
  (cl-loop with diffinfos = git-gutter:diffinfos
           for win in (window-list)
           for buf  = (window-buffer win)
           for base = (buffer-base-buffer buf)
           when (and base (string= (buffer-file-name base) orig-file))
           do
           (with-current-buffer buf
             (git-gutter:update-diffinfo diffinfos))))

;;;###autoload
(defun git-gutter ()
  "Show diff information in gutter"
  (interactive)
  (when (or git-gutter:vcs-type (git-gutter:in-repository-p))
    (let* ((file (git-gutter:base-file))
           (proc-buf (git-gutter:diff-process-buffer file)))
      (when (and (called-interactively-p 'interactive) (get-buffer proc-buf))
        (kill-buffer proc-buf))
      (when (and file (file-exists-p file) (not (get-buffer proc-buf)))
        (git-gutter:start-diff-process (file-name-nondirectory file)
                                       (get-buffer-create proc-buf))))))

(defun git-gutter:kill-indirect-buffer ()
  (with-current-buffer (buffer-base-buffer)
    (when git-gutter:has-indirect-buffers
      (if (< 1 git-gutter:has-indirect-buffers)
          (setq git-gutter:has-indirect-buffers (1- git-gutter:has-indirect-buffers))
        (kill-local-variable 'git-gutter:has-indirect-buffers)))))

(defun git-gutter:make-indirect-buffer (oldfun base-buffer &rest args)
  (with-current-buffer (or (buffer-base-buffer (window-normalize-buffer base-buffer))
                           base-buffer)
    (if git-gutter:has-indirect-buffers
        (setq git-gutter:has-indirect-buffers (1+ git-gutter:has-indirect-buffers))
      (setq-local git-gutter:has-indirect-buffers 1))
    (with-current-buffer (apply oldfun base-buffer args)
      (add-hook 'kill-buffer-hook #'git-gutter:kill-indirect-buffer nil t)
      (current-buffer))))
(advice-add 'make-indirect-buffer :around #'git-gutter:make-indirect-buffer)

(defun git-gutter:vc-revert (&rest _args)
  (when git-gutter-mode
    (run-with-idle-timer 0.1 nil 'git-gutter)))
(advice-add 'vc-revert :after #'git-gutter:vc-revert)

(defun git-gutter:toggle-truncate-lines (&rest _args)
  (when (and git-gutter-mode git-gutter:visual-line)
    (run-with-idle-timer 0.1 nil 'git-gutter)))
(advice-add 'toggle-truncate-lines :after #'git-gutter:toggle-truncate-lines)

;; `quit-window' and `switch-to-buffer' are called from other
;; commands. So calling git-gutter from `post-command-hook' is not enough, use
;; advices instead.
(defun git-gutter:quit-window (&rest _args)
  (when git-gutter-mode
    (git-gutter)))
(advice-add 'quit-window :after #'git-gutter:quit-window)

(defun git-gutter:switch-to-buffer (&rest _args)
  (when git-gutter-mode
    (git-gutter)))
(advice-add 'switch-to-buffer :after #'git-gutter:switch-to-buffer)

(defun git-gutter:clear ()
  "Clear diff information in gutter."
  (interactive)
  (git-gutter-mode -1))
(make-obsolete 'git-gutter:clear #'git-gutter-mode "0.86")

;;;###autoload
(defun git-gutter:toggle ()
  "Toggle to show diff information."
  (interactive)
  (if git-gutter-mode
      (git-gutter-mode -1)
    (git-gutter-mode +1)))
(make-obsolete 'git-gutter:toggle #'git-gutter-mode "0.86")

(defun git-gutter:revision-valid-p (revision)
  (zerop (cl-case git-gutter:vcs-type
           (git (git-gutter:execute-command "git" nil
                                            "rev-parse" "--quiet" "--verify"
                                            revision))
           (svn (git-gutter:execute-command "svn" nil "info" "-r" revision
                                            (file-relative-name (buffer-file-name))))
           (hg (git-gutter:execute-command "hg" nil "id" "-r" revision))
           (bzr (git-gutter:execute-command "bzr" nil
                                            "revno" "-r" revision)))))

(defun git-gutter:set-start-revision (start-rev)
  "Set start revision. If `start-rev' is nil or empty string then reset
start revision."
  (interactive
   (list (read-string "Start Revision: "
                      nil 'git-gutter:revision-history)))
  (when (and start-rev (not (string= start-rev "")))
    (unless (git-gutter:revision-valid-p start-rev)
      (error "Revision '%s' is not valid." start-rev)))
  (setq git-gutter:start-revision start-rev)
  (git-gutter))

(defun git-gutter:update-all-windows ()
  "Update git-gutter information for all visible buffers."
  (interactive)
  (dolist (buf (buffer-list))
    (when (get-buffer-window buf 'visible)
      (with-current-buffer buf
        (when git-gutter-mode
          (git-gutter))))))

(defun git-gutter:start-update-timer ()
  (interactive)
  (when git-gutter:update-timer
    (error "Update timer is already running."))
  (setq git-gutter:update-timer
        (run-with-idle-timer git-gutter:update-interval t 'git-gutter:live-update)))

(defun git-gutter:cancel-update-timer ()
  (interactive)
  (unless git-gutter:update-timer
    (error "Timer is no running."))
  (cancel-timer git-gutter:update-timer)
  (setq git-gutter:update-timer nil))

(defsubst git-gutter:write-current-content (tmpfile)
  (let ((content (buffer-substring-no-properties (point-min) (point-max))))
    (with-temp-file tmpfile
      (insert content))))

(defun git-gutter:original-file-content (file vcs)
  (with-temp-buffer
    (cl-case vcs
      (git
       (when (zerop (process-file "git" nil t nil "show" (concat ":" file)))
         (buffer-substring-no-properties (point-min) (point-max))))
      ((svn hg bzr)
       (let ((command (symbol-name vcs)))
         (when (zerop (process-file command nil t nil "cat" file))
           (buffer-substring-no-properties (point-min) (point-max))))))))

(defun git-gutter:write-original-content (tmpfile filename)
  (git-gutter:awhen (git-gutter:original-file-content filename git-gutter:vcs-type)
    (with-temp-file tmpfile
      (insert it)
      t)))

(defsubst git-gutter:start-raw-diff-process (proc-buf original now)
  (start-file-process "git-gutter:update-timer" proc-buf
                      "diff" "-U0" original now))

(defun git-gutter:start-live-update (file original now)
  (let ((proc-bufname (git-gutter:diff-process-buffer file)))
    (when (get-buffer proc-bufname)
      (kill-buffer proc-bufname))
    (let* ((curbuf (current-buffer))
           (proc-buf (get-buffer-create proc-bufname))
           (process (git-gutter:start-raw-diff-process proc-buf original now)))
      (set-process-query-on-exit-flag process nil)
      (set-process-sentinel
       process
       (lambda (proc _event)
         (when (eq (process-status proc) 'exit)
           (setq git-gutter:enabled nil)
           (let ((diffinfos (git-gutter:process-diff-output (process-buffer proc))))
             (when (buffer-live-p curbuf)
               (with-current-buffer curbuf
                 (git-gutter:update-diffinfo diffinfos)
                 (setq git-gutter:enabled t)))
             (kill-buffer proc-buf)
             (delete-file original)
             (delete-file now))))))))

(defun git-gutter:should-update-p ()
  (let ((chars-modified-tick (buffer-chars-modified-tick)))
    (unless (equal chars-modified-tick git-gutter:last-chars-modified-tick)
      (setq git-gutter:last-chars-modified-tick chars-modified-tick))))

(defun git-gutter:vcs-root (vcs)
  (with-temp-buffer
    (cl-case vcs
      (git
       (when (zerop (process-file "git" nil t nil "rev-parse" "--show-toplevel"))
         (goto-char (point-min))
         (file-name-as-directory
          (buffer-substring-no-properties (point) (line-end-position)))))
      (svn
       (when (zerop (process-file "svn" nil t nil "info"))
         (goto-char (point-min))
         (when (re-search-forward "^Working Copy Root Path: \(.+\)$" nil t)
           (file-name-as-directory (match-string-no-properties 1)))))
      ((hg bzr)
       (let ((command (symbol-name vcs)))
         (when (zerop (process-file command nil t nil "root"))
           (goto-char (point-min))
           (file-name-as-directory
            (buffer-substring-no-properties (point) (line-end-position)))))))))

(defun git-gutter:live-update ()
  (git-gutter:awhen (git-gutter:base-file)
    (when (and git-gutter:enabled
               (git-gutter:should-update-p))
      (let ((file (file-name-nondirectory it))
            (root (file-truename (git-gutter:vcs-root git-gutter:vcs-type)))
            (now (make-temp-file "git-gutter-cur"))
            (original (make-temp-file "git-gutter-orig")))
        (if (git-gutter:write-original-content original (file-relative-name it root))
            (progn
              (git-gutter:write-current-content now)
              (git-gutter:start-live-update file original now))
          (delete-file now)
          (delete-file original))))))

;; for linum-user
(when (and (and (boundp 'global-linum-mode) global-linum-mode) (not (boundp 'git-gutter-fringe)))
  (git-gutter:linum-setup))

(defun git-gutter:all-hunks ()
  "Cound unstaged hunks in all buffers"
  (let ((sum 0))
    (dolist (buf (buffer-list))
      (with-current-buffer buf
        (when git-gutter-mode
          (cl-incf sum (git-gutter:buffer-hunks)))))
    sum))

(defun git-gutter:buffer-hunks ()
  "Count unstaged hunks in current buffer."
  (length git-gutter:diffinfos))

(defun git-gutter:stat-hunk (hunk)
  (cl-case (git-gutter-hunk-type hunk)
    (modified (with-temp-buffer
                (insert (git-gutter-hunk-content hunk))
                (goto-char (point-min))
                (let ((added 0)
                      (deleted 0))
                  (while (not (eobp))
                    (cond ((looking-at-p "\\+") (cl-incf added))
                          ((looking-at-p "\\-") (cl-incf deleted)))
                    (forward-line 1))
                  (cons added deleted))))
    (added (cons (- (git-gutter-hunk-end-line hunk)
                    (git-gutter-hunk-start-line hunk))
                 0))
    (deleted (cons 0
                   (- (git-gutter-hunk-end-line hunk)
                      (git-gutter-hunk-start-line hunk))))))

(defun git-gutter:statistic ()
  "Return statistic unstaged hunks in current buffer."
  (interactive)
  (cl-loop for hunk in git-gutter:diffinfos
           for (add . del) = (git-gutter:stat-hunk hunk)
           sum add into added
           sum del into deleted
           finally
           return (progn
                    (when (called-interactively-p 'interactive)
                      (message "Added %d lines, Deleted %d lines" added deleted))
                    (cons added deleted))))

(provide 'git-gutter)

;;; git-gutter.el ends here

;; Local Variables:
;; fill-column: 85
;; indent-tabs-mode: nil
;; elisp-lint-indent-specs: ((git-gutter:awhen . 1))
;; End:
