;;; git-gutter.el --- Port of Sublime Text plugin GitGutter -*- lexical-binding: t; -*-

;; Copyright (C) 2014 by Syohei YOSHIDA

;; Author: Syohei YOSHIDA <syohex@gmail.com>
;; URL: https://github.com/syohex/emacs-git-gutter
;; Package-Version: 0.80
;; Version: 0.80
;; Package-Requires: ((cl-lib "0.5") (emacs "24"))

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

(defcustom git-gutter:window-width nil
  "Character width of gutter window. Emacs mistakes width of some characters.
It is better to explicitly assign width to this variable, if you use full-width
character for signs of changes"
  :type 'integer
  :group 'git-gutter)

(defcustom git-gutter:diff-option ""
  "Option of 'git diff'"
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:mercurial-diff-option ""
  "Option of 'hg diff'"
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:bazaar-diff-option ""
  "Option of 'bzr diff'"
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
  "Each command of this list is executed, gutter information is updated and
gutter information of other windows."
  :type '(list (function :tag "Update command")
               (repeat :inline t (function :tag "Update command")))
  :group 'git-gutter)

(defcustom git-gutter:update-hooks
  '(after-save-hook after-revert-hook find-file-hook after-change-major-mode-hook
    text-scale-mode-hook magit-revert-buffer-hook)
  "hook points of updating gutter"
  :type '(list (hook :tag "HookPoint")
               (repeat :inline t (hook :tag "HookPoint")))
  :group 'git-gutter)

(defcustom git-gutter:always-show-separator nil
  "Show separator even if there are no changes."
  :type 'boolean
  :group 'git-gutter)

(defcustom git-gutter:separator-sign nil
  "Separator sign"
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:modified-sign "="
  "Modified sign"
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:added-sign "+"
  "Added sign"
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:deleted-sign "-"
  "Deleted sign"
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:unchanged-sign nil
  "Unchanged sign"
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:hide-gutter nil
  "Hide gutter if there are no changes"
  :type 'boolean
  :group 'git-gutter)

(defcustom git-gutter:lighter " GitGutter"
  "Minor mode lighter in mode-line"
  :type 'string
  :group 'git-gutter)

(defcustom git-gutter:verbosity 0
  "Log/message level. 4 means all, 0 nothing."
  :type 'integer
  :group 'git-gutter)

(defface git-gutter:separator
  '((t (:foreground "cyan" :weight bold)))
  "Face of separator"
  :group 'git-gutter)

(defface git-gutter:modified
  '((t (:foreground "magenta" :weight bold)))
  "Face of modified"
  :group 'git-gutter)

(defface git-gutter:added
  '((t (:foreground "green" :weight bold)))
  "Face of added"
  :group 'git-gutter)

(defface git-gutter:deleted
  '((t (:foreground "red" :weight bold)))
  "Face of deleted"
  :group 'git-gutter)

(defface git-gutter:unchanged
  '((t (:background "yellow")))
  "Face of unchanged"
  :group 'git-gutter)

(defcustom git-gutter:disabled-modes nil
  "A list of modes which `global-git-gutter-mode' should be disabled."
  :type '(repeat symbol)
  :group 'git-gutter)

(defcustom git-gutter:handled-backends '(git)
  "List of version control backends for which `git-gutter.el` will be used.
`git', `hg', and `bzr' are supported."
  :type '(repeat symbol)
  :group 'git-gutter)

(defvar git-gutter:view-diff-function 'git-gutter:view-diff-infos
  "Function of viewing changes")

(defvar git-gutter:clear-function 'git-gutter:clear-diff-infos
  "Function of clear changes")

(defvar git-gutter:init-function 'nil
  "Function of initialize")

(defcustom git-gutter-mode-on-hook nil
  "Hook run when git-gutter mode enable"
  :type 'hook
  :group 'git-gutter)

(defcustom git-gutter-mode-off-hook nil
  "Hook run when git-gutter mode disable"
  :type 'hook
  :group 'git-gutter)

(defvar git-gutter:enabled nil)
(defvar git-gutter:toggle-flag t)
(defvar git-gutter:force nil)
(defvar git-gutter:diffinfos nil)
(defvar git-gutter:has-indirect-buffers nil)
(defvar git-gutter:real-this-command nil)
(defvar git-gutter:linum-enabled nil)
(defvar git-gutter:linum-prev-window-margin nil)
(defvar git-gutter:vcs-type nil)
(defvar git-gutter:start-revision nil)
(defvar git-gutter:revision-history nil)

(defvar git-gutter:popup-buffer "*git-gutter:diff*")
(defvar git-gutter:ignore-commands
  '(minibuffer-complete-and-exit
    exit-minibuffer
    ido-exit-minibuffer
    helm-maybe-exit-minibuffer
    helm-confirm-and-exit-minibuffer))

(defmacro git-gutter:awhen (test &rest body)
  "Anaphoric when."
  (declare (indent 1))
  `(let ((it ,test))
     (when it ,@body)))

(defsubst git-gutter:execute-command (cmd output &rest args)
  (apply 'process-file cmd nil output nil args))

(defun git-gutter:in-git-repository-p ()
  (when (executable-find "git")
    (with-temp-buffer
      (when (zerop (git-gutter:execute-command "git" t "rev-parse" "--is-inside-work-tree"))
        (goto-char (point-min))
        (string= "true" (buffer-substring-no-properties
                         (point) (line-end-position)))))))

(defun git-gutter:in-hg-repository-p ()
  (and (executable-find "hg")
       (locate-dominating-file default-directory ".hg")
       (zerop (git-gutter:execute-command "hg" nil "root"))
       (not (string-match-p "/\.hg/" default-directory))))

(defun git-gutter:in-bzr-repository-p ()
  (and (executable-find "bzr")
       (locate-dominating-file default-directory ".bzr")
       (zerop (git-gutter:execute-command "bzr" nil "root"))
       (not (string-match-p "/\.bzr/" default-directory))))

(defsubst git-gutter:vcs-check-function (vcs)
  (cl-case vcs
    (git 'git-gutter:in-git-repository-p)
    (hg 'git-gutter:in-hg-repository-p)
    (bzr 'git-gutter:in-bzr-repository-p)))

(defsubst git-gutter:in-repository-p ()
  (cl-loop for vcs in git-gutter:handled-backends
           for check-func = (git-gutter:vcs-check-function vcs)
           when (funcall check-func)
           return (set (make-local-variable 'git-gutter:vcs-type) vcs)))

(defsubst git-gutter:changes-to-number (str)
  (if (string= str "")
      1
    (string-to-number str)))

(defsubst git-gutter:make-diffinfo (type content start end)
  (list :type type :content content :start-line start :end-line end))

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

(defun git-gutter:process-diff-output (proc)
  (when (buffer-live-p (process-buffer proc))
    (let ((regexp "^@@ -\\(?:[0-9]+\\),?\\([0-9]*\\) \\+\\([0-9]+\\),?\\([0-9]*\\) @@"))
      (with-current-buffer (process-buffer proc)
        (goto-char (point-min))
        (cl-loop while (re-search-forward regexp nil t)
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
                   (git-gutter:make-diffinfo type content start end)))))))

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
    (nreverse (cons file args))))

(defun git-gutter:start-git-diff-process (file proc-buf)
  (let ((arg (git-gutter:git-diff-arguments file)))
    (apply 'start-file-process "git-gutter" proc-buf
           "git" "--no-pager" "diff" "--no-color" "--no-ext-diff" "--relative" "-U0"
           arg)))

(defun git-gutter:hg-diff-arguments (file)
  (let (args)
    (unless (string= git-gutter:mercurial-diff-option "")
      (setq args (nreverse (split-string git-gutter:mercurial-diff-option))))
    (when (git-gutter:revision-set-p)
      (push "-r" args)
      (push git-gutter:start-revision args))
    (nreverse (cons file args))))

(defsubst git-gutter:start-hg-diff-process (file proc-buf)
  (let ((args (git-gutter:hg-diff-arguments file)))
    (apply 'start-file-process "git-gutter" proc-buf "hg" "diff" "-U0" args)))

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
    (apply 'start-file-process "git-gutter" proc-buf
           "bzr" "diff" "--context=0" args)))

(defun git-gutter:start-diff-process1 (file proc-buf)
  (cl-case git-gutter:vcs-type
    (git (git-gutter:start-git-diff-process file proc-buf))
    (hg (git-gutter:start-hg-diff-process file proc-buf))
    (bzr (git-gutter:start-bzr-diff-process file proc-buf))))

(defun git-gutter:start-diff-process (curfile proc-buf)
  (git-gutter:set-window-margin (git-gutter:window-margin))
  (let ((file (git-gutter:base-file)) ;; for tramp
        (curbuf (current-buffer))
        (process (git-gutter:start-diff-process1 curfile proc-buf)))
    (set-process-query-on-exit-flag process nil)
    (set-process-sentinel
     process
     (lambda (proc _event)
       (when (eq (process-status proc) 'exit)
         (setq git-gutter:enabled nil)
         (let ((diffinfos (git-gutter:process-diff-output proc)))
           (when (buffer-live-p curbuf)
             (with-current-buffer curbuf
               (git-gutter:update-diffinfo diffinfos)
               (when git-gutter:has-indirect-buffers
                 (git-gutter:update-indirect-buffers file))
               (setq git-gutter:enabled t)))
           (kill-buffer proc-buf)))))))

(defsubst git-gutter:gutter-sperator ()
  (when git-gutter:separator-sign
    (propertize git-gutter:separator-sign 'face 'git-gutter:separator)))

(defun git-gutter:before-string (sign)
  (let ((gutter-sep (concat sign (git-gutter:gutter-sperator))))
    (propertize " " 'display `((margin left-margin) ,gutter-sep))))

(defsubst git-gutter:select-face (type)
  (cl-case type
    (added 'git-gutter:added)
    (modified 'git-gutter:modified)
    (deleted 'git-gutter:deleted)))

(defsubst git-gutter:select-sign (type)
  (cl-case type
    (added git-gutter:added-sign)
    (modified git-gutter:modified-sign)
    (deleted git-gutter:deleted-sign)))

(defun git-gutter:propertized-sign (type)
  (let ((sign (git-gutter:select-sign type))
        (face (git-gutter:select-face type)))
    (propertize sign 'face face)))

(defsubst git-gutter:linum-get-overlay (pos)
  (cl-loop for ov in (overlays-in pos pos)
           when (overlay-get ov 'linum-str)
           return ov))

(defun git-gutter:view-at-pos-linum (sign pos)
  (git-gutter:awhen (git-gutter:linum-get-overlay pos)
    (overlay-put it 'before-string
                 (propertize " "
                             'display
                             `((margin left-margin)
                               ,(concat sign (overlay-get it 'linum-str)))))))

(defun git-gutter:view-at-pos (sign pos)
  (if git-gutter:linum-enabled
      (git-gutter:view-at-pos-linum sign pos)
    (let ((ov (make-overlay pos pos)))
      (overlay-put ov 'before-string (git-gutter:before-string sign))
      (overlay-put ov 'git-gutter t))))

(defsubst git-gutter:sign-width (sign)
  (cl-loop for s across sign
           sum (char-width s)))

(defun git-gutter:longest-sign-width ()
  (let ((signs (list git-gutter:modified-sign
                     git-gutter:added-sign
                     git-gutter:deleted-sign)))
    (when git-gutter:unchanged-sign
      (push git-gutter:unchanged-sign signs))
    (+ (apply 'max (mapcar 'git-gutter:sign-width signs))
       (git-gutter:sign-width git-gutter:separator-sign))))

(defun git-gutter:view-for-unchanged ()
  (save-excursion
    (let ((sign (if git-gutter:unchanged-sign
                    (propertize git-gutter:unchanged-sign
                                'face 'git-gutter:unchanged)
                  " ")))
      (goto-char (point-min))
      (while (not (eobp))
        (git-gutter:view-at-pos sign (point))
        (forward-line 1)))))

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
         (unless global-linum-mode
           (git-gutter:update-other-window-buffers (selected-window) (current-buffer))))))

(defsubst git-gutter:diff-process-buffer (curfile)
  (concat " *git-gutter-" curfile "-*"))

(defun git-gutter:kill-buffer-hook ()
  (let ((buf (git-gutter:diff-process-buffer (git-gutter:base-file))))
    (git-gutter:awhen (get-buffer buf)
      (kill-buffer it))))

(defsubst git-gutter:linum-padding ()
  (cl-loop repeat (git-gutter:window-margin)
           collect " " into paddings
           finally return (apply 'concat paddings)))

(defun git-gutter:linum-prepend-spaces ()
  (save-excursion
    (goto-char (point-min))
    (let ((padding (git-gutter:linum-padding)))
      (while (not (eobp))
        (git-gutter:view-at-pos-linum padding (point))
        (forward-line 1)))))

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
  (set (make-local-variable 'git-gutter:linum-enabled) t)
  (make-local-variable 'git-gutter:linum-prev-window-margin))

;;;###autoload
(defun git-gutter:linum-setup ()
  "Setup for linum-mode."
  (setq git-gutter:init-function 'git-gutter:linum-init
        git-gutter:view-diff-function nil)
  (defadvice linum-update-window (after git-gutter:linum-update-window activate)
    (if (and git-gutter-mode git-gutter:diffinfos)
        (git-gutter:linum-update git-gutter:diffinfos)
      (let ((curwin (get-buffer-window))
            (margin (or git-gutter:linum-prev-window-margin
                        (car (window-margins)))))
        (set-window-margins curwin margin (cdr (window-margins curwin)))))))

;;;###autoload
(define-minor-mode git-gutter-mode
  "Git-Gutter mode"
  :group      'git-gutter
  :init-value nil
  :global     nil
  :lighter    git-gutter:lighter
  (if git-gutter-mode
      (if (and (git-gutter:check-file-and-directory)
               (git-gutter:in-repository-p))
          (progn
            (when git-gutter:init-function
              (funcall git-gutter:init-function))
            (make-local-variable 'git-gutter:enabled)
            (set (make-local-variable 'git-gutter:has-indirect-buffers) nil)
            (set (make-local-variable 'git-gutter:toggle-flag) t)
            (make-local-variable 'git-gutter:diffinfos)
            (set (make-local-variable 'git-gutter:start-revision) nil)
            (add-hook 'kill-buffer-hook 'git-gutter:kill-buffer-hook nil t)
            (add-hook 'pre-command-hook 'git-gutter:pre-command-hook)
            (add-hook 'post-command-hook 'git-gutter:post-command-hook nil t)
            (dolist (hook git-gutter:update-hooks)
              (add-hook hook 'git-gutter nil t))
            (git-gutter))
        (when (> git-gutter:verbosity 2)
          (message "Here is not Git/Mercurial work tree"))
        (git-gutter-mode -1))
    (remove-hook 'kill-buffer-hook 'git-gutter:kill-buffer-hook t)
    (remove-hook 'pre-command-hook 'git-gutter:pre-command-hook)
    (remove-hook 'post-command-hook 'git-gutter:post-command-hook t)
    (dolist (hook git-gutter:update-hooks)
      (remove-hook hook 'git-gutter t))
    (git-gutter:clear)))

(defun git-gutter--turn-on ()
  (when (and (buffer-file-name)
             (not (memq major-mode git-gutter:disabled-modes)))
    (git-gutter-mode +1)))

;;;###autoload
(define-global-minor-mode global-git-gutter-mode git-gutter-mode git-gutter--turn-on
  :group 'git-gutter)

(defsubst git-gutter:show-gutter-p (diffinfos)
  (if git-gutter:hide-gutter
      (or diffinfos git-gutter:unchanged-sign)
    (or global-git-gutter-mode git-gutter:unchanged-sign diffinfos)))

(defun git-gutter:show-gutter (diffinfos)
  (when (git-gutter:show-gutter-p diffinfos)
    (git-gutter:set-window-margin (git-gutter:window-margin))))

(defun git-gutter:view-set-overlays (diffinfos)
  (save-excursion
    (goto-char (point-min))
    (cl-loop with curline = 1
             for info in diffinfos
             for start-line = (plist-get info :start-line)
             for end-line = (plist-get info :end-line)
             for type = (plist-get info :type)
             for sign = (git-gutter:propertized-sign type)
             do
             (progn
               (forward-line (- start-line curline))
               (cl-case type
                 ((modified added)
                  (setq curline start-line)
                  (while (and (<= curline end-line) (not (eobp)))
                    (git-gutter:view-at-pos sign (point))
                    (cl-incf curline)
                    (forward-line 1)))
                 (deleted
                  (git-gutter:view-at-pos sign (point))
                  (forward-line 1)
                  (setq curline (1+ end-line))))))))

(defun git-gutter:view-diff-infos (diffinfos)
  (when (or diffinfos git-gutter:always-show-separator)
    (when (or git-gutter:unchanged-sign git-gutter:separator-sign)
      (git-gutter:view-for-unchanged))
    (git-gutter:view-set-overlays diffinfos))
  (git-gutter:show-gutter diffinfos))

(defsubst git-gutter:reset-window-margin-p ()
  (or git-gutter:force
      git-gutter:hide-gutter
      (not global-git-gutter-mode)))

(defun git-gutter:clear-diff-infos ()
  (when (git-gutter:reset-window-margin-p)
    (git-gutter:set-window-margin 0))
  (remove-overlays (point-min) (point-max) 'git-gutter t))

(defsubst git-gutter:clear-gutter ()
  (when git-gutter:clear-function
    (funcall git-gutter:clear-function)))

(defun git-gutter:update-diffinfo (diffinfos)
  (save-restriction
    (widen)
    (git-gutter:clear-gutter)
    (setq git-gutter:diffinfos diffinfos)
    (when git-gutter:view-diff-function
      (funcall git-gutter:view-diff-function diffinfos))))

(defun git-gutter:search-near-diff-index (diffinfos is-reverse)
  (cl-loop with current-line = (line-number-at-pos)
           with cmp-fn = (if is-reverse '> '<)
           for diffinfo in (if is-reverse (reverse diffinfos) diffinfos)
           for index = 0 then (1+ index)
           for start-line = (plist-get diffinfo :start-line)
           when (funcall cmp-fn current-line start-line)
           return (if is-reverse
                      (1- (- (length diffinfos) index))
                    index)))

(defun git-gutter:search-here-diffinfo (diffinfos)
  (cl-loop with current-line = (line-number-at-pos)
           for diffinfo in diffinfos
           for start = (plist-get diffinfo :start-line)
           for end   = (or (plist-get diffinfo :end-line) (1+ start))
           when (and (>= current-line start) (<= current-line end))
           return diffinfo))

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
    (let ((start-line (plist-get diffinfo :start-line))
          (end-line (plist-get diffinfo :end-line))
          (content (plist-get diffinfo :content)))
      (cl-case (plist-get diffinfo :type)
        (added (git-gutter:delete-added-lines start-line end-line))
        (deleted (when (git-gutter:delete-from-first-line-p start-line end-line)
                   (forward-line start-line))
                 (git-gutter:insert-deleted-lines content))
        (modified (git-gutter:delete-added-lines start-line end-line)
                  (git-gutter:insert-deleted-lines content))))))

(defsubst git-gutter:popup-buffer-window ()
  (get-buffer-window (get-buffer git-gutter:popup-buffer)))

;;;###autoload
(defun git-gutter:revert-hunk ()
  "Revert current hunk."
  (interactive)
  (git-gutter:awhen (git-gutter:search-here-diffinfo git-gutter:diffinfos)
    (save-window-excursion
      (git-gutter:popup-hunk it)
      (when (yes-or-no-p "Revert current hunk ?")
        (git-gutter:do-revert-hunk it)
        (save-buffer))
      (delete-window (git-gutter:popup-buffer-window)))))

(defun git-gutter:extract-hunk-header ()
  (git-gutter:awhen (git-gutter:base-file)
    (with-temp-buffer
      (when (zerop (git-gutter:execute-command "git" t "diff" "--relative" it))
        (goto-char (point-min))
        (forward-line 4)
        (buffer-substring-no-properties (point-min) (point))))))

(defun git-gutter:read-hunk-header (header)
  (let ((header-regexp "^@@ -\\([0-9]+\\),?\\([0-9]*\\) \\+\\([0-9]+\\),?\\([0-9]*\\) @@"))
    (when (string-match header-regexp header)
      (list (string-to-number (match-string 1 header))
            (git-gutter:changes-to-number (match-string 2 header))
            (string-to-number (match-string 3 header))
            (git-gutter:changes-to-number (match-string 4 header))))))

(defun git-gutter:convert-hunk-header (type)
  (let ((header (buffer-substring-no-properties (point) (line-end-position))))
    (delete-region (point) (line-end-position))
    (cl-destructuring-bind
        (orig-line orig-changes new-line new-changes) (git-gutter:read-hunk-header header)
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
  (let ((content (plist-get diff-info :content))
        (type (plist-get diff-info :type))
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
        (unless (zerop (apply 'git-gutter:execute-command
                              "git" nil "apply" "--unidiff-zero"
                              options))
          (message "Failed: stating this hunk"))
        (delete-file patch)))))

;;;###autoload
(defun git-gutter:stage-hunk ()
  "Stage this hunk like 'git add -p'."
  (interactive)
  (git-gutter:awhen (git-gutter:search-here-diffinfo git-gutter:diffinfos)
    (save-window-excursion
      (git-gutter:popup-hunk it)
      (when (yes-or-no-p "Stage current hunk ?")
        (git-gutter:do-stage-hunk it)
        (git-gutter))
      (delete-window (git-gutter:popup-buffer-window)))))

(defun git-gutter:update-popuped-buffer (diffinfo)
  (with-current-buffer (get-buffer-create git-gutter:popup-buffer)
    (view-mode -1)
    (setq buffer-read-only nil)
    (erase-buffer)
    (insert (plist-get diffinfo :content))
    (insert "\n")
    (goto-char (point-min))
    (diff-mode)
    (view-mode +1)
    (current-buffer)))

;;;###autoload
(defun git-gutter:popup-hunk (&optional diffinfo)
  "Popup current diff hunk."
  (interactive)
  (git-gutter:awhen (or diffinfo
                        (git-gutter:search-here-diffinfo git-gutter:diffinfos))
    (save-selected-window
      (pop-to-buffer (git-gutter:update-popuped-buffer it)))))

;;;###autoload
(defun git-gutter:next-hunk (arg)
  "Move to next diff hunk"
  (interactive "p")
  (if (not git-gutter:diffinfos)
      (when (> git-gutter:verbosity 3)
        (message "There are no changes!!"))
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
      (forward-line (1- (plist-get diffinfo :start-line)))
      (when (buffer-live-p (get-buffer git-gutter:popup-buffer))
        (git-gutter:update-popuped-buffer diffinfo)))))

;;;###autoload
(defun git-gutter:previous-hunk (arg)
  "Move to previous diff hunk"
  (interactive "p")
  (git-gutter:next-hunk (- arg)))

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
  (when (or git-gutter:force git-gutter:toggle-flag)
    (let* ((file (git-gutter:base-file))
           (proc-buf (git-gutter:diff-process-buffer file)))
      (when (and (called-interactively-p 'interactive) (get-buffer proc-buf))
        (kill-buffer proc-buf))
      (when (and file (file-exists-p file) (not (get-buffer proc-buf)))
        (git-gutter:start-diff-process (file-name-nondirectory file)
                                       (get-buffer-create proc-buf))))))

(defadvice make-indirect-buffer (before git-gutter:has-indirect-buffers activate)
  (when (and git-gutter-mode (not (buffer-base-buffer)))
    (setq git-gutter:has-indirect-buffers t)))

(defadvice vc-revert (after git-gutter:vc-revert activate)
  (when git-gutter-mode
    (run-with-idle-timer 0.1 nil 'git-gutter)))

;; `quit-window' and `switch-to-buffer' are called from other
;; commands. So we should use `defadvice' instead of `post-command-hook'.
(defadvice quit-window (after git-gutter:quit-window activate)
  (when git-gutter-mode
    (git-gutter)))

(defadvice switch-to-buffer (after git-gutter:switch-to-buffer activate)
  (when git-gutter-mode
    (git-gutter)))

;;;###autoload
(defun git-gutter:clear ()
  "Clear diff information in gutter."
  (interactive)
  (save-restriction
    (widen)
    (git-gutter:clear-gutter))
  (setq git-gutter:enabled nil
        git-gutter:diffinfos nil))

;;;###autoload
(defun git-gutter:toggle ()
  "Toggle to show diff information."
  (interactive)
  (let ((git-gutter:force t))
    (if git-gutter:enabled
        (progn
          (git-gutter:clear)
          (setq git-gutter-mode nil
                git-gutter:toggle-flag nil))
      (git-gutter)
      (setq git-gutter-mode t
            git-gutter:toggle-flag t))
    (force-mode-line-update)))

(defun git-gutter:revision-valid-p (revision)
  (zerop (cl-case git-gutter:vcs-type
           (git (git-gutter:execute-command "git" nil
                                            "rev-parse" "--quiet" "--verify"
                                            revision))
           (hg (git-gutter:execute-command "hg" nil "id" "-r" revision))
           (bzr (git-gutter:execute-command "bzr" nil
                                            "revno" "-r" revision)))))

;;;###autoload
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

;;;###autoload
(defun git-gutter:update-all-windows ()
  "Update git-gutter informations for all visible buffers."
  (interactive)
  (dolist (win (window-list))
    (let ((buf (window-buffer win)))
      (with-current-buffer buf
        (when git-gutter-mode
          (git-gutter))))))

;; for linum-user
(when (and global-linum-mode (not (boundp 'git-gutter-fringe)))
  (git-gutter:linum-setup))

(provide 'git-gutter)

;;; git-gutter.el ends here
