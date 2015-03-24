;;; helm-ls-git.el --- list git files. -*- lexical-binding: t -*-

;; Copyright (C) 2012 ~ 2014 Thierry Volpiatto <thierry.volpiatto@gmail.com>

;; Package-Requires: ((helm "1.5"))

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

;;; Code

(require 'cl-lib)
(require 'vc)
(require 'helm-files)

(defvaralias 'helm-c-source-ls-git 'helm-source-ls-git)
(make-obsolete-variable 'helm-c-source-ls-git 'helm-source-ls-git "1.5.1")
(defvaralias 'helm-c-source-ls-git-status 'helm-source-ls-git-status)
(make-obsolete-variable 'helm-c-source-ls-git-status 'helm-source-ls-git-status "1.5.1")


(defgroup helm-ls-git nil
  "Helm completion for git repos."
  :group 'helm)

(defcustom helm-ls-git-show-abs-or-relative 'absolute
  "Show full path or relative path to repo when using `helm-ff-toggle-basename'.
Valid values are symbol 'abs (default) or 'relative."
  :group 'helm-ls-git
  :type  '(radio :tag "Show full path or relative path to Git repo when toggling"
           (const :tag "Show full path" absolute)
           (const :tag "Show relative path" relative)))

(defcustom helm-ls-git-status-command 'vc-dir
  "Favorite git-status command for emacs."
  :group 'helm-ls-git
  :type 'symbol)

(defcustom helm-ls-git-fuzzy-match nil
  "Enable fuzzy matching in `helm-source-ls-git-status' and `helm-source-ls-git'."
  :group 'helm-ls-git
  :type 'boolean)

(defcustom helm-ls-git-grep-command "git grep -n%cH --color=never --full-name -e %p %f"
  "The git grep default command line.
The option \"--color=always\" can be used safely, it is disabled by default though.
The color of matched items can be customized in your .gitconfig."
  :group 'helm-ls-git
  :type 'string)

(defface helm-ls-git-modified-not-staged-face
    '((t :foreground "yellow"))
  "Files which are modified but not yet staged."
  :group 'helm-ls-git)

(defface helm-ls-git-modified-and-staged-face
    '((t :foreground "Gold"))
  "Files which are modified and already staged."
  :group 'helm-ls-git)

(defface helm-ls-git-renamed-modified-face
    '((t :foreground "Gold"))
  "Files which are renamed or renamed and modified."
  :group 'helm-ls-git)

(defface helm-ls-git-untracked-face
    '((t :foreground "red"))
  "Files which are not yet tracked by git."
  :group 'helm-ls-git)

(defface helm-ls-git-added-copied-face
    '((t :foreground "green"))
  "Files which are newly added or copied."
  :group 'helm-ls-git)

(defface helm-ls-git-added-modified-face
    '((t :foreground "blue"))
  "Files which are newly added and have unstaged modifications."
  :group 'helm-ls-git)

(defface helm-ls-git-deleted-not-staged-face
    '((t :foreground "Darkgoldenrod3"))
  "Files which are deleted but not staged."
  :group 'helm-ls-git)

(defface helm-ls-git-deleted-and-staged-face
    '((t :foreground "DimGray"))
  "Files which are deleted and staged."
  :group 'helm-ls-git)

(defface helm-ls-git-conflict-face
    '((t :foreground "MediumVioletRed"))
  "Files which contain rebase/merge conflicts."
  :group 'helm-ls-git)


(defvar helm-ls-git-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map helm-generic-files-map)
    (define-key map (kbd "C-s") 'helm-ls-git-run-grep)
    map))

;; Append visited files from `helm-source-ls-git' to `file-name-history'.
(add-to-list 'helm-files-save-history-extra-sources "Git files")


(defvar helm-ls-git-log-file nil) ; Set it for debugging.


(defun helm-ls-git-list-files ()
  (when (and helm-ls-git-log-file
             (file-exists-p helm-ls-git-log-file))
    (delete-file helm-ls-git-log-file))
  ;; `helm-resume' will use the value of `helm-default-directory'
  ;; as value for `default-directory'.
  (helm-aif (helm-ls-git-root-dir)
      (with-helm-default-directory it
          (with-output-to-string
              (with-current-buffer standard-output
                (apply #'process-file
                       "git"
                       nil (list t helm-ls-git-log-file) nil
                       (list "ls-files" "--full-name" "--")))))))

(cl-defun helm-ls-git-root-dir (&optional (directory default-directory))
  (let ((root (locate-dominating-file directory ".git")))
    (and root (file-name-as-directory root))))

(defun helm-ls-git-not-inside-git-repo ()
  (not (helm-ls-git-root-dir)))

(defun helm-ls-git-transformer (candidates)
  (cl-loop with root = (helm-ls-git-root-dir helm-default-directory)
        for i in candidates
        for abs = (expand-file-name i root)
        for disp = (if (and helm-ff-transformer-show-only-basename
                            (not (string-match "[.]\\{1,2\\}$" i)))
                       (helm-basename i)
                     (cl-case helm-ls-git-show-abs-or-relative
                       (absolute abs)
                       (relative i)))
        collect
        (cons (propertize disp 'face 'helm-ff-file) abs)))

(defun helm-ls-git-sort-fn (candidates)
  "Transformer for sorting candidates."
  (helm-ff-sort-candidates candidates nil))

(defun helm-ls-git-init ()
  (let ((data (helm-ls-git-list-files)))
    (when (string= data "")
      (setq data
            (if helm-ls-git-log-file
                (with-current-buffer
                    (find-file-noselect helm-ls-git-log-file)
                  (prog1
                      (buffer-substring-no-properties
                       (point-min) (point-max))
                    (kill-buffer)))
              data)))
    (helm-init-candidates-in-buffer 'global data)))

(defun helm-ls-git-header-name (name)
  (format "%s (%s)"
          name
          (with-temp-buffer
            (let ((ret (call-process-shell-command "git symbolic-ref --short HEAD" nil t)))
              ;; Use sha of HEAD when branch name is missing.
              (unless (zerop ret)
                (erase-buffer)
                (call-process-shell-command "git rev-parse --short HEAD" nil t)))
            (buffer-substring-no-properties (goto-char (point-min))
                                            (line-end-position)))))

(defun helm-ls-git-actions-list ()
  (let ((actions (helm-actions-from-type-file)))
    (helm-append-at-nth
     actions
     (helm-make-actions "Git grep files (`C-u' only files with ext, `C-u C-u' all)"
                        'helm-ls-git-grep
                        "Search in Git log (C-u show patch)"
                        'helm-ls-git-search-log)
     3)))

;; Define the sources.
(defvar helm-source-ls-git-status nil)
(defvar helm-source-ls-git nil)

;;;###autoload
(defclass helm-ls-git-source (helm-source-in-buffer)
  ((header-name :initform 'helm-ls-git-header-name)
   (init :initform 'helm-ls-git-init)
   (keymap :initform helm-ls-git-map)
   (help-message :initform helm-generic-file-help-message)
   (mode-line :initform helm-generic-file-mode-line-string)
   (match-part :initform (lambda (candidate)
                           (if helm-ff-transformer-show-only-basename
                               (helm-basename candidate)
                               candidate)))
   (candidate-transformer :initform '(helm-ls-git-transformer
                                      helm-ls-git-sort-fn))
   (action-transformer :initform 'helm-transform-file-load-el)
   (action :initform (helm-ls-git-actions-list))))

;;;###autoload
(defclass helm-ls-git-status-source (helm-source-in-buffer)
  ((header-name :initform 'helm-ls-git-header-name)
   (init :initform
         (lambda ()
           (helm-init-candidates-in-buffer 'global
             (helm-ls-git-status))))
   (keymap :initform helm-ls-git-map)
   (filtered-candidate-transformer :initform 'helm-ls-git-status-transformer)
   (persistent-action :initform 'helm-ls-git-diff)
   (persistent-help :initform "Diff")
   (action-transformer :initform 'helm-ls-git-status-action-transformer)
   (action :initform
           (helm-make-actions
            "Find file" 'helm-find-many-files
            "Git status" (lambda (_candidate)
                           (with-current-buffer helm-buffer
                             (funcall helm-ls-git-status-command
                                      helm-default-directory)))))))


(defun helm-ls-git-grep (_candidate)
  (let* ((helm-grep-default-command helm-ls-git-grep-command)
         helm-grep-default-recurse-command
         (files (cond ((equal helm-current-prefix-arg '(4))
                       (list "--"
                             (format "'%s'" (mapconcat
                                             'identity
                                             (helm-grep-get-file-extensions
                                             (helm-marked-candidates))
                                             " "))))
                      ((equal helm-current-prefix-arg '(16))
                       '("--"))
                      (t (helm-marked-candidates))))
         ;; Expand filename of each candidate with the git root dir.
         ;; The filename will be in the help-echo prop.
         (helm-grep-default-directory-fn 'helm-ls-git-root-dir)
         ;; set `helm-ff-default-directory' to the root of project.
         (helm-ff-default-directory (helm-ls-git-root-dir)))
    (helm-do-grep-1 files)))

(defun helm-ls-git-run-grep ()
  "Run Git Grep action from helm-ls-git."
  (interactive)
  (with-helm-alive-p
    (helm-quit-and-execute-action 'helm-ls-git-grep)))


(defun helm-ls-git-search-log (_candidate)
  (let* ((query (helm-read-string "Search log: "))
         (coms (if helm-current-prefix-arg
                   (list "log" "-p" "--grep" query)
                 (list "log" "--grep" query))))
    (with-current-buffer (get-buffer-create "*helm ls log*")
      (set (make-local-variable 'buffer-read-only) nil)
      (erase-buffer)
      (apply #'process-file "git" nil (list t nil) nil coms)))
  (pop-to-buffer "*helm ls log*")
  (goto-char (point-min))
  (diff-mode)
  (set (make-local-variable 'buffer-read-only) t))


(defun helm-ls-git-status ()
  (when (and helm-ls-git-log-file
             (file-exists-p helm-ls-git-log-file))
    (delete-file helm-ls-git-log-file))
  (with-output-to-string
      (with-current-buffer standard-output
        (apply #'process-file
               "git"
               nil (list t helm-ls-git-log-file) nil
               (list "status" "--porcelain")))))

(defun helm-ls-git-status-transformer (candidates _source)
  (cl-loop with root = (helm-ls-git-root-dir helm-default-directory)
        for i in candidates
        collect
        (cond ((string-match "^\\( M \\)\\(.*\\)" i) ; modified.
               (cons (propertize i 'face 'helm-ls-git-modified-not-staged-face)
                     (expand-file-name (match-string 2 i) root)))
              ((string-match "^\\(M+ *\\)\\(.*\\)" i) ; modified and staged.
               (cons (propertize i 'face 'helm-ls-git-modified-and-staged-face)
                     (expand-file-name (match-string 2 i) root)))
              ((string-match "^\\([?]\\{2\\} \\)\\(.*\\)" i)
               (cons (propertize i 'face 'helm-ls-git-untracked-face)
                     (expand-file-name (match-string 2 i) root)))
              ((string-match "^\\([AC] +\\)\\(.*\\)" i)
               (cons (propertize i 'face 'helm-ls-git-added-copied-face)
                     (expand-file-name (match-string 2 i) root)))
              ((string-match "^\\( [D] \\)\\(.*\\)" i)
               (cons (propertize i 'face 'helm-ls-git-deleted-not-staged-face)
                     (expand-file-name (match-string 2 i) root)))
              ((string-match "^\\(RM?\\).* -> \\(.*\\)" i)
               (cons (propertize i 'face 'helm-ls-git-renamed-modified-face)
                     (expand-file-name (match-string 2 i) root)))
              ((string-match "^\\([D] \\)\\(.*\\)" i)
               (cons (propertize i 'face 'helm-ls-git-deleted-and-staged-face)
                     (expand-file-name (match-string 2 i) root)))
              ((string-match "^\\(UU \\)\\(.*\\)" i)
               (cons (propertize i 'face 'helm-ls-git-conflict-face)
                     (expand-file-name (match-string 2 i) root)))
              ((string-match "^\\(AM \\)\\(.*\\)" i)
               (cons (propertize i 'face 'helm-ls-git-added-modified-face)
                     (expand-file-name (match-string 2 i) root)))
              (t i))))

(defun helm-ls-git-status-action-transformer (actions _candidate)
  (let ((disp (helm-get-selection nil t)))
    (cond ((string-match "^[?]\\{2\\}" disp)
           (append actions
                   (list '("Add file(s)"
                           . (lambda (candidate)
                               (let ((default-directory
                                      (file-name-directory candidate))
                                     (marked (helm-marked-candidates)))
                                 (vc-call-backend 'Git 'register marked))))
                         '("Delete file(s)" . helm-delete-marked-files)
                         '("Copy bnames to .gitignore"
                           . (lambda (candidate)
                               (let ((default-directory
                                      (file-name-directory candidate))
                                     (marked (helm-marked-candidates)))
                                 (with-current-buffer (find-file-noselect
                                                       (expand-file-name
                                                        ".gitignore"
                                                        (helm-ls-git-root-dir)))
                                   (goto-char (point-max))
                                   (cl-loop with last-bname 
                                         for f in marked
                                         for bname = (helm-basename f)
                                         unless (string= bname last-bname)
                                         do (insert (concat bname "\n"))
                                         do (setq last-bname bname))
                                   (save-buffer))))))))
          ((string-match "^ ?M+ *" disp)
           (append actions (list '("Diff file" . helm-ls-git-diff)
                                 '("Commit file(s)"
                                   . (lambda (candidate)
                                       (let* ((marked (helm-marked-candidates))
                                              (default-directory
                                               (file-name-directory (car marked))))
                                         (vc-checkin marked 'Git))))
                                 '("Revert file(s)" . (lambda (candidate)
                                                     (let ((marked (helm-marked-candidates)))
                                                       (cl-loop for f in marked do
                                                             (progn
                                                               (vc-git-revert f)
                                                               (helm-aif (get-file-buffer f)
                                                                   (with-current-buffer it
                                                                     (revert-buffer t t)))))))))))
          ((string-match "^ D " disp)
           (append actions (list '("Git delete" . vc-git-delete-file))))
          (t actions))))

(defun helm-ls-git-diff (candidate)
  (let (helm-persistent-action-use-special-display)
    (with-current-buffer (find-file-noselect candidate)
      (when (buffer-live-p (get-buffer "*vc-diff*"))
        (kill-buffer "*vc-diff*")
        (balance-windows))
      (call-interactively #'vc-diff))))


;;;###autoload
(defun helm-ls-git-ls ()
  (interactive)
  (unless (and helm-source-ls-git-status
               helm-source-ls-git)
    (setq helm-source-ls-git-status
          (helm-make-source "Git status" 'helm-ls-git-status-source
            :fuzzy-match helm-ls-git-fuzzy-match)
          helm-source-ls-git
          (helm-make-source "Git files" 'helm-ls-git-source
            :fuzzy-match helm-ls-git-fuzzy-match)))
  (helm :sources '(helm-source-ls-git-status
                   helm-source-ls-git)
        ;; When `helm-ls-git-ls' is called from lisp
        ;; `default-directory' is normally let-bounded,
        ;; to some other value;
        ;; we now set this new let-bounded value local
        ;; to `helm-default-directory'.
        :default-directory default-directory
        :buffer "*helm lsgit*"))


;;; Helm-find-files integration.
;;
(defun helm-ff-ls-git-find-files (_candidate)
  (let ((default-directory helm-ff-default-directory))
    (helm-run-after-quit
     #'(lambda (d)
         (let ((default-directory d))
           (helm-ls-git-ls)))
     default-directory)))

(defun helm-ls-git-ff-dir-git-p (file)
  (when (or (file-exists-p file)
            (file-directory-p file))
    (stringp (condition-case nil
                 (helm-ls-git-root-dir
                  helm-ff-default-directory)
               (error nil)))))


(provide 'helm-ls-git)

;;; helm-ls-git.el ends here
