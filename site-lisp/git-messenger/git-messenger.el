;;; git-messenger.el --- Pop up last commit information of current line

;; Copyright (C) 2015 by Syohei YOSHIDA

;; Author: Syohei YOSHIDA <syohex@gmail.com>
;; URL: https://github.com/syohex/emacs-git-messenger
;; Version: 0.15
;; Package-Requires: ((popup "0.5.0") (cl-lib "0.5"))

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

;; This package provides a function called git-messenger:popup-message
;; that when called will pop-up the last git commit message for the
;; current line. This uses the git-blame tool internally.
;;
;; Example usage:
;;   (require 'git-messenger)
;;   (global-set-key (kbd "C-x v p") 'git-messenger:popup-message)
;;

;;; Code:

(require 'cl-lib)
(require 'popup)

(defgroup git-messenger nil
  "git messenger"
  :group 'vc)

(defcustom git-messenger:show-detail nil
  "Pop up commit ID and author name too"
  :type 'boolean
  :group 'git-messenger)

(defcustom git-messenger:before-popup-hook nil
  "Hook run before popup commit message. This hook is taken popup-ed message"
  :type 'hook
  :group 'git-messenger)

(defcustom git-messenger:after-popup-hook nil
  "Hook run after popup commit message. This hook is taken popup-ed message"
  :type 'hook
  :group 'git-messenger)

(defcustom git-messenger:popup-buffer-hook nil
  "Hook run after popup buffer(popup diff, popup show etc)"
  :type 'hook
  :group 'git-messenger)

(defcustom git-messenger:handled-backends '(git svn)
  "List of version control backends for which `git-messenger' will be used.
Entries in this list will be tried in order to determine whether a
file is under that sort of version control."
  :type '(repeat symbol)
  :group 'git-messenger)

(defvar git-messenger:last-message nil
  "Last message displayed by git-messenger.

This is set before the pop-up is displayed so accessible in the hooks
and menus.")

(defvar git-messenger:last-commit-id nil
  "Last commit id for the last message displayed.

This is set before the pop-up is displayed so accessible in the hooks
and menus.")

(defvar git-messenger:vcs nil)

(defconst git-messenger:directory-of-vcs
  '((git . ".git")
    (svn . ".svn")))

(defun git-messenger:blame-arguments (vcs file line)
  (cl-case vcs
    (git (list "--no-pager" "blame" "-w" "-L"
               (format "%d,+1" line)
               "--porcelain" (file-name-nondirectory file)))
    (svn (list "blame" file))))

(defsubst git-messenger:cat-file-arguments (commit-id)
  (list "--no-pager" "cat-file" "commit" commit-id))

(defsubst git-messenger:vcs-command (vcs)
  (cl-case vcs
    (git "git")
    (svn "svn")))

(defun git-messenger:execute-command (vcs args output)
  (apply 'process-file (git-messenger:vcs-command vcs) nil output nil args))

(defun git-messenger:git-commit-info-at-line ()
  (let* ((id-line (buffer-substring-no-properties
                   (line-beginning-position) (line-end-position)))
         (commit-id (car (split-string id-line)))
         (author (if (re-search-forward "^author \\(.+\\)$" nil t)
                     (match-string-no-properties 1)
                   "unknown")))
    (cons commit-id author)))

(defun git-messenger:svn-commit-info-at-line (line)
  (forward-line (1- line))
  (if (looking-at "^\\s-*\\([0-9]+\\)\\s-+\\(\\S-+\\)")
      (cons (match-string-no-properties 1) (match-string-no-properties 2))
    (cons "-" "-")))

(defun git-messenger:commit-info-at-line (vcs file line)
  (with-temp-buffer
    (let ((args (git-messenger:blame-arguments vcs file line)))
      (unless (zerop (git-messenger:execute-command vcs args t))
        (error "Failed: '%s blame'" (git-messenger:vcs-command vcs)))
      (goto-char (point-min))
      (cl-case vcs
        (git (git-messenger:git-commit-info-at-line))
        (svn (git-messenger:svn-commit-info-at-line line))))))

(defsubst git-messenger:not-committed-id-p (commit-id)
  (or (string-match-p "\\`\\(?:0+\\|-\\)\\'" commit-id)))

(defun git-messenger:git-commit-message (commit-id)
  (let ((args (git-messenger:cat-file-arguments commit-id)))
    (unless (zerop (git-messenger:execute-command 'git args t))
      (error "Failed: 'git cat-file'"))
    (goto-char (point-min))
    (forward-paragraph)
    (buffer-substring-no-properties (point) (point-max))))

(defun git-messenger:svn-commit-message (commit-id)
  (let ((args (list "log" "-c" commit-id)))
    (unless (zerop (git-messenger:execute-command 'svn args t))
      (error "Failed: 'svn log"))
    (goto-char (point-min))
    (let (end)
      (forward-paragraph)
      (when (re-search-forward "^-\\{25\\}" nil t)
        (forward-line -1)
        (setq end (point)))
      (buffer-substring-no-properties (point-min) (or end (point-max))))))

(defun git-messenger:commit-message (vcs commit-id)
  (with-temp-buffer
    (if (git-messenger:not-committed-id-p commit-id)
        "* not yet committed *"
      (cl-case vcs
        (git (git-messenger:git-commit-message commit-id))
        (svn (git-messenger:svn-commit-message commit-id))))))

(defun git-messenger:commit-date (commit-id)
  (let ((args (list "--no-pager" "show" "--pretty=%cd" commit-id)))
    (with-temp-buffer
      (unless (zerop (git-messenger:execute-command 'git args t))
        (error "Failed 'git show'"))
      (goto-char (point-min))
      (buffer-substring-no-properties
       (line-beginning-position) (line-end-position)))))

(defun git-messenger:format-detail (vcs commit-id author message)
  (cl-case vcs
    (git (let ((date (git-messenger:commit-date commit-id)))
           (format "commit : %s \nAuthor : %s\nDate   : %s \n%s"
                   (substring commit-id 0 8) author date message)))
    (svn (with-temp-buffer
           (insert message)
           (goto-char (point-min))
           (forward-line 1)
           (let ((line (buffer-substring-no-properties (point) (line-end-position)))
                 (re "^\\s-*\\(?:r[0-9]+\\)\\s-+|\\s-+\\([^|]+\\)|\\s-+\\([^|]+\\)"))
             (unless (string-match re line)
               (error "Can't get revision %s" line))
             (let ((author (match-string-no-properties 1 line))
                   (date (match-string-no-properties 2 line)))
               (forward-paragraph)
               (format "commit : r%s \nAuthor : %s\nDate  : %s\n%s"
                       commit-id author date
                       (buffer-substring-no-properties (point) (point-max)))))))))

(defun git-messenger:show-detail-p (commit-id)
  (and (or git-messenger:show-detail current-prefix-arg)
       (not (git-messenger:not-committed-id-p commit-id))))

(defun git-messenger:popup-close ()
  (interactive)
  (throw 'git-messenger-quit "Delete popup window"))

(defun git-messenger:copy-message ()
  "Copy current displayed commit message to kill-ring."
  (interactive)
  (when git-messenger:last-message
    (kill-new git-messenger:last-message))
  (git-messenger:popup-close))

(defun git-messenger:copy-commit-id ()
  "Copy current displayed commit id to kill-ring."
  (interactive)
  (when git-messenger:last-commit-id
    (kill-new git-messenger:last-commit-id))
  (git-messenger:popup-close))

(defun git-messenger:popup-common (vcs args &optional mode)
  (with-current-buffer (get-buffer-create "*git-messenger*")
    (setq buffer-read-only nil)
    (fundamental-mode)
    (erase-buffer)
    (unless (zerop (git-messenger:execute-command vcs args t))
      (error "Failed: '%s(args=%s)'" (git-messenger:vcs-command vcs) args))
    (pop-to-buffer (current-buffer))
    (when mode
      (funcall mode))
    (run-hooks 'git-messenger:popup-buffer-hook)
    (setq buffer-read-only t)
    (goto-char (point-min)))
  (git-messenger:popup-close))

(defun git-messenger:popup-svn-show ()
  (git-messenger:popup-common
   'svn (list "diff" "-c" git-messenger:last-commit-id) 'diff-mode))

(defun git-messenger:popup-diff ()
  (interactive)
  (cl-case git-messenger:vcs
    (git (let ((args (list "--no-pager" "diff" "--no-ext-diff"
                           (concat git-messenger:last-commit-id "^!"))))
           (git-messenger:popup-common 'git args 'diff-mode)))
    (svn (git-messenger:popup-svn-show))))

(defun git-messenger:popup-show ()
  (interactive)
  (cl-case git-messenger:vcs
    (git (let ((args (list "--no-pager" "show" "--no-ext-diff" "--stat"
                           git-messenger:last-commit-id)))
           (git-messenger:popup-common 'git args)))
    (svn (git-messenger:popup-svn-show))))

(defun git-messenger:popup-show-verbose ()
  (interactive)
  (cl-case git-messenger:vcs
    (git (let ((args (list "--no-pager" "show" "--no-ext-diff" "--stat" "-p"
                           git-messenger:last-commit-id)))
           (git-messenger:popup-common 'git args)))
    (svn (error "'svn' does not support `popup-show-verbose'"))))

(defvar git-messenger-map
  (let ((map (make-sparse-keymap)))
    ;; key bindings
    (define-key map (kbd "q") 'git-messenger:popup-close)
    (define-key map (kbd "c") 'git-messenger:copy-commit-id)
    (define-key map (kbd "d") 'git-messenger:popup-diff)
    (define-key map (kbd "s") 'git-messenger:popup-show)
    (define-key map (kbd "S") 'git-messenger:popup-show-verbose)
    (define-key map (kbd "M-w") 'git-messenger:copy-message)
    map)
  "Key mappings of git-messenger. This is enabled when commit message is popup-ed.")

(defun git-messenger:find-vcs ()
  (cl-loop for vcs in git-messenger:handled-backends
           for dir = (assoc-default vcs git-messenger:directory-of-vcs)
           when (locate-dominating-file default-directory dir)
           return vcs))

(defun git-messenger:svn-message (msg)
  (with-temp-buffer
    (insert msg)
    (goto-char (point-min))
    (forward-paragraph)
    (buffer-substring-no-properties (point) (point-max))))

;;;###autoload
(defun git-messenger:popup-message ()
  (interactive)
  (let* ((vcs (git-messenger:find-vcs))
         (file (buffer-file-name (buffer-base-buffer)))
         (line (line-number-at-pos))
         (commit-info (git-messenger:commit-info-at-line vcs file line))
         (commit-id (car commit-info))
         (author (cdr commit-info))
         (msg (git-messenger:commit-message vcs commit-id))
         (popuped-message (if (git-messenger:show-detail-p commit-id)
                              (git-messenger:format-detail vcs commit-id author msg)
                            (cl-case vcs
                              (git msg)
                              (svn (if (string= commit-id "-")
                                       msg
                                     (git-messenger:svn-message msg)))))))
    (setq git-messenger:vcs vcs
          git-messenger:last-message popuped-message
          git-messenger:last-commit-id commit-id)
    (run-hook-with-args 'git-messenger:before-popup-hook popuped-message)
    (let ((menu (popup-tip popuped-message :nowait t)))
      (unwind-protect
          (catch 'git-messenger-quit
            (popup-menu-event-loop menu git-messenger-map 'popup-menu-fallback))
        (popup-delete menu)))
    (run-hook-with-args 'git-messenger:after-popup-hook popuped-message)))

(provide 'git-messenger)

;; Local Variables:
;; coding: utf-8
;; indent-tabs-mode: nil
;; End:

;;; git-messenger.el ends here
