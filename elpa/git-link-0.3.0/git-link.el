;;; git-link.el --- Get the GitHub/Bitbucket/Gitorious URL for a buffer location

;; Author: Skye Shaw <skye.shaw@gmail.com>
;; Version: 0.3.0
;; Package-Version: 0.3.0
;; Keywords: git
;; URL: http://github.com/sshaw/git-link

;; This file is NOT part of GNU Emacs.

;;; License:

;; This program is free software: you can redistribute it and/or modify
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

;; Create URLs for files and commits in GitHub/Bitbucket/Gitorious/...
;; repositories. `git-link' returns the URL for the current buffer's file
;; location at the current line number or active region. `git-link-commit'
;; returns the URL for a commit. URLs are added to the kill ring.
;;
;; With a prefix argument prompt for the remote's name. Defaults to "origin".

;;; Change Log:

;; 2015-09-21 - v0.3.0
;; * Support for setting branch and remote names via `git config`
;; * Added git-link-default-branch
;; * Removed some functions, use emacs "private" convention for others
;;
;; 2015-09-12 - v0.2.2
;; * Support for BitBucket's multiline format
;;
;; 2015-07-25 - v0.2.1
;; * Fix for BitBucket's new URL format (Thanks Ev Dolzhenko)
;; * Fix for GitLab's multiline format (Thanks Enrico Carlesso)
;;
;; 2015-06-05 - v0.2.0
;; * Deactivate mark after killing the link (Thanks Kaushal Modi)
;; * Support for GitLab (Thanks Swaroop C H)
;; * Use completing-read when prompting for remotes (Thanks Andrew Gwozdziewycz)
;; * Display URL in minibuffer when adding to kill ring (Thanks Andrew Gwozdziewycz)
;; * Added git-link-use-commit variable (Thanks Kaushal Modi)
;; * Fix for displaying link in minibuffer when interprogram-cut-function is set (Thanks Ric Lister)
;; * Fix to ignore point at beginning of line in regions (Thanks Kaushal Modi)
;; * Fix for narrow-to-region (Bug #10, thanks Andrew Gwozdziewycz)
;; * Fix to use remote hostname when constructing link URLs (Thanks David Hull)
;;
;; 2015-02-05 - v0.1.0
;; * Added git-link-commit (Thanks Ryan Barrett)
;; * Added git-link-open-in-browser variable (Thanks Ryan Barrett)
;; * Use call-process instead of shell-command-to-string
;; * Use --short option when calling symbolic-ref (Thanks Steven Huwig)
;;
;; 2014-02-27 - v0.0.2
;; * Fix for buffers visiting files through symlinks (Bug #1, thanks Evgeniy Dolzhenko)

;;; Code:

(require 'thingatpt)

(defvar git-link-default-remote "origin"
  "Name of the remote to link to.")

(defvar git-link-default-branch nil
  "Name of the branch to link to.")

(defvar git-link-open-in-browser nil
  "If non-nil also open link in browser via `browse-url'.")

(defvar git-link-use-commit nil
  "If non-nil use the latest commit's hash in the link instead of the branch name.")

(defvar git-link-remote-alist
  '(("github.com"    git-link-github)
    ("bitbucket.org" git-link-bitbucket)
    ("gitorious.org" git-link-gitorious)
    ("gitlab.com"    git-link-gitlab))
  "Maps remote hostnames to a function capable of creating the appropriate file URL")

(defvar git-link-commit-remote-alist
  '(("github.com"    git-link-commit-github)
    ("bitbucket.org" git-link-commit-bitbucket)
    ("gitorious.org" git-link-commit-gitorious)
    ("gitlab.com"    git-link-commit-github))
  "Maps remote hostnames to a function capable of creating the appropriate commit URL")

;; Matches traditional URL and scp style
;; This probably wont work for git remotes that aren't services
(defconst git-link-remote-regex "\\([-.[:word:]]+\\)[:/]\\([^/]+/[^/]+?\\)\\(?:\\.git\\)?$")

(defun git-link--last-commit ()
  (car (git-link--exec "--no-pager" "log" "-n1" "--pretty=format:%H")))

(defun git-link--branch ()
  (or (car (git-link--exec "config" "--get" "git-link.branch"))
      git-link-default-branch
      (car (git-link--exec "symbolic-ref" "--short" "HEAD"))))

(defun git-link--remote ()
  (or (car (git-link--exec "config" "--get" "git-link.remote"))
      git-link-default-remote))

(defun git-link--repo-root ()
  (car (git-link--exec "rev-parse" "--show-toplevel")))

(defun git-link--remote-url (name)
  (car (git-link--exec "config" "--get" (format "remote.%s.url" name))))

(defun git-link--relative-filename ()
  (let* ((filename (buffer-file-name))
	 (dir      (git-link--repo-root)))
    (if (and dir filename)
	(substring (file-truename filename)
		   (1+ (length dir))))))

(defun git-link--remote-host (remote-name)
  (let ((url (git-link--remote-url remote-name)))
    (if (and url (string-match git-link-remote-regex url))
	(match-string 1 url))))

(defun git-link--remote-dir (remote-name)
  (let ((url (git-link--remote-url remote-name)))
    (if (and url (string-match git-link-remote-regex url))
        (match-string 2 url))))

(defun git-link--exec(&rest args)
  (ignore-errors (apply 'process-lines `("git" ,@(when args args)))))

(defun git-link--remotes ()
  (git-link--exec "remote"))

(defun git-link--read-remote ()
  (let ((remotes (git-link--remotes))
	(current (git-link--remote)))
    (if remotes
        (completing-read "Remote: "
                         remotes
                         nil
                         t
                         ""
                         nil
                         (if (member current remotes)
                             current
                         (car remotes)))
     current)))

(defun git-link--get-region ()
  (save-restriction
    (widen)
    (save-excursion
      (let* ((use-region (use-region-p))
             (start (when use-region (region-beginning)))
             (end   (when use-region (region-end)))
             (line-start (line-number-at-pos start))
             line-end)
        (when use-region
          ;; When region is selected from bottom to top, exchange point and mark
          ;; so that the `point' and `(region-end)' are the same
          (when (< (point) (mark))
            (exchange-point-and-mark))
          ;; If the `end' position is at the beginning of a line
          ;; decrement the position by 1, so that the resultant
          ;; position is on the previous line.
          (when (= end (line-beginning-position))
            (setq end (1- end)))
          (setq line-end (line-number-at-pos end))
          (when (<= line-end line-start)
            (setq line-end nil)))
        (list line-start line-end)))))

(defun git-link--new (link)
  (kill-new link)
  (message link)
  (setq deactivate-mark t)
  (when git-link-open-in-browser
    (browse-url link)))

(defun git-link-gitlab (hostname dirname filename branch commit start end)
  (format "https://%s/%s/blob/%s/%s#%s"
	  hostname
	  dirname
	  (or branch commit)
	  filename
	  (if end
	      (format "L%s-%s" start end)
	    (format "L%s" start))))

(defun git-link-github (hostname dirname filename branch commit start end)
  (format "https://%s/%s/blob/%s/%s#%s"
	  hostname
	  dirname
	  (or branch commit)
	  filename
	  (if end
	      (format "L%s-L%s" start end)
	    (format "L%s" start))))

(defun git-link-commit-github (hostname dirname commit)
  (format "https://%s/%s/commit/%s"
	  hostname
	  dirname
	  commit))

(defun git-link-gitorious (hostname dirname filename branch commit start end)
  (format "https://%s/%s/source/%s:%s#L%s"
	  hostname
	  dirname
	  commit
	  filename
	  start))

(defun git-link-commit-gitorious (hostname dirname commit)
  (format "https://%s/%s/commit/%s"
	  hostname
	  dirname
	  commit))

(defun git-link-bitbucket (hostname dirname filename branch commit start end)
  ;; ?at=branch-name
  (format "https://%s/%s/src/%s/%s#%s-%s"
	  hostname
	  dirname
	  commit
	  filename
	  (file-name-nondirectory filename)
	  (if end
	      (format "%s:%s" start end)
	    start)))

(defun git-link-commit-bitbucket (hostname dirname commit)
  ;; ?at=branch-name
  (format "https://%s/%s/commits/%s"
	  hostname
	  dirname
	  commit))

;;;###autoload
(defun git-link (remote start end)
  "Create a URL representing the current buffer's location in its
GitHub/Bitbucket/Gitorious/... repository at the current line number
or active region. The URL will be added to the kill ring.

With a prefix argument prompt for the remote's name.
Defaults to \"origin\"."
  (interactive (let* ((remote (if current-prefix-arg
                                  (git-link--read-remote)
                                (git-link--remote)))
                      (region (git-link--get-region)))
                 (list remote (car region) (cadr region))))
  (let* ((remote-host (git-link--remote-host remote))
	 (filename    (git-link--relative-filename))
	 (branch      (git-link--branch))
	 (commit      (git-link--last-commit))
	 (handler     (cadr (assoc remote-host git-link-remote-alist))))

    (cond ((null filename)
	   (message "Buffer has no file"))
	  ((null remote-host)
	   (message "Unknown remote '%s'" remote))
	  ((and (null commit) (null branch))
	   (message "Not on a branch, and repo does not have commits"))
	  ((not (functionp handler))
	   (message "No handler for %s" remote-host))
	  ;; null ret val
	  ((git-link--new
	    (funcall handler
		     remote-host
		     (git-link--remote-dir remote)
		     filename
		     (if git-link-use-commit nil branch)
		     commit
		     start
		     end))))))

;;;###autoload
(defun git-link-commit (remote)
  "Create a URL representing the commit for the hash under point
in the current buffer's GitHub/Bitbucket/Gitorious/...
repository. The URL will be added to the kill ring.

With a prefix argument prompt for the remote's name.
Defaults to \"origin\"."

  (interactive (list (if current-prefix-arg
                         (git-link--read-remote)
                       (git-link--remote))))
  (let* ((remote-host (git-link--remote-host remote))
	 (commit      (word-at-point))
	 (handler     (cadr (assoc remote-host git-link-commit-remote-alist))))
    (cond ((null remote-host)
	   (message "Unknown remote '%s'" remote))
	  ((not (string-match "[a-z0-9]\\{7,40\\}" (or commit "")))
	   (message "Point is not on a commit hash"))
	  ((not (functionp handler))
	   (message "No handler for %s" remote-host))
	  ;; null ret val
	  ((git-link--new
	    (funcall handler
		     remote-host
		     (git-link--remote-dir remote)
		     commit))))))

(provide 'git-link)
;;; git-link.el ends here
