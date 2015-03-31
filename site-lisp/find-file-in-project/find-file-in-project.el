;;; find-file-in-project.el --- Find files in a project quickly.

;; Copyright (C) 2006-2009, 2011-2012
;;   Phil Hagelberg, Doug Alcorn, and Will Farrington

;; Author: Phil Hagelberg, Doug Alcorn, and Will Farrington
;; URL: http://www.emacswiki.org/cgi-bin/wiki/FindFileInProject
;; Git: git://github.com/technomancy/find-file-in-project.git
;; Version: 3.3
;; Created: 2008-03-18
;; Keywords: project, convenience
;; EmacsWiki: FindFileInProject

;; This file is NOT part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This library provides a couple methods for quickly finding any file
;; in a given project.  It depends on GNU find.

;; A project is found by searching up the directory tree until a file
;; is found that matches `ffip-project-file'.  (".git" by default.)
;; You can set `ffip-project-root-function' to provide an alternate
;; function to search for the project root.  By default, it looks only
;; for files whose names match `ffip-patterns',

;; If you have so many files that it becomes unwieldy, you can set
;; `ffip-find-options' to a string which will be passed to the `find'
;; invocation in order to exclude irrelevant subdirectories.  For
;; instance, in a Ruby on Rails project, you may be interested in all
;; .rb files that don't exist in the "vendor" directory.  In that case
;; you could set `ffip-find-options' to "-not -regex \".*vendor.*\"".

;; All these variables may be overridden on a per-directory basis in
;; your .dir-locals.el.  See (info "(Emacs) Directory Variables") for
;; details.

;; Recommended binding: (global-set-key (kbd "C-x f") 'find-file-in-project)

;;; TODO:

;; Add compatibility with BSD find (PDI; I can't virtualize OS X)

;;; Code:

(require 'cl)

(defvar ffip-find-executable nil "Path of GNU find. If nil, we will find `find' path automatically")

(defvar ffip-project-file ".git"
  "The file that should be used to define a project root.

May be set using .dir-locals.el. Checks each entry if set to a list.")

(defvar ffip-patterns
  '("*.html" "*.org" "*.txt" "*.md" "*.el" "*.clj" "*.py" "*.rb" "*.js" "*.pl"
    "*.sh" "*.erl" "*.hs" "*.ml")
  "List of patterns to look for with `find-file-in-project'.")

(defvar ffip-prune-patterns
  '(".git")
  "List of directory patterns to not decend into when listing files in `find-file-in-project'.")

(defvar ffip-find-options ""
  "Extra options to pass to `find' when using `find-file-in-project'.

Use this to exclude portions of your project: \"-not -regex \\\".*svn.*\\\"\".")

(defvar ffip-project-root nil
  "If non-nil, overrides the project root directory location.")

(defvar ffip-project-root-function nil
  "If non-nil, this function is called to determine the project root.

This overrides variable `ffip-project-root' when set.")

(defvar ffip-limit 512
  "Limit results to this many files.")

(defvar ffip-full-paths nil
  "If non-nil, show fully project-relative paths.")

(defun ffip-project-root ()
  "Return the root of the project."
  (let ((project-root (or ffip-project-root
                          (if (functionp ffip-project-root-function)
                              (funcall ffip-project-root-function)
                            (if (listp ffip-project-file)
                                (some (apply-partially 'locate-dominating-file
                                                       default-directory)
                                      ffip-project-file)
                              (locate-dominating-file default-directory
                                                      ffip-project-file))))))
    (or project-root
        (progn (message "No project was defined for the current file.")
               nil))))

(defun ffip--guess-gnu-find ()
  (let ((rlt "find"))
    (if (eq system-type 'windows-nt)
        (cond
         ((executable-find "c:\\\\cygwin64\\\\bin\\\\find")
          (setq rlt "c:\\\\cygwin64\\\\bin\\\\find"))
         ((executable-find "d:\\\\cygwin64\\\\bin\\\\find")
          (setq rlt "d:\\\\cygwin64\\\\bin\\\\find"))
         ((executable-find "e:\\\\cygwin64\\\\bin\\\\find")
          (setq rlt "e:\\\\cygwin64\\\\bin\\\\find"))
         ((executable-find "c:\\\\cygwin\\\\bin\\\\find")
          (setq rlt "c:\\\\cygwin\\\\bin\\\\find"))
         ((executable-find "d:\\\\cygwin\\\\bin\\\\find")
          (setq rlt "d:\\\\cygwin\\\\bin\\\\find"))
         ((executable-find "e:\\\\cygwin\\\\bin\\\\find")
          (setq rlt "e:\\\\cygwin\\\\bin\\\\find"))))
    rlt))

(defun ffip-uniqueify (file-cons)
  "Set the car of FILE-CONS to include the directory name plus the file name."
  (setcar file-cons
          (concat (cadr (reverse (split-string (cdr file-cons) "/"))) "/"
                  (car file-cons))))

(defun ffip-join-patterns ()
  "Turn `ffip-patterns' into a string that `find' can use."
  (mapconcat (lambda (pat) (format "-name \"%s\"" pat))
             ffip-patterns " -or "))

(defun ffip-prune-patterns ()
  "Turn `ffip-prune-patterns' into a string that `find' can use."
  (mapconcat (lambda (pat) (format "-name \"%s\"" pat))
             ffip-prune-patterns " -or "))


(defun ffip-project-files ()
  "Return an alist of all filenames in the project and their path.

Files with duplicate filenames are suffixed with the name of the
directory they are found in so that they are unique."
  (let ((file-alist nil)
        (root (expand-file-name (or ffip-project-root (ffip-project-root)
                                    (error "No project root found")))))
    (mapcar (lambda (file)
              (if ffip-full-paths
                  (cons (substring (expand-file-name file) (length root))
                        (expand-file-name file))
                (let ((file-cons (cons (file-name-nondirectory file)
                                       (expand-file-name file))))
                  (when (assoc (car file-cons) file-alist)
                    (ffip-uniqueify (assoc (car file-cons) file-alist))
                    (ffip-uniqueify file-cons))
                  (add-to-list 'file-alist file-cons)
                  file-cons)))
            (split-string (shell-command-to-string
                           (format "%s %s -type d -a \\( %s \\) -prune -o -type f \\( %s \\) -print %s | head -n %s"
                                   (if ffip-find-executable ffip-find-executable (ffip--guess-gnu-find))
                                   (file-name-as-directory root) (ffip-prune-patterns) (ffip-join-patterns)
                                   ffip-find-options ffip-limit))))))

;;;###autoload
(defun find-file-in-project ()
  "Prompt with a completing list of all files in the project to find one.

The project's scope is defined as the first directory containing
an `.emacs-project' file.  You can override this by locally
setting the variable `ffip-project-root'."
  (interactive)
  (let* ((project-files (ffip-project-files))
         (files (mapcar 'car project-files))
         (file (if (and (boundp 'ido-mode) ido-mode)
                   (ido-completing-read "Find file in project: " files)
                 (completing-read "Find file in project: " files))))
    (find-file (cdr (assoc file project-files)))))

;;;###autoload
(defalias 'ffip 'find-file-in-project)

;; safe locals
;;;###autoload
(progn
  (put 'ffip-patterns 'safe-local-variable 'listp)
  (put 'ffip-project-file 'safe-local-variable 'stringp)
  (put 'ffip-project-root 'safe-local-variable 'stringp)
  (put 'ffip-limit 'safe-local-variable 'integerp))

(provide 'find-file-in-project)
;;; find-file-in-project.el ends here
