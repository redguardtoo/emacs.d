;;; find-file-in-project.el --- Find files in a project quickly.

;; Copyright (C) 2006-2009, 2011-2012, 2015
;;   Phil Hagelberg, Doug Alcorn, and Will Farrington
;; Author: Phil Hagelberg, Doug Alcorn, and Will Farrington
;; Maintainer: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://www.emacswiki.org/cgi-bin/wiki/FindFileInProject
;; Git: git://github.com/technomancy/find-file-in-project.git
;; Version: 3.5
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

;; This program provides a couple methods for quickly finding any file
;; in a given project.  It depends on GNU find.
;;
;; Usage,
;;   - `M-x find-file-in-project` will start search immediately
;;   - `M-x find-file-in-project-by-selected` use the your selected
;;      region as keyword to search. Or you need provide the keyword
;;      if no region selected.
;;
;; A project is found by searching up the directory tree until a file
;; is found that matches `ffip-project-file'.  (".git" by default.)
;; You can set `ffip-project-root-function' to provide an alternate
;; function to search for the project root.  By default, it looks only
;; for files whose names match `ffip-patterns',

;; If you have so many files that it becomes unwieldy, you can set
;; `ffip-find-options' to a string which will be passed to the `find'
;; invocation in order to exclude irrelevant subdirectories/files.
;; For instance, in a Ruby on Rails project, you are interested in all
;; .rb files that don't exist in the "vendor" directory.  In that case
;; you could set `ffip-find-options' to "-not -regex \".*vendor.*\"".

;; All these variables may be overridden on a per-directory basis in
;; your .dir-locals.el.  See (info "(Emacs) Directory Variables") for
;; details.

;; Ivy.el from https://github.com/abo-abo/swiper could be automatically
;; used if you insert below line into ~/.emacs,
;;   (autoload 'ivy-read "ivy")
;; In Ivy.el, SPACE is translated to regex ".*".
;; For exmaple, the search string "dec fun pro" is transformed into
;; a regex "\\(dec\\).*\\(fun\\).*\\(pro\\)"
;;
;; If Ivy.el is not available, ido will be used.

;; GNU Find can be installed,
;;   - through `brew' on OS X
;;   - through `cygwin' on Windows.
;;
;; This program works on Windows/Cygwin/Linux/Mac Emacs.
;; See https://github.com/technomancy/find-file-in-project for advanced tips

;; Recommended binding: (global-set-key (kbd "C-x f") 'find-file-in-project)

;;; Code:

(require 'cl)

(defvar ffip-find-executable nil "Path of GNU find. If nil, we will find `find' path automatically")

(defvar ffip-project-file ".git"
  "The file that should be used to define a project root.

May be set using .dir-locals.el. Checks each entry if set to a list.")

(defvar ffip-patterns nil
  "List of patterns to look for with `find-file-in-project'.")

(defvar ffip-prune-patterns
  '(;; VCS
    ".git"
    ".svn"
    ".cvs"
    ".bzr"
    ".hg"
    ;; project misc
    "*.log"
    "bin"
    "dist"
    "target"
    ;; Mac
    ".DS_Store"
    ;; Ctags
    "tags"
    "TAGS"
    ;; Global/Cscope
    "GTAGS"
    "GPATH"
    "GRTAGS"
    "cscope.files"
    ;; html/javascript/css
    "*min.js"
    "*min.css"
    "node_modules"
    "bower_components"
    ;; Images
    "*.png"
    "*.jpg"
    "*.jpeg"
    "*.gif"
    "*.bmp"
    "*.tiff"
    ;; documents
    "*.doc"
    "*.docx"
    "*.pdf"
    ;; C/C++
    "*.obj"
    "*.o"
    "*.a"
    "*.dylib"
    "*.lib"
    "*.d"
    "*.dll"
    "*.exe"
    ;; Java
    ".metadata"
    ".gradle"
    "*.class"
    "*.war"
    "*.jar"
    ;; Emacs/Vim
    "*flymake"
    "#*#"
    ".#*"
    "*.swp"
    "*~"
    "*.elc"
    ".cask"
    ;; Python
    "*.pyc")
  "List of directory/file patterns to not descend into when listing files in `find-file-in-project'.")

(defvar ffip-find-options ""
  "Extra options to pass to `find' when using `find-file-in-project'.

Use this to exclude portions of your project: \"-not -regex \\\".*svn.*\\\"\".")

(defvar ffip-project-root nil
  "If non-nil, overrides the project root directory location.")

(defvar ffip-project-root-function nil
  "If non-nil, this function is called to determine the project root.

This overrides variable `ffip-project-root' when set.")

(defvar ffip-limit 0
  "Limit results to this many files. 0 means no limit")

(defvar ffip-full-paths t
  "If non-nil, show fully project-relative paths.")

(defvar ffip-debug nil "Print debug information")

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

(defun ffip-join-patterns ()
  "Turn `ffip-patterns' into a string that `find' can use."
  (if ffip-patterns
      (format "\\( %s \\)"
              (mapconcat (lambda (pat) (format "-name \"%s\"" pat))
                         ffip-patterns " -or "))
    ""))

(defun ffip-prune-patterns ()
  "Turn `ffip-prune-patterns' into a string that `find' can use."
  (mapconcat (lambda (pat) (format "-name \"%s\"" pat))
             ffip-prune-patterns " -or "))

(defun ffip-limit-find-results ()
  (let ((rlt ""))
    (if (and (executable-find "head") (> ffip-limit 0))
        (setq rlt (format " | head -n %d" ffip-limit)))
    rlt))

(defun ffip-completing-read (prompt collection)
  (let (rlt)
    (cond
     ( (= 1 (length collection))
       ;; open file directly
       (setq rlt (car collection)))
     ((fboundp 'ivy-read)
      (setq rlt (ivy-read prompt collection)))
     ((and (boundp 'ido-mode) ido-mode)
      (setq rlt (ido-completing-read prompt collection)))
     (t
      (setq rlt (completing-read prompt collection))))
    rlt))

(defun ffip-project-files (keyword NUM)
  "Return an alist of all filenames in the project and their path.

Files with duplicate filenames are suffixed with the name of the
directory they are found in so that they are unique."
  (let (rlt
        cmd
        (old-default-directory default-directory)
        (file-alist nil)
        (root (expand-file-name (or ffip-project-root (ffip-project-root)
                                    (error "No project root found")))))
    (cd (file-name-as-directory root))
    ;; make the prune pattern more general
    (setq cmd (format "%s . \\( %s \\) -prune -o -type f %s %s %s %s -print %s"
                      (if ffip-find-executable ffip-find-executable (ffip--guess-gnu-find))
                      (ffip-prune-patterns)
                      (ffip-join-patterns)
                      (if keyword (concat "-name \"*" keyword "*\"") "")
                      (if (and NUM (> NUM 0)) (format "-mtime -%d" NUM) "")
                      ffip-find-options
                      (ffip-limit-find-results)))

    (if ffip-debug (message "run cmd at %s: %s" default-directory cmd))
    (setq rlt
          (mapcar (lambda (file)
                    (if ffip-full-paths
                        (cons (replace-regexp-in-string "^\./" "" file)
                              (expand-file-name file))
                      (let ((file-cons (cons (file-name-nondirectory file)
                                             (expand-file-name file))))
                        (add-to-list 'file-alist file-cons)
                        file-cons)))
                  ;; #15 improving handling of directories containing space
                  (split-string (shell-command-to-string cmd) "[\r\n]+" t)))

    ;; restore the original default-directory
    (cd old-default-directory)
    rlt))

(defun ffip-find-files (keyword NUM)
  (let* ((project-files (ffip-project-files keyword NUM))
         (files (mapcar 'car project-files))
         file root)
    (cond
     ((and files (> (length files) 0))
      (setq root (file-name-nondirectory (directory-file-name (or ffip-project-root (ffip-project-root)))))
      (setq file (ffip-completing-read (format "Find file in %s/: " root)  files))
      (find-file (cdr (assoc file project-files))))
     (t (message "No match file exist!")))
    ))

;;;###autoload
(defun ffip-current-full-filename-match-pattern-p (REGEX)
  "Is current full file name (including directory) match the REGEX?"
  (let ((dir (if (buffer-file-name) (buffer-file-name) "")))
    (string-match-p REGEX dir)))

;;;###autoload
(defun find-file-in-project (&optional NUM)
  "Prompt with a completing list of all files in the project to find one.
If NUM is given, only files modfied NUM days before will be selected.

The project's scope is defined as the first directory containing
a `ffip-project-file' (It's value is \".git\" by default.

You can override this by setting the variable `ffip-project-root'."

  (interactive "P")
  (ffip-find-files nil NUM))

;;;###autoload
(defun ffip-get-project-root-directory ()
  "Get the full path of project root directory"
  (expand-file-name (or ffip-project-root
                        (ffip-project-root))))

;;;###autoload
(defun find-file-in-project-by-selected (&optional NUM)
  "Similar to find-file-in-project.
But use string from selected region to search files in the project.
If no region is selected, you need provide one.
If NUM is given, only files modfied NUM days before will be selected.
"
  (interactive "P")
  (let ((keyword (if (region-active-p)
                     (buffer-substring-no-properties (region-beginning) (region-end))
                   (read-string "Enter keyword:"))))
    (ffip-find-files keyword NUM)))

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
