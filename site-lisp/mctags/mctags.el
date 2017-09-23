;;; mctags.el ---  Complete solution to use ctags in Emacs

;; Copyright (C) 2014-2017 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/mctags
;; Package-Requires: ((emacs "24.3") (popup "0.5.0"))
;; Keywords: ctags grep find
;; Version: 1.0.0

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
;; This file is not part of GNU Emacs.

;;; Commentary:

;; Usage:
;;   "M-x mctags-scan-code" to create tags file
;;   "M-x mctags-find-tag-at-point" to navigate
;;
;; That's all!
;;
;; See https://github.com/redguardtoo/mctags/ for more advanced tips.

;;; Code:

(require 'ivy)

(defcustom mctags-ignore-path-patterns
  '(;; VCS
    "*/.git/*"
    "*/.svn/*"
    "*/.cvs/*"
    "*/.bzr/*"
    "*/.hg/*"
    ;; simple text file
    "*.json"
    ;; project misc
    "*.log"
    "*/bin/*"
    ;; Mac
    "*/.DS_Store/*"
    ;; Ctags
    "*/tags"
    "*/TAGS"
    ;; Global/Cscope
    "*/GTAGS"
    "*/GPATH"
    "*/GRTAGS"
    "*/cscope.files"
    ;; html/javascript/css
    "*/.npm/*"
    "*/.tmp/*" ; TypeScript
    "*/.sass-cache/*" ; SCSS/SASS
    "*/.idea/*"
    "*min.js"
    "*min.css"
    "*/node_modules/*"
    "*/bower_components/*"
    ;; Images
    "*.png"
    "*.jpg"
    "*.jpeg"
    "*.gif"
    "*.bmp"
    "*.tiff"
    "*.ico"
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
    "*/.metadata*"
    "*/.gradle/*"
    "*.class"
    "*.war"
    "*.jar"
    ;; Emacs/Vim
    "*flymake"
    "*/#*#"
    ".#*"
    "*.swp"
    "*~"
    "*.elc"
    "*/.cask/*"
    ;; Python
    "*.pyc")
  "Ignore path patterns."
  :type '(repeat 'string))

(defcustom mctags-project-file '(".svn" ".hg" ".git")
  "The file/directory used to locate project root.
May be set using .dir-locals.el.  Checks each entry if set to a list."
  :type '(repeat 'string))

(defcustom mctags-max-file-size 64
  "Ignore files bigger than `mctags-max-file-size' kilobytes."
  :type 'integer)

(defcustom mctags-update-interval 300
  "The interval (seconds) to update TAGS.
Used by `mctags-update-tags-file'.
Default value is 300 seconds."
  :type 'integer)

(defcustom mctags-find-program nil
  "GNU find.  Program is automatically detected if it's nil."
  :type 'string)

(defcustom mctags-ctags-program nil
  "Ctags. Program is automatically detected if it's nil."
  :type 'string)

;; Timer to run auto-update TAGS.
(defvar mctags-timer nil "Internal timer.")

(defun mctags-guess-program (name)
  "Guess executable path from its NAME on Windows."
  (let (rlt)
    (if (eq system-type 'windows-nt)
        (cond
         ((file-executable-p (setq rlt (concat "c:\\\\cygwin64\\\\bin\\\\" name ".exe"))))
         ((file-executable-p (setq rlt (concat "d:\\\\cygwin64\\\\bin\\\\" name ".exe"))))
         ((file-executable-p (setq rlt (concat "e:\\\\cygwin64\\\\bin\\\\" name ".exe"))))
         (t (setq rlt nil))))
    (if rlt rlt name)))

;;;###autoload
(defun mctags-get-hostname ()
  "Reliable way to get current hostname.
`(getenv \"HOSTNAME\")' won't work because $HOSTNAME is NOT an
 environment variable.
`system-name' won't work because /etc/hosts could be modified"
  (with-temp-buffer
    (shell-command "hostname" t)
    (goto-char (point-max))
    (delete-char -1)
    (buffer-string)))

(defun mctags-locate-tags-file ()
  "Find tags file: either from `tags-file-name' or parent directory."
  (cond
   ((and tags-file-name (file-exists-p tags-file-name))
    tags-file-name)
   (t
    (let* ((dir (locate-dominating-file default-directory "TAGS")))
      (if dir (concat dir "TAGS"))))))

(defun mctags-project-root ()
  "Return the root of the project."
  (let* ((project-root (if (listp ffip-project-file)
                          (cl-some (apply-partially 'locate-dominating-file
                                                    default-directory)
                                   ffip-project-file)
                        (locate-dominating-file default-directory
                                                ffip-project-file))))
    (or (file-name-as-directory project-root)
        (progn (message "No project was defined.")
               nil))))

(defun mctags-scan-dir (src-dir &optional force)
  "Create tags file from SRC_DIR.
If FORCE is t, the commmand is executed without checking the timer."
  ;; TODO save the ctags-opts into hash
  (let* ((find-pg (or mctags-find-program
                       (mctags-guess-program "find")))
         (ctags-pg (or mctags-ctags-program
                        (mctags-guess-program "ctags")))
         (default-directory src-dir)
         ;; run find&ctags to create TAGS
         (cmd (format "%s . \\( %s \\) -prune -o -type f -not -name 'TAGS' -not -size +%sk | %s -e -L -"
                      find-pg
                      (mapconcat (lambda (p) (format "-iwholename \"%s\"" p))
                                 mctags-ignore-path-patterns " -or ")
                      mctags-max-file-size
                      ctags-pg))
         (tags-file (concat (file-name-as-directory src-dir) "TAGS"))
         (doit (or force (not (file-exists-p tags-file)))))
      ;; always update cli options
      (when doit
        (message "%s at %s" cmd default-directory)
        (shell-command cmd)
        (visit-tags-table tags-file t))))

;;;###autoload
(defun mctags-directory-p (regex)
  "Does directory of `buffer-file-name' match REGEX?"
  (let* ((dir (or (if buffer-file-name (file-name-directory buffer-file-name))
                  ;; buffer is created in real time
                  default-directory
                  "")))
    (string-match-p regex dir)))

;;;###autoload
(defun mctags-filename-p (regex)
  "Does `buffer-file-name' match REGEX?"
  (let* ((file (or buffer-file-name default-directory "")))
    (string-match-p regex file)))

;;;###autoload
(defun mctags-update-tags-file-force (&optional quiet)
  "Update tags file.  Be quiet if QUIET is t"
  (interactive)
  (let* ((tags-file (mctags-locate-tags-file)))
    (when tags-file
      (mctags-scan-dir (file-name-directory tags-file) t)
      (unless quiet
        (message "%s is updated!" tags-file)))))

(defun mctags-read-file (file)
  "Return FILE's content."
  (with-temp-buffer
    (insert-file-contents file)
    (buffer-string)))

(defun mctags-collect-tags (tagname)
  "Parse tags file to find matches of TAGNAME."
  (let* ((str (mctags-read-file (mctags-locate-tags-file)))
         (tag-regex (concat "^.*?\\(" "\^?\\(.+[:.']" tagname "\\)\^A"
                            "\\|" "\^?" tagname "\^A"
                            "\\|" "\\<" tagname "[ \f\t()=,;]*\^?[0-9,]"
                            "\\)"))
         (tag-file-path (file-name-directory (mctags-locate-tags-file)))
         full-tagname
         filename
         cands
         linenum)
    (with-temp-buffer
      (insert str)
      (modify-syntax-entry ?_ "w")
      (goto-char (point-min))
      (while (search-forward tagname nil t)
        (beginning-of-line)
        (when (re-search-forward tag-regex (point-at-eol) 'goto-eol)
          (setq full-tagname (or (match-string-no-properties 2) tagname))
          (beginning-of-line)
          (re-search-forward "\\s-*\\(.*?\\)\\s-*\^?\\(.*?\\)\\([0-9]+\\),[0-9]+$")
          (setq tag-line (match-string-no-properties 1))
          (setq linenum (string-to-number (match-string-no-properties 3)))
          (end-of-line)
          (save-excursion
            (re-search-backward "\f")
            (re-search-forward "^\\(.*?\\),")
            (setq filename (match-string-no-properties 1)))
          (add-to-list 'cands
                       (cons (format "%s:%d:%s" filename linenum tag-line)
                             (list filename linenum tagname)))))
      (modify-syntax-entry ?_ "_"))
    cands))

(defun mctags-tagname-at-point ()
  "Get tag name at point."
  (if (region-active-p) (buffer-substring-no-properties (region-beginning) (region-end))
    (find-tag-default)))

(defun mctags-forward-line (lnum)
  "Forward LNUM lines."
  (when (and lnum (> lnum 0))
    (goto-char (point-min))
    (forward-line (1- lnum))))

(defun mctags-open-file (item)
  "Find and open file of ITEM."
  (let* ((val (cdr item))
         (file (nth 0 val))
         (linenum (nth 1 val))
         (tagname (nth 2 val))
         (default-directory (file-name-directory (mctags-locate-tags-file))))
    ;; open file
    (find-file file)
    ;; goto line
    (mctags-forward-line linenum)
    ;; highlight the tag
    (beginning-of-line)
    (re-search-forward tagname)
    (goto-char (match-beginning 0))
    ;; flash, Emacs v25 only API
    (when (featurep 'xref)
      (require 'xref)
      (xref-pulse-momentarily))))

(defun mctags-open-cand (cands)
  "Open CANDS."
  ;; mark current point for `pop-tag-mark'
  (ring-insert find-tag-marker-ring (point-marker))
  (cond
   ((= 1 (length cands))
    ;; open the file directly
    (mctags-open-file (car cands)))
   (t
    (ivy-read "tag? "
              cands
              :action #'mctags-open-file))))

(defun mctags-tags-file-must-exist ()
  "Make sure tags file does exist."
  (let* (rlt src-dir)
    (cond
     ((not (mctags-locate-tags-file))
      (when (setq src-dir (read-directory-name "Ctags will scan code at:"
                                               (mctags-project-root)))
        (mctags-scan-dir src-dir t)
        (setq rlt t)))
     (t
      (setq rlt t)))
    (unless rlt
      (error "Can't find TAGS.  Please run `mctags-scan-code' at least once."))))

;;;###autoload
(defun mctags-scan-code (&option dir)
  "Use Ctags to scan code at DIR."
  (interactive)
  (let* ((src-dir (or dir
                      (read-directory-name "Ctags will scan code at:"
                                           (mctags-project-root)))))
    (if src-dir (mctags-scan-dir src-dir t))))

;;;###autoload
(defun mctags-find-tag-at-point ()
  "Find tag at point, and display all matches."
  (interactive)
  (mctags-tags-file-must-exist)
  (let* ((tagname (mctags-tagname-at-point))
         (cands (mctags-collect-tags tagname)))
    (cond
     ((not cands)
      (message (format "No matches for tag \"%s\"" tagname)))
     (t
      (mctags-open-cand cands)))))

;;;###autoload
(defun mctags-update-tags-file()
  "Scan the code and create tags file again."
  (interactive)
  (let* ((dir (and buffer-file-name
                   (file-name-directory buffer-file-name)))
         (tags-file (mctags-locate-tags-file)))
    (when (and dir
               tags-file
               (string-match-p (file-name-directory tags-file)
                               dir))
      (cond
       ((not mctags-timer)
        ;; start timer if not started yet
        (setq mctags-timer (current-time)))

       ((< (- (float-time (current-time)) (float-time mctags-timer))
           mctags-update-interval)
        ;; do nothing, can't run ctags too often
        )

       (t
        (setq mctags-timer (current-time))
        (mctags-update-tags-file-force t)
        (message "All tag files have been updated after %d seconds!"
                 (- (float-time (current-time))
                    (float-time mctags-timer))))))))

(provide 'mctags)
;;; mctags.el ends here
