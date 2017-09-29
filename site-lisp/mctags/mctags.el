;;; mctags.el ---  Complete solution to use ctags

;; Copyright (C) 2017 by Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/mctags
;; Package-Requires: ((emacs "24.3") (counsel "0.9.1"))
;; Keywords: tools, convenience
;; Version: 1.1.6

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
;;   "M-x mctags-find-tag-at-point" to navigate.  This command will also
;;   run `mctags-scan-code' automatically if tags file is not built yet.
;;
;;   "M-x mctags-scan-code" to create tags file
;;   "M-x mctags-grep" to grep
;;
;; That's all!
;;
;; Tips:
;; You can use ivy's negative pattern to filter candidates.
;; For example, input "keyword1 !keyword2 keyword3" means:
;;   "(keyword1 and (not (keyword2 or keyword3))"
;;
;; See https://github.com/redguardtoo/mctags/ for more advanced tips.

;;; Code:

(require 'counsel) ; counsel dependent on ivy

(defgroup mctags nil
  "Complete solution to use ctags."
  :group 'tools)

(defcustom mctags-ignore-directories
  '(;; VCS
    ".git"
    ".svn"
    ".cvs"
    ".bzr"
    ".hg"
    ;; project misc
    "bin"
    ;; Mac
    ".DS_Store"
    ;; html/javascript/css
    ".npm"
    ".tmp" ; TypeScript
    ".sass-cache" ; SCSS/SASS
    ".idea*"
    "node_modules"
    "bower_components"
    ;; Java
    ".cask")
  "Ignore directories.  Wildcast is supported."
  :group 'mctags
  :type '(repeat 'string))

(defcustom mctags-ignore-filenames
  '(;; VCS
    ;; simple text file
    "*.json"
    ;; project misc
    "*.log"
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
    "*.xls"
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
    ".metadata*"
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
    ;; Python
    "*.pyc")
  "Ignore file names.  Wildcast is supported."
  :group 'mctags
  :type '(repeat 'string))

(defcustom mctags-project-file '(".svn" ".hg" ".git")
  "The file/directory used to locate project root.
May be set using .dir-locals.el.  Checks each entry if set to a list."
  :group 'mctags
  :type '(repeat 'string))

(defcustom mctags-max-file-size 64
  "Ignore files bigger than `mctags-max-file-size' kilobytes."
  :group 'mctags
  :type 'integer)


(defcustom mctags-after-update-tags-file-hook nil
  "Hook after tags file is actually updated.
The parameter of hook is full path of tags file."
  :group 'mctags
  :type 'hook)

(defcustom mctags-update-interval 300
  "The interval (seconds) to update TAGS.
Used by `mctags-update-tags-file'.
Default value is 300 seconds."
  :group 'mctags
  :type 'integer)

(defcustom mctags-find-program nil
  "GNU find program.  Automatically detected if it's nil."
  :group 'mctags
  :type 'string)

(defcustom mctags-ctags-program nil
  "Ctags program.  Automatically detected if it's nil."
  :group 'mctags
  :type 'string)

(defcustom mctags-grep-program nil
  "Grep program.  Automatically detected if it's nil."
  :group 'mctags
  :type 'string)

;; Timer to run auto-update TAGS.
(defvar mctags-timer nil "Internal timer.")

(defvar mctags-keyword nil "The keyword to grep.")

(defvar mctags-opts-cache '() "Grep CLI options cache.")

(defvar mctags-tagname-history nil "History of tagnames.")

(defvar mctags-find-tag-candidates nil "Find tag candidate.")

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
  (let* ((project-root (if (listp mctags-project-file)
                          (cl-some (apply-partially 'locate-dominating-file
                                                    default-directory)
                                   mctags-project-file)
                        (locate-dominating-file default-directory
                                                mctags-project-file))))
    (or (file-name-as-directory project-root)
        (progn (message "No project was defined.")
               nil))))

(defun mctags-scan-dir (src-dir &optional force)
  "Create tags file from SRC-DIR.
If FORCE is t, the commmand is executed without checking the timer."
  ;; TODO save the ctags-opts into hash
  (let* ((find-pg (or mctags-find-program (mctags-guess-program "find")))
         (ctags-pg (or mctags-ctags-program (mctags-guess-program "ctags")))
         (default-directory src-dir)
         ;; run find&ctags to create TAGS
         (cmd (format "%s . \\( %s \\) -prune -o -type f -not -size +%sk %s | %s -e -L -"
                      find-pg
                      (mapconcat (lambda (p) (format "-iwholename \"*/%s*\""
                                                     (file-name-as-directory p)))
                                 mctags-ignore-directories " -or ")
                      mctags-max-file-size
                      (mapconcat (lambda (n) (format "-not -name \"%s\"" n))
                                 mctags-ignore-filenames " ")
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
  "Does directory of current file match REGEX?"
  (let* ((dir (or (if buffer-file-name (file-name-directory buffer-file-name))
                  ;; buffer is created in real time
                  default-directory
                  "")))
    (string-match-p regex dir)))

;;;###autoload
(defun mctags-filename-p (regex)
  "Does current file match REGEX?"
  (let* ((file (or buffer-file-name default-directory "")))
    (string-match-p regex file)))

;;;###autoload
(defun mctags-update-tags-file-force (&optional quiet)
  "Update tags file.  Be quiet if QUIET is t."
  (interactive)
  (let* ((tags-file (mctags-locate-tags-file)))
    (when tags-file
      (mctags-scan-dir (file-name-directory tags-file) t)
      (run-hook-with-args 'mctags-after-update-tags-file-hook tags-file)
      (unless quiet
        (message "%s is updated!" tags-file)))))

(defun mctags-read-file (file)
  "Return FILE's content."
  (with-temp-buffer
    (insert-file-contents file)
    (buffer-string)))

(defun mctags-collect-cands (tagname)
  "Parse tags file to find occurrences of TAGNAME."
  (let* ((str (mctags-read-file (mctags-locate-tags-file)))
         (tag-regex (concat "^.*?\\(" "\^?\\(.+[:.']" tagname "\\)\^A"
                            "\\|" "\^?" tagname "\^A"
                            "\\|" "\\<" tagname "[ \f\t()=,;]*\^?[0-9,]"
                            "\\)"))
         (tag-file-path (file-name-directory (mctags-locate-tags-file)))
         full-tagname
         filename
         tag-line
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

(defun mctags-selected-str ()
  "Get selected string."
  (if (region-active-p)
      (buffer-substring-no-properties (region-beginning) (region-end))))

(defun mctags-tagname-at-point ()
  "Get tag name at point."
  (if (mctags-selected-str) (mctags-selected-str)
    (find-tag-default)))

(defun mctags-forward-line (lnum)
  "Forward LNUM lines."
  (when (and lnum (> lnum 0))
    (goto-char (point-min))
    (forward-line (1- lnum))))

(defun mctags-open-file-api (file linenum dir &optional tagname)
  "Open FILE and goto LINENUM while `default-directory' is DIR.
Focus on TAGNAME if it's not nil."
  (let* ((default-directory dir))
    ;; open file
    (find-file file)
    ;; goto line
    (mctags-forward-line linenum)
    (when tagname
      ;; highlight the tag
      (beginning-of-line)
      (re-search-forward tagname)
      (goto-char (match-beginning 0)))
    ;; flash, Emacs v25 only API
    (when (featurep 'xref)
      (require 'xref)
      (xref-pulse-momentarily)))
  )

(defun mctags-open-file (item)
  "Find and open file of ITEM."
  (let* ((val (cdr item)))
    (mctags-open-file-api (nth 0 val) ; file
                          (nth 1 val) ; linenum
                          (file-name-directory (mctags-locate-tags-file))
                          (nth 2 val) ; tagname
                          )))

(defun mctags-open-cand (cands time)
  "Open CANDS.  Start open tags file at TIME."
  ;; mark current point for `pop-tag-mark'
  (xref-push-marker-stack)
  (cond
   ((= 1 (length cands))
    ;; open the file directly
    (mctags-open-file (car cands)))
   (t
    (ivy-read (format  "Find Tag (%.01f seconds): "
                       (float-time (time-since time)))
              cands
              :action #'mctags-open-file
              :caller 'mctags-find-tag))))

(defun mctags-find-tag-occur ()
  "Generate a custom occur buffer for `mctags-find-tag'."
  (unless (eq major-mode 'ivy-occur-grep-mode)
    (ivy-occur-grep-mode))
  ;; we use regex in elisp, don't unquote regex
  (let* ((cands (ivy--filter ivy-text mctags-find-tag-candidates)))
    ;; Need precise number of header lines for `wgrep' to work.
    (insert (format "-*- mode:grep; default-directory: %S -*-\n\n\n"
                    (file-name-directory (mctags-locate-tags-file))))
    (insert (format "%d candidates:\n" (length cands)))
    (ivy--occur-insert-lines
     (mapcar
      (lambda (cand) (concat "./" cand))
      cands))))
(ivy-set-occur 'mctags-find-tag 'mctags-find-tag-occur)
(ivy-set-display-transformer 'mctags-find-tag 'counsel-git-grep-transformer)

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
      (error "Can't find TAGS.  Please run `mctags-scan-code' at least once!"))))

;;;###autoload
(defun mctags-scan-code (&optional dir)
  "Use Ctags to scan code at DIR."
  (interactive)
  (let* ((src-dir (or dir
                      (read-directory-name "Ctags will scan code at:"
                                           (mctags-project-root)))))
    (if src-dir (mctags-scan-dir src-dir t))))

(defun mctags-find-tag-api (tagname)
  "Find tag with given TAGNAME."
  (let* ((time (current-time)))
    (setq mctags-find-tag-candidates (mctags-collect-cands tagname))
    (add-to-list 'mctags-tagname-history tagname)
    (cond
     ((not mctags-find-tag-candidates)
      ;; OK let's try grep if no tag found
      (mctags-grep tagname "No tag found. "))
     (t
      (mctags-open-cand mctags-find-tag-candidates time)))))

;;;###autoload
(defun mctags-find-tag ()
  "Input tagname to find tag."
  (interactive)
  (let* ((tagname (read-string "Please input tag name:")))
    (when (and tagname (not (string= tagname "")))
        (mctags-find-tag-api tagname))))

;;;###autoload
(defun mctags-find-tag-at-point ()
  "Find tag using tagname at point, and display all matched tags."
  (interactive)
  (mctags-tags-file-must-exist)
  (let* ((tagname (mctags-tagname-at-point)))
    (cond
     (tagname
      (mctags-find-tag-api tagname))
     (t
      (message "No tag at point")))))

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

(defun mctags-read-keyword (hint)
  "Read keyword with HINT."
  (cond
   ((region-active-p)
    (setq mctags-keyword (counsel-unquote-regex-parens (mctags-selected-str)))
    ;; de-select region
    (set-mark-command nil))
   (t
    (setq mctags-keyword (read-string hint))))
  mctags-keyword)

(defun mctags-has-quick-grep ()
  "Does ripgrep program exist?"
  (executable-find "rg"))

(defun mctags-exclude-opts (use-cache)
  "Grep CLI options.  IF USE-CACHE is t, the options is read from cache."
  (let* ((ignore-dirs (if use-cache (plist-get mctags-opts-cache :ignore-dirs)
                        mctags-ignore-directories))
         (ignore-file-names (if use-cache (plist-get mctags-opts-cache :ignore-file-names)
                              mctags-ignore-filenames)))
    (cond
     ((mctags-has-quick-grep)
      (concat (mapconcat (lambda (e) (format "-g='!%s/*'" e))
                         ignore-dirs " ")
              " "
              (mapconcat (lambda (e) (format "-g='!%s'" e))
                         ignore-file-names " ")))
     (t
      (concat (mapconcat (lambda (e) (format "--exclude-dir='%s'" e))
                         ignore-dirs " ")
              " "
              (mapconcat (lambda (e) (format "--exclude='%s'" e))
                         ignore-file-names " "))))))

(defun mctags-grep-cli (keyword use-cache &optional extra-opts)
  "Use KEYWORD, USE-CACHE, and EXTRA-OPTS to build CLI.
Extended regex is used, like (pattern1|pattern2)."
  (let* (opts cmd)
    (unless extra-opts (setq extra-opts ""))
    (cond
     ((mctags-has-quick-grep)
      (setq cmd (format "%s %s %s \"%s\" --"
                        (concat (executable-find "rg")
                                " -n -M 512 --no-heading --color never -s")
                        (mctags-exclude-opts use-cache)
                        extra-opts
                        keyword)))
     (t
      ;; use extended regex always
      (setq cmd (format "%s -rsnE %s %s \"%s\" *"
                        (or mctags-grep-program (mctags-guess-program "grep"))
                        (mctags-exclude-opts use-cache)
                        extra-opts
                        keyword))))
    cmd))

;;;###autoload
(defun mctags-grep (&optional default-keyword hint)
  "Grep at project root directory or current directory.
Try to find best grep program (ripgrep, grep...) automatically.
Extended regex like (pattern1|pattern2) is used.
If DEFAULT-KEYWORD is not nil, it's used as grep keyword.
If HINT is not nil, it's used as grep hint."
  (interactive)
  (let* ((keyword (if default-keyword default-keyword
                    (mctags-read-keyword "Enter grep pattern: ")))
         (default-directory (mctags-project-root))
         (time (current-time))
         (collection (split-string (shell-command-to-string (mctags-grep-cli keyword nil)) "[\r\n]+" t))
         (dir-summary (file-name-as-directory (file-name-base (directory-file-name (mctags-project-root))))))

    (setq mctags-opts-cache (plist-put mctags-opts-cache :ignore-dirs mctags-ignore-directories))
    (setq mctags-opts-cache (plist-put mctags-opts-cache :ignore-file-names mctags-ignore-filenames))

    (ivy-read (concat hint (format "Grep \"%s\" at %s (%.01f seconds): "
                                   keyword
                                   dir-summary
                                   (float-time (time-since time))))
              collection
              :history 'counsel-git-grep-history ; share history with counsel
              :action `(lambda (line)
                         (let* ((lst (split-string line ":"))
                                (file (car lst))
                                (linenum (string-to-number (cadr lst))))
                           (mctags-open-file-api file linenum (mctags-project-root))))
              :caller 'mctags-grep)))

(defun mctags-grep-occur ()
  "Generate a custom occur buffer for `mctags-grep'."
  (unless (eq major-mode 'ivy-occur-grep-mode)
    (ivy-occur-grep-mode))
  ;; useless to set `default-directory', it's already correct
  ;; we use regex in elisp, don't unquote regex
  (let* ((cands (ivy--filter ivy-text
                             (split-string (shell-command-to-string (mctags-grep-cli mctags-keyword t))
                                           "[\r\n]+" t))))
    ;; Need precise number of header lines for `wgrep' to work.
    (insert (format "-*- mode:grep; default-directory: %S -*-\n\n\n"
                    default-directory))
    (insert (format "%d candidates:\n" (length cands)))
    (ivy--occur-insert-lines
     (mapcar
      (lambda (cand) (concat "./" cand))
      cands))))

(ivy-set-occur 'mctags-grep 'mctags-grep-occur)
(ivy-set-display-transformer 'mctags-grep 'counsel-git-grep-transformer)

(provide 'mctags)
;;; mctags.el ends here
