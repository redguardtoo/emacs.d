;;; counsel-etags.el ---  Fast and complete Ctags/Etags solution using ivy  -*- lexical-binding: t -*-

;; Copyright (C) 2018, 2019 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/counsel-etags
;; Package-Requires: ((emacs "24.4") (counsel "0.10.0") (ivy "0.10.0"))
;; Keywords: tools, convenience
;; Version: 1.9.1

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;; This file is not part of GNU Emacs.

;;; Commentary:

;;  Setup:
;;   "Ctags" (Universal Ctags is recommended) should exist.
;;   "GNU Find" is used if it's installed but it's optional.
;;   Or else, customize `counsel-etags-update-tags-backend' to generate tags file
;;
;; Usage:
;;
;;   `counsel-etags-find-tag-at-point' to navigate.  This command will also
;;   run `counsel-etags-scan-code' AUTOMATICALLY if tags file is not built yet.
;;
;;   Run `counsel-etags-list-tag-in-current-file' to list tags in current file.
;;
;;   Or just use native imenu with below setup,
;;      (setq imenu-create-index-function
;;            'counsel-etags-imenu-default-create-index-function)
;;
;;   `counsel-etags-scan-code' to create tags file
;;   `counsel-etags-grep' to grep
;;   `counsel-etags-grep-current-directory' to grep in current directory
;;   `counsel-etags-recent-tag' to open recent tag
;;   `counsel-etags-find-tag' to two steps tag matching use regular expression and filter
;;   `counsel-etags-list-tag' to list all tags
;;   `counsel-etags-update-tags-force' to update current tags file by force
;;
;; Tips:
;; - Add below code into "~/.emacs" to AUTOMATICALLY update tags file:
;;
;;   ;; Don't ask before reloading updated tags files
;;   (setq tags-revert-without-query t)
;;   ;; NO warning when loading large tag files
;;   (setq large-file-warning-threshold nil)
;;   (add-hook 'prog-mode-hook
;;     (lambda ()
;;       (add-hook 'after-save-hook
;;                 'counsel-etags-virtual-update-tags 'append 'local)))
;;
;; - You can use ivy's exclusion patterns to filter candidates.
;;   For example, input "keyword1 !keyword2 keyword3" means:
;;   "(keyword1 and (not (or keyword2 keyword3)))"
;;
;; - `counsel-etags-extra-tags-files' contains extra tags files to parse.
;;   Set it like,
;;     (setq counsel-etags-extra-tags-files
;;           '("./TAGS" "/usr/include/TAGS" "$PROJ1/include/TAGS"))
;;
;;   Files in `counsel-etags-extra-tags-files' have only symbol with absolute path.
;;
;; - You can set up `counsel-etags-ignore-directories' and `counsel-etags-ignore-filenames',
;;   (eval-after-load 'counsel-etags
;;     '(progn
;;        ;; counsel-etags-ignore-directories does NOT support wildcast
;;        (add-to-list 'counsel-etags-ignore-directories "build_clang")
;;        (add-to-list 'counsel-etags-ignore-directories "build_clang")
;;        ;; counsel-etags-ignore-filenames supports wildcast
;;        (add-to-list 'counsel-etags-ignore-filenames "TAGS")
;;        (add-to-list 'counsel-etags-ignore-filenames "*.json")))
;;
;;  - Rust programming language is supported.
;;    The easiest setup is to use ".dir-locals.el".
;;   in root directory.  The content of .dir-locals.el" is as below,
;;   ((nil . ((counsel-etags-update-tags-backend . (lambda (src-dir) (shell-command "rusty-tags Emacs")))
;;            (counsel-etags-tags-file-name . "rusty-tags.emacs"))))
;;
;;  - User could use `counsel-etags-convert-grep-keyword' to customize grep keyword.
;;    Below setup enable `counsel-etags-grep' to search Chinese using pinyinlib,
;;
;;    (unless (featurep 'pinyinlib) (require 'pinyinlib))
;;    (setq counsel-etags-convert-grep-keyword
;;      (lambda (keyword)
;;        (if (and keyword (> (length keyword) 0))
;;            (pinyinlib-build-regexp-string keyword t)
;;          keyword)))
;;
;;  - `counsel-etags-find-tag-name-function' finds tag name at point.  If it returns nil,
;;    `find-tag-default' is used.  `counsel-etags-word-at-point' gets word at point.
;;
;;  - User could append the extra content into tags file in `counsel-etags-after-update-tags-hook'.
;;    The parameter of hook is full path of the tags file.  `counsel-etags-tags-line' is a tool function
;;    to help user

;; See https://github.com/redguardtoo/counsel-etags/ for more tips.

;;; Code:

(require 'xref nil t) ; xref is optional
(require 'etags)
(require 'cl-lib)
(require 'find-file)
(require 'counsel nil t) ; counsel => swiper => ivy

(defgroup counsel-etags nil
  "Complete solution to use ctags."
  :group 'tools)

(defcustom counsel-etags-smart-rules nil
  "Plugins to match filter out candidates when using `counsel-etags-find-tag-at-point'."
  :group 'counsel-etags
  :type '(repeat 'string))

(defcustom counsel-etags-command-to-scan-single-code-file nil
  "Shell Command to scan single file.
If it's nil, a command using ctags is automatically created."
  :group 'counsel-etags
  :type 'string)

(defcustom counsel-etags-extra-tags-files nil
  "List of extra tags files to load.  They are not updated automatically.

A typical format is

    (\"./TAGS\" \"/usr/include/TAGS\" \"$PROJECT/*/include/TAGS\")

Environment variables can be inserted between slashes (`/').
They will be replaced by their definition.  If a variable does
not exist, it is replaced (silently) with an empty string.

Symbol location inside tags file should use absolute path.
A CLI to create tags file:

  find /usr/include | ctags -e -L -"
  :group 'counsel-etags
  :type '(repeat 'string))

(defcustom counsel-etags-stop-auto-update-tags nil
  "If t, tags will not be updated automatically."
  :group 'counsel-etags
  :type 'boolean)

(defcustom counsel-etags-convert-grep-keyword 'identity
  "Convert keyword to grep to new regex to feed into grep program.

Here is code to enable grepping Chinese using pinyinlib,

  (unless (featurep 'pinyinlib) (require 'pinyinlib))
  (setq counsel-etags-convert-grep-keyword
         (lambda (keyword)
           (if (and keyword (> (length keyword) 0))
               (pinyinlib-build-regexp-string keyword t)
             keyword)))"
  :group 'counsel-etags
  :type 'function)

(defcustom counsel-etags-can-skip-project-root nil
  "If t, scanning project root is optional."
  :group 'counsel-etags
  :type 'boolean)

(defcustom counsel-etags-find-tag-name-function nil
  "The function to use to find tag name at point.
It should be a function that takes no arguments and returns an string.
If it returns nil, the `find-tag-default' is used.

The function `counsel-etags-word-at-point' could be used find word at point.
The definition of word is customized by the user."
  :group 'counsel-etags
  :type 'function)

;; (defvar counsel-etags-unit-test-p nil
;;   "Running unit test.  This is internal variable.")

(defun counsel-etags-load-smart-rules(modes rule)
  "Load MODES's smart RULE."
  (dolist (mode modes)
    (setq counsel-etags-smart-rules
          (plist-put counsel-etags-smart-rules
                     mode
                     (let* ((rule-filename (concat "counsel-etags-" (symbol-name rule)))
                            (fn-prefix (concat "counsel-etags-" (symbol-name rule)))
                            (collect-function (intern (concat fn-prefix "-collect")))
                            (predicate-function (intern (concat fn-prefix "-predicate"))))
                       (autoload collect-function rule-filename nil)
                       (autoload predicate-function rule-filename nil)
                       (cons collect-function predicate-function))))))

(defun counsel-etags-setup-smart-rules ()
  "Initialize `counsel-etags-smart-rules'."
  (interactive)
  (counsel-etags-load-smart-rules '(js-mode js2-mode rjsx-mode js2-jsx-mode) 'javascript))

(defun counsel-etags-execute-collect-function ()
  "Return context before finding tag definition."
  (let* ((fn (car (plist-get counsel-etags-smart-rules major-mode))))
    (cond
     (fn
      (funcall fn))
     (t
      nil))))

(defun counsel-etags-execute-predicate-function (context candidate)
  "Use CONTEXT to test CANDIDATE.  If return nil, the CANDIDATE is excluded."
  (let* ((m (plist-get context :major-mode))
         (fn (cdr (plist-get counsel-etags-smart-rules m))))
    (cond
     (fn
      (funcall fn context candidate))
     (t
      ;; If there is no predicate, candidate is included.
      t))))

(defcustom counsel-etags-ignore-directories
  '(;; VCS
    ".git"
    ".svn"
    ".cvs"
    ".bzr"
    ".hg"
    ;; project misc
    "bin"
    "fonts"
    "images"
    ;; Mac
    ".DS_Store"
    ;; html/javascript/css
    ".npm"
    ".tmp" ; TypeScript
    ".sass-cache" ; SCSS/SASS
    ".idea"
    "node_modules"
    "bower_components"
    ;; python
    ".tox"
    ;; vscode
    ".vscode"
    ;; emacs
    ".cask")
  "Ignore directory names."
  :group 'counsel-etags
  :type '(repeat 'string))

(defcustom counsel-etags-ignore-filenames
  '(;; VCS
    ;; project misc
    "*.log"
    ;; rusty-tags
    "rusty-tags.vim"
    "rusty-tags.emacs"
    ;; Ctags
    "tags"
    "TAGS"
    ;; compressed
    "*.tgz"
    "*.gz"
    "*.xz"
    "*.zip"
    "*.tar"
    "*.rar"
    ;; Global/Cscope
    "GTAGS"
    "GPATH"
    "GRTAGS"
    "cscope.files"
    ;; html/javascript/css
    "*bundle.js"
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
    "*.ppt"
    "*.pdf"
    "*.odt"
    ;; C/C++
    ".clang-format"
    "*.obj"
    "*.so"
    "*.o"
    "*.a"
    "*.ifso"
    "*.tbd"
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
  :group 'counsel-etags
  :type '(repeat 'string))

(defcustom counsel-etags-project-file '("TAGS" "tags" ".svn" ".hg" ".git")
  "The file/directory used to locate project root directory.
You can set up it in \".dir-locals.el\"."
  :group 'counsel-etags
  :type '(repeat 'string))

(defcustom counsel-etags-project-root nil
  "Project root directory.  The directory automatically detects if it's nil."
  :group 'counsel-etags
  :type 'string)

(defcustom counsel-etags-tags-file-name "TAGS"
  "Tags file name."
  :group 'counsel-etags
  :type 'string)

(defcustom counsel-etags-ctags-options-file "~/.ctags"
  "File to read options from, like \"~/.ctags\".
Universal Ctags won't read options from \"~/.ctags\" by default.
So we force Universal Ctags to load \"~/.ctags\".

Exuberant Ctags actually can NOT open option file \".ctags\" through cli option.

But path \"~/.ctags\" is OK because we use Emacs Lisp to load \"~.ctags\".

Please use file name like \"ctags.cnf\" instead \".ctags\" when customize this variable.

Universal Ctags does NOT have this bug."
  :group 'counsel-etags
  :type 'string)

(defcustom counsel-etags-candidates-optimize-limit 256
  "Re-order candidates if candidate count is less than this variable's value.
Candidates whose file path has Levenshtein distance to current file/directory.
You may set it to nil to disable re-ordering for performance reason."
  :group 'counsel-etags
  :type 'integer)

(defcustom counsel-etags-max-file-size 512
  "Ignore files bigger than `counsel-etags-max-file-size' kilobytes.
This option is ignored if GNU find is not installed."
  :group 'counsel-etags
  :type 'integer)

(defcustom counsel-etags-after-update-tags-hook nil
  "Hook after tags file is actually updated.
The parameter of hook is full path of the tags file."
  :group 'counsel-etags
  :type 'hook)

(defcustom counsel-etags-update-interval 300
  "The interval (seconds) to update tags file.
Used by `counsel-etags-virtual-update-tags'.
Default value is 300 seconds."
  :group 'counsel-etags
  :type 'integer)

(defcustom counsel-etags-find-program nil
  "GNU find program.  Program is automatically detected if it's nil.
On Windows program path separator IS four backward slashes by default."
  :group 'counsel-etags
  :type 'string)

(defcustom counsel-etags-tags-program nil
  "Tags Program.  Program is automatically detected if it's nil.
You can set up this variable manually instead.
If you use Emacs etags, set this variable to \"etags\".'.
If you use Exuberant Ctags, set this variable to \"ctags -e -L\".'.
You may add extra options to tags program.  For example, as C developer
may set this variable to \"ctags --c-kinds=defgpstux -e -L\".
On Windows program path separator IS four backward slashes by default."
  :group 'counsel-etags
  :type 'string)

(defcustom counsel-etags-grep-program nil
  "Grep program.  Program is automatically detected if it's nil.
On Windows program path separator IS four backward slashes by default."
  :group 'counsel-etags
  :type 'string)

(defcustom counsel-etags-quiet-when-updating-tags t
  "Be quiet when updating tags."
  :group 'counsel-etags
  :type 'boolean)

(defcustom counsel-etags-update-tags-backend
  'counsel-etags-scan-dir-internal
  "A user-defined function to update tags file during auto-updating.
The function has same parameters as `counsel-etags-scan-dir-internal'."
  :group 'counsel-etags
  :type 'sexp)

(defconst counsel-etags-no-project-msg
  "No project found.  You can create tags file using `counsel-etags-scan-code'.
So we don't need the project root at all.
Or you can set up `counsel-etags-project-root'."
  "Message to display when no project is found.")

(defvar counsel-etags-debug nil "Enable debug mode.")

;; Timer to run auto-update tags file
(defvar counsel-etags-timer nil "Internal timer.")

(defvar counsel-etags-keyword nil "The keyword to grep.")

(defvar counsel-etags-opts-cache '() "Grep CLI options cache.")

(defvar counsel-etags-tag-history nil "History of tagnames.")

(defvar counsel-etags-tags-file-history nil
  "Tags files history.  Recently accessed file is at the top of history.
The file is also used by tags file auto-update process.")

(defvar counsel-etags-find-tag-candidates nil "Find tag candidate.")

(defvar counsel-etags-cache nil "Cache of multiple tags files.")

(defun counsel-etags-win-path (executable-name drive)
  "Guess EXECUTABLE-NAME's full path in Cygwin on DRIVE."
  (let* ((path (concat drive ":\\\\cygwin64\\\\bin\\\\" executable-name ".exe")))
    (if (file-exists-p path) path)))

;;;###autoload
(defun counsel-etags-guess-program (executable-name)
  "Guess path from its EXECUTABLE-NAME on Windows.
Return nil if it's not found."
  (cond
   ((file-remote-p default-directory)
    ;; Assume remote server has already added EXE into $PATH!
    executable-name)
   ((eq system-type 'windows-nt)
    (or (counsel-etags-win-path executable-name "c")
        (counsel-etags-win-path executable-name "d")
        (counsel-etags-win-path executable-name "e")
        (counsel-etags-win-path executable-name "f")
        (counsel-etags-win-path executable-name "g")
        (counsel-etags-win-path executable-name "h")))
   (t
    (if (executable-find executable-name) (executable-find executable-name)))))

;;;###autoload
(defun counsel-etags-version ()
  "Return version."
  (message "1.9.1"))

;;;###autoload
(defun counsel-etags-get-hostname ()
  "Reliable way to get current hostname.
`(getenv \"HOSTNAME\")' won't work because $HOSTNAME is NOT an
 environment variable.
`system-name' won't work because /etc/hosts could be modified"
  (with-temp-buffer
    (shell-command "hostname" t)
    (goto-char (point-max))
    (delete-char -1)
    (buffer-string)))

(defun counsel-etags-get-tags-file-path (dir)
  "Get full path of tags file from DIR."
  (and dir (file-truename (concat (file-name-as-directory dir)
                                  counsel-etags-tags-file-name))))

(defun counsel-etags-locate-tags-file ()
  "Find tags file: Search `counsel-etags-tags-file-history' and parent directories."
  (counsel-etags-get-tags-file-path (locate-dominating-file default-directory
                                                            counsel-etags-tags-file-name)))

(defun counsel-etags-tags-file-directory ()
  "Directory of tags file."
  (let* ((f (counsel-etags-locate-tags-file)))
    (if f (file-name-directory (file-truename f)))))

(defun counsel-etags-locate-project ()
  "Return the root of the project."
  (let* ((tags-dir (if (listp counsel-etags-project-file)
                       (cl-some (apply-partially 'locate-dominating-file
                                                 default-directory)
                                counsel-etags-project-file)
                     (locate-dominating-file default-directory
                                             counsel-etags-project-file)))
         (project-root (or counsel-etags-project-root
                           (and tags-dir (file-name-as-directory tags-dir)))))
    (or project-root
        (progn (message counsel-etags-no-project-msg)
               nil))))

(defun counsel-etags-add-tags-file-to-history (tags-file)
  "Add TAGS-FILE to the top of `counsel-etags-tags-file-history'."
  (let* ((file (file-truename tags-file))
         (rlt (delq nil (mapcar
                         (lambda (s)
                           (unless (string= file (file-truename s)) s))
                         counsel-etags-tags-file-history))))
    (add-to-list 'rlt tags-file)
    (setq counsel-etags-tags-file-history rlt)))

;;;###autoload
(defun counsel-etags-async-shell-command (command tags-file)
  "Execute string COMMAND and create TAGS-FILE asynchronously."
  (let* ((proc (start-process "Shell" nil shell-file-name shell-command-switch command)))
    (set-process-sentinel
     proc
     `(lambda (process signal)
        (let* ((status (process-status process)))
          (when (memq status '(exit signal))
            (cond
             ((string= (substring signal 0 -1) "finished")
              (let* ((cmd (car (cdr (cdr (process-command process))))))
                (if counsel-etags-debug (message "`%s` executed." cmd))
                ;; reload tags-file
                (when (and ,tags-file (file-exists-p ,tags-file))
                  (run-hook-with-args 'counsel-etags-after-update-tags-hook ,tags-file)
                  (message "Tags file %s was created." ,tags-file))))
             (t
              (message "Failed to create tags file.")))))))))

(defun counsel-etags-dir-pattern (dir)
  "Trim * from DIR."
  (replace-regexp-in-string "\\`[*]*" "" (replace-regexp-in-string "[*/]*\\'" "" dir)))


(defun counsel-etags-emacs-bin-path ()
  "Get Emacs binary path."
  (let* ((emacs-executable (file-name-directory (expand-file-name invocation-name
                                                                  invocation-directory))))
    (replace-regexp-in-string "/" "\\\\" emacs-executable)))

(defun counsel-etags-is-exuberant-ctags (ctags-program)
  "If CTAGS-PROGRAM is Exuberant Ctags."
  (let* ((cmd-output (shell-command-to-string (concat ctags-program " --version"))))
    (and (not (string-match-p "Universal Ctags" cmd-output))
         (string-match-p "Exuberant Ctags" cmd-output))))

(defun counsel-etags-ctags-options-file-cli (ctags-program)
  "Use CTAGS-PROGRAM to create command line for `counsel-etags-ctags-options-file'."
  (cond
   ;; no options file
   ((or (not counsel-etags-ctags-options-file)
        (string= counsel-etags-ctags-options-file ""))
    "")

   ;; If options file is "~/.ctags" and ctags program is Exuberant Ctags
   ;; "~/.ctags" won't be loaded.
   ;; But if options file is empty, "~/.ctags" will be loaded.
   ;; It's a bug of Exuberant Ctags, have to work around it here.
   ((and (counsel-etags-is-exuberant-ctags ctags-program)
         (string= (file-truename "~/.ctags")
                  (file-truename counsel-etags-ctags-options-file)))
    "")

   (t
    (format "--options=\"%s\""
            (file-truename counsel-etags-ctags-options-file)))))

(defun counsel-etags-get-scan-command (find-program ctags-program &optional code-file)
  "Create scan command for SHELL from FIND-PROGRAM and CTAGS-PROGRAM.
If CODE-FILE is a real file, the command scans it and output to stdout."
  (let* ((cmd ""))
    (cond
     ;; use both find and ctags
     ((and find-program ctags-program)
      (setq cmd (format "%s . \\( %s \\) -prune -o -type f -not -size +%sk %s -print | %s -e %s -L -"
                        find-program
                        (mapconcat (lambda (p)
                                     (format "-iwholename \"*/%s\"" (counsel-etags-dir-pattern p)) )
                                   counsel-etags-ignore-directories " -or ")
                        counsel-etags-max-file-size
                        (mapconcat (lambda (n) (format "-not -name \"%s\"" n))
                                   counsel-etags-ignore-filenames " ")
                        ctags-program
                        (counsel-etags-ctags-options-file-cli ctags-program))))
     ;; Use ctags only
     (ctags-program
      (setq cmd (format "%s %s %s -e %s %s -R %s"
                        ctags-program
                        (mapconcat (lambda (p)
                                     (format "--exclude=\"%s\"" (counsel-etags-dir-pattern p)) )
                                   counsel-etags-ignore-directories " ")
                        (mapconcat (lambda (p)
                                     (format "--exclude=\"%s\"" p))
                                   counsel-etags-ignore-filenames " ")
                        (counsel-etags-ctags-options-file-cli ctags-program)
                        (if code-file "-f -" "")
                        (if code-file (format "\"%s\"" code-file ) "."))))

     ;; fall back to Emacs bundled etags
     (t
      ;; (setq ctags-program (cond
      ;;                 ((eq system-type 'windows-nt)
      ;;                  (setq ctags-program (concat (counsel-etags-emacs-bin-path) "etags.exe")))
      ;;                 (t
      ;;                  (setq ctags-program "etags"))))
      ;; (setq cmd (format "%s ." ctags-program))
      (message "You need install Ctags at first.  Universal Ctags is highly recommended.")))
    (when counsel-etags-debug
      (message "counsel-etags-get-scan-command called => find-program=%s ctags-program=%s cmd=%s"
               find-program ctags-program cmd))
    cmd))

;;;###autoload
(defun counsel-etags-scan-dir-internal (src-dir)
  "Create tags file from SRC-DIR."
  ;; TODO save the ctags-opts into hash
  (let* ((find-program (or counsel-etags-find-program
                           (counsel-etags-guess-program "find")))
         (ctags-program (or counsel-etags-tags-program
                            (counsel-etags-guess-program "ctags")))
         (default-directory src-dir)
         ;; if both find and ctags exist, use both
         ;; if only ctags exists, use ctags
         ;; run find&ctags to create TAGS, `-print` is important option to filter correctly
         (cmd (counsel-etags-get-scan-command find-program ctags-program))
         (tags-file (counsel-etags-get-tags-file-path src-dir)))
    (unless ctags-program
      (error "Please install Ctags before running this program!"))
    (when counsel-etags-debug (message "counsel-etags-scan-dir-internal called => src-dir=%s find-program=%s ctags-program=%s default-directory=%s cmd=%s" src-dir find-program ctags-program default-directory cmd))
    ;; always update cli options
    (message "%s at %s" (if counsel-etags-debug cmd "Scan") default-directory)
    (counsel-etags-async-shell-command cmd tags-file)))

(defun counsel-etags-toggle-auto-update-tags ()
  "Stop/Start tags auto update."
  (interactive)
  (if (setq counsel-etags-stop-auto-update-tags
            (not counsel-etags-stop-auto-update-tags))
      (message "Tags is NOT automatically updated any more.")
    (message "Tags will be automatically updated.")))

(defun counsel-etags-scan-dir (src-dir)
  "Create tags file from SRC-DIR."
  (if counsel-etags-debug (message "counsel-etags-scan-dir called => %s" src-dir))
  (cond
   (counsel-etags-stop-auto-update-tags
    ;; do nothing
    )
   (t
    (funcall counsel-etags-update-tags-backend src-dir))))

;;;###autoload
(defun counsel-etags-directory-p (regex)
  "Does directory of current file match REGEX?"
  (let* ((case-fold-search nil)
         (dir (or (when buffer-file-name
                    (file-name-directory buffer-file-name))
                  ;; buffer is created in real time
                  default-directory
                  "")))
    (string-match-p regex dir)))

;;;###autoload
(defun counsel-etags-filename-p (regex)
  "Does current file match REGEX?"
  (let* ((case-fold-search nil)
         (file (or buffer-file-name default-directory "")))
    (string-match-p regex file)))

(defun counsel-etags-read-file-internal (file)
  "Read FILE content."
  (with-temp-buffer
    (insert-file-contents file)
    (buffer-string)))

(defun counsel-etags-read-file (file)
  "Return FILE content with child files included."
  (let* ((raw-content (counsel-etags-read-file-internal file))
         (start 0)
         (re "^\\([^,]+\\),include$")
         included
         (extra-content ""))
    (while (setq start (string-match re raw-content start))
      (when (file-exists-p (setq included (match-string 1 raw-content)))
        (setq extra-content (concat extra-content
                                    "\n"
                                    (counsel-etags-read-file-internal included))))
      (setq start (+ start (length included))))
    (concat raw-content extra-content)))

(defmacro counsel-etags--tset (table x y val row-width)
  "Set TABLE cell at position (X, Y) with VAL and ROW-WIDTH."
  `(aset ,table (+ ,x (* ,row-width ,y)) ,val))

(defmacro counsel-etags--tref (table x y row-width)
  "Get TABLE cell at position (X, Y) with ROW-WIDTH."
  `(aref ,table (+ ,x (* ,row-width ,y))))

(defun counsel-etags-levenshtein-distance (str1 str2 hash)
  "Return the edit distance between strings STR1 and STR2.
HASH store the previous distance."
  (let* ((val (gethash str1 hash)))
    (unless val
      (let* ((length-str1 (length str1))
             (length-str2 (length str2))
             ;; it's impossible files name has more than 512 characters
             (d (make-vector (* (1+ length-str1) (1+ length-str2)) 0))
             ;; d is a table with lenStr2+1 rows and lenStr1+1 columns
             (row-width (1+ length-str1))
             (rlt 0)
             (i 0)
             (j 0))
        ;; i and j are used to iterate over str1 and str2
        (while (<= i length-str1) ;; for i from 0 to lenStr1
          (counsel-etags--tset d i 0 i row-width) ;; d[i, 0] := i
          (setq i (1+ i)))
        (while (<= j length-str2) ;; for j from 0 to lenStr2
          (counsel-etags--tset d 0 j j row-width) ;; d[0, j] := j
          (setq j (1+ j)))
        (setq i 1)
        (while (<= i length-str1) ;; for i from 1 to lenStr1
          (setq j 1)
          (while (<= j length-str2) ;; for j from 1 to lenStr2
            (let* ((cost
                    ;; if str[i] = str[j] then cost:= 0 else cost := 1
                    (if (equal (aref str1 (1- i)) (aref str2 (1- j))) 0 1))
                   ;; d[i-1, j] + 1     // deletion
                   (deletion (1+ (counsel-etags--tref d (1- i) j row-width)))
                   ;; d[i, j-1] + 1     // insertion
                   (insertion (1+ (counsel-etags--tref d i (1- j) row-width)))
                   ;; d[i-j,j-1] + cost // substitution
                   (substitution (+ (counsel-etags--tref d (1- i) (1- j) row-width) cost))
                   (distance (min insertion deletion substitution)))
              (counsel-etags--tset d i j distance row-width)
              (setq j (1+ j))))
          (setq i (1+ i))) ;; i++
        ;; return d[lenStr1, lenStr2] or the max distance
        (setq val (counsel-etags--tref d length-str1 length-str2 row-width))
        (puthash str1 val hash)))
    val))

(defun counsel-etags--strip-path (path strip-count)
  "Strip PATH with STRIP-COUNT."
  (let* ((i (1- (length path))))
    (while (and (> strip-count 0)
                (> i 0))
      (when (= (aref path i) ?/)
        (setq strip-count (1- strip-count)))
      (setq i (1- i)))
    (if (= 0 strip-count) (substring path (+ 1 i))
      path)))

(defun counsel-etags-sort-candidates-maybe (cands strip-count is-string current-file)
  "Sort CANDS if `counsel-etags-candidates-optimize-limit' is t.
STRIP-COUNT strips the string before calculating distance.
IS-STRING is t if the candidate is string.
CURRENT-FILE is used to compare with candidate path."
  (let* ((ref (and current-file (counsel-etags--strip-path current-file strip-count))))
    (cond
     ;; don't sort candidates
     ((or (not ref)
          (not counsel-etags-candidates-optimize-limit)
          (>= (length cands) counsel-etags-candidates-optimize-limit))
      cands)

     ;; sort in Lisp
     ((not (fboundp 'string-distance))
      (let* ((h (make-hash-table :test 'equal)))
        (sort cands `(lambda (item1 item2)
                       (let* ((a (counsel-etags--strip-path (file-truename (if ,is-string item1 (cadr item1))) ,strip-count))
                              (b (counsel-etags--strip-path (file-truename (if ,is-string item2 (cadr item2))) ,strip-count)))
                         (< (counsel-etags-levenshtein-distance a ,ref ,h)
                            (counsel-etags-levenshtein-distance b ,ref ,h)))))))

     ;; Emacs 27 `string-distance' is as 100 times fast as Lisp implementation.
     ;; sort in C
     (t
      (sort cands `(lambda (item1 item2)
                     (let* ((a (counsel-etags--strip-path (file-truename (if ,is-string item1 (cadr item1))) ,strip-count))
                            (b (counsel-etags--strip-path (file-truename (if ,is-string item2 (cadr item2))) ,strip-count)))
                       (< (string-distance a ,ref t)
                          (string-distance b ,ref t)))))))))


(defun counsel-etags-cache-content (tags-file)
  "Read cache using TAGS-FILE as key."
  (let* ((info (plist-get counsel-etags-cache (intern tags-file))))
    (plist-get info :content)))

(defun counsel-etags-cache-filesize (tags-file)
  "Read cache using TAGS-FILE as key."
  (let* ((info (plist-get counsel-etags-cache (intern tags-file))))
    (or (plist-get info :filesize) 0)))

(defmacro counsel-etags-put (key value dictionary)
  "Add KEY VALUE pair into DICTIONARY."
  `(setq ,dictionary (plist-put ,dictionary ,key ,value)))

(defun counsel-etags-build-cand (info)
  "Build tag candidate from INFO.
If SHOW-ONLY-TEXT is t, the candidate shows only text."
  (let* ((file (plist-get info :file))
         (lnum (plist-get info :line-number))
         (text (plist-get info :text))
         (tagname (plist-get info :tagname))
         (head (format "%s:%s:%s" file lnum text)))
    (cons head
          (list file lnum tagname))))

(defmacro counsel-etags-push-one-candidate (cands tagname-re bound root-dir context)
  "Push new candidate into CANDS.
Use TAGNAME-RE to search in current buffer with BOUND in ROOT-DIR.
CONTEXT is extra information."
    `(cond
      ((re-search-forward ,tagname-re ,bound t)
       (let* ((line-number (match-string-no-properties 3))
              (text (match-string-no-properties 1))
              ;; file must be set after above variables
              (file (etags-file-of-tag t))
              (cand (list :file file ; relative path
                          :fullpath (if (file-name-absolute-p file) file
                                      (concat ,root-dir file)) ; absolute path
                          :line-number line-number
                          :text text
                          :tagname (match-string-no-properties 2))))
         (when (or (not ,context)
                   (counsel-etags-execute-predicate-function context cand))
           ;; if root-dir is nil, only one file is processed.
           ;; So don't bother about file path
           (push (counsel-etags-build-cand cand) ,cands)))
       t)
      (t
       ;; need push cursor forward
       (end-of-line)
       nil)))

(defun counsel-etags-extract-cands (tags-file tagname fuzzy context)
  "Parse TAGS-FILE to find occurrences of TAGNAME using FUZZY algorithm.
CONTEXT is extra information collected before find tag definition."
  (let* ((root-dir (file-name-directory tags-file))
         (tagname-re (concat "\\([^\177\001\n]+\\)\177\\("
                             (if fuzzy "[^\177\001\n]+" tagname)
                             "\\)\001\\([0-9]+\\),\\([0-9]+\\)"))
         cands
         file-size
         file-content)
    ;; ONLY when the checksum (file size) is different from the physical file size,
    ;; update cache by reading from physical file.
    ;; Not precise but acceptable algorithm.
    (when (and tags-file
               (file-exists-p tags-file)
               ;; TAGS file is smaller when being created.
               ;; Do NOT load incomplete tags file
               (< (counsel-etags-cache-filesize tags-file)
                  (setq file-size (nth 7 (file-attributes tags-file)))))
      (when counsel-etags-debug
        (message "Read file .... %s %s" (counsel-etags-cache-filesize tags-file) file-size))
      (counsel-etags-put (intern tags-file)
                         (list :content
                               (counsel-etags-read-file tags-file)
                               :filesize
                               file-size)
                         counsel-etags-cache))

    ;; Get better performance by scan from beginning to end.
    (when counsel-etags-debug
      (message "tags-file=%s tagname=%s" tags-file tagname))

    (when (and tags-file
               (setq file-content (counsel-etags-cache-content tags-file)))
      (with-temp-buffer
        (insert file-content)
        (modify-syntax-entry ?_ "w")
        (goto-char (point-min))
        ;; first step, regex should be simple to speed up search
        (let* ((case-fold-search fuzzy))
            ;; normal tag search algorithm
          (while (re-search-forward tagname nil t)
            (beginning-of-line)
            ;; second step, more precise search
            (counsel-etags-push-one-candidate cands
                                              tagname-re
                                              (point-at-eol)
                                              root-dir
                                              context)))))
    (and cands (nreverse cands))))

(defun counsel-etags-collect-cands (tagname fuzzy current-file &optional dir context)
  "Find TAGNAME using FUZZY algorithm in CURRENT-FILE of DIR.
CONTEXT is extra information collected before find tag definition."
  (let* (rlt
         (force-tags-file (and dir
                               (file-exists-p (counsel-etags-get-tags-file-path dir))
                               (counsel-etags-get-tags-file-path dir)))
         (tags-file (or force-tags-file
                        (counsel-etags-locate-tags-file)))
         (cands (and tags-file (counsel-etags-extract-cands tags-file
                                                            tagname
                                                            fuzzy
                                                            context))))

    ;; current-file is used to calculated string distance.
    (setq rlt (mapcar 'car (counsel-etags-sort-candidates-maybe cands 3 nil current-file)))
    (when counsel-etags-extra-tags-files
      ;; don't sort candidate from 3rd party libraries
      (dolist (file (ff-list-replace-env-vars counsel-etags-extra-tags-files))
        (when (setq cands (counsel-etags-extract-cands file
                                                       tagname
                                                       fuzzy
                                                       context))
          ;; don't bother sorting candidates from third party tags file
          (setq rlt (append rlt (mapcar 'car cands))))))
    rlt))

(defun counsel-etags-encode(s)
  "Encode S."
  ;; encode "{}[]"
  (setq s (replace-regexp-in-string "\"" "\\\\\"" s))
  (setq s (replace-regexp-in-string "\\?" "\\\\\?" s))
  (setq s (replace-regexp-in-string "\\$" "\\\\x24" s))
  (setq s (replace-regexp-in-string "\\*" "\\\\\*" s))
  (setq s (replace-regexp-in-string "\\." "\\\\\." s))
  (setq s (replace-regexp-in-string "\\[" "\\\\\[" s))
  (setq s (replace-regexp-in-string "\\]" "\\\\\]" s))
  ;; perl-regex support non-ASCII characters
  ;; Turn on `-P` from `git grep' and `grep'
  ;; the_silver_searcher and ripgrep need no setup
  (setq s (replace-regexp-in-string "{" "\\\\{" s))
  (setq s (replace-regexp-in-string "}" "\\\\}" s))
  s)

(defun counsel-etags-selected-str ()
  "Get selected string.  Suppose plain text instead regex in selected text.
So we need *encode* the string."
  (if (region-active-p)
      (counsel-etags-encode (buffer-substring-no-properties (region-beginning)
                                                            (region-end)))))

(defmacro counsel-etags-tagname-at-point ()
  "Get tag name at point."
  `(or (counsel-etags-selected-str)
       (and counsel-etags-find-tag-name-function
            (funcall counsel-etags-find-tag-name-function))
       (find-tag-default)))

(defun counsel-etags-forward-line (lnum)
  "Forward LNUM lines."
  (setq lnum (string-to-number lnum))
  (when (and lnum (> lnum 0))
    (goto-char (point-min))
    (forward-line (1- lnum))))

(defun counsel-etags-open-file-api (item dir &optional tagname)
  "Open ITEM while `default-directory' is DIR.
Focus on TAGNAME if it's not nil."
  ;; jump
  (let* ((is-str (and (stringp item)
                      (string-match "\\`\\(.*?\\):\\([0-9]+\\):\\(.*\\)\\'"
                                    item)))
         (file (if is-str (match-string-no-properties 1 item)
                 (nth 0 item)))
         (linenum (if is-str (match-string-no-properties 2 item)
                    (nth 1 item)))
         ;; always calculate path relative to TAGS
         (default-directory dir))

    (when counsel-etags-debug
      (message "counsel-etags-open-file-api called => dir=%s, linenum=%s, file=%s" dir linenum file))

    ;; item's format is like '~/proj1/ab.el:39: (defun hello() )'
    (counsel-etags-push-marker-stack (point-marker))
    ;; open file, go to certain line
    (find-file file)
    (counsel-etags-forward-line linenum))

  ;; move focus to the tagname
  (beginning-of-line)
  ;; search tagname in current line might fail
  ;; maybe tags files is updated yet
  (when (and tagname
             ;; focus on the tag if possible
             (re-search-forward tagname (line-end-position) t))
    (goto-char (match-beginning 0)))

  ;; flash, Emacs v25 only API
  (when (fboundp 'xref-pulse-momentarily)
    (xref-pulse-momentarily)))

(defun counsel-etags-push-marker-stack (mark)
  "Save current MARK (position)."
  ;; un-select region
  (if (region-active-p) (pop-mark))
  ;; flash
  (if (fboundp 'xref-push-marker-stack)
      (xref-push-marker-stack mark)
    (and (boundp 'find-tag-marker-ring)
         (ring-insert find-tag-marker-ring mark))))

(defun counsel-etags-remember (cand dir)
  "Remember CAND whose `default-directory' is DIR."
  (setq counsel-etags-tag-history
        (cl-remove-if `(lambda (s) (string= ,cand (car s)))
                      counsel-etags-tag-history))
  (add-to-list 'counsel-etags-tag-history (cons cand dir)))

(defun counsel-etags--time-cost (start-time)
  "Show time cost since START-TIME."
  (let* ((time-passed (float-time (time-since start-time))))
    (format "%.01f second%s"
            time-passed
            (if (<= time-passed 2) "" "s"))))

(defun counsel-etags-open-tag-cand (tagname cands time)
  "Find TAGNAME from CANDS.  Open tags file at TIME."
  ;; mark current point for `pop-tag-mark'
  (let* ((dir (counsel-etags-tags-file-directory)))
    (cond
     ((= 1 (length cands))
      ;; open the file directly
      (counsel-etags-remember (car cands) dir)
      (counsel-etags-open-file-api (car cands)
                                   dir
                                   tagname))
     (t
      (ivy-read (format  "Find Tag (%s): "
                         (counsel-etags--time-cost time))
                cands
                :action `(lambda (e)
                           (counsel-etags-remember e ,dir)
                           (counsel-etags-open-file-api e
                                                        ,dir
                                                        ,tagname))
                :caller 'counsel-etags-find-tag)))))

(defun counsel-etags-tags-file-must-exist ()
  "Make sure tags file does exist."
  (let* ((tags-file (counsel-etags-locate-tags-file))
         src-dir)
    (when (and (not tags-file)
               (not counsel-etags-can-skip-project-root))
      (setq src-dir (read-directory-name "Ctags will scan code at:"
                                         (counsel-etags-locate-project)))
      (cond
       (src-dir
        (counsel-etags-scan-dir src-dir)
        (setq tags-file (counsel-etags-get-tags-file-path src-dir)))
       (t
        (error "Can't find TAGS.  Please run `counsel-etags-scan-code'!"))))
    ;; the tags file IS touched
    (when tags-file
      (counsel-etags-add-tags-file-to-history tags-file))))

;;;###autoload
(defun counsel-etags-word-at-point (predicate)
  "Get word at point.  PREDICATE should return t on testing word character.

For example, get a word when dot character is part of word,

   (counsel-etags-word-at-point (lambda (c)
                                  (or (= c ?.)
                                      (and (>= c ?0) (<= c ?9))
                                      (and (>= c ?A) (<= c ?Z))
                                      (and (>= c ?a) (<= c ?z)))))"
  (let* ((rlt (char-to-string (following-char)))
         (b (line-beginning-position))
         (e (line-end-position)))
    ;; backward
    (save-excursion
      (backward-char)
      (while (and (>= (point) b) (funcall predicate (following-char)))
        (setq rlt (concat (char-to-string (following-char)) rlt))
        (backward-char)))

    (save-excursion
      (forward-char)
      (while (and (< (point) e) (funcall predicate (following-char)))
        (setq rlt (concat rlt (char-to-string (following-char)) ))
        (forward-char)))
    rlt))

;;;###autoload
(defun counsel-etags-scan-code (&optional dir)
  "Use Ctags to scan code at DIR."
  (interactive)
  (let* ((src-dir (or dir
                      (read-directory-name "Ctags will scan code at:"
                                           (or (counsel-etags-locate-project)
                                               default-directory)))))
    (when src-dir
      (counsel-etags-scan-dir src-dir))))

(defun counsel-etags-positive-regex (patterns)
  "Extract positive regex from PATTERNS."
  (let* ((re (car patterns)))
    (cond
     ((or (not re) (string= re ""))
      "[^ \t]+")
     (t
      (ivy--regex re)))))

(defun counsel-etags-exclusion-regex (patterns)
  "Extract exclusion PATTERNS."
  (let* ((re (cadr patterns)))
    (unless re (setq re ""))
    ;; remove trailing spaces
    (setq re (replace-regexp-in-string " +$" "" re))
    (cond
     ((string= re "")
      (setq re nil))
     (t
      (mapconcat 'ivy--regex
                 (split-string re " +")
                 "\\\|")))))

(defun counsel-etags-list-tag-function (string current-file)
  "Find matching tags by search STRING.
Tags might be sorted by comparing tag's path with CURRENT-FILE."
  (cond
   ((< (length string) 3)
    ;; new version
    (ivy-more-chars))
   (t
    ;; I prefer build the regex by myself
    (let* ((patterns (split-string string " *!"))
           (pos-re (counsel-etags-positive-regex patterns))
           (neg-re (counsel-etags-exclusion-regex patterns))
           rlt)
      ;; use positive pattern to get collection
      ;; when using dynamic collection
      (setq rlt (counsel-etags-collect-cands pos-re t current-file))
      ;; then use exclusion patterns to exclude candidates
      (when (and rlt neg-re)
        (setq rlt (delq nil (mapcar
                             `(lambda (s)
                               (unless (string-match-p ,neg-re s) s))
                             rlt))))
      (setq counsel-etags-find-tag-candidates rlt)
      rlt))))

(defun counsel-etags-find-tag-api (tagname fuzzy current-file &optional context)
  "Find TAGNAME using FUZZY algorithm from CURRENT-FILE.
CONTEXT is extra information collected before finding tag definition."
  (let* ((time (current-time))
         (dir (counsel-etags-tags-file-directory)))
    (when counsel-etags-debug
      (message "counsel-etags-find-tag-api called => tagname=%s fuzzy=%s dir%s current-file=%s context=%s"
               tagname
               fuzzy
               dir
               current-file
               context))
    ;; Dir could be nil. User could use `counsel-etags-extra-tags-files' instead
    (cond
     ((not tagname)
      ;; OK, need use ivy-read to find candidate
      (ivy-read "Fuzz matching tags:"
                `(lambda (s)
                   (counsel-etags-list-tag-function s ,current-file))
                :history 'counsel-git-grep-history
                :dynamic-collection t
                :action `(lambda (e)
                           (counsel-etags-open-file-api e ,dir))
                :caller 'counsel-etags-find-tag))

     ((not (setq counsel-etags-find-tag-candidates
                 (counsel-etags-collect-cands tagname fuzzy current-file dir context)))
      ;; OK let's try grep if no tag found
      (counsel-etags-grep tagname "No tag found. "))

     (t
      ;; open the one selected candidate
      (counsel-etags-open-tag-cand tagname counsel-etags-find-tag-candidates time)))))


;;;###autoload
(defun counsel-etags-list-tag ()
  "List all tags.  Tag is fuzzy and case insensitively matched."
  (interactive)
  (counsel-etags-tags-file-must-exist)
  (counsel-etags-find-tag-api nil t buffer-file-name))


;;;###autoload
(defun counsel-etags-imenu-default-create-index-function ()
  "Create an index alist for the definitions in the current buffer."
  (let* ((ctags-program (or counsel-etags-tags-program
                            (counsel-etags-guess-program "ctags")))
         (code-file buffer-file-name)
         (tagname-re (concat "\\([^\177\001\n]+\\)\177\\("
                             "[^\177\001\n]+"
                             "\\)\001\\([0-9]+\\),\\([0-9]+\\)"))
         cmd
         imenu-items
         cands)
    (unless code-file
      (setq code-file
            (make-temp-file (expand-file-name "coet"
                                              temporary-file-directory))))

    (when (and code-file (file-exists-p code-file))
      (setq cmd
            (cond
             (counsel-etags-command-to-scan-single-code-file
              (concat counsel-etags-command-to-scan-single-code-file
                      "\""
                      code-file
                      "\""))
             (t
              (counsel-etags-get-scan-command nil ctags-program code-file))))

      ;; create one item for imenu list
      ;; (cons name
      ;;       (if imenu-use-markers (point-marker) (point)))
      (with-temp-buffer
        (insert (shell-command-to-string cmd))
        (modify-syntax-entry ?_ "w")
        (goto-char (point-min))
        (let* ((case-fold-search nil))
          ;; normal tag search algorithm
          (while (re-search-forward tagname-re (point-max) t)
            ;; push (name . line)
            (push (cons (match-string-no-properties 2)
                        (match-string-no-properties 3))
                  cands))))

      ;; now cands is just name and line number
      ;; we need convert it into imenu items (name . marker)
      (save-excursion
        (dolist (c cands)
          (let* ((name (car c)))
            (goto-char (point-min))
            (counsel-etags-forward-line (cdr c))
            (search-forward name (point-at-eol))
            (forward-char (- (length name)))
            (push (cons name (point-marker)) imenu-items)))))
    imenu-items))

;;;###autoload
(defun counsel-etags-list-tag-in-current-file()
  "List tags in current file."
  (interactive)
  (let* ((imenu-items (counsel-etags-imenu-default-create-index-function)))
    (when imenu-items
      (ivy-read "Recent tag names:"
                imenu-items
                :action (lambda (e)
                          (goto-char (cdr e)))))))

;;;###autoload
(defun counsel-etags-find-tag ()
  "Find tag in two step.
Step 1, user need input regex to fuzzy and case insensitively match tag.
Any tag whose sub-string matches regex will be listed.

Step 2, user keeps filtering tags."
  (interactive)
  (counsel-etags-tags-file-must-exist)
  (let* ((tagname (read-string "Regex to match tag: "
                               (or (counsel-etags-selected-str) ""))))
    (when (and tagname (not (string= tagname "")))
        (counsel-etags-find-tag-api tagname t buffer-file-name))))

;;;###autoload
(defun counsel-etags-find-tag-at-point ()
  "Find tag using tagname at point.
Please note parsing tags file containing line with 2K characters could be slow.
That's the known issue of Emacs Lisp.  The program itself is perfectly fine."
  (interactive)
  (counsel-etags-tags-file-must-exist)
  (let* ((tagname (counsel-etags-tagname-at-point))
         (context (counsel-etags-execute-collect-function)))
    (cond
     (tagname
        ;; TODO try to get context here from rule and pass
        ;; into API call
        (counsel-etags-find-tag-api tagname nil buffer-file-name context))
     (t
      (message "No tag at point")))))

;;;###autoload
(defun counsel-etags-recent-tag ()
  "Find tag using tagname from `counsel-etags-tag-history'."
  (interactive)
  (cond
   ((not counsel-etags-tag-history)
    (message "`counsel-etags-tag-history' is empty."))
   (t
    (let* ((dir (counsel-etags-tags-file-directory))
           ;; filter the recent tags from this project
           (collection (delq nil (mapcar
                                  (lambda (e) (if (string= dir (cdr e)) e))
                           counsel-etags-tag-history))))
      (when collection
        (ivy-read "Recent tag names:"
                  collection
                  :action `(lambda (e)
                             (counsel-etags-open-file-api (car e) (cdr e)))
                  :caller 'counsel-etags-recent-tag))))))

;;;###autoload
(defun counsel-etags-virtual-update-tags()
  "Scan code and create tags file again.
It's the interface used by other hooks or commands.
The tags updating might not happen."
  (interactive)
  (let* ((dir (and buffer-file-name
                   (file-name-directory buffer-file-name)))
         (tags-file (and counsel-etags-tags-file-history
                         (car counsel-etags-tags-file-history))))
    (when (and dir
               tags-file
               (string-match-p (file-name-directory (file-truename tags-file))
                               (file-truename dir)))
      (cond
       ((not counsel-etags-timer)
        ;; start timer if not started yet
        (setq counsel-etags-timer (current-time)))

       ((< (- (float-time (current-time)) (float-time counsel-etags-timer))
           counsel-etags-update-interval)
        ;; do nothing, can't run ctags too often
        )

       (t
        (setq counsel-etags-timer (current-time))
        (let* ((tags-file (counsel-etags-locate-tags-file))
               (dir (file-name-directory (file-truename tags-file))))
          (funcall counsel-etags-update-tags-backend dir)))))))

(defun counsel-etags-unquote-regex-parens (str)
  "Unquote regexp parentheses in STR."
  (replace-regexp-in-string "\\\\[(){}]\\|[()]"
                            (lambda (s)
                              (or (cdr (assoc s '(("\\(" . "(")
                                                  ("\\)" . ")")
                                                  ("(" . "\\(")
                                                  (")" . "\\)")
                                                  ("\\{" . "{")
                                                  ("\\}" . "}"))))
                                  (error "Unexpected parenthesis: %S" s)))
                            str t t))

(defun counsel-etags-read-keyword (hint &optional symbol-at-point)
  "Read keyword with HINT.
If SYMBOL-AT-POINT is nil, don't read symbol at point."
  (let* ((str (cond
               ((region-active-p)
                (setq counsel-git-grep-history
                      (add-to-list 'counsel-git-grep-history
                                   (counsel-etags-selected-str)))
                (counsel-etags-selected-str))
               (t
                (read-from-minibuffer hint
                                      (if symbol-at-point (thing-at-point 'symbol))
                                      nil
                                      nil
                                      'counsel-git-grep-history)))))
    (when str
      (cond
       ((region-active-p)
        (add-to-list 'minibuffer-history str)
        (setq counsel-etags-keyword (counsel-etags-unquote-regex-parens str))
        ;; de-select region
        (set-mark-command nil))
       (t
        ;; processing double quotes character
        (setq counsel-etags-keyword (replace-regexp-in-string "\"" "\\\\\""str))))))
  counsel-etags-keyword)

(defun counsel-etags-has-quick-grep ()
  "Does ripgrep program exist?"
  (executable-find "rg"))

(defun counsel-etags-exclude-opts (use-cache)
  "Grep CLI options.  IF USE-CACHE is t, the options is read from cache."
  (let* ((ignore-dirs (if use-cache (plist-get counsel-etags-opts-cache :ignore-dirs)
                        counsel-etags-ignore-directories))
         (ignore-file-names (if use-cache (plist-get counsel-etags-opts-cache :ignore-file-names)
                              counsel-etags-ignore-filenames)))
    ;; please note Windows DOS CLI only support double quotes
    (cond
     ((counsel-etags-has-quick-grep)
      (concat (mapconcat (lambda (e)
                           (format "-g=\"!%s/*\"" e))
                         ignore-dirs " ")
              " "
              (mapconcat (lambda (e)
                           (format "-g=\"!%s\"" e))
                         ignore-file-names " ")))
     (t
      (concat (mapconcat (lambda (e)
                           (format "--exclude-dir=\"%s\"" e))
                         ignore-dirs " ")
              " "
              (mapconcat (lambda (e)
                           (format "--exclude=\"%s\"" e))
                         ignore-file-names " "))))))

(defun counsel-etags-grep-cli (keyword use-cache)
  "Use KEYWORD and USE-CACHE to build CLI.
Extended regex is used, like (pattern1|pattern2)."
  (cond
   ((counsel-etags-has-quick-grep)
    ;; "--hidden" force ripgrep to search hidden files/directories, that's default
    ;; behavior of grep
    (format "%s --hidden %s \"%s\" --"
            (concat (executable-find "rg")
                    ;; (if counsel-etags-debug " --debug")
                    " -n -M 1024 --no-heading --color never -s --path-separator /")
            (counsel-etags-exclude-opts use-cache)
            keyword))
   (t
    ;; use extended regex always
    (format "%s -rsnE %s \"%s\" *"
            (or counsel-etags-grep-program (counsel-etags-guess-program "grep"))
            (counsel-etags-exclude-opts use-cache)
            keyword))))

(defun counsel-etags-parent-directory (level directory)
  "Return LEVEL up parent directory of DIRECTORY."
  (let* ((rlt directory))
    (while (and (> level 0) (not (string= "" rlt)))
      (setq rlt (file-name-directory (directory-file-name rlt)))
      (setq level (1- level)))
    (if (string= "" rlt) (setq rlt nil))
    rlt))

(defun counsel-etags-dirname (directory)
  "Get DIRECTORY name without parent."
  (file-name-as-directory (file-name-base (directory-file-name directory))))

;;;###autoload
(defun counsel-etags-grep (&optional default-keyword hint root)
  "Grep at project root directory or current directory.
Try to find best grep program (ripgrep, grep...) automatically.
Extended regex like (pattern1|pattern2) is used.
If DEFAULT-KEYWORD is not nil, it's used as grep keyword.
If HINT is not nil, it's used as grep hint.
ROOT is root directory to grep."
  (interactive)
  (let* ((text (if default-keyword default-keyword
                  (counsel-etags-read-keyword "Grep pattern: ")))
         (keyword (funcall counsel-etags-convert-grep-keyword text))
         (default-directory (file-truename (or root
                                               (counsel-etags-locate-project))))
         (time (current-time))
         (cmd (counsel-etags-grep-cli keyword nil))
         (cands (split-string (shell-command-to-string cmd) "[\r\n]+" t))
         (dir-summary (counsel-etags-dirname default-directory)))

    (if counsel-etags-debug (message "counsel-etags-grep called => %s %s %s %s"
                                     keyword default-directory cmd cands))
    (counsel-etags-put :ignore-dirs
                       counsel-etags-ignore-directories
                       counsel-etags-opts-cache)

    (counsel-etags-put :ignore-file-names
                       counsel-etags-ignore-filenames
                       counsel-etags-opts-cache)

    ;; Slow down grep 10 times
    (ivy-read (concat hint (format "Grep \"%s\" at %s (%s): "
                                   text
                                   dir-summary
                                   (counsel-etags--time-cost time)))
              cands
              :history 'counsel-git-grep-history ; share history with counsel
              :action `(lambda (item)
                         ;; when grepping, we grepping in project root
                         (counsel-etags-open-file-api item
                                                      ,default-directory
                                                      ,keyword))
              :caller 'counsel-etags-grep)))

;;;###autoload
(defun counsel-etags-grep-current-directory (&optional level)
  "Grep current directory or LEVEL up parent directory."
  (interactive "P")
  (unless level (setq level 0))
  (let* ((root (counsel-etags-parent-directory level default-directory)))
    (counsel-etags-grep nil nil root)))

;;;###autoload
(defun counsel-etags-update-tags-force (&optional forced-tags-file)
  "Update current tags file using default implementation.
If FORCED-TAGS-FILE is nil, the updating process might now happen."
  (interactive)
  (let* ((tags-file (or forced-tags-file
                        (counsel-etags-locate-tags-file))))
    (when tags-file
      (counsel-etags-scan-dir (file-name-directory (file-truename tags-file)))
      (unless counsel-etags-quiet-when-updating-tags
        (message "%s is updated!" tags-file)))))

;;;###autoload
(defun counsel-etags-tag-line (code tag-name line-number &optional byte-offset)
  "One line in tag file using CODE, TAG-NAME, LINE-NUMBER, and BYTE-OFFSET."
  (format "%s\177%s\001%s,%s\n"
          code
          tag-name
          line-number
          (or byte-offset 0)))

;; {{ occur setup
(defun counsel-etags-tag-occur-api (items)
  "Create occur buffer for ITEMS."
  (unless (eq major-mode 'ivy-occur-grep-mode)
    (ivy-occur-grep-mode))
  ;; we use regex in elisp, don't unquote regex
  (let* ((cands (ivy--filter ivy-text items)))
    ;; Need precise number of header lines for `wgrep' to work.
    (insert (format "-*- mode:grep; default-directory: %S -*-\n\n\n"
                    (file-name-directory (counsel-etags-locate-tags-file))))
    (insert (format "%d candidates:\n" (length cands)))
    (ivy--occur-insert-lines
     (mapcar
      (lambda (cand) (concat "./" cand))
      cands))))

(defun counsel-etags-recent-tag-occur ()
  "Open occur buffer for `counsel-etags-recent-tag'."
  (counsel-etags-tag-occur-api counsel-etags-tag-history))

(defun counsel-etags-occur-insert-lines (cands)
  "A alternative of `swiper--occur-insert-lines'."
  (cond
   ((fboundp 'swiper--occur-insert-lines)
    (swiper--occur-insert-lines cands))
   (t
    ;; below code could be delete when new stable version of swiper/ivy is released
    (let ((inhibit-read-only t))
      (insert (format "-*- mode:grep; default-directory: %S -*-\n\n\n"
                      default-directory))
      (insert (format "%d candidates:\n" (length cands)))
      (ivy--occur-insert-lines cands)
      (goto-char (point-min))
      (forward-line 4)))))

(defun counsel-etags-find-tag-occur ()
  "Open occur buffer for `counsel-etags-find-tag' and `counsel-etagslist-tag'."
  (counsel-etags-tag-occur-api counsel-etags-find-tag-candidates))

(defun counsel-etags-grep-occur (&optional _cands)
  "Open occur buffer for `counsel-etags-grep'."
  (unless (eq major-mode 'ivy-occur-grep-mode)
    (ivy-occur-grep-mode)
    (font-lock-mode -1))
  ;; useless to set `default-directory', it's already correct
  ;; we use regex in elisp, don't unquote regex
  (let* ((cands (ivy--filter ivy-text
                             (split-string (shell-command-to-string (counsel-etags-grep-cli counsel-etags-keyword t))
                                           "[\r\n]+" t))))
    (counsel-etags-occur-insert-lines
     (mapcar
      (lambda (cand) (concat "./" cand))
      cands))))

(ivy-set-occur 'counsel-etags-recent-tag 'counsel-etags-recent-tag-occur)
(ivy-set-display-transformer 'counsel-etags-recent-tag 'counsel-git-grep-transformer)
(ivy-set-occur 'counsel-etags-find-tag 'counsel-etags-find-tag-occur)
(ivy-set-display-transformer 'counsel-etags-find-tag 'counsel-git-grep-transformer)

(ivy-set-occur 'counsel-etags-grep 'counsel-etags-grep-occur)
(ivy-set-display-transformer 'counsel-etags-grep 'counsel-git-grep-transformer)
;; }}

(counsel-etags-setup-smart-rules)

(provide 'counsel-etags)
;;; counsel-etags.el ends here
