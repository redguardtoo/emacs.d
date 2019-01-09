;;; counsel-etags.el ---  Fast and complete Ctags/Etags solution using ivy

;; Copyright (C) 2017,2018 Free Software Foundation, Inc.

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/counsel-etags
;; Package-Requires: ((emacs "24.4") (counsel "0.10.0") (ivy "0.10.0"))
;; Keywords: tools, convenience
;; Version: 1.7.4

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
;;   `counsel-etags-scan-code' to create tags file
;;   `counsel-etags-grep' to grep
;;   `counsel-etags-grep-symbol-at-point' to grep the symbol at point
;;   `counsel-etags-recent-tag' to open recent tag
;;   `counsel-etags-find-tag' to two step tag matching use regular expression and filter
;;   `counsel-etags-list-tag' to list all tags
;;
;; Tips:
;; - Add below code into "~/.emacs" to AUTOMATICALLY update tags file:
;;
;;   ;; Don't ask before re-reading changed TAGS files
;;   (setq tags-revert-without-query t)
;;   ;; NO warning when loading large TAGS files
;;   (setq large-file-warning-threshold nil)
;;   (add-hook 'prog-mode-hook
;;     (lambda ()
;;       (add-hook 'after-save-hook
;;                 'counsel-etags-virtual-update-tags 'append 'local)))
;;
;; - You can use ivy's negative pattern to filter candidates.
;;   For example, input "keyword1 !keyword2 keyword3" means:
;;   "(keyword1 and (not (keyword2 or keyword3))"
;;
;; - You can setup `counsel-etags-ignore-directories' and `counsel-etags-ignore-filenames',
;;   (eval-after-load 'counsel-etags
;;     '(progn
;;        ;; counsel-etags-ignore-directories does NOT support wildcast
;;        (add-to-list 'counsel-etags-ignore-directories "build_clang")
;;        (add-to-list 'counsel-etags-ignore-directories "build_clang")
;;        ;; counsel-etags-ignore-filenames supports wildcast
;;        (add-to-list 'counsel-etags-ignore-filenames "TAGS")
;;        (add-to-list 'counsel-etags-ignore-filenames "*.json")))

;; See https://github.com/redguardtoo/counsel-etags/ for more tips.

;;; Code:

(require 'xref nil t) ; xref is optional
(require 'etags)
(require 'cl-lib)
(require 'ivy)
(require 'counsel)

(defgroup counsel-etags nil
  "Complete solution to use ctags."
  :group 'tools)

(defcustom counsel-etags-smart-rules nil
  "Plugins to match filter out candidates when using `counsel-etags-find-tag-at-point'."
  :group 'counsel-etags
  :type '(repeat 'string))

(defcustom counsel-etags-stop-auto-update-tags nil
  "If t, tags will not be updated automatically."
  :group 'counsel-etags
  :type 'boolean)

(defun counsel-etags-load-smart-rules(modes rule)
  "Load MODES's smart RULES."
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
  (counsel-etags-load-smart-rules '(js-mode js2-mode rjsx-mode) 'javascript))

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
    ;; emacs
    ".cask")
  "Ignore directory names."
  :group 'counsel-etags
  :type '(repeat 'string))

(defcustom counsel-etags-ignore-filenames
  '(;; VCS
    ;; project misc
    "*.log"
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
You can setup it using \".dir-locals.el\"."
  :group 'counsel-etags
  :type '(repeat 'string))

(defcustom counsel-etags-project-root nil
  "Project root directory.  The directory is automatically detect if it's nil."
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

(defcustom counsel-etags-case-sensitive nil
  "Case sensensitive search tag name if t."
  :group 'counsel-etags
  :type 'boolean)

(defcustom counsel-etags-max-file-size 512
  "Ignore files bigger than `counsel-etags-max-file-size' kilobytes.
This option is ignore if GNU find is not installed."
  :group 'counsel-etags
  :type 'integer)

(defcustom counsel-etags-after-update-tags-hook nil
  "Hook after tags file is actually updated.
The parameter of hook is full path of tags file."
  :group 'counsel-etags
  :type 'hook)

(defcustom counsel-etags-update-interval 300
  "The interval (seconds) to update TAGS.
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
You can setup this variable manually instead.
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
  'counsel-etags-update-tags-force
  "The function we used to update tags file during auto-updating.
By default, it's `counsel-etags-update-tags-force', but you can define your
own function instead."
  :group 'counsel-etags
  :type 'sexp)

;; Timer to run auto-update TAGS.
(defconst counsel-etags-no-project-msg
  "No project found.  You can create tags file using `counsel-etags-scan-code'.
So we don't need project root at all.  Or you can setup `counsel-etags-project-root'."
  "Message to display when no project is found.")

(defvar counsel-etags-debug nil "Enable debug mode.")

(defvar counsel-etags-timer nil "Internal timer.")

(defvar counsel-etags-keyword nil "The keyword to grep.")

(defvar counsel-etags-opts-cache '() "Grep CLI options cache.")

(defvar counsel-etags-tag-history nil "History of tagnames.")

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
  (message "1.7.4"))

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

(defun counsel-etags-locate-tags-file ()
  "Find tags file: Search in parent directory or use `tags-file-name'."
  (let* ((dir (locate-dominating-file default-directory "TAGS")))
    (cond
     ;; Since we use `tags-file-name' only. The assumption is that the
     ;; only one tags file is created per project. So in theory we should find
     ;; tags file in parent directory
     ;; Besides, we don't need worry about right location of tags file when
     ;; switching projects,  using "search-parent-directory-first" method.
     (dir
      (concat dir "TAGS"))
     ((and tags-file-name (file-exists-p tags-file-name))
      tags-file-name))))

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

(defun counsel-etags-async-shell-command (command tags-file)
  "Execute string COMMAND and create TAGS-FILE asynchronously."
  (let* (proc
         (directory default-directory)
         ;; Run the shell command without any interrupt or extra information
         (buffer (generate-new-buffer "*Etags Generating Command*"))
         (display-buffer-alist '(("Etags Generating Command" display-buffer-no-window))))
    (with-current-buffer buffer
      (setq buffer-read-only nil)
      (let* ((inhibit-read-only t))
        (erase-buffer))
      (display-buffer buffer '(nil (allow-no-window . t)))
      (setq default-directory directory)
      (setq proc (start-process "Shell" buffer shell-file-name
                                shell-command-switch command))
      (set-process-sentinel proc `(lambda (process signal)

                                    (let* ((status (process-status process)))
                                    (when (memq status '(exit signal))
                                      (cond
                                       ((string= (substring signal 0 -1) "finished")
                                        (let* ((cmd (car (cdr (cdr (process-command process))))))
                                          (if counsel-etags-debug (message "`%s` executed." cmd))
                                          ;; reload tags-file
                                          (when (and ,tags-file (file-exists-p ,tags-file))
                                            (message "Tags file %s was created." ,tags-file)
                                            ;; `visit-tags-table' create buffer local variable `tags-file-name'
                                            ;; so we need make sure current buffer is correct
                                            (set-buffer ,buffer)
                                            (visit-tags-table ,tags-file t))))
                                       (t
                                        (message "Failed to create tags file.")))))))
      ;; Use the comint filter for proper handling of carriage motion
      ;; (see `comint-inhibit-carriage-motion'),.
      (set-process-filter proc 'comint-output-filter))))

(defun counsel-etags-dir-pattern (dir)
  "Trim * from DIR."
  (replace-regexp-in-string "\\`[*]*" "" (replace-regexp-in-string "[*/]*\\'" "" dir)))


(defun counsel-etags-emacs-bin-path ()
  "Get Emacs binary path."
  (let* ((emacs-executable (file-name-directory (expand-file-name invocation-name invocation-directory))))
    (replace-regexp-in-string "/" "\\\\" emacs-executable)))

(defun counsel-etags-is-exuberant-ctags (ctags-program)
  "If CTAGS-PROGRAM is Exuberant Ctags."
  (if (string-match-p "Exuberant Ctags"
                      (shell-command-to-string (concat ctags-program " --version")))
      t))

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

(defun counsel-etags-get-scan-command (find-program ctags-program)
  "Create scan command for SHELL from FIND-PROGRAM and CTAGS-PROGRAM."
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
      (setq cmd (format "%s %s %s -e %s -R ."
                        ctags-program
                        (mapconcat (lambda (p)
                                     (format "--exclude=\"%s\"" (counsel-etags-dir-pattern p)) )
                                   counsel-etags-ignore-directories " ")
                        (mapconcat (lambda (p)
                                     (format "--exclude=\"%s\"" p))
                                   counsel-etags-ignore-filenames " ")
                        (counsel-etags-ctags-options-file-cli ctags-program))))

     ;; fall back to Emacs bundled etags
     (t
      ;; (setq ctags-program (cond
      ;;                 ((eq system-type 'windows-nt)
      ;;                  (setq ctags-program (concat (counsel-etags-emacs-bin-path) "etags.exe")))
      ;;                 (t
      ;;                  (setq ctags-program "etags"))))
      ;; (setq cmd (format "%s ." ctags-program))
      (message "You need install ctags first.")))
    (when counsel-etags-debug (message "counsel-etags-get-scan-command called => find-program=%s ctags-program=%s cmd=%s" find-program ctags-program cmd))
    cmd))

(defun counsel-etags-scan-dir-internal (src-dir &optional force)
  "Create tags file from SRC-DIR.
If FORCE is t, the command is executed without checking the timer."
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
         (tags-file (file-truename (concat (file-name-as-directory src-dir) "TAGS")))
         (doit (or force (not (file-exists-p tags-file)))))
    (unless ctags-program
      (error "Please install Ctags before running this program!"))
    (when counsel-etags-debug (message "counsel-etags-scan-dir-internal called => src-dir=%s force=%s find-program=%s ctags-program=%s default-directory=%s cmd=%s" src-dir force find-program ctags-program default-directory cmd))
    ;; always update cli options
    (when doit
      (message "%s at %s" (if counsel-etags-debug cmd "Scan") default-directory)
      (counsel-etags-async-shell-command cmd tags-file))))

(defun counsel-etags-toggle-auto-update-tags ()
  "Stop/Start tags auto update."
  (interactive)
  (if (setq counsel-etags-stop-auto-update-tags
            (not counsel-etags-stop-auto-update-tags))
      (message "Tags is NOT automatically updated any more.")
    (message "Tags will be automatically updated.")))

(defun counsel-etags-scan-dir (src-dir &optional force)
  "Create tags file from SRC-DIR.
If FORCE is t, the command is executed without checking the timer.
If `counsel-etags-update-tags-backend' is customized, executed it to create tags file."
  (when counsel-etags-debug (message "counsel-etags-scan-dir called => %s %s" src-dir force))
  (cond
   (counsel-etags-stop-auto-update-tags
    ;; do nothing
    )
   ;; default backend
   ((eq counsel-etags-update-tags-backend 'counsel-etags-update-tags-force)
    (counsel-etags-scan-dir-internal src-dir force))
   ;; user has customized backend
   (t
    (funcall counsel-etags-update-tags-backend))))

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

;;;###autoload
(defun counsel-etags-update-tags-force ()
  "Update tags file now using default implementation."
  (interactive)
  (let* ((tags-file (counsel-etags-locate-tags-file)))
    (when tags-file
      (counsel-etags-scan-dir (counsel-etags-tags-file-directory) t)
      (run-hook-with-args 'counsel-etags-after-update-tags-hook tags-file)
      (unless counsel-etags-quiet-when-updating-tags
        (message "%s is updated!" tags-file)))))

(defun counsel-etags-read-file (file)
  "Return FILE content."
  (with-temp-buffer
    (insert-file-contents file)
    (buffer-string)))

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

(defun counsel-etags-sort-candidates-maybe (cands strip-count is-string)
  "Sort CANDS if `counsel-etags-candidates-optimize-limit' is t.
STRIP-COUNT strips the string before calculating distance.
IS-STRING is t if the candidate is string."
  (let* ((ref (and buffer-file-name
                   (counsel-etags--strip-path buffer-file-name strip-count))))
    (cond
     ;; Emacs 27 `string-distance' is as 100 times fast as Lisp implementation.
     ((fboundp 'string-distance)
      (sort cands `(lambda (item1 item2)
                     (let* ((a (counsel-etags--strip-path (file-truename (if ,is-string item1 (cadr item1))) ,strip-count))
                            (b (counsel-etags--strip-path (file-truename (if ,is-string item2 (cadr item2))) ,strip-count)))
                       (< (string-distance a ,ref t)
                          (string-distance b ,ref t))))))
     ((and ref
           counsel-etags-candidates-optimize-limit
           (< (length cands) counsel-etags-candidates-optimize-limit))
      (let* ((h (make-hash-table :test 'equal)))
        (sort cands `(lambda (item1 item2)
                       (let* ((a (counsel-etags--strip-path (file-truename (if ,is-string item1 (cadr item1))) ,strip-count))
                              (b (counsel-etags--strip-path (file-truename (if ,is-string item2 (cadr item2))) ,strip-count)))
                         (< (counsel-etags-levenshtein-distance a ,ref ,h)
                            (counsel-etags-levenshtein-distance b ,ref ,h)))))))
     (t
      cands))))


(defun counsel-etags-cache-content (tags-file)
  "Read cache using TAGS-FILE as key."
  (let* ((info (plist-get counsel-etags-cache (intern tags-file))))
    (plist-get info :content)))

(defun counsel-etags-cache-checksum (tags-file)
  "Read cache using TAGS-FILE as key."
  (let* ((info (plist-get counsel-etags-cache (intern tags-file))))
    (plist-get info :size)))

(defmacro counsel-etags-put (key value dictionary)
  "Add KEY VALUE pair into DICTIONARY."
  `(setq ,dictionary (plist-put ,dictionary ,key ,value)))

(defun counsel-etags-build-cand (info)
  "Build tag candidate from INFO."
  (let* ((file (plist-get info :file))
         (lnum (plist-get info :line-number))
         (text (plist-get info :text))
         (tagname (plist-get info :tagname)))
    (cons (format "%s:%s:%s" file lnum text)
          (list file lnum tagname))))

(defun counsel-etags-collect-cands (tagname fuzzy &optional dir context)
  "Parse tags file to find occurrences of TAGNAME using FUZZY algorithm in DIR.
CONTEXT is extra information collected before find tag definition."
  (when counsel-etags-debug
    (message "counsel-etags-collect-cands => tagname=%s fuzz=%s dir=%s" tagname fuzzy dir))
  (let* ((force-tags-file (and dir
                               (file-exists-p (concat (file-name-as-directory dir) "TAGS"))
                               (concat (file-name-as-directory dir) "TAGS")))
         (tags-file (or force-tags-file
                        (counsel-etags-locate-tags-file)))
         (root-dir (file-name-directory tags-file))
         (re (concat "\\([^\177\001\n]+\\)\177"
                     (if fuzzy "[^\177\001\n]+" tagname)
                     "\001\\([0-9]+\\),\\([0-9]+\\)"))
         cands
         file-size
         file-content)

    ;; ONLY when the checksum (file size) is different from the physical file size,
    ;; update cache by reading from physical file.
    ;; Not precise but acceptable algorithm.
    (when (and tags-file
               (file-exists-p tags-file)
               (not (string= (counsel-etags-cache-checksum tags-file)
                             (setq file-size (format "%s" (nth 7 (file-attributes tags-file)))))))
      (if counsel-etags-debug (message "Read file .... %s %s" (counsel-etags-cache-checksum tags-file) file-size))
      (counsel-etags-put (intern tags-file)
                         (list :content
                               (counsel-etags-read-file tags-file)
                               :size
                               file-size)
                         counsel-etags-cache))

    ;; Get better performance by scan from beginning to end.
    (when counsel-etags-debug
      (message "tags-file=%s" tags-file)
      (message "counsel-etags-cache[tags-file]=%s" (plist-get counsel-etags-cache tags-file))
      (message "force-tags-file=%s tags-file=%s" force-tags-file tags-file)
      (message "tagname=%s" tagname))

    (when (and tags-file
               (setq file-content (counsel-etags-cache-content tags-file)))
      (with-temp-buffer
        (insert file-content)
        (modify-syntax-entry ?_ "w")

        (goto-char (point-min))
        ;; first step, regex should be simple to speed up search
        (let* ((case-fold-search counsel-etags-case-sensitive))
          (while (re-search-forward tagname nil t)
            (beginning-of-line)
            ;; second step, more precise search
            (cond
             ((re-search-forward re (point-at-eol) t)
              (let* ((line-number (match-string-no-properties 2))
                     (text (match-string-no-properties 1))
                     ;; file must be set after above variables
                     (file (concat root-dir (etags-file-of-tag t)))
                     (cand (list :file file
                                 :line-number line-number
                                 :text text
                                 :tagname tagname)))
                (when (or (not context)
                          (counsel-etags-execute-predicate-function context cand))
                  (add-to-list 'cands (counsel-etags-build-cand cand)))))
             (t
              ;; need push cursor forward
              (end-of-line)))))))
    (mapcar 'car (counsel-etags-sort-candidates-maybe cands 3 nil))))

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

(defun counsel-etags-tagname-at-point ()
  "Get tag name at point."
  (or (counsel-etags-selected-str) (find-tag-default)))

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
  (when (string-match "\\`\\(.*?\\):\\([0-9]+\\):\\(.*\\)\\'" item)
    (let* ((file (match-string-no-properties 1 item))
           (linenum (match-string-no-properties 2 item))
           ;; always calculate path relative to TAGS
           (default-directory dir))

      ;; item's format is like '~/proj1/ab.el:39: (defun hello() )'
      (counsel-etags-push-marker-stack (point-marker))
      ;; open file, go to certain line
      (find-file file)
      (counsel-etags-forward-line linenum))

    ;; move focus to the tagname
    (when tagname
      ;; highlight the tag
      (beginning-of-line)
      (re-search-forward tagname)
      (goto-char (match-beginning 0)))

    ;; flash, Emacs v25 only API
    (when (fboundp 'xref-pulse-momentarily)
      (xref-pulse-momentarily))))

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
  (add-to-list 'counsel-etags-tag-history (cons cand dir)))

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
      (ivy-read (format  "Find Tag (%.01f seconds): "
                         (float-time (time-since time)))
                cands
                :action `(lambda (e)
                           (counsel-etags-remember e ,dir)
                           (counsel-etags-open-file-api e
                                                        ,dir
                                                        ,tagname))
                :caller 'counsel-etags-find-tag)))))

(defun counsel-etags-tags-file-must-exist ()
  "Make sure tags file does exist."
  (when (not (counsel-etags-locate-tags-file))
    (let* ((src-dir (read-directory-name "Ctags will scan code at:"
                                         (counsel-etags-locate-project))))
      (if src-dir (counsel-etags-scan-dir src-dir t)
        (error "Can't find TAGS.  Please run `counsel-etags-scan-code'!")))))

;;;###autoload
(defun counsel-etags-scan-code (&optional dir)
  "Use Ctags to scan code at DIR."
  (interactive)
  (let* ((src-dir (or dir
                      (read-directory-name "Ctags will scan code at:"
                                           (or (counsel-etags-locate-project)
                                               default-directory)))))
    (when src-dir
      (counsel-etags-scan-dir src-dir t))))

(defun counsel-etags-positive-regex (patterns)
  "Extract positive regex from PATTERNS."
  (let* ((re (car patterns)))
    (cond
     ((or (not re) (string= re ""))
      "[^ \t]+")
     (t
      (ivy--regex re)))))

(defun counsel-etags-negative-regex (patterns)
  "Extract negative regex from PATTERNS."
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

(defun counsel-etags-list-tag-function (string)
  "Find matching tags by search STRING."
  (cond
   ((< (length string) 3)
    ;; new version
    (ivy-more-chars))
   (t
    ;; I prefer build the regex by myself
    (let* ((patterns (split-string string " *!"))
           (pos-re (counsel-etags-positive-regex patterns))
           (neg-re (counsel-etags-negative-regex patterns))
           rlt)
      ;; use positive pattern to get collection
      ;; when using dynamic collection
      (setq rlt (counsel-etags-collect-cands pos-re t))
      ;; then use negative pattern to exclude candidates
      (when (and rlt neg-re)
        (setq rlt (delq nil (mapcar
                             `(lambda (s)
                               (unless (string-match-p ,neg-re s) s))
                             rlt))))
      (setq counsel-etags-find-tag-candidates rlt)
      rlt))))

(defun counsel-etags-find-tag-api (tagname fuzzy &optional context)
  "Find TAGNAME using FUZZY algorithm.  CONTEXT is extra information collected before finding tag definition."
  (let* ((time (current-time))
         (dir (counsel-etags-tags-file-directory)))
    (when counsel-etags-debug (message "counsel-etags-find-tag-api called => %s %s %s" tagname fuzzy dir))
    ;; Dir should not be nil
    (when dir
      (cond
       ((not tagname)
        ;; OK, need use ivy-read to find candidate
        (ivy-read "Fuzz matching tags:"
                  #'counsel-etags-list-tag-function
                  :history 'counsel-git-grep-history
                  :dynamic-collection t
                  :action `(lambda (e)
                             (counsel-etags-open-file-api e ,dir))
                  :caller 'counsel-etags-find-tag))

       ((not (setq counsel-etags-find-tag-candidates
                   (counsel-etags-collect-cands tagname fuzzy dir context)))
        ;; OK let's try grep if no tag found
        (counsel-etags-grep tagname "No tag found. "))

       (t
        ;; open the one selected candidate
        (counsel-etags-open-tag-cand tagname counsel-etags-find-tag-candidates time))))))


;;;###autoload
(defun counsel-etags-list-tag ()
  "List all tags."
  (interactive)
  (counsel-etags-tags-file-must-exist)
  (counsel-etags-find-tag-api nil t))

;;;###autoload
(defun counsel-etags-find-tag ()
  "Find tag in two step.
Step 1, user need input regex to fuzzy match tag.
Any tag whose sub-string matches regex will be listed.

Step 2, user could filter tags."
  (interactive)
  (counsel-etags-tags-file-must-exist)
  (let* ((tagname (read-string "Regex to match tag:"
                               (or (counsel-etags-selected-str) ""))))
    (when (and tagname (not (string= tagname "")))
        (counsel-etags-find-tag-api tagname t))))

;;;###autoload
(defun counsel-etags-find-tag-at-point ()
  "Find tag using tagname at point."
  (interactive)
  (counsel-etags-tags-file-must-exist)
  (let* ((tagname (counsel-etags-tagname-at-point))
         (context (counsel-etags-execute-collect-function)))
    (cond
     (tagname
      (let* ((counsel-etags-case-sensitive t))
        ;; TODO try to get context here from rule and pass
        ;; into API call
        (counsel-etags-find-tag-api tagname nil context)))
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
the tags updating might not happen."
  (interactive)
  (let* ((dir (and buffer-file-name
                   (file-name-directory buffer-file-name)))
         (tags-file (counsel-etags-locate-tags-file)))
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
        (funcall counsel-etags-update-tags-backend)
        (message "counsel-etags took %d seconds to update TAGS!"
                 (- (float-time (current-time))
                    (float-time counsel-etags-timer))))))))

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

(defun counsel-etags-read-keyword (hint)
  "Read keyword with HINT."
  (let* ((str (if (region-active-p) (counsel-etags-selected-str)
                (read-string hint))))
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
    (format "%s %s \"%s\" --"
            (concat (executable-find "rg")
                    ;; (if counsel-etags-debug " --debug")
                    " -n -M 512 --no-heading --color never -s --path-separator /")
            (counsel-etags-exclude-opts use-cache)
            keyword))
   (t
    ;; use extended regex always
    (format "%s -rsnE %s \"%s\" *"
            (or counsel-etags-grep-program (counsel-etags-guess-program "grep"))
            (counsel-etags-exclude-opts use-cache)
            keyword))))

;;;###autoload
(defun counsel-etags-grep (&optional default-keyword hint)
  "Grep at project root directory or current directory.
Try to find best grep program (ripgrep, grep...) automatically.
Extended regex like (pattern1|pattern2) is used.
If DEFAULT-KEYWORD is not nil, it's used as grep keyword.
If HINT is not nil, it's used as grep hint."
  (interactive)
  (let* ((keyword (if default-keyword default-keyword
                    (counsel-etags-read-keyword "Enter grep pattern: ")))
         (default-directory (file-truename (counsel-etags-locate-project)))
         (time (current-time))
         (cmd (counsel-etags-grep-cli keyword nil))
         (cands (split-string (shell-command-to-string cmd) "[\r\n]+" t))
         (dir-summary (file-name-as-directory (file-name-base (directory-file-name (counsel-etags-locate-project))))))

    (if counsel-etags-debug (message "counsel-etags-grep called => %s %s %s %s" keyword default-directory cmd cands))
    (counsel-etags-put :ignore-dirs
                       counsel-etags-ignore-directories
                       counsel-etags-opts-cache)

    (counsel-etags-put :ignore-file-names
                       counsel-etags-ignore-filenames
                       counsel-etags-opts-cache)

    ;; Slow down grep 10 times
    (ivy-read (concat hint (format "Grep \"%s\" at %s (%.01f seconds): "
                                   keyword
                                   dir-summary
                                   (float-time (time-since time))))
              cands
              :history 'counsel-git-grep-history ; share history with counsel
              :action `(lambda (item)
                         ;; when grepping, we grepping in project root
                         (counsel-etags-open-file-api item
                                                      ,default-directory
                                                      ,keyword))
              :caller 'counsel-etags-grep)))

;;;###autoload
(defun counsel-etags-grep-symbol-at-point ()
  "Similar to `counsel-etags-grep' but grep symbol at point."
  (interactive)
  (counsel-etags-grep (or (counsel-etags-selected-str)
                          (thing-at-point 'symbol))))

;; {{ occur setup
(defun counsel-etags-tag-occur-api (items)
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

(defun counsel-etags-find-tag-occur ()
  "Open occur buffer for `counsel-etags-find-tag' and `counsel-etagslist-tag'."
  (counsel-etags-tag-occur-api counsel-etags-find-tag-candidates))

(defun counsel-etags-grep-occur ()
  "Open occur buffer for `counsel-etags-grep'."
  (unless (eq major-mode 'ivy-occur-grep-mode)
    (ivy-occur-grep-mode))
  ;; useless to set `default-directory', it's already correct
  ;; we use regex in elisp, don't unquote regex
  (let* ((cands (ivy--filter ivy-text
                             (split-string (shell-command-to-string (counsel-etags-grep-cli counsel-etags-keyword t))
                                           "[\r\n]+" t))))
    ;; Need precise number of header lines for `wgrep' to work.
    (insert (format "-*- mode:grep; default-directory: %S -*-\n\n\n"
                    default-directory))
    (insert (format "%d candidates:\n" (length cands)))
    (ivy--occur-insert-lines
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
