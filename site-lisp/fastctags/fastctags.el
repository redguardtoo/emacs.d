;;; fastctags.el -- navigate&complete code with Universal Ctags  -*- lexical-binding: t -*-

;; Copyright (C) 2026 Chen Bin

;; Author: Chen Bin
;; URL: https://github.com/redguardtoo/fastctags
;; Version: 0.0.1
;; Keywords: convenience
;; Package-Requires: ((emacs "29.1"))

;; This file is NOT part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This library completes code using tags file created by Ctags.
;; It uses a much faster algorithm optimized for ctags.
;; It takes only 9 seconds to load 300M tags file which is created by
;; scanning the Linux Kernel code v5.3.1.
;; After initial loading, this library will respond immediately
;; when new tags file is created.
;;
;; Usage:
;;
;;   Step 1, insert below code into your configuration,
;;
;;     (fastctags-auto-setup)
;;
;;   Step 2, use Ctags to create tags file and enjoy,
;;
;;   Step 3,
;;     Code navigation:
;;      - "M-x fastctags-nav-find-tag-at-point"
;;      - "M-x fastctags-nav-find-tag"
;;      - "M-x fastctags-nav-recent-tag"
;;    Code completion:
;;      - Use company or corfu or anything you like
;;
;; Tips:
;;
;;   - Set `fastctags-extra-tags-files' to load extra tags files,
;;       (setq fastctags-extra-tags-files '("$HOME/TAGS" "/usr/include/TAGS"))
;;
;;   - Set `fastctags-complete-ignore-case-p' to ignore case when fetching candidates
;;
;;   - Use rusty-tags to generate tags file for Rust programming language.
;;   Add below code into ~/.emacs,
;;       (setq fastctags-tags-file-name "rusty-tags.emacs")
;;
;;   - Make sure CLI program diff is executable on Windows.
;;   It's optional but highly recommended.  It can speed up tags file updating.
;;   This package uses diff through variable `diff-command'.
;;
;;   - "M-x fastctags-debug-info" for debugging.
;;
;;   -- Make sure `fastctags-update-tags-file-interval' is greater than the total
;;   seconds Ctags program takes to scan code.
;;

;;; Code:

(require 'xref nil t) ; xref is optional
(require 'rx)
(require 'cl-lib)
(require 'tramp nil t)
(require 'find-file)
(require 'subr-x)

(defgroup fastctags nil
  "Completion backend for ctags."
  :group 'convenience)

(defcustom fastctags-complete-ignore-case-p nil
  "Non-nil to ignore case in code completion candidates."
  :type 'boolean)

(defcustom fastctags-extra-tags-files nil
  "List of extra tags files which are loaded only once.

A typical format is,

    (\"./TAGS\" \"/usr/include/TAGS\" \"$PROJECT/*/include/TAGS\")

Environment variables can be inserted between slashes (`/').
They will be replaced by their definitions.  If a variable does
not exist, it is replaced (silently) with an empty string."
  :type '(repeat string))

(defcustom fastctags-quiet nil
  "Be quiet and do not notify user tags file status."
  :type 'boolean)

(defcustom fastctags-complete-everywhere nil
  "Non-nil to offer code completions in comments&strings."
  :type '(choice (const :tag "Off" nil)
                 (const :tag "On" t)))

(defcustom fastctags-update-tags-file-interval 150
  "The interval (seconds) to generate the tags file and update cache.
Used by `fastctags-virtual-update-tags'."
  :type 'integer)

(defcustom fastctags-tags-file-loading-speedup-min-size (* 4 1024 1024)
  "Minimum size of tags file whose loading can be optimized."
  :type 'integer)

(defcustom fastctags-tag-name-valid-characters
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ$#@%_!*&1234567890"
  "The characters of tag name.  It's used for partition algorithm."
  :type 'string)

(defvar-local fastctags-cached-current-tags-file nil)

(defvar fastctags-tags-file-cache nil
  "The cached tags files.")

(defvar fastctags-debug nil
  "Enable debug logging.")

(defvar fastctags-complete-cached-candidates nil
  "The cached candidates searched with certain prefix.")

(defcustom fastctags-ignore-config-files
  '(".gitignore"
    ".hgignore"
    "~/.ignore")
  "Path of configuration file which specifies files that should ignore.
Path is either absolute path or relative to the tags file."
  :group 'fastctags
  :type '(repeat string))

(defcustom fastctags-stop-auto-update-tags nil
  "If t, tags will not be updated automatically."
  :group 'fastctags
  :type 'boolean)

(defcustom fastctags-use-git-grep-p t
  "Use git grep as grep program if current project is under git control."
  :group 'fastctags
  :type 'boolean)

(defcustom fastctags-use-ripgrep-force nil
  "Force use ripgrep as grep program.
If rg is not in $PATH, then it need be defined in `fastctags-grep-program'."
  :group 'fastctags
  :type 'boolean)

(defcustom fastctags-ripgrep-default-options
  ;; @see https://github.com/BurntSushi/ripgrep/issues/501
  ;; some shell will expand "/" to a complete file path.
  ;; so try to avoid "/" in shell
  (format "-n -M 1024 --no-heading --color never -s %s"
          (if (eq system-type 'windows-nt) "--path-separator \"\x2f\"" ""))
  "Default options passed to ripgrep command line program."
  :group 'fastctags
  :type 'boolean)

(defcustom fastctags-grep-extra-arguments ""
  "Extra arguments passed to grep program."
  :group 'fastctags
  :type 'string)

(defcustom fastctags-convert-grep-keyword #'identity
  "Convert keyword to grep to new regex to feed into grep program."
  :group 'fastctags
  :type 'function)

(defcustom fastctags-fallback-grep-function #'fastctags-grep
  "The fallback grep function if tag can't be found at first.
Hope grep can find something.

Below parameters is passed to the function.
The parameter \"keyword\" is the search keyword.
The parameter \"hint\" is the hint for grep ui.
The parameter \"root\" is the project root directory."
  :group 'fastctags
  :type 'function)

(defcustom fastctags-can-skip-project-root nil
  "If t, scanning project root is optional."
  :group 'fastctags
  :type 'boolean)

(defcustom fastctags-nav-find-tag-name-function
  #'fastctags-nav-find-tag-name-default
  "The function to use to find tag name at point.
It's function that takes no arguments and returns an string.
If it returns nil, the `find-tag-default' is used."
  :group 'fastctags
  :type 'function)

(defcustom fastctags-nav-format-candidate-function
  #'fastctags-nav-format-candidate-default
  "Format code navigation candidate for display.
It's function that takes one candidate and return a string.
The candidate is like,

  (list :file  \"my/relative/path\"
        :fullpath \"my/full/path\"
        :excmd \"excmd\"
        :text \"text\"
        :rank 0
        :kind \"f\"
        :tagname \"tagname\")"
  :group 'fastctags
  :type 'function)

(defcustom fastctags-major-modes-to-strip-default-tag-name
  '(org-mode
    markdown-mode)
  "Major mode where default tag name need be stripped.
It's used by `fastctags-nav-find-tag-name-default'."
  :group 'fastctags
  :type '(repeat sexp))

(defcustom fastctags-ignore-directories
  '(;; VCS
    ".git"
    ".svn"
    ".cvs"
    ".bzr"
    ".hg"
    ;; project misc
    "bin"
    "dist"
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
  :group 'fastctags
  :type '(repeat string))

(defcustom fastctags-ignore-filenames
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
  :group 'fastctags
  :type '(repeat string))

(defcustom fastctags-project-file '("tags" ".svn" ".git")
  "The file/directory used to locate project root directory.
You can set up it in \".dir-locals.el\"."
  :group 'fastctags
  :type '(repeat string))

(defcustom fastctags-project-root nil
  "Project root directory.  The directory automatically detects if it's nil."
  :group 'fastctags
  :type 'string)

(defcustom fastctags-tags-file-name "tags"
  "Tags file name."
  :group 'fastctags
  :type 'string)

(defcustom fastctags-candidates-optimize-limit 1024
  "Sort candidates if its size is less than this variable's value.
Candidates whose file path has Levenshtein distance to current file/directory.
You may set it to nil to disable re-ordering for performance reason.
If `string-distance' exists, sorting happens and this variable is ignored."
  :group 'fastctags
  :type 'integer)

(defcustom fastctags-sort-grep-result-p t
  "Sort grep result by string distance."
  :group 'fastctags
  :type 'boolean)

(defcustom fastctags-after-update-tags-hook nil
  "Hook after tags file is actually updated.
The parameter of hook is full path of the tags file."
  :group 'fastctags
  :type 'hook)

(defcustom fastctags-ctags-program "ctags"
  "Ctags Program.  You can set it to the full path of the executable."
  :group 'fastctags
  :type 'string)

(defcustom fastctags-grep-program "grep"
  "Grep program.  Program is automatically detected if it's nil.
You can set it to the full path of the executable."
  :group 'fastctags
  :type 'string)

(defcustom fastctags-quiet-when-updating-tags t
  "Be quiet when updating tags."
  :group 'fastctags
  :type 'boolean)

(defcustom fastctags-update-tags-backend
  #'fastctags-scan-dir-internal
  "A user-defined function to update tags file during auto-updating.
The function has same parameters as `fastctags-scan-dir-internal'."
  :group 'fastctags
  :type 'sexp)

(defconst fastctags-no-project-msg
  "No project found.  You can create tags file using `fastctags-scan-code'.
So we don't need the project root at all.
Or you can set up `fastctags-project-root'."
  "Message to display when no project is found.")


;; Timer to run auto-update tags file
(defvar fastctags-timer nil "Internal timer.")

(defvar fastctags-keyword nil "The keyword to grep.")

(defvar fastctags-opts-cache '() "Grep CLI options cache.")

(defvar fastctags-nav-tag-history nil "History of tag names.")

(defvar fastctags-tags-file-history nil
  "Tags files history.  Recently accessed file is at the top of history.
The file is also used by tags file auto-update process.")

(defvar fastctags-nav-find-tag-candidates nil "Find tag candidate.")

(defvar fastctags-last-tagname-at-point nil
  "Last tagname queried at point.")

(defun fastctags-in-string-or-comment ()
  "Return non-nil if point is within a string or comment."
  (let ((ppss (syntax-ppss)))
    (or (car (setq ppss (nthcdr 3 ppss)))
        (car (setq ppss (cdr ppss)))
        (nth 3 ppss))))

(defun fastctags-find-tags-file ()
  "Find tags file."
  (let* ((file-name fastctags-tags-file-name)
         (file-names (if (stringp file-name) (list file-name) file-name))
         file)
    (when (cl-find-if (lambda (fn)
                        (setq file (expand-file-name
                                    fn
                                    (locate-dominating-file (or buffer-file-name
                                                                default-directory)
                                                            fn)))
                        (and file (file-regular-p file)))
                      file-names)
      file)))

(defun fastctags-current-tags-file ()
  "Find tags file per current buffer."
  (or fastctags-cached-current-tags-file
      (setq fastctags-cached-current-tags-file
            (fastctags-find-tags-file))))

(defun fastctags-char-in-string-p (character string)
  "Test if CHARACTER is in STRING."
  (let (rlt (i 0) (len (length string)))
    (while (and (not rlt) (< i len))
      (setq rlt (eq (elt string i) character))
      (setq i (1+ i)))
    rlt))

(defun fastctags-tag-name-character-p (character)
  "Test if CHARACTER is in `fastctags-tag-name-valid-characters'."
  (fastctags-char-in-string-p character
                              fastctags-tag-name-valid-characters))

(defmacro fastctags-complete-candidates-by-character (character dict)
  "Get value of CHARACTER in DICT hash table."
  `(gethash ,character ,dict))

(defun fastctags-n-items (n items)
  "Return first N items of ITEMS."
  (cond
   ((<= (length items) n)
    items)
   (t
    (let (rlt (i 0))
      (while (< i n)
        (push (nth i items) rlt)
        (setq i (1+ i)))
      (push " ..." rlt)
      (nreverse rlt)))))

(defun fastctags-truncate-string (str n)
  "Truncate STR to N characters."
  (setq str (string-trim str))
  (if (<= (length str) n)
      str
    (concat (substring str 0 n) "...")))

;;;###autoload
(defun fastctags-debug-info ()
  "Print all debug information."
  (interactive)
  (let* ((caches fastctags-tags-file-cache)
         (keys (hash-table-keys caches)))
    (message "* cache contents")
    (dolist (k keys)
      (let* ((h (gethash k caches))
             (dict (plist-get h :tagname-dict))
             (dict-keys (hash-table-keys dict)))
        (message "** key=%s timestamp=%s filesize=%s\n"
                 k
                 (plist-get h :timestamp)
                 (plist-get h :filesize))
        (message "** raw-content:\n%s\n" (fastctags-truncate-string (plist-get h :raw-content) 10000))
        (message "** diff-output:\n%s\n" (plist-get h :diff-output))
        (message "** code complete dict:\n")
        (dolist (dk dict-keys)
          (when k
            (let* ((items (gethash dk dict)))
              (when (> (length items) 0)
                (message "  %s[%s]: %s"
                         (string dk)
                         (length items)
                         (fastctags-n-items 4 items))))))))))

(defun fastctags-init-tagname-dict ()
  "Initialize tagname dict."
  (let* ((i 0)
         (dict (make-hash-table))
         (len (length fastctags-tag-name-valid-characters)))
    (while (< i len)
      (puthash (elt fastctags-tag-name-valid-characters i) '() dict)
      (setq i (1+ i)))
    dict))

(defun fastctags-complete-parse-tags (text &optional dict)
  "Extract tag names from TEXT of tags file.
DICT is the existing lookup dictionary contains tag names.
If it's nil, return a dictionary, or else return the existing dictionary."
  (let* ((start 0)
         (vim-regex "^\\([^!\f\t\n\r()=,; ]+\\)\t\\(.+\\)$")
         (case-fold-search fastctags-complete-ignore-case-p)
         tagname
         c)

    (when fastctags-debug (message "fastctags-complete-parse-tags called"))
    (unless dict (setq dict (fastctags-init-tagname-dict)))

    ;; Code inside the loop should be optimized.
    ;; Please avoid calling lisp function inside the loop.
    ;; tags file is in vim format
    (while (string-match vim-regex text start)
      (setq tagname (substring text (match-beginning 1) (match-end 1)))
      (setq c (elt tagname 0))
      (when (fastctags-tag-name-character-p c)
        ;; latest tag name is at the beginning
        (push tagname (fastctags-complete-candidates-by-character c dict)))
      (setq start (match-end 2)))

    dict))

(defun fastctags-all-completions (string collection)
  "Search  match to STRING in COLLECTION to see if it begins with STRING."
  (let ((case-fold-search fastctags-complete-ignore-case-p))
    (all-completions string collection)))

(defun fastctags-fetch-by-first-char (c prefix tagname-dict)
  "Fetch candidates by first character C of PREFIX from TAGNAME-DICT."
  (let* ((rlt (fastctags-all-completions prefix (fastctags-complete-candidates-by-character c tagname-dict))))
    (when fastctags-complete-ignore-case-p
      (let (c2 (offset (- ?a ?A)))
        (cond
         ((fastctags-char-in-string-p c "abcdefghijklmnopqrstuvwxyz")
          (setq c2 (- c offset)))

         ((fastctags-char-in-string-p c "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
          (setq c2 (+ c offset))))

        (when c2
          (setq rlt (nconc rlt
                           (fastctags-all-completions prefix
                                                      (fastctags-complete-candidates-by-character c2
                                                                                                  tagname-dict)))))))
    rlt))

(defun fastctags-clean-diff-output (diff-output)
  "Clean DIFF-OUTPUT.  Only keep the lines start with '<'."
  (setq diff-output (replace-regexp-in-string "^[^<].*$" "" diff-output))
  (setq diff-output (replace-regexp-in-string "^\\(\n\\|< \\)" "" diff-output))
  diff-output)

(defun fastctags-get-tags-file-info (tags-file)
  "Get the info of TAGS-FILE from cache."
  (and fastctags-tags-file-cache
       tags-file
       (gethash tags-file fastctags-tags-file-cache)))

(defun fastctags-read-file (file)
  "Read content of FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (buffer-string)))

(defmacro fastctags-put (key value dictionary)
  "Add KEY VALUE pair into DICTIONARY."
  `(setq ,dictionary (plist-put ,dictionary ,key ,value)))

(defun fastctags-load-tags-file (file static-p &optional force no-diff-prog)
  "Load tags from FILE.  Tags file generated by Emacs and Vim is supported.
If STATIC-P is t, the corresponding tags file is read only once.
If FORCE is t, tags file is read without `fastctags-tags-file-cache'.
If NO-DIFF-PROG is t, do NOT use diff on tags file.
This function return t if FILE is reloaded."
  (let* (raw-content
         (file-info (fastctags-get-tags-file-info file))
         (use-diff-maybe (and (not no-diff-prog)
                              file-info
                              (plist-get file-info :raw-content)
                              (executable-find diff-command)))
         tagname-dict
         diff-output
         (real-tags-file-size (or (file-attribute-size (file-attributes file)) 0))
         reloaded)

    (when fastctags-debug
      (message "fastctags-load-tags-file: file=%s use-diff-maybe=%s force=%s no-file-info=%s"
               file
               use-diff-maybe
               force
               (not file-info)))

    (when (or force
              (not file-info)
              (and
               ;; the tags file is static and is already read into cache
               ;; so don't read it again
               ;; time to expire cache from tags file
               (> (- (float-time (current-time)) (plist-get file-info :timestamp))
                  fastctags-update-tags-file-interval)
               ;; When generating new tags file, file size could be
               ;; temporarily smaller than cached file size.
               ;; Don't reload tags file until new tags file is bigger.
               (fastctags-need-load-tags-file (plist-get file-info :filesize) real-tags-file-size)))

      ;; Read file content
      (setq reloaded t)
      (cond
       ((and use-diff-maybe
             (> real-tags-file-size fastctags-tags-file-loading-speedup-min-size))
        ;; actually don't change raw-content attached to file-info
        (setq raw-content (plist-get file-info :raw-content))

        ;; use diff to find the new tags
        (with-temp-buffer
          ;; when process finished, replace temp buffer with program output
          (call-process-region raw-content nil diff-command nil t nil "-ab" file "-")
          (setq diff-output (fastctags-clean-diff-output (buffer-string))))
        ;; compare old and new tags file, extract tag names from diff output which
        ;; should be merged with old tag names
        (setq tagname-dict
              (fastctags-complete-parse-tags diff-output
                                             (plist-get file-info :tagname-dict))))
       (t
        (unless fastctags-quiet (message "Please be patient when loading %s" file))
        (setq raw-content (fastctags-read-file file))
        (setq tagname-dict (fastctags-complete-parse-tags raw-content))
        (unless fastctags-quiet
          (message "%s with Vim format is loaded." file))))

      ;; initialize hash table if needed
      (unless fastctags-tags-file-cache
        (set 'fastctags-tags-file-cache (make-hash-table :test #'equal)))

      ;; finalize tags file info
      (puthash file
               ;; if the tags file is read only once, it will never be updated
               ;; by `diff-command', but raw content is still needed for code navigation
               (list :raw-content raw-content
                     :tagname-dict tagname-dict
                     :static-p static-p
                     :timestamp (float-time (current-time))
                     :diff-output diff-output
                     :filesize real-tags-file-size)
               fastctags-tags-file-cache))
    (when (and reloaded (not static-p))
      ;; invalidate cached candidates if the tags file is reloaded
      (setq fastctags-complete-cached-candidates nil))))

(defun fastctags-test-cached-candidates (prefix)
  "Test PREFIX in `fastctags-complete-cached-candidates'."
  (let* ((cands fastctags-complete-cached-candidates)
         (key (plist-get cands :key))
         (keylen (length key))
         (case-fold-search fastctags-complete-ignore-case-p))
    ;;  prefix is "hello" and cache's prefix "ell"
    (and (>= (length prefix) keylen)
         ;; key is the beginning of prefix
         (string= (substring prefix 0 keylen) key))))

(defun fastctags-complete-candidates (prefix)
  "Get code complete candidate with PREFIX."
  (when fastctags-debug
    (message "fastctags-complete-candidates called => %s" prefix))

  (when (and prefix (> (length prefix) 0))
    (let* ((completion-ignore-case fastctags-complete-ignore-case-p)
           (extra-tags-files (ff-list-replace-env-vars fastctags-extra-tags-files))
           (tags-file (fastctags-current-tags-file))
           all-tags-files
           rlt)

      ;; load tags files, maybe
      (when (and tags-file (file-exists-p tags-file))
        ;; primary tags file, not static
        (fastctags-load-tags-file tags-file nil)

        (when extra-tags-files
          (dolist (f extra-tags-files)
            (when (and f (file-exists-p f))
              ;; tags file in `fastctags-extra-tags-files' is read only once.
              ;; static tags file, read only once
              (fastctags-load-tags-file f t))))

        (cond
         ;; re-use cached candidates
         ((and fastctags-complete-cached-candidates
               (fastctags-test-cached-candidates prefix))

          (let* ((cands (plist-get fastctags-complete-cached-candidates :cands)))
            (setq rlt (fastctags-all-completions prefix cands))))

         ;; search candidates through tags files
         (t
          (setq all-tags-files (nconc (list tags-file) extra-tags-files))
          (dolist (f all-tags-files)
            (let* ((cache (gethash f fastctags-tags-file-cache))
                   (tagname-dict (plist-get cache :tagname-dict)))
              (when tagname-dict
                (setq rlt (nconc rlt (fastctags-fetch-by-first-char (elt prefix 0) prefix tagname-dict))))))

          (setq fastctags-complete-cached-candidates
                ;; clone the rlt into cache
                (list :key prefix :cands (mapcar 'identity rlt))))))

      ;; cleanup
      (if rlt (delete-dups rlt)))))

(defun fastctags-completion-table (string pred action)
  "Completion table for fastctags with STRING PRED ACTION."
  (if (eq action 'metadata)
      `(metadata (category . fastctags-complete)
                 (cycle-sort-function . identity)
                 (display-sort-function . identity))
    (let ((candidates (fastctags-complete-candidates string)))
      (complete-with-action action candidates string pred))))

;;;###autoload
(defun fastctags-completion-at-point ()
  "The native Completion At Point Function for fastctags."
  (when (or fastctags-complete-everywhere
            (not (fastctags-in-string-or-comment)))
    (let ((bnd (bounds-of-thing-at-point 'symbol)))
      (when bnd
        (list (car bnd)
              (cdr bnd)
              #'fastctags-completion-table
              :exclusive 'no)))))

;;;###autoload
(defun fastctags-guess-program (executable-name)
  "Guess path from its EXECUTABLE-NAME on Windows.
Return nil if it's not found."
  (cond
   ((file-remote-p default-directory)
    ;; Assume remote server has already added EXE into $PATH!
    executable-name)
   (t
    (if (executable-find executable-name) (executable-find executable-name)))))

;;;###autoload
(defun fastctags-version ()
  "Return version."
  (message "2.0.5"))

;;;###autoload
(defun fastctags-get-hostname ()
  "Reliable way to get current hostname.
`(getenv \"HOSTNAME\")' won't work because $HOSTNAME is NOT an
 environment variable.
`system-name' won't work because /etc/hosts could be modified"
  (with-temp-buffer
    (shell-command "hostname" t)
    (goto-char (point-max))
    (delete-char -1)
    (buffer-string)))

(defun fastctags-get-tags-file-path (dir)
  "Get full path of tags file from DIR."
  (and dir (expand-file-name (concat (file-name-as-directory dir)
                                     fastctags-tags-file-name))))

(defun fastctags-locate-tags-file ()
  "Find tags file: Search `fastctags-tags-file-history' and parent directories."
  (fastctags-get-tags-file-path (locate-dominating-file default-directory
                                                        fastctags-tags-file-name)))

(defun fastctags-tags-file-directory ()
  "Directory of tags file."
  (let* ((f (fastctags-locate-tags-file)))
    (if f (file-name-directory (expand-file-name f)))))

(defun fastctags-locate-project ()
  "Return the root of the project."
  (let* ((tags-dir (if (listp fastctags-project-file)
                       (cl-some (apply-partially 'locate-dominating-file
                                                 default-directory)
                                fastctags-project-file)
                     (locate-dominating-file default-directory
                                             fastctags-project-file)))
         (project-root (or fastctags-project-root
                           (and tags-dir (file-name-as-directory tags-dir)))))
    (or project-root
        (progn (message fastctags-no-project-msg)
               nil))))

(defun fastctags-add-tags-file-to-history (tags-file)
  "Add TAGS-FILE to the top of `fastctags-tags-file-history'."
  (let* ((file (expand-file-name tags-file)))
    (setq fastctags-tags-file-history
          (delq nil (mapcar
                     (lambda (s)
                       (unless (string= file (expand-file-name s)) s))
                     fastctags-tags-file-history)))
    (push tags-file fastctags-tags-file-history)))

;;;###autoload
(defun fastctags-async-shell-command (command tags-file)
  "Execute string COMMAND and create TAGS-FILE asynchronously."
  (let* ((proc (start-file-process "Shell" nil shell-file-name shell-command-switch command)))
    (set-process-sentinel
     proc
     `(lambda (process signal)
        (let* ((status (process-status process)))
          (when (memq status '(exit signal))
            (cond
             ((string= (substring signal 0 -1) "finished")
              (let* ((cmd (car (cdr (cdr (process-command process))))))
                (if fastctags-debug (message "`%s` executed." cmd))
                ;; If tramp exists and file is remote, clear file cache
                (when (and (fboundp 'tramp-cleanup-this-connection)
                           ,tags-file
                           (file-remote-p ,tags-file))
                  (tramp-cleanup-this-connection))
                ;; reload tags-file
                (when (and ,tags-file (file-exists-p ,tags-file))
                  (run-hook-with-args 'fastctags-after-update-tags-hook ,tags-file)
                  (message "Tags file %s was created." ,tags-file))))
             (t
              (message "Failed to create tags file. Error=%s CLI=%s"
                       signal
                       ,command)))))))))

(defun fastctags-dir-pattern (dir)
  "Trim * from DIR."
  (setq dir (replace-regexp-in-string "[*/]*\\'" "" dir))
  (setq dir (replace-regexp-in-string "\\`[*]*" "" dir))
  dir)


(defun fastctags-emacs-bin-path ()
  "Get Emacs binary path."
  (let* ((emacs-executable (file-name-directory (expand-file-name invocation-name
                                                                  invocation-directory))))
    (replace-regexp-in-string "/" "\\\\" emacs-executable)))

(defun fastctags--ctags--info (ctags-program)
  "Get CTAGS-PROGRAM information."
  (shell-command-to-string (concat ctags-program " --version")))

(defun fastctags-valid-ctags (ctags-program)
  "If CTAGS-PROGRAM is Ctags return the program.
If it's Emacs etags return nil."
  (when ctags-program
    (let* ((cmd-output (fastctags--ctags--info ctags-program)))
      (unless (string-match-p " ETAGS.README" cmd-output)
        ctags-program))))

(defun fastctags-languages (ctags-program)
  "List languages CTAGS-PROGRAM supports."
  (let* ((cmd (concat ctags-program " --list-languages")))
    (split-string (shell-command-to-string cmd) "\n")))

(defun fastctags-convert-config (config program)
  "Convert CONFIG of PROGRAM into Universal Ctags format."
  (let* ((rlt config)
         (langs (fastctags-languages program))
         ch
         regex)
    (dolist (lang langs)
      (when (not (string= "" lang))
        (setq ch (substring-no-properties lang 0 1))
        (setq regex (format "--langdef=[%s%s]%s *$"
                            ch
                            (downcase ch)
                            (substring-no-properties lang 1)))
        (setq rlt (replace-regexp-in-string regex "" rlt))))
    rlt))

(defun fastctags-ctags-ignore-config ()
  "Specify ignore configuration file (.gitignore, for example) for Ctags."
  (let* (rlt configs filename)
    (dolist (f fastctags-ignore-config-files)
      (when (file-exists-p (setq filename (expand-file-name f)))
        (push (file-local-name filename) configs)))
    (setq rlt (mapconcat (lambda (c) (format "--exclude=\"@%s\"" c)) configs " "))
    (when fastctags-debug
      (message "fastctags-ctags-ignore-config returns %s" rlt))
    rlt))

(defun fastctags-get-scan-command (ctags-program &optional code-file)
  "Create command for CTAGS-PROGRAM.
If CODE-FILE is a real file, the command scans it and output to stdout."
  (let* ((cmd ""))
    (cond
     ;; Use ctags only
     (ctags-program
      (setq cmd
            (format "%s %s %s %s %s -R %s"
                    ctags-program
                    (mapconcat (lambda (p)
                                 (format "--exclude=\"*/%s/*\" --exclude=\"%s/*\""
                                         (fastctags-dir-pattern p)
                                         (fastctags-dir-pattern p)))
                               fastctags-ignore-directories " ")
                    (mapconcat (lambda (p)
                                 (format "--exclude=\"%s\"" p))
                               fastctags-ignore-filenames " ")
                    (fastctags-ctags-ignore-config)
                    ;; print a tabular, human-readable cross reference
                    ;; --<my-lang>-kinds=f still accept all user defined regex
                    ;; so we have to filter in Emacs Lisp
                    (if code-file "-x -w" "")
                    (if code-file (format "\"%s\"" code-file) ""))))

     (t
      (message "You need install Ctags at first.  Universal Ctags is highly recommended.")))
    (when fastctags-debug
      (message "fastctags-get-scan-command called => ctags-program=%s cmd=%s"
               ctags-program cmd))
    cmd))

;;;###autoload
(defun fastctags-scan-dir-internal (src-dir)
  "Create tags file from SRC-DIR."
  (let* ((ctags-program fastctags-ctags-program)
         (default-directory src-dir)
         (cmd (fastctags-get-scan-command ctags-program))
         (tags-file (fastctags-get-tags-file-path src-dir)))
    (unless ctags-program
      (error "Please install Universal Ctags first!"))
    (when fastctags-debug
      (message "fastctags-scan-dir-internal called => src-dir=%s" src-dir)
      (message "default-directory=%s cmd=%s" default-directory cmd))
    ;; always update cli options
    (message "%s at %s" (if fastctags-debug cmd "Scan") default-directory)
    (fastctags-async-shell-command cmd tags-file)))

(defun fastctags-toggle-auto-update-tags ()
  "Stop/Start tags auto update."
  (interactive)
  (if (setq fastctags-stop-auto-update-tags
            (not fastctags-stop-auto-update-tags))
      (message "Tags is NOT automatically updated any more.")
    (message "Tags will be automatically updated.")))

(defun fastctags-scan-dir (src-dir)
  "Create tags file from SRC-DIR."
  (if fastctags-debug (message "fastctags-scan-dir called => %s" src-dir))
  (cond
   (fastctags-stop-auto-update-tags
    ;; do nothing
    )
   (t
    (funcall fastctags-update-tags-backend src-dir))))

;;;###autoload
(defun fastctags-directory-p (regex)
  "Does directory of current file match REGEX?"
  (let* ((case-fold-search nil)
         (dir (or (when buffer-file-name
                    (file-name-directory buffer-file-name))
                  ;; buffer is created in real time
                  default-directory
                  "")))
    (string-match-p regex dir)))

;;;###autoload
(defun fastctags-filename-p (regex)
  "Does current file match REGEX?"
  (let* ((case-fold-search nil)
         (file (or buffer-file-name default-directory "")))
    (string-match-p regex file)))

(defun fastctags-write-internal (content file)
  "Write CONTENT into FILE."
  (write-region content nil file))

(defun fastctags--strip-path (path strip-count)
  "Strip PATH with STRIP-COUNT."
  (let* ((i (1- (length path))))
    (while (and (> strip-count 0)
                (> i 0))
      (when (= (aref path i) ?/)
        (setq strip-count (1- strip-count)))
      (setq i (1- i)))
    (if (= 0 strip-count) (substring path (+ 1 i))
      path)))

(defun fastctags-nav-sort-candidates-maybe (cands strip-count current-file)
  "Sort CANDS by string distance.
STRIP-COUNT strips the string before calculating distance.
CURRENT-FILE is used to compare with candidate path."
  (let* ((ref (and current-file (fastctags--strip-path current-file strip-count))))
    (cond
     ;; don't sort candidates if `current-file' is nil
     ((or (not ref)
          (not fastctags-candidates-optimize-limit)
          (>= (length cands) fastctags-candidates-optimize-limit))
      cands)

     (t
      (sort cands
            `(lambda (item1 item2)
               (let* ((a (fastctags--strip-path (plist-get (cdr item1) :fullpath) ,strip-count))

                      (b (fastctags--strip-path (plist-get (cdr item2) :fullpath) ,strip-count))
                      (a-rank (plist-get (cdr item1) :rank))
                      (b-rank (plist-get (cdr item2) :rank)))
                 (cond
                  ((= a-rank b-rank)
                   (< (string-distance a ,ref t)
                      (string-distance b ,ref t)))
                  (t
                   (< a-rank b-rank))))))))))

(defun fastctags-tags-file-cache-invalidate (tags-file)
  "Invalidate the cache of TAGS-FILE."
  (let* ((file-info (fastctags-get-tags-file-info tags-file)))
    (when file-info
      (fastctags-put :raw-content nil file-info))))

(defun fastctags-cached-tags-file-size (tags-file)
  "Cached file size  using TAGS-FILE as key."
  (let* ((file-info (fastctags-get-tags-file-info tags-file)))
    (or (plist-get file-info :filesize) 0)))

(defun fastctags-nav-build-candidate (candidate)
  "Build tag CANDIDATE."
  (cons (funcall fastctags-nav-format-candidate-function candidate)
        candidate))

(defun fastctags-excmd-display-text (excmd)
  "Return human-readable text extracted from Vim ctags EXCMD."
  (cond
   ;; line number
   ((and (string-match "^[0-9]+$" excmd)
         (= (match-beginning 0) 0))
    (format "line %s" excmd))

   ;; /pattern/
   ((string-match "^/\\(.*\\)/$" excmd)
    (let ((pat (match-string 1 excmd)))
      ;; remove ^ and $ at boundaries
      (setq pat (replace-regexp-in-string "^\\^" "" pat))
      (setq pat (replace-regexp-in-string "\\$$" "" pat))
      pat))

   ;; fallback
   (t excmd)))

(defun fastctags-search-regex (tagname)
  "Return regex to match a Vim ctags line containing TAGNAME using rx."
  (rx-to-string
   `(seq line-start
         ;; Group 1: Tag Name
         (group ,(or tagname '(one-or-more (not (any "\t")))))
         "\t"
         ;; Group 2: Filename (changed to one-or-more)
         (group (one-or-more (not (any "\t"))))
         "\t"
         ;; Group 3: Ex-command (the search pattern or line number)
         (group (+? any))
         ";\""
         ;; Group 4: Kind (made optional and more flexible for trailing fields)
         (zero-or-more whitespace)
         (group (any "a-zA-Z"))
         ;; Allow for extra fields like line:42 or class:X
         (zero-or-more any)
         line-end)))

(defun fastctags-apply-excmd (excmd)
  "Jump according to Vim ctags EXCMD."
  (cond
   ;; line number
   ((and (string-match "^[0-9]+$" excmd)
         (= (match-beginning 0) 0))
    (goto-char (point-min))
    (forward-line (1- (string-to-number excmd))))

   ;; /pattern/
   ((string-match "^/\\([^/]*\\)/$" excmd)
    (let ((pat (match-string 1 excmd)))
      (goto-char (point-min))
      (search-forward (string-remove-suffix "$" (string-remove-prefix "^" pat)))))

   ;; fallback
   (t
    (goto-char (point-min))
    (re-search-forward (regexp-quote excmd) nil t))))

(defun fastctags-delete-duplicates (candidates)
  "Delete duplicated CANDIDATES."
  (let ((h (make-hash-table :test 'equal))
        rlt
        key)
    (dolist (cand candidates)
      (setq key (concat (plist-get (cdr cand) :fullpath)
                        (plist-get (cdr cand) :tagname)
                        (plist-get (cdr cand) :text)))
      (unless (gethash key h)
        (push cand rlt)
        (puthash key t h)))
    (nreverse rlt)))

(defun fastctags-nav-parse-cands (str tagname-re tagname root-dir fuzzy rank)
  "Parse string STR with TAGNAME-RE TAGNAME ROOT-DIR FUZZY RANK.
Return candidate."
  (when (> (length (string-trim (or str ""))) 0)
    (let* (cands cand)
      (with-temp-buffer
        ;; old tags file
        (insert str)
        (goto-char (point-min))
        (let* ((case-fold-search fuzzy))
          ;; normal tag search algorithm
          (while (re-search-forward tagname nil t) ; find line start with tagname
            (beginning-of-line)
            (setq cand (cond
                        ((re-search-forward tagname-re (line-end-position) t)
                         (let* ((ta (match-string-no-properties 1))
                                ;; file must be set after above variables
                                (file (match-string-no-properties 2))
                                (excmd (match-string-no-properties 3))
                                (kind (match-string-no-properties 4))
                                (text (fastctags-excmd-display-text excmd))
                                (cand (list :file file ; relative path
                                            :fullpath (if (file-name-absolute-p file) file
                                                        (concat root-dir file)) ; absolute path
                                            :excmd excmd
                                            :text text
                                            :rank rank ; smaller value is at top
                                            :kind kind
                                            :tagname ta)))
                           (fastctags-nav-build-candidate cand)))
                        (t
                         ;; need push cursor forward
                         (end-of-line)
                         nil)))

            (when (and cand
                       ;; partial match by `tagname' in fuzzy mode per `tagname-re'
                       (string-match tagname (plist-get (cdr cand) :tagname)))
              (push cand cands)))))
      (nreverse cands))))

(defun fastctags-need-load-tags-file (cached-tags-file-size real-tags-file-size)
  "Check tags file need be loaded with CACHED-TAGS-FILE-SIZE REAL-TAGS-FILE-SIZE."
  (cond
   ((and (> real-tags-file-size 0)
         (< real-tags-file-size fastctags-tags-file-loading-speedup-min-size))
    ;; ONLY when the checksum (file size) is different from the physical file size,
    ;; update cache by reading from physical file.
    ;; Not precise but acceptable algorithm.
    (/= cached-tags-file-size real-tags-file-size))
   (t
    ;; bigger tags file takes long time to generate
    ;; make sure incomplete (smaller) tags file is not loaded
    (< cached-tags-file-size real-tags-file-size))))

(defun fastctags-nav-extract-cands (tags-file tagname fuzzy)
  "In TAGS-FILE find occurrences of TAGNAME using FUZZY algorithm (maybe)."
  (let* ((root-dir (file-name-directory tags-file))
         (tagname-re (fastctags-search-regex (unless fuzzy tagname)))
         cands
         file-content
         diff-output
         file-info
         (cached-tags-file-size (fastctags-cached-tags-file-size tags-file))
         (real-tags-file-size (file-attribute-size (file-attributes tags-file))))
    (when fastctags-debug
      (message "fastctags-nav-extract-cands called. tags-file=%s" tags-file))

    (when (and tags-file
               (file-exists-p tags-file)
               (fastctags-need-load-tags-file cached-tags-file-size real-tags-file-size))
      (when fastctags-debug
        (message "Read file .... %s %s" cached-tags-file-size real-tags-file-size))
      (fastctags-load-tags-file tags-file nil))

    (setq file-info (fastctags-get-tags-file-info tags-file))

    (when fastctags-debug
      (message "fastctags-nav-extract-cands called. tags-file=%s tagname=%s" tags-file tagname))

    (when (and tags-file
               file-info
               (setq file-content (plist-get file-info :raw-content)))

      ;; diff-output could be nil
      (setq diff-output (plist-get file-info :diff-output))
      ;; Get better performance by scan from beginning to end.
      (setq cands (nconc (fastctags-nav-parse-cands diff-output tagname-re tagname root-dir fuzzy 0)
                         (fastctags-nav-parse-cands file-content tagname-re tagname root-dir fuzzy 1))))

    (setq cands (and cands (fastctags-delete-duplicates (nreverse cands))))
    cands))

(defun fastctags-nav-collect-cands (tagname fuzzy current-file &optional dir)
  "Find TAGNAME using FUZZY algorithm in CURRENT-FILE of DIR."
  (let* (rlt
         (force-tags-file (and dir
                               (file-exists-p (fastctags-get-tags-file-path dir))
                               (fastctags-get-tags-file-path dir)))
         (tags-file (or force-tags-file
                        (fastctags-locate-tags-file)))
         (cands (and tags-file (fastctags-nav-extract-cands tags-file tagname fuzzy))))

    (when fastctags-debug
      (message "fastctags-nav-collect-cands called. tags-file=%s cands=%s" tags-file cands))
    ;; current-file is used to calculated string distance.
    (setq rlt (fastctags-nav-sort-candidates-maybe cands 3 current-file))
    (when fastctags-extra-tags-files
      ;; don't sort candidate from 3rd party libraries
      (dolist (file (ff-list-replace-env-vars fastctags-extra-tags-files))
        (when fastctags-debug
          (message "load %s in %s" file fastctags-extra-tags-files))
        (when (setq cands (fastctags-nav-extract-cands file tagname fuzzy))
          ;; don't bother sorting candidates from third party tags file
          (setq rlt (nconc rlt cands)))))
    rlt))

(defun fastctags-selected-str ()
  "Get selected string.  Suppose plain text instead regex in selected text.
So we need *encode* the string."
  (when (region-active-p)
    (regexp-quote (buffer-substring-no-properties (region-beginning)
                                                  (region-end)))))

(defun fastctags-tagname-at-point ()
  "Get tag name at point."
  (setq fastctags-last-tagname-at-point
        (or (fastctags-selected-str)
            (funcall fastctags-nav-find-tag-name-function))))

;;;###autoload
(defun fastctags-push-marker-stack ()
  "Save current position."
  ;; un-select region
  (let* ((mark (point-marker)))
    (when (region-active-p) (pop-mark))
    ;; save current position into evil jump list
    ;; so user can press "C-o" to jump back
    (when (fboundp 'evil-set-jump) (evil-set-jump))
    ;; flash
    (cond
     ((fboundp 'xref-push-marker-stack)
      (xref-push-marker-stack mark))
     ((boundp 'find-tag-marker-ring)
      (ring-insert find-tag-marker-ring mark)))))

(defun fastctags-open-file-api (item dir &optional tagname)
  "Open ITEM while `default-directory' is DIR.
Focus on TAGNAME if it's not nil."
  (when fastctags-debug
    (message "fastctags-open-file-api called => %s" item))
  ;; jump
  (let* ((is-str (and (stringp item)
                      (string-match "\\`\\(.*?\\):\\([0-9]+\\):\\(.*\\)\\'"
                                    item)))
         (file (if is-str (match-string-no-properties 1 item)
                 (plist-get (cdr item) :fullpath)))
         ;; excmd could be just line number (string type)
         (excmd (if is-str (match-string-no-properties 2 item)
                  (plist-get (cdr item) :excmd)))
         ;; always calculate path relative to tags
         (default-directory dir))

    (when fastctags-debug
      (message "fastctags-open-file-api called => is-str=%s dir=%s, excmd=%s, file=%s" is-str dir excmd file))

    ;; item's format is like '~/proj1/ab.el:39: (defun hello() )'
    (fastctags-push-marker-stack)

    ;; open file, go to certain line
    (find-file file)
    (fastctags-apply-excmd excmd)

    ;; move focus to the tagname
    (beginning-of-line)
    ;; search tagname in current line might fail
    ;; maybe tags files is updated yet
    (when (and tagname
               ;; focus on the tag if possible
               (re-search-forward tagname (line-end-position) t))
      (goto-char (match-beginning 0)))

    ;; flash, Emacs v25 only API
    (xref-pulse-momentarily)))


(defun fastctags-nav-remember (cand dir)
  "Remember CAND whose `default-directory' is DIR."
  (setq fastctags-nav-tag-history
        (cl-remove-if (lambda (s)
                        (string= (car cand) (car s)))
                      fastctags-nav-tag-history))
  (let* ((v (cdr cand)))
    (fastctags-put :tags-file-directory dir v)
    (push (cons (car cand) v) fastctags-nav-tag-history)))

(defun fastctags--time-cost (start-time)
  "Show time cost since START-TIME."
  (let* ((time-passed (float-time (time-since start-time))))
    (format "%.01f second%s"
            time-passed
            (if (<= time-passed 2) "" "s"))))

(defun fastctags-find-tag-completion-table (cands)
  "Create a completion table with `fastctags-find-tag' category from CANDS."
  (lambda (string pred action)
    (if (eq action 'metadata)
        `(metadata (category . fastctags-find-tag))
      (complete-with-action action cands string pred))))

(defun fastctags-open-tag-cand (tagname cands time)
  "Find TAGNAME from CANDS.  Open tags file at TIME."
  ;; mark current point for `pop-tag-mark'
  (when fastctags-debug
    (message "fastctags-open-tag-cand called => %s %s %s" tagname cands time))
  (let* ((dir (fastctags-tags-file-directory))
         selected)
    (cond
     ((= 1 (length cands))
      ;; open the file directly
      (fastctags-nav-remember (nth 0 cands) dir)
      (fastctags-open-file-api (nth 0 cands)
                               dir
                               tagname))
     ((setq selected (completing-read (format "Find Tag (%s): "
                                              (fastctags--time-cost time))
                                      (fastctags-find-tag-completion-table cands)
                                      nil
                                      t))
      (fastctags-nav-remember (assoc selected cands) dir)
      (fastctags-open-file-api (assoc selected cands) dir tagname)))))

(defun fastctags-tags-file-must-exist ()
  "Make sure tags file does exist."
  (let* ((tags-file (fastctags-locate-tags-file))
         src-dir)
    (when (and (not tags-file)
               ;; No need to hint after user set `fastctags-extra-tags-files'
               (not fastctags-extra-tags-files)
               (not fastctags-can-skip-project-root))
      (setq src-dir (read-directory-name "Ctags will scan code at: "
                                         (fastctags-locate-project)))
      (cond
       (src-dir
        (fastctags-scan-dir src-dir)
        (setq tags-file (fastctags-get-tags-file-path src-dir)))
       (t
        (error "Can't find tags.  Please run `fastctags-scan-code'!"))))
    ;; the tags file IS touched
    (when tags-file
      (fastctags-add-tags-file-to-history tags-file))))

;;;###autoload
(defun fastctags-nav-find-tag-name-default ()
  "Find tag at point."
  (let ((tag-name (find-tag-default)))
    (when (and (memq major-mode
                     fastctags-major-modes-to-strip-default-tag-name)
               (string-match "^\\(`.*`\\|=.*=\\|~.*~\\|\".*\"\\|'.*'\\)$" tag-name))
      (setq tag-name (substring tag-name 1 (1- (length tag-name)))))
    tag-name))

(defun fastctags-nav-format-candidate-default (candidate)
  "Format code navigation CANDIDATE for display."
  (format "%s:%s:%s"
          (plist-get candidate :kind)
          (plist-get candidate :file)
          (plist-get candidate :text)))

;;;###autoload
(defun fastctags-scan-code (&optional dir)
  "Use Ctags to scan code at DIR."
  (interactive)
  (let* ((src-dir (or dir
                      (read-directory-name "Ctags will scan code at: "
                                           (or (fastctags-locate-project)
                                               default-directory)))))
    (when src-dir
      (fastctags-scan-dir src-dir))))

(defun fastctags-nav-find-tag-api (tagname fuzzy current-file)
  "Find TAGNAME using FUZZY algorithm from CURRENT-FILE."
  (let* ((time (current-time))
         (dir (fastctags-tags-file-directory))
         (current-file (and current-file (file-local-name current-file))))
    (if dir (setq dir (file-local-name dir)))
    (when fastctags-debug
      (message "fastctags-nav-find-tag-api called => tagname=%s fuzzy=%s dir%s current-file=%s"
               tagname
               fuzzy
               dir
               current-file))
    ;; Dir could be nil. User could use `fastctags-extra-tags-files' instead
    (cond
     ((and (not dir) (not fastctags-extra-tags-files))
      (message "Tags file is not ready yet."))
     ((not tagname)
      (error "Please provide a keyword to search tag"))

     ((not (setq fastctags-nav-find-tag-candidates
                 (fastctags-nav-collect-cands tagname fuzzy current-file dir)))
      ;; OK, let's try grep the whole project if no tag is found yet
      (funcall fastctags-fallback-grep-function
               tagname
               "No tag is found. "
               (fastctags-locate-project)))

     (t
      ;; open the one selected candidate
      (fastctags-open-tag-cand tagname fastctags-nav-find-tag-candidates time)))))

;;;###autoload
(defun fastctags-nav-find-tag ()
  "Find tag in two step.
Step 1, user need input regex to fuzzy and case insensitively match tag.
Any tag whose sub-string matches regex will be listed.

Step 2, user keeps filtering tags."
  (interactive)
  (fastctags-tags-file-must-exist)
  (let* ((tagname (completing-read "Regex to match tag: " nil nil nil (or (fastctags-selected-str) ""))))
    (when (and tagname (not (string= tagname "")))
      (fastctags-nav-find-tag-api tagname t buffer-file-name))))

;;;###autoload
(defun fastctags-nav-find-tag-at-point ()
  "Find tag using tagname at point.  Use `pop-tag-mark' to jump back.
Please note parsing tags file containing line with 2K characters could be slow.
That's the known issue of Emacs Lisp.  The program itself is perfectly fine."
  (interactive)
  (fastctags-tags-file-must-exist)
  (let* ((tagname (fastctags-tagname-at-point)))
    (cond
     (tagname
      (fastctags-nav-find-tag-api tagname nil buffer-file-name))
     (t
      (message "No tag at point")))))

;;;###autoload
(defun fastctags-nav-recent-tag ()
  "Find tag using tagname from `fastctags-nav-tag-history'."
  (interactive)
  (cond
   ((not fastctags-nav-tag-history)
    (message "`fastctags-nav-tag-history' is empty."))
   (t
    (let* ((dir (fastctags-tags-file-directory))
           ;; filter the recent tags from this project
           (cands (delq nil (mapcar
                             (lambda (e)
                               (when (string= dir (plist-get (cdr e) :tags-file-directory))
                                 e))
                             fastctags-nav-tag-history)))
           selected)
      (when (and cands
                 (setq selected (completing-read "Recent tag names: " cands nil t)))
        (fastctags-open-file-api (assoc selected cands) dir))))))

;;;###autoload
(defun fastctags-virtual-update-tags()
  "Scan code and create tags file again.
It's the interface used by other hooks or commands.
The tags updating might not happen."
  (interactive)
  (let* ((dir (and buffer-file-name
                   (file-name-directory buffer-file-name)))
         (tags-file (and fastctags-tags-file-history
                         (car fastctags-tags-file-history))))

    (when fastctags-debug
      (message "fastctags-virtual-update-tags called. dir=%s tags-file=%s" dir tags-file))

    (when (and dir
               tags-file
               (string-match-p (file-name-directory (expand-file-name tags-file))
                               (expand-file-name dir)))
      (cond
       ((or (not fastctags-timer)
            (> (- (float-time (current-time)) (float-time fastctags-timer))
               fastctags-update-tags-file-interval))

        ;; start timer if not started yet
        (setq fastctags-timer (current-time))

        ;; start updating
        (if fastctags-debug (message "fastctags-virtual-update-tags actually happened."))

        (let* ((tags-file (fastctags-locate-tags-file))
               dir)
          (when (and tags-file (file-exists-p tags-file))
            (setq dir (file-name-directory (expand-file-name tags-file)))
            (if fastctags-debug (message "update tags in %s" dir))
            (funcall fastctags-update-tags-backend dir))))

       (t
        ;; do nothing, can't run ctags too often
        (if fastctags-debug (message "fastctags-virtual-update-tags is actually skipped.")))))))

(defun fastctags-unquote-regex-parens (str)
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

(defun fastctags-read-keyword (hint)
  "Read keyword with HINT.
If SYMBOL-AT-POINT is nil, don't read symbol at point."
  (let* ((str (cond
               ((region-active-p)
                (fastctags-selected-str))
               (t
                (completing-read hint nil)))))
    (when str
      (cond
       ((region-active-p)
        (push str minibuffer-history)
        (setq fastctags-keyword (fastctags-unquote-regex-parens str))
        ;; de-select region
        (set-mark-command nil))
       (t
        ;; processing double quotes character
        (setq fastctags-keyword (replace-regexp-in-string "\"" "\\\\\""str))))))
  fastctags-keyword)

(defun fastctags-has-quick-grep-p ()
  "Test if ripgrep program exist."
  (or fastctags-use-ripgrep-force (fastctags-guess-program "rg")))

(defun fastctags-shell-quote (argument)
  "Quote ARGUMENT."
  (if (eq system-type 'windows-nt) argument
    (shell-quote-argument argument)))

(defun fastctags-exclude-opts (use-cache)
  "Grep CLI options.  IF USE-CACHE is t, the options is read from cache."
  (let* ((ignore-dirs (if use-cache (plist-get fastctags-opts-cache :ignore-dirs)
                        fastctags-ignore-directories))
         (ignore-file-names (if use-cache (plist-get fastctags-opts-cache :ignore-file-names)
                              fastctags-ignore-filenames)))
    ;; please note Windows DOS CLI only support double quotes
    (cond
     ((fastctags-has-quick-grep-p)
      (concat (mapconcat (lambda (e)
                           (format "-g=\"!%s/*\"" (fastctags-shell-quote e)))
                         ignore-dirs " ")
              " "
              (mapconcat (lambda (e)
                           (format "-g=\"!%s\"" (fastctags-shell-quote e)))
                         ignore-file-names " ")))
     (t
      (concat (mapconcat (lambda (e)
                           (format "--exclude-dir=\"%s\"" (fastctags-shell-quote e)))
                         ignore-dirs " ")
              " "
              (mapconcat (lambda (e)
                           (format "--exclude=\"%s\"" (fastctags-shell-quote e)))
                         ignore-file-names " "))))))

(defun fastctags-grep-cli (keyword &optional use-cache)
  "Use KEYWORD and USE-CACHE to build CLI.
Extended regex is used, like (pattern1|pattern2)."
  (cond
   ((and fastctags-use-git-grep-p (executable-find "git"))
    (format "git --no-pager grep -n --no-color -I -e \"%s\"" keyword))

   ((fastctags-has-quick-grep-p)
    ;; "--hidden" force ripgrep to search hidden files/directories, that's default
    ;; behavior of grep
    (format "\"%s\" %s %s --hidden %s \"%s\" --"
            ;; if rg is not in $PATH, then it's in `fastctags-grep-program'
            (or (fastctags-guess-program "rg") fastctags-grep-program)
            ;; (if fastctags-debug " --debug")
            fastctags-ripgrep-default-options
            fastctags-grep-extra-arguments
            (fastctags-exclude-opts use-cache)
            keyword))
   (t
    ;; use extended regex always
    (format "\"%s\" -rsnE %s %s \"%s\" *"
            (or fastctags-grep-program (fastctags-guess-program "grep"))
            fastctags-grep-extra-arguments
            (fastctags-exclude-opts use-cache)
            keyword))))

(defun fastctags-parent-directory (level directory)
  "Return LEVEL up parent directory of DIRECTORY."
  (let* ((rlt directory))
    (while (and (> level 0) (not (string= "" rlt)))
      (setq rlt (file-name-directory (directory-file-name rlt)))
      (setq level (1- level)))
    (if (string= "" rlt) (setq rlt nil))
    rlt))

(defun fastctags-dirname (directory)
  "Get DIRECTORY name without parent."
  (file-name-as-directory (file-name-base (directory-file-name directory))))

(defun fastctags-grep-completion-table (cands)
  "Create a completion table with `fastctags-grep' category from CANDS."
  (lambda (string pred action)
    (if (eq action 'metadata)
        `(metadata (category . fastctags-grep))
      (complete-with-action action cands string pred))))

;;;###autoload
(defun fastctags-grep (&optional default-keyword hint root)
  "Grep at project with best grep program (ripgrep, grep...) automatically.
Extended regex like (pattern1|pattern2) is used.
If DEFAULT-KEYWORD is not nil, it's used as grep keyword.
If HINT is not nil, it's used as grep hint.
ROOT is the directory to grep.  It's automatically detected.
If `fastctags-use-git-grep-p' is t, git grep is grep program."
  (interactive)

  (unless hint
    (setq hint (if (eq fastctags-convert-grep-keyword 'identity)
                   "Regular expression for grep: "
                 "Keyword for searching: ")))

  (let* ((text (or default-keyword (fastctags-read-keyword hint)))
         (keyword (funcall fastctags-convert-grep-keyword text))
         (default-directory (expand-file-name (or root
                                                  (fastctags-locate-project)
                                                  default-directory)))
         (time (current-time))
         (cmd (fastctags-grep-cli keyword nil))
         (cands (split-string (shell-command-to-string cmd) "[\r\n]+" t))
         (dir-summary (fastctags-dirname default-directory))
         selected)

    (when (and cands
               buffer-file-name
               fastctags-sort-grep-result-p
               fastctags-candidates-optimize-limit
               ;; string-distance is faster
               (< (length cands) fastctags-candidates-optimize-limit))
      ;; grep should not waste time on lisp version of string distance
      ;; So `string-distance' from Emacs 27 is required
      (let* ((ref (file-relative-name buffer-file-name root)))
        (setq cands
              (sort cands
                    `(lambda (a b)
                       (< (string-distance (car (split-string a ":")) ,ref t)
                          (string-distance (car (split-string b ":")) ,ref t)))))))

    (when fastctags-debug
      (message "fastctags-grep called: keyword=%s\n  root=%s\n  cmd=%s\n  cands=%s"
               keyword default-directory cmd cands))
    (fastctags-put :ignore-dirs
                   fastctags-ignore-directories
                   fastctags-opts-cache)

    (fastctags-put :ignore-file-names
                   fastctags-ignore-filenames
                   fastctags-opts-cache)

    (when (and cands
               (setq selected (completing-read (concat hint (format "Grep \"%s\" at %s (%s): "
                                                                    text
                                                                    dir-summary
                                                                    (fastctags--time-cost time)))
                                               (fastctags-grep-completion-table cands)
                                               nil
                                               t)))
      (fastctags-open-file-api selected default-directory keyword))))

;;;###autoload
(defun fastctags-grep-current-directory (&optional level)
  "Grep current directory or LEVEL up parent directory.
If `fastctags-use-git-grep-p' is t, git grep is grep program."
  (interactive "P")
  (unless level (setq level 0))
  (let* ((root (fastctags-parent-directory level default-directory)))
    (fastctags-grep nil nil root)))

;;;###autoload
(defun fastctags-update-tags-force (&optional forced-tags-file)
  "Update current tags file using default implementation.
If FORCED-TAGS-FILE is nil, the updating process might now happen."
  (interactive)
  (let* ((tags-file (or forced-tags-file
                        (fastctags-locate-tags-file))))
    (when tags-file
      ;; If code file is moved and TAGS is updated, invalidate the cache.
      (fastctags-tags-file-cache-invalidate tags-file)
      ;; scan the code now
      (fastctags-scan-dir (file-name-directory (expand-file-name tags-file)))
      (unless fastctags-quiet-when-updating-tags
        (message "%s is updated!" tags-file)))))

;;;###autoload
(defun fastctags-auto-setup ()
  "Set up `completion-at-point-functions'."
  (add-hook 'prog-mode-hook
            (lambda ()
              (add-hook 'completion-at-point-functions #'fastctags-completion-at-point nil t)
              (add-hook 'after-save-hook #'fastctags-virtual-update-tags 'append 'local)))

  ;; Don't ask before rereading the TAGS files if they have changed
  (setq tags-revert-without-query t)
  ;; Do case-sensitive tag searches
  (setq tags-case-fold-search nil) ;; t=case-insensitive, nil=case-sensitive
  ;; Don't warn when TAGS files are large
  (setq large-file-warning-threshold nil))

(provide 'fastctags)
;;; fastctags.el ends here
