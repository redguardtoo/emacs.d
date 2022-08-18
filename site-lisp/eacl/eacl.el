;;; eacl.el --- Auto-complete lines by grepping project

;; Copyright (C) 2017-2021 Chen Bin
;;
;; Version: 2.2.0

;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: http://github.com/redguardtoo/eacl
;; Package-Requires: ((emacs "25.1"))
;; Keywords: abbrev, convenience, matching

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; Multiple commands are provided to grep files in the project to get
;; auto complete candidates.
;;
;; The keyword to grep is text from the line beginning to current cursor.
;;
;; Project is *automatically* detected if Git/Mercurial/Subversion is used.
;; You can override the project root by setting `eacl-project-root',
;;
;; List of commands,
;;
;; `eacl-complete-line' completes single line by grepping the project root.
;; Line candidates are extracted from the files in the project root.
;; "C-u M-x eacl-complete-line" completes single line from deleted code
;; if current project is tracked by Git.
;;
;; `eacl-complete-multiline' completes multiline code or html tag.
;;
;; `eacl-complete-line-from-buffer' completes single line by searching text
;; in the buffers.  Set `eacl-ignore-buffers' and `eacl-include-buffers' to specify
;; ignored&included buffers.
;;
;; `eacl-complete-line-from-buffer-or-project' completes one line by grepping
;; the project root when editing a physical file.  Or else, it completes one line
;; by search all buffers.
;;
;; Modify `grep-find-ignored-directories' and `grep-find-ignored-files'
;; to setup directories and files grep should ignore:
;;   (with-eval-after-load 'grep
;;      (dolist (v '("node_modules"
;;                   "bower_components"
;;                   ".sass_cache"
;;                   ".cache"
;;                   ".npm"))
;;        (add-to-list 'grep-find-ignored-directories v))
;;      (dolist (v '("*.min.js"
;;                   "*.bundle.js"
;;                   "*.min.css"
;;                   "*.json"
;;                   "*.log"))
;;        (add-to-list 'grep-find-ignored-files v)))
;;
;; Or you can setup above ignore options in ".dir-locals.el".
;; The content of ".dir-locals.el":
;;   ((nil . ((eval . (progn
;;                      (dolist (v '("node_modules"
;;                                   "bower_components"
;;                                   ".sass_cache"
;;                                   ".cache"
;;                                   ".npm"))
;;                        (add-to-list 'grep-find-ignored-directories v))
;;                      (dolist (v '("*.min.js"
;;                                   "*.bundle.js"
;;                                   "*.min.css"
;;                                   "*.json"
;;                                   "*.log"))
;;                        (add-to-list 'grep-find-ignored-files v)))))))
;;
;; "git grep" is automatically used for grepping in git repository.
;; Please note "git grep" does NOT use `grep-find-ignored-directories' OR
;; `grep-find-ignored-files'.
;;
;; The command line program of grep and git need be added into environment variable
;; "PATH".  Or else you need set `eacl-grep-program' and `eacl-git-program' to
;; specify their path.
;;
;; Set `eacl-git-grep-untracked' if untracked files should be git grepped too.
;;

;;; Code:
(require 'grep)
(require 'cl-lib)
(require 'subr-x)
(require 'comint)

(defgroup eacl nil
  "Emacs auto-complete line(s) by grepping project."
  :group 'tools)

(defcustom eacl-grep-program "grep"
  "The path of GNU Grep command line program."
  :type 'string
  :group 'eacl)

(defcustom eacl-git-program "git"
  "The path of Git command line program."
  :type 'string
  :group 'eacl)

(defcustom eacl-git-grep-untracked t
  "Search text in untracked files in Git repository."
  :type 'boolean
  :group 'eacl)

(defcustom eacl-project-root nil
  "The project root.  If it's nil project root is detected automatically."
  :type 'string
  :group 'eacl)

(defcustom eacl-project-file '(".svn" ".hg" ".git")
  "The file/directory used to locate project root."
  :type '(repeat sexp)
  :group 'eacl)

(defcustom eacl-project-root-callback 'eacl-get-project-root
  "The callback to get project root directory.
The callback is expected to return the path of project root."
  :type 'function
  :group 'eacl)

(defcustom eacl-ignore-buffers
  '("^ *\\*.*\\*$"
    dired-mode)
  "A list specifying which buffers not to search (if not current).
Can contain both regexps matching buffer names (as strings) and major modes
\(as atoms).
Please note `eacl-include-buffers' has higher priority than this variable."
  :type '(repeat (choice regexp (symbol :tag "Major Mode")))
  :group 'eacl)

(defcustom eacl-include-buffers
  '("^\\*shell\\*$")
  "A list specifying which buffers to search (if not current).
Can contain regexps matching buffer names (as strings).
Please note `eacl-ignore-buffers' has lower priority than this variable."
  :type '(repeat regexp)
  :group 'eacl)

(defcustom eacl-search-buffer-max-size
  (* 16 1024 1024)
  "Only search buffer whose size is not greater than this number."
  :type 'number
  :group 'eacl)

(defcustom eacl-use-git-grep-p nil
  "Use git grep even current file is not tracked by Git."
  :type 'boolean
  :group 'eacl)

(defvar eacl-keyword-start nil
  "The start position of multiline keyword.  Internal variable.")

(defvar eacl-debug nil
  "Enable debug mode.  Internal variable.")

(defvar projectile-project-root) ;; avoid compiling error

(defalias 'eacl-complete-statement 'eacl-complete-multiline)
(defalias 'eacl-complete-snippet 'eacl-complete-multiline)
(defalias 'eacl-complete-tag 'eacl-complete-multiline)

;; {{ make linter happy
(defvar evil-state)
;; }}

(defun eacl-relative-path ()
  "Relative path of current file."
  (let* ((p (if buffer-file-truename buffer-file-truename "")))
    (file-relative-name p (eacl-get-project-root))))

;;;###autoload
(defun eacl-get-project-root ()
  "Get project root."
  (or eacl-project-root
      ;; use projectile to find project root
      (and (fboundp 'projectile-project-root)
           (unless (featurep 'projectile) (require 'projectile))
           (funcall 'projectile-project-root))
      ;; use find-file-in-project to find project root
      (and (fboundp 'ffip-project-root) (ffip-project-root))
      ;; find project root manually
      (cl-some (apply-partially 'locate-dominating-file
                                default-directory)
               eacl-project-file)))

;;;###autoload
(defun eacl-current-line-info ()
  "Current line."
  (let* ((b (line-beginning-position))
         (e (line-end-position)))
    (cons (buffer-substring-no-properties b (point))
          (buffer-substring-no-properties b e))))

(defun eacl-current-line-text ()
  "Current line text."
  (buffer-substring-no-properties (line-beginning-position) (line-end-position)))

(defmacro eacl-process-space-in-regex (regex)
  "Space character in REGEX is converted to pattern to match any string."
  `(replace-regexp-in-string "[\t ]+" ".*" ,regex))

(defun eacl-encode(str)
  "Encode STR."
  (setq str (regexp-quote str))
  ;; 1, Be generic about quotes. Most script languages could use either double quotes
  ;; or single quote to wrap string.
  ;; In this case, we don't care, we just want to get mores candidates for
  ;; code completion.
  ;; For example, in javascript, `import { Button } from "react-bootstrap"` and
  ;; `import { Button } from 'react-bootstrap';` are same.
  ;; 2, white spaces match any string (see `eacl-shell-quote-argument')
  (replace-regexp-in-string "'\\|\"" "." str))

(defun eacl-shell-quote-argument (argument)
  "Try `shell-quote-argument' ARGUMENT and process special characters."
  (cond
   ((eq system-type 'ms-dos)
    (shell-quote-argument argument))
   ((equal argument "")
    "''")
   (t
    ;; We only use GNU Grep from Cygwin/MSYS2 even on Windows.
    ;; So we can safely assume the Linux Shell is available.
    ;; Below code is copied from `shell-quote-argument'. []
    (replace-regexp-in-string
     "\\\\\]" "]"
     (replace-regexp-in-string
      "[^-0-9a-zA-Z<>{}\[:_./\n()*]" "\\\\\\&"
      (eacl-process-space-in-regex argument))))))

(defun eacl-grep-exclude-opts ()
  "Create grep exclude options."
  (concat (mapconcat (lambda (e) (format "--exclude-dir='%s'" e))
                     grep-find-ignored-directories " ")
          " "
          (mapconcat (lambda (e) (format "--exclude='%s'" e))
                     grep-find-ignored-files " ")))

;;;###autoload
(defun eacl-get-keyword (line &optional space-p)
  "Get trimmed keyword from LINE.
If SPACE-P is t, space characters are converted to pattern matching any string."
  (let ((keyword (eacl-encode (string-trim line))))
    (if space-p (eacl-process-space-in-regex keyword)
      keyword)))

(defun eacl-replace-text (content end)
  "Delete current line and insert CONTENT.
Original text from END is preserved."
  (delete-region eacl-keyword-start end)
  (insert content))

(defun eacl-clean-summary (s)
  "Clean candidate summary S."
  (string-trim-left (replace-regexp-in-string "[ \t]*[\n\r]+[ \t]*" "\\\\n" s)))

(defun eacl-multiline-candidate-summary (s)
  "If S is too wide to fit into the screen, return pair summary and S."
  (let* ((w (frame-width))
         (key (eacl-clean-summary s))
         (len (length key))
         (tw (- w 4)))
    ;; fit to the minibuffer width by remove trailing characters
    (cond
     ((<= len w)) ; do nothing

     ((< len (+ w (/ w 8)))
      ;; strip candidate end
      (setq key (concat (substring key 0 tw) "...")))

     (eacl-keyword-start
      ;; strip candidate beginning (text we already inserted)
      (let* ((from (- (point) eacl-keyword-start))
             (to (min (+ from tw)
                      (- len from))))
        ;; a corner case to cover
        (when (>= from to)
          (setq from (- len tw))
          (setq to len))
        (if eacl-debug (message "from=%s w=%s len=%s tw=%s" from w len tw))
        (setq key (concat "..." (substring key from to))))))
    (cons key s)))

(defun eacl-get-candidates (cmd sep keyword &optional deleted-p)
  "Create candidates by running CMD.  Use SEP to split output into lines.
Candidates same as KEYWORD in current file is excluded.
If DELETED-P is t and git grep is used, grep only from deleted code."
  (when eacl-debug
    (message "eacl-get-candidates called. cmd=%s deleted-p=%s" cmd deleted-p))

  (let* ((cands (split-string (shell-command-to-string cmd) sep t "[ \t\r\n]+"))
         (str (format "%s:1:%s" (eacl-relative-path) keyword))
         rlt)

    ;; the candidate match pattern "^-" if delete-p is t
    (when deleted-p
      (setq cands (mapcar (lambda (cand) (replace-regexp-in-string "^-" "" cand)) cands)))

    (setq rlt (cl-remove-if `(lambda (e) (string= ,str e)) cands))
    (when eacl-debug (message "cands=%s" cands))
    cands))

(defun eacl-clean-candidates (cands)
  "Remove duplicated lines from CANDS."
  (delq nil (delete-dups cands)))

(defun eacl-git-p ()
  "Return non-nil if current file is in a git repository."
  (let ((path (buffer-file-name)))
    (or eacl-use-git-grep-p
        (and path
             (zerop (call-process eacl-git-program nil nil nil "ls-files" "--error-unmatch" path))))))

(defun eacl-search-command (search-regex multiline-p &optional deleted-p)
  "Return a shell command searching for SEARCH-REGEX.
If MULTILINE-P is t, command is for multiline matching.
If DELETED-P is t and git grep is used, grep only from deleted code."
  (let* ((git-p (eacl-git-p))
         (git-grep-opts (concat "-I --no-color"
                                (if eacl-git-grep-untracked " --untracked"))))
    ;; (setq git-p nil) ; debug
    (cond

     ;; auto-complete multiple lines
     (multiline-p
      (cond
       ;; use git grep
       (git-p
        (format "%s --no-pager grep -n %s \"%s\""
                eacl-git-program
                git-grep-opts
                search-regex))

       ;; use grep
       (t
        (format "%s -rsnI %s -- \"%s\" ."
                eacl-grep-program
                (eacl-grep-exclude-opts)
                search-regex))))

     ;; auto-complete single line
     (t
      (cond
       ;; use git grep
       (git-p
        (if deleted-p (format "%s --no-pager log -p --all -G \"%s\" | %s \"^-.*%s\""
                              eacl-git-program
                              search-regex
                              eacl-grep-program search-regex)
          (format "%s --no-pager grep -h %s \"%s\""
                  eacl-git-program
                  git-grep-opts
                  search-regex)))

       ;; use grep
       (t
        (format "%s -rshI %s -- \"%s\" ."
                eacl-grep-program
                (eacl-grep-exclude-opts)
                search-regex)))))))

(defun eacl-root-directory ()
  "Get directory to grep text with N."
  (or (funcall eacl-project-root-callback) default-directory))

(defun eacl-hint (time)
  "Hint for candidates since TIME."
  (format "candidates (%.01f seconds): "
          (float-time (time-since time))))

(defun eacl-insert-text-at-point (lines &optional no-confirm-p)
  "Use one of the LINES to insert text at point.
If NO-CONFIRM-P is t and, there's only one candidate, input it immediately."
  (let* (selected
         (line-end (line-end-position)))

    (cond
     ((or (not lines) (= 0 (length lines)))
      (message "Matched line does not exist."))

     ((and no-confirm-p (= 1 (length lines)))
      ;; one candidate, just complete it now
      (eacl-replace-text (car lines) line-end))

     (t
      (when (setq selected (completing-read (eacl-hint (current-time)) lines))
        (eacl-replace-text selected line-end))))))

(defun eacl-complete-line-internal (keyword extra &optional deleted-p)
  "Complete line(s) by grepping with KEYWORD, EXTRA information.
If DELETED-P is t and git grep is used, grep only from deleted code."
  (let* ((default-directory (eacl-root-directory))
         (cmd (eacl-search-command (eacl-shell-quote-argument keyword) nil deleted-p))
         (orig-collection (eacl-get-candidates cmd "[\r\n]+" keyword deleted-p))
         (line (string-trim (cdr extra)))
         (collection (delq nil (mapcar `(lambda (s) (unless (string= s ,line) s))
                                       (eacl-clean-candidates orig-collection)))))

    (when eacl-debug
      (message "eacl-complete-line-internal called. cmd=%s" cmd))

    (eacl-insert-text-at-point collection extra)))

(defun eacl-line-beginning-position ()
  "Get line beginning position."
  (save-excursion (back-to-indentation) (point)))

(defun eacl-ensure-no-region-selected ()
  "If region is selected, delete text out of selected region."
  (when (region-active-p)
    (let* ((b (region-beginning))
           (e (region-end)))
      ;; delete text outside of selected region
      (cond
       ((or (< b (line-beginning-position))
            (< (line-end-position) e))
        (error "Please select region inside current line!"))
       (t
        (delete-region e (line-end-position))
        (delete-region (line-beginning-position) b)))

      ;; de-select region and move focus to region end
      (when (and (boundp 'evil-mode) evil-mode (eq evil-state 'visual))
        (evil-exit-visual-state)
        (evil-insert-state))
      (goto-char (line-end-position)))))

;;;###autoload
(defun eacl-complete-line (&optional deleted-p)
  "Complete line by grepping in root.
The selected region will replace current line first.
The text from line beginning to current point is used as grep keyword.
Whitespace in the keyword could match any characters.
If DELETED-P is t and current file is tracked by Git, complete from deleted code."
  (interactive "P")
  (eacl-ensure-no-region-selected)
  (let* ((cur-line-info (eacl-current-line-info))
         (cur-line (car cur-line-info))
         (eacl-keyword-start (eacl-line-beginning-position))
         (keyword (eacl-get-keyword cur-line)))

    (eacl-complete-line-internal keyword cur-line-info deleted-p)
    (setq eacl-keyword-start nil)))

(defmacro eacl-find-multiline-end (indentation)
  "Find next line with same INDENTATION."
  `(let* ((rlt (re-search-forward ,indentation (point-max) t)))
     (if rlt (line-end-position))))

(defun eacl-html-p ()
  "Is html related mode."
  (or (memq major-mode '(web-mode rjsx-mode xml-mode js2-jsx-mode))
      (derived-mode-p 'sgml-mode)))

(defun eacl-extract-matched-multiline (line linenum file &optional html-p)
  "Extract matched lines start from LINE at LINENUM in FILE.
If HTML-P is not t, current `major-mode' support html tags.
Return (cons multiline-text end-line-text) or nil."
  (when eacl-debug
    (message "eacl-extract-matched-multiline called => %s %s %s %s" line linenum file html-p))
  (let* ((beg (line-beginning-position))
         end
         rlt)
    (when (string-match "^\\([ \t]*\\)\\(.*\\)*" line)
      (let* ((case-fold-search nil)
             (leading-whitespaces (match-string 1 line))
             (pattern (concat "^" leading-whitespaces "[^ \t\r\n]"))
             end-line
             (continue t)
             line)
        (save-excursion
          (while continue
            ;; skip current line which is already processed
            (forward-line)
            (goto-char (line-beginning-position))

            (cond
             ((not (setq end (eacl-find-multiline-end pattern)))
              ;; no multiline candidate, quit
              (setq continue nil))
             (t
              (goto-char end)
              (setq line (eacl-current-line-text))
              (when (and (not (string-match "^[ \t]*[\\[{(][ \t]*$" line))
                         (not (and html-p
                                   ;; eng html tag can't be ">"
                                   (string-match "^[ \t]*>[ \t]*$" line))))
                ;; candidate found!
                (setq rlt (buffer-substring-no-properties beg end))
                (setq continue nil))))))))

    (when eacl-debug
      (message "eacl-extract-matched-multiline rlt=%s" rlt))

    rlt))

;;;###autoload
(defun eacl-complete-multiline ()
  "Complete multi-line code or html tag.
The selected region will replace current line first.
The text from line beginning to current point is used as grep keyword.
Whitespace in keyword could match any characters."
  (interactive)
  (eacl-ensure-no-region-selected)
  (let* ((orig-linenum (count-lines 1 (point)))
         (orig-file (and buffer-file-name (file-truename buffer-file-name)))
         (eacl-keyword-start (eacl-line-beginning-position))
         (keyword (eacl-get-keyword (car (eacl-current-line-info))))
         (default-directory (eacl-root-directory))
         (cmd (eacl-search-command (eacl-shell-quote-argument keyword) t))
         (time (current-time))
         (orig-collection (eacl-get-candidates cmd "[\r\n]+" keyword))
         (line-end (line-end-position))
         (html-p (eacl-html-p))
         rlt
         cached-file-name
         cached-file-content)
    (when orig-collection
      (dolist (item orig-collection)
        (when (string-match "\\`\\([^:]+\\):\\([0-9]+\\):\\([^:]+\\)\\'" item)
          (let* ((strs (split-string item ":"))
                 (file (car strs))
                 (linenum (string-to-number (nth 1 strs)))
                 (line (nth 2 strs))
                 cand)
            (when (or (not (string= file orig-file))
                      (not (= linenum orig-linenum)))
              ;; item's format is like '~/proj1/ab.el:39: (defun hello() )'
              (with-temp-buffer
                (cond
                 ((or (not (string= cached-file-name file))
                      (not cached-file-content))
                  (insert-file-contents file)
                  (setq cached-file-name file)
                  (setq cached-file-content (buffer-string)))
                 (t
                  (insert cached-file-content)))
                (goto-char (point-min))
                (forward-line (1- linenum))
                (goto-char (line-beginning-position))
                (when (setq cand (eacl-extract-matched-multiline line
                                                                 linenum
                                                                 file
                                                                 html-p))
                  (when eacl-debug (message "cand=%s" cand))
                  (add-to-list 'rlt cand)))))))
      (cond
       ((or (not rlt) (= (length rlt)  0))
        (message "No multiline match was found!"))
       ((= (length rlt) 1)
        (eacl-replace-text (car rlt) line-end))
       (t
        (let* ((cands (mapcar 'eacl-multiline-candidate-summary rlt))
               (selected (completing-read (eacl-hint time) cands)))
          (when selected
            (eacl-replace-text (cdr (assoc selected cands)) line-end))))))))

(defun eacl-extract-matched-lines (keyword buffer info)
  "Extract lines matching KEYWORD from the BUFFER with INFO of current input."
  (set-buffer buffer)
  (let* ((strip-prompt (and (get-buffer-process (current-buffer))
                            comint-prompt-regexp))
         (current-input (car info))
         (lines (split-string (buffer-string) "[\r\n]+")))

    (when strip-prompt
      (setq strip-prompt (concat strip-prompt "\\(.*\\)$"))
      ;; strip the prompt in shell buffer
      (setq lines (mapcar (lambda (l)
                            (when (string-match strip-prompt l)
                              (setq l (match-string 1 l)))
                            l)
                          lines)))

    (setq lines (cl-remove-if (lambda (l)
                                (or (not (string-match keyword l))
                                    (equal l current-input)))
                              lines))
    (setq lines (cl-remove-duplicates lines))

    lines))

(defun eacl-buffer-ignore-p (buffer)
  "Ignore the BUFFER for line candidates extraction."
  (let ((buf-name (buffer-name buffer)))
    (set-buffer buffer)
    (cl-some (lambda (e)
               (or (and (stringp e)
                        (string-match e buf-name)
                        (not (cl-some (lambda (p) (string-match p buf-name))
                                      eacl-include-buffers)))
                   (eq e major-mode)
                   (> (buffer-size buffer) eacl-search-buffer-max-size)))
             eacl-ignore-buffers)))

(defun eacl-complete-line-from-buffer ()
  "Complete one line from buffer(s).
Set `eacl-ignore-buffers' and `eacl-include-buffers' to specify ignored&included
buffers."
  (interactive)
  (let* ((original-buf (current-buffer))
         strip-prompt
         (original-buf-name (buffer-name original-buf))
         (eacl-keyword-start (eacl-line-beginning-position))
         (info (eacl-current-line-info))
         (keyword (eacl-get-keyword (car info) t))
         (all-bufs (cl-delete-if 'eacl-buffer-ignore-p (buffer-list)))
         lines
         cands)

    ;; Use current buffer to complete
    (when (eacl-buffer-ignore-p original-buf)
      (push original-buf all-bufs))

    ;; Use other buffer plus current buffer
    (dolist (buf all-bufs)
      (when (setq lines (eacl-extract-matched-lines keyword buf info))
        ;; append lines to cands
        (setq cands (nconc cands lines))))

    ;; go back to original buffer
    (set-buffer original-buf)

    ;; complete line now
    (eacl-insert-text-at-point cands)
    (setq eacl-keyword-start nil)))

(defun eacl-complete-line-from-buffer-or-project (&optional deleted-p)
  "When editing a physical file, complete one line by grepping project root.
Or else, complete one line by search all buffers.
If DELETED-P is t and git grep is used, grep only from deleted code.
You can set `eacl-ignore-buffers' and `eacl-include-buffers' to specify
ignored&included buffers.  Please note `eacl-include-buffers' has higher
priority than `eacl-ignore-buffers'."
  (interactive "P")
  (cond
   (buffer-file-name
    (eacl-complete-line deleted-p))
   (t
    (eacl-complete-line-from-buffer))))

(provide 'eacl)
;;; eacl.el ends here
