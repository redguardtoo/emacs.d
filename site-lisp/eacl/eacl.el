;;; eacl.el --- Auto-complete lines by grepping project

;; Copyright (C) 2017, 2018 Chen Bin
;;
;; Version: 2.0.3

;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: http://github.com/redguardtoo/eacl
;; Package-Requires: ((emacs "24.4") (ivy "0.9.1"))
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
;; The keyword to grep is text from line beginning to current cursor.
;; Project is *automatically* detected if Git/Mercurial/Subversion is used.
;; You can override the project root by setting `eacl-project-root',
;;
;; List of commands,
;;
;; `eacl-complete-line' complete single line.
;; `eacl-complete-multiline' completes multiline code or html tag.
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
;; `grep-find-ignored-files'. You could set `eacl-git-grep-untracked' to tell
;; git whether untracked files should be grepped in the repository.


;;; Code:
(require 'ivy nil t)
(require 'grep)
(require 'cl-lib)

(defgroup eacl nil
  "Emacs auto-complete line(s) by grepping project."
  :group 'tools)

(defcustom eacl-grep-program "grep"
  "GNU Grep program."
  :type 'string
  :group 'eacl)

(defcustom eacl-git-grep-untracked t
  "Grep untracked files in Git repository."
  :type 'boolean
  :group 'eacl)

(defcustom eacl-project-root nil
  "Project root.  If it's nil project root is detected automatically."
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

(defvar eacl-keyword-start nil
  "The start position of multiline keyword.  Internal variable.")

(defvar eacl-debug nil
  "Enable debug mode.  Internal variable.")

(defalias 'eacl-complete-statement 'eacl-complete-multiline)
(defalias 'eacl-complete-snippet 'eacl-complete-multiline)
(defalias 'eacl-complete-tag 'eacl-complete-multiline)

(defun eacl-relative-path ()
  "Relative path of current file."
  (let* ((p (if buffer-file-truename buffer-file-truename "")))
    (file-relative-name p (eacl-get-project-root))))

;;;###autoload
(defun eacl-get-project-root ()
  "Get project root."
  (or eacl-project-root
      ;; use projectile to find project root
      (and (fboundp 'projectile-find-file)
           (if (featurep 'projectile) t (require 'projectile))
           (projectile-project-root))
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

(defun eacl-trim-left (s)
  "Remove whitespace at the beginning of S."
  (if (string-match "\\`[ \t\n\r]+" s) (replace-match "" t t s) s))

(defun eacl-encode(str)
  "Encode STR."
  (setq str (regexp-quote str))
  ;; 1, Be generic about quotes. Most script languages could use either double quotes
  ;; or single quote to wrap string.
  ;; In this case, we don't care, we just want to get mores candidates for
  ;; code completion.
  ;; For example, in javascript, `import { Button } from "react-bootstrap"` and
  ;; `import { Button } from 'react-bootstrap';` are same.
  ;; 2, white spaces match any string.
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
      (replace-regexp-in-string
       "[\t ]+" ".*"
       argument))))))

(defun eacl-grep-exclude-opts ()
  "Create grep exclude options."
  (concat (mapconcat (lambda (e) (format "--exclude-dir='%s'" e))
                     grep-find-ignored-directories " ")
          " "
          (mapconcat (lambda (e) (format "--exclude='%s'" e))
                     grep-find-ignored-files " ")))

(defun eacl-trim-string (string)
  "Trim STRING."
  (replace-regexp-in-string "\\`[ \t\n]*" "" (replace-regexp-in-string "[ \t\n]*\\'" "" string)))

;;;###autoload
(defun eacl-get-keyword (line)
  "Get trimmed keyword from LINE."
  (let* ((keyword (replace-regexp-in-string "^[ \t]+\\|[ \t]+$" "" line)))
    (eacl-encode keyword)))

(defun eacl-replace-text (content end)
  "Delete current line and insert CONTENT.
Original text from END is preserved."
  (delete-region eacl-keyword-start end)
  (insert content))

(defun eacl-clean-summary (s)
  "Clean candidate summary S."
  (eacl-trim-left (replace-regexp-in-string "[ \t]*[\n\r]+[ \t]*" "\\\\n" s)))

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

(defun eacl-get-candidates (cmd sep keyword)
  "Create candidates by running CMD.
Use SEP to split output into lines.
Candidates same as KEYWORD in current file is excluded."
  (if eacl-debug (message "cmd=%s" cmd))
  (let* ((cands (split-string (shell-command-to-string cmd) sep t "[ \t\r\n]+"))
         (str (format "%s:1:%s" (eacl-relative-path) keyword))
         rlt)
    (setq rlt (cl-remove-if `(lambda (e) (string= ,str e)) cands))
    (when eacl-debug (message "cands=%s" cands))
    cands))

(defun eacl-clean-candidates (cands)
  "Remove duplicated lines from CANDS."
  (delq nil (delete-dups cands)))

(defun eacl-git-p (path)
  "Return non-nil if PATH is in a git repository."
  (zerop (call-process "git" nil nil nil "ls-files" "--error-unmatch" path)))

(defun eacl-search-command (search-regex multiline-p)
  "Return a shell command searching for SEARCH-REGEX.
If MULTILINE-P is t, command is for multiline matching."
  (let* ((git-p (and (buffer-file-name)
                     (eacl-git-p (buffer-file-name))))
         (git-grep-opts (concat "-I --no-color"
                                (if eacl-git-grep-untracked " --untracked"))))
    ;; (setq git-p nil) ; debug
    (cond
     (multiline-p
      (cond
       (git-p
        (format "git grep -n %s \"%s\"" git-grep-opts search-regex))
       (t
        (format "%s -rsnI %s -- \"%s\" ."
                eacl-grep-program
                (eacl-grep-exclude-opts)
                search-regex))))

     ;; git-grep does not support multiline searches.
     ((and (buffer-file-name) (eacl-git-p (buffer-file-name)))
      (format "git grep -h %s \"%s\"" git-grep-opts search-regex))

     (t
      (cond
       (git-p
        (format "git grep -h %s \"%s\"" git-grep-opts search-regex))
       (t
        (format "%s -rshI %s -- \"%s\" ."
                eacl-grep-program
                (eacl-grep-exclude-opts)
                search-regex)))))))

(defun eacl-complete-line-internal (keyword extra)
  "Complete line by grepping with KEYWORD.
EXTRA is optional information to filter candidates."
  (let* ((default-directory (or (funcall eacl-project-root-callback) default-directory))
         (cmd (eacl-search-command (eacl-shell-quote-argument keyword) nil))
         (orig-collection (eacl-get-candidates cmd "[\r\n]+" keyword))
         (line (eacl-trim-string (cdr extra)))
         (collection (delq nil (mapcar `(lambda (s) (unless (string= s ,line) s))
                                       (eacl-clean-candidates orig-collection))))
         (line-end (line-end-position))
         (time (current-time)))

    (if eacl-debug (message "cmd=%s" cmd))

    (cond
     ((or (not collection) (= 0 (length collection)))
      (message "No single line match was found!"))
     ((and extra (= 1 (length collection)))
      ;; one candidate, just complete it now
      (eacl-replace-text (car collection) line-end))
     (t
      (ivy-read (format "candidates (%.01f seconds):"
                        (float-time (time-since time)))
                collection
                :action `(lambda (l)
                           (if (consp l) (setq l (cdr l)))
                           (eacl-replace-text l ,line-end)))))))

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
        (error "Please select region inside current line."))
       (t
        (delete-region e (line-end-position))
        (delete-region (line-beginning-position) b)))

      ;; de-select region and move focus to region end
      (when (and (boundp 'evil-mode) (eq evil-state 'visual))
        (evil-exit-visual-state)
        (evil-insert-state))
      (goto-char (line-end-position)))))

;;;###autoload
(defun eacl-complete-line ()
  "Complete line by grepping project.
The selected region will replace current line first.
The text from line beginning to current point is used as grep keyword.
Whitespace in the keyword could match any characters."
  (eacl-ensure-no-region-selected)
  (interactive)
  (let* ((cur-line-info (eacl-current-line-info))
         (cur-line (car cur-line-info))
         (eacl-keyword-start (eacl-line-beginning-position))
         (keyword (eacl-get-keyword cur-line)))
    (eacl-complete-line-internal keyword cur-line-info)
    (setq eacl-keyword-start nil)))

(defmacro eacl-find-multiline-end (indentation)
  "Find next line with same INDENTATION."
  `(let* ((rlt (re-search-forward ,indentation (point-max) t)))
     (if rlt (line-end-position))))

(defun eacl-html-p ()
  "Is html related mode."
  (or (memq major-mode '(web-mode rjsx-mode xml-mode js2-jsx-mode))
      (derived-mode-p 'sgml-mode)))

(defmacro eacl-match-html-start-tag-p (line html-p)
  "LINE is like '>'."
  `(and ,html-p
        ;; eng html tag can't be ">"
        (string-match "^[ \t]*>[ \t]*$" ,line)))

(defmacro eacl-match-start-bracket-p (line)
  "LINE is '{'."
  `(string-match "^[ \t]*[\\[{(][ \t]*$" ,line))

(defun eacl-extract-matched-multiline (line linenum file &optional html-p)
  "Extract matched lines start from LINE at LINENUM in FILE.
If HTML-P is not t, current `major-mode' support html tags.
Return (cons multiline-text end-line-text) or nil."
  (if eacl-debug (message "eacl-extract-matched-multiline called => %s %s %s %s" line linenum file html-p))
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
              (when (and (not (eacl-match-start-bracket-p line))
                         (not (eacl-match-html-start-tag-p line html-p)))
                ;; candidate found!
                (setq rlt (buffer-substring-no-properties beg end))
                (setq continue nil))))))))
    (if eacl-debug (message "rlt=%s" rlt))
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
         (default-directory (or (funcall eacl-project-root-callback) default-directory))
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
                  (setq cached-file-content (buffer-substring-no-properties (point-min) (point-max))))
                 (t
                  (insert cached-file-content)))
                (goto-char (point-min))
                (forward-line (1- linenum))
                (goto-char (line-beginning-position))
                (when (setq cand (eacl-extract-matched-multiline line linenum file html-p))
                  (when eacl-debug (message "cand=%s" cand))
                  (add-to-list 'rlt cand)))))))
      (cond
       ((or (not rlt) (= (length rlt)  0))
        (message "No multiline match was found!"))
       ((= (length rlt) 1)
        (eacl-replace-text (car rlt) line-end))
       (t
        (ivy-read (format "candidates (%.01f seconds):"
                          (float-time (time-since time)))
                  (mapcar 'eacl-multiline-candidate-summary rlt)
                  :action `(lambda (l)
                             (if (consp l) (setq l (cdr l)))
                             (eacl-replace-text l ,line-end))))))))

(provide 'eacl)
;;; eacl.el ends here
