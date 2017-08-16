;;; eacl.el --- Emacs auto-complete line by GNU grep

;; Copyright (C) 2017 Chen Bin
;;
;; Version: 0.0.3
;; Keywords: autocomplete line
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: http://github.com/redguardtoo/eapl
;; Package-Requires: ((ivy "0.9.1") (emacs "24.3"))

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; Mutiple commands are provided to grep files in the project to get
;; Multiple commands are provided to grep files in the project to get
;; auto complete candidates.
;; The keyword to grep is the text from line beginning to current cursor.
;; Project is *automatically* detected if Git/Mercurial/Subversion is used.
;; You can override the project root by setting `eacl-project-root',
;;
;; List of commands,
;;
;; `eacl-complete-line' complete line.  You could assign key binding
;; "C-x C-l" to this command.
;;
;; `eacl-complete-statement' completes statement.  Statement could be
;; multiple lines and is matched by pattern `eacl-statement-regex'.
;; According to default value of `eacl-statement-regex'.
;; Statement ends with ";"
;;
;; `eacl-complete-snippet' completes snippets ending with "}"
;;
;; `eacl-complete-tag' completes HTML tag ending with ">"
;;
;; GNU Grep, Emacs 24.3 and counsel (https://github.com/abo-abo/swiper)
;; are required.

;;; Code:
(require 'ivy)
(require 'cl-lib)

(defgroup eacl nil
  "eacl")

(defcustom eacl-statement-regex "[^;]*;"
  "Regular expression to match the statement."
  :type 'string
  :group 'eacl)

(defcustom eacl-grep-program "grep"
  "GNU Grep program."
  :type 'string
  :group 'eacl)

(defcustom eacl-project-root nil
  "Project root.  If it's nil project root is detected automatically."
  :type 'string
  :group 'eacl)

(defcustom eacl-project-file '(".svn" ".hg" ".git")
  "The file/directory used to locate project root."
  :type '(repeat sexp)
  :group 'eacl)

(defcustom eacl-grep-ignore-dirs
  '(".git"
    ".bzr"
    ".svn"
    "bower_components"
    "node_modules"
    ".sass-cache"
    ".cache"
    "test"
    "tests"
    ".metadata"
    "logs")
  "Directories to ignore when grepping."
  :type '(repeat sexp)
  :group 'eacl)

(defcustom eacl-grep-ignore-file-exts
  '("log"
    "properties"
    "session"
    "swp")
  "File extensions to ignore when grepping."
  :type '(repeat sexp)
  :group 'eacl)

(defcustom eacl-grep-ignore-file-names
  '("TAGS"
    "tags"
    "GTAGS"
    "GPATH"
    ".bookmarks.el"
    "*.svg"
    "history"
    "#*#"
    "*.min.js"
    "*bundle*.js"
    "*vendor*.js"
    "*.min.css"
    "*~")
  "File names to ignore when grepping."
  :type '(repeat sexp)
  :group 'eacl)

;;;###autoload
(defun eacl-get-project-root ()
  "Get project root."
  (or eacl-project-root
      (cl-some (apply-partially 'locate-dominating-file
                                default-directory)
               eacl-project-file)))

;;;###autoload
(defun eacl-current-line ()
  "Current line."
  (buffer-substring-no-properties (line-beginning-position)
                                  (point)))

;;;###autoload
(defun eacl-leading-spaces (cur-line)
  "Leading space at the begining of CUR-LINE."
  (if (string-match "^\\([ \t]*\\)" cur-line)
      (match-string 1 cur-line)
    ""))

(defun eacl-grep-exclude-opts ()
  "Create grep exclude options."
  (concat (mapconcat (lambda (e) (format "--exclude-dir='%s'" e))
                     eacl-grep-ignore-dirs " ")
          " "
          (mapconcat (lambda (e) (format "--exclude='*.%s'" e))
                     eacl-grep-ignore-file-exts " ")
          " "
          (mapconcat (lambda (e) (format "--exclude='%s'" e))
                     eacl-grep-ignore-file-names " ")))

(defun eacl-unquote-regex-parens (str)
  (let ((start 0)
        ms)
    (while (setq start (string-match "\\\\)\\|\\\\(\\|[()]" str start))
      (setq ms (match-string-no-properties 0 str))
      (cond ((equal ms "\\(")
             (setq str (replace-match "(" nil t str))
             (setq start (+ start 1)))
            ((equal ms "\\)")
             (setq str (replace-match ")" nil t str))
             (setq start (+ start 1)))
            ((equal ms "(")
             (setq str (replace-match "\\(" nil t str))
             (setq start (+ start 2)))
            ((equal ms ")")
             (setq str (replace-match "\\)" nil t str))
             (setq start (+ start 2)))
            (t
             (error "unexpected"))))
    str))

;;;###autoload
(defun eacl-get-keyword (cur-line)
  "Get trimmed keyword from CUR-LINE."
  (let* ((keyword (replace-regexp-in-string "^[ \t]*"
                                            ""
                                            cur-line)))
    (eacl-unquote-regex-parens keyword)))

(defun eacl-replace-current-line (leading-spaces content)
  "Insert LEADING-SPACES and CONTENT."
  (beginning-of-line)
  (kill-line)
  (insert (concat leading-spaces content))
  (end-of-line))

(defun eacl-create-candidate-summary (s)
  "If S is too wide to fit into the screen, return pair summary and S."
  (let* ((w (frame-width))
         ;; display kill ring item in one line
         (key (replace-regexp-in-string "[ \t]*[\n\r]+[ \t]*" "\\\\n" s)))
    ;; strip the whitespace
    (setq key (replace-regexp-in-string "^[ \t]+" "" key))
    ;; fit to the minibuffer width
    (if (> (length key) w)
        (setq key (concat (substring key 0 (- w 4)) "...")))
    (cons key s)))

(defun eacl-complete-line-or-statement (regex cur-line keyword)
  "Complete line or statement according to REGEX.
CUR-LINE and KEYWORD are also required.
If REGEX is not nil, complete statement."
  (let* ((default-directory (or (eacl-get-project-root) default-directory))
         (cmd-format-opts (if regex "%s -rsnhPzoI %s \"%s\" *"
                            "%s -rshEI %s \"%s\" *"))
         (cmd (format cmd-format-opts
                      eacl-grep-program
                      (eacl-grep-exclude-opts)
                      (if regex (concat keyword regex)
                        keyword)))
         (leading-spaces (eacl-leading-spaces cur-line))
         (sep (if regex "^[0-9]+:" "[\r\n]+"))
         (collection (split-string (shell-command-to-string cmd) sep t "[ \t\r\n]+")))
    (when collection
      (setq collection (delq nil (delete-dups collection)))
      (cond
       ((= 1 (length collection))
        ;; insert only candidate
        (eacl-replace-current-line leading-spaces (car collection)))
       ((> (length collection) 1)
        ;; uniq
        (if regex
          (setq collection (mapcar 'eacl-create-candidate-summary collection)))
        (ivy-read "candidates:"
                  collection
                  :action (lambda (l)
                            (if (consp l) (setq l (cdr l)))
                            (eacl-replace-current-line leading-spaces l))))))))

;;;###autoload
(defun eacl-complete-line ()
  "Complete line by grepping in project.
The keyword to grep is the text from line beginning to current cursor."
  (interactive)
  (let* ((cur-line (eacl-current-line))
         (keyword (eacl-get-keyword cur-line)))
    (eacl-complete-line-or-statement nil cur-line keyword)))

;;;###autoload
(defun eacl-complete-statement ()
  "Complete statement which end with pattern `eacl-statement-regex'.
The keyword to grep is the text from line beginning to current cursor."
  (interactive)
  (let* ((cur-line (eacl-current-line))
         (keyword (eacl-get-keyword cur-line)))
    (eacl-complete-line-or-statement eacl-statement-regex cur-line keyword)))

;;;###autoload
(defun eacl-complete-snippet ()
  "Complete snippet which ends with \"}\".
The keyword to grep is the text from line beginning to current cursor."
  (interactive)
  (let* ((eacl-statement-regex "[^}]*}"))
    (eacl-complete-statement)))

;;;###autoload
(defun eacl-complete-tag ()
  "Complete snippet which ends with \">\".
The keyword to grep is the text from line beginning to current cursor."
  (interactive)
  (let* ((cur-line (eacl-current-line))
         (keyword (concat "<" (replace-regexp-in-string "^<" "" (eacl-get-keyword cur-line))))
         (regex "[^>]*>"))
    (eacl-complete-line-or-statement regex cur-line keyword)))

(provide 'eacl)
;;; eacl.el ends here

