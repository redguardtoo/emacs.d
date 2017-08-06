;;; eacl.el --- Emacs auto-complete line by GNU grep

;; Copyright (C) 2017 Chen Bin
;;
;; Version: 0.0.1
;; Keywords: autocomplete line
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: http://github.com/redguardtoo/eapl
;; Package-Requires: ((counsel "0.9.1") (emacs "24.3"))

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

;; `eacl-complete-line' complete line. You could assign key binding
;; "C-x C-l" to this command.
;; `eacl-complete-statement' complete statement. Statement could be
;; multiple lines and is matched by pattern `eacl-statement-regex'.
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

(defvar eacl-grep-ignore-file-names
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
  "File names to ignore when grepping.")

(defun eacl-get-project-root ()
  "Get project root."
  (or eacl-project-root
      (cl-some (apply-partially 'locate-dominating-file
                                default-directory)
               eacl-project-file)))

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

(defun eacl-get-keyword (cur-line)
  "Get trimmed keyword from CUR-LINE."
  (let* ((keyword (replace-regexp-in-string "^[ \t]*"
                                            ""
                                            cur-line)))
    (counsel-unquote-regex-parens keyword)))

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

(defun eacl-complete-line-or-statement (complete-line)
  "Complete line or statement according to boolean flag COMPLETE-LINE."
  (let* ((default-directory (or (eacl-get-project-root) default-directory))
         (cur-line (buffer-substring-no-properties (line-beginning-position) (point)))
         (keyword (eacl-get-keyword cur-line))
         (cmd-format-opts (if complete-line "%s -rshI %s \"%s\" *"
                            "%s -rsnhPzoI %s \"%s\" *"))
         (cmd (format cmd-format-opts
                      eacl-grep-program
                      (eacl-grep-exclude-opts)
                      (if complete-line keyword (concat keyword eacl-statement-regex))))
         (leading-spaces "")
         (sep (if complete-line "[\r\n]+" "^[0-9]+:"))
         (collection (split-string (shell-command-to-string cmd) sep t "[ \t\r\n]+")))
    (when collection
      (if (string-match "^\\([ \t]*\\)" cur-line)
          (setq leading-spaces (match-string 1 cur-line)))
      (cond
       ((= 1 (length collection))
        ;; insert only candidate
        (eacl-replace-current-line leading-spaces (car collection)))
       ((> (length collection) 1)
        ;; uniq
        (setq collection (delq nil (delete-dups collection)))
        (unless complete-line
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
  (eacl-complete-line-or-statement t))

;;;###autoload
(defun eacl-complete-statement ()
  "Complete statement which end with pattern `eacl-statement-regex'.
The keyword to grep is the text from line beginning to current cursor."
  (interactive)
  (eacl-complete-line-or-statement nil))

(provide 'eacl)
;;; eacl.el ends here

