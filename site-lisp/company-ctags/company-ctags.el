;;; company-ctags.el --- Fastest company-mode completion backend for ctags

;; Copyright (C) 2019 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/company-ctags
;; Version: 0.0.1
;; Keywords: convenience
;; Package-Requires: ((emacs "24.3") (company "0.9.0"))

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.


;;; Commentary:

;; This library completes code using tags file created by Ctags.
;; It uses a new algorithm optimized for ctags.  So it's much faster.
;; For example, it needs 9 seconds to load about 300M tags file which
;; is created by scanning the Linux Kernel code v5.3.1.
;; After initial loading, this library will always respond immediately
;; even when new tags file is created.
;;
;; Usage,
;;   (require 'company-ctags)
;;   (company-ctags-auto-setup)
;;
;; You can also turn on `company-ctags-support-etags' to support tags
;; file created by etags.  But it will increase initial loading time.

;;; Code:

(require 'company)
(require 'cl-lib)

(defgroup company-ctags nil
  "Completion backend for ctags."
  :group 'company)

(defcustom company-ctags-use-main-table-list t
  "Always search `tags-table-list' if set.
If this is disabled, `company-ctags' will try to find the one table for each
buffer automatically."
  :type '(choice (const :tag "off" nil)
                 (const :tag "on" t)))

(defcustom company-ctags-ignore-case nil
  "Non-nil to ignore case in completion candidates."
  :type 'boolean
  :package-version '(company . "0.7.3"))

(defcustom company-ctags-support-etags nil
  "Support tags file created by etags.
If t, it increases the loading time."
  :type 'boolean)

(defcustom company-ctags-everywhere nil
  "Non-nil to offer completions in comments and strings.
Set it to t or to a list of major modes."
  :type '(choice (const :tag "Off" nil)
                 (const :tag "Any supported mode" t)
                 (repeat :tag "Some major modes"
                         (symbol :tag "Major mode")))
  :package-version '(company . "0.9.0"))

(defcustom company-ctags-check-tags-file-interval 30
  "The interval (seconds) to check tags file.
Default value is 30 seconds."
  :type 'integer)


(defcustom company-ctags-tags-file-name "TAGS"
  "The name of tags file."
  :type 'string)

(defvar company-ctags-modes
  '(prog-mode
    c-mode
    objc-mode
    c++-mode
    java-mode
    jde-mode
    pascal-mode
    perl-mode
    python-mode
    lua-mode
    web-mode))

(defvar-local company-ctags-buffer-table 'unknown)

(defvar company-ctags-tags-file-caches nil
  "The cached tags files.")

(defvar company-ctags-cached-candidates nil
  "The cached candidates searched with certain prefix.
It's like (prefix . candidates).")

(defconst company-ctags-fast-pattern
  "\177\\([^\177\001\n]+\\)\001"
  "Pattern to extract tag name created by Ctags only.")

(defconst company-ctags-slow-pattern
  "\\([^\f\t\n\r()=,; ]*\\)[\f\t\n\r()=,; ]*\177\\\(?:\\([^\n\001]+\\)\001\\)?"
  "Pattern to extract tag name created by Ctags/Etags.")

(defun company-ctags-find-table ()
  "Find tags file."
  (let* ((file (expand-file-name
                company-ctags-tags-file-name
                (locate-dominating-file (or buffer-file-name
                                            default-directory)
                                        company-ctags-tags-file-name))))
    (when (and file (file-regular-p file))
      (list file))))

(defun company-ctags-buffer-table ()
  "Find buffer table."
  (or (and company-ctags-use-main-table-list tags-table-list)
      (if (eq company-ctags-buffer-table 'unknown)
          (setq company-ctags-buffer-table (company-ctags-find-table))
        company-ctags-buffer-table)))

(defmacro company-ctags-push-tagname (tagname tagname-dict)
  "Push TAGNAME into TAGNAME-DICT."
  `(let* ((c (elt ,tagname 0)))
    (cond
     ((or (and (>= c ?a) (<= c ?z))
          (and (>= c ?A) (<= c ?Z))
          (eq c ?$)
          (eq c ?#)
          (eq c ?@)
          (eq c ?%)
          (eq c ?_)
          (eq c ?!)
          (eq c ?*)
          (eq c ?&)
          (and (>= c ?0) (<= c ?9)))
      (push ,tagname (gethash c ,tagname-dict)))
     (t
      (push ,tagname (gethash ?' ,tagname-dict))))))

(defun company-ctags-extract-tagnames (text)
  "Extract tag names from TEXT."
  (let* ((start 0)
         (tagname-dict (make-hash-table))
         (i 0))

    ;; initialize hashtable whose key is from a...z and A...Z
    (while (< i 26)
      ;; make sure the hash value is not nil
      (puthash (+ ?a i) '() tagname-dict)
      (puthash (+ ?A i) '() tagname-dict)
      (setq i (1+ i)))

    ;; initialize hashtable whose key is from 0...9
    (setq i 0)
    (while (< i 10)
      ;; make sure the hash value is not nil
      (puthash (+ ?0 i) '() tagname-dict)
      (setq i (1+ i)))
    ;; other key used as the first character of variable name
    (puthash ?$ '() tagname-dict)
    (puthash ?_ '() tagname-dict)
    (puthash ?# '() tagname-dict)
    (puthash ?& '() tagname-dict)
    (puthash ?@ '() tagname-dict)
    (puthash ?! '() tagname-dict)
    (puthash ?* '() tagname-dict)
    (puthash ?% '() tagname-dict)
    ;; rubbish bin
    (puthash ?' '() tagname-dict)

    ;; Code inside the loop should be optimized.
    ;; Please avoid calling lisp function inside the loop.
    (cond
     (company-ctags-support-etags
      ;; slow algorithm, need support both explicit and implicit tags name
      (while (string-match company-ctags-slow-pattern text start)
        (cond
         ((match-beginning 2)
          ;; There is an explicit tag name.
          (company-ctags-push-tagname (substring text (match-beginning 2) (match-end 2))
                                      tagname-dict))
         (t
          ;; No explicit tag name.  Backtrack a little,
          ;; and look for the implicit one.
          (company-ctags-push-tagname (substring text (match-beginning 1) (match-end 1))
                                      tagname-dict)))
        (setq start (+ 4 (match-end 0)))))
     (t
      ;; fast algorithm, support explicit tags name only
      (while (string-match company-ctags-fast-pattern text start)
        (company-ctags-push-tagname (substring text (match-beginning 1) (match-end 1))
                                    tagname-dict)
        (setq start (+ 4 (match-end 0))))))

    tagname-dict))

(defun company-ctags-append-new-tagname-dict (new-tagnames file-info)
  "Append NEW-TAGNAMES to FILE-INFO."
  (dolist (tagname new-tagnames)
    (company-ctags-push-tagname tagname (plist-get file-info :tagname-dict))))

(defun company-ctags-all-completions (prefix tagname-dict)
  "Search for partial match to PREFIX in TAGNAME-DICT."
  (let* ((c (elt prefix 0))
         (arr (gethash c tagname-dict (gethash ?' tagname-dict))))
    (all-completions prefix arr)))

(defun company-ctags-load-tags-file (file &optional force no-diff-prog)
  "Load tags from FILE.
If FORCE is t, tags file is read without `company-ctags-tags-file-caches'.
If NO-DIFF-PROG is t, do NOT use diff on tags file.
This function return t if any tag file is reloaded."
  (let* (raw-content
         (file-info (and company-ctags-tags-file-caches
                         (gethash file company-ctags-tags-file-caches)))
         (use-diff (and (not no-diff-prog) file-info (executable-find diff-command)))
         tagname-dict
         reloaded)
    (when (or force
              (not file-info)
              (and
               ;; time to expire cache from tags file
               (> (- (float-time (current-time))
                     (plist-get file-info :timestamp))
                  company-ctags-check-tags-file-interval)
               ;; When generating new tags file, file size could be
               ;; temporarily smaller than cached file size.
               ;; Don't reload tags file until new tags file is bigger.
               (> (nth 7 (file-attributes file))
                  (plist-get file-info :filesize))))

      ;; Read file content
      (setq reloaded t)
      (message "Loading %s ..." file)
      (cond
       (use-diff
        ;; actually don't change raw-content attached to file-info
        (setq raw-content (plist-get file-info :raw-content))

        ;; use diff to find the new tags
        (let* ((tmp-file (make-temp-file "company-ctags-diff"))
               (cmd (format "%s -ab %s %s" diff-command tmp-file file)))
          ;; create old tags file
          (with-temp-buffer
            (insert (plist-get file-info :raw-content))
            (write-region (point-min) (point-max) tmp-file nil :silent))
          ;; compare old and new tags file, extract tag names from diff output which
          ;; should be merged with old tag names
          (setq tagname-dict (company-ctags-append-new-tagname-dict (company-ctags-extract-tagnames (shell-command-to-string cmd))
                                                      file-info))
          ;; clean up
          (delete-file tmp-file)))
       (t
        (setq raw-content (with-temp-buffer
                            (insert-file-contents file)
                            (buffer-string)))
        ;; collect all tag names
        (setq tagname-dict (company-ctags-extract-tagnames raw-content))))

      ;; initialize hash table if needed
      (unless company-ctags-tags-file-caches
        (set 'company-ctags-tags-file-caches (make-hash-table :test #'equal)))

      ;; finalize tags file info
      (puthash file
               (list :raw-content raw-content
                     :tagname-dict tagname-dict
                     :timestamp (float-time (current-time))
                     :filesize (nth 7 (file-attributes file)))
               company-ctags-tags-file-caches)
      (message "%s is loaded." file))
    reloaded))

(defun company-ctags--candidates (prefix)
  "Get candidate with PREFIX."
  (when (and prefix (> (length prefix) 0))
    (let* ((file (and tags-file-name (file-truename tags-file-name)))
           (completion-ignore-case company-ctags-ignore-case)
           (all-tags-files (mapcar (lambda (f)
                                     (file-truename f))
                                   (delete-dups (append (if file (list file))
                                                        (company-ctags-buffer-table)))))
           rlt)

      ;; load tags files, maybe
      (dolist (f all-tags-files)
        (when (and f (file-exists-p f))
          (when (company-ctags-load-tags-file f)
            ;; clear cached candidates if any tags file is reloaded
            (setq company-ctags-cached-candidates nil))))

      (cond
       ;; re-use cached candidates
       ((and company-ctags-cached-candidates
             (>= (length prefix) (length (car company-ctags-cached-candidates)))
             (string= (substring prefix 0 (length (car company-ctags-cached-candidates)))
                      (car company-ctags-cached-candidates)))
        (setq rlt (all-completions prefix (cdr company-ctags-cached-candidates))))

       ;; search candidates through tags files
       (t
        (dolist (f all-tags-files)
          (let* ((cache (gethash f company-ctags-tags-file-caches))
                 (tagname-dict (plist-get cache :tagname-dict)))
            (when tagname-dict
              (setq rlt (append rlt (company-ctags-all-completions prefix tagname-dict))))))
        (setq company-ctags-cached-candidates (cons prefix rlt))))

      ;; cleanup
      (if rlt (delete-dups rlt)))))

;;;###autoload
(defun company-ctags (command &optional arg &rest ignored)
  "Completion backend of for ctags.
Execute COMMAND with ARG and IGNORED."
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-ctags))
    (prefix (and (apply #'derived-mode-p company-ctags-modes)
                 (or (eq t company-ctags-everywhere)
                     (apply #'derived-mode-p company-ctags-everywhere)
                     (not (company-in-string-or-comment)))
                 (company-ctags-buffer-table)
                 (or (company-grab-symbol) 'stop)))
    (candidates (company-ctags--candidates arg))
    (location (let ((tags-table-list (company-ctags-buffer-table)))
                (when (fboundp 'find-tag-noselect)
                  (save-excursion
                    (let ((buffer (find-tag-noselect arg)))
                      (cons buffer (with-current-buffer buffer (point))))))))
    (ignore-case company-ctags-ignore-case)))

;;;###autoload
(defun company-ctags-replace-backend (backends)
  "Replace `company-etags' with `company-ctags' in BACKENDS."
  (let* (rlt)
    (dolist (b company-backends)
      (cond
       ((eq b 'company-etags)
        (push 'company-ctags rlt))
       ((listp b)
        (let* (children)
          (dolist (c b)
            (cond
             ((eq c 'company-etags)
              (push 'company-ctags children))
             (t
              (push c children))))
          (push (nreverse children) rlt)))
       (t
        (push b rlt))))
    (nreverse rlt)))

;;;###autoload
(defun company-ctags-auto-setup ()
  "Set up `company-backends'."
  (setq company-backends
        (company-ctags-replace-backend company-backends)))

(provide 'company-ctags)
;;; company-ctags.el ends here
