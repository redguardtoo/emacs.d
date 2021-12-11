;;; company-ctags.el --- Fastest company-mode completion backend for ctags  -*- lexical-binding: t -*-

;; Copyright (C) 2019,2020 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: https://github.com/redguardtoo/company-ctags
;; Version: 0.0.7
;; Keywords: convenience
;; Package-Requires: ((emacs "25.1") (company "0.9.0"))

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
;;   Step 0, Make sure `company-mode' is already set up
;;   See http://company-mode.github.io/ for details.
;;
;;   Step 1, insert below code into your configuration,
;;
;;     (with-eval-after-load 'company
;;        (company-ctags-auto-setup))
;;
;;   Step 2, Use Ctags to create tags file and enjoy.
;;
;; Tips:
;;
;; - Turn on `company-ctags-support-etags' to support tags
;; file created by etags.  But it will increase initial loading time.
;;
;; - Set `company-ctags-extra-tags-files' to load extra tags files,
;;
;;   (setq company-ctags-extra-tags-files '("$HOME/TAGS" "/usr/include/TAGS"))
;;
;; - Set `company-ctags-fuzzy-match-p' to fuzzy match the candidates.
;;   The input could match any part of the candidate instead of the beginning of
;;   the candidate.
;;
;; - Set `company-ctags-ignore-case' to ignore case when fetching candidates
;;
;; - Use rusty-tags to generate tags file for Rust programming language.
;;   Add below code into ~/.emacs,
;;     (setq company-ctags-tags-file-name "rusty-tags.emacs")
;;
;; - Make sure CLI program diff is executable on Windows.
;; It's optional but highly recommended.  It can speed up tags file updating.
;; This package uses diff through variable `diff-command'.
;;
;; - `company-ctags-debug-info' for debugging.
;;

;;; Code:

(require 'find-file)
(require 'company nil t)
(require 'cl-lib)
(require 'subr-x)

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

(defcustom company-ctags-extra-tags-files nil
  "List of extra tags files which are loaded only once.

A typical format is,

    (\"./TAGS\" \"/usr/include/TAGS\" \"$PROJECT/*/include/TAGS\")

Environment variables can be inserted between slashes (`/').
They will be replaced by their definitions.  If a variable does
not exist, it is replaced (silently) with an empty string."
  :type '(repeat 'string))

(defcustom company-ctags-quiet nil
  "Be quiet and do not notify user tags file status."
  :type 'boolean)

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

(defcustom company-ctags-tag-name-valid-characters
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ$#@%_!*&1234567890"
  "The characters of tag name.  It's used for partition algorithm."
  :type 'string)

(defcustom company-ctags-fuzzy-match-p nil
  "If t, fuzzy match the candidates.
The input could match any part of the candidate instead of the beginning of
the candidate."
  :type 'boolean)

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

(defvar company-backends) ; avoid compiling warning

(defvar-local company-ctags-buffer-table-internal nil)

(defvar company-ctags-tags-file-caches nil
  "The cached tags files.")

(defvar company-ctags-cached-candidates nil
  "The cached candidates searched with certain prefix.")

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
      (or company-ctags-buffer-table-internal
          (setq company-ctags-buffer-table-internal
                (company-ctags-find-table)))))

(defun company-ctags-char-in-string-p (character string)
  "Test if CHARACTER is in STRING."
  (let (rlt (i 0) (len (length string)))
    (while (and (not rlt) (< i len))
      (setq rlt (eq (elt string i) character))
      (setq i (1+ i)))
    rlt))

(defun company-ctags-tag-name-character-p (character)
  "Test if CHARACTER is in `company-ctags-tag-name-valid-characters'."
  (company-ctags-char-in-string-p character
                                  company-ctags-tag-name-valid-characters))

(defmacro company-ctags-push-tagname (tagname tagname-dict)
  "Push TAGNAME into TAGNAME-DICT."
  `(let ((c (elt ,tagname 0)))
     (when (company-ctags-tag-name-character-p c)
       (push ,tagname (gethash c ,tagname-dict)))))

(defun company-ctags-n-items (n tagnames)
  "Return first N items of TAGNAMES."
  (cond
   ((<= (length tagnames) n)
    tagnames)
   (t
    (let (rlt (i 0))
      (while (< i n)
        (push (nth i tagnames) rlt)
        (setq i (1+ i)))
      (push " ..." rlt)
      (nreverse rlt)))))

;;;###autoload
(defun company-ctags-debug-info ()
  "Print all debug information."
  (interactive)
  (let* ((caches company-ctags-tags-file-caches)
         (keys (hash-table-keys caches)))
    (message "* cache contents")
    (dolist (k keys)
      (let* ((h (gethash k caches))
             (timestamp (plist-get h :timestamp))
             (filesize (plist-get h :filesize))
             (dict (plist-get h :tagname-dict))
             (dict-keys (hash-table-keys dict)))
        (message "** key=%s timestamp=%s filesize=%s\n" k timestamp filesize)
        (dolist (dk dict-keys)
          (let* ((items (company-ctags-n-items 4 (gethash dk dict))))
            (when (> (length items) 0)
              (message "  %s: %s" (string dk) items))))))))

(defun company-ctags-init-tagname-dict ()
  "Initialize tagname dict."
  (let* ((i 0)
         (dict (make-hash-table))
         (len (length company-ctags-tag-name-valid-characters)))
    (while (< i len)
      (puthash (elt company-ctags-tag-name-valid-characters i) '() dict)
      (setq i (1+ i)))
    dict))

(defun company-ctags-parse-tags (text &optional dict)
  "Extract tag names from TEXT.
DICT is the existing lookup dictionary contains tag names.
If it's nil, return a dictionary, or else return the existing dictionary."
  (let* ((start 0)
         (case-fold-search company-ctags-ignore-case))
    (unless dict (setq dict (company-ctags-init-tagname-dict)))

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
                                      dict))
         (t
          ;; No explicit tag name.  Backtrack a little,
          ;; and look for the implicit one.
          (company-ctags-push-tagname (substring text (match-beginning 1) (match-end 1))
                                      dict)))
        (setq start (+ 4 (match-end 0)))))
     (t
      ;; fast algorithm, support explicit tags name only
      (while (string-match company-ctags-fast-pattern text start)
        (company-ctags-push-tagname (substring text (match-beginning 1) (match-end 1))
                                    dict)
        (setq start (+ 4 (match-end 0))))))

    dict))

(defun company-ctags-all-completions (string collection)
  "Search  match to STRING in COLLECTION to see if it begins with STRING.
If `company-ctags-fuzzy-match-p' is t, check if the match contains STRING."
  (let ((case-fold-search company-ctags-ignore-case))
    (cond
     (company-ctags-fuzzy-match-p
      (let* (rlt)
        ;; code should be efficient in side the this loop
        (dolist (c collection)
          (if (string-match string c) (push c rlt)))
        rlt))
     (t
      (all-completions string collection)))))

(defun company-ctags-fetch-by-first-char (c prefix tagname-dict)
  "Fetch candidates by first character C of PREFIX from TAGNAME-DICT."
  (let* ((rlt (company-ctags-all-completions prefix (gethash c tagname-dict))))
    (when company-ctags-ignore-case
      (let (c2 (offset (- ?a ?A)))
        (cond
         ((company-ctags-char-in-string-p c "abcdefghijklmnopqrstuvwxyz")
          (setq c2 (- c offset)))

         ((company-ctags-char-in-string-p c "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
          (setq c2 (+ c offset))))

        (when c2
          (setq rlt (nconc rlt (company-ctags-all-completions prefix (gethash c2 tagname-dict)))))))
    rlt))

(defun company-ctags-all-candidates (prefix tagname-dict)
  "Search for partial match to PREFIX in TAGNAME-DICT."
  (cond
   (company-ctags-fuzzy-match-p
    (let* ((keys (hash-table-keys tagname-dict))
           rlt)
      ;; search all hash tables
      ;; don't care the first character of prefix
      (dolist (c keys)
        (setq rlt (nconc rlt (company-ctags-fetch-by-first-char c prefix tagname-dict))))
      rlt))
   (t
    (company-ctags-fetch-by-first-char (elt prefix 0) prefix tagname-dict))))

(defun company-ctags-load-tags-file (file static-p &optional force no-diff-prog)
  "Load tags from FILE.
If STATIC-P is t, the corresponding tags file is read only once.
If FORCE is t, tags file is read without `company-ctags-tags-file-caches'.
If NO-DIFF-PROG is t, do NOT use diff on tags file.
This function return t if any tag file is reloaded."
  (let* (raw-content
         (file-info (and company-ctags-tags-file-caches
                         (gethash file company-ctags-tags-file-caches)))
         (use-diff (and (not no-diff-prog)
                        file-info
                        (plist-get file-info :raw-content)
                        (executable-find diff-command)))
         tagname-dict
         reloaded)

    (when (or force
              (not file-info)
              (and
               ;; the tags file is static and is already read into cache
               ;; so don't read it again
               ;; (not (plist-get file-info :static-p))
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
      (cond
       (use-diff
        ;; actually don't change raw-content attached to file-info
        (setq raw-content (plist-get file-info :raw-content))

        ;; use diff to find the new tags
        (let (diff-output)
          (with-temp-buffer
            (insert (plist-get file-info :raw-content))
            ;; when process finished, replace temp buffer with program output
            (call-process-region (point-min) (point-max) diff-command t t nil "-ab" file "-")
            (setq diff-output (buffer-string)))

          ;; compare old and new tags file, extract tag names from diff output which
          ;; should be merged with old tag names
          (setq tagname-dict
                (company-ctags-parse-tags diff-output
                                          (plist-get file-info :tagname-dict)))))
       (t
        (unless company-ctags-quiet (message "Please be patient when loading %s" file))
        (setq raw-content (with-temp-buffer
                            (insert-file-contents file)
                            (buffer-string)))
        ;; collect all tag names
        (setq tagname-dict (company-ctags-parse-tags raw-content))
        (unless company-ctags-quiet (message "%s is loaded." file))))

      ;; initialize hash table if needed
      (unless company-ctags-tags-file-caches
        (set 'company-ctags-tags-file-caches (make-hash-table :test #'equal)))

      ;; finalize tags file info
      (puthash file
               ;; if the tags file is read only once, it will never be updated
               ;; by `diff-command', so don't need store original raw content
               ;; of tags file in order to save memory.
               (list :raw-content (unless static-p raw-content)
                     :tagname-dict tagname-dict
                     :static-p static-p
                     :timestamp (float-time (current-time))
                     :filesize (nth 7 (file-attributes file)))
               company-ctags-tags-file-caches))
    reloaded))

(defun company-ctags--test-cached-candidates (prefix)
  "Test PREFIX in `company-ctags-cached-candidates'."
  (let* ((cands company-ctags-cached-candidates)
         (key (plist-get cands :key))
         (keylen (length key))
         (case-fold-search company-ctags-ignore-case))
    ;;  prefix is "hello" and cache's prefix "ell"
    (and (>= (length prefix) keylen)
         (if company-ctags-fuzzy-match-p (string-match key prefix)
           ;; key is the beginning of prefix
           (string= (substring prefix 0 keylen) key)))))

(defun company-ctags--candidates (prefix)
  "Get candidate with PREFIX."
  (when (and prefix (> (length prefix) 0))
    (let* ((file (and tags-file-name (file-truename tags-file-name)))
           (completion-ignore-case company-ctags-ignore-case)
           (all-tags-files (mapcar (lambda (f)
                                     (file-truename f))
                                   (delete-dups (append (if file (list file))
                                                        (company-ctags-buffer-table)))))
           (extra-tags-files (ff-list-replace-env-vars company-ctags-extra-tags-files))
           rlt)

      ;; load tags files, maybe
      (dolist (f all-tags-files)
        (when (and f (file-exists-p f))
          (when (company-ctags-load-tags-file f
                                              nil ; primary tags file, not static
                                              nil
                                              nil)
            ;; invalidate cached candidates if any tags file is reloaded
            (setq company-ctags-cached-candidates nil))))

      (when extra-tags-files
        (dolist (f extra-tags-files)
          (when (and f (file-exists-p f))
            ;; tags file in `company-ctags-extra-tags-files' is read only once.
            (company-ctags-load-tags-file f
                                          t ; static tags file, read only once
                                          nil
                                          nil))))

      (cond
       ;; re-use cached candidates
       ((and (not company-ctags-fuzzy-match-p)
             company-ctags-cached-candidates
             (company-ctags--test-cached-candidates prefix))

        (let* ((cands (plist-get company-ctags-cached-candidates :cands)))
          (setq rlt (company-ctags-all-completions prefix cands))))

       ;; search candidates through tags files
       (t
        (dolist (f (nconc all-tags-files extra-tags-files))
          (let* ((cache (gethash f company-ctags-tags-file-caches))
                 (tagname-dict (plist-get cache :tagname-dict)))
            (when tagname-dict
              (setq rlt (append rlt (company-ctags-all-candidates prefix tagname-dict))))))

        ;; fuzzy algorithm don't use caching algorithm
        (unless company-ctags-fuzzy-match-p
          (setq company-ctags-cached-candidates
                ;; clone the rlt into cache
                (list :key prefix :cands (mapcar 'identity rlt))))))

      ;; cleanup
      (if rlt (delete-dups rlt)))))

;;;###autoload
(defun company-ctags (command &optional arg &rest ignored)
  "Completion backend of for ctags.  Execute COMMAND with ARG and IGNORED."
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
    (dolist (b backends)
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
