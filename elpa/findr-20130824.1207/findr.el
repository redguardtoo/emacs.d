;;; findr.el --- Breadth-first file-finding facility for (X)Emacs

;; Copyright (C) 1999 Free Software Foundation, Inc.

;; Author: David Bakhash <cadet@bu.edu>
;; Maintainer: David Bakhash <cadet@bu.edu>
;; Version: 0.9.11
;; Package-Version: 20130824.1207
;; Created: Tue Jul 27 12:49:22 EST 1999
;; Keywords: files

;; This file is not part of emacs or XEmacs.

;; This file is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of the
;; License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with XEmacs; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
;; 02111-1307, USA.


;;; Commentary:

;; This code contains a command, called `findr', which allows you to
;; search for a file breadth-first.  This works on UNIX, Windows, and
;; over the network, using efs and ange-ftp. It's pretty quick, and (at
;; times) is a better and easier alternative to other mechanisms of
;; finding nested files, when you've forgotten where they are.

;; You pass `findr' a regexp, which must match the file you're looking
;; for, and a directory, and then it just does its thing:

;; M-x findr <ENTER> ^my-lib.p[lm]$ <ENTER> c:/ <ENTER>

;; If called interactively, findr will prompt the user for opening the
;; found file(s).  Regardless, it will continue to search, until
;; either the search is complete or the user quits the search.
;; Regardless of the exit (natural or user-invoked), a findr will
;; return a list of found matches.

;; Two other entrypoints let you to act on regexps within the files:
;; `findr-search' to search
;; `findr-query-replace' to replace


;;; Installation:

;; (autoload 'findr "findr" "Find file name." t)
;; (define-key global-map [(meta control S)] 'findr)

;; (autoload 'findr-search "findr" "Find text in files." t)
;; (define-key global-map [(meta control s)] 'findr-search)

;; (autoload 'findr-query-replace "findr" "Replace text in files." t)
;; (define-key global-map [(meta control r)] 'findr-query-replace)


;; Change Log:

;; 0.1: Added prompt to open file, if uses so chooses, following
;;      request and code example from Thomas Plass.
;; 0.2: Made `findr' not stop after the first match, based on the
;;      request by Thomas Plass.
;;      Also, fixed a minor bug where findr was finding additional
;;      files that were not correct matches, based on
;;      `file-relative-name' misuse (I had to add the 2nd arg to it).
;; 0.3: Added a `sit-for' for redisplay reasons.
;;      Modifications as suggested by RMS: e.g. docstring.
;; 0.4  Added `findr-query-replace', courtesy of Dan Nelsen.
;; 0.5  Fixed spelling and minor bug in `findr-query-replace' when
;;      non-byte-compiled.
;; 0.6  http://groups.google.com/groups?selm=cxjhfml4b2c.fsf_-_%40acs5.bu.edu :
;; From: David Bakhash (cadet@bu.edu)
;; Subject: Re: latest version of findr.el (5)
;; Date: 1999/07/31
;; Courtesy of Dan Nelsen, this version has search-and-replace capabilities.
;; it's still a bit experimental, so I wouldn't expect too much of it.  But it
;; hasn't been tested yet for friendly behavior.
;;
;; The function `findr-query-replace' wasn't working unless you byte-compile the
;; file.  But, since findr is really designed for speed, that's not a bad thing
;; (i.e. it forces you to byte-compile it).  It's as simple as:
;;
;; M-x byte-compile-file <ENTER> /path/to/findr.el <ENTER>
;;
;; anyhow, I think it should work now.
;;
;; dave
;;
;; 0.7: Added `findr-search', broke `findr' by Patrick Anderson
;; 0.8: fixed 0.7 breakage by Patrick Anderson
;; 0.9: Added customize variables, added file/directory filter regexp
;;      minibuffer history by attila.lendvai@gmail.com
;; 0.9.1: Updated date at the top of the file, added .svn filter
;; 0.9.2: Added support for skipping symlinks by attila.lendvai@gmail.com
;; 0.9.3: Smarter minibuffer handling by attila.lendvai@gmail.com
;; 0.9.4: Better handle symlinks by levente.meszaros@gmail.com
;; 0.9.5: Collect resolved files in the result by attila.lendvai@gmail.com
;; 0.9.6: Use a seen hashtable to deal with circles through symlinks by attila.lendvai@gmail.com
;; 0.9.7: Fix wrong calls to message by Michael Heerdegen
;; 0.9.8: Fix 'symbol-calue' typo in non-exposed code path by Michael Heerdegen
;; 0.9.9: Call message less frequent by attila.lendvai@gmail.com
;; 0.9.10: match findr-skip-directory-regexp agaisnt the whole path by attila.lendvai@gmail.com
;; 0.9.11: Fix header line to use ELPA-compliant triple dash by Steve Purcell

(require 'cl)

(provide 'findr)

(defgroup findr nil
  "findr configuration."
  :prefix "findr-"
  :group 'findr)

;; To build the expression below:
;;(let ((result nil))
;;  (dolist (el (list ".backups" "_darcs" ".git" "CVS" ".svn"))
;;    (setf result (if result
;;                     (concatenate 'string result "\\|")
;;                     ""))
;;    (setf result (concatenate 'string result "^" (regexp-quote el) "$")))
;;  result)

(defcustom findr-skip-directory-regexp "\\/.backups$\\|/_darcs$\\|/\\.git$\\|/CVS$\\|/\\.svn$"
  "A regexp filter to skip directory paths."
  :type 'string
  :group 'findr)

(defcustom findr-skip-file-regexp "^[#\\.]"
  "A regexp that all file names will be matched against (including directories) and matching files are skipped."
  :type 'string
  :group 'findr)

(defvar findr-search-regexp-history nil)
(defvar findr-search-replacement-history nil)
(defvar findr-file-name-regexp-history nil)
(defvar findr-directory-history nil)

(defun findr-propertize-string (string properties)
  (add-text-properties 0 (length string) properties string)
  string)

(defmacro findr-with-infrequent-message (&rest body)
  (let ((last-message-at (gensym "last-message-at")))
    `(let ((,last-message-at 0))
       (labels ((message* (message &rest args)
                  (when (> (- (time-to-seconds) ,last-message-at) 0.5)
                    (setq ,last-message-at (time-to-seconds))
                    (apply 'message message args))))
         ,@body))))

(defun findr-propertize-prompt (string)
  (findr-propertize-string string '(read-only t intangible t)))

(defun* findr-read-from-minibuffer (prompt history &key initial-content
                                           store-empty-answer-in-history)
  (let ((minibuffer-message-timeout 0)
        (history-position (position initial-content (symbol-value history)
                                    :test 'string=)))
    (let ((result (read-from-minibuffer
                   (findr-propertize-prompt prompt)
                   initial-content nil nil (if (and (not (consp history))
                                                    history-position)
                                               (cons history (1+ history-position))
                                               history))))
      (when (and store-empty-answer-in-history
                 (zerop (length result)))
        (setf (symbol-value history)
              (delete-if (lambda (el)
                           (zerop (length el)))
                         (symbol-value history)))
        (push result (symbol-value history)))
      result)))

(defun* findr-read-from-minibuffer-defaulting (prompt history &key store-empty-answer-in-history)
  (let* ((default (if (consp history)
                      (elt (symbol-value (car history)) (cdr history))
                      (first (symbol-value history))))
         (result (findr-read-from-minibuffer
                  (format prompt (or default ""))
                  history
                  :store-empty-answer-in-history store-empty-answer-in-history)))
    (if (= (length result) 0)
        default
        result)))

(defun findr-read-search-regexp (&optional prompt)
  (findr-read-from-minibuffer-defaulting
   "Search through files for (regexp, default: \"%s\"): "
   'findr-search-regexp-history))

(defun findr-read-file-regexp (&optional prompt)
  (findr-read-from-minibuffer
   "Look in these files (regexp): "
   'findr-file-name-regexp-history
   :initial-content (first findr-file-name-regexp-history)
   :store-empty-answer-in-history t))

(defun findr-read-starting-directory (&optional prompt)
  (setq prompt (or prompt "Start in directory: "))
  (if (and (fboundp 'ido-read-directory-name)
           ido-mode)
      (ido-read-directory-name prompt)
      (apply 'read-directory-name
             (append
              (list prompt default-directory default-directory t nil)
              (when (featurep 'xemacs)
                (list 'findr-directory-history))))))

;;;; breadth-first file finder...

(defun* findr (name dir &key (prompt-p (interactive-p)) (skip-symlinks nil) (resolve-symlinks t))
  "Search directory DIR breadth-first for files matching regexp NAME.
If PROMPT-P is non-nil, or if called interactively, Prompts for visiting
search result\(s\)."
  (findr-with-infrequent-message
    (let ((*dirs* (findr-make-queue))
          (seen-directories (make-hash-table :test 'equal))
          *found-files*)
      (labels ((findr-1 (dir)
                 (message* "Collecting in dir %s" dir)
                 (let ((files (directory-files dir t "\\w")))
                   (loop
                     for file in files
                     for fname = (file-relative-name file dir)
                     when (and (file-directory-p file)
                               (not (string-match findr-skip-directory-regexp file))
                               (not (gethash (file-truename file) seen-directories))
                               (or (not skip-symlinks)
                                   (not (file-symlink-p file))))
                     do (progn
                          (print file)
                          (setf (gethash (file-truename file) seen-directories) t)
                          (findr-enqueue file *dirs*))
                     when (and (string-match name fname)
                               (not (string-match findr-skip-file-regexp fname))
                               (or (not skip-symlinks)
                                   (not (file-symlink-p file))))
                     do
                     ;; Don't return directory names when
                     ;; building list for `tags-query-replace' or `tags-search'
                     ;;(when (and (file-regular-p file)
                     ;;           (not prompt-p))
                     ;;  (push file *found-files*))

                     ;; _never_ return directory names
                     (when (file-regular-p file)
                       (push (if resolve-symlinks
                                 (file-truename file)
                                 file)
                             *found-files*))
                     (message* "Collecting file %s" file)
                     (when (and prompt-p
                                (y-or-n-p (format "Find file %s? " file)))
                       (find-file file)
                       (sit-for 0)	; redisplay hack
                       )))))
        (unwind-protect
             (progn
               (findr-enqueue dir *dirs*)
               (while (findr-queue-contents *dirs*)
                 (findr-1 (findr-dequeue *dirs*)))
               (message "Searching... done."))
          (return-from findr (nreverse *found-files*)))))))

(defun findr-query-replace (from to name dir)
  "Do `query-replace-regexp' of FROM with TO, on each file found by findr.
If you exit (\\[keyboard-quit] or ESC), you can resume the query replace
with the command \\[tags-loop-continue]."
  (interactive (let ((search-for (findr-read-search-regexp "Search through files for (regexp): ")))
                 (list search-for
                       (findr-read-from-minibuffer-defaulting
                        (format "Query replace '%s' with %s: "
                                search-for "(default: \"%s\")")
                        'findr-search-replacement-history)
                       (findr-read-file-regexp)
                       (findr-read-starting-directory))))
  (tags-query-replace from to nil '(findr name dir)))

(defun findr-search (regexp files dir)
  "Search through all files listed in tags table for match for REGEXP.
Stops when a match is found.
To continue searching for next match, use command \\[tags-loop-continue]."
  (interactive (list (findr-read-search-regexp)
                     (findr-read-file-regexp)
                     (findr-read-starting-directory)))
  (tags-search regexp '(findr files dir)))


(defun findr-find-files (files dir)
  "Same as `findr' except file names are put in a compilation buffer."
  (interactive (list (findr-read-file-regexp)
                     (findr-read-starting-directory)))
  ;; TODO: open a scratch buffer or store in the clipboard
  (mapcar (lambda (file)
            (message "%s" file))
          (findr files dir)))

;;;; Queues

(defun findr-make-queue ()
  "Build a new queue, with no elements."
  (let ((q (cons nil nil)))
    (setf (car q) q)
    q))

(defun findr-enqueue (item q)
  "Insert item at the end of the queue."
  (setf (car q)
        (setf (rest (car q))
              (cons item nil)))
  q)

(defun findr-dequeue (q)
  "Remove an item from the front of the queue."
  (prog1 (pop (cdr q))
    (when (null (cdr q))
      (setf (car q) q))))

(defsubst findr-queue-contents (q)
  (cdr q))

;;; findr.el ends here
