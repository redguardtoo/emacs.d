;;; company-dabbrev.el --- dabbrev-like company-mode completion back-end  -*- lexical-binding: t -*-

;; Copyright (C) 2009, 2011, 2014  Free Software Foundation, Inc.

;; Author: Nikolaj Schumacher

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
;;

;;; Code:

(require 'company)
(require 'cl-lib)

(defgroup company-dabbrev nil
  "dabbrev-like completion back-end."
  :group 'company)

(defcustom company-dabbrev-other-buffers 'all
  "Determines whether `company-dabbrev' should search other buffers.
If `all', search all other buffers, except the ignored ones.  If t, search
buffers with the same major mode.  See also `company-dabbrev-time-limit'."
  :type '(choice (const :tag "Off" nil)
                 (const :tag "Same major mode" t)
                 (const :tag "All" all)))

(defcustom company-dabbrev-ignore-buffers "\\`[ *]"
  "Regexp matching the names of buffers to ignore."
  :type 'regexp)

(defcustom company-dabbrev-time-limit .1
  "Determines how many seconds `company-dabbrev' should look for matches."
  :type '(choice (const :tag "Off" nil)
                 (number :tag "Seconds")))

(defcustom company-dabbrev-char-regexp "\\sw"
  "A regular expression matching the characters `company-dabbrev' looks for."
  :type 'regexp)

(defcustom company-dabbrev-ignore-case 'keep-prefix
  "Non-nil to ignore case when collecting completion candidates.
When it's `keep-prefix', the text before point will remain unchanged after
candidate is inserted, even some of its characters have different case.")

(defcustom company-dabbrev-downcase 'case-replace
  "Whether to downcase the returned candidates.

The value of nil means keep them as-is.
`case-replace' means use the value of `case-replace'.
Any other value means downcase.

If you set this value to nil, you may also want to set
`company-dabbrev-ignore-case' to any value other than `keep-prefix'.")

(defcustom company-dabbrev-minimum-length 4
  "The minimum length for the completion candidate to be included.
This variable affects both `company-dabbrev' and `company-dabbrev-code'."
  :type 'integer
  :package-version '(company . "0.8.3"))

(defmacro company-dabrev--time-limit-while (test start limit &rest body)
  (declare (indent 3) (debug t))
  `(let ((company-time-limit-while-counter 0))
     (catch 'done
       (while ,test
         ,@body
         (and ,limit
              (eq (cl-incf company-time-limit-while-counter) 25)
              (setq company-time-limit-while-counter 0)
              (> (float-time (time-since ,start)) ,limit)
              (throw 'done 'company-time-out))))))

(defsubst company-dabbrev--make-regexp (prefix)
  (concat "\\<" (if (equal prefix "")
              company-dabbrev-char-regexp
            (regexp-quote prefix))
          "\\(" company-dabbrev-char-regexp "\\)*\\>"))

(defun company-dabbrev--search-buffer (regexp pos symbols start limit
                                       ignore-comments)
  (save-excursion
    (let (match)
      (goto-char (if pos (1- pos) (point-min)))
      ;; search before pos
      (company-dabrev--time-limit-while (re-search-backward regexp nil t)
          start limit
        (setq match (match-string-no-properties 0))
        (if (and ignore-comments (company-in-string-or-comment))
            (goto-char (nth 8 (syntax-ppss)))
          (when (>= (length match) company-dabbrev-minimum-length)
            (push match symbols))))
      (goto-char (or pos (point-min)))
      ;; search after pos
      (company-dabrev--time-limit-while (re-search-forward regexp nil t)
          start limit
        (setq match (match-string-no-properties 0))
        (if (and ignore-comments (company-in-string-or-comment))
            (re-search-forward "\\s>\\|\\s!\\|\\s\"" nil t)
          (when (>= (length match) company-dabbrev-minimum-length)
            (push match symbols))))
      symbols)))

(defun company-dabbrev--search (regexp &optional limit other-buffer-modes
                                ignore-comments)
  (let* ((start (current-time))
         (symbols (company-dabbrev--search-buffer regexp (point) nil start limit
                                                  ignore-comments)))
    (when other-buffer-modes
      (cl-dolist (buffer (delq (current-buffer) (buffer-list)))
        (with-current-buffer buffer
          (when (if (eq other-buffer-modes 'all)
                    (not (string-match-p company-dabbrev-ignore-buffers
                                         (buffer-name)))
                  (apply #'derived-mode-p other-buffer-modes))
            (setq symbols
                  (company-dabbrev--search-buffer regexp nil symbols start
                                                  limit ignore-comments))))
        (and limit
             (> (float-time (time-since start)) limit)
             (cl-return))))
    symbols))

;;;###autoload
(defun company-dabbrev (command &optional arg &rest ignored)
  "dabbrev-like `company-mode' completion back-end."
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-dabbrev))
    (prefix (company-grab-word))
    (candidates
     (let* ((case-fold-search company-dabbrev-ignore-case)
            (words (company-dabbrev--search (company-dabbrev--make-regexp arg)
                                            company-dabbrev-time-limit
                                            (pcase company-dabbrev-other-buffers
                                              (`t (list major-mode))
                                              (`all `all))))
            (downcase-p (if (eq company-dabbrev-downcase 'case-replace)
                            case-replace
                          company-dabbrev-downcase)))
       (if downcase-p
           (mapcar 'downcase words)
         words)))
    (ignore-case company-dabbrev-ignore-case)
    (duplicates t)))

(provide 'company-dabbrev)
;;; company-dabbrev.el ends here
