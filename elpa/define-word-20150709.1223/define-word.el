;;; define-word.el --- display the definition of word at point. -*- lexical-binding: t -*-

;; Copyright (C) 2015 Oleh Krehel

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/define-word
;; Package-Version: 20150709.1223
;; Version: 0.1.0
;; Package-Requires: ((emacs "24.1"))
;; Keywords: dictionary, convenience

;; This file is not part of GNU Emacs

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This package will send an anonymous request to http://wordnik.com/
;; to get the definition of word or phrase at point, parse the resulting HTML
;; page, and display it with `message'.
;;
;; The HTML page is retrieved asynchronously, using `url-retrieve'.
;;
;;; Code:

(require 'url-parse)
(require 'url-http)

(defgroup define-word nil
  "Define word at point using an online dictionary."
  :group 'convenience
  :prefix "define-word-")

(defconst define-word-limit 10
  "Maximum amount of results to display.")

(defcustom define-word-unpluralize t
  "When non-nil, change the word to singular when appropriate.
The rule is that all definitions must contain \"Plural of\".")

;;;###autoload
(defun define-word (word)
  "Define WORD using the Wordnik website."
  (interactive (list (read-string "Word: ")))
  (let ((link (concat "http://wordnik.com/words/" (downcase word))))
    (save-match-data
      (url-retrieve
       link
       (lambda (status)
         (let ((err (plist-get status :error)))
           (if err (error
                    "\"%s\" %s" link
                    (downcase (nth 2 (assq (nth 2 err) url-http-codes)))))
           (let (results beg part)
             (while (re-search-forward "<li><abbr[^>]*>\\([^<]*\\)</abbr>" nil t)
               (setq part (match-string 1))
               (unless (= 0 (length part))
                 (setq part (concat part " ")))
               (skip-chars-forward " ")
               (setq beg (point))
               (when (re-search-forward "</li>")
                 (push (concat (propertize part 'face 'font-lock-keyword-face)
                               (buffer-substring-no-properties beg (match-beginning 0)))
                       results)))
             (setq results (nreverse results))
             (cond ((= 0 (length results))
                    (message "0 definitions found"))
                   ((and define-word-unpluralize
                         (cl-every (lambda (x) (string-match "[Pp]\\(?:lural\\|l\\.\\).*of \\(.*\\)\\." x))
                                   results))
                    (define-word (match-string 1 (car (last results)))))
                   (t
                    (when (> (length results) define-word-limit)
                      (setq results (cl-subseq results 0 define-word-limit)))
                    (message (mapconcat #'identity results "\n")))))))
       nil
       t t))))

;;;###autoload
(defun define-word-at-point ()
  "Use `define-word' to define word at point.
When the region is active, define the marked phrase."
  (interactive)
  (if (use-region-p)
      (define-word
        (buffer-substring-no-properties
         (region-beginning)
         (region-end)))
    (define-word (substring-no-properties
                  (thing-at-point 'word)))))

(provide 'define-word)

;;; define-word.el ends here
