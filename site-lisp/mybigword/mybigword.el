;;; mybigword.el --- Vocabulary builder using Zipf to extract English big words -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2020 Chen Bin <chenbin DOT sh AT gmail.com>
;;
;; Author: Chen Bin <chenbin DOT sh AT gmail.com>
;; URL: https://github.com/redguardtoo/mybigword
;; Version: 0.0.2
;; Keywords: convenience
;; Package-Requires: ((emacs "24.4"))
;;
;; This file is not part of GNU Emacs.

;;; License:
;;
;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This program extract big words from text.
;; The words whose Zipf frequency less than `mybigword-upper-limit' are
;; big words.
;;
;; Zipf scale was proposed by Marc Brysbaert, who created the SUBTLEX lists.
;; Zipf frequency of a word is the base-10 logarithm of the number of times it
;; appears per billion words.
;;
;; A word with Zipf value 6 appears once per thousand words,for example, and a
;; word with Zipf value 3 appears once per million words.
;;
;; Reasonable Zipf values are between 0 and 8, but the minimum Zipf value
;; appearing here is 1.0.
;;
;; We use 0 as the default Zipf value for words that do not appear in the given
;; word list,although it should mean one occurrence per billion words."
;;
;; Thanks to https://github.com/LuminosoInsight/wordfreq for providing the data.
;;
;; Usage,
;;
;;   Run `mybigword-show-big-words-from-file'
;;   Run `mybigword-show-big-words-from-current-buffer'

;;; Code:

(defgroup mybigword nil
  "Filter the words by the frequency usage of each word."
  :group 'tools)

(defcustom mybigword-data-file nil
  "The word frequency file whose lines are sorted alphabetically.
Each line has two fields.  The first field is the lowercase word.
The second field is the frequency usage of the word.
If nil, the default data is used."
  :group 'mybigword
  :type 'string)

(defcustom mybigword-excluded-words
  '("anybody"
    "anymore"
    "anyone"
    "anyway"
    "couldn"
    "dear"
    "didn"
    "doesn"
    "ever"
    "everybody"
    "glad"
    "guess"
    "hasn"
    "hate"
    "haven"
    "hello"
    "idiot"
    "listen"
    "maybe"
    "okay"
    "our"
    "ours"
    "ourselves"
    "sorry"
    "thank"
    "theirs"
    "then"
    "wasn"
    "worry"
    "wouldn")
  "The words being excluded."
  :group 'mybigword
  :type '(repeat string))

(defcustom mybigword-upper-limit 4
  "The word whose zipf frequency is below this limit is big word."
  :group 'mybigword
  :type 'float)

;; internal variable
(defvar mybigword-cache nil
  "Cached frequency data.")

(defvar mybigword-debug nil
  "For debug only.")

;;;###autoload
(defun mybigword-update-cache ()
  "Update cache using `mybigword-data-file'."
  (let* ((file (or mybigword-data-file
                   (concat (file-name-directory
                            (locate-library "mybigword.el"))
                           "eng.zipf")))
         (i 0)
         (beg 0)
         end
         raw-content
         content)

    (when mybigword-debug
      (message "mybigword-update-cache called file=%s" file))

    (when (file-exists-p file)
      ;; initialize hash table whose key is from a...z
      (setq content (make-hash-table :test #'equal))

      ;; read content of file
      (setq raw-content (with-temp-buffer
                          (insert-file-contents file)
                          (buffer-string)))
      (setq i 1)
      (while (< i 26)
        (let* ((ch (+ ?a i)))
          (setq end (string-match (format "^%c" ch) raw-content beg))
          (when (and beg end (< beg end))
            (puthash (1- ch)
                     (substring-no-properties raw-content beg end)
                     content)
            (setq beg end)))
        (setq i (1+ i)))
      ;; last missing piece
      (puthash ?z
               (substring-no-properties raw-content beg (length raw-content))
               content)
      (setq mybigword-cache (list :content content
                                 :file file
                                 :timestamp (float-time (current-time))
                                 :filesize (nth 7 (file-attributes file))))
      (message "Frequency file %s is loaded." file))))

(defmacro mybigword-extract-freq (word str)
  "Extract WORD's usage frequency from STR."
  `(and (string-match (format "^%s \\([0-9.]*\\)$" ,word) ,str)
        (string-to-number (match-string 1 ,str))))

(defun mybigword-convert-word (raw-word)
  "Convert RAW-WORD to the word to look up."
  (let* ((rlt raw-word))
    (cond
     ((string-match "\\([a-z]+\\)i\\(ed\\|ly\\|es\\)$" raw-word)
      (setq rlt (concat (match-string 1 raw-word) "y")))

     ((string-match "\\([a-z]+\\)\\(t\\|r\\|p\\|n\\)\\{2\\}\\(ed\\|ing\\)$" raw-word)
      (setq rlt (concat (match-string 1 raw-word) (match-string 2 raw-word))))

     ((string-match "\\([a-z]+\\)\\(ly\\|s\\|ing\\|ingly\\)$" raw-word)
      (setq rlt (match-string 1 raw-word)))

     ((string-match "\\([a-z]+\\)\\(ed\\|es\\)$" raw-word)
      (setq rlt (match-string 1 raw-word))))
    rlt))

(defun mybigword-convert-word-again (raw-word)
  "Convert RAW-WORD to the word to look up."
  (let* ((rlt raw-word))
    (cond
     ((string-match "\\([a-z]+e\\)\\(d\\|s\\)$" raw-word)
      (setq rlt (match-string 1 raw-word))))
    rlt))

(defun mybigword-show-big-words-from-content (content)
  "Show words whose zipf frequency is below `mybigword-upper-limit' in CONTENT."
  (unless mybigword-cache (mybigword-update-cache))
  (let* ((big-words (mybigword-extract-words content)))
    (cond
       (big-words
        ;; sort windows
        (setq big-words (sort big-words (lambda (a b) (< (cdr a) (cdr b)))))
        (switch-to-buffer-other-window "*BigWords*")
        (erase-buffer)
        (dolist (bw big-words)
          (insert (format "%s %s\n" (car bw) (cdr bw))))
        (goto-char (point-min)))
       (t
        (message "No big word is found!")))))

(defmacro mybigword-push-cand (word dict cands)
  "Get WORD and its frequency from DICT.  Push them into CANDS."
  `(push (cons ,word (mybigword-extract-freq ,word ,dict)) ,cands))

(defmacro mybigword-push-word (word frequency result)
  "Push WORD FREQUENCY into RESULT."
  `(unless (member ,word mybigword-excluded-words)
     (push (cons ,word ,frequency) ,result)))

;;;###autoload
(defun mybigword-extract-words (text)
  "Words whose usage frequency is below `mybigword-upper-limit' in TEXT."
  (let* ((raw-words (mapcar #'downcase (split-string text "[^A-Za-z]+")))
         (words (delq nil (delete-dups (sort raw-words #'string<))))
         h str
         rlt)

    (when mybigword-debug
      (message "mybigword-cache file=%s size=%s"
               (plist-get mybigword-cache :file)
               (plist-get mybigword-cache :filesize)))

    (when mybigword-cache
      (setq h (plist-get mybigword-cache :content))
      (dolist (word words)
        (when (and (> (length word) 3)
                   (setq str (gethash (elt word 0) h)))
          (let* (cands (max-item '(nil . 0)))
            (mybigword-push-cand word str cands)
            (mybigword-push-cand (mybigword-convert-word word) str cands)
            (mybigword-push-cand (mybigword-convert-word-again word) str cands)

            ;; find the one with highest zipf frequency
            (dolist (c cands)
              (let* ((freq (cdr c)))
                (when (and freq (> freq (cdr max-item)))
                  (setq max-item c))))
            (cond
             ((car max-item)
              (when (< (cdr max-item) mybigword-upper-limit)
                (mybigword-push-word (car max-item) (cdr max-item) rlt)))
             (t
              ;; word is not found in dictionary
              (mybigword-push-word word -1 rlt)))))))
    rlt))

;;;###autoload
(defun mybigword-show-big-words-from-current-buffer ()
  "Show big words in current buffer."
  (interactive)
  (mybigword-show-big-words-from-content (buffer-string)))

;;;###autoload
(defun mybigword-show-big-words-from-file (file)
  "Show bug words from FILE."
  (interactive (list (read-file-name "Find file: " nil default-directory t)))
  (when (and file (file-exists-p file))
    (unless mybigword-cache (mybigword-update-cache))
    (let* ((content (with-temp-buffer
                      (insert-file-contents file)
                      (buffer-string))))
      (mybigword-show-big-words-from-content content))))

(provide 'mybigword)
;;; mybigword.el ends here
