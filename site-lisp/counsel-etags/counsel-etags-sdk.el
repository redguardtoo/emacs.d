;;; counsel-etags-sdk.el --- counsel-etags SDK  -*- lexical-binding: t -*-

;; Copyright (C) 2018, 2019 Chen Bin

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

;;; Code:

(defun counsel-etags-sdk-get-context ()
  "Return current `major-mode', line number, file, font-face, text of current line."
  (list
   :major-mode major-mode
   :line-number (line-number-at-pos)
   :fullpath (and (buffer-file-name) (file-truename (buffer-file-name)))
   :font-face (get-text-property (point) 'face)
   :line-text (buffer-substring-no-properties (line-beginning-position)
                                              (line-end-position))))

(defmacro counsel-etags-sdk-string-contains (str ch)
  "If STR contain character CH."
  `(let* ((i 0)
          (len (length ,str))
          (continue t)
          rlt)
     (cond
      ((not ,str)
       (setq rlt t))
      (t
       (while continue
         (cond
          ((= ,ch (aref ,str i))
           (setq rlt t)
           (setq continue nil))
          (t
           (setq i (1+ i))
           (if (>= i len) (setq continue nil)))))))
     rlt))

(defmacro counsel-etags-sdk-is-word-character (ch)
  "Is CH a character of word."
  `(or (and (>= ,ch ?0) (<= ,ch ?9))
       (and (>= ,ch ?a) (<= ,ch ?z))
       (and (>= ,ch ?A) (<= ,ch ?Z))))

(defun counsel-etags-sdk-thing-at-point (&optional word-chars)
  "Get thing at point which contain characters from WORD-CHARS."
  (let* ((begin (point))
         (end (1+ begin))
         (lb (line-beginning-position))
         (le (line-end-position))
         ch)
    (save-excursion
      (while (and (>= (point) lb)
                  (setq ch (following-char))
                  (or (counsel-etags-sdk-string-contains word-chars ch)
                      (counsel-etags-sdk-is-word-character ch)))
        (backward-char))
      (setq begin (1+ (point))))
    (save-excursion
      (while (and (< (point) le)
                  (setq ch (following-char))
                  (or (counsel-etags-sdk-string-contains word-chars ch)
                      (counsel-etags-sdk-is-word-character ch)))
        (forward-char))
      (setq end (1+ (point))))
    (buffer-substring-no-properties begin (1- end))))

(provide 'counsel-etags-sdk)
;;; counsel-etags-sdk.el ends here
