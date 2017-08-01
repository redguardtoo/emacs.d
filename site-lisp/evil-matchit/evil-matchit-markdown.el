;;; evil-matchit-markdown.el --- markdown-mode plugin of evil-matchit

;; Copyright (C) 2014-2017 Chen Bin <chenbin.sh@gmail.com>

;; Author: Chen Bin <chenbin.sh@gmail.com>

;; This file is not part of GNU Emacs.

;;; License:

;; This file is part of evil-matchit
;;
;; evil-matchit is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; evil-matchit is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.


;;; Code:

;; OPTIONAL, you don't need SDK to write a plugin for evil-matchit
;; but SDK don make you write less code, isn't it?
;; All you need to do is just define the match-tags for SDK algorithm to lookup.
(require 'evil-matchit-sdk)

;;;###autoload
(defun evilmi-markdown-get-tag ()
  "Get current tag.
Return (list start-position tag)."
  (let* ((cur-line (evilmi-sdk-curline))
         rlt
         forward-direction)
    (if (string-match "^\\(```\\)" cur-line)
        (let* ((str (match-string 1 cur-line))
               (prefix (buffer-substring-no-properties (point-min)
                                                       (line-beginning-position)))
               (forward-direction (evenp (evilmi-count-matches str prefix))))
          (setq rlt (list (if forward-direction (line-beginning-position)
                            (line-end-position))
                          forward-direction
                          str))))
    rlt))

;;;###autoload
(defun evilmi-markdown-jump (info num)
  "Jump to the next tag."
  (let* ((forward-direction (nth 1 info))
         (str (nth 2 info))
         (pos (point))
         (rlt pos))
    (cond
     ((string= str "```")
      (let* ((prefix (buffer-substring-no-properties (point-min)
                                                     (line-beginning-position))))
        (cond
         (forward-direction
          ;; jump forward
          (goto-char (+ pos (length str)))
          (search-forward str)
          (setq rlt (line-end-position)))
         (t
          ;; jump backward
          (goto-char (- pos (length str)))
          (search-backward str)
          (setq rlt (line-beginning-position))))))
     (t
      ;; do nothing
      ))
    rlt))

(provide 'evil-matchit-markdown)
