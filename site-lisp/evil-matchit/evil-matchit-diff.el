;;; evil-matchit-diff.el -- diff-mode  plugin of evil-matchit

;; Copyright (C) 2014-2016 Chen Bin <chenbin.sh@gmail.com>

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

(require 'evil-matchit-sdk)

(defun evilmi-diff-guess-final-pos ()
  (let* ((final-pos (point)))
    (save-excursion
      (let* (tmp-line)
        (forward-line -1)
        (setq tmp-line (evilmi-sdk-curline))
        (if (string-match-p "^index [0-9a-z]+\\.+[0-9a-z]+ [0-9]+$" tmp-line)
            (forward-line -1))
        (setq tmp-line (evilmi-sdk-curline))
        (if (string-match-p "^diff [^ ]" tmp-line)
            (forward-line -1))
        (setq final-pos (line-end-position))))
    final-pos))

;;;###autoload
(defun evilmi-diff-get-tag ()
  ;; do nothing
  (let* ((cur-line (evilmi-sdk-curline))
         (final-pos (point)))
    (if (string-match-p "^--- " cur-line)
        (save-excursion
          (setq final-pos (evilmi-diff-guess-final-pos))))
    (list final-pos)))

;;;###autoload
(defun evilmi-diff-jump (rlt NUM)
  (let* ((cur-line (evilmi-sdk-curline))
         (final-pos (point)))
    (cond
     ((string-match-p "^\\+\\+\\+ " cur-line)
      ;; next file in diff-mode
      (cond
       ((re-search-forward "^--- " (point-max) t)
        (setq final-pos (evilmi-diff-guess-final-pos))
        (re-search-forward "^\\+\\+\\+ " (point-max) t)
        (goto-char (line-beginning-position)))
       (t
        (setq final-pos (goto-char (point-max))))))

     ((string-match "^--- " cur-line)
      ;; previous file in diff-mode
      (when (re-search-backward "^\\+\\+\\+ " (point-min) t)
        (save-excursion
          (forward-line 1)
          (setq final-pos (line-end-position)))
        (re-search-backward "^--- " (point-min) t)
        (goto-char (line-beginning-position))))

     ((string-match-p "^@@ " cur-line)
      (forward-line 1)
      ;; previous file in diff-mode
      (cond
       ((re-search-forward "^\\(diff\\|---\\|@@ \\)" (point-max) t)
        (goto-char (line-beginning-position))
        (save-excursion
          (forward-line -1)
          (setq final-pos (line-end-position))))
       (t
        (setq final-pos (goto-char (point-max)))))))
    final-pos))

(provide 'evil-matchit-diff)
