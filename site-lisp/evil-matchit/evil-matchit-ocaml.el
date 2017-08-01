;;; evil-matchit-ocaml.el -- tuareg-mode  plugin of evil-matchit

;; Copyright (C) 2014-2017 Chen Bin <chenbin.sh@gmail.com>

;; Author: Tomasz Kołodziejski <tkolodziejski@gmail.com>

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

(defvar evilmi-ocaml-keywords
  '((("struct" "begin" "sig" "object") ("end"))
    (("if") ("then"))
    (("match") ("with"))
    (("match" "try") ("with"))
    (("while" "for") ("done"))
    (("let") ("in"))
    ())
  "Ocaml keywords.")

(defvar evilmi-ocaml-all-keywords
  (apply 'append (apply 'append evilmi-ocaml-keywords)))

(defvar evilmi-ocaml-keywords-regex
  (format "\\<\\(%s\\)\\>" (mapconcat 'identity evilmi-ocaml-all-keywords "\\|"))
  "Regexp to find next/previous keyword.")

;; jumps to next keyword. Returs nil if there's no next word
(defun evilmi-ocaml-next-keyword (direction)
  (if (= direction 0)
      (let ((new-point (save-excursion
          (forward-char)
          (if (search-forward-regexp evilmi-ocaml-keywords-regex nil t)
              (search-backward-regexp evilmi-ocaml-keywords-regex)
            nil)
        )))
        (if new-point (goto-char new-point)))
    (search-backward-regexp evilmi-ocaml-keywords-regex nil t)))

(defun evilmi-ocaml-end-word ()
  (save-excursion
    (search-forward-regexp "\\>")
    (point)))

(defun evilmi-ocaml-get-word ()
  (buffer-substring-no-properties (point) (evilmi-ocaml-end-word)))

(defun evilmi-ocaml-is-keyword (l keyword)
  "Checks if the keyword belongs to a row."
  (find-if (lambda (w) (string-equal w keyword)) (apply 'append l)))

(defun evilmi-ocaml-get-tag-info (keyword)
  "Find the row in the evilmi-ocaml-keywords."
  (find-if (lambda (l) (evilmi-ocaml-is-keyword l keyword)) evilmi-ocaml-keywords))

;; 0 - forward
;; 1 - backward
(defun evilmi-ocaml-go (tag-info level direction)
  (if (= level 0)
      (point)
    (if (evilmi-ocaml-next-keyword direction)
        (progn
          (setq keyword (evilmi-ocaml-get-word))

          (if (evilmi-ocaml-is-keyword tag-info keyword)
              ;; interesting tag
              (if (member keyword (nth direction tag-info))
                  (evilmi-ocaml-go tag-info (+ level 1) direction)
                (evilmi-ocaml-go tag-info (- level 1) direction))

            ;; other tag
            (evilmi-ocaml-go tag-info level direction)))
      nil)))

(defun evilmi-ocaml-goto-word-beginning ()
  (let ((bounds (bounds-of-thing-at-point 'word))
        (word (thing-at-point 'word))
        (line-end (line-end-position)))
    (if bounds (goto-char (car bounds)))
    (let ((next-keyword
           (save-excursion
             (if (find word evilmi-ocaml-all-keywords :test 'equal)
                 (point)
               (evilmi-ocaml-next-keyword 0)
               (if (< (point) line-end) (point))))))
      (if next-keyword (goto-char next-keyword)))))

;;;###autoload
(defun evilmi-ocaml-get-tag ()
  "Return information of current tag: (list position-of-word word)."
  (save-excursion
    (evilmi-ocaml-goto-word-beginning)
    (list (car (bounds-of-thing-at-point 'word))
          (evilmi-ocaml-get-word))))

;;;###autoload
(defun evilmi-ocaml-jump (rlt num)
  (let* ((keyword (cadr rlt))
         (tag-info (evilmi-ocaml-get-tag-info keyword))
         (direction (if (member keyword (car tag-info)) 0 1)))
    (let ((new-point (save-excursion
                       (evilmi-ocaml-goto-word-beginning)
                       (evilmi-ocaml-go tag-info 1 direction))))
      (if new-point (goto-char new-point)))))

(provide 'evil-matchit-ocaml)
