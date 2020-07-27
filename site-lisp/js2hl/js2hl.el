;;; js2hl.el --- Highlight/rename things using `js2-mode' parser  -*- lexical-binding: t -*-
;;
;; Copyright (C) 2020 Chen Bin <chenbin DOT sh@gmail DOT com>
;; Copyright (C) 2016-2017 Mihai Bazon <mihai.bazon@gmail.com>
;;
;; Version: 0.0.1
;; Keywords: conveniences
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: https://github.com/redguardtoo/js2hl
;; Package-Requires: ((emacs "24.4") (js2-mode "20190219")

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; The program provides methods to highlight and rename things in `js2-mode'.
;; Its based on "js2r-highlights.el" by Mihai Bazon.
;; See http://lisperator.net/blog/emacs-and-javascript-in-2017/
;; I clean the code to make this program only dependent on `js2-mode'.
;;
;; Usage,
;;
;; `js2hl-show-thing-at-point' to show things at point.
;; Things are variable, strings, numbers, names like "this" or "super".
;; It uses parser of `js2-mode' to extract correct things.
;;
;; `js2hl-rename-thing-at-point' to rename things at point.
;;
;; `js2hl-show-exits' to show exit points from the function surrounding point.
;; That is, `return' and `throw' statements.
;;
;; `js2hl-forget-it' to exit highlight mode.
;;
;; `js2hl-move-next' and `js2hl-move-prev' move between the highlights.
;;

;;; Code:

(require 'cl-lib)
(require 'js2-mode nil t)

(defvar js2-mode-ast)

(defun js2hl-name-node(pos)
  "Get name node at POS."
  (let* ((node (js2-node-at-point pos)))
    (if (js2-name-node-p node) node)))

(defun js2hl-local-name-node-at-point ()
  "Get local name node at point."
  (let* ((pos (point)))
    (or (js2hl-name-node pos) (js2hl-name-node (1- pos)))))

(defun js2hl-name-node-defining-scope (name-node)
  "Get NAME-NODE defining scope."
  (js2-get-defining-scope (js2-node-get-enclosing-scope name-node)
                          (js2-name-node-name name-node)))

(defun js2hl-local-name-node-p (node)
  "Test if NODE is local name node."
  (let* ((parent (js2-node-parent node)))
    (and parent (js2-name-node-p node)
         (not (and (js2-object-prop-node-p parent)
                   (eq node (js2-object-prop-node-left parent))))
         (not (and (js2-prop-get-node-p parent)
                   (eq node (js2-prop-get-node-right parent)))))))

(defmacro js2hl-push-node-region (node result &optional node-length)
  "Push region of NODE into RESULT.
If NODE-LENGTH is not nil, use it to calculate end of region."
  `(let* ((beg (js2-node-abs-pos ,node))
          (end (if ,node-length (+ ,node-length beg)
                 (js2-node-abs-end ,node))))
     (push (cons beg end) ,result)))

(defun js2hl-get-var-regions ()
  "Get variable regions."
  (let* ((name-node (js2hl-local-name-node-at-point))
         (name (js2-name-node-name name-node))
         (len (js2-node-len name-node))
         (scope (js2hl-name-node-defining-scope name-node))
         result)
    (js2-visit-ast scope
                   (lambda (node end-p)
                     (when (and (not end-p)
                                (js2hl-local-name-node-p node)
                                (string= name (js2-name-node-name node))
                                (eq scope (js2hl-name-node-defining-scope node)))
                       (js2hl-push-node-region node result len))
                     t))
    (nreverse result)))



(defun js2hl-constant-node-value (node)
  "Get value of constant NODE."
  (cond
   ((js2-number-node-p node)
    (js2-number-node-value node))
   ((js2-string-node-p node)
    (js2-string-node-value node))
   ((js2-regexp-node-p node)
    (js2-regexp-node-value node))
   (t (error "Not a constant node"))))

(defun js2hl-get-constant-regions (const)
  "Get regions of CONST."
  (let* (regions
         (type (js2-node-type const))
         (value (js2hl-constant-node-value const)))
    (js2-visit-ast js2-mode-ast
                   (lambda (node end-p)
                      (when (and (not end-p)
                                 (= type (js2-node-type node))
                                 (equal value (js2hl-constant-node-value node)))
                        (js2hl-push-node-region node regions))
                      t))
    regions))

(defun js2hl-get-this-regions (node)
  "Get region of NODE which is js keyword this."
  (let* ((func (js2-mode-find-parent-fn node))
         (type (js2-node-type node))
         (regions (list)))
    (unless func
      (error "Not inside a function"))
    (js2-visit-ast func
                   (lambda (node end-p)
                     (ignore end-p)
                     (cond
                      ((js2-function-node-p node)
                       (or (eq node func)
                           (eq (js2-function-node-form node) 'FUNCTION_ARROW)))
                      ((eq (js2-node-type node) type)
                       (js2hl-push-node-region node regions))
                      (t t))))
    regions))

(defun js2hl-get-regions (pos)
  "Get regions at position POS."
  (let* ((node (js2-node-at-point pos)))
    (cond
     ((js2-name-node-p node) (js2hl-get-var-regions))
     ((or (js2-string-node-p node)
          (js2-number-node-p node)
          (js2-regexp-node-p node))
      (js2hl-get-constant-regions node))
     ((js2-this-or-super-node-p node)
      (js2hl-get-this-regions node)))))

(defun js2hl-get-exits-regions (pos)
  "Get exist regions at position POS."
  (let* ((node (js2-node-at-point pos t))
         (func (js2-mode-find-parent-fn node))
         (regions (list)))
    (unless func
      (error "Not inside a function"))
    (js2-visit-ast func
                   (lambda (node end-p)
                     (cond
                      ((js2-function-node-p node)
                       (eq node func))
                      ((not end-p)
                       (when (or (js2-throw-node-p node)
                                 (js2-return-node-p node))
                         (js2hl-push-node-region node regions))
                       t))))
    regions))

(defun js2hl-get-overlays (reverse)
  "Get overlays in REVERSE direction or not."
  (sort (cl-remove-if-not (lambda (ov)
                            (overlay-get ov 'js2hl))
                          (overlays-in (point-min) (point-max)))
        (if reverse
            (lambda (a b)
              (> (overlay-start a) (overlay-start b)))
          (lambda (a b)
            (< (overlay-start a) (overlay-start b))))))

(defun js2hl-things (things)
  "Show highlighted THINGS."
  (let ((things (sort things #'js2hl-compare-regions)))
    (cond
     (things
      (let ((data (cl-loop
                   for ref in things
                   for beg = (car ref)
                   for end = (cdr ref)
                   do (let ((ovl (make-overlay beg end)))
                        (overlay-put ovl 'face 'highlight)
                        (overlay-put ovl 'evaporate t)
                        (overlay-put ovl 'js2hl t))
                   collect (list (buffer-substring-no-properties beg end) beg end))))
        (message "%d places highlighted" (length things))
        (js2hl-mode 1)
        data))
     (t
      (message "No places found")))))

(defun js2hl-get-regions-at-point ()
  "Get regions at point."
  (let* ((pos (point)))
    (or (js2hl-get-regions pos) (js2hl-get-regions (1- pos)))))

;;;###autoload
(defun js2hl-show-thing-at-point ()
  "Highlight all occurrences of the thing at point.
Use this when the point is on a variable, and it will
highlight all usages of it in its defining scope.  You can also
use it on strings, numbers or literal regexps (highlights
occurrences in the whole buffer), or on keywords `this' and
`super' (highlights occurrences in the current function)."
  (interactive)
  (js2-reparse)
  (js2hl-forget-it)
  (js2hl-things (js2hl-get-regions-at-point)))

;;;###autoload
(defun js2hl-show-exits ()
  "Show exit points from the function surrounding point.
That is, `return' and `throw' statements."
  (interactive)
  (js2-reparse)
  (js2hl-forget-it)
  (js2hl-things (js2hl-get-exits-regions (point))))

(defun js2hl-compare-regions (a b)
  "Compare region A and B by region start."
  (< (car a) (car b)))

(defun js2hl-get-old-name (places)
  "Get old name from PLACES."
  (let* (first-place)
    (cond
     ((and places (consp (setq first-place (nth 0 places))))
      (buffer-substring-no-properties (car first-place) (cdr first-place)))
     (t
      ""))))

;;;###autoload
(defun js2hl-rename-thing-at-point ()
  "Replace the highlighted things with NEW-NAME.
Only works if the mode was called with `js2hl-show-thing-at-point'."
  (interactive)
  (let* ((places (sort (js2hl-get-regions-at-point) #'js2hl-compare-regions))
         (old-name (js2hl-get-old-name places))
         (new-name (read-string (format "Replace \"%s\" with: " old-name))))
    (when (and places new-name)
      (save-excursion
        (dolist (p (nreverse places))
          (let* ((begin (car p))
                 (end (cdr p)))
            (delete-region begin end)
            (goto-char begin)
            (insert new-name)))
        (message "%d occurrences renamed to %s" (length places) new-name)))
    (js2hl-forget-it)))

;;;###autoload
(defun js2hl-forget-it ()
  "Exit the highlight minor mode."
  (interactive)
  (remove-overlays (point-min) (point-max) 'js2hl t)
  (js2hl-mode 0))

;;;###autoload
(defun js2hl-move-next ()
  "Move cursor to the next highlighted node."
  (interactive)
  (catch 'done
    (dolist (i (js2hl-get-overlays nil))
      (let ((x (overlay-start i)))
        (when (> x (point))
          (goto-char x)
          (throw 'done nil))))))

;;;###autoload
(defun js2hl-move-prev ()
  "Move cursor to the previous highlighted node."
  (interactive)
  (catch 'done
    (dolist (i (js2hl-get-overlays t))
      (when (< (overlay-end i) (point))
        (goto-char (overlay-start i))
        (throw 'done nil)))))

(defvar js2hl-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-g") 'js2hl-forget-it)
    map)
  "Minor mode keymap for Js2hl mode.")

;;;###autoload
(define-minor-mode js2hl-mode
  "Internal mode used by `js2hl'."
  nil "JS2HL" nil)

(provide 'js2hl)
;;; js2hl.el ends here
