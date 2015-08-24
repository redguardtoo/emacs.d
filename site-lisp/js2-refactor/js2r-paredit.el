;;; js2r-paredit.el --- Paredit-like extensions for js2-refactor

;; Copyright (C) 2012-2014 Magnar Sveen
;; Copyright (C) 2015 Magnar Sveen and Nicolas Petton

;; Author: Magnar Sveen <magnars@gmail.com>,
;;         Nicolas Petton <nicolas@petton.fr>
;; Keywords: conveniences

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:

(require 'dash)

(defun js2r--nesting-node-p (node)
  (or (js2-function-node-p node)
      (js2-if-node-p node)
      (js2-for-node-p node)
      (js2-while-node-p node)))

(defun js2r--standalone-node-p (node)
  (or (js2-stmt-node-p node)
      (and (js2-function-node-p node)
           (eq 'FUNCTION_STATEMENT (js2-function-node-form node)))))

(defun js2r-kill ()
  "Kill a line like `kill-line' but tries to respect node boundaries.
Falls back to `kill-line' if the buffer has parse errors.

if(|foo) {bar();}       -> if() {bar();}

function foo() {|2 + 3} -> function foo() {}

// some |comment        -> // some

'this is a| string'     -> 'this is a'
"
  (interactive)
  (if js2-parsed-errors
      (progn
        (message "Buffer has parse errors. Killing the line")
        (kill-line))
    (js2r--kill-line)))

(defun js2r--kill-line ()
  "Kill a line, but respecting node boundaries."
  (let ((node (js2r--next-node)))
    (cond
     ((js2-comment-node-p node) (kill-line))
     ((js2-string-node-p node) (js2r--kill-line-in-string))
     (t (js2r--kill-line-in-sexp))))
  (js2r--cleanup-after-kill))

(defun js2r--next-node ()
  "Return the node at point, or the node after the point if the
  point is at the exact end of a node."
  (save-excursion
    (when (= (js2-node-abs-end (js2-node-at-point))
             (point))
      (forward-char 1))
    (js2-node-at-point)))

(defun js2r--cleanup-after-kill ()
  (while (looking-at ";")
    (kill-forward-chars 1)))

(defun js2r--kill-line-in-sexp ()
  "Kill a line, but only kills until the closest outer sexp on
  the current line, delimited with \")}]\". If no sexp is found
  on the current line, falls back to
  `js2r--kill-line-with-inner-sexp'."
  (condition-case error
      (let* ((beg (point))
             (end (save-excursion
                    (up-list)
                    (forward-char -1)
                    (point))))
        (if (js2-same-line end)
            (kill-region beg end)
          (js2r--kill-line-with-inner-sexp)))
    (scan-error
     (js2r--kill-line-with-inner-sexp))))

(defun js2r--kill-line-with-inner-sexp ()
  "Kill a line, but respecting inner killed sexps, ensuring that
we kill up to the end to the next inner sexp if it starts in
the current line.

If the parentheses are unbalanced, fallback to `kill-line' and
warn the user."
  (condition-case error
      (let* ((beg (point))
             (end (save-excursion
                    (forward-visible-line 1)
                    (point)))
             (beg-of-sexp (save-excursion
                            (js2r--goto-last-sexp-on-line)
                            (point)))
             (end-of-sexp (save-excursion
                            (goto-char beg-of-sexp)
                            (forward-list)
                            (point))))
        (if (js2-same-line beg-of-sexp)
            (kill-region beg (max end end-of-sexp))
          (kill-line)))
    (scan-error
     (message "Unbalanced parentheses. Killing the line.")
     (kill-line))))

(defun js2r--goto-last-sexp-on-line ()
  "Move the cursor to the opening of the last sexp on the current
line, or to the end of the line if no sexp is found."
  (let ((pos (point)))
    (down-list)
    (backward-char 1)
    (forward-list)
    (if (js2-same-line pos)
        (js2r--goto-last-sexp-on-line)
      (backward-list))))

(defun js2r--kill-line-in-string ()
  "Kill a line in a string node, respecting the node boundaries.
When at the beginning of the node, kill from outside of it."
  (let ((node (js2-node-at-point))
        (beg (point))
        (node-start (js2-node-abs-pos node))
        (node-end (js2-node-abs-end node)))
    (if (= beg node-start)
        (js2r--kill-line-in-sexp)
      (kill-region beg (1- node-end)))))

(defun js2r-forward-slurp (&optional arg)
  (interactive "p")
  (js2r--guard)
  (let* ((nesting (js2r--closest 'js2r--nesting-node-p))
         (standalone (if (js2r--standalone-node-p nesting)
                         nesting
                       (js2-node-parent-stmt nesting)))
         (next-sibling (js2-node-next-sibling standalone))
         (beg (js2-node-abs-pos next-sibling))
         (last-sibling (if (wholenump arg)
                           (let ((num arg)
                                 (iter-sibling next-sibling))
                             (while (> num 1) ;; Do next-sibling arg nbr of times
                               (setq iter-sibling (js2-node-next-sibling iter-sibling))
                               (setq num (1- num)))
                             iter-sibling)
                         next-sibling)) ;; No optional arg. Just use next-sibling
         (end (1+ (js2-node-abs-end last-sibling))) ;; include whitespace after statement
         (text (buffer-substring beg end)))
    (save-excursion
      (delete-region beg end)
      (goto-char (js2-node-abs-end nesting))
      (forward-char -1)
      (when (looking-back "{ *") (newline))
      (setq beg (point))
      (insert text)
      (indent-region beg end))))

(defun js2r-forward-barf (&optional arg)
  (interactive "p")
  (js2r--guard)
  (let* ((nesting (js2r--closest 'js2r--nesting-node-p))
         (standalone (if (js2r--standalone-node-p nesting)
                         nesting
                       (js2-node-parent-stmt nesting)))
         (standalone-end (js2-node-abs-end standalone))
         (last-child (car (last (if (js2-if-node-p nesting)
                                    (js2-scope-kids (js2r--closest 'js2-scope-p))
                                  (js2r--node-kids nesting)))))
         (first-barf-child (if (wholenump arg)
                               (let ((num arg)
                                     (iter-child last-child))
                                 (while (> num 1) ;; Do prev-sibling arg nbr of times
                                   (setq iter-child (js2-node-prev-sibling iter-child))
                                   (setq num (1- num)))
                                 iter-child)
                             last-child)); No optional arg. Just use last-child
         (last-child-beg (save-excursion
                           (goto-char (js2-node-abs-pos first-barf-child))
                           (skip-syntax-backward " ")
                           (while (looking-back "\n") (backward-char))
                           (point)))
         (last-child-end (js2-node-abs-end last-child))
         (text (buffer-substring last-child-beg last-child-end)))
    (save-excursion
      (js2r--execute-changes
       (list
        (list :beg last-child-beg :end last-child-end :contents "")
        (list :beg standalone-end :end standalone-end :contents text))))))

(provide 'js2r-paredit)
;;; js2r-paredit.el ends here
