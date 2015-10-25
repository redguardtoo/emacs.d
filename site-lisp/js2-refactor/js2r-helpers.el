;;; js2r-helpers.el --- Private helper functions for js2-refactor

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
(require 's)

(defun js2r--fix-special-modifier-combinations (key)
  (case key
    ("C-s-i" "s-TAB")
    ("C-s-m" "s-RET")
    (otherwise key)))

(defun js2r--key-pairs-with-modifier (modifier keys)
  (->> (string-to-list keys)
    (--map (js2r--fix-special-modifier-combinations
            (concat modifier (char-to-string it))))
    (s-join " ")
    (read-kbd-macro)))

(defun js2r--key-pairs-with-prefix (prefix keys)
  (read-kbd-macro (concat prefix " " keys)))

(defun js2r--guard ()
  (when js2-parsed-errors
    (error "Can't refactor while buffer has parse errors")))

(defun js2r--current-quotes-char ()
  "The char that is the current quote delimiter"
  (nth 3 (syntax-ppss)))

(defalias 'js2r--point-inside-string-p 'js2r--current-quotes-char)

(defun js2r--closest-node-where (p node)
  (if (or (null node)
          (apply p node nil))
      node
    (js2r--closest-node-where p (js2-node-parent node))))

(defun js2r--closest (p)
  (save-excursion
    (cond
     ((bolp) (back-to-indentation))
     ((looking-at ";") (forward-char -1))
     ((looking-back ";") (forward-char -2))
     ((looking-back "}") (forward-char -1)))
    (js2r--closest-node-where p (js2-node-at-point))))

(defun js2r--goto-and-delete-node (node)
  (goto-char (js2-node-abs-pos node))
  (delete-char (js2-node-len node)))


(defun js2r--path-to-root (node)
  (when node
    (cons node (js2r--path-to-root (js2-node-parent node)))))

(defun js2r--first-common-ancestor (node1 node2)
  (if (eq node1 node2)
      node1
    (let ((path1 (reverse (js2r--path-to-root node1)))
          (path2 (reverse (js2r--path-to-root node2)))
          (last-common nil))
      (while (eq (car path1) (car path2))
        (setq last-common (car path1))
        (setq path1 (cdr path1))
        (setq path2 (cdr path2)))
      last-common)))

(defun js2r--first-common-ancestor-in-region (beg end)
  (js2r--first-common-ancestor (js2-node-at-point beg)
                               (js2-node-at-point end)))

;; abstract away node type on some common property getters
(defun js2r--node-target (node)
  (cond
   ((js2-call-node-p node) (js2-call-node-target node))
   ((js2-new-node-p node) (js2-new-node-target node))
   (:else nil)))

(defun js2r--node-args (node)
  (cond
   ((js2-call-node-p node) (js2-call-node-args node))
   ((js2-new-node-p node) (js2-new-node-args node))
   (:else nil)))

(defun js2r--node-lp (node)
  (cond
   ((js2-call-node-p node) (js2-call-node-lp node))
   ((js2-new-node-p node) (js2-new-node-lp node))
   (:else nil)))

(defun js2r--node-rp (node)
  (cond
   ((js2-call-node-p node) (js2-call-node-rp node))
   ((js2-new-node-p node) (js2-new-node-rp node))
   (:else nil)))

(defun js2r--node-kids (node)
  (cond
   ((js2-function-node-p node) (js2-block-node-kids (js2-function-node-body node)))
   ((js2-if-node-p node) (js2-scope-kids (js2-if-node-then-part node)))
   ((js2-for-node-p node) (js2-block-node-kids (js2-for-node-body node)))
   ((js2-while-node-p node) (js2-block-node-kids (js2-while-node-body node)))))

;; finding expressions and arguments

(defun js2r--closest-extractable-node ()
  "Return the most appropriate node the be extracted into a variable or paramter.
Lookup the closest expression node from the point, or the closest literal node instead.
If no node is found, signal an error."
  (or (or (js2r--closest #'js2r--expression-p)
          (js2r--closest #'js2r--literal-node-p))
      (error "Cannot perform refactoring: Nothing to extract at point")))

(defun js2r--closest-stmt-node ()
  "Return the closest standalone statement node.
Special care is taken for if branch nodes: if a statement node is
part of an if branch node (like 'else if' nodes), return the
parent node."
  (let* ((node (js2-node-parent-stmt (js2-node-at-point)))
        (parent (js2-node-parent node)))
    (if (and (js2-if-node-p node)
             (js2-if-node-p parent))
        parent
      node)))

(defun js2r--argument-p (node)
  (let ((parent (js2-node-parent node)))
    (and (js2-call-node-p parent)
         (member node (js2-call-node-args parent)))))

(defun js2r--expression-p (node)
  (or (js2-call-node-p node)
      (js2r--argument-p node)
      (and (js2-prop-get-node-p node)
           (not (js2-call-node-p (js2-node-parent node))))))

(defun js2r--literal-node-p (node)
  (or (js2-object-node-p node)
      (js2-string-node-p node)
      (js2-number-node-p node)
      (js2r--boolean-node-p node)))

(defun js2r--boolean-node-p (node)
  (let* ((beg (js2-node-abs-pos node))
         (end (js2-node-abs-end node))
         (content (buffer-substring beg end)))
    (and (js2-keyword-node-p node)
         (member content '("true" "false")))))

(defun js2r--single-complete-expression-between-p (beg end)
  (let ((ancestor (js2r--first-common-ancestor-in-region beg (- end 1))))
    (and (= beg (js2-node-abs-pos ancestor))
         (= end (js2-node-abs-end ancestor)))))


;; executing a list of changes
;; ensures changes are executed from last to first

(defun js2r--by-end-descending (change1 change2)
  (> (plist-get change1 :end)
     (plist-get change2 :end)))

(defun js2r--any-overlapping-changes (sorted-changes)
  (--any?
   (let ((one (car it))
         (two (cadr it)))
     (< (plist-get one :beg)
        (plist-get two :end)))
   (-partition-in-steps 2 1 sorted-changes)))

(defun js2r--execute-changes (changes)
  (when changes
    (let ((sorted-changes (sort changes 'js2r--by-end-descending)))
      (when (js2r--any-overlapping-changes sorted-changes)
        (error "These changes overlap, cannot execute properly."))
      (let ((abs-end (set-marker (make-marker) (1+ (plist-get (car sorted-changes) :end))))
            (abs-beg (plist-get (car (last sorted-changes)) :beg)))
        (--each sorted-changes
          (goto-char (plist-get it :beg))
          (delete-char (- (plist-get it :end) (plist-get it :beg)))
          (insert (plist-get it :contents)))
        (indent-region abs-beg abs-end)
        (set-marker abs-end nil)))))

(provide 'js2r-helpers)
;;; js2-helpers.el ends here
