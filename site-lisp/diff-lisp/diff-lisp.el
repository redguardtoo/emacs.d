;;; diff-lisp.el --- diff files&strings in pure Lisp -*- lexical-binding: t -*-

;; Copyright (C) 2021-2025 Chen Bin
;;
;; Version: 0.2.1
;; Keywords: convenience patch diff vc
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: https://github.com/redguardtoo/diff-lisp
;; Package-Requires: ((emacs "27.1"))

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

;; Usage,
;;   - Select a region and run the command `diff-lisp-mark-selected-text-as-a'.
;;   - Select another region and run `diff-lisp-diff-a-and-b'.
;;   - The difference of two region is displayed in a buffer.
;;
;; API `diff-lisp-diff-strings' and `diff-lisp-diff-files' are provided.
;;
;; The diff algorithm is written in pure Lisp.
;; See "An O(ND) Difference Algorithm and its Variations", by Eugene Myers.
;;
;; Histogram will be supported soon.

;;; Code:
(require 'files)
(require 'subr-x)
(require 'diff-lisp-sdk)
(require 'diff-lisp-myers)


(defgroup diff-lisp nil
  "Create diff in purse lisp."
  :group 'convenience)

(defcustom diff-lisp-output-unified-context 3
  "Output NUM (default 3) lines of unified context."
  :group 'diff-lisp
  :type 'integer)

(defcustom diff-lisp-major-mode-function 'diff-mode
  "Function to enable major mode in diff output."
  :group 'diff-lisp
  :type 'function)

(defcustom diff-lisp-get-clipboard-function nil
  "Function to get clipboard content."
  :group 'diff-lisp
  :type 'function)

;; {{ make linter happy
(defvar evil-state)
;; }}

(defsubst diff-lisp-create-hunk (x y u v)
  "Create hunk from X Y U V."
  (list x y u v))

(defun diff-lisp-snakes-to-hunks (snakes n m)
  "Convert SNAKES to hunks.  M and N are the length of sequences to compare.
Numbers are zero-originated in the hunk."
  (let* (rlt
         (a-start 0)
         (b-start 0))

    (while snakes
      (pcase-let ((`(,x ,y ,u ,v) (car snakes)))
        (push (diff-lisp-create-hunk a-start b-start x y) rlt)
        (setq a-start u
              b-start v))
      (setq snakes (cdr snakes)))


    ;; manually add last change
    (when (or (> n a-start)
              (> m b-start))
      (push (diff-lisp-create-hunk a-start b-start n m) rlt))

    (setq rlt (nreverse rlt))

    ;; first hunk could be empty
    (when rlt
      (pcase-let ((`(,x ,y ,u ,v) (car rlt)))
        (when (and (= u 0) (= v 0)) (setq rlt (cdr rlt)))))
    rlt))

(defun diff-lisp-change-compact (hunks a b)
  "Compact HUNKS of A and B.
Similar to xdl_change_compact in git."
  ;; TODO
  hunks)

(defun diff-lisp-emit-diff (all-changes a b &optional diff-header)
  "Output ALL-CHANGES between A and B.  DIFF-HEADER is output at the beginning.
Similar to xdl_emit_diff in git."
  (with-temp-buffer
    (when all-changes
      (insert (or diff-header (format "--- a\n+++ b\n"))))
    (dolist (change all-changes)
      ;; change: (x1 y1 x2 y2 hunks)
      (let ((x1 (nth 0 change))
            (y1 (nth 1 change))
            (x2 (nth 2 change))
            (y2 (nth 3 change))
            (hunks (nth 4 change)))
        ;; header
        (insert "@@ -"
                (number-to-string (1+ x1)) "," (number-to-string (- x2 x1))
                " +" (number-to-string (1+ y1)) "," (number-to-string (- y2 y1))
                " @@\n")
        ;; push dummy and reverse once
        (setq hunks (nreverse (cons (list x2 y2 x2 y2) hunks)))

        (let ((context-start x1)
              context-end i)
          (dolist (hunk hunks)
            (let ((hx1 (nth 0 hunk))
                  (hy1 (nth 1 hunk))
                  (hx2 (nth 2 hunk))
                  (hy2 (nth 3 hunk)))
              ;; context
              (setq i context-start
                    context-end hx1)
              (while (< i context-end)
                (insert " " (aref a i) "\n")
                (setq i (1+ i)))
              (setq context-start hx2)
              ;; deletions
              (setq i hx1)
              (while (< i hx2)
                (insert "-" (aref a i) "\n")
                (setq i (1+ i)))
              ;; insertions
              (setq i hy1)
              (while (< i hy2)
                (insert "+" (aref b i) "\n")
                (setq i (1+ i))))))
        )
      )
    (buffer-string)))

;;;###autoload
(defun diff-lisp-diff-strings (s1 s2 &optional diff-header)
  "Diff string S1 and string S2.  DIFF-HEADER is output at the beginning."
  (let* ((a (vconcat (split-string s1 "\n" nil)))
         (b (vconcat (split-string s2 "\n" nil)))
         (a-length (length a))
         (b-length (length b))
         (snakes (diff-lisp-myers-do-diff (diff-lisp-line-to-hash a)
                                          a-length
                                          (diff-lisp-line-to-hash b)
                                          b-length))
         recent-change
         hunk-list
         changes)

    (dolist (hunk (diff-lisp-snakes-to-hunks snakes a-length b-length))
      (pcase-let ((`(,x1 ,y1 ,x2 ,y2) hunk))

        (setq x1 (- x1 diff-lisp-output-unified-context))
        (setq y1 (- y1 diff-lisp-output-unified-context))
        (setq x2 (+ x2 diff-lisp-output-unified-context))
        (setq y2 (+ y2 diff-lisp-output-unified-context))

        (cond
         ((and (setq recent-change (nth 0 changes))
               (or (<= x1 (nth 2 recent-change))
                   (<= y1 (nth 3 recent-change))))
          ;; If the hunk overlaps with latest change, merge it into the change
          (setf (nth 2 (nth 0 changes)) (min x2 a-length))
          (setf (nth 3 (nth 0 changes)) (min y2 b-length))
          (setq hunk-list (nth 4 recent-change))
          (push hunk hunk-list)
          (setf (nth 4 (nth 0 changes)) hunk-list))

         (t
          (push (list (max x1 0)
                      (max y1 0)
                      (min x2 a-length)
                      (min y2 b-length)
                      (list hunk))
                changes)))))

    ;; compact changes
    (setq changes (diff-lisp-change-compact (nreverse changes) a b))

    ;; output all changes
    (diff-lisp-emit-diff changes a b diff-header)))

;;;###autoload
(defun diff-lisp-diff-files (f1 f2)
  "Diff file F1 and file F2."
  (let* ((s1 (diff-lisp-file-to-string f1))
         (s2 (diff-lisp-file-to-string f2)))
    (diff-lisp-diff-strings s1 s2 (format "--- %s\n+++ %s\n" f1 f2))))

(defun diff-lisp-format-region-boundary (b e)
  "Make sure lines are selected and B is less than E."
  ; rotate b e
  (let ((tmp b))
    (setq b e
          e tmp))

  ;; select lines
  (save-excursion
    ;; Another workaround for evil-visual-line bug:
    ;; In evil-mode, if we use hotkey V or `M-x evil-visual-line` to select line,
    ;; the (line-beginning-position) of the line which is after the last selected
    ;; line is always (region-end)! Don't know why.
    (when (and (> e b)
               (save-excursion (goto-char e) (= e (line-beginning-position)))
               (boundp 'evil-state) (eq evil-state 'visual))
      (setq e (1- e)))
    (goto-char b)
    (setq b (line-beginning-position))
    (goto-char e)
    (setq e (line-end-position)))
  (list b e))

(defun diff-lisp-open-diff-output (content buffer-name)
  "Insert CONTENT into a buffer named BUFFER-NAME."
  (let ((rlt-buf (get-buffer-create buffer-name)))
    (save-current-buffer
      (switch-to-buffer-other-window rlt-buf)
      (set-buffer rlt-buf)
      (erase-buffer)
      (insert content)
      (funcall diff-lisp-major-mode-function)
      (goto-char (point-min)))))

;;;###autoload
(defun diff-lisp-mark-selected-text-as-a ()
  "Select a region to compare."
  (interactive)
  (cond
   ((region-active-p)
    (let* ((region (diff-lisp-format-region-boundary (region-beginning) (region-end)))
           (buf (get-buffer-create "*diff-lisp-A*")))
      ;; select lines
      (save-current-buffer
        (set-buffer buf)
        (erase-buffer))
      (append-to-buffer buf (nth 0 region) (nth 1 region)))
    (message "Now select the other text to compare and run `diff-lisp-diff-a-and-b'"))

   (t
    (message "Please select the text first."))))

;;;###autoload
(defun diff-lisp-diff-a-and-b ()
  "Compare current region with region from `diff-lisp-mark-selected-text-as-a'.
If no region is selected, `kill-ring' or clipboard is used instead."
  (interactive)
  (let* (diff-output
         (a (save-current-buffer
              (set-buffer (get-buffer-create "*diff-lisp-A*"))
              (buffer-string)))
         (b (cond
             ;; text from selected region
             ((region-active-p)
              (let ((region (diff-lisp-format-region-boundary (region-beginning) (region-end))))
                (buffer-substring (nth 0 region) (nth 1 region))))

             ;; text from `kill-ring' or clipboard
             (t
              (pcase (completing-read "No region is selected. Compare text from: "
                                      '("kill-ring" "clipboard"))
                ("kill-ring"
                 (car kill-ring))
                ("clipboard"
                 (when (functionp diff-lisp-get-clipboard-function)
                   (funcall diff-lisp-get-clipboard-function))))))))

    (when (and a b)
      (cond
       ((string-empty-p (setq diff-output (diff-lisp-diff-strings a b)))
        (message "Two regions are SAME!"))

       (t
        ;; show the diff output
        (diff-lisp-open-diff-output diff-output "*diff-lisp-output*"))))))

(provide 'diff-lisp)
;;; diff-lisp.el ends here
