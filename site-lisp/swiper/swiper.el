;;; swiper.el --- Isearch with an overview. Oh, man! -*- lexical-binding: t -*-

;; Copyright (C) 2015  Free Software Foundation, Inc.

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/swiper
;; Version: 0.4.0
;; Package-Requires: ((emacs "24.1"))
;; Keywords: matching

;; This file is part of GNU Emacs.

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
;; This package gives an overview of the current regex search
;; candidates.  The search regex can be split into groups with a
;; space.  Each group is highlighted with a different face.
;;
;; It can double as a quick `regex-builder', although only single
;; lines will be matched.
;;
;; It also provides `ivy-mode': a global minor mode that uses the
;; matching back end of `swiper' for all matching on your system,
;; including file matching. You can use it in place of `ido-mode'
;; (can't have both on at once).

;;; Code:
(require 'ivy)

(defgroup swiper nil
  "`isearch' with an overview."
  :group 'matching
  :prefix "swiper-")

(defface swiper-match-face-1
  '((t (:inherit isearch-lazy-highlight-face)))
  "The background face for `swiper' matches.")

(defface swiper-match-face-2
  '((t (:inherit isearch)))
  "Face for `swiper' matches modulo 1.")

(defface swiper-match-face-3
  '((t (:inherit match)))
  "Face for `swiper' matches modulo 2.")

(defface swiper-match-face-4
  '((t (:inherit isearch-fail)))
  "Face for `swiper' matches modulo 3.")

(defface swiper-line-face
  '((t (:inherit highlight)))
  "Face for current `swiper' line.")

(defcustom swiper-faces '(swiper-match-face-1
                          swiper-match-face-2
                          swiper-match-face-3
                          swiper-match-face-4)
  "List of `swiper' faces for group matches.")

(defcustom swiper-min-highlight 2
  "Only highlight matches for regexps at least this long."
  :type 'integer)

(defvar swiper-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "M-q") 'swiper-query-replace)
    (define-key map (kbd "C-l") 'swiper-recenter-top-bottom)
    map)
  "Keymap for swiper.")

(defun swiper-query-replace ()
  "Start `query-replace' with string to replace from last search string."
  (interactive)
  (if (null (window-minibuffer-p))
      (user-error "Should only be called in the minibuffer through `swiper-map'")
    (let* ((enable-recursive-minibuffers t)
           (from (ivy--regex ivy-text))
           (to (query-replace-read-to from "Query replace" t)))
      (delete-minibuffer-contents)
      (ivy-set-action (lambda ()
                        (with-selected-window swiper--window
                          (perform-replace from to
                                           t t nil))))
      (swiper--cleanup)
      (exit-minibuffer))))

(defvar swiper--window nil
  "Store the current window.")

(defun swiper-recenter-top-bottom (&optional arg)
  "Call (`recenter-top-bottom' ARG) in `swiper--window'."
  (interactive "P")
  (with-selected-window swiper--window
    (recenter-top-bottom arg)))

(defun swiper-font-lock-ensure ()
  "Ensure the entired buffer is highlighted."
  (unless (or (derived-mode-p 'magit-mode)
              (memq major-mode '(package-menu-mode
                                 gnus-summary-mode
                                 gnus-article-mode
                                 gnus-group-mode
                                 emms-playlist-mode erc-mode
                                 org-agenda-mode
                                 dired-mode
                                 jabber-chat-mode
                                 elfeed-search-mode)))
    (unless (> (buffer-size) 100000)
      (if (fboundp 'font-lock-ensure)
          (font-lock-ensure)
        (with-no-warnings (font-lock-fontify-buffer))))))

(defvar swiper--format-spec ""
  "Store the current candidates format spec.")

(defun swiper--candidates ()
  "Return a list of this buffer lines."
  (let ((n-lines (count-lines (point-min) (point-max))))
    (unless (zerop n-lines)
      (setq swiper--format-spec
            (format "%%-%dd %%s" (1+ (floor (log n-lines 10)))))
      (let ((line-number 0)
            candidates)
        (save-excursion
          (goto-char (point-min))
          (swiper-font-lock-ensure)
          (while (< (point) (point-max))
            (push (format swiper--format-spec
                          (cl-incf line-number)
                          (buffer-substring
                           (line-beginning-position)
                           (line-end-position)))
                  candidates)
            (forward-line 1))
          (nreverse candidates))))))

(defvar swiper--opoint 1
  "The point when `swiper' starts.")

;;;###autoload
(defun swiper (&optional initial-input)
  "`isearch' with an overview.
When non-nil, INITIAL-INPUT is the initial search pattern."
  (interactive)
  (swiper--ivy initial-input))

(defvar swiper--anchor nil
  "A line number to which the search should be anchored.")

(defvar swiper--len 0
  "The last length of input for which an anchoring was made.")

(defun swiper--init ()
  "Perform initialization common to both completion methods."
  (deactivate-mark)
  (setq swiper--opoint (point))
  (setq swiper--len 0)
  (setq swiper--anchor (line-number-at-pos))
  (setq swiper--window (selected-window))
  (setq ivy--regex-function
        (cdr (assoc t ivy-re-builders-alist))))

(defun swiper--ivy (&optional initial-input)
  "`isearch' with an overview using `ivy'.
When non-nil, INITIAL-INPUT is the initial search pattern."
  (interactive)
  (unless (eq (length (help-function-arglist 'ivy-read)) 4)
    (warn "You seem to be using the outdated stand-alone \"ivy\" package.
Please remove it and update the \"swiper\" package."))
  (swiper--init)
  (let ((candidates (swiper--candidates))
        (preselect (format
                    swiper--format-spec
                    (line-number-at-pos)
                    (regexp-quote
                     (buffer-substring-no-properties
                      (line-beginning-position)
                      (line-end-position)))))
        res)
    (unwind-protect
         (setq res (ivy-read
                    (replace-regexp-in-string
                     "%s" "pattern: " swiper--format-spec)
                    candidates
                    :initial-input initial-input
                    :keymap swiper-map
                    :preselect preselect
                    :require-match t
                    :update-fn #'swiper--update-input-ivy
                    :unwind #'swiper--cleanup))
      (if (null ivy-exit)
          (goto-char swiper--opoint)
        (swiper--action res ivy-text)))))

(defun swiper--ensure-visible ()
  "Remove overlays hiding point."
  (let ((overlays (overlays-at (point)))
        ov expose)
    (while (setq ov (pop overlays))
      (if (and (invisible-p (overlay-get ov 'invisible))
               (setq expose (overlay-get ov 'isearch-open-invisible)))
          (funcall expose ov)))))

(defvar swiper--overlays nil
  "Store overlays.")

(defun swiper--cleanup ()
  "Clean up the overlays."
  (while swiper--overlays
    (delete-overlay (pop swiper--overlays)))
  (save-excursion
    (goto-char (point-min))
    (isearch-clean-overlays)))

(defun swiper--update-input-ivy ()
  "Called when `ivy' input is updated."
  (swiper--cleanup)
  (let* ((re (funcall ivy--regex-function ivy-text))
         (str ivy--current)
         (num (if (string-match "^[0-9]+" str)
                  (string-to-number (match-string 0 str))
                0)))
    (with-selected-window swiper--window
      (goto-char (point-min))
      (when (cl-plusp num)
        (goto-char (point-min))
        (forward-line (1- num))
        (isearch-range-invisible (line-beginning-position)
                                 (line-end-position))
        (unless (and (>= (point) (window-start))
                     (<= (point) (window-end swiper--window t)))
          (recenter)))
      (swiper--add-overlays re))))

(defun swiper--add-overlays (re &optional beg end)
  "Add overlays for RE regexp in visible part of the current buffer.
BEG and END, when specified, are the point bounds."
  (let ((ov (make-overlay
             (line-beginning-position)
             (1+ (line-end-position)))))
    (overlay-put ov 'face 'swiper-line-face)
    (overlay-put ov 'window swiper--window)
    (push ov swiper--overlays))
  (let* ((wh (window-height))
         (beg (or beg (save-excursion
                        (forward-line (- wh))
                        (point))))
         (end (or end (save-excursion
                        (forward-line wh)
                        (point)))))
    (when (>= (length re) swiper-min-highlight)
      (save-excursion
        (goto-char beg)
        ;; RE can become an invalid regexp
        (while (and (ignore-errors (re-search-forward re end t))
                    (> (- (match-end 0) (match-beginning 0)) 0))
          (let ((i 0))
            (while (<= i ivy--subexps)
              (when (match-beginning i)
                (let ((overlay (make-overlay (match-beginning i)
                                             (match-end i)))
                      (face
                       (cond ((zerop ivy--subexps)
                              (cadr swiper-faces))
                             ((zerop i)
                              (car swiper-faces))
                             (t
                              (nth (1+ (mod (+ i 2) (1- (length swiper-faces))))
                                   swiper-faces)))))
                  (push overlay swiper--overlays)
                  (overlay-put overlay 'face face)
                  (overlay-put overlay 'window swiper--window)
                  (overlay-put overlay 'priority i)))
              (cl-incf i))))))))

(defun swiper--action (x input)
  "Goto line X and search for INPUT."
  (if (null x)
      (user-error "No candidates")
    (goto-char (point-min))
    (forward-line (1- (read x)))
    (re-search-forward
     (funcall ivy--regex-function input) (line-end-position) t)
    (swiper--ensure-visible)
    (when (/= (point) swiper--opoint)
      (unless (and transient-mark-mode mark-active)
        (push-mark swiper--opoint t)
        (message "Mark saved where search started")))))

(provide 'swiper)

;;; swiper.el ends here
