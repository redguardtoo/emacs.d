;;; hl-sexp.el --- highlight the current sexp

;; Copyright (C) 1998, 2000, 2001 Free Software Foundation, Inc.
;; Copyright (C) 2002 Edward O'Connor <ted@oconnor.cx>

;; Author:  Edward O'Connor <ted@oconnor.cx>
;; Created: 2002-03-03
;; Keywords: faces, frames, emulation
;; Package-Version: 1.0.0
;; Version: 1.0.0

;; This file is NOT part of GNU Emacs, but is very much a derived work
;; of hl-line.el, which is a part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; A cheap hack of hl-line.el to highlight the thingy at point instead
;; of the line at point. Sort of inspired by a post by Kent Pitman to
;; CLL in which he ranted about font-locking. You can find the latest
;; version here: <URL:http://oconnor.cx/elisp/hl-sexp.el>

;; An overlay is used, active only on the selected window.  Hooks are
;; added to `pre-command-hook' and `post-command-hook' to activate and
;; deactivate (by deleting) the overlay.  `hl-sexp-unhighlight', on
;; `pre-command-hook', deactivates it unconditionally in case the
;; command changes the selected window.  (It does so rather than
;; keeping track of changes in the selected window).
;; `hl-sexp-highlight', on `post-command-hook', activates it again
;; across the window width.

;; You could make variable `hl-sexp-mode' buffer-local to avoid
;; highlighting specific buffers.

;;; Code:

(require 'thingatpt)

(defgroup hl-sexp nil
  "Highlight the current sexp."
  :version "21.1"
  :group 'editing)

(defface hl-sexp-face
  '((((type tty))
     (:bold t))
    (((class color) (background light))
     (:background "lightgray"))
    (((class color) (background dark))
     (:background "gray10"))
    (t (:bold t)))
  "Face used to fontify the sexp you're looking at."
  :group 'faces)

(defvar hl-sexp-overlay nil)

(defun hl-sexp-highlight ()
  "Active the Hl-Sexp overlay on the current sexp in the current window.
\(Unless it's a minibuffer window.)"
  (when hl-sexp-mode			; Could be made buffer-local.
    (unless (window-minibuffer-p (selected-window)) ; silly in minibuffer
      (unless hl-sexp-overlay
	(setq hl-sexp-overlay (make-overlay 1 1)) ; to be moved
	(overlay-put hl-sexp-overlay 'face 'hl-sexp-face))
      (overlay-put hl-sexp-overlay 'window (selected-window))
      (save-excursion
        (condition-case nil
            (backward-up-list 1)
          (error nil))
        (let ((bounds (bounds-of-thing-at-point 'sexp)))
        (when bounds
          (move-overlay hl-sexp-overlay
                        (car bounds) (cdr bounds)
                        (current-buffer))))))))

(defun hl-sexp-unhighlight ()
  "Deactivate the Hl-Sexp overlay on the current sexp in the current window."
  (if hl-sexp-overlay
      (delete-overlay hl-sexp-overlay)))

;;;###autoload
(define-minor-mode hl-sexp-mode
  "Minor mode to highlight the sexp about point in the current window.
With ARG, turn Hl-Sexp mode on if ARG is positive, off otherwise.
Uses functions `hl-sexp-unhighlight' and `hl-sexp-highlight' on
`pre-command-hook' and `post-command-hook'."
  nil nil nil
  (if hl-sexp-mode
      (progn
	(add-hook 'pre-command-hook #'hl-sexp-unhighlight)
	(add-hook 'post-command-hook #'hl-sexp-highlight))
    (hl-sexp-unhighlight)
    (remove-hook 'pre-command-hook #'hl-sexp-unhighlight)
    (remove-hook 'post-command-hook #'hl-sexp-highlight)))

;;;###autoload
(easy-mmode-define-global-mode
 global-hl-sexp-mode hl-sexp-mode hl-sexp-mode
 :group 'hl-sexp)

(provide 'hl-sexp)

;;; hl-sexp.el ends here
