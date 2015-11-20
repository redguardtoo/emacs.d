;;; company-template.el

;; Copyright (C) 2009, 2010, 2014 Free Software Foundation, Inc.

;; Author: Nikolaj Schumacher

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:

(require 'cl-lib)

(defface company-template-field
  '((((background dark)) (:background "yellow" :foreground "black"))
    (((background light)) (:background "orange" :foreground "black")))
  "Face used for editable text in template fields."
  :group 'company)

(defvar company-template-nav-map
  (let ((keymap (make-sparse-keymap)))
    (define-key keymap [tab] 'company-template-forward-field)
    (define-key keymap (kbd "TAB") 'company-template-forward-field)
    keymap))

(defvar-local company-template--buffer-templates nil)

;; interactive ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun company-template-templates-at (pos)
  (let (os)
    (dolist (o (overlays-at pos))
      ;; FIXME: Always return the whole list of templates?
      ;; We remove templates not at point after every command.
      (when (memq o company-template--buffer-templates)
        (push o os)))
    os))

(defun company-template-move-to-first (templ)
  (interactive)
  (goto-char (overlay-start templ))
  (company-template-forward-field))

(defun company-template-forward-field ()
  (interactive)
  (let* ((start (point))
         (templates (company-template-templates-at (point)))
         (minimum (apply 'max (mapcar 'overlay-end templates)))
         (fields (cl-loop for templ in templates
                          append (overlay-get templ 'company-template-fields))))
    (dolist (pos (mapcar 'overlay-start fields))
      (and pos
           (> pos (point))
           (< pos minimum)
           (setq minimum pos)))
    (push-mark)
    (goto-char minimum)
    (company-template-remove-field (company-template-field-at start))))

(defun company-template-field-at (&optional point)
  (cl-loop for ovl in (overlays-at (or point (point)))
           when (overlay-get ovl 'company-template-parent)
           return ovl))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun company-template-declare-template (beg end)
  (let ((ov (make-overlay beg end)))
    ;; (overlay-put ov 'face 'highlight)
    (overlay-put ov 'keymap company-template-nav-map)
    (overlay-put ov 'priority 101)
    (overlay-put ov 'evaporate t)
    (push ov company-template--buffer-templates)
    (add-hook 'post-command-hook 'company-template-post-command nil t)
    ov))

(defun company-template-remove-template (templ)
  (mapc 'company-template-remove-field
        (overlay-get templ 'company-template-fields))
  (setq company-template--buffer-templates
        (delq templ company-template--buffer-templates))
  (delete-overlay templ))

(defun company-template-add-field (templ pos text &optional display)
  "Add new field to template TEMPL at POS, inserting TEXT.
When DISPLAY is non-nil, set the respective property on the overlay.
Leave point at the end of the field."
  (cl-assert templ)
  (goto-char pos)
  (insert text)
  (when (> (point) (overlay-end templ))
    (move-overlay templ (overlay-start templ) (point)))
  (let ((ov (make-overlay pos (+ pos (length text))))
        (siblings (overlay-get templ 'company-template-fields)))
    ;; (overlay-put ov 'evaporate t)
    (overlay-put ov 'intangible t)
    (overlay-put ov 'face 'company-template-field)
    (when display
      (overlay-put ov 'display display))
    (overlay-put ov 'company-template-parent templ)
    (overlay-put ov 'insert-in-front-hooks '(company-template-insert-hook))
    (push ov siblings)
    (overlay-put templ 'company-template-fields siblings)))

(defun company-template-remove-field (ovl &optional clear)
  (when (overlayp ovl)
    (when (overlay-buffer ovl)
      (when clear
        (delete-region (overlay-start ovl) (overlay-end ovl)))
      (delete-overlay ovl))
    (let* ((templ (overlay-get ovl 'company-template-parent))
           (siblings (overlay-get templ 'company-template-fields)))
      (setq siblings (delq ovl siblings))
      (overlay-put templ 'company-template-fields siblings))))

(defun company-template-clean-up (&optional pos)
  "Clean up all templates that don't contain POS."
  (let ((local-ovs (overlays-at (or pos (point)))))
    (dolist (templ company-template--buffer-templates)
      (unless (memq templ local-ovs)
        (company-template-remove-template templ)))))

;; hooks ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun company-template-insert-hook (ovl after-p &rest _ignore)
  "Called when a snippet input prompt is modified."
  (unless after-p
    (company-template-remove-field ovl t)))

(defun company-template-post-command ()
  (company-template-clean-up)
  (unless company-template--buffer-templates
    (remove-hook 'post-command-hook 'company-template-post-command t)))

;; common ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun company-template-c-like-templatify (call)
  (let* ((end (point-marker))
         (beg (- (point) (length call)))
         (cnt 0)
         (templ (company-template-declare-template beg end))
         paren-open paren-close)
    (with-syntax-table (make-syntax-table (syntax-table))
      (modify-syntax-entry ?< "(")
      (modify-syntax-entry ?> ")")
      (when (search-backward ")" beg t)
        (setq paren-close (point-marker))
        (forward-char 1)
        (delete-region (point) end)
        (backward-sexp)
        (forward-char 1)
        (setq paren-open (point-marker)))
      (when (search-backward ">" beg t)
        (let ((angle-close (point-marker)))
          (forward-char 1)
          (backward-sexp)
          (forward-char)
          (setq cnt (company-template--c-like-args templ angle-close
                                                   cnt))))
      (when paren-open
        (goto-char paren-open)
        (company-template--c-like-args templ paren-close cnt)))
    (if (overlay-get templ 'company-template-fields)
        (company-template-move-to-first templ)
      (company-template-remove-template templ)
      (goto-char end))))

(defun company-template--c-like-args (templ end counter)
  (let ((last-pos (point)))
    (while (re-search-forward "\\([^,]+\\),?" end 'move)
      (when (zerop (car (parse-partial-sexp last-pos (point))))
        (let ((sig (buffer-substring-no-properties last-pos (match-end 1))))
          (save-excursion
            (company-template-add-field templ last-pos
                                        (format "arg%d" counter) sig)
            (delete-region (point) (+ (point) (length sig))))
          (skip-chars-forward " ")
          (setq last-pos (point))
          (cl-incf counter)))))
  counter)

(provide 'company-template)
;;; company-template.el ends here
