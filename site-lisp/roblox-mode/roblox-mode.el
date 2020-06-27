;;; roblox-mode.el --- a mode to edit Roblox Stuido rbxlx files -*- lexical-binding: t -*-

;; Copyright (C) 2020 Chen Bin <chenbin DOT sh AT gmail DOT com>
;;
;; Version: 0.0.1
;; Keywords: languages, XML
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: https://github.com/redguardtoo/roblox-mode
;; Package-Requires: ((emacs "24.4") (lua-mode "20151025"))

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

;; roblox-mode provides support for editing Roblox Studio rbxlx files,
;; "M-x roblox-edit-script" to edit embedded script in a special editor.

;;; Code:

(require 'files)

(defvar roblox-debug nil "Enable debug logger.")

;; internal variables
(defvar roblox-src--overlay nil)
(defvar roblox-src--beg-marker nil)
(defvar roblox-src--end-marker nil)
(defvar roblox--saved-temp-window-config nil)
(defvar roblox-src--header "<ProtectedString name=\"Source\"><![CDATA[")
(defvar roblox-src--footer "]]></ProtectedString>")
(defconst roblox-src--hint "-- Roblox hint: Press C-c C-c to commit change.\n")

(defun roblox-src--remove-overlay ()
  "Remove overlay from current source buffer."
  (when (overlayp roblox-src--overlay)
    (delete-overlay roblox-src--overlay)))

(defun roblox-edited-code ()
  "Get edited code."
  (save-excursion
    (goto-char (point-min))
    (search-forward roblox-src--hint (point-max) t)
    (goto-char (line-beginning-position))
    (buffer-substring-no-properties (point) (point-max))))

(defun roblox-edit-src-save ()
  "Save parent buffer with current state source-code buffer."
  (interactive)
  (set-buffer-modified-p nil)
  (let* ((edited-code (roblox-edited-code))
         (beg roblox-src--beg-marker)
         (end roblox-src--end-marker)
         (overlay roblox-src--overlay))
    (with-current-buffer (marker-buffer roblox-src--beg-marker)
      (undo-boundary)
      (goto-char beg)
      ;; Temporarily disable read-only features of OVERLAY in order to
      ;; insert new contents.
      (delete-overlay overlay)
      (delete-region beg end)
      (let* ((expecting-bol (bolp)))
        (insert edited-code)
        (when (and expecting-bol (not (bolp))) (insert "\n")))
      (save-buffer)
      (move-overlay overlay beg (point))))
  ;; `write-contents-functions' requires the function to return
  ;; a non-nil value so that other functions are not called.
  t)

(defun roblox-src-mode-configure-edit-buffer ()
  "Set up clean up functions when editing source code."
  (add-hook 'kill-buffer-hook #'roblox-src--remove-overlay nil 'local)
  (setq buffer-offer-save t)
  (setq-local write-contents-functions '(roblox-edit-src-save)))

(defvar roblox-src-mode-hook nil
  "Hook run after switching embedded script to its `lua-mode'.")

;;;###autoload
(defun roblox-restore-windows-layout ()
  "Restore windows layout before opening special editor."
  (interactive)
  (when roblox--saved-temp-window-config
    (set-window-configuration roblox--saved-temp-window-config)
    (setq roblox--saved-temp-window-config nil)))

(defun roblox-edit-src-exit ()
  "Kill current sub-editing buffer and return to source buffer."
  (interactive)
  (let* ((beg roblox-src--beg-marker)
         (end roblox-src--end-marker)
         (edit-buffer (current-buffer))
         (source-buffer (marker-buffer beg)))
    (roblox-edit-src-save)
    (unless source-buffer (error "Source buffer disappeared.  Aborting"))
    ;; Insert modified code.  Ensure it ends with a newline character.
    (kill-buffer edit-buffer)

    ;; to the beginning of the block opening line.
    (goto-char beg)

    ;; Clean up left-over markers and restore window configuration.
    (set-marker beg nil)
    (set-marker end nil)
    (roblox-restore-windows-layout)))

(defvar roblox-src-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-c") 'roblox-edit-src-exit)
    (define-key map (kbd "C-x C-s") 'roblox-edit-src-save)
    map))

(define-minor-mode roblox-src-mode
  "Minor mode for org major mode buffers generated from mail body."
  nil "RobloxSrc" nil)
(add-hook 'roblox-src-mode-hook #'roblox-src-mode-configure-edit-buffer)

(defun roblox-src--make-source-overlay (beg end)
  "Create overlay between BEG and END positions and return it."
  (let* ((overlay (make-overlay beg end)))
    (overlay-put overlay 'face 'secondary-selection)
    (let ((read-only
           (list
            (lambda (&rest _)
              (user-error
               "Cannot modify an area being edited in a dedicated buffer")))))
      (overlay-put overlay 'modification-hooks read-only)
      (overlay-put overlay 'insert-in-front-hooks read-only)
      (overlay-put overlay 'insert-behind-hooks read-only))
    overlay))

(defun roblox-src-range ()
  "Return range of script code."
  (let* (b e rlt)
    ;;;; search to extract script embedded in XML
    (save-excursion
      (setq b (search-backward roblox-src--header (point-min) t))
      (setq e (search-forward roblox-src--footer (point-max) t)))

    ;; should be valid range
    (when (and b e (< b e))
      (setq b (+ b (length roblox-src--header)))
      (setq e (- e (length roblox-src--footer)))
      (setq rlt (cons b e)))

    (when roblox-debug
      (message "roblox-src-range returns %s" rlt))

    rlt))

;;;###autoload
(defun roblox-edit-script ()
  "Call a special editor to edit embedded script."
  (interactive)
  (setq roblox--saved-temp-window-config (current-window-configuration))
  (let* ((src-range (roblox-src-range)))
    (cond
     (src-range
      (let* ((beg (copy-marker (car src-range)))
             (end (copy-marker (cdr src-range)))
             (buffer (generate-new-buffer "Roblox"))
             (overlay (roblox-src--make-source-overlay beg end))
             (text (buffer-substring-no-properties beg end)))
        (setq roblox-src--beg-marker beg)
        (setq roblox-src--end-marker end)
        (setq roblox-src--overlay overlay)

        (save-excursion
          (delete-other-windows)
          (switch-to-buffer-other-window buffer)
          (erase-buffer)
          (insert roblox-src--hint)
          (insert text)
          (goto-char (point-min))
          (lua-mode)
          (roblox-src-mode))))
     (t
      (message "No script at point.")))))

(defvar roblox-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c '") 'roblox-edit-script)
    map)
  "Keymap for `roblox-mode'.")

;;;###autoload
(define-derived-mode roblox-mode nxml-mode "RBXLX"
  "Major mode for editing Roblox Studio rbxlx files."
  )

(provide 'roblox-mode)
;;; roblox-mode.el ends here
