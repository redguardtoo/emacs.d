;;; iedit-rect.el --- visible rectangle editing support based on Iedit.

;; Copyright (C) 2010, 2011, 2012 Victor Ren

;; Time-stamp: <2013-10-21 16:15:25 Victor Ren>
;; Author: Victor Ren <victorhge@gmail.com>
;; Keywords: occurrence region simultaneous rectangle refactoring
;; Version: 0.97
;; X-URL: http://www.emacswiki.org/emacs/Iedit
;; Compatibility: GNU Emacs: 22.x, 23.x, 24.x

;; This file is not part of GNU Emacs, but it is distributed under
;; the same terms as GNU Emacs.

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

;;; Commentary:

;; This package also provides rectangle support with *visible rectangle*
;; highlighting, which is similar with cua-mode rectangle support. But it is
;; lighter weight and uses iedit mechanisms.

;; The code was developed and fully tested on Gnu Emacs 24.0.93, partially
;; tested on Gnu Emacs 22. If you have any compatible problem, please let me
;; know.

;;; todo:
;; - Add restrict function back

;;; Code:

(eval-when-compile (require 'cl))
(require 'rect) ;; kill-rectangle
(require 'iedit-lib)

(defvar iedit-rectangle-mode nil) ;; Name of the minor mode

(make-variable-buffer-local 'iedit-rectangle-mode)
(or (assq 'iedit-rectangle-mode minor-mode-alist)
    (nconc minor-mode-alist
           (list '(iedit-rectangle-mode iedit-rectangle-mode))))


;;; Default key bindings:
(define-key ctl-x-r-map [return] 'iedit-rectangle-mode)

(defvar iedit-rectangle nil
  "This buffer local variable which is the rectangle geometry if
current mode is iedit-rect. Otherwise it is nil.
\(car iedit-rectangle) is the top-left corner and
\(cadr iedit-rectangle) is the bottom-right corner" )

(make-variable-buffer-local 'iedit-rectangle)

;;; Define Iedit rect mode map
(defvar iedit-rect-keymap
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map iedit-occurrence-keymap-default)
    (define-key map (kbd "M-K") 'iedit-kill-rectangle)
    map)
  "Keymap used within overlays in Iedit-rect mode.")

(or (assq 'iedit-rectangle-mode minor-mode-map-alist)
    (setq minor-mode-map-alist
          (cons (cons 'iedit-rectangle-mode iedit-lib-keymap) minor-mode-map-alist)))


;; Avoid to restore Iedit-rect mode when restoring desktop
(add-to-list 'desktop-minor-mode-handlers
             '(iedit-rectangle-mode . nil))

;;;###autoload
(defun iedit-rectangle-mode (&optional beg end)
  "Toggle Iedit-rect mode.

When Iedit-rect mode is on, a rectangle is started with visible
rectangle highlighting.  Rectangle editing support is based on
Iedit mechanism.

Commands:
\\{iedit-rect-keymap}"
  (interactive (when (iedit-region-active)
                 (list (region-beginning)
                       (region-end))))

  ;; enforce skip modification once, errors may happen to cause this to be
  ;; unset.
  (setq iedit-skip-modification-once t)
  (if iedit-rectangle-mode
      (iedit-rectangle-done)
    (iedit-barf-if-lib-active)
    (if (and beg end)
        (progn (setq mark-active nil)
               (run-hooks 'deactivate-mark-hook)
               (iedit-rectangle-start beg end))
      (error "no region available."))))

(defun iedit-rectangle-start (beg end)
  "Start Iedit mode for the region as a rectangle."
  (barf-if-buffer-read-only)
  (setq beg (copy-marker beg))
  (setq end (copy-marker end t))
  (setq iedit-occurrences-overlays nil)
  (setq iedit-initial-string-local nil)
  (setq iedit-occurrence-keymap iedit-rect-keymap)
  (save-excursion
    (let ((beg-col (progn (goto-char beg) (current-column)))
          (end-col (progn (goto-char end) (current-column))))
      (when (< end-col beg-col)
        (rotatef beg-col end-col))
      (goto-char beg)
      (while
          (progn
            (push (iedit-make-occurrence-overlay
                   (progn
                     (move-to-column beg-col t)
                     (point))
                   (progn
                     (move-to-column end-col t)
                     (point)))
                  iedit-occurrences-overlays)
            (and (< (point) end) (forward-line 1))))))
  (setq iedit-rectangle (list beg end))
  (setq iedit-rectangle-mode
        (propertize
         (concat " Iedit-rect:"
                 (number-to-string (length iedit-occurrences-overlays)))
         'face
         'font-lock-warning-face))
  (force-mode-line-update)
  (add-hook 'kbd-macro-termination-hook 'iedit-rectangle-done nil t)
  (add-hook 'change-major-mode-hook 'iedit-rectangle-done nil t)
  (add-hook 'iedit-aborting-hook 'iedit-rectangle-done nil t))

(defun iedit-rectangle-done ()
  "Exit Iedit mode.
Save the current occurrence string locally and globally.  Save
the initial string globally."
  (when iedit-buffering
      (iedit-stop-buffering))
  (iedit-cleanup)
  (setq iedit-rectangle-mode nil)
  (force-mode-line-update)
  (remove-hook 'kbd-macro-termination-hook 'iedit-rectangle-done t)
  (remove-hook 'change-major-mode-hook 'iedit-rectangle-done t)
  (remove-hook 'iedit-aborting-hook 'iedit-rectangle-done t))

(defun iedit-kill-rectangle(&optional fill)
  "Kill the rectangle.
The behavior is the same as `kill-rectangle' in rect mode."
  (interactive "*P")
  (or (and iedit-rectangle (iedit-same-column))
      (error "Not a rectangle"))
  (let ((inhibit-modification-hooks t))
    (kill-rectangle (marker-position (car iedit-rectangle))
                    (marker-position (cadr iedit-rectangle)) fill)))

(provide 'iedit-rect)

;;; iedit-rect.el ends here

;;  LocalWords:  iedit el MERCHANTABILITY kbd isearch todo ert Lindberg Tassilo
;;  LocalWords:  eval rect defgroup defcustom boolean defvar assq alist nconc
;;  LocalWords:  substring cadr keymap defconst purecopy bkm defun princ prev
;;  LocalWords:  iso lefttab backtab upcase downcase concat setq autoload arg
;;  LocalWords:  refactoring propertize cond goto nreverse progn rotatef eq elp
;;  LocalWords:  dolist pos unmatch args ov sReplace iedit's cdr quote'ed
