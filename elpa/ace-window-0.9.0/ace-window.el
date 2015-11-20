;;; ace-window.el --- Quickly switch windows. -*- lexical-binding: t -*-

;; Copyright (C) 2015  Free Software Foundation, Inc.

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; Maintainer: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/ace-window
;; Package-Version: 0.9.0
;; Version: 0.8.1
;; Package-Requires: ((avy "0.2.0"))
;; Keywords: window, location

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
;; The main function, `ace-window' is meant to replace `other-window'.
;; In fact, when there are only two windows present, `other-window' is
;; called.  If there are more, each window will have its first
;; character highlighted.  Pressing that character will switch to that
;; window.
;;
;; To setup this package, just add to your .emacs:
;;
;;    (global-set-key (kbd "M-p") 'ace-window)
;;
;; replacing "M-p"  with an appropriate shortcut.
;;
;; Depending on your window usage patterns, you might want to set
;;
;;    (setq aw-keys '(?a ?s ?d ?f ?g ?h ?j ?k ?l))
;;
;; This way they are all on the home row, although the intuitive
;; ordering is lost.
;;
;; If you don't want the gray background that makes the red selection
;; characters stand out more, set this:
;;
;;    (setq aw-background nil)
;;
;; If you want to know the selection characters ahead of time, you can
;; turn on `ace-window-display-mode'.
;;
;; When prefixed with one `universal-argument', instead of switching
;; to selected window, the selected window is swapped with current one.
;;
;; When prefixed with two `universal-argument', the selected window is
;; deleted instead.

;;; Code:
(require 'avy)
(require 'ring)

;;* Customization
(defgroup ace-window nil
  "Quickly switch current window."
  :group 'convenience
  :prefix "aw-")

(defcustom aw-keys '(?1 ?2 ?3 ?4 ?5 ?6 ?7 ?8 ?9)
  "Keys for selecting window.")

(defcustom aw-scope 'global
  "The scope used by `ace-window'."
  :type '(choice
          (const :tag "global" global)
          (const :tag "frame" frame)))

(defcustom aw-ignored-buffers '("*Calc Trail*" "*LV*")
  "List of buffers to ignore when selecting window."
  :type '(repeat string))

(defcustom aw-ignore-on t
  "When t, `ace-window' will ignore `aw-ignored-buffers'.
Use M-0 `ace-window' to toggle this value."
  :type 'boolean)

(defcustom aw-ignore-current nil
  "When t, `ace-window' will ignore `selected-window'."
  :type 'boolean)

(defcustom aw-background t
  "When t, `ace-window' will dim out all buffers temporarily when used.'."
  :type 'boolean)

(defcustom aw-leading-char-style 'char
  "Style of the leading char overlay."
  :type '(choice
          (const :tag "single char" 'char)
          (const :tag "full path" 'path)))

(defcustom aw-dispatch-always nil
  "When non-nil, `ace-window' will issue a `read-char' even for one window.
This will make `ace-window' act different from `other-window' for
  one or two windows."
  :type 'boolean)

(defface aw-leading-char-face
    '((((class color)) (:foreground "red"))
      (((background dark)) (:foreground "gray100"))
      (((background light)) (:foreground "gray0"))
      (t (:foreground "gray100" :underline nil)))
  "Face for each window's leading char.")

(defface aw-background-face
  '((t (:foreground "gray40")))
  "Face for whole window background during selection.")

(defface aw-mode-line-face
    '((t (:inherit mode-line-buffer-id)))
  "Face used for displaying the ace window key in the mode-line.")

;;* Implementation
(defun aw-ignored-p (window)
  "Return t if WINDOW should be ignored."
  (or (and aw-ignore-on
           (member (buffer-name (window-buffer window))
                   aw-ignored-buffers))
      (and aw-ignore-current
           (equal window (selected-window)))))

(defun aw-window-list ()
  "Return the list of interesting windows."
  (sort
   (cl-remove-if
    (lambda (w)
      (let ((f (window-frame w))
            (b (window-buffer w)))
        (or (not (and (frame-live-p f)
                      (frame-visible-p f)))
            (string= "initial_terminal" (terminal-name f))
            (aw-ignored-p w)
            (with-current-buffer b
              (and buffer-read-only
                   (= 0 (buffer-size b)))))))
    (cl-case aw-scope
      (global
       (cl-mapcan #'window-list (frame-list)))
      (frame
       (window-list))
      (t
       (error "Invalid `aw-scope': %S" aw-scope))))
   'aw-window<))

(defvar aw-overlays-back nil
  "Hold overlays for when `aw-background' is t.")

(defvar ace-window-mode nil
  "Minor mode during the selection process.")

;; register minor mode
(or (assq 'ace-window-mode minor-mode-alist)
    (nconc minor-mode-alist
           (list '(ace-window-mode ace-window-mode))))

(defun aw--done ()
  "Clean up mode line and overlays."
  ;; mode line
  (aw-set-mode-line nil)
  ;; background
  (mapc #'delete-overlay aw-overlays-back)
  (setq aw-overlays-back nil)
  (avy--remove-leading-chars))

(defun aw--lead-overlay (path leaf)
  "Create an overlay using PATH at LEAF.
LEAF is (PT . WND)."
  (let* ((pt (car leaf))
         (wnd (cdr leaf))
         (ol (make-overlay pt (1+ pt) (window-buffer wnd)))
         (old-str (or
                   (ignore-errors
                     (with-selected-window wnd
                       (buffer-substring pt (1+ pt))))
                   ""))
         (new-str
          (concat
           (cl-case aw-leading-char-style
             (char
              (apply #'string (last path)))
             (path
              (apply #'string (reverse path)))
             (t
              (error "Bad `aw-leading-char-style': %S"
                     aw-leading-char-style)))
           (cond ((string-equal old-str "\t")
                  (make-string (1- tab-width) ?\ ))
                 ((string-equal old-str "\n")
                  "\n")
                 (t
                  (make-string
                   (max 0 (1- (string-width old-str)))
                   ?\ ))))))
    (overlay-put ol 'face 'aw-leading-char-face)
    (overlay-put ol 'window wnd)
    (overlay-put ol 'display new-str)
    (push ol avy--overlays-lead)))

(defun aw--make-backgrounds (wnd-list)
  "Create a dim background overlay for each window on WND-LIST."
  (when aw-background
    (setq aw-overlays-back
          (mapcar (lambda (w)
                    (let ((ol (make-overlay
                               (window-start w)
                               (window-end w)
                               (window-buffer w))))
                      (overlay-put ol 'face 'aw-background-face)
                      ol))
                  wnd-list))))

(define-obsolete-variable-alias
    'aw-flip-keys 'aw--flip-keys "0.1.0"
    "Use `aw-dispatch-alist' instead.")

(defvar aw-dispatch-function 'aw-dispatch-default
  "Function to call when a character not in `aw-keys' is pressed.")

(defvar aw-action nil
  "Function to call at the end of `aw-select'.")

(defun aw-set-mode-line (str)
  "Set mode line indicator to STR."
  (setq ace-window-mode str)
  (force-mode-line-update))

(defvar aw-dispatch-alist
  '((?x aw-delete-window " Ace - Delete Window")
    (?m aw-swap-window " Ace - Swap Window")
    (?n aw-flip-window)
    (?v aw-split-window-vert " Ace - Split Vert Window")
    (?b aw-split-window-horz " Ace - Split Horz Window")
    (?i delete-other-windows " Ace - Maximize Window")
    (?o delete-other-windows))
  "List of actions for `aw-dispatch-default'.")

(defun aw-dispatch-default (char)
  "Perform an action depending on CHAR."
  (let ((val (cdr (assoc char aw-dispatch-alist))))
    (if val
        (if (and (car val) (cadr val))
            (prog1 (setq aw-action (car val))
              (aw-set-mode-line (cadr val)))
          (funcall (car val))
          (throw 'done 'exit))
      (avy-handler-default char))))

(defun aw-select (mode-line &optional action)
  "Return a selected other window.
Amend MODE-LINE to the mode line for the duration of the selection."
  (setq aw-action action)
  (let ((start-window (selected-window))
        (next-window-scope (cl-case aw-scope
                             ('global 'visible)
                             ('frame 'frame)))
        (wnd-list (aw-window-list))
        window)
    (setq window
          (cond ((<= (length wnd-list) 1)
                 (when aw-dispatch-always
                   (setq aw-action
                         (unwind-protect
                              (catch 'done
                                (funcall aw-dispatch-function (read-char)))
                           (aw--done)))
                   (when (eq aw-action 'exit)
                     (setq aw-action nil)))
                 (or (car wnd-list) start-window))
                ((and (= (length wnd-list) 2) (not aw-dispatch-always))
                 (let ((wnd (next-window nil nil next-window-scope)))
                   (while (and (aw-ignored-p wnd)
                               (not (equal wnd start-window)))
                     (setq wnd (next-window wnd nil next-window-scope)))
                   wnd))
                (t
                 (let ((candidate-list
                        (mapcar (lambda (wnd)
                                  ;; can't jump if the buffer is empty
                                  (with-current-buffer (window-buffer wnd)
                                    (when (= 0 (buffer-size))
                                      (insert " ")))
                                  (cons (aw-offset wnd) wnd))
                                wnd-list)))
                   (aw--make-backgrounds wnd-list)
                   (aw-set-mode-line mode-line)
                   ;; turn off helm transient map
                   (remove-hook 'post-command-hook 'helm--maybe-update-keymap)
                   (unwind-protect
                        (let* ((avy-handler-function aw-dispatch-function)
                               (res (avy-read (avy-tree candidate-list aw-keys)
                                              #'aw--lead-overlay
                                              #'avy--remove-leading-chars)))
                          (if (eq res 'exit)
                              (setq aw-action nil)
                            (or (cdr res)
                                start-window)))
                     (aw--done))))))
    (if aw-action
        (funcall aw-action window)
      window)))

;;* Interactive
;;;###autoload
(defun ace-select-window ()
  "Ace select window."
  (interactive)
  (aw-select " Ace - Window"
             #'aw-switch-to-window))

;;;###autoload
(defun ace-delete-window ()
  "Ace delete window."
  (interactive)
  (aw-select " Ace - Delete Window"
             #'aw-delete-window))

;;;###autoload
(defun ace-swap-window ()
  "Ace swap window."
  (interactive)
  (aw-select " Ace - Swap Window"
             #'aw-swap-window))

;;;###autoload
(defun ace-maximize-window ()
  "Ace maximize window."
  (interactive)
  (aw-select " Ace - Maximize Window"
             #'delete-other-windows))

;;;###autoload
(defun ace-window (arg)
  "Select a window.
Perform an action based on ARG described below.

By default, behaves like extended `other-window'.

Prefixed with one \\[universal-argument], does a swap between the
selected window and the current window, so that the selected
buffer moves to current window (and current buffer moves to
selected window).

Prefixed with two \\[universal-argument]'s, deletes the selected
window."
  (interactive "p")
  (cl-case arg
    (0
     (setq aw-ignore-on
           (not aw-ignore-on))
     (ace-select-window))
    (4 (ace-swap-window))
    (16 (ace-delete-window))
    (t (ace-select-window))))

;;* Utility
(defun aw-window< (wnd1 wnd2)
  "Return true if WND1 is less than WND2.
This is determined by their respective window coordinates.
Windows are numbered top down, left to right."
  (let ((f1 (window-frame wnd1))
        (f2 (window-frame wnd2))
        (e1 (window-edges wnd1))
        (e2 (window-edges wnd2)))
    (cond ((string< (frame-parameter f1 'window-id)
                    (frame-parameter f2 'window-id))
           t)
          ((< (car e1) (car e2))
           t)
          ((> (car e1) (car e2))
           nil)
          ((< (cadr e1) (cadr e2))
           t))))

(defvar aw--window-ring (make-ring 10)
  "Hold the window switching history.")

(defun aw--push-window (window)
  "Store WINDOW to `aw--window-ring'."
  (when (or (zerop (ring-length aw--window-ring))
            (not (equal
                  (ring-ref aw--window-ring 0)
                  window)))
    (ring-insert aw--window-ring (selected-window))))

(defun aw--pop-window ()
  "Return the removed top of `aw--window-ring'."
  (let (res)
    (condition-case nil
        (while (or (not (window-live-p
                         (setq res (ring-remove aw--window-ring 0))))
                   (equal res (selected-window))))
      (error
       (if (= (length (aw-window-list)) 2)
           (progn
             (other-window 1)
             (setq res (selected-window)))
         (error "No previous windows stored"))))
    res))

(defun aw-switch-to-window (window)
  "Switch to the window WINDOW."
  (let ((frame (window-frame window)))
    (when (and (frame-live-p frame)
               (not (eq frame (selected-frame))))
      (select-frame-set-input-focus frame))
    (if (window-live-p window)
        (progn
          (aw--push-window (selected-window))
          (select-window window))
      (error "Got a dead window %S" window))))

(defun aw-flip-window ()
  "Switch to the window you were previously in."
  (interactive)
  (aw-switch-to-window (aw--pop-window)))

(defun aw-delete-window (window)
  "Delete window WINDOW."
  (let ((frame (window-frame window)))
    (when (and (frame-live-p frame)
               (not (eq frame (selected-frame))))
      (select-frame-set-input-focus (window-frame window)))
    (if (= 1 (length (window-list)))
        (delete-frame frame)
      (if (window-live-p window)
          (delete-window window)
        (error "Got a dead window %S" window)))))

(defun aw-swap-window (window)
  "Swap buffers of current window and WINDOW."
  (cl-labels ((swap-windows (window1 window2)
                "Swap the buffers of WINDOW1 and WINDOW2."
                (let ((buffer1 (window-buffer window1))
                      (buffer2 (window-buffer window2)))
                  (set-window-buffer window1 buffer2)
                  (set-window-buffer window2 buffer1)
                  (select-window window2))))
    (let ((frame (window-frame window))
          (this-window (selected-window)))
      (when (and (frame-live-p frame)
                 (not (eq frame (selected-frame))))
        (select-frame-set-input-focus (window-frame window)))
      (when (and (window-live-p window)
                 (not (eq window this-window)))
        (aw--push-window this-window)
        (swap-windows this-window window)))))

(defun aw-split-window-vert (window)
  "Split WINDOW vertically."
  (select-window window)
  (split-window-vertically))

(defun aw-split-window-horz (window)
  "Split WINDOW horizontally."
  (select-window window)
  (split-window-horizontally))

(defun aw-offset (window)
  "Return point in WINDOW that's closest to top left corner.
The point is writable, i.e. it's not part of space after newline."
  (let ((h (window-hscroll window))
        (beg (window-start window))
        (end (window-end window))
        (inhibit-field-text-motion t))
    (with-current-buffer
        (window-buffer window)
      (save-excursion
        (goto-char beg)
        (while (and (< (point) end)
                    (< (- (line-end-position)
                          (line-beginning-position))
                       h))
          (forward-line))
        (+ (point) h)))))

;;* Mode line
;;;###autoload
(define-minor-mode ace-window-display-mode
    "Minor mode for showing the ace window key in the mode line."
  :global t
  (if ace-window-display-mode
      (progn
        (aw-update)
        (set-default
         'mode-line-format
         `((ace-window-display-mode
            (:eval (window-parameter (selected-window) 'ace-window-path)))
           ,@(assq-delete-all
              'ace-window-display-mode
              (default-value 'mode-line-format))))
        (force-mode-line-update t)
        (add-hook 'window-configuration-change-hook 'aw-update))
    (set-default
     'mode-line-format
     (assq-delete-all
      'ace-window-display-mode
      (default-value 'mode-line-format)))
    (remove-hook 'window-configuration-change-hook 'aw-update)))

(defun aw-update ()
  "Update ace-window-path window parameter for all windows."
  (avy-traverse
   (avy-tree (aw-window-list) aw-keys)
   (lambda (path leaf)
     (set-window-parameter
      leaf 'ace-window-path
      (propertize
       (apply #'string (reverse path))
       'face 'aw-mode-line-face)))))

(provide 'ace-window)

;;; ace-window.el ends here
