;;; writeroom-mode.el --- Minor mode for distraction-free writing  -*- lexical-binding: t -*-

;; Copyright (c) 2012-2014 Joost Kremers

;; Author: Joost Kremers <joostkremers@fastmail.fm>
;; Maintainer: Joost Kremers <joostkremers@fastmail.fm>
;; Created: 11 July 2012
;; Package-Requires: ((emacs "24.1") (visual-fill-column "1.4"))
;; Version: 2.9
;; Keywords: text

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;;
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in the
;;    documentation and/or other materials provided with the distribution.
;; 3. The name of the author may not be used to endorse or promote products
;;    derived from this software without specific prior written permission.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
;; IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
;; OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
;; IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
;; INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
;; NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES ; LOSS OF USE,
;; DATA, OR PROFITS ; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
;; THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:

;; writeroom-mode is a minor mode for Emacs that implements a
;; distraction-free writing mode similar to the famous Writeroom editor for
;; OS X. writeroom-mode is meant for GNU Emacs 24 and isn't tested on older
;; versions.
;;
;; See the README or info manual for usage instructions.
;;
;;; Code:

(require 'visual-fill-column)

(defvar writeroom--buffers nil
  "List of buffers in which `writeroom-mode' is activated.")

(defvar writeroom--local-variables '(mode-line-format
                                     header-line-format
                                     line-spacing)
  "Local variables whose values need to be saved when `writeroom-mode' is activated.")

(defvar-local writeroom--saved-data nil
  "Buffer-local data to be stored when `writeroom-mode' is
  activated, so that the settings can be restored when
  `writeroom-mode' is deactivated.")

(defvar-local writeroom--mode-line-showing nil
  "Flag indicating whether the original mode line is displayed.")

(defvar-local writeroom--saved-visual-fill-column nil
  "Status of `visual-fill-column-mode' before activating `writeroom-mode'.")

(defvar writeroom--saved-window-config nil
  "Window configuration active before `writeroom-mode' is activated.")

(defgroup writeroom nil "Minor mode for distraction-free writing."
  :group 'wp
  :prefix "writeroom-")

(defcustom writeroom-width 80
  "Width of the writeroom writing area."
  :group 'writeroom
  :type '(choice (integer :label "Absolute width:")
                 (float :label "Relative width:" :value 0.5)))

(defcustom writeroom-mode-line nil
  "The mode line format to use.
By default, this option is set to nil, which disables the mode
line when `writeroom-mode' is activated. By setting the option to
t, the standard mode line is retained. Alternatively, it is
possible to specify a special mode line for `writeroom-mode'
buffers. If this option is chosen, the default is to only show
the buffer's modification status and the buffer name, but the
format can be customized. See the documentation for the variable
`mode-line-format' for further information."
  :group 'writeroom
  :type '(choice (const :tag "Disable the mode line" nil)
                 (const :tag "Use default mode line" t)
                 (sexp :tag "Customize mode line"
                       :value ("   " mode-line-modified "   " mode-line-buffer-identification))))

(make-obsolete-variable 'writeroom-disable-fringe
                        "The variable `writeroom-disable-fringe' is no longer used."
                        "`writeroom-mode' version 2.9")

(defcustom writeroom-maximize-window t
  "Whether to maximize the current window in its frame.
When set to t, `writeroom-mode' deletes all other windows in
the current frame."
  :group 'writeroom
  :type '(choice (const :tag "Maximize window" t)
                 (const :tag "Do not maximize window" nil)))

(defcustom writeroom-fullscreen-effect 'fullboth
  "Effect applied when enabling fullscreen.
The value can be `fullboth', in which case fullscreen is
activated, or `maximized', in which case the relevant frame is
maximized but window decorations are still available."
  :group 'writeroom
  :type '(choice (const :tag "Fullscreen" fullboth)
                 (const :tag "Maximized" maximized)))

(defcustom writeroom-border-width 30
  "Width in pixels of the border.
To use this option, select the option \"Add border\" in `Global
Effects'. This adds a border around the text area."
  :group 'writeroom
  :type '(integer :tag "Border width"))

(defcustom writeroom-fringes-outside-margins t
  "If set, place the fringes outside the modeline."
  :group 'writeroom
  :type '(choice (const :tag "Place fringes outside margins" t)
                 (const :tag "Place fringes inside margins" nil)))

(defcustom writeroom-major-modes '(text-mode)
  "List of major modes in which writeroom-mode is activated.
This option is only relevant when activating `writeroom-mode'
with `global-writeroom-mode'."
  :group 'writeroom
  :type '(repeat (symbol :tag "Major mode")))

(defcustom writeroom-restore-window-config nil
  "If set, restore window configuration after disabling `writeroom-mode'.
Setting this option makes sense primarily if `writeroom-mode' is
used in one buffer only. The window configuration that is stored
is the one that exists when `writeroom-mode' is first called, and
it is restored when `writeroom-mode' is deactivated in the last
buffer."
  :group 'writeroom
  :type '(choice (const :tag "Do not restore window configuration" nil)
                 (const :tag "Restore window configuration" t)))

(defcustom writeroom-extra-line-spacing nil
  "Additional line spacing for `writeroom-mode`"
  :group 'writeroom
  :type '(choice (const :tag "Do not add extra line spacing" :value nil)
                 (integer :tag "Absolute height" :value 5)
                 (float :tag "Relative height" :value 0.8)))

(defcustom writeroom-global-effects '(writeroom-toggle-fullscreen
                                      writeroom-toggle-alpha
                                      writeroom-toggle-vertical-scroll-bars
                                      writeroom-toggle-menu-bar-lines
                                      writeroom-toggle-tool-bar-lines)
  "List of global effects for `writeroom-mode'.
These effects are enabled when `writeroom-mode' is activated in
the first buffer and disabled when it is deactivated in the last
buffer."
  :group 'writeroom
  :type '(set (const :tag "Fullscreen" writeroom-toggle-fullscreen)
              (const :tag "Disable transparency" writeroom-toggle-alpha)
              (const :tag "Disable menu bar" writeroom-toggle-menu-bar-lines)
              (const :tag "Disable tool bar" writeroom-toggle-tool-bar-lines)
              (const :tag "Disable scroll bar" writeroom-toggle-vertical-scroll-bars)
              (const :tag "Add border" writeroom-toggle-internal-border-width)
              (repeat :inline t :tag "Custom effects" function)))

(define-obsolete-variable-alias 'writeroom-global-functions 'writeroom-global-effects "`writeroom-mode' version 2.0")

(defmacro define-writeroom-global-effect (fp value)
  "Define a global effect.
The effect is activated by setting frame parameter FP to VALUE.
FP should be an unquoted symbol, the name of a frame parameter;
VALUE must be quoted (unless it is a string or a number, of
course). It can also be an unquoted symbol, in which case it
should be the name of a global variable whose value is then
assigned to FP.

This macro defines a function `writeroom-toggle-<FP>' that takes
one argument and activates the effect if this argument is t and
deactivates it when it is nil. When the effect is activated,
the original value of frame parameter FP is stored in a frame
parameter `writeroom-<FP>', so that it can be restored when the
effect is deactivated."
  (declare (indent defun))
  (let ((wfp (intern (format "writeroom-%s" fp))))
    `(fset (quote ,(intern (format "writeroom-toggle-%s" fp)))
           (lambda (arg)
             (if arg
                 (progn
                   (set-frame-parameter nil (quote ,wfp) (frame-parameter nil (quote ,fp)))
                   (set-frame-parameter nil (quote ,fp) ,value))
               (set-frame-parameter nil (quote ,fp) (frame-parameter nil (quote ,wfp)))
               (set-frame-parameter nil (quote ,wfp) nil))))))

(define-writeroom-global-effect fullscreen writeroom-fullscreen-effect)
(define-writeroom-global-effect alpha '(100 100))
(define-writeroom-global-effect vertical-scroll-bars nil)
(define-writeroom-global-effect menu-bar-lines 0)
(define-writeroom-global-effect tool-bar-lines 0)
(define-writeroom-global-effect internal-border-width writeroom-border-width)

(defun turn-on-writeroom-mode ()
  "Turn on `writeroom-mode'.
This function activates `writeroom-mode' in a buffer if that
buffer's major mode is a member of `writeroom-major-modes'."
  (if (memq major-mode writeroom-major-modes)
      (writeroom-mode 1)))

(defvar writeroom-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "s-?") #'writeroom-toggle-mode-line)
    map)
  "Keymap for writeroom-mode.")

;;;###autoload
(define-minor-mode writeroom-mode
  "Minor mode for distraction-free writing."
  :init-value nil :lighter nil :global nil
  (if writeroom-mode
      (writeroom--enable)
    (writeroom--disable)))

;;;###autoload
(define-globalized-minor-mode global-writeroom-mode writeroom-mode turn-on-writeroom-mode
  :require 'writeroom-mode
  :group 'writeroom)

(defun writeroom--kill-buffer-function ()
  "Disable `writeroom-mode' before killing a buffer, if necessary.
This function is for use in `kill-buffer-hook'. It checks whether
`writeroom-mode' is enabled in the buffer to be killed and
adjusts `writeroom--buffers' and the global effects accordingly."
  (when writeroom-mode
    (setq writeroom--buffers (delq (current-buffer) writeroom--buffers))
    (when (not writeroom--buffers)
      (writeroom--activate-global-effects nil))))

(add-hook 'kill-buffer-hook #'writeroom--kill-buffer-function)

(defun writeroom--activate-global-effects (arg)
  "Activate or deactivate global effects.
The effects are activated if ARG is non-nil, and deactivated
otherwise."
  (mapc (lambda (fn)
          (funcall fn arg))
        writeroom-global-effects))

(defun writeroom-toggle-mode-line ()
  "Toggle display of the original mode line in the header line."
  (interactive)
  (cond
   ((not writeroom--mode-line-showing)
    (setq header-line-format (or (cdr (assq 'mode-line-format writeroom--saved-data))
                                 (default-value 'mode-line-format)))
    (setq writeroom--mode-line-showing t))
   (writeroom--mode-line-showing
    (setq header-line-format (cdr (assq 'header-line-format writeroom--saved-data)))
    (setq writeroom--mode-line-showing nil)))
  (set-window-buffer (selected-window) (current-buffer) 'keep-margins))

(defun writeroom--enable ()
  "Set up writeroom-mode for the current buffer.
This function also runs the functions in
`writeroom-global-effects' if the current buffer is the first
buffer in which `writeroom-mode' is activated."
  ;; save buffer-local variables, if they have a buffer-local binding
  (setq writeroom--saved-data (mapcar (lambda (sym)
                                        (if (local-variable-p sym)
                                            (cons sym (buffer-local-value sym (current-buffer)))
                                          sym))
                                      writeroom--local-variables))
  (setq writeroom--saved-visual-fill-column visual-fill-column-mode)

  (when (not writeroom--buffers)
    (writeroom--activate-global-effects t)
    (if writeroom-restore-window-config
        (setq writeroom--saved-window-config (current-window-configuration))))
  (add-to-list 'writeroom--buffers (current-buffer))

  (when writeroom-maximize-window
    (delete-other-windows))

  (when writeroom-extra-line-spacing
    (setq line-spacing writeroom-extra-line-spacing))

  (unless (eq writeroom-mode-line t) ; if t, use standard mode line
    (setq mode-line-format writeroom-mode-line))

  (setq visual-fill-column-width (if (floatp writeroom-width)
                                     (truncate (* (window-total-width) writeroom-width))
                                   writeroom-width)
        visual-fill-column-center-text t
        visual-fill-column-fringes-outside-margins writeroom-fringes-outside-margins)
  (visual-fill-column-mode 1)

  ;; if the current buffer is displayed in some window, the windows'
  ;; margins and fringes must be adjusted.
  (mapc (lambda (w)
          (with-selected-window w
            (visual-fill-column--adjust-window)))
        (get-buffer-window-list (current-buffer) nil)))

(defun writeroom--disable ()
  "Reset the current buffer to its normal appearance.
This function also runs the functions in
`writeroom-global-effects' to undo their effects if
`writeroom-mode' is deactivated in the last buffer in which it
was active."
  ;; disable visual-fill-column-mode
  (visual-fill-column-mode -1)
  (kill-local-variable 'visual-fill-column-width)
  (kill-local-variable 'visual-fill-column-center-text)
  (kill-local-variable 'visual-fill-column-fringes-outside-margins)

  ;; restore global effects if necessary
  (setq writeroom--buffers (delq (current-buffer) writeroom--buffers))
  (when (not writeroom--buffers)
    (writeroom--activate-global-effects nil)
    (if writeroom-restore-window-config
        (set-window-configuration writeroom--saved-window-config)))

  ;; restore local variables
  (mapc (lambda (val)
          (if (symbolp val)
              (kill-local-variable val)
            (set (car val) (cdr val))))
        writeroom--saved-data)

  ;; if the current buffer is displayed in some window, the windows'
  ;; margins and fringes must be adjusted.
  (mapc (lambda (w)
          (with-selected-window w
            (set-window-margins (selected-window) 0 0)
            (set-window-fringes (selected-window) nil)))
        (get-buffer-window-list (current-buffer) nil))

  ;; reenable `visual-fill-colummn-mode' with original settings if it was
  ;; active before activating `writeroom-mode'.
  (if writeroom--saved-visual-fill-column
      (visual-fill-column-mode 1)))

(provide 'writeroom-mode)

;;; writeroom-mode.el ends here
