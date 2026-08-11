;;; xclip.el --- Copy&paste GUI clipboard from text terminal  -*- lexical-binding:t -*-

;; Copyright (C) 2007-2024  Free Software Foundation, Inc.

;; Author: Leo Liu <sdl.web@gmail.com>
;; Keywords: convenience, tools
;; Created: 2007-12-30
;; Version: 1.11.1

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This package allows Emacs to copy to and paste from the GUI clipboard
;; when running in text terminal.
;;
;; It can use external command-line tools for that, which you may need
;; to install in order for the package to work.
;; More specifically, it can use the following tools:
;; - Under X11: `xclip' or `xsel' (https://xclip.sourceforge.net and
;;   https://www.vergenet.net/~conrad/software/xsel/ respectively).
;; - MacOS: `pbpaste/pbcopy'
;; - Cygwin: `getclip/putclip'
;; - Under Wayland: `wl-clipboard' (https://github.com/bugaevc/wl-clipboard)
;; - Termux: `termux-clipboard-get/set'
;; - Emacs: It can also use Emacs's built-in GUI support to talk to the GUI.
;;   This requires an Emacs built with GUI support.
;;   It uses `make-frame-on-display' which has been tested to work under X11,
;;   but it's not known whether it works under MacOS or Windows.
;;
;; To use, just add (xclip-mode 1) to your ~/.emacs or do `M-x clip-mode'
;; after which the usual kill/yank commands will use the GUI selections
;; according to `select-enable-clipboard/primary'.

;; An alternative package for use under X11 is
;; [Gpastel](https://gitlab.petton.fr/DamienCassou/gpastel), which uses
;; [GPaste](https://github.com/Keruspe/GPaste/) rather than Xclip and hooks
;; into Emacs in a different way.  AFAICT it currently only supports
;; copy/pasting from an external application to Emacs and not from Emacs to
;; another application (for which it relies on the default code).

;;; News:

;; Since 1.11:
;;
;; - Bugfixes only so far.
;;
;; Changes in 1.11:
;;
;; - Add tentative WSL support
;;
;; Changes in 1.9:
;;
;; - Add support for Termux and Wayland.
;;
;; Changes in 1.7:
;;
;; - Add `emacs' method to use built-in GUI code i.s.o external executable.

;;; Code:

(defgroup xclip ()
  "Copy&paste GUI clipboard from text terminal."
  :group 'killing)

(defcustom xclip-select-enable-clipboard t
  "Non-nil means cutting and pasting uses the clipboard.
This is in addition to, but in preference to, the primary selection."
  :type 'boolean)
(make-obsolete 'xclip-select-enable-clipboard
               'select-enable-clipboard "Emacs-25")

(defvar xclip-use-pbcopy&paste (and (eq system-type 'darwin)
                                    (executable-find "pbcopy")
                                    t)
  "Non-nil means using pbcopy and pbpaste instead of xclip.
If non-nil `xclip-program' is ignored.")
(make-obsolete 'xclip-use-pbcopy&paste 'xclip-method "xclip-1.5")

(defcustom xclip-method
  (or
   (and xclip-use-pbcopy&paste 'pbpaste)
   (and (eq system-type 'cygwin) (executable-find "getclip") 'getclip)
   (and (executable-find "xclip") 'xclip)
   (and (executable-find "xsel") 'xsel)
   (and (executable-find "wl-copy") 'wl-copy) ;github.com/bugaevc/wl-clipboard
   (and (executable-find "termux-clipboard-get") 'termux-clipboard-get)
   (and (fboundp 'x-create-frame) (getenv "DISPLAY") 'emacs)
   (and (eq system-type 'gnu/linux) ;FIXME: How do we detect WSL?
        (executable-find "powershell.exe") 'powershell)
   'xclip)
  "Method to use to access the GUI's clipboard.
Can be one of `pbpaste' for MacOS, `xclip' or `xsel' for X11,
and `getclip' under Cygwin, or `emacs' to use Emacs's GUI code for that."
  :type '(choice
          (const :tag "MacOS: pbcopy/pbpaste" pbpaste)
          (const :tag "Cygwin: getclip/putclip" getclip)
          (const :tag "X11: xclip" xclip)
          (const :tag "X11: xsel" xsel)
          (const :tag "Wayland: wl-copy" wl-copy)
          (const :tag "Termux: termux-clipboard-get/set" termux-clipboard-get)
          (const :tag "WSL: clip.exe/powershell.exe" powershell)
          (const :tag "X11: Emacs" emacs)))

(defcustom xclip-program (symbol-name xclip-method)
  "Name of the clipboard access command."
  :type 'string)

;;;; Core functions.

(defvar xclip-mode)

(defun xclip-set-selection (type data)
  "TYPE is a symbol: primary, secondary and clipboard.
TYPE and DATA are the same as for `gui-set-selection'."
  (if (eq xclip-method 'emacs)
      (with-selected-frame (xclip--hidden-frame)
        (let ((xclip-mode nil)) ;;Just out of paranoia.
          (gui-backend-set-selection type data)))
    (let* ((process-connection-type nil)
           (proc
            (pcase xclip-method
              (`emacs nil)
              (`pbpaste
               (when (memq type '(clipboard CLIPBOARD))
                 (start-process
                  "pbcopy" nil
                  (replace-regexp-in-string "\\(.*\\)pbpaste" "\\1pbcopy"
                                            xclip-program 'fixedcase))))
              (`powershell
               (when (memq type '(clipboard CLIPBOARD))
                 (start-process "clip.exe" nil "clip.exe")))
              (`getclip
               (when (memq type '(clipboard CLIPBOARD))
                 (start-process
                  "putclip" nil
                  (replace-regexp-in-string "\\(.*\\)getclip" "\\1putclip"
                                            xclip-program 'fixedcase))))
              (`xclip
               (when (getenv "DISPLAY")
                 (start-process "xclip" nil xclip-program
                                "-selection" (symbol-name type))))
              (`xsel
               (when (and (getenv "DISPLAY")
                          (memq type '(clipboard CLIPBOARD
                                       primary PRIMARY
                                       secondary SECONDARY)))
                 (start-process
                  "xsel" nil xclip-program
                  "-i" (concat "--" (downcase (symbol-name type))))))
              (`wl-copy
               (when (and (getenv "WAYLAND_DISPLAY")
                          (memq type '(clipboard CLIPBOARD primary PRIMARY)))
                 (apply #'start-process
                        "wl-copy" nil xclip-program
                        (if (memq type '(primary PRIMARY)) '("-p")))))
              (`termux-clipboard-get
               (when (memq type '(clipboard CLIPBOARD))
                 (start-process "termux-clipboard-set" nil
                                (replace-regexp-in-string
                                 "\\(.*\\)get" "\\1set"
                                 xclip-program 'fixedcase))))
              (method (error "Unknown `xclip-method': %S" method)))))
      (when proc
        (process-send-string proc data)
        (process-send-eof proc))
      data)))

(defun xclip-get-selection (type)
  "TYPE is a symbol: primary, secondary and clipboard."
  (if (eq xclip-method 'emacs)
      (with-selected-frame (xclip--hidden-frame)
        (let ((xclip-mode nil))         ;;Just out of paranoia.
          (gui-backend-get-selection type 'STRING)))
    (with-output-to-string
      (pcase xclip-method
        (`pbpaste
         (when (memq type '(clipboard CLIPBOARD))
           (call-process xclip-program nil standard-output nil
                         "-Prefer" "txt")))
        (`powershell
         (when (memq type '(clipboard CLIPBOARD))
           (let ((coding-system-for-read 'dos)) ;Convert CR->LF.
             (call-process "powershell.exe" nil `(,standard-output nil) nil
                           "-command" "Get-Clipboard"))))
        (`getclip
         (when (memq type '(clipboard CLIPBOARD))
           (call-process xclip-program nil standard-output nil)))
        (`xclip
         (when (getenv "DISPLAY")
           (call-process xclip-program nil standard-output nil
                         "-o" "-selection" (symbol-name type))))
        (`xsel
         (when (and (getenv "DISPLAY")
                    (memq type '(clipboard CLIPBOARD
                                 primary PRIMARY
                                 secondary SECONDARY)))
           (call-process xclip-program nil standard-output nil
                         "-o" (concat "--" (downcase (symbol-name type))))))
        (`wl-copy
         (when (and (getenv "WAYLAND_DISPLAY")
                    (memq type '(clipboard CLIPBOARD primary PRIMARY)))
           (apply #'call-process
                  (replace-regexp-in-string "\\(.*\\)copy" "\\1paste"
                                            xclip-program 'fixedcase)
                  nil standard-output nil
                  ;; From wl-paste's doc:
                  ;;   -n, --no-newline  Do not append a newline character
                  ;;    after the pasted clipboard content. This option is
                  ;;    automatically enabled for non-text content types and
                  ;;    when using the --watch mode.
                  "-n" (if (memq type '(primary PRIMARY)) '("-p")))))
        (`termux-clipboard-get
         (when (memq type '(clipboard CLIPBOARD))
           (call-process xclip-program nil standard-output nil)))
        (method (error "Unknown `xclip-method': %S" method))))))

;;;###autoload
(define-minor-mode xclip-mode
  "Minor mode to use the `xclip' program to copy&paste."
  :global t
  (when (fboundp 'xclip--setup)
    (remove-hook 'terminal-init-xterm-hook #'xclip--setup))
  (when xclip-mode
    (unless (executable-find xclip-program)
      (setq xclip-mode nil)
      (signal 'file-error (list "Searching for program"
				xclip-program "no such file")))
    (when (fboundp 'xclip--setup)
      ;; NOTE: See `tty-run-terminal-initialization' and term/README
      (add-hook 'terminal-init-xterm-hook #'xclip--setup))))

;;;; Support code for the internal `emacs' method.

(defvar xclip--hidden-frame nil)

(defun xclip--hidden-frame ()
  (or (and (frame-live-p xclip--hidden-frame) xclip--hidden-frame)
      (setq xclip--hidden-frame
            (make-frame-on-display (getenv "DISPLAY")
                                   '((visibility . nil)
                                     (user-position . t)
                                     (left . 0)
                                     (top . 0)
                                     (no-other-frame . t))))))

;;;; Glue code for Emacs ≥ 25

(eval-when-compile
  (defmacro xclip--if (test then &rest else)
    ;; FIXME: copy&pasted from AUCTeX's tex.el.
    "Execute THEN if TEST is non-nil and ELSE otherwise.

TEST is assumed to be \"monotone\" in Emacs versions: if it is non-nil in
Emacs-NN, it should also always be non-nil in Emacs≥NN.

The macro takes care of byte-compilation issues that might affect THEN,
where the byte-code for it could signal an error if it has been compiled with
Emacs-NN and is then later run by Emacs>NN."
    (declare (indent 2) (debug (symbolp form &rest form)))
    (if (eval test t)    ;If test is already true at compile-time, just use it.
        then
      `(if ,test                        ;Else, check at run-time.
	   (eval ',then)                ;If it does, then run the then code.
         ,@else))))                     ;Otherwise, run the else code.

(xclip--if (>= emacs-major-version 25)
    (progn
      ;; FIXME: implement the methods for gui-backend-selection-owner-p
      ;; and gui-backend-selection-exists-p.  Not sure about pbcopy, but at
      ;; least with xcopy, gui-backend-selection-owner-p should just require us
      ;; to use "-silent" and keep track of the liveness of the subprocess.

      (cl-defmethod gui-backend-get-selection (selection-symbol _target-type
                                               &context (window-system nil))
        (if (not xclip-mode)
            (cl-call-next-method)
          (xclip-get-selection selection-symbol)))

      (cl-defmethod gui-backend-set-selection (selection-symbol value
                                               &context (window-system nil))
        (if (not xclip-mode)
            (cl-call-next-method)
          (xclip-set-selection selection-symbol value)
          nil))

      ;; BIG UGLY HACK!
      ;; term/xterm.el has a defmethod to use some (poorly supported) escape
      ;; sequences (code named OSC 52) for clipboard interaction, and enables
      ;; it by default.
      ;; Problem is that its defmethod takes precedence over our defmethod,
      ;; so we need to disable it in order to be called.
      (cl-defmethod gui-backend-set-selection :extra "xclip-override"
          (selection-symbol value
           &context (window-system nil)
                    ((terminal-parameter nil 'xterm--set-selection) (eql t))
                    ;; This extra test gives this method higher precedence
                    ;; over the one in term/xterm.el.
                    ((featurep 'term/xterm) (eql t)))
        ;; Disable this method which doesn't work anyway in 99% of the cases!
        (setf (terminal-parameter nil 'xterm--set-selection) nil)
        ;; Try again!
        (gui-backend-set-selection selection-symbol value)))

;;;; Glue code for Emacs < 25

  (defvar xclip-last-selected-text-clipboard nil
    "The value of the CLIPBOARD X selection from xclip.")

  (defvar xclip-last-selected-text-primary nil
    "The value of the PRIMARY X selection from xclip.")

  (defun xclip-select-text (text)
    "See `x-select-text'."
    (xclip-set-selection 'primary text)
    (setq xclip-last-selected-text-primary text)
    (when xclip-select-enable-clipboard
      (xclip-set-selection 'clipboard text)
      (setq xclip-last-selected-text-clipboard text)))

  (defun xclip-selection-value ()
    "See `x-selection-value'."
    (let ((clip-text (when xclip-select-enable-clipboard
                       (xclip-get-selection 'CLIPBOARD))))
      (setq clip-text
            (cond                       ; Check clipboard selection.
             ((or (not clip-text) (string= clip-text ""))
              (setq xclip-last-selected-text-clipboard nil))
             ((eq clip-text xclip-last-selected-text-clipboard)
              nil)
             ((string= clip-text xclip-last-selected-text-clipboard)
              ;; Record the newer string so subsequent calls can use the
              ;; `eq' test.
              (setq xclip-last-selected-text-clipboard clip-text)
              nil)
             (t (setq xclip-last-selected-text-clipboard clip-text))))
      (or clip-text
          (when (and (memq xclip-method '(xsel xclip)) (getenv "DISPLAY"))
            (let ((primary-text (with-output-to-string
                                  (call-process xclip-program nil
                                                standard-output nil "-o"))))
              (setq primary-text
                    (cond               ; Check primary selection.
                     ((or (not primary-text) (string= primary-text ""))
                      (setq xclip-last-selected-text-primary nil))
                     ((eq primary-text xclip-last-selected-text-primary)
                      nil)
                     ((string= primary-text xclip-last-selected-text-primary)
                      ;; Record the newer string so subsequent calls can
                      ;; use the `eq' test.
                      (setq xclip-last-selected-text-primary primary-text)
                      nil)
                     (t (setq xclip-last-selected-text-primary primary-text))))
              primary-text)))))

  (defun xclip--setup ()
    (setq interprogram-cut-function 'xclip-select-text)
    (setq interprogram-paste-function 'xclip-selection-value)))


(provide 'xclip)
;;; xclip.el ends here
