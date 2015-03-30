;;; simpleclip.el --- Simplified access to the system clipboard
;;
;; Copyright (c) 2012 Roland Walker
;;
;; Author: Roland Walker <walker@pobox.com>
;; Homepage: http://github.com/rolandwalker/simpleclip
;; URL: http://raw.github.com/rolandwalker/simpleclip/master/simpleclip.el
;; Package-Version: 1.0.0
;; Version: 1.0.0
;; Last-Updated: 25 Oct 2013
;; Keywords: convenience
;;
;; Simplified BSD License
;;
;;; Commentary:
;;
;; Quickstart
;;
;;     (require 'simpleclip)
;;
;;     (simpleclip-mode 1)
;;
;;     ;; Press super-c to copy without affecting the kill ring.
;;     ;; Press super-x or super-v to cut or paste.
;;     ;; On OS X, use ⌘-c, ⌘-v, ⌘-x.
;;
;; Explanation
;;
;; By default, Emacs orchestrates a subtle interaction between the
;; internal kill ring and the external system clipboard.
;;
;; `simpleclip-mode' radically simplifies clipboard handling: the
;; system clipboard and the Emacs kill ring are made completely
;; independent, and never influence each other.
;;
;; `simpleclip-mode' also enables support for accessing the system
;; clipboard from a TTY where possible.  You will likely need to
;; set up custom keybindings if you want to take advantage of that.
;;
;; To use simpleclip, place the simpleclip.el library somewhere
;; Emacs can find it, and add the following to your ~/.emacs file:
;;
;;     (require 'simpleclip)
;;     (simpleclip-mode 1)
;;
;; Keybindings
;;
;; Turning on `simpleclip-mode' activates clipboard-oriented key
;; bindings which are modifiable in customize.
;;
;; The default bindings override keystrokes which may be bound as
;; alternatives for kill/yank commands on your system.  "Traditional"
;; kill/yank keys (control-k, control-y, meta-y) are unaffected.
;;
;; The default keybindings are
;;
;;              super-c   simpleclip-copy
;;              super-x   simpleclip-cut
;;              super-v   simpleclip-paste
;;
;;     control-<insert>   simpleclip-copy
;;       shift-<delete>   simpleclip-cut
;;       shift-<insert>   simpleclip-paste
;;
;; The "super" keybindings are friendly for OS X.  The "insert"/"delete"
;; keybindings are better suited for Unix and MS Windows.
;;
;; See Also
;;
;;     M-x customize-group RET simpleclip RET
;;
;; Notes
;;
;; `x-select-enable-primary' is not affected by `simpleclip-mode'.
;;
;; Access to the system clipboard from a TTY is provided for those
;; cases where a literal paste is needed -- for example, where
;; autopair interferes with pasted input which is interpreted as
;; keystrokes.  If you are already happy with the copy/paste provided
;; by your terminal emulator, then you don't need to set up
;; simpleclip's TTY support.
;;
;; The following functions may be useful to call from Lisp:
;;
;;     `simpleclip-get-contents'
;;     `simpleclip-set-contents'
;;
;; Compatibility and Requirements
;;
;;     GNU Emacs version 24.4-devel     : yes, at the time of writing
;;     GNU Emacs version 24.3           : yes
;;     GNU Emacs version 23.3           : yes
;;     GNU Emacs version 22.2           : yes, with some limitations
;;     GNU Emacs version 21.x and lower : unknown
;;
;;     No external dependencies
;;
;;     Tested on OS X, X11, and MS Windows
;;
;; Bugs
;;
;;     Assumes that transient-mark-mode is on.
;;
;;     Menu items under Edit are rebound successfully, but the visible
;;     menu text does not change.  cua-mode does this correctly --
;;     because of remap?  because of emulation-mode-map-alists?
;;
;;     Key bindings do not work out-of-the-box with Aquamacs.
;;
;; TODO
;;
;;     TTY-friendly key bindings.
;;
;;     Keep kill-ring commands in Edit menu under modified names.
;;
;;     Support non-string data types.
;;
;;; License
;;
;; Simplified BSD License:
;;
;; Redistribution and use in source and binary forms, with or
;; without modification, are permitted provided that the following
;; conditions are met:
;;
;;    1. Redistributions of source code must retain the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer.
;;
;;    2. Redistributions in binary form must reproduce the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer in the documentation and/or other materials
;;       provided with the distribution.
;;
;; This software is provided by Roland Walker "AS IS" and any express
;; or implied warranties, including, but not limited to, the implied
;; warranties of merchantability and fitness for a particular
;; purpose are disclaimed.  In no event shall Roland Walker or
;; contributors be liable for any direct, indirect, incidental,
;; special, exemplary, or consequential damages (including, but not
;; limited to, procurement of substitute goods or services; loss of
;; use, data, or profits; or business interruption) however caused
;; and on any theory of liability, whether in contract, strict
;; liability, or tort (including negligence or otherwise) arising in
;; any way out of the use of this software, even if advised of the
;; possibility of such damage.
;;
;; The views and conclusions contained in the software and
;; documentation are those of the authors and should not be
;; interpreted as representing official policies, either expressed
;; or implied, of Roland Walker.
;;
;;; Code:
;;

;;; requirements

;; for callf, assert
(require 'cl)

(autoload 'term-send-raw-string "term")

;;; declarations

(eval-when-compile
  (defvar x-select-enable-clipboard))

;;; customizable variables

;;;###autoload
(defgroup simpleclip nil
  "Simplified access to the system clipboard."
  :version "1.0.0"
  :link '(emacs-commentary-link :tag "Commentary" "simpleclip")
  :link '(url-link :tag "GitHub" "http://github.com/rolandwalker/simpleclip")
  :link '(url-link :tag "EmacsWiki" "http://emacswiki.org/emacs/Simpleclip")
  :prefix "simpleclip-"
  :group 'convenience)

(defcustom simpleclip-less-feedback nil
  "Give less echo area feedback."
  :type 'boolean
  :group 'simpleclip)

(defcustom simpleclip-edit-menu t
  "Rebind Cut/Copy/Paste in the Edit menu."
  :type 'boolean
  :group 'simpleclip)

;;;###autoload
(defgroup simpleclip-keys nil
  "Key bindings for `simpleclip-mode'."
  :group 'simpleclip)

(defcustom simpleclip-copy-keystrokes '(
                                        "s-c"
                                        "C-<insert>"
                                        "C-<insertchar>"
                                        )
  "List of key sequences to invoke `simpleclip-copy'.

The key bindings are in effect whenever `simpleclip-mode' minor
mode is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'simpleclip-keys)

(defcustom simpleclip-cut-keystrokes '(
                                       "s-x"
                                       "S-<delete>"
                                       )
  "List of key sequences to invoke `simpleclip-cut'.

The key bindings are in effect whenever `simpleclip-mode' minor
mode is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'simpleclip-keys)

(defcustom simpleclip-paste-keystrokes '(
                                         "s-v"
                                         "S-<insert>"
                                         "S-<insertchar>"
                                         )
  "List of key sequences to invoke `simpleclip-paste'.

The key bindings are in effect whenever `simpleclip-mode' minor
mode is active.

The format for key sequences is as defined by `kbd'."
  :type '(repeat string)
  :group 'simpleclip-keys)

;;; variables

(defvar simpleclip-mode nil "Mode variable for `simpleclip-mode'.")
(defvar simpleclip-commands '(simpleclip-paste simpleclip-copy simpleclip-cut)
  "Interactive commands provided by `simpleclip-mode'.")

(defvar simpleclip-saved-icf nil
  "Saved value of `interprogram-cut-function'.")
(defvar simpleclip-saved-ipf nil
  "Saved value of `interprogram-paste-function'.")
(defvar simpleclip-saved-xsec nil
  "Saved value of `x-select-enable-clipboard'.")

;; MS Windows workaround - w32-get-clipboard-data returns nil
;; when Emacs was the originator of the clipboard data.
(defvar simpleclip-contents nil
  "Value of most-recent cut or paste.")

;;; keymaps

(defvar simpleclip-mode-map
  (let ((map (make-sparse-keymap)))
    (dolist (cmd simpleclip-commands)
      (dolist (key (symbol-value (intern (format "%s-keystrokes" cmd))))
        (define-key map (read-kbd-macro key) cmd)))
    map) "Keymap for `simpleclip-mode' minor-mode.")

(when simpleclip-edit-menu
  (let ((map (copy-keymap (lookup-key global-map [menu-bar edit]))))
    (define-key map [cut]   '(menu-item
                              "Cut"
                              simpleclip-cut
                              :enable
                              (and use-region-p (not buffer-read-only))
                              :help
                              "Cut (to clipboard) text in region between mark and current position"))
    (define-key map [copy]  '(menu-item
                              "Copy"
                              simpleclip-copy
                              :enable
                              use-region-p
                              :help
                              "Copy (to clipboard) text in region between mark and current position"))
    (define-key map [paste] '(menu-item
                              "Paste"
                              simpleclip-paste
                              :enable
                              (and (if (fboundp 'x-selection-exists-p)
                                       (x-selection-exists-p 'CLIPBOARD)
                                     t)
                                   (not buffer-read-only))
                              :help
                              "Paste (from clipboard) text most recently cut/copied"))
    (define-key simpleclip-mode-map [menu-bar edit] map)))

;;; macros

(defmacro simpleclip-called-interactively-p (&optional kind)
  "A backward-compatible version of `called-interactively-p'.

Optional KIND is as documented at `called-interactively-p'
in GNU Emacs 24.1 or higher."
  (cond
    ((not (fboundp 'called-interactively-p))
     '(interactive-p))
    ((condition-case nil
         (progn (called-interactively-p 'any) t)
       (error nil))
     `(called-interactively-p ,kind))
    (t
     '(called-interactively-p))))

;;; utility functions

;;;###autoload
(defun simpleclip-get-contents ()
  "Return the contents of the system clipboard as a string."
  (condition-case nil
      (cond
        ((fboundp 'ns-get-pasteboard)
         (ns-get-pasteboard))
        ((fboundp 'w32-get-clipboard-data)
         (or (w32-get-clipboard-data)
             simpleclip-contents))
        ((and (featurep 'mac)
              (fboundp 'x-get-selection))
         (x-get-selection 'CLIPBOARD 'NSStringPboardType))
        ((fboundp 'x-get-selection)
         (x-get-selection 'CLIPBOARD))
        (t
         (error "Clipboard support not available")))
    (error
     (condition-case nil
         (cond
           ((eq system-type 'darwin)
            (with-output-to-string
              (with-current-buffer standard-output
                (call-process "/usr/bin/pbpaste" nil t nil "-Prefer" "txt"))))
           ((eq system-type 'cygwin)
            (with-output-to-string
              (with-current-buffer standard-output
                (call-process "getclip" nil t nil))))
           ((memq system-type '(gnu gnu/linux gnu/kfreebsd))
            (with-output-to-string
              (with-current-buffer standard-output
                (call-process "xsel" nil t nil "--clipboard" "--output"))))
           (t
            (error "Clipboard support not available")))
       (error
        (error "Clipboard support not available"))))))

;;;###autoload
(defun simpleclip-set-contents (str-val)
  "Set the contents of the system clipboard to STR-VAL."
  (callf or str-val "")
  (assert (stringp str-val) nil "STR-VAL must be a string or nil")
  (condition-case nil
      (cond
        ((fboundp 'ns-set-pasteboard)
         (ns-set-pasteboard str-val))
        ((fboundp 'w32-set-clipboard-data)
         (w32-set-clipboard-data str-val)
         (setq simpleclip-contents str-val))
        ((fboundp 'x-set-selection)
         (x-set-selection 'CLIPBOARD str-val))
        (t
         (error "Clipboard support not available")))
    (error
     (condition-case nil
         (cond
           ((eq system-type 'darwin)
            (with-temp-buffer
              (insert str-val)
              (call-process-region (point-min) (point-max) "/usr/bin/pbcopy")))
           ((eq system-type 'cygwin)
            (with-temp-buffer
              (insert str-val)
              (call-process-region (point-min) (point-max) "putclip")))
           ((memq system-type '(gnu gnu/linux gnu/kfreebsd))
            (with-temp-buffer
              (insert str-val)
              (call-process-region (point-min) (point-max) "xsel" nil nil nil "--clipboard" "--input")))
           (t
            (error "Clipboard support not available")))
       (error
        (error "Clipboard support not available"))))))

;;; minor-mode definition

;;;###autoload
(define-minor-mode simpleclip-mode
  "Turn on `simpleclip-mode'.

When called interactively with no prefix argument this command
toggles the mode.  With a prefix argument, it enables the mode
if the argument is positive and otherwise disables the mode.

When called from Lisp, this command enables the mode if the
argument is omitted or nil, and toggles the mode if the argument
is 'toggle."
  :keymap simpleclip-mode-map
  :group 'simpleclip
  :global t
  (cond
   (simpleclip-mode
    (setq simpleclip-saved-icf interprogram-cut-function)
    (setq simpleclip-saved-ipf interprogram-paste-function)
    (when (boundp 'x-select-enable-clipboard)
      (setq simpleclip-saved-xsec x-select-enable-clipboard))
    (setq interprogram-cut-function nil)
    (setq interprogram-paste-function nil)
    (setq x-select-enable-clipboard nil)
    (when (and (simpleclip-called-interactively-p 'interactive)
               (not simpleclip-less-feedback))
      (message "simpleclip mode enabled")))
   (t
    (setq interprogram-cut-function simpleclip-saved-icf)
    (setq interprogram-paste-function simpleclip-saved-ipf)
    (when (boundp 'x-select-enable-clipboard)
      (setq x-select-enable-clipboard simpleclip-saved-xsec))
    (setq simpleclip-saved-icf nil)
    (setq simpleclip-saved-ipf nil)
    (setq simpleclip-saved-xsec nil)
    (when (and (simpleclip-called-interactively-p 'interactive)
               (not simpleclip-less-feedback))
      (message "simpleclip mode disabled")))))

;;; interactive commands

;;;###autoload
(defun simpleclip-copy (beg end)
  "Copy the active region (from BEG to END) to the system clipboard."
  (interactive "r")
  (unless (use-region-p)
    (error "No region to copy"))
  (simpleclip-set-contents
   (substring-no-properties
    (filter-buffer-substring beg end)))
  (when (and (not (minibufferp))
             (not simpleclip-less-feedback)
             (simpleclip-called-interactively-p 'interactive))
    (message "copied to clipboard")))

;;;###autoload
(defun simpleclip-cut (beg end)
  "Cut the active region (from BEG to END) to the system clipboard."
  (interactive "*r")
  (unless (use-region-p)
    (error "No region to cut"))
  (simpleclip-set-contents
   (substring-no-properties
    (filter-buffer-substring beg end)))
  (delete-region beg end)
    (when (and (not (minibufferp))
               (not simpleclip-less-feedback)
               (simpleclip-called-interactively-p 'interactive))
      (message "cut to clipboard")))

;;;###autoload
(defun simpleclip-paste ()
  "Paste the contents of the system clipboard at the point."
  (interactive "*")
  (let ((str-val (simpleclip-get-contents)))
    (unless str-val
      (error "No content to paste"))
    (cond
      ((derived-mode-p 'term-mode)
       (term-send-raw-string str-val))
      (t
       (when (use-region-p)
         (delete-region (region-beginning) (region-end)))
       (push-mark (point) t)
       (insert-for-yank str-val)))
    (when (and (not (minibufferp))
               (not simpleclip-less-feedback)
               (simpleclip-called-interactively-p 'interactive))
      (message "pasted from clipboard"))))

(provide 'simpleclip)

;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions redefine)
;; End:
;;
;; LocalWords: Simpleclip ARGS alist devel callf pbpaste xsel pbcopy
;; LocalWords: simpleclip insertchar
;;

;;; simpleclip.el ends here
