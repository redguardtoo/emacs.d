;;; workgroups2.el --- New workspaces for Emacs -*- coding: utf-8; lexical-binding: t -*-
;;
;; Copyright (C) 2020 Chen Bin
;; Copyright (C) 2013-2014 Sergey Pashinin
;; Copyright (C) 2010-2011 tlh
;;
;; Author: Sergey Pashinin <sergey at pashinin dot com>
;; Keywords: session management window-configuration persistence
;; Homepage: https://github.com/pashinin/workgroups2
;; Version: 1.2.1
;; Package-Requires: ((emacs "25.1") (dash "2.8.0"))
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or (at
;; your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
;; USA
;;
;;; Commentary:
;;
;; Workgroups2 is an Emacs session manager. It is based on the
;; experimental branch of the original "workgroups" extension.
;;
;; If you find a bug - please post it here:
;; https://github.com/pashinin/workgroups2/issues
;;
;; Quick start,
;;
;; - use `wg-create-workgroup' to save current windows layout
;; - use `wg-open-workgroup' to open saved windows layout
;;
;; Optionally, you can use minor-mode `workgroups-mode' by put below
;; line into .emacs ,
;;
;; (workgroups-mode 1)
;;
;; Most commands start with prefix `wg-prefix-key'.
;; You can change it before activating workgroups.
;; Change prefix key (before activating WG)
;;
;; (setq wg-prefix-key (kbd "C-c z"))
;;
;; By default prefix is: "C-c z"
;;
;; <prefix> <key>
;;
;; <prefix> c    - create workgroup
;; <prefix> A    - rename workgroup
;; <prefix> k    - kill workgroup
;; <prefix> v    - switch to workgroup
;; <prefix> C-s  - save session
;; <prefix> C-f  - load session
;; <prefix> ?    -  for more help
;;
;; Change workgroups session file,
;; (setq wg-session-file "~/.emacs.d/.emacs_workgroups"
;;
;;; Code:

(require 'cl-lib)
(require 'dash)
(require 'ring)

(defconst wg-version "1.2.1" "Current version of Workgroups.")

(defgroup workgroups nil
  "Workgroups for Emacs -- Emacs session manager"
  :group 'convenience)

(defcustom wg-session-file "~/.emacs_workgroups"
  "Default filename to be used to save workgroups."
  :type 'file
  :group 'workgroups)
(defvaralias 'wg-default-session-file 'wg-session-file)

(defcustom wg-prefix-key (kbd "C-c z")
  "Workgroups' prefix key.
Setting this variable requires that `workgroups-mode' be turned
off and then on again to take effect."
  :type 'string
  :group 'workgroups)

(defvar workgroups-mode-map nil "Workgroups Mode's keymap.")

(defvar wg-incorrectly-restored-bufs nil
  "FIXME: docstring this.")
;; TODO: check it on switching WG

(defvar wg-record-incorrectly-restored-bufs nil
  "FIXME: docstring this.")

(defvar wg-log-level 1
  "Use later.
0 means no messages at all (for tests)")

(defcustom wg-emacs-exit-save-behavior 'save
  "Determines save behavior on Emacs exit.

`ask'           Ask the user whether to save if there are unsaved changes
`save'          Call `wg-save-session' when there are unsaved changes
Anything else   Exit Emacs without saving changes"
  :type 'symbol
  :group 'workgroups)

(defcustom wg-workgroups-mode-exit-save-behavior 'save
  "Determines save behavior on `workgroups-mode' exit.

`ask'           Ask the user whether to saveif there are unsaved changes
`save'          Call `wg-save-session' when there are unsaved changes
Anything else   Exit `workgroups-mode' without saving changes"
  :type 'symbol
  :group 'workgroups)

(defcustom wg-session-load-on-start (not (daemonp))
  "Load a session file on Workgroups start.
Don't do it with Emacs --daemon option."
  :type 'boolean
  :group 'workgroups)
(defvaralias 'wg-use-default-session-file 'wg-session-load-on-start)

(defcustom workgroups-mode nil
  "Non-nil if Workgroups mode is enabled."
  :set 'custom-set-minor-mode
  :initialize 'custom-initialize-default
  :group 'workgroups
  :type 'boolean)

(defcustom wg-first-wg-name "First workgroup"
  "Title of the first workgroup created."
  :type 'string
  :group 'workgroups)

(defcustom wg-modeline-string " wg"
  "Appears in modeline."
  :type 'string
  :group 'workgroups)

(defcustom wg-mode-line-display-on (not (featurep 'powerline))
  "Toggles Workgroups' mode-line display."
  :type 'boolean
  :group 'workgroups
  :set (lambda (sym val)
         (custom-set-default sym val)
         (force-mode-line-update)))

(defcustom wg-mode-line-use-faces nil
  "Non-nil means use faces in the mode-line display.
It can be tricky to choose faces that are visible in both active
and inactive mode-lines, so this feature defaults to off."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-mode-line-decor-left-brace "("
  "String displayed at the left of the mode-line display."
  :type 'string
  :group 'workgroups)

(defcustom wg-mode-line-decor-right-brace ")"
  "String displayed at the right of the mode-line display."
  :type 'string
  :group 'workgroups)

(defcustom wg-mode-line-decor-divider ":"
  "String displayed between elements of the mode-line display."
  :type 'string
  :group 'workgroups)

(defcustom wg-mode-line-decor-window-dedicated
  #("#" 0 1 (help-echo "This window is dedicated to its buffer."))
  "Indicates that the window is dedicated to its buffer."
  :type 'string
  :group 'workgroups)

(defcustom wg-mode-line-decor-window-undedicated
  #("-" 0 1 (help-echo "This window is not dedicated to its buffer."))
  "Indicates that the window is not dedicated to its buffer."
  :type 'string
  :group 'workgroups)

(defcustom wg-mode-line-decor-session-modified
  #("*" 0 1 (help-echo "The session is modified"))
  "Indicates that the session is modified."
  :type 'string
  :group 'workgroups)

(defcustom wg-mode-line-decor-session-unmodified
  #("-" 0 1 (help-echo "The session is unmodified"))
  "Indicates that the session is unmodified."
  :type 'string
  :group 'workgroups)

(defcustom wg-mode-line-decor-workgroup-modified
  #("*" 0 1 (help-echo "The current workgroup is modified"))
  "Indicates that the current workgroup is modified."
  :type 'string
  :group 'workgroups)

(defcustom wg-mode-line-decor-workgroup-unmodified
  #("-" 0 1 (help-echo "The current workgroup is unmodified"))
  "Indicates that the current workgroup is unmodified."
  :type 'string
  :group 'workgroups)

(defcustom wg-load-last-workgroup t
  "Load last active (not first) workgroup from all your workgroups if it exists."
  :group 'workgroups
  :type 'boolean)

(defcustom wg-control-frames t
  "Save/restore frames."
  :group 'workgroups
  :type 'boolean)

(defcustom workgroups-mode-hook nil
  "Hook run when `workgroups-mode' is turned on."
  :type 'hook
  :group 'workgroups)

(defcustom workgroups-mode-exit-hook nil
  "Hook run when `workgroups-mode' is turned off."
  :type 'hook
  :group 'workgroups)

(defcustom wg-before-switch-to-workgroup-hook nil
  "Hook run by `wg-switch-to-workgroup'."
  :type 'hook
  :group 'workgroups)

(defcustom wg-after-switch-to-workgroup-hook nil
  "Hook run by `wg-switch-to-workgroup'."
  :type 'hook
  :group 'workgroups)
(define-obsolete-variable-alias 'wg-switch-to-workgroup-hook 'wg-after-switch-to-workgroup-hook)

(defcustom wg-pre-window-configuration-change-hook nil
  "Hook run before any function that triggers `window-configuration-change-hook'."
  :type 'hook
  :group 'workgroups)

(defcustom wg-open-this-wg nil
  "Try to open this workgroup on start.
If nil - nothing happens."
  :type 'string
  :group 'workgroups)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; FIXME:
;;
;; Only set `wg-workgroup-base-wconfig' on `wg-save-session-as' or
;; `delete-frame' and only with the most recently changed working-wconfig.
;; Then, since it's not overwritten on every call to
;; `wg-workgroup-working-wconfig', its restoration can be retried after manually
;; recreating buffers that couldn't be restored.  So it takes over the
;; 'incorrect restoration' portion of the base wconfig's duty.  All that leaves
;; to base wconfigs is that they're a saved wconfig the user felt was important.
;; So why not allow more of of them?  A workgroup could stash an unlimited
;; number of wconfigs.
;;
;; TODO:
;;
;;   * Write new commands for restoring stashed wconfigs
;;
;;   * Add this message on improper restoration of `base-wconfig':
;;
;;       "Unable to restore 'buf1', 'buf2'... Hit C-whatever to retry after
;;        manually recreating these buffers."
;;
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; TODO: possibly add `buffer-file-coding-system', `text-scale-mode-amount'
(defcustom wg-buffer-local-variables-alist
  `((major-mode nil wg-deserialize-buffer-major-mode)
    (mark-ring wg-serialize-buffer-mark-ring wg-deserialize-buffer-mark-ring)
    (left-fringe-width nil nil)
    (right-fringe-width nil nil)
    (fringes-outside-margins nil nil)
    (left-margin-width nil nil)
    (right-margin-width nil nil)
    (vertical-scroll-bar nil nil))
  "Alist mapping buffer-local variable symbols to serdes functions.

The `car' of each entry should be a buffer-local variable symbol.

The `cadr' of the entry should be either nil or a function of no
arguments.  If nil, the variable's value is used as-is, and
should have a readable printed representation.  If a function,
`funcall'ing it should yield a serialization of the value of the
variable.

The `caddr' of the entry should be either nil or a function of
one argument.  If nil, the serialized value from above is
assigned to the variable as-is.  It a function, `funcall'ing it
on the serialized value from above should do whatever is
necessary to properly restore the original value of the variable.
For example, in the case of `major-mode' it should funcall the
value (a major-mode function symbol) rather than just assigning
it to `major-mode'."
  :type 'alist
  :group 'workgroups)


(defcustom wg-nowg-string "No workgroups"
  "Display this string if there are no workgroups and
`wg-display-nowg' is t."
  :type 'string
  :group 'workgroups)

(defcustom wg-display-nowg nil
  "Display something if there are no workgroups."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-remote-buffers t
  "Restore buffers that get \"t\" with `file-remote-p'."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-frame-position t
  "Non-nil means restore frame position on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-scroll-bars t
  "Non-nil means restore scroll-bar settings on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-fringes t
  "Non-nil means restore fringe settings on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-margins t
  "Non-nil means restore margin settings on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-point t
  "Non-nil means restore `point' on workgroup restore.
This is included mainly so point restoration can be suspended
during `wg-morph' -- you probably want this non-nil."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-point-max t
  "Controls point restoration when point is at `point-max'.
If `point' is at `point-max' when a wconfig is created, put
`point' back at `point-max' when the wconfig is restored, even if
`point-max' has increased in the meantime.  This is useful in,
say, irc buffers where `point-max' is constantly increasing."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-mark t
  "Non-nil means restore mark data on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-window-dedicated-p t
  "Non-nil means restore `window-dedicated-p' on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-remember-frame-for-each-wg nil
  "When switching workgroups - restore frame parameters for each workgroup.

When nil - save/restore frame parameters to/from the first workgroup."
  :type 'boolean
  :group 'workgroups)


(defcustom wg-wconfig-undo-list-max 20
  "Number of past window configs to retain for undo."
  :type 'integer
  :group 'workgroups)

(defcustom wg-wconfig-kill-ring-max 20
  "Maximum length of the `wg-wconfig-kill-ring'."
  :type 'integer
  :group 'workgroups)

(defvar wg-wconfig-kill-ring nil
  "Ring of killed or kill-ring-saved wconfigs.")

(defvar wg-buffer-uid nil
  "Symbol for the current buffer's wg-buf's uid.
Every Workgroups buffer object (wg-buf) has a uid.  When
Workgroups creates or encounters an Emacs buffer object
corresponding to a wg-buf, it tags it with the wg-buf's uid to
unambiguously pair the two.")
(make-variable-buffer-local 'wg-buffer-uid)

(defcustom wg-flag-modified t
  "Show \"modified\" flags in modeline."
  :type 'boolean
  :group 'workgroups
  :set (lambda (sym val)
         (custom-set-default sym val)
         (force-mode-line-update)))



(defvar wg-window-configuration-changed nil
  "Flag set by `window-configuration-change-hook'.")

(defvar wg-already-updated-working-wconfig nil
  "Flag set by `wg-update-working-wconfig-hook'.")

(defvar wg-undoify-window-configuration-change t
  "Should windows undo info be updated or not.
When you change window configuration.")

(defvar wg-current-workgroup nil "Bound to the current workgroup.")

(defvar wg-window-min-width 2
  "Bound to `window-min-width' when restoring wtrees.")

(defvar wg-window-min-height 1
  "Bound to `window-min-height' when restoring wtrees.")

(defvar wg-window-min-pad 2
  "Added to `wg-window-min-foo' to produce the actual minimum window size.")

(defvar wg-actual-min-width (+ wg-window-min-width wg-window-min-pad)
  "Actual minimum window width when creating windows.")

(defvar wg-actual-min-height (+ wg-window-min-height wg-window-min-pad)
  "Actual minimum window height when creating windows.")

(defvar wg-min-edges `(0 0 ,wg-actual-min-width ,wg-actual-min-height)
  "Smallest allowable edge list of windows created by Workgroups.")

(defvar wg-null-edges '(0 0 0 0) "Null edge list.")

(defvar wg-window-tree-selected-window nil
  "Used during wconfig restoration to hold the selected window.")

(defvar wg-buffer-workgroup nil
  "A workgroup in which this buffer most recently appeared.
Buffer-local.")
(make-variable-buffer-local 'wg-buffer-workgroup)

(defcustom wg-default-buffer "*scratch*"
  "Show this in case everything else fails.
When a buffer can't be restored, when creating a blank wg."
  :type 'string
  :group 'workgroups)


;;
;; Crazy stuff...
;;
(defcustom wg-associate-blacklist (list "*helm mini*" "*Messages*" "*scratch*"
                                        "*helm action*")
  "Do not autoassociate these buffers."
  :type 'list
  :group 'workgroups)

(defconst wg-buffer-list-original (symbol-function 'buffer-list))
(fset 'wg-buffer-list-emacs wg-buffer-list-original)

(defun buffer-list (&optional frame)
  "Redefinition of `buffer-list'.
Pass FRAME to it.
Remove file and dired buffers that are not associated with workgroup."
  (let ((res (wg-buffer-list-emacs frame))
        (wg-buf-uids (wg-workgroup-associated-buf-uids)))
    (--remove (and (or (buffer-file-name it)
                       (eq (buffer-local-value 'major-mode it) 'dired-mode))
                   ;;(not (member b wg-buffers))
                   (not (member (wg-buffer-uid-or-add it) wg-buf-uids)))
              res)))

(defconst wg-buffer-list-function (symbol-function 'buffer-list))
(fset 'buffer-list wg-buffer-list-original)

;; locate-dominating-file
(defcustom wg-mess-with-buffer-list nil
  "Redefine `buffer-list' to show buffers for each workgroup.

Crazy stuff that allows to reduce amount of code, gives new
features but is fucking unstable, so disabled by default"
  :type 'boolean
  :group 'workgroups
  :set (lambda (sym val)
         (custom-set-default sym val)
         (if (and workgroups-mode val)
             (fset 'buffer-list wg-buffer-list-function)
           (fset 'buffer-list wg-buffer-list-original))))
(fset 'buffer-list wg-buffer-list-original)

(defcustom wg-use-faces t
  "Non-nil means use faces in various messages."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-list-display-decor-left-brace "( "
  "String displayed to the left of the list display."
  :type 'string
  :group 'workgroups)

(defcustom wg-list-display-decor-right-brace " )"
  "String displayed to the right of the list display."
  :type 'string
  :group 'workgroups)

(defcustom wg-list-display-decor-divider " | "
  "String displayed between elements of the list display."
  :type 'string
  :group 'workgroups)

(defcustom wg-list-display-decor-current-left "-<{ "
  "String displayed to the left of the current element of the list display."
  :type 'string
  :group 'workgroups)

(defcustom wg-list-display-decor-current-right " }>-"
  "String displayed to the right of the current element of the list display."
  :type 'string
  :group 'workgroups)

(defcustom wg-list-display-decor-previous-left "< "
  "String displayed to the left of the previous element of the list display."
  :type 'string
  :group 'workgroups)

(defcustom wg-list-display-decor-previous-right " >"
  "String displayed to the right of the previous element of the list display."
  :type 'string
  :group 'workgroups)


(defvar wg-face-abbrevs nil
  "Assoc list mapping face abbreviations to face names.")

(defmacro wg-defface (face key spec doc &rest args)
  "`defface' wrapper adding a lookup key used by `wg-fontify'."
  (declare (indent 2))
  `(progn
     (cl-pushnew (cons ,key ',face) wg-face-abbrevs :test #'equal)
     (defface ,face ,spec ,doc ,@args)))

(wg-defface wg-current-workgroup-face :cur
  '((t :inherit font-lock-constant-face :bold nil))
  "Face used for current elements in list displays."
  :group 'workgroups)

(wg-defface wg-previous-workgroup-face :prev
  '((t :inherit font-lock-keyword-face :bold nil))
  "Face used for the name of the previous workgroup in the list display."
  :group 'workgroups)

(wg-defface wg-other-workgroup-face :other
  '((t :inherit font-lock-string-face :bold nil))
  "Face used for the names of other workgroups in the list display."
  :group 'workgroups)

(wg-defface wg-command-face :cmd
  '((t :inherit font-lock-function-name-face :bold nil))
  "Face used for command/operation strings."
  :group 'workgroups)

(wg-defface wg-divider-face :div
  '((t :inherit font-lock-builtin-face :bold nil))
  "Face used for dividers."
  :group 'workgroups)

(wg-defface wg-brace-face :brace
  '((t :inherit font-lock-builtin-face :bold nil))
  "Face used for left and right braces."
  :group 'workgroups)

(wg-defface wg-message-face :msg
  '((t :inherit font-lock-string-face :bold nil))
  "Face used for messages."
  :group 'workgroups)

(wg-defface wg-mode-line-face :mode
  '((t :inherit font-lock-doc-face :bold nil))
  "Face used for workgroup position and name in the mode-line display."
  :group 'workgroups)

(wg-defface wg-filename-face :file
  '((t :inherit font-lock-keyword-face :bold nil))
  "Face used for filenames."
  :group 'workgroups)


;;; fancy displays

(defmacro aif (cond then &rest else)
  "Like `if', but the result of evaluating COND is bound to `it'.
The variable `it' is available within THEN and ELSE.
COND, THEN, and ELSE are otherwise as documented for `if'."
  `(let ((it ,cond))
     (if it ,then ,@else)))

(defmacro awhen (cond &rest body)
  "Like `when', but the result of evaluating COND is bound to `it'.
The variable `it' is available within BODY.
COND and BODY are otherwise as documented for `when'."
  `(aif ,cond (progn ,@body)))

(defun wg-element-display (elt elt-string &optional current-elt-p previous-elt-p)
  "Return display string for ELT."
  (cond ((and current-elt-p (funcall current-elt-p elt))
         (wg-fontify (:cur (concat wg-list-display-decor-current-left
                                   elt-string
                                   wg-list-display-decor-current-right))))
        ((and previous-elt-p (funcall previous-elt-p elt))
         (wg-fontify (:prev (concat wg-list-display-decor-previous-left
                                    elt-string
                                    wg-list-display-decor-previous-right))))
        (t (wg-fontify (:other elt-string)))))

(defun wg-workgroup-display (workgroup index)
  "Return display string for WORKGROUP at INDEX."
  (if (not workgroup) wg-nowg-string
    (wg-element-display
     workgroup
     (format "%d: %s" index (wg-workgroup-name workgroup))
     'wg-current-workgroup-p
     'wg-previous-workgroup-p)))

(defun wg-buffer-display (buffer index)
  "Return display string for BUFFER.  INDEX is ignored."
  (ignore index)
  (if (not buffer) "No buffers"
    (wg-element-display
     (wg-get-buffer buffer)
     (format "%s" (wg-buffer-name buffer))
     'wg-current-buffer-p)))

(defun wg-message (format-string &rest args)
  "Call `message' with FORMAT-STRING and ARGS."
  (if (> wg-log-level 0) (apply #'message format-string args)))

(defmacro wg-fontified-message (&rest format)
  "`wg-fontify' FORMAT and call `wg-message' on it."
  (declare (indent defun))
  `(wg-message (wg-fontify ,@format)))

(defun wg-add-face (facekey string)
  "Return a copy of STRING fontified according to FACEKEY.
FACEKEY must be a key in `wg-face-abbrevs'."
  (let ((face (wg-aget wg-face-abbrevs facekey))
        (string  (copy-sequence string)))
    (unless face (error "No face with key %s" facekey))
    (if (not wg-use-faces) string
      (put-text-property 0 (length string) 'face face string)
      string)))

(defmacro wg-fontify (&rest specs)
  "A small fontification DSL.
The results of all SPECS are `concat'd together.
If a spec is a cons with a keyword car, apply `wg-add-face' to it.
Other conses get evaluated, and should produce a strings.
If a spec is a string it is used unmodified.
Anything else is formatted with %s to produce a string."
  (declare (indent defun))
  `(concat
    ,@(wg-docar (spec specs)
        (cond ((and (consp spec)
                    (keywordp (car spec)))
               `(wg-add-face ,@spec))
              ;;((listp spec) (cdr (eval spec)))
              ;;((listp spec)
              ;; ;;(prin1-to-string (nth 1 (eval spec)))
              ;; )
              ((consp spec) spec)
              ((stringp spec) spec)
              (t `(format "%s" ,spec))))))

(defmacro wg-with-gensyms (syms &rest body)
  "Bind all symbols in SYMS to `gensym's, and eval BODY."
  (declare (indent 1))
  `(let (,@(mapcar (lambda (sym) `(,sym (cl-gensym))) syms)) ,@body))

(defmacro wg-dbind (args expr &rest body)
  "Bind the variables in ARGS to the result of EXPR and execute BODY.
Abbreviation of `destructuring-bind'."
  (declare (indent 2))
  `(cl-destructuring-bind ,args ,expr ,@body))

(defun wg-partition (list &optional n step)
  "Take LIST, return a list of N length sublists, offset by STEP.
N defaults to 2, and STEP defaults to N.
Iterative to prevent stack overflow."
  (let* ((n (or n 2)) (step (or step n)) acc)
    (while list
      (push (-take n list) acc)
      (setq list (nthcdr step list)))
    (nreverse acc)))

(defmacro wg-when-boundp (symbols &rest body)
  "When all SYMBOLS are bound, `eval' BODY."
  (declare (indent 1))
  `(when (and ,@(mapcar (lambda (sym) `(boundp ',sym)) symbols))
     ,@body))

(defmacro wg-docar (spec &rest body)
  "do-style wrapper for `mapcar'.

\(fn (VAR LIST) BODY...)"
  (declare (indent 1))
  `(mapcar (lambda (,(car spec)) ,@body) ,(cadr spec)))

(defmacro wg-dohash (spec &rest body)
  "do-style wrapper for `maphash'.

\(fn (KEY VALUE TABLE [RESULT]) BODY...)"
  (declare (indent 1))
  (wg-dbind (key val table &optional result) spec
    `(progn (maphash (lambda (,key ,val) ,@body) ,table) ,result)))

(defmacro wg-doconcat (spec &rest body)
  "do-style wrapper for `mapconcat'.

\(fn (VAR SEQ [SEPARATOR]) BODY...)"
  (declare (indent 1))
  (wg-dbind (elt seq &optional sep) spec
    `(mapconcat (lambda (,elt) ,@body) ,seq (or ,sep ""))))

(defmacro wg-asetf (&rest places-and-values)
  "Anaphoric `setf'."
  `(progn ,@(mapcar (lambda (pv) `(let ((it ,(car pv))) (setf ,@pv)))
                    (wg-partition places-and-values 2))))

(defmacro wg-destructuring-dolist (spec &rest body)
  "Loop over a list.
Evaluate BODY, destructuring LIST into SPEC, then evaluate RESULT
to get a return value, defaulting to nil.  The only hitch is that
spec must end in dotted style, collecting the rest of the list
into a var, like so: (a (b c) . rest)

\(fn (SPEC LIST [RESULT]) BODY...)"
  (declare (indent 1))
  (wg-dbind (loopspec list &optional result) spec
    (let ((rest (cdr (last loopspec))))
      (wg-with-gensyms (list-sym)
        `(let ((,list-sym ,list))
           (while ,list-sym
             (wg-dbind ,loopspec ,list-sym
               ,@body
               (setq ,list-sym ,rest)))
           ,result)))))


;;; numbers
(defun wg-within (num lo hi &optional hi-inclusive)
  "Return t when NUM is within bounds LO and HI.
HI-INCLUSIVE non-nil means the HI bound is inclusive."
  (and (>= num lo) (if hi-inclusive (<= num hi) (< num hi))))

(defun wg-int-to-b36-one-digit (i)
  "Return a character in 0..9 or A..Z from I, and integer 0<=I<32.
Cribbed from `org-id-int-to-b36-one-digit'."
  (cond ((not (wg-within i 0 36))
         (error "%s out of range" i))
        ((< i 10) (+ ?0 i))
        ((< i 36) (+ ?A i -10))))

(defun wg-b36-to-int-one-digit (i)
  "Turn a character 0..9, A..Z, a..z into a number 0..61.
The input I may be a character, or a single-letter string.
Cribbed from `org-id-b36-to-int-one-digit'."
  (and (stringp i) (setq i (string-to-char i)))
  (cond ((and (>= i ?0) (<= i ?9)) (- i ?0))
        ((and (>= i ?A) (<= i ?Z)) (+ (- i ?A) 10))
        (t (error "Invalid b36 character"))))

(defun wg-int-to-b36 (i &optional length)
  "Return a base 36 string from I."
  (let ((base 36) b36)
    (cl-labels ((add-digit () (push (wg-int-to-b36-one-digit (mod i base)) b36)
                           (setq i (/ i base))))
      (add-digit)
      (while (> i 0) (add-digit))
      (setq b36 (cl-map 'string 'identity b36))
      (if (not length) b36
        (concat (make-string (max 0 (- length (length b36))) ?0) b36)))))

(defun wg-b36-to-int (str)
  "Convert STR, a base-36 string, into the corresponding integer.
Cribbed from `org-id-b36-to-int'."
  (let ((result 0))
    (mapc (lambda (i)
            (setq result (+ (* result 36)
                            (wg-b36-to-int-one-digit i))))
          str)
    result))


;;; lists

(defmacro wg-removef-p (item seq-place &rest keys)
  "If ITEM is a `member
*' of SEQ-PLACE, remove it from SEQ-PLACE and return t.
Otherwise return nil.  KEYS can be any keywords accepted by `remove*'."
  `(> (length ,seq-place)
      (length (setf ,seq-place (cl-remove ,item ,seq-place ,@keys)))))

(defmacro wg-pushnew-p (item seq-place &rest keys)
  "If ITEM is not a `member' of SEQ-PLACE, push it to SEQ-PLACE and return t.
Otherwise return nil.  KEYS can be any keyword args accepted by `pushnew'."
  `(< (length ,seq-place)
      (length (cl-pushnew ,item ,seq-place ,@keys))))

(defun wg-range (start end)
  "Return a list of integers from START up to but not including END."
  (let (accum (i start))
    (while (< i end)
      (push i accum)
      (setq i (1+ i)))
    (nreverse accum)))

(defun wg-insert-before (elt list index)
  "Insert ELT into LIST before INDEX."
  (if (zerop index) (cons elt list)
    (-insert-at index elt list)))

(defun wg-move-elt (elt list index &rest keys)
  "Move ELT before INDEX in LIST.
KEYS is passed to `remove*'."
  (wg-insert-before elt (apply 'cl-remove elt list keys) index))

(defun wg-cyclic-nth (list n)
  "Return the Nth element of LIST, modded by the length of list."
  (nth (mod n (length list)) list))

(defun wg-cyclic-offset-elt (elt list n)
  "Cyclically offset ELT's position in LIST by N."
  (-when-let (pos (cl-position elt list))
    (wg-move-elt elt list (mod (+ n pos) (length list)))))

(defun wg-cyclic-nth-from-elt (elt list n &rest keys)
  "Return the elt in LIST N places cyclically from ELT.
If ELT is not present is LIST, return nil.
KEYS is passed to `position'."
  (-when-let (pos (apply 'cl-position elt list keys))
    (wg-cyclic-nth list (+ pos n))))

(defun wg-string-list-union (&optional list1 list2)
  "Return the `union' of LIST1 and LIST2, using `string=' as the test.
This only exists to get rid of duplicate lambdas in a few reductions."
  (cl-union list1 list2 :test 'string=))



;;; alists

(defun wg-aget (alist key &optional default)
  "Return the value of KEY in ALIST. Uses `assq'.
If PARAM is not found, return DEFAULT which defaults to nil."
  (aif (assq key alist) (cdr it) default))

(defun wg-aput (alist key value)
  "Return a new alist from ALIST with KEY's value set to VALUE."
  (let* ((found nil)
         (new (wg-docar (kvp alist)
                (if (not (eq key (car kvp))) kvp
                  (setq found (cons key value))))))
    (if found new (cons (cons key value) new))))

(defun wg-aremove (alist key)
  "`remove' KEY's key-value-pair from ALIST."
  (remove (assoc key alist) alist))


;;; symbols and strings
(defun wg-get-buffer (buffer-or-name)
  "Return BUFFER-OR-NAME's buffer, or error."
  (or (get-buffer buffer-or-name)
      (error "%S does not identify a buffer" buffer-or-name)))

(defun wg-buffer-name (buffer-or-name)
  "Return BUFFER-OR-NAME's `buffer-name', or error."
  (buffer-name (wg-get-buffer buffer-or-name)))

(defun wg-current-buffer-p (buffer-or-name)
  "Return t if BUFFER-OR-NAME is the current buffer, nil otherwise."
  (eq (wg-get-buffer buffer-or-name) (current-buffer)))

(defmacro wg-defstruct (name-form &rest slot-defs)
  "`defstruct' wrapper that namespace-prefixes all generated functions.
Note: this doesn't yet work with :conc-name, and possibly other
options."
  (declare (indent 2))
  (let* ((prefix "wg")
         (name (symbol-name name-form)) ; string type
         (prefixed-name (concat prefix "-" name))
         (symbol-prefixed-name (intern prefixed-name)))
    (cl-labels ((rebind (opstr)
                        (let ((oldfnsym (intern (concat opstr "-" prefixed-name)))
                              (newfnsym (intern (concat prefix "-" opstr "-" name))))
                          `((fset ',newfnsym (symbol-function ',oldfnsym))
                            (fmakunbound ',oldfnsym)))))
      ;; `eval-and-compile' gets rid of byte-comp warnings ("function `foo' not
      ;; known to be defined").  We can accomplish this with `declare-function'
      ;; too, but it annoyingly requires inclusion of the function's arglist,
      ;; which gets ugly.
      `(eval-and-compile
         (cl-defstruct ,symbol-prefixed-name ,@slot-defs)
         ,@(rebind "make")
         ,@(rebind "copy")
         ',symbol-prefixed-name))))

;; {{
(wg-defstruct session
  (uid (wg-generate-uid))
  (name)
  (modified)
  (parameters)
  (file-name)
  (version wg-version)
  (workgroup-list)
  (buf-list))

(wg-defstruct workgroup
  (uid (wg-generate-uid))
  (name)
  (modified)
  (parameters)
  (base-wconfig)
  (selected-frame-wconfig)
  (saved-wconfigs)
  (strong-buf-uids)
  (weak-buf-uids))

(wg-defstruct workgroup-state
  (undo-pointer)
  (undo-list))

(wg-defstruct wconfig
  (uid (wg-generate-uid))
  (name)
  (parameters)
  (left)
  (top)
  (width)
  (height)
  (vertical-scroll-bars)
  (scroll-bar-width)
  (wtree))

(wg-defstruct wtree
  (uid)
  (dir)
  (edges)
  (wlist))

(wg-defstruct win
  (uid)
  (parameters)
  (edges)
  (point)
  (start)
  (hscroll)
  (dedicated)
  (selected)
  (minibuffer-scroll)
  (buf-uid))

(wg-defstruct buf
  (uid (wg-generate-uid))
  (name)
  (file-name)
  (point)
  (mark)
  (local-vars)
  (special-data)
  ;; This may be used later:
  (gc))
;; }}


(defmacro wg-with-slots (obj slot-bindings &rest body)
  "Bind OBJ's slot values to symbols in BINDS, then eval BODY.
The car of each element of SLOT-BINDINGS is the bound symbol, and
the cadr as the accessor function."
  (declare (indent 2))
  (wg-with-gensyms (objsym)
    `(let* ((,objsym ,obj)
            ,@(wg-docar (slot slot-bindings)
                `(,(car slot) (,(cadr slot) ,objsym))))
       ,@body)))

(defun wg-add-or-remove-hooks (remove &rest pairs)
  "Add FUNCTION to or remove it from HOOK, depending on REMOVE."
  (dolist (pair (wg-partition pairs 2))
    (funcall (if remove 'remove-hook 'add-hook)
             (car pair) (cadr pair))))

(defmacro wg-set-parameter (place parameter value)
  "Set PARAMETER to VALUE at PLACE.
This needs to be a macro to allow specification of a setf'able place."
  (wg-with-gensyms (p v)
    `(let ((,p ,parameter) (,v ,value))
       (wg-pickelable-or-error ,p)
       (wg-pickelable-or-error ,v)
       (setf ,place (wg-aput ,place ,p ,v))
       ,v)))

(defun wg-time-to-b36 ()
  "Convert `current-time' into a b36 string."
  (apply 'concat (wg-docar (time (current-time))
                   (wg-int-to-b36 time 4))))

(defun wg-b36-to-time (b36)
  "Parse the time in B36 string from UID."
  (cl-loop for i from 0 to 8 by 4
           collect (wg-b36-to-int (cl-subseq b36 i (+ i 4)))))
(defalias 'wg-uid-to-time 'wg-b36-to-time)

(defun wg-generate-uid ()
  "Return a new uid."
  (concat (wg-time-to-b36) "-" (wg-int-to-b36 string-chars-consed)))

(defun wg-get-value (arg)
  "Get a value of ARG if it exists."
  (if (boundp `,arg) arg))

(defmacro wg-support (mode pkg params)
  "Macro to create (de)serialization functions for a buffer.
You need to save/restore a specific MODE which is loaded from a
package PKG.  In PARAMS you give local variables to save and a
deserialization function."
  (declare (indent 2))
  `(let ((mode-str (symbol-name ,mode))
         (args ,params))

     (eval `(defun ,(intern (format "wg-deserialize-%s-buffer" mode-str)) (buffer)
              "DeSerialization function created with `wg-support'.
Gets saved variables and runs code to restore a BUFFER."
              (when (require ',,pkg nil 'noerror)
                (wg-dbind (this-function variables) (wg-buf-special-data buffer)
                  (let ((default-directory (car variables))
                        (df (cdr (assoc 'deserialize ',,params)))
                        (user-vars (cadr variables)))
                    (if df
                        (funcall df buffer user-vars)
                      (get-buffer-create wg-default-buffer))
                    )))))

     (eval `(defun ,(intern (format "wg-serialize-%s-buffer" mode-str)) (buffer)
              "Serialization function created with `wg-support'.
Saves some variables to restore a BUFFER later."
              (when (get-buffer buffer)
                (with-current-buffer buffer
                  (when (eq major-mode ',,mode)
                    (let ((sf (cdr (assoc 'serialize ',,params)))
                          (save (cdr (assoc 'save ',,params))))
                      (list ',(intern (format "wg-deserialize-%s-buffer" mode-str))
                            (list default-directory
                                  (if sf
                                      (funcall sf buffer)
                                    (if save (mapcar 'wg-get-value save)))
                                  ))))))))
     ;; Maybe change a docstring for functions
     ;;(put (intern (format "wg-serialize-%s-buffer" (symbol-name mode)))
     ;;     'function-documentation
     ;;     (format "A function created by `wg-support'."))

     ;; Add function to `wg-special-buffer-serdes-functions' variable
     (eval `(add-to-list 'wg-special-buffer-serdes-functions
                         ',(intern (format "wg-serialize-%s-buffer" mode-str)) t))
     ))

(defconst wg-font-lock-keywords
  '(("(\\(wg-support\\|wg-support\\)[ \t]*"
     (1 font-lock-keyword-face)
     ;;(2 font-lock-keyword-face)
     )))
(font-lock-add-keywords 'emacs-lisp-mode wg-font-lock-keywords)

(defvar wg-current-session nil "Current session object.")
(defun wg-current-session (&optional noerror)
  "Return `wg-current-session' or error unless NOERROR."
  (or wg-current-session
      (if workgroups-mode
          (unless noerror (error "No session is defined"))
        (unless noerror
          (error "Activate workgroups with (workgroups-mode 1)")))))

;; locate-dominating-file
(defun wg-get-first-existing-dir (&optional dir)
  "Test if DIR exists and return it.
If not - try to go to the parent dir and do the same."
  (let* ((d (or dir default-directory)))
    (if (file-directory-p d) d
      (let* ((cur d) (parent (file-name-directory (directory-file-name cur))))
        (while (and (> (length cur) (length parent))
                    (not (file-directory-p parent)))
          (message "Test %s" parent)
          (setq cur parent)
          (setq parent (file-name-directory (directory-file-name cur))))
        parent))))


(defconst wg-pickel-identifier '~pickel!~
  "Symbol identifying a stream as a pickel.")

(defvar wg-pickel-pickelable-types
  '(integer
    float
    symbol
    string
    cons
    vector
    hash-table
    buffer
    marker
    wg-wconfig
    ;;window-configuration
    ;;frame
    ;;window
    ;;process
    )
  "Types pickel can serialize.")

(defvar wg-pickel-object-serializers
  '((integer    . identity)
    (float      . identity)
    (string     . identity)
    (symbol     . wg-pickel-symbol-serializer)
    (cons       . wg-pickel-cons-serializer)
    (vector     . wg-pickel-vector-serializer)
    (hash-table . wg-pickel-hash-table-serializer)
    (buffer     . wg-pickel-buffer-serializer)
    (marker     . wg-pickel-marker-serializer)
    ;;(window-configuration   . wg-pickel-window-configuration-serializer)
    )
  "Alist mapping types to object serialization functions.")
(defvar wg-pickel-object-deserializers
  '((s . wg-pickel-deserialize-uninterned-symbol)
    (c . wg-pickel-deserialize-cons)
    (v . wg-pickel-deserialize-vector)
    (h . wg-pickel-deserialize-hash-table)
    (b . wg-pickel-deserialize-buffer)
    (m . wg-pickel-deserialize-marker)
    (d . wg-pickel-deserialize-default)
    ;;(f . wg-pickel-deserialize-frame)
    )
  "Alist mapping type keys to object deserialization functions.")

(defvar wg-pickel-link-serializers
  '((cons       . wg-pickel-cons-link-serializer)
    (vector     . wg-pickel-vector-link-serializer)
    (hash-table . wg-pickel-hash-table-link-serializer))
  "Alist mapping types to link serialization functions.")
(defvar wg-pickel-link-deserializers
  `((c . wg-pickel-cons-link-deserializer)
    (v . wg-pickel-vector-link-deserializer)
    (h . wg-pickel-hash-table-link-deserializer))
  "Alist mapping type keys to link deserialization functions.")



;;; errors and predicates

(put 'wg-pickel-unpickelable-type-error
     'error-conditions
     '(error wg-pickel-errors wg-pickel-unpickelable-type-error))

(put 'wg-pickel-unpickelable-type-error
     'error-message
     "Attempt to pickel unpickelable type")

(defun wg-pickelable-or-error (obj)
  "Error when OBJ isn't pickelable."
  (unless (memq (type-of obj) wg-pickel-pickelable-types)
    (signal 'wg-pickel-unpickelable-type-error
            (format "Can't pickel objects of type: %S" (type-of obj))))
  (cl-typecase obj
    (cons
     (wg-pickelable-or-error (car obj))
     (wg-pickelable-or-error (cdr obj)))
    (vector
     (cl-map nil 'wg-pickelable-or-error obj))
    (hash-table
     (wg-dohash (key value obj)
       (wg-pickelable-or-error key)
       (wg-pickelable-or-error value)))))

(defun wg-pickel-p (obj)
  "Return t when OBJ is a pickel, nil otherwise."
  (and (consp obj) (eq (car obj) wg-pickel-identifier)))

;; accessor functions
(defun wg-pickel-default-serializer (object)
  "Return OBJECT's data."
  (list 'd (prin1-to-string object)))

(defun wg-pickel-object-serializer (obj)
  "Return the object serializer for the `type-of' OBJ."
  (or (wg-aget wg-pickel-object-serializers (type-of obj))
      #'wg-pickel-default-serializer))

(defun wg-pickel-link-serializer (obj)
  "Return the link serializer for the `type-of' OBJ."
  (wg-aget wg-pickel-link-serializers (type-of obj)))

(defun wg-pickel-object-deserializer (key)
  "Return the object deserializer for type key KEY, or error."
  (or (wg-aget wg-pickel-object-deserializers key)
      (error "Invalid object deserializer key: %S" key)))

(defun wg-pickel-link-deserializer (key)
  "Return the link deserializer for type key KEY, or error."
  (or (wg-aget wg-pickel-link-deserializers key)
      (error "Invalid link deserializer key: %S" key)))



;;; bindings

(defun wg-pickel-make-bindings-table (obj)
  "Return a table binding unique subobjects of OBJ to ids."
  (let ((binds (make-hash-table :test 'eq))
        (id -1))
    (cl-labels
        ((inner (obj)
                (unless (gethash obj binds)
                  (puthash obj (cl-incf id) binds)
                  (cl-case (type-of obj)
                    (cons
                     (inner (car obj))
                     (inner (cdr obj)))
                    (vector
                     (dotimes (idx (length obj))
                       (inner (aref obj idx))))
                    (hash-table
                     (wg-dohash (key val obj)
                       (inner key)
                       (inner val)))))))
      (inner obj)
      binds)))



;;; Objects
(defun wg-pickel-symbol-serializer (symbol)
  "Return SYMBOL's serialization."
  (cond ((eq symbol t) t)
        ((eq symbol nil) nil)
        ((intern-soft symbol) symbol)
        (t (list 's (symbol-name symbol)))))

(defun wg-pickel-deserialize-uninterned-symbol (name)
  "Return a new uninterned symbol from NAME."
  (make-symbol name))


;; buffer
(defun wg-pickel-buffer-serializer (buffer)
  "Return BUFFER's UID in workgroups buffer list."
  (list 'b (wg-add-buffer-to-buf-list buffer)))

(defun wg-pickel-deserialize-buffer (uid)
  "Return a restored buffer from it's UID."
  (wg-restore-buffer (wg-find-buf-by-uid uid)))


;; marker
(defun wg-pickel-marker-serializer (marker)
  "Return MARKER's data."
  (list 'm (list (marker-position marker)
                 (wg-add-buffer-to-buf-list (marker-buffer marker)))))

(defun wg-pickel-deserialize-marker (data)
  "Return marker from it's DATA."
  (let ((m (make-marker)))
    (set-marker m (car data) (wg-pickel-deserialize-buffer (car (cdr data))))))

(defun wg-pickel-deserialize-default (object)
  "Return data from OBJECT."
  (read object))

;; cons - http://www.gnu.org/software/emacs/manual/html_node/eintr/cons.html
(defun wg-pickel-cons-serializer (cons)
  "Return CONS's serialization."
  (list 'c))
(defun wg-pickel-deserialize-cons ()
  "Return a new cons cell initialized to nil."
  (cons nil nil))
(defun wg-pickel-cons-link-serializer (cons binds)
  "Return the serialization of CONS's links in BINDS."
  (list 'c
        (gethash cons binds)
        (gethash (car cons) binds)
        (gethash (cdr cons) binds)))
(defun wg-pickel-cons-link-deserializer (cons-id car-id cdr-id binds)
  "Relink a cons cell with its car and cdr in BINDS."
  (let ((cons (gethash cons-id binds)))
    (setcar cons (gethash car-id binds))
    (setcdr cons (gethash cdr-id binds))))



;; vector - http://www.gnu.org/software/emacs/manual/html_node/elisp/Vector-Functions.html
;; (wg-unpickel (wg-pickel (make-vector 9 'Z)))
;;
(defun wg-pickel-vector-serializer (vector)
  "Return VECTOR's serialization."
  (list 'v (length vector)))
(defun wg-pickel-deserialize-vector (length)
  "Return a new vector of length LENGTH."
  (make-vector length nil))
(defun wg-pickel-vector-link-serializer (vector binds)
  "Return the serialization of VECTOR's links in BINDS."
  (let (result)
    (dotimes (i (length vector) result)
      (setq result
            (nconc (list 'v
                         (gethash vector binds)
                         i
                         (gethash (aref vector i) binds))
                   result)))))

(defun wg-pickel-vector-link-deserializer (vector-id index value-id binds)
  "Relink a vector with its elements in BINDS."
  (aset (gethash vector-id binds) index (gethash value-id binds)))

;; hash table - http://www.gnu.org/software/emacs/manual/html_node/elisp/Hash-Tables.html
(defun wg-pickel-hash-table-serializer (table)
  "Return HASH-TABLE's serialization."
  (list 'h
        (hash-table-test table)
        (hash-table-size table)
        (hash-table-rehash-size table)
        (hash-table-rehash-threshold table)
        (hash-table-weakness table)))

(defun wg-pickel-deserialize-hash-table (test size rsize rthresh weakness)
  "Return a new hash-table with the specified properties."
  (make-hash-table :test test :size size :rehash-size rsize
                   :rehash-threshold rthresh :weakness weakness))

(defun wg-pickel-hash-table-link-serializer (table binds)
  "Return the serialization of TABLE's links in BINDS."
  (let (result)
    (wg-dohash (key value table result)
      (setq result
            (nconc (list 'h
                         (gethash key binds)
                         (gethash value binds)
                         (gethash table binds))
                   result)))))
(defun wg-pickel-hash-table-link-deserializer (key-id value-id table-id binds)
  "Relink a hash-table with its keys and values in BINDS."
  (puthash (gethash key-id binds)
           (gethash value-id binds)
           (gethash table-id binds)))


;; TODO
(defun wg-pickel-window-configuration-serializer (wc)
  "Return Window configuration WC's serialization."
  (list 'wc 1))

(defun wg-pickel-serialize-objects (binds)
  "Return a list of serializations of the objects in BINDS."
  (let (result)
    (wg-dohash (obj id binds result)
      (setq result
            (nconc (list id (funcall (wg-pickel-object-serializer obj) obj))
                   result)))))

(defun wg-pickel-deserialize-objects (serial-objects)
  "Return a hash-table of objects deserialized from SERIAL-OBJECTS."
  (let ((binds (make-hash-table)))
    (wg-destructuring-dolist ((id obj . rest) serial-objects binds)
      (puthash id
               (if (atom obj) obj
                 (wg-dbind (key . data) obj
                   (apply (wg-pickel-object-deserializer key) data)))
               binds))))



(defun wg-pickel-serialize-links (binds)
  "Return a list of serializations of the links between objects in BINDS."
  (let (result)
    (wg-dohash (obj id binds result)
      (awhen (wg-pickel-link-serializer obj)
        (setq result (nconc (funcall it obj binds) result))))))
(defun wg-pickel-deserialize-links (serial-links binds)
  "Return BINDS after relinking all its objects according to SERIAL-LINKS."
  (wg-destructuring-dolist ((key arg1 arg2 arg3 . rest) serial-links binds)
    (funcall (wg-pickel-link-deserializer key) arg1 arg2 arg3 binds)))

(defun wg-pickel (obj)
  "Return the serialization of OBJ."
  (wg-pickelable-or-error obj)
  (let ((binds (wg-pickel-make-bindings-table obj)))
    (list wg-pickel-identifier
          (wg-pickel-serialize-objects binds)
          (wg-pickel-serialize-links binds)
          (gethash obj binds))))

(defun wg-pickel-to-string (obj)
  "Serialize OBJ to a string and return the string."
  (format "%S" (wg-pickel obj)))

(defun wg-unpickel (pickel)
  "Return the deserialization of PICKEL."
  (unless (wg-pickel-p pickel)
    (error "Attempt to unpickel a non-pickel."))
  (wg-dbind (id serial-objects serial-links result) pickel
    (gethash
     result
     (wg-pickel-deserialize-links
      serial-links
      (wg-pickel-deserialize-objects serial-objects)))))

;; `wg-pre-window-configuration-change-hook' implementation advice
(cl-macrolet ((define-p-w-c-c-h-advice
                (fn)
                `(defadvice ,fn (before wg-pre-window-configuration-change-hook)
                   "Call `wg-update-working-wconfig-hook' before this
function to save up-to-date undo information before the
window-configuration changes."
                   (run-hooks 'wg-pre-window-configuration-change-hook))))
  (define-p-w-c-c-h-advice split-window)
  (define-p-w-c-c-h-advice enlarge-window)
  (define-p-w-c-c-h-advice delete-window)
  (define-p-w-c-c-h-advice delete-other-windows)
  (define-p-w-c-c-h-advice delete-windows-on)
  (define-p-w-c-c-h-advice switch-to-buffer)
  (define-p-w-c-c-h-advice set-window-buffer))


(defadvice save-buffers-kill-emacs (around wg-freeze-wconfig)
  "`save-buffers-kill-emacs' calls `list-processes' when active
processes exist, screwing up the window config right before
Workgroups saves it.  This advice freezes `wg-current-wconfig' in
its correct state, prior to any window-config changes caused by
`s-b-k-e'."
  (wg-with-current-wconfig nil (wg-frame-to-wconfig)
    ad-do-it))

(defadvice select-frame (before wg-update-current-workgroup-working-wconfig)
  "Update `selected-frame's current workgroup's working-wconfig.
Before selecting a new frame."
  (wg-update-current-workgroup-working-wconfig))

(defun wg-enable-all-advice ()
  "Enable and activate all of Workgroups' advice."
  ;; switch-to-buffer
  (ad-enable-advice 'switch-to-buffer 'after 'wg-auto-associate-buffer)
  (ad-enable-advice 'switch-to-buffer 'before 'wg-pre-window-configuration-change-hook)
  (ad-activate 'switch-to-buffer)

  ;; set-window-buffer
  (ad-enable-advice 'set-window-buffer 'after 'wg-auto-associate-buffer)
  (ad-enable-advice 'set-window-buffer 'before 'wg-pre-window-configuration-change-hook)
  (ad-activate 'set-window-buffer)

  ;; split-window
  (ad-enable-advice 'split-window 'before 'wg-pre-window-configuration-change-hook)
  (ad-activate 'split-window)

  ;; enlarge-window
  (ad-enable-advice 'enlarge-window 'before 'wg-pre-window-configuration-change-hook)
  (ad-activate 'enlarge-window)

  ;; delete-window
  (ad-enable-advice 'delete-window 'before 'wg-pre-window-configuration-change-hook)
  (ad-activate 'delete-window)

  ;; delete-other-windows
  (ad-enable-advice 'delete-other-windows 'before 'wg-pre-window-configuration-change-hook)
  (ad-activate 'delete-other-windows)

  ;; delete-windows-on
  (ad-enable-advice 'delete-windows-on 'before 'wg-pre-window-configuration-change-hook)
  (ad-activate 'delete-windows-on)

  ;; save-buffers-kill-emacs
  (ad-enable-advice 'save-buffers-kill-emacs 'around 'wg-freeze-wconfig)
  (ad-activate 'save-buffers-kill-emacs)

  ;; select-frame
  ;;(ad-enable-advice 'select-frame 'before
  ;;                  'wg-update-current-workgroup-working-wconfig)
  ;;(ad-activate 'select-frame)
  )


;; disable all advice
;; (wg-disable-all-advice)
(defun wg-disable-all-advice ()
  "Disable and deactivate all of Workgroups' advice."
  ;; switch-to-buffer
  (ad-disable-advice 'switch-to-buffer 'after  'wg-auto-associate-buffer)
  (ad-disable-advice 'switch-to-buffer 'before 'wg-pre-window-configuration-change-hook)
  (ad-deactivate 'switch-to-buffer)

  ;; set-window-buffer
  (ad-disable-advice 'set-window-buffer 'after  'wg-auto-associate-buffer)
  (ad-disable-advice 'set-window-buffer 'before 'wg-pre-window-configuration-change-hook)
  (ad-deactivate 'set-window-buffer)

  ;; split-window
  (ad-disable-advice 'split-window 'before 'wg-pre-window-configuration-change-hook)
  (ad-deactivate 'split-window)

  ;; enlarge-window
  (ad-disable-advice 'enlarge-window 'before 'wg-pre-window-configuration-change-hook)
  (ad-deactivate 'enlarge-window)

  ;; delete-window
  (ad-disable-advice 'delete-window 'before 'wg-pre-window-configuration-change-hook)
  (ad-deactivate 'delete-window)

  ;; delete-other-windows
  (ad-disable-advice 'delete-other-windows 'before 'wg-pre-window-configuration-change-hook)
  (ad-deactivate 'delete-other-windows)

  ;; delete-windows-on
  (ad-disable-advice 'delete-windows-on    'before 'wg-pre-window-configuration-change-hook)
  (ad-deactivate 'delete-windows-on)

  ;; save-buffers-kill-emacs
  (ad-disable-advice 'save-buffers-kill-emacs 'around 'wg-freeze-wconfig)
  (ad-deactivate 'save-buffers-kill-emacs)

  ;; select-frame
  ;;(ad-disable-advice 'select-frame 'before
  ;;                   'wg-update-current-workgroup-working-wconfig)
  ;;(ad-deactivate 'select-frame)
  )


;; buffer auto-association advice

(defcustom wg-buffer-auto-association-on t
  "Non-nil means buffer auto-association is on.
-nil means it's off.  See `wg-buffer-auto-association'."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-buffer-auto-association 'weak
  "Specifies the behavior for auto-associating buffers with workgroups.

When a buffer is made visible in a window it can be automatically
associated with the current workgroup in the window's frame.
This setting determines whether and how that happens.

Allowable values:

`weak' - weakly associate the buffer with the workgroup
`strong' - strongly associate the buffer with the workgroup

A function (a function-symbol or a lambda) - `funcall' the function to
determine whether and how to associate the buffer with the
workgroup.  The function should accept two arguments -- the
buffer and the workgroup -- and should return one of the
allowable values for this variable.

`nil' or any other value - don't associate the buffer with the
workgroup.

Becomes workgroup-local when set with `wg-set-workgroup-parameter'.
Becomes session-local when set with `wg-set-session-parameter'."
  :type 'sexp
  :group 'workgroups)

(defcustom wg-dissociate-buffer-on-kill-buffer t
  "Non-nil means dissociate buffers killed with `kill-buffer'."
  :type 'boolean
  :group 'workgroups)

(defun wg-auto-associate-buffer-helper (workgroup buffer assoc)
  "Associate BUFFER with WORKGROUP based on ASSOC.
See `wg-buffer-auto-association' for allowable values of ASSOC."
  (cond ((memq assoc '(weak strong))
         (wg-workgroup-associate-bufobj workgroup buffer (eq assoc 'weak)))
        ((functionp assoc)
         (wg-auto-associate-buffer-helper
          workgroup buffer (funcall assoc workgroup buffer)))
        (t nil)))

(defun wg-auto-associate-buffer (buffer &optional frame)
  "Conditionally associate BUFFER with the current workgroup in FRAME.
Frame defaults to `selected-frame'.  See `wg-buffer-auto-association'."
  (when wg-buffer-auto-association-on
    (-when-let* ((wg (wg-current-workgroup t frame))
                 (b (get-buffer buffer)))
      (unless (or (wg-workgroup-bufobj-association-type wg buffer)
                  (member wg wg-deactivation-list)
                  (member (buffer-name b) wg-associate-blacklist)
                  (not (or (buffer-file-name b)
                           (eq (buffer-local-value 'major-mode b) 'dired-mode))))
        (wg-auto-associate-buffer-helper
         wg buffer (wg-local-value 'wg-buffer-auto-association wg))))))

(defadvice switch-to-buffer (after wg-auto-associate-buffer)
  "Automatically associate the buffer with the current workgroup."
  (wg-auto-associate-buffer ad-return-value))

(defadvice set-window-buffer (after wg-auto-associate-buffer)
  "Automatically associate the buffer with the current workgroup."
  (wg-auto-associate-buffer
   (ad-get-arg 1)
   (window-frame (or (ad-get-arg 0) (selected-window)))))

(defun wg-mode-line-string ()
  "Return the string to be displayed in the mode-line."
  (let ((wg (wg-current-workgroup t))
        (wg-use-faces wg-mode-line-use-faces))
    (cond (wg (wg-fontify " "
                (:brace wg-mode-line-decor-left-brace)
                (:mode (wg-workgroup-name wg))
                (if wg-flag-modified
                    (concat
                     (wg-add-face :div wg-mode-line-decor-divider)
                     ;;(if (window-dedicated-p)
                     ;;    wg-mode-line-decor-window-dedicated
                     ;;  wg-mode-line-decor-window-undedicated)
                     ;;(wg-add-face :div wg-mode-line-decor-divider)
                     (if (wg-session-modified (wg-current-session))
                         wg-mode-line-decor-session-modified
                       wg-mode-line-decor-session-unmodified)
                     (if (wg-workgroup-modified wg)
                         wg-mode-line-decor-workgroup-modified
                       wg-mode-line-decor-workgroup-unmodified)))
                (:brace wg-mode-line-decor-right-brace)))
          (t (if wg-display-nowg
                 (wg-fontify " "
                   (:brace wg-mode-line-decor-left-brace)
                   (:mode wg-nowg-string)
                   (:brace wg-mode-line-decor-right-brace))
               "")))))

(defun wg-change-modeline ()
  "Add Workgroups' mode-line format to `mode-line-format'."
  (unless (assq 'wg-mode-line-display-on mode-line-format)
    (let ((format '(wg-mode-line-display-on (:eval (wg-mode-line-string))))
          (pos (or (cl-position 'mode-line-position mode-line-format) 10)))
      (set-default 'mode-line-format (-insert-at (1+ pos) format mode-line-format))
      (force-mode-line-update))))

(defun wg-remove-mode-line-display ()
  "Remove Workgroups' mode-line format from `mode-line-format'."
  (awhen (assq 'wg-mode-line-display-on mode-line-format)
    (set-default 'mode-line-format (remove it mode-line-format))
    (force-mode-line-update)))

(defun wg-add-workgroups-mode-minor-mode-entries ()
  "Add Workgroups' minor-mode entries.
Adds entries to `minor-mode-list', `minor-mode-alist' and
`minor-mode-map-alist'."
  (cl-pushnew 'workgroups-mode minor-mode-list)
  (cl-pushnew '(workgroups-mode wg-modeline-string) minor-mode-alist :test 'equal)
  (setq minor-mode-map-alist
        (cons (cons 'workgroups-mode (wg-make-workgroups-mode-map))
              (delete (assoc 'workgroups-mode minor-mode-map-alist)
                      minor-mode-map-alist))))

(defun wg-fill-keymap (keymap &rest binds)
  "Return KEYMAP after defining in it all keybindings in BINDS."
  (while binds
    (define-key keymap (car binds) (cadr binds))
    (setq binds (cddr binds)))
  keymap)

(defvar wg-prefixed-map
  (wg-fill-keymap
   (make-sparse-keymap)

   ;; workgroups
   (kbd "C-c")        'wg-create-workgroup
   (kbd "c")          'wg-create-workgroup
   (kbd "A")          'wg-rename-workgroup
   (kbd "C-'")        'wg-switch-to-workgroup
   (kbd "'")          'wg-switch-to-workgroup
   (kbd "C-v")        'wg-switch-to-workgroup
   (kbd "v")          'wg-switch-to-workgroup

   ;; session
   (kbd "C-s")        'wg-save-session
   (kbd "C-w")        'wg-save-session-as
   (kbd "C-f")        'wg-open-session

   ;; killing and yanking
   (kbd "C-k")        'wg-kill-workgroup
   (kbd "k")          'wg-kill-workgroup
   (kbd "C-y")        'wg-yank-wconfig
   (kbd "y")          'wg-yank-wconfig
   (kbd "M-k")        'wg-kill-workgroup-and-buffers
   (kbd "K")          'wg-delete-other-workgroups


   ;; workgroup switching
   (kbd "C-j")        'wg-switch-to-workgroup-at-index
   (kbd "j")          'wg-switch-to-workgroup-at-index
   (kbd "0")          'wg-switch-to-workgroup-at-index-0
   (kbd "1")          'wg-switch-to-workgroup-at-index-1
   (kbd "2")          'wg-switch-to-workgroup-at-index-2
   (kbd "3")          'wg-switch-to-workgroup-at-index-3
   (kbd "4")          'wg-switch-to-workgroup-at-index-4
   (kbd "5")          'wg-switch-to-workgroup-at-index-5
   (kbd "6")          'wg-switch-to-workgroup-at-index-6
   (kbd "7")          'wg-switch-to-workgroup-at-index-7
   (kbd "8")          'wg-switch-to-workgroup-at-index-8
   (kbd "9")          'wg-switch-to-workgroup-at-index-9
   (kbd "C-p")        'wg-switch-to-workgroup-left
   (kbd "p")          'wg-switch-to-workgroup-left
   (kbd "C-n")        'wg-switch-to-workgroup-right
   (kbd "n")          'wg-switch-to-workgroup-right
   (kbd "C-a")        'wg-switch-to-previous-workgroup
   (kbd "a")          'wg-switch-to-previous-workgroup


   ;; updating and reverting
   ;; wconfig undo/redo
   (kbd "C-r")        'wg-revert-workgroup
   (kbd "r")          'wg-revert-workgroup
   (kbd "C-S-r")      'wg-revert-all-workgroups
   (kbd "R")          'wg-revert-all-workgroups
   (kbd "<left>")     'wg-undo-wconfig-change
   (kbd "<right>")    'wg-redo-wconfig-change
   (kbd "[")          'wg-undo-wconfig-change
   (kbd "]")          'wg-redo-wconfig-change


   ;; wconfig save/restore
   (kbd "C-d C-s")    'wg-save-wconfig
   (kbd "C-d C-'")    'wg-restore-saved-wconfig
   (kbd "C-d C-k")    'wg-kill-saved-wconfig


   ;; workgroup movement
   (kbd "C-,")        'wg-offset-workgroup-left
   (kbd "C-.")        'wg-offset-workgroup-right

   ;; toggling
   (kbd "C-t C-m")    'wg-toggle-mode-line-display
   (kbd "C-t C-d")    'wg-toggle-window-dedicated-p


   ;; misc
   (kbd "!")          'wg-reset
   (kbd "?")          'wg-help

   )
  "The keymap that sits on `wg-prefix-key'.")

(defun wg-make-workgroups-mode-map ()
  "Return Workgroups' minor-mode-map.
This map includes `wg-prefixed-map' on `wg-prefix-key', as well
as Workgroups' command remappings."
  (let ((map (make-sparse-keymap)))
    (define-key map wg-prefix-key
      wg-prefixed-map)
    (when (and (fboundp 'winner-undo)
               (fboundp 'winner-redo))
      (define-key map [remap winner-undo] 'wg-undo-wconfig-change)
      (define-key map [remap winner-redo] 'wg-redo-wconfig-change))
    (setq workgroups-mode-map map)))


(defun wg-min-size (dir)
  "Return the minimum window size in split direction DIR."
  (if dir wg-window-min-height wg-window-min-width))

(defun wg-actual-min-size (dir)
  "Return the actual minimum window size in split direction DIR."
  (if dir wg-actual-min-height wg-actual-min-width))

(defmacro wg-with-edges (w spec &rest body)
  "Bind W's edge list to SPEC and eval BODY."
  (declare (indent 2))
  `(wg-dbind ,spec (wg-w-edges ,w) ,@body))

(defmacro wg-with-bounds (wtree dir spec &rest body)
  "Bind SPEC to W's bounds in DIR, and eval BODY.
\"bounds\" are a direction-independent way of dealing with edge lists."
  (declare (indent 3))
  (wg-with-gensyms (dir-sym l1 t1 r1 b1)
    (wg-dbind (ls1 hs1 lb1 hb1) spec
      `(wg-with-edges ,wtree (,l1 ,t1 ,r1 ,b1)
         (cond (,dir (let ((,ls1 ,l1) (,hs1 ,r1) (,lb1 ,t1) (,hb1 ,b1))
                       ,@body))
               (t    (let ((,ls1 ,t1) (,hs1 ,b1) (,lb1 ,l1) (,hb1 ,r1))
                       ,@body)))))))

(defun wg-set-bounds (w dir ls hs lb hb)
  "Set W's edges in DIR with bounds LS HS LB and HB."
  (wg-set-edges w (if dir (list ls lb hs hb) (list lb ls hb hs))))

(defun wg-first-win (w)
  "Return the first actual window in W."
  (if (wg-win-p w) w
    (wg-first-win (car (wg-wtree-wlist w)))))

(defun wg-last-win (w)
  "Return the last actual window in W."
  (if (wg-win-p w) w
    (wg-last-win (-last-item (wg-wtree-wlist w)))))

(defun wg-minify-win (w)
  "Set W's edges to the smallest allowable."
  (let* ((edges (wg-w-edges w))
         (left (car edges))
         (top (cadr edges)))
    (wg-set-edges w (list left top
                          (+ left wg-actual-min-width)
                          (+ top  wg-actual-min-height)))))

(defun wg-w-size (w &optional height)
  "Return the width or height of W, calculated from its edge list."
  (wg-with-edges w (l1 t1 r1 b1)
    (if height (- b1 t1) (- r1 l1))))

(defun wg-adjust-w-size (w width-fn height-fn &optional new-left new-top)
  "Adjust W's width and height with WIDTH-FN and HEIGHT-FN."
  (wg-with-edges w (left top right bottom)
    (let ((left (or new-left left)) (top (or new-top top)))
      (wg-set-edges (wg-copy-w w)
                    (list left
                          top
                          (+ left (funcall width-fn  (- right  left)))
                          (+ top  (funcall height-fn (- bottom top))))))))

(defun wg-scale-w-size (w width-scale height-scale)
  "Scale W's size by WIDTH-SCALE and HEIGHT-SCALE."
  (cl-labels
      ((wscale (width)  (truncate (* width  width-scale)))
       (hscale (height) (truncate (* height height-scale))))
    (wg-adjust-w-size w #'wscale #'hscale)))

(defun wg-restore-window (win)
  "Restore WIN in `selected-window'."
  (let ((selwin (selected-window))
        (buf (wg-find-buf-by-uid (wg-win-buf-uid win))))
    (if (not buf)
        (wg-restore-default-buffer)
      (when (wg-restore-buffer buf t)

        ;; Restore various positions in WINDOW from their values in WIN
        ;; (wg-restore-window-positions win selwin)
        (let ((window (or selwin (selected-window))))
          (wg-with-slots win
              ((win-point wg-win-point)
               (win-start wg-win-start)
               (win-hscroll wg-win-hscroll))
            (set-window-start window win-start t)
            (set-window-hscroll window win-hscroll)
            (set-window-point
             window
             (cond ((not wg-restore-point) win-start)
                   ((eq win-point :max) (point-max))
                   (t win-point)))
            (when (>= win-start (point-max)) (recenter))))

        (when wg-restore-window-dedicated-p
          (set-window-dedicated-p selwin (wg-win-dedicated win)))))
    (ignore-errors
      (set-window-prev-buffers
       selwin (wg-unpickel (wg-win-parameter win 'prev-buffers)))
      (set-window-next-buffers
       selwin (wg-unpickel (wg-win-parameter win 'next-buffers))))
    (dolist (param '(window-side window-slot))
      (let ((value (wg-win-parameter win param)))
        (when value
          (set-window-parameter selwin param value))))))


(defun wg-window-point (ewin)
  "Return `point' or :max.  See `wg-restore-point-max'.
EWIN should be an Emacs window object."
  (let ((p (window-point ewin)))
    (if (and wg-restore-point-max (= p (point-max))) :max p)))

(defun wg-win-parameter (win parameter &optional default)
  "Return WIN's value for PARAMETER.
If PARAMETER is not found, return DEFAULT which defaults to nil.
SESSION nil defaults to the current session."
  (wg-aget (wg-win-parameters win) parameter default))

(defun wg-set-win-parameter (win parameter value)
  "Set WIN's value of PARAMETER to VALUE.
SESSION nil means use the current session.
Return value."
  (wg-set-parameter (wg-win-parameters win) parameter value)
  value)
;; (wg-win-parameters (wg-window-to-win (selected-window)))

(defun wg-window-to-win (&optional window)
  "Return the serialization (a wg-win) of Emacs window WINDOW."
  (let ((window (or window (selected-window)))
        (selected (eq window (selected-window)))
        win)
    (with-selected-window window
      (setq win
            (wg-make-win
             :edges              (window-edges window)
             :point              (wg-window-point window)
             :start              (window-start window)
             :hscroll            (window-hscroll window)
             :selected           selected
             :minibuffer-scroll  (eq window minibuffer-scroll-window)
             :dedicated          (window-dedicated-p window)
             :buf-uid            (wg-buffer-uid-or-add (window-buffer window))))
      (unless (version< emacs-version "24")
        ;; To solve: https://github.com/pashinin/workgroups2/issues/51
        ;; shouldn't ignore here
        (ignore-errors
          (wg-set-win-parameter
           win 'next-buffers (wg-pickel (remove nil (cl-subseq (window-next-buffers window) 0 4))))
          (wg-set-win-parameter
           win 'prev-buffers (wg-pickel (remove nil (cl-subseq (window-prev-buffers window) 0 4)))))
        (dolist (param '(window-side window-slot))
          (let ((value (window-parameter window param)))
            (when value
              (wg-set-win-parameter win param value))))))
    win))

(defun wg-toggle-window-dedicated-p ()
  "Toggle `window-dedicated-p' in `selected-window'."
  (interactive)
  (set-window-dedicated-p nil (not (window-dedicated-p)))
  (force-mode-line-update t)
  (wg-fontified-message
    (:cmd "Window:")
    (:cur (concat (unless (window-dedicated-p) " not") " dedicated"))))

(defun wg-w-edges (w)
  "Return W's edge list."
  (cl-etypecase w
    (wg-win (wg-win-edges w))
    (wg-wtree (wg-wtree-edges w))))

(defun wg-copy-w (w)
  "Return a copy of W.  W should be a wg-win or a wg-wtree."
  (cl-etypecase w
    (wg-win (wg-copy-win w))
    (wg-wtree (wg-copy-wtree w))))

(defun wg-set-edges (w edges)
  "Set W's EDGES list, and return W."
  (cl-etypecase w
    (wg-win (setf (wg-win-edges w) edges))
    (wg-wtree (setf (wg-wtree-edges w) edges)))
  w)

(defun wg-equal-wtrees (w1 w2)
  "Return t when W1 and W2 have equal structure."
  (cond ((and (wg-win-p w1) (wg-win-p w2))
         (equal (wg-w-edges w1) (wg-w-edges w2)))
        ((and (wg-wtree-p w1) (wg-wtree-p w2))
         (and (eq (wg-wtree-dir w1) (wg-wtree-dir w2))
              (equal (wg-wtree-edges w1) (wg-wtree-edges w2))
              (cl-every #'wg-equal-wtrees
                        (wg-wtree-wlist w1)
                        (wg-wtree-wlist w2))))))

(defun wg-normalize-wtree (wtree)
  "Clean up and return a new wtree from WTREE.
Recalculate the edge lists of all subwins, and remove subwins
outside of WTREE's bounds.  If there's only one element in the
new wlist, return it instead of a new wtree."
  (if (wg-win-p wtree) wtree
    (wg-with-slots wtree ((dir wg-wtree-dir)
                          (wlist wg-wtree-wlist))
      (wg-with-bounds wtree dir (ls1 hs1 lb1 hb1)
        (let* ((min-size (wg-min-size dir))
               (max (- hb1 1 min-size))
               (lastw (-last-item wlist)))
          (cl-labels
              ((mapwl
                (wl)
                (wg-dbind (sw . rest) wl
                  (cons (wg-normalize-wtree
                         (wg-set-bounds
                          sw dir ls1 hs1 lb1
                          (setq lb1 (if (eq sw lastw) hb1
                                      (let ((hb2 (+ lb1 (wg-w-size sw dir))))
                                        (if (>= hb2 max) hb1 hb2))))))
                        (when (< lb1 max) (mapwl rest))))))
            (let ((new (mapwl wlist)))
              (if (not (cdr new)) (car new)
                (setf (wg-wtree-wlist wtree) new)
                wtree))))))))

(defun wg-scale-wtree (wtree wscale hscale)
  "Return a copy of WTREE with its dimensions scaled by WSCALE and HSCALE.
All WTREE's subwins are scaled as well."
  (let ((scaled (wg-scale-w-size wtree wscale hscale)))
    (if (wg-win-p wtree) scaled
      (wg-asetf (wg-wtree-wlist scaled)
                (wg-docar (sw it) (wg-scale-wtree sw wscale hscale)))
      scaled)))

(defun wg-wtree-buf-uids (wtree)
  "Return a new list of the buf uids of all wins in WTREE."
  (if (not wtree)
      (error "WTREE is nil in `wg-wtree-buf-uids'!"))
  (wg-flatten-wtree wtree 'wg-win-buf-uid))


(defun wg-wtree-unique-buf-uids (wtree)
  "Return a list of the unique buf uids of all wins in WTREE."
  (cl-remove-duplicates (wg-wtree-buf-uids wtree) :test 'string=))


(defun wg-reset-window-tree ()
  "Delete all but one window in `selected-frame', and reset
various parameters of that window in preparation for restoring
a wtree."
  (delete-other-windows)
  (set-window-dedicated-p nil nil))

(defun wg-restore-window-tree-helper (w)
  "Recursion helper for `wg-restore-window-tree' W."
  (if (wg-wtree-p w)
      (cl-loop with dir = (wg-wtree-dir w)
               for (win . rest) on (wg-wtree-wlist w)
               do (when rest (split-window nil (wg-w-size win dir) (not dir)))
               do (wg-restore-window-tree-helper win))
    (wg-restore-window w)
    (when (wg-win-selected w)
      (setq wg-window-tree-selected-window (selected-window)))
    (when (wg-win-minibuffer-scroll w)
      (setq minibuffer-scroll-window (selected-window)))
    (other-window 1)))

(defun wg-restore-window-tree (wtree)
  "Restore WTREE in `selected-frame'."
  (let ((window-min-width wg-window-min-width)
        (window-min-height wg-window-min-height)
        (wg-window-tree-selected-window nil))
    (wg-reset-window-tree)
    (wg-restore-window-tree-helper wtree)
    (awhen wg-window-tree-selected-window (select-window it))))

(defun wg-window-tree-to-wtree (&optional window-tree)
  "Return the serialization (a wg-wtree) of Emacs window tree WINDOW-TREE."
  (wg-barf-on-active-minibuffer)
  (unless window-tree
    (setq window-tree (window-tree)))
  (cl-labels
      ((inner (w) (if (windowp w) (wg-window-to-win w)
                    (wg-dbind (dir edges . wins) w
                      (wg-make-wtree
                       :dir    dir
                       :edges  edges
                       :wlist  (mapcar #'inner wins))))))
    (let ((w (car window-tree)))
      (when (and (windowp w) (window-minibuffer-p w))
        (error "Workgroups can't operate on minibuffer-only frames."))
      (inner w))))


(defun wg-flatten-wtree (wtree &optional key)
  "Return a new list by flattening WTREE.
KEY non returns returns a list of WTREE's wins.
KEY non-nil returns a list of the results of calling KEY on each win."
  (cl-labels
      ((inner (w) (if (wg-win-p w) (list (if key (funcall key w) w))
                    (cl-mapcan #'inner (wg-wtree-wlist w)))))
    (inner wtree)))

(defun wg-reverse-wlist (w &optional dir)
  "Reverse W's wlist and those of all its sub-wtrees in direction DIR.
If DIR is nil, reverse WTREE horizontally.
If DIR is 'both, reverse WTREE both horizontally and vertically.
Otherwise, reverse WTREE vertically."
  (cl-labels
      ((inner (w) (if (wg-win-p w) w
                    (wg-with-slots w ((d1 wg-wtree-dir))
                      (wg-make-wtree
                       :dir d1
                       :edges (wg-wtree-edges w)
                       :wlist (let ((wl2 (mapcar #'inner (wg-wtree-wlist w))))
                                (if (or (eq dir 'both) (eq dir d1))
                                    (nreverse wl2)
                                  wl2)))))))
    (wg-normalize-wtree (inner w))))

(defun wg-wtree-move-window (wtree offset)
  "Offset `selected-window' OFFSET places in WTREE."
  (cl-labels
      ((inner (w) (if (wg-win-p w) w
                    (wg-with-slots w ((wlist wg-wtree-wlist))
                      (wg-make-wtree
                       :dir (wg-wtree-dir w)
                       :edges (wg-wtree-edges w)
                       :wlist (aif (cl-find t wlist :key 'wg-win-selected)
                                  (wg-cyclic-offset-elt it wlist offset)
                                (mapcar #'inner wlist)))))))
    (wg-normalize-wtree (inner wtree))))

(defun wg-frame-to-wconfig (&optional frame)
  "Return the serialization (a wg-wconfig) of Emacs frame FRAME.
FRAME nil defaults to `selected-frame'."
  (let* ((frame (or frame (selected-frame)))
         (fullscrn (frame-parameter frame 'fullscreen)))
    (wg-make-wconfig
     :left                  (frame-parameter frame 'left)
     :top                   (frame-parameter frame 'top)
     :width                 (frame-parameter frame 'width)
     :height                (frame-parameter frame 'height)
     :parameters            `((fullscreen . ,fullscrn))
     :vertical-scroll-bars  (frame-parameter frame 'vertical-scroll-bars)
     :scroll-bar-width      (frame-parameter frame 'scroll-bar-width)
     :wtree                 (wg-window-tree-to-wtree (window-tree frame))
     )))

(defun wg-current-wconfig ()
  "Return the current wconfig.
If `wg-current-wconfig' is non-nil, return it.  Otherwise return
`wg-frame-to-wconfig'."
  (or (frame-parameter nil 'wg-current-wconfig)
      (wg-frame-to-wconfig)))

(defmacro wg-with-current-wconfig (frame wconfig &rest body)
  "Eval BODY with WCONFIG current in FRAME.
FRAME nil defaults to `selected-frame'."
  (declare (indent 2))
  (wg-with-gensyms (frame-sym old-value)
    `(let* ((,frame-sym (or ,frame (selected-frame)))
            (,old-value (frame-parameter ,frame-sym 'wg-current-wconfig)))
       (unwind-protect
           (progn
             (set-frame-parameter ,frame-sym 'wg-current-wconfig ,wconfig)
             ,@body)
         (when (frame-live-p ,frame-sym)
           (set-frame-parameter ,frame-sym 'wg-current-wconfig ,old-value))))))

(defun wg-make-blank-wconfig (&optional buffer)
  "Return a new blank wconfig.
BUFFER or `wg-default-buffer' is visible in the only window."
  (save-window-excursion
    (delete-other-windows)
    (switch-to-buffer (or buffer wg-default-buffer))
    (wg-frame-to-wconfig)))

;;; base wconfig updating

(defun wg-update-working-wconfig-on-delete-frame (frame)
  "Update FRAME's current workgroup's working-wconfig before
FRAME is deleted, so we don't lose its state."
  (wg-flag-session-modified)
  (with-selected-frame frame
    (wg-update-current-workgroup-working-wconfig)))

(defun wg-update-working-wconfig-on-make-frame (frame)
  "Update FRAME's current workgroup's working-wconfig before
FRAME is deleted, so we don't lose its state."
  (if (> (length (frame-list)) 1)
      (wg-flag-session-modified))
  ;;(with-selected-frame frame
  ;;  (wg-update-current-workgroup-working-wconfig))
  )

(defun wg-wconfig-buf-uids (wconfig)
  "Return WCONFIG's wtree's `wg-wtree-buf-uids'."
  (if (not (wg-wconfig-wtree wconfig))
      (error "WTREE is nil in `wg-wconfig-buf-uids'!"))
  (wg-wtree-unique-buf-uids (wg-wconfig-wtree wconfig)))

(defun wg-wconfig-restore-frame-position (wconfig &optional frame)
  "Use WCONFIG to restore FRAME's position.
If frame is nil then `selected-frame'."
  (-when-let* ((left (wg-wconfig-left wconfig))
               (top (wg-wconfig-top wconfig)))
    ;; Check that arguments are integers
    ;; Problem: https://github.com/pashinin/workgroups2/issues/15
    (if (and (integerp left)
             (integerp top))
        (set-frame-position frame left top))))

(defun wg-wconfig-restore-scroll-bars (wconfig)
  "Restore `selected-frame's scroll-bar settings from WCONFIG."
  (set-frame-parameter
   nil 'vertical-scroll-bars (wg-wconfig-vertical-scroll-bars wconfig))
  (set-frame-parameter
   nil 'scroll-bar-width (wg-wconfig-scroll-bar-width wconfig)))

(defun wg-scale-wconfigs-wtree (wconfig new-width new-height)
  "Scale WCONFIG's wtree with NEW-WIDTH and NEW-HEIGHT.
Return a copy WCONFIG's wtree scaled with `wg-scale-wtree' by the
ratio or NEW-WIDTH to WCONFIG's width, and NEW-HEIGHT to
WCONFIG's height."
  (wg-normalize-wtree
   (wg-scale-wtree
    (wg-wconfig-wtree wconfig)
    (/ (float new-width)  (wg-wconfig-width wconfig))
    (/ (float new-height) (wg-wconfig-height wconfig)))))

(defun wg-scale-wconfig-to-frame (wconfig)
  "Scale WCONFIG buffers to fit current frame size.
Return a scaled copy of WCONFIG."
  (interactive)
  (wg-scale-wconfigs-wtree wconfig
                           (frame-parameter nil 'width)
                           (frame-parameter nil 'height)))

(defun wg-restore-frames ()
  "Try to recreate opened frames, take info from session's 'frame-list parameter."
  (interactive)
  (delete-other-frames)
  (when wg-current-session
    (let ((fl (wg-session-parameter 'frame-list nil wg-current-session))
          (frame (selected-frame)))
      (mapc (lambda (wconfig)
              (with-selected-frame (make-frame)
                (wg-restore-wconfig wconfig)
                ))
            fl)
      (select-frame-set-input-focus frame))))

;; FIXME: throw a specific error if the restoration was unsuccessful
(defun wg-restore-wconfig (wconfig &optional frame)
  "Restore a workgroup configuration WCONFIG in a FRAME.
Runs each time you're switching workgroups."
  (unless frame (setq frame (selected-frame)))
  (let ((wg-record-incorrectly-restored-bufs t)
        (wg-incorrectly-restored-bufs nil)
        (params (wg-wconfig-parameters wconfig))
        fullscreen)
    (wg-barf-on-active-minibuffer)
    (when wg-restore-scroll-bars
      (wg-wconfig-restore-scroll-bars wconfig))

    (when (null (wg-current-workgroup t))
      (set-frame-parameter frame 'fullscreen (if (assoc 'fullscreen params)
                                                 (cdr (assoc 'fullscreen params))
                                               nil)))

    ;; Restore frame position
    (when (and wg-restore-frame-position
               (not (frame-parameter nil 'fullscreen))
               (null (wg-current-workgroup t)))
      (wg-wconfig-restore-frame-position wconfig frame))

    ;; Restore buffers
    (wg-restore-window-tree (wg-scale-wconfig-to-frame wconfig))

    (when wg-incorrectly-restored-bufs
      (message "Unable to restore these buffers: %S\
If you want, restore them manually and try again."
               (mapcar 'wg-buf-name wg-incorrectly-restored-bufs)))))


;;; saved wconfig commands

(defun wg-save-wconfig ()
  "Save the current wconfig to the current workgroup's saved wconfigs."
  (interactive)
  (let* ((workgroup (wg-current-workgroup))
         (name (wg-read-saved-wconfig-name workgroup))
         (wconfig (wg-current-wconfig)))
    (setf (wg-wconfig-name wconfig) name)
    (wg-workgroup-save-wconfig wconfig workgroup)
    (wg-fontified-message
      (:cmd "Saved: ")
      (:cur name))))

(defun wg-restore-saved-wconfig ()
  "Restore one of the current workgroup's saved wconfigs in `selected-frame'."
  (interactive)
  (let ((workgroup (wg-current-workgroup)))
    (wg-restore-wconfig-undoably
     (wg-workgroup-get-saved-wconfig
      (wg-completing-read "Saved wconfig: "
                          (mapcar 'wg-wconfig-name (wg-workgroup-saved-wconfigs workgroup))
                          nil t)
      workgroup))))

(defun wg-kill-saved-wconfig ()
  "Kill one of the current workgroup's saved wconfigs.
Also add it to the wconfig kill-ring."
  (interactive)
  (let* ((workgroup (wg-current-workgroup))
         (wconfig (wg-read-saved-wconfig workgroup)))
    (wg-workgroup-kill-saved-wconfig workgroup wconfig)
    (wg-add-to-wconfig-kill-ring wconfig)
    (wg-fontified-message
      (:cmd "Deleted: ")
      (:cur (wg-wconfig-name wconfig)))))


(defun wg-reverse-wconfig (wconfig &optional dir)
  "Reverse WCONFIG's wtree's wlist in direction DIR."
  (wg-asetf (wg-wconfig-wtree wconfig) (wg-reverse-wlist it dir))
  wconfig)


;; specialbufs
(defcustom wg-special-buffer-serdes-functions
  '(wg-serialize-comint-buffer
    )
  "Functions providing serialization/deserialization for complex buffers.

Use `wg-support' macro and this variable will be filled
automatically.

An entry should be either a function symbol or a lambda, and should
accept a single Emacs buffer object as an argument.

When a buffer is to be serialized, it is passed to each of these
functions in turn until one returns non-nil, or the list ends.  A
return value of nil indicates that the function can't handle
buffers of that type.  A non-nil return value indicates that it
can.  The first non-nil return value becomes the buffer's special
serialization data.  The return value should be a cons, with a
deserialization function (a function symbol or a lambda) as the car,
and any other serialization data as the cdr.

When it comes time to deserialize the buffer, the deserialization
function (the car of the cons mentioned above) is passed the
wg-buf object, from which it should restore the buffer.  The
special serialization data itself can be accessed
with (cdr (wg-buf-special-data <wg-buf>)).  The deserialization
function must return the restored Emacs buffer object.

See the definitions of the functions in this list for examples of
how to write your own."
  :type 'alist
  :group 'workgroups)

;; Dired
(wg-support 'dired-mode 'dired
  `((deserialize . ,(lambda (buffer vars)
                      (when (or wg-restore-remote-buffers
                                (not (file-remote-p default-directory)))
                        (let ((d (wg-get-first-existing-dir)))
                          (if (file-directory-p d) (dired d))))))))

;; `Info-mode'     C-h i
(wg-support 'Info-mode 'info
  `((save . (Info-current-file Info-current-node))
    (deserialize . ,(lambda (buffer vars)
                      ;;(with-current-buffer
                      ;;    (get-buffer-create (wg-buf-name buffer))
                      (aif vars
                          (if (fboundp 'Info-find-node)
                              (apply #'Info-find-node it))
                        (info)
                        (get-buffer (wg-buf-name buffer)))))))

;; `help-mode'
;; Bug: https://github.com/pashinin/workgroups2/issues/29
;; bug in wg-get-value
(wg-support 'help-mode 'help-mode
  `((save . (help-xref-stack-item help-xref-stack help-xref-forward-stack))
    (deserialize . ,(lambda (buffer vars)
                      (wg-dbind (item stack forward-stack) vars
                        (condition-case err
                            (apply (car item) (cdr item))
                          (error (message "%s" err)))
                        (awhen (get-buffer "*Help*")
                          (set-buffer it)
                          (wg-when-boundp (help-xref-stack help-xref-forward-stack)
                            (setq help-xref-stack stack
                                  help-xref-forward-stack forward-stack))))))))

;; ielm
(wg-support 'inferior-emacs-lisp-mode 'ielm
  `((deserialize . ,(lambda (buffer vars)
                      (ielm) (get-buffer "*ielm*")))))

;; Magit status
(wg-support 'magit-status-mode 'magit
  `((deserialize . ,(lambda (buffer vars)
                      (if (file-directory-p default-directory)
                          (magit-status default-directory)
                        (let ((d (wg-get-first-existing-dir)))
                          (if (file-directory-p d) (dired d))))))))

;; Shell
(wg-support 'shell-mode 'shell
  `((deserialize . ,(lambda (buffer vars)
                      (shell (wg-buf-name buffer))))))

;; org-agenda buffer
(defun wg-get-org-agenda-view-commands ()
  "Return commands to restore the state of Agenda buffer.
Can be restored using \"(eval commands)\"."
  (interactive)
  (when (boundp 'org-agenda-buffer-name)
    (if (get-buffer org-agenda-buffer-name)
        (with-current-buffer org-agenda-buffer-name
          (let* ((p (or (and (looking-at "\\'") (1- (point))) (point)))
                 (series-redo-cmd (get-text-property p 'org-series-redo-cmd)))
            (if series-redo-cmd
                (get-text-property p 'org-series-redo-cmd)
              (get-text-property p 'org-redo-cmd)))))))

(defun wg-run-agenda-cmd (f)
  "Run commands F in Agenda buffer.
You can get these commands using `wg-get-org-agenda-view-commands'."
  (when (and (boundp 'org-agenda-buffer-name)
             (fboundp 'org-current-line)
             (fboundp 'org-goto-line))
    (if (get-buffer org-agenda-buffer-name)
        (save-window-excursion
          (with-current-buffer org-agenda-buffer-name
            (let* ((line (org-current-line)))
              (if f (eval f))
              (org-goto-line line)))))))

(wg-support 'org-agenda-mode 'org-agenda
  '((serialize . (lambda (buffer)
                   (wg-get-org-agenda-view-commands)))
    (deserialize . (lambda (buffer vars)
                     (org-agenda-list)
                     (awhen (get-buffer org-agenda-buffer-name)
                       (with-current-buffer it
                         (wg-run-agenda-cmd vars))
                       it)))))

;; eshell
(wg-support 'eshell-mode 'esh-mode
  '((deserialize . (lambda (buffer vars)
                     (prog1 (eshell t)
                       (rename-buffer (wg-buf-name buffer) t))))))

;; term-mode
;;
;; This should work for `ansi-term's, too, as there doesn't seem to
;; be any difference between the two except how the name of the
;; buffer is generated.
;;
(wg-support 'term-mode 'term
  `((serialize . ,(lambda (buffer)
                    (if (get-buffer-process buffer)
                        (-last-item (process-command (get-buffer-process buffer)))
                      "/bin/bash")))
    (deserialize . ,(lambda (buffer vars)
                      (cl-labels ((term-window-width () 80)
                                  (window-height () 24))
                        (prog1 (term vars)
                          (rename-buffer (wg-buf-name buffer) t)))))))

;; `inferior-python-mode'
(wg-support 'inferior-python-mode 'python
  `((save . (python-shell-interpreter python-shell-interpreter-args))
    (deserialize . ,(lambda (buffer vars)
                      (wg-dbind (pythoncmd pythonargs) vars
                        (run-python (concat pythoncmd " " pythonargs))
                        (awhen (get-buffer (process-buffer
                                            (python-shell-get-or-create-process)))
                          (with-current-buffer it (goto-char (point-max)))
                          it))))))


;; Sage shell ;;
(wg-support 'inferior-sage-mode 'sage-mode
  `((deserialize . ,(lambda (buffer vars)
                      (save-window-excursion
                        (if (boundp' sage-command)
                            (run-sage t sage-command t)))
                      (if (boundp 'sage-buffer)
                          (awhen sage-buffer
                            (set-buffer it)
                            (switch-to-buffer sage-buffer)
                            (goto-char (point-max))))))))

;; `inferior-ess-mode'     M-x R
(wg-support 'inferior-ess-mode 'ess-inf
  `((save . (inferior-ess-program))
    (deserialize . ,(lambda (buffer vars)
                      (wg-dbind (cmd) vars
                        (let ((ess-ask-about-transfile nil)
                              (ess-ask-for-ess-directory nil)
                              (ess-history-file nil))
                          (R)
                          (get-buffer (wg-buf-name buffer))))))))

;; `inferior-octave-mode'
(wg-support 'inferior-octave-mode 'octave
  `((deserialize . ,(lambda (buffer vars)
                      (prog1 (run-octave)
                        (rename-buffer (wg-buf-name buffer) t))))))

;; `prolog-inferior-mode'
(wg-support 'prolog-inferior-mode 'prolog
  `((deserialize . ,(lambda (buffer vars)
                      (save-window-excursion
                        (run-prolog nil))
                      (switch-to-buffer "*prolog*")
                      (goto-char (point-max))))))

;; `ensime-inf-mode'
(wg-support 'ensime-inf-mode 'ensime
  `((deserialize . ,(lambda (buffer vars)
                      (save-window-excursion
                        (ensime-inf-switch))
                      (when (boundp 'ensime-inf-buffer-name)
                        (switch-to-buffer ensime-inf-buffer-name)
                        (goto-char (point-max)))))))

;; compilation-mode
;;
;; I think it's not a good idea to compile a program just to switch
;; workgroups. So just restoring a buffer name.
(wg-support 'compilation-mode 'compile
  `((serialize . ,(lambda (buffer)
                    (if (boundp' compilation-arguments) compilation-arguments)))
    (deserialize . ,(lambda (buffer vars)
                      (save-window-excursion
                        (get-buffer-create (wg-buf-name buffer)))
                      (with-current-buffer (wg-buf-name buffer)
                        (when (boundp' compilation-arguments)
                          (make-local-variable 'compilation-arguments)
                          (setq compilation-arguments vars)))
                      (switch-to-buffer (wg-buf-name buffer))
                      (goto-char (point-max))))))

;; grep-mode
;; see grep.el - `compilation-start' - it is just a compilation buffer
;; local variables:
;; `compilation-arguments' == (cmd mode nil nil)
(wg-support 'grep-mode 'grep
  `((serialize . ,(lambda (buffer)
                    (if (boundp' compilation-arguments) compilation-arguments)))
    (deserialize . ,(lambda (buffer vars)
                      (compilation-start (car vars) (nth 1 vars))
                      (switch-to-buffer "*grep*")))))

(defun wg-deserialize-slime-buffer (buf)
  "Deserialize `slime' buffer BUF."
  (when (require 'slime nil 'noerror)
    (wg-dbind (this-function args) (wg-buf-special-data buf)
      (let ((default-directory (car args))
            (arguments (nth 1 args)))
        (when (and (fboundp 'slime-start*)
                   (fboundp 'slime-process))
          (save-window-excursion
            (slime-start* arguments))
          (switch-to-buffer (process-buffer (slime-process)))
          (current-buffer))))))

;; `comint-mode'  (general mode for all shells)
;;
;; It may have different shells. So we need to determine which shell is
;; now in `comint-mode' and how to restore it.
;;
;; Just executing `comint-exec' may be not enough because we can miss
;; some hooks or any other stuff that is executed when you run a
;; specific shell.
(defun wg-serialize-comint-buffer (buffer)
  "Serialize comint BUFFER."
  (with-current-buffer buffer
    (if (fboundp 'comint-mode)
        (when (eq major-mode 'comint-mode)
          ;; `slime-inferior-lisp-args' var is used when in `slime'
          (when (and (boundp 'slime-inferior-lisp-args)
                     slime-inferior-lisp-args)
            (list 'wg-deserialize-slime-buffer
                  (list default-directory slime-inferior-lisp-args)
                  ))))))

;; inf-mongo
;; https://github.com/tobiassvn/inf-mongo
;; `mongo-command' - command used to start inferior mongo
(wg-support 'inf-mongo-mode 'inf-mongo
  `((serialize . ,(lambda (buffer)
                    (if (boundp 'inf-mongo-command) inf-mongo-command)))
    (deserialize . ,(lambda (buffer vars)
                      (save-window-excursion
                        (when (fboundp 'inf-mongo)
                          (inf-mongo vars)))
                      (when (get-buffer "*mongo*")
                        (switch-to-buffer "*mongo*")
                        (goto-char (point-max)))))))

(defun wg-temporarily-rename-buffer-if-exists (buffer)
  "Rename BUFFER if it exists."
  (when (get-buffer buffer)
    (with-current-buffer buffer
      (rename-buffer "*wg--temp-buffer*" t))))

;; SML shell
;; Functions to serialize deserialize inferior sml buffer
;; `inf-sml-program' is the program run as inferior sml, is the
;; `inf-sml-args' are the extra parameters passed, `inf-sml-host'
;; is the host on which sml was running when serialized
(wg-support 'inferior-sml-mode 'sml-mode
  `((serialize . ,(lambda (buffer)
                    (list (if (boundp 'sml-program-name) sml-program-name)
                          (if (boundp 'sml-default-arg) sml-default-arg)
                          (if (boundp 'sml-host-name) sml-host-name))))
    (deserialize . ,(lambda (buffer vars)
                      (wg-dbind (program args host) vars
                        (save-window-excursion
                          ;; If a inf-sml buffer already exists rename it temporarily
                          ;; otherwise `run-sml' will simply switch to the existing
                          ;; buffer, however we want to create a separate buffer with
                          ;; the serialized name
                          (let* ((inf-sml-buffer-name (concat "*"
                                                              (file-name-nondirectory program)
                                                              "*"))
                                 (existing-sml-buf (wg-temporarily-rename-buffer-if-exists
                                                    inf-sml-buffer-name)))
                            (with-current-buffer (run-sml program args host)
                              ;; Rename the buffer
                              (rename-buffer (wg-buf-name buffer) t)

                              ;; Now we can re-rename the previously renamed buffer
                              (when existing-sml-buf
                                (with-current-buffer existing-sml-buf
                                  (rename-buffer inf-sml-buffer-name t))))))
                        (switch-to-buffer (wg-buf-name buffer))
                        (goto-char (point-max)))))))

;; Geiser repls
;; http://www.nongnu.org/geiser/
(wg-support 'geiser-repl-mode 'geiser
  `((save . (geiser-impl--implementation))
    (deserialize . ,(lambda (buffer vars)
                      (when (fboundp 'run-geiser)
                        (wg-dbind (impl) vars
                          (run-geiser impl)
                          (goto-char (point-max))))
                      (switch-to-buffer (wg-buf-name buffer))))))

;; w3m-mode
(wg-support 'w3m-mode 'w3m
  `((save . (w3m-current-url))
    (deserialize . ,(lambda (buffer vars)
                      (wg-dbind (url) vars
                        (w3m-goto-url url))))))

;; notmuch
(wg-support 'notmuch-hello-mode 'notmuch
  `((deserialize . ,(lambda (buffer vars)
                      (ignore vars)
                      (notmuch)
                      (get-buffer (wg-buf-name buffer))))))

;; dired-sidebar
(wg-support 'dired-sidebar-mode 'dired-sidebar
  `((serialize . ,(lambda (_buffer) dired-sidebar-display-alist))
    (deserialize
     . ,(lambda (_buffer saved-display-alist)
          (when (and (or wg-restore-remote-buffers
                         (not (file-remote-p default-directory)))
                     ;; Restore buffer only if `dired-sidebar-show-sidebar'
                     ;; will place it in the same side window as before.
                     (equal dired-sidebar-display-alist saved-display-alist))
            (let ((dir (wg-get-first-existing-dir)))
              (when (file-directory-p dir)
                (let ((buffer (dired-sidebar-get-or-create-buffer dir)))
                  ;; Set up the buffer by calling `dired-sidebar-show-sidebar'
                  ;; for side effects only, discarding the created window. We
                  ;; don't want to add extra new windows during the session
                  ;; restoration process.
                  (save-window-excursion (dired-sidebar-show-sidebar buffer))
                  ;; HACK: Replace the just-restored window after session is
                  ;; restored. This ensures that we perform any additional
                  ;; window setup that was not done by deserialization. The
                  ;; point is to avoid depending too closely on the
                  ;; implementation details of dired-sidebar. Rather than
                  ;; serialize every detail, we let `dired-sidebar-show-sidebar'
                  ;; do the work.
                  (let ((frame (selected-frame)))
                    (run-at-time 0 nil
                                 (lambda ()
                                   (with-selected-frame frame
                                     (dired-sidebar-hide-sidebar)
                                     (dired-sidebar-show-sidebar buffer)))))
                  buffer))))))))

;;; buffer-local variable serdes

(defun wg-serialize-buffer-mark-ring ()
  "Return a new list of the positions of the marks in `mark-ring'."
  (mapcar 'marker-position mark-ring))

(defun wg-deserialize-buffer-mark-ring (positions)
  "Set `mark-ring' to a new list of markers created from POSITIONS."
  (setq mark-ring
        (mapcar (lambda (pos) (set-marker (make-marker) pos))
                positions)))

(defun wg-deserialize-buffer-major-mode (major-mode-symbol)
  "Conditionally retore MAJOR-MODE-SYMBOL in `current-buffer'."
  (and (fboundp major-mode-symbol)
       (not (eq major-mode-symbol major-mode))
       (funcall major-mode-symbol)))

(defun wg-deserialize-buffer-local-variables (buf)
  "Restore BUF's buffer local variables in `current-buffer'."
  (cl-loop for ((var . val) . rest) on (wg-buf-local-vars buf)
           do (awhen (assq var wg-buffer-local-variables-alist)
                (wg-dbind (var ser des) it
                  (if des (funcall des val)
                    (set var val))))))

(defmacro wg-workgroup-list ()
  "Setf'able `wg-current-session' modified slot accessor."
  `(wg-session-workgroup-list (wg-current-session)))

(defmacro wg-buf-list ()
  "Setf'able `wg-current-session' buf-list slot accessor."
  `(wg-session-buf-list (wg-current-session)))

(defun wg-restore-default-buffer (&optional switch)
  "Return `wg-default-buffer' and maybe SWITCH to it."
  (if switch
      (switch-to-buffer wg-default-buffer t)
    (get-buffer-create wg-default-buffer)))

(defun wg-restore-existing-buffer (buf &optional switch)
  "Return existing buffer from BUF and maybe SWITCH to it."
  (-when-let (b (wg-find-buf-in-buffer-list buf (wg-buffer-list-emacs)))
    (if switch (switch-to-buffer b t))
    (with-current-buffer b
      (wg-set-buffer-uid-or-error (wg-buf-uid buf))
      b)))

(defun wg-restore-file-buffer (buf &optional switch)
  "Restore BUF by finding its file and maybe SWITCH to it.
Return the created buffer.
If BUF's file doesn't exist, call `wg-restore-default-buffer'"
  ;;(-when-let ((file-name (wg-buf-file-name buf)))
  (let ((file-name (wg-buf-file-name buf)))
    (when (and file-name
               (or wg-restore-remote-buffers
                   (not (file-remote-p file-name))))
      (cond ((file-exists-p file-name)
             ;; jit ignore errors
             ;;(ignore-errors
             (condition-case err
                 (let ((b (find-file-noselect file-name nil nil nil)))
                   (with-current-buffer b
                     (rename-buffer (wg-buf-name buf) t)
                     (wg-set-buffer-uid-or-error (wg-buf-uid buf))
                     (when wg-restore-mark
                       (set-mark (wg-buf-mark buf))
                       (deactivate-mark))
                     (wg-deserialize-buffer-local-variables buf)
                     )
                   (if switch (switch-to-buffer b))
                   b)
               (error
                (message "Error while restoring a file %s:\n  %s" file-name (error-message-string err))
                nil)))
            (t
             ;; try directory
             (if (file-directory-p (file-name-directory file-name))
                 (dired (file-name-directory file-name))
               (progn
                 (message "Attempt to restore nonexistent file: %S" file-name)
                 nil))
             )))))

(defun wg-restore-special-buffer (buf &optional switch)
  "Restore a buffer BUF with DESERIALIZER-FN and maybe SWITCH to it."
  (-when-let*
      ((special-data (wg-buf-special-data buf))
       (buffer (save-window-excursion
                 (condition-case err
                     (funcall (car special-data) buf)
                   (error (message "Error deserializing %S: %S" (wg-buf-name buf) err)
                          nil)))))
    (if switch (switch-to-buffer buffer t))
    (with-current-buffer buffer
      (wg-set-buffer-uid-or-error (wg-buf-uid buf)))
    buffer))

(defun wg-restore-buffer (buf &optional switch)
  "Restore BUF, return it and maybe SWITCH to it."
  (when buf
  (fset 'buffer-list wg-buffer-list-original)
  (prog1
      (or (wg-restore-existing-buffer buf switch)
          (wg-restore-special-buffer buf switch)  ;; non existent dired problem
          (wg-restore-file-buffer buf switch)
          (progn (wg-restore-default-buffer switch) nil))
    (if wg-mess-with-buffer-list
        (fset 'buffer-list wg-buffer-list-function)))))



;;; buffer object utils

(defun wg-completing-read (prompt choices &optional pred require-match initial-input history default)
  "Do a completing read.  Use `ido-mode` if enabled."
  (if ido-mode
      (ido-completing-read prompt choices pred require-match
                           initial-input history default)
    (completing-read prompt choices pred require-match
                     initial-input history default)))

(defun wg-buffer-uid (buffer-or-name)
  "Return BUFFER-OR-NAME's buffer-local value of `wg-buffer-uid'."
  (buffer-local-value 'wg-buffer-uid (wg-get-buffer buffer-or-name)))

(defun wg-bufobj-uid (bufobj)
  "Return BUFOBJ's uid."
  (cl-etypecase bufobj
    (buffer (wg-buffer-uid bufobj))
    (wg-buf (wg-buf-uid bufobj))
    (string (wg-bufobj-uid (wg-get-buffer bufobj)))))

(defun wg-bufobj-name (bufobj)
  "Return BUFOBJ's buffer name."
  (cl-etypecase bufobj
    (buffer (buffer-name bufobj))
    (wg-buf (wg-buf-name bufobj))
    (string (wg-buffer-name bufobj))))

(defun wg-bufobj-file-name (bufobj)
  "Return BUFOBJ's filename."
  (cl-etypecase bufobj
    (buffer (buffer-file-name bufobj))
    (wg-buf (wg-buf-file-name bufobj))
    (string (wg-bufobj-file-name (wg-get-buffer bufobj)))))

;; `wg-equal-bufobjs' and `wg-find-bufobj' may need to be made a lot smarter
(defun wg-equal-bufobjs (bufobj1 bufobj2)
  "Return t if BUFOBJ1 is \"equal\" to BUFOBJ2."
  (let ((fname1 (wg-bufobj-file-name bufobj1))
        (fname2 (wg-bufobj-file-name bufobj2)))
    (cond ((and fname1 fname2) (string= fname1 fname2))
          ((or fname1 fname2) nil)
          ((string= (wg-bufobj-name bufobj1) (wg-bufobj-name bufobj2)) t))))

(defun wg-find-bufobj (bufobj bufobj-list)
  "Find BUFOBJ in BUFOBJ-LIST, testing with `wg-equal-bufobjs'."
  (cl-find bufobj bufobj-list :test 'wg-equal-bufobjs))

(defun wg-find-bufobj-by-uid (uid bufobj-list)
  "Find the bufobj in BUFOBJ-LIST with uid UID."
  (cl-find uid bufobj-list :test 'string= :key 'wg-bufobj-uid))

(defun wg-find-buffer-in-buf-list (buffer-or-name buf-list)
  "Find BUFFER-OR-NAME in BUF-LIST."
  (aif (wg-buffer-uid buffer-or-name)
      (wg-find-bufobj-by-uid it buf-list)
    (wg-find-bufobj buffer-or-name buf-list)))

(defun wg-find-buf-in-buffer-list (buf buffer-list)
  "Find BUF in BUFFER-LIST."
  (or (wg-find-bufobj-by-uid (wg-buf-uid buf) buffer-list)
      (wg-find-bufobj buf buffer-list)))

(defun wg-find-buf-by-uid (uid)
  "Find a buf in `wg-buf-list' by UID."
  (when uid
    (wg-find-bufobj-by-uid uid (wg-buf-list))))

(defun wg-set-buffer-uid-or-error (uid &optional buffer)
  "Change UID value of a BUFFER's local var `wg-buffer-uid'.
If BUFFER already has a buffer local value of `wg-buffer-uid',
and it's not equal to UID, error."
  (if wg-buffer-uid
      ;;(if (string= wg-buffer-uid uid) uid
      ;;  (error "uids don't match %S and %S" uid wg-buffer-uid))
      (setq wg-buffer-uid uid)))


(defun wg-buffer-special-data (buffer)
  "Return BUFFER's auxiliary serialization, or nil."
  (cl-some (lambda (fn) (funcall fn buffer)) wg-special-buffer-serdes-functions))


(defun wg-serialize-buffer-local-variables ()
  "Return an alist of buffer-local variable symbols and their values.
See `wg-buffer-local-variables-alist' for details."
  (wg-docar (entry wg-buffer-local-variables-alist)
    (wg-dbind (var ser des) entry
      (when (local-variable-p var)
        (cons var (if ser (funcall ser) (symbol-value var)))))))

(defun wg-buffer-to-buf (buffer)
  "Return the serialization (a wg-buf) of Emacs buffer BUFFER."
  (with-current-buffer buffer
    (wg-make-buf
     :name           (buffer-name)
     :file-name      (buffer-file-name)
     :point          (point)
     :mark           (mark)
     :local-vars     (wg-serialize-buffer-local-variables)
     :special-data   (wg-buffer-special-data buffer))))

(defun wg-add-buffer-to-buf-list (buffer)
  "Make a buf from BUFFER, and add it to `wg-buf-list' if necessary.
If there isn't already a buf corresponding to BUFFER in
`wg-buf-list', make one and add it.  Return BUFFER's uid
in either case."
  (when buffer
  (with-current-buffer buffer
    (setq wg-buffer-uid
          (aif (wg-find-buffer-in-buf-list buffer (wg-buf-list))
              (wg-buf-uid it)
            (let ((buf (wg-buffer-to-buf buffer)))
              (push buf (wg-buf-list))
              (wg-buf-uid buf)))))))

(defun wg-buffer-uid-or-add (buffer)
  "Return BUFFER's uid.
If there isn't already a buf corresponding to BUFFER in
`wg-buf-list', make one and add it."
  (or (wg-buffer-uid buffer) (wg-add-buffer-to-buf-list buffer)))

(defun wg-bufobj-uid-or-add (bufobj)
  "If BUFOBJ is a wg-buf, return its uid.
If BUFOBJ is a buffer or a buffer name, see `wg-buffer-uid-or-add'."
  (cl-etypecase bufobj
    (wg-buf (wg-buf-uid bufobj)) ;; possibly also add to `wg-buf-list'
    (buffer (wg-buffer-uid-or-add bufobj))
    (string (wg-bufobj-uid-or-add (wg-get-buffer bufobj)))))

(defun wg-reset-buffer (buffer)
  "Return BUFFER.
Currently only sets BUFFER's `wg-buffer-uid' to nil."
  (with-current-buffer buffer (setq wg-buffer-uid nil)))

(defun wg-update-buffer-in-buf-list (&optional buffer)
  "Update BUFFER's corresponding buf in `wg-buf-list'.
BUFFER nil defaults to `current-buffer'."
  (let ((buffer (or buffer (current-buffer))))
    (-when-let* ((uid (wg-buffer-uid buffer))
                 (old-buf (wg-find-buf-by-uid uid))
                 (new-buf (wg-buffer-to-buf buffer)))
      (setf (wg-buf-uid new-buf) (wg-buf-uid old-buf))
      (wg-asetf (wg-buf-list) (cons new-buf (remove old-buf it))))))

(defvar wg-just-exited-minibuffer nil
  "Flag set by `minibuffer-exit-hook'.
To exempt from undoification those window-configuration changes
caused by exiting the minibuffer.  This is ugly, but necessary.
It may seem like we could just null out
`wg-undoify-window-configuration-change' in
`minibuffer-exit-hook', but that also prevents undoification of
window configuration changes triggered by commands called with
`execute-extended-command' -- i.e. it's just too coarse.")

(defcustom wg-no-confirm-on-destructive-operation nil
  "Do not request confirmation before various destructive operations."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-minibuffer-message-timeout 0.75
  "Bound to `minibuffer-message-timeout' when messaging while the
minibuffer is active."
  :type 'float
  :group 'workgroups)

(defun wg-read-object (prompt test warning &optional initial-contents keymap
                              read hist default-value inherit-input-method)
  "PROMPT for an object that satisfies TEST.  WARNING if necessary.
INITIAL-CONTENTS KEYMAP READ HIST DEFAULT-VALUE
INHERIT-INPUT-METHOD are `read-from-minibuffer's args."
  (cl-labels ((read () (read-from-minibuffer
                        prompt initial-contents keymap read hist
                        default-value inherit-input-method)))
    (let ((obj (read)))
      (when (and (equal obj "") default-value) (setq obj default-value))
      (while (not (funcall test obj))
        (message warning)
        (sit-for wg-minibuffer-message-timeout)
        (setq obj (read)))
      obj)))

(defun wg-read-new-workgroup-name (&optional prompt)
  "Read a non-empty name string from the minibuffer.
Print PROMPT"
  (let ((default (wg-new-default-workgroup-name)))
    (wg-read-object
     (or prompt (format "Name (default: %S): " default))
     (lambda (new) (and (stringp new)
                        (not (equal new ""))))
     "Please enter a non-empty name"
     nil nil nil nil default)))

(defun wg-read-workgroup-index ()
  "Prompt for the index of a workgroup."
  (let ((max (1- (length (wg-workgroup-list-or-error)))))
    (wg-read-object
     (format "%s\n\nEnter [0-%d]: " (wg-workgroup-list-display) max)
     (lambda (obj) (and (integerp obj) (wg-within obj 0 max t)))
     (format "Please enter an integer [%d-%d]" 0 max)
     nil nil t)))

(defun wg-minibuffer-inactive-p ()
  "Return t when `minibuffer-depth' is zero, nil otherwise."
  (zerop (minibuffer-depth)))

(defun wg-barf-on-active-minibuffer ()
  "Throw an error when the minibuffer is active."
  (when (not (wg-minibuffer-inactive-p))
    (error "Exit minibuffer to use workgroups functions!")))

(defvar wg-deactivation-list nil
  "A stack of workgroups that are currently being switched away from.
Used to avoid associating the old workgroup's buffers with the
new workgroup during a switch.")

(defun wg-flag-session-modified ()
  "Set SESSION's modified flag."
  (when (and wg-flag-modified wg-current-session)
    (setf (wg-session-modified wg-current-session) t)))

(defun wg-flag-workgroup-modified (&optional workgroup)
  "Set WORKGROUP's and the current session's modified flags."
  (unless workgroup
    (setq workgroup (wg-get-workgroup nil t)))
  (when (and wg-flag-modified workgroup)
    (setf (wg-workgroup-modified workgroup) t)
    (wg-flag-session-modified)))

(defun wg-current-workgroup (&optional noerror frame)
  "Return current workgroup in frame.
Error unless NOERROR, in FRAME if specified."
  (or wg-current-workgroup
      (aif (frame-parameter frame 'wg-current-workgroup-uid)
          (wg-find-workgroup-by :uid it noerror)
        (unless noerror (error "No current workgroup in this frame")))))

(defun wg-previous-workgroup (&optional noerror frame)
  "Return the previous workgroup in FRAME, or error unless NOERROR."
  (aif (frame-parameter frame 'wg-previous-workgroup-uid)
      (wg-find-workgroup-by :uid it noerror)
    (unless noerror (error "No previous workgroup in this frame"))))

(defun wg-set-current-workgroup (workgroup &optional frame)
  "Set the current workgroup to WORKGROUP in FRAME.
WORKGROUP should be a workgroup or nil."
  (set-frame-parameter frame 'wg-current-workgroup-uid
                       (when workgroup (wg-workgroup-uid workgroup))))

(defun wg-set-previous-workgroup (workgroup &optional frame)
  "Set the previous workgroup to WORKGROUP in FRAME.
WORKGROUP should be a workgroup or nil."
  (set-frame-parameter frame 'wg-previous-workgroup-uid
                       (when workgroup (wg-workgroup-uid workgroup))))

(defun wg-current-workgroup-p (workgroup &optional frame)
  "Return t when WORKGROUP is the current workgroup, nil otherwise."
  (awhen (wg-current-workgroup t frame)
    (eq workgroup it)))

(defun wg-previous-workgroup-p (workgroup &optional frame)
  "Return t when WORKGROUP is the previous workgroup, nil otherwise."
  (awhen (wg-previous-workgroup t frame)
    (eq workgroup it)))

(defun wg-get-workgroup (obj &optional noerror)
  "Return a workgroup from OBJ.
If OBJ is a workgroup, return it.
If OBJ is a string, return the workgroup named OBJ, or error unless NOERROR.
If OBJ is nil, return the current workgroup, or error unless NOERROR."
  (cond ((wg-workgroup-p obj) obj)
        ((stringp obj) (wg-find-workgroup-by :name obj noerror))
        ((null obj) (wg-current-workgroup noerror))
        (t (error "Can't get workgroup from type:: %S" (type-of obj)))))


;;; workgroup parameters
;;
;; Quick test:
;; (wg-workgroup-parameters (wg-current-workgroup))
;; (wg-set-workgroup-parameter (wg-current-workgroup) 'test1 t)
;; (wg-workgroup-parameter (wg-current-workgroup) 'test1)
(defun wg-workgroup-parameter (workgroup parameter &optional default)
  "Return WORKGROUP's value for PARAMETER.
If PARAMETER is not found, return DEFAULT which defaults to nil.
WORKGROUP should be accepted by `wg-get-workgroup'."
  (wg-aget (wg-workgroup-parameters (wg-get-workgroup workgroup))
           parameter default))

(defun wg-set-workgroup-parameter (parameter value &optional workgroup)
  "Set PARAMETER to VALUE in a WORKGROUP.
WORKGROUP should be a value accepted by `wg-get-workgroup'.
Return VALUE."
  (-when-let (workgroup (wg-get-workgroup (or workgroup (wg-current-workgroup t)) t))
    (wg-set-parameter (wg-workgroup-parameters workgroup) parameter value)
    (wg-flag-workgroup-modified workgroup)
    value))

(defun wg-remove-workgroup-parameter (parameter &optional workgroup)
  "Remove PARAMETER from WORKGROUP's parameters."
  (-when-let (workgroup (wg-get-workgroup workgroup t))
    (wg-flag-workgroup-modified workgroup)
    (wg-asetf (wg-workgroup-parameters workgroup) (wg-aremove it parameter))))

(defun wg-workgroup-local-value (variable &optional workgroup)
  "Return the value of VARIABLE in WORKGROUP.
WORKGROUP nil defaults to the current workgroup.  If there is no
current workgroup, or if VARIABLE does not have a workgroup-local
binding in WORKGROUP, resolve VARIABLE with `wg-session-local-value'."
  (let ((workgroup (wg-get-workgroup workgroup t)))
    (if (not workgroup) (wg-session-local-value variable)
      (let* ((undefined (cl-gensym))
             (value (wg-workgroup-parameter workgroup variable undefined)))
        (if (not (eq value undefined)) value
          (wg-session-local-value variable))))))
(defalias 'wg-local-value 'wg-workgroup-local-value)


(defun wg-workgroup-saved-wconfig-names (workgroup)
  "Return a new list of the names of all WORKGROUP's saved wconfigs."
  (mapcar 'wg-wconfig-name (wg-workgroup-saved-wconfigs workgroup)))

(defun wg-workgroup-get-saved-wconfig (wconfig-or-name &optional workgroup)
  "Return the wconfig by WCONFIG-OR-NAME from WORKGROUP's saved wconfigs.
WCONFIG-OR-NAME must be either a string or a wconfig.  If
WCONFIG-OR-NAME is a string and there is no saved wconfig with
that name, return nil.  If WCONFIG-OR-NAME is a wconfig, and it
is a member of WORKGROUP's saved wconfigs, return is as given.
Otherwise return nil."
  (let ((wconfigs (wg-workgroup-saved-wconfigs (or workgroup (wg-current-workgroup)))))
    (cl-etypecase wconfig-or-name
      (wg-wconfig (car (memq wconfig-or-name wconfigs)))
      (string (cl-find wconfig-or-name wconfigs
                       :key 'wg-wconfig-name
                       :test 'string=)))))

(defun wg-workgroup-save-wconfig (wconfig &optional workgroup)
  "Add WCONFIG to WORKGROUP's saved wconfigs.
WCONFIG must have a name.  If there's already a wconfig with the
same name in WORKGROUP's saved wconfigs, replace it."
  (let ((name (wg-wconfig-name wconfig)))
    (unless name (error "Attempt to save a nameless wconfig"))
    (setf (wg-workgroup-modified workgroup) t)
    (wg-asetf (wg-workgroup-saved-wconfigs workgroup)
              (cons wconfig (cl-remove name it
                                       :key 'wg-wconfig-name
                                       :test 'string=)))))

(defun wg-workgroup-kill-saved-wconfig (workgroup wconfig-or-name)
  "Delete WCONFIG-OR-NAME from WORKGROUP's saved wconfigs.
WCONFIG-OR-NAME is resolved with `wg-workgroup-get-saved-wconfig'."
  (-when-let (wconfig (wg-workgroup-get-saved-wconfig
                       workgroup wconfig-or-name))
    (wg-asetf (wg-workgroup-saved-wconfigs workgroup) (remq wconfig it)
              (wg-workgroup-modified workgroup) t)))



(defun wg-workgroup-base-wconfig-buf-uids (workgroup)
  "Return a new list of all unique buf uids in WORKGROUP's working wconfig."
  (wg-wconfig-buf-uids (wg-workgroup-base-wconfig workgroup)))

(defun wg-workgroup-saved-wconfigs-buf-uids (workgroup)
  "Return a new list of all unique buf uids in WORKGROUP's base wconfig."
  (cl-reduce 'wg-string-list-union
             (wg-workgroup-saved-wconfigs workgroup)
             :key 'wg-wconfig-buf-uids))

(defun wg-workgroup-all-buf-uids (workgroup)
  "Return a new list of all unique buf uids in WORKGROUP."
  (cl-reduce 'wg-string-list-union
             (list (wg-workgroup-base-wconfig-buf-uids workgroup)
                   (wg-workgroup-saved-wconfigs-buf-uids workgroup))))

(defun wg-restore-workgroup (workgroup)
  "Restore WORKGROUP in `selected-frame'."
  (let (wg-flag-modified)
    (wg-restore-wconfig-undoably (wg-workgroup-working-wconfig workgroup) t)))

(defun wg-workgroup-list-or-error (&optional noerror)
  "Return the value of `wg-current-session's :workgroup-list slot.
Or scream unless NOERROR."
  (aif (wg-current-session noerror)
      (or (wg-session-workgroup-list it)
          (unless noerror (error "No workgroups are defined.")))
    (unless noerror (error "Current session is nil. No workgroups are defined"))))

(defun wg-find-workgroup-by (slotkey value &optional noerror)
  "Return the workgroup on which ACCESSOR returns VALUE or error."
  (let ((accessor (cl-ecase slotkey
                    (:name 'wg-workgroup-name)
                    (:uid  'wg-workgroup-uid))))
    (or (cl-find value (wg-workgroup-list-or-error noerror) :test 'equal :key accessor)
        (unless noerror
          (error "There are no workgroups with a %S of %S"
                 accessor value)))))

(defun wg-cyclic-nth-from-workgroup (workgroup &optional n)
  "Return the workgroup N places from WORKGROUP in `wg-workgroup-list'."
  (wg-cyclic-nth-from-elt workgroup (wg-workgroup-list-or-error) (or n 1)))

(defun wg-workgroup-names (&optional noerror)
  "Return a list of workgroup names or scream unless NOERROR."
  (mapcar 'wg-workgroup-name (wg-workgroup-list-or-error noerror)))

(defun wg-read-workgroup-name (&optional require-match)
  "Read a workgroup name from `wg-workgroup-names'.
REQUIRE-MATCH to match."
  (wg-completing-read "Workgroup: " (wg-workgroup-names) nil require-match nil nil
                      (awhen (wg-current-workgroup t) (wg-workgroup-name it))))

(defun wg-new-default-workgroup-name ()
  "Return a new, unique, default workgroup name."
  (let ((names (wg-workgroup-names t)) (index -1) result)
    (while (not result)
      (let ((new-name (format "wg%s" (cl-incf index))))
        (unless (member new-name names)
          (setq result new-name))))
    result))

(defun wg-read-saved-wconfig-name (workgroup &optional prompt require-match)
  "Read the name of a saved wconfig, completing on the names of
WORKGROUP's saved wconfigs."
  (wg-completing-read (or prompt "Saved wconfig name: ")
                      (wg-workgroup-saved-wconfig-names workgroup)
                      nil require-match))

(defun wg-read-saved-wconfig (workgroup)
  "Read the name of and return one of WORKGROUP's saved wconfigs."
  (wg-workgroup-get-saved-wconfig
   workgroup (wg-read-saved-wconfig-name workgroup nil t)))


;;; workgroup-list reorganization commands

(defun wg-offset-workgroup-left (&optional workgroup n)
  "Offset WORKGROUP leftward in `wg-workgroup-list' cyclically."
  (interactive (list nil current-prefix-arg))
  (wg-cyclic-offset-workgroup (wg-get-workgroup workgroup) (or n -1))
  (wg-fontified-message
    (:cmd "Offset left: ")
    (wg-workgroup-list-display)))

(defun wg-offset-workgroup-right (&optional workgroup n)
  "Offset WORKGROUP rightward in `wg-workgroup-list' cyclically."
  (interactive (list nil current-prefix-arg))
  (wg-cyclic-offset-workgroup (wg-get-workgroup workgroup) (or n 1))
  (wg-fontified-message
    (:cmd "Offset right: ")
    (wg-workgroup-list-display)))


;;; undo/redo commands

(defun wg-undo-wconfig-change (&optional workgroup)
  "Undo a change to the current workgroup's window-configuration."
  (interactive)
  (let* ((workgroup (wg-get-workgroup workgroup))
         (undid? (wg-workgroup-offset-position-in-undo-list workgroup 1)))
    (wg-fontified-message
      (:cmd "Undo")
      (:cur (if undid? "" "  No more undo info")))))

(defun wg-redo-wconfig-change (&optional workgroup)
  "Redo a change to the current workgroup's window-configuration."
  (interactive)
  (let* ((workgroup (wg-get-workgroup workgroup))
         (redid? (wg-workgroup-offset-position-in-undo-list workgroup -1)))
    (wg-fontified-message
      (:cmd "Redo")
      (:cur (if redid? "" "  No more redo info")))))


;;; window-tree commands
;;
(defun wg-rename-workgroup (newname &optional workgroup)
  "Set NEWNAME to WORKGROUP's name."
  (interactive (list (wg-read-new-workgroup-name "New name: ") nil))
  (-when-let (workgroup (wg-get-workgroup workgroup))
    (let* ((oldname (wg-workgroup-name workgroup)))
      (setf (wg-workgroup-name workgroup) newname)
      (wg-flag-workgroup-modified workgroup)
      (wg-fontified-message
        (:cmd "Renamed: ")
        (:cur oldname)
        (:msg " to ")
        (:cur (wg-workgroup-name workgroup))))))

(defun wg-reset (&optional force)
  "Reset Workgroups.
Resets all frame parameters, buffer-local vars, the current
Workgroups session object, etc."
  (interactive "P")
  (unless (or force wg-no-confirm-on-destructive-operation
              (y-or-n-p "Really reset Workgroups? "))
    (error "Canceled"))
  (wg-reset-internal (wg-make-session))
  (wg-save-session t)
  (wg-fontified-message (:cmd "Reset: ") (:msg "Workgroups")))

(defun wg-query-and-save-if-modified ()
  "Query for save when `wg-modified-p'."
  (or (not (wg-modified-p))
      (when (y-or-n-p "Save modified workgroups? ")
        (wg-save-session))))

(defun wg-create-workgroup (name &optional blank)
  "Create and add a workgroup named NAME.
Optional argument BLANK non-nil (set interactively with a prefix
arg) means use a blank, one window window-config.  Otherwise use
the current window-configuration.  Keep in mind that even though
the current window-config may be used, other parameters of the
current workgroup are not copied to the created workgroup.  For
that, use `wg-clone-workgroup'."
  (interactive (list (wg-read-new-workgroup-name) current-prefix-arg))

  (unless (file-exists-p (wg-get-session-file))
    (wg-reset t)
    (wg-save-session t))

  (unless wg-current-session
    ;; code extracted from `wg-open-session'.
    ;; open session but do NOT load any workgroup.
    (let* ((session (read (wg-read-text wg-session-file))))
      (setf (wg-session-file-name session) wg-session-file)
      (wg-reset-internal (wg-unpickel-session-parameters session))))

  (wg-switch-to-workgroup (wg-make-and-add-workgroup name blank))

  ;; save the session file in real time
  (wg-save-session t)

  (wg-fontified-message
    (:cmd "Created: ") (:cur name) "  " (wg-workgroup-list-display)))

(defun wg-switch-to-workgroup (workgroup &optional noerror)
  "Switch to WORKGROUP.
NOERROR means fail silently."
  (interactive (list (wg-read-workgroup-name)))
  (fset 'buffer-list wg-buffer-list-original)
  (let ((workgroup (wg-get-workgroup-create workgroup))
        (current (wg-current-workgroup t)))
    (when (and (eq workgroup current) (not noerror))
      (error "Already on: %s" (wg-workgroup-name current)))
    (when current (push current wg-deactivation-list))
    (unwind-protect
        (progn
          ;; Before switch
          (run-hooks 'wg-before-switch-to-workgroup-hook)
          ;; Save info about some hard-to-work-with libraries
          (let (wg-flag-modified)
            (wg-set-workgroup-parameter 'ecb (and (boundp 'ecb-minor-mode)
                                                  ecb-minor-mode)))
          ;;(wg-set-workgroup-parameter (wg-current-workgroup t) 'ecb-win-config (ecb-current-window-configuration))
          ;; (type-of (ecb-current-window-configuration))
          ;; (type-of (car (ecb-current-window-configuration)))
          ;; (type-of (car (nthcdr 3 (ecb-current-window-configuration))))
          ;; (wg-pickelable-or-error (ecb-current-window-configuration))
          ;;(ecb-current-window-configuration)
          ;;)

          ;; Before switching - turn off ECB
          ;; https://github.com/pashinin/workgroups2/issues/34
          (if (and (boundp 'ecb-minor-mode)
                   (boundp 'ecb-frame)
                   (fboundp 'ecb-deactivate)
                   ecb-minor-mode
                   (equal ecb-frame (selected-frame)))
              (let ((ecb-split-edit-window-after-start 'before-deactivation))
                (ecb-deactivate)))

          ;; Switch
          (wg-restore-workgroup workgroup)
          (wg-set-previous-workgroup current)
          (wg-set-current-workgroup workgroup)

          ;; After switch
          ;; Save "last-workgroup" to the session params
          (let (wg-flag-modified)
            (awhen (wg-current-workgroup t)
              (wg-set-session-parameter 'last-workgroup (wg-workgroup-name it)))
            (awhen (wg-previous-workgroup t)
              (wg-set-session-parameter 'prev-workgroup (wg-workgroup-name it))))

          ;; If a workgroup had ECB - turn it on
          (if (and (boundp 'ecb-minor-mode)
                   (not ecb-minor-mode)
                   (fboundp 'ecb-activate)
                   (wg-workgroup-parameter (wg-current-workgroup t) 'ecb nil))
              (let ((ecb-split-edit-window-after-start 'before-deactivation))
                (ecb-activate)))
          ;;(ecb-last-window-config-before-deactivation
          ;; (wg-workgroup-parameter (wg-current-workgroup t) 'ecb-win-config nil)))

          ;; `sr-speedbar'
          ;; if *SPEEDBAR* buffer is visible - set some variables
          (let* ((buffers (mapcar 'window-buffer (window-list)))
                 (buffer-names (mapcar 'buffer-name buffers)))
            (when (and (featurep 'sr-speedbar)
                       (member sr-speedbar-buffer-name buffer-names))
              (setq sr-speedbar-window (get-buffer-window sr-speedbar-buffer-name))))

          ;; Finally
          (if wg-mess-with-buffer-list
              (fset 'buffer-list wg-buffer-list-function))
          (wg-fontified-message (:cmd "Switched: ") (wg-workgroup-name (wg-current-workgroup t)))
          (run-hooks 'wg-after-switch-to-workgroup-hook))
      (when current (pop wg-deactivation-list)))))

(defun wg-switch-to-workgroup-at-index (index)
  "Switch to the workgroup at INDEX in `wg-workgroup-list'."
  (interactive (list (or current-prefix-arg (wg-read-workgroup-index))))
  (let ((wl (wg-workgroup-list-or-error)))
    (wg-switch-to-workgroup
     (or (nth index wl) (error "There are only %d workgroups" (length wl))))))

(cl-macrolet
    ((define-range-of-switch-to-workgroup-at-index (num)
       `(progn
          ,@(wg-docar (i (wg-range 0 num))
              `(defun ,(intern (format "wg-switch-to-workgroup-at-index-%d" i)) ()
                 ,(format "Switch to the workgroup at index %d." i)
                 (interactive)
                 (wg-switch-to-workgroup-at-index ,i))))))
  (define-range-of-switch-to-workgroup-at-index 10))

(defun wg-switch-to-cyclic-nth-from-workgroup (workgroup n)
  "Switch N workgroups cyclically from WORKGROUP in `wg-workgroup-list.'"
  (let ((workgroup-list (wg-workgroup-list-or-error))
        (workgroup (wg-get-workgroup workgroup t)))
    (wg-switch-to-workgroup
     (cond ((not workgroup) (car workgroup-list))
           ((= 1 (length workgroup-list)) (error "There's only one workgroup"))
           (t (wg-cyclic-nth-from-workgroup workgroup n))))))

(defun wg-switch-to-workgroup-left (&optional workgroup n)
  "Switch to WORKGROUP that is (- N) places away from WORKGROUP in `wg-workgroup-list'.
Use `current-prefix-arg' for N if non-nil.  Otherwise N defaults to 1."
  (interactive (list nil current-prefix-arg))
  (wg-switch-to-cyclic-nth-from-workgroup workgroup (- (or n 1))))

(defun wg-switch-to-workgroup-right (&optional workgroup n)
  "Switch to the workgroup N places from WORKGROUP in `wg-workgroup-list'.
Use `current-prefix-arg' for N if non-nil.  Otherwise N defaults to 1."
  (interactive (list nil current-prefix-arg))
  (wg-switch-to-cyclic-nth-from-workgroup workgroup (or n 1)))

(defun wg-switch-to-previous-workgroup ()
  "Switch to the previous workgroup."
  (interactive)
  (wg-switch-to-workgroup (wg-previous-workgroup)))

(defun wg-wconfig-kill-ring ()
  "Return `wg-wconfig-kill-ring', creating it first if necessary."
  (or wg-wconfig-kill-ring
      (setq wg-wconfig-kill-ring (make-ring wg-wconfig-kill-ring-max))))

(defun wg-add-to-wconfig-kill-ring (wconfig)
  "Add WCONFIG to `wg-wconfig-kill-ring'."
  (ring-insert (wg-wconfig-kill-ring) wconfig))

(defun wg-kill-workgroup (&optional workgroup)
  "Kill WORKGROUP, saving its working-wconfig to the kill ring."
  (interactive)
  (let* ((workgroup (wg-get-workgroup workgroup))
         (to (or (wg-previous-workgroup t)
                 (wg-cyclic-nth-from-workgroup workgroup))))
    (wg-add-to-wconfig-kill-ring (wg-workgroup-working-wconfig workgroup))
    (wg-delete-workgroup workgroup)
    (if (eq workgroup to) (wg-restore-wconfig (wg-make-blank-wconfig))
      (wg-switch-to-workgroup to))
    (wg-fontified-message
      (:cmd "Killed: ")
      (:cur (wg-workgroup-name workgroup)) "  "
      (wg-workgroup-list-display))))

(defun wg-yank-wconfig ()
  "Restore a wconfig from `wg-wconfig-kill-ring'.
Successive yanks restore wconfigs sequentially from the kill
ring, starting at the front."
  (interactive)
  (when (zerop (ring-length (wg-wconfig-kill-ring)))
    (error "The kill-ring is empty"))
  (let ((pos (if (not (eq real-last-command 'wg-yank-wconfig)) 0
               (1+ (or (get 'wg-yank-wconfig :position) 0)))))
    (put 'wg-yank-wconfig :position pos)
    (wg-restore-wconfig-undoably (ring-ref (wg-wconfig-kill-ring) pos))
    (wg-fontified-message
      (:cmd "Yanked: ")
      (:msg (format "%S" pos)) "  "
      (wg-workgroup-list-display))))

(defun wg-kill-workgroup-and-buffers (&optional workgroup)
  "Kill WORKGROUP and the buffers in its working-wconfig."
  (interactive)
  (let* ((workgroup (wg-get-workgroup workgroup))
         (bufs (save-window-excursion
                 (wg-restore-workgroup workgroup)
                 (mapcar #'window-buffer (window-list)))))
    (wg-kill-workgroup workgroup)
    (mapc #'kill-buffer bufs)
    (wg-fontified-message
      (:cmd "Killed: ")
      (:cur (wg-workgroup-name workgroup))
      (:msg " and its buffers ") "\n"
      (wg-workgroup-list-display))))

(defun wg-delete-other-workgroups (&optional workgroup)
  "Delete all workgroups but WORKGROUP."
  (interactive)
  (let ((workgroup (wg-get-workgroup workgroup)))
    (unless (or wg-no-confirm-on-destructive-operation
                (y-or-n-p "Really delete all other workgroups? "))
      (error "Cancelled"))
    (dolist (w (wg-workgroup-list-or-error))
      (unless (eq w workgroup)
        (wg-delete-workgroup w)))
    (unless (wg-current-workgroup-p workgroup)
      (wg-switch-to-workgroup workgroup))
    (wg-fontified-message
      (:cmd "Deleted: ")
      (:msg "All workgroups but ")
      (:cur (wg-workgroup-name workgroup)))))

(defun wg-revert-workgroup (&optional workgroup)
  "Restore WORKGROUP's window configuration to its state at the last save."
  (interactive)
  (let* ((workgroup (wg-get-workgroup workgroup))
         (base-wconfig (wg-workgroup-base-wconfig workgroup)))
    (if (wg-current-workgroup-p workgroup)
        (wg-restore-wconfig-undoably base-wconfig)
      (wg-add-wconfig-to-undo-list workgroup base-wconfig))
    (wg-fontified-message
      (:cmd "Reverted: ")
      (:cur (wg-workgroup-name workgroup)))))

(defun wg-revert-all-workgroups ()
  "Revert all workgroups to their base wconfigs.
Only workgroups' working-wconfigs in `selected-frame' are
reverted."
  (interactive)
  (mapc #'wg-revert-workgroup (wg-workgroup-list-or-error))
  (wg-fontified-message
    (:cmd "Reverted: ")
    (:msg "All")))

(defun wg-workgroup-state-table (&optional frame)
  "Return FRAME's workgroup table, creating it first if necessary."
  (or (frame-parameter frame 'wg-workgroup-state-table)
      (let ((wtree (make-hash-table :test 'equal)))
        (set-frame-parameter frame 'wg-workgroup-state-table wtree)
        wtree)))

(defun wg-get-workgroup-state (workgroup &optional frame)
  "Return WORKGROUP's state table in a FRAME."
  (let ((uid (wg-workgroup-uid workgroup))
        (state-table (wg-workgroup-state-table frame)))
    (or (gethash uid state-table)
        (let ((wgs (wg-make-workgroup-state
                    :undo-pointer 0
                    :undo-list
                    (list (or (wg-workgroup-selected-frame-wconfig workgroup)
                              (wg-workgroup-base-wconfig workgroup))))))
          (puthash uid wgs state-table)
          wgs))))

(defmacro wg-with-undo (workgroup spec &rest body)
  "Bind WORKGROUP's undo state to SPEC and eval BODY."
  (declare (indent 2))
  (wg-dbind (state undo-pointer undo-list) spec
    `(let* ((,state (wg-get-workgroup-state ,workgroup))
            (,undo-pointer (wg-workgroup-state-undo-pointer ,state))
            (,undo-list (wg-workgroup-state-undo-list ,state)))
       ,@body)))

(defun wg-flag-just-exited-minibuffer ()
  "Added to `minibuffer-exit-hook'."
  (setq wg-just-exited-minibuffer t))

(defun wg-flag-window-configuration-changed ()
  "Set `wg-window-configuration-changed' to t.
But only if not the minibuffer was just exited.  Added to
`window-configuration-change-hook'."
  (if wg-just-exited-minibuffer
      (setq wg-just-exited-minibuffer nil)
    (progn
      (wg-flag-workgroup-modified)
      (setq wg-window-configuration-changed t))))

(defun wg-unflag-undoify-window-configuration-change ()
  "Set `wg-undoify-window-configuration-change' to nil, exempting
from undoification any window-configuration changes caused by the
current command."
  (setq wg-undoify-window-configuration-change nil))

(defun wg-set-workgroup-working-wconfig (workgroup wconfig)
  "Set the working-wconfig of WORKGROUP to WCONFIG."
  (wg-flag-workgroup-modified workgroup)
  (setf (wg-workgroup-selected-frame-wconfig workgroup) wconfig)
  (wg-with-undo workgroup (state undo-pointer undo-list)
    (setcar (nthcdr undo-pointer undo-list) wconfig)))

(defun wg-add-wconfig-to-undo-list (workgroup wconfig)
  "Add WCONFIG to WORKGROUP's undo list, truncating its future if necessary."
  (wg-with-undo workgroup (state undo-pointer undo-list)
    (let ((undo-list (cons nil (nthcdr undo-pointer undo-list))))
      (awhen (nthcdr wg-wconfig-undo-list-max undo-list) (setcdr it nil))
      (setf (wg-workgroup-state-undo-list state) undo-list))
    (setf (wg-workgroup-state-undo-pointer state) 0))
  (wg-set-workgroup-working-wconfig workgroup wconfig))

(defun wg-workgroup-working-wconfig (workgroup &optional noupdate)
  "Return WORKGROUP's working-wconfig.
If WORKGROUP is the current workgroup in `selected-frame', and
NOUPDATE is nil, set its working wconfig in `selected-frame' to
`wg-current-wconfig' and return the updated wconfig.  Otherwise
return WORKGROUP's current undo state."
  (if (and (not noupdate) (wg-current-workgroup-p workgroup))
      (wg-set-workgroup-working-wconfig workgroup (wg-current-wconfig))
    (wg-with-undo workgroup (state undo-pointer undo-list)
      (nth undo-pointer undo-list))))

(defun wg-update-current-workgroup-working-wconfig ()
  "Update `selected-frame's current workgroup's working-wconfig with `wg-current-wconfig'."
  (awhen (wg-current-workgroup t)
    (wg-set-workgroup-working-wconfig it (wg-current-wconfig))))

(defun wg-restore-wconfig-undoably (wconfig &optional noundo)
  "Restore WCONFIG in `selected-frame', saving undo information.
Skip undo when NOUNDO."
  (when noundo (wg-unflag-undoify-window-configuration-change))
  (wg-update-current-workgroup-working-wconfig)
  (wg-restore-wconfig wconfig))

(defun wg-workgroup-offset-position-in-undo-list (workgroup increment)
  "Increment WORKGROUP's undo-pointer by INCREMENT.
Also restore the wconfig at the incremented undo-pointer if
WORKGROUP is current."
  (wg-with-undo workgroup (state undo-pointer undo-list)
    (let ((new-pointer (+ undo-pointer increment)))
      (when (wg-within new-pointer 0 (length undo-list))
        (when (wg-current-workgroup-p workgroup)
          (wg-restore-wconfig-undoably (nth new-pointer undo-list) t))
        (setf (wg-workgroup-state-undo-pointer state) new-pointer)))))

(defun wg-undoify-window-configuration-change ()
  "Conditionally `wg-add-wconfig-to-undo-list'.
Added to `post-command-hook'."
  (when (and wg-window-configuration-changed         ;; When the window config has changed,
             wg-undoify-window-configuration-change  ;; and undoification is still on for the current command
             (wg-minibuffer-inactive-p))             ;; and the change didn't occur while the minibuffer is active,
    (-when-let (workgroup (wg-current-workgroup t))  ;; and there's a current workgroup,
      ;; add the current wconfig to that workgroup's undo list:
      (wg-add-wconfig-to-undo-list workgroup (wg-current-wconfig))))
  ;; Reset all flags no matter what:
  (setq wg-window-configuration-changed nil
        wg-undoify-window-configuration-change t
        wg-already-updated-working-wconfig nil))

(defun wg-update-working-wconfig-hook ()
  "Used in before advice on all functions that trigger `window-configuration-change-hook'.
To save up to date undo info before the change."
  (when (and (not wg-already-updated-working-wconfig)
             (wg-minibuffer-inactive-p))
    (wg-update-current-workgroup-working-wconfig)
    (setq wg-already-updated-working-wconfig t)))

(defun wg-workgroup-gc-buf-uids (workgroup)
  "Remove buf uids from WORKGROUP that have no referent in `wg-buf-list'."
  (wg-asetf (wg-workgroup-strong-buf-uids workgroup)
            (cl-remove-if-not 'wg-find-buf-by-uid it)
            (wg-workgroup-weak-buf-uids workgroup)
            (cl-remove-if-not 'wg-find-buf-by-uid it)))

(defun wg-display-internal (elt-fn list)
  "Return display string built by calling ELT-FN on each element of LIST."
  (let ((div (wg-add-face :div wg-list-display-decor-divider))
        (i -1))
    (wg-fontify
      (:brace wg-list-display-decor-left-brace)
      (if (not list) (funcall elt-fn nil nil)
        (wg-doconcat (elt list div) (funcall elt-fn elt (cl-incf i))))
      (:brace wg-list-display-decor-right-brace))))

(defun wg-workgroup-list-display (&optional workgroup-list)
  "Return the WORKGROUP-LIST display string.
The string contains the names of all workgroups in `wg-workgroup-list',
decorated with faces, dividers and strings identifying the
current and previous workgroups."
  (when wg-current-session
    (wg-display-internal 'wg-workgroup-display
                         (or workgroup-list (wg-workgroup-list)))))

(defun wg-create-first-wg ()
  "Create a first workgroup if needed."
  (when (and workgroups-mode
             wg-session-load-on-start
             (= (length (wg-workgroup-list)) 0))
    (wg-create-workgroup wg-first-wg-name)
    (wg-mark-everything-unmodified)))

(defun wg-pickel-workgroup-parameters (workgroup)
  "Return a copy of WORKGROUP after pickeling its parameters.
If WORKGROUP's parameters are non-nil, otherwise return
WORKGROUP."
  (if (not (wg-workgroup-parameters workgroup)) workgroup
    (let ((copy (wg-copy-workgroup workgroup)))
      (wg-asetf (wg-workgroup-parameters copy) (wg-pickel it))
      copy)))

(defun wg-unpickel-workgroup-parameters (workgroup)
  "If WORKGROUP's parameters are non-nil, return a copy of
WORKGROUP after unpickeling its parameters. Otherwise return
WORKGROUP."
  (if (not (wg-workgroup-parameters workgroup)) workgroup
    (let ((copy (wg-copy-workgroup workgroup)))
      (wg-asetf (wg-workgroup-parameters copy) (wg-unpickel it))
      copy)))

(defun wg-delete-workgroup (workgroup)
  "Remove WORKGROUP from `wg-workgroup-list'.
Also delete all references to it by `wg-workgroup-state-table',
`wg-current-workgroup' and `wg-previous-workgroup'."
  (dolist (frame (frame-list))
    (remhash (wg-workgroup-uid workgroup) (wg-workgroup-state-table frame))
    (when (wg-current-workgroup-p workgroup frame)
      (wg-set-current-workgroup nil frame))
    (when (wg-previous-workgroup-p workgroup frame)
      (wg-set-previous-workgroup nil frame)))
  (setf (wg-workgroup-list) (remove workgroup (wg-workgroup-list-or-error)))
  (wg-flag-session-modified)
  workgroup)

(defun wg-add-workgroup (workgroup &optional index)
  "Add WORKGROUP to `wg-workgroup-list' at INDEX or the end.
If a workgroup with the same name exists, overwrite it."
  (awhen (wg-find-workgroup-by :name (wg-workgroup-name workgroup) t)
    (unless index (setq index (cl-position it (wg-workgroup-list-or-error))))
    (wg-delete-workgroup it))
  (wg-asetf (wg-workgroup-list)
            (wg-insert-before workgroup it (or index (length it))))
  (wg-flag-session-modified)
  workgroup)

(defun wg-check-and-add-workgroup (workgroup)
  "Add WORKGROUP to `wg-workgroup-list'.
Ask to overwrite if a workgroup with the same name exists."
  (let ((name (wg-workgroup-name workgroup))
        (uid (wg-workgroup-uid workgroup)))
    (when (wg-find-workgroup-by :uid uid t)
      (error "A workgroup with uid %S already exists" uid))
    (when (wg-find-workgroup-by :name name t)
      (unless (or wg-no-confirm-on-destructive-operation
                  (y-or-n-p (format "%S exists. Overwrite? " name)))
        (error "Cancelled"))))
  (wg-add-workgroup workgroup))

(defun wg-make-and-add-workgroup (name &optional blank)
  "Create a workgroup named NAME with current `window-tree'.
If BLANK - then just scratch buffer.
Add it with `wg-check-and-add-workgroup'."
  (wg-check-and-add-workgroup
   (wg-make-workgroup
    :name name
    :base-wconfig (if blank (wg-make-blank-wconfig)
                    (wg-current-wconfig)))))

(defun wg-get-workgroup-create (workgroup)
  "Return the workgroup specified by WORKGROUP, creating a new one if needed.
If `wg-get-workgroup' on WORKGROUP returns a workgroup, return it.
Otherwise, if WORKGROUP is a string, create a new workgroup with
that name and return it.  Otherwise error."
  (or (wg-get-workgroup workgroup t)
      (if (stringp workgroup)
          (wg-make-and-add-workgroup workgroup)
        (wg-get-workgroup workgroup))))  ; Call this again for its error message

(defun wg-cyclic-offset-workgroup (workgroup n)
  "Offset WORKGROUP's position in `wg-workgroup-list' by N."
  (let ((workgroup-list (wg-workgroup-list-or-error)))
    (unless (member workgroup workgroup-list)
      (error "Workgroup isn't present in `wg-workgroup-list'."))
    (setf (wg-workgroup-list) (wg-cyclic-offset-elt workgroup workgroup-list n)
          (wg-session-modified (wg-current-session)) t)))

(defun wg-read-text (path)
  "Read text with PATH, using `utf-8' coding."
  (decode-coding-string
   (with-temp-buffer
     (set-buffer-multibyte nil)
     (setq buffer-file-coding-system 'binary)
     (insert-file-contents-literally path)
     (buffer-substring-no-properties (point-min) (point-max)))
   'utf-8))

(defun wg-open-session (filename)
  "Load a session visiting FILENAME, creating one if none already exists."
  (interactive "FFind session file: ")
  (cond ((file-exists-p filename)
         ;; TODO: handle errors when reading object
         (let ((session (read (wg-read-text filename))))
           (unless (wg-session-p session)
             (error "%S is not a Workgroups session file." filename))
           (setf (wg-session-file-name session) filename)
           (wg-reset-internal (wg-unpickel-session-parameters session)))

         (if wg-control-frames (wg-restore-frames))

         (awhen (wg-workgroup-list)
           (if (and wg-open-this-wg
                    (member wg-open-this-wg (wg-workgroup-names)))
               (wg-switch-to-workgroup wg-open-this-wg)
             (if (and wg-load-last-workgroup
                      (member (wg-session-parameter 'last-workgroup) (wg-workgroup-names)))
                 (wg-switch-to-workgroup (wg-session-parameter 'last-workgroup))
               (wg-switch-to-workgroup (car it))))
           (awhen (wg-session-parameter 'prev-workgroup)
             (when (and (member it (wg-workgroup-names))
                        (wg-get-workgroup it t))
               (wg-set-previous-workgroup (wg-get-workgroup it t)))))
         (wg-fontified-message (:cmd "Loaded: ") (:file filename))
         (wg-mark-everything-unmodified))
        (t
         (wg-query-and-save-if-modified)
         (wg-reset-internal (wg-make-session :file-name filename))
         (wg-fontified-message (:cmd "(New Workgroups session file)")))))
(defalias 'wg-find-session-file 'wg-open-session)

(defun wg-write-sexp-to-file (sexp file)
  "Write the printable representation of SEXP to FILE."
  (with-temp-buffer
    (let ((print-level nil)  (print-length nil))
      (insert (format "%S" sexp)))
    (write-file file)))

;; FIXME: Duplicate buf names probably shouldn't be allowed.  An unrelated error
;; causes two *scratch* buffers to be present, triggering the "uids don't match"
;; error.  Write something to remove bufs with duplicate names.
(defun wg-perform-session-maintenance ()
  "Perform various maintenance operations on the current Workgroups session."
  (wg-update-current-workgroup-working-wconfig)

  ;; Update every workgroup's base wconfig with `wg-workgroup-update-base-wconfig'
  (dolist (workgroup (wg-workgroup-list))
    (awhen (wg-workgroup-selected-frame-wconfig workgroup)
      (setf (wg-workgroup-base-wconfig workgroup) it
            (wg-workgroup-selected-frame-wconfig workgroup) nil)))

  ;; Garbage collection

  ;; Commenting this will cause a constantly growing session file:
  ;; (tried to comment this block to solve https://github.com/pashinin/workgroups2/issues/48)
  (let ((all-buf-uids (wg-all-buf-uids)))
    (wg-asetf (wg-buf-list)
              (cl-remove-if-not (lambda (uid) (member uid all-buf-uids)) it
                                :key 'wg-buf-uid)))

  (mapc 'wg-workgroup-gc-buf-uids (wg-workgroup-list))  ; Remove buf uids that have no referent in `wg-buf-list'
  (mapc 'wg-update-buffer-in-buf-list (wg-buffer-list-emacs)))

(defun wg-save-session-as (filename &optional confirm)
  "Write the current session into file FILENAME.
This makes the session visit that file, and marks it as not modified.

If optional second arg CONFIRM is non-nil, this function asks for
confirmation before overwriting an existing file.  Interactively,
confirmation is required unless you supply a prefix argument."
  (interactive (list (read-file-name "Save session as: ")
                     (not current-prefix-arg)))
  (when (and confirm (file-exists-p filename))
    (unless (y-or-n-p (format "File `%s' exists; overwrite? " filename))
      (error "Cancelled")))
  (unless (file-writable-p filename)
    (error "File %s can't be written to" filename))
  (wg-perform-session-maintenance)
  (setf (wg-session-file-name (wg-current-session)) filename)
  (setf (wg-session-version (wg-current-session)) wg-version)

  ;; Save opened frames as a session parameter "frame-list".
  ;; Exclude `selected-frame' and daemon one (if any).
  ;; http://stackoverflow.com/questions/21151992/why-emacs-as-daemon-gives-1-more-frame-than-is-opened
  (if wg-control-frames
      (let ((fl (frame-list)))
        ;; TODO: remove using dash
        (mapc (lambda (frame)
                (if (string-equal "initial_terminal" (terminal-name frame))
                    (delete frame fl))) fl)
        (setq fl (delete (selected-frame) fl))
        (let (wg-flag-modified)
          (wg-set-session-parameter 'frame-list (mapcar 'wg-frame-to-wconfig fl)))))
  (wg-write-sexp-to-file (wg-pickel-all-session-parameters) filename)
  (wg-fontified-message (:cmd "Wrote: ") (:file filename))
  (wg-mark-everything-unmodified))
(defalias 'wg-write-session-file 'wg-save-session-as)

(defun wg-get-session-file ()
  "Return the filename in which to save the session."
  (or (and wg-current-session
           (wg-session-file-name wg-current-session))
      wg-session-file))

(defun wg-save-session (&optional force)
  "Save the current Workgroups session if it's been modified.
When FORCE - save session regardless of whether it's been modified."
  (interactive "P")
  (ignore force)
  (wg-save-session-as (wg-get-session-file)))

(defun wg-reset-internal (session)
  "Reset Workgroups, setting `wg-current-session' to SESSION.
Resets all frame parameters, buffer-local vars, current session
object, etc.  SESSION nil defaults to a new, blank session."
  (mapc 'wg-reset-frame (frame-list))
  (mapc 'wg-reset-buffer (wg-buffer-list-emacs))
  (setq wg-wconfig-kill-ring nil)
  (setq wg-current-session session))

(defun wg-all-buf-uids (&optional session buffer-list)
  "Return the union of all SESSION buf-uids and BUFFER-LIST uids."
  (cl-union (cl-reduce 'wg-string-list-union  ; (wg-session-all-buf-uids session)
                       (wg-session-workgroup-list (or session (wg-current-session)))
                       :key 'wg-workgroup-all-buf-uids)
            ;; (wg-buffer-list-all-uids buffer-list)
            (delq nil (mapcar 'wg-buffer-uid (or buffer-list (wg-buffer-list-emacs))))
            :test 'string=))

(defun wg-modified-p ()
  "Return t when the current session or any of its workgroups are modified."
  (and wg-current-session
       (or (wg-session-modified wg-current-session)
           (cl-some 'wg-workgroup-modified (wg-workgroup-list)))))

(defun wg-mark-everything-unmodified ()
  "Mark the session and all workgroups as unmodified."
  (let (wg-undoify-window-configuration-change)    ; to skip WG's `post-command-hook' that marks "modified" again
    (when wg-current-session
      (setf (wg-session-modified wg-current-session) nil))
    (dolist (workgroup (wg-workgroup-list))
      (setf (wg-workgroup-modified workgroup) nil))))

(defun wg-session-parameter (parameter &optional default session)
  "Return session's value for PARAMETER.
If PARAMETER is not found, return DEFAULT which defaults to nil.
SESSION nil defaults to the current session."
  (wg-aget (wg-session-parameters (or session (wg-current-session)))
           parameter default))

(defun wg-set-session-parameter (parameter value)
  "Set PARAMETER to VALUE in SESSION.
SESSION nil means use the current session.  Return value."
  (when wg-current-session
    (wg-set-parameter (wg-session-parameters wg-current-session) parameter value)
    (wg-flag-session-modified)
    value))

(defun wg-session-local-value (variable &optional session)
  "Return the value of VARIABLE in SESSION.
SESSION nil defaults to the current session.  If VARIABLE does
not have a session-local binding in SESSION, the value is
resolved by Emacs."
  (let* ((undefined (cl-gensym))
         (value (wg-session-parameter variable undefined session)))
    (if (not (eq value undefined)) value
      (symbol-value variable))))

(defun wg-reset-frame (frame)
  "Reset Workgroups' `frame-parameters' in FRAME to nil."
  (set-frame-parameter frame 'wg-workgroup-state-table nil)
  (set-frame-parameter frame 'wg-current-workgroup-uid nil)
  (set-frame-parameter frame 'wg-previous-workgroup-uid nil))

(defun wg-save-session-on-exit (behavior)
  "Perform session-saving operations based on BEHAVIOR."
  (cl-case behavior
    (ask (wg-query-and-save-if-modified))
    (save (wg-save-session))))

(defun wg-reload-session ()
  "Reload current workgroups session."
  (interactive)
  (let* ((file (wg-get-session-file)))
    (condition-case err
        (wg-open-session file)
      (progn
        (wg-create-first-wg)
        (message "Error loading session-file: %s" err))))
        ;; TODO: print what exactly happened
  (wg-create-first-wg))

(defun wg-save-session-on-emacs-exit ()
  "Call `wg-save-session-on-exit' with `wg-emacs-exit-save-behavior'.
Added to `kill-emacs-query-functions'."
  (wg-save-session-on-exit wg-emacs-exit-save-behavior) t)

(defun wg-save-session-on-workgroups-mode-exit ()
  "Call `wg-save-session-on-exit' with `wg-workgroups-mode-exit-save-behavior'.
Called when `workgroups-mode' is turned off."
  (wg-save-session-on-exit wg-workgroups-mode-exit-save-behavior) t)

(defun wg-pickel-all-session-parameters (&optional session)
  "Return a copy of SESSION after pickeling its parameters.
And the parameters of all its workgroups."
  (let ((copy (wg-copy-session (or session (wg-current-session)))))
    (when (wg-session-parameters copy)
      (wg-asetf (wg-session-parameters copy) (wg-pickel it)))
    (wg-asetf (wg-session-workgroup-list copy)
              (cl-mapcar 'wg-pickel-workgroup-parameters it))
    copy))

(defun wg-unpickel-session-parameters (session)
  "Return a copy of SESSION after unpickeling its parameters.
And the parameters of all its workgroups."
  (let ((copy (wg-copy-session session)))
    (when (wg-session-parameters copy)
      (wg-asetf (wg-session-parameters copy) (wg-unpickel it)))
    (wg-asetf (wg-session-workgroup-list copy)
              (cl-mapcar 'wg-unpickel-workgroup-parameters it))
    copy))

(defvar wg-buffer-workgroup nil
  "Associating each buffer with the workgroup.
In which it most recently appeared.")
(make-variable-buffer-local 'wg-buffer-workgroup)

(defun wg-workgroup-associated-buf-uids (&optional workgroup)
  "Return a new list containing all of WORKGROUP's associated buf uids."
  (awhen (or workgroup (wg-current-workgroup t))
    (append (wg-workgroup-strong-buf-uids it)
            (wg-workgroup-weak-buf-uids it))))

(defun wg-workgroup-associated-bufs (workgroup)
  "Return a new list containing all of WORKGROUP's associated bufs."
  (delete nil (mapcar 'wg-find-buf-by-uid
                      (wg-workgroup-associated-buf-uids workgroup))))

(defun wg-workgroup-strongly-associate-bufobj (workgroup bufobj)
  "Strongly associate BUFOBJ with WORKGROUP."
  (let* ((uid (wg-bufobj-uid-or-add bufobj))
         (remp (wg-removef-p uid (wg-workgroup-weak-buf-uids workgroup)
                             :test 'string=))
         (addp (wg-pushnew-p uid (wg-workgroup-strong-buf-uids workgroup)
                             :test 'string=)))
    (when (or remp addp)
      (wg-flag-workgroup-modified workgroup)
      bufobj)))

(defun wg-workgroup-weakly-associate-bufobj (workgroup bufobj)
  "Weakly associate BUFOBJ with WORKGROUP."
  (let* ((uid (wg-bufobj-uid-or-add bufobj))
         (remp (wg-removef-p uid (wg-workgroup-strong-buf-uids workgroup)
                             :test 'string=))
         (addp (wg-pushnew-p uid (wg-workgroup-weak-buf-uids workgroup)
                             :test 'string=)))
    (when (or remp addp)
      (wg-flag-workgroup-modified workgroup)
      bufobj)))

(defun wg-workgroup-associate-bufobj (workgroup bufobj &optional weak)
  "Associate BUFOBJ with WORKGROUP.
WEAK non-nil means weakly associate it.  Otherwise strongly associate it."
  (if weak (wg-workgroup-weakly-associate-bufobj workgroup bufobj)
    (wg-workgroup-strongly-associate-bufobj workgroup bufobj)))

(defun wg-workgroup-dissociate-bufobj (workgroup bufobj)
  "Dissociate BUFOBJ from WORKGROUP."
  (let* ((uid (wg-bufobj-uid-or-add bufobj))
         (rem1p (wg-removef-p uid (wg-workgroup-strong-buf-uids workgroup)
                              :test 'string=))
         (rem2p (wg-removef-p uid (wg-workgroup-weak-buf-uids workgroup)
                              :test 'string=)))
    (when (or rem1p rem2p)
      (wg-flag-workgroup-modified workgroup)
      bufobj)))

(defun wg-auto-dissociate-buffer-hook ()
  "`kill-buffer-hook' that automatically dissociates buffers from workgroups."
  (when wg-dissociate-buffer-on-kill-buffer
    (awhen (wg-current-workgroup t)
      (wg-workgroup-dissociate-bufobj it (current-buffer)))))

(defun wg-associate-visible-buffers-with-workgroup (&optional workgroup weak)
  "Associate all buffers visible in `selected-frame' with WORKGROUP.
WEAK non-nil means weakly associate them.  Otherwise strongly
associate them."
  (interactive (list nil current-prefix-arg))
  (let ((workgroup (wg-get-workgroup workgroup))
        (buffers (mapcar 'window-buffer (window-list))))
    (dolist (buffer buffers)
      (wg-workgroup-associate-bufobj workgroup buffer weak))
    (wg-fontified-message
      (:cmd (format "%s associated: " (if weak "Weakly" "Strongly")))
      (wg-display-internal 'wg-buffer-display buffers))))

(defun wg-dissociate-buffer-from-workgroup (&optional workgroup buffer)
  "Dissociate BUFFER from WORKGROUP."
  (interactive (list nil nil))
  (let ((workgroup (wg-get-workgroup workgroup))
        (buffer (or buffer (current-buffer))))
    (wg-message
     (if (wg-workgroup-dissociate-bufobj workgroup buffer)
         "Dissociated %S from %s" "%S isn't associated with %s")
     (wg-buffer-name buffer)
     (wg-workgroup-name workgroup))))

(defun wg-associate-buffers (workgroup window-or-emacs-window-tree)
  "Associate the buffers visible in window elements of
WINDOW-OR-EMACS-WINDOW-TREE with the given WORKGROUP.
WINDOW-OR-EMACS-WINDOW-TREE must be either a window or a tree of
the form produced by `(car (window-tree))'."
  (if (windowp window-or-emacs-window-tree)
      (with-current-buffer (window-buffer window-or-emacs-window-tree)
        (setq wg-buffer-workgroup workgroup))
    (dolist (w (cddr window-or-emacs-window-tree))
      (when w (wg-associate-buffers workgroup w)))))

(defun wg-workgroup-bufobj-association-type (workgroup bufobj)
  "Return BUFOBJ's association-type in WORKGROUP, or nil if unassociated."
  (let ((uid (wg-bufobj-uid-or-add bufobj)))
    (or (and (member uid (wg-workgroup-strong-buf-uids workgroup)) 'strong)
        (and (member uid (wg-workgroup-weak-buf-uids workgroup)) 'weak))))

(defun wg-add-or-remove-workgroups-hooks (remove)
  "Add or remove all of Workgroups' hooks, depending on REMOVE."
  (wg-add-or-remove-hooks
   remove
   'kill-emacs-query-functions       'wg-save-session-on-emacs-exit
   'delete-frame-hook                'wg-update-working-wconfig-on-delete-frame
   'after-make-frame-functions       'wg-update-working-wconfig-on-make-frame
   'wg-pre-window-configuration-change-hook 'wg-update-working-wconfig-hook
   'window-configuration-change-hook 'wg-flag-window-configuration-changed
   'post-command-hook                'wg-undoify-window-configuration-change
   'minibuffer-exit-hook             'wg-flag-just-exited-minibuffer
   'kill-buffer-hook                 'wg-update-buffer-in-buf-list
   'kill-buffer-hook                 'wg-auto-dissociate-buffer-hook
   ))

;;;###autoload
(defun workgroups-mode (&optional arg)
  "Turn `workgroups-mode' on and off.
ARG is nil - toggle
ARG >= 1   - turn on
ARG == 0   - turn off
ARG is anything else, turn on `workgroups-mode'."
  (interactive (list current-prefix-arg))
  (setq workgroups-mode
        (cond ((not arg) (not workgroups-mode))
              ((integerp arg) (if (> arg 0) t nil))
              (t)))
  (cond
   (workgroups-mode
    (if (boundp 'desktop-restore-frames)
        (setq desktop-restore-frames nil))
    (wg-reset-internal (wg-make-session))                              ; creates a new `wg-current-session'
    (wg-add-workgroups-mode-minor-mode-entries)
    (wg-enable-all-advice)
    (wg-add-or-remove-workgroups-hooks nil)
    (wg-change-modeline)

    ;; some sr-speedbar hooks can harm
    (when (featurep 'sr-speedbar)
      (ad-disable-advice 'delete-other-windows 'around 'sr-speedbar-delete-other-window-advice)
      (ad-disable-advice 'delete-window 'before 'sr-speedbar-delete-window-advice))

    ;; Load session
    (when (and wg-session-load-on-start
               (file-exists-p wg-session-file))
      (condition-case err
          (wg-open-session wg-session-file)
        (error (message "Error finding `wg-session-file': %s" err))))
    (run-hooks 'workgroups-mode-hook))
   (t
    (wg-save-session-on-workgroups-mode-exit)
    (wg-disable-all-advice)
    (wg-add-or-remove-workgroups-hooks t)
    (wg-remove-mode-line-display)
    (run-hooks 'workgroups-mode-exit-hook)))
  (wg-fontified-message
    (:cmd "Workgroups Mode: ") (:msg (if workgroups-mode "on" "off")))
  (wg-create-first-wg)
  workgroups-mode)

;;;###autoload
(defun wg-help ()
  "Just call `apropos-command' on \"^wg-\".
There used to be a bunch of help-buffer construction stuff here,
including a `wg-help' variable that basically duplicated every
command's docstring;  But why, when there's `apropos-command'?"
  (interactive)
  (apropos-command "^wg-"))

;;;###autoload
(defun wg-open-workgroup ()
  "Open specific workgroup."
  (interactive)
  (let* ((group-names (mapcar (lambda (group)
                                ;; re-shape group for `completing-read'
                                (cons (wg-workgroup-name group) group))
                              (wg-session-workgroup-list
                               (read (wg-read-text wg-session-file)))))
         (selected-group (completing-read "Select work group: " group-names)))

    (when selected-group
      (wg-find-session-file wg-session-file)
      (wg-switch-to-workgroup selected-group))))

(provide 'workgroups2)
;;; workgroups2.el ends here
