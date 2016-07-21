;;; ido-ubiquitous.el --- Use ido (nearly) everywhere. -*- lexical-binding: t -*-

;; Copyright (C) 2011-2015 Ryan C. Thompson

;; Author: Ryan C. Thompson
;; URL: https://github.com/DarwinAwardWinner/ido-ubiquitous
;; Version: 3.15
;; Created: 2011-09-01
;; Keywords: convenience, completion, ido
;; EmacsWiki: InteractivelyDoThings
;; Package-Requires: ((emacs "24.1") (ido-completing-read+ "3.15") (cl-lib "0.5"))
;; Filename: ido-ubiquitous.el

;; This file is NOT part of GNU Emacs.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:

;; If you use the excellent `ido-mode' for efficient completion of
;; file names and buffers, you might wonder if you can get ido-style
;; completion everywhere else too. Well, that's what this package
;; does! ido-ubiquitous is here to enable ido-style completion for
;; (almost) every function that uses the standard completion function
;; `completing-read'.

;; To use this package, call `ido-ubiquitous-mode' to enable the mode,
;; or use `M-x customize-variable ido-ubiquitous-mode' it to enable it
;; permanently. Once the mode is enabled, most functions that use
;; `completing-read' will now have ido completion. If you decide in
;; the middle of a command that you would rather not use ido, just C-f
;; or C-b at the end/beginning of the input to fall back to non-ido
;; completion (this is the same shortcut as when using ido for buffers
;; or files).

;; Note that `completing-read' has some quirks and complex behavior
;; that ido cannot emulate. Ido-ubiquitous attempts to detect some of
;; these quirks and avoid using ido when it sees them. So some
;; functions will not have ido completion even when this mode is
;; enabled. Some other functions have ido disabled in them because
;; their packages already provide support for ido via other means (for
;; example, magit). See `M-x customize-group ido-ubiquitous' and read
;; about the override variables for more information.

;; ido-ubiquitous version 3.0 is a major update, including a split
;; into two packages, and some of the configuration options have
;; changed in non-backwards-compatible ways. If you have customized
;; ido-ubiquitous, be sure to check out `M-x customize-group
;; ido-ubiquitous' and `M-x customize-group ido-completing-read+'
;; after updating to 3.0 and make sure the new settings are to your
;; liking.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or (at
;; your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(defconst ido-ubiquitous-version "3.15"
  "Currently running version of ido-ubiquitous.

Note that when you update ido-ubiquitous, this variable may not
be updated until you restart Emacs.")

(eval-when-compile
  (when (or (not (boundp 'completing-read-function))
            (< emacs-major-version 24))
    (error "Could not find required variable `completing-read-function'. Are you using Emacs version 24 or higher? If you have Emacs 23 or lower, please downgrade to ido-ubiquitous version 1.7 (or upgrade Emacs).")))

(require 'ido)
(require 'advice)
(require 'cl-lib)
(require 'cus-edit)
(require 'ido-completing-read+)

;; Only exists in emacs 24.4 and up; we don't use this library
;; directly, but we load it here so we can test if it's available,
;; because if it isn't we need enable a workaround.
(require 'nadvice nil 'noerror)

;;; Debug messages

;;;###autoload
(define-minor-mode ido-ubiquitous-debug-mode
  "If non-nil, ido-ubiquitous will print debug info.

Debug info is printed to the *Messages* buffer."
  nil
  :global t
  :group 'ido-ubiquitous)

;; Defined as a macro for efficiency (args are not evaluated unless
;; debug mode is on)
(defmacro ido-ubiquitous--debug-message (format-string &rest args)
  `(when ido-ubiquitous-debug-mode
     (message (concat "ido-ubiquitous: " ,format-string) ,@args)))

(defun ido-ubiquitous--explain-fallback (arg)
  ;; This function accepts a string, or an ido-ubiquitous-fallback
  ;; signal.
  (when ido-ubiquitous-debug-mode
    (when (and (listp arg)
               (eq (car arg) 'ido-ubiquitous-fallback))
      (setq arg (cdr arg)))
    (ido-ubiquitous--debug-message "Falling back to `%s' because %s."
                                   ido-cr+-fallback-function arg)))

;;; Internal utility functions

(defun ido-ubiquitous--as-string (sym-or-str)
  "Return name of symbol, return string as is."
  (if (symbolp sym-or-str)
      (symbol-name sym-or-str)
    sym-or-str))

(defun ido-ubiquitous--as-symbol (sym-or-str)
  "Return string as symbol, return symbol as is."
  (if (symbolp sym-or-str)
      sym-or-str
    (intern sym-or-str)))

;;; Custom widget definitions

;; We need to define some custom widget types for use in the override
;; variables.

(define-widget 'lazy-notag 'lazy
  "Like lazy widget, but does not display its tag, only its value."
  :format "%v")

;; Define matcher functions and widgets for match specifications
(defvar ido-ubiquitous-match-spec-widget-types nil
  "List of widget names for match specs.")
(defvar ido-ubiquitous-spec-matchers nil
  "Alist of functions for matching function specs against function names.")
(cl-loop for (widget-name widget-tag key field-type matcher) in
         '((exact-match "Exact match" exact string string=)
           (prefix-match "Prefix match" prefix string string-prefix-p)
           (regexp-match "Regexp match" regexp regexp string-match-p))
         do (define-widget (ido-ubiquitous--as-symbol widget-name) 'lazy-notag widget-tag
              :menu-tag widget-tag
              :type `(list :tag ,widget-tag :format "%v"
                           (const :format ""
                                  :tag ,widget-tag
                                  ,key)
                           (,field-type :tag ,widget-tag)))
         do (add-to-list 'ido-ubiquitous-match-spec-widget-types
                         widget-name 'append)
         do (add-to-list 'ido-ubiquitous-spec-matchers
                         (cons key matcher) 'append))

(define-widget 'ido-ubiquitous-match-spec 'lazy-notag
  "Choice of exact, prefix, or regexp match."
  :type `(choice :tag "Match type"
                 ,@ido-ubiquitous-match-spec-widget-types))

(define-widget 'ido-ubiquitous-command-override-spec 'lazy-notag
  "Choice of override action plus match specification."
  :type '(cons :tag "Override rule"
               (choice :tag "For matching commands"
                       (const :menu-tag "Disable"
                              :tag "Disable ido-ubiquitous"
                              disable)
                       (const :menu-tag "Enable"
                              :tag "Enable ido-ubiquitous in normal default mode"
                              enable)
                       (const :menu-tag "Enable old-style default"
                              :tag "Enable ido-ubiquitous in old-style default mode"
                              enable-old))
               ido-ubiquitous-match-spec))

(define-widget 'ido-ubiquitous-function-override-spec 'lazy-notag
  "Choice of override action and function name. (Exact match only.)"
  :type '(list :tag "Override rule"
               (choice :tag "Do the following"
                       (const :menu-tag "Disable"
                              :tag "Disable ido-ubiquitous"
                              disable)
                       (const :menu-tag "Enable"
                              :tag "Enable ido-ubiquitous in normal default mode"
                              enable)
                       (const :menu-tag "Enable old-style default"
                              :tag "Enable ido-ubiquitous in old-style default mode"
                              enable-old))
               (const :format "" exact)
               (string :tag "For function")))

;;; Custom Declarations

(defgroup ido-ubiquitous nil
  "Use ido for (almost) all completion."
  :group 'ido
  :group 'ido-completing-read-plus)

;;;###autoload
(define-obsolete-variable-alias 'ido-ubiquitous
  'ido-ubiquitous-mode "ido-ubiquitous 0.8")
;;;###autoload
(define-obsolete-function-alias 'ido-ubiquitous
  'ido-ubiquitous-mode "ido-ubiquitous 0.8")

;;;###autoload
(define-minor-mode ido-ubiquitous-mode
  "Use `ido-completing-read' instead of `completing-read' almost everywhere.

If this mode causes problems for a function, you can customize
when ido completion is or is not used by customizing
`ido-ubiquitous-command-overrides' or
`ido-ubiquitous-function-overrides'."
  nil
  :global t
  :group 'ido-ubiquitous
  ;; Actually enable/disable the mode by setting
  ;; `completing-read-function'.
  (setq completing-read-function
        (if ido-ubiquitous-mode
            #'completing-read-ido-ubiquitous
          ido-cr+-fallback-function)))

;; Variables for functionality that has moved to ido-completing-read+
(define-obsolete-variable-alias
  'ido-ubiquitous-max-items
  'ido-cr+-max-items
  "ido-ubiquitous 3.0")
(define-obsolete-variable-alias
  'ido-ubiquitous-fallback-completing-read-function
  'ido-cr+-fallback-function
  "ido-ubiquitous 3.0")

(define-obsolete-variable-alias
  'ido-ubiquitous-enable-compatibility-globally
  'ido-ubiquitous-enable-old-style-default
  "ido-ubiquitous 2.0")

(defcustom ido-ubiquitous-default-state 'enable
  "Default ido-ubiquitous mode of operation for commands with no override.

This can be set to one of three options:

  * `enable': use normal ido completion;
  * `enable-old': use ido completion, but with emulation of the
    old-style default selection of `completing-read';
  * `disable': use non-ido completion.

Command-specific and function-specific overrides are available to
override this default for specific commands/functions. See
`ido-ubiquitous-command-overrides' and
`ido-ubiquitous-function-overrides'.

The `enable-old' option swaps the behavior of RET and C-j but
only for the first keypress after beginning completion.
Specifically, on the first keypress, RET will return an empty
string and C-j will return the first item on the list. The
purpose of this is to emulate a legacy compatibility quirk of
`completing-read'. From the `completing-read' docstring:

> If the input is null, `completing-read' returns DEF, or the
> first element of the list of default values, or an empty string
> if DEF is nil, regardless of the value of REQUIRE-MATCH.

This odd behavior is required for compatibility with an old-style
usage pattern whereby the default was requested by returning an
empty string. In this mode, the caller receives the empty string
and handles the default case manually, while `completing-read'
never has any knowledge of the default. This is a problem for
ido, which normally returns the first element in the list, not an
empty string, when the input is empty and you press RET. Without
knowledge of the default, it cannot ensure that the default is
first on the list, so returning the first item is not the correct
behavior. Instead, it must return an empty string like
`completing-read'.

The `disable' mode is available as a default, which seems
counterintuitive. But this allows you, if you so desire, to
enable ido-ubiquitous selectively for only a few specific commands
using overrides and disable it for everything else."
  :type '(choice :tag "Default mode"
                 (const :menu-tag "Disable"
                        :tag "Disable ido-ubiquitous"
                        disable)
                 (const :menu-tag "Enable"
                        :tag "Enable ido-ubiquitous in normal default mode"
                        enable)
                 (const :menu-tag "Enable old-style default"
                        :tag "Enable ido-ubiquitous in old-style default mode"
                        enable-old))
  :group 'ido-ubiquitous)

(make-obsolete-variable
 'ido-ubiquitous-enable-old-style-default
 "This variable no longer has any effect. Set
`ido-ubiquitous-default-state' to `enable-old' instead."
 "ido-ubiquitous 3.0")

(defconst ido-ubiquitous-default-command-overrides
  '(;; If you want ido for M-x, install smex
    (disable exact "execute-extended-command")
    ;; Wanderlust uses new-style default
    (enable prefix "wl-")
    ;; Info functions use old-style default selection
    (enable-old prefix "Info-")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/4
    (enable exact "webjump")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/28
    (enable regexp "\\`\\(find\\|load\\|locate\\)-library\\'")
    ;; https://github.com/bbatsov/prelude/issues/488
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/44
    ;; tmm implements its own non-standard completion mechanics
    (disable prefix "tmm-")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/47
    ;; theme functions don't need old-style compatibility
    (enable regexp "\\`\\(load\\|enable\\|disable\\|describe\\|custom-theme-visit\\)-theme\\'")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/79
    (enable-old prefix "bbdb-")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/83
    (enable-old exact "where-is")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/60
    (disable exact "todo-add-category")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/51
    (enable exact "find-tag")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/89
    (enable prefix "etags-select-")
    ) ; Close paren on separate line for better VC diffs
  "Default value of `ido-ubiquitous-command-overrides'.

You can restore these using the command `ido-ubiquitous-restore-default-overrides'.")

(defconst ido-ubiquitous-default-function-overrides
  '((disable exact "read-file-name")
    (disable exact "read-file-name-internal")
    (disable exact "read-buffer")
    (disable exact "gnus-emacs-completing-read")
    (disable exact "gnus-iswitchb-completing-read")
    (disable exact "grep-read-files")
    (disable exact "magit-builtin-completing-read")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/36
    (enable exact "bookmark-completing-read")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/4
    (enable-old exact "webjump-read-choice")
    (enable-old exact "webjump-read-url-choice")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/9
    (disable exact "isearchp-read-unicode-char")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/38
    (enable exact "read-char-by-name")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/39
    (disable exact "Info-read-node-name")
    ;; https://github.com/purcell/emacs.d/issues/182#issuecomment-44212927
    (disable exact "tmm-menubar")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/58
    ;; https://github.com/mooz/js2-mode/issues/181
    (enable exact "imenu--completion-buffer")
    ;; https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/74
    (enable-old exact "auto-insert")
    ) ; Close paren on separate line for better VC diffs
  "Default value of `ido-ubiquitous-function-overrides'.

You can restore these using the command `ido-ubiquitous-restore-default-overrides'.")

(defcustom ido-ubiquitous-command-overrides ido-ubiquitous-default-command-overrides
  "List of command override specifications for ido-ubiquitous

Each override specification describes how ido-ubiquitous should
behave one or many commands. A specification has the
form `(BEHAVIOR MATCH-TYPE MATCH-TEXT)'. BEHAVIOR is one of the
following:

  * `disable': ido-ubiquitous should not be used at all for the
    specified commands;
  * `enable': ido-ubiquitous may be used with the specified
    commands, without emulating the old-style default selection
    of `completing-read';
  * `enable-old': ido-ubiquitous may be used with the specified
    commands, and should emulate the old-style default selection
    of `completing-read'.

MATCH-TYPE affects how MATCH-TEXT is interpreted, as follows:

  * `exact': the specification only affects the one command
    whose name is MATCH-TEXT;
  * `prefix': the specification affects any command whose name
    starts with MATCH-TEXT (This is useful for specifying a
    certain behavior for an entire package);
  * `regexp': the specification affects any command whose name
    matches MATCH-TEXT (with MATCH-TEXT being interpreted as a
    regular expression)

MATCH-TEXT should be a string.

Since this variable's has a somewhat complex structure, it is
recommended that you set this variable through Customize.

Note that this variable only affects *commands*, which are
functions marked as interactive. See
`ido-ubiquitous-function-overrides' for how to modify the
behavior of ido-ubiquitous for arbitrary functions.

Note: If multiple overrides match the same commmand, the first
one in the list will take precedence.

If you need to add a new specification to this list, please also
file a bug report at https://github.com/DarwinAwardWinner/ido-ubiquitous/issues"
  :type '(repeat ido-ubiquitous-command-override-spec)
  :group 'ido-ubiquitous)

(defmacro ido-ubiquitous-with-override (override &rest body)
  "Eval BODY with specified OVERRIDE in place.

The OVERRIDE argument is evaluated normally, so if it is a
literal symbol, it must be quoted.

See `ido-ubiquitous-command-overrides' for valid override types."
  (declare (indent 1))
  ;; Eval override
  `(let ((ido-ubiquitous-next-override ,override))
     ,@body))

(defun ido-ubiquitous-apply-function-override (func override)
  "Set the override property on FUNC to OVERRIDE and set up advice to apply the override."
  (setq func (ido-ubiquitous--as-symbol func)
        override (ido-ubiquitous--as-symbol override))
  (if (memq override '(disable enable enable-old nil))
      (progn
        (put func 'ido-ubiquitous-override override)
        (when override
          (let ((docstring
                 (format "Override ido-ubiquitous behavior in %s if its `ido-ubiquitous-override' property is non-nil." func)))
            (eval
             `(defadvice ,func (around ido-ubiquitous-override activate)
                ,docstring
                (let* ((func ',func)
                       (override (get func 'ido-ubiquitous-override)))
                  (when override
                    (ido-ubiquitous--debug-message
                     "Using override `%s' for function `%s'"
                     override func))
                  (ido-ubiquitous-with-override override
                    ad-do-it)))))))
    (display-warning
     'ido-ubiquitous
     (format "Ignoring invalid override action `%s' for function `%s' found in `ido-ubiquitous-function-overrides'."
             override func)
     :warning)))

(defun ido-ubiquitous-set-function-overrides (sym newval)
  "Custom setter function for `ido-ubiquitous-function-overrides'.

In addition to setting the variable, this also sets up advice on
each function to apply the appropriate override."
  ;; Unset all previous overrides
  (when (boundp sym)
    (let ((oldval (eval sym)))
      (cl-loop for (_action _match-type func) in oldval
               do (ido-ubiquitous-apply-function-override func nil))))
  ;; Ensure that function names are strings, not symbols
  (setq newval
        (cl-loop for (action match-type func) in newval
                 collect (list action match-type
                               (ido-ubiquitous--as-string func))))
  ;; set new overrides
  (cl-loop for override in newval
           for (action match-type func) = override

           ;; Remove duplicate overrides
           if (member func overridden-functions)
           do (display-warning
               'ido-ubiquitous
               (format
                "Removing duplicate override for function `%s'" func))

           ;; Apply valid overrides
           else if (eq match-type 'exact)
           do (ido-ubiquitous-apply-function-override func action)
           and collect func into overridden-functions
           and collect override into final-value

           ;; Remove invalid overrides
           else
           do (display-warning
               'ido-ubiquitous
               (format
                "Removing invalid function override match-type `%s' for function `%s'; only match-type `exact' is supported in `ido-ubiquitous-function-overrides'."
                match-type func))

           ;; Set the value to only the overrides that were actually
           ;; applied.
           finally return
           (set-default sym final-value)))

(defcustom ido-ubiquitous-auto-update-overrides 'notify
  "Whether to add new overrides when updating ido-ubiquitous.

Ido-ubiquitous comes with a default set of overrides for commands
that are known to require them. New versions of ido-ubiquitous
may come with updates to the default overrides as more commands
are discovered to require them. However, customizing your own
overrides would normally prevent you from receiving these
updates, since Emacs will not overwrite your customizations.

To resolve this problem, you can set this variable to `t', and
then ido-ubiquitous can automatically add any new built-in
overrides whenever it is updated. (Actually, the update will
happen the next time Emacs is restarted after the update.) This
allows you to add your own overrides but still receive updates to
the default set. The default overrides will always be added with
lower precedence than user-added ones.

If you want ido-ubiquitous to just notify you about new default
overrides instead of adding them itself, set this variable to
`notify'. If you don't want this auto-update behavior at all, set
it to `nil'.

(Note that having this option enabled effectively prevents you
from removing any of the built-in default overrides, since they
will simply be re-added the next time Emacs starts. However, your
custom overrides will still take precedence, so this shouldn't be
a problem.)"
  :type '(choice :tag "When new overrides are available:"
                 (const :menu-tag "Auto-add"
                        :tag "Add them automatically"
                        t)
                 (const :menu-tag "Notify"
                        :tag "Notify the user about them"
                        notify)
                 (const :menu-tag "Ignore"
                        :tag "Ignore them"
                        nil))
  :group 'ido-ubiquitous)

(defcustom ido-ubiquitous-function-overrides ido-ubiquitous-default-function-overrides
  "List of function override specifications for ido-ubiquitous

Function override specifications have a similar structure to
command override specifications (see
`ido-ubiquitous-command-overrides'). A function override
specification has the form `(BEHAVIOR MATCH-TYPE MATCH-TEXT)'.
However, `MATCH-TYPE' may ONLY be `exact'; No other match type is
supported.

Note: If multiple overrides are set for the same function, the
first one in the list will take precedence, and the rest will be
ignored and deleted from the override list, with a warning.
Invalid override specifications will also be deleted with a
warning.

If you need to add a new specification to this list, please also file a
bug report at https://github.com/DarwinAwardWinner/ido-ubiquitous/issues

Setting this variable directly has no effect. You must set it
through Customize."
  :type '(repeat ido-ubiquitous-function-override-spec)
  :set 'ido-ubiquitous-set-function-overrides
  :group 'ido-ubiquitous)

(defcustom ido-ubiquitous-allow-on-functional-collection nil
  "Allow ido completion when COLLECTION is a function.

The `completing-read' function allows its COLLECTION argument to
be a function instead of a list of choices. Some such functions
simply return a list of completions and are suitable for use with
ido, but others implement more complex behavior and will result
in incorrect behavior if used with ido. Since there is no way to
tell the difference, this preference defaults to nil, which means
that ido-ubiquitous will not work when COLLECTION is a function
unless there is a specific override in effect. To disable this
safeguard and GUARANTEE ERRORS on some functions, you may set
this to non-nil, but this is not recommended."
  :type 'boolean
  :group 'ido-ubiquitous)

;;; ido-ubiquitous core

;; These variable are used to make ido-ubiquitous work properly in the
;; case that `completing-read' is called recursively (which is
;; possible when `enable-recursive-minibuffers' is non-nil.)
(defvar ido-ubiquitous-enable-next-call nil
  "If non-nil, then the next call to `ido-completing-read' is by ido-ubiquitous.")
(defvar ido-ubiquitous-enable-this-call nil
  "If non-nil, then the current call to `ido-completing-read' is by ido-ubiquitous.")
(defvar ido-ubiquitous-next-override nil
  "This holds the override to be applied on the next call to `completing-read'.

It's value can be nil or one of the symbols `disable', `enable', or
`enable-old'.

You should not modify this variable directly. Instead use the
macro `ido-ubiquitous-with-override'.")
(defvar ido-ubiquitous-active-override nil
  "This holds the override being applied to the current call to `completing-read'.

It's value can be nil or one of the symbols `disable', `enable', or
`enable-old'.

You should not modify this variable directly. Instead use the
macro `ido-ubiquitous-with-override'.")
(defvar ido-ubiquitous-active-state nil
  "This holds the ido-ubiquitous mode of operation for the current call to `completing-read'.

It's value can be nil or one of the symbols `disable', `enable', or
`enable-old'.

You should not modify this variable directly.")

(defadvice ido-completing-read (around ido-ubiquitous activate)
  "Enable ido-ubiquitous features if this call was done through ido-ubiquitous.

This advice ensures that `ido-ubiquitous-enable-this-call' is set
properly while `ido-completing-read' is executing. This variable
is used to determine whether to enable certain behaviors only for
ido-ubiquitous, not for ordinary ido completion."
  ;; Set "this" and clear "next" so it doesn't apply to nested calls.
  (let* ((ido-ubiquitous-enable-this-call ido-ubiquitous-enable-next-call)
         (ido-ubiquitous-enable-next-call nil)
         (ido-ubiquitous-initial-item nil))
    ad-do-it))

;; Signal used to trigger fallback (don't use `define-error' because
;; it's only supported in 24.4 and up)
(put 'ido-ubiquitous-fallback 'error-conditions '(ido-ubiquitous-fallback error))
(put 'ido-ubiquitous-fallback 'error-message "ido-ubiquitous-fallback")

(defun completing-read-ido-ubiquitous
    (prompt collection &optional predicate
            require-match initial-input
            hist def inherit-input-method)
  "ido-based method for reading from the minibuffer with completion.

See `completing-read' for the meaning of the arguments.

This function is a wrapper for `ido-completing-read' designed to
be used as the value of `completing-read-function'. Importantly,
it detects edge cases that ido cannot handle and uses normal
completion for them."
  (let (;; Save the original arguments in case we need to do the
        ;; fallback
        (orig-args
         (list prompt collection predicate require-match
               initial-input hist def inherit-input-method)))
    ;; Outer `condition-case' is the fallback handler
    (condition-case sig
        ;; Inner `condition-case' converts any unexpected errors into
        ;; fallback signals.
        (condition-case err
            (let* (;; Set the active override and clear the "next" one so it
                   ;; doesn't apply to nested calls.
                   (ido-ubiquitous-active-override ido-ubiquitous-next-override)
                   (ido-ubiquitous-next-override nil)
                   ;; Apply the active override, if any
                   (ido-ubiquitous-active-state
                    (or ido-ubiquitous-active-override
                        ido-ubiquitous-default-state
                        'enable)))
              ;; If ido-ubiquitous is disabled this time, fall back
              (when (eq ido-ubiquitous-active-state 'disable)
                (signal 'ido-ubiquitous-fallback
                        "`ido-ubiquitous-active-state' is `disable'"))
              ;; Handle a collection that is a function: either expand
              ;; completion list now or fall back
              (when (functionp collection)
                (if (or ido-ubiquitous-allow-on-functional-collection
                        (memq ido-ubiquitous-active-override
                              '(enable enable-old)))
                    (setq collection (all-completions "" collection predicate)
                          ;; `all-completions' will apply the predicate,
                          ;; so it now becomes redundant.
                          predicate nil)
                  (signal 'ido-ubiquitous-fallback
                          "COLLECTION is a function and there is no override")))
              (let ((ido-ubiquitous-enable-next-call t))
                (ido-completing-read+
                 prompt collection predicate require-match
                 initial-input hist def inherit-input-method)))
          (error
           (signal 'ido-ubiquitous-fallback
                   (format "ido-ubiquitous encountered an unexpected error: %S"
                           err))))
      ;; Handler for ido-ubiquitous-fallback signal
      (ido-ubiquitous-fallback
       (ido-ubiquitous--explain-fallback sig)
       (apply ido-cr+-fallback-function orig-args)))))
(define-obsolete-function-alias 'completing-read-ido 'completing-read-ido-ubiquitous
  "ido-ubiquitous 3.0")

;;; Old-style default support

(defvar ido-ubiquitous-initial-item nil
  "The first item selected when ido starts.

This is initialized to the first item in the list of completions
when ido starts, and is cleared when any character is entered
into the prompt or the list is cycled. If it is non-nil and still
equal to the first item in the completion list when ido exits,
then if `ido-ubiquitous-active-state' is `enable-old', ido
returns an empty string instead of the first item on the list.")

(defmacro ido-ubiquitous-set-initial-item (item)
  "Wrapper for `(setq ido-ubiquitous-initial-item ITEM)'.

This wrapper differs from simply doing `(setq
ido-ubiquitous-initial-item ITEM)' in several ways. First, it has
no effect (and does not evaluate ITEM) unless
`ido-ubiquitous-active-state' is `enable-old'. Second, it emits
appropriate debug messages."
  `(when (eq ido-ubiquitous-active-state 'enable-old)
     (let ((item ,item))
       (cond
        (item
         (ido-ubiquitous--debug-message
          "Setting `ido-ubiquitous-initial-item' to `%S'."
          item))
        (ido-ubiquitous-initial-item
         (ido-ubiquitous--debug-message "Clearing `ido-ubiquitous-initial-item'.")))
       (setq ido-ubiquitous-initial-item item))))

(defadvice ido-read-internal (before ido-ubiquitous-clear-initial-item activate)
  (ido-ubiquitous-set-initial-item nil))

(defadvice ido-make-choice-list (after ido-ubiquitous-set-initial-item activate)
  (ido-ubiquitous-set-initial-item
   (when (and ad-return-value (listp ad-return-value))
     (car ad-return-value))))

(defadvice ido-next-match (after ido-ubiquitous-clear-initial-item activate)
  (ido-ubiquitous-set-initial-item nil))

(defadvice ido-prev-match (after ido-ubiquitous-clear-initial-item activate)
  (ido-ubiquitous-set-initial-item nil))

;; Clear initial item after `self-insert-command'
(defun ido-ubiquitous-post-insert-hook ()
  (eval '(ido-ubiquitous-set-initial-item nil)))

(defun ido-ubiquitous-ido-minibuffer-setup-hook ()
  (add-hook
   'post-self-insert-hook
   #'ido-ubiquitous-post-insert-hook
   nil
   'local))

(add-hook 'ido-minibuffer-setup-hook
          #'ido-ubiquitous-ido-minibuffer-setup-hook)

(defun ido-ubiquitous-should-use-old-style-default ()
  "Returns non nil if ido-ubiquitous should emulate old-style default.

This function simply encapsulates all the checks that need to be
done in order to decide whether to swap RET and C-j. See
`ido-ubiquitous-default-state' for more information."
  ;; These checks outside the loop don't produce debug messages
  (and
   ;; Only if old-style default enabled
   (eq ido-ubiquitous-active-state 'enable-old)
   ;; This loop is just an implementation of `and' that reports which
   ;; arg was nil for debugging purposes.
   (cl-loop
    for test in
    '((bound-and-true-p ido-cur-item)
      ;; Only if completing a list, not a buffer or file
      (eq ido-cur-item 'list)
      ;; Only if this call was done through ido-ubiquitous
      ido-ubiquitous-enable-this-call
      ;; Only if default is nil
      (null ido-default-item)
      ;; Only if input is empty
      (string= ido-text "")
      ;; Only if `ido-ubiquitous-initial-item' hasn't been cleared
      ido-ubiquitous-initial-item
      ;; Only if initial item hasn't changed
      (string= (car ido-cur-list)
               ido-ubiquitous-initial-item))
    for test-result = (eval test)
    if (not test-result)
    do (ido-ubiquitous--debug-message
        "Not enabling old-style default selection because `%S' is nil"
        test)
    and return nil
    finally do (ido-ubiquitous--debug-message
                "Enabling old-style default selection")
    finally return t)))

(defadvice ido-exit-minibuffer (around ido-ubiquitous-old-style-default-compat activate)
  "Emulate a quirk of `completing-read'.

> If the input is null, `completing-read' returns DEF, or the
> first element of the list of default values, or an empty string
> if DEF is nil, regardless of the value of REQUIRE-MATCH.

See `ido-ubiquitous-default-state', which controls whether this
advice has any effect."
  (condition-case nil
      (if (ido-ubiquitous-should-use-old-style-default)
          (let ((ido-ubiquitous-active-state 'enable))
            (ido-select-text))
        ad-do-it)
    (error
     (display-warning 'ido-ubiquitous "Advice on `ido-exit-minibuffer' failed." :warning)
     ad-do-it))
  (ido-ubiquitous-set-initial-item nil))

(defadvice ido-select-text (around ido-ubiquitous-old-style-default-compat activate)
  "Emulate a quirk of `completing-read'.

> If the input is null, `completing-read' returns DEF, or the
> first element of the list of default values, or an empty string
> if DEF is nil, regardless of the value of REQUIRE-MATCH.

See `ido-ubiquitous-default-state', which controls whether this
advice has any effect."
  (condition-case nil
      (if (ido-ubiquitous-should-use-old-style-default)
          (let ((ido-ubiquitous-active-state 'enable))
            (ido-exit-minibuffer))
        ad-do-it)
    (error
     (display-warning 'ido-ubiquitous "Advice on `ido-select-text' failed." :warning)
     ad-do-it))
  (ido-ubiquitous-set-initial-item nil))

;;; Overrides

(defun ido-ubiquitous--overrides-have-same-target-p (o1 o2)
  (cl-destructuring-bind (oride1 type1 text1) o1
    (cl-destructuring-bind(oride2 type2 text2) o2
      ;; Avoid warnings about unused vars
      oride1 oride2
      (and (string= text1 text2)
           (eq type1 type2)))))

(defun ido-ubiquitous--combine-override-lists (olist1 olist2)
  "Append OLIST2 to OLIST1, but remove redundant elements.

Redundancy is determined using
`ido-ubiquitous--overrides-have-same-target-p'."
  (let ((olist2
         (cl-remove-if
          (lambda (o2) (cl-member
                   o2 olist1
                   :test #'ido-ubiquitous--overrides-have-same-target-p))
          olist2)))
    (append olist1 olist2)))

(defun ido-ubiquitous-update-overrides (&optional save quiet)
  "Re-add the default overrides without erasing custom overrides.

This is useful after an update of ido-ubiquitous that adds new
default overrides. See `ido-ubiquitous-auto-update-overrides' for
more information.

If SAVE is non-nil, also save the overrides to the user's custom
file (but only if they were already customized). When called
interactively, a prefix argument triggers a save.

When called from Lisp code, this function returns the list of
variables whose values were modified. In particular, it returns
non-nil if any variables were modified, and nil if no modifications
were made."
  (interactive "P")
  (let ((unmodified-vars nil)
        (updated-vars nil)
        (final-message-lines nil)
        (final-message-is-warning nil))
    (cl-loop
     for (var def) in
     '((ido-ubiquitous-command-overrides
        ido-ubiquitous-default-command-overrides)
       (ido-ubiquitous-function-overrides
        ido-ubiquitous-default-function-overrides))
     do (let* ((var-state (custom-variable-state var (eval var)))
               (curval (eval var))
               (defval (eval def))
               (newval (ido-ubiquitous--combine-override-lists
                        curval defval)))
          (cond
           ;; Nothing to add to var, do nothing
           ((and (equal curval newval)
                 (eq var-state 'saved))
            (ido-ubiquitous--debug-message
             "No need to modify value of option `%s'"
             var)
            (push var unmodified-vars))
           ;; Var is not customized, just set the new default
           ((eq var-state 'standard)
            (ido-ubiquitous--debug-message
             "Setting uncustomized option `%s' to its default value"
             var)
            (push var unmodified-vars)
            (set var defval))
           ;; Var is saved to custom.el, set and save new value (if
           ;; SAVE is t)
           ((and save
                 (eq var-state 'saved))
            (ido-ubiquitous--debug-message
             "Updating option `%s' with new overrides and saving it."
             var)
             (push var updated-vars)
             (customize-save-variable var newval))
           ;; Var is modified but not saved (or SAVE is nil), update it
           ;; but don't save it
           (t
            (ido-ubiquitous--debug-message
             "Updating option `%s' with new overrides but not saving it for future sessions."
             var)
            (push var updated-vars)
            (customize-set-variable var newval)))))
    (unless quiet
      ;; Now compose a single message that summarizes what was done
      (if (null updated-vars)
          (push "No updates to ido-ubiquitous override variables were needed."
                final-message-lines)
        (push
         (format "Updated the following ido-ubiquitous override variables: %S"
                 (sort updated-vars #'string<))
         final-message-lines)
        (if save
            (push
             "All updated variables were successfully saved."
             final-message-lines)
          (push
           "However, they have not been saved for future sessions. To save them, re-run this command with a prefix argument: `C-u M-x ido-ubiquitous-update-overrides'; or else manually inspect and save their values using `M-x customize-group ido-ubiquitous'."
           final-message-lines)
          (setq final-message-is-warning t)))
      (if final-message-is-warning
          (display-warning 'ido-ubiquitous
                           (mapconcat 'identity (nreverse final-message-lines) "\n"))
        (message (mapconcat 'identity (nreverse final-message-lines) "\n"))))
    updated-vars))

(defun ido-ubiquitous--find-override-updates (current-value available-updates)
  (cl-set-difference (ido-ubiquitous--combine-override-lists
                    current-value available-updates)
                     current-value))

(defun ido-ubiquitous--maybe-update-overrides ()
  "Maybe call `ido-ubiquitous-update-overrides.

See `ido-ubiquitous-auto-update-overrides."
  (if ido-ubiquitous-auto-update-overrides
      (let* ((command-override-updates
              (ido-ubiquitous--find-override-updates
               ido-ubiquitous-command-overrides
               ido-ubiquitous-default-command-overrides))
             (function-override-updates
              (ido-ubiquitous--find-override-updates
               ido-ubiquitous-function-overrides
               ido-ubiquitous-default-function-overrides))
             (update-count
              (+ (length command-override-updates)
                 (length function-override-updates))))
        (if (> update-count 0)
            (if (eq ido-ubiquitous-auto-update-overrides 'notify)
                (display-warning
                 'ido-ubiquitous
                 (format "There are %s new overrides available. Use `M-x ido-ubiquitous-update-overrides' to enable them. (See `ido-ubiquitous-auto-update-overrides' for more information.)"
                         update-count))
              (ido-ubiquitous--debug-message "Applying override updates.")
              (ido-ubiquitous-update-overrides t))
          (ido-ubiquitous--debug-message "No override updates availble.")))
    (ido-ubiquitous--debug-message "Skipping override updates by user preference.")))

(define-obsolete-function-alias
  'ido-ubiquitous-restore-default-overrides
  'ido-ubiquitous-update-overrides
  "ido-ubiquitous 3.9")

(defun ido-ubiquitous-spec-match (spec symbol)
  "Returns t if SPEC matches SYMBOL (which should be a function name).

See `ido-ubiquitous-command-overrides'. If the match spec is
invalid or any other error occurs, the error is demoted to a
warning and the function returns nil."
  (condition-case err
      (when (and symbol (symbolp symbol))
        (cl-destructuring-bind (type text) spec
          (let ((matcher (cdr (assoc type ido-ubiquitous-spec-matchers)))
                (text (ido-ubiquitous--as-string text))
                (symname (ido-ubiquitous--as-string symbol)))
            (if matcher
                (funcall matcher text symname)
              ;; If the matcher is invalid, issue a warning and return
              ;; nil.
              (error "Unknown match spec type \"%s\". See `ido-ubiquitous-spec-matchers' for valid types." type)
              nil))))
    (error
     (display-warning 'ido-ubiquitous "Error during ido-ubiquitous spec matching: %S" err)
     nil)))

(defun ido-ubiquitous-get-command-override (cmd)
  "Return the override associated with the command CMD.

If there is no override set for CMD in
`ido-ubiquitous-command-overrides', return nil."
  (when (and cmd (symbolp cmd))
    (cl-loop for override in ido-ubiquitous-command-overrides
             for (action . spec) = override
             for valid-action = (and (memq action '(disable enable enable-old nil))
                                     (assoc (car spec) ido-ubiquitous-spec-matchers))
             unless valid-action
             do (progn
                  (display-warning
                   'ido-ubiquitous
                   (format "Removing invalid override `%S' from `ido-ubiquitous-command-overrides'"
                           (cons action spec))
                   :warning)
                  (setq ido-ubiquitous-command-overrides
                        (remove override ido-ubiquitous-command-overrides)))
             when (and valid-action (ido-ubiquitous-spec-match spec cmd))
             return action

             finally return nil)))

;;; Workaround for https://github.com/DarwinAwardWinner/ido-ubiquitous/issues/24

;; When `call-interactively' is advised, `called-interactively-p'
;; always returns nil. So we redefine it (and `interactive-p') to test
;; the correct condition.

(defsubst ido-ubiquitous--looks-like-advised-orig (func)
  "Returns t if FUNC is a symbol starting with \"ad-Orig-\".

Such symbols are used to store the original definitions of
functions that have been advised by `defadvice' or similar."
  (and (symbolp func)
       (string-prefix-p "ad-Orig-" (symbol-name func))))

(defsubst ido-ubiquitous--looks-like-call-interactively (func)
  "Returns t if FUNC looks like the function `call-interactively'.

FUNC \"looks like\" `call-interactively' if it is the literal
symbol `call-interactively', or the value of `(symbol-function
'call-interactively)', or a symbol whose `symbol-function' is the
same as that of `call-interactively'.

This function is used to determine whether a given function was
\"called by\" `call-interactively' and therefore was called
interactively."
  (when func
    (eq (symbol-function 'call-interactively)
        (if (symbolp func)
            (symbol-function func)
          func))))

(defun ido-ubiquitous--backtrace-from (fun)
  "Return all backtrace frames, starting with the one for FUN.

FUN may be a list of functions, in which case the first one found
on the stack will be used."
  (let ((stack
         (cl-loop for i upfrom 0
                  for frame = (backtrace-frame i)
                  while frame
                  collect frame))
        (funcs (if (functionp fun)
                   (list fun)
                 fun)))
    (while (and stack
                (not (memq (cl-cadar stack) funcs)))
      (setq stack (cdr stack)))
    stack))

(defun ido-ubiquitous--clean-advice-from-backtrace (stack)
  "Takes a stack trace and cleans all evidence of advice.

Specifically, for each call to a function starting with
\"ad-Orig-\", that call and all prior calls up to but not
including the advised function's original name are deleted from
the stack."
  (let ((skipping-until nil))
    (cl-loop for frame in stack
             for func = (cadr frame)
             ;; Check if we found the frame we we're skipping to
             if (and skipping-until
                     (eq func skipping-until))
             do (setq skipping-until nil)
             ;; If we're looking at an the original form of an advised
             ;; function, skip until the real name of that function.
             if (and (not skipping-until)
                     (ido-ubiquitous--looks-like-advised-orig func))
             do (setq skipping-until
                      (intern
                       (substring (symbol-name func)
                                  (eval-when-compile (length "ad-Orig-")))))
             unless skipping-until collect frame)))

(defsubst ido-ubiquitous--interactive-internal ()
  "Equivalent of the INTERACTIVE macro in the Emacs C source.

This is an internal function that should never be called
directly.

See the C source for the logic behind this function."
  (and (not executing-kbd-macro)
       (not noninteractive)))

(defun ido-ubiquitous--interactive-p-internal ()
  "Equivalent of C function \"interactive_p\".

This is an internal function that should never be called
directly.

See the C source for the logic behind this function."
  (let ((stack
         ;; We clean advice from the backtrace. This ensures that we
         ;; get the right answer even if `call-interactively' has been
         ;; advised.
         (ido-ubiquitous--clean-advice-from-backtrace
          (cdr
           (ido-ubiquitous--backtrace-from
            '(called-interactively-p interactive-p))))))
    ;; See comments in the C function for the logic here.
    (while (and stack
                (or (eq (cl-cadar stack) 'bytecode)
                    (null (caar stack))))
      (setq stack (cdr stack)))
    ;; Top of stack is now the function that we want to know
    ;; about. Pop it, then check if the next function is
    ;; `call-interactively', using a more permissive test than the default.
    (ido-ubiquitous--looks-like-call-interactively (cl-cadadr stack))))

(defadvice call-interactively (around ido-ubiquitous activate)
  "Implements the behavior specified in `ido-ubiquitous-command-overrides'."
  (let* ((cmd (ad-get-arg 0))
         (override (ido-ubiquitous-get-command-override cmd)))
    (when override
      (ido-ubiquitous--debug-message "Using override `%s' for command `%s'"
                                     override cmd))
    (ido-ubiquitous-with-override override
        ad-do-it)))

;; Work around `called-interactively-p' in Emacs 24.3 and earlier,
;; which always returns nil when `call-interactively' is advised.
(when (not (and (featurep 'nadvice)
                (boundp 'called-interactively-p-functions)))

  (defadvice interactive-p (around ido-ubiquitous activate)
    "Return the correct result when `call-interactively' is advised.

This advice completely overrides the original definition."
    (condition-case nil
        (setq ad-return-value
              (and (ido-ubiquitous--interactive-internal)
                   (ido-ubiquitous--interactive-p-internal)))
      ;; In case of error in the advice, fall back to the default
      ;; implementation
      (error ad-do-it)))

  (defadvice called-interactively-p (around ido-ubiquitous activate)
    "Return the correct result when `call-interactively' is advised.

This advice completely overrides the original definition."
    (condition-case nil
        (setq ad-return-value
              (and (or (ido-ubiquitous--interactive-internal)
                       (not (eq kind 'interactive)))
                   (ido-ubiquitous--interactive-p-internal)))
      ;; In case of error in the advice, fall back to the default
      ;; implementation
      (error ad-do-it))))

;;; Other

(defsubst ido-ubiquitous--fixup-old-advice ()
  ;; Clean up old versions of ido-ubiquitous advice if they exist
  (ignore-errors (ad-remove-advice 'completing-read 'around 'ido-ubiquitous))
  (ignore-errors (ad-remove-advice 'ido-completing-read 'around 'detect-replacing-cr))
  (ignore-errors (ad-remove-advice 'ido-magic-forward-char 'before 'ido-ubiquitous-fallback))
  (ignore-errors (ad-remove-advice 'ido-magic-backward-char 'before 'ido-ubiquitous-fallback))
  (ignore-errors (ad-remove-advice 'ido-exit-minibuffer 'around 'compatibility))
  (ad-activate-all))

(defsubst ido-ubiquitous--fixup-old-magit-overrides ()
  (let ((old-override '(disable prefix "magit-"))
        (new-override '(disable exact "magit-builtin-completing-read")))
    (when (member old-override
                  ido-ubiquitous-command-overrides)
      (customize-set-variable
       'ido-ubiquitous-command-overrides
       (remove old-override ido-ubiquitous-command-overrides))
      (unless (member new-override ido-ubiquitous-function-overrides)
        (customize-set-variable 'ido-ubiquitous-function-overrides
                                (append ido-ubiquitous-function-overrides
                                        (list new-override))))
      (display-warning
       'ido-ubiquitous
       "Fixing obsolete magit overrides.

Magit has changed recently such that the old override that
ido-ubiquitous defined for it now causes problems. This old
override has been automatically removed and the new one added.
Please use `M-x customize-group ido-ubiquitous' and review the
override variables and save them to your customization file."
       :warning))))

(defun ido-ubiquitous-initialize ()
  "Do initial setup for ido-ubiquitous.

This only needs to be called once when the file is first loaded.
It cleans up any traces of old versions of ido-ubiquitous and
then sets up the mode."
  (ido-ubiquitous--fixup-old-advice)
  (ido-ubiquitous--fixup-old-magit-overrides)
  (ido-ubiquitous--maybe-update-overrides)
  ;; Make sure the mode is turned on/off as specified by the value of
  ;; the mode variable
  (ido-ubiquitous-mode (if ido-ubiquitous-mode 1 0)))
(ido-ubiquitous-initialize)

(provide 'ido-ubiquitous)
;; Local Variables:
;; indent-tabs-mode: nil
;; End:
;;; ido-ubiquitous.el ends here
