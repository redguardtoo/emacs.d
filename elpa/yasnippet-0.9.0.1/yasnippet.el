;;; yasnippet.el --- Yet another snippet extension for Emacs.

;; Copyright (C) 2008-2013 Free Software Foundation, Inc.
;; Authors: pluskid <pluskid@gmail.com>,  João Távora <joaotavora@gmail.com>
;; Maintainer: João Távora <joaotavora@gmail.com>
;; Version: 0.8.1
;; Package-version: 0.8.0
;; X-URL: http://github.com/capitaomorte/yasnippet
;; Keywords: convenience, emulation
;; URL: http://github.com/capitaomorte/yasnippet
;; EmacsWiki: YaSnippetMode

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;;   Basic steps to setup:
;;
;;    (add-to-list 'load-path
;;                 "~/path-to-yasnippet")
;;    (require 'yasnippet)
;;    (yas-global-mode 1)
;;
;;
;;   Interesting variables are:
;;
;;       `yas-snippet-dirs'
;;
;;           The directory where user-created snippets are to be
;;           stored.  Can also be a list of directories.  In that case,
;;           when used for bulk (re)loading of snippets (at startup or
;;           via `yas-reload-all'), directories appearing earlier in
;;           the list shadow other dir's snippets.  Also, the first
;;           directory is taken as the default for storing the user's
;;           new snippets.
;;
;;           The deprecated `yas/root-directory' aliases this variable
;;           for backward-compatibility.
;;
;;
;;   Major commands are:
;;
;;       M-x yas-expand
;;
;;           Try to expand snippets before point.  In `yas-minor-mode',
;;           this is normally bound to TAB, but you can customize it in
;;           `yas-minor-mode-map'.
;;
;;       M-x yas-load-directory
;;
;;           Prompts you for a directory hierarchy of snippets to load.
;;
;;       M-x yas-activate-extra-mode
;;
;;           Prompts you for an extra mode to add snippets for in the
;;           current buffer.
;;
;;       M-x yas-insert-snippet
;;
;;           Prompts you for possible snippet expansion if that is
;;           possible according to buffer-local and snippet-local
;;           expansion conditions.  With prefix argument, ignore these
;;           conditions.
;;
;;       M-x yas-visit-snippet-file
;;
;;           Prompts you for possible snippet expansions like
;;           `yas-insert-snippet', but instead of expanding it, takes
;;           you directly to the snippet definition's file, if it
;;           exists.
;;
;;       M-x yas-new-snippet
;;
;;           Lets you create a new snippet file in the correct
;;           subdirectory of `yas-snippet-dirs', according to the
;;           active major mode.
;;
;;       M-x yas-load-snippet-buffer
;;
;;           When editing a snippet, this loads the snippet.  This is
;;           bound to "C-c C-c" while in the `snippet-mode' editing
;;           mode.
;;
;;       M-x yas-tryout-snippet
;;
;;           When editing a snippet, this opens a new empty buffer,
;;           sets it to the appropriate major mode and inserts the
;;           snippet there, so you can see what it looks like.  This is
;;           bound to "C-c C-t" while in `snippet-mode'.
;;
;;       M-x yas-describe-tables
;;
;;           Lists known snippets in a separate buffer.  User is
;;           prompted as to whether only the currently active tables
;;           are to be displayed, or all the tables for all major
;;           modes.
;;
;;   If you have `dropdown-list' installed, you can optionally use it
;;   as the preferred "prompting method", putting in your .emacs file,
;;   for example:
;;
;;       (require 'dropdown-list)
;;       (setq yas-prompt-functions '(yas-dropdown-prompt
;;                                    yas-ido-prompt
;;                                    yas-completing-prompt))
;;
;;   Also check out the customization group
;;
;;        M-x customize-group RET yasnippet RET
;;
;;   If you use the customization group to set variables
;;   `yas-snippet-dirs' or `yas-global-mode', make sure the path to
;;   "yasnippet.el" is present in the `load-path' *before* the
;;   `custom-set-variables' is executed in your .emacs file.
;;
;;   For more information and detailed usage, refer to the project page:
;;      http://github.com/capitaomorte/yasnippet

;;; Code:

(require 'cl)
(require 'cl-lib)
(require 'easymenu)
(require 'help-mode)

(defvar yas--editing-template)
(defvar yas--guessed-modes)
(defvar yas--indent-original-column)
(defvar yas--scheduled-jit-loads)
(defvar yas-keymap)
(defvar yas-selected-text)
(defvar yas-verbosity)
(defvar yas--current-template)


;;; User customizable variables

(defgroup yasnippet nil
  "Yet Another Snippet extension"
  :group 'editing)

(defvar yas-installed-snippets-dir nil)
(setq yas-installed-snippets-dir
      (when load-file-name
        (concat (file-name-directory load-file-name) "snippets")))

(defcustom yas-snippet-dirs (remove nil
                                    (list "~/.emacs.d/snippets"
                                          'yas-installed-snippets-dir))
  "List of top-level snippet directories.

Each element, a string or a symbol whose value is a string,
designates a top-level directory where per-mode snippet
directories can be found.

Elements appearing earlier in the list shadow later elements'
snippets.

The first directory is taken as the default for storing snippet's
created with `yas-new-snippet'. "
  :type '(choice (string :tag "Single directory (string)")
                 (repeat :args (string) :tag "List of directories (strings)"))
  :group 'yasnippet
  :require 'yasnippet
  :set #'(lambda (symbol new)
           (let ((old (and (boundp symbol)
                           (symbol-value symbol))))
             (set-default symbol new)
             (unless (or (not (fboundp 'yas-reload-all))
                         (equal old new))
               (yas-reload-all)))))

(defun yas-snippet-dirs ()
  "Return variable `yas-snippet-dirs' as list of strings."
  (cl-loop for e in (if (listp yas-snippet-dirs)
                        yas-snippet-dirs
                      (list yas-snippet-dirs))
           collect
           (cond ((stringp e) e)
                 ((and (symbolp e)
                       (boundp e)
                       (stringp (symbol-value e)))
                  (symbol-value e))
                 (t
                  (error "[yas] invalid element %s in `yas-snippet-dirs'" e)))))

(defvaralias 'yas/root-directory 'yas-snippet-dirs)

(defcustom yas-new-snippet-default "\
# -*- mode: snippet; require-final-newline: nil -*-
# name: $1
# key: ${2:${1:$(yas--key-from-desc yas-text)}}${3:
# binding: ${4:direct-keybinding}}
# --
$0"
  "Default snippet to use when creating a new snippet.
If nil, don't use any snippet."
  :type 'string
  :group 'yasnippet)

(defcustom yas-prompt-functions '(yas-x-prompt
                                  yas-dropdown-prompt
                                  yas-completing-prompt
                                  yas-ido-prompt
                                  yas-no-prompt)
  "Functions to prompt for keys, templates, etc interactively.

These functions are called with the following arguments:

- PROMPT: A string to prompt the user

- CHOICES: a list of strings or objects.

- optional DISPLAY-FN : A function that, when applied to each of
the objects in CHOICES will return a string.

The return value of any function you put here should be one of
the objects in CHOICES, properly formatted with DISPLAY-FN (if
that is passed).

- To signal that your particular style of prompting is
unavailable at the moment, you can also have the function return
nil.

- To signal that the user quit the prompting process, you can
signal `quit' with

  (signal 'quit \"user quit!\")."
  :type '(repeat function)
  :group 'yasnippet)

(defcustom yas-indent-line 'auto
  "Controls indenting applied to a recent snippet expansion.

The following values are possible:

- `fixed' Indent the snippet to the current column;

- `auto' Indent each line of the snippet with `indent-according-to-mode'

Every other value means don't apply any snippet-side indentation
after expansion (the manual per-line \"$>\" indentation still
applies)."
  :type '(choice (const :tag "Nothing"  nothing)
                 (const :tag "Fixed"    fixed)
                 (const :tag "Auto"     auto))
  :group 'yasnippet)

(defcustom yas-also-auto-indent-first-line nil
  "Non-nil means also auto indent first line according to mode.

Naturally this is only valid when `yas-indent-line' is `auto'"
  :type 'boolean
  :group 'yasnippet)

(defcustom yas-snippet-revival t
  "Non-nil means re-activate snippet fields after undo/redo."
  :type 'boolean
  :group 'yasnippet)

(defcustom yas-triggers-in-field nil
  "If non-nil, allow stacked expansions (snippets inside snippets).

Otherwise `yas-next-field-or-maybe-expand' just moves on to the
next field"
  :type 'boolean
  :group 'yasnippet)

(defcustom yas-fallback-behavior 'call-other-command
  "How to act when `yas-expand' does *not* expand a snippet.

- `call-other-command' means try to temporarily disable YASnippet
    and call the next command bound to whatever key was used to
    invoke `yas-expand'.

- nil or the symbol `return-nil' mean do nothing. (and
  `yas-expand' returns nil)

- A Lisp form (apply COMMAND . ARGS) means interactively call
  COMMAND, if ARGS is non-nil, call COMMAND non-interactively
  with ARGS as arguments."
  :type '(choice (const :tag "Call previous command"  call-other-command)
                 (const :tag "Do nothing"             return-nil))
  :group 'yasnippet)

(defcustom yas-choose-keys-first nil
  "If non-nil, prompt for snippet key first, then for template.

Otherwise prompts for all possible snippet names.

This affects `yas-insert-snippet' and `yas-visit-snippet-file'."
  :type 'boolean
  :group 'yasnippet)

(defcustom yas-choose-tables-first nil
  "If non-nil, and multiple eligible snippet tables, prompts user for tables first.

Otherwise, user chooses between the merging together of all
eligible tables.

This affects `yas-insert-snippet', `yas-visit-snippet-file'"
  :type 'boolean
  :group 'yasnippet)

(defcustom yas-use-menu 'abbreviate
  "Display a YASnippet menu in the menu bar.

When non-nil, submenus for each snippet table will be listed
under the menu \"Yasnippet\".

- If set to `abbreviate', only the current major-mode
menu and the modes set in `yas--extra-modes' are listed.

- If set to `full', every submenu is listed

- If set to `nil', hide the menu.

Any other non-nil value, every submenu is listed."
  :type '(choice (const :tag "Full"  full)
                 (const :tag "Abbreviate" abbreviate)
                 (const :tag "No menu" nil))
  :group 'yasnippet)

(defcustom yas-trigger-symbol (or (and (eq window-system 'mac)
                                       (ignore-errors
                                         (char-to-string ?\x21E5))) ;; little ->| sign
                                  " =>")
  "The text that will be used in menu to represent the trigger."
  :type 'string
  :group 'yasnippet)

(defcustom yas-wrap-around-region nil
  "If non-nil, snippet expansion wraps around selected region.

The wrapping occurs just before the snippet's exit marker.  This
can be overridden on a per-snippet basis."
  :type 'boolean
  :group 'yasnippet)

(defcustom yas-good-grace t
  "If non-nil, don't raise errors in inline elisp evaluation.

An error string \"[yas] error\" is returned instead."
  :type 'boolean
  :group 'yasnippet)

(defcustom yas-visit-from-menu nil
  "If non-nil visit snippets's files from menu, instead of expanding them.

This can only work when snippets are loaded from files."
  :type 'boolean
  :group 'yasnippet)

(defcustom yas-expand-only-for-last-commands nil
  "List of `last-command' values to restrict tab-triggering to, or nil.

Leave this set at nil (the default) to be able to trigger an
expansion simply by placing the cursor after a valid tab trigger,
using whichever commands.

Optionally, set this to something like '(self-insert-command) if
you to wish restrict expansion to only happen when the last
letter of the snippet tab trigger was typed immediately before
the trigger key itself."
  :type '(repeat function)
  :group 'yasnippet)

;; Only two faces, and one of them shouldn't even be used...
;;
(defface yas-field-highlight-face
  '((t (:inherit 'region)))
  "The face used to highlight the currently active field of a snippet"
  :group 'yasnippet)

(defface yas--field-debug-face
  '()
  "The face used for debugging some overlays normally hidden"
  :group 'yasnippet)


;;; User-visible variables

(defvar yas-keymap  (let ((map (make-sparse-keymap)))
                      (define-key map [(tab)]       'yas-next-field-or-maybe-expand)
                      (define-key map (kbd "TAB")   'yas-next-field-or-maybe-expand)
                      (define-key map [(shift tab)] 'yas-prev-field)
                      (define-key map [backtab]     'yas-prev-field)
                      (define-key map (kbd "C-g")   'yas-abort-snippet)
                      (define-key map (kbd "C-d")   'yas-skip-and-clear-or-delete-char)
                      map)
  "The active keymap while a snippet expansion is in progress.")

(defvar yas-key-syntaxes (list "w" "w_" "w_." "w_.()"
                               #'yas-try-key-from-whitespace)
  "Syntaxes and functions to help look for trigger keys before point.

Each element in this list specifies how to skip buffer positions
backwards and look for the start of a trigger key.

Each element can be either a string or a function receiving the
original point as an argument. A string element is simply passed
to `skip-syntax-backward' whereas a function element is called
with no arguments and should also place point before the original
position.

The string between the resulting buffer position and the original
point is matched against the trigger keys in the active snippet
tables.

If no expandable snippets are found, the next element is the list
is tried, unless a function element returned the symbol `again',
in which case it is called again from the previous position and
may once more reposition point.

For example, if `yas-key-syntaxes'' value is '(\"w\" \"w_\"),
trigger keys composed exclusively of \"word\"-syntax characters
are looked for first. Failing that, longer keys composed of
\"word\" or \"symbol\" syntax are looked for. Therefore,
triggering after

foo-bar

will, according to the \"w\" element first try \"barbaz\". If
that isn't a trigger key, \"foo-barbaz\" is tried, respecting the
second \"w_\" element. Notice that even if \"baz\" is a trigger
key for an active snippet, it won't be expanded, unless a
function is added to `yas-key-syntaxes' that eventually places
point between \"bar\" and \"baz\".

See also Info node `(elisp) Syntax Descriptors'.")

(defvar yas-after-exit-snippet-hook
  '()
  "Hooks to run after a snippet exited.

The hooks will be run in an environment where some variables bound to
proper values:

`yas-snippet-beg' : The beginning of the region of the snippet.

`yas-snippet-end' : Similar to beg.

Attention: These hooks are not run when exiting nested/stacked snippet expansion!")

(defvar yas-before-expand-snippet-hook
  '()
  "Hooks to run just before expanding a snippet.")

(defvar yas-buffer-local-condition
  '(if (and (or (fourth (syntax-ppss))
                (fifth (syntax-ppss)))
	    this-command
            (eq this-command 'yas-expand-from-trigger-key))
       '(require-snippet-condition . force-in-comment)
     t)
  "Snippet expanding condition.

This variable is a Lisp form which is evaluated every time a
snippet expansion is attempted:

    * If it evaluates to nil, no snippets can be expanded.

    * If it evaluates to the a cons (require-snippet-condition
      . REQUIREMENT)

       * Snippets bearing no \"# condition:\" directive are not
         considered

       * Snippets bearing conditions that evaluate to nil (or
         produce an error) won't be considered.

       * If the snippet has a condition that evaluates to non-nil
         RESULT:

          * If REQUIREMENT is t, the snippet is considered

          * If REQUIREMENT is `eq' RESULT, the snippet is
            considered

          * Otherwise, the snippet is not considered.

    * If it evaluates to the symbol 'always, all snippets are
      considered for expansion, regardless of any conditions.

    * If it evaluates to t or some other non-nil value

       * Snippet bearing no conditions, or conditions that
         evaluate to non-nil, are considered for expansion.

       * Otherwise, the snippet is not considered.

Here's an example preventing snippets from being expanded from
inside comments, in `python-mode' only, with the exception of
snippets returning the symbol 'force-in-comment in their
conditions.

 (add-hook 'python-mode-hook
           '(lambda ()
              (setq yas-buffer-local-condition
                    '(if (python-in-string/comment)
                         '(require-snippet-condition . force-in-comment)
                       t))))

The default value is similar, it filters out potential snippet
expansions inside comments and string literals, unless the
snippet itself contains a condition that returns the symbol
`force-in-comment'.")


;;; Internal variables

(defvar yas--version "0.8.0beta")

(defvar yas--menu-table (make-hash-table)
  "A hash table of MAJOR-MODE symbols to menu keymaps.")

(defvar yas--known-modes
  '(ruby-mode rst-mode markdown-mode)
  "A list of mode which is well known but not part of Emacs.")

(defvar yas--escaped-characters
  '(?\\ ?` ?\" ?' ?$ ?} ?{ ?\( ?\))
  "List of characters which *might* need to be escaped.")

(defconst yas--field-regexp
  "${\\([0-9]+:\\)?\\([^}]*\\)}"
  "A regexp to *almost* recognize a field.")

(defconst yas--multi-dollar-lisp-expression-regexp
  "$+[ \t\n]*\\(([^)]*)\\)"
  "A regexp to *almost* recognize a \"$(...)\" expression.")

(defconst yas--backquote-lisp-expression-regexp
  "`\\([^`]*\\)`"
  "A regexp to recognize a \"`lisp-expression`\" expression." )

(defconst yas--transform-mirror-regexp
  "${\\(?:\\([0-9]+\\):\\)?$\\([ \t\n]*([^}]*\\)"
  "A regexp to *almost* recognize a mirror with a transform.")

(defconst yas--simple-mirror-regexp
  "$\\([0-9]+\\)"
  "A regexp to recognize a simple mirror.")

(defvar yas--snippet-id-seed 0
  "Contains the next id for a snippet.")

(defun yas--snippet-next-id ()
  (let ((id yas--snippet-id-seed))
    (incf yas--snippet-id-seed)
    id))


;;; Minor mode stuff

;; XXX: `last-buffer-undo-list' is somehow needed in Carbon Emacs for MacOSX
(defvar last-buffer-undo-list nil)

(defvar yas--minor-mode-menu nil
  "Holds the YASnippet menu.")

(defvar yas-minor-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(tab)]     'yas-expand)
    (define-key map (kbd "TAB") 'yas-expand)
    (define-key map "\C-c&\C-s" 'yas-insert-snippet)
    (define-key map "\C-c&\C-n" 'yas-new-snippet)
    (define-key map "\C-c&\C-v" 'yas-visit-snippet-file)
    map)
  "The keymap used when `yas-minor-mode' is active.")

(easy-menu-define yas--minor-mode-menu
      yas-minor-mode-map
      "Menu used when `yas-minor-mode' is active."
  '("YASnippet" :visible yas-use-menu
    "----"
    ["Expand trigger" yas-expand
     :help "Possibly expand tab trigger before point"]
    ["Insert at point..." yas-insert-snippet
     :help "Prompt for an expandable snippet and expand it at point"]
    ["New snippet..." yas-new-snippet
     :help "Create a new snippet in an appropriate directory"]
    ["Visit snippet file..." yas-visit-snippet-file
     :help "Prompt for an expandable snippet and find its file"]
    "----"
    ("Snippet menu behaviour"
     ["Visit snippets" (setq yas-visit-from-menu t)
      :help "Visit snippets from the menu"
      :active t :style radio   :selected yas-visit-from-menu]
     ["Expand snippets" (setq yas-visit-from-menu nil)
      :help "Expand snippets from the menu"
      :active t :style radio :selected (not yas-visit-from-menu)]
     "----"
     ["Show all known modes" (setq yas-use-menu 'full)
      :help "Show one snippet submenu for each loaded table"
      :active t :style radio   :selected (eq yas-use-menu 'full)]
     ["Abbreviate according to current mode" (setq yas-use-menu 'abbreviate)
      :help "Show only snippet submenus for the current active modes"
      :active t :style radio   :selected (eq yas-use-menu 'abbreviate)])
    ("Indenting"
     ["Auto" (setq yas-indent-line 'auto)
      :help "Indent each line of the snippet with `indent-according-to-mode'"
      :active t :style radio   :selected (eq yas-indent-line 'auto)]
     ["Fixed" (setq yas-indent-line 'fixed)
      :help "Indent the snippet to the current column"
      :active t :style radio   :selected (eq yas-indent-line 'fixed)]
     ["None" (setq yas-indent-line 'none)
      :help "Don't apply any particular snippet indentation after expansion"
      :active t :style radio   :selected (not (member yas-indent-line '(fixed auto)))]
     "----"
     ["Also auto indent first line" (setq yas-also-auto-indent-first-line
                                          (not yas-also-auto-indent-first-line))
      :help "When auto-indenting also, auto indent the first line menu"
      :active (eq yas-indent-line 'auto)
      :style toggle :selected yas-also-auto-indent-first-line]
     )
    ("Prompting method"
     ["System X-widget" (setq yas-prompt-functions
                              (cons 'yas-x-prompt
                                    (remove 'yas-x-prompt
                                            yas-prompt-functions)))
      :help "Use your windowing system's (gtk, mac, windows, etc...) default menu"
      :active t :style radio   :selected (eq (car yas-prompt-functions)
                                             'yas-x-prompt)]
     ["Dropdown-list" (setq yas-prompt-functions
                            (cons 'yas-dropdown-prompt
                                  (remove 'yas-dropdown-prompt
                                          yas-prompt-functions)))
      :help "Use a special dropdown list"
      :active t :style radio   :selected (eq (car yas-prompt-functions)
                                             'yas-dropdown-prompt)]
     ["Ido" (setq yas-prompt-functions
                  (cons 'yas-ido-prompt
                        (remove 'yas-ido-prompt
                                yas-prompt-functions)))
      :help "Use an ido-style minibuffer prompt"
      :active t :style radio   :selected (eq (car yas-prompt-functions)
                                             'yas-ido-prompt)]
     ["Completing read" (setq yas-prompt-functions
                              (cons 'yas-completing-prompt
                                    (remove 'yas-completing-prompt
                                            yas-prompt-functions)))
      :help "Use a normal minibuffer prompt"
      :active t :style radio   :selected (eq (car yas-prompt-functions)
                                             'yas-completing-prompt)]
     )
    ("Misc"
     ["Wrap region in exit marker"
      (setq yas-wrap-around-region
            (not yas-wrap-around-region))
      :help "If non-nil automatically wrap the selected text in the $0 snippet exit"
      :style toggle :selected yas-wrap-around-region]
     ["Allow stacked expansions "
      (setq yas-triggers-in-field
            (not yas-triggers-in-field))
      :help "If non-nil allow snippets to be triggered inside other snippet fields"
      :style toggle :selected yas-triggers-in-field]
     ["Revive snippets on undo "
      (setq yas-snippet-revival
            (not yas-snippet-revival))
      :help "If non-nil allow snippets to become active again after undo"
      :style toggle :selected yas-snippet-revival]
     ["Good grace "
      (setq yas-good-grace
            (not yas-good-grace))
      :help "If non-nil don't raise errors in bad embedded elisp in snippets"
      :style toggle :selected yas-good-grace]
     )
    "----"
    ["Load snippets..."  yas-load-directory
     :help "Load snippets from a specific directory"]
    ["Reload everything" yas-reload-all
     :help "Cleanup stuff, reload snippets, rebuild menus"]
    ["About"            yas-about
     :help "Display some information about YASnippet"]))

(defvar yas--extra-modes nil
  "An internal list of modes for which to also lookup snippets.

This variable probably makes more sense as buffer-local, so
ensure your use `make-local-variable' when you set it.")
(define-obsolete-variable-alias 'yas-extra-modes 'yas--extra-modes "0.8.1")

(defvar yas--tables (make-hash-table)
  "A hash table of mode symbols to `yas--table' objects.")

(defvar yas--parents (make-hash-table)
  "A hash table of mode symbols do lists of direct parent mode symbols.

This list is populated when reading the \".yas-parents\" files
found when traversing snippet directories with
`yas-load-directory'.

There might be additional parenting information stored in the
`derived-mode-parent' property of some mode symbols, but that is
not recorded here.")

(defvar yas--direct-keymaps (list)
  "Keymap alist supporting direct snippet keybindings.

This variable is placed in `emulation-mode-map-alists'.

Its elements looks like (TABLE-NAME . KEYMAP).  They're
instantiated on `yas-reload-all' but KEYMAP is added to only when
loading snippets.  `yas--direct-TABLE-NAME' is then a variable set
buffer-locally when entering `yas-minor-mode'.  KEYMAP binds all
defined direct keybindings to the command
`yas-expand-from-keymap' which then which snippet to expand.")

(defun yas-direct-keymaps-reload ()
  "Force reload the direct keybinding for active snippet tables."
  (interactive)
  (setq yas--direct-keymaps nil)
  (maphash #'(lambda (name table)
               (push (cons (intern (format "yas--direct-%s" name))
                           (yas--table-direct-keymap table))
                     yas--direct-keymaps))
           yas--tables))

(defun yas--modes-to-activate ()
  "Compute list of mode symbols that are active for `yas-expand'
and friends."
  (let (dfs)
    (setq dfs (lambda (mode &optional explored)
                (push mode explored)
                (cons mode
                      (loop for neighbour
                            in (cl-list* (get mode 'derived-mode-parent)
                                         (ignore-errors (symbol-function mode))
                                         (gethash mode yas--parents))
                            when (and neighbour
                                      (not (memq neighbour explored))
                                      (symbolp neighbour))
                            append (funcall dfs neighbour explored)))))
    (remove-duplicates (append yas--extra-modes
                               (funcall dfs major-mode)))))

(defvar yas-minor-mode-hook nil
  "Hook run when `yas-minor-mode' is turned on.")

;;;###autoload
(define-minor-mode yas-minor-mode
  "Toggle YASnippet mode.

When YASnippet mode is enabled, `yas-expand', normally bound to
the TAB key, expands snippets of code depending on the major
mode.

With no argument, this command toggles the mode.
positive prefix argument turns on the mode.
Negative prefix argument turns off the mode.

Key bindings:
\\{yas-minor-mode-map}"
  nil
  ;; The indicator for the mode line.
  " yas"
  :group 'yasnippet
  (cond (yas-minor-mode
         ;; Install the direct keymaps in `emulation-mode-map-alists'
         ;; (we use `add-hook' even though it's not technically a hook,
         ;; but it works). Then define variables named after modes to
         ;; index `yas--direct-keymaps'.
         ;;
         ;; Also install the post-command-hook.
         ;;
         (add-hook 'emulation-mode-map-alists 'yas--direct-keymaps)
         (add-hook 'post-command-hook 'yas--post-command-handler nil t)
         ;; Set the `yas--direct-%s' vars for direct keymap expansion
         ;;
         (dolist (mode (yas--modes-to-activate))
           (let ((name (intern (format "yas--direct-%s" mode))))
             (set-default name nil)
             (set (make-local-variable name) t)))
         ;; Perform JIT loads
         ;;
         (yas--load-pending-jits))
        (t
         ;; Uninstall the direct keymaps and the post-command hook
         ;;
         (remove-hook 'post-command-hook 'yas--post-command-handler t)
         (remove-hook 'emulation-mode-map-alists 'yas--direct-keymaps))))

(defun yas-activate-extra-mode (mode)
  "Activates the snippets for the given `mode' in the buffer.

The function can be called in the hook of a minor mode to
activate snippets associated with that mode."
  (interactive
   (let (modes
         symbol)
     (maphash (lambda (k _)
                (setq modes (cons (list k) modes)))
              yas--parents)
     (setq symbol (completing-read
                   "Activate mode: " modes nil t))
     (list
      (when (not (string= "" symbol))
        (intern symbol)))))
  (when mode
    (add-to-list (make-local-variable 'yas--extra-modes) mode)
    (yas--load-pending-jits)))

(defun yas-deactivate-extra-mode (mode)
  "Deactivates the snippets for the given `mode' in the buffer."
  (interactive
   (list (intern
          (completing-read
           "Deactivate mode: " (mapcar #'list yas--extra-modes) nil t))))
  (set (make-local-variable 'yas--extra-modes)
       (remove mode
               yas--extra-modes)))

(defvar yas-dont-activate '(minibufferp)
  "If non-nil don't let `yas-global-mode' affect some buffers.

If a function of zero arguments, then its result is used.

If a list of functions, then all functions must return nil to
activate yas for this buffer.

In Emacsen <= 23, this variable is buffer-local.  Because
`yas-minor-mode-on' is called by `yas-global-mode' after
executing the buffer's major mode hook, setting this variable
there is an effective way to define exceptions to the \"global\"
activation behaviour.

In Emacsen > 23, only the global value is used.  To define
per-mode exceptions to the \"global\" activation behaviour, call
`yas-minor-mode' with a negative argument directily in the major
mode's hook.")
(unless (> emacs-major-version 23)
  (with-no-warnings
    (make-variable-buffer-local 'yas-dont-activate)))


(defun yas-minor-mode-on ()
  "Turn on YASnippet minor mode.

Honour `yas-dont-activate', which see."
  (interactive)
  ;; Check `yas-dont-activate'
  (unless (cond ((functionp yas-dont-activate)
                 (funcall yas-dont-activate))
                ((consp yas-dont-activate)
                 (some #'funcall yas-dont-activate))
                (yas-dont-activate))
    (yas-minor-mode 1)))

;;;###autoload
(define-globalized-minor-mode yas-global-mode yas-minor-mode yas-minor-mode-on
  :group 'yasnippet
  :require 'yasnippet)

(defun yas--global-mode-reload-with-jit-maybe ()
  "Run `yas-reload-all' when `yas-global-mode' is on."
  (when yas-global-mode (yas-reload-all)))

(add-hook 'yas-global-mode-hook 'yas--global-mode-reload-with-jit-maybe)


;;; Major mode stuff

(defvar yas--font-lock-keywords
  (append '(("^#.*$" . font-lock-comment-face))
          lisp-font-lock-keywords-2
          '(("$\\([0-9]+\\)"
             (0 font-lock-keyword-face)
             (1 font-lock-string-face t))
            ("${\\([0-9]+\\):?"
             (0 font-lock-keyword-face)
             (1 font-lock-warning-face t))
            ("${" . font-lock-keyword-face)
            ("$[0-9]+?" . font-lock-preprocessor-face)
            ("\\(\\$(\\)" 1 font-lock-preprocessor-face)
            ("}"
             (0 font-lock-keyword-face)))))

(defvar snippet-mode-map
  (let ((map (make-sparse-keymap)))
    (easy-menu-define nil
      map
      "Menu used when snippet-mode is active."
      (cons "Snippet"
            (mapcar #'(lambda (ent)
                        (when (third ent)
                          (define-key map (third ent) (second ent)))
                        (vector (first ent) (second ent) t))
                    '(("Load this snippet" yas-load-snippet-buffer "\C-c\C-l")
                      ("Load and quit window" yas-load-snippet-buffer-and-close "\C-c\C-c")
                      ("Try out this snippet" yas-tryout-snippet "\C-c\C-t")))))
    map)
  "The keymap used when `snippet-mode' is active.")


(define-derived-mode snippet-mode text-mode "Snippet"
  "A mode for editing yasnippets"
  (setq font-lock-defaults '(yas--font-lock-keywords))
  (set (make-local-variable 'require-final-newline) nil)
  (set (make-local-variable 'comment-start) "#")
  (set (make-local-variable 'comment-start-skip) "#+[\t ]*"))



;;; Internal structs for template management

(defstruct (yas--template (:constructor yas--make-blank-template))
  "A template for a snippet."
  key
  content
  name
  condition
  expand-env
  file
  keybinding
  uuid
  menu-binding-pair
  group      ;; as dictated by the #group: directive or .yas-make-groups
  perm-group ;; as dictated by `yas-define-menu'
  table
  )

(defun yas--populate-template (template &rest args)
  "Helper function to populate TEMPLATE with properties."
  (while args
    (aset template
          (position (intern (substring (symbol-name (car args)) 1))
                    (mapcar #'car (get 'yas--template 'cl-struct-slots)))
          (second args))
    (setq args (cddr args)))
  template)

(defstruct (yas--table (:constructor yas--make-snippet-table (name)))
  "A table to store snippets for a particular mode.

Has the following fields:

`yas--table-name'

  A symbol name normally corresponding to a major mode, but can
  also be a pseudo major-mode to be used in
  `yas-activate-extra-mode', for example.

`yas--table-hash'

  A hash table (KEY . NAMEHASH), known as the \"keyhash\". KEY is
  a string or a vector, where the former is the snippet's trigger
  and the latter means it's a direct keybinding. NAMEHASH is yet
  another hash of (NAME . TEMPLATE) where NAME is the snippet's
  name and TEMPLATE is a `yas--template' object.

`yas--table-direct-keymap'

  A keymap for the snippets in this table that have direct
  keybindings. This is kept in sync with the keyhash, i.e., all
  the elements of the keyhash that are vectors appear here as
  bindings to `yas-expand-from-keymap'.

`yas--table-uuidhash'

  A hash table mapping snippets uuid's to the same `yas--template'
  objects. A snippet uuid defaults to the snippet's name."
  name
  (hash (make-hash-table :test 'equal))
  (uuidhash (make-hash-table :test 'equal))
  (parents nil)
  (direct-keymap (make-sparse-keymap)))

(defun yas--get-template-by-uuid (mode uuid)
  "Find the snippet template in MODE by its UUID."
  (let* ((table (gethash mode yas--tables mode)))
    (when table
      (gethash uuid (yas--table-uuidhash table)))))

;; Apropos storing/updating in TABLE, this works in two steps:
;;
;; 1. `yas--remove-template-by-uuid' removes any
;;    keyhash-namehash-template mappings from TABLE, grabbing the
;;    snippet by its uuid. Also removes mappings from TABLE's
;;    `yas--table-direct-keymap' (FIXME: and should probably take care
;;    of potentially stale menu bindings right?.)
;;
;; 2. `yas--add-template' adds this all over again.
;;
;;    Create a new or add to an existing keyhash-namehash mapping.
;;
;;  For reference on understanding this, consider three snippet
;;  definitions:
;;
;;  A:   # name: The Foo
;;       # key: foo
;;       # binding: C-c M-l
;;
;;  B:   # name: Mrs Foo
;;       # key: foo
;;
;;  C:   # name: The Bar
;;       # binding: C-c M-l
;;
;;  D:   # name: Baz
;;       # key: baz
;;
;;  keyhash       namehashes(3)      yas--template structs(4)
;;  -----------------------------------------------------
;;                                            __________
;;                                           /          \
;;  "foo"      --->  "The Foo" --->  [yas--template A]   |
;;                   "Mrs Foo" --->  [yas--template B]   |
;;                                                      |
;;  [C-c M-l]  --->  "The Foo" -------------------------/
;;                   "The Bar" --->  [yas--template C]
;;
;;  "baz"      --->  "Baz"     --->  [yas--template D]
;;
;; Additionally, since uuid defaults to the name, we have a
;; `yas--table-uuidhash' for TABLE
;;
;; uuidhash       yas--template structs
;; -------------------------------
;; "The Foo" ---> [yas--template A]
;; "Mrs Foo" ---> [yas--template B]
;; "The Bar" ---> [yas--template C]
;; "Baz"     ---> [yas--template D]
;;
;; FIXME: the more I look at this data-structure the more I think I'm
;; stupid. There has to be an easier way (but beware lots of code
;; depends on this).
;;
(defun yas--remove-template-by-uuid (table uuid)
  "Remove from TABLE a template identified by UUID."
  (let ((template (gethash uuid (yas--table-uuidhash table))))
    (when template
      (let* ((name                (yas--template-name template))
             (empty-keys          nil))
        ;; Remove the name from each of the targeted namehashes
        ;;
        (maphash #'(lambda (k v)
                     (let ((template (gethash name v)))
                       (when (and template
                                  (eq uuid (yas--template-uuid template)))
                         (remhash name v)
                         (when (zerop (hash-table-count v))
                           (push k empty-keys)))))
                 (yas--table-hash table))
        ;; Remove the namehash themselves if they've become empty
        ;;
        (dolist (key empty-keys)
          (when (vectorp key)
            (define-key (yas--table-direct-keymap table) key nil))
          (remhash key (yas--table-hash table)))

        ;; Finally, remove the uuid from the uuidhash
        ;;
        (remhash uuid (yas--table-uuidhash table))))))

(defun yas--add-template (table template)
  "Store in TABLE the snippet template TEMPLATE.

KEY can be a string (trigger key) of a vector (direct
keybinding)."
  (let ((name (yas--template-name template))
        (key (yas--template-key template))
        (keybinding (yas--template-keybinding template))
        (_menu-binding-pair (yas--template-menu-binding-pair-get-create template)))
    (dolist (k (remove nil (list key keybinding)))
      (puthash name
               template
               (or (gethash k
                            (yas--table-hash table))
                   (puthash k
                            (make-hash-table :test 'equal)
                            (yas--table-hash table))))
      (when (vectorp k)
        (define-key (yas--table-direct-keymap table) k 'yas-expand-from-keymap)))

    ;; Update TABLE's `yas--table-uuidhash'
    (puthash (yas--template-uuid template)
             template
             (yas--table-uuidhash table))))

(defun yas--update-template (table template)
  "Add or update TEMPLATE in TABLE.

Also takes care of adding and updating to the associated menu."
  ;; Remove from table by uuid
  ;;
  (yas--remove-template-by-uuid table (yas--template-uuid template))
  ;; Add to table again
  ;;
  (yas--add-template table template)
  ;; Take care of the menu
  ;;
  (yas--update-template-menu table template))

(defun yas--update-template-menu (table template)
  "Update every menu-related for TEMPLATE."
  (let ((menu-binding-pair (yas--template-menu-binding-pair-get-create template))
        (key (yas--template-key template))
        (keybinding (yas--template-keybinding template)))
    ;; The snippet might have changed name or keys, so update
    ;; user-visible strings
    ;;
    (unless (eq (cdr menu-binding-pair) :none)
      ;; the menu item name
      ;;
      (setf (cadar menu-binding-pair) (yas--template-name template))
      ;; the :keys information (also visible to the user)
      (setf (getf (cdr (car menu-binding-pair)) :keys)
            (or (and keybinding (key-description keybinding))
                (and key (concat key yas-trigger-symbol))))))
  (unless (yas--template-menu-managed-by-yas-define-menu template)
    (let ((menu-keymap
           (yas--menu-keymap-get-create (yas--table-mode table)
                                        (mapcar #'yas--table-mode
                                                (yas--table-parents table))))
          (group (yas--template-group template)))
      ;; Remove from menu keymap
      ;;
      (assert menu-keymap)
      (yas--delete-from-keymap menu-keymap (yas--template-uuid template))

      ;; Add necessary subgroups as necessary.
      ;;
      (dolist (subgroup group)
        (let ((subgroup-keymap (lookup-key menu-keymap (vector (make-symbol subgroup)))))
          (unless (and subgroup-keymap
                       (keymapp subgroup-keymap))
            (setq subgroup-keymap (make-sparse-keymap))
            (define-key menu-keymap (vector (make-symbol subgroup))
              `(menu-item ,subgroup ,subgroup-keymap)))
          (setq menu-keymap subgroup-keymap)))

      ;; Add this entry to the keymap
      ;;
      (define-key menu-keymap
        (vector (make-symbol (yas--template-uuid template)))
        (car (yas--template-menu-binding-pair template))))))

(defun yas--namehash-templates-alist (namehash)
  "Return NAMEHASH as an alist."
  (let (alist)
    (maphash #'(lambda (k v)
                 (push (cons k v) alist))
             namehash)
    alist))

(defun yas--fetch (table key)
  "Fetch templates in TABLE by KEY.

Return a list of cons (NAME . TEMPLATE) where NAME is a
string and TEMPLATE is a `yas--template' structure."
  (let* ((keyhash (yas--table-hash table))
         (namehash (and keyhash (gethash key keyhash))))
    (when namehash
      (yas--filter-templates-by-condition (yas--namehash-templates-alist namehash)))))


;;; Filtering/condition logic

(defun yas--eval-condition (condition)
  (condition-case err
      (save-excursion
        (save-restriction
          (save-match-data
            (eval condition))))
    (error (progn
             (yas--message 1 "Error in condition evaluation: %s" (error-message-string err))
             nil))))


(defun yas--filter-templates-by-condition (templates)
  "Filter the templates using the applicable condition.

TEMPLATES is a list of cons (NAME . TEMPLATE) where NAME is a
string and TEMPLATE is a `yas--template' structure.

This function implements the rules described in
`yas-buffer-local-condition'.  See that variables documentation."
  (let ((requirement (yas--require-template-specific-condition-p)))
    (if (eq requirement 'always)
        templates
      (remove-if-not #'(lambda (pair)
                         (yas--template-can-expand-p
                          (yas--template-condition (cdr pair)) requirement))
                     templates))))

(defun yas--require-template-specific-condition-p ()
  "Decide if this buffer requests/requires snippet-specific
conditions to filter out potential expansions."
  (if (eq 'always yas-buffer-local-condition)
      'always
    (let ((local-condition (or (and (consp yas-buffer-local-condition)
                                    (yas--eval-condition yas-buffer-local-condition))
                               yas-buffer-local-condition)))
      (when local-condition
        (if (eq local-condition t)
            t
          (and (consp local-condition)
               (eq 'require-snippet-condition (car local-condition))
               (symbolp (cdr local-condition))
               (cdr local-condition)))))))

(defun yas--template-can-expand-p (condition requirement)
  "Evaluate CONDITION and REQUIREMENT and return a boolean."
  (let* ((result (or (null condition)
                     (yas--eval-condition condition))))
    (cond ((eq requirement t)
           result)
          (t
           (eq requirement result)))))

(defun yas--table-templates (table)
  (when table
    (let ((acc (list)))
      (maphash #'(lambda (_key namehash)
                   (maphash #'(lambda (name template)
                                (push (cons name template) acc))
                            namehash))
               (yas--table-hash table))
      (yas--filter-templates-by-condition acc))))

(defun yas--templates-for-key-at-point ()
  "Find `yas--template' objects for any trigger keys preceding point.
Returns (TEMPLATES START END). This function respects
`yas-key-syntaxes', which see."
  (save-excursion
    (let ((original (point))
          (methods yas-key-syntaxes)
          (templates)
          (method))
      (while (and methods
                  (not templates))
        (unless (eq method (car methods))
          ;; TRICKY: `eq'-ness test means we can only be here if
          ;; `method' is a function that returned `again', and hence
          ;; don't revert back to original position as per
          ;; `yas-key-syntaxes'.
          (goto-char original))
        (setq method (car methods))
        (cond ((stringp method)
               (skip-syntax-backward method)
               (setq methods (cdr methods)))
              ((functionp method)
               (unless (eq (funcall method original)
                           'again)
                 (setq methods (cdr methods))))
              (t
               (yas--warning "Warning invalid element %s in `yas-key-syntaxes'" method)))
        (let ((possible-key (buffer-substring-no-properties (point) original)))
          (save-excursion
            (goto-char original)
            (setq templates
                  (mapcan #'(lambda (table)
                              (yas--fetch table possible-key))
                          (yas--get-snippet-tables))))))
      (when templates
        (list templates (point) original)))))

(defun yas--table-all-keys (table)
  "Get trigger keys of all active snippets in TABLE."
  (let ((acc))
    (maphash #'(lambda (key namehash)
                 (when (yas--filter-templates-by-condition (yas--namehash-templates-alist namehash))
                   (push key acc)))
             (yas--table-hash table))
    acc))

(defun yas--table-mode (table)
  (intern (yas--table-name table)))


;;; Internal functions and macros:

(defun yas--real-mode? (mode)
  "Try to find out if MODE is a real mode.

The MODE bound to a function (like `c-mode') is considered real
mode.  Other well known mode like `ruby-mode' which is not part of
Emacs might not bound to a function until it is loaded.  So
yasnippet keeps a list of modes like this to help the judgment."
  (or (fboundp mode)
      (find mode yas--known-modes)))

(defun yas--handle-error (err)
  "Handle error depending on value of `yas-good-grace'."
  (let ((msg (yas--format "elisp error: %s" (error-message-string err))))
    (if yas-good-grace msg
      (error "%s" msg))))

(defun yas--eval-lisp (form)
  "Evaluate FORM and convert the result to string."
  (let ((retval (catch 'yas--exception
                  (condition-case err
                      (save-excursion
                        (save-restriction
                          (save-match-data
                            (widen)
                            (let ((result (eval form)))
                              (when result
                                (format "%s" result))))))
                    (error (yas--handle-error err))))))
    (when (and (consp retval)
               (eq 'yas--exception (car retval)))
      (error (cdr retval)))
    retval))

(defun yas--eval-lisp-no-saves (form)
  (condition-case err
      (eval form)
    (error (message "%s" (yas--handle-error err)))))

(defun yas--read-lisp (string &optional nil-on-error)
  "Read STRING as a elisp expression and return it.

In case STRING in an invalid expression and NIL-ON-ERROR is nil,
return an expression that when evaluated will issue an error."
  (condition-case err
      (read string)
    (error (and (not nil-on-error)
                `(error (error-message-string ,err))))))

(defun yas--read-keybinding (keybinding)
  "Read KEYBINDING as a snippet keybinding, return a vector."
  (when (and keybinding
             (not (string-match "keybinding" keybinding)))
    (condition-case err
        (let ((res (or (and (string-match "^\\[.*\\]$" keybinding)
                            (read keybinding))
                       (read-kbd-macro keybinding 'need-vector))))
          res)
      (error
       (yas--message 3 "warning: keybinding \"%s\" invalid since %s."
                keybinding (error-message-string err))
       nil))))

(defun yas--table-get-create (mode)
  "Get or create the snippet table corresponding to MODE."
  (let ((table (gethash mode
                        yas--tables)))
    (unless table
      (setq table (yas--make-snippet-table (symbol-name mode)))
      (puthash mode table yas--tables)
      (push (cons (intern (format "yas--direct-%s" mode))
                  (yas--table-direct-keymap table))
            yas--direct-keymaps))
    table))

(defun yas--get-snippet-tables ()
  "Get snippet tables for current buffer.

Return a list of `yas--table' objects.  The list of modes to
consider is returned by `yas--modes-to-activate'"
  (remove nil
          (mapcar #'(lambda (name)
                      (gethash name yas--tables))
                  (yas--modes-to-activate))))

(defun yas--menu-keymap-get-create (mode &optional parents)
  "Get or create the menu keymap for MODE and its PARENTS.

This may very well create a plethora of menu keymaps and arrange
them all in `yas--menu-table'"
  (let* ((menu-keymap (or (gethash mode yas--menu-table)
                          (puthash mode (make-sparse-keymap) yas--menu-table))))
    (mapc #'yas--menu-keymap-get-create parents)
    (define-key yas--minor-mode-menu (vector mode)
        `(menu-item ,(symbol-name mode) ,menu-keymap
                    :visible (yas--show-menu-p ',mode)))
    menu-keymap))


(defmacro yas--called-interactively-p (&optional kind)
  "A backward-compatible version of `called-interactively-p'.

Optional KIND is as documented at `called-interactively-p'
in GNU Emacs 24.1 or higher."
  (if (string< emacs-version "24.1")
      '(called-interactively-p)
    `(called-interactively-p ,kind)))


;;; Template-related and snippet loading functions

(defun yas--parse-template (&optional file)
  "Parse the template in the current buffer.

Optional FILE is the absolute file name of the file being
parsed.

Optional GROUP is the group where the template is to go,
otherwise we attempt to calculate it from FILE.

Return a snippet-definition, i.e. a list

 (KEY TEMPLATE NAME CONDITION GROUP VARS FILE KEYBINDING UUID)

If the buffer contains a line of \"# --\" then the contents above
this line are ignored. Directives can set most of these with the syntax:

# directive-name : directive-value

Here's a list of currently recognized directives:

 * type
 * name
 * contributor
 * condition
 * group
 * key
 * expand-env
 * binding
 * uuid"
  (goto-char (point-min))
  (let* ((type 'snippet)
         (name (and file
                    (file-name-nondirectory file)))
         (key nil)
         template
         bound
         condition
         (group (and file
                     (yas--calculate-group file)))
         expand-env
         binding
         uuid)
    (if (re-search-forward "^# --\n" nil t)
        (progn (setq template
                     (buffer-substring-no-properties (point)
                                                     (point-max)))
               (setq bound (point))
               (goto-char (point-min))
               (while (re-search-forward "^# *\\([^ ]+?\\) *: *\\(.*\\)$" bound t)
                 (when (string= "uuid" (match-string-no-properties 1))
                   (setq uuid (match-string-no-properties 2)))
                 (when (string= "type" (match-string-no-properties 1))
                   (setq type (if (string= "command" (match-string-no-properties 2))
                                  'command
                                'snippet)))
                 (when (string= "key" (match-string-no-properties 1))
                   (setq key (match-string-no-properties 2)))
                 (when (string= "name" (match-string-no-properties 1))
                   (setq name (match-string-no-properties 2)))
                 (when (string= "condition" (match-string-no-properties 1))
                   (setq condition (yas--read-lisp (match-string-no-properties 2))))
                 (when (string= "group" (match-string-no-properties 1))
                   (setq group (match-string-no-properties 2)))
                 (when (string= "expand-env" (match-string-no-properties 1))
                   (setq expand-env (yas--read-lisp (match-string-no-properties 2)
                                                   'nil-on-error)))
                 (when (string= "binding" (match-string-no-properties 1))
                   (setq binding (match-string-no-properties 2)))))
      (setq template
            (buffer-substring-no-properties (point-min) (point-max))))
    (unless (or key binding)
      (setq key (and file (file-name-nondirectory file))))
    (when (eq type 'command)
      (setq template (yas--read-lisp (concat "(progn" template ")"))))
    (when group
      (setq group (split-string group "\\.")))
    (list key template name condition group expand-env file binding uuid)))

(defun yas--calculate-group (file)
  "Calculate the group for snippet file path FILE."
  (let* ((dominating-dir (locate-dominating-file file
                                                 ".yas-make-groups"))
         (extra-path (and dominating-dir
                          (replace-regexp-in-string (concat "^"
                                                            (expand-file-name dominating-dir))
                                                    ""
                                                    (expand-file-name file))))
         (extra-dir (and extra-path
                         (file-name-directory extra-path)))
         (group (and extra-dir
                     (replace-regexp-in-string "/"
                                               "."
                                               (directory-file-name extra-dir)))))
    group))

(defun yas--subdirs (directory &optional filep)
  "Return subdirs or files of DIRECTORY according to FILEP."
  (remove-if (lambda (file)
               (or (string-match "^\\."
                                 (file-name-nondirectory file))
                   (string-match "^#.*#$"
                                 (file-name-nondirectory file))
                   (string-match "~$"
                                 (file-name-nondirectory file))
                   (if filep
                       (file-directory-p file)
                     (not (file-directory-p file)))))
             (directory-files directory t)))

(defun yas--make-menu-binding (template)
  (let ((mode (yas--table-mode (yas--template-table template))))
    `(lambda () (interactive) (yas--expand-or-visit-from-menu ',mode ,(yas--template-uuid template)))))

(defun yas--expand-or-visit-from-menu (mode uuid)
  (let* ((table (yas--table-get-create mode))
         (yas--current-template (and table
                                    (gethash uuid (yas--table-uuidhash table)))))
    (when yas--current-template
      (if yas-visit-from-menu
          (yas--visit-snippet-file-1 yas--current-template)
        (let ((where (if (region-active-p)
                         (cons (region-beginning) (region-end))
                       (cons (point) (point)))))
          (yas-expand-snippet (yas--template-content yas--current-template)
                              (car where)
                              (cdr where)
                              (yas--template-expand-env yas--current-template)))))))

(defun yas--key-from-desc (text)
  "Return a yasnippet key from a description string TEXT."
  (replace-regexp-in-string "\\(\\w+\\).*" "\\1" text))


;;; Popping up for keys and templates

(defun yas--prompt-for-template (templates &optional prompt)
  "Interactively choose a template from the list TEMPLATES.

TEMPLATES is a list of `yas--template'.

Optional PROMPT sets the prompt to use."
  (when templates
    (setq templates
          (sort templates #'(lambda (t1 t2)
                              (< (length (yas--template-name t1))
                                 (length (yas--template-name t2))))))
    (some #'(lambda (fn)
              (funcall fn (or prompt "Choose a snippet: ")
                       templates
                       #'yas--template-name))
          yas-prompt-functions)))

(defun yas--prompt-for-keys (keys &optional prompt)
  "Interactively choose a template key from the list KEYS.

Optional PROMPT sets the prompt to use."
  (when keys
    (some #'(lambda (fn)
              (funcall fn (or prompt "Choose a snippet key: ") keys))
          yas-prompt-functions)))

(defun yas--prompt-for-table (tables &optional prompt)
  "Interactively choose a table from the list TABLES.

Optional PROMPT sets the prompt to use."
  (when tables
    (some #'(lambda (fn)
              (funcall fn (or prompt "Choose a snippet table: ")
                       tables
                       #'yas--table-name))
          yas-prompt-functions)))

(defun yas-x-prompt (prompt choices &optional display-fn)
  "Display choices in a x-window prompt."
  (when (and window-system choices)
    (or
     (x-popup-menu
      (if (fboundp 'posn-at-point)
          (let ((x-y (posn-x-y (posn-at-point (point)))))
            (list (list (+ (car x-y) 10)
                        (+ (cdr x-y) 20))
                  (selected-window)))
        t)
      `(,prompt ("title"
                 ,@(mapcar* (lambda (c d) `(,(concat "   " d) . ,c))
                            choices
                            (if display-fn (mapcar display-fn choices) choices)))))
     (keyboard-quit))))

(defun yas-ido-prompt (prompt choices &optional display-fn)
  (when (and (fboundp 'ido-completing-read)
	     (or (>= emacs-major-version 24)
		 ido-mode))
    (yas-completing-prompt prompt choices display-fn #'ido-completing-read)))

(defun yas-dropdown-prompt (_prompt choices &optional display-fn)
  (when (fboundp 'dropdown-list)
    (let* ((formatted-choices
            (if display-fn (mapcar display-fn choices) choices))
           (n (dropdown-list formatted-choices)))
      (if n (nth n choices)
        (keyboard-quit)))))

(defun yas-completing-prompt (prompt choices &optional display-fn completion-fn)
  (let* ((formatted-choices
          (if display-fn (mapcar display-fn choices) choices))
         (chosen (funcall (or completion-fn #'completing-read)
                          prompt formatted-choices
                          nil 'require-match nil nil)))
    (if (eq choices formatted-choices)
        chosen
      (nth (or (position chosen formatted-choices :test #'string=) 0)
           choices))))

(defun yas-no-prompt (_prompt choices &optional _display-fn)
  (first choices))


;;; Defining snippets
;; This consists of creating and registering `yas--template' objects in the
;; correct tables.
;;

(defvar yas--creating-compiled-snippets nil)

(defun yas--define-snippets-1 (snippet snippet-table)
  "Helper for `yas-define-snippets'."
  ;; X) Calculate some more defaults on the values returned by
  ;; `yas--parse-template'.
  ;;
  (let* ((file (seventh snippet))
         (key (car snippet))
         (name (or (third snippet)
                   (and file
                        (file-name-directory file))))
         (condition (fourth snippet))
         (group (fifth snippet))
         (keybinding (yas--read-keybinding (eighth snippet)))
         (uuid (or (ninth snippet)
                  name))
         (template (or (gethash uuid (yas--table-uuidhash snippet-table))
                       (yas--make-blank-template))))
    ;; X) populate the template object
    ;;
    (yas--populate-template template
                           :table       snippet-table
                           :key         key
                           :content     (second snippet)
                           :name        (or name key)
                           :group       group
                           :condition   condition
                           :expand-env  (sixth snippet)
                           :file        (seventh snippet)
                           :keybinding  keybinding
                           :uuid         uuid)
    ;; X) Update this template in the appropriate table. This step
    ;;    also will take care of adding the key indicators in the
    ;;    templates menu entry, if any
    ;;
    (yas--update-template snippet-table template)
    ;; X) Return the template
    ;;
    ;;
    template))

(defun yas-define-snippets (mode snippets)
  "Define SNIPPETS for MODE.

SNIPPETS is a list of snippet definitions, each taking the
following form

 (KEY TEMPLATE NAME CONDITION GROUP EXPAND-ENV FILE KEYBINDING UUID)

Within these, only KEY and TEMPLATE are actually mandatory.

TEMPLATE might be a Lisp form or a string, depending on whether
this is a snippet or a snippet-command.

CONDITION, EXPAND-ENV and KEYBINDING are Lisp forms, they have
been `yas--read-lisp'-ed and will eventually be
`yas--eval-lisp'-ed.

The remaining elements are strings.

FILE is probably of very little use if you're programatically
defining snippets.

UUID is the snippet's \"unique-id\". Loading a second snippet
file with the same uuid would replace the previous snippet.

You can use `yas--parse-template' to return such lists based on
the current buffers contents."
  (if yas--creating-compiled-snippets
      (progn
        (insert ";;; Snippet definitions:\n;;;\n")
        (let ((literal-snippets (list))
              (print-length nil))
          (dolist (snippet snippets)
            (let ((key                    (nth 0 snippet))
                  (template-content       (nth 1 snippet))
                  (name                   (nth 2 snippet))
                  (condition              (nth 3 snippet))
                  (group                  (nth 4 snippet))
                  (expand-env             (nth 5 snippet))
                  (file                   nil) ;; omit on purpose
                  (binding                (nth 7 snippet))
                  (uuid                   (nth 8 snippet)))
              (push `(,key
                      ,template-content
                      ,name
                      ,condition
                      ,group
                      ,expand-env
                      ,file
                      ,binding
                      ,uuid)
                    literal-snippets)))
          (insert (pp-to-string
                   `(yas-define-snippets ',mode ',literal-snippets)))
          (insert "\n\n")))
    ;; Normal case.
    (let ((snippet-table (yas--table-get-create mode))
          (template nil))
      (dolist (snippet snippets)
        (setq template (yas--define-snippets-1 snippet
                                               snippet-table)))
      template)))


;;; Loading snippets from files

(defun yas--load-yas-setup-file (file)
  (if (not yas--creating-compiled-snippets)
      ;; Normal case.
      (load file 'noerror)
    (let ((elfile (concat file ".el")))
      (when (file-exists-p elfile)
        (insert ";;; .yas-setup.el support file if any:\n;;;\n")
        (insert-file-contents elfile)
        (goto-char (point-max))))))

(defun yas--define-parents (mode parents)
  "Add PARENTS to the list of MODE's parents."
  (puthash mode (remove-duplicates
                 (append parents
                         (gethash mode yas--parents)))
           yas--parents))

(defun yas-load-directory (top-level-dir &optional use-jit interactive)
  "Load snippets in directory hierarchy TOP-LEVEL-DIR.

Below TOP-LEVEL-DIR each directory should be a mode name.

With prefix argument USE-JIT do jit-loading of snippets."
  (interactive
   (list (read-directory-name "Select the root directory: " nil nil t)
         current-prefix-arg t))
  (unless yas-snippet-dirs
    (setq yas-snippet-dirs top-level-dir))
  (let ((impatient-buffers))
    (dolist (dir (yas--subdirs top-level-dir))
      (let* ((major-mode-and-parents (yas--compute-major-mode-and-parents
                                      (concat dir "/dummy")))
             (mode-sym (car major-mode-and-parents))
             (parents (cdr major-mode-and-parents)))
        ;; Attention: The parents and the menus are already defined
        ;; here, even if the snippets are later jit-loaded.
        ;;
        ;; * We need to know the parents at this point since entering a
        ;;   given mode should jit load for its parents
        ;;   immediately. This could be reviewed, the parents could be
        ;;   discovered just-in-time-as well
        ;;
        ;; * We need to create the menus here to support the `full'
        ;;   option to `yas-use-menu' (all known snippet menus are shown to the user)
        ;;
        (yas--define-parents mode-sym parents)
        (yas--menu-keymap-get-create mode-sym)
        (let ((fun `(lambda () ;; FIXME: Simulating lexical-binding.
                      (yas--load-directory-1 ',dir ',mode-sym))))
          (if use-jit
              (yas--schedule-jit mode-sym fun)
            (funcall fun)))
        ;; Look for buffers that are already in `mode-sym', and so
        ;; need the new snippets immediately...
        ;; 
        (when use-jit 
          (cl-loop for buffer in (buffer-list)
                   do (with-current-buffer buffer
                        (when (eq major-mode mode-sym)
                          (yas--message 3 "Discovered there was already %s in %s" buffer mode-sym)
                          (push buffer impatient-buffers)))))))
    ;; ...after TOP-LEVEL-DIR has been completely loaded, call
    ;; `yas--load-pending-jits' in these impatient buffers.
    ;; 
    (cl-loop for buffer in impatient-buffers
             do (with-current-buffer buffer (yas--load-pending-jits))))
  (when interactive
    (yas--message 3 "Loaded snippets from %s." top-level-dir)))

(defun yas--load-directory-1 (directory mode-sym)
  "Recursively load snippet templates from DIRECTORY."
  (if yas--creating-compiled-snippets
      (let ((output-file (expand-file-name ".yas-compiled-snippets.el"
                                           directory)))
        (with-temp-file output-file
          (insert (format ";;; Compiled snippets and support files for `%s'\n"
                          mode-sym))
          (yas--load-directory-2 directory mode-sym)
          (insert (format ";;; Do not edit! File generated at %s\n"
                          (current-time-string)))))
    ;; Normal case.
    (unless (file-exists-p (concat directory "/" ".yas-skip"))
      (if (and (progn (yas--message 2 "Loading compiled snippets from %s" directory) t)
               (load (expand-file-name ".yas-compiled-snippets" directory) 'noerror (<= yas-verbosity 3)))
          (yas--message 2 "Loading snippet files from %s" directory)
        (yas--load-directory-2 directory mode-sym)))))

(defun yas--load-directory-2 (directory mode-sym)
  ;; Load .yas-setup.el files wherever we find them
  ;;
  (yas--load-yas-setup-file (expand-file-name ".yas-setup" directory))
  (let* ((default-directory directory)
         (snippet-defs nil))
    ;; load the snippet files
    ;;
    (with-temp-buffer
      (dolist (file (yas--subdirs directory 'no-subdirs-just-files))
        (when (file-readable-p file)
          (insert-file-contents file nil nil nil t)
          (push (yas--parse-template file)
                snippet-defs))))
    (when snippet-defs
      (yas-define-snippets mode-sym
                           snippet-defs))
    ;; now recurse to a lower level
    ;;
    (dolist (subdir (yas--subdirs directory))
      (yas--load-directory-2 subdir
                            mode-sym))))

(defun yas--load-snippet-dirs (&optional nojit)
  "Reload the directories listed in `yas-snippet-dirs' or
prompt the user to select one."
  (let (errors)
    (if yas-snippet-dirs
        (dolist (directory (reverse (yas-snippet-dirs)))
          (cond ((file-directory-p directory)
                 (yas-load-directory directory (not nojit))
                 (if nojit
                     (yas--message 3 "Loaded %s" directory)
                   (yas--message 3 "Prepared just-in-time loading for %s" directory)))
                (t
                 (push (yas--message 0 "Check your `yas-snippet-dirs': %s is not a directory" directory) errors))))
      (call-interactively 'yas-load-directory))
    errors))

(defun yas-reload-all (&optional no-jit interactive)
  "Reload all snippets and rebuild the YASnippet menu.

When NO-JIT is non-nil force immediate reload of all known
snippets under `yas-snippet-dirs', otherwise use just-in-time
loading.

When called interactively, use just-in-time loading when given a
prefix argument."
  (interactive (list (not current-prefix-arg) t))
  (catch 'abort
    (let ((errors)
          (snippet-editing-buffers
           (remove-if-not #'(lambda (buffer)
                              (with-current-buffer buffer yas--editing-template))
                          (buffer-list))))
      ;; Warn if there are buffers visiting snippets, since reloading will break
      ;; any on-line editing of those buffers.
      ;;
      (when snippet-editing-buffers
          (if interactive
              (if (y-or-n-p "Some buffers editing live snippets, close them and proceed with reload? ")
                  (mapc #'kill-buffer snippet-editing-buffers)
                (yas--message 1 "Aborted reload...")
                (throw 'abort nil))
            ;; in a non-interactive use, at least set
            ;; `yas--editing-template' to nil, make it guess it next time around
            (mapc #'(lambda (buffer)
                      (with-current-buffer buffer
                        (kill-local-variable 'yas--editing-template)))
                  (buffer-list))))

      ;; Empty all snippet tables and parenting info
      ;;
      (setq yas--tables (make-hash-table))
      (setq yas--parents (make-hash-table))

      ;; Before killing `yas--menu-table' use its keys to cleanup the
      ;; mode menu parts of `yas--minor-mode-menu' (thus also cleaning
      ;; up `yas-minor-mode-map', which points to it)
      ;;
      (maphash #'(lambda (menu-symbol _keymap)
                   (define-key yas--minor-mode-menu (vector menu-symbol) nil))
               yas--menu-table)
      ;; Now empty `yas--menu-table' as well
      (setq yas--menu-table (make-hash-table))

      ;; Cancel all pending 'yas--scheduled-jit-loads'
      ;;
      (setq yas--scheduled-jit-loads (make-hash-table))

      ;; Reload the directories listed in `yas-snippet-dirs' or prompt
      ;; the user to select one.
      ;;
      (setq errors (yas--load-snippet-dirs no-jit))
      ;; Reload the direct keybindings
      ;;
      (yas-direct-keymaps-reload)

      (run-hooks 'yas-after-reload-hook)
      (yas--message 3 "Reloaded everything%s...%s."
                   (if no-jit "" " (snippets will load just-in-time)")
                   (if errors " (some errors, check *Messages*)" "")))))

(defvar yas-after-reload-hook nil
  "Hooks run after `yas-reload-all'.")

(defun yas--load-pending-jits ()
  (dolist (mode (yas--modes-to-activate))
    (let ((funs (reverse (gethash mode yas--scheduled-jit-loads))))
      ;; must reverse to maintain coherence with `yas-snippet-dirs'
      (dolist (fun funs)
        (yas--message  3 "Loading for `%s', just-in-time: %s!" mode fun)
        (funcall fun))
      (remhash mode yas--scheduled-jit-loads))))

;; (when (<= emacs-major-version 22)
;;   (add-hook 'after-change-major-mode-hook 'yas--load-pending-jits))

(defun yas--quote-string (string)
  "Escape and quote STRING.
foo\"bar\\! -> \"foo\\\"bar\\\\!\""
  (concat "\""
          (replace-regexp-in-string "[\\\"]"
                                    "\\\\\\&"
                                    string
                                    t)
          "\""))

;;; Snippet compilation function

(defun yas--initialize ()
  "For backward compatibility, enable `yas-minor-mode' globally."
  (yas-global-mode 1))

(defun yas-compile-directory (top-level-dir)
  "Create .yas-compiled-snippets.el files under subdirs of TOP-LEVEL-DIR.

This works by stubbing a few functions, then calling
`yas-load-directory'."
  (interactive "DTop level snippet directory?")
  (let ((yas--creating-compiled-snippets t))
    (yas-load-directory top-level-dir nil)))

(defun yas-recompile-all ()
  "Compile every dir in `yas-snippet-dirs'."
  (interactive)
  (mapc #'yas-compile-directory (yas-snippet-dirs)))


;;; JIT loading
;;;

(defvar yas--scheduled-jit-loads (make-hash-table)
  "Alist of mode-symbols to forms to be evaled when `yas-minor-mode' kicks in.")

(defun yas--schedule-jit (mode fun)
  (push fun (gethash mode yas--scheduled-jit-loads)))



;;; Some user level functions

(defun yas-about ()
  (interactive)
  (message (concat "yasnippet (version "
                   yas--version
                   ") -- pluskid <pluskid@gmail.com>/joaotavora <joaotavora@gmail.com>")))


;;; Apropos snippet menu:
;;
;; The snippet menu keymaps are store by mode in hash table called
;; `yas--menu-table'. They are linked to the main menu in
;; `yas--menu-keymap-get-create' and are initially created empty,
;; reflecting the table hierarchy.
;;
;; They can be populated in two mutually exclusive ways: (1) by
;; reading `yas--template-group', which in turn is populated by the "#
;; group:" directives of the snippets or the ".yas-make-groups" file
;; or (2) by using a separate `yas-define-menu' call, which declares a
;; menu structure based on snippets uuids.
;;
;; Both situations are handled in `yas--update-template-menu', which
;; uses the predicate `yas--template-menu-managed-by-yas-define-menu'
;; that can tell between the two situations.
;;
;; Note:
;;
;; * if `yas-define-menu' is used it must run before
;;   `yas-define-snippets' and the UUIDS must match, otherwise we get
;;   duplicate entries. The `yas--template' objects are created in
;;   `yas-define-menu', holding nothing but the menu entry,
;;   represented by a pair of ((menu-item NAME :keys KEYS) TYPE) and
;;   stored in `yas--template-menu-binding-pair'. The (menu-item ...)
;;   part is then stored in the menu keymap itself which make the item
;;   appear to the user. These limitations could probably be revised.
;;
;; * The `yas--template-perm-group' slot is only used in
;;   `yas-describe-tables'.
;;
(defun yas--template-menu-binding-pair-get-create (template &optional type)
  "Get TEMPLATE's menu binding or assign it a new one.

TYPE may be `:stay', signaling this menu binding should be
static in the menu."
  (or (yas--template-menu-binding-pair template)
      (let (;; (key (yas--template-key template))
            ;; (keybinding (yas--template-keybinding template))
            )
        (setf (yas--template-menu-binding-pair template)
              (cons `(menu-item ,(or (yas--template-name template)
                                     (yas--template-uuid template))
                                ,(yas--make-menu-binding template)
                                :keys ,nil)
                    type)))))
(defun yas--template-menu-managed-by-yas-define-menu (template)
  "Non-nil if TEMPLATE's menu entry was included in a `yas-define-menu' call."
  (cdr (yas--template-menu-binding-pair template)))


(defun yas--show-menu-p (mode)
  (cond ((eq yas-use-menu 'abbreviate)
         (find mode
               (mapcar #'(lambda (table)
                           (yas--table-mode table))
                       (yas--get-snippet-tables))))
        (yas-use-menu t)))

(defun yas--delete-from-keymap (keymap uuid)
  "Recursively delete items with UUID from KEYMAP and its submenus."

  ;; XXX: This used to skip any submenus named \"parent mode\"
  ;;
  ;; First of all, recursively enter submenus, i.e. the tree is
  ;; searched depth first so that stale submenus can be found in the
  ;; higher passes.
  ;;
  (mapc #'(lambda (item)
            (when (and (listp (cdr item))
                       (keymapp (third (cdr item))))
              (yas--delete-from-keymap (third (cdr item)) uuid)))
        (rest keymap))
  ;; Set the uuid entry to nil
  ;;
  (define-key keymap (vector (make-symbol uuid)) nil)
  ;; Destructively modify keymap
  ;;
  (setcdr keymap (delete-if #'(lambda (item)
                                (or (null (cdr item))
                                    (and (keymapp (third (cdr item)))
                                         (null (cdr (third (cdr item)))))))
                            (rest keymap))))

(defun yas-define-menu (mode menu &optional omit-items)
  "Define a snippet menu for MODE according to MENU, omitting OMIT-ITEMS.

MENU is a list, its elements can be:

- (yas-item UUID) : Creates an entry the snippet identified with
  UUID.  The menu entry for a snippet thus identified is
  permanent, i.e. it will never move (be reordered) in the menu.

- (yas-separator) : Creates a separator

- (yas-submenu NAME SUBMENU) : Creates a submenu with NAME,
  SUBMENU has the same form as MENU.  NAME is also added to the
  list of groups of the snippets defined thereafter.

OMIT-ITEMS is a list of snippet uuid's that will always be
omitted from MODE's menu, even if they're manually loaded."
  (let* ((table (yas--table-get-create mode))
         (hash (yas--table-uuidhash table)))
    (yas--define-menu-1 table
                        (yas--menu-keymap-get-create mode)
                        menu
                        hash)
    (dolist (uuid omit-items)
      (let ((template (or (gethash uuid hash)
                          (yas--populate-template (puthash uuid
                                                           (yas--make-blank-template)
                                                           hash)
                                                  :table table
                                                  :uuid uuid))))
        (setf (yas--template-menu-binding-pair template) (cons nil :none))))))

(defun yas--define-menu-1 (table menu-keymap menu uuidhash &optional group-list)
  "Helper for `yas-define-menu'."
  (dolist (e (reverse menu))
    (cond ((eq (first e) 'yas-item)
           (let ((template (or (gethash (second e) uuidhash)
                               (yas--populate-template (puthash (second e)
                                                               (yas--make-blank-template)
                                                               uuidhash)
                                                      :table table
                                                      :perm-group group-list
                                                      :uuid (second e)))))
             (define-key menu-keymap (vector (gensym))
               (car (yas--template-menu-binding-pair-get-create template :stay)))))
          ((eq (first e) 'yas-submenu)
           (let ((subkeymap (make-sparse-keymap)))
             (define-key menu-keymap (vector (gensym))
               `(menu-item ,(second e) ,subkeymap))
             (yas--define-menu-1 table
                                subkeymap
                                (third e)
                                uuidhash
                                (append group-list (list (second e))))))
          ((eq (first e) 'yas-separator)
           (define-key menu-keymap (vector (gensym))
             '(menu-item "----")))
          (t
           (yas--message 3 "Don't know anything about menu entry %s" (first e))))))

(defun yas--define (mode key template &optional name condition group)
  "Define a snippet.  Expanding KEY into TEMPLATE.

NAME is a description to this template.  Also update the menu if
`yas-use-menu' is t.  CONDITION is the condition attached to
this snippet.  If you attach a condition to a snippet, then it
will only be expanded when the condition evaluated to non-nil."
  (yas-define-snippets mode
                       (list (list key template name condition group))))

(defun yas-hippie-try-expand (first-time?)
  "Integrate with hippie expand.

Just put this function in `hippie-expand-try-functions-list'."
  (when yas-minor-mode
    (if (not first-time?)
        (let ((yas-fallback-behavior 'return-nil))
          (yas-expand))
      (undo 1)
      nil)))


;;; Apropos condition-cache:
;;;
;;;
;;;
;;;
(defvar yas--condition-cache-timestamp nil)
(defmacro yas-define-condition-cache (func doc &rest body)
  "Define a function FUNC with doc DOC and body BODY.
BODY is executed at most once every snippet expansion attempt, to check
expansion conditions.

It doesn't make any sense to call FUNC programatically."
  `(defun ,func () ,(if (and doc
                             (stringp doc))
                        (concat doc
"\n\nFor use in snippets' conditions. Within each
snippet-expansion routine like `yas-expand', computes actual
value for the first time then always returns a cached value.")
                      (setq body (cons doc body))
                      nil)
     (let ((timestamp-and-value (get ',func 'yas--condition-cache)))
       (if (equal (car timestamp-and-value) yas--condition-cache-timestamp)
           (cdr timestamp-and-value)
         (let ((new-value (progn
                            ,@body
                            )))
           (put ',func 'yas--condition-cache (cons yas--condition-cache-timestamp new-value))
           new-value)))))

(defalias 'yas-expand 'yas-expand-from-trigger-key)
(defun yas-expand-from-trigger-key (&optional field)
  "Expand a snippet before point.

If no snippet expansion is possible, fall back to the behaviour
defined in `yas-fallback-behavior'.

Optional argument FIELD is for non-interactive use and is an
object satisfying `yas--field-p' to restrict the expansion to."
  (interactive)
  (setq yas--condition-cache-timestamp (current-time))
  (let (templates-and-pos)
    (unless (and yas-expand-only-for-last-commands
                 (not (member last-command yas-expand-only-for-last-commands)))
      (setq templates-and-pos (if field
                                  (save-restriction
                                    (narrow-to-region (yas--field-start field)
                                                      (yas--field-end field))
                                    (yas--templates-for-key-at-point))
                                (yas--templates-for-key-at-point))))
    (if templates-and-pos
        (yas--expand-or-prompt-for-template (first templates-and-pos)
                                            (second templates-and-pos)
                                            (third templates-and-pos))
      (yas--fallback))))

(defun yas-expand-from-keymap ()
  "Directly expand some snippets, searching `yas--direct-keymaps'.

If expansion fails, execute the previous binding for this key"
  (interactive)
  (setq yas--condition-cache-timestamp (current-time))
  (let* ((vec (subseq (this-command-keys-vector) (if current-prefix-arg
                                                     (length (this-command-keys))
                                                   0)))
         (templates (mapcan #'(lambda (table)
                                (yas--fetch table vec))
                            (yas--get-snippet-tables))))
    (if templates
        (yas--expand-or-prompt-for-template templates)
      (let ((yas-fallback-behavior 'call-other-command))
        (yas--fallback)))))

(defun yas--expand-or-prompt-for-template (templates &optional start end)
  "Expand one of TEMPLATES from START to END.

Prompt the user if TEMPLATES has more than one element, else
expand immediately.  Common gateway for
`yas-expand-from-trigger-key' and `yas-expand-from-keymap'."
  (let ((yas--current-template (or (and (rest templates) ;; more than one
                                        (yas--prompt-for-template (mapcar #'cdr templates)))
                                   (cdar templates))))
    (when yas--current-template
      (yas-expand-snippet (yas--template-content yas--current-template)
                          start
                          end
                          (yas--template-expand-env yas--current-template)))))

;; Apropos the trigger key and the fallback binding:
;;
;; When `yas-minor-mode-map' binds <tab>, that correctly overrides
;; org-mode's <tab>, for example and searching for fallbacks correctly
;; returns `org-cycle'. However, most other modes bind "TAB". TODO,
;; improve this explanation.
;;
(defun yas--fallback ()
  "Fallback after expansion has failed.

Common gateway for `yas-expand-from-trigger-key' and
`yas-expand-from-keymap'."
  (cond ((eq yas-fallback-behavior 'return-nil)
         ;; return nil
         nil)
        ((eq yas-fallback-behavior 'call-other-command)
         (let* ((beyond-yasnippet (yas--keybinding-beyond-yasnippet)))
           (yas--message 4 "Falling back to %s"  beyond-yasnippet)
           (assert (or (null beyond-yasnippet) (commandp beyond-yasnippet)))
           (setq this-original-command beyond-yasnippet)
           (when beyond-yasnippet
             (call-interactively beyond-yasnippet))))
        ((and (listp yas-fallback-behavior)
              (cdr yas-fallback-behavior)
              (eq 'apply (car yas-fallback-behavior)))
         (if (cddr yas-fallback-behavior)
             (apply (cadr yas-fallback-behavior)
                    (cddr yas-fallback-behavior))
           (when (commandp (cadr yas-fallback-behavior))
             (setq this-command (cadr yas-fallback-behavior))
             (call-interactively (cadr yas-fallback-behavior)))))
        (t
         ;; also return nil if all the other fallbacks have failed
         nil)))

(defun yas--keybinding-beyond-yasnippet ()
  "Return the ??"
  (let* ((yas-minor-mode nil)
         (yas--direct-keymaps nil)
         (keys (this-single-command-keys)))
    (or (key-binding keys t)
        (key-binding (yas--fallback-translate-input keys) t))))

(defun yas--fallback-translate-input (keys)
  "Emulate `read-key-sequence', at least what I think it does.

Keys should be an untranslated key vector.  Returns a translated
vector of keys.  FIXME not thoroughly tested."
  (let ((retval [])
        (i 0))
    (while (< i (length keys))
      (let ((j i)
            (translated local-function-key-map))
        (while (and (< j (length keys))
                    translated
                    (keymapp translated))
          (setq translated (cdr (assoc (aref keys j) (remove 'keymap translated)))
                j (1+ j)))
        (setq retval (vconcat retval (cond ((symbolp translated)
                                            `[,translated])
                                           ((vectorp translated)
                                            translated)
                                           (t
                                            (substring keys i j)))))
        (setq i j)))
    retval))


;;; Utils for snippet development:

(defun yas--all-templates (tables)
  "Get `yas--template' objects in TABLES, applicable for buffer and point.

Honours `yas-choose-tables-first', `yas-choose-keys-first' and
`yas-buffer-local-condition'"
  (when yas-choose-tables-first
    (setq tables (list (yas--prompt-for-table tables))))
  (mapcar #'cdr
          (if yas-choose-keys-first
              (let ((key (yas--prompt-for-keys
                          (mapcan #'yas--table-all-keys tables))))
                (when key
                  (mapcan #'(lambda (table)
                              (yas--fetch table key))
                          tables)))
            (remove-duplicates (mapcan #'yas--table-templates tables)
                               :test #'equal))))

(defun yas-insert-snippet (&optional no-condition)
  "Choose a snippet to expand, pop-up a list of choices according
to `yas-prompt-functions'.

With prefix argument NO-CONDITION, bypass filtering of snippets
by condition."
  (interactive "P")
  (setq yas--condition-cache-timestamp (current-time))
  (let* ((yas-buffer-local-condition (or (and no-condition
                                              'always)
                                         yas-buffer-local-condition))
         (templates (yas--all-templates (yas--get-snippet-tables)))
         (yas--current-template (and templates
                                    (or (and (rest templates) ;; more than one template for same key
                                             (yas--prompt-for-template templates))
                                        (car templates))))
         (where (if (region-active-p)
                    (cons (region-beginning) (region-end))
                  (cons (point) (point)))))
    (if yas--current-template
        (yas-expand-snippet (yas--template-content yas--current-template)
                            (car where)
                            (cdr where)
                            (yas--template-expand-env yas--current-template))
      (yas--message 3 "No snippets can be inserted here!"))))

(defun yas-visit-snippet-file ()
  "Choose a snippet to edit, selection like `yas-insert-snippet'.

Only success if selected snippet was loaded from a file.  Put the
visited file in `snippet-mode'."
  (interactive)
  (let* ((yas-buffer-local-condition 'always)
         (templates (yas--all-templates (yas--get-snippet-tables)))
         (yas-prompt-functions '(yas-ido-prompt yas-completing-prompt))
         (template (and templates
                        (or (yas--prompt-for-template templates
                                                     "Choose a snippet template to edit: ")
                            (car templates)))))

    (if template
        (yas--visit-snippet-file-1 template)
      (message "No snippets tables active!"))))

(defun yas--visit-snippet-file-1 (template)
  "Helper for `yas-visit-snippet-file'."
  (let ((file (yas--template-file template)))
    (cond ((and file (file-readable-p file))
           (find-file-other-window file)
           (snippet-mode)
           (set (make-local-variable 'yas--editing-template) template))
          (file
           (message "Original file %s no longer exists!" file))
          (t
           (switch-to-buffer (format "*%s*"(yas--template-name template)))
           (let ((type 'snippet))
             (when (listp (yas--template-content template))
               (insert (format "# type: command\n"))
               (setq type 'command))
             (insert (format "# key: %s\n" (yas--template-key template)))
             (insert (format "# name: %s\n" (yas--template-name template)))
             (when (yas--template-keybinding template)
               (insert (format "# binding: %s\n" (yas--template-keybinding template))))
             (when (yas--template-expand-env template)
               (insert (format "# expand-env: %s\n" (yas--template-expand-env template))))
             (when (yas--template-condition template)
               (insert (format "# condition: %s\n" (yas--template-condition template))))
             (insert "# --\n")
             (insert (if (eq type 'command)
                         (pp-to-string (yas--template-content template))
                       (yas--template-content template))))
           (snippet-mode)
           (set (make-local-variable 'yas--editing-template) template)))))

(defun yas--guess-snippet-directories-1 (table)
  "Guess possible snippet subdirectories for TABLE."
  (cons (yas--table-name table)
        (mapcan #'(lambda (parent)
                    (yas--guess-snippet-directories-1
                     parent))
                (yas--table-parents table))))

(defun yas--guess-snippet-directories (&optional table)
  "Try to guess suitable directories based on the current active
tables (or optional TABLE).

Returns a list of elements (TABLE . DIRS) where TABLE is a
`yas--table' object and DIRS is a list of all possible directories
where snippets of table might exist."
  (let ((main-dir (replace-regexp-in-string
                   "/+$" ""
                   (or (first (or (yas-snippet-dirs)
                                  (setq yas-snippet-dirs '("~/.emacs.d/snippets")))))))
        (tables (or (and table
                         (list table))
                    (yas--get-snippet-tables))))
    ;; HACK! the snippet table created here is actually registered!
    ;;
    (unless (or table (gethash major-mode yas--tables))
      (push (yas--table-get-create major-mode)
            tables))

    (mapcar #'(lambda (table)
                (cons table
                      (mapcar #'(lambda (subdir)
                                  (concat main-dir "/" subdir))
                              (yas--guess-snippet-directories-1 table))))
            tables)))

(defun yas--make-directory-maybe (table-and-dirs &optional main-table-string)
  "Return a dir inside TABLE-AND-DIRS, prompts for creation if none exists."
  (or (some #'(lambda (dir) (when (file-directory-p dir) dir)) (cdr table-and-dirs))
      (let ((candidate (first (cdr table-and-dirs))))
        (unless (file-writable-p (file-name-directory candidate))
          (error (yas--format "%s is not writable." candidate)))
        (if (y-or-n-p (format "Guessed directory (%s) for%s%s table \"%s\" does not exist! Create? "
                              candidate
                              (if (gethash (yas--table-mode (car table-and-dirs))
                                           yas--tables)
                                  ""
                                " brand new")
                              (or main-table-string
                                  "")
                              (yas--table-name (car table-and-dirs))))
            (progn
              (make-directory candidate 'also-make-parents)
              ;; create the .yas-parents file here...
              candidate)))))

(defun yas-new-snippet (&optional no-template)
  "Pops a new buffer for writing a snippet.

Expands a snippet-writing snippet, unless the optional prefix arg
NO-TEMPLATE is non-nil."
  (interactive "P")
  (let ((guessed-directories (yas--guess-snippet-directories)))

    (switch-to-buffer "*new snippet*")
    (erase-buffer)
    (kill-all-local-variables)
    (snippet-mode)
    (yas-minor-mode 1)
    (set (make-local-variable 'yas--guessed-modes) (mapcar #'(lambda (d)
                                                              (yas--table-mode (car d)))
                                                          guessed-directories))
    (if (and (not no-template) yas-new-snippet-default)
        (yas-expand-snippet yas-new-snippet-default))))

(defun yas--compute-major-mode-and-parents (file)
  "Given FILE, find the nearest snippet directory for a given mode.

Returns a list (MODE-SYM PARENTS), the mode's symbol and a list
representing one or more of the mode's parents.

Note that MODE-SYM need not be the symbol of a real major mode,
neither do the elements of PARENTS."
  (let* ((file-dir (and file
                        (directory-file-name (or (some #'(lambda (special)
                                                           (locate-dominating-file file special))
                                                       '(".yas-setup.el"
                                                         ".yas-make-groups"
                                                         ".yas-parents"))
                                                 (directory-file-name (file-name-directory file))))))
         (parents-file-name (concat file-dir "/.yas-parents"))
         (major-mode-name (and file-dir
                               (file-name-nondirectory file-dir)))
         (major-mode-sym (or (and major-mode-name
                                  (intern major-mode-name))))
         (parents (when (file-readable-p parents-file-name)
                         (mapcar #'intern
                                 (split-string
                                  (with-temp-buffer
                                    (insert-file-contents parents-file-name)
                                    (buffer-substring-no-properties (point-min)
                                                                    (point-max))))))))
    (when major-mode-sym
      (cons major-mode-sym (remove major-mode-sym parents)))))

(defvar yas--editing-template nil
  "Supporting variable for `yas-load-snippet-buffer' and `yas--visit-snippet'.")

(defvar yas--current-template nil
  "Holds the current template being expanded into a snippet.")

(defvar yas--guessed-modes nil
  "List of guessed modes supporting `yas-load-snippet-buffer'.")

(defun yas--read-table ()
  "Ask user for a snippet table, help with some guessing."
  (let ((prompt (if (and (featurep 'ido)
                         ido-mode)
                    'ido-completing-read 'completing-read)))
    (unless yas--guessed-modes
      (set (make-local-variable 'yas--guessed-modes)
           (or (yas--compute-major-mode-and-parents buffer-file-name))))
    (intern
     (funcall prompt (format "Choose or enter a table (yas guesses %s): "
                             (if yas--guessed-modes
                                 (first yas--guessed-modes)
                               "nothing"))
              (mapcar #'symbol-name yas--guessed-modes)
              nil
              nil
              nil
              nil
              (if (first yas--guessed-modes)
                  (symbol-name (first yas--guessed-modes)))))))

(defun yas-load-snippet-buffer (table &optional interactive)
  "Parse and load current buffer's snippet definition into TABLE.

TABLE is a symbol naming a passed to `yas--table-get-create'.

When called interactively, prompt for the table name."
  (interactive (list (yas--read-table) t))
  (cond
   ;;  We have `yas--editing-template', this buffer's content comes from a
   ;;  template which is already loaded and neatly positioned,...
   ;;
   (yas--editing-template
    (yas--define-snippets-1 (yas--parse-template (yas--template-file yas--editing-template))
                           (yas--template-table yas--editing-template)))
   ;; Try to use `yas--guessed-modes'. If we don't have that use the
   ;; value from `yas--compute-major-mode-and-parents'
   ;;
   (t
    (unless yas--guessed-modes
      (set (make-local-variable 'yas--guessed-modes) (or (yas--compute-major-mode-and-parents buffer-file-name))))
    (let* ((table (yas--table-get-create table)))
      (set (make-local-variable 'yas--editing-template)
           (yas--define-snippets-1 (yas--parse-template buffer-file-name)
                                  table)))))
  (when interactive
    (yas--message 3 "Snippet \"%s\" loaded for %s."
                  (yas--template-name yas--editing-template)
                  (yas--table-name (yas--template-table yas--editing-template)))))

(defun yas-load-snippet-buffer-and-close (table &optional kill)
  "Load the snippet with `yas-load-snippet-buffer', possibly
  save, then `quit-window' if saved.

If the snippet is new, ask the user whether (and where) to save
it. If the snippet already has a file, just save it.

The prefix argument KILL is passed to `quit-window'.

Don't use this from a Lisp program, call `yas-load-snippet-buffer'
and `kill-buffer' instead."
  (interactive (list (yas--read-table) current-prefix-arg))
  (yas-load-snippet-buffer table t)
  (when (and (or
              ;; Only offer to save this if it looks like a library or new
              ;; snippet (loaded from elisp, from a dir in `yas-snippet-dirs'
              ;; which is not the first, or from an unwritable file)
              ;;
              (not (yas--template-file yas--editing-template))
              (not (file-writable-p (yas--template-file yas--editing-template)))
              (and (listp yas-snippet-dirs)
                   (second yas-snippet-dirs)
                   (not (string-match (expand-file-name (first yas-snippet-dirs))
                                      (yas--template-file yas--editing-template)))))
             (y-or-n-p (yas--format "Looks like a library or new snippet. Save to new file? ")))
    (let* ((option (first (yas--guess-snippet-directories (yas--template-table yas--editing-template))))
           (chosen (and option
                        (yas--make-directory-maybe option))))
      (when chosen
        (let ((default-file-name (or (and (yas--template-file yas--editing-template)
                                          (file-name-nondirectory (yas--template-file yas--editing-template)))
                                     (yas--template-name yas--editing-template))))
          (write-file (concat chosen "/"
                              (read-from-minibuffer (format "File name to create in %s? " chosen)
                                                    default-file-name)))
          (setf (yas--template-file yas--editing-template) buffer-file-name)))))
  (when buffer-file-name
    (save-buffer)
    (quit-window kill)))

(defun yas-tryout-snippet (&optional debug)
  "Test current buffer's snippet template in other buffer."
  (interactive "P")
  (let* ((major-mode-and-parent (yas--compute-major-mode-and-parents buffer-file-name))
         (parsed (yas--parse-template))
         (test-mode (or (and (car major-mode-and-parent)
                             (fboundp (car major-mode-and-parent))
                             (car major-mode-and-parent))
                        (first yas--guessed-modes)
                        (intern (read-from-minibuffer (yas--format "Please input a mode: ")))))
         (yas--current-template
          (and parsed
               (fboundp test-mode)
               (yas--populate-template (yas--make-blank-template)
                                      :table       nil ;; no tables for ephemeral snippets
                                      :key         (first parsed)
                                      :content     (second parsed)
                                      :name        (third parsed)
                                      :expand-env  (sixth parsed)))))
    (cond (yas--current-template
           (let ((buffer-name (format "*testing snippet: %s*" (yas--template-name yas--current-template))))
             (kill-buffer (get-buffer-create buffer-name))
             (switch-to-buffer (get-buffer-create buffer-name))
             (setq buffer-undo-list nil)
             (condition-case nil (funcall test-mode) (error nil))
	     (yas-minor-mode 1)
             (setq buffer-read-only nil)
             (yas-expand-snippet (yas--template-content yas--current-template)
                                 (point-min)
                                 (point-max)
                                 (yas--template-expand-env yas--current-template))
             (when (and debug
                        (require 'yasnippet-debug nil t))
               (add-hook 'post-command-hook 'yas-debug-snippet-vars nil t))))
          (t
           (yas--message 3 "Cannot test snippet for unknown major mode")))))

(defun yas-active-keys ()
  "Return all active trigger keys for current buffer and point."
  (remove-duplicates
   (remove-if-not #'stringp (mapcan #'yas--table-all-keys (yas--get-snippet-tables)))
   :test #'string=))

(defun yas--template-fine-group (template)
  (car (last (or (yas--template-group template)
                 (yas--template-perm-group template)))))

(defun yas-describe-tables (&optional choose)
  "Display snippets for each table."
  (interactive "P")
  (let* ((by-name-hash (and choose
                            (y-or-n-p "Show by namehash? ")))
         (buffer (get-buffer-create "*YASnippet tables*"))
         (active-tables (yas--get-snippet-tables))
         (remain-tables (let ((all))
                          (maphash #'(lambda (_k v)
                                       (unless (find v active-tables)
                                         (push v all)))
                                   yas--tables)
                          all))
         (table-lists (list active-tables remain-tables))
         (original-buffer (current-buffer))
         (continue t)
         (yas--condition-cache-timestamp (current-time)))
    (with-current-buffer buffer
      (setq buffer-read-only nil)
      (erase-buffer)
      (cond ((not by-name-hash)
             (insert "YASnippet tables: \n")
             (while (and table-lists
                         continue)
               (dolist (table (car table-lists))
                 (yas--describe-pretty-table table original-buffer))
               (setq table-lists (cdr table-lists))
               (when table-lists
                 (yas--create-snippet-xrefs)
                 (display-buffer buffer)
                 (setq continue (and choose (y-or-n-p "Show also non-active tables? ")))))
             (yas--create-snippet-xrefs)
             (help-mode)
             (goto-char 1))
            (t
             (insert "\n\nYASnippet tables by NAMEHASH: \n")
             (dolist (table (append active-tables remain-tables))
               (insert (format "\nSnippet table `%s':\n\n" (yas--table-name table)))
               (let ((keys))
                 (maphash #'(lambda (k _v)
                              (push k keys))
                          (yas--table-hash table))
                 (dolist (key keys)
                   (insert (format "   key %s maps snippets: %s\n" key
                                   (let ((names))
                                     (maphash #'(lambda (k _v)
                                                  (push k names))
                                              (gethash key (yas--table-hash table)))
                                     names))))))))
      (goto-char 1)
      (setq buffer-read-only t))
    (display-buffer buffer)))

(defun yas--describe-pretty-table (table &optional original-buffer)
  (insert (format "\nSnippet table `%s'"
                  (yas--table-name table)))
  (if (yas--table-parents table)
      (insert (format " parents: %s\n"
                      (mapcar #'yas--table-name
                              (yas--table-parents table))))
    (insert "\n"))
  (insert (make-string 100 ?-) "\n")
  (insert "group                   state name                                    key             binding\n")
  (let ((groups-hash (make-hash-table :test #'equal)))
    (maphash #'(lambda (_k v)
                 (let ((group (or (yas--template-fine-group v)
                                  "(top level)")))
                   (when (yas--template-name v)
                     (puthash group
                              (cons v (gethash group groups-hash))
                              groups-hash))))
             (yas--table-uuidhash table))
    (maphash
     #'(lambda (group templates)
         (setq group (truncate-string-to-width group 25 0 ?  "..."))
         (insert (make-string 100 ?-) "\n")
         (dolist (p templates)
           (let ((name (truncate-string-to-width (propertize (format "\\\\snippet `%s'" (yas--template-name p))
                                                             'yasnippet p)
                                                 50 0 ? "..."))
                 (group (prog1 group
                          (setq group (make-string (length group) ? ))))
                 (condition-string (let ((condition (yas--template-condition p)))
                                     (if (and condition
                                              original-buffer)
                                         (with-current-buffer original-buffer
                                           (if (yas--eval-condition condition)
                                               "(y)"
                                             "(s)"))
                                       "(a)"))))
             (insert group " ")
             (insert condition-string " ")
             (insert name
                     (if (string-match "\\.\\.\\.$" name)
                         "'"
                       " ")
                     " ")
             (insert (truncate-string-to-width (or (yas--template-key p) "")
                                               15 0 ?  "...") " ")
             (insert (truncate-string-to-width (key-description (yas--template-keybinding p))
                                               15 0 ?  "...") " ")
             (insert "\n"))))
     groups-hash)))



;;; User convenience functions, for using in `yas-key-syntaxes'

(defun yas-try-key-from-whitespace (_start-point)
  "As `yas-key-syntaxes' element, look for whitespace delimited key.

A newline will be considered whitespace even if the mode syntax
marks it as something else (typically comment ender)."
  (skip-chars-backward "^[:space:]\n"))

(defun yas-shortest-key-until-whitespace (_start-point)
  "Like `yas-longest-key-from-whitespace' but take the shortest key."
  (when (/= (skip-chars-backward "^[:space:]\n" (1- (point))) 0)
    'again))

(defun yas-longest-key-from-whitespace (start-point)
  "As `yas-key-syntaxes' element, look for longest key between point and whitespace.

A newline will be considered whitespace even if the mode syntax
marks it as something else (typically comment ender)."
  (if (= (point) start-point)
      (yas-try-key-from-whitespace start-point)
    (forward-char))
  (unless (<= start-point (1+ (point)))
    'again))



;;; User convenience functions, for using in snippet definitions

(defvar yas-modified-p nil
  "Non-nil if field has been modified by user or transformation.")

(defvar yas-moving-away-p nil
  "Non-nil if user is about to exit field.")

(defvar yas-text nil
  "Contains current field text.")

(defun yas-substr (str pattern &optional subexp)
  "Search PATTERN in STR and return SUBEXPth match.

If found, the content of subexp group SUBEXP (default 0) is
  returned, or else the original STR will be returned."
  (let ((grp (or subexp 0)))
    (save-match-data
      (if (string-match pattern str)
          (match-string-no-properties grp str)
        str))))

(defun yas-choose-value (&rest possibilities)
  "Prompt for a string in POSSIBILITIES and return it.

The last element of POSSIBILITIES may be a list of strings."
  (unless (or yas-moving-away-p
              yas-modified-p)
    (let* ((last-link (last possibilities))
           (last-elem (car last-link)))
      (when (listp last-elem)
        (setcar last-link (car last-elem))
        (setcdr last-link (cdr last-elem))))
    (some #'(lambda (fn)
              (funcall fn "Choose: " possibilities))
          yas-prompt-functions)))

(defun yas-key-to-value (alist)
  (unless (or yas-moving-away-p
              yas-modified-p)
    (let ((key (read-key-sequence "")))
      (when (stringp key)
        (or (cdr (find key alist :key #'car :test #'string=))
            key)))))

(defun yas-throw (text)
  "Throw a yas--exception with TEXT as the reason."
  (throw 'yas--exception (cons 'yas--exception text)))

(defun yas-verify-value (possibilities)
  "Verify that the current field value is in POSSIBILITIES.

Otherwise throw exception."
  (when (and yas-moving-away-p (notany #'(lambda (pos) (string= pos yas-text)) possibilities))
    (yas-throw (yas--format "Field only allows %s" possibilities))))

(defun yas-field-value (number)
  "Get the string for field with NUMBER.

Use this in primary and mirror transformations to tget."
  (let* ((snippet (car (yas--snippets-at-point)))
         (field (and snippet
                     (yas--snippet-find-field snippet number))))
    (when field
      (yas--field-text-for-display field))))

(defun yas-text ()
  "Return `yas-text' if that exists and is non-empty, else nil."
  (if (and yas-text
           (not (string= "" yas-text)))
      yas-text))

(defun yas-selected-text ()
  "Return `yas-selected-text' if that exists and is non-empty, else nil."
  (if (and yas-selected-text
           (not (string= "" yas-selected-text)))
      yas-selected-text))

(defun yas--get-field-once (number &optional transform-fn)
  (unless yas-modified-p
    (if transform-fn
        (funcall transform-fn (yas-field-value number))
      (yas-field-value number))))

(defun yas-default-from-field (number)
  (unless yas-modified-p
    (yas-field-value number)))

(defun yas-inside-string ()
  "Return non-nil if the point is inside a string according to font-lock."
  (equal 'font-lock-string-face (get-char-property (1- (point)) 'face)))

(defun yas-unimplemented (&optional missing-feature)
  (if yas--current-template
      (if (y-or-n-p (format "This snippet is unimplemented (missing %s) Visit the snippet definition? "
                            (or missing-feature
                                "something")))
          (yas--visit-snippet-file-1 yas--current-template))
    (message "No implementation. Missing %s" (or missing-feature "something"))))


;;; Snippet expansion and field management

(defvar yas--active-field-overlay nil
  "Overlays the currently active field.")

(defvar yas--field-protection-overlays nil
  "Two overlays protect the current active field.")

(defvar yas-selected-text nil
  "The selected region deleted on the last snippet expansion.")

(defvar yas--start-column nil
  "The column where the snippet expansion started.")

(make-variable-buffer-local 'yas--active-field-overlay)
(make-variable-buffer-local 'yas--field-protection-overlays)
(put 'yas--active-field-overlay 'permanent-local t)
(put 'yas--field-protection-overlays 'permanent-local t)

(defstruct (yas--snippet (:constructor yas--make-snippet ()))
  "A snippet.

..."
  (fields '())
  (exit nil)
  (id (yas--snippet-next-id) :read-only t)
  (control-overlay nil)
  active-field
  ;; stacked expansion: the `previous-active-field' slot saves the
  ;; active field where the child expansion took place
  previous-active-field
  force-exit)

(defstruct (yas--field (:constructor yas--make-field (number start end parent-field)))
  "A field.

NUMBER is the field number.
START and END are mostly buffer markers, but see \"apropos markers-to-points\".
PARENT-FIELD is a `yas--field' this field is nested under, or nil.
MIRRORS is a list of `yas--mirror's
TRANSFORM is a lisp form.
MODIFIED-P is a boolean set to true once user inputs text.
NEXT is another `yas--field' or `yas--mirror' or `yas--exit'.
"
  number
  start end
  parent-field
  (mirrors '())
  (transform nil)
  (modified-p nil)
  next)


(defstruct (yas--mirror (:constructor yas--make-mirror (start end transform)))
  "A mirror.

START and END are mostly buffer markers, but see \"apropos markers-to-points\".
TRANSFORM is a lisp form.
PARENT-FIELD is a `yas--field' this mirror is nested under, or nil.
NEXT is another `yas--field' or `yas--mirror' or `yas--exit'
DEPTH is a count of how many nested mirrors can affect this mirror"
  start end
  (transform nil)
  parent-field
  next
  depth)

(defstruct (yas--exit (:constructor yas--make-exit (marker)))
  marker
  next)

(defun yas--apply-transform (field-or-mirror field &optional empty-on-nil-p)
  "Calculate transformed string for FIELD-OR-MIRROR from FIELD.

If there is no transform for ht field, return nil.

If there is a transform but it returns nil, return the empty
string iff EMPTY-ON-NIL-P is true."
  (let* ((yas-text (yas--field-text-for-display field))
         (yas-modified-p (yas--field-modified-p field))
         (yas-moving-away-p nil)
         (transform (if (yas--mirror-p field-or-mirror)
                        (yas--mirror-transform field-or-mirror)
                      (yas--field-transform field-or-mirror)))
         (start-point (if (yas--mirror-p field-or-mirror)
                          (yas--mirror-start field-or-mirror)
                        (yas--field-start field-or-mirror)))
         (transformed (and transform
                           (save-excursion
                             (goto-char start-point)
                             (let ((ret (yas--eval-lisp transform)))
                               (or ret (and empty-on-nil-p "")))))))
    transformed))

(defsubst yas--replace-all (from to &optional text)
  "Replace all occurrences from FROM to TO.

With optional string TEXT do it in that string."
  (if text
      (replace-regexp-in-string (regexp-quote from) to text t t)
    (goto-char (point-min))
    (while (search-forward from nil t)
      (replace-match to t t text))))

(defun yas--snippet-find-field (snippet number)
  (find-if #'(lambda (field)
               (eq number (yas--field-number field)))
           (yas--snippet-fields snippet)))

(defun yas--snippet-sort-fields (snippet)
  "Sort the fields of SNIPPET in navigation order."
  (setf (yas--snippet-fields snippet)
        (sort (yas--snippet-fields snippet)
              #'yas--snippet-field-compare)))

(defun yas--snippet-field-compare (field1 field2)
  "Compare FIELD1 and FIELD2.

The field with a number is sorted first.  If they both have a
number, compare through the number.  If neither have, compare
through the field's start point"
  (let ((n1 (yas--field-number field1))
        (n2 (yas--field-number field2)))
    (if n1
        (if n2
            (or (zerop n2) (and (not (zerop n1))
                                (< n1 n2)))
          (not (zerop n1)))
      (if n2
          (zerop n2)
        (< (yas--field-start field1)
           (yas--field-start field2))))))

(defun yas--field-probably-deleted-p (snippet field)
  "Guess if SNIPPET's FIELD should be skipped."
  (and
   ;; field must be zero length
   ;;
   (zerop (- (yas--field-start field) (yas--field-end field)))
   ;; skip if:
   (or
    ;;  1) is a nested field and it's been modified
    ;;
    (and (yas--field-parent-field field)
         (yas--field-modified-p field))
    ;;  2) ends just before the snippet end
    ;;
    (and (eq field (car (last (yas--snippet-fields snippet))))
         (= (yas--field-start field) (overlay-end (yas--snippet-control-overlay snippet)))))
   ;; the field numbered 0, just before the exit marker, should
   ;; never be skipped
   ;;
   (not (zerop (yas--field-number field)))))

(defun yas--snippets-at-point (&optional all-snippets)
  "Return a sorted list of snippets at point.

The most recently-inserted snippets are returned first."
  (sort
   (remove nil (remove-duplicates (mapcar #'(lambda (ov)
                                              (overlay-get ov 'yas--snippet))
                                          (if all-snippets
                                              (overlays-in (point-min) (point-max))
                                            (nconc (overlays-at (point)) (overlays-at (1- (point))))))))
   #'(lambda (s1 s2)
       (<= (yas--snippet-id s2) (yas--snippet-id s1)))))

(defun yas-next-field-or-maybe-expand ()
  "Try to expand a snippet at a key before point.

Otherwise delegate to `yas-next-field'."
  (interactive)
  (if yas-triggers-in-field
      (let ((yas-fallback-behavior 'return-nil)
            (active-field (overlay-get yas--active-field-overlay 'yas--field)))
        (when active-field
          (unless (yas-expand-from-trigger-key active-field)
            (yas-next-field))))
    (yas-next-field)))

(defun yas-next-field (&optional arg)
  "Navigate to the ARGth next field.

If there's none, exit the snippet."
  (interactive)
  (let* ((arg (or arg
                  1))
         (snippet (first (yas--snippets-at-point)))
         (active-field (overlay-get yas--active-field-overlay 'yas--field))
         (live-fields (remove-if #'(lambda (field)
                                     (and (not (eq field active-field))
                                          (yas--field-probably-deleted-p snippet field)))
                                 (yas--snippet-fields snippet)))
         (active-field-pos (position active-field live-fields))
         (target-pos (and active-field-pos (+ arg active-field-pos)))
         (target-field (and target-pos (nth target-pos live-fields))))
    ;; First check if we're moving out of a field with a transform
    ;;
    (when (and active-field
               (yas--field-transform active-field))
      (let* ((yas-moving-away-p t)
             (yas-text (yas--field-text-for-display active-field))
             (yas-modified-p (yas--field-modified-p active-field)))
        ;; primary field transform: exit call to field-transform
        (yas--eval-lisp (yas--field-transform active-field))))
    ;; Now actually move...
    (cond ((and target-pos (>= target-pos (length live-fields)))
           (yas-exit-snippet snippet))
          (target-field
           (yas--move-to-field snippet target-field))
          (t
           nil))))

(defun yas--place-overlays (snippet field)
  "Correctly place overlays for SNIPPET's FIELD."
  (yas--make-move-field-protection-overlays snippet field)
  (yas--make-move-active-field-overlay snippet field))

(defun yas--move-to-field (snippet field)
  "Update SNIPPET to move to field FIELD.

Also create some protection overlays"
  (goto-char (yas--field-start field))
  (yas--place-overlays snippet field)
  (overlay-put yas--active-field-overlay 'yas--field field)
  (let ((number (yas--field-number field)))
    ;; check for the special ${0: ...} field
    (if (and number (zerop number))
        (progn
          (set-mark (yas--field-end field))
          (setf (yas--snippet-force-exit snippet)
                (or (yas--field-transform field)
                    t)))
      ;; make this field active
      (setf (yas--snippet-active-field snippet) field)
      ;; primary field transform: first call to snippet transform
      (unless (yas--field-modified-p field)
        (if (yas--field-update-display field)
            (yas--update-mirrors snippet)
          (setf (yas--field-modified-p field) nil))))))

(defun yas-prev-field ()
  "Navigate to prev field.  If there's none, exit the snippet."
  (interactive)
  (yas-next-field -1))

(defun yas-abort-snippet (&optional snippet)
  (interactive)
  (let ((snippet (or snippet
                     (car (yas--snippets-at-point)))))
    (when snippet
      (setf (yas--snippet-force-exit snippet) t))))

(defun yas-exit-snippet (snippet)
  "Goto exit-marker of SNIPPET."
  (interactive (list (first (yas--snippets-at-point))))
  (when snippet
    (setf (yas--snippet-force-exit snippet) t)
    (goto-char (if (yas--snippet-exit snippet)
                   (yas--exit-marker (yas--snippet-exit snippet))
                 (overlay-end (yas--snippet-control-overlay snippet))))))

(defun yas-exit-all-snippets ()
  "Exit all snippets."
  (interactive)
  (mapc #'(lambda (snippet)
            (yas-exit-snippet snippet)
            (yas--check-commit-snippet))
        (yas--snippets-at-point 'all-snippets)))


;;; Some low level snippet-routines:

(defvar yas--inhibit-overlay-hooks nil
  "Bind this temporarily to non-nil to prevent running `yas--on-*-modification'.")

(defmacro yas--inhibit-overlay-hooks (&rest body)
  "Run BODY with `yas--inhibit-overlay-hooks' set to t."
  (declare (indent 0))
  `(let ((yas--inhibit-overlay-hooks t))
     ,@body))

(defvar yas-snippet-beg nil "Beginning position of the last snippet committed.")
(defvar yas-snippet-end nil "End position of the last snippet committed.")

(defun yas--commit-snippet (snippet)
  "Commit SNIPPET, but leave point as it is.

This renders the snippet as ordinary text."

  (let ((control-overlay (yas--snippet-control-overlay snippet)))
    ;;
    ;; Save the end of the moribund snippet in case we need to revive it
    ;; its original expansion.
    ;;
    (when (and control-overlay
               (overlay-buffer control-overlay))
      (setq yas-snippet-beg (overlay-start control-overlay))
      (setq yas-snippet-end (overlay-end control-overlay))
      (delete-overlay control-overlay))

    (yas--inhibit-overlay-hooks
      (when yas--active-field-overlay
        (delete-overlay yas--active-field-overlay))
      (when yas--field-protection-overlays
        (mapc #'delete-overlay yas--field-protection-overlays)))

    ;; stacked expansion: if the original expansion took place from a
    ;; field, make sure we advance it here at least to
    ;; `yas-snippet-end'...
    ;;
    (let ((previous-field (yas--snippet-previous-active-field snippet)))
      (when (and yas-snippet-end previous-field)
        (yas--advance-end-maybe previous-field yas-snippet-end)))

    ;; Convert all markers to points,
    ;;
    (yas--markers-to-points snippet)

    ;; Take care of snippet revival
    ;;
    (if yas-snippet-revival
        (push `(apply yas--snippet-revive ,yas-snippet-beg ,yas-snippet-end ,snippet)
              buffer-undo-list)
      ;; Dismember the snippet... this is useful if we get called
      ;; again from `yas--take-care-of-redo'....
      (setf (yas--snippet-fields snippet) nil)))

  (yas--message 3 "Snippet %s exited." (yas--snippet-id snippet)))

(defun yas--safely-run-hooks (hook-var)
  (condition-case error
      (run-hooks hook-var)
    (error
     (yas--message 3 "%s error: %s" hook-var (error-message-string error)))))


(defun yas--check-commit-snippet ()
  "Check if point exited the currently active field of the snippet.

If so cleans up the whole snippet up."
  (let* ((snippets (yas--snippets-at-point 'all-snippets))
         (snippets-left snippets)
         (snippet-exit-transform))
    (dolist (snippet snippets)
      (let ((active-field (yas--snippet-active-field snippet)))
        (setq snippet-exit-transform (yas--snippet-force-exit snippet))
        (cond ((or snippet-exit-transform
                   (not (and active-field (yas--field-contains-point-p active-field))))
               (setq snippets-left (delete snippet snippets-left))
               (setf (yas--snippet-force-exit snippet) nil)
               (yas--commit-snippet snippet))
              ((and active-field
                    (or (not yas--active-field-overlay)
                        (not (overlay-buffer yas--active-field-overlay))))
               ;;
               ;; stacked expansion: this case is mainly for recent
               ;; snippet exits that place us back int the field of
               ;; another snippet
               ;;
               (save-excursion
                 (yas--move-to-field snippet active-field)
                 (yas--update-mirrors snippet)))
              (t
               nil))))
    (unless (or (null snippets) snippets-left)
      (if snippet-exit-transform
          (yas--eval-lisp-no-saves snippet-exit-transform))
      (yas--safely-run-hooks 'yas-after-exit-snippet-hook))))

;; Apropos markers-to-points:
;;
;; This was found useful for performance reasons, so that an
;; excessive number of live markers aren't kept around in the
;; `buffer-undo-list'. However, in `markers-to-points', the
;; set-to-nil markers can't simply be discarded and replaced with
;; fresh ones in `points-to-markers'. The original marker that was
;; just set to nil has to be reused.
;;
;; This shouldn't bring horrible problems with undo/redo, but it
;; you never know
;;
(defun yas--markers-to-points (snippet)
  "Convert all markers in SNIPPET to a cons (POINT . MARKER)
where POINT is the original position of the marker and MARKER is
the original marker object with the position set to nil."
  (dolist (field (yas--snippet-fields snippet))
    (let ((start (marker-position (yas--field-start field)))
          (end (marker-position (yas--field-end field))))
      (set-marker (yas--field-start field) nil)
      (set-marker (yas--field-end field) nil)
      (setf (yas--field-start field) (cons start (yas--field-start field)))
      (setf (yas--field-end field) (cons end (yas--field-end field))))
    (dolist (mirror (yas--field-mirrors field))
      (let ((start (marker-position (yas--mirror-start mirror)))
            (end (marker-position (yas--mirror-end mirror))))
        (set-marker (yas--mirror-start mirror) nil)
        (set-marker (yas--mirror-end mirror) nil)
        (setf (yas--mirror-start mirror) (cons start (yas--mirror-start mirror)))
        (setf (yas--mirror-end mirror) (cons end (yas--mirror-end mirror))))))
  (let ((snippet-exit (yas--snippet-exit snippet)))
    (when snippet-exit
      (let ((exit (marker-position (yas--exit-marker snippet-exit))))
        (set-marker (yas--exit-marker snippet-exit) nil)
        (setf (yas--exit-marker snippet-exit) (cons exit (yas--exit-marker snippet-exit)))))))

(defun yas--points-to-markers (snippet)
  "Convert all cons (POINT . MARKER) in SNIPPET to markers.

This is done by setting MARKER to POINT with `set-marker'."
  (dolist (field (yas--snippet-fields snippet))
    (setf (yas--field-start field) (set-marker (cdr (yas--field-start field))
                                              (car (yas--field-start field))))
    (setf (yas--field-end field) (set-marker (cdr (yas--field-end field))
                                            (car (yas--field-end field))))
    (dolist (mirror (yas--field-mirrors field))
      (setf (yas--mirror-start mirror) (set-marker (cdr (yas--mirror-start mirror))
                                                  (car (yas--mirror-start mirror))))
      (setf (yas--mirror-end mirror) (set-marker (cdr (yas--mirror-end mirror))
                                                (car (yas--mirror-end mirror))))))
  (let ((snippet-exit (yas--snippet-exit snippet)))
    (when snippet-exit
      (setf (yas--exit-marker snippet-exit) (set-marker (cdr (yas--exit-marker snippet-exit))
                                                       (car (yas--exit-marker snippet-exit)))))))

(defun yas--field-contains-point-p (field &optional point)
  (let ((point (or point
                   (point))))
    (and (>= point (yas--field-start field))
         (<= point (yas--field-end field)))))

(defun yas--field-text-for-display (field)
  "Return the propertized display text for field FIELD."
  (buffer-substring (yas--field-start field) (yas--field-end field)))

(defun yas--undo-in-progress ()
  "True if some kind of undo is in progress."
  (or undo-in-progress
      (eq this-command 'undo)
      (eq this-command 'redo)))

(defun yas--make-control-overlay (snippet start end)
  "Create the control overlay that surrounds the snippet and
holds the keymap."
  (let ((overlay (make-overlay start
                               end
                               nil
                               nil
                               t)))
    (overlay-put overlay 'keymap yas-keymap)
    (overlay-put overlay 'priority 100)
    (overlay-put overlay 'yas--snippet snippet)
    overlay))

(defun yas-skip-and-clear-or-delete-char (&optional field)
  "Clears unmodified field if at field start, skips to next tab.

Otherwise deletes a character normally by calling `delete-char'."
  (interactive)
  (let ((field (or field
                   (and yas--active-field-overlay
                        (overlay-buffer yas--active-field-overlay)
                        (overlay-get yas--active-field-overlay 'yas--field)))))
    (cond ((and field
                (not (yas--field-modified-p field))
                (eq (point) (marker-position (yas--field-start field))))
           (yas--skip-and-clear field)
           (yas-next-field 1))
          (t
           (call-interactively 'delete-char)))))

(defun yas--skip-and-clear (field)
  "Deletes the region of FIELD and sets it's modified state to t."
  ;; Just before skipping-and-clearing the field, mark its children
  ;; fields as modified, too. If the children have mirrors-in-fields
  ;; this prevents them from updating erroneously (we're skipping and
  ;; deleting!).
  ;;
  (yas--mark-this-and-children-modified field)
  (delete-region (yas--field-start field) (yas--field-end field)))

(defun yas--mark-this-and-children-modified (field)
  (setf (yas--field-modified-p field) t)
  (let ((fom (yas--field-next field)))
    (while (and fom
                (yas--fom-parent-field fom))
      (when (and (eq (yas--fom-parent-field fom) field)
                 (yas--field-p fom))
        (yas--mark-this-and-children-modified fom))
      (setq fom (yas--fom-next fom)))))

(defun yas--make-move-active-field-overlay (snippet field)
  "Place the active field overlay in SNIPPET's FIELD.

Move the overlay, or create it if it does not exit."
  (if (and yas--active-field-overlay
           (overlay-buffer yas--active-field-overlay))
      (move-overlay yas--active-field-overlay
                    (yas--field-start field)
                    (yas--field-end field))
    (setq yas--active-field-overlay
          (make-overlay (yas--field-start field)
                        (yas--field-end field)
                        nil nil t))
    (overlay-put yas--active-field-overlay 'priority 100)
    (overlay-put yas--active-field-overlay 'face 'yas-field-highlight-face)
    (overlay-put yas--active-field-overlay 'yas--snippet snippet)
    (overlay-put yas--active-field-overlay 'modification-hooks '(yas--on-field-overlay-modification))
    (overlay-put yas--active-field-overlay 'insert-in-front-hooks
                 '(yas--on-field-overlay-modification))
    (overlay-put yas--active-field-overlay 'insert-behind-hooks
                 '(yas--on-field-overlay-modification))))

(defun yas--on-field-overlay-modification (overlay after? _beg _end &optional _length)
  "Clears the field and updates mirrors, conditionally.

Only clears the field if it hasn't been modified and it point it
at field start.  This hook doesn't do anything if an undo is in
progress."
  (unless (or yas--inhibit-overlay-hooks
              (yas--undo-in-progress))
    (let* ((field (overlay-get overlay 'yas--field))
           (snippet (overlay-get yas--active-field-overlay 'yas--snippet)))
      (cond (after?
             (yas--advance-end-maybe field (overlay-end overlay))
             (save-excursion
               (yas--field-update-display field))
             (yas--update-mirrors snippet))
            (field
             (when (and (not after?)
                        (not (yas--field-modified-p field))
                        (eq (point) (if (markerp (yas--field-start field))
                                        (marker-position (yas--field-start field))
                                      (yas--field-start field))))
               (yas--skip-and-clear field))
             (setf (yas--field-modified-p field) t))))))

;;; Apropos protection overlays:
;;
;; These exist for nasty users who will try to delete parts of the
;; snippet outside the active field. Actual protection happens in
;; `yas--on-protection-overlay-modification'.
;;
;; Currently this signals an error which inhibits the command. For
;; commands that move point (like `kill-line'), point is restored in
;; the `yas--post-command-handler' using a global
;; `yas--protection-violation' variable.
;;
;; Alternatively, I've experimented with an implementation that
;; commits the snippet before actually calling `this-command'
;; interactively, and then signals an error, which is ignored. but
;; blocks all other million modification hooks. This presented some
;; problems with stacked expansion.
;;
(defun yas--make-move-field-protection-overlays (snippet field)
  "Place protection overlays surrounding SNIPPET's FIELD.

Move the overlays, or create them if they do not exit."
  (let ((start (yas--field-start field))
        (end (yas--field-end field)))
    ;; First check if the (1+ end) is contained in the buffer,
    ;; otherwise we'll have to do a bit of cheating and silently
    ;; insert a newline. the `(1+ (buffer-size))' should prevent this
    ;; when using stacked expansion
    ;;
    (when (< (buffer-size) end)
      (save-excursion
        (yas--inhibit-overlay-hooks
          (goto-char (point-max))
          (newline))))
    ;; go on to normal overlay creation/moving
    ;;
    (cond ((and yas--field-protection-overlays
                (every #'overlay-buffer yas--field-protection-overlays))
           (move-overlay (first yas--field-protection-overlays) (1- start) start)
           (move-overlay (second yas--field-protection-overlays) end (1+ end)))
          (t
           (setq yas--field-protection-overlays
                 (list (make-overlay (1- start) start nil t nil)
                       (make-overlay end (1+ end) nil t nil)))
           (dolist (ov yas--field-protection-overlays)
             (overlay-put ov 'face 'yas--field-debug-face)
             (overlay-put ov 'yas--snippet snippet)
             ;; (overlay-put ov 'evaporate t)
             (overlay-put ov 'modification-hooks '(yas--on-protection-overlay-modification)))))))

(defvar yas--protection-violation nil
  "When non-nil, signals attempts to erroneously exit or modify the snippet.

Functions in the `post-command-hook', for example
`yas--post-command-handler' can check it and reset its value to
nil.  The variables value is the point where the violation
originated")

(defun yas--on-protection-overlay-modification (_overlay after? _beg _end &optional _length)
  "Signals a snippet violation, then issues error.

The error should be ignored in `debug-ignored-errors'"
  (unless yas--inhibit-overlay-hooks
    (cond ((not (or after?
                    (yas--undo-in-progress)))
           (setq yas--protection-violation (point))
           (error "Exit the snippet first!")))))

(add-to-list 'debug-ignored-errors "^Exit the snippet first!$")


;;; Snippet expansion and "stacked" expansion:
;;
;; Stacked expansion is when you try to expand a snippet when already
;; inside a snippet expansion.
;;
;; The parent snippet does not run its fields modification hooks
;; (`yas--on-field-overlay-modification' and
;; `yas--on-protection-overlay-modification') while the child snippet
;; is active. This means, among other things, that the mirrors of the
;; parent snippet are not updated, this only happening when one exits
;; the child snippet.
;;
;; Unfortunately, this also puts some ugly (and not fully-tested)
;; bits of code in `yas-expand-snippet' and
;; `yas--commit-snippet'. I've tried to mark them with "stacked
;; expansion:".
;;
;; This was thought to be safer in an undo/redo perspective, but
;; maybe the correct implementation is to make the globals
;; `yas--active-field-overlay' and `yas--field-protection-overlays' be
;; snippet-local and be active even while the child snippet is
;; running. This would mean a lot of overlay modification hooks
;; running, but if managed correctly (including overlay priorities)
;; they should account for all situations...
;;
(defun yas-expand-snippet (content &optional start end expand-env)
  "Expand snippet CONTENT at current point.

Text between START and END will be deleted before inserting
template.  EXPAND-ENV is are let-style variable to value bindings
considered when expanding the snippet."
  (run-hooks 'yas-before-expand-snippet-hook)

  ;;
  (let* ((yas-selected-text (or yas-selected-text
                                (and (region-active-p)
                                     (buffer-substring-no-properties (region-beginning)
                                                                     (region-end)))))
         (start (or start
                    (and (region-active-p)
                         (region-beginning))
                    (point)))
         (end (or end
                  (and (region-active-p)
                       (region-end))
                  (point)))
         (to-delete (and start
                         end
                         (buffer-substring-no-properties start end)))
         snippet)
    (goto-char start)
    (setq yas--indent-original-column (current-column))
    ;; Delete the region to delete, this *does* get undo-recorded.
    ;;
    (when (and to-delete
               (> end start))
      (delete-region start end))

    (cond ((listp content)
           ;; x) This is a snippet-command
           ;;
           (yas--eval-lisp-no-saves content))
          (t
           ;; x) This is a snippet-snippet :-)
           ;;
           ;;    Narrow the region down to the content, shoosh the
           ;;    `buffer-undo-list', and create the snippet, the new
           ;;    snippet updates its mirrors once, so we are left with
           ;;    some plain text.  The undo action for deleting this
           ;;    plain text will get recorded at the end.
           ;;
           ;;    stacked expansion: also shoosh the overlay modification hooks
           (let ((buffer-undo-list t))
             ;; snippet creation might evaluate users elisp, which
             ;; might generate errors, so we have to be ready to catch
             ;; them mostly to make the undo information
             ;;
             (setq yas--start-column (current-column))
             (yas--inhibit-overlay-hooks
               (setq snippet
                     (if expand-env
                         (eval `(let* ,expand-env
                                  (insert content)
                                  (yas--snippet-create start (point))))
                       (insert content)
                       (yas--snippet-create start (point))))))

           ;; stacked-expansion: This checks for stacked expansion, save the
           ;; `yas--previous-active-field' and advance its boundary.
           ;;
           (let ((existing-field (and yas--active-field-overlay
                                      (overlay-buffer yas--active-field-overlay)
                                      (overlay-get yas--active-field-overlay 'yas--field))))
             (when existing-field
               (setf (yas--snippet-previous-active-field snippet) existing-field)
               (yas--advance-end-maybe existing-field (overlay-end yas--active-field-overlay))))

           ;; Exit the snippet immediately if no fields
           ;;
           (unless (yas--snippet-fields snippet)
             (yas-exit-snippet snippet))

           ;; Push two undo actions: the deletion of the inserted contents of
           ;; the new snippet (without the "key") followed by an apply of
           ;; `yas--take-care-of-redo' on the newly inserted snippet boundaries
           ;;
           ;; A small exception, if `yas-also-auto-indent-first-line'
           ;; is t and `yas--indent' decides to indent the line to a
           ;; point before the actual expansion point, undo would be
           ;; messed up. We call the early point "newstart"".  case,
           ;; and attempt to fix undo.
           ;;
           (let ((newstart (overlay-start (yas--snippet-control-overlay snippet)))
                 (end (overlay-end (yas--snippet-control-overlay snippet))))
             (when (< newstart start)
               (push (cons (make-string (- start newstart) ? ) newstart) buffer-undo-list))
             (push (cons newstart end) buffer-undo-list)
             (push `(apply yas--take-care-of-redo ,start ,end ,snippet)
                   buffer-undo-list))
           ;; Now, schedule a move to the first field
           ;;
           (let ((first-field (car (yas--snippet-fields snippet))))
             (when first-field
               (sit-for 0) ;; fix issue 125
               (yas--move-to-field snippet first-field)))
           (yas--message 3 "snippet expanded.")
           t))))

(defun yas--take-care-of-redo (_beg _end snippet)
  "Commits SNIPPET, which in turn pushes an undo action for reviving it.

Meant to exit in the `buffer-undo-list'."
  ;; slightly optimize: this action is only needed for snippets with
  ;; at least one field
  (when (yas--snippet-fields snippet)
    (yas--commit-snippet snippet)))

(defun yas--snippet-revive (beg end snippet)
  "Revives SNIPPET and creates a control overlay from BEG to END.

BEG and END are, we hope, the original snippets boundaries.
All the markers/points exiting existing inside SNIPPET should point
to their correct locations *at the time the snippet is revived*.

After revival, push the `yas--take-care-of-redo' in the
`buffer-undo-list'"
  ;; Reconvert all the points to markers
  ;;
  (yas--points-to-markers snippet)
  ;; When at least one editable field existed in the zombie snippet,
  ;; try to revive the whole thing...
  ;;
  (let ((target-field (or (yas--snippet-active-field snippet)
                          (car (yas--snippet-fields snippet)))))
    (when target-field
      (setf (yas--snippet-control-overlay snippet) (yas--make-control-overlay snippet beg end))
      (overlay-put (yas--snippet-control-overlay snippet) 'yas--snippet snippet)

      (yas--move-to-field snippet target-field)

      (push `(apply yas--take-care-of-redo ,beg ,end ,snippet)
            buffer-undo-list))))

(defun yas--snippet-create (begin end)
  "Create a snippet from a template inserted at BEGIN to END.

Returns the newly created snippet."
  (save-restriction
    (narrow-to-region begin end)
    (let ((snippet (yas--make-snippet)))
      (goto-char begin)
      (yas--snippet-parse-create snippet)

      ;; Sort and link each field
      (yas--snippet-sort-fields snippet)

      ;; Create keymap overlay for snippet
      (setf (yas--snippet-control-overlay snippet)
            (yas--make-control-overlay snippet (point-min) (point-max)))

      ;; Move to end
      (goto-char (point-max))

      snippet)))


;;; Apropos adjacencies and "fom's":
;;
;; Once the $-constructs bits like "$n" and "${:n" are deleted in the
;; recently expanded snippet, we might actually have many fields,
;; mirrors (and the snippet exit) in the very same position in the
;; buffer. Therefore we need to single-link the
;; fields-or-mirrors-or-exit (which I have abbreviated to "fom")
;; according to their original positions in the buffer.
;;
;; Then we have operation `yas--advance-end-maybe' and
;; `yas--advance-start-maybe', which conditionally push the starts and
;; ends of these foms down the chain.
;;
;; This allows for like the printf with the magic ",":
;;
;;   printf ("${1:%s}\\n"${1:$(if (string-match "%" text) "," "\);")}  \
;;   $2${1:$(if (string-match "%" text) "\);" "")}$0
;;
(defun yas--fom-start (fom)
  (cond ((yas--field-p fom)
         (yas--field-start fom))
        ((yas--mirror-p fom)
         (yas--mirror-start fom))
        (t
         (yas--exit-marker fom))))

(defun yas--fom-end (fom)
  (cond ((yas--field-p fom)
         (yas--field-end fom))
        ((yas--mirror-p fom)
         (yas--mirror-end fom))
        (t
         (yas--exit-marker fom))))

(defun yas--fom-next (fom)
  (cond ((yas--field-p fom)
         (yas--field-next fom))
        ((yas--mirror-p fom)
         (yas--mirror-next fom))
        (t
         (yas--exit-next fom))))

(defun yas--fom-parent-field (fom)
  (cond ((yas--field-p fom)
         (yas--field-parent-field fom))
        ((yas--mirror-p fom)
         (yas--mirror-parent-field fom))
        (t
         nil)))

(defun yas--calculate-adjacencies (snippet)
  "Calculate adjacencies for fields or mirrors of SNIPPET.

This is according to their relative positions in the buffer, and
has to be called before the $-constructs are deleted."
  (let* ((fom-set-next-fom
         (lambda (fom nextfom)
           (cond ((yas--field-p fom)
                  (setf (yas--field-next fom) nextfom))
                 ((yas--mirror-p fom)
                  (setf (yas--mirror-next fom) nextfom))
                 (t
                  (setf (yas--exit-next fom) nextfom)))))
        (compare-fom-begs
         (lambda (fom1 fom2)
           (if (= (yas--fom-start fom2) (yas--fom-start fom1))
               (yas--mirror-p fom2)
             (>= (yas--fom-start fom2) (yas--fom-start fom1)))))
        (link-foms fom-set-next-fom))
    ;; make some yas--field, yas--mirror and yas--exit soup
    (let ((soup))
      (when (yas--snippet-exit snippet)
        (push (yas--snippet-exit snippet) soup))
      (dolist (field (yas--snippet-fields snippet))
        (push field soup)
        (dolist (mirror (yas--field-mirrors field))
          (push mirror soup)))
      (setq soup
            (sort soup compare-fom-begs))
      (when soup
        (reduce link-foms soup)))))

(defun yas--calculate-mirrors-in-fields (snippet mirror)
  "Attempt to assign a parent field of SNIPPET to the mirror MIRROR.

Use the tightest containing field if more than one field contains
the mirror.  Intended to be called *before* the dollar-regions are
deleted."
  (let ((min (point-min))
        (max (point-max)))
    (dolist (field (yas--snippet-fields snippet))
      (when (and (<= (yas--field-start field) (yas--mirror-start mirror))
                 (<= (yas--mirror-end mirror) (yas--field-end field))
               (< min (yas--field-start field))
               (< (yas--field-end field) max))
          (setq min (yas--field-start field)
                max (yas--field-end field))
          (setf (yas--mirror-parent-field mirror) field)))))

(defun yas--advance-end-maybe (fom newend)
  "Maybe advance FOM's end to NEWEND if it needs it.

If it does, also:

* call `yas--advance-start-maybe' on FOM's next fom.

* in case FOM is field call `yas--advance-end-maybe' on its parent
  field

Also, if FOM is an exit-marker, always call
`yas--advance-start-maybe' on its next fom.  This is because
exit-marker have identical start and end markers."
  (cond ((and fom (< (yas--fom-end fom) newend))
         (set-marker (yas--fom-end fom) newend)
         (yas--advance-start-maybe (yas--fom-next fom) newend)
         (yas--advance-end-of-parents-maybe (yas--fom-parent-field fom) newend))
        ((yas--exit-p fom)
         (yas--advance-start-maybe (yas--fom-next fom) newend))))

(defun yas--advance-start-maybe (fom newstart)
  "Maybe advance FOM's start to NEWSTART if it needs it.

If it does, also call `yas--advance-end-maybe' on FOM."
  (when (and fom (< (yas--fom-start fom) newstart))
    (set-marker (yas--fom-start fom) newstart)
    (yas--advance-end-maybe fom newstart)))

(defun yas--advance-end-of-parents-maybe (field newend)
  "Like `yas--advance-end-maybe' but for parent fields.

Only works for fields and doesn't care about the start of the
next FOM.  Works its way up recursively for parents of parents."
  (when (and field
             (< (yas--field-end field) newend))
    (set-marker (yas--field-end field) newend)
    (yas--advance-end-of-parents-maybe (yas--field-parent-field field) newend)))

(defvar yas--dollar-regions nil
  "When expanding the snippet the \"parse-create\" functions add
cons cells to this var.")

(defvar yas--backquote-markers-and-strings nil
  "List of (MARKER . STRING) marking where the values from
backquoted Lisp expressions should be inserted at the end of
expansion.")

(defun yas--snippet-parse-create (snippet)
  "Parse a recently inserted snippet template, creating all
necessary fields, mirrors and exit points.

Meant to be called in a narrowed buffer, does various passes"
  (let ((parse-start (point)))
    ;; Reset the yas--dollar-regions
    ;;
    (setq yas--dollar-regions nil)
    ;; protect just the backquotes
    ;;
    (yas--protect-escapes nil '(?`))
    ;; replace all backquoted expressions
    ;;
    (goto-char parse-start)
    (yas--save-backquotes)
    ;; protect escaped characters
    ;;
    (yas--protect-escapes)
    ;; parse fields with {}
    ;;
    (goto-char parse-start)
    (yas--field-parse-create snippet)
    ;; parse simple mirrors and fields
    ;;
    (goto-char parse-start)
    (yas--simple-mirror-parse-create snippet)
    ;; parse mirror transforms
    ;;
    (goto-char parse-start)
    (yas--transform-mirror-parse-create snippet)
    ;; calculate adjacencies of fields and mirrors
    ;;
    (yas--calculate-adjacencies snippet)
    ;; Delete $-constructs
    ;;
    (save-restriction (widen) (yas--delete-regions yas--dollar-regions))
    ;; restore backquoted expression values
    ;;
    (yas--restore-backquotes)
    ;; restore escapes
    ;;
    (goto-char parse-start)
    (yas--restore-escapes)
    ;; update mirrors for the first time
    ;;
    (yas--update-mirrors snippet)
    ;; indent the best we can
    ;;
    (goto-char parse-start)
    (yas--indent snippet)))

(defun yas--indent-according-to-mode (snippet-markers)
  "Indent current line according to mode, preserving SNIPPET-MARKERS."
  ;;; Apropos indenting problems....
  ;;
  ;; `indent-according-to-mode' uses whatever `indent-line-function'
  ;; is available. Some implementations of these functions delete text
  ;; before they insert. If there happens to be a marker just after
  ;; the text being deleted, the insertion actually happens after the
  ;; marker, which misplaces it.
  ;;
  ;; This would also happen if we had used overlays with the
  ;; `front-advance' property set to nil.
  ;;
  ;; This is why I have these `trouble-markers', they are the ones at
  ;; they are the ones at the first non-whitespace char at the line
  ;; (i.e. at `yas--real-line-beginning'. After indentation takes place
  ;; we should be at the correct to restore them to. All other
  ;; non-trouble-markers have been *pushed* and don't need special
  ;; attention.
  ;;
  (goto-char (yas--real-line-beginning))
  (let ((trouble-markers (remove-if-not #'(lambda (marker)
                                            (= marker (point)))
                                        snippet-markers)))
    (save-restriction
      (widen)
      (condition-case _
          (indent-according-to-mode)
        (error (yas--message 3 "Warning: `yas--indent-according-to-mode' having problems running %s" indent-line-function)
               nil)))
    (mapc #'(lambda (marker)
              (set-marker marker (point)))
          trouble-markers)))

(defvar yas--indent-original-column nil)
(defun yas--indent (snippet)
  (let ((snippet-markers (yas--collect-snippet-markers snippet)))
    ;; Look for those $>
    (save-excursion
      (while (re-search-forward "$>" nil t)
        (delete-region (match-beginning 0) (match-end 0))
        (when (not (eq yas-indent-line 'auto))
          (yas--indent-according-to-mode snippet-markers))))
    ;; Now do stuff for 'fixed and 'auto
    (save-excursion
      (cond ((eq yas-indent-line 'fixed)
             (while (and (zerop (forward-line))
                         (zerop (current-column)))
               (indent-to-column yas--indent-original-column)))
            ((eq yas-indent-line 'auto)
             (let ((end (set-marker (make-marker) (point-max)))
                   (indent-first-line-p yas-also-auto-indent-first-line))
               (while (and (zerop (if indent-first-line-p
                                      (prog1
                                          (forward-line 0)
                                        (setq indent-first-line-p nil))
                                    (forward-line 1)))
                           (not (eobp))
                           (<= (point) end))
                 (yas--indent-according-to-mode snippet-markers))))
            (t
             nil)))))

(defun yas--collect-snippet-markers (snippet)
  "Make a list of all the markers used by SNIPPET."
  (let (markers)
    (dolist (field (yas--snippet-fields snippet))
      (push (yas--field-start field) markers)
      (push (yas--field-end field) markers)
      (dolist (mirror (yas--field-mirrors field))
        (push (yas--mirror-start mirror) markers)
        (push (yas--mirror-end mirror) markers)))
    (let ((snippet-exit (yas--snippet-exit snippet)))
      (when (and snippet-exit
                 (marker-buffer (yas--exit-marker snippet-exit)))
        (push (yas--exit-marker snippet-exit) markers)))
    markers))

(defun yas--real-line-beginning ()
  (let ((c (char-after (line-beginning-position)))
        (n (line-beginning-position)))
    (while (or (eql c ?\ )
               (eql c ?\t))
      (incf n)
      (setq c (char-after n)))
    n))

(defun yas--escape-string (escaped)
  (concat "YASESCAPE" (format "%d" escaped) "PROTECTGUARD"))

(defun yas--protect-escapes (&optional text escaped)
  "Protect all escaped characters with their numeric ASCII value.

With optional string TEXT do it in string instead of buffer."
  (let ((changed-text text)
        (text-provided-p text))
    (mapc #'(lambda (escaped)
              (setq changed-text
                    (yas--replace-all (concat "\\" (char-to-string escaped))
                                     (yas--escape-string escaped)
                                     (when text-provided-p changed-text))))
          (or escaped yas--escaped-characters))
    changed-text))

(defun yas--restore-escapes (&optional text escaped)
  "Restore all escaped characters from their numeric ASCII value.

With optional string TEXT do it in string instead of the buffer."
  (let ((changed-text text)
        (text-provided-p text))
    (mapc #'(lambda (escaped)
              (setq changed-text
                    (yas--replace-all (yas--escape-string escaped)
                                     (char-to-string escaped)
                                     (when text-provided-p changed-text))))
          (or escaped yas--escaped-characters))
    changed-text))

(defun yas--save-backquotes ()
  "Save all the \"`(lisp-expression)`\"-style expressions
with their evaluated value into `yas--backquote-markers-and-strings'."
  (while (re-search-forward yas--backquote-lisp-expression-regexp nil t)
    (let ((current-string (match-string-no-properties 1)) transformed)
      (save-restriction (widen)
                        (delete-region (match-beginning 0) (match-end 0)))
      (setq transformed (yas--eval-lisp (yas--read-lisp (yas--restore-escapes current-string '(?`)))))
      (goto-char (match-beginning 0))
      (when transformed
        (let ((marker (make-marker)))
          (save-restriction
            (widen)
            (insert "Y") ;; quite horrendous, I love it :)
            (set-marker marker (point))
            (insert "Y"))
          (push (cons marker transformed) yas--backquote-markers-and-strings))))))

(defun yas--restore-backquotes ()
  "Replace markers in `yas--backquote-markers-and-strings' with their values."
  (while yas--backquote-markers-and-strings
    (let* ((marker-and-string (pop yas--backquote-markers-and-strings))
           (marker (car marker-and-string))
           (string (cdr marker-and-string)))
      (save-excursion
        (goto-char marker)
        (save-restriction
          (widen)
          (delete-char -1)
          (insert string)
          (delete-char 1))
        (set-marker marker nil)))))

(defun yas--scan-sexps (from count)
  (condition-case _
      (with-syntax-table (standard-syntax-table)
        (scan-sexps from count))
    (error
     nil)))

(defun yas--make-marker (pos)
  "Create a marker at POS with nil `marker-insertion-type'."
  (let ((marker (set-marker (make-marker) pos)))
    (set-marker-insertion-type marker nil)
    marker))

(defun yas--field-parse-create (snippet &optional parent-field)
  "Parse most field expressions in SNIPPET, except for the simple one \"$n\".

The following count as a field:

* \"${n: text}\", for a numbered field with default text, as long as N is not 0;

* \"${n: text$(expression)}, the same with a Lisp expression;
  this is caught with the curiously named `yas--multi-dollar-lisp-expression-regexp'

* the same as above but unnumbered, (no N:) and number is calculated automatically.

When multiple expressions are found, only the last one counts."
  ;;
  (save-excursion
    (while (re-search-forward yas--field-regexp nil t)
      (let* ((real-match-end-0 (yas--scan-sexps (1+ (match-beginning 0)) 1))
             (number (and (match-string-no-properties 1)
                          (string-to-number (match-string-no-properties 1))))
             (brand-new-field (and real-match-end-0
                                   ;; break if on "$(" immediately
                                   ;; after the ":", this will be
                                   ;; caught as a mirror with
                                   ;; transform later.
                                   (not (save-match-data
                                          (eq (string-match "$[ \t\n]*("
                                                            (match-string-no-properties 2)) 0)))
                                   ;; allow ${0: some exit text}
                                   ;; (not (and number (zerop number)))
                                   (yas--make-field number
                                                   (yas--make-marker (match-beginning 2))
                                                   (yas--make-marker (1- real-match-end-0))
                                                   parent-field))))
        (when brand-new-field
          (goto-char real-match-end-0)
          (push (cons (1- real-match-end-0) real-match-end-0)
                yas--dollar-regions)
          (push (cons (match-beginning 0) (match-beginning 2))
                yas--dollar-regions)
          (push brand-new-field (yas--snippet-fields snippet))
          (save-excursion
            (save-restriction
              (narrow-to-region (yas--field-start brand-new-field) (yas--field-end brand-new-field))
              (goto-char (point-min))
              (yas--field-parse-create snippet brand-new-field)))))))
  ;; if we entered from a parent field, now search for the
  ;; `yas--multi-dollar-lisp-expression-regexp'. This is used for
  ;; primary field transformations
  ;;
  (when parent-field
    (save-excursion
      (while (re-search-forward yas--multi-dollar-lisp-expression-regexp nil t)
        (let* ((real-match-end-1 (yas--scan-sexps (match-beginning 1) 1)))
          ;; commit the primary field transformation if:
          ;;
          ;; 1. we don't find it in yas--dollar-regions (a subnested
          ;; field) might have already caught it.
          ;;
          ;; 2. we really make sure we have either two '$' or some
          ;; text and a '$' after the colon ':'. This is a FIXME: work
          ;; my regular expressions and end these ugly hacks.
          ;;
          (when (and real-match-end-1
                     (not (member (cons (match-beginning 0)
                                        real-match-end-1)
                                  yas--dollar-regions))
                     (not (eq ?:
                              (char-before (1- (match-beginning 1))))))
            (let ((lisp-expression-string (buffer-substring-no-properties (match-beginning 1)
                                                                          real-match-end-1)))
              (setf (yas--field-transform parent-field)
                    (yas--read-lisp (yas--restore-escapes lisp-expression-string))))
            (push (cons (match-beginning 0) real-match-end-1)
                  yas--dollar-regions)))))))

(defun yas--transform-mirror-parse-create (snippet)
  "Parse the \"${n:$(lisp-expression)}\" mirror transformations in SNIPPET."
  (while (re-search-forward yas--transform-mirror-regexp nil t)
    (let* ((real-match-end-0 (yas--scan-sexps (1+ (match-beginning 0)) 1))
           (number (string-to-number (match-string-no-properties 1)))
           (field (and number
                       (not (zerop number))
                       (yas--snippet-find-field snippet number)))
           (brand-new-mirror
            (and real-match-end-0
                 field
                 (yas--make-mirror (yas--make-marker (match-beginning 0))
                                  (yas--make-marker (match-beginning 0))
                                  (yas--read-lisp
                                   (yas--restore-escapes
                                    (buffer-substring-no-properties (match-beginning 2)
                                                                    (1- real-match-end-0))))))))
      (when brand-new-mirror
        (push brand-new-mirror
              (yas--field-mirrors field))
        (yas--calculate-mirrors-in-fields snippet brand-new-mirror)
        (push (cons (match-beginning 0) real-match-end-0) yas--dollar-regions)))))

(defun yas--simple-mirror-parse-create (snippet)
  "Parse the simple \"$n\" fields/mirrors/exitmarkers in SNIPPET."
  (while (re-search-forward yas--simple-mirror-regexp nil t)
    (let ((number (string-to-number (match-string-no-properties 1))))
      (cond ((zerop number)

             (setf (yas--snippet-exit snippet)
                   (yas--make-exit (yas--make-marker (match-end 0))))
             (save-excursion
               (goto-char (match-beginning 0))
               (when yas-wrap-around-region
                 (cond (yas-selected-text
                        (insert yas-selected-text))
                       ((and (eq yas-wrap-around-region 'cua)
                             cua-mode
                             (get-register ?0))
                        (insert (prog1 (get-register ?0)
                                  (set-register ?0 nil))))))
               (push (cons (point) (yas--exit-marker (yas--snippet-exit snippet)))
                     yas--dollar-regions)))
            (t
             (let ((field (yas--snippet-find-field snippet number)))
               (if field
                   (let ((brand-new-mirror (yas--make-mirror
                                            (yas--make-marker (match-beginning 0))
                                            (yas--make-marker (match-beginning 0))
                                            nil)))
                     (push brand-new-mirror
                           (yas--field-mirrors field))
                     (yas--calculate-mirrors-in-fields snippet brand-new-mirror))
                 (push (yas--make-field number
                                       (yas--make-marker (match-beginning 0))
                                       (yas--make-marker (match-beginning 0))
                                       nil)
                       (yas--snippet-fields snippet))))
             (push (cons (match-beginning 0) (match-end 0))
                   yas--dollar-regions))))))

(defun yas--delete-regions (regions)
  "Sort disjuct REGIONS by start point, then delete from the back."
  (mapc #'(lambda (reg)
            (delete-region (car reg) (cdr reg)))
        (sort regions
              #'(lambda (r1 r2)
                  (>= (car r1) (car r2))))))

(defun yas--calculate-mirror-depth (mirror &optional traversed)
  (let* ((parent (yas--mirror-parent-field mirror))
         (parents-mirrors (and parent
                               (yas--field-mirrors parent))))
    (or (yas--mirror-depth mirror)
        (setf (yas--mirror-depth mirror)
              (cond ((memq mirror traversed)
                     0)
                    ((and parent parents-mirrors)
                     (1+ (reduce #'max
                                 (mapcar #'(lambda (m)
                                             (yas--calculate-mirror-depth m
                                                                          (cons mirror
                                                                                traversed)))
                                         parents-mirrors))))
                    (parent
                     1)
                    (t
                     0))))))

(defun yas--update-mirrors (snippet)
  "Update all the mirrors of SNIPPET."
  (save-excursion
    (dolist (field-and-mirror (sort
                               ;; make a list of ((F1 . M1) (F1 . M2) (F2 . M3) (F2 . M4) ...)
                               ;; where F is the field that M is mirroring
                               ;;
                               (mapcan #'(lambda (field)
                                           (mapcar #'(lambda (mirror)
                                                       (cons field mirror))
                                                   (yas--field-mirrors field)))
                                       (yas--snippet-fields snippet))
                               ;; then sort this list so that entries with mirrors with parent
                               ;; fields appear before. This was important for fixing #290, and
                               ;; luckily also handles the case where a mirror in a field causes
                               ;; another mirror to need reupdating
                               ;;
                               #'(lambda (field-and-mirror1 field-and-mirror2)
                                   (> (yas--calculate-mirror-depth (cdr field-and-mirror1))
                                      (yas--calculate-mirror-depth (cdr field-and-mirror2))))))
      (let* ((field (car field-and-mirror))
             (mirror (cdr field-and-mirror))
             (parent-field (yas--mirror-parent-field mirror)))
        ;; before updating a mirror with a parent-field, maybe advance
        ;; its start (#290)
        ;;
        (when parent-field
          (yas--advance-start-maybe mirror (yas--fom-start parent-field)))
        ;; update this mirror
        ;;
        (yas--mirror-update-display mirror field)
        ;; `yas--place-overlays' is needed if the active field and
        ;; protected overlays have been changed because of insertions
        ;; in `yas--mirror-update-display'
        ;;
        (when (eq field (yas--snippet-active-field snippet))
          (yas--place-overlays snippet field))))))

(defun yas--mirror-update-display (mirror field)
  "Update MIRROR according to FIELD (and mirror transform)."

  (let* ((mirror-parent-field (yas--mirror-parent-field mirror))
         (reflection (and (not (and mirror-parent-field
                                    (yas--field-modified-p mirror-parent-field)))
                          (or (yas--apply-transform mirror field 'empty-on-nil)
                              (yas--field-text-for-display field)))))
    (when (and reflection
               (not (string= reflection (buffer-substring-no-properties (yas--mirror-start mirror)
                                                                        (yas--mirror-end mirror)))))
      (goto-char (yas--mirror-start mirror))
      (yas--inhibit-overlay-hooks
        (insert reflection))
      (if (> (yas--mirror-end mirror) (point))
          (delete-region (point) (yas--mirror-end mirror))
        (set-marker (yas--mirror-end mirror) (point))
        (yas--advance-start-maybe (yas--mirror-next mirror) (point))
        ;; super-special advance
        (yas--advance-end-of-parents-maybe mirror-parent-field (point))))))

(defun yas--field-update-display (field)
  "Much like `yas--mirror-update-display', but for fields."
  (when (yas--field-transform field)
    (let ((transformed (and (not (eq (yas--field-number field) 0))
                            (yas--apply-transform field field))))
      (when (and transformed
                 (not (string= transformed (buffer-substring-no-properties (yas--field-start field)
                                                                           (yas--field-end field)))))
        (setf (yas--field-modified-p field) t)
        (goto-char (yas--field-start field))
        (yas--inhibit-overlay-hooks
          (insert transformed)
          (if (> (yas--field-end field) (point))
              (delete-region (point) (yas--field-end field))
            (set-marker (yas--field-end field) (point))
            (yas--advance-start-maybe (yas--field-next field) (point)))
          t)))))


;;; Post-command hook:
;;
(defun yas--post-command-handler ()
  "Handles various yasnippet conditions after each command."
  (cond (yas--protection-violation
         (goto-char yas--protection-violation)
         (setq yas--protection-violation nil))
        ((eq 'undo this-command)
         ;;
         ;; After undo revival the correct field is sometimes not
         ;; restored correctly, this condition handles that
         ;;
         (let* ((snippet (car (yas--snippets-at-point)))
                (target-field (and snippet
                                   (find-if-not #'(lambda (field)
                                                    (yas--field-probably-deleted-p snippet field))
                                                (remove nil
                                                        (cons (yas--snippet-active-field snippet)
                                                              (yas--snippet-fields snippet)))))))
           (when target-field
             (yas--move-to-field snippet target-field))))
        ((not (yas--undo-in-progress))
         ;; When not in an undo, check if we must commit the snippet
         ;; (user exited it).
         (yas--check-commit-snippet))))

;;; Fancy docs:
;;
;; The docstrings for some functions are generated dynamically
;; depending on the context.
;;
(put 'yas-expand  'function-documentation
     '(yas--expand-from-trigger-key-doc t))
(defun yas--expand-from-trigger-key-doc (context)
  "A doc synthesizer for `yas--expand-from-trigger-key-doc'."
  (let* ((yas-fallback-behavior (and context yas-fallback-behavior))
         (fallback-description
          (cond ((eq yas-fallback-behavior 'call-other-command)
                 (let* ((fallback (yas--keybinding-beyond-yasnippet)))
                   (or (and fallback
                            (format "call command `%s'."
                                    (pp-to-string fallback)))
                       "do nothing (`yas-expand' doesn't shadow\nanything).")))
                ((eq yas-fallback-behavior 'return-nil)
                 "do nothing.")
                (t "defer to `yas-fallback-behavior' (which see)."))))
    (concat "Expand a snippet before point. If no snippet
expansion is possible, "
            fallback-description
            "\n\nOptional argument FIELD is for non-interactive use and is an
object satisfying `yas--field-p' to restrict the expansion to.")))

(put 'yas-expand-from-keymap 'function-documentation
     '(yas--expand-from-keymap-doc t))
(defun yas--expand-from-keymap-doc (context)
  "A doc synthesizer for `yas--expand-from-keymap-doc'."
  (add-hook 'temp-buffer-show-hook 'yas--snippet-description-finish-runonce)
  (concat "Expand/run snippets from keymaps, possibly falling back to original binding.\n"
          (when (and context (eq this-command 'describe-key))
            (let* ((vec (this-single-command-keys))
                   (templates (mapcan #'(lambda (table)
                                          (yas--fetch table vec))
                                      (yas--get-snippet-tables)))
                   (yas--direct-keymaps nil)
                   (fallback (key-binding vec)))
              (concat "In this case, "
                      (when templates
                        (concat "these snippets are bound to this key:\n"
                                (yas--template-pretty-list templates)
                                "\n\nIf none of these expands, "))
                      (or (and fallback
                               (format "fallback `%s' will be called." (pp-to-string fallback)))
                          "no fallback keybinding is called."))))))

(defun yas--template-pretty-list (templates)
  (let ((acc)
        (yas-buffer-local-condition 'always))
    (dolist (plate templates)
      (setq acc (concat acc "\n*) "
                        (propertize (concat "\\\\snippet `" (car plate) "'")
                                    'yasnippet (cdr plate)))))
    acc))

(define-button-type 'help-snippet-def
  :supertype 'help-xref
  'help-function (lambda (template) (yas--visit-snippet-file-1 template))
  'help-echo (purecopy "mouse-2, RET: find snippets's definition"))

(defun yas--snippet-description-finish-runonce ()
  "Final adjustments for the help buffer when snippets are concerned."
  (yas--create-snippet-xrefs)
  (remove-hook 'temp-buffer-show-hook 'yas--snippet-description-finish-runonce))

(defun yas--create-snippet-xrefs ()
  (save-excursion
    (goto-char (point-min))
    (while (search-forward-regexp "\\\\\\\\snippet[ \s\t]+`\\([^']+\\)'" nil t)
      (let ((template (get-text-property (match-beginning 1)
                                         'yasnippet)))
        (when template
          (help-xref-button 1 'help-snippet-def template)
          (kill-region (match-end 1) (match-end 0))
          (kill-region (match-beginning 0) (match-beginning 1)))))))

;;; Utils

(defvar yas-verbosity 4
  "Log level for `yas--message' 4 means trace most anything, 0 means nothing.")

(defun yas--message (level message &rest args)
  "When LEVEL is above `yas-verbosity-level', log MESSAGE and ARGS."
  (when (> yas-verbosity level)
    (message "%s" (apply #'yas--format message args))))

(defun yas--warning (format-control &rest format-args)
  (let ((msg (apply #'format format-control format-args)))
    (display-warning 'yasnippet msg :warning)
    (yas--message 1 msg)))

(defun yas--format (format-control &rest format-args)
  (apply #'format (concat "[yas] " format-control) format-args))


;;; Some hacks:
;;
;; The functions
;;
;; `locate-dominating-file'
;; `region-active-p'
;;
;; added for compatibility in emacsen < 23
(unless (>= emacs-major-version 23)
  (unless (fboundp 'region-active-p)
    (defun region-active-p ()  (and transient-mark-mode mark-active)))

  (unless (fboundp 'locate-dominating-file)
    (defvar locate-dominating-stop-dir-regexp
      "\\`\\(?:[\\/][\\/][^\\/]+[\\/]\\|/\\(?:net\\|afs\\|\\.\\.\\.\\)/\\)\\'"
      "Regexp of directory names which stop the search in `locate-dominating-file'.
Any directory whose name matches this regexp will be treated like
a kind of root directory by `locate-dominating-file' which will stop its search
when it bumps into it.
The default regexp prevents fruitless and time-consuming attempts to find
special files in directories in which filenames are interpreted as hostnames,
or mount points potentially requiring authentication as a different user.")

    (defun locate-dominating-file (file name)
      "Look up the directory hierarchy from FILE for a file named NAME.
Stop at the first parent directory containing a file NAME,
and return the directory.  Return nil if not found."
      ;; We used to use the above locate-dominating-files code, but the
      ;; directory-files call is very costly, so we're much better off doing
      ;; multiple calls using the code in here.
      ;;
      ;; Represent /home/luser/foo as ~/foo so that we don't try to look for
      ;; `name' in /home or in /.
      (setq file (abbreviate-file-name file))
      (let ((root nil)
            try)
        (while (not (or root
                        (null file)
                        ;; FIXME: Disabled this heuristic because it is sometimes
                        ;; inappropriate.
                        ;; As a heuristic, we stop looking up the hierarchy of
                        ;; directories as soon as we find a directory belonging
                        ;; to another user.  This should save us from looking in
                        ;; things like /net and /afs.  This assumes that all the
                        ;; files inside a project belong to the same user.
                        ;; (let ((prev-user user))
                        ;;   (setq user (nth 2 (file-attributes file)))
                        ;;   (and prev-user (not (equal user prev-user))))
                        (string-match locate-dominating-stop-dir-regexp file)))
          (setq try (file-exists-p (expand-file-name name file)))
          (cond (try (setq root file))
                ((equal file (setq file (file-name-directory
                                         (directory-file-name file))))
                 (setq file nil))))
        root))))


;;; Backward compatibility to yasnippet <= 0.7

(defvar yas--backported-syms '(;; `defcustom's
                             ;;
                             yas-snippet-dirs
                             yas-prompt-functions
                             yas-indent-line
                             yas-also-auto-indent-first-line
                             yas-snippet-revival
                             yas-triggers-in-field
                             yas-fallback-behavior
                             yas-choose-keys-first
                             yas-choose-tables-first
                             yas-use-menu
                             yas-trigger-symbol
                             yas-wrap-around-region
                             yas-good-grace
                             yas-visit-from-menu
                             yas-expand-only-for-last-commands
                             yas-field-highlight-face

                             ;; these vars can be customized as well
                             ;;
                             yas-keymap
                             yas-verbosity
                             yas-extra-modes
                             yas-key-syntaxes
                             yas-after-exit-snippet-hook
                             yas-before-expand-snippet-hook
                             yas-buffer-local-condition
                             yas-dont-activate

                             ;; prompting functions
                             ;;
                             yas-x-prompt
                             yas-ido-prompt
                             yas-no-prompt
                             yas-completing-prompt
                             yas-dropdown-prompt

                             ;; interactive functions
                             ;;
                             yas-expand
                             yas-minor-mode
                             yas-global-mode
                             yas-direct-keymaps-reload
                             yas-minor-mode-on
                             yas-load-directory
                             yas-reload-all
                             yas-compile-directory
                             yas-recompile-all
                             yas-about
                             yas-expand-from-trigger-key
                             yas-expand-from-keymap
                             yas-insert-snippet
                             yas-visit-snippet-file
                             yas-new-snippet
                             yas-load-snippet-buffer
                             yas-tryout-snippet
                             yas-describe-tables
                             yas-next-field-or-maybe-expand
                             yas-next-field
                             yas-prev-field
                             yas-abort-snippet
                             yas-exit-snippet
                             yas-exit-all-snippets
                             yas-skip-and-clear-or-delete-char

                             ;; symbols that I "exported" for use
                             ;; in snippets and hookage
                             ;;
                             yas-expand-snippet
                             yas-define-snippets
                             yas-define-menu
                             yas-snippet-beg
                             yas-snippet-end
                             yas-modified-p
                             yas-moving-away-p
                             yas-substr
                             yas-choose-value
                             yas-key-to-value
                             yas-throw
                             yas-verify-value
                             yas-field-value
                             yas-text
                             yas-selected-text
                             yas-default-from-field
                             yas-inside-string
                             yas-unimplemented
                             yas-define-condition-cache
                             yas-hippie-try-expand

                             ;; debug definitions
                             ;; yas-debug-snippet-vars
                             ;; yas-exterminate-package
                             ;; yas-debug-test

                             ;; testing definitions
                             ;; yas-should-expand
                             ;; yas-should-not-expand
                             ;; yas-mock-insert
                             ;; yas-make-file-or-dirs
                             ;; yas-variables
                             ;; yas-saving-variables
                             ;; yas-call-with-snippet-dirs
                             ;; yas-with-snippet-dirs
)
  "Backported yasnippet symbols.

They are mapped to \"yas/*\" variants.")

(dolist (sym yas--backported-syms)
  (let ((backported (intern (replace-regexp-in-string "^yas-" "yas/" (symbol-name sym)))))
    (when (boundp sym)
      (make-obsolete-variable backported sym "yasnippet 0.8")
      (defvaralias backported sym))
    (when (fboundp sym)
      (make-obsolete backported sym "yasnippet 0.8")
      (defalias backported sym))))

(defvar yas--exported-syms
  (let (exported)
    (mapatoms (lambda (atom)
                (if (and (or (and (boundp atom)
                                  (not (get atom 'byte-obsolete-variable)))
                             (and (fboundp atom)
                                  (not (get atom 'byte-obsolete-info))))
                         (string-match-p "^yas-[^-]" (symbol-name atom)))
                    (push atom exported))))
    exported)
  "Exported yasnippet symbols.

i.e. the ones with \"yas-\" single dash prefix. I will try to
keep them in future yasnippet versions and other elisp libraries
can more or less safely rely upon them.")


(provide 'yasnippet)

;;; yasnippet.el ends here
;; Local Variables:
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions)
;; End:
