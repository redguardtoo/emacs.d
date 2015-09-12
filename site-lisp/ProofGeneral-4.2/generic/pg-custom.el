;;; pg-custom.el --- Proof General per-prover settings
;;
;; Copyright (C) 2008, 2010 LFCS Edinburgh.
;; Author:      David Aspinall <David.Aspinall@ed.ac.uk> and others
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; pg-custom.el,v 12.1 2012/01/03 09:36:05 tews Exp
;;
;;; Commentary:
;;
;; Prover specific settings and user options.
;;
;; The settings defined here automatically use the current proof
;; assistant symbol as a prefix, i.e.  isar-favourites, coq-favourites,
;; or whatever will be defined on evaluation.
;;
;; This file is loaded only by mode stubs defined in `proof-site.el',
;; immediately after `proof-assistant' and similar settings have been
;; configured.
;;
;; WARNING: loading this file without these variables being set will
;; give errors, because defpgcustom calls are expanded to top-level
;; forms that refer to `proof-assistant', which is only properly set
;; when the mode for a proof assistant is started (see mode stub).
;;
;; See also:
;;
;;  proof-useropts.el
;;  pg-vars.el

;;; Code:

(require 'pg-pamacs)		   ; defpgcustom
(require 'pg-vars)		   ; for proof-next-command-on-new-line
(require 'proof-config)		   ; for proof-toolbar-entries-default

(defpgcustom script-indent t
  "*If non-nil, enable indentation code for proof scripts."
  :type 'boolean
  :group 'proof-user-options)

(defconst proof-toolbar-entries-default
`((state "Display Proof State" "Display the current proof state" t
	   proof-showproof-command)
  (context "Display Context" "Display the current context" t
	     proof-context-command)
  (goal      "Start a New Proof" "Start a new proof" t nil)
  (retract   "Retract Buffer"     "Retract (undo) whole buffer" t t)
  (undo      "Undo Step"          "Undo the previous proof command" t t)
  (delete    "Delete Step"        "Delete the last proof command" nil t)
  (next      "Next Step"          "Process the next proof command" t t)
  (use       "Use Buffer"         "Process whole buffer" t t)
  (goto      "Goto Point"         "Process or undo to the cursor position" t t)
  (qed       "Finish Proof"       "Close/save proved theorem" t nil)
  (home      "Goto Locked End"    "Goto end of the last command processed" t t)
  (find      "Find Theorems"	  "Find theorems" t proof-find-theorems-command)
  (info      "Identifier Info"    "Information about identifier" t proof-query-identifier-command)
  (command   "Issue Command"	  "Issue a non-scripting command" t t)
  (prooftree "Start/Stop Prooftree" "Start/Stop external proof-tree display" t proof-tree-configured)
  (interrupt "Interrupt Prover"   "Interrupt the proof assistant" t t)
  (restart   "Restart Scripting"  "Restart scripting (clear all locked regions)" t t)
  (visibility "Toggle Visibility" "Show or hide hidden proofs" nil t)
  (help	nil   "Proof General manual" t t))
"Example value for proof-toolbar-entries.  Also used to define scripting menu.
This gives a bare toolbar that works for any prover, providing the
appropriate configuration variables are set.
To add/remove prover specific buttons, adjust the `<PA>-toolbar-entries'
variable, and follow the pattern in `proof-toolbar.el' for
defining functions, images.")

(defpgcustom toolbar-entries proof-toolbar-entries-default
  "List of entries for Proof General toolbar and Scripting menu.
Format of each entry is (TOKEN MENUNAME TOOLTIP TOOLBAR-P [VISIBLE-P]).

For each TOKEN, we expect an icon with base filename TOKEN,
a function proof-toolbar-<TOKEN>, and (optionally) a dynamic enabler
proof-toolbar-<TOKEN>-enable-p.

If VISIBLE-P is absent, or evaluates to non-nil, the item will
appear on the toolbar or menu.  If it evaluates to nil, the item
is not shown.

If MENUNAME is nil, item will not appear on the scripting menu.

If TOOLBAR-P is nil, item will not appear on the toolbar.

The default value is `proof-toolbar-entries-default' which contains
the standard Proof General buttons.")

(defpgcustom prog-args nil
  "Arguments to be passed to `proof-prog-name' to run the proof assistant.
If non-nil, will be treated as a list of arguments for `proof-prog-name'.
Otherwise `proof-prog-name' will be split on spaces to form arguments.

Remark: Arguments are interpreted strictly: each one must contain only one
word, with no space (unless it is the same word). For example if the
arguments are -x foo -y bar, then the list should be '(\"-x\" \"foo\"
\"-y\" \"bar\"), notice that '(\"-x foo\" \"-y bar\") is *wrong*."
  :type '(repeat string)
  :group 'proof-shell)

(defpgcustom prog-env nil
  "Modifications to `process-environment' made before running `proof-prog-name'.
Each element should be a string of the form ENVVARNAME=VALUE.  They will be
added to the environment before launching the prover (but not pervasively).
For example for coq on Windows you might need something like:
\(setq coq-prog-env '(\"HOME=C:\\Program Files\\Coq\\\"))"
  :type '(repeat string)
  :group 'proof-shell)

(defpgcustom quit-timeout 
  (cond
   ((eq proof-assistant-symbol 'isar)    45)
   (t					 5))
  "The number of seconds to wait after sending `proof-shell-quit-cmd'.
After this timeout, the proof shell will be killed off more rudely.
If your proof assistant takes a long time to clean up (for
example writing persistent databases out or the like), you may
need to bump up this value."
   :type 'number
   :group 'proof-shell)

(defpgcustom favourites nil
  "*Favourite commands for this proof assistant.
A list of lists of the form (COMMAND INSCRIPT MENUNAME KEY),
arguments for `proof-add-favourite', which see.")

(defpgcustom menu-entries nil
  "Extra entries for proof assistant specific menu.
A list of menu items [NAME CALLBACK ENABLER ...].  See the documentation
of `easy-menu-define' for more details."
  :type 'sexp
  :group 'prover-config)

(defpgcustom help-menu-entries nil
  "Extra entries for help submenu for proof assistant specific help menu.
A list of menu items [NAME CALLBACK ENABLER ...].  See the documentation
of `easy-menu-define' for more details."
  :type 'sexp
  :group 'prover-config)

(defpgcustom keymap (make-keymap (concat proof-assistant " keymap"))
  "Proof assistant specific keymap, used under prefix C-c a."
  :type 'sexp
  :group 'prover-config)

(defpgcustom completion-table nil
  "List of identifiers to use for completion for this proof assistant.
Completion is activated with \\[complete].

If this table is empty or needs adjusting, please make changes using
`customize-variable' and post suggestions at
http://proofgeneral.inf.ed.ac.uk/trac"
  :type '(repeat string)
  :group 'prover-config)

;; TODO: not used yet.
(defpgcustom tags-program nil
  "Program to run to generate TAGS table for proof assistant.
Currently this setting is UNIMPLEMENTED, changes have no effect."
  :type 'file
  :group 'prover-config)

;; TODO: not used yet.  Want to move specific enabling of holes modes
;; to generic code (coq.el enables it in script and shell).
;; See http://proofgeneral.inf.ed.ac.uk/trac/ticket/211
(defpgcustom use-holes (eq proof-assistant-symbol 'coq)
  "Whether or not to use the holes (editing template) mechanism.
Enabled by default for Coq.
Currently this setting is UNIMPLEMENTED, changes have no effect."
  :type 'boolean
  :group 'prover-config)

(defpgcustom one-command-per-line
  (cond
   ((eq proof-assistant-symbol 'isar)  nil)
   (t t))
  "*If non-nil, format for newlines after each command in a script."
  :type 'boolean
  :group 'proof-user-options)


;; Contributed modes

(defpgcustom maths-menu-enable nil
  "*Non-nil for Unicode maths menu in Proof General for this assistant."
  :type 'boolean
  :set 'proof-set-value
  :group 'proof-user-options)

(defpgcustom unicode-tokens-enable (eq proof-assistant-symbol 'isar)
  "*Non-nil for using Unicode token input mode in Proof General."
  :type 'boolean
  :set 'proof-set-value
  :group 'proof-user-options)

(defpgcustom mmm-enable nil
  "*Whether to use MMM Mode in Proof General for this assistant.
MMM Mode allows multiple modes to be used in the same buffer.
If you activate this variable, whether or not you really get MMM
support depends on whether your proof assistant supports it."
  :type 'boolean
  :set 'proof-set-value
  :group 'proof-user-options)



(provide 'pg-custom)

;;; pg-custom.el ends here
