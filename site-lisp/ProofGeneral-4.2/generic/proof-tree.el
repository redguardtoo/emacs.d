;;; tree-tree.el --- Proof General prooftree communication.
;;
;; Copyright (C) 2012 Hendrik Tews
;; Authors:   Hendrik Tews
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; proof-tree.el,v 12.4 2012/09/12 12:33:13 tews Exp
;;
;;; Commentary:
;;
;; Generic code for the communication with prooftree. Prooftree
;; is an ocaml-gtk program that displays proof trees.
;;
;; The main problem with proof tree visualization is that Coq (and
;; probably other proof assistants as well) does not provide any
;; information about which subgoals are new and have been created by
;; the last proof command and which subgoals stem from older proof
;; commands.
;;
;; To solve this problem prooftree relies on unique identification
;; strings of goals, which are called goal or sequent ID's in the
;; code. With these ID's it is easy to keep track which goals are new.
;;
;; A second problem is that, for an undo command, Coq (and probably
;; other proof assistants as well) does not tell which subgoals and
;; which finished branches must be deleted. Therefore prooftree needs
;; a continuously increasing proof state number and keeps a complete
;; undo history for every proof.
;;
;; A third problem is that Coq (and probably other proof assistants as
;; well) is not able to generate the information for a proof tree in
;; the middle of a proof. Therefore, if the user wants to start the
;; proof-tree display in the middle of the proof, it is necessary to
;; retract to the start of the proof and then to reassert to the
;; previous end of the locked region. To achieve this one has to call
;; `accept-process-output' at suitable points to let Proof General
;; process the `proof-action-list'.
;; 
;; A fourth problem is that proof-tree display can only work when the
;; prover output is not suppressed (via `proof-full-annotation').
;; `proof-shell-should-be-silent' takes care of that.
;; 
;; The design of Prooftree, of the glue code inside Proof General
;; (mostly in this file) and of the communication protocol tries to
;; achieve the following two goals:
;;
;;   * Functionality is preferably transferred into prooftree, to
;;     enlarge Proof General not unnecessarily.
;;
;;   * To avoid synchronization trouble the communication between
;;     Proof General and prooftree is almost one way only: Only Proof
;;     General sends display or undo commands to Prooftree. Prooftree
;;     never requests any proof-state information from Proof General.
;;     Prooftree only sends a quit message to Proof General when the
;;     user closes the proof-tree display of the current proof. This
;;     goal requires that some of the heuristics, which decide which
;;     subgoals are new and which have to be refreshed, have to be
;;     implemented here.
;;
;; In general the glue code here works on the delayed output. That is,
;; the glue code here runs when the next proof command has already
;; been sent to the proof assistant. The glue code makes a light
;; analysis on the output of the proof assistant, extracts the
;; necessary parts with regular expressions and sends appropriate
;; commands to prooftree. This is achieved by calling the main entry
;; here, the function `proof-tree-handle-delayed-output' from the
;; proof shell filter function after `proof-shell-exec-loop' has
;; finished.
;;
;; However, some aspects can not be delayed. Those are treated by
;; `proof-tree-urgent-action'. Its primary use is for inserting
;; special goal-displaying commands into `proof-action-list' before
;; the next real proof command runs. For Coq this needs to be done for
;; newly generated subgoals and for goals that contain an existential
;; variable that got instantiated in the last proof step.


;;; Code:

(require 'cl)

(eval-when (compile)
  (require 'proof-shell))


;;
;; User options
;;

(defgroup proof-tree ()
  "Customization for the proof tree visualizer"
  :group 'proof-general
  :package-version '(ProofGeneral . "4.2"))

(defcustom proof-tree-program (proof-locate-executable "prooftree" t nil)
  "Command to invoke prooftree."
  :type 'string
  :group 'proof-tree)

(defcustom proof-tree-arguments ()
  "Command line arguments for prooftree."
  :type '(repeat string)
  :group 'proof-tree)


;;
;; Proof assistant options
;;

(defgroup proof-tree-internals ()
  "Proof assistant specific customization of prooftree."
  :group 'proof-general-internals
  :package-version '(ProofGeneral . "4.2"))

;; defcustom proof-tree-configured is in proof-config.el, because it is
;; needed in pg-custom.el

(defcustom proof-tree-ignored-commands-regexp nil
  "Commands that should be ignored for the prooftree display.
The output of commands matching this regular expression is not
sent to prooftree. It should match commands that display
additional information but do not make any proof progress. Leave
at nil to act on all commands.

For Coq this regular expression should contain all commands such
as Lemma, that can start a proof."
  :type '(choice regexp (const nil))
  :group 'proof-tree-internals)

(defcustom proof-tree-navigation-command-regexp nil
  "Regexp to match a navigation command.
A navigation command typically focusses on a different open goal
without changing any of the open goals. Leave at nil if there are
no navigation commands."
  :type '(choice regexp (const nil))
  :group 'proof-tree-internals)

(defcustom proof-tree-cheating-regexp nil
  "Regexp to match cheating proofer commands.
A cheating command finishes the current goal without proving it
to permit the user to first focus on other parts of the
development. Examples are \"sorry\" in Isabelle and \"admit\" in
Coq. Leave at nil if there are no cheating commands."
  :type '(choice regexp (const nil))
  :group 'proof-tree-internals)

(defcustom proof-tree-current-goal-regexp nil
  "Regexp to match the current goal and its ID.
The regexp is matched against the output of the proof assistant
to extract the current goal with its ID. The regexp must have 2
grouping constructs, the first one matches just the ID, the
second one the complete sequent text that is to be sent to
prooftree."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-update-goal-regexp nil
  "Regexp to match a goal and its ID.
The regexp is matched against the output of additional show-goal
commands inserted by Proof General with a command returned by
`proof-tree-show-sequent-command'. Proof General inserts such
commands to update the goal text in prooftree. This is necessary,
for instance, when existential variables get instantiated. This
regexp must have 2 grouping constructs, the first matching the ID
of the goal, the second the complete sequent text."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-additional-subgoal-ID-regexp nil
  "Regular expression to match ID's of additional subgoals.
This regexp is used to extract the ID's of all additionally open
goals. The regexp is used in a while loop and must match one
subgoal ID with subgroup 1."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-existential-regexp nil
  "Regexp to match existential variables.
Existential variables exist for instance in Isabelle/Hol and in
Coq. They are placeholders for terms that might (for Coq they
must) get instantiated in a later stage of the proof. This regexp
should match one existential variable in subgroup 1. It is used
inside a while loop to extract all existential variables from the
goal text or from a list of existential variables.

Leave this variable at nil for proof assistants that do not have
existential variables."
  :type '(choice regexp (const nil))
  :group 'proof-tree-internals)

(defcustom proof-tree-existentials-state-start-regexp nil
  "Regexp to match the start of the state display of existential variables.
Together with `proof-tree-existentials-state-end-regexp', this
regular expression is used to determine the state display of
existential variables, which contains information about which
existentials are still uninstantiated and about dependencies of
instantiated existential variables. Leave this variable nil, if
there is no such state display."
  :type '(choice regexp (const nil))
  :group 'proof-tree-internals)

(defcustom proof-tree-existentials-state-end-regexp nil
  "Regexp to match the end of the state display of existential variables.
Together with `proof-tree-existentials-state-start-regexp', this
regular expression is used to determine the state display of
existential variables, which contains information about which
existentials are still uninstantiated and about dependencies of
instantiated existential variables. If this variable is nil (and
if `proof-tree-existentials-state-start-regexp' is non-nil), then
the state display expands to the end of the prover output."
  :type '(choice regexp (const nil))
  :group 'proof-tree-internals)

(defcustom proof-tree-proof-finished-regexp nil
  "Regexp to match the no-more-subgoals message."
  :type 'regexp
  :group 'proof-tree-internals)

(defcustom proof-tree-get-proof-info nil
  "Proof assistant specific function for information about the current proof.
This function takes no arguments. It must return a list, which
contains, in the following order:

* the current state number (as positive integer)
* the name of the current proof (as string) or nil

The state number is used to implement undo in prooftree. The
proof name is used to distinguish different proofs inside
prooftree.

The state number is interpreted as the state that has been
reached after the last command has been processed. It must be
consistent in the following sense. Firstly, it must be strictly
increasing for successive commands that can be individually
retracted. Secondly, the state number reported after some command
X has been processed must be strictly greater than the state
reported when X is retracted. Finally, state numbers of commands
preceding X must be less than or equal the state reported when X
is retracted (but no stuff before X)."
  :type 'function
  :group 'proof-tree-internals)

(defcustom proof-tree-extract-instantiated-existentials nil
  "Proof assistant specific function for instantiated existential variables.
This function must only be defined if the prover has existential
variables, that is, if `proof-tree-existential-regexp' is
non-nil.

If defined, this function should return the list of currently
instantiated existential variables as a list of strings. The
function is called with `proof-shell-buffer' as current
buffer and with two arguments start and stop, which designate the
region containing the last output from the proof assistant.

`proof-tree-extract-list' might be useful for writing this
function."
  :type '(choice function (const nil))
  :group 'proof-tree-internals)

(defcustom proof-tree-show-sequent-command nil
  "Proof assistant specific function for a show-goal command.
This function is applied to an ID of a goal and should return a
command (as string) that will display the complete sequent with
that ID. The regexp `proof-tree-update-goal-regexp' should match
the output of the proof assistant for the returned command, such
that `proof-tree-update-sequent' will update the sequent ID
inside prooftree.

If the proof assistant is unable to redisplay sequent ID the
function should return nil and prooftree will not get updated."
  :type 'function
  :group 'proof-tree-internals)

(defcustom proof-tree-find-begin-of-unfinished-proof nil
  "Proof assistant specific function for the start of the current proof.
This function is called with no argument when the user switches
the external proof-tree display on. Then, this function must
determine if there is a currently unfinished proof for which the
proof-tree display should be started. If yes this function must
return the starting position of the command that started this
proof. If there is no such proof, this function must return nil."
  :type 'function
  :group 'proof-tree-internals)

(defcustom proof-tree-urgent-action-hook ()
  "Normal hook for prooftree actions that cannot be delayed.
This hook is called (indirectly) from inside
`proof-shell-exec-loop' after the preceeding command and any
comments that follow have been choped off `proof-action-list' and
before the next command is sent to the proof assistant. This hook
can therefore be used to insert additional commands into
`proof-action-list' that must be executed before the next real
proof command.

Functions in this hook can rely on `proof-info' being bound to
the result of `proof-tree-get-proof-info'.

This hook is used, for instance, for Coq to insert Show commands
for newly generated subgoals. (The normal Coq output does not
contain the complete sequent text of newly generated subgoals.)"
  :type 'hook
  :group 'proof-tree-internals)


;;
;; Internal variables
;;

(defvar proof-tree-external-display nil
  "Display proof trees in external prooftree windows if t.
Actually, if this variable is t then the user requested an
external proof-tree display. If there was no unfinished proof
when proof-tree display was requested and if no proof has been
started since then, then there is obviously no proof-tree
display. In this case, this variable stays t and the proof-tree
display will be started for the next proof.

Controlled by `proof-tree-external-display-toggle'.")

(defvar proof-tree-process nil
  "Emacs lisp process object of the prooftree process.")

(defconst proof-tree-process-name "proof-tree"
  "Name of the prooftree process for Emacs lisp.")

(defconst proof-tree-process-buffer
  (concat "*" proof-tree-process-name "*")
  "Buffer for stdout and stderr of the prooftree process.")

(defconst proof-tree-emacs-exec-regexp
  "\nemacs exec: \\([-a-z]+\\) *\\([^\n]*\\)\n"
  "Regular expression to match callback commands from the prooftree process.")

(defvar proof-tree-last-state 0
  "Last state of the proof assistant.
Used for undoing in prooftree.")

(defvar proof-tree-current-proof nil
  "Name of the current proof or nil if there is none.
This variable is only maintained and meaningful if
`proof-tree-external-display' is t.")

(defvar proof-tree-sequent-hash nil
  "Hash table to remember sequent ID's.
Needed because some proof assistants do not distinguish between
new subgoals, which have been created by the last proof command,
and older, currently unfocussed subgoals. If Proof General meets
a goal, it is treated as new subgoal if it is not in this hash yet.

The hash is mostly used as a set of sequent ID's. However, for
undo operations it is necessary to delete all those sequents from
the hash that have been created in a state later than the undo
state. For this purpose this hash maps sequent ID's to the state
number in which the sequent has been created.

The hash table is initialized in `proof-tree-start-process'.")

(defvar proof-tree-existentials-alist nil
  "Alist mapping existential variables to sequent ID's.
Used to remember which goals need a refresh when an existential
variable gets instantiated. To support undo commands the old
contents of this list must be stored in
`proof-tree-existentials-alist-history'. To ensure undo is
properly working, this variable should only be changed by using
`proof-tree-delete-existential-assoc',
`proof-tree-add-existential-assoc' or
`proof-tree-clear-existentials'.")

(defvar proof-tree-existentials-alist-history nil
  "Alist mapping state numbers to old values of `proof-tree-existentials-alist'.
Needed for undo.")
  

;;
;; process filter function that receives prooftree output
;;

(defun proof-tree-stop-external-display ()
  "Prooftree callback for the command \"stop-displaying\"."
  (if proof-tree-current-proof
      (message "External proof-tree display switched off"))
  (proof-tree-quit-proof)
  (setq proof-tree-external-display nil))


(defun proof-tree-insert-output (string)
  "Insert output or a message into the prooftree process buffer."
  (with-current-buffer (get-buffer-create proof-tree-process-buffer)
    (let ((moving (= (point) (point-max))))
      (save-excursion
	;; Insert the text, advancing the process marker.
	(goto-char (point-max))
	(insert string))
      (if moving (goto-char (point-max))))))


(defun proof-tree-process-filter (proc string)
  "Output filter for prooftree.
Records the output in the prooftree process buffer and checks for
callback function requests."
  (proof-tree-insert-output string)
  (save-excursion
    (let ((start 0))
      (while (proof-string-match proof-tree-emacs-exec-regexp string start)
	(let ((end (match-end 0))
	      (cmd (match-string 1 string))
	      (data (match-string 2 string)))
	  (cond
	   ((equal cmd "stop-displaying")
	    (proof-tree-stop-external-display))
	   (t
	    (display-warning
	     '(proof-general proof-tree)
	     (format "Unknown prooftree command %s" cmd)
	     :warning)))
	  (setq start end))))))


;;
;; Process creation
;;

(defun proof-tree-process-sentinel (proc event)
  "Sentinel for prooftee.
Runs on process status changes and cleans up when prooftree dies."
  (proof-tree-insert-output (concat "\nsubprocess status change: " event))
  (unless (proof-tree-is-running)
    (proof-tree-stop-external-display)
    (setq proof-tree-process nil)))

(defun proof-tree-start-process ()
  "Start the external prooftree process.
Does also initialize the communication channel and some internal
variables."
  (let ((old-proof-tree (get-process proof-tree-process-name)))
    ;; first clean up any old processes
    (when old-proof-tree
      (delete-process old-proof-tree)
      (proof-tree-insert-output "\n\nProcess terminated by Proof General\n\n"))
    ;; now start the new process
    (proof-tree-insert-output "\nStart new prooftree process\n\n")
    (setq proof-tree-process
	  (apply 'start-process
	   proof-tree-process-name
	   proof-tree-process-buffer
	   proof-tree-program
	   proof-tree-arguments))
    (set-process-coding-system proof-tree-process 'utf-8-unix 'utf-8-unix)
    (set-process-filter proof-tree-process 'proof-tree-process-filter)
    (set-process-sentinel proof-tree-process 'proof-tree-process-sentinel)
    (set-process-query-on-exit-flag proof-tree-process nil)
    ;; other initializations
    (setq proof-tree-sequent-hash (make-hash-table :test 'equal)
	  proof-tree-last-state 0
	  proof-tree-existentials-alist nil
	  proof-tree-existentials-alist-history nil)
    (proof-tree-send-configure)))


(defun proof-tree-is-running ()
  "Return t if prooftree is properly running."
  (and proof-tree-process
       (eq (process-status proof-tree-process) 'run)))

(defun proof-tree-ensure-running ()
  "Ensure the prooftree process is running properly."
  (unless (proof-tree-is-running)
    (proof-tree-start-process)))


;;
;; Low-level communication primitives
;;

(defconst proof-tree-protocol-version 2
  "Version of the communication protocol between Proof General and Prooftree.
Must be increased if one of the low-level communication
primitives is changed.")

(defun proof-tree-send-message (second-line data)
  "Send a complete message to Prooftree.
Send a message with command line SECOND-LINE and all strings in
DATA as data sections to Prooftree."
  (let ((second-line-len (string-bytes second-line)))
    (assert (< second-line-len 999))
    (process-send-string
     proof-tree-process
     (format "second line %03d\n%s\n%s%s"
	     (1+ second-line-len)
	     second-line
	     (mapconcat 'identity data "\n")
	     (if data "\n" "")))))

(defun proof-tree-send-configure ()
  "Send the configure message."
  (proof-tree-send-message
   (format "configure for \"%s\" and protocol version %02d"
	   proof-assistant
	   proof-tree-protocol-version)
   ()))

(defun proof-tree-send-goal-state (state proof-name command-string cheated-flag
				   current-sequent-id current-sequent-text
				   additional-sequent-ids existential-info)
  "Send the current goal state to prooftree."
  ;; (message "PTSGS id %s sequent %s ex-info %s"
  ;; 	   current-sequent-id current-sequent-text existential-info)
  (let* ((add-id-string (mapconcat 'identity additional-sequent-ids " "))
	 (second-line
	  (format
	   (concat "current-goals state %d current-sequent %s %s "
		   "proof-name-bytes %d "
		   "command-bytes %d sequent-text-bytes %d "
		   "additional-id-bytes %d existential-bytes %d")
	   state
	   current-sequent-id
	   (if cheated-flag "cheated" "not-cheated")
	   (1+ (string-bytes proof-name))
	   (1+ (string-bytes command-string))
	   (1+ (string-bytes current-sequent-text))
	   (1+ (string-bytes add-id-string))
	   (1+ (string-bytes existential-info)))))
    (proof-tree-send-message
     second-line
     (list proof-name command-string current-sequent-text
	   add-id-string existential-info))))

(defun proof-tree-send-update-sequent (state proof-name sequent-id sequent-text)
  "Send the updated sequent text to prooftree."
  (let ((second-line
	 (format
	  (concat "update-sequent state %d sequent %s proof-name-bytes %d "
		  "sequent-text-bytes %d")
	  state sequent-id
	  (1+ (string-bytes proof-name))
	  (1+ (string-bytes sequent-text)))))
    (proof-tree-send-message
     second-line
     (list proof-name sequent-text))))

(defun proof-tree-send-switch-goal (proof-state proof-name current-id)
  "Send switch-to command to prooftree."
  (let ((second-line
	 (format "switch-goal state %d sequent %s proof-name-bytes %d"
		 proof-state
		 current-id
		 (1+ (string-bytes proof-name)))))
    (proof-tree-send-message second-line (list proof-name))))

(defun proof-tree-send-proof-finished (state proof-name cmd-string
					     cheated-flag existential-info)
  "Send proof-finished to prooftree."
  (proof-tree-send-message
   (format
    (concat "proof-finished state %d %s proof-name-bytes %d command-bytes %d "
	    "existential-bytes %d")
    state
    (if cheated-flag "cheated" "not-cheated")
    (1+ (string-bytes proof-name))
    (1+ (string-bytes cmd-string))
    (1+ (string-bytes existential-info)))
   (list proof-name cmd-string existential-info)))

(defun proof-tree-send-proof-complete (state proof-name)
  "Send proof-complete to prooftree."
  (proof-tree-send-message
   (format "proof-complete state %d proof-name-bytes %d"
	   state
	   (1+ (string-bytes proof-name)))
   (list proof-name)))

(defun proof-tree-send-undo (proof-state)
  "Tell prooftree to undo."
  (let ((second-line (format "undo-to state %d" proof-state)))
    (proof-tree-send-message second-line nil)))

(defun proof-tree-send-quit-proof (proof-name)
  "Tell prooftree to close the window for PROOF-NAME."
  (let ((second-line (format "quit-proof proof-name-bytes %d"
			    (1+ (string-bytes proof-name)))))
    (proof-tree-send-message second-line (list proof-name))))


;;
;; proof-tree-existentials-alist manipulations and history
;;

(defun proof-tree-record-existentials-state (state &optional dont-copy)
  "Store the current state of `proof-tree-existentials-alist' for undo.
Usually this involves making a copy of
`proof-tree-existentials-alist' because of the destructive
updates used on that list. If optional argument DONT-COPY is
non-nil no copy is done."
  (setq proof-tree-existentials-alist-history
	(cons (cons state
		    (if dont-copy
			 proof-tree-existentials-alist
		      (copy-alist proof-tree-existentials-alist)))
	      proof-tree-existentials-alist-history)))

(defun proof-tree-undo-state-var (proof-state var-symbol history-symbol)
  "Undo changes to VAR-SYMBOL using HISTORY-SYMBOL.
This is a general undo function for variables that keep their
undo information in a alist that maps state numbers to old
values. Argument PROOF-STATE is the state to reestablish,
VAR-SYMBOL is (the symbol of) the variable to undo and
HISTORY-SYMBOL is (the symbol of) the undo history alist."
  (let ((undo-not-finished t)
	(history (symbol-value history-symbol))
	(var (symbol-value var-symbol)))
    (while (and undo-not-finished history)
      (if (> (caar history) proof-state)
	  (progn
	    (setq var (cdr (car history)))
	    (setq history (cdr history)))
	(setq undo-not-finished nil)))
    (set var-symbol var)
    (set history-symbol history)))

(defun proof-tree-undo-existentials (proof-state)
  "Undo changes in `proof-tree-existentials-alist'.
Change `proof-tree-existentials-alist' back to its contents in
state PROOF-STATE."
  (proof-tree-undo-state-var proof-state
			     'proof-tree-existentials-alist
			     'proof-tree-existentials-alist-history))

(defun proof-tree-delete-existential-assoc (state ex-assoc)
  "Delete mapping EX-ASSOC from 'proof-tree-existentials-alist'."
  (proof-tree-record-existentials-state state)
  (setq proof-tree-existentials-alist
	(delq ex-assoc proof-tree-existentials-alist)))
  
(defun proof-tree-add-existential-assoc (state ex-var sequent-id)
  "Add the mapping EX-VAR -> SEQUENT-ID to 'proof-tree-existentials-alist'.
Do nothing if this mapping does already exist."
  (let ((ex-var-assoc (assoc ex-var proof-tree-existentials-alist)))
    (if ex-var-assoc
	(unless (member sequent-id (cdr ex-var-assoc))
	  (proof-tree-record-existentials-state state)
	  (setcdr ex-var-assoc (cons sequent-id (cdr ex-var-assoc))))
      (proof-tree-record-existentials-state state)
      (setq proof-tree-existentials-alist
	    (cons (cons ex-var (list sequent-id))
		  proof-tree-existentials-alist)))))

(defun proof-tree-clear-existentials ()
  "Clear the mapping in `proof-tree-existentials-alist' and its history."
  (setq proof-tree-existentials-alist nil)
  (setq proof-tree-existentials-alist-history nil))


;;
;; Process urgent output from the proof assistant
;;

(defun proof-tree-show-goal-callback (state)
  "Callback for display-goal commands inserted by this package.
Update the sequent and run hooks in `proof-state-change-hook'.
Argument STATE is the state number (i.e., an integer) with which
the update sequent command should be associated.

The STATE is necessary, because a comment following a branching
command cat get retired together with the branching command
before the show-goal commands that update sequents are processed.
The effect of the sequent update would therefore be undone when
the comment alone is retracted.

You CANNOT put this function directly as callback into
`proof-action-list' because callbacks receive the span as
argument and this function expects an integer! Rather you should
call `proof-tree-make-show-goal-callback', which evaluates to a
lambda expressions that you can put into `proof-action-list'."
  ;;(message "PTSGC %s" state)
  (proof-tree-update-sequent state)
  (run-hooks 'proof-state-change-hook))

(defun proof-tree-make-show-goal-callback (state)
  "Create the callback for display-goal commands."
  `(lambda (span) (proof-tree-show-goal-callback ,state)))

(defun proof-tree-urgent-action (flags)
  "Handle urgent points before the next item is sent to the proof assistant.
Schedule goal updates when existential variables have changed and
call `proof-tree-urgent-action-hook'. All this is only done if
the current output does not come from a command (with the
'proof-tree-show-subgoal flag) that this package inserted itself.

Urgent actions are only needed if the external proof display is
currently running. Therefore this function should not be called
when `proof-tree-external-display' is nil. 

This function assumes that the prover output is not suppressed.
Therefore, `proof-tree-external-display' being t is actually a
necessary precondition.

The not yet delayed output is in the region
\[proof-shell-delayed-output-start, proof-shell-delayed-output-end]."
  ;; (message "PTUA flags %s start %s end %s pal %s ptea %s"
  ;; 	   flags
  ;; 	   proof-shell-delayed-output-start
  ;; 	   proof-shell-delayed-output-end
  ;; 	   proof-action-list
  ;; 	   proof-tree-existentials-alist)
  (let* ((proof-info (funcall proof-tree-get-proof-info))
	 (state (car proof-info))
	 (start proof-shell-delayed-output-start)
	 (end proof-shell-delayed-output-end)
	 inst-ex-vars)
    (when (and (not (memq 'proof-tree-show-subgoal flags))
	       (> state proof-tree-last-state))
      ;; Only deal with existentials if the proof assistant has them
      ;; (i.e., proof-tree-existential-regexp is set) and if there are some
      ;; goals with existentials.
      (when (and proof-tree-existential-regexp
		 proof-tree-existentials-alist)
	(setq inst-ex-vars
	      (with-current-buffer proof-shell-buffer
		(funcall proof-tree-extract-instantiated-existentials
			 start end)))
	(dolist (ex-var inst-ex-vars)
	  (let ((var-goal-assoc (assoc ex-var proof-tree-existentials-alist)))
	    (when var-goal-assoc
	      (dolist (sequent-id (cdr var-goal-assoc))
		(let ((show-cmd
		       (funcall proof-tree-show-sequent-command sequent-id)))
		  (if show-cmd
		      (setq proof-action-list
			    (cons (proof-shell-action-list-item
				   show-cmd
				   (proof-tree-make-show-goal-callback state)
				   '(no-goals-display no-response-display
				     proof-tree-show-subgoal))
				  proof-action-list)))))
	      (proof-tree-delete-existential-assoc state var-goal-assoc)))))
      (run-hooks 'proof-tree-urgent-action-hook))
    ;; (message "PTUA END pal %s ptea %s"
    ;; 	   proof-action-list
    ;; 	   proof-tree-existentials-alist)
  ))


;;
;; Process output from the proof assistant
;;

(defun proof-tree-quit-proof ()
  "Reset internal state when there is no current proof any more.
Because currently it is not possible to undo into the middle of a
proof, we can safely flush the `proof-tree-sequent-hash' and
`proof-tree-existentials-alist-history' when the current proof is
finished or quit."
  (clrhash proof-tree-sequent-hash)
  (proof-tree-clear-existentials)
  (setq proof-tree-current-proof nil))

(defun proof-tree-register-existentials (current-state sequent-id sequent-text)
  "Register existential variables that appear in SEQUENT-TEXT.
If SEQUENT-TEXT contains existential variables, then SEQUENT-ID
is stored in `proof-tree-existentials-alist'."
  (if proof-tree-existential-regexp
      (let ((start 0))
	(while (proof-string-match proof-tree-existential-regexp
				   sequent-text start)
	  (setq start (match-end 0))
	  (proof-tree-add-existential-assoc current-state
					    (match-string 1 sequent-text)
					    sequent-id)))))

(defun proof-tree-extract-goals (start end)
  "Extract the current goal state information from the delayed output.
If there is a current goal, return a list containing (in
this order) the ID of the current sequent, the text of the
current sequent and the list of ID's of additionally open goals.
The delayed output is expected between START and END in the
current buffer."
  (goto-char start)
  (if (proof-re-search-forward proof-tree-current-goal-regexp end t)
      (let ((sequent-id (match-string-no-properties 1))
	    (sequent-text (match-string-no-properties 2))
	    additional-goal-ids)
	(goto-char start)
	(while (proof-re-search-forward proof-tree-additional-subgoal-ID-regexp
					end t)
	  (let ((other-id (match-string-no-properties 1)))
	    (setq additional-goal-ids (cons other-id additional-goal-ids))))
	(setq additional-goal-ids (nreverse additional-goal-ids))
	(list sequent-id sequent-text additional-goal-ids))
    nil))


(defun proof-tree-extract-list (start end start-regexp end-regexp item-regexp)
  "Extract items between START-REGEXP and END-REGEXP.
In the region given by START and END, determine the subregion
between START-REGEXP and END-REGEXP and return the list of all
items in the subregion. An item is a match of subgroub 1 of
ITEM-REGEXP. The items in the returned list have the same order
as in the text.

Return nil if START-REGEXP or ITEM-REGEXP is nil. The subregion
extends up to END if END-REGEXP is nil."
  (let (result)
    (when (and start-regexp item-regexp)
      (goto-char start)
      (when (proof-re-search-forward start-regexp end t)
	(setq start (point))
	(if (and end-regexp (proof-re-search-forward end-regexp end t))
	    (setq end (match-beginning 0)))
	(goto-char start)
        (while (proof-re-search-forward item-regexp end t)
          (setq result (cons (match-string-no-properties 1)
                             result)))))
    (nreverse result)))

(defun proof-tree-extract-existential-info (start end)
  "Extract the information display of existential variables.
This function cuts out the text between
`proof-tree-existentials-state-start-regexp' and
`proof-tree-existentials-state-end-regexp' from the prover
output, including the matches of these regular expressions. If
the start regexp is nil, the empty string is returned. If the end
regexp is nil, the match expands to the end of the prover output."
  (if (and proof-tree-existentials-state-start-regexp
	   (proof-re-search-forward proof-tree-existentials-state-start-regexp
				    end t))
      (progn
	(setq start (match-beginning 0))
	(when (and proof-tree-existentials-state-end-regexp
		   (proof-re-search-forward
		    proof-tree-existentials-state-end-regexp end t))
	  (setq end (match-end 0)))
	(buffer-substring-no-properties start end))
    ""))

(defun proof-tree-handle-proof-progress (cmd-string proof-info)
  "Send CMD-STRING and goals in delayed output to prooftree.
This function is called if there is some real progress in a
proof. This function sends the current state, the current goal
and the list of additional open subgoals to Prooftree. Prooftree
will sort out the rest.

The delayed output is in the region
\[proof-shell-delayed-output-start, proof-shell-delayed-output-end]."
  ;; (message "PTHPO cmd |%s| info %s flags %s start %s end %s"
  ;; 	   cmd proof-info flags
  ;; 	   proof-shell-delayed-output-start
  ;; 	   proof-shell-delayed-output-end)
  (let* ((start proof-shell-delayed-output-start)
	 (end   proof-shell-delayed-output-end)
	 (proof-state (car proof-info))
	 (proof-name (cadr proof-info))
	 (cheated-flag
	  (and proof-tree-cheating-regexp
	       (proof-string-match proof-tree-cheating-regexp cmd-string)))
	 (current-goals (proof-tree-extract-goals start end))
	 (existential-info
	  (proof-tree-extract-existential-info start end)))
    (if current-goals
	(let ((current-sequent-id (car current-goals))
	      (current-sequent-text (nth 1 current-goals))
	      ;; nth 2 current-goals  contains the  additional ID's
	      )
	  ;; send all to prooftree
	  (proof-tree-send-goal-state
	   proof-state proof-name cmd-string
	   cheated-flag
	   current-sequent-id
	   current-sequent-text
	   (nth 2 current-goals)
	   existential-info)
	  ;; put current sequent into hash (if it is not there yet)
	  (unless (gethash current-sequent-id proof-tree-sequent-hash)
	    (puthash current-sequent-id proof-state proof-tree-sequent-hash))
	  (proof-tree-register-existentials proof-state
					    current-sequent-id
					    current-sequent-text))
      
      ;; no current goal found, maybe the proof has been finished?
      (goto-char start)
      (if (proof-re-search-forward proof-tree-proof-finished-regexp end t)
	  (progn
	    (proof-tree-send-proof-finished
	     proof-state proof-name cmd-string
	     cheated-flag existential-info))))))

(defun proof-tree-handle-navigation (proof-info)
  "Handle a navigation command.
This function is called if there was a navigation command, which
results in a different goal being current now.

The delayed output of the navigation command is in the region
\[proof-shell-delayed-output-start, proof-shell-delayed-output-end]."
  (let ((start proof-shell-delayed-output-start)
	(end   proof-shell-delayed-output-end)
	(proof-state (car proof-info))
	(proof-name (cadr proof-info)))
    (goto-char start)
    (if (proof-re-search-forward proof-tree-current-goal-regexp end t)
	(let ((current-id (match-string-no-properties 1)))
	  ;; send all to prooftree
	  (proof-tree-send-switch-goal proof-state proof-name current-id)))))


(defun proof-tree-handle-proof-command (cmd proof-info)
  "Display current goal in prooftree unless CMD should be ignored."
  ;; (message "PTHPC")
  (let ((proof-state (car proof-info))
	(cmd-string (mapconcat 'identity cmd " ")))
    (unless (and proof-tree-ignored-commands-regexp
		 (proof-string-match proof-tree-ignored-commands-regexp
				     cmd-string))
      (if (and proof-tree-navigation-command-regexp
	       (proof-string-match proof-tree-navigation-command-regexp
				   cmd-string))
	  (proof-tree-handle-navigation proof-info)
	(proof-tree-handle-proof-progress cmd-string proof-info)))
    (setq proof-tree-last-state (car proof-info))))
    
(defun proof-tree-handle-undo (proof-info)
  "Undo prooftree to current state.
Send the undo command to prooftree and undo changes to the
internal state of this package. The latter involves currently two
points:
* delete those goals from `proof-tree-sequent-hash' that have
  been generated after the state to which we undo now
* change proof-tree-existentials-alist back to its previous content"
  ;; (message "PTHU info %s" proof-info)
  (let ((proof-state (car proof-info)))
    ;; delete sequents from the hash
    (maphash
     (lambda (sequent-id state)
       (if (> state proof-state)
	   (remhash sequent-id proof-tree-sequent-hash)))
     proof-tree-sequent-hash)
    ;; undo changes in other state vars
    (proof-tree-undo-existentials proof-state)
    (unless (equal (cadr proof-info) proof-tree-current-proof)
      ;; went back to a point before the start of the proof that we
      ;; are displaying;
      ;; or we have not started to display something
      (proof-tree-quit-proof))
    ;; disable proof tree display when undoing to a point outside a proof
    (unless proof-tree-current-proof
      (setq proof-tree-external-display nil))
    ;; send undo
    (if (proof-tree-is-running)
	(proof-tree-send-undo proof-state))
    (setq proof-tree-last-state (- proof-state 1))))


(defun proof-tree-update-sequent (proof-state)
  "Prepare an update-sequent command for prooftree.
This function processes delayed output that the proof assistant
generated in response to commands that Proof General inserted in
order to keep prooftree up-to-date. Such commands are tagged with
a 'proof-tree-show-subgoal flag.

This function uses `proof-tree-update-goal-regexp' to find a
sequent and its ID in the delayed output. If something is found
an appropriate update-sequent command is sent to prooftree.

The update-sequent command is associated with state PROOF-STATE
for proper undo effects, see also the comments for
`proof-tree-show-goal-callback'.

The delayed output is in the region
\[proof-shell-delayed-output-start, proof-shell-delayed-output-end]."
  ;; (message "PTUS buf %s output %d-%d state %s"
  ;; 	   (current-buffer)
  ;; 	   proof-shell-delayed-output-start proof-shell-delayed-output-end
  ;; 	   proof-state)
  (if (proof-tree-is-running)
      (with-current-buffer proof-shell-buffer
	(let* ((start proof-shell-delayed-output-start)
	       (end   proof-shell-delayed-output-end)
	       (proof-info (funcall proof-tree-get-proof-info))
	       (proof-name (cadr proof-info)))
	  (goto-char start)
	  (if (proof-re-search-forward proof-tree-update-goal-regexp end t)
	      (let ((sequent-id (match-string-no-properties 1))
		    (sequent-text (match-string-no-properties 2)))
		(proof-tree-send-update-sequent
		 proof-state proof-name sequent-id sequent-text)
		;; put current sequent into hash (if it is not there yet)
		(unless (gethash sequent-id proof-tree-sequent-hash)
		  (puthash sequent-id proof-state proof-tree-sequent-hash))
		(proof-tree-register-existentials proof-state
						  sequent-id
						  sequent-text)))))))


(defun proof-tree-handle-delayed-output (cmd flags span)
  "Process delayed output for prooftree.
This function is the main entry point of the Proof General
prooftree support. It examines the delayed output in order to
take appropriate actions and maintains the internal state.

All arguments are (former) fields of the `proof-action-list'
entry that is now finally retired. CMD is the command, FLAGS are
the flags and SPAN is the span."
  ;; (message "PTHDO cmd %s flags %s span %s-%s" cmd flags
  ;; 	   (if span (span-start span)) (if span (span-end span)))
  (assert proof-tree-external-display)
  (unless (or (memq 'invisible flags) (memq 'proof-tree-show-subgoal flags))
    (let* ((proof-info (funcall proof-tree-get-proof-info))
	   (current-proof-name (cadr proof-info)))
      (save-excursion
	(if (<= (car proof-info) proof-tree-last-state)
	    ;; went back to some old state: there must have been an undo command
	    (proof-tree-handle-undo proof-info)

	  ;; else -- no undo command
	  ;; first maintain proof-tree-current-proof
	  (cond
	   ((and (null proof-tree-current-proof) current-proof-name)
	    ;; started a new proof
	    (setq proof-tree-current-proof current-proof-name))
	   ((and proof-tree-current-proof (null current-proof-name))
	    ;; finished the current proof
	    (proof-tree-send-proof-complete (car proof-info)
					    proof-tree-current-proof)
	    (proof-tree-quit-proof)
	    (setq proof-tree-external-display nil))
	   ((and proof-tree-current-proof current-proof-name
		 (not (equal proof-tree-current-proof current-proof-name)))
	    ;; new proof before old was finished?
	    (display-warning
	     '(proof-general proof-tree)
	     "Nested proofs are not supported in prooftree display"
	     :warning)
	    ;; try to keep consistency nevertheless
	    (setq proof-tree-current-proof current-proof-name)))

	  ;; send stuff to prooftree now
	  (when current-proof-name
	    ;; we are inside a proof: display something
	    (proof-tree-ensure-running)
	    (proof-tree-handle-proof-command cmd proof-info)))))))


;;
;; Send undo command when leaving a buffer
;;

(defun proof-tree-leave-buffer ()
  "Send an undo command to prooftree when leaving a buffer."
  (if (and proof-tree-configured (proof-tree-is-running))
      (proof-tree-send-undo 0)))

(add-hook 'proof-deactivate-scripting-hook 'proof-tree-leave-buffer)


;;
;; User interface
;;

(defun proof-tree-display-current-proof (proof-start)
  "Start an external proof-tree display for the current proof.
Coq (and probably other proof assistants as well) does not
support outputing the current proof tree. Therefore this function
retracts to the start of the current proof, switches the
proof-tree display on, and reasserts then until the former end of
the locked region. Argument PROOF-START must contain the start
position of the current proof."
  ;;(message "PTDCP %s" proof-tree-external-display)
  (unless (and proof-script-buffer
	       (equal proof-script-buffer (current-buffer)))
    (error
     "Enabling prooftree inside a proof outside the current scripting buffer"))
  (proof-shell-ready-prover)
  (assert proof-locked-span)
  (message "Start proof-tree display for current proof")
  (save-excursion
    (save-window-excursion
      (let ((locked-end (span-end proof-locked-span)))
	(goto-char proof-start)
	;; enable external display to make sure the undo command is send
	(setq proof-tree-external-display t)
	(proof-retract-until-point)
	(while (consp proof-action-list)
	  (accept-process-output))
	;; undo switched external display off; switch on again
	(setq proof-tree-external-display t)
	(goto-char locked-end)
	(proof-assert-until-point)
	(while (consp proof-action-list)
	  (accept-process-output))))))

(defun proof-tree-external-display-toggle ()
  "Toggle the external proof-tree display.
When called outside a proof the external proof-tree display will
be enabled for the next proof. When called inside a proof the
proof display will be created for the current proof. If the
external proof-tree display is currently on, then this toggle
will switch it off. At the end of the proof the proof-tree
display is switched off."
  (interactive)
  (unless proof-tree-configured
    (error "External proof-tree display not configured for %s" proof-assistant))
  (cond
   (proof-tree-external-display
    ;; Currently on -> switch off
    (setq proof-tree-external-display nil)
    (when proof-tree-current-proof
      (proof-tree-send-quit-proof proof-tree-current-proof)
      (proof-tree-quit-proof))
    (message "External proof-tree display switched off"))
   (t
    ;; Currently off
    (let ((proof-start (funcall proof-tree-find-begin-of-unfinished-proof)))
      ;; ensure internal variables are initialized, because otherwise
      ;; we cannot process undo's after this
      (proof-tree-ensure-running)
      (setq proof-tree-current-proof nil)
      (setq proof-tree-last-state (car (funcall proof-tree-get-proof-info)))
      (if proof-start
	  ;; inside an unfinished proof -> start for this proof
	  (proof-tree-display-current-proof proof-start)
	;; outside a proof -> wait for the next proof
	(setq proof-tree-external-display t)
	(proof-tree-send-undo proof-tree-last-state)
	(message
	 "External proof-tree display switched on for the next proof"))))))
    

;;
;; Trailer
;; 

(provide 'proof-tree)

;;; tree-tree.el ends here
