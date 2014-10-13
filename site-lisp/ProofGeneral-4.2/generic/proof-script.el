;;; proof-script.el --- Major mode for proof assistant script files.
;;
;; Copyright (C) 1994-2010 LFCS Edinburgh.
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; proof-script.el,v 12.5 2012/08/16 15:01:05 da Exp
;;
;;; Commentary:
;;
;; This implements the main mode for script management, including
;; parsing script buffers and setting spans inside them.
;;
;; Compile note: functions used here from proof-shell, pg-user,
;; pg-response, pg-goals auto-loaded to prevent circular dependency.

;;; Code:

(require 'cl)				; various
(require 'span)				; abstraction of overlays/extents
(require 'proof-utils)			; proof-utils macros
(require 'proof-syntax)			; utils for manipulating syntax

(eval-when-compile
  (require 'easymenu)
  (defvar proof-mode-menu nil)
  (defvar proof-assistant-menu nil))

(declare-function proof-shell-strip-output-markup "proof-shell"
		  (string &optional push))
(declare-function proof-shell-make-associated-buffers "proof-shell" ())
(declare-function proof-layout-windows "pg-response" (&rest args))
(declare-function pg-response-warning "pg-response" (&rest args))
(declare-function proof-segment-up-to "proof-script")
(declare-function proof-autosend-enable "pg-user")
(declare-function proof-interrupt-process "pg-shell")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  PRIVATE VARIABLES
;;
;;  Local variables used by proof-script-mode
;;

;; Buffer-local variables

(deflocal proof-active-buffer-fake-minor-mode nil
  "An indication in the modeline that this is the *active* script buffer")

(deflocal proof-script-buffer-file-name nil
  ;; NB: if buffer-file-name is nil for some other reason, this may break.
   "A copied value of buffer-file-name to cope with `find-alternative-file'.
The `find-alternative-file' function has a nasty habit of setting the
buffer file name to nil before running kill buffer, which breaks PG's
kill buffer hook.  This variable is used when buffer-file-name is nil.")

(deflocal pg-script-portions nil
  "Alist of hash tables for symbols naming processed script portions.")

(defalias 'proof-active-buffer-fake-minor-mode
  'proof-toggle-active-scripting)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Counting and naming proof elements
;;

(defun proof-next-element-count (idiom)
  "Return count for next element of type IDIOM.
This uses the size of the hash table for IDIOM."
  (let ((tbl  (cdr-safe (assq idiom pg-script-portions))))
    (if tbl (1+ (hash-table-count tbl)) 1)))

(defun proof-element-id (idiom number)
  "Return a string identifier composed from symbol IDIOM and NUMBER."
  (concat (symbol-name idiom) "-" (int-to-string number)))

(defun proof-next-element-id (idiom)
  "Return a string suitable for naming the next element of type IDIOM."
  (proof-element-id idiom (proof-next-element-count idiom)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Basic functions for handling the locked and queue regions
;;
;; --------------------------------------------------------------
;;
;; Notes on regions in the scripting buffer. (da)
;;
;; The locked region is covered by a collection of non-overlaping
;; spans (spans are our abstraction of extents/overlays).
;;
;; Each span has a 'type property, one of:
;;
;;  'goalsave     A goal..savegoal region in the buffer, a completed proof.
;;  'vanilla      Initialised in proof-semis-to-vanillas, for
;;  'comment      A comment outside a command.
;;  'proverproc   A region closed by the prover, processed outwith PG
;;  'pbp	  A PBP command inserted automatically into the script
;;
;; For an unfinished proof, there is one extent for each command
;; or comment outside a command.   For a finished proof, there
;; is one extent for the whole proof.
;;
;;  A spans corresponding to a command has a 'cmd property, which is set
;;  to a string of its command.  This is the text in the buffer
;;  stripped of leading whitespace and any comments.
;;

;; ** Variables

(deflocal proof-locked-span nil
  "The locked span of the buffer.
Each script buffer has its own locked span, which may be detached
from the buffer.
Proof General allows buffers in other modes also to be locked;
these also have a non-nil value for this variable.")

(deflocal proof-queue-span nil
  "The queue span of the buffer.  May be detached if inactive or empty.
Each script buffer has its own queue span, although only the active
scripting buffer may have an active queue span.")
;; da: reason for buffer local queue span is because initialisation
;; in proof-init-segmentation can happen when a file is visited.
;; So nasty things might happen if a locked file is visited whilst
;; another buffer has a non-empty queue region being processed.

(deflocal proof-overlay-arrow nil
  "Marker holding the overlay arrow position for this buffer.")


;; ** Getters and setters

(defun proof-span-give-warning (&rest args)
  "Give a warning message.
Optional argument ARGS is ignored."
  (unless inhibit-read-only
    (message "You should not edit here!")))

(defun proof-span-read-only (span &optional always)
  "Make SPAN read-only, following variable `proof-strict-read-only' or ALWAYS."
  (if (or always (not (memq proof-strict-read-only '(nil retract))))
      (span-read-only span)
    (span-write-warning span
			(if (eq proof-strict-read-only 'retract)
			    'proof-retract-before-change
			  'proof-span-give-warning))))

(defun proof-strict-read-only ()
  "Set spans read-only according to variable `proof-strict-read-only'.
Action is taken on all script buffers."
  ;; NB: read-only is synchronized in all script buffers
  (interactive)
  (proof-map-buffers
   (proof-buffers-in-mode proof-mode-for-script)
   (if (span-live-p proof-locked-span)
       (proof-span-read-only proof-locked-span))))

(defsubst proof-set-queue-endpoints (start end)
  "Set the queue span to be START, END."
  (span-set-endpoints proof-queue-span start end))

(defun proof-set-overlay-arrow (pos)
  "Set the position of the overlay marker to POS."
  (and (markerp proof-overlay-arrow)
       (set-marker proof-overlay-arrow
		   (save-excursion
		     (goto-char pos)
		     (skip-chars-forward " \t\s\n")
		     (unless (eq (point) (point-max))
		       (beginning-of-line)
		       (point))))))

(defsubst proof-set-locked-endpoints (start end)
  "Set the locked span to be START, END."
  (span-set-endpoints proof-locked-span start end)
  (proof-set-overlay-arrow end))

(defsubst proof-detach-queue ()
  "Remove the span for the queue region."
  (and proof-queue-span
       (span-detach proof-queue-span)))

(defsubst proof-detach-locked ()
  "Remove the span for the locked region."
  (and proof-locked-span
       (span-detach proof-locked-span))
  (and (markerp proof-overlay-arrow)
       (set-marker proof-overlay-arrow nil)))

(defsubst proof-set-queue-start (start)
  "Set the queue span to begin at START."
  (span-set-start proof-queue-span start))

(defsubst proof-set-locked-end (end)
  "Set the end of the locked region to be END.
If END is at or before (point-min), remove the locked region.
Otherwise set the locked region to be from (point-min) to END."
  (if (>= (point-min) end)
      ;; Detach queue span, otherwise may have read-only character at end.
      (proof-detach-locked)
    (proof-set-locked-endpoints
     (point-min)
      ;; safety in case called with end>point-max
     (min (point-max) end))))

(defsubst proof-set-queue-end (end)
  "Set the queue span to end at END."
  (if (or (>= (point-min) end)
	  (not (span-live-p  proof-queue-span))
	  (<= end (span-start proof-queue-span)))
      (proof-detach-queue)
    (span-set-end proof-queue-span end)))


;; ** Initialise spans for a buffer

(defun proof-init-segmentation ()
  "Initialise the queue and locked spans in a proof script buffer.
Allocate spans if need be.  The spans are detached from the
buffer, so the regions are made empty by this function.
Also clear list of script portions."
  ;; Initialise queue span, remove it from buffer.
  (unless proof-queue-span
    (setq proof-queue-span (span-make 1 1))
    (span-raise proof-queue-span))
  (span-set-property proof-queue-span 'start-closed t)
  (span-set-property proof-queue-span 'end-open t)
  (proof-span-read-only proof-queue-span 'always)
  (span-set-property proof-queue-span 'face 'proof-queue-face)
  (span-detach proof-queue-span)
  ;; Initialise locked span, remove it from buffer
  (unless proof-locked-span
      (setq proof-locked-span (span-make 1 1))
      (span-raise proof-locked-span))
  (span-set-property proof-locked-span 'start-closed t)
  (span-set-property proof-locked-span 'end-open t)
  (proof-span-read-only proof-locked-span)
  (proof-colour-locked-span)
  (span-detach proof-locked-span)
  (setq proof-overlay-arrow (make-marker))
  (setq overlay-arrow-position proof-overlay-arrow)
  (setq proof-last-theorem-dependencies nil)
  (pg-clear-script-portions)
  (pg-clear-input-ring))

;;;###autoload
(defun proof-colour-locked ()
  "Alter the colour of all locked regions according to variable `proof-colour-locked'."
  (interactive)
  (proof-map-buffers (proof-buffers-in-mode proof-mode-for-script)
   (and (span-live-p proof-locked-span)
	(proof-colour-locked-span))))

(defun proof-colour-locked-span ()
  "Alter the colour of the locked region according to variable `proof-colour-locked'."
  (if proof-colour-locked
      (span-set-property proof-locked-span 'face 'proof-locked-face)
    (span-set-property  proof-locked-span 'face nil)))

(defun proof-sticky-errors ()
  "Alter the colour of sticky errors to match `proof-sticky-errors'.
This function is not yet implemented, so the colouring will stay
in effect until the regions are next cleared, or only be added the
next time an error is processed."
  ;; TODO: we need to tag spans separately as error spans, and
  ;; map over all spans in all buffers.
  )
  
  

;; ** Restarting and clearing spans

(defun proof-restart-buffers (buffers)
  "Remove all extents in BUFFERS and maybe reset `proof-script-buffer'.
The high-level effect is that all members of BUFFERS are
completely unlocked, including all the necessary cleanup. No
effect on a buffer which is nil or killed. If one of the buffers
is the current scripting buffer, then `proof-script-buffer' will
deactivated."
  (mapcar
   (lambda (buffer)
     (save-excursion
       (if (buffer-live-p buffer)
	   (with-current-buffer buffer
	     (if proof-active-buffer-fake-minor-mode
		 (setq proof-active-buffer-fake-minor-mode nil))
	     (proof-script-delete-spans (point-min) (point-max))
	     (proof-script-delete-secondary-spans (point-min) (point-max))
	     (setq pg-script-portions nil)
	     (proof-detach-queue)
	     (proof-detach-locked)
	     (proof-init-segmentation)))
       (if (eq buffer proof-script-buffer)
	   (setq proof-script-buffer nil))))
   buffers))

(defun proof-script-buffers-with-spans ()
  "Return a list of all buffers with spans.
This is calculated by finding all the buffers with a non-nil
value of proof-locked span."
  (let ((bufs-left (buffer-list))
	bufs-got)
    (dolist (buf bufs-left bufs-got)
      (if (with-current-buffer buf proof-locked-span)
	  (setq bufs-got (cons buf bufs-got))))))

(defun proof-script-remove-all-spans-and-deactivate ()
  "Remove all spans from scripting buffers via `proof-restart-buffers'."
  (proof-restart-buffers (proof-script-buffers-with-spans)))

(defun proof-script-clear-queue-spans-on-error (badspan &optional interruptp)
  "Remove the queue span from buffer, cleaning spans no longer queued.
If BADSPAN is non-nil, assume that this was the span whose command
caused the error.  Go to the start of it if `proof-follow-mode' is
'locked.

If INTERRUPTP is non-nil, do not consider BADSPAN itself as faulty.

This is a subroutine used in proof-shell-handle-{error,interrupt}."
    (let ((start (proof-unprocessed-begin))
	  (end   (proof-queue-or-locked-end))
	  (infop (span-live-p badspan)))
      (proof-detach-queue)
      (when infop
	(unless proof-autosend-running
	  (when (eq proof-follow-mode 'locked)
	    ;; jump to start of error: should this be configurable?
	    (goto-char (span-start badspan))
	    (skip-chars-forward " \t\n")))
	(unless interruptp
	  (when proof-sticky-errors
	    (pg-set-span-helphighlights badspan
					'proof-script-highlight-error-face
					'proof-script-sticky-error-face))))
      (proof-script-delete-spans start end)))

(defun proof-script-delete-spans (beg end)
  "Delete primary spans between BEG and END.  Secondary 'pghelp spans are left."
  (span-delete-spans beg end 'type)
  (span-delete-spans beg end 'idiom))

(defun proof-script-delete-secondary-spans (beg end)
  "Delete secondary spans between BEG and END (currently, 'pghelp spans)."
  (span-delete-spans beg end 'pghelp))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Buffer position functions
;;

;;;###autoload
(defun proof-unprocessed-begin ()
  "Return end of locked region in current buffer or (point-min) otherwise.
The position is actually one beyond the last locked character."
  (or
   (and proof-locked-span
	(span-end proof-locked-span))
   (point-min)))

(defun proof-script-end ()
  "Return the character beyond the last non-whitespace character.
This is the same position `proof-unprocessed-begin' ends up at when asserting
the script.  Works for any kind of buffer."
  (save-excursion
    (goto-char (point-max))
    (skip-chars-backward " \t\n")
    (point)))

(defun proof-queue-or-locked-end ()
  "Return the end of the queue region, or locked region, or (point-min).
This position should be the first writable position in the buffer.
An appropriate point to move point to (or make sure is displayed)
when a queue of commands is being processed."
  (or
   ;; span-end returns nil if span is detached
   (and proof-queue-span (span-end proof-queue-span))
   (and proof-locked-span (span-end proof-locked-span))
   (point-min)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Predicates for locked region.
;;

;;;###autoload
(defun proof-locked-region-full-p ()
  "Non-nil if the locked region covers all the buffer's non-whitespace.
Works on any buffer."
  (save-excursion
    (goto-char (point-max))
    (skip-chars-backward " \t\n")
    (>= (proof-unprocessed-begin) (point))))

;;;###autoload
(defun proof-locked-region-empty-p ()
  "Non-nil if the locked region is empty.  Works on any buffer."
  (eq (proof-unprocessed-begin) (point-min)))

(defun proof-only-whitespace-to-locked-region-p ()
  "Non-nil if only whitespace from char-after point and end of locked region.
Point must be after the locked region or this will signal an error."
  (save-excursion
    (or (eq (point) (point-max))
	(forward-char 1))
    (not (proof-re-search-backward
	  "\\S-"
	  (proof-unprocessed-begin) t))))

(defun proof-in-locked-region-p ()
  "Non-nil if point is in locked region.  Assumes script buffer current."
  (< (point) (proof-unprocessed-begin)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Misc movement functions
;;

(defun proof-goto-end-of-locked (&optional switch)
  "Jump to the end of the locked region, maybe switching to script buffer.
If called interactively or SWITCH is non-nil, switch to script buffer.
If called interactively, a mark is set at the current location with `push-mark'"
  (interactive)
  (if (and proof-script-buffer (called-interactively-p 'any))
      (push-mark))
  (proof-with-script-buffer
   (if ;; there is an active scripting buffer and it's not displayed
       (and proof-script-buffer
	    (not (get-buffer-window proof-script-buffer))
	    (or switch (called-interactively-p 'any)))
       ;; display it
       (switch-to-buffer proof-script-buffer))
   (goto-char (proof-unprocessed-begin))))

;; Careful: movement can happen when the user is typing, not very nice!
(defun proof-goto-end-of-locked-if-pos-not-visible-in-window ()
  "If the end of the locked region is not visible, jump to the end of it.
A possible hook function for `proof-shell-handle-error-or-interrupt-hook'.
Does nothing if there is no active scripting buffer, or if
`proof-follow-mode' is set to 'ignore."
  (interactive)
  (if (and proof-script-buffer
	   (not (eq proof-follow-mode 'ignore)))
      (unless (proof-end-of-locked-visible-p)
	(proof-goto-end-of-locked t))))

(defun proof-goto-end-of-locked-on-error-if-pos-not-visible-in-window ()
  "As `proof-goto-end-of-locked-if-pos-not-visible-in-window', but not for interrupts.
Intended as a hook function for `proof-shell-handle-error-or-interrupt-hook'."
  (interactive)
  (unless (eq proof-follow-mode 'ignore)
    (if (eq proof-shell-last-output-kind 'error)
	(proof-goto-end-of-locked-if-pos-not-visible-in-window)))
  (proof-with-current-buffer-if-exists
   proof-script-buffer
   (unless (proof-end-of-locked-visible-p)
     (pg-jump-to-end-hint))))

(defun proof-end-of-locked-visible-p ()
  "Return non-nil if end of locked region is visible."
  (let* ((pos (proof-with-current-buffer-if-exists proof-script-buffer
		(proof-unprocessed-begin)))
	 (win (and pos (get-buffer-window proof-script-buffer t))))
    (and win (pos-visible-in-window-p pos))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Names of proofs (and other parts) in a script.
;;
;; Elements are represented as spans (overlays).
;;
;; Each kind of part ("idiom") in a proof script has its own name
;; space.  Idioms are named with symbols.
;;

(defconst pg-idioms '(proof)
  "List of script element kinds PG is aware of for this prover.")

(defconst pg-all-idioms (append pg-idioms
				'(comment command other))
  "List of all possible script element kinds.")

(defun pg-clear-script-portions ()
  "Clear record of script portion names and types from internal list."
  (dolist (idtbl pg-script-portions)
    (maphash (lambda (k span) (span-delete span)) (cdr idtbl))
    (clrhash (cdr idtbl))))

(defun pg-remove-element (idiom id)
  "Remove the identifier ID from the script portion IDIOM."
  (let* ((elts (cdr-safe (assq idiom pg-script-portions)))
	 (span (and elts (gethash idiom elts))))
    (when span
      (span-detach span) ;; delete overlay, without pre-del fn
      (remhash id elts))))

(defun pg-get-element (idiomsym id)
  "Return proof script element of type IDIOM identifier ID.
IDIOM is a symbol, ID is a string."
  (assert (symbolp idiomsym))
  (assert (stringp id))
  (let ((idsym  (intern id))
	(elts   (cdr-safe (assq idiomsym pg-script-portions))))
    (if elts
	(gethash idsym elts))))
    
(defun pg-add-element (idiomsym id span &optional name)
  "Add element of type IDIOMSYM with identifier ID, referred to by SPAN.
This records the element in `pg-script-portions' and sets span
properties accordingly.

IDIOMSYM is a symbol, whereas ID and optional NAME are strings.
Identifiers must be unique for a given idiom; the optional NAME
will be recorded as a textual name used instead of ID for users;
NAME does not need to be unique.

NAME is a name that comes from the proof script or prover output.
It is recorded in the span with the 'rawname property."
  (assert (symbolp idiomsym))
  (assert (stringp id))
  (if name (assert (stringp name)))
  (let* ((idsym    (intern id))
	 (rawname  name)
	 (name	   (or name id))
	 (idiom    (symbol-name idiomsym))
	 (delfn	   `(lambda () (pg-remove-element
				(quote ,idiomsym) (quote ,idsym))))
	 (elts (cdr-safe (assq idiomsym pg-script-portions))))
    (unless elts
      (setq pg-script-portions
	    (cons (cons idiomsym (setq elts (make-hash-table)))
		  pg-script-portions)))
    (if (gethash idsym elts)
	(proof-debug "Element named %s (type %s) was already in buffer."
		     name idiom))
    (puthash idsym span elts)
    ;; Idiom and ID are stored in the span as symbols; name as a string.
    (span-set-property span 'idiom idiomsym)
    (span-set-property span 'id idsym)
    (span-set-property span 'name name)
    (span-set-property span 'rawname rawname)
    (span-add-delete-action span delfn)
    
    ;; Ideally: would keep invisible property to be the idiom type
    ;; (span-set-property span 'invisible idiom)
    ;; BUT: problems overlapping invisible regions with
    ;; Unicode Tokens (crucial for hiding control sequences).

    ;; Nice behaviour in with isearch: open invisible regions temporarily.
    (span-set-property span 'isearch-open-invisible
      'pg-open-invisible-span)
    (span-set-property span 'isearch-open-invisible-temporary
		       'pg-open-invisible-span)))

(defun pg-invisible-prop (idiom)
  "Return an invisibility symbol for the given IDIOM.
This is a value for the overlay 'invisible property."
  (intern (concat "pg-" (symbol-name (or idiom 'other)))))

(defun pg-set-element-span-invisible (span invisiblep)
  "Function to adjust visibility of span to INVISIBLEP.
We use list values of the 'invisible property which contain
private symbols, that should play well with other conforming modes
and `buffer-invisibility-spec'."
  (let* ((invisible-prop  (pg-invisible-prop (span-property span 'idiom)))
	 (invisible-rest  (remq invisible-prop
				(span-property span 'invisible))))
    (span-set-property span 'invisible 
		       (if invisiblep 
			   (cons invisible-prop invisible-rest)
			 invisible-rest))))
		       
(defun pg-toggle-element-span-visibility (span)
  "Toggle visibility of SPAN."
  (pg-set-element-span-invisible span
   (not (span-property span 'invisible))))

(defun pg-open-invisible-span (span &optional invisible)
  "Function for `isearch-open-invisible' property."
  ;; alias
  (pg-set-element-span-invisible span invisible))

(defun pg-make-element-invisible (idiomsym id)
  "Make element ID of type IDIOMSYM invisible, with ellipsis."
  (let ((span (pg-get-element idiomsym id)))
    (if span (pg-set-element-span-invisible span t))))

(defun pg-make-element-visible (idiomsym id)
  "Make element ID of type IDIOMSYM visible."
  (let ((span (pg-get-element idiomsym id)))
    (if span (pg-set-element-span-invisible span nil))))

(defun pg-toggle-element-visibility (idiomsym id)
  "Toggle visibility of script element of type IDIOMSYM, named ID.
IDIOMSYM is a symbol and ID is a strings."
  (let ((span (pg-get-element idiomsym id)))
    (if span (pg-toggle-element-span-visibility span))))

(defun pg-show-all-portions (idiom &optional hide)
  "Show or conceal portions of kind IDIOM; if HIDE is non-nil, conceal."
  (interactive
   (list
    (intern
     (completing-read
      (concat "Make " 
	      (if current-prefix-arg "in" "") 
	      "visible all regions of: ")
      (apply 'vector pg-idioms) nil t))
    current-prefix-arg))
  (let ((elts    (cdr-safe (assq idiom pg-script-portions)))
	(alterfn (if hide
		     (lambda (k span)
		       (pg-set-element-span-invisible span t))
		   (lambda (k span)
		     (pg-set-element-span-invisible span nil)))))
    (when elts
      (proof-with-script-buffer ; may be called from menu
       (maphash alterfn elts)))))

;; Next two could be in pg-user.el.  No key-bindings for these.
(defun pg-show-all-proofs ()
  "Display all completed proofs in the buffer."
  (interactive)
  (pg-show-all-portions "proof"))

(defun pg-hide-all-proofs ()
  "Hide all completed proofs in the buffer."
  (interactive)
  (pg-show-all-portions "proof" 'hide))

(defun pg-add-proof-element (name span controlspan)
  "Add a span proof element to SPAN with name NAME and parent CONTROLSPAN."
  (let ((proofid   (proof-next-element-id 'proof)))
    (pg-add-element 'proof proofid span name)
    ;; Set id in controlspan [NB: intern here means symbol-name elsewhere]
    (span-set-property controlspan 'id (intern proofid))
    ;; Make a navigable link between the two spans.
    (span-set-property span 'controlspan controlspan)
    (span-set-property controlspan 'children
		       (cons span (span-property controlspan 'children)))
    (pg-set-span-helphighlights span proof-region-mouse-highlight-face)
    (span-set-property span 'priority 10)  ; lower than default
    (if proof-disappearing-proofs
	(pg-make-element-invisible 'proof proofid))))

(defun pg-span-name (span)
  "Return a user-level name for SPAN.
This is based on its name and type.

Each span has a 'type property, one of:

    'goalsave     A goal..savegoal region in the buffer, a completed proof.
    'vanilla      Initialised in proof-semis-to-vanillas, for
    'comment      A comment outside a command.
    'proverproc   A region closed by the prover, processed outwith PG
    'pbp	  A PBP command inserted automatically into the script
"
  (let ((type    (span-property span 'type))
	(idiom   (span-property span 'idiom))
	(name    (span-property span 'name))
	(rawname (span-property span 'rawname)))
    (cond
     (idiom
      (concat (upcase-initials (symbol-name idiom))
	      ;; only use rawnames, not internally generated ones
	      (if (and rawname
		       (not (equal rawname proof-unnamed-theorem-name)))
		  (concat " [" rawname "]"))))
     ((or (eq type 'proof) (eq type 'goalsave))
      (concat "Proof"
	      (let ((name (span-property span 'name)))
		(if name (concat " of " name)))))
     ((eq type 'comment)   "Comment")
     ((eq type 'vanilla)   "Command")
     ((eq type 'pbp)       "PBP command")
     ((eq type 'proverproc)
			   "Prover-processed"))))

(defvar pg-span-context-menu-keymap
  (let ((map (make-sparse-keymap
	      "Keymap for context-sensitive menus on spans")))
      (define-key map [down-mouse-3] 'pg-span-context-menu)
      map)
    "Keymap for the span context menu.")

(defun pg-last-output-displayform ()
  "Return displayable form of `proof-shell-last-output'.
This is used to annotate the buffer with the result of proof steps."
  ;; NOTE: Isabelle/Isar uses urgent messages (sigh) in its ordinary output.
  ;; ("Successful attempt...").  This loses here.
  (if (string= proof-shell-last-output "") ""
    (let* ((text (proof-shell-strip-output-markup
		  (if (and (boundp 'unicode-tokens-mode)
			   unicode-tokens-mode)
		      (unicode-tokens-encode-str proof-shell-last-output)
		    proof-shell-last-output))))

      ;; HACK: for Isabelle which puts ugly leading \n's around proofstate.
      (if (and (> (length text) 0)
	       (string= (substring text 0 1) "\n"))
	  (setq text (substring text 1)))
      (if (and (> (length text) 0)
	       (string= (substring text -1) "\n"))
	  (setq text (substring text 0 -1)))
	
      text)))

;;;###autoload
(defun pg-set-span-helphighlights (span &optional mouseface face)
  "Add a daughter help span for SPAN with help message, highlight, actions.
The daughter span covers the non whitespace content of the main span.

We add the last output (when non-empty) to the hover display, and
also as the 'response property on the span.

Optional argument MOUSEFACE means use the given face as a mouse highlight
face, if it is a face, otherwise, if it is non-nil but not a face,
do not add a mouse highlight.  

In any case, a mouse highlight and tooltip are only set if
`proof-output-tooltips' is non-nil.

Argument FACE means add 'face property FACE to the span."
  (let* ((output     (pg-last-output-displayform))
	 (newstart   (save-excursion
		       (goto-char (span-start span))
		       (skip-chars-forward " \n\t")
		       (point)))
	 (newend     (save-excursion
		       (goto-char (span-end span))
		       (skip-chars-backward " \n\t")
		       (point)))
	 (newspan     (span-make-modifying-removing-span newstart newend)))
    
    (span-set-property span 'pg-helpspan newspan) ; link from parent

    (span-set-property newspan 'pghelp t)
    (span-set-property newspan 'response output)

    (when proof-output-tooltips
      (span-set-property newspan 'help-echo
			 (if (<= (length output) 2)
			     (pg-span-name span)
			   output)))

    ;; Here's the message we used to show in minibuffer
    ;; when pg-show-hints was on:
    ;;
    ;; " ("
    ;; (substitute-command-keys
    ;;  (if (span-property span 'idiom)
    ;;	"with point in region, \\[pg-toggle-visibility] to show/hide; "
    ;;    "\\<pg-span-context-menu-keymap>\\[pg-span-context-menu]"))
    ;; " for menu)")))

    (span-set-property newspan 'keymap pg-span-context-menu-keymap)
    (if (or (facep mouseface)
	    (setq mouseface
		  (unless mouseface 'proof-mouse-highlight-face)))
	(when proof-output-tooltips
	  (span-set-property newspan 'mouse-face mouseface)))
    (if face
	(span-set-property newspan 'face face))
    (span-set-property newspan 'priority 50)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Multiple file handling
;;
(defun proof-complete-buffer-atomic (buffer)
  "Ensure BUFFER marked completely processed, completing with a single step.

If buffer already contains a locked region, only the remainder of the
buffer is closed off atomically (although undo for the initial portion
is unlikely to work, the decoration may be worth retaining).

This works for buffers which are not in proof scripting mode too,
to allow other files loaded by proof assistants to be marked read-only."
  (with-current-buffer buffer
    (save-excursion ;; prevent point moving if user viewing file
      (if (< (proof-unprocessed-begin) (proof-script-end))
	(let ((span (span-make (proof-unprocessed-begin)
			       (proof-script-end))))
	  ;; Reset queue and locked regions.
	  (proof-init-segmentation)
	  ;; End of locked region is always end of buffer
	  (proof-set-locked-end (proof-script-end))
	  ;; Configure the overlay span
	  (span-set-property span 'type 'proverproc)
	  (pg-set-span-helphighlights span 'nohighlight))))))


;; Note: desirable to clean odd asymmetry here: we have a nice setting
;; for proof-register-possibly-new-processed-file but something much
;; more complicated for retracting, because we allow a hook function
;; to calculate the new included files list.

;;;###autoload
(defun proof-register-possibly-new-processed-file
  (file &optional informprover noquestions)
  "Register a possibly new FILE as having been processed by the prover.

If INFORMPROVER is non-nil, the proof assistant will be told about this,
to co-ordinate with its internal file-management.  (Otherwise we assume
that it is a message from the proof assistant which triggers this call).
In this case, the user will be queried to save some buffers, unless
NOQUESTIONS is non-nil.

No action is taken if the file is already registered.

A warning message is issued if the register request came from the
proof assistant and Emacs has a modified buffer visiting the file."
  (let* ((cfile (file-truename file))
	 (buffer (find-buffer-visiting cfile)))
    (proof-debug (concat "Registering file " cfile
			 (if (member cfile proof-included-files-list)
			     " (already registered, no action)." ".")))
    (unless (member cfile proof-included-files-list)
      (and buffer
	   (not informprover)
	   (buffer-modified-p buffer)
	   (pg-response-warning (concat "Changes to "
				  (buffer-name buffer)
				  " have not been saved!")))
      ;; Add the new file onto the front of the list
      (setq proof-included-files-list
	    (cons cfile proof-included-files-list))
      ;; If the file is loaded into a buffer, make sure it is completely locked
      (if buffer
	  (proof-complete-buffer-atomic buffer))
      ;; Tell the proof assistant, if we should and if we can
      (if (and informprover proof-shell-inform-file-processed-cmd)
	  (progn
	    (if (and
		 proof-query-file-save-when-activating-scripting
		 (not noquestions))
		(unwind-protect
		    (save-some-buffers nil #'proof-query-save-this-buffer-p)))
	    ;; Tell the prover
	    (proof-shell-invisible-command
	     (proof-format-filename proof-shell-inform-file-processed-cmd
				    cfile)
	     'wait))))))

(defun proof-query-save-this-buffer-p ()
  "Predicate testing whether `save-some-buffers' during scripting should query."
  (and (eq major-mode proof-mode-for-script)
       (not (eq (current-buffer) proof-script-buffer))))

(defun proof-inform-prover-file-retracted (rfile)
  "Send a message to the prover to tell it RFILE has been undone."
  (cond
   ((stringp proof-shell-inform-file-retracted-cmd)
    (proof-shell-invisible-command
     (proof-format-filename proof-shell-inform-file-retracted-cmd
			    rfile)
     'wait))
   ;; If it's a function it might not actually be informing the prover at all,
   ;; but merely cleans up proof-included-files-list by its own magic.  We
   ;; do the same thing as in proof-shell.el.
   ;; FIXME: clean and amalgamate this code.
   ((functionp proof-shell-inform-file-retracted-cmd)
    (let ((current-included proof-included-files-list))
      (funcall proof-shell-inform-file-retracted-cmd rfile)
      (proof-restart-buffers
       (proof-files-to-buffers
	(set-difference current-included
			proof-included-files-list)))))))

(defun proof-auto-retract-dependencies (cfile &optional informprover)
  "Perhaps automatically retract the (linear) dependencies of CFILE.
If `proof-auto-multiple-files' is nil, no action is taken.
If CFILE does not appear on `proof-included-files-list', no action taken.

Any buffers which are visiting files in `proof-included-files-list'
before CFILE are retracted using `proof-protected-process-or-retract'.
They are retracted in reverse order.

Since the `proof-included-files-list' is examined, we expect scripting
to be turned off before calling here (because turning it off could
otherwise change `proof-included-files-list').

If INFORMPROVER is non-nil,  the proof assistant will be told about this,
using `proof-shell-inform-file-retracted-cmd', to co-ordinate with its
internal file-management.

Files which are not visited by any buffer are not retracted, on the
basis that we may not have the information necessary to retract them
-- spans that cover the buffer with definition/declaration
information.  A warning message is given for these cases, since it
could cause inconsistency problems.

NB!  Retraction can cause recursive calls of this function.
This is a subroutine for `proof-unregister-buffer-file-name'."
  (if proof-auto-multiple-files
      (let ((depfiles (reverse
		       (cdr-safe
			(member cfile (reverse proof-included-files-list)))))
	    rfile rbuf)
	(while (setq rfile (car-safe depfiles))
	  ;; If there's a buffer visiting a dependent file, retract it.
	  ;; We test that the file to retract hasn't been retracted
	  ;; already by a recursive call here.  (But since we do retraction
	  ;; in reverse order, this shouldn't happen...)
	  (if (and (member rfile proof-included-files-list)
		   (setq rbuf (find-buffer-visiting rfile)))
	      (progn
		(proof-debug "Automatically retracting " rfile)
		(proof-protected-process-or-retract 'retract rbuf)
		(setq proof-included-files-list
		      (delete rfile proof-included-files-list))
		;; Tell the proof assistant, if we should and we can.
		;; This may be useful if we synchronise the *prover* with
		;; PG's management of multiple files.  If the *prover*
		;; informs PG (better case), then we hope the prover will
		;; retract dependent files and we shouldn't use this
		;; degenerate (linear dependency) code.
		(if informprover
		    (proof-inform-prover-file-retracted rfile)))
	    ;; If no buffer available, issue a warning that nothing was done
	    (pg-response-warning "Not retracting unvisited file " rfile))
	  (setq depfiles (cdr depfiles))))))

(defun proof-unregister-buffer-file-name (&optional informprover)
  "Remove current buffer's filename from the list of included files.
No effect if the current buffer has no file name.
If INFORMPROVER is non-nil,  the proof assistant will be told about this,
using `proof-shell-inform-file-retracted-cmd', to co-ordinate with its
internal file-management.

If `proof-auto-multiple-files' is non-nil, any buffers on
`proof-included-files-list' before this one will be automatically
retracted using `proof-auto-retract-dependencies'."
  (if buffer-file-name
      (let ((cfile (file-truename
		    (or buffer-file-name
			proof-script-buffer-file-name))))
	(proof-debug (concat "Unregistering file " cfile
			       (if (not (member cfile
						proof-included-files-list))
				   " (not registered, no action)." ".")))
	(if (member cfile proof-included-files-list)
	    (progn
	      (proof-auto-retract-dependencies cfile informprover)
	      (setq proof-included-files-list
		    (delete cfile proof-included-files-list))
	      ;; If we're not allowed to undo into a processed
	      ;; file, we had better remove all the history.
	      (if proof-cannot-reopen-processed-files
		  (proof-restart-buffers (list (current-buffer))))
	      ;; Tell the proof assistant, if we should and we can.
	      ;; This case may be useful if there is a combined
	      ;; management of multiple files between PG and prover.
	      (if informprover
		  (proof-inform-prover-file-retracted cfile)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Activating and Deactivating Scripting
;;
;; The notion of "active scripting buffer" clarifies how
;; scripting across multiple files is handled.  Only one
;; script buffer is allowed to be active, and actions are
;; taken when scripting is turned off/on.
;;

(defsubst proof-action-completed (action)
  (or (and (eq action 'retract) (proof-locked-region-empty-p))
      (and (eq action 'process) (proof-locked-region-full-p))))

(defun proof-protected-process-or-retract (action &optional buffer)
  "If ACTION='process, process, If ACTION='retract, retract.
Process or retract the current buffer, which should be the active
scripting buffer, according to ACTION.
Retract buffer BUFFER if set, otherwise use the current buffer.
Gives a message in the minibuffer and busy-waits for the retraction
or processing to complete.  If it fails for some reason,
an error is signalled here."
  (unless (or (eq action 'process) (eq action 'retract))
    (error "proof-protected-process-or-retract: invalid argument"))
  (let ((buf (or buffer (current-buffer))))
    (with-current-buffer buf
      (unless (proof-action-completed action)
	(let ((fn   (cond ((eq action 'process) 'proof-process-buffer)
			  ((eq action 'retract) 'proof-retract-buffer)))
	      (name (cond ((eq action 'process) "Processing")
			  ((eq action 'retract) "Retracting"))))
	  (unwind-protect
	      (progn
		(message "%s buffer %s..." name buf)
		(funcall fn)
		(proof-shell-wait) ; busy wait
		(message "%s buffer %s...done." name buf)
		(sit-for 0))
	    ;; Test to see if action was successful
	    (unless (proof-action-completed action)
	      (error "%s of %s failed!" name buf))))))))

(defun proof-deactivate-scripting-auto ()
  "Deactivate scripting without asking questions or raising errors.
If the locked region is full, register the file as processed.
Otherwise retract it.  Errors are ignored"
  (ignore-errors
    (proof-deactivate-scripting
     (proof-with-script-buffer
      (if (proof-locked-region-full-p) 'process 'retract)))))

(defun proof-deactivate-scripting-query-user-action ()
  "Display the script and query the user for a deactivate action.
Returns 'retract, 'process or finally nil if user declined."
  ;; Would be nicer to ask a single question, but
  ;; a nuisance to define our own dialogue since it
  ;; doesn't really fit with one of the standard ones.
  (save-window-excursion
    (unless
	;; Test to see whether to display the buffer or not.  Could
	;; have user option here to avoid switching or maybe borrow
	;; similar standard setting
	;; save-some-buffers-query-display-buffer
	(or
	 (eq (current-buffer)
	     (window-buffer (selected-window)))
	 (eq (selected-window) (minibuffer-window)))
      (unless (one-window-p)
	(delete-other-windows))
      (switch-to-buffer proof-script-buffer t))
    (let ((action  (cond
		    ((y-or-n-p
		      (format
		       "Scripting incomplete in buffer %s, retract? "
		       proof-script-buffer))
		     'retract)
		    ((and
		      (not proof-no-fully-processed-buffer)
		      (y-or-n-p
		       (format
			"Completely process buffer %s instead? "
			proof-script-buffer)))
		     'process))))
      (or action
	  (progn
	    ;; Give an acknowledgement to user's choice
	    ;; neither to assert or retract.
	    (message "Scripting still active in %s"
		     proof-script-buffer)
	    ;; Delay because this can be followed by an error
	    ;; message in proof-activate-scripting when trying
	    ;; to switch to another scripting buffer.
	    (sit-for 1)
	    nil)))))

(defun proof-deactivate-scripting-choose-action ()
  "Select a deactivation action, 'process, 'retract or nil."
  (let ((auto-action
	 (if (and proof-no-fully-processed-buffer
		  (eq proof-auto-action-when-deactivating-scripting
		      'process))
	     nil
	   proof-auto-action-when-deactivating-scripting)))
    (or auto-action
	(proof-deactivate-scripting-query-user-action))))


(defun proof-deactivate-scripting (&optional forcedaction)
  "Try to deactivate scripting for the active scripting buffer.

Aims to set `proof-script-buffer' to nil and turn off the
modeline indicator.  No action is required there is no active
scripting buffer.

We make sure that the active scripting buffer either has no locked
region or a full locked region (everything in it has been processed).
If this is not already the case, we question the user whether to
retract or assert, or automatically take the action indicated in the
user option `proof-auto-action-when-deactivating-scripting'.

If `proof-no-fully-processed-buffer' is t there is only the choice
to fully retract the active scripting buffer. In this case the
active scripting buffer is retracted even if it was fully processed.
Setting `proof-auto-action-when-deactivating-scripting' to 'process
is ignored in this case.

If the scripting buffer is (or has become) fully processed, and it is
associated with a file, it is registered on
`proof-included-files-list'.  Conversely, if it is (or has become)
empty, we make sure that it is *not* registered.  This is to be
certain that the included files list behaves as we might expect with
respect to the active scripting buffer, in an attempt to harmonize
mixed scripting and file reading in the prover.

This function either succeeds, fails because the user refused to
process or retract a partly finished buffer, or gives an error message
because retraction or processing failed.  If this function succeeds,
then `proof-script-buffer' is nil afterwards.

The optional argument FORCEDACTION overrides the user option
`proof-auto-action-when-deactivating-scripting' and prevents
questioning the user.  It is used to make a value for
the `kill-buffer-hook' for scripting buffers, so that when
a scripting buffer is killed it is always retracted."
  (interactive)
  (proof-with-current-buffer-if-exists 
   proof-script-buffer
   ;; Examine buffer.

   ;; We must ensure that the locked region is either empty or full,
   ;; to make sense for multiple-file scripting.  (A proof assistant
   ;; won't be able to process just part of a file typically; moreover
   ;; switching between buffers during a proof makes no sense.)
   (let* ((complete   (or (proof-locked-region-empty-p)
			  (and (not proof-no-fully-processed-buffer)
			       (proof-locked-region-full-p))))
	  (action     (unless complete
			(or forcedaction
			    (proof-deactivate-scripting-choose-action)))))
     (if action
	 (proof-protected-process-or-retract action))
     
     (unless (and (not complete) (not action))

       ;; If we get here, then the locked region is (now) either
       ;; completely empty or completely full.

       ;; We can immediately indicate that there is no active
       ;; scripting buffer
       (setq proof-previous-script-buffer proof-script-buffer)
       (setq proof-script-buffer nil)

       (if (proof-locked-region-full-p)
	   ;; If locked region is full, make sure that this buffer
	   ;; is registered on the included files list, and
	   ;; let the prover know it can consider it processed.
	   (if (or buffer-file-name proof-script-buffer-file-name)
	       (proof-register-possibly-new-processed-file
		(or buffer-file-name proof-script-buffer-file-name)
		'tell-the-prover
		forcedaction)))

       (if (proof-locked-region-empty-p)
	   ;; If locked region is empty, make sure this buffer is
	   ;; *off* the included files list.
	   ;; FIXME: probably this isn't necessary: the
	   ;; file should be unregistered by the retract
	   ;; action, or in any case since it was only
	   ;; partly processed.
	   ;; FIXME 2: be careful about automatic
	   ;; multiple file handling here, since it calls
	   ;; for activating scripting elsewhere.
	   ;; We move the onus on unregistering now to
	   ;; the activate-scripting action.
	   (proof-unregister-buffer-file-name))

       ;; Turn off Scripting indicator here.
       (setq proof-active-buffer-fake-minor-mode nil)
       (force-mode-line-update)
       
       ;; Finally, run hooks
       (run-hooks 'proof-deactivate-scripting-hook)))))


(defun proof-activate-scripting (&optional nosaves queuemode)
  "Ready prover and activate scripting for the current script buffer.

The current buffer is prepared for scripting.  No changes are
necessary if it is already in Scripting minor mode.  Otherwise, it
will become the new active scripting buffer, provided scripting can be
switched off in the previous active scripting buffer with
`proof-deactivate-scripting'.

Activating a new script buffer is a good time to ask if the user
wants to save some buffers; this is done if the user option
`proof-query-file-save-when-activating-scripting' is set and
provided the optional argument NOSAVES is non-nil.

The optional argument QUEUEMODE relaxes the test for a busy proof
shell to allow one which has mode QUEUEMODE.  In all other cases,
a proof shell busy error is given.

Finally, the hooks `proof-activate-scripting-hook' are run.  This can
be a useful place to configure the proof assistant for scripting in a
particular file, for example, loading the correct theory, or whatever.
If the hooks issue commands to the proof assistant (via
`proof-shell-invisible-command') which result in an error, the
activation is considered to have failed and an error is given."
  (interactive)
  (unless (eq proof-buffer-type 'script)
    (error "Must be running in a script buffer!"))

  (unless (equal (current-buffer) proof-script-buffer)

    ;; TODO: narrow the scope of this save-excursion.
    ;; Where is it needed?  Maybe hook functions.
    (save-excursion
      ;; If there's another buffer currently active, we need to
      ;; deactivate it (also fixing up the included files list).
      (when proof-script-buffer
	    (proof-deactivate-scripting)
	    ;; Test whether deactivation worked
	    (if proof-script-buffer
		(error
	     "You cannot have more than one active scripting buffer!")))

      ;; Ensure this buffer is off the included files list.  If we
      ;; re-activate scripting in an already completed buffer, the
      ;; proof assistant may need to retract some dependencies.
      (proof-unregister-buffer-file-name 'tell-the-prover)

      ;; If automatic retraction happened in the above step, we may
      ;; have inadvertently activated scripting somewhere else.
      ;; Better turn it off again.  This should succeed trivially.
      ;; NB: it seems that we could move the first test for an already
      ;; active buffer here, but it is more subtle: the first
      ;; deactivation can extend the proof-included-files list, which
      ;; would affect what retraction was done in
      ;; proof-unregister-buffer-file-name.
      (if proof-script-buffer
	  (proof-deactivate-scripting))
      (assert (null proof-script-buffer)
	      "Bug in proof-activate-scripting: deactivate failed.")

      ;; Fire up the prover (or check it's going the right way).
      (proof-shell-ready-prover queuemode)

      ;; Set the active scripting buffer, and initialise regions
      (setq proof-script-buffer (current-buffer))
      (if (proof-locked-region-empty-p) ; leave alone if non-empty
	  (proof-init-segmentation))

      ;; Turn on the minor mode, make it show up.
      (setq proof-active-buffer-fake-minor-mode t)
      (force-mode-line-update)

      ;; A good time to ask if the user wants to save some buffers
      ;; (idea being they may be included in imports at top of new buffer).
      (if (and
	   proof-query-file-save-when-activating-scripting
	   (not nosaves))
	  (save-some-buffers nil #'proof-query-save-this-buffer-p))

      ;; Run hooks with a variable which suggests whether or not to
      ;; block.  NB: The hook function may send commands to the
      ;; process which will re-enter this function, but should exit
      ;; immediately because scripting has been turned on now.
      (if proof-activate-scripting-hook
	  (let
	      ((activated-interactively	(called-interactively-p 'any)))
	    (setq proof-shell-last-output-kind nil)
	    (run-hooks 'proof-activate-scripting-hook)
	    ;; If activate scripting functions caused an error,
	    ;; prevent switching to another buffer.  Might be better
	    ;; to leave to specific instances, or simply run the hooks
	    ;; as the last step before turning on scripting properly.
	    (when (or (eq 'error proof-shell-last-output-kind)
		      (eq 'interrupt proof-shell-last-output-kind))
	      (proof-deactivate-scripting) ;; turn off again!
	      ;; Give an error to prevent further actions.
	      (error 
	       "Scripting not activated because of error or interrupt")))))))


(defun proof-toggle-active-scripting (&optional arg)
  "Toggle active scripting mode in the current buffer.
With ARG, turn on scripting iff ARG is positive."
  (interactive "P")
  (if (if (null arg)
	  (not (eq proof-script-buffer (current-buffer)))
	(> (prefix-numeric-value arg) 0))
      (progn
	(if proof-script-buffer
	    ;; deactivate elsewhere first
	    (call-interactively 'proof-deactivate-scripting))
	(call-interactively 'proof-activate-scripting))
    (call-interactively 'proof-deactivate-scripting)))

;;
;;  End of activating and deactivating scripting section
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Processing the script management queue -- PART 1: "advancing"
;;
;; The proof-action-list contains a list of (span,command,action)
;; triples. The loop looks like: Execute the command, and if it's
;; successful, do action on span.  If the command's not successful, we
;; bounce the rest of the queue and do some error processing.
;;
;; When a span has been processed, it is classified as
;; 'comment, 'goalsave, 'vanilla, etc.
;;
;; The main function for dealing with processed spans is
;; `proof-done-advancing'

(defun proof-done-advancing (span)
  "The callback function for `assert-until-point'.
Argument SPAN has just been processed."
  (let ((end     (span-end span))
	(cmd     (span-property span 'cmd)))

    (proof-set-locked-end end)

    (if (span-live-p proof-queue-span)
	(proof-set-queue-start end))

    (cond
     ;; CASE 1: Comments just get highlighted
     ((eq (span-property span 'type) 'comment)
      (proof-done-advancing-comment span))

     ;; CASE 2: Save command seen, now we may amalgamate spans.
     ((and (proof-string-match-safe proof-save-command-regexp cmd)
	   (funcall proof-really-save-command-p span cmd)
	   (decf proof-nesting-depth) ;; [always non-nil/true]
	   (if proof-nested-goals-history-p
	       ;; For now, we only support this nesting behaviour:
	       ;; don't amalgamate unless the nesting depth is 0,
	       ;; i.e. we're in a top-level proof.
	       ;; This assumes prover keeps history for nested proofs.
	       ;; (True for Isabelle/Isar).
	       (eq proof-nesting-depth 0)
	     t))
      (proof-done-advancing-save span))

     ;; CASE 3: Proof completed one step or more ago, non-save
     ;; command seen, no nested goals allowed.
     ;;
     ;; We make a fake goal-save from any previous
     ;; goal to the command before the present one.
     ;;
     ;; This allows smooth undoing in proofs which have no "qed"
     ;; statements.  If your proof assistant doesn't allow these
     ;; "unclosed" proofs, then you can safely set
     ;; proof-completed-proof-behaviour.
     ((and
       proof-shell-proof-completed
       (or (and (eq proof-completed-proof-behaviour 'extend)
		(>= proof-shell-proof-completed 0))
	   (and (eq proof-completed-proof-behaviour 'closeany)
		(> proof-shell-proof-completed 0))
	   (and (eq proof-completed-proof-behaviour 'closegoal)
		(funcall proof-goal-command-p span))))
      (proof-done-advancing-autosave span))

     ;; CASE 4: A "Require" type of command is seen (Coq).
     ;; Case 4 has been flushed, because its functionality has been
     ;; superseeded by the new auto-compilation feature for Coq.

     ;; CASE 5:  Some other kind of command (or a nested goal).
     (t
      (proof-done-advancing-other span)))

    ;; Add the processed command to the input ring
    (unless (or (not (span-live-p span))
		(eq (span-property span 'type) 'comment))
      (pg-add-to-input-history cmd)))

  ;; Finally: state of scripting may have changed now, run hooks.
  (run-hooks 'proof-state-change-hook))



(defun proof-done-advancing-comment (span)
  "A subroutine of `proof-done-advancing'.  Add comment element for SPAN."
  ;; Add an element for a new span, which should span
  ;; the text of the comment.
  ;; FIXME: might be better to use regexps/skip spaces for matching
  ;; start/end of comments, rather than comment-start and
  ;; comment-end skip (which assumes comments are nicely formatted).
  ;;
  (let ((bodyspan  (span-make
		    (+ (length comment-start) (span-start span))
		    (- (span-end span)
		       (max 1 (length comment-end)))))
	(id        (proof-next-element-id 'comment))
	str)
    (pg-add-element 'comment id bodyspan)
    (span-set-property span 'id (intern id))
    (span-set-property span 'idiom 'comment)
    (let ((proof-shell-last-output "")) ; comments not sent, no last output 
      (pg-set-span-helphighlights bodyspan))

    ;; possibly evaluate some arbitrary Elisp.  SECURITY RISK!
    (save-match-data
      (setq str (buffer-substring-no-properties (span-start span)
						(span-end span)))
      (if (proof-string-match-safe proof-script-evaluate-elisp-comment-regexp str)
	  (condition-case nil
	      (eval (car (read-from-string (match-string-no-properties 1 str))))
	    (t (proof-debug
		(concat
		 "lisp error when obeying proof-shell-evaluate-elisp-comment-regexp: \n"
		 (prin1-to-string (match-string-no-properties 1))
		 "\n"))))))))


(defun proof-done-advancing-save (span)
  "A subroutine of `proof-done-advancing'.  Add info for save span SPAN."
  (unless (or (eq proof-shell-proof-completed 1)
	      (eq proof-assistant-symbol 'isar))
    ;; We expect saves to succeed only for recently completed top-level proofs.
    ;; NB: not true in Isar, because save commands can perform proof.
    (proof-debug
     (format
      "PG: save command with proof-shell-proof-completed=%s, proof-nesting-depth=%s"
      proof-shell-proof-completed proof-nesting-depth)))

  (setq proof-shell-proof-completed nil)

  ;; FIXME: need subroutine here:
  (let ((gspan     span)		  ; putative goal span
	(savestart (span-start span))
	(saveend   (span-end span))
	(cmd       (span-property span 'cmd))
	lev nestedundos nam next)

    (and proof-save-with-hole-regexp
	 (proof-string-match proof-save-with-hole-regexp cmd)
	 ;; Give a message of a name if one can be determined
	 (proof-minibuffer-message
	  (format "proved %s"
		  (setq nam
			(if (stringp proof-save-with-hole-result)
			    (replace-match proof-save-with-hole-result nil nil cmd)
			  (match-string proof-save-with-hole-result cmd))))))

    ;; Search back for a goal command, deleting spans along the way:
    ;; they may be amalgamated into a single goal-save region, which
    ;; corresponds to the prover discarding the proof history.
    (setq lev 1)
    (setq nestedundos 0)
    (while (and gspan (> lev 0))
      (setq next (prev-span gspan 'type))
      (unless proof-arbitrary-undo-positions
	(span-delete gspan))
      (setq gspan next)
      (if gspan
	  (progn
	    (setq cmd (span-property gspan 'cmd))
	    (cond
	     ;; Ignore comments [may have null cmd setting]
	     ((eq (span-property gspan 'type) 'comment))
	     ;; Nested goal saves: add in any nestedcmds
	     ((eq (span-property gspan 'type) 'goalsave)
	      (setq nestedundos
		    (+ nestedundos 1
		       (or (span-property gspan 'nestedundos) 0))))
	     ;; Increment depth for a nested save, in case
	     ;; prover supports history of nested proofs
	     ((and proof-nested-goals-history-p
		   proof-save-command-regexp
		   (proof-string-match proof-save-command-regexp cmd))
	      (incf lev))
	     ;; Decrement depth when a goal is hit
	     ((funcall proof-goal-command-p gspan)
	      (decf lev))
	     ;; Remainder cases: see if command matches something we
	     ;; should count for a global undo
	     ((and proof-nested-undo-regexp
		   (proof-string-match proof-nested-undo-regexp cmd))
	      (incf nestedundos))
	     ))))

    (if (not gspan)
	;; No goal span found!  Issue a warning and do nothing more.
	(pg-response-warning
	 "Proof General: script management confused, couldn't find goal span for save.")

      ;; If the name isn't set, try to set it from the goal, or as a
      ;; final desparate attempt, set the name to
      ;; proof-unnamed-theorem-name (Coq uses a default name for
      ;; unnamed theorems, believe it or not, and issues a
      ;; name-binding error for two unnamed theorems in a row!).
      (setq nam (or nam
		    (proof-get-name-from-goal gspan)
		    proof-unnamed-theorem-name))

      (proof-make-goalsave gspan (span-end gspan)
			   savestart saveend nam nestedundos)

      ;; *** Theorem dependencies ***
      (if proof-last-theorem-dependencies
	  (proof-depends-process-dependencies nam gspan)))))

(defun proof-make-goalsave
  (gspan goalend savestart saveend nam &optional nestedundos)
  "Make new goal-save span, using GSPAN. Subroutine of `proof-done-advancing-save'.
Argument GOALEND is the end of the goal;."
  (unless proof-arbitrary-undo-positions
    (span-set-end gspan saveend)
    (span-set-property gspan 'type 'goalsave))
  (span-set-property gspan 'idiom 'proof);; links to nested proof element
  (span-set-property gspan 'name nam)
  (and nestedundos (span-set-property gspan 'nestedundos nestedundos))
  (pg-set-span-helphighlights gspan proof-region-mouse-highlight-face)
  ;; Now make a nested span covering the purported body of the proof,
  ;; and add to buffer-local list of elements.
  (let ((proofbodyspan
	 (span-make goalend (if proof-script-integral-proofs
				saveend savestart))))
    (pg-add-proof-element nam proofbodyspan gspan)))

(defun proof-get-name-from-goal (gspan)
  "Try to return a goal name from GSPAN.
Subroutine of `proof-done-advancing-save'."
  (let ((cmdstr (span-property gspan 'cmd)))
    (and proof-goal-with-hole-regexp
	 (proof-string-match proof-goal-with-hole-regexp cmdstr)
	 (if (stringp proof-goal-with-hole-result)
	     (replace-match proof-goal-with-hole-result nil nil cmdstr)
	   (match-string proof-goal-with-hole-result cmdstr)))))


;; FIXME: this next function should be more like proof-done-advancing-save,
;; perhaps simplifying the proof-completed-proof-behaviour functionality,
;; which isn't seriously used in any prover.  At the moment the behaviour
;; here is incomplete compared with proof-done-advancing-save.
;; NB: in this function we assume non-nested proofs, which explains
;; some of the logic.  There is no attempt to fix up proof-nesting-depth.
;; NB: 'extend behaviour is not currently compatible with appearance of
;; save commands, since proof-done-advancing-save allow for goalspan
;; already existing.
(defun proof-done-advancing-autosave (span)
  "A subroutine of `proof-done-advancing'."

  ;; In the extend case, the context of proof grows until hit a save
  ;; or new goal.
  (if (eq proof-completed-proof-behaviour 'extend)
      (incf proof-shell-proof-completed)
    (setq proof-shell-proof-completed nil))

  (let* ((swallow  (eq proof-completed-proof-behaviour 'extend))
	 (gspan    (if swallow span (prev-span span 'type)))
	 (newend   (if swallow (span-end span) (span-start span)))
	 (cmd      (span-property span 'cmd))
	 (newgoal  (funcall proof-goal-command-p span))
	 nam hitsave dels ncmd)
    ;; Search backwards to see if we can find a previous goal
    ;; before a save or the start of the buffer.
    ;; FIXME: this should really do the work done in
    ;; proof-done-advancing-save above, too, with nested undos, etc.
    (while ;; big ugly condition
	(and
	 gspan
	 (or
	  (eq (span-property gspan 'type) 'comment)
	  (and
	   (setq ncmd (span-property gspan 'cmd))
	   (setq cmd ncmd) ; dynamic scope for funcall below
	   (not (funcall proof-goal-command-p gspan))
	   (not
	    (and proof-save-command-regexp
		 (proof-string-match proof-save-command-regexp cmd)
		 (funcall proof-really-save-command-p span cmd)
		 (setq hitsave t))))))
      (setq dels (cons gspan dels))
      (setq gspan (prev-span gspan 'type)))
    (cond
     ((or hitsave (null gspan))
      (proof-debug
	 "Proof General strangeness: unclosed proof completed, but couldn't find its start!")
      (pg-set-span-helphighlights span))
     ((and swallow newgoal)
      ;; If extending the region, goalsave already there; just highlight new region
      (setq proof-shell-proof-completed nil)
      (pg-set-span-helphighlights span))
     (t
      ;; If, search back through spans, we haven't hit a save or the
      ;; start of the buffer, we make a fake goal-save region.

      ;; Delete spans between the previous goal and new command
      (mapc 'span-delete dels)

      ;; Try to set the name from the goal... [as above]
      (setq nam (or (proof-get-name-from-goal gspan)
		    proof-unnamed-theorem-name))

      ;; NB: if extending an already closed region, ought to delete
      ;; the body and extend that too: currently we make multiple nested
      ;; bodies, a bit messy.
      ;; (NB: savestart used for nested region: here use saveend)
      (proof-make-goalsave gspan
			   (+ (span-start gspan)
			      (length (or (span-property-safe gspan 'cmd))))
			   newend newend nam)))))

(defun proof-done-advancing-other (span)
  (let ((bodyspan  span) ;; might take subscript after first word/line
	(id        (proof-next-element-id 'command)))
  ;; Hidable regions for commands: the problem is that they have no
  ;; natural surrounding region, so makes it difficult to define a
  ;; region for revealing again.
  (cond
   ((funcall proof-goal-command-p span)
    (pg-add-element 'statement id bodyspan)
    (incf proof-nesting-depth))
   (t
    (pg-add-element 'command id bodyspan)))

  (if proof-shell-proof-completed
      (incf proof-shell-proof-completed))

  (pg-set-span-helphighlights span proof-command-mouse-highlight-face)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Parsing functions for parsing commands in script
;;
;; Command parsing is suprisingly subtle with various possibilities of
;; command syntax (terminated, not terminated, or lisp-style), whether
;; or not PG silently ignores comments, etc.

(defun proof-segment-up-to-parser (pos &optional next-command-end)
  "Parse the script buffer from end of queue/locked region to POS.
This partitions the script buffer into contiguous regions, classifying
them by type.  Return a list of lists of the form
  
   (TYPE TEXT ENDPOS)

where:

  TYPE is a symbol indicating the type of text found, either 'cmd or 'comment;
  TEXT is the string content taken from the buffer;
  ENDPOS is the position of the final character of the text.

The behaviour around comments is set by
`proof-script-fly-past-comments', which see.

This version is used when `proof-script-parse-function' is set,
to the function which parses the script segment by segment."
  (save-excursion
    (let* ((start (goto-char (proof-queue-or-locked-end)))
	   (cur   (1- start))
	   (seg   t)
	   prevtype realstart cmdseen segs)
      ;; Keep parsing until:
      ;;   - we fail to find a segment   (seg = nil)
      ;;   - we go beyond the stop point (cur >= end)
      ;;      - unless we're flying past comments, in which case
      ;;        wait for a command (cmdseen<>nil)
      (while (and seg
		  (or (< cur pos)
		      (and proof-script-fly-past-comments
			   (not cmdseen))))
	;; Skip whitespace before this element
	(skip-chars-forward " \t\n")
	(setq realstart (point))
	(let* ((type  (funcall proof-script-parse-function)))
	  (setq seg nil)
	  (cond
	   ((eq type 'comment)
	    (setq seg (list 'comment "" (point))))
	   ((eq type 'cmd)
	    (setq cmdseen t)
	    (setq seg (list
		       'cmd
		       (buffer-substring-no-properties realstart (point))
		       (point))))
	   ((null type))		; nothing left in buffer
	   (t
	    (error
  "Proof-segment-up-to-parser: bad TYPE value from proof-script-parse-function")))
	  ;;
	  (if seg
	      (progn
		;; Add the new segment, coalescing comments if the
		;; user likes it that way.  I first made coalescing a
		;; separate configuration option, but it works well
		;; used in tandem with the fly-past behaviour.
		(setq segs (cons seg
				 (if (and proof-script-fly-past-comments
					  (eq type 'comment)
					  (eq prevtype 'comment))
				     (cdr segs)
				   segs)))
		;; Update state
		(setq cur (point))
		(setq prevtype type)))))
      ;; Return segment list
      segs)))

;;;###autoload
(defun proof-script-generic-parse-find-comment-end ()
  "Find the end of the comment point is at the start of.  Nil if not found."
  (let ((notout t))
    ;; Find end of comment (NB: doesn't undertand nested comments)
    (while (and notout (re-search-forward
			proof-script-comment-end-regexp nil 'movetolimit))
      (setq notout (proof-buffer-syntactic-context)))
    (not (proof-buffer-syntactic-context))))

(defun proof-script-generic-parse-cmdend ()
  "For `proof-script-parse-function' if `proof-script-command-end-regexp' set."
  (if (looking-at proof-script-comment-start-regexp)
      ;; Handle comments
      (if (proof-script-generic-parse-find-comment-end) 'comment)
    ;; Handle non-comments: assumed to be commands
    (let (foundend)
      ;; Find end of command
      (while (and (setq foundend
			(progn
			  (and
			   (re-search-forward proof-script-command-end-regexp nil t)
			   (or (match-beginning 1) ;; optional start of white space
			       (match-end 0)))))
		  (proof-buffer-syntactic-context))
	;; inside a string or comment before the command end
	)
      (if (and foundend
	       (goto-char foundend)	; move to command end
	       (not (proof-buffer-syntactic-context)))
	  ;; Found command end outside string/comment
	  'cmd
	;; Didn't find command end
	nil))))


;; This was added for the fine-grained command structure of Isar
;;
;; It more involved than the case of just scanning for command end; we
;; have to find two successive command starts and go backwards from
;; the second.  This coalesces comments following commands with
;; commands themselves, and sends them to the prover (only case where
;; it does).  It's needed particularly for Isar's text command (text
;; {* foo *}) so we can define the buffer syntax for text as comment.
;;
;; To avoid doing that, we would need to scan also for comments but
;; it would be difficult to distinguish between:
;;   complete command (* that's it *)
;; and
;;   complete (* almost *) command
;;
;; Maybe the second case should be disallowed in command-start regexp
;; case?
;;
;; Another improvement idea might be to take into account both
;; command starts *and* ends, but let's leave that for another day.
;;
;; NB: proof-script-comment-start-regexp doesn't need to be the same
;; as (reqexp-quote comment-start).
;;

(defun proof-script-generic-parse-cmdstart ()
  "For `proof-script-parse-function' if `proof-script-command-start-regexp' is set."
  (let ((case-fold-search proof-case-fold-search))
    (if (looking-at proof-script-comment-start-regexp)
	;; Find end of comment
	(if (proof-script-generic-parse-find-comment-end) 'comment)
    ;; Handle non-comments: assumed to be commands
    (when (looking-at proof-script-command-start-regexp)
      ;; We've got at least the beginnings of a command, skip past it
      (goto-char (match-end 0))
      (let (foundstart)
	;; Find next command start
	(while (and (setq
		     foundstart
		     (and
		      (re-search-forward proof-script-command-start-regexp
					 nil 'movetolimit)
		      (and (match-beginning 0)
			   ;; jiggery pokery here is to move outside a
			   ;; comment in case a comment start is considered to
			   ;; be a command start (for non fly-past behaviour)
			   (goto-char (match-beginning 0)))))
		    (proof-buffer-syntactic-context)
		    (goto-char (1+ (point))))
	  ;; loop while in a string/comment before the next command start
	  )
	(unless (proof-buffer-syntactic-context)  ; not inside a comment/string
	  (cond
	   (foundstart			; found a second command start
	    (goto-char foundstart)	; beginning of command start
	    (skip-chars-backward " \t\n") ; end of previous command
	    'cmd)
	   ((eq (point) (point-max))	  ; At the end of the buffer
	    (skip-chars-backward " \t\n") ; benefit of the doubt, let
	    'cmd)))		      ; the PA moan if it's incomplete
	    ;; Return nil otherwise, no complete command found
	)))))


(defun proof-script-generic-parse-sexp ()
  "Used for `proof-script-parse-function' if `proof-script-sexp-commands' is set."
  ;; Usual treatment of comments
  (if (looking-at proof-script-comment-start-regexp)
      ;; Find end of comment
      (if (proof-script-generic-parse-find-comment-end) 'comment)
    (let* ((parse-sexp-ignore-comments t)	; gobble comments into commands
	   (end (scan-sexps (point) 1)))
      (if end
	  (progn (goto-char end) 'cmd)))))


(defun proof-semis-to-vanillas (semis &optional queueflags)
  "Create vanilla spans for SEMIS and a list for the queue.
Proof terminator positions SEMIS has the form returned by
the function `proof-segment-up-to'.  The argument list is destroyed.
The callback in each queue element is `proof-done-advancing'.

If the variable `proof-script-preprocess' is set (to the name of
a function), call that function to construct the first element of
each queue item.

The optional QUEUEFLAGS are added to each queue item."
  (let ((start (proof-queue-or-locked-end))
	(file  (or (buffer-file-name) (buffer-name)))
	(cb    'proof-done-advancing)
	span alist semi item end)
    (setq semis (nreverse semis))
    (save-match-data
      (dolist (semi semis)
	(setq end (nth 2 semi))
	(setq span  (span-make start end))
	(if (eq (car semi) 'cmd)
	    (progn ;; command span
	      (let* ((cmd  (nth 1 semi))
		     (qcmd (if proof-script-preprocess
			       (funcall proof-script-preprocess
					file
					;; ignore spaces at start of command
					(+ start (save-excursion
						   (goto-char start)
						   (skip-chars-forward " \t\n")))
					end
					cmd)
			     (list cmd)))
		     (qitem  (list span qcmd cb queueflags)))
		(span-set-property span 'type 'vanilla)
		(span-set-property span 'cmd cmd)
		(setq alist (cons qitem alist))))
	  ;; ignored text
	  (let ((qitem  
		 (list span nil cb queueflags))) ; nil was `proof-no-command' 
	  (span-set-property span 'type 'comment)
	    (setq alist (cons qitem alist))))
	(setq start end)))
    (nreverse alist)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Moving point in proof script buffer
;;

(defun proof-next-command-new-line ()
  "Return non-nil if next command should start a new line."
  (or proof-next-command-on-new-line ; pg-vars
      (with-no-warnings (proof-ass one-command-per-line))))

(defun proof-script-next-command-advance ()
  "Move point to the beginning of the next command if it's nearby.
Assumes that point is at the end of a command."
  (interactive)
  (skip-chars-forward " \t")
  (if (and (eolp)
	   (proof-next-command-new-line))
      (forward-line)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Assert-until-point.
;;
;; This function parses some region of the script buffer into
;; commands, and the adds the commands into the queue.
;;

(defun proof-assert-until-point (&optional displayflags)
  "Process the region from the end of the locked-region until point."
  (if (proof-only-whitespace-to-locked-region-p)
      (error
	 "At end of the locked region, nothing to do to!"))
  (proof-activate-scripting nil 'advancing)
  (let ((semis (save-excursion
		 (skip-chars-backward " \t\n"
				      (proof-queue-or-locked-end))
		 (proof-segment-up-to-using-cache (point)))))
    (if (eq 'unclosed-comment (car semis))
	(setq semis (cdr semis)))
    (if (null semis) ; maybe inside a string or something.
	(error "I can't find any complete commands to process!"))
    (proof-assert-semis semis displayflags)))

(defun proof-assert-electric-terminator ()
  "Insert the proof command terminator, and assert up to it.
This is a little bit clever with placement of semicolons, and will
try to avoid duplicating them in the buffer.
When used in the locked region (and so with strict read only off), it
always defaults to inserting a semi (nicer might be to parse for a
comment, and insert or skip to the next semi)."
  (let ((mrk         (point)) 
	(termregexp  (regexp-quote proof-terminal-string))
	ins incomment nwsp)
    (if (< mrk (proof-unprocessed-begin))
	(insert proof-terminal-string) ; insert immediately in locked region
      (if (proof-only-whitespace-to-locked-region-p)
	  (error "There's nothing to do!"))
      (skip-chars-backward " \t\n")
      (setq nwsp (point)) ; char after first non-whitespace
      (unless (or proof-electric-terminator-noterminator
		  ;; before the terminal
		  (looking-at termregexp)
		  ;; after the terminal
		  (and
		   (re-search-backward termregexp (proof-unprocessed-begin) t)
		   (goto-char nwsp)
		   (eq (match-end 0) nwsp)))
	(insert proof-terminal-string)
	(setq ins t))
      (proof-activate-scripting nil 'advancing)
      (let* ((pos
	      (if proof-electric-terminator-noterminator (1- (point)) (point)))
	     (semis
	      (save-excursion
		(proof-segment-up-to-using-cache pos))))
	(unless semis
	  (error "Can't find a parseable command!"))
	(when (eq 'unclosed-comment (caar semis))
	  (setq incomment t)
	  ;; delete spurious char in comment
	  (if ins (backward-delete-char 1))
	  (goto-char mrk)
	  (insert proof-terminal-string))
	;; assert the region
	(proof-assert-semis semis)
	(proof-script-next-command-advance)))))

(defun proof-assert-semis (semis &optional displayflags)
  "Add to the command queue the list SEMIS of command positions.
SEMIS must be a non-empty list, in reverse order (last position first).
We assume that the list is contiguous and begins at (proof-queue-or-locked-end).
We also delete help spans which appear in the same region (in the expectation
that these may be overwritten).
This function expects the buffer to be activated for advancing."
  (assert semis nil "proof-assert-semis: argument must be a list")
  (let ((startpos  (proof-queue-or-locked-end))
	(lastpos   (nth 2 (car semis)))
	(vanillas  (proof-semis-to-vanillas semis displayflags)))
    (proof-script-delete-secondary-spans startpos lastpos)
    (proof-extend-queue lastpos vanillas)))

(defun proof-retract-before-change (beg end)
  "For `before-change-functions'.  Retract to BEG unless BEG and END in comment.
No effect if prover is busy."
  (when (and (> (proof-queue-or-locked-end) beg)
	     (not (and (proof-inside-comment beg)
		       (proof-inside-comment end))))
    (when proof-shell-busy
      (message "Interrupting prover")
      (proof-interrupt-process)
      (proof-shell-wait))
    (save-excursion
      (save-restriction ;; see Trac#403
	(widen)
	(goto-char beg)
	(proof-retract-until-point)
	(proof-shell-wait)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; PBP call-backs
;;
;;;###autoload
(defun proof-insert-pbp-command (cmd)
  "Insert CMD into the proof queue."
  (proof-activate-scripting)
  (let (span)
    (proof-goto-end-of-locked)
    (if (proof-next-command-new-line) (insert "\n"))
    (insert cmd)
    (setq span (span-make (proof-unprocessed-begin) (point)))
    (span-set-property span 'type 'pbp)
    (span-set-property span 'cmd cmd)
    (proof-start-queue (proof-unprocessed-begin) (point)
		       (list (list span (list cmd)
				   'proof-done-advancing)))))

;;;###autoload
(defun proof-insert-sendback-command (cmd)
  "Insert CMD into the proof script, execute assert-until-point."
  (proof-with-script-buffer
    (proof-goto-end-of-locked)
    (insert "\n") ;; could be user opt
    (insert cmd)
    (proof-assert-until-point)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Processing the script management queue -- PART 2: retracting
;;

;; Most of the hard work (computing the commands to do the retraction)
;; is implemented in the customisation module (lego.el or coq.el), so
;; code here is fairly straightforward.


;; TODO: we need to adjust proof-nesting-depth appropriately here.
;; It would help to know the type of retraction which has just
;; occurred: a kill-proof may be assumed to set nesting depth
;; to zero; an undo sequence may alter it some other way.
;; NB: at the moment, the adjustment is made in the wrong place!!

(defun proof-done-retracting (span)
  "Callback for `proof-retract-until-point'.
We update display after proof process has reset its state.
See also the documentation for `proof-retract-until-point'.
Optionally delete the region corresponding to the proof sequence.
After an undo, we clear the proof completed flag.  The rationale
is that undoing never leaves prover in a \"proof just completed\"
state, which is true for some proof assistants (but probably not
others)."
  ;; TODO: need to fixup proof-nesting-depth
  (setq proof-shell-proof-completed nil)
  (if (span-live-p span)
      (let ((start (span-start span))
	    (end (span-end span))
	    (killfn (span-property span 'remove-action)))
	;; da: check for empty region seems odd here?
	;; [prevents regions from being detached in set-locked-end]
	(unless (proof-locked-region-empty-p)
	  (proof-set-locked-end start)
	  (proof-set-queue-end start))
	;; Try to clean input history (NB: rely on order here)
;; PG 3.7 release: disable this, it's not yet robust.
;;	(let ((cmds (spans-at-region-prop start end 'cmd))
;;	      (fn   (lambda (span)
;;		      (unless (eq (span-property span 'type) 'comment)
;;			(pg-remove-from-input-history
;;			 (span-property span 'cmd))))))
;;	  (mapc fn (reverse cmds)))

	(proof-script-delete-spans start end)
	(span-delete span)
	(if killfn (funcall killfn start end))))
  ;; State of scripting may have changed now
  (run-hooks 'proof-state-change-hook))

(defun proof-setup-retract-action (start end proof-commands remove-action &optional 
					 displayflags)
  "Make span from START to END which corresponds to retraction.
Returns retraction action destined for proof shell queue, and make span.
Action holds PROOF-COMMANDS and `proof-done-retracting' callback.
Span deletion property set to function REMOVE-ACTION.
DISPLAYFLAGS control output shown to user, see `proof-action-list'."
  (let ((span (span-make start end)))
    (span-set-property span 'remove-action remove-action)
    (list (list span proof-commands 'proof-done-retracting displayflags))))


(defun proof-last-goal-or-goalsave ()
  "Return the span which is the last goal or save before point."
  (save-excursion
    (let ((span (span-at-before (proof-unprocessed-begin) 'type)))
      (while (and span
		  (not (eq (span-property span 'type) 'goalsave))
		  (or (eq (span-property span 'type) 'proof)
		      (eq (span-property span 'type) 'comment)
		      (eq (span-property span 'type) 'proverproc)
		      (not (funcall proof-goal-command-p span))))
	(setq span (prev-span span 'type)))
      span)))

;;
;; NB: Should carefully explain/document this behaviour somewhere.
;; The undo is three-phase:
;;    undo-cmd - ...  - undo-cmd  within proof
;;    kill proof		  exit proof
;;    forget-to-declaration       forget target span
;;
;; It turns out that this behaviour is not quite right for Coq.
;; It might be simpler to just use a single undo/forget
;; command, which is called in all cases.
;;
(defun proof-retract-target (target undo-action displayflags)
  "Retract the span TARGET and apply UNDO-ACTION to undone region if non-nil.
Notice that this necessitates retracting any spans following TARGET,
up to the end of the locked region.
DISPLAYFLAGS control output shown to user, see `proof-action-list'."
  (let ((end   (proof-unprocessed-begin))
	(start (span-start target))
	(span  (if proof-arbitrary-undo-positions
		   target
		 (proof-last-goal-or-goalsave)))
	actions)

    ;; NB: first section only entered if proof-kill-goal-command is
    ;; non-nil.  Otherwise we expect proof-find-and-forget-fn to do
    ;; all relevent work for arbitrary retractions.  FIXME: clean up

    ;; Examine the last span in the locked region.

    ;; If the last goal or save span is not a proof or
    ;; prover processed file, we examine to see how to remove it.
    (if (and span proof-kill-goal-command
	     (not (or
		   (memq (span-property span 'type)
			 '(goalsave proverproc)))))
	;; If the goal or goalsave span ends before the target span,
	;; then we are retracting within the last unclosed proof,
	;; and the retraction just amounts to a number of undo
	;; steps.
	;; FIXME: really, there shouldn't be more work to do: so
	;;  why call proof-find-and-forget-fn later?
	(if (< (span-end span) (span-end target))
	    (progn
	      ;; Skip comment/non-undoable spans at and immediately following target
	      (setq span target)
	      (while (and span
			  (memq (span-property span 'type) '(comment proverproc)))
		(setq span (next-span span 'type)))
	      ;; Calculate undos for the current open segment
	      ;; of proof commands
	      (setq actions (proof-setup-retract-action
			     start end
			     (if (null span) nil ; was: proof-no-command
			       (funcall proof-count-undos-fn span))
			     undo-action)
		    end start))
	  ;; Otherwise, start the retraction by killing off the
	  ;; currently active goal.
	  ;; FIXME: and couldn't we move the end upwards?
	  ;; FIXME: hack proof-nesting-depth here.  This is
	  ;; in the wrong place: it should be done *after* the
	  ;; retraction has succeeded.
	  (setq proof-nesting-depth (1- proof-nesting-depth))
	  (setq actions
		(proof-setup-retract-action (span-start span) end
					    (list proof-kill-goal-command)
						    undo-action
						    displayflags)
		end (span-start span))))
    ;; Check the start of the target span lies before the end
    ;; of the locked region (should always be true since we don't
    ;; make spans outside the locked region at the moment)...
    ;; But end may have moved backwards above: this just checks whether
    ;; there is more retraction to be done.
    (if (> end start)
	(setq actions
	      ;; Append a retract action to clear the entire start-end
	      ;; region.  Rely on proof-find-and-forget-fn to
	      ;; calculate a command which "forgets" back to the first
	      ;; definition, declaration, or whatever that comes after
	      ;; the target span.
	      (nconc actions (proof-setup-retract-action
			      start end
			      (funcall proof-find-and-forget-fn target)
			      undo-action
			      displayflags))))

    (proof-start-queue (min start end) (proof-unprocessed-begin) 
		       actions 'retracting)))

(defun proof-retract-until-point-interactive (&optional delete-region)
  "Tell the proof process to retract until point.
If invoked outside a locked region, undo the last successfully processed
command.  If called with a prefix argument (DELETE-REGION non-nil), also
delete the retracted region from the proof-script."
  (interactive "P")
  (proof-retract-until-point 
   (if delete-region 'kill-region)))

(defun proof-retract-until-point (&optional undo-action displayflags)
  "Set up the proof process for retracting until point.
This calculates the commands to undo to the current point within
the locked region.  If invoked outside the locked region, undo
the last successfully processed command.  See `proof-retract-target'.

After retraction has succeeded in the prover, the filter will call
`proof-done-retracting'.  If UNDO-ACTION is non-nil, it will 
then be invoked on the region in the proof script corresponding to 
the proof command sequence.
DISPLAYFLAGS control output shown to user, see `proof-action-list'.

Before the retraction is calculated, we enforce the file-level
protocol with `proof-activate-scripting'.  This has a couple
of effects:

1. If the file is completely processed, we have to re-open it
for scripting again which may involve retracting
other (dependent) files.

2. We may query the user whether to save some buffers.  

Step 2 may seem odd -- we're undoing (in) the buffer, after all
-- but what may happen is that when scripting starts going
forward again, we hit a command that loads other files, but the
user hasn't saved the latest edits.  Therefore it is right to
query saves here."
  (if (proof-locked-region-empty-p)
      (error "No locked region")
    (proof-activate-scripting)
    ;; enforce not busy to avoid retracting items from the queue region,
    ;; which is not supported currently, see #443
    ;; (future: may allow retracting from queue in progress)
    (proof-shell-ready-prover)
    (unless (proof-locked-region-empty-p) ;; re-opening may discard locked region!
      (let ((span (span-at (point) 'type)))
	;; If no span at point, retracts the last span in the buffer.
	(unless span
	  (proof-goto-end-of-locked)
	  (backward-char)
	  (setq span (span-at (point) 'type)))
	(if span
	    (proof-retract-target span undo-action displayflags)
	  ;; something wrong
	  (proof-debug
	   "proof-retract-until-point: couldn't find a span!"))))))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Proof General scripting mode definition, part 1.
;;

;;;###autoload
(define-derived-mode proof-mode fundamental-mode
  proof-general-name
  "Proof General major mode class for proof scripts.
\\{proof-mode-map}"

  (setq proof-buffer-type 'script)

  ;; Set default indent function (can be overriden in derived modes)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'proof-indent-line)

  ;; During write-file it can happen that we re-set the mode for the
  ;; currently active scripting buffer.  The user might also do this
  ;; for some reason.  We could maybe let this pass through, but it
  ;; seems safest to treat it as a kill buffer operation (retract and
  ;; clear spans).  NB: other situations cause double calls to proof-mode.
  (if (eq (current-buffer) proof-script-buffer)
      (proof-script-kill-buffer-fn))

  ;; We set hook functions here rather than in proof-config-done so
  ;; that they can be adjusted by prover specific code if need be.
  (proof-script-set-buffer-hooks)

  ;; Set after change functions
  (proof-script-set-after-change-functions)

  (add-hook 'after-set-visited-file-name-hooks
	    'proof-script-set-visited-file-name nil t)

  (add-hook 'proof-activate-scripting-hook 'proof-cd-sync nil t))

;; NB: proof-mode-map declared above
(proof-menu-define-keys proof-mode-map)
(proof-eval-when-ready-for-assistant
 (define-key proof-mode-map [(control c) (control a)] (proof-ass keymap)))

(defun proof-script-set-visited-file-name ()
  "Called when visited file name is changed.

This is a hook function for `after-set-visited-file-name-hooks'.

For some provers, the file from which script commands are being
processed may be important, and if it is changed with \\[write-file], for
example, we might have to retract the contents or inform the proof
assistant of the new name.  This should be done by adding
additional functions to `after-set-visited-file-name-hooks'.

At the least, we need to set the buffer local hooks again
with `proof-script-set-buffer-hooks' which is what this function does,
as well as setting `proof-script-buffer-file-name' (which see).

This hook also gives a warning in case this is the active scripting buffer."
  (setq proof-script-buffer-file-name buffer-file-name)
  (if (eq (current-buffer) proof-script-buffer)
      (pg-response-warning
"Active scripting buffer changed name; synchronization risked if prover tracks filenames!"))
  (proof-script-set-buffer-hooks))

(defun proof-script-set-buffer-hooks ()
  "Set the hooks for a proof script buffer.
The hooks set here are cleared by `write-file', so we use this function
to restore them using `after-set-visited-file-name-hooks'."
  (add-hook 'kill-buffer-hook 'proof-script-kill-buffer-fn t t)
  ;; Reverting buffer is same as killing it as far as PG is concerned
  (add-hook 'before-revert-hook 'proof-script-kill-buffer-fn t t))

(defun proof-script-kill-buffer-fn ()
  "Value of `kill-buffer-hook' for proof script buffers.
Clean up before a script buffer is killed.
If killing the active scripting buffer, run `proof-deactivate-scripting-auto'.
Otherwise just do `proof-restart-buffers' to delete some spans from memory."
  ;; Deactivate scripting in the current buffer if need be, forcing
  ;; automatic retraction if the buffer is not fully processed.
  (if (eq (current-buffer) proof-script-buffer)
      (proof-deactivate-scripting-auto))
  (proof-restart-buffers (list (current-buffer)))
  ;; Hide away goals, response, and tracing.  This is a hack because
  ;; otherwise we can lead the user to frustration with the
  ;; dedicated windows nonsense.
  (proof-map-buffers
   (list proof-goals-buffer proof-response-buffer proof-trace-buffer)
   (bury-buffer (current-buffer))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  Proof General scripting mode definition - part 2
;;

;; The functions proof-config-done[-related] are called after the
;; derived mode has made its settings.

;; The callback *-config-done mechanism is an irritating hack - there
;; should be some elegant mechanism for computing constants after the
;; child has configured.  Should petition the author of "derived-mode"
;; about this!

(defun proof-config-done-related ()
  "Finish setup of Proof General scripting and related modes.
This is a subroutine of `proof-config-done'.

This is intended for proof assistant buffers which are similar to
script buffers, but for which scripting is not enabled.  In
particular, we: lock the buffer if it appears on
`proof-included-files-list'; configure font-lock support from
`proof-script-font-lock-keywords'.

This is used for Isabelle theory files, which share some scripting
mode features, but are only ever processed atomically by the proof
assistant."
  (setq proof-script-buffer-file-name buffer-file-name)

  (setq font-lock-defaults 
	(list '(proof-script-font-lock-keywords)
	      ;; see defadvice in proof-syntax 
	      (fboundp (proof-ass-sym font-lock-fontify-syntactically-region))))

  ;; Has buffer already been processed?
  ;; NB: call to file-truename is needed for GNU Emacs which
  ;; chooses to make buffer-file-truename abbreviate-file-name
  ;; form of file-truename.
  (and buffer-file-truename
       (member (file-truename buffer-file-truename)
	       proof-included-files-list)
       (proof-complete-buffer-atomic (current-buffer)))

  (make-local-variable 'comment-start)
  (setq comment-start (concat proof-script-comment-start " "))
  (make-local-variable 'comment-end)
  (setq comment-end
	;; For end of line terminated comments, stays empty.
	(if (string-equal "" proof-script-comment-end)
	    ""
	  ;; Otherwise, an extra space before comment delimiter
	  (concat " " proof-script-comment-end)))

  (unless proof-script-comment-start-regexp
    (setq proof-script-comment-start-regexp (regexp-quote proof-script-comment-start)))
  (unless proof-script-comment-end-regexp
    (setq proof-script-comment-end-regexp
	  (if (string-equal "" proof-script-comment-end)
	      (regexp-quote "\n") ;; end-of-line terminated comments
	    (regexp-quote proof-script-comment-end))))

  ;; FIXME: This is clearly bogus: it sets the *start* matcher based on the
  ;; *end* marker.  But I'm not sure what's the right fix: OT1H the code is
  ;; careful to build a correct end-matcher, but OTOH it's not as careful as
  ;; the default code in newcomment.el anyway.  So I'm tempted to just remove
  ;; this code altogether.
  (make-local-variable 'comment-start-skip)
  (unless comment-start-skip
    (setq comment-start-skip
	  (if (string-equal "" proof-script-comment-end)
	      (regexp-quote "\n") ;; end-of-line terminated comments
	    (regexp-quote proof-script-comment-end)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Generic defaults for hooks, based on regexps.
;;

;; The next step is to use proof-stringfn-match scheme more widely, to
;; allow settings which are string or fn, so we don't need both regexp
;; and function hooks, and so that the other hooks can be functions too.

(defun proof-generic-goal-command-p (span)
  "Is SPAN a goal?  Decide by matching with `proof-goal-command-regexp'."
  (proof-string-match-safe proof-goal-command-regexp
			   (or (span-property span 'cmd) "")))

(defun proof-generic-state-preserving-p (cmd)
  "Is CMD state preserving?  Match on `proof-non-undoables-regexp'."
  ;; FIXME: logic here is not quite finished: proof-non-undoables are
  ;; certainly not state preserving, but so are a bunch more things,
  ;; i.e. ordinary proof commands which may appear in proof scripts.
  ;; Might be better to add positive and negative regexps for
  ;; state-preserving tests (only one of which needs to be set).
  (not (proof-string-match-safe proof-non-undoables-regexp cmd)))

(defun proof-generic-count-undos (span)
  "Count number of undos in SPAN, return commands needed to undo that far.
Command is set using `proof-undo-n-times-cmd'.

A default value for `proof-count-undos-fn'.

For this function to work properly, you must configure
`proof-undo-n-times-cmd' and `proof-ignore-for-undo-count'."
  (let
      ((case-fold-search proof-case-fold-search)
       (ct 0) str i
       (tl (length proof-terminal-string)))
    (while span
      (setq str (span-property span 'cmd))
      (cond ((eq (span-property span 'type) 'vanilla)
	     (unless (proof-stringfn-match proof-ignore-for-undo-count str)
	       (incf ct)))
	    ((eq (span-property span 'type) 'pbp)
	     (setq i 0)
	     (while (< i (length str))
	       (if (string-equal (substring str i (+ i tl)) proof-terminal-string)
		   (incf ct))
	       (incf i))))
      (setq span (next-span span 'type)))
    (if (= ct 0)
	nil ; was proof-no-command
      (cond ((stringp proof-undo-n-times-cmd)
	     (list (format proof-undo-n-times-cmd ct)))
	    ((functionp proof-undo-n-times-cmd)
	     (list (funcall proof-undo-n-times-cmd ct)))))))

(defun proof-generic-find-and-forget (span)
  "Calculate a forget/undo command to forget back to SPAN.
This is a long-range forget: we know that there is no
open goal at the moment, so forgetting involves unbinding
declarations, etc, rather than undoing proof steps.

This generic implementation assumes it is enough to find the
nearest following span with a `name' property, and retract
that using `proof-forget-id-command' with the given name.

If this behaviour is not correct, you must customize the function
with something different."
  ;; Modelled on Isar's find-and-forget function, but less
  ;; general at the moment: will only issue one und command.
  ;; FIXME: would be much cleaner to wrap up the undo behaviour
  ;; also within proofs in this function.
  (cond
   ((not proof-forget-id-command)
    (proof-debug "proof-generic-find-and-forget: proof-forget-id-command is unset, no action taken.")
    "")
   (t
    (let (ans typ name answers cmd)
      (while span
	(setq ans nil)
	(setq cmd (span-property span 'cmd))
	(setq typ (span-property span 'type))
	(cond
	 ;; comment, diagnostic, prover processed, nested proof command: skip
	 ((or (eq typ 'comment)
	      (eq typ 'proverproc)
	      (eq typ 'proof)
	      (and proof-ignore-for-undo-count cmd
		   (proof-string-match proof-ignore-for-undo-count cmd))))
	 ;; some named element: use generic forget-id function; finish.
	 ((setq name (span-property span 'name))
	  (setq ans (format proof-forget-id-command name))
	  (setq span nil)))
	(if ans (setq answers (cons ans answers)))
	(if span (setq span (next-span span 'type))))
      answers))))

;;
;; End of new generic functions
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;
;; Sanity checks on important settings
;;

(defconst proof-script-important-settings
  '(proof-script-comment-start			;
    proof-script-comment-end
    proof-save-command-regexp		; [actually, some provers may not have save command]
;    proof-goal-command-regexp		; not needed if proof-goal-command-p is set
;    proof-goal-with-hole-regexp		; non-essential?
;    proof-save-with-hole-regexp		; non-essential?
;    proof-showproof-command		; non-essential
;    proof-goal-command			; non-essential
;    proof-save-command			; do
;    proof-kill-goal-command		; do
    ))


;;;###autoload
(defun proof-config-done ()
  "Finish setup of Proof General scripting mode.
Call this function in the derived mode for the proof assistant to
finish setup which depends on specific proof assistant configuration."

  ;; Common configuration for shared script/other related buffers.
  (proof-config-done-related)

  ;; Make mode class "pg-sticky" so renaming doesn't change the mode.
  (put major-mode 'mode-class 'pg-sticky)

  (if (and proof-non-undoables-regexp
	   (not proof-ignore-for-undo-count))
      (setq proof-ignore-for-undo-count
	    proof-non-undoables-regexp))

  ;; Give warnings if some crucial settings haven't been made
  (dolist (sym proof-script-important-settings)
    (proof-warn-if-unset "proof-config-done" sym))

  ;; Additional key def for (first character of) terminal string
  (if proof-terminal-string
      (progn
	(define-key proof-mode-map
	  (vconcat [(control c)] (vector (aref proof-terminal-string 0)))
	  'proof-electric-terminator-toggle)
	(define-key proof-mode-map (vector (aref proof-terminal-string 0))
	  'proof-electric-terminator)))

  ;; Toolbar, main menu (loads proof-toolbar,setting p.-toolbar-scripting-menu)
  (proof-toolbar-setup)

  ;; Menus: the Proof-General and the specific menu
  (proof-menu-define-main)
  (proof-menu-define-specific)
  (easy-menu-add proof-mode-menu proof-mode-map)
  (easy-menu-add proof-assistant-menu proof-mode-map)

  ;; Define parsing functions
  (proof-setup-parsing-mechanism)

  ;; Setup imenu and add it to menu if enabled.
  (proof-setup-imenu)
  (proof-imenu-enable)

  ;; Save file-less script mode buffers in case of accidental exit
  (or (buffer-file-name)
      (setq buffer-offer-save t))

  ;; Turn on autosend if enabled
  (proof-autosend-enable 'nomsg)

  ;; Invisibility management: show ellipsis
  (mapc (lambda (p)
	    (add-to-invisibility-spec 
	     (cons (pg-invisible-prop p) t)))
	  pg-all-idioms)

  ;; If we're excited to get going straightaway, make and layout windows
  (when proof-layout-windows-on-visit-file
      (proof-shell-make-associated-buffers)
      (proof-layout-windows))

  ;; Make sure the user has been welcomed!
  (proof-splash-message))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Subroutines of proof-config-done
;;

(defun proof-setup-parsing-mechanism ()
  "Choose parsing mechanism according to different kinds of script syntax.
Choice of function depends on configuration setting."
  (unless (fboundp 'proof-segment-up-to)
    (defalias 'proof-segment-up-to 'proof-segment-up-to-parser)
    (cond
     (proof-script-parse-function
      ;; already set, nothing to do
      )
     (proof-script-sexp-commands
      (setq proof-script-parse-function 'proof-script-generic-parse-sexp))
     (proof-script-command-start-regexp
      (setq proof-script-parse-function 'proof-script-generic-parse-cmdstart))
     ((or proof-script-command-end-regexp proof-terminal-string)
      (setq  proof-script-parse-function 'proof-script-generic-parse-cmdend)
      (unless proof-script-command-end-regexp
	(proof-warn-if-unset "probof-config-done" 'proof-terminal-string)
	(setq proof-script-command-end-regexp
	      (if proof-terminal-string
		  (regexp-quote proof-terminal-string)
		"$"))))
     (t
      (error "Configuration error: must set `proof-terminal-string' or one of its friends")))))

(defun proof-setup-imenu ()
  "Setup a default for imenu, perhaps using `proof-script-imenu-generic-expression'."
  (unless ;; already setup, leave it alone
      (and (boundp 'imenu-generic-expression)
	   imenu-generic-expression)
    (set (make-local-variable 'imenu-generic-expression)
	 (or
	  proof-script-imenu-generic-expression
	     (delq nil
	       (list
		(if proof-goal-with-hole-regexp
		    (list nil proof-goal-with-hole-regexp
			  proof-goal-with-hole-result))
		(if proof-save-with-hole-regexp
		    (list "Saves" proof-save-with-hole-regexp
			  proof-save-with-hole-result))))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Caching parse results for unedited portions of the buffer
;;
;; Added in PG 4.1
;;
;; A simplistic first attempt: we only cache the last region that was
;; parsed.  It would be better to maintain a parse cache for the
;; unedited prefix of the buffer or for individual segments like
;; PGIP Emacs PG does.  Or to parse during idle like font-lock.
;;
;; We assume that extending the parsed region can only possibly affect
;; the last command in the cache but leaves the rest intact.  (NB: in
;; Isabelle/Isar a command can be a proper prefix of a longer one and
;; there are no explicit terminators).


(deflocal proof-segment-up-to-cache nil
  "Cache used to speed up parsing.
Stores recent results of `proof-segment-up-to' in reverse order.")

(deflocal proof-segment-up-to-cache-start 0)
(deflocal proof-segment-up-to-cache-end 0)
(deflocal proof-last-edited-low-watermark nil)

(defun proof-segment-up-to-using-cache (pos &rest args)
  "A wrapper for `proof-segment-up-to' which uses a cache to speed things up."
  (let (res)
    (if (and
	 proof-use-parser-cache      ;; safety off valve
	 proof-segment-up-to-cache
	 (>= (proof-queue-or-locked-end) 
	     proof-segment-up-to-cache-start)
	 (setq res (proof-segment-cache-contents-for pos))
	 ;; only use result if last edit point is >1 segment below
	 (or (not proof-last-edited-low-watermark)
	     (> proof-last-edited-low-watermark
		(nth 2 (car res)))))
	(progn
	  (proof-debug "proof-segment-up-to-using-cache: re-using %d parse results"
		       (length res))
	  res)
      ;; Cache not useful, perform a fresh parse
      (let ((semis (proof-segment-up-to pos args)))
	(setq proof-segment-up-to-cache (reverse semis))
	(setq proof-segment-up-to-cache-start (proof-queue-or-locked-end))
	(setq proof-segment-up-to-cache-end (if semis (nth 2 (car semis)) 0))
	(when proof-last-edited-low-watermark
	  (if (<= proof-last-edited-low-watermark
		  proof-segment-up-to-cache-end)
	      (setq proof-last-edited-low-watermark nil)))
	semis))))

(defun proof-segment-cache-contents-for (pos)
  ;; only return result if we have cache for complete region
  (when (<= pos proof-segment-up-to-cache-end) 
    (let ((semis   proof-segment-up-to-cache)
	  (start  (proof-queue-or-locked-end))
	  usedsemis semiend)
      (while semis
	(setq semiend (nth 2 (car semis)))
	(if (> semiend start)
	    (setq usedsemis (cons (car semis) usedsemis)))
	(setq semis
	      (if (or (< semiend pos) 
		      ;; matches parsing-until-find-something behaviour
		      (and (= semiend pos) (not usedsemis)))
		  (cdr semis))))
      usedsemis)))

(defun proof-script-after-change-function (start end prelength)
  "Value for `after-change-functions' in proof script buffers."
  (setq proof-last-edited-low-watermark
	(min (or proof-last-edited-low-watermark (point-max))
	     start))
  (if (and (markerp proof-overlay-arrow)
	   (marker-position proof-overlay-arrow)
	   ; only move marker up:
	   ;(< start (marker-position proof-overlay-arrow))
	   (>= start (proof-queue-or-locked-end)))
      (proof-set-overlay-arrow (proof-queue-or-locked-end))))

(defun proof-script-set-after-change-functions ()
  "Set `after-change-functions' for script buffers."
  (add-hook 'after-change-functions
	    'proof-script-after-change-function nil t))



(provide 'proof-script)
;;; proof-script.el ends here
