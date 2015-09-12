;;; proof-menu.el --- Menus, keymaps, misc commands for Proof General
;;
;; Copyright (C) 2000,2001,2009,2010,2011 LFCS Edinburgh.
;; Authors:   David Aspinall
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; proof-menu.el,v 12.3 2012/08/16 15:01:05 da Exp
;;

(require 'cl)				; mapcan

;;; Code:
(eval-when (compile)
  (defvar proof-assistant-menu nil) ; defined by macro in proof-menu-define-specific
  (defvar proof-mode-map nil))

(require 'proof-utils)    ; proof-deftoggle, proof-eval-when-ready-for-assistant
(require 'proof-useropts)
(require 'proof-config)


    


(eval-when-compile
  (defvar proof-assistant-menu)	  ; defined by macro in proof-menu-define-specific
  (defvar proof-mode-map))
    


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Miscellaneous commands
;;;

(defvar proof-display-some-buffers-count 0)

(defun proof-display-some-buffers ()
  "Display the reponse, trace, goals, or shell buffer, rotating.
A fixed number of repetitions of this command switches back to
the same buffer.
Also move point to the end of the response buffer if it's selected.
If in three window or multiple frame mode, display two buffers.
The idea of this function is to change the window->buffer mapping
without adjusting window layout."
  (interactive)
  ;; Idea: a humane toggle, which allows habituation.
  ;; E.g. two taps of C-c C-l always shows the goals buffer, three the
  ;; trace buffer, etc.  (Makes less sense from the menu, though,
  ;; where it seems more natural just to rotate from last position)
  (cond
   ((and (called-interactively-p 'any)
	 (eq last-command 'proof-display-some-buffers))
    (incf proof-display-some-buffers-count))
   (t
    (setq proof-display-some-buffers-count 0)))
  (let* ((assocbufs   (remove-if-not 'buffer-live-p
				     (list proof-response-buffer
					   proof-thms-buffer
					   proof-trace-buffer
					   proof-goals-buffer
					   )))
					;proof-shell-buffer
	 (numassoc    (length assocbufs)))
    ;; If there's no live other buffers, we don't do anything.
    (unless (zerop numassoc)
      (let
	 ((selectedbuf (nth (mod proof-display-some-buffers-count
				 numassoc) assocbufs))
	  (nextbuf     (nth (mod (1+ proof-display-some-buffers-count)
				 numassoc) assocbufs)))
	(cond
	 ((or proof-three-window-enable proof-multiple-frames-enable)
	  ;; Display two buffers: next in rotation and goals/response
	  ;; FIXME: this doesn't work as well as it might.
	  (proof-switch-to-buffer selectedbuf 'noselect)
	  (proof-switch-to-buffer (if (eq selectedbuf proof-goals-buffer)
				      proof-response-buffer
				    proof-goals-buffer) 'noselect))
	 (selectedbuf
	  (proof-switch-to-buffer selectedbuf 'noselect)))
	(if (eq selectedbuf proof-response-buffer)
	    (set-window-point (get-buffer-window proof-response-buffer t)
			      (point-max)))
	(pg-response-buffers-hint (buffer-name nextbuf))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Key bindings
;;;

;;;###autoload
(defun proof-menu-define-keys (map)
  "Prover specific keymap under C-c C-a."
  ;; M-a and M-e are usually {forward,backward}-sentence.
  ;; Some modes also override these with similar commands
  (define-key map [(meta a)] 'proof-backward-command)
  (define-key map [(meta e)] 'proof-forward-command)
  (define-key map [(meta up)] 'proof-backward-command)
  (define-key map [(meta down)] 'proof-forward-command)
  (define-key map [(control meta a)] 'proof-goto-command-start)
  (define-key map [(control meta e)] 'proof-goto-command-end)
  (define-key map [(control c) (control b)] 'proof-process-buffer)
  ;; C-c C-c is proof-interrupt-process in universal-keys
  (define-key map [(control c) (control d)] 'proof-tree-external-display-toggle)
  ;; C-c C-f is proof-find-theorems in universal-keys
  (define-key map [(control c) (control H)] 'proof-help)
  ;; C-c C-l is proof-layout-windows in universal-keys
  ;; C-c C-n is proof-assert-next-command-interactive in universal-keys
  ;; C-c C-o is proof-display-some-buffers in universal-keys
  (define-key map [(control c) (control p)] 'proof-prf)
  (define-key map [(control c) (control r)] 'proof-retract-buffer)
  (define-key map [(control c) (control s)] 'proof-toggle-active-scripting)
  (define-key map [(control c) (control t)] 'proof-ctxt)
  (define-key map [(control c) (control i)] 'proof-query-identifier)
  ;; C-c C-u is proof-undo-last-successful-command in universal-keys
  ;; C-c C-w is pg-response-clear-displays in universal-keys
  (define-key map [(control c) (control z)] 'proof-frob-locked-end)
  (define-key map [(control c) (control backspace)]
    'proof-undo-and-delete-last-successful-command)
  ;; C-c C-v is proof-minibuffer-cmd in universal-keys
  ;; C-c C-. is proof-goto-end-of-locked in universal-keys
  (define-key map [(control c) (control return)] 'proof-goto-point)
  (define-key map [(control c) ?v] 'pg-toggle-visibility)
  (define-key map [(control meta mouse-3)] 'proof-mouse-goto-point)
  ;; NB: next binding overwrites comint-find-source-code.
  (define-key map [(meta p)] 'pg-previous-matching-input-from-input)
  (define-key map [(meta n)] 'pg-next-matching-input-from-input)
  ;; Standard binding for completion
  (define-key map [(control return)] 'proof-script-complete)
  (define-key map [(control c) (control ?\;)] 'pg-insert-last-output-as-comment)
  ;;
  (define-key map [(control meta up)] 'pg-move-region-up)
  (define-key map [(control meta down)] 'pg-move-region-down)
  ;;
  (define-key map [(control c) ?b] 'proof-toolbar-toggle)
  (define-key map [(control c) ?>] 'proof-autosend-toggle)
  ;; Add the universal keys bound in all PG buffers.
  ;; NB: C-c ` is next-error in universal-keys
  (proof-define-keys map proof-universal-keys))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Functions to define the menus
;;;

;; The main Proof-General generic menu

;;;###autoload
(defun proof-menu-define-main ()
  (easy-menu-define
   proof-mode-menu
   proof-mode-map
   "The main Proof General menu"
   (proof-main-menu)))

;; The proof assistant specific menu

(defvar proof-menu-favourites nil
  "The Proof General favourites menu for the current proof assistant.")

(defvar proof-menu-settings nil
  "Settings submenu for Proof General.")

;;;###autoload
(defun proof-menu-define-specific ()
  (easy-menu-do-define
   'proof-assistant-menu
   proof-mode-map
   (concat "The menu for " proof-assistant)
   (cons proof-assistant
	    (append
	     (proof-ass menu-entries)
	     '("----")
	     (or proof-menu-favourites
		 (proof-menu-define-favourites-menu))
	     (or proof-menu-settings
		 (proof-menu-define-settings-menu))
	     '("----")
	     (list
	      (vector
	       (concat "Start " proof-assistant)
	     'proof-shell-start
	     ':active '(not (proof-shell-live-buffer)))
	      (vector
	       (concat "Exit " proof-assistant)
	       'proof-shell-exit
	       ':active '(proof-shell-live-buffer))
	      ;; TODO: doc <PA>-set-command here
	      (vector
	       (concat "Set " proof-assistant " Command")
	       (proof-ass-sym set-command)
	       ':visible '(fboundp (proof-ass-sym set-command))))
	     '("----")
	     (list
	      (cons "Help"
		    (append
		     (list
		      (vector
		       (concat proof-assistant " Information")
		       'proof-help
		       :visible proof-info-command)
		      (vector
		       (concat proof-assistant " Web Page")
		       '(browse-url proof-assistant-home-page)
		       :visible proof-assistant-home-page))
		     (proof-ass help-menu-entries))))))))

(defun proof-assistant-menu-update ()
  "Update proof assistant menu in scripting buffers."
  (proof-map-buffers (proof-buffers-in-mode proof-mode-for-script)
    (easy-menu-remove proof-assistant-menu)
    (proof-menu-define-settings-menu)
    (proof-menu-define-specific)
    (easy-menu-add proof-assistant-menu (proof-ass mode-map))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Contents of sub menus
;;

(defvar proof-help-menu
  '("Help"
    ["About PG"        proof-splash-display-screen t]
    ["Info"	(info "ProofGeneral") t]
    ["Homepage"	(browse-url proof-general-home-page) t]
    ["Send Bug Report" proof-submit-bug-report t])
  "Proof General help menu.")

(defvar proof-show-hide-menu
  '(("Show All"
     ["Proofs"    (pg-show-all-portions 'proof) t]
     ["Commands"  (pg-show-all-portions 'command) t]
     ["Comments"  (pg-show-all-portions 'comment) t])
    ("Hide All"
     ["Proofs"     (pg-show-all-portions 'proof 'hide) t]
     ["Commands"   (pg-show-all-portions 'command 'hide) t]
     ["Comments"   (pg-show-all-portions 'comment 'hide) t]))
  "Show/hide submenu.")

(defvar proof-buffer-menu
  (cons "Buffers"
	'(["Layout Windows"
	   proof-layout-windows]
	  ["Rotate Output Buffers"
	   proof-display-some-buffers
	   :visible (not proof-three-window-enable)
	   :active (buffer-live-p proof-goals-buffer)]
	  ["Clear Responses"
	   pg-response-clear-displays
	   :active (buffer-live-p proof-response-buffer)]
	  "----"
	  ["Active Scripting"
	   (proof-switch-to-buffer proof-script-buffer)
	   :active (buffer-live-p proof-script-buffer)]
	  ["Goals"
	   (proof-switch-to-buffer proof-goals-buffer t)
	   :active (buffer-live-p proof-goals-buffer)]
	  ["Response"
	   (proof-switch-to-buffer proof-response-buffer t)
	   :active (buffer-live-p proof-response-buffer)]
	  ["Trace"
	   (proof-switch-to-buffer proof-trace-buffer)
	   :active (buffer-live-p proof-trace-buffer)
	   :visible proof-shell-trace-output-regexp]
	  ["Shell"
	   (proof-switch-to-buffer proof-shell-buffer)
	   :active (buffer-live-p proof-shell-buffer)]))
  "Proof General buffer menu.")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; "Quick" (or main) options
;;

;; First, make the togglers used in options menu below

(proof-deftoggle proof-script-fly-past-comments)
(proof-deftoggle proof-delete-empty-windows)
(proof-deftoggle proof-shrink-windows-tofit)
(proof-deftoggle proof-multiple-frames-enable proof-multiple-frames-toggle)
(proof-deftoggle proof-layout-windows-on-visit-file 
		 proof-layout-windows-eagerly-toggle)
(proof-deftoggle proof-three-window-enable proof-three-window-toggle)
(proof-deftoggle proof-auto-raise-buffers proof-auto-raise-toggle)
(proof-deftoggle proof-disappearing-proofs)
(proof-deftoggle proof-full-annotation)
(proof-deftoggle proof-colour-locked)
(proof-deftoggle proof-sticky-errors)
(proof-deftoggle proof-shell-quiet-errors)
(proof-deftoggle proof-minibuffer-messages)
(proof-deftoggle proof-output-tooltips)
(proof-deftoggle proof-autosend-enable proof-autosend-toggle)
(proof-deftoggle proof-fast-process-buffer)
(proof-deftoggle proof-imenu-enable proof-imenu-toggle)
(proof-deftoggle proof-keep-response-history)

(proof-eval-when-ready-for-assistant
 ;; togglers for settings separately configurable per-prover
  (proof-deftoggle-fn
   (proof-ass-sym unicode-tokens-enable) 'proof-unicode-tokens-toggle)
  (proof-deftoggle-fn
   (proof-ass-sym maths-menu-enable) 'proof-maths-menu-toggle)
  (proof-deftoggle-fn (proof-ass-sym mmm-enable) 'proof-mmm-toggle))

(defun proof-keep-response-history ()
  "Enable associated buffer histories following `proof-keep-response-history'."
  (if proof-keep-response-history
      (proof-map-buffers (proof-associated-buffers) (bufhist-init))
    (proof-map-buffers (proof-associated-buffers) (bufhist-exit))))

;; Here is the menu

(defconst proof-quick-opts-menu
  (cons
   "Quick Options"
   `(

;;; TODO: Add this in PG 4.0 once bufhist robust; see trac #169
;;;      ["Response history" proof-keep-response-history-toggle
;;;       :style toggle
;;;       :selected proof-keep-response-history]

     ("Processing"
      ["Fast Process Buffer" proof-fast-process-buffer-toggle
       :style toggle
       :selected proof-fast-process-buffer
       :help "Use a fast loop when processing whole buffer (disables input)"]
      ["Electric Terminator" proof-electric-terminator-toggle
       :style toggle
       :selected proof-electric-terminator-enable
       :help "Automatically send commands when terminator typed"]
      ["Beep on Errors" proof-shell-quiet-errors-toggle
       :style toggle
       :selected (not proof-shell-quiet-errors)
       :help "Beep on errors or interrupts"]      
      ["Fly Past Comments" proof-script-fly-past-comments-toggle
       :style toggle
       :selected proof-script-fly-past-comments
       :help "Coalesce and skip over successive comments"]
      ["Full Annotation" proof-full-annotation-toggle
       :style toggle
       :selected proof-full-annotation
       :help "Record full information to decorate scripts (may cause slowdown)"]
     ["Process Automatically" proof-autosend-toggle
       :style toggle
       :selected proof-autosend-enable
       :help "Automatically send commands when idle"]
      ("Automatic Processing Mode"
       ["Next Command"
	(customize-set-variable 'proof-autosend-all nil)
       :style radio
       :selected (eq proof-autosend-all nil)
       :active proof-autosend-enable
       :help "Automatically try out the next commmand"]
       ["Send Whole Buffer"
	(customize-set-variable 'proof-autosend-all t)
	:style radio
	:selected (eq proof-autosend-all t)
	:active proof-autosend-enable
	:help "Automatically send the whole buffer"]))
     ("Display"
      ["Toolbar" proof-toolbar-toggle
       :style toggle
       :visible (featurep 'tool-bar)
       :selected proof-toolbar-enable
       :help "Use the Proof General toolbar"]
      ["Unicode Tokens"
      (proof-unicode-tokens-toggle (if (boundp 'unicode-tokens-mode)
				       (if unicode-tokens-mode 0 1) 1))
      :active (proof-unicode-tokens-support-available)
      :style toggle
      :selected (and (boundp 'unicode-tokens-mode)
		     unicode-tokens-mode)
      :help "Enable display of tokens as Unicode characters"]
      ["Minibuffer Messages" proof-minibuffer-messages-toggle
       :style toggle
       :selected proof-minibuffer-messages
       :help "Show progress messages in minibuffer"]
      ["Output Tooltips" proof-output-tooltips-toggle
       :style toggle
       :selected proof-output-tooltips
       :help "Add tooltips for prover output"]
      ["Auto Raise" proof-auto-raise-toggle
       :style toggle
       :selected proof-auto-raise-buffers
       :help "Automatically raise buffers when output arrives"]
      ["Use Three Panes" proof-three-window-toggle
       :style toggle
       :active (not proof-multiple-frames-enable)
       :selected proof-three-window-enable
       :help "Use three panes"]
      ;; We use non-Emacs terminology "Windows" in this menu to help
      ;; non-Emacs users.  Cf. Gnome usability studies: menus saying
      ;; "Web Browser" more useful to novices than menus saying "Mozilla"!!
      ["Layout Eagerly" proof-layout-windows-eagerly-toggle
       :style toggle
       :selected proof-layout-windows-on-visit-file
       :help "Display prover output windows when script file is opened."]
      ["Multiple Windows" proof-multiple-frames-toggle
       :active (and window-system t)
       :style toggle
       :selected proof-multiple-frames-enable
       :help "Use multiple windows (Emacs frames) for display"]
      ["Delete Empty Panes" proof-delete-empty-windows-toggle
       :active (not proof-multiple-frames-enable)
       :style toggle
       :selected proof-delete-empty-windows
       :help "Dynamically remove empty panes from display"]
      ["Shrink to Fit" proof-shrink-windows-tofit-toggle
       :active (not proof-multiple-frames-enable)
       :style toggle
       :selected proof-shrink-windows-tofit
       :help "Dynamically shrink size of output panes to fit contents"]
      ["Colour Locked" proof-colour-locked-toggle
       :style toggle
       :selected proof-colour-locked
       :help "Add highlighting to locked (checked) text"]
      ["Sticky Errors" proof-sticky-errors-toggle
       :style toggle
       :selected proof-sticky-errors
       :help "Highlight commands that caused errors"]
      ["Disppearing Proofs" proof-disappearing-proofs-toggle
       :style toggle
       :selected proof-disappearing-proofs
       :help "Hide proofs as they are completed"]
      "----"
      ["Document Centred" proof-set-document-centred
       :help "Select options for document-centred working"]
      ["Default" proof-set-non-document-centred
       :help "Set options for classic Proof General interaction"])
     ("Read Only"
      ["Strict Read Only"
       (customize-set-variable 'proof-strict-read-only t)
       :style radio
       :selected (eq proof-strict-read-only t)
       :help "Do not allow editing in processed region"]
      ["Undo On Edit"
       (customize-set-variable 'proof-strict-read-only 'retract)
      :style radio
      :selected (eq proof-strict-read-only 'retract)
      :help "Automatically retract on edits in processed region"]
      ["Freely Edit"
       (customize-set-variable 'proof-strict-read-only nil)
      :style radio
      :selected (null proof-strict-read-only)
      :help "No write protection, edit anywhere.  Dangerous!"])
     ("Follow Mode"
      ["Follow Locked Region"
       (customize-set-variable 'proof-follow-mode 'locked)
       :style radio
       :selected (eq proof-follow-mode 'locked)
       :help "Point follows the locked region"]
;; Not implemented.  See Trac #187
;;       ["Follow On Success"
;;        (customize-set-variable 'proof-follow-mode 'followsuccess)
;;        :style radio
;;        :selected (eq proof-follow-mode 'followdown)]
      ["Follow Locked Region Down"
       (customize-set-variable 'proof-follow-mode 'followdown)
       :style radio
       :selected (eq proof-follow-mode 'followdown)
       :help "Point follows the locked region when processsing"]
      ["Keep Locked Region Displayed"
       (customize-set-variable 'proof-follow-mode 'follow)
       :style radio
       :selected (eq proof-follow-mode 'follow)
       :help "Scroll to ensure end of lock region is visible"]
      ["Never Move"
       (customize-set-variable 'proof-follow-mode 'ignore)
       :style radio
       :selected (eq proof-follow-mode 'ignore)
       :help "Do not move cursor during processing"])
     ("Deactivate Action"
      ["Retract"
       (customize-set-variable 'proof-auto-action-when-deactivating-scripting
			       'retract)
       :style radio
       :selected (eq proof-auto-action-when-deactivating-scripting 'retract)]
      ["Process"
       (customize-set-variable 'proof-auto-action-when-deactivating-scripting
			       'process)
       :style radio
       :selected (eq proof-auto-action-when-deactivating-scripting 'process)]
      ["Query"
       (customize-set-variable 'proof-auto-action-when-deactivating-scripting nil)
       :style radio
       :selected (null proof-auto-action-when-deactivating-scripting)])

     ("Minor Modes"
     ["Unicode Maths Menu"
      (proof-maths-menu-toggle (if (boundp 'maths-menu-mode)
				       (if maths-menu-mode 0 1) 1))
      :active (proof-maths-menu-support-available)
      :style toggle
      :selected (and (boundp 'maths-menu-mode) maths-menu-mode)
      :help "Maths menu for inserting Unicode characters"]

     ["Multiple Modes" (proof-mmm-toggle (if mmm-mode 0 1))
      :active (proof-mmm-support-available)
      :style toggle
      :selected (and (boundp 'mmm-mode) mmm-mode)
      :help "Allow multiple major modes"]

     ["Index Menu" proof-imenu-toggle
      :active (stringp (locate-library "imenu"))
      :style toggle
      :selected proof-imenu-enable
      :help "Generate an index menu of definitions, display which function in modeline"]

     "----"
     
     ;; NB: next group not saved, just for convenience here to
     ;; hint they're defined for PG
     ["Outline" outline-minor-mode
      :active (stringp (locate-library "outline"))
      :style toggle
      :selected (and (boundp 'outline-minor-mode) outline-minor-mode)
      :help "Outline mode for folding (note: option not saved)"]

     ["Hide/Show" hs-minor-mode
      :active (stringp (locate-library "hideshow"))
      :style toggle
      :selected (and (boundp 'hs-minor-mode) hs-minor-mode)
      :help "Hide/Show mode for folding (note: option not saved)"]

     ["Speedbar" speedbar
      :active (stringp (locate-library "speedbar"))
      :style toggle
      :selected (and (boundp 'speedbar-frame) speedbar-frame)
      :help "Speedbar navigation window (note: option not saved)"])

     "----"
     ["Reset Options" (proof-quick-opts-reset)
      (proof-quick-opts-changed-from-defaults-p)]
     ["Save Options" (proof-quick-opts-save)
      (proof-quick-opts-changed-from-saved-p)]))
  "Proof General quick options.")

(defun proof-quick-opts-vars ()
  "Return a list of the quick option variables."
  (list
   'proof-electric-terminator-enable
   'proof-autosend-enable
   'proof-fast-process-buffer
   'proof-script-fly-past-comments
   'proof-disappearing-proofs
   'proof-full-annotation
   'proof-strict-read-only
   (proof-ass-sym unicode-tokens-enable)
   (proof-ass-sym maths-menu-enable)
   (proof-ass-sym mmm-enable)
   'proof-toolbar-enable
   'proof-keep-response-history
   'proof-imenu-enable
   'proof-shell-quiet-errors
   ;; Display sub-menu
   'proof-minibuffer-messages
   'proof-auto-raise-buffers
   'proof-three-window-enable
   'proof-delete-empty-windows
   'proof-multiple-frames-enable
   'proof-shrink-windows-tofit
   'proof-multiple-frames-enable
   'proof-colour-locked
   'proof-sticky-errors
   ;; Follow mode sub-menu
   'proof-follow-mode
   ;; Deactivate scripting action
   proof-auto-action-when-deactivating-scripting))

(defun proof-quick-opts-changed-from-defaults-p ()
  ;; NB: would be nice to add.  Custom support?
  t)

(defun proof-quick-opts-changed-from-saved-p ()
  ;; NB: would be nice to add.  Custom support?
  t)

;;
;; Changing several options together (ugly UI)
;;

(defun proof-set-document-centred ()
  "Select options for document-centred working"
  (interactive)
  (proof-full-annotation-toggle 1)
  (proof-auto-raise-toggle 0)
  (proof-colour-locked-toggle 0)
  (proof-sticky-errors-toggle 1)
  (proof-autosend-toggle 1)
  (customize-set-variable 'proof-strict-read-only 'retract)
  (customize-set-variable 'proof-autosend-all t)
  (customize-set-variable 'proof-follow-mode 'ignore))


(defun proof-set-non-document-centred ()
  "Set options for classic Proof General interaction"
  (interactive)
  ;; default: (proof-full-annotation-toggle 1) 
  (proof-auto-raise-toggle 1)
  (proof-colour-locked-toggle 1)
  (proof-sticky-errors-toggle 0)
  (proof-autosend-toggle 0)
  ;; default: (customize-set-variable 'proof-strict-read-only 'retract)
  (customize-set-variable 'proof-autosend-all nil)
  (customize-set-variable 'proof-follow-mode 'ignore))


;;
;; We have menu items for saving options and reseting them.
;; We could just store the settings automatically (no save),
;; but then the reset option would have to change to restore
;; to manufacturer settings (rather then user-stored ones).
;;
(defun proof-quick-opts-save ()
  "Save current values of PG Options menu items using custom."
  (interactive)
  (apply 'pg-custom-save-vars (proof-quick-opts-vars)))

(defun proof-quick-opts-reset ()
  "Reset PG Options menu to default (or user-set) values, using custom."
  (interactive)
  (apply 'pg-custom-reset-vars (proof-quick-opts-vars)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Main menu
;;


(defconst proof-config-menu
  (list "----"
	;; buffer menu might better belong in toolbar menu?
	proof-buffer-menu
	proof-quick-opts-menu)
  "Proof General configuration menu.")

(defconst proof-advanced-menu
  (cons "Advanced"
	(append
	 '(["Complete Identifier" proof-script-complete
	    :help "Complete the identifier at point"]
	   ["Insert Last Output" pg-insert-last-output-as-comment
	    :active proof-shell-last-output
	    :help "Insert the last output into the proof script as a comment"]
	   ["Make Movie" pg-movie-export
	    :help "Export processed portion as Movie XML file (enable Full Annotations first!)"])
	 (list "-----")
	 proof-show-hide-menu
	 (list "-----")
	 (list (customize-menu-create 'proof-general))
	 (list (customize-menu-create 'proof-general-internals "Internals"))))
  "Advanced sub-menu of script functions and customize.")


(defvar proof-menu
  '(["Next Error" proof-next-error
     :active pg-next-error-regexp]
    ["Scripting Active" proof-toggle-active-scripting
     :style toggle
     :selected (eq proof-script-buffer (current-buffer))])
  "The Proof General generic menu for scripting buffers.")


(defun proof-main-menu ()
  "Construct and return PG main menu used in scripting buffers."
  (cons proof-general-name
	(append
	 (proof-toolbar-scripting-menu)
	 proof-menu
	 proof-config-menu
	 (list (customize-menu-create 'proof-user-options "Customize Options"))
	 (list proof-advanced-menu)
	 (list proof-help-menu))))

;;;###autoload
(defun proof-aux-menu ()
  "Construct and return PG auxiliary menu used in non-scripting buffers."
  (cons proof-general-name
	(append
	 (proof-toolbar-scripting-menu)
	 proof-config-menu
	 (list proof-help-menu))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Favourites mechanism for prover-specific menu
;;;

(defun proof-menu-define-favourites-menu ()
  "Return menu generated from `PA-favourites'."
  (let ((favs (reverse (proof-ass favourites))) ents)
    (while favs
      (setq ents (cons (apply 'proof-def-favourite (car favs)) ents))
      (setq favs (cdr favs)))
    (setq proof-menu-favourites
	  (list
	   (cons "Favourites"
		 (append ents
			 ;; (list "----")  doesn't work for adding before
			 '(["Add Favourite"
			    (call-interactively 'proof-add-favourite) t]
			   ["Delete Favourite"
			    (call-interactively 'proof-del-favourite) t]
			   ["Save Favourites"
			    (proof-save-favourites) t])))))))

;;; Define stuff from favourites

(defun proof-def-favourite (command inscript menuname &optional key new)
  "Define and a \"favourite\" proof assisant function.
See doc of `proof-add-favourite' for first four arguments.
Extra NEW flag means that this should be a new favourite, so check
that function defined is not already bound.
This function defines a function and returns a menu entry
suitable for adding to the proof assistant menu."
  (let* ((menunames	(split-string (downcase menuname)))
	 (menuname-sym  (proof-sym (mapconcat 'identity menunames "-")))
	 (menu-fn	menuname-sym) (i 1))
    (while (and new (fboundp menu-fn))
      (setq menu-fn (intern (concat (symbol-name menuname-sym)
				    "-" (int-to-string i))))
      (incf i))
    (if inscript
	(eval `(proof-defshortcut ,menu-fn ,command ,key))
      (eval `(proof-definvisible ,menu-fn ,command ,key)))
    ;; Return menu entry
    (vector menuname menu-fn t)))



;;; Commentary:
;; 

;;; Code for adding "favourites" to the proof-assistant specific menu

(defvar proof-make-favourite-cmd-history nil
  "History for proof-make-favourite.")

(defvar proof-make-favourite-menu-history nil
  "History for proof-make-favourite.")

(defun proof-save-favourites ()
  "Save favourites in customization settings."
  (interactive)
  (pg-custom-save-vars (proof-ass-sym favourites)))

(defun proof-del-favourite (menuname)
  "Delete \"favourite\" command recorded at MENUNAME."
  (interactive
   (list
    (completing-read "Menu item to delete: "
		     (mapcar 'cddr (proof-ass favourites))
		     nil t)))
  (let*
      ((favs       (proof-ass favourites))
       (rmfavs	   (remove-if
		    (lambda (f) (string-equal menuname (caddr f)))
		    favs)))
    (unless (equal favs rmfavs)
      (easy-menu-remove-item proof-assistant-menu
			     '("Favourites") menuname)
      (customize-set-variable  (proof-ass-sym favourites) rmfavs))))

(defun proof-read-favourite ()
  (let*
      ((guess  (buffer-substring (save-excursion
				   (beginning-of-line-text)
				   (point)) (point)))
       (cmd (read-string
	     (concat "Command to send to " proof-assistant ": ")
	     guess
	     proof-make-favourite-cmd-history))
       (ins (y-or-n-p "Should command be recorded in script? "))
       (men (read-string
	     "Name of command on menu: "
	     cmd
	     proof-make-favourite-menu-history))
       (key (if (y-or-n-p "Set a keybinding for this command? ")
		;; FIXME: better validation here would be to check
		;; this is a new binding, or remove old binding below.
		 (read-key-sequence
		  "Type the key to use (binding will be C-c C-a <key>): "
		  nil t))))
    ;; result
    (list cmd ins men key)))


(defun proof-add-favourite (command inscript menuname &optional key)
  "Define and add a \"favourite\" proof-assisant function to the menu bar.
The favourite function will issue COMMAND to the proof assistant.
COMMAND is inserted into script (not sent immediately) if INSCRIPT non-nil.
MENUNAME is the name of the function for the menu.
KEY is the optional key binding."
  (interactive (proof-read-favourite))
  (let*
      ((menu-entry (proof-def-favourite command inscript menuname key t))
       (favs       (proof-ass favourites))
       (rmfavs	   (remove-if
		    (lambda (f) (string-equal menuname (caddr f)))
		    favs))
       (newfavs    (append
		    rmfavs
		    (list (list command inscript menuname key)))))
    ;; If def succeeds, add to customize var
    (customize-set-variable  (proof-ass-sym favourites) newfavs)
    (easy-menu-add-item proof-assistant-menu
			'("Favourites") menu-entry "Add Favourite")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Proof assistant settings mechanism.
;;;

(defun proof-menu-define-settings-menu ()
  "Return menu generated from `proof-assistant-settings', update `proof-menu-settings'."
  (if proof-assistant-settings
      (let ((save  (list "----"
			 ["Reset Settings" (proof-settings-reset)
			  (proof-settings-changed-from-defaults-p)]
			 ["Save Settings" (proof-settings-save)
			  (proof-settings-changed-from-saved-p)]))
	    groups ents)
	(mapc (lambda (stg) (add-to-list 'groups (get (car stg) 'pggroup)))
	      proof-assistant-settings)
	(dolist (grp (reverse groups))
	  (let* ((gstgs (mapcan (lambda (stg)
				  (if (eq (get (car stg) 'pggroup) grp)
				      (list stg)))
				proof-assistant-settings))
		 (cmds  (mapcar (lambda (stg)
				  (apply 'proof-menu-entry-for-setting stg))
				(reverse gstgs))))
	    (setq ents
		  (if grp (cons (cons grp cmds) ents)
		    (append cmds
			    (if (> (length groups) 1) '("----"))
			    ents)))))
	(setq proof-menu-settings
	      (list (cons "Settings"
			  (nconc ents save)))))))


(defun proof-menu-entry-name (symbol)
  "Return a nice menu entry name for SYMBOL."
  (let ((grp (get symbol 'pggroup))
	(nm  (symbol-name symbol)))
    (upcase-initials
     (replace-regexp-in-string "-" " "
      ;; strip the group name from the menu entry name.
      (if grp (replace-regexp-in-string (concat (downcase grp) ":") "" nm)
	nm)))))

(defun proof-menu-entry-for-setting (symbol setting type descr)
  (let ((entry-name  (proof-menu-entry-name symbol))
	(pasym	     (proof-ass-symv symbol)))
    (cond
     ((eq type 'boolean)
      (vector entry-name
	      (proof-deftoggle-fn pasym)
	      :style 'toggle
	      :selected pasym
	      :help descr))
     ((eq type 'integer)
      (vector entry-name
	      (proof-defintset-fn pasym)
	      :help descr))
     ((eq type 'number)
      (vector entry-name
	      (proof-deffloatset-fn pasym)
	      :help descr))
     ((eq type 'string)
      (vector entry-name
	      (proof-defstringset-fn pasym)
	      :help descr)))))

(defun proof-settings-vars ()
  "Return a list of proof assistant setting variables."
  (mapcar (lambda (setting) (proof-ass-symv (car setting)))
	  proof-assistant-settings))

(defun proof-settings-changed-from-defaults-p ()
  ;; FIXME: would be nice to add.  Custom support?
  t)

(defun proof-settings-changed-from-saved-p ()
  ;; FIXME: would be nice to add.  Custom support?
  t)

(defun proof-settings-save ()
  "Save current values of proof assistant settings using Custom."
  (interactive)
  (apply 'pg-custom-save-vars (proof-settings-vars)))

(defun proof-settings-reset ()
  "Reset proof assistant settings to their default values."
  (interactive)
  (apply 'pg-custom-reset-vars (proof-settings-vars)))

(defun proof-assistant-invisible-command-ifposs (cmd)
  "Send CMD as an \"invisible command\" if the proof process is available."
  ;; FIXME: better would be to queue the command, or even interrupt a
  ;; queue in progress.  Also must send current settings at start of
  ;; session somehow.  (This might happen automatically if a queue of
  ;; deffered commands is set, since defcustom calls proof-set-value
  ;; even to set the default/initial value?)
  (if (proof-shell-available-p)
      (progn
	(proof-shell-invisible-command cmd t)
	;; refresh display,
	;; FIXME: should only do if goals display is active,
	;; messy otherwise.
	;; (we need a new flag for "active goals display").
	;; PG 3.5 (patch 22.04.04):
	;; Let's approximate that by looking at proof-nesting-depth.
	(if (and proof-showproof-command
		 (> proof-nesting-depth 0))
	    (proof-shell-invisible-command proof-showproof-command))
	;;  Could also repeat last command if non-state destroying.
	)))

(defun proof-maybe-askprefs ()
  "If `proof-use-pgip-askprefs' is non-nil, try to issue <askprefs>.
This will configure dynamic settings used in the current prover session
and extend `proof-assistant-settings'.
We first clear the dynamic settings from `proof-assistant-settings'."
  (when (and proof-use-pgip-askprefs proof-shell-issue-pgip-cmd)
    (let (newsettings)
      (dolist (setting proof-assistant-settings)
	(let ((name (car setting)))
	  (if (get name 'pgdynamic)
	      (undefpgcustom name)
	    (push setting newsettings))))
      (setq proof-assistant-settings newsettings))
    (pg-pgip-askprefs)))


(defun proof-assistant-settings-cmd (setting)
  "Return string for making SETTING in Proof General customization."
  (let ((expr (assq setting proof-assistant-settings)))
    (if (and expr (cadr expr))
	(proof-assistant-format
	 (cadr expr)
	 (eval (proof-ass-symv (car expr)))))))

(defun proof-assistant-settings-cmds ()
  "Return strings for settings kept in Proof General customizations."
  (let (cmds)
    (dolist (setting proof-assistant-settings)
      (let ((sym       (car setting))
	    (pacmd     (cadr setting))) 
	(if (and pacmd
		 (or (not (get sym 'pgdynamic))
		     (proof-ass-differs-from-default sym)))
	    (push (proof-assistant-format pacmd
					  (eval (proof-ass-symv sym)))
		  cmds))))
    cmds))


(defvar proof-assistant-format-table
  (list
   (cons "%b" '(proof-assistant-format-bool curvalue))
   (cons "%i" '(proof-assistant-format-int curvalue))
   (cons "%f" '(proof-assistant-format-float curvalue))
   (cons "%s" '(proof-assistant-format-string curvalue)))
  "Table to use with `proof-format' for formatting CURVALUE for assistant.
NB: variable curvalue is dynamically scoped (used in `proof-assistant-format').")

(defun proof-assistant-format-bool (value)
  (if value proof-assistant-true-value proof-assistant-false-value))

(defun proof-assistant-format-int (value)
  (funcall proof-assistant-format-int-fn value))

(defun proof-assistant-format-float (value)
  (funcall proof-assistant-format-float-fn value))

(defun proof-assistant-format-string (value)
  (funcall proof-assistant-format-string-fn value))

(defun proof-assistant-format (string curvalue)
  "Replace a format characters in STRING by formatted CURVALUE.
Format character is one of %b, %i, %f, or %s.
Formatting suitable for current proof assistant, controlled by
`proof-assistant-format-table' which see.
Finally, apply `proof-assistant-setting-format' if non-nil.
Alternatively, STRING can be a function which yields a string when applied
to the CURVALUE.
As another special case for boolean settings: the setting STRING
can be a cons cell of two strings, the first one for true (non-nil
value) and the second for false."
  (let ((setting
	 (cond
	  ((stringp string)   ;; use % format characters
	   (proof-format proof-assistant-format-table string))
	  ((functionp string) ;; call the function
	   (funcall string curvalue))
	  ((consp string)     ;; true/false options
	   (if curvalue (car string) (cdr string)))
	  (t ;; no idea what to do
	   (error "proof-assistant-format: called with invalid string arg %s" string)))))
    (if proof-assistant-setting-format
	(funcall proof-assistant-setting-format setting)
      setting)))





(provide 'proof-menu)

;;; proof-menu.el ends here
