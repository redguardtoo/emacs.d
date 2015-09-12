;; proof-utils.el --- Proof General utility functions and macros
;;
;; Copyright (C) 1998-2002, 2009, 2011 LFCS Edinburgh.
;; Author:      David Aspinall <David.Aspinall@ed.ac.uk> and others
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; proof-utils.el,v 12.1 2012/09/05 23:01:45 pier Exp
;;
;;; Commentary:
;;
;; Loading note: this file is required immediately from proof.el, so
;; no autoloads cookies are added here.
;;
;; Compilation note: see etc/development-tips.txt
;;

;;; Code:

;;
;; Give Emacs version mismatch error here.
;;
;; This file is loaded early, and may be first compiled file
;; loaded if proof-site.el is loaded instead of proof-site.elc.
;;
(eval-and-compile
  (defun pg-emacs-version-cookie ()
    (format "GNU Emacs %d.%d"
	    emacs-major-version emacs-minor-version))

  (defconst pg-compiled-for
    (eval-when-compile (pg-emacs-version-cookie))
    "Version of Emacs we're compiled for (or running on, if interpreted)."))

(if (or (not (boundp 'emacs-major-version))
	(< emacs-major-version 23)
	(string-match "XEmacs" emacs-version))
    (error "Proof General is not compatible with Emacs %s" emacs-version))

(unless (equal pg-compiled-for (pg-emacs-version-cookie))
  (warn
   "Proof General compiled for %s but running on %s: \"make clean; make\" is recommended."
   pg-compiled-for (pg-emacs-version-cookie)))



(require 'proof-site)			; basic vars
(require 'proof-compat)		        ; compatibility
(require 'pg-pamacs)			; macros for pa config
(require 'proof-config)			; config vars
(require 'bufhist)			; bufhist
(require 'proof-syntax)			; syntax utils
(require 'proof-autoloads)		; interface fns
(require 'scomint)			; for proof-shell-live-buffer

;;; Code:

;;
;; Handy macros
;;

(defmacro proof-with-current-buffer-if-exists (buf &rest body)
  "As with-current-buffer if BUF exists and is live, otherwise nothing."
  `(if (buffer-live-p ,buf)
       (with-current-buffer ,buf
	 ,@body)))

;; Slightly specialized version of above.  This is used in commands
;; which work from different PG buffers (goals, response), typically
;; bound to toolbar commands.
(defmacro proof-with-script-buffer (&rest body)
  "Execute BODY in some script buffer: current buf or otherwise proof-script-buffer.
Return nil if not a script buffer or if no active scripting buffer."
  `(cond
    ((eq proof-buffer-type 'script)
     (progn
       ,@body))
    ((buffer-live-p proof-script-buffer)
     (with-current-buffer proof-script-buffer
       ,@body))))

(defmacro proof-map-buffers (buflist &rest body)
  "Do BODY on each buffer in BUFLIST, if it exists."
  `(dolist (buf ,buflist)
     (proof-with-current-buffer-if-exists buf ,@body)))

(defmacro proof-sym (string)
  "Return symbol for current proof assistant using STRING."
 `(intern (concat (symbol-name proof-assistant-symbol) "-" ,string)))


(defsubst proof-try-require (symbol)
  "Try requiring SYMBOL.  No error if the file for SYMBOL isn't found."
  (condition-case ()
      (require symbol)
    (file-error nil))
  (featurep symbol))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Simplified version of save-some-buffers, with useful arg
;;

(defun proof-save-some-buffers (buffers)
  "Query the user whether to save each of BUFFERS."
  ;; code based on extract from files.el in XEmacs 21.4.14
  (map-y-or-n-p
   (lambda (buffer)
     (if
	 (and (buffer-modified-p buffer)
	      (not (buffer-base-buffer buffer))
	      (buffer-file-name buffer))
	 ;; we deliberately don't switch to show the buffer;
	 ;; let's assume user can see it or knows what's in it.
	 (format "Save file %s? "
		 (buffer-file-name buffer))))
   (lambda (buffer)
     (set-buffer buffer)
     (condition-case ()
	 (save-buffer)
       (error nil)))
   buffers))

(defun proof-save-this-buffer ()
  "Query the user whether to save the current buffer."
  (if (and (buffer-modified-p)
	   (buffer-file-name (current-buffer))
	   (y-or-n-p (format "Save file %s? "
			     (buffer-file-name (current-buffer)))))
      (save-buffer)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Buffers and filenames

(defun proof-file-truename (filename)
  "Return the true name of the file FILENAME or nil if file non-existent."
  (and filename (file-exists-p filename) (file-truename filename)))

(defun proof-files-to-buffers (filenames)
  "Convert a list of FILENAMES into a list of BUFFERS."
  (let (bufs buf)
    (dolist (file filenames)
      (if (setq buf (find-buffer-visiting file))
	  (setq bufs (cons buf bufs))))
    bufs))

(defun proof-buffers-in-mode (mode &optional buflist)
  "Return a list of the buffers in the buffer list in major mode MODE.
Restrict to BUFLIST if it's set."
  (let ((bufs-left (or buflist (buffer-list)))
	bufs-got)
    (dolist (buf bufs-left bufs-got)
      (if (with-current-buffer buf (eq mode major-mode))
	  (setq bufs-got (cons buf bufs-got))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Associated buffers
;;

(defun pg-save-from-death ()
  "Prevent this associated buffer from being killed: merely erase it.
A hook function for `kill-buffer-hook'.
This is a fairly crude and not-entirely-robust way to prevent the
user accidently killing an associated buffer."
  (if (and (proof-shell-live-buffer) proof-buffer-type)
      (progn
	(let ((bufname (buffer-name)))
	  (bufhist-erase-buffer)
	  (set-buffer-modified-p nil)
	  (bury-buffer)
	  (error
	   "Warning: buffer %s not killed; still associated with prover process"
	   bufname)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Key functions

(defun proof-define-keys (map kbl)
  "Adds keybindings KBL in MAP.
The argument KBL is a list of tuples (k . f) where `k' is a keybinding
\(vector) and `f' the designated function."
  (mapcar
   (lambda (kbl)
     (let ((k (car kbl)) (f (cdr kbl)))
	 (define-key map k f)))
   kbl))


(defun pg-remove-specials (&optional start end)
  "Remove special characters in region.  Default to whole buffer.
Leave point at END."
  (let ((start (or start (point-min)))
	(end   (or end (point-max))))
    (goto-char start)
    (while (re-search-forward pg-special-char-regexp end t)
      (replace-match ""))
    (goto-char end)))

(defun pg-remove-specials-in-string (string)
  (proof-replace-regexp-in-string pg-special-char-regexp "" string))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Messaging and display functions
;;

(defun proof-safe-split-window-vertically ()
  (if (<= (window-height) (* 2 window-min-height))
      (enlarge-window (+ 3 (* 2 window-min-height))))
  (split-window-vertically))

(defun proof-warn-if-unset (tag sym)
  "Give a warning (with TAG) if symbol SYM is unbound or nil."
  (unless (and (boundp sym) (symbol-value sym))
    (warn "Proof General %s: %s is unset."  tag (symbol-name sym))))

(defun proof-get-window-for-buffer (buffer)
  "Find a window for BUFFER, display it there, return the window.
NB: may change the selected window."
  ;; IF there *isn't* a visible window showing buffer...
  (unless (get-buffer-window buffer 0)
    ;; THEN find somewhere nice to display it
	  (if (and
	     ;; If we're in two-window mode and already displaying a
	     ;; script/response/goals, try to just switch the buffer
	     ;; instead of calling display-buffer which alters sizes.
	     ;; Gives user some stability on display.
	     (not proof-three-window-enable)
	     (> (count-windows) 1)
	     ;; was: (not (eq (next-window) (selected-window)))
	     (memq (window-buffer (next-window nil 'ignoreminibuf))
		   ;; NB: 3.5: added rest of assoc'd buffers here
		   (cons proof-script-buffer (proof-associated-buffers))))
	    (if (eq (selected-window) (minibuffer-window))
		;; 17.8.01: avoid switching the minibuffer's contents
		;; -- terrrible confusion -- use next-window after
		;; script buffer instead.
		;; (another hack which is mostly right)
		(set-window-buffer
		 (next-window
		  (car-safe (get-buffer-window-list proof-script-buffer))
		  'ignoreminibuf) buffer)
	      (if (eq (window-buffer (next-window nil 'ignoreminibuf))
		      proof-script-buffer)
		  ;; switch this window
		  (set-window-buffer (selected-window) buffer)
		;; switch other window
		(set-window-buffer (next-window nil 'ignoreminibuf) buffer)))
	    ;; o/w: call display buffer to configure windows nicely.
	    (display-buffer buffer)))
  ;; Return the window, hopefully the one we first thought of.
  (get-buffer-window buffer 0))

(defun proof-display-and-keep-buffer (buffer &optional pos force)
  "Display BUFFER and make window according to display mode.
If optional POS is present, will set point to POS.
Otherwise move point to the end of the buffer.
Ensure that point is visible in window."
  (if (or force proof-auto-raise-buffers)
    (save-excursion
    (save-selected-window
      (let ((window (proof-get-window-for-buffer buffer)))
	(if (window-live-p window) ;; [fails sometimes?]
	    (progn
	      ;; Set the size and point position.
	      (if proof-three-window-enable
		  (set-window-dedicated-p window proof-three-window-enable))
	      (select-window window)
	      (if proof-shrink-windows-tofit
		  (proof-resize-window-tofit)
		;; If we're not shrinking to fit, allow the size of
		;; this window to change.  [NB: might be nicer to
		;; fix the size based on user choice]
		(setq window-size-fixed nil))
	      ;; For various reasons, point may get moved around in
	      ;; response buffer.  Attempt to normalise its position.
	      (goto-char (or pos (point-max)))
	      (if pos
		  (beginning-of-line)
		(skip-chars-backward "\n\t "))
	      ;; Ensure point visible.  Again, window may have died
	      ;; inside shrink to fit, for some reason
	      (when (window-live-p window)
		(unless (pos-visible-in-window-p (point) window)
		  (recenter -1))
		(with-current-buffer buffer
		  (if (window-bottom-p window)
		      (unless (local-variable-p 'mode-line-format)
			;; Don't show any mode line.
			(set (make-local-variable 'mode-line-format) nil))
		    (unless mode-line-format
		      ;; If the buffer gets displayed elsewhere, re-add
		      ;; the modeline.
		      (kill-local-variable 'mode-line-format))))))))))))

(defun proof-clean-buffer (buffer)
  "Erase buffer and hide from display if proof-delete-empty-windows set.
Auto deletion only affects selected frame.  (We assume that the selected
frame is the one showing the script buffer.)
No effect if buffer is dead."
  (if (buffer-live-p buffer)
      (with-current-buffer buffer
	(let ((inhibit-read-only t))
	  (unless (eq 0 (buffer-size)) ;; checkpoint unless already empty
	    (bufhist-checkpoint-and-erase)))
	(set-buffer-modified-p nil)
	(if (eq buffer proof-response-buffer)
	    (setq pg-response-next-error nil))	; all error msgs lost!
	(if proof-delete-empty-windows
	    (delete-windows-on buffer t)))))

(defun pg-internal-warning (message &rest args)
  "Display internal warning MESSAGE with ARGS as for format."
  (let ((formatted (apply 'format message args)))
    (if (fboundp 'display-warning)
	(display-warning 'proof-general formatted)
    (message formatted))))

;;;###autoload
(defun proof-debug (msg &rest args)
  "Issue the debugging message (format MSG ARGS) in the *PG Debug* buffer.
If flag `proof-general-debug' is nil, do nothing."
  (when proof-general-debug
    (with-current-buffer (get-buffer-create "*PG Debug*")
      (help-mode)
      (let ((formatted (apply 'format msg args))
	    (log-warning-minimum-level :debug)
	    (warning-minimum-level :debug)
	    (buffer-read-only nil))
	(display-warning 'proof-general
			 formatted :debug
			 "*PG Debug*")))))

;; Utility used in the "Buffers" menu, and throughout
(defun proof-switch-to-buffer (buf &optional noselect)
  "Switch to or display buffer BUF in other window unless already displayed.
If optional arg NOSELECT is true, don't switch, only display it.
No action if BUF is nil or killed."
  (and (buffer-live-p buf) ; maybe use proof-display-and-keep-buffer ?
       (unless (eq buf (window-buffer (selected-window)))
	 (if noselect
	     (display-buffer buf 'not-this-window)
	   (let ((pop-up-windows t))
	     (pop-to-buffer buf 'not-this-window 'norecord))))))


;; Originally based on `shrink-window-if-larger-than-buffer', which
;; has a pretty weird implementation.
;; FIXME: GNU Emacs has useful "window-size-fixed" which we use
;; HOWEVER, it's still not quite the right thing, it seems to me.
;; We'd like to specifiy a *minimum size* for a given buffer,
;; not a maximum.  With a frame split with just goals/response
;; we'd still get resize errors here using window-size-fixed.
;; FIXME: shrink-to-fit doesn't really work in three-buffer mode,
;; since shrinking one of the associated buffers tends to enlarge the
;; other (rather than just enlarging the proof state)
(defun proof-resize-window-tofit (&optional window)
  "Shrink the WINDOW to be as small as possible to display its contents.
Do not shrink to less than `window-min-height' lines.
Do nothing if the buffer contains more lines than the present window height,
or if some of the window's contents are scrolled out of view,
or if the window is not the full width of the frame,
or if the window is the only window of its frame."
;; da: actually seems okay in this case
  (interactive)
  (or window (setq window (selected-window)))
  ;; some checks before resizing to avoid messing custom display
  ;; [probably somewhat superfluous/extra rare]
  (if
      (or
       ;; The frame must not be minibuffer-only.
       (eq (frame-parameter (window-frame window) 'minibuffer) 'only)
       ;; We've got more than one window, right?
       (= 1 (let ((frame (selected-frame)))
	      (select-frame (window-frame window))
	      (unwind-protect ;; [why is this protected?]
		  (count-windows)
		(select-frame frame)
		(select-window window))))
       ;; the window is the full width, right?
       ;; [if not, we may be in horiz-split scheme, problematic]
       (not (window-leftmost-p window))
       (not (window-rightmost-p window)))
      ;; OK, we're not going to adjust the height here.  Moreover,
      ;; we'll make sure the height can be changed elsewhere.
      (setq window-size-fixed nil)
    (with-current-buffer (window-buffer window)
      (let*
	  ;; weird test cases:
	  ;; cur=45, max=23, desired=121, extraline=0
	  ;; current height
	  ;;; ((cur-height (window-height window))
	   ;; Most window is allowed to grow to
	  ((max-height
	     (/ (frame-height (window-frame window))
		(if proof-three-window-enable
		    ;; we're in three-window-mode with
		    ;; all horizontal splits, so share the height.
		    3
		  ;; Otherwise assume a half-and-half split.
		  2)))
	   ;; I find that I'm willing to use a bit more than the max in
	   ;; those cases where it allows me to see the whole
	   ;; response/goal.  --Stef
	   (absolute-max-height
	    (truncate
	     (/ (frame-height (window-frame window))
		(if proof-three-window-enable
		    ;; we're in three-window-mode with
		    ;; all horizontal splits, so share the height.
		    2
		  ;; Otherwise assume a half-and-half split.
		  1.5))))
	   ;; If buffer ends with a newline and point is right after it, then
	   ;; add a final empty line (to display the cursor).
	   (extraline (if (and (eobp) (bolp)) 1 0))
	   ;; (test-pos (- (point-max) extraline))
	   ;; Direction of resizing based on whether max position is
	   ;; currently visible.  [ FIXME: not completely sensible:
	   ;; may be displaying end fraction of buffer! ]
	   ;; (shrink (pos-visible-in-window-p test-pos window))
	   ;; Likely desirable height is given by count-lines
	   (desired-height
	    ;; FIXME: is count-lines too expensive for v.large
	    ;; buffers?  Probably not an issue for us, but one
	    ;; wonders at the shrink to fit strategy.
	    ;; NB: way to calculate pixel fraction?
	    (+ extraline (count-lines (point-min) (point-max)))))
	;; Let's shrink or expand.  Uses new GNU Emacs function.
	(let ((window-size-fixed nil))
	  (set-window-text-height window
				  ;; As explained earlier: use abs-max-height
				  ;; but only if that makes it display all.
				  (if (> desired-height absolute-max-height)
				      max-height desired-height)))
	(if (window-live-p window)
	    (progn
	      (if (>= (window-text-height window) desired-height)
		  (set-window-start window (point-min)))
	      ;; window-size-fixed is a GNU Emacs buffer local variable
	      ;; which determines window size of buffer.
	      ;; (setq window-size-fixed (window-height window))
	      ))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Function for submitting bug reports.
;;

(defun proof-submit-bug-report ()
  "Submit an bug report or other report for Proof General."
  (interactive)
  (require 'reporter)
  (let
      ((reporter-prompt-for-summary-p
	"(Very) brief summary of problem or suggestion: "))
    (reporter-submit-bug-report
     "da+pg-bugs@inf.ed.ac.uk"
     "Proof General"
     (list 'proof-general-version 'proof-assistant)
     nil nil
     "*** Proof General now uses Trac for project management and bug reporting, please go to:
***
***    http://proofgeneral.inf.ed.ac.uk/trac/search
***
*** To see if your bug has been reported already, and a new ticket if not.
*** To report a bug, either register yourself as a user, or use the generic account
*** username \"pgemacs\" with password \"pgemacs\"
***
*** Please only continue with this email mechanism instead IF YOU REALLY MUST.
*** The address is not monitored very often and quite possibly will be ignored.
***
*** When reporting a bug, please include a small test case for us to repeat it.
*** Please also check that it is not already covered in the BUGS or FAQ files that came with
*** the distribution, or the latest versions at
***    http://proofgeneral.inf.ed.ac.uk/BUGS  and
***    http://proofgeneral.inf.ed.ac.uk/FAQ ")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Utils for making functions to adjust user settings
;;;

(defun proof-deftoggle-fn (var &optional othername)
  "Define a function <VAR>-toggle for toggling a boolean customize setting VAR.
Args as for the macro `proof-deftoggle', except will be evaluated."
  (eval
   `(defun ,(if othername othername
	      (intern (concat (symbol-name var) "-toggle"))) (&optional arg)
	      ,(concat "Toggle `" (symbol-name var) "'. With ARG, turn on iff ARG>0.
This function simply uses customize-set-variable to set the variable.")
; It was constructed with `proof-deftoggle-fn'."
	      (interactive "P")
	      (customize-set-variable
	       (quote ,var)
	       (if (null arg) (not ,var)
		 (> (prefix-numeric-value arg) 0))))))

(defmacro proof-deftoggle (var &optional othername)
  "Define a function VAR-toggle for toggling a boolean customize setting VAR.
The toggle function uses `customize-set-variable' to change the variable.
OTHERNAME gives an alternative name than the default <VAR>-toggle.
The name of the defined function is returned."
  `(progn
     (declare-function ,(if othername othername
			  (intern (concat (symbol-name var) "-toggle")))
		       "proof-utils")
     (proof-deftoggle-fn (quote ,var) (quote ,othername))))

(defun proof-defintset-fn (var &optional othername)
  "Define a function <VAR>-intset for setting an integer customize setting VAR.
Args as for the macro `proof-defintset', except will be evaluated."
  (eval
   `(defun ,(if othername othername
	      (intern (concat (symbol-name var) "-intset"))) (arg)
	      ,(concat "Set `" (symbol-name var) "' to ARG.
This function simply uses customize-set-variable to set the variable.
It was constructed with `proof-defintset-fn'.")
	      (interactive (list
			    (read-number
			     (format "Value for %s (int, currently %s): "
				     (symbol-name (quote ,var))
				     (symbol-value (quote ,var))))))
	      (unless (integerp arg)
		;; type-check to avoid customize type mismatch
		(error "Value should be an integer!"))
	      (customize-set-variable (quote ,var) arg))))

(defmacro proof-defintset (var &optional othername)
  "Define a function <VAR>-intset for setting an integer customize setting VAR.
The setting function uses `customize-set-variable' to change the variable.
OTHERNAME gives an alternative name than the default <VAR>-intset.
The name of the defined function is returned."
  `(proof-defintset-fn (quote ,var) (quote ,othername)))

(defun proof-deffloatset-fn (var &optional othername)
  "Define a function <VAR>-floatset for setting an float customize setting VAR.
Args as for the macro `proof-deffloatset', except will be evaluated."
  (eval
   `(defun ,(if othername othername
	      (intern (concat (symbol-name var) "-floatset"))) (arg)
	      ,(concat "Set `" (symbol-name var) "' to ARG.
This function simply uses customize-set-variable to set the variable.
It was constructed with `proof-deffloatset-fn'.")
	      (interactive (list
			    (read-number
			     (format "Value for %s (float, currently %s): "
				     (symbol-name (quote ,var))
				     (symbol-value (quote ,var))))))
	      (customize-set-variable (quote ,var) arg))))

(defmacro proof-deffloatset (var &optional othername)
  "Define a function <VAR>-floatset for setting an float customize setting VAR.
The setting function uses `customize-set-variable' to change the variable.
OTHERNAME gives an alternative name than the default <VAR>-floatset.
The name of the defined function is returned."
  `(proof-deffloatset-fn (quote ,var) (quote ,othername)))

(defun proof-defstringset-fn (var &optional othername)
  "Define a function <VAR>-toggle for setting an integer customize setting VAR.
Args as for the macro `proof-defstringset', except will be evaluated."
  (eval
   `(defun ,(if othername othername
	      (intern (concat (symbol-name var) "-stringset"))) (arg)
	      ,(concat "Set `" (symbol-name var) "' to ARG.
This function simply uses customize-set-variable to set the variable.
It was constructed with `proof-defstringset-fn'.")
	      (interactive ,(format "sValue for %s (a string): "
				    (symbol-name var)))
	      (customize-set-variable (quote ,var) arg))))

(defmacro proof-defstringset (var &optional othername)
  "The setting function uses customize-set-variable to change the variable.
OTHERNAME gives an alternative name than the default <VAR>-stringset.
The name of the defined function is returned."
  `(proof-defstringset-fn (quote ,var) (quote ,othername)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Macris for defining user-level functions (previously in proof-menu.el)
;;;

(defun proof-escape-keymap-doc (string)
  "Avoid action of `substitute-command-keys' on STRING."
  (replace-regexp-in-string "\\\\" "\\\\=\\\\" string))

(defmacro proof-defshortcut (fn string &optional key)
  "Define shortcut function FN to insert STRING, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is inserted using `proof-insert', which see.
KEY is added onto proof assistant map."
  `(progn
     (if ,key
	 (define-key (proof-ass keymap) (quote ,key) (quote ,fn)))
     (defun ,fn ()
       ,(concat "Shortcut command to insert "
		(proof-escape-keymap-doc string)
		" into the current buffer.\nThis simply calls `proof-insert', which see.")
       (interactive)
       (proof-insert ,string))))

(defmacro proof-definvisible (fn string &optional key)
  "Define function FN to send STRING to proof assistant, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is sent using `proof-shell-invisible-command', which see.
STRING may be a string or a function which returns a string.
KEY is added onto proof assistant map."
  `(progn
     (if ,key
	 (define-key (proof-ass keymap) (quote ,key) (quote ,fn)))
     (defun ,fn ()
       ,(concat "Command to send "
		(if (stringp string)
		    (proof-escape-keymap-doc string)
		  "an instruction")
		" to the proof assistant.")
       (interactive)
       ,(if (stringp string)
	    (list 'proof-shell-invisible-command string)
	  (list 'proof-shell-invisible-command (eval string))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Interface to custom lib
;;;

;; EMACSFIXME: A function that custom could provide.
(defun pg-custom-save-vars (&rest variables)
  "Save custom vars VARIABLES."
  (dolist (symbol variables)
    (let ((value (get symbol 'customized-value)))
      ;; See customize-save-customized; adjust properties so
      ;; that custom-save-all will save the value.
      (when value
	(put symbol 'saved-value value)
	(custom-push-theme 'theme-value symbol 'user 'set value)
	(put symbol 'customized-value nil))))
  (custom-save-all))

;; FIXME: this doesn't do quite same thing as reset button,
;; which *removes* a setting from `custom-set-variables' list
;; in custom.el.  Instead, this adds something to a
;; custom-reset-variables list.
(defun pg-custom-reset-vars (&rest variables)
  "Reset custom vars VARIABLES to their default values."
  ;; FIXME: probably this XEmacs specific
  (apply 'custom-reset-variables
	 (mapcar (lambda (var) (list var 'default))
		 variables)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Finding executables
;;

(defun proof-locate-executable (progname &optional returnnopath extrapath)
  "Search for PROGNAME on environment PATH.  Return the full path to PROGNAME, or nil.
If RETURNNOPATH is non-nil, return PROGNAME even if we can't find a full path.
EXTRAPATH is a list of extra path components"
  (or
   (let ((exec-path (append exec-path extrapath)))
     (executable-find progname))
   (if returnnopath progname)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Word utility
;;

;; This is adapted from simple.el in GNU Emacs 23.
(defun pg-current-word-pos (&optional strict really-word)
  "Return the start and end positions of symbol that point is on (or nearby).
The return value includes no text properties.
If optional arg STRICT is non-nil, return nil unless point is within
or adjacent to a symbol or word.  In all cases the value can be nil
if there is no word nearby.
The function, belying its name, normally finds a symbol.
If optional arg REALLY-WORD is non-nil, it finds just a word."
  (save-excursion
    (let* ((oldpoint (point)) (start (point)) (end (point))
	   (syntaxes (if really-word "w" "w_"))
	   (not-syntaxes (concat "^" syntaxes)))
      (skip-syntax-backward syntaxes) (setq start (point))
      (goto-char oldpoint)
      (skip-syntax-forward syntaxes) (setq end (point))
      (when (and (eq start oldpoint) (eq end oldpoint)
		 ;; Point is neither within nor adjacent to a word.
		 (not strict))
	;; Look for preceding word in same line.
	(skip-syntax-backward not-syntaxes
			      (save-excursion (beginning-of-line)
					      (point)))
	(if (bolp)
	    ;; No preceding word in same line.
	    ;; Look for following word in same line.
	    (progn
	      (skip-syntax-forward not-syntaxes
				   (save-excursion (end-of-line)
						   (point)))
	      (setq start (point))
	      (skip-syntax-forward syntaxes)
	      (setq end (point)))
	  (setq end (point))
	  (skip-syntax-backward syntaxes)
	  (setq start (point))))
      ;; If we found something nonempty, return it as a pair of positions.
      (unless (= start end)
	(cons start end)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Stripping output and message
;;

(defsubst proof-shell-strip-output-markup (string &optional push)
  "Strip output markup from STRING.
Convenience function to call function `proof-shell-strip-output-markup'.
Optional argument PUSH is ignored."
  (funcall proof-shell-strip-output-markup string))

(defun proof-minibuffer-message (str)
  "Output STR in minibuffer."
  (if proof-minibuffer-messages
      (message "%s" ;; to escape format characters
	       (concat "[" proof-assistant "] "
		       ;; TODO: rather than stripping, could try fontifying
		       (proof-shell-strip-output-markup str)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Extracting visible text in a buffer
;;
;; NB: this is possible automatic alternative to proof-shell-strip-output,
;; but is more reliable to have specific setting.
;;
;; (defun proof-buffer-substring-visible (start end)
;;   "Return the substring from START to END with no invisible property set."
;;   (let ((pos start)
;;	(vis (get-text-property start 'invisible))
;;	(result "")
;;	nextpos)
;;     (while (and (< pos end)
;;		(setq nextpos (next-single-property-change pos 'invisible
;;							   nil end)))
;;       (unless (get-text-property pos 'invisible)
;;	(setq result (concat result (buffer-substring-no-properties
;;				     pos nextpos))))
;;       (setq pos nextpos))
;;     (unless (get-text-property end 'invisible)
;;       (setq result (concat result (buffer-substring-no-properties
;;				   pos end))))))


(provide 'proof-utils)
;;; proof-utils.el ends here
