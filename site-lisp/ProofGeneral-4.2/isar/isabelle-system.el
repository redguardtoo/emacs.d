;; isabelle-system.el --- Interface with Isabelle system
;;
;; Copyright (C) 2000 LFCS Edinburgh, David Aspinall.
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; isabelle-system.el,v 12.4 2012/08/30 14:30:23 monnier Exp
;;
;; Most of this code is taken from the final version of Isamode.
;; --------------------------------------------------------------
;;

;;; Code:
(eval-when-compile
  (require 'cl))			;  mapcan, eval-when

(eval-when (compile)
  (require 'span)		        
  (require 'scomint)		        
  (require 'proof-site)
  (require 'proof-menu)
  (require 'proof-syntax)
  (proof-ready-for-assistant 'isar)	; compile for isar
  (defvar proof-assistant-menu nil))

(declare-function mapcan "cl-extra")	; spurious bytecomp warning


;; The isabelle custom group won't have been defined yet.
(defgroup isabelle nil
  "Customization of user options for Isabelle and Isabelle/Isar Proof General"
  :group 'proof-general)

(defcustom isabelle-web-page
  "http://www.cl.cam.ac.uk/Research/HVG/Isabelle/"
  "URL of web page for Isabelle."
  :type 'string
  :group 'isabelle)


;;; ================ Extract Isabelle settings ================

(defcustom isa-isabelle-command
  (or (if proof-rsh-command
	  ;; not much hope to locate executable remotely
	  (concat proof-rsh-command " isabelle"))
      (getenv "ISABELLE_TOOL")
      (proof-locate-executable "isabelle" nil
			       (list
				;; support default unpack in home dir situation
				(concat (getenv "HOME") "/Isabelle/bin/")))
      "path_to_isabelle_is_unknown")
  "Command to invoke the main Isabelle wrapper 'isabelle'.
Emacs should be able to find `isabelle' if it is on the PATH when
started.  Then several standard locations are attempted.
Otherwise you should set this, using a full path name here for reliable
working."
  :type 'file
  :group 'isabelle)

(defvar isabelle-not-found nil
  "Non-nil if user has been prompted for `isabelle' already and it wasn't found.")

(defun isa-set-isabelle-command (&optional force)
  "Make sure `isa-isabelle-command' points to a valid executable.
If it does not, or if prefix arg supplied, prompt the user for
the proper setting.  If `proof-rsh-command' is set, leave this
unverified.  Otherwise, returns non-nil if isa-isabelle-command
is surely an executable with full path."
  (interactive "p")
  (when (and (not noninteractive)
	     (not proof-rsh-command)
	     (or force
		 isabelle-not-found
		 (not (file-executable-p isa-isabelle-command))))
    (setq isa-isabelle-command
	  (read-file-name
	   "Full path to `isabelle' command (anything non-executable if you don't have it): "
	   nil nil nil))
    (unless (file-executable-p isa-isabelle-command)
      (setq isabelle-not-found t)
      (beep)
      (warn "Proof General: isabelle command not found; some menus will be incomplete and Isabelle may not run correctly.  Please check your Isabelle installation.")))
  (or proof-rsh-command
      (file-executable-p isa-isabelle-command)))

(defun isa-shell-command-to-string (command)
  "Like shell-command-to-string except the last character is stripped."
  (let ((s (shell-command-to-string command)))
    (if (equal (length s) 0) s
      (substring s 0 -1))))

(defun isa-getenv (envvar &optional default)
  "Extract environment variable ENVVAR setting using the `isabelle' program.
If the isabelle command is not available, try using elisp's getenv
to extract the value from Emacs' environment.
If there is no setting for the variable, DEFAULT will be returned"
  (isa-set-isabelle-command)
  (if (or proof-rsh-command
	  (file-executable-p isa-isabelle-command))
      (let ((setting (isa-shell-command-to-string
		      (concat "\"" isa-isabelle-command
			      "\" getenv -b " envvar))))
	(if (string-equal setting "")
	    default
	  setting))
    (or (getenv envvar) default)))

;;;
;;; ======= Interaction with System using Isabelle tools =======
;;;

(defcustom isabelle-program-name-override nil
  "*Name of executable program to run Isabelle.

You can set customize this in case the automatic settings
mechanism does not work for you, perhaps because isabelle
is not on your path, or you are running it remotely.

The logic image name is tagged onto the end."
  :type 'file
  :group 'isabelle)

(defun isa-tool-list-logics ()
  "Generate a list of available object logics."
  (if (isa-set-isabelle-command)
      (delete "" (split-string
		  (isa-shell-command-to-string
		   (concat "\"" isa-isabelle-command "\" findlogics")) "[ \t]"))))

(defcustom isabelle-logics-available nil
  "*List of logics available to use with Isabelle.
If the `isabelle' program is available, this is automatically
generated with the Lisp form `(isa-tool-list-logics)'."
  :type (list 'string)
  :group 'isabelle)

(unless noninteractive
  (setq isabelle-logics-available (isa-tool-list-logics)))

(defcustom isabelle-chosen-logic nil
  "*Choice of logic to use with Isabelle.
If non-nil, added onto the Isabelle command line for invoking Isabelle.

You can set this as a file local variable, using a special comment
at the top of your theory file, like this:

   (* -*- isabelle-chosen-logic: \"ZF\" -*- *)"
  :type (append
	 (list 'choice)
	 (mapcar (lambda (str) (list 'const str)) isabelle-logics-available)
	 (list '(string :tag "Choose another")
	       '(const :tag "Unset (use default)" nil)))
  :group 'isabelle)
(put 'isabelle-chosen-logic 'safe-local-variable 'stringp)

(defvar isabelle-chosen-logic-prev nil
  "Value of `isabelle-chosen-logic' on last call of `isabelle-set-prog-name'.")

(defun isabelle-hack-local-variables-function ()
  "Hook function for `hack-local-variables-hook'."
  (if (and isabelle-chosen-logic
	   (not (equal isabelle-chosen-logic
		       isabelle-chosen-logic-prev))
	   (proof-shell-live-buffer))
      (message "Warning: chosen logic %s does not match running Isabelle instance"
	       isabelle-chosen-logic)))

(add-hook 'hack-local-variables-hook
	  'isabelle-hack-local-variables-function)

(defun isabelle-set-prog-name (&optional filename)
  "Make proper command line for running Isabelle.
This function sets `proof-prog-name' and `isar-prog-args'."
  (let*
      ;; The ISABELLE_PROCESS and PROOFGENERAL_LOGIC values (set when
      ;; run under the interface wrapper script) indicate command line
      ;; is set in current Isabelle settings environment.
      ((isabelle (or
		  isabelle-program-name-override  ; override in Emacs
		  (getenv "ISABELLE_PROCESS")	  ; command line override
		  (isa-getenv "ISABELLE_PROCESS") ; choose to match isabelle
		  "isabelle-process"))		  ; to
       (isabelle-opts (split-string (or (getenv "ISABELLE_OPTIONS") "")))
       (opts (append (list "-PI")  ;; Proof General + Isar
		     (if proof-shell-unicode (list "-m" "PGASCII") nil)
		     isabelle-opts))
       (logic (or isabelle-chosen-logic
		  (getenv "PROOFGENERAL_LOGIC")))
       (logicarg (if (and logic (not (equal logic "")))
		     (list logic) nil)))
    (setq isabelle-chosen-logic-prev isabelle-chosen-logic)
    (setq isar-prog-args (append opts logicarg))
    (setq proof-prog-name isabelle)))

(defun isabelle-choose-logic (logic)
  "Adjust isabelle-prog-name and proof-prog-name for running LOGIC."
  (interactive
   (list (completing-read
	  "Use logic: "
	  (mapcar 'list (cons "Default"
			      isabelle-logics-available)))))
  (if (proof-shell-live-buffer)
      (error "Can't change logic while Isabelle is running, please exit process first!"))
  (customize-set-variable 'isabelle-chosen-logic
			  (unless (string-equal logic "Default") logic))
  (isabelle-set-prog-name)
  ;; Settings are potentially different between logics, and
  ;; so are Isar keywords.  Set these to nil so they get
  ;; automatically re-initialised.
  ;; FIXME: Isar keywords change not handled yet.
  (setq proof-assistant-settings nil)
  (setq proof-menu-settings nil))

(defun isa-view-doc (docname)
  "View Isabelle document DOCNAME, using Isabelle tools."
  (if (isa-set-isabelle-command)
      (apply 'start-process
	     "isa-view-doc" nil
	     (list isa-isabelle-command "doc" docname))))

(defun isa-tool-list-docs ()
  "Generate a list of documentation files available, with descriptions.
This function returns a list of lists of the form
 ((DOCNAME DESCRIPTION) ....)
of Isabelle document names and descriptions.  When DOCNAME is
passed to isa-tool-doc-command, DOCNAME will be viewed."
  (if (isa-set-isabelle-command)
      (let ((docs (isa-shell-command-to-string
		   (concat "\"" isa-isabelle-command "\" doc"))))
	(unless (string-equal docs "")
	  (mapcan
	   (function (lambda (docdes)
		       (if (proof-string-match "^[ \t]+\\(\\S-+\\)[ \t]+" docdes)
			   (list (list
				  (substring docdes (match-beginning 1) (match-end 1))
				  (substring docdes (match-end 0)))))))
	   (split-string docs "\n"))))))

(defconst isabelle-verbatim-regexp "\\`\^VERBATIM: \\(\\(.\\|\n\\)*\\)\\'"
  "Regexp matching internal marker for verbatim command output.")

(defun isabelle-verbatim (str)
  "Mark internal command STR for verbatim output."
  (concat "\^VERBATIM: " str))


;;; ==========  Utility functions ==========

(defcustom isabelle-refresh-logics t
  "*Whether to refresh the list of logics during an interactive session.
If non-nil, then `isabelle findlogics' will be used to regenerate
the `isabelle-logics-available' setting.  If this tool does not work
for you, you should disable this behaviour."
  :type 'boolean
  :group 'isabelle)

(defvar isabelle-docs-menu
  (let ((vc (lambda (docdes)
              (vector (car (cdr docdes))
                      (list 'isa-view-doc (car docdes)) t))))
    (list (cons "Isabelle Documentation" (mapcar vc (isa-tool-list-docs)))))
  "Isabelle documentation menu.  Constructed when PG is loaded.")

(defvar isabelle-logics-menu-entries nil
  "Menu of logics available.")

(defun isabelle-logics-menu-calculate ()
  (setq isabelle-logics-menu-entries
	(cons "Logics"
	      (append
	       '(["Default"
		  (isabelle-choose-logic nil)
		  :active (not (proof-shell-live-buffer))
		  :style radio
		  :selected (not isabelle-chosen-logic)
		  :help "Switch to default logic"])
	       (mapcar (lambda (l)
			 (vector l (list 'isabelle-choose-logic l)
				 :active '(not (proof-shell-live-buffer))
				 :style 'radio
				 :selected (list 'equal 'isabelle-chosen-logic l)
				 :help (format "Switch to %s logic" l)))
		       isabelle-logics-available)))))

(unless noninteractive
  (isabelle-logics-menu-calculate))

(defvar isabelle-time-to-refresh-logics t
  "Non-nil if we should refresh the logics list.")


(defun isabelle-logics-menu-refresh ()
  "Refresh isabelle-logics-menu-entries, returning new entries."
  (interactive)
  (if (and isabelle-refresh-logics
	   (or isabelle-time-to-refresh-logics (called-interactively-p 'any)))
      (progn
	(setq isabelle-logics-available (isa-tool-list-logics))
	(isabelle-logics-menu-calculate)
	;; update the menu manually
	(easy-menu-add-item proof-assistant-menu nil
			    isabelle-logics-menu-entries)
	(setq isabelle-time-to-refresh-logics nil) ;; just done it, don't repeat!
	(run-with-timer 4 nil ;; short delay to avoid doing this too often
			(lambda () (setq isabelle-time-to-refresh-logics t))))))

(defun isabelle-menu-bar-update-logics ()
  "Update logics menu."
  (and (current-local-map)
       (keymapp (lookup-key (current-local-map)
			    (vector 'menu-bar (intern proof-assistant))))
       (isabelle-logics-menu-refresh)))

(add-hook 'menu-bar-update-hook 'isabelle-menu-bar-update-logics)


;; Added in PG 3.4: load isar-keywords file.
;; This roughly follows the method given in the interface script.
;; It could be used to add an elisp command at the bottom of
;; a theory file, if we sorted out the load order a bit, or
;; added a facility to reconfigure.
;; TODO: also add something to spill out a keywords file?
(defun isabelle-load-isar-keywords (&optional kw)
  (interactive "sLoad isar keywords: ")
  (let ((userhome  (isa-getenv "ISABELLE_HOME_USER"))
	(isahome   (isa-getenv "ISABELLE_HOME"))
	(isarkwel  "%s/etc/isar-keywords-%s.el")
	(isarel    "%s/etc/isar-keywords.el")
	(ifrdble   (lambda (f) (if (file-readable-p f) f))))
    (load-file
     (or
      (and kw (funcall ifrdble (format isarkwel userhome kw)))
      (and kw (funcall ifrdble (format isarkwel isahome kw)))
      (funcall ifrdble (format isarel userhome))
      (funcall ifrdble (format isarel isahome))
      (locate-library "isar-keywords")))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Context-senstive in-span menu additions
;;

(defun isabelle-create-span-menu (span idiom name)
  (if (eq idiom 'proof)
      (let ((thm (span-property span 'name)))
	(list (vector
	       "Visualise dependencies"
	       `(proof-shell-invisible-command
		 ,(format "thm_deps %s;" thm))
	       (not (string-equal thm proof-unnamed-theorem-name)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; XML as an SML string: add escapes for quotes
;;

(defun isabelle-xml-sml-escapes (xmlstring)
  (replace-regexp-in-string "\"" "\\\"" xmlstring t t))

(defun isabelle-process-pgip (xmlstring)
  "Return an Isabelle or Isabelle/Isar command to process PGIP in XMLSTRING."
  (format "ProofGeneral.process_pgip \"%s\";"
	  (isabelle-xml-sml-escapes xmlstring)))


(provide 'isabelle-system)
;;; isabelle-system.el ends here
