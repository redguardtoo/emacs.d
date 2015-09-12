;; pg-pgip.el --- PGIP manipulation for Proof General
;;
;; Copyright (C) 2000-2002, 2010 LFCS Edinburgh.
;; Author:   David Aspinall <David.Aspinall@ed.ac.uk>
;; License:  GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; pg-pgip.el,v 12.1 2011/10/17 10:11:45 da Exp
;;
;; STATUS: Experimental
;;
;; Proof General Kit uses PGIP, an XML-message protocol
;; for interactive proof.  This file contains functions
;; to process PGIP commands sent from the proof assistant
;; and to construct PGIP commands to send out.
;;
;; TESTING NOTES: turn on `proof-general-debug' for
;; useful tracing messages: (setq proof-general-debug t).
;;
;; TODO NEXT:
;; -- completion command for completion tables
;; -- parsescript input/outputs
;; -- guiconfig, some parts of
;; -- support fully native PGIP mode
;;


;;; Commentary:
;;

(require 'cl)				; incf
(require 'pg-xml)			;

(declare-function pg-response-warning "pg-response")
(declare-function pg-response-message "pg-response")
(declare-function proof-segment-up-to "proof-script") 
(declare-function proof-insert-pbp-command "proof-script")

;;; Code:
(defalias 'pg-pgip-debug   'proof-debug)
(defalias 'pg-pgip-error   'error)
(defalias 'pg-pgip-warning 'pg-internal-warning)

(defconst pg-pgip-version-supported "2.0"
  "Version of PGIP supported by this library.")

;;;###autoload
(defun pg-pgip-process-packet (pgips)
  "Process the command packet PGIP, which is parsed XML according to pg-xml-parse-*.
The list PGIPS may contain one or more PGIP packets, whose contents are processed."
  ;; PGIP processing is split into two steps:
  ;; (1) process each command, altering internal data structures
  ;; (2) post-process for each command type, affecting external interface (menus, etc).
  (mapc 'pg-pgip-post-process
	(reduce 'union (mapcar 'pg-pgip-process-pgip pgips))))

;; TODO: use id's and sequence numbers to reconstruct streams of messages.
(defvar pg-pgip-last-seen-id nil)
(defvar pg-pgip-last-seen-seq nil)

(defun pg-pgip-process-pgip (pgip)
  "Process the commands in the PGIP XML-node PGIP."
  ;; NB: appearances of 'notreallyoptional below should be removed,
  ;; but they are needed for compatibility with Isabelle at the moment,
  ;; whose PGIP follows an older schema.
  (let* ((name	   (xml-node-name pgip))
	 (tag      (pg-xml-get-attr 'tag pgip 'optional))
	 (id	   (pg-xml-get-attr 'id pgip 'optional))
 	 (class	   (pg-xml-get-attr 'messageclass pgip 'notreallyoptional))
	 (refseq   (pg-xml-get-attr 'refseq pgip 'optional))
	 (refid    (pg-xml-get-attr 'refid pgip 'optional))
 	 (seq	   (pg-xml-get-attr 'seq pgip 'notreallyoptional)))
    (setq pg-pgip-last-seen-id id)
    (setq pg-pgip-last-seen-seq seq)
    (if (eq name 'pgip)
	;; NB: schema currently allows only one message here
	(mapcar 'pg-pgip-process-msg (xml-node-children pgip))
      (pg-internal-warning "pg-pgip-process-pgip: expected PGIP element, got %s" name))))

(defun pg-pgip-process-msg (pgipmsg)
  "Process the PGIP message in the XML node PGIPMSG.
Return a symbol representing the PGIP command processed, or nil."
  (let* ((name        (xml-node-name pgipmsg))
	 (fname	      (intern (concat "pg-pgip-process-" (symbol-name name)))))
    (if (fboundp fname)
	(progn
	  (pg-pgip-debug "Processing PGIP message seq %s, type %s"
			 (or (pg-xml-get-attr 'seq pgipmsg 'notreallyoptional) "<missing>")
			 name)
	  (funcall fname pgipmsg)
	  name)
      (pg-internal-warning "!!! unrecognized/unimplemented PGIP message element `%s'" name)
      nil)))

(defvar pg-pgip-post-process-functions
  '((hasprefs . proof-assistant-menu-update)
    (oldhaspref . proof-assistant-menu-update) ;; NB: Isabelle compatibility
    (menuadd  . proof-assistant-menu-update)
    (menudel  . proof-assistant-menu-update)
    (idtable  . pg-pgip-update-idtables)       ;; TODO: not yet implemented
    (addid    . pg-pgip-update-idtables)
    (delid    . pg-pgip-update-idtables))
  "Table of functions to call after processing PGIP commands.")

(defun pg-pgip-post-process (cmdname)
  "Perform post-processing for a PGIP command type CMDNAME (a symbol)."
  (let ((ppfn  (cdr-safe (assoc cmdname pg-pgip-post-process-functions))))
    (if (fboundp ppfn)
	(progn
	  (pg-pgip-debug 
	   "Post-processing for PGIP message type `%s' with function `%s'" cmdname ppfn)
	  (funcall ppfn))
      (pg-pgip-debug "[No post-processing defined for PGIP message type `%s']" cmdname))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Message processing: fromprovermsg/kitconfig
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pg-pgip-process-askpgip (node)
  (pg-pgip-debug "Received <askpgip> message with version `%s'"
		 (pg-xml-get-attr 'version node 'notreallyoptional))
  ;; TODO: send a uses PGIP message back?
  )

(defun pg-pgip-process-usespgip (node)
  (let ((version (pg-pgip-get-version node)))
    (pg-pgip-debug "Received <usespgip> message with version `%s'" version)))

(defun pg-pgip-process-usespgml (node)
  (let ((version (pg-pgip-get-version node)))
    (pg-pgip-debug "Received <usespgml> message with version `%s'" version)))

(defun pg-pgip-process-pgmlconfig (node)
  ;; symconfig specify an ascii alternative string for a named symbol;
  ;; we process it by storing a property 'pgml-alt on the elisp symbol.
  (let ((pgmlconfigures (xml-get-children node 'symconfig)))
    (dolist (config pgmlconfigures)
      (cond
       ((and (not (stringp config))
	     (eq (xml-node-name config) "symconfig"))
	(let
	    ((symname   (pg-pgip-get-symname node))
	     (asciialt  (pg-xml-get-attr 'alt node t)))
	  (put (intern symname)
	       'pgml-alt asciialt)))
       (t
	(pg-pgip-warning "Unexpected child of <pgmlconfig> node: %s" config))))))

(defun pg-pgip-process-proverinfo (node)
  (let* ((name	      (pg-pgip-get-name node))
	 (descr	      (pg-pgip-get-descr node t "<no description supplied>"))
	 (version     (pg-pgip-get-version node t "<no version supplied>"))
	 (url         (pg-pgip-get-url node t))
	 (welcomeelt  (pg-xml-get-child 'welcomemsg node))
	 (welcomemsg  (if welcomeelt (pg-xml-get-text-content welcomeelt)))
	 (icon	      (xml-get-children node 'icon))
	 (helpdocs    (xml-get-children node 'helpdocs)))
  ;; TODO: enter the data into a table of provers (see proof-site.el).
  ;; Seems little point doing this while we have the single-prover limitation.
    ))

;;
;; Preferences
;;

(defun pg-pgip-process-hasprefs (node)
  (let* ((prefcat	(pg-pgip-get-prefcat node))
	 (hasprefnodes  (xml-get-children node 'haspref)))
    (dolist (node hasprefnodes)
      (let* ((name	(pg-pgip-get-name node))
	     (descr	(pg-pgip-get-descr node 'optional))
	     (pgiptype	(pg-pgip-get-pgiptype (pg-xml-child-elt node)))
	     (default	(pg-pgip-get-default node 'optional))
	     (defaultlsp (if default
			     (pg-pgip-interpret-value default pgiptype)
			   (pg-pgip-default-for pgiptype)))
	     (icon	(pg-pgip-get-icon node 'optional))) ;; TODO; ignored
      (pg-pgip-haspref name pgiptype prefcat descr defaultlsp)))))

(defun pg-pgip-haspref (name type prefcat descr default)
  "Call `defpacustom' with values from a <haspref> element."
  (let* ((subst    (pg-pgip-subst-for type))
	 ;; FIXME: this substitution mechanism is not really good enough, we
	 ;; want to escape XML characters, etc.  Should be possible: turn this
	 ;; into a function.
	 (pgipcmd  (concat "<setpref name=\"" name "\" prefcategory=\"" prefcat "\">"
			   subst "</setpref>"))
	 (symname  (intern name)))
    (pg-pgip-debug
     "haspref calling defpacustom: name:%s default:%s type:%s pgipcmd:%s" symname default type pgipcmd)
    (eval
     `(defpacustom ,symname ,default ,descr
	:type (quote ,type)
	:pggroup ,prefcat
	:pgipcmd ,pgipcmd
	:pgdynamic t))))

(defun pg-pgip-process-prefval (node)
;;
;; <prefval name="n">value</prefval>
;;
;; Proof assistant advises that preference n has been updated.
;;
;; Protocol is that <setpref> sent on a PGIP channel is assumed to
;; succeed, so is not required to be acknowledged with a <prefval>
;; message from prover.  But no harm will result if it is --- and that
;; might be appropriate if some canonicalisation occurs.

; in progress [FIXME: Isabelle can send this as reply to getpref now]
;(defun pg-pgip-prefval (attrs value)
;  "Process a <prefval> element, by setting interface's copy of preference."
;  (let*
;      ((name	(pg-xml-get-attr 'haspref 'name attrs t))
;       (type    (
  )




;;
;; guiconfig
;;


(defun pg-pgip-process-guiconfig (node)
  )

;;
;; Identifiers: managing obarrays of symbols used for completion
;;

(defvar proof-assistant-idtables nil
  "List of idtables (objtype symbols) for currently running proof assistant.")

(defun pg-pgip-process-ids (node)
  "Manipulate identifier tables, according to setids/addids/delids in NODE."
  (let ((idtables  (pg-xml-child-elts node))
	(opn	   (xml-node-name node)))
    (dolist (idtable idtables)
      (let* ((context  (pg-xml-get-attr 'context idtable 'optional))
	     (objtype  (intern (pg-pgip-get-objtype idtable)))
	     (idents   (mapcar 'pg-xml-get-text-content
			       (xml-get-children idtable 'identifier)))
	     (obarray  (or (and (not (eq opn 'setids))
				(get objtype 'pgsymbols))
			   ;; new empty obarray for setids or if unset
			   (put objtype 'pg-symbols (make-vector 31 0)))))
	(setq proof-assistant-idtables
	      (if (and (null idents) (eq opn 'setids))
		  (delete objtype proof-assistant-idtables)
		(adjoin objtype proof-assistant-idtables)))
	(cond
	 ((or (eq opn 'setids) (eq opn 'addids))
	  (mapc (lambda (i) (intern i obarray)) idents))
	 ((eq opn 'delids)
	  (mapc (lambda (i) (unintern i obarray)) idents))
	 (t
	  (pg-pgip-error "Pg-pgip-process-ids: called on wrong node %s"
			 (xml-node-name node))))))))

(defun pg-complete-idtable-symbol ()
  (interactive)
  ;; TODO: complete based on blah
  )

(defalias 'pg-pgip-process-setids 'pg-pgip-process-ids)
(defalias 'pg-pgip-process-addids 'pg-pgip-process-ids)
(defalias 'pg-pgip-process-delids 'pg-pgip-process-ids)


(defun pg-pgip-process-idvalue (node)
  (let ((name     (pg-pgip-get-name node))
	(objtype  (pg-pgip-get-objtype node))
	(text     (pg-pgip-get-displaytext node)))
    ;; TODO: display and cache the value in a dedicated buffer
    ;; FIXME: should idvalue have a context?
    (pg-response-message text)))
    
;;
;; Menu configuration [TODO]
;;

(defun pg-pgip-process-menuadd (node)
  )

(defun pg-pgip-process-menudel (node)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Message processing: fromprovermsg/proveroutput
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pg-pgip-process-ready (node)
  )

(defun pg-pgip-process-cleardisplay (node)
  (let ((area	(pg-pgip-get-area node)))
    (cond
     ((equal area "message")
      (pg-response-maybe-erase nil t t))
     ((equal area "display")
      (proof-clean-buffer proof-goals-buffer))
     ((equal area "all")
      (pg-response-maybe-erase nil t t)
      (proof-clean-buffer proof-goals-buffer)
      ;; TODO: could also erase trace here.
      ;; [PGIP: Should trace have a separate cat?]
      ))))

(defun pg-pgip-process-proofstate (node)
  ;(let ((pgml	(pg-xml-child )
  )

(defun pg-pgip-process-normalresponse (node)
  (let ((text     (pg-pgip-get-displaytext node)))
    (pg-response-message text)))

(defun pg-pgip-process-errorresponse (node)
  (let ((text     (pg-pgip-get-displaytext node)))
    (pg-response-warning text)))

(defun pg-pgip-process-scriptinsert (node)
  (let ((text     (pg-pgip-get-displaytext node)))
    (proof-insert-pbp-command text)))


(defun pg-pgip-process-metainforesponse (node)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Message processing: fromprovermsg/fileinfomsg
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pg-pgip-file-of-url (urlstr)
  (save-match-data
    (if (string-match "^file:///\\(.*\\)$" urlstr)
	(match-string 1 urlstr))))

(defun pg-pgip-process-informfileloaded (node)
  (let* ((thyname   (pg-pgip-get-thyname node))
	 (url	    (pg-pgip-get-url node))
	 (filename  (pg-pgip-file-of-url url)))
    (proof-register-possibly-new-processed-file filename)))

(defun pg-pgip-process-informfileretracted (node)
  (let* ((thyname    (pg-pgip-get-thyname node))
	 (url	     (pg-pgip-get-url node))
	 (filename   (pg-pgip-file-of-url url)))
    ;(proof-unregister-possibly-processed-file filename))) ;; unimplemented!
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Message processing: todisplaymsg/brokermsg
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pg-pgip-process-brokerstatus (node)
  )

(defun pg-pgip-process-proveravailmsg (node)
  )

(defun pg-pgip-process-newprovermsg (node)
  )

(defun pg-pgip-process-proverstatusmsg (node)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Message processing: todisplaymsg/dispmsg/dispfilemsg
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar pg-pgip-srcids nil
  "Association list of srcrds to (buffer file) lists")

;; FIXME: right action?
(defun pg-pgip-process-newfile (node)
  "Process <newfile> message from broker by displaying file.
Also sets local proverid and srcid variables for buffer."
  (let* ((srcid	    (pg-pgip-get-srcid node))
	 (proverid  (pg-pgip-get-proverid node))
	 (url	    (pg-pgip-get-url node))
	 (file	    (pg-pgip-file-of-url url)))
    (find-file file)
    (let ((buffer (get-file-buffer file)))
      (with-current-buffer buffer
	(make-local-variable 'proverid)
	(setq proverid proverid))
      (set pg-pgip-srcids (acons srcid (list buffer file) pg-pgip-srcids)))))


;; FIXME: right action?
(defun pg-pgip-process-filestatus (node)
  "Process <filestatus> flag by adjusting buffer's modified flag."
  (let* ((srcid	    (pg-pgip-get-srcid node))
	 (filestat  (pg-xml-get-attr 'filestat node))
	 (buffer    (car-safe (cdr-safe (assoc srcid pg-pgip-srcids)))))
    (proof-with-current-buffer-if-exists buffer
      (cond
       ((equal filestat "changed")
	(set-buffer-modified-p t))
       ((equal filestat "saved")
	(set-buffer-modified-p nil))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Message processing: todisplaymsg/dispmsg/dispobjmsg
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pg-pgip-process-newobj (node)
  )

(defun pg-pgip-process-delobj (node)
  )

(defun pg-pgip-process-objectstatus (node)
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Message processing: parsescript [incomplete]
;;
;; NB: pgip.rnc v 2.18 only has parsescript sent to prover,
;; so if we get here we have a invalid document.
;;
;; Provide parsing functionality for other interfaces (sacrilege!)
;;

(defun pg-pgip-process-parsescript (node)
  ;; Text ought to be cdata or something. We'll stick it into a buffer
  ;; and run the proof-script code on it.
  (save-excursion
    (let* ((text (pg-xml-get-text-content node))
	   (buf  (get-buffer-create " *pgip-parsescript*")))
      (delete-region (point-min) (point-max)) ; wipe previous contents
      (insert text)
      (let ((semis (proof-segment-up-to (point))))
	;; semis is now a list of (type, string, int) tuples (in reverse order).
	;; we'll turn it into XML and send it back to the prover
	;; FIXME: todo: make parseresult element according to types,
	;; properscriptcmd = properproofcmd | properfilecmd | bindid
	))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; PGIP types and values <-> Elisp types and values
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun pg-pgip-get-pgiptype (node)
  "Return internal (custom format) representation for <pgiptype> element in NODE."
  (let ((tyname (and node (xml-node-name node))))
    (cond
     ((eq tyname 'pgipbool)	'boolean)
     ((eq tyname 'pgipint)	'integer) ;; TODO: implement range limits
     ((eq tyname 'pgipfloat)	'float)   ;; TODO: implement range limits
     ((eq tyname 'pgipstring)	'string)
     ((eq tyname 'pgipconst)
      (let ((name	(pg-pgip-get-name node 'optional))
	    (val	(pg-pgip-get-value node)))
	(if name
	    (list 'const :tag name val)
	  (list 'const val))))
     ((eq tyname 'pgipchoice)
      (let* ((choicesnodes  (pg-xml-child-elts node))
	     (choices       (mapcar 'pg-pgip-get-pgiptype choicesnodes)))
	(list 'choice choices)))
     (t
      (pg-pgip-warning "pg-pgip-get-pgiptype: unrecognized/missing typename \"%s\"" tyname)))))

(defun pg-pgip-default-for (type)
  "Synthesize a default value for type TYPE."
  (cond
   ((eq type 'boolean)  nil)
   ((eq type 'integer)  0)
   ((eq type 'string)   "")
   ((eq (car-safe type) 'const)
    (car (last type)))
   ((eq (car-safe type) 'choice)
    (pg-pgip-default-for (car-safe (cdr-safe type))))
   (t
    (pg-pgip-error "pg-pgip-default-for: unrecognized type passed in"))))

(defun pg-pgip-subst-for (type)
  "Return a substitution string for type TYPE."
  (cond
   ((eq type 'boolean) "%b")
   ((eq type 'integer) "%i")
   ((eq type 'float) "%f")
   (t "%s")))


;; Converting PGIP representations to elisp representations.  This is
;; the inverse of proof-assistant-format translations in
;; proof-menu.el, although we fix PGIP value syntax.

(defun pg-pgip-interpret-value (value type)
  "Interpret the PGIP value VALUE at (lisp-representation for) TYPE."
  (cond
   ((eq type 'boolean)
    (cond
     ((or (string-equal value "true") (string-equal value "1"))  t)
     ((or (string-equal value "false") (string-equal value "0")) nil)
     (t (progn
	  (pg-pgip-warning "pg-pgip-interpret-value: received non-bool value %s" value)
	  nil))))
   ((eq type 'integer)	(string-to-number value))
   ((eq type 'float)	(string-to-number value))
   ((eq type 'string)	 value)
   ((eq (car-safe type) 'const)  value)
   ((eq (car-safe type) 'choice)
    (pg-pgip-interpret-choice (cdr type) value))
   (t
    (pg-pgip-error "pg-pgip-interpret-value: unkown type %s" type))))

(defun pg-pgip-interpret-choice (choices value)
  ;; Untagged union types: test for value in each type in turn.
  (let (res)
    (while (and choices (not res))
      (let ((type (car choices)))
	(cond
	 ((and (eq (car-safe type) 'const)
	       (string-equal value (cadr type)))
	  (setq res (pg-pgip-interpret-value value 'const)))
	 ((and (eq type 'integer)
	       (string-match "[+-]?[0-9]+$" value))
	  (setq res (pg-pgip-interpret-value value 'integer)))
	 ((and (eq type 'boolean)
	       (or (string-equal value "true")
		   (string-equal value "false")
		   (string-equal value "0")
		   (string-equal value "1")))
	  (setq res (pg-pgip-interpret-value value 'boolean)))
	 ((eq type 'string)
	  (setq res (pg-pgip-interpret-value value 'string)))))
      (setq choices (cdr choices)))
    (or res
	(pg-pgip-error
	 "pg-pgip-interpret-choice: mismatching value %s for choices %s"
	 value choices))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Sending PGIP commands to prover
;;

(defun pg-pgip-string-of-command (pgip &optional refseq refid otherclass)
  "Convert XML node PGIP or string into a command string to send to the prover.
This wraps the node in a <pgip> packet with appropriate attributes.
See `pg-pgip-assemble-packet' "
  (let ((wrappedpgip
	 (pg-xml-string-of
	  (list (pg-pgip-assemble-packet (list pgip) refseq refid otherclass)))))
    (cond
     ((stringp proof-shell-issue-pgip-cmd)
      (format proof-shell-issue-pgip-cmd wrappedpgip))
     ((functionp proof-shell-issue-pgip-cmd)
      (funcall proof-shell-issue-pgip-cmd wrappedpgip))
     (t
      ;; FIXME: Empty setting: might be better to send a comment
      (pg-pgip-warning "pg-prover-interpret-pgip-command: `proof-shell-issue-pgip' is unset!")
      ""))))

(defconst pg-pgip-id
  ;; Identifier based on hostname, user, time, and (FIXME: possible?) ppid
  (concat (getenv "HOSTNAME") "/" (getenv "USER") "/"
	  (let ((tm (current-time))) (format "%d.%d" (car tm) (cadr tm))))
  "PGIP Identifier for this Emacs Proof General component.")

(defvar pg-pgip-refseq nil
  "The sequence number of the received message this reply refers to")
(defvar pg-pgip-refid nil
  "The identity of the component this message is being sent to")

(defvar pg-pgip-seq 0 "Sequence number of messages sent out.")

(defun pg-pgip-assemble-packet (body &optional refseq refid otherclass)
  "Construct a PGIP node with body list BODY.
REFSEQ and REFID are used for the corresponding attributes, if present.
By default, the class of the message is \"pa\" (destined for prover).
OTHERCLASS overrides this."
  (let* ((tag	        (pg-xml-attr tag
				     (concat "EmacsPG/"
					     proof-general-short-version
					     "/" proof-assistant)))
	 (id		(pg-xml-attr id pg-pgip-id))
	 (class		(pg-xml-attr class (or otherclass "pa")))
	 (seq		(pg-xml-attr seq (int-to-string (incf pg-pgip-seq))))
	 (refseq        (if refseq (list (pg-xml-attr refseq refseq))))
	 (refid         (if refid (list (pg-xml-attr refid refid))))
	 (pgip_attrs	(append (list tag id class seq)
				refseq refid)))
    (pg-xml-node pgip pgip_attrs body)))

(defun pg-pgip-issue (pgip &optional block refseq refid otherclass)
  "Issue a PGIP command via `proof-shell-issue-pgip-cmd' and `proof-shell-invisible-command'.
This expects a single XML node/string in PGIP, which will have a PGIP
header attached.  If BLOCK is non-nil, we wait for the response from
the prover.  For remaining optional args, see doc of
`pgip-assemble-packet'."
  (proof-shell-invisible-command
   (pg-pgip-string-of-command pgip refseq refid otherclass) block))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Functions to send particular commands
;;

;;;###autoload
(defun pg-pgip-maybe-askpgip ()
  "Send an <askpgip> message to the prover if PGIP is supported."
  (if proof-shell-issue-pgip-cmd
      (pg-pgip-issue "<askpgip/>" 'block)))

;;;###autoload
(defun pg-pgip-askprefs ()
  "Send an <askprefs> message to the prover."
  (pg-pgip-issue "<askprefs/>" 'block))

(defun pg-pgip-askids (&optional objtype thyname)
  "Send an <askids> message to the prover."
  (pg-pgip-issue
   (pg-xml-node askids
		(append
		 (if thyname
		     (list (pg-xml-attr 'thyname objtype)))
		 (if objtype
		     (list (pg-xml-attr 'objtype objtype))))
		nil)
   'block))


(defun pg-pgip-reset ()
  "Reset state of the PGIP module"
  (setq pg-pgip-refseq nil
	pg-pgip-refid  nil
	pg-pgip-last-seen-id nil
	pg-pgip-last-seen-seq nil
	pg-pgip-seq 0
	proof-assistant-settings nil ;; optional
	proof-assistant-idtables nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Standalone PGIP processing -- Emacs in batch mode, yuk!
;;

;; TODO: output PGIP on stdout, read in on stdin.

;; standard-input
;; standard-output

;; (defun pg-pgip-filter ()
;;   (let (instuff outstuff)
;;     (while (setq (read-char standard-input)) ;; reads lisp!!!
;; )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Constants for export
;;

(defconst pg-pgip-start-element-regexp "<pgip\\s-")
(defconst pg-pgip-end-element-regexp   "</pgip>")



(provide 'pg-pgip)
;;; pg-pgip.el ends here
