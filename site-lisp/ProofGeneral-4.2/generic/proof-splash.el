;; proof-splash.el -- Splash welcome screen for Proof General
;;
;; Copyright (C) 1998-2005, 2009, 2010 LFCS Edinburgh.
;; Author:    David Aspinall
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; proof-splash.el,v 12.2 2012/01/14 12:50:48 tews Exp
;;
;;
;;; Commentary:
;; 
;; Provide splash screen for Proof General.
;;
;; The idea is to have a replacement for the usual splash screen.
;; This is slightly tricky: when to call proof-splash-display-screen?
;; We'd like to call it during loading/initialising.  But it's hard to
;; make the screen persist after loading because of the action of
;; display-buffer invoked after the mode function during find-file.
;;
;; To approximate the best behaviour, we assume that this file is
;; loaded by a call to proof-mode.  We display the screen now and add
;; a wait procedure temporarily to proof-mode-hook which prevents
;; redisplay until proof-splash-time has elapsed.
;;

;;; Code:

(require 'proof-site)

;;
;; Customization of splash screen
;;

(defcustom proof-splash-enable t
  "*If non-nil, display a splash screen when Proof General is loaded."
  :type 'boolean
  :group 'proof-user-options)

(defcustom proof-splash-time 8
  "Minimum number of seconds to display splash screen for.
The splash screen may be displayed for a wee while longer than
this, depending on how long it takes the machine to initialise
Proof General."
  :type 'number
  :group 'proof-general-internals)

(defcustom proof-splash-contents
  '(list
    nil
    (proof-get-image "pg-text" t)
    nil
    (proof-get-image "ProofGeneral")
    nil
    "Welcome to"
    (concat proof-assistant " Proof General!")
    nil
    (concat "Version " proof-general-short-version ".")
    nil
    (concat "(C) LFCS, University of Edinburgh " proof-general-version-year)
    nil
    nil
    :link '("    Read the "
	    "Proof General documentation"
	   (lambda (button) (info "ProofGeneral")))
    :link '("    Please report problems at "
	    "Proof General trac"
	   (lambda (button)
	     (browse-url "http://proofgeneral.inf.ed.ac.uk/trac"))
	   "Report bugs at http://proofgeneral.inf.ed.ac.uk/trac")
    :link '("Visit the " "Proof General wiki"
	   (lambda (button)
	     (browse-url "http://proofgeneral.inf.ed.ac.uk/wiki"))
	   "Write lots of helpful things at http://proofgeneral.inf.ed.ac.uk/wiki")
    :link '("or the " "homepage"
	   (lambda (button)
	     (browse-url "http://proofgeneral.inf.ed.ac.uk/"))
	   "Browse http://proofgeneral.inf.ed.ac.uk/")
    nil
     :link '("Find out about Emacs on the Help menu -- start with the "
	     "Emacs Tutorial" (lambda (button) (help-with-tutorial)))
    nil
    "See this screen again with Proof-General -> About"
    )
  "Evaluated to configure splash screen displayed when entering Proof General.
A list of the screen contents.  If an element is a string or an image
specifier, it is displayed centred on the window on its own line.
If it is nil, a new line is inserted."
  :type 'sexp
  :group 'proof-general-internals)

(defconst proof-splash-startup-msg
  '(if (featurep 'proof-config) nil
     ;; Display additional hint if we guess we're being loaded
     ;; by shell script rather than find-file.
     '(list
       "To start using Proof General, visit a proof script file"
       "for your prover, using C-x C-f or the File menu."))
  "Additional form evaluated and put onto splash screen.")

(defconst proof-splash-welcome "*Proof General Welcome*"
  "Name of the Proof General splash buffer.")

(define-derived-mode proof-splash-mode fundamental-mode
  "Splash" "Mode for splash.  
\\{proof-splash-mode-map}"
  (set-buffer-modified-p nil)
  (setq buffer-read-only t))

(define-key proof-splash-mode-map "q" 'bury-buffer)
(define-key proof-splash-mode-map [mouse-3] 'bury-buffer)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defsubst proof-emacs-imagep (img)
  "See if IMG is an Emacs image descriptor."
  (and (listp img) (eq (car img) 'image)))


(defun proof-get-image (name &optional nojpeg default)
  "Construct an image instantiator for an image, or string failing that.
Different formats are chosen from according to what can be displayed.
Unless NOJPEG is set, try jpeg first. Then try gif, then xpm.
Gif filename depends on colour depth of display.
DEFAULT gives return value in case image not valid."
  (let ((jpg (vector 'jpeg :file
		     (concat proof-images-directory name ".jpg")))
	(gif (vector 'gif :file
		     (concat proof-images-directory ".gif")))
	img)
  (cond
   (window-system
    (find-image
     (list
      (list :type 'jpeg
	    :file (concat proof-images-directory name ".jpg"))
      (list :type 'gif
	    :file (concat proof-images-directory name ".gif")))))
   (t
    (or default (concat "[ image " name " ]"))))))

(defvar proof-splash-timeout-conf nil
  "Holds timeout ID and previous window config for proof splash screen.")

(defun proof-splash-centre-spaces (glyph)
  "Return number of spaces to insert in order to center given GLYPH or string.
Borrowed from startup-center-spaces."
  (let* ((avg-pixwidth     (round (/ (frame-pixel-width) (frame-width))))
	 (fill-area-width  (* avg-pixwidth (- fill-column left-margin)))
	 (glyph-pixwidth   (cond ((stringp glyph)
				  (* avg-pixwidth (length glyph)))
				 ((proof-emacs-imagep glyph)
				  (car (with-no-warnings 
					; image-size not available in tty emacs
					 (image-size glyph 'inpixels))))
				 (t
				  (error
				   "proof-splash-centre-spaces: bad arg")))))
    (+ left-margin
       (round (/ (/ (- fill-area-width glyph-pixwidth) 2) avg-pixwidth)))))

;; We take some care to preserve the users window configuration
;; underneath the splash screen.  This is just to be polite.
;; NB: not as polite as it could be: if minibuffer is active,
;; this may deactivate it.
;; NB2: There is something worse here: pending input 
;; causes this function to spoil the mode startup, if the splash
;; buffer is killed before the input has been processed.
;; Symptom is ProofGeneral mode instead of the native script mode.
;; 

(defun proof-splash-remove-screen (&optional nothing)
  "Remove splash screen and restore window config."
  (let ((splashbuf (get-buffer proof-splash-welcome)))
    (proof-splash-unset-frame-titles)
    (if (and 
	 splashbuf
	 proof-splash-timeout-conf)
	(progn
	  (if (get-buffer-window splashbuf)
	      ;; Restore the window config if splash is being displayed
	      (if (cdr proof-splash-timeout-conf)
		  (set-window-configuration (cdr proof-splash-timeout-conf))))
	  ;; Indicate removed splash screen; disable timeout
	  (disable-timeout (car proof-splash-timeout-conf))
	  (setq proof-splash-timeout-conf nil)
	  (proof-splash-remove-buffer)))))

(defun proof-splash-remove-buffer ()
  "Remove the splash buffer if it's still present."
  (let
      ((splashbuf (get-buffer proof-splash-welcome)))
    (if splashbuf 
	;; Kill should be right, but it can cause core dump
	;; on XEmacs (kill-buffer splashbuf) (TODO: check Emacs now)
	(if (eq (selected-window) (window-buffer 
				   (selected-window)))
	    (bury-buffer splashbuf)))))

(defvar proof-splash-seen nil
  "Flag indicating the user has been subjected to a welcome message.")

(defun proof-splash-insert-contents ()
  "Insert splash buffer contents into current buffer."
 (let*
     ((splash-contents (append
			(eval proof-splash-contents)
			(eval proof-splash-startup-msg)))
      s)
   (setq buffer-read-only nil)
   (erase-buffer)
   (while splash-contents
     (setq s (car splash-contents))
     (cond
      ((proof-emacs-imagep s)
       (indent-to (proof-splash-centre-spaces s))
       (insert-image s))
      ((eq s :link)
       (setq splash-contents (cdr splash-contents))
       (let ((spec (car splash-contents)))
	 (if (functionp spec)
	     (setq spec (funcall spec)))
	 (indent-to (proof-splash-centre-spaces 
		     (concat (car spec) (cadr spec))))
	 (insert (car spec))
	 (insert-button (cadr spec)
			'face (list 'link)
			'action (nth 2 spec)
			'help-echo (concat "mouse-2, RET: "
					   (or (nth 3 spec)
						     "Follow this link"))
			'follow-link t)))
      ((stringp s)
       (indent-to (proof-splash-centre-spaces s))
       (insert s)))
     (newline)
     (setq splash-contents (cdr splash-contents)))
   (goto-char (point-min))
   (proof-splash-mode)))


;;;###autoload
(defun proof-splash-display-screen (&optional timeout)
  "Save window config and display Proof General splash screen.
If TIMEOUT is non-nil, time out outside this function, definitely
by end of configuring proof mode.  Otherwise, make a key
binding to remove this buffer."
 (interactive "P")
 (proof-splash-set-frame-titles)
 (let* (;; Keep win config explicitly instead of pushing/popping because
	;; if the user switches windows by hand in some way, we want
	;; to ignore the saved value.  Unfortunately there seems to
	;; be no way currently to remove the top item of the stack.
	(winconf   (current-window-configuration))
	(curwin	   (get-buffer-window (current-buffer)))
	(curfrm    (and curwin (window-frame curwin)))
	(after-change-functions nil)	; no font-lock, thank-you.
	 ;; NB: maybe leave next one in for frame-crazy folk
	 ;;(pop-up-frames nil)		; display in the same frame.
	(splashbuf (get-buffer-create proof-splash-welcome)))

   (with-current-buffer splashbuf
     (proof-splash-insert-contents)
     (let* ((splashwin     (display-buffer splashbuf))
	    (splashfm      (window-frame splashwin))
	    ;; Only save window config if we're on same frame
	    (savedwincnf   (if (eq curfrm splashfm) winconf)))
       (delete-other-windows splashwin)
       (when timeout
	 (setq proof-splash-timeout-conf
	       (cons
		(add-timeout proof-splash-time
			     'proof-splash-remove-screen nil)
		savedwincnf))
	 (add-hook 'proof-mode-hook 'proof-splash-timeout-waiter))))

   (setq proof-splash-seen t)))

(defalias 'pg-about 'proof-splash-display-screen)

;;;###autoload
(defun proof-splash-message ()
  "Make sure the user gets welcomed one way or another."
  (interactive)
  (unless (or proof-splash-seen noninteractive)
    (if proof-splash-enable
	(progn
	  ;; disable ordinary emacs splash
	  (setq inhibit-startup-message t)
	  (proof-splash-display-screen (not (called-interactively-p 'any))))
      ;; Otherwise, a message
      (message "Welcome to %s Proof General!" proof-assistant))
    (setq proof-splash-seen t)))

(defun proof-splash-timeout-waiter ()
  "Wait for proof-splash-timeout or input, then remove self from hook."
  (while (and proof-splash-timeout-conf ;; timeout still active
	      (not (input-pending-p)))
    (sit-for 0.1))
  (if proof-splash-timeout-conf         ;; not removed yet
      (proof-splash-remove-screen))
  (if (fboundp 'next-command-event) ; 3.3: Emacs removed this
      (if (input-pending-p)
	  (setq unread-command-events
		(cons (next-command-event) unread-command-events))))
  (remove-hook 'proof-mode-hook 'proof-splash-timeout-waiter))

(defvar proof-splash-old-frame-title-format nil)

(defun proof-splash-set-frame-titles ()
  (let ((instance-name (concat
			(if (not (zerop (length proof-assistant)))
			   (concat proof-assistant " "))
		       "Proof General")))
    (setq proof-splash-old-frame-title-format frame-title-format)
    (setq frame-title-format
	  (concat instance-name ":   %b"))))

(defun proof-splash-unset-frame-titles ()
  (when proof-splash-old-frame-title-format
    (setq frame-title-format proof-splash-old-frame-title-format)
    (setq proof-splash-old-frame-title-format nil)))


(provide 'proof-splash)

;;; proof-splash.el ends here
