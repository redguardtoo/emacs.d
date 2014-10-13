;; pg-pbrpm.el --- Proof General - Proof By Rules Pop-up Menu - mode.
;;
;; Copyright (C) 2004 - Universite de Savoie, France.
;; Authors:   Jean-Roch SOTTY, Christophe Raffalli
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; pg-pbrpm.el,v 12.0 2011/10/13 10:54:49 da Exp
;;
;;; Commentary:
;; 
;; Analyse the goal buffer to produce a popup menu.
;;
;; NB: this code is currently XEmacs specific
;; (uses make-gui-button, insert-gui-button, make-dialog-frame)
;;
;; da: can you simply use
;;   make-button/make-text-button and something like
;;
;;   (make-frame '((minibuffer . nil) (menu-bar-lines . 0) (tool-bar-lines . nil)))

(declare-function proof-pbrpm-generate-menu "nofile")
(declare-function insert-gui-button "nofile")
(declare-function make-gui-button "nofile")
(declare-function make-dialog-frame "nofile")
(declare-function event-point "nofile")
(declare-function event-buffer "nofile")
(declare-function default-mouse-track-return-dragged-selection "nofile")
(declare-function default-mouse-track-drag-hook "nofile")
(declare-function mouse-track "nofile")

;;



;;; Code:
(require 'span)
(eval-when-compile
  (require 'proof-utils))

(require 'proof)

;;;
;;; Configuration
;;;
(defvar pg-pbrpm-use-buffer-menu t
  "If t, pbrpm will use a menu displayed in a dialog frame instead of a popup menu.")

(defvar pg-pbrpm-start-goal-regexp nil
  "Regexp to match start of goals.
Used to produce a table of goal descriptions in `pg-pbrpm-analyse-goal-buffer'.")

(defvar pg-pbrpm-start-goal-regexp-par-num nil
  "Match number for `pg-pbrpm-start-goal-regexp' to extract goal number.")

(defvar pg-pbrpm-end-goal-regexp nil
  "Regexp to match end of goal.
Used to produce a table of goal descriptions in `pg-pbrpm-analyse-goal-buffer'.")

(defvar pg-pbrpm-start-hyp-regexp nil
  "Regexp to match start of hypothesis.
Used to produce a table of goal descriptions in `pg-pbrpm-analyse-goal-buffer'.")

(defvar pg-pbrpm-start-hyp-regexp-par-num nil
  "Match number for `pg-pbrpm-start-hyp-regexp' to extract hypothesis number.
Used to produce a table of goal descriptions in `pg-pbrpm-analyse-goal-buffer'.")

(defvar pg-pbrpm-start-concl-regexp nil
  "Regexp to match start of conclusions.
Used to produce a table of goal descriptions in `pg-pbrpm-analyse-goal-buffer'.")

(defvar pg-pbrpm-auto-select-regexp nil
  "Regexp used to select regions of text around point.
Matches the region to be returned.")

;;;
;;; Local variables
;;;
(defvar pg-pbrpm-buffer-menu nil)
(defvar pg-pbrpm-spans nil)
(defvar pg-pbrpm-goal-description nil)
(defvar pg-pbrpm-windows-dialog-bug nil)
(defvar pbrpm-menu-desc nil)

(defun pg-pbrpm-erase-buffer-menu ()
  (with-current-buffer pg-pbrpm-buffer-menu
    (mapc 'span-delete pg-pbrpm-spans)
    (setq pg-pbrpm-spans nil)
    (erase-buffer)))

(defun pg-pbrpm-menu-change-hook (start end len)
  (save-excursion
    (let ((span (span-at (- start 1) 'editable)))
      (if (not span) (setq span (span-at start 'editable)))
      (if span
	  (let ((len (- (span-end span) (span-start span))))
	    (mapc (lambda (sp)
		    (let* ((p1 (span-start sp))
			   (p2 (span-end sp))
			   (spl (span-at p1 'pglock)))
		      (span-read-write spl)
		      (goto-char p1)
		      (insert (span-string span))
		      (delete-region (+ p1 len) (+ p2 len))
		      (span-read-only spl)))
		  (span-property span 'occurrences)))))))


(defun pg-pbrpm-create-reset-buffer-menu ()
  "Create if necessary and erase all text in the buffer menu."
  (if (or (not pg-pbrpm-buffer-menu) (not (buffer-live-p pg-pbrpm-buffer-menu)))
      (progn
	(setq pg-pbrpm-buffer-menu
	      (generate-new-buffer (generate-new-buffer-name "*proof-menu*")))
	(set-buffer pg-pbrpm-buffer-menu)
; needs to be fixed here, the mode could be some other prover
;	(phox-mode)
; da: proof-mode-for-script should do it
; cr: proof-mode-for-script is not defined in 3.7
;	(if (functionp 'proof-mode-for-script)
;	    (funcall 'proof-mode-for-shell) (funcall 'proof-mode))
; da: it's the name of a function, not fn itself. See pg-vars
	(funcall proof-mode-for-script)
	(add-hook 'after-change-functions 'pg-pbrpm-menu-change-hook nil t)
    (pg-pbrpm-erase-buffer-menu)))
  (set-buffer pg-pbrpm-buffer-menu))

(defun pg-pbrpm-analyse-goal-buffer ()
  "This function analyses the goal buffer and produces a table to find goals and hypothesis.
If stores, in the variable pg-pbrpm-goal-description, a list with shape

   (start-goal end-goal goal-name start-concl hyps ...) with 5 elements for each goal:

     start-goal: the position of the first char of the goal
     end-goal: the position of the last char of the goal
     goal-name: the goal name (or number)
     start-concl: the position of first char of the conclusion of the goal
     hyps: the list of hypothesis with the shape:

  (start-hyp start-hyp-text end-hyp hyp-name ...) with 4 elemets per hypothesis:
     start-hyp: the position of the first char of the hypothesis (including its name)
     start-hyp-text: the position of the first char of the hypothesis formula (no name)
     end-hyp: the position of the last char of the hypothesis
     hyp-name: then name of the hypothesis."
  (with-current-buffer proof-goals-buffer
  (save-excursion
    (goto-char 0)
    (let
	((goals nil))
      (progn
	(while (search-forward-regexp pg-pbrpm-start-goal-regexp nil t)
	  (let
	      ((hyps nil)
	       (start-goal (match-end 0))
	       (goal-num (match-string pg-pbrpm-start-goal-regexp-par-num))
	       (end-goal (search-forward-regexp pg-pbrpm-end-goal-regexp nil t)))
	    (goto-char start-goal)
	    (while (search-forward-regexp pg-pbrpm-start-hyp-regexp end-goal t)
	      (let
		  ((start-hyp (match-beginning 0))
		   (start-hyp-text (match-end 0))
		   (hyp-name (match-string pg-pbrpm-start-hyp-regexp-par-num))
		   (end-hyp (- (if
				(search-forward-regexp pg-pbrpm-start-hyp-regexp end-goal t)
				(match-beginning 0)
			      (search-forward-regexp pg-pbrpm-start-concl-regexp end-goal t)
			      (match-beginning 0)) 1)))
		(goto-char start-hyp-text)
		(setq hyps
		      (append
		       (list start-hyp start-hyp-text end-hyp hyp-name)
		       hyps))))

	    (setq goals
		  (append
		   (list start-goal end-goal goal-num
			 (search-forward-regexp pg-pbrpm-start-concl-regexp nil t) hyps)
		   goals))))
	  (setq pg-pbrpm-goal-description goals))))))

(add-hook 'proof-shell-handle-delayed-output-hook 'pg-pbrpm-analyse-goal-buffer)


;;--------------------------------------------------------------------------;;
;; the Rules Popup Menu functions
;;--------------------------------------------------------------------------;;

(defun pg-pbrpm-button-action (event)
"This function is bound to a CTRL-RightClick in the Proof General goals buffer."
   (interactive "e")
   (save-excursion
   (pg-pbrpm-build-menu event (point-marker) (mark-marker))
   )
)
(defun pg-pbrpm-exists (f l0)
  (if (null l0) nil
    (or (funcall f (car l0)) (pg-pbrpm-exists f (cdr l0)))))

(defun pg-pbrpm-eliminate-id (acc l)
  (if (null l) (reverse acc)
    (if
	(pg-pbrpm-exists (lambda (x)
			   (string= (car x) (car (car l)))) acc)
	(pg-pbrpm-eliminate-id acc (cdr l))
      (pg-pbrpm-eliminate-id (cons (car l) acc) (cdr l)))))

(defun pg-pbrpm-build-menu (event start end)
"Build a Proof By Rules pop-up menu according to the state of the proof, the event and a selected region (between the start and end markers).
The prover command is processed via pg-pbrpm-run-command."
;; first, run the prover specific (name, rule)'s list generator
   (let ((click-info (pg-pbrpm-process-click event start end))) ; retrieve click informations
     (if click-info
	 (let ((pbrpm-list
		(pg-pbrpm-eliminate-id
		 nil
		 (mapcar 'cdr
			 (sort
			  (proof-pbrpm-generate-menu
			   click-info
			   (pg-pbrpm-process-regions-list))
			  (lambda (l1 l2) (< (car l1) (car l2)))))))
	       (count 0))
	   ;; retrieve selected region informations
	   ;; then make that list a menu description
	   (if pbrpm-list
	       (if (not pg-pbrpm-use-buffer-menu)
		   (progn
		     (setq pbrpm-menu-desc '("PBRPM-menu"))
		     (while pbrpm-list
		       (let* ((pbrpm-list-car (pop pbrpm-list))
			      (description (pop pbrpm-list-car))
			      (command (concat "(*" description "*)\n"
					       (pop pbrpm-list-car))))
			 (setq pbrpm-menu-desc
			       (append pbrpm-menu-desc
				       (list (vector
					      description
					      (list 'pg-pbrpm-run-command
						    (list command nil nil))))))))
		     ;; finally display the pop-up-menu
		     (popup-menu pbrpm-menu-desc))
		 (pg-pbrpm-create-reset-buffer-menu)
		 (while pbrpm-list
		   (let* ((pbrpm-list-car (pop pbrpm-list))
			  (description (pop pbrpm-list-car))
			  (command (pop pbrpm-list-car))
			  (act (pop pbrpm-list-car))
			  (pos (point)))
		     (setq count (+ 1 count))
		     (insert " ")
		     (insert description)
		     (insert " ") ; hack for renaming of last name
		     (let ((spans (pg-pbrpm-setup-span pos (point))))
		       (insert-gui-button (make-gui-button
					   (concat (int-to-string count) ")")
					   'pg-pbrpm-run-command
					   (list command act spans)) pos))
		     (insert "\n")))
		 (insert-gui-button
		  (make-gui-button
		   "Cancel"
		   (lambda (n) (pg-pbrpm-erase-buffer-menu) (delete-frame)) nil))
		 ;; needs to be fixed for other prover than phox
		 ;; da: I've removed code here, we should simply keep this
		 ;; buffer with font lock on.
		 (mapc 'span-read-only pg-pbrpm-spans)
		 (make-dialog-frame '(width 80 height 30)))
	       (beep))))))

(defun pg-pbrpm-setup-span (start end)
  "Set up the span in the menu buffer."
  (save-excursion
    (let ((rank 0) (spans nil) (allspan (span-make start end)))
      (while (< start end)
	(goto-char start)
	(let ((pos (search-forward "\\[" end 0)) (goalnum 0))
	  (if pos (progn
		    (delete-char -2)
		    (setq end (- end 2))
		    (setq pos (- pos 2))))
;	  (message "make l span %d %d" start (if pos pos end))
	  (let ((span (span-make start (if pos pos end))))
	    (span-set-property span 'pglock t)
	    (setq pg-pbrpm-spans (cons span pg-pbrpm-spans)))
	  (if pos
	      (progn
		(search-forward "\\]" end)
		(delete-char -2)
		(setq end (- end 2))
		(setq start (point))
		(save-excursion
		  (goto-char pos)
		  (if (search-forward-regexp "\\\\|\\([0-9]\\)" start t)
		      (progn
			(setq goalnum (string-to-number (match-string 1)))
			(let ((len (- (match-end 0) (match-beginning 0))))
			  (setq end (- end len))
			  (setq start (- start len)))
			(delete-region (match-beginning 0) (match-end 0)))))
		(let* ((span (span-make pos start))
		       (str (concat "\\{" (span-string span)
				    (if (= goalnum 0) ""
				      (concat "\\|" (int-to-string goalnum)))
				    "\\}"))
		       (len (- start pos))
		       (occurrences nil))
		(save-excursion
		  (goto-char pos)
		  (while (search-forward str end t)
		    (setq end (+ (- end (- (match-end 0) (match-beginning 0))) len))
		    (delete-region (match-beginning 0) (match-end 0))
		    (insert (span-string span))
;		    (message "span o %d %d"  (match-beginning 0) (+ (match-beginning 0) len))
		    (setq occurrences (cons (span-make (match-beginning 0) (+ (match-beginning 0) len))
					   occurrences))))
;		(message "make w span %d %d %s %d" pos start (span-string span) goalnum)
		(setq spans (cons span spans))
		(setq rank (+ rank 1))
		(span-set-property span 'editable t)
		(span-set-property span 'rank rank)
		(span-set-property span 'goalnum goalnum)
		(span-set-property span 'occurrences occurrences)
		(span-set-property span 'original-text (span-string span))
		(span-set-property span 'face 'pg-pbrpm-menu-input-face)))
	    (setq start (if pos pos end)))))
      (cons allspan (sort (reverse spans) (lambda (sp1 sp2)
				  (< (span-property sp1 'goalnum)
				     (span-property sp1 'goalnum))))))))

(defun pg-pbrpm-run-command (args)
"Insert COMMAND into the proof queue and then run it.
-- adapted from proof-insert-pbp-command --"
   (let* ((command (pop args)) (act (pop args)) (spans (pop args)) (allspan (pop spans)))
     (if act (setq command (apply act command spans nil)))
     (if allspan (setq command (concat "(* " (span-string allspan) " *)\n" command ".")))
     ; delete buffer (and its span) after applying "act"
     (pg-pbrpm-erase-regions-list)
     (if pg-pbrpm-use-buffer-menu
	 (progn
	   (pg-pbrpm-erase-buffer-menu)
	   (delete-frame)))
     ;; da: why not just this?
     (pop-to-buffer proof-script-buffer)
     (let ((proof-next-command-on-new-line t))
       (proof-insert-pbp-command command))))
     ;; (let (span)
     ;;   (pop-to-buffer proof-script-buffer)
     ;;   (proof-goto-end-of-locked)
     ;;   (proof-activate-scripting nil 'advancing)
     ;;   (insert (concat "\n" command))
     ;;   (setq span (span-make (proof-unprocessed-begin) (point)))
     ;;  ; TODO : define the following properties for PBRPM, I don't understand their use ...
     ;;   (span-set-property span 'type 'pbp)
     ;;   (span-set-property span 'cmd command)
     ;;   (proof-start-queue (proof-unprocessed-begin) (point)
     ;; 			  (list (list span (list command)
     ;; 				      'proof-done-advancing))))))

;;--------------------------------------------------------------------------;;
;; Click Informations extractors
;;--------------------------------------------------------------------------;;

(defun pg-pbrpm-get-pos-info (pos)
  "Get position information for POS.
Returns (n . s) where
    n is the goal name
    s if either the hypothesis name,
	 \"none\" (for the conclusion),
	 or \"whole\" in strange cases."
  (let ((l pg-pbrpm-goal-description)
	(found nil)
	start-goal end-goal goal-name start-concl hyps
	the-goal-name the-click-info start-hyp end-hyp
	start-hyp-text hyp-name)
    (while (and pos l (not found))
      (setq start-goal (car l))
      (setq end-goal (cadr l))
      (setq goal-name (caddr l))
      (setq start-concl (cadddr l))
      (setq hyps (car (cddddr l)))
      (setq l (cdr (cddddr l)))
      (if (and (<= start-goal pos) (<= pos end-goal))
	  (progn
	    (setq found t)
	    (setq the-goal-name goal-name))))
    (if found
	(progn
	  (if (<= start-concl pos)
	      (setq the-click-info "none")
	    (setq found nil)
	    (while (and hyps (not found))
	      (setq start-hyp (car hyps))
	      (setq start-hyp-text (cadr hyps))
	      (setq end-hyp (caddr hyps))
	      (setq hyp-name (cadddr hyps))
	      (setq hyps (cddddr hyps))
	      (if (and (<= start-hyp pos) (<= pos end-hyp))
		  (progn
		    (setq found t)
		    (setq the-click-info hyp-name))))
	    (if (not found)
		(setq the-click-info "whole")))
	  (cons the-goal-name the-click-info)))))

(defun pg-pbrpm-get-region-info (start end)
  "Get position info for a region, if region is within a single position.
See `pg-pbrpm-get-pos-info'."
   (let ((r1 (pg-pbrpm-get-pos-info start))
	 (r2 (pg-pbrpm-get-pos-info end))) ;; da: this said start, surely wrong?
     (if (and r1 r2 (string-equal (car r1) (car r2)))
	 (if (string-equal (cdr r1) (cdr r2))
	     r1
	   (cons (car r1) "whole"))
       nil)))

(defun pg-pbrpm-auto-select-around-point ()
  "Extract some text arround point, according to `pg-pbrpm-auto-select-regexp'.
If no match found, return the empty string."
  (save-excursion
    (let ((pos (point)))
      (beginning-of-line)
      (block 'loop
	(while (< (point) pos)
	  (unless (search-forward-regexp pg-pbrpm-auto-select-regexp nil t)
	    (return-from 'loop ""))
	  (if (and (<= (match-beginning 0) pos)
		   (<= pos (match-end 0)))
	      (return-from 'loop (match-string 0))))
	(return-from 'loop "")))))

(defun pg-pbrpm-translate-position (buffer pos)
  "return pos if buffer is goals-buffer otherwise, return the point position in
the goal buffer"
  (if (eq proof-goals-buffer buffer)
      pos
    (with-current-buffer proof-goals-buffer
      (point))))

(defun pg-pbrpm-process-click (event start end)
"Returns the list of informations about the click needed to call generate-menu. EVENT is an event."
  (save-excursion
    (save-window-excursion
      (mouse-set-point event)
      (let* ((pos (event-point event))
	     (buffer (event-buffer event))
	     (r (pg-pbrpm-get-pos-info  (pg-pbrpm-translate-position buffer pos))))
	(if r (list
	       (string-to-number (car r)) ; should not be an int for other prover
	       (if (eq proof-goals-buffer buffer) (cdr r) (pg-pbrpm-auto-select-around-point))
	       (if (and start end (eq proof-goals-buffer buffer)
			(<= (marker-position start) pos) (<= pos  (marker-position end)))
		   (pg-pbrpm-region-expression buffer (marker-position start)
					       (marker-position end))
		 (pg-pbrpm-auto-select-around-point))))))))

;;--------------------------------------------------------------------------;;
;; Selected Region informations extractors
;;--------------------------------------------------------------------------;;
(defvar pg-pbrpm-remember-region-selected-region nil)
(defvar pg-pbrpm-regions-list nil)

(defun pg-pbrpm-erase-regions-list ()
  (mapc (lambda (span) (span-delete span)) pg-pbrpm-regions-list)
  (setq pg-pbrpm-regions-list nil)
  nil)

(add-hook 'mouse-track-drag-up-hook (lambda (event count)
				      (if (not (member 'control (event-modifiers event)))
					  (pg-pbrpm-erase-regions-list))))

(defun pg-pbrpm-filter-regions-list ()
  (let ((l pg-pbrpm-regions-list))
    (setq pg-pbrpm-regions-list nil)
    (mapc (lambda (span) (if (span-live-p span)
			     (setq pg-pbrpm-regions-list (cons span pg-pbrpm-regions-list))
			   (span-delete span))) l)))

(defface pg-pbrpm-multiple-selection-face
  (proof-face-specs
   (:background "orange")
   (:background "darkorange")
   (:italic t))
  "*Face for showing (multiple) selection."
  :group 'proof-faces)

(defface pg-pbrpm-menu-input-face
  (proof-face-specs
   (:background "Gray80")
   (:background "Gray65")
   (:italic t))
  "*Face for showing (multiple) selection."
  :group 'proof-faces)

(defun pg-pbrpm-do-remember-region (start end)
  (pg-pbrpm-filter-regions-list)
   (if (and start end (not (eq start end))) ; if a region is selected
       (let ((span (span-make start end))
	     (found nil))
	 (setq pg-pbrpm-regions-list (reverse (mapcar (lambda (oldspan)
		   (let ((oldstart (span-start oldspan))
			 (oldend (span-end oldspan)))
		     (if (and (eq (current-buffer) (span-buffer oldspan))
			      (or (and (<= start oldstart) (<= oldstart end))
				  (and (<= start oldend) (<= oldend end))))
			 (progn
			   (setq found t)
			   (span-delete oldspan)
			   span)
			 oldspan))) pg-pbrpm-regions-list)))
	 (if (not found) (setq pg-pbrpm-regions-list (cons span pg-pbrpm-regions-list)))
	 (span-set-property span 'face 'pg-pbrpm-multiple-selection-face))))

; the follwing are adapted from mouse-track-insert from mouse.el

(defun pg-pbrpm-remember-region-drag-up-hook (event click-count)
  (setq pg-pbrpm-remember-region-selected-region
	(default-mouse-track-return-dragged-selection event)))

(defun pg-pbrpm-remember-region-click-hook (event click-count)
  (default-mouse-track-drag-hook event click-count nil)
  (pg-pbrpm-remember-region-drag-up-hook event click-count)
  t)

(defun pg-pbrpm-remember-region (event &optional delete)
  "Allow multiple selection as a list of spam stored in ???. The current (standard)
   selection in the same buffer is also stored"
  (interactive "*e")
  (setq pg-pbrpm-remember-region-selected-region nil)
  (let ((mouse-track-drag-up-hook 'pg-pbrpm-remember-region-drag-up-hook)
	(mouse-track-click-hook 'pg-pbrpm-remember-region-click-hook)
	(start (point)) (end (mark)))
	       (if (and start end) (pg-pbrpm-do-remember-region start end))
	       (mouse-track event)
	       (if (consp pg-pbrpm-remember-region-selected-region)
		   (let ((pair pg-pbrpm-remember-region-selected-region))
		     (pg-pbrpm-do-remember-region (car pair) (cdr pair))))))

(defun pg-pbrpm-process-region (span)
"Returns the list of informations about the the selected region needed to call generate-menu. span is a span covering the selected region"
   (let ((start (span-start span))
	 (end (span-end span))
	 (buffer (span-buffer span))
	 r)
     (if (and start end) ; if a region is selected
	 (if (eq proof-goals-buffer buffer)
	     (progn
	       (setq r (pg-pbrpm-get-region-info start end))
	       (if r
		   (list
		    (string-to-number (car r)) ; should not be an int for other prover
		    (cdr r)
		    (pg-pbrpm-region-expression buffer start end))
		 (list 0 "none" (pg-pbrpm-region-expression buffer start end))))
	   (list 0 "none" (pg-pbrpm-region-expression buffer start end))))))

(defun pg-pbrpm-process-regions-list ()
  (pg-pbrpm-do-remember-region (point-marker) (mark-marker))
  (mapcar (lambda (span) (pg-pbrpm-process-region span)) pg-pbrpm-regions-list))

(defun pg-pbrpm-region-expression (buffer start end)
  "Valid parenthesis'd expression."
  ;; an expression is valid if it has as many left paren' as right paren'
  (with-current-buffer buffer
    (buffer-substring start end)))
;    (let
;      ((pbrpm-left-pars 0)
;      (pbrpm-right-pars 0)
;      (pos start))
;     (while (< pos end)
;       (if (proof-pbrpm-left-paren-p (char-after pos))
;	   (setq pbrpm-left-pars (+ pbrpm-left-pars 1)))
;       (if (proof-pbrpm-right-paren-p (char-after pos))
;	   (setq pbrpm-right-pars (+ pbrpm-right-pars 1)))
;       (setq pos (+ pos 1)))
;     (if (= pbrpm-left-pars pbrpm-right-pars)
;	 (buffer-substring start end buffer)
;       (progn
;	 nil ; TODO : define how to manage this error case
;					;we could call (pg-pbrpm-dialog "Selected region is not valid), then what about the state of the process ?
;	 ))))

;;--------------------------------------------------------------------------;;

(eval-after-load "pg-goals"
  '(progn
     (define-key proof-goals-mode-map [(button3)] 'pg-pbrpm-button-action)
     (define-key proof-goals-mode-map [(control button3)] 'pg-goals-yank-subterm)
     (define-key proof-goals-mode-map [(control button1)] 'pg-pbrpm-remember-region)
     (define-key proof-mode-map [(button3)] 'pg-pbrpm-button-action)
     (define-key proof-mode-map [(control button3)] 'pg-goals-yank-subterm)
     (define-key proof-mode-map [(control button1)] 'pg-pbrpm-remember-region)))

(eval-after-load "proof-script"
  '(progn
     (define-key pg-span-context-menu-keymap [(button3)] 'pg-pbrpm-button-action)
     (define-key pg-span-context-menu-keymap [(control button3)] 'pg-span-context-menu)))

(provide 'pg-pbrpm)
;;; pg-pbrpm ends here
