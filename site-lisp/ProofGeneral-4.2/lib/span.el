;;; span.el --- Datatype of "spans" for Proof General
;;
;; Copyright (C) 1998-2009 LFCS Edinburgh
;; Author:      Healfdene Goguen
;; Maintainer:  David Aspinall <David.Aspinall@ed.ac.uk>
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; span.el,v 12.0 2011/10/13 10:54:50 da Exp
;;
;;; Commentary:
;;
;; Spans are our abstraction of extents/overlays.  Nowadays
;; we implement them directly with overlays.
;;
;; In future this module should be used to implement the abstraction
;; for script buffers (only) more directly.
;;

;;; Code:
(eval-when-compile (require 'cl))       ;For lexical-let.

(defalias 'span-start 'overlay-start)
(defalias 'span-end 'overlay-end)
(defalias 'span-set-property 'overlay-put)
(defalias 'span-property 'overlay-get)
(defalias 'span-make 'make-overlay)
(defalias 'span-detach 'delete-overlay)
(defalias 'span-set-endpoints 'move-overlay)
(defalias 'span-buffer 'overlay-buffer)

(defun span-read-only-hook (overlay after start end &optional len)
  (unless inhibit-read-only
    (error "Region is read-only")))
(add-to-list 'debug-ignored-errors "Region is read-only")

(defsubst span-read-only (span)
  "Set SPAN to be read only."
  ;; Note: using the standard 'read-only property does not work.
  ;; (overlay-put span 'read-only t))
  (span-set-property span 'modification-hooks '(span-read-only-hook))
  (span-set-property span 'insert-in-front-hooks '(span-read-only-hook)))

(defsubst span-read-write (span)
  "Set SPAN to be writeable."
  (span-set-property span 'modification-hooks nil)
  (span-set-property span 'insert-in-front-hooks nil))

(defsubst span-write-warning (span fun)
  "Give a warning message when SPAN is changed, unless `inhibit-read-only' is non-nil."
  (lexical-let ((fun fun))
    (let ((funs (list (lambda (span afterp beg end &rest args)
			(if (and (not afterp) (not inhibit-read-only))
			    (funcall fun beg end))))))
      (span-set-property span 'modification-hooks funs)
      (span-set-property span 'insert-in-front-hooks funs))))

;; We use end first because proof-locked-queue is often changed, and
;; its starting point is always 1
(defsubst span-lt (s u)
  (or (< (span-end s) (span-end u))
      (and (eq (span-end s) (span-end u))
	   (< (span-start s) (span-start u)))))

(defsubst spans-at-point-prop (pt prop)
  (let (ols)
    (if (null prop) 
	(overlays-at pt)
      (dolist (ol (overlays-at pt))
	(if (overlay-get ol prop) 
	    (push ol ols)))
      ols)))

(defsubst spans-at-region-prop (start end prop)
  "Return a list of the spans in START END with PROP."
  (let (ols)
    (if (null prop)
	(overlays-in start end)
      (dolist (ol (overlays-in start end))
	(if (overlay-get ol prop)
	    (push ol ols)))
      ols)))

(defsubst span-at (pt prop)
  "Return some SPAN at point PT with property PROP."
  (car-safe (spans-at-point-prop pt prop)))

(defsubst span-delete (span)
  "Run the 'span-delete-actions and delete SPAN."
  (mapc (lambda (predelfn) (funcall predelfn))
	(span-property span 'span-delete-actions))
  (delete-overlay span))

(defsubst span-add-delete-action (span action)
  "Add ACTION to the list of functions called when SPAN is deleted."
  (span-set-property span 'span-delete-actions
		     (cons action (span-property span 'span-delete-actions))))

;; The next two change ordering of list of spans:
(defsubst span-mapcar-spans (fn start end prop)
  "Map function FN over spans between START and END with property PROP."
  (mapcar fn (spans-at-region-prop start end prop)))

(defsubst span-mapc-spans (fn start end prop)
  "Apply function FN to spans between START and END with property PROP."
  (mapc fn (spans-at-region-prop start end prop)))

(defsubst span-mapcar-spans-inorder (fn start end prop)
  "Map function FN over spans between START and END with property PROP."
  (mapcar fn 
	  (sort (spans-at-region-prop start end prop)
		'span-lt)))

(defun span-at-before (pt prop)
  "Return the smallest SPAN at before PT with property PROP.
A span is before PT if it begins before the character before PT."
  (let ((ols (if (eq (point-min) pt)
		 nil ;; (overlays-at pt)
	       (overlays-in (1- pt) pt))))
    ;; Check the PROP is set.
    (when prop
      (dolist (ol (prog1 ols (setq ols nil)))
	(if (overlay-get ol prop) (push ol ols))))
    ;; Eliminate the case of an empty overlay at (1- pt).
    (dolist (ol (prog1 ols (setq ols nil)))
      (if (>= (overlay-end ol) pt) (push ol ols)))
    ;; "Get the smallest".  I have no idea what that means, so I just do
    ;; something somewhat random but vaguely meaningful.  -Stef
    (car (last (sort ols 'span-lt)))))

(defsubst prev-span (span prop)
  "Return span before SPAN with property PROP."
  (span-at-before (span-start span) prop))

; overlays are [start, end)

(defsubst next-span (span prop)
  "Return span after SPAN with property PROP."
  ;; Presuming the span-extents.el is the reference, its code does the
  ;; same as the code below.
  (span-at (span-end span) prop))

(defsubst span-live-p (span)
  "Return non-nil if SPAN is in a live buffer."
  (and span
       (overlay-buffer span)
       (buffer-live-p (overlay-buffer span))))

(defsubst span-raise (span)
  "Set priority of SPAN to make it appear above other spans."
  (span-set-property span 'priority 100))

(defsubst span-string (span)
  (with-current-buffer (overlay-buffer span)
    (buffer-substring-no-properties 
     (overlay-start span) (overlay-end span))))

(defsubst set-span-properties (span plist)
  "Set SPAN's properties from PLIST which is a plist."
  (while plist
    (overlay-put span (car plist) (cadr plist))
    (setq plist (cddr plist))))

(defsubst span-find-span (overlay-list &optional prop)
  "Return first overlay of OVERLAY-LIST having property PROP (default 'span).
Return nil if no such overlay belong to the list."
  (let ((l overlay-list))
    (while (and l (not (overlay-get (car l) (or prop 'span))))
      (setq l (cdr l)))
    (car l)))

(defsubst span-at-event (event &optional prop)
  "Find a span at position of EVENT, optionally with property PROP."
  (span-find-span 
   (overlays-at (posn-point (event-start event))) 
   prop))

(defun fold-spans (f &optional buffer from to maparg ignored-flags prop val)
  (with-current-buffer (or buffer (current-buffer))
    (let ((ols (overlays-in (or from (point-min)) (or to (point-max))))
	  res)
      ;; Check the PROP.
      (when prop
	(dolist (ol (prog1 ols (setq ols nil)))
	  (if (if val (eq val (overlay-get ol prop)) (overlay-get ol prop))
	      (push ol ols))))
      ;; Iterate in order.
      (setq ols (sort ols 'span-lt))
      (while (and ols (not (setq res (funcall f (pop ols) maparg)))))
      res)))

(defsubst span-detached-p (span)
  "Is this SPAN detached? nil for no, t for yes."
  (null (overlay-buffer span)))

(defsubst set-span-face (span face)
  "Set the FACE of a SPAN."
  (overlay-put span 'face face))

(defsubst set-span-keymap (span map)
  "Set the keymap of SPAN to MAP."
  (overlay-put span 'keymap map))

;;
;; Generic functions built on low-level concrete ones.
;;

(defsubst span-delete-spans (start end prop)
  "Delete all spans between START and END with property PROP set."
  (span-mapc-spans 'span-delete start end prop))

(defsubst span-property-safe (span name)
  "Like span-property, but return nil if SPAN is nil."
  (and span (span-property span name)))

(defsubst span-set-start (span value)
  "Set the start point of SPAN to VALUE."
  (span-set-endpoints span value (span-end span)))

(defsubst span-set-end (span value)
  "Set the end point of SPAN to VALUE."
  (span-set-endpoints span (span-start span) value))

;;
;; Handy overlay utils
;;

(defun span-make-self-removing-span (beg end &rest props)
  "Add a self-removing span from BEG to END with properties PROPS.
The span will remove itself after a timeout of 2 seconds."
  (let ((ol (make-overlay beg end)))
    (while props
      (overlay-put ol (car props) (cadr props))
      (setq props (cddr props)))
    (add-timeout 2 'delete-overlay ol)
    ol))

(defun span-delete-self-modification-hook (span &rest args)
  "Hook for overlay modification-hooks, which deletes SPAN."
  (if (span-live-p span)
      (span-delete span)))

(defun span-make-modifying-removing-span (beg end &rest props)
  "Add a self-removing span from BEG to END with properties PROPS.
The span will remove itself after any edit within its range.
Return the span."
  (let ((ol (make-overlay beg end)))
    (while props
      (overlay-put ol (car props) (cadr props))
      (setq props (cddr props)))
    (span-set-property ol 'modification-hooks
		       (list 'span-delete-self-modification-hook))
    ol))



(provide 'span)

;;; span.el ends here
