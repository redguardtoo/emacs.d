;; bufhist.el --- keep read-only history of buffer contents for browsing

;; Copyright   (C) 2006, 2009 David Aspinall / University of Edinburgh

;; Author:     David Aspinall <David.Aspinall@ed.ac.uk>
;; License:    GPL (GNU GENERAL PUBLIC LICENSE)
;; Keywords:   tools
;;
;; bufhist.el,v 12.0 2011/10/13 10:54:50 da Exp
;;
;; This file is distributed under the terms of the GNU General Public
;; License, Version 2.  Find a copy of the GPL with your version of
;; GNU Emacs or Texinfo.
;;
;; This library implements a minor mode for which keeps a ring history of
;; buffer contents.  Intended to be used for small buffers which are
;; intermittently updated (e.g. status panels/displays), for which history
;; browsing is useful.
;;

;; TODO: this will be replaced by a more PG-specific and efficient
;; approach which keep regions within a single buffer rather than
;; copying strings in and out.  That way we can use cloned (indirect)
;; buffers which allow independent browsing of the history.
;;
;; FIXMEs: - autoloading this doesn't work too well.
;;         - advice on erase-buffer doesn't work
;;         - duplicated first item in ring after clear (& on startup).
;;         - buttons are put at top of buffer but inserts happen before them
;;

(require 'ring)

(declare-function bufhist-ordinary-erase-buffer "bufhist")

;;; First a function which ought to be in ring.el

(defun bufhist-ring-update (ring index newitem)
  "Update RING at position INDEX with NEWITEM."
  (if (ring-empty-p ring)
      (error "Accessing an empty ring")
    (let* ((hd (car ring))  (ln (car (cdr ring)))  (vec (cdr (cdr ring))))
      (aset vec (ring-index index hd ln (length vec)) newitem))))

;;; Now our code

(defgroup bufhist nil
  "In-memory history of buffer contents"
  :group 'tools)

(defcustom bufhist-ring-size 30
  "*Default size of buffer history ring."
  :group 'bufhist
  :type 'integer)

(defvar bufhist-ring nil
  "Ring history of buffer.  Always non-empty.")

(defvar bufhist-ring-pos nil
  "Current position in ring history of buffer.")

(defvar bufhist-lastswitch-modified-tick nil
  "Value of (buffer-modified-tick) at last switch buffer.")

(defvar bufhist-read-only-history t
  "Whether history is editable.")

(defvar bufhist-saved-mode-line-format nil
  "Ordinary value of `mode-line-format' for this buffer.")

(defvar bufhist-normal-read-only nil
  "Ordinary value `buffer-read-only' for this buffer.")

(defvar bufhist-top-point 0
  "Poistion of top of real buffer contents, after buttons.")

(defun bufhist-mode-line-format-entry ()
  (when bufhist-ring-pos
    (let* ((histpos   (- (ring-length bufhist-ring) bufhist-ring-pos))
	   (histsize  (ring-length bufhist-ring))
	   (desc      (format "History %d of %d; mouse-1 previous; mouse-3 next"
			      histpos histsize))
	   (indicator (format "[%d/%d]" histpos histsize)))
      (propertize
       indicator
       'help-echo desc
       'keymap (eval-when-compile
		 (let ((map (make-sparse-keymap)))
		   ;; FIXME: clicking can go wrong here because the
		   ;; current buffer can be something else which has no hist!
		   (define-key map [mode-line mouse-1] 'bufhist-prev)
		   (define-key map [mode-line mouse-3] 'bufhist-next)
		   ;; (define-key map [mode-line control mouse-1] 'bufhist-first)
		   ;; (define-key map [mode-line control mouse-3] 'bufhist-last)
		   map))
       'mouse-face 'mode-line-highlight))))

;simple:
;  '(" [hist:"
;    (:eval (int-to-string (- (ring-length bufhist-)
;			     bufhist-ring-pos))) "/"
;    (:eval (int-to-string (ring-length bufhist-ring))) "]"))

;;; Minor mode

(defconst bufhist-minor-mode-map
  (let ((map (make-sparse-keymap)))
    ;; (define-key map [mouse-2] 'bufhist-popup-menu)
    (define-key map [(meta left)] 'bufhist-prev)
    (define-key map [(meta right)] 'bufhist-next)
    (define-key map [(meta up)] 'bufhist-first)
    (define-key map [(meta down)] 'bufhist-last)
    (define-key map [(meta c)] 'bufhist-clear)
    (define-key map [(meta d)] 'bufhist-delete)
    map)
  "Keymap for `bufhist-minor-mode'.")

;;;###autoload
(define-minor-mode bufhist-mode
  "Minor mode retaining an in-memory history of the buffer contents.

Commands:\\<bufhist-minor-mode-map>
\\[bufhist-prev]    bufhist-prev    go back in history
\\[bufhist-next]    bufhist-next    go forward in history
\\[bufhist-first]   bufhist-first   go to first item in history
\\[bufhist-last]    bufhist-last    go to last (current) item in history.
\\[bufhist-clear]   bufhist-clear   clear history.
\\[bufhist-delete]  bufhist-clear   delete current item from history."
  nil "" bufhist-minor-mode-map
  :group 'bufhist
  (if bufhist-mode
      (bufhist-init)
    (bufhist-exit)))

(make-variable-buffer-local 'bufhist-ring)
(make-variable-buffer-local 'bufhist-ring-pos)
(make-variable-buffer-local 'bufhist-lastswitch-modified-tick)
(make-variable-buffer-local 'bufhist-read-only-history)
(make-variable-buffer-local 'bufhist-top-point)

(defun bufhist-get-buffer-contents ()
  "Return the stored representation of the current buffer contents.
This is as a pair (POINT . CONTENTS)."
  (cons (point)
	(buffer-substring bufhist-top-point (point-max))))

(fset 'bufhist-ordinary-erase-buffer (symbol-function 'erase-buffer))
;(defalias 'bufhist-ordinary-erase-buffer 'erase-buffer)

(defun bufhist-restore-buffer-contents (buf)
  "Restore BUF as the contents of the current buffer."
  (bufhist-ordinary-erase-buffer)
  (bufhist-insert-buttons)
  (insert (cdr buf))
  ;; don't count this as a buffer update
  (setq bufhist-lastswitch-modified-tick (buffer-modified-tick))
  (goto-char (car buf)))

(defun bufhist-checkpoint ()
  "Add buffer contents to the ring history.  No action if not in bufhist mode."
  (interactive)
  (if bufhist-mode ;; safety
      (ring-insert bufhist-ring (bufhist-get-buffer-contents))))

;; Unfortunately, erase-buffer doesn't call before-change-functions.
;; We could provide advice for erase-buffer, but instead make this part of API.
(defun bufhist-erase-buffer ()
  "Erase buffer contents, maybe running bufhist-before-change-function first."
  (if (and
       bufhist-mode
       (memq 'bufhist-before-change-function before-change-functions))
      (let ((before-change-functions nil)
	    (after-change-functions nil))
	(bufhist-before-change-function)))
  (erase-buffer)
  (bufhist-insert-buttons))

(defun bufhist-checkpoint-and-erase ()
  "Add buffer contents to history then erase. Only erase if not in bufhist mode"
  (interactive)
  (bufhist-checkpoint)
  (bufhist-erase-buffer))

(defun bufhist-switch-to-index (n &optional nosave browsing)
  "Switch to position N in buffer history, maybe updating history.
If optional NOSAVE is non-nil, do not try to save current contents."
  (unless (equal n bufhist-ring-pos)
    ;; we're moving to different position
    (let ((tick (buffer-modified-tick)))
      ;; Save changes back to history for most recent contents or for
      ;; older contents if we have read-write history
      (unless (or nosave
		  (and bufhist-read-only-history (not (eq bufhist-ring-pos 0)))
		  (equal tick bufhist-lastswitch-modified-tick))
	;; If we're browsing away from position 0, checkpoint instead
	;; of updating.
	;; NB: logic here should ideally keep flag to say whether
	;; changes are "during" a browse or not.  This is going
	;; to result in too many checkpoints if we have manual
	;; editing.
	(if (and browsing (eq bufhist-ring-pos 0))
	    ;(progn
	    (bufhist-checkpoint)
	  ; (setq n (1+ n)))
	  ;; Otherwise update in-position
	  (bufhist-ring-update bufhist-ring bufhist-ring-pos
			       (bufhist-get-buffer-contents))))
      (setq bufhist-lastswitch-modified-tick tick)
      (let ((before-change-functions nil)
	    (buffer-read-only nil))
	(bufhist-restore-buffer-contents (ring-ref bufhist-ring n)))
      (if bufhist-read-only-history
	  (setq buffer-read-only
		(if (eq n 0) bufhist-normal-read-only t)))
      (setq bufhist-ring-pos n)
      (force-mode-line-update)
      (if browsing
	  (message "History position %d of %d in %s"
		   (- (ring-length bufhist-ring) n)
		   (ring-length bufhist-ring)
		   (buffer-name))))))

(defun bufhist-first ()
  "Switch to most oldest buffer contents."
  (interactive)
  (bufhist-switch-to-index (1- (ring-length bufhist-ring)) nil 'browsing))

(defun bufhist-last ()
  "Switch to last (most recent; current) buffer contents."
  (interactive)
  (bufhist-switch-to-index 0 nil 'browsing))

(defun bufhist-prev (&optional n)
  "Browse backward in the history of buffer contents."
  (interactive "p")
  (bufhist-switch-to-index
   (mod (+ bufhist-ring-pos (or n 1))
	(ring-length bufhist-ring))
   nil 'browsing))

(defun bufhist-next (&optional n)
  "Browse forward in the history of buffer contents."
  (interactive "p")
  (bufhist-prev (- (or n 1))))

(defun bufhist-delete ()
  "Delete the current item in the buffer history."
  (interactive)
  (message "History item deleted from buffer %s." (buffer-name))
  (unless (eq 0 bufhist-ring-pos)
    (ring-remove bufhist-ring bufhist-ring-pos)
    (bufhist-switch-to-index (1- bufhist-ring-pos) 'nosave)))

;; FIXME: glitch here: we get duplicated first item after clear.
;; Bit like on startup: we always get empty buffer/current contents
;; twice.  Reason is because of invariant of non-empty ring;
;; when we checkpoint we always add to ring.
(defun bufhist-clear ()
  "Clear history."
  (interactive)
  (message "Buffer history in %s cleared." (buffer-name))
  (bufhist-switch-to-index 0 'nosave)
  (setq bufhist-ring (make-ring (ring-size bufhist-ring)))
  (setq bufhist-ring-pos 0)
  (bufhist-checkpoint)
  (setq bufhist-lastswitch-modified-tick (buffer-modified-tick))
  (force-mode-line-update))


;; Setup functions

;;;###autoload
(defun bufhist-init (&optional readwrite ringsize)
  "Initialise a ring history for the current buffer.
The history will be read-only unless READWRITE is non-nil.
For read-only histories, edits to the buffer switch to the latest version.
The size defaults to `bufhist-ring-size'."
  (interactive)
  (setq bufhist-ring (make-ring (or ringsize bufhist-ring-size)))
  (setq bufhist-normal-read-only buffer-read-only)
  (setq bufhist-read-only-history (not readwrite))
  (setq bufhist-ring-pos 0)
  (setq bufhist-saved-mode-line-format mode-line-format)
  (save-excursion
    (goto-char (point-min))
    (bufhist-insert-buttons))
  (bufhist-checkpoint)
  (setq mode-line-format
	(cons '(bufhist-mode
		(:eval (bufhist-mode-line-format-entry)))
	      ;; surely it's always a list, but in case not
	      (if (listp mode-line-format)
		  mode-line-format
		(list mode-line-format))))
  (force-mode-line-update)
  (make-local-variable 'before-change-functions)
  (bufhist-set-readwrite readwrite))


;;;###autoload
(defun bufhist-exit ()
  "Stop keeping ring history for current buffer."
  (interactive)
  (bufhist-switch-to-index 0)
  (setq bufhist-ring-pos nil)
  (bufhist-set-readwrite t)
  (setq mode-line-format bufhist-saved-mode-line-format)
  (force-mode-line-update))


(defun bufhist-set-readwrite (readwrite)
  "Set `before-change-functions' for read-only history."
  (if readwrite
      ;; edit directly
      (progn
	(setq before-change-functions
	      (remq 'bufhist-before-change-function before-change-functions)))
;	    (ad-disable-advice 'erase-buffer 'before 'bufhist-last-advice)))
    ;; readonly history: switch to latest contents
    (setq before-change-functions
	  (cons 'bufhist-before-change-function before-change-functions))))
;	    (ad-enable-advice 'erase-buffer 'before 'bufhist-last-advice))))

;; Restore the latest buffer contents before changes from elsewhere.

(defun bufhist-before-change-function (&rest args)
  "Restore the most recent contents of the buffer before changes."
  (bufhist-switch-to-index 0))

;; Unfortunately, erase-buffer does not call before-change-function
;      (defadvice erase-buffer (before bufhist-last-advice activate)
;	(if (and bufhist-mode bufhist-read-only-history)
;	    (bufhist-last)))
;      (ad-activate-on 'erase-buffer)))

;;;
;;; Buttons
;;;

(define-button-type 'bufhist-next
  'follow-link t
  'help-echo "Next"
  'action #'bufhist-next)
(define-button-type 'bufhist-prev
  'follow-link t
  'help-echo "Previous"
  'action #'bufhist-prev)

;; Little bit tricky: inserts by clients start at (point-min) which
;; is going to insert above these buttons
(defun bufhist-insert-buttons ()
  (when bufhist-mode
    (let ((inhibit-read-only t))
      (save-excursion
	(goto-char (point-min))
	(insert-text-button " < " :type 'bufhist-prev)
	(insert " ")
	(insert-text-button " > " :type 'bufhist-next)
	(insert "\n\n")
	(setq bufhist-top-point (point))))))

(provide 'bufhist)
