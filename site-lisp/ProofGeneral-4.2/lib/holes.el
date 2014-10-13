;;; holes.el --- a little piece of elisp to define holes in your buffer
;;
;; Copyright (C) 2001 Pierre Courtieu
;;
;; holes.el,v 12.2 2012/09/19 13:34:47 pier Exp
;;
;; This file uses spans, an interface for extent (XEmacs) and overlays
;; (emacs), by Healfdene Goguen for the proofgeneral mode.
;;
;; Credits also to Stefan Monnier for great help in making this file
;; cleaner.
;;
;; Further cleanups by David Aspinall.
;;
;; This software is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public
;; License version 2, as published by the Free Software Foundation.
;;
;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
;;
;; See the GNU General Public License version 2 for more details
;; (enclosed in the file GPL).
;;
;; See documentation in variable holes-short-doc.
;;

;;; Commentary:
;;
;; See documentation of `holes-mode'.


(eval-when-compile 
  (require 'span))
(require 'cl)

;;; Code:

;;;
;;; initialization
;;;

(defvar holes-default-hole 
  (let ((ol (make-overlay 0 0)))
    (delete-overlay ol) ol)
  "An empty detached hole used as the default hole.
You should not use this variable.")

(defvar holes-active-hole holes-default-hole
  "The current active hole.
There can be only one active hole at a time,
and this is this one.  This is not buffer local.")


;;;
;;; Customizable
;;;

(defgroup holes nil
  "Customization for Holes minor mode."
  :prefix "holes-"
  :group 'editing)

(defcustom holes-empty-hole-string "#"
  "String to be inserted for empty hole (don't put an empty string)."
  :type 'string
  :group 'holes)

(defcustom holes-empty-hole-regexp "#\\|@{\\([^{}]*\\)}"
  "Regexp denoting a hole in abbrevs.
Subgroup 1 is treated specially: if it matches, it is assumed that
everything before it and after it in the regexp matches delimiters
which should be removed when making the text into a hole."
  :type 'regexp
  :group 'holes)


;(defcustom holes-search-limit 1000
;  "Number of chars to look forward when looking for the next hole, unused for now.") 
;unused for the moment

;; The following is customizable by a command of the form:
;;for dark background
;;(custom-set-faces
;; '(holes-active-hole-face
;;   ((((type x) (class color) (background light))
;;     (:background "paleVioletRed")))
;;   )
;; )

(defface active-hole-face
  '((((class grayscale) (background light)) :background "dimgrey")
    (((class grayscale) (background dark))  :background "LightGray")
    (((class color) (background dark))
     :background "darkred" :foreground "white")
    (((class color) (background light))
     :background "paleVioletRed" :foreground "black"))
  "Font Lock face used to highlight the active hole."
  :group 'holes)

(defface inactive-hole-face
  '((((class grayscale) (background light)) :background "lightgrey")
    (((class grayscale) (background dark))  :background "Grey")
    (((class color) (background dark))
     :background "mediumblue" :foreground "white")
    (((class color) (background light))
     :background "lightsteelblue" :foreground "black"))
  "Font Lock  face used to highlight the active hole."
  :group 'holes)

;;;
;;; Keymaps
;;;

(defvar hole-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(mouse-1)] 'holes-mouse-set-active-hole)
    (define-key map [(mouse-3)] 'holes-mouse-destroy-hole)
    (define-key map [(mouse-2)] 'holes-mouse-forget-hole)
    map)
  "Keymap to use on the holes's overlays.
This keymap is used only when point is on a hole.  
See `holes-mode-map' for the keymap of `holes-mode'.")

(defvar holes-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(control c) (h)] 'holes-set-make-active-hole)
    (define-key map [(control c) (control y)] 'holes-replace-update-active-hole)
    (define-key map [(control meta down-mouse-1)] 
      'holes-mouse-set-make-active-hole)
    (define-key map [(control meta shift down-mouse-1)] 
      'holes-mouse-replace-active-hole)
    (define-key map [(control c) (control j)] 
      'holes-set-point-next-hole-destroy)
    map)
  "Keymap of `holes-mode'.

This one is active whenever we are on a buffer where `holes-mode' is active.

This is not the keymap used on holes's overlay (see `hole-map' instead).")

(easy-menu-define nil (list holes-mode-map)
  "Menu used in Holes minor mode."
  '("Holes"
     ;; da: I tidied this menu a bit.  I personally think this "trick"
     ;; of inserting strings to add documentation looks like a real
     ;; mess in menus ... I've removed it for the three below since
     ;; the docs below appear in popup in messages anyway.
     ;;
     ;; "Make a hole active   click on it"
     ;; "Disable a hole   click on it (button 2)"
     ;; "Destroy a hole   click on it (button 3)"
     ["Make Hole At Point"  holes-set-make-active-hole t]
     ["Make Selection A Hole"  holes-set-make-active-hole t]
     ["Replace Active Hole By Selection"  holes-replace-update-active-hole t]
     ["Jump To Active Hole"  holes-set-point-next-hole-destroy t]
     ["Forget All Holes"  holes-clear-all-buffer-holes t]
     ;; look a bit better at the bottom
     "---"
     ["About Holes" holes-show-doc t]
     "Hint: make hole with mouse: C-M-select"
     "Hint: replace hole with mouse: C-M-Shift-select"
     ))



;;;
;;; Utility functions
;;;

(defun holes-region-beginning-or-nil ()
  "Return the beginning of the acitve region, or nil."
  (and mark-active (region-beginning)))

(defun holes-region-end-or-nil ()
  "Return the end of the acitve region, or nil."
  (and mark-active (region-end)))

(defun holes-copy-active-region ()
  "Copy and retuurn the active region."
  (assert mark-active nil "the region is not active now.")
  (copy-region-as-kill (region-beginning) (region-end))
  (car kill-ring))

(defun holes-is-hole-p (span)
  "Non-nil if SPAN is a HOLE."
  (span-property span 'hole))

(defun holes-hole-start-position (hole)
  "Return start position of HOLE."
  (assert (holes-is-hole-p hole) t 
	  "holes-hole-start-position: %s is not a hole")
  (span-start hole))

(defun holes-hole-end-position (hole)
  "Return end position of HOLE."
  (assert (holes-is-hole-p hole) t "holes-hole-end-position: %s is not a hole")
  (span-end hole))

(defun holes-hole-buffer (hole)
  "Return the buffer of HOLE."
  "Internal."
  (assert (holes-is-hole-p hole) t "holes-hole-buffer: %s is not a hole")
  (span-buffer hole))

(defun holes-hole-at (&optional pos)
  "Return the hole (a span) at POS in current buffer.
If pos is not in a hole raises an error."
  (span-at (or pos (point)) 'hole))

(defun holes-active-hole-exist-p ()
  "Return t if the active hole exists and is not empty (ie detached).
Use this to know if the active hole is set and usable (don't use the
active-hole-marker variable)."
  (not (span-detached-p holes-active-hole)))


(defun holes-active-hole-start-position ()
  "Return the position of the start of the active hole.
See `active-hole-buffer' to get its buffer.  Returns an error if
active hole doesn't exist (the marker is set to nothing)."
  (assert (holes-active-hole-exist-p) t
	  "holes-active-hole-start-position: no active hole")
  (holes-hole-start-position holes-active-hole))

(defun holes-active-hole-end-position ()
  "Return the position of the start of the active hole.
See `active-hole-buffer' to get its buffer.  Returns an error if
active hole doesn't exist (the marker is set to nothing)."
  (assert (holes-active-hole-exist-p) t
	  "holes-active-hole-end-position: no active hole")
  (holes-hole-end-position holes-active-hole))


(defun holes-active-hole-buffer ()
  "Return the buffer containing the active hole.
Raise an error if the active hole is not set.  Don't care if the
active hole is empty."
  (assert (holes-active-hole-exist-p) t
	  "holes-active-hole-buffer: no active hole")
  (holes-hole-buffer holes-active-hole))

(defun holes-goto-active-hole ()
  "Set point to active hole.
Raises an error if active-hole is not set."
  (interactive)
  (assert (holes-active-hole-exist-p) t
	  "holes-goto-active-hole: no active hole")
  (goto-char (holes-active-hole-start-position)))


(defun holes-highlight-hole-as-active (hole)
  "Highlight a HOLE with the `active-hole-face'.
DON'T USE this as it would break synchronization (non active hole
highlighted)."
  (assert (holes-is-hole-p hole) t
	  "holes-highlight-hole-as-active: %s is not a hole")
  (set-span-face hole 'active-hole-face))

(defun holes-highlight-hole (hole)
  "Highlight a HOLE with the not active face.
DON'T USE this as it would break synchronization (active hole non
highlighted)."
  (assert (holes-is-hole-p hole) t
	  "holes-highlight-hole: %s is not a hole")
  (set-span-face hole 'inactive-hole-face))

(defun holes-disable-active-hole ()
  "Disable the active hole.
The goal remains but is not the active one anymore.  Does nothing if
the active hole is already disable."
  (if (not (holes-active-hole-exist-p))
      ()
    ;; HACK: normal hole color, this way undo will show this hole
    ;; normally and not as active hole.  Ideally, undo should restore
    ;; the active hole, but it doesn't, so we put the 'not active'
    ;; color.
    (holes-highlight-hole holes-active-hole)
    (setq holes-active-hole holes-default-hole)))

(defun holes-set-active-hole (hole)
  "Set active hole to HOLE.
Error if HOLE is not a hole."
  (assert (holes-is-hole-p hole) t
	  "holes-set-active-hole: %s is not a hole")
  (if (holes-active-hole-exist-p) 
      (holes-highlight-hole holes-active-hole))
  (setq holes-active-hole hole)
  (holes-highlight-hole-as-active holes-active-hole))

(defun holes-is-in-hole-p (&optional pos)
  "Return non-nil if POS (default: point) is in a hole, nil otherwise."
  (holes-hole-at pos))

(defun holes-make-hole (start end)
  "Make and return an (span) hole from START to END."
  (let ((ext (span-make start end)))
    (set-span-properties
     ext `(hole t
	   mouse-face highlight
	   priority 100 ;; what should I put here? I want big priority
	   face secondary-selection
	   start-open nil
	   end-open t
	   duplicable t
	   evaporate t  ;; really disappear if empty
	   ;; pointer frame-icon-glyph
	   keymap ,hole-map
	   help-echo "this is a \"hole\", button 2 to forget, button 3 to destroy, button 1 to make active"
	   'balloon-help "this is a \"hole\", button 2 to forget, button 3 to destroy, button 1 to make active"))
    ext))

(defun holes-make-hole-at (&optional start end)
  "Make a hole from START to END.
If no arg default hole after point.  If only one arg: error.  Return
the span."
  (interactive)
  (let* ((rstart (or start (holes-region-beginning-or-nil) (point)))
	 (rend (or end (holes-region-end-or-nil) (point))))
    (if (eq rstart rend)
	(progn
	  (goto-char rstart)
	  (insert holes-empty-hole-string)
	  (setq rend (point))))
    (holes-make-hole rstart rend)))

(defun holes-clear-hole (hole)
  "Clear the HOLE."
  (assert (holes-is-hole-p hole) t
	  "holes-clear-hole: %s is not a hole")
  (if (and (holes-active-hole-exist-p) 
	   (eq holes-active-hole hole))
      (holes-disable-active-hole))
  (span-delete hole))

(defun holes-clear-hole-at (&optional pos)
  "Clear hole at POS (default=point)."
  (interactive)
  (if (not (holes-is-in-hole-p (or pos (point))))
      (error "Holes-clear-hole-at: no hole here"))
  (holes-clear-hole (holes-hole-at (or pos (point)))))


(defun holes-map-holes (function &optional object from to)
  "Map function FUNCTION across holes."
  (fold-spans function object from to nil nil 'hole))

(defun holes-clear-all-buffer-holes (&optional start end)
  "Clear all holes leaving their contents.
Operate betwenn START and END if non nil."
  (interactive)
  (holes-disable-active-hole)
  (span-mapcar-spans
   'holes-clear-hole (or start (point-min)) (or end (point-max)) 
   'hole))

;; limit ?
(defun holes-next (pos buffer)
  "Return the first hole after POS in BUFFER.
Or after the hole at pos if there is one (default pos=point).  If no
hole found, return nil."
  (holes-map-holes 
   (lambda (h x) (and (holes-is-hole-p h) h)) buffer pos))

(defun holes-next-after-active-hole ()
  "Internal."
  (assert (holes-active-hole-exist-p) t
	  "next-active-hole: no active hole")
  (holes-next (holes-active-hole-end-position)
	      (holes-active-hole-buffer)))

(defun holes-set-active-hole-next (&optional buffer pos)
  "Set the active hole in BUFFER to the first hole after POS.
Default pos = point and buffer = current."
  (interactive)
  (let ((nxthole (holes-next (or pos (point))
			     (or buffer (current-buffer)))))
    (if nxthole
	(holes-set-active-hole nxthole)
      (holes-disable-active-hole))))

;;;(defun holes-set-active-hole-next-after-active ()
;;  "sets the active hole to the first hole after active
;;  hole.";;;;

;;;  (interactive)
;;  (holes-next-after-active-hole)
;;)


(defun holes-replace-segment (start end str &optional buffer)
  "Erase chars between START and END, and replace them with STR."
  (with-current-buffer (or buffer (current-buffer))
    (goto-char end)
    ;; Insert before deleting, so the markers at `start' and `end'
    ;; don't get mixed up together.
    (insert str)
    (delete-region start end)))

(defun holes-replace (str &optional thehole)
  "Replace the current hole by STR, replace THEHOLE instead if given.
Do not use this, it breaks the right colorization of the active
goal(FIXME?).  Use `replace-active-hole' instead."
  (if (and (not thehole)
	   (not (holes-active-hole-exist-p)))
      (error "No hole to fill")
    ;; defensive: replacing the hole should make it detached and
    ;; therefore inexistent.  other reason: this is a hack: unhighlight
    ;; so that undo wont show it highlighted)
    (if (and (holes-active-hole-exist-p)
	     thehole
	     (eq holes-active-hole thehole))
	(holes-disable-active-hole)
      )
    (let ((exthole (or thehole holes-active-hole)))
      (holes-replace-segment (holes-hole-start-position exthole)
			     (holes-hole-end-position exthole)
			     (or str (car kill-ring)) ;kill ring?
			     (span-buffer exthole)
			     )
      (span-detach exthole) ;; this seems necessary for span overlays,
      ;; where the buffer attached to the span is not removed
      ;; automatically by the fact that the span is removed from the
      ;; buffer (holes-replace-segment should perhaps take care of
      ;; that)
      )))

(defun holes-replace-active-hole (&optional str)
  "Replace the active hole by STR, if no str is given, then put the selection instead."
  (if (not (holes-active-hole-exist-p)) nil
    (holes-replace
     (or str (current-kill 0) (error "Nothing to put in hole"))
     holes-active-hole)))

(defun holes-replace-update-active-hole (&optional str)
  "Replace the active hole by STR.
Like `holes-replace-active-hole', but then sets the active hole to the
following hole if it exists."
  (interactive)
  (assert (holes-active-hole-exist-p) t
	  "holes-replace-update-active-hole: no active hole")
  (if (holes-active-hole-exist-p)
      (let ((nxthole (holes-next-after-active-hole)))
	(holes-replace-active-hole
	 (or str
	     (and mark-active 
		  (holes-copy-active-region))
	     (current-kill 0) 
	     (error "Nothing to put in hole")))
	(if nxthole (holes-set-active-hole nxthole)
	  (setq holes-active-hole holes-default-hole)))))

(defun holes-delete-update-active-hole ()
  "Deletes the active hole and supresses its content.
Sets `holes-active-hole' to the next hole if it exists."
  (interactive)
  (holes-replace-update-active-hole ""))


;;;###autoload
(defun holes-set-make-active-hole (&optional start end)
  "Make a new hole between START and END or at point, and make it active."

  (interactive)
  (holes-set-active-hole (holes-make-hole-at start end)))


;; mouse stuff, I want to make something close to `mouse-track-insert'
;; of XEmacs, but with modifier ctrl-meta and ctrl-meta-shift

;; Emacs and XEmacs have different ways of dealing with mouse
;; selection, but `mouse-track'(XEmacs) mouse-drag-region(Emacs)
;; have nearly the same meaning for me.  So I define this
;; track-mouse-selection.

(defalias 'holes-track-mouse-selection 'mouse-drag-track)
(defsubst holes-track-mouse-clicks ()
  "See `mouse-track-click-count'"
  (+ mouse-selection-click-count 1))

(defun holes-mouse-replace-active-hole (event)
  "Replace the active hole with one under mouse EVENT."
  (interactive "*e")
  (holes-track-mouse-selection event)
  (save-excursion
    ;;HACK: nothing if one click (but a second is perhaps coming)
    (if (and (eq (holes-track-mouse-clicks) 1)
	     (not mark-active))
	()
      (if (not mark-active)
	  (error "Nothing to put in hole")
	(holes-replace-update-active-hole (current-kill 0))
	(message "hole replaced")))))

(defun holes-destroy-hole (&optional span)
  "Destroy the hole SPAN."
  (interactive)
  (let* ((sp (or span (holes-hole-at (point)) 
		 (error "No hole to destroy"))))
    (save-excursion
      (if (and (holes-active-hole-exist-p)
	       (eq sp holes-active-hole))
	  (holes-disable-active-hole))
      (holes-replace "" sp)
      (span-detach sp))
    (message "hole killed")))


(defsubst holes-hole-at-event (event)
  "Return the hole at EVENT."
  (span-at-event event 'hole))

(defun holes-mouse-destroy-hole (event)
  "Destroy the hole at EVENT."
  (interactive "*e")
  (holes-destroy-hole (holes-hole-at-event event)))

;;;(span-at-event EVENT &optional PROPERTY BEFORE AT-FLAG)
;;comprend pas??
(defun holes-mouse-forget-hole (event)
  "Delete and deactivate the hole at EVENT."
  (interactive "*e")
  (save-excursion
    (let ((ext (holes-hole-at-event event)))
      (if (eq ext holes-active-hole)
	  (holes-disable-active-hole))
      (span-detach ext)))
  (message "hole deleted"))

(defun holes-mouse-set-make-active-hole (event)
  "Make a new hole at EVENT click activate it."
  (interactive "*e")
  (holes-track-mouse-selection event)

  (if (and (eq (holes-track-mouse-clicks) 1)
	   (not mark-active))
      (holes-set-make-active-hole (point) (point))

    (if mark-active
	(holes-set-make-active-hole)
      (let ((ext (holes-hole-at-event event)))
	(if (and ext (holes-is-hole-p ext))
	    (error "Already a hole here")
	  (holes-set-active-hole (holes-make-hole-at)))))))

(defun holes-mouse-set-active-hole (event)
  "Make the hole at EVENT click active."
  (interactive "*e")
  (let ((ext (holes-hole-at-event event)))
    (if (and ext (holes-is-hole-p ext))
	(holes-set-active-hole ext)
      (error "No hole here"))))


(defun holes-set-point-next-hole-destroy ()
  "Moves the point to current active hole (if any and if in current buffer).
Destroy it and makes the next hole active if any."
  (interactive)
  (assert (holes-active-hole-exist-p) nil "no active hole")
  (assert (eq (current-buffer) (holes-active-hole-buffer)) nil
	  "active hole not in this buffer")
  (holes-goto-active-hole)
  (holes-delete-update-active-hole))


;; utilities to be used in conjunction with abbrevs.
;; The idea is to put abbrevs of the form:
;;(define-abbrev-table 'tuareg-mode-abbrev-table
;;      '(
;;	("l" "let # = # in" replace-#-after-abbrev2 0)
;;	)
;;      )
;; where replace-#-after-abbrev2 should be a function which replace the
;; two #'s (two occurences going backward from abbrev expantion point)
;; by holes and leave point at the first # (deleting
;; it).  holes-set-point-next-hole-destroy allow to go to the next hole.

;;following function allow to replace occurrences of a string by a
;;hole.

(defun holes-replace-string-by-holes-backward (limit)
  "Change each occurrence of REGEXP into a hole.
Sets the active hole to the last created hole and unsets it if no hole is
created.  Return the number of holes created."
  (holes-disable-active-hole)
  (let ((n 0))
    (save-excursion
      (while (re-search-backward holes-empty-hole-regexp limit t)
	(incf n)
	(if (not (match-end 1))
	    (holes-make-hole (match-beginning 0) (match-end 0))
	  (holes-make-hole (match-beginning 1) (match-end 1))
	  ;; delete end first to avoid shifting of marks
	  (delete-region (match-end 1) (match-end 0))
	  (delete-region (match-beginning 0) (match-beginning 1)))
	(holes-set-active-hole-next)))
    n))

(defun holes-skeleton-end-hook ()
  "Default hook after a skeleton insertion: put holes at each interesting position."
  ;; Not all versions of skeleton provide `skeleton-positions' and the
  ;; corresponding @ operation :-(
  (unless (boundp 'mmm-inside-insert-by-key) ; pc: this hack is ok for me
    (when (boundp 'skeleton-positions)
      (dolist (pos skeleton-positions)	;; put holes here
	(holes-set-make-active-hole pos pos)))))

(defconst holes-jump-doc
  (concat "Hit \\[holes-set-point-next-hole-destroy] to jump "
	  "to active hole.  C-h v holes-doc to see holes doc.")
  "Shortcut reminder string for jumping to active hole.")



(defun holes-replace-string-by-holes-backward-jump (pos &optional noindent)
  "Put holes between POS and point, backward, indenting.
\"#\" and \"@{..}\" between this positions will become holes."
  (unless noindent (save-excursion (indent-region pos (point) nil)))
  (let ((n (holes-replace-string-by-holes-backward pos)))
    (case n
      (0 nil)				; no hole, stay here.
      (1
       (goto-char pos)
       (holes-set-point-next-hole-destroy)) ; if only one hole, go to it.
      (t
       (goto-char pos)
       (unless (active-minibuffer-window) ; otherwise minibuffer gets hidden
	 (message (substitute-command-keys
		   "\\[holes-set-point-next-hole-destroy] to jump to active hole.  \\[holes-short-doc] to see holes doc.")))))))


;;;###autoload
(define-minor-mode holes-mode 
  "Toggle Holes minor mode.
With arg, turn Outline minor mode on if arg is positive, off otherwise.

The mode `holes-mode' is meant to help program editing.  It is
useful to build complicated expressions by copy pasting several
peices of text from different parts of a buffer (or even from
different buffers).

HOLES

A hole is a piece of (highlighted) text that may be replaced by
another part of text later.  There is no information stored on the
file for holes, so you can save and modify files containing holes with
no harm... You can even insert or delete characters inside holes like
any other characters.

USE

At any time only one particular hole, called \"active\", can be
\"filled\".  Holes can be in several buffers but there is always one or
zero active hole globally.  It is highlighted with a different color.

Functions described below have default shortcuts when `holes-mode' is
on that you can customize.

TO DEFINE A HOLE, two methods:

 o Select a region with keyboard or mouse, then use
   \\[holes-set-make-active-hole].  If the selected region is empty,
   then a hole containing # is created at point.

 o Select text with mouse while pressing ctrl and meta (`C-M-select').
   If the selected region is empty (i.e. if you just click while
   pressing ctrl+meta), then a hole containing # is created.

TO ACTIVATE A HOLE, click on it with the button 1 of your mouse.  The
previous active hole will be deactivated.

TO FORGET A HOLE without deleting its text, click on it with the
button 2 (middle) of your mouse.

TO DESTROY A HOLE and delete its text, click on it with the button 3
of your mouse.

TO FILL A HOLE with a text selection, first make sure it is active,
then two methods:

 o Select text with keyboard or mouse and hit
   \\[holes-replace-update-active-hole]

 o Select text with mouse while pressing ctrl, meta and shift
   (`C-M-S-select').  This is a
   generalization of the `mouse-track-insert' feature of XEmacs.  This
   method allows you to fill different holes faster than with the usual
   copy-paste method.

After replacement the next hole is automatically made active so you
can fill it immediately by hitting again
\\[holes-replace-update-active-hole] or `C-M-S-select'.

TO JUMP TO THE ACTIVE HOLE, just hit
\\[holes-set-point-next-hole-destroy].  You must
be in the buffer containing the active hole.  the point will move to
the active hole, and the active hole will be destroyed so you can type
something to put at its place.  The following hole is automatically
made active, so you can hit \\[holes-set-point-next-hole-destroy]
again.

It is useful in combination with abbreviations.  For example in
`coq-mode' \"fix\" is an abbreviation for Fixpoint # (# : #) {struct #} :
# := #, where each # is a hole. Then hitting
\\[holes-set-point-next-hole-destroy] goes from one hole to the
following and you can fill-in each hole very quickly.

COMBINING HOLES AND SKELETONS

`holes' minor mode is made to work with minor mode `skeleton' minor
mode.

KNOWN BUGS

 o Don't try to make overlapping holes, it doesn't work. (what would
it mean anyway?)

 o Cutting or pasting a hole will not produce new holes, and
undoing on holes cannot make holes re-appear."
  nil " Holes" holes-mode-map
  :group 'holes
  (if holes-mode
      (add-hook 'skeleton-end-hook 'holes-skeleton-end-hook nil t)
    (remove-hook 'skeleton-end-hook 'holes-skeleton-end-hook t)
    (holes-clear-all-buffer-holes)))

;;;###autoload
(defun holes-abbrev-complete ()
  "Complete abbrev by putting holes and indenting.
Moves point at beginning of expanded text.  Put this function as
call-back for your abbrevs, and just expanded \"#\" and \"@{..}\" will
become holes."
  (if holes-mode
      (holes-replace-string-by-holes-backward-jump last-abbrev-location)))


;;;###autoload
(defun holes-insert-and-expand (s)
  "Insert S, expand it and replace #s and @{]s by holes."
  ;; insert the expansion of abbrev s, and replace #s by holes.  It was
  ;; possible to implement it with a simple ((insert s) (expand-abbrev))
  ;; but undo would show the 2 steps, which is bad.
  (let ((pos (point))
	(ins (abbrev-expansion s)))
    (insert (or ins s))
    (setq last-abbrev-location pos)
    (holes-abbrev-complete)))

(provide 'holes)

;;; holes.el ends here
