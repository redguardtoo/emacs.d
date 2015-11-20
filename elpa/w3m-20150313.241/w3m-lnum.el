;;; w3m-lnum.el --- Operations using link numbers

;; Copyright (C) 2004-2014 TSUCHIYA Masatoshi <tsuchiya@namazu.org>

;; Authors: TSUCHIYA Masatoshi <tsuchiya@namazu.org>
;;          Andrey Kotlarski <m00naticus@gmail.com>
;; Keywords: w3m, WWW, hypermedia

;; This file is a part of emacs-w3m.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This file provides a minor mode to enable Conkeror style operations
;; using link numbers.  Mostly point operations are extended beyond
;; current point but there are also new features like `w3m-lnum-goto'
;; for quickly navigating to links, form fields images or buttons;
;; `w3m-lnum-follow' for visiting links, activating form fields,
;; toggling images or pushing buttons and `w3m-lnum-universal' for
;; selecting whatever element and then giving relevant options
;; depending on what is selected.

;;; Usage:

;; Install this file to an appropriate directory, and add this
;; expression to your ~/.emacs-w3m if you want automatically
;; activating this minor mode
;; (w3m-lnum-mode 1)
;; or alternatively this to your .emacs file before loading w3m
;; (add-hook 'w3m-mode-hook 'w3m-lnum-mode)
;; or just use interactive command `w3m-lnum-mode' to toggle mode.

;;; Code:

(require 'w3m)

(defface w3m-lnum
  '((((class color) (min-colors 16) (background light))
     (:foreground "gray60"))
    (((class color) (min-colors 16) (background dark))
     (:foreground "gray50"))
    (t (:foreground "gray")))
  "Face used to highlight link numbers."
  :group 'w3m-face)

(defface w3m-lnum-minibuffer-prompt
  '((((class color) (background light) (type tty))
     (:foreground "blue"))
    (((class color) (background dark)) (:foreground "cyan"))
    (t (:foreground "medium blue")))
  "Face for w3m lnum minibuffer prompt."
  :group 'w3m-face)

(defface w3m-lnum-match
  '((((class color) (background light) (type tty))
     (:background "yellow" :foreground "black"))
    (((class color) (background dark) (type tty))
     (:background "blue" :foreground "white"))
    (((class color) (background light)) (:background "yellow1"))
    (((class color) (background dark)) (:background "RoyalBlue3"))
    (t (:background "gray")))
  "Face used to highlight matches in `w3m-lnum-mode'."
  :group 'w3m-face)

(defcustom w3m-lnum-mode-hook nil
  "Hook run after command `w3m-lnum-mode' initialization."
  :group 'w3m
  :type 'hook)

(defcustom w3m-lnum-quick-browsing 'quick-numbers
  "If non-nil, do aggressive selection.  Possible values are:
`quick-numbers' quick selection only when entering numbers
`quick-filter' ditto only when filtering
`quick-all' always quick selecting"
  :group 'w3m
  :type '(radio (const :format "%v " nil)
		(const :format "%v " quick-numbers)
		(const :format "%v " quick-filter)
		(const :format "%v" quick-all)))

(defcustom w3m-lnum-context-alist
  '(("news.ycombinator.com" . 2) ("reddit.com" . 1))
  "Alist specifying number of additional items to be numbered after \
filtering over an url being matched by the car."
  :group 'w3m
  :type 'alist)

(defvar w3m-lnum-actions-custom-type
  '(repeat (choice :format "%[Value Menu%] %v"
		   (string :tag "Information line")
		   (group :tag "Keycode and Action" :indent 2
			  (character :tag "Key")
			  function
			  (string :tag "Prompt")))))

(defcustom w3m-lnum-actions-general
  '("----  Default   ----"
    (?F (lambda (info) (push-mark (point))
	  (goto-char (cadr info))) "Move to anchor"))
  "Alist specifying keycodes and available actions over selected anchor."
  :group 'w3m
  :type w3m-lnum-actions-custom-type)

(defcustom w3m-lnum-actions-image-alist
  '("----  Image  ----"
    (?t (lambda (info) (goto-char (cadr info))
	  (w3m-toggle-inline-image)) "Goto image and toggle it")
    (?T (lambda (info) (save-excursion (goto-char (cadr info))
				  (w3m-toggle-inline-image)))
	"Toggle")
    (?O (lambda (info) (w3m-external-view (nth 2 info))) "View externally")
    (?S (lambda (info) (w3m-download (nth 2 info))) "Save")
    (?r (lambda (info) (w3m-lnum-remove-overlays) ;some images invoke scrolling
	  (goto-char (cadr info))
	  (w3m-resize-image-interactive (car info))) "Resize"))
  "Alist specifying keycodes and available actions over a selected image."
  :group 'w3m
  :type w3m-lnum-actions-custom-type)

(defcustom w3m-lnum-actions-link-alist
  '("----  Link   ----"
    (?g (lambda (info) (w3m-lnum-visit info)) "Visit")
    (?G (lambda (info) (w3m-lnum-visit info t)) "Visit in new session")
    (?B (lambda (info) (w3m-lnum-visit info :background))
	"Visit in background")
    (?v (lambda (info) (w3m-lnum-visit info nil t)) "Edit and visit")
    (?V (lambda (info) (w3m-lnum-visit info t t))
	"Edit and visit in new session")
    (?& (lambda (info) (w3m-lnum-visit info :background t))
	"Edit url and visit in background")
    (?e (lambda (info) (w3m-edit-url (car info))) "Edit page")
    (?s (lambda (info) (save-excursion
		    (goto-char (cadr info))
		    (w3m-download-this-url))) "Download")
    (?b (lambda (info)
	  (w3m-bookmark-add
	   (car info)
	   (let ((pos (cadr info)))
	     (if (= pos 16)		; 0th anchor selected
		 w3m-current-title
	       (buffer-substring-no-properties
		(previous-single-property-change (1+ pos)
						 'w3m-href-anchor)
		(next-single-property-change pos
					     'w3m-href-anchor))))))
	"Add to bookmarks")
    (?u (lambda (info)
	  (let ((url (car info)))
	    (kill-new url)
	    (w3m-message "%s%s" (let ((im-alt (nth 3 info)))
				  (if (zerop (length im-alt)) ""
				    (concat im-alt ": ")))
			 url)))
	"Copy")
    (?M (lambda (info) (w3m-view-url-with-browse-url (car info)))
	"Open in external browser"))
  "Alist specifying keycodes and available actions over a selected link."
  :group 'w3m
  :type w3m-lnum-actions-custom-type)

(defcustom w3m-lnum-actions-button-alist
  '("---- Button  ----"
    (?p (lambda (info) (push-mark (point))
	  (goto-char (cadr info))
	  (widget-button-press (cadr info) (car info)))
	"Goto button and push it")
    (?P (lambda (info) (widget-button-press (cadr info) (car info)))
	"Push"))
  "Alist specifying keycodes and available actions over a selected button."
  :group 'w3m
  :type w3m-lnum-actions-custom-type)

(defcustom w3m-lnum-actions-form-alist
  '("----  Form   ----"
    (?p (lambda (info) (setq mode-line-format original-mode-line-format)
	  (w3m-lnum-remove-overlays)
	  (push-mark (point))
	  (goto-char (cadr info))
	  (let ((w3m-form-new-session t)
		(w3m-form-download nil))
	    (eval action))) "Goto form and activate it")
    (?P (lambda (info) (w3m-lnum-remove-overlays)
	  (save-excursion
	    (goto-char (cadr info))
	    (let ((w3m-form-new-session nil)
		  (w3m-form-download nil))
	      (eval action)))) "Activate"))
  "Alist specifying keycodes and available actions over a selected form field."
  :group 'w3m
  :type w3m-lnum-actions-custom-type)

(defvar w3m-lnum-mode-map nil
  "Keymap used when command `w3m-lnum-mode' is active.")
(unless w3m-lnum-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "f" 'w3m-lnum-follow)
    (define-key map "F" 'w3m-lnum-goto)
    (define-key map "w" 'w3m-lnum-universal)
    (w3m-substitute-key-definitions
     map w3m-mode-map
     'w3m-view-image 'w3m-lnum-view-image
     'w3m-save-image 'w3m-lnum-save-image
     'w3m-download-this-url 'w3m-lnum-download-this-url
     'w3m-edit-this-url 'w3m-lnum-edit-this-url
     'w3m-toggle-inline-image 'w3m-lnum-toggle-inline-image
     'w3m-print-this-url 'w3m-lnum-print-this-url
     'w3m-view-url-with-browse-url 'w3m-lnum-external-view-this-url
     'w3m-bookmark-add-this-url 'w3m-lnum-bookmark-add-this-url
     'w3m-zoom-in-image 'w3m-lnum-zoom-in-image
     'w3m-zoom-out-image 'w3m-lnum-zoom-out-image)
    (setq w3m-lnum-mode-map map)))

(defvar w3m-lnum-mode nil
  "Non-nil if w3m operations using link numbers are enabled.")
(make-variable-buffer-local 'w3m-lnum-mode)
(unless (assq 'w3m-lnum-mode minor-mode-alist)
  (push (list 'w3m-lnum-mode "[ln]") minor-mode-alist))
(unless (assq 'w3m-lnum-mode minor-mode-map-alist)
  (push (cons 'w3m-lnum-mode w3m-lnum-mode-map)
	minor-mode-map-alist))

(defun w3m-lnum-remove-overlays (&optional start end)
  "Remove numbering and match overlays between START and END points.
If missing, clear the current visible window."
  (let* ((start-pos (window-start))
	 (window-size (- (window-end) start-pos))
	 (start (or start (max (- start-pos window-size)
			       (point-min))))
	 (end (or end (min (+ start-pos (* 2 window-size))
			   (point-max)))))
    (dolist (overlay (overlays-in start end))
      (if (or (overlay-get overlay 'w3m-lnum-overlay)
	      (overlay-get overlay 'w3m-lnum-match))
	  (delete-overlay overlay)))))

;;;###autoload
(defun w3m-lnum-mode (&optional arg)
  "Minor mode to extend point commands by using Conkeror style number selection.
With prefix ARG 0 disable battery included point functions, otherwise
enable them.  With no prefix ARG - toggle."
  (interactive "P")
  (let ((w3m-lnum-status w3m-lnum-mode))
    ;; find current numbering status of w3m buffers
    (or (eq major-mode 'w3m-mode)
	(save-current-buffer
	  (setq w3m-lnum-status
		(catch 'found-w3m
		  (dolist (buf (buffer-list))
		    (set-buffer buf)
		    (if (eq major-mode 'w3m-mode)
			(throw 'found-w3m
			       w3m-lnum-mode)))))))
    (setq arg (not (if arg (zerop arg)
		     w3m-lnum-status)))
    (unless (eq arg w3m-lnum-status)	; if change of mode status
      (if arg
	  (progn (add-hook 'w3m-mode-hook 'w3m-lnum-mode)
		 (run-hooks 'w3m-lnum-mode-hook)
		 (w3m-message "Link numbering keys on"))
	(remove-hook 'w3m-mode-hook 'w3m-lnum-mode)
	(w3m-message "Link numbering keys off"))
      ;; change numbering status of all w3m buffers
      (save-current-buffer
	(dolist (buf (buffer-list))
	  (set-buffer buf)
	  (if (eq major-mode 'w3m-mode)
	      (setq w3m-lnum-mode arg)))))))

(defmacro w3m-lnum-set-overlay (pos index pmax)
  "Set numbering overlay at POS with INDEX and until PMAX."
  `(let ((overlay (make-overlay ,pos (1+ ,pos))))
     (let ((num (format "[%d]" (setq ,index (1+ ,index)))))
       (overlay-put overlay 'before-string num)
       (w3m-static-if (featurep 'xemacs)
	   (set-glyph-face (extent-begin-glyph overlay) 'w3m-lnum)
	 (w3m-add-face-property 0 (length num) 'w3m-lnum num)
	 (overlay-put overlay 'evaporate t)))
     (overlay-put overlay 'w3m-lnum-overlay ,index)
     (let ((hseq (get-char-property ,pos 'w3m-anchor-sequence))
	   (pos2 ,pos))
       (if hseq				; multiline anchors
	   (while (and (setq pos2 (next-single-property-change
				   pos2 'w3m-anchor-sequence))
		       (setq pos2 (text-property-any
				   pos2 ,pmax
				   'w3m-anchor-sequence hseq)))
	     (setq overlay (make-overlay pos2 (1+ pos2)))
	     (overlay-put overlay 'w3m-lnum-overlay ,index))))))

(defun w3m-lnum-set-numbering (&optional next-func reg dont-clear-p)
  "Make overlays that display link numbers.  Return last used index.
NEXT-FUNC is function to iterate numbered elements, if not given,
use `w3m-goto-next-anchor-or-image'.  REG is filter string for anchor text.
DONT-CLEAR-P determines whether previous numbering has to be cleared."
  (setq reg
	(if reg
	    (w3m-replace-regexps-in-string ; escape special characters
	     reg "\\?" "\\\\?" "\\!" "\\\\!" "\\[" "\\\\["
	     "\\*" "\\\\*" "\\+" "\\\\+" "\\." "\\\\." "\\^" "\\\\^"
	     "\\$" "\\\\$")
	  "")
	next-func (or next-func 'w3m-goto-next-anchor-or-image))
  (or dont-clear-p
      (w3m-lnum-remove-overlays))
  (let ((pos (max (1- (window-start)) (point-min)))
	(pmax (min (window-end) (point-max)))
	(index 0)
	(context (or (assoc-default w3m-current-url
				    w3m-lnum-context-alist
				    'w3m-string-match-p)
		     0)))
    (while (and pos
		(setq pos (funcall next-func pos))
		(< pos pmax))
      (let ((str ""))
	(let ((hseq (get-char-property pos 'w3m-anchor-sequence)))
	  (if hseq			; multiline anchors
	      (let ((pos2 (next-single-property-change
			   pos 'w3m-anchor-sequence)))
		(while (and pos2
			    (setq pos2 (text-property-any
					pos2 pmax
					'w3m-anchor-sequence hseq)))
		  (let ((pos3 pos2))
		    (if (setq pos2 (next-single-property-change
				    pos2 'w3m-anchor-sequence))
			(setq str
			      (concat str
				      (buffer-substring-no-properties
				       pos3 pos2)))))))))
	(when (w3m-string-match-p reg
				  (concat
				   (buffer-substring-no-properties
				    pos
				    (next-single-property-change
				     pos
				     (cond ((w3m-anchor-sequence pos)
					    'w3m-anchor-sequence)
					   ((w3m-image pos)
					    'w3m-image))))
				   str))
	  (w3m-lnum-set-overlay pos index pmax)
	  (let ((counter context))
	    (while (and (>= (setq counter (1- counter)) 0)
			(setq pos (funcall next-func pos))
			(< pos pmax))
	      (w3m-lnum-set-overlay pos index pmax))))))
    index))

(defun w3m-lnum-next-filter (type filter pmin pmax)
  "Search next element according to TYPE and FILTER.
Do this in region between points PMIN and PMAX.
If such element is found, return its position.  Nil otherwise."
  (setq filter
	(w3m-replace-regexps-in-string	; escape special characters
	 filter "\\?" "\\\\?" "\\!" "\\\\!" "\\[" "\\\\["
	 "\\*" "\\\\*" "\\+" "\\\\+" "\\." "\\\\." "\\^" "\\\\^"
	 "\\$" "\\\\$"))
  (let ((pos pmin)
	(next-func (cond ((= type 1) 'w3m-goto-next-link)
			 ((= type 2) 'w3m-goto-next-image2)
			 (t 'w3m-goto-next-anchor-or-image))))
    (catch 'found
      (while (and pos (setq pos (funcall next-func pos))
		  (< pos pmax))
	(let ((str ""))
	  (let ((hseq (get-char-property pos 'w3m-anchor-sequence)))
	    (if hseq			; multiline anchors
		(let ((pos2 (next-single-property-change
			     pos 'w3m-anchor-sequence)))
		  (while (and pos2
			      (setq pos2 (text-property-any
					  pos2 pmax
					  'w3m-anchor-sequence hseq)))
		    (let ((pos3 pos2))
		      (if (setq pos2 (next-single-property-change
				      pos2 'w3m-anchor-sequence))
			  (setq str
				(concat str
					(buffer-substring-no-properties
					 pos3 pos2)))))))))
	  (if (w3m-string-match-p filter
				  (concat
				   (buffer-substring-no-properties
				    pos
				    (next-single-property-change
				     pos
				     (cond ((w3m-anchor-sequence pos)
					    'w3m-anchor-sequence)
					   ((w3m-image pos)
					    'w3m-image))))
				   str))
	      (throw 'found pos)))))))

(defun w3m-lnum (arg &optional filter dont-clear-p)
  "Make overlays that display link numbers.  Return last used index.
With ARG 0 clear numbering overlay.  With ARG 1 index only links.
With ARG 2 index only images.  Otherwise index all anchors.
FILTER is filter string for anchor text.
DONT-CLEAR-P determines whether previous numbering has to be cleared."
  (if (zerop arg) (w3m-lnum-remove-overlays)
    (w3m-lnum-set-numbering (cond ((= arg 1) 'w3m-goto-next-link)
				  ((= arg 2) 'w3m-goto-next-image2)
				  (t 'w3m-goto-next-anchor-or-image))
			    filter dont-clear-p)))

(defmacro w3m-lnum-prompt-str (num fun start def-anchor filter
				   &optional show-num)
  "Construct a prompt string for function `w3m-lnum-read-interactive'.
NUM is a number variable for currently to be selected element.
FUN is a function to be called with NUM as argument.
START is a string to start the prompt.
DEF-ANCHOR is info for the default 0 element.
FILTER is current string used for filtering.
SHOW-NUM if specified replaces NUM."
  `(let ((anchor (funcall ,fun ,num))
	 (show-num ,show-num))
     (setq anchor (if anchor (concat " [" anchor "]")
		    (setq ,num 0
			  show-num "")
		    ,def-anchor))
     (concat ,start
	     (or show-num (propertize
			   (number-to-string ,num)
			   'face 'w3m-lnum-minibuffer-prompt))
	     " " ,filter anchor)))

(defmacro w3m-read-event (prompt key)
  "Read event with PROMPT and return keycode.
KEY is what XEmacs gives for event-key."
  (w3m-static-if (featurep 'xemacs)
      `(progn
	 (display-message 'no-log ,prompt)
	 (let ((event (next-command-event)))
	   (if (key-press-event-p event)
	       (or (event-to-character event)
		   (characterp
		    (setq ,key (event-key event)))
		   ,key))))
    `(read-event ,prompt t)))

(eval-when-compile
  (if (fboundp 'redisplay) nil
    (defalias 'redisplay 'ignore)))

(defun w3m-lnum-read-interactive (prompt fun type last-index &optional
					 def-anchor filter def-num)
  "Interactively read a valid integer from minubuffer with PROMPT.
Execute a one argument function FUN with every current valid integer.
TYPE is type of link numbering.  DEF-ANCHOR is initial element to print.
FILTER is the initial aplied filter.
DEF-NUM is the initial selected element, 1 if not given.
Use <return> to submit current selection; <backspace> for correction;
<C-g> or <escape> to quit action;
`<', `>', <space> and <delete> for scrolling page.
Entering 0 may choose default anchor without <return>.
Every other character is appended to a filtering string.
<CTRL>+<DIGIT> is appended to the filtering string as <DIGIT>.
If `w3m-lnum-quick-browse' is non-nil, choose without
<return> on single possible selection.
Return list of selected number and last applied filter."
  (setq def-anchor (if def-anchor (concat " [" def-anchor "]")
		     "")
	prompt (propertize prompt 'face 'w3m-lnum-minibuffer-prompt))
  (let ((filter (or filter ""))
	(auto-num (or (null def-num) (= def-num 0)))
	ch key)
    (let ((num (if auto-num 1 def-num)))
      (catch 'select
	(let ((temp-prompt (w3m-lnum-prompt-str num fun prompt
						def-anchor filter
						(if auto-num ""))))
	  (while (not (memq		; while not return or escape
		       (setq ch (w3m-read-event temp-prompt key))
		       '(return 10 13 ?\n ?\r ?\C-g escape 27 ?\e)))
	    (cond
	     ((memq ch '(backspace 8 127 ?\C-h))
	      (if auto-num
		  (unless (string-equal filter "") ; delete last filter character
		    (setq num 1
			  filter (w3m-substring-no-properties
				  filter 0 (1- (length filter)))
			  last-index (w3m-lnum type filter)
			  temp-prompt
			  (w3m-lnum-prompt-str num fun prompt
					       def-anchor filter "")))
		(setq num (/ num 10))	; delete last digit
		(if (zerop num)
		    (setq num 1
			  auto-num t))
		(setq temp-prompt
		      (w3m-lnum-prompt-str num fun prompt
					   def-anchor filter
					   (if auto-num "")))))
	     ;; scroll options
	     ((memq ch '(32 ?\ ))		; scroll down
	      (w3m-lnum-remove-overlays (point-min) (point-max))
	      (ignore-errors
		(w3m-scroll-up)
		;; scroll-up sets wrongly window-start/end
		(if (and (fboundp 'redisplay)
			 (not (eq (symbol-function 'redisplay) 'ignore)))
		    (redisplay)
		  (sit-for 0)))
	      #1=
	      (setq last-index (w3m-lnum type filter t)
		    num (if (zerop last-index) 0 1)
		    auto-num t
		    temp-prompt (w3m-lnum-prompt-str num fun prompt
						     def-anchor
						     filter "")))
	     ((eq ch 'delete)		; scroll up
	      (w3m-lnum-remove-overlays (point-min) (point-max))
	      (ignore-errors (scroll-down nil))
	      #1#)
	     ((memq ch '(60 ?<)) (w3m-scroll-right nil))
	     ((memq ch '(62 ?>)) (w3m-scroll-left nil))
	     ;; iteration options
	     ((memq ch '(left up))
	      (setq num (if (> num 1) (1- num)
			  last-index)
		    auto-num t
		    temp-prompt
		    (w3m-lnum-prompt-str num fun prompt def-anchor
					 filter "")))
	     ((memq ch '(right down))
	      (setq num (if (< num last-index)
			    (1+ num)
			  1)
		    auto-num t
		    temp-prompt
		    (w3m-lnum-prompt-str num fun prompt def-anchor
					 filter "")))
	     ((and (w3m-static-if (featurep 'xemacs) ; digit
		       (characterp ch)
		     (numberp ch))
		   (< 47 ch) (< ch 58))
	      (if auto-num
		  (if (= ch 48) (throw 'select (setq num 0))
		    (setq num (- ch 48)
			  auto-num nil))
		(setq num (+ (* num 10) ch -48)))
	      (if (> num last-index)
		  (if (zerop (setq num (/ num 10)))
		      (setq num 1
			    auto-num t))
		(and (memq w3m-lnum-quick-browsing
			   '(quick-all quick-numbers))
		     (> (* num 10) last-index)
		     (throw 'select num)))
	      (setq temp-prompt
		    (w3m-lnum-prompt-str num fun prompt def-anchor
					 filter (if auto-num ""))))
	     (t (setq ch (string (w3m-static-if (featurep 'xemacs)
				     (cond
				      ((eq ch t) key)
				      ((= ch ?\^@) ?\ ) ;<ctrl>+SPACE
				      (t ch))
				   (cond
				    ((= ch 67108896) 32) ;<ctrl>+SPACE
				    ((and (< 67108911 ch) ;treat <ctrl>+DIGIT
					  (< ch 67108922))
				     (- ch 67108864)) ; as DIGIT
				    (t ch))))
		      filter (concat filter ch)
		      last-index (w3m-lnum type filter))
		(if (and (= last-index 1)
			 (memq w3m-lnum-quick-browsing
			       '(quick-all quick-filter)))
		    (throw 'select (setq num 1))
		  (when (zerop last-index) ; filter left nothing
		    (let* ((pmax (point-max))
			   (pos (or (w3m-lnum-next-filter ;search below
				     type filter
				     (min (window-end) pmax) pmax)
				    (w3m-lnum-next-filter ;search above
				     type filter
				     (point-min) (window-start)))))
		      (when pos
			(goto-char pos)
			(if (and (fboundp 'redisplay)
				 (not (eq (symbol-function 'redisplay)
					  'ignore)))
			    (redisplay)
			  (sit-for 0))
			(setq last-index (w3m-lnum type filter t))))
		    (if (zerop last-index) ; search found nothing, remove new char
			(setq filter (w3m-substring-no-properties
				      filter 0 (1- (length filter)))
			      last-index (w3m-lnum type filter t))))
		  (setq num 1
			auto-num t
			temp-prompt
			(w3m-lnum-prompt-str num fun prompt def-anchor
					     filter "")))))))
	(if (memq ch '(?\C-g escape 27 ?\e))
	    (keyboard-quit)))
      (list num filter))))

(defmacro w3m-with-lnum (type filter &rest body)
  "Within TYPE anchor numbering with FILTER execute BODY.
Types are: 0 no numbering, 1 links, 2 images, otherwise all anchors.
Then clear numbering overlays.  Within BODY, `last-index' is bound to
the last used index number."
  `(let ((original-mode-line-format mode-line-format)
	 (buffer (current-buffer)))
     (unwind-protect (progn
		       (setq mode-line-format
			     "RET: select | BACKSPACE: correction | \
chars, C-digit, C-SPACE: add chars, digits or space to string \
filter | arrows: move selection | SPACE,DEL,<,>: scroll | \
ESC, C-g: quit")
		       (w3m-force-mode-line-update)
		       (let ((last-index (w3m-lnum ,type ,filter)))
			 ,@body))
       (with-current-buffer buffer
	 (setq mode-line-format original-mode-line-format)
	 (w3m-lnum-remove-overlays (point-min) (point-max))))))

(defun w3m-lnum-highlight-anchor (arg)
  "Highlight specified by ARG number anchor.
Return selected anchor."
  (let (marked-label)
    (dolist (overlay (overlays-in (max (1- (window-start))
				       (point-min))
				  (min (window-end) (point-max))))
      (cond
       ((overlay-get overlay 'w3m-lnum-match)
	(delete-overlay overlay))
       ((eq arg (overlay-get overlay 'w3m-lnum-overlay))
	(let* ((start (overlay-start overlay))
	       (match-overlay
		(make-overlay
		 start
		 (next-single-property-change
		  start
		  (cond ((w3m-anchor-sequence start)
			 'w3m-anchor-sequence)
			((w3m-image start) 'w3m-image)
			(t 'w3m-action))))))
	  (overlay-put match-overlay 'w3m-lnum-match t)
	  (overlay-put match-overlay 'face 'w3m-lnum-match)
	  (or marked-label
	      (setq marked-label
		    (or (w3m-anchor start)
			(w3m-image start)
			(buffer-substring-no-properties
			 start (next-single-property-change
				start 'w3m-action)))))))))
    marked-label))

(defmacro w3m-lnum-get-match-info (condition found-tag)
  "For the first overlay matching CONDITION throw through FOUND-TAG \
anchor info."
  `(dolist (overlay (overlays-in (max (1- (window-start)) (point-min))
				 (min (window-end) (point-max))))
     (if ,condition
	 (let* ((pos (overlay-start overlay))
		(href (w3m-anchor pos)))
	   (throw ,found-tag
		  (if href (list href pos (w3m-image pos)
				 (w3m-image-alt pos))
		    (list (w3m-action pos) pos (w3m-image pos)
			  (w3m-image-alt pos))))))))

(defun w3m-lnum-get-anchor-info (&optional num)
  "Get info (url/action position image image-alt) of anchor numbered as NUM.
If NUM is not specified, use currently highlighted anchor."
  (catch 'found
    (if num (w3m-lnum-get-match-info
	     (eq num (overlay-get overlay 'w3m-lnum-overlay))
	     'found)
      (w3m-lnum-get-match-info (overlay-get overlay 'w3m-lnum-match)
			       'found))))

(defun w3m-lnum-get-action (&optional prompt type)
  "Turn on link numbers and return list of url or action, position \
and image url if such of PROMPT selected anchor.
TYPE sets types of anchors to be numbered: 0 - no numbering,
1 - only links, 2 - only images, otherwise - all anchors.
Highlight every intermediate result anchor.
Input 0 corresponds to location url."
  (setq type (or type 3))
  (w3m-with-lnum
   type ""
   (if (and (= type 2)			; image lack of selection
	    (= last-index 1))
       (if (y-or-n-p "Single image found.  Select it? ")
	   (w3m-lnum-get-anchor-info 1))
     (if (and (zerop last-index)
	      (not (= type 2)))
	 (if (y-or-n-p (concat "No items found. Select default? ["
			       w3m-current-url "] "))
	     (list w3m-current-url 16 nil nil)
	   (keyboard-quit))
       (let ((num (car (w3m-lnum-read-interactive
			(or prompt "Anchor number: ")
			'w3m-lnum-highlight-anchor
			type last-index (unless (= type 2)
					  w3m-current-url)))))
	 (if (and (zerop num)
		  (not (= type 2)))
	     (list w3m-current-url 16 nil nil)
	   (w3m-lnum-get-anchor-info num)))))))

;;;###autoload
(defun w3m-lnum-goto ()
  "Turn on link, image and form numbers and ask for one to go to.
0 corresponds to location url."
  (interactive)
  (let ((info (w3m-lnum-get-action)))
    (if info (progn (push-mark (point))
		    (goto-char (cadr info)))
      (w3m-message "No valid anchor selected"))))

(defun w3m-lnum-visit (info &optional new-session edit)
  "Visit URL determined with selection INFO.
If NEW-SESSION, visit in new buffer, optionally in `:background'.
If EDIT, edit URL before visiting."
  (cond ((eq new-session :background)
	 (save-window-excursion
	   (w3m-goto-url-new-session
	    (if edit (read-string "Visit url in new session: "
				  (car info))
	      (car info)))))
	(new-session
	 (w3m-goto-url-new-session
	  (if edit (read-string "Visit url in new session: "
				(car info))
	    (car info))))
	(t (push-mark (point))
	   (goto-char (cadr info))
	   (w3m-history-store-position)
	   (w3m-goto-url
	    (if edit (read-string "Visit url: "
				  (car info))
	      (car info))))))

;;;###autoload
(defun w3m-lnum-follow (arg)
  "Turn on link numbers, ask for one and execute appropriate action on it.
If link - visit it, when button - press, when input - activate it,
If image - toggle it.
With prefix ARG visit link in new session or don't move over
field/button/image on activation/push/toggle.
With `-' ARG, for link image - go to it and toggle it, if link,
visit in background.  With -4 ARG, for link image - toggle it.
With double prefix ARG, prompt for url to visit.
With triple prefix ARG, prompt for url to visit in new session."
  (interactive "p")
  (let ((info (w3m-lnum-get-action
	       (concat "Follow " (if (> arg 1) "in new session ")
		       "(select anchor): "))))
    (if info
	(let ((action (car info)))
	  (cond ((null action)		; image
		 (if (> arg 1) (save-excursion
				 (goto-char (cadr info))
				 (w3m-toggle-inline-image))
		   (goto-char (cadr info))
		   (w3m-toggle-inline-image)))
		((stringp action)	; url
		 (cond ((or (= arg 1) (and (= arg -1) ; visit
					   (not (nth 2 info))))
			(w3m-lnum-visit info (if (= arg -1)
						 :background)))
		       ((= arg -1)	; goto image and toggle it
			(goto-char (cadr info))
			(w3m-toggle-inline-image))
		       ((= arg 4)	; new session
			(w3m-lnum-visit info t))
		       ((and (= arg -4) (nth 2 info))
			(save-excursion ; toggle image
			  (goto-char (cadr info))
			  (w3m-toggle-inline-image)))
		       ((= arg 16)	; prompt for url
			(w3m-lnum-visit info nil t))
		       ((= arg 64)    ; prompt for url for new session
			(w3m-lnum-visit info t t))
		       ((= arg -4) ; prompt for url and open in background
			(w3m-lnum-visit info :background t))))
		((eq (car action) 'w3m-form-submit) ; button
		 (when (= arg 1)
		   (push-mark (point))
		   (goto-char (cadr info)))
		 (widget-button-press (cadr info) action))
		(t (if (> arg 1) (save-excursion ; form field
				   (goto-char (cadr info))
				   (let ((w3m-form-new-session nil)
					 (w3m-form-download nil))
				     (eval action)))
		     (push-mark (point))
		     (goto-char (cadr info))
		     (let ((w3m-form-new-session t)
			   (w3m-form-download nil))
		       (eval action))))))
      (w3m-message "No valid anchor selected"))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; universal

(defmacro w3m-lnum-make-action (text cmd)
  "Return a TEXT propertized as a link that invokes CMD when clicked."
  `(propertize ,text 'action ,cmd 'mouse-face 'highlight))

(defun w3m-lnum-universal-dispatch (info label action-alist)
  "Print available options for determined by INFO element.
LABEL is identifier to be echoed in the minibuffer.
ACTION-ALIST is an alist of available options where each element
is in the following format: (keycode function docstring).
Function has to take one argument that is selection info."
  (let ((action-alist (append action-alist w3m-lnum-actions-general))
	char key default-option selection-made)
    (save-window-excursion
      (let ((original-mode-line-format mode-line-format))
	(unwind-protect
	    (let ((selection-buffer (get-buffer-create
				     "*Emacs-w3m action selection*")))
	      (set-buffer selection-buffer)
	      (setq mode-line-format "RET, left click: select | \
<down>,TAB/<up>,BACKTAB: move to next/previous action"
		    buffer-read-only nil)
	      (w3m-force-mode-line-update)
	      (mapc (lambda (option)
		      (if (consp option)
			  (insert
			   (w3m-lnum-make-action
			    (concat "[    " (char-to-string
					     (car option)) "    ] "
					     (nth 2 option))
			    (cadr option))
			   "\n")
			(insert option "\n")))
		    action-alist)
	      (insert (w3m-lnum-make-action
		       "[Backspace] Back to selection"
		       (lambda (info) 'restart-selection))
		      "\n")
	      (insert (w3m-lnum-make-action "[   ESC   ] Quit"
					    (lambda (info) nil)))
	      (setq buffer-read-only t)
	      (goto-char (point-min))
	      (while (not (get-text-property (point) 'action))
		(forward-line))		; go over first action
	      (pop-to-buffer selection-buffer)
	      (setq char (w3m-read-event
			  (concat
			   (propertize
			    "Select action: " 'face
			    'w3m-lnum-minibuffer-prompt)
			   "[" label "]")
			  key))
	      (while (and (not selection-made)
			  (or (consp char)
			      (memq char '(up down tab backtab
					      return 10 13 ?\n ?\r))))
		(if (consp char)		; mouse click?!
		    (progn (mouse-set-point char)	; move to mouse point
			   (let ((action (get-text-property (point)
							    'action)))
			     (if action (setq selection-made action))))
		  (cond ((memq char '(up backtab)) ; move to previous action
			 (when (/= (forward-line -1) 0)
			   (goto-char (point-max)) ; ...or start from bottom
			   (beginning-of-line))
			 (while (and (not (get-text-property (point) 'action))
				     (= (forward-line -1) 0))))
			((memq char '(down tab)) ; move to next action
			 (forward-line)
			 (if (= (point) (point-max))
			     (goto-char (point-min))) ; or move to top
			 (while (and (not (get-text-property (point) 'action))
				     (/= (point) (point-max)))
			   (forward-line)))
			((memq char '(return 10 13 ?\n ?\r)) ; <return> select
			 (let ((action (get-text-property (point)
							  'action)))
			   (if action (setq selection-made action))))))
		(unless selection-made
		  (setq char (w3m-read-event
			      (concat (propertize
				       "Select action: " 'face
				       'w3m-lnum-minibuffer-prompt)
				      "[" label "]")
			      key)))))
	  (setq mode-line-format original-mode-line-format)
	  (kill-buffer (current-buffer)))))
    (unless (memq char '(?\C-g escape 27 ?\e))
      (cond (selection-made (funcall selection-made info))
	    ((memq char '(backspace 8 ?\C-h)) ; require new selection
	     'restart-selection)
	    (t (let ((dispatch (assoc-default char action-alist 'eq)))
		 (if dispatch (funcall (car dispatch) info)
		   (w3m-message "Invalid selection"))))))))

;;;###autoload
(defun w3m-lnum-universal ()
  "Turn on link numbers, ask for one and offer actions over it \
depending on selection type.
Actions may be selected either by hitting corresponding key,
pressing <return> over the action line or left clicking."
  (interactive)
  (let ((filter "")
	(label w3m-current-url)
	num)
    (while
	(eq 'restart-selection
	    (w3m-with-lnum
	     3 filter
	     (let ((info
		    (if (zerop last-index)
			(list w3m-current-url 16 nil nil)
		      (let ((selection (w3m-lnum-read-interactive
					"Anchor number: "
					'w3m-lnum-highlight-anchor
					3 last-index w3m-current-url
					filter
					(if (eq num 1) nil num))))
			(setq num (car selection)
			      filter (cadr selection))
			(if (zerop num)
			    (progn (setq label w3m-current-url)
				   (list w3m-current-url 16 nil nil))
			  (setq label (w3m-lnum-highlight-anchor num))
			  (w3m-lnum-get-anchor-info num))))))
	       (if info
		   (let ((action (car info)))
		     (cond ((null action) ; image
			    (w3m-lnum-universal-dispatch
			     info label
			     w3m-lnum-actions-image-alist))
			   ((stringp action)		   ; url
			    (if (or (stringp (nth 2 info)) ; image url
				    (stringp (nth 3 info)))
				(w3m-lnum-universal-dispatch
				 info label
				 (append w3m-lnum-actions-link-alist
					 w3m-lnum-actions-image-alist))
			      (w3m-lnum-universal-dispatch
			       info label
			       w3m-lnum-actions-link-alist)))
			   ((eq (car action) 'w3m-form-submit) ; button
			    (w3m-lnum-universal-dispatch
			     info label
			     w3m-lnum-actions-button-alist))
			   (t (w3m-lnum-universal-dispatch ; form field
			       info label
			       w3m-lnum-actions-form-alist))))
		 (w3m-message "No valid anchor selected"))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lnum alternatives to w3m user commands on point

;;;###autoload
(defun w3m-lnum-toggle-inline-image (&optional arg)
  "If image at point, toggle it.
Otherwise turn on link numbers and toggle selected image.
With prefix ARG open url under image in new session.
If no such url, move over image and toggle it."
  (interactive "P")
  (if (w3m-image)
      (let ((url (get-char-property (point) 'w3m-href-anchor)))
	(if (and arg url)
	    (w3m-goto-url-new-session url)
	  (w3m-toggle-inline-image)))
    (let ((im (w3m-lnum-get-action
	       (if arg "Open image url in new session: "
		 "Toggle image: ")
	       2)))
      (if im
	  (if arg
	      (if (car im) (w3m-goto-url-new-session (car im))
		(push-mark (point))
		(goto-char (cadr im))
		(w3m-toggle-inline-image))
	    (save-excursion (goto-char (cadr im))
			    (w3m-toggle-inline-image)))
	(w3m-message "No image selected")))))

;;;###autoload
(defun w3m-lnum-view-image ()
  "Display the image under point in the external viewer.
If no image at poing, turn on image numbers and display selected.
The viewer is defined in `w3m-content-type-alist' for every type of an
image."
  (interactive)
  (let ((im (w3m-url-valid (w3m-image))))
    (cond (im (w3m-external-view im))
	  ((setq im (w3m-lnum-get-action
		     "Open image url in external viewer: " 2))
	   (w3m-external-view (nth 2 im)))
	  (t (w3m-message "No image selected")))))

;;;###autoload
(defun w3m-lnum-save-image ()
  "Save the image under point to a file.
If no image at poing, turn on image numbers and save selected.
The default name will be the original name of the image."
  (interactive)
  (let ((im (w3m-url-valid (w3m-image))))
    (cond (im (w3m-download im))
	  ((setq im (w3m-lnum-get-action "Save image: " 2))
	   (w3m-download (nth 2 im)))
	  (t (w3m-message "No image selected")))))

(defmacro w3m-lnum-zoom-image (rate &optional in)
  "Zoom image under point and interactively resize after that.
Numeric prefix RATE specifies how many percent the image is
changed by.  Default is the value of the `w3m-resize-image-scale'
variable.  If no image under point, activate numbering and ask
for one, then interactively resize.
If IN zoom in, otherwise zoom out."
  `(progn
     (or (w3m-display-graphic-p)
	 (error "Can't display images in this environment"))
     (or (w3m-imagick-convert-program-available-p)
	 (error "ImageMagick's `convert' program is required"))
     (let ((im (w3m-image)))
       (if im
	   (progn
	     (let ((percent (,(if in '+ '-) 100
			     (or ,rate w3m-resize-image-scale))))
	       (w3m-resize-inline-image-internal im percent)
	       (w3m-resize-image-interactive im ,rate
					     (/ percent 100.0))))
	 (setq im (w3m-lnum-get-action
		   ,(concat "Zoom " (if in "in" "out") " image: ") 2))
	 (save-excursion
	   (goto-char (cadr im))
	   (let ((percent (,(if in '+ '-) 100
			   (or ,rate w3m-resize-image-scale))))
	     (w3m-resize-inline-image-internal
	      (car im) percent)
	     (w3m-resize-image-interactive (car im) ,rate
					   (/ percent 100.0))))))))

(defun w3m-lnum-zoom-in-image (&optional rate)
  "Zoom in an image under point and interactively resize after that.
Numeric prefix RATE specifies how many percent the image is
enlarged by (30 means enlarging the image by 130%).  The default
is the value of the `w3m-resize-image-scale' variable.  If no
image under point, activate numbering and ask for one, then
interactively resize."
  (interactive "P")
  (w3m-lnum-zoom-image rate t))

(defun w3m-lnum-zoom-out-image (&optional rate)
  "Zoom out an image on unter point and interactively resize after that.
Numeric prefix RATE specifies how many percent the image is
shrunk by (30 means shrinking the image by 70%).  The default is
the value of the `w3m-resize-image-scale' variable.  If no image
under point, activate numbering and ask for one, then
interactively resize."
  (interactive "P")
  (w3m-lnum-zoom-image rate))

;;;###autoload
(defun w3m-lnum-external-view-this-url ()
  "Launch the external browser and display the link at point.
If no link at point, turn on link numbers and open selected externally."
  (interactive)
  (let ((url (w3m-url-valid (or (w3m-anchor) (w3m-image)
				(car
				 (w3m-lnum-get-action
				  "Open in external browser: " 1))))))
    (if url
	(w3m-view-url-with-browse-url url)
      (w3m-message "No URL selected"))))

;;;###autoload
(defun w3m-lnum-edit-this-url ()
  "Edit the page linked from the anchor under the cursor.
If no such, turn on link numbers and edit selected."
  (interactive)
  (let ((url (or (w3m-url-valid (w3m-anchor))
		 (car (w3m-lnum-get-action
		       "Select link to edit: " 1)))))
    (if url (w3m-edit-url url)
      (w3m-message "No URL selected"))))

;;;###autoload
(defun w3m-lnum-print-this-url ()
  "Display the url under point in the echo area and put it into `kill-ring'.
If no url under point, activate numbering and select one."
  (interactive)
  (if (or (w3m-anchor) (w3m-image))
      (w3m-print-this-url t)
    (let ((link (w3m-lnum-get-action "Select URL to copy: " 1)))
      (if link
	  (let ((url (car link)))
	    (kill-new url)
	    (w3m-message "%s%s" (let ((im-alt (nth 3 link)))
				  (if (zerop (length im-alt)) ""
				    (concat im-alt ": ")))
			 url))
	(w3m-message "No URL selected")))))

;;;###autoload
(defun w3m-lnum-download-this-url ()
  "Download the file or the page pointed to by the link under point.
If no point, activate numbering and select andchor to download."
  (interactive)
  (if (or (w3m-anchor) (w3m-image) (w3m-action))
      (w3m-download-this-url)
    (let ((info (w3m-lnum-get-action
		 "Select anchor to download: ")))
      (if info
	  (save-excursion
	    (goto-char (cadr info))
	    (w3m-download-this-url))
	(w3m-message "No anchor selected")))))

;;;###autoload
(defun w3m-lnum-bookmark-add-this-url ()
  "Add link under cursor to bookmarks.
If no link under point, activate numbering and ask for one."
  (interactive)
  (let ((url (w3m-anchor)))
    (cond
     (url (w3m-bookmark-add
	   url
	   (buffer-substring-no-properties
	    (previous-single-property-change (1+ (point))
					     'w3m-href-anchor)
	    (next-single-property-change (point) 'w3m-href-anchor)))
	  (w3m-message "Added"))
     ((setq url (w3m-lnum-get-action "Select URL to bookmark: " 1))
      (w3m-bookmark-add
       (car url)
       (let ((pos (cadr url)))
	 (if (= pos 16)		; 0th anchor selected
	     w3m-current-title
	   (buffer-substring-no-properties
	    (previous-single-property-change (1+ pos)
					     'w3m-href-anchor)
	    (next-single-property-change pos 'w3m-href-anchor)))))
      (w3m-message "added"))
     (t (w3m-message "No url selected")))))


;;; add link action for generic browser
(if browse-url-generic-program
    (setq w3m-lnum-actions-link-alist
	  (append w3m-lnum-actions-link-alist
		  `((?m (lambda (info) (browse-url-generic (car info)))
			,(concat "Open with "
				 browse-url-generic-program))))))

;;; add link action for curl if present
(if (executable-find "curl")
    (setq w3m-lnum-actions-link-alist
	  (append w3m-lnum-actions-link-alist
		  '((?D (lambda (info)
			  (let ((olddir default-directory))
			    (cd (read-directory-name
				 "Save to: " (getenv "HOME")
				 nil t))
			    (shell-command
			     (concat "curl -k -O '" (car info) "' &")
			     "*Curl*")
			    (cd olddir)))
			"Download with Curl")))))


(provide 'w3m-lnum)

;;; w3m-lnum.el ends here
