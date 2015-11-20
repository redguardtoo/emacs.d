;;; bookmark+-lit.el --- Bookmark highlighting for Bookmark+.
;;
;; Filename: bookmark+-lit.el
;; Description: Bookmark highlighting for Bookmark+.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2010-2015, Drew Adams, all rights reserved.
;; Created: Wed Jun 23 07:49:32 2010 (-0700)
;; Last-Updated: Sun Feb 22 09:01:13 2015 (-0800)
;;           By: dradams
;;     Update #: 901
;; URL: http://www.emacswiki.org/bookmark+-lit.el
;; Doc URL: http://www.emacswiki.org/BookmarkPlus
;; Keywords: bookmarks, highlighting, bookmark+
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `bookmark', `pp', `pp+'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Bookmark highlighting for Bookmark+ (library `bookmark+.el').
;;
;;    The Bookmark+ libraries are:
;;
;;    `bookmark+.el'     - main code library
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit.el' - code for highlighting bookmarks (this file)
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*'
;;    `bookmark+-1.el'   - other required code (non-bmenu)
;;    `bookmark+-key.el' - key and menu bindings
;;
;;    `bookmark+-doc.el' - documentation (comment-only file)
;;    `bookmark+-chg.el' - change log (comment-only file)
;;
;;    This library (`bookmark+-lit.el') is a Bookmark+ option.  If you
;;    want to use it then load it before loading `bookmark+.el', so
;;    that its commands can be bound to keys and menu items.
;;
;;    The documentation (in `bookmark+-doc.el') includes how to
;;    byte-compile and install Bookmark+.  The documentation is also
;;    available in these ways:
;;
;;    1. From the bookmark list (`C-x r l'):
;;       Use `?' to show the current bookmark-list status and general
;;       help, then click link `Doc in Commentary' or link `Doc on the
;;       Web'.
;;
;;    2. From the Emacs-Wiki Web site:
;;       http://www.emacswiki.org/BookmarkPlus.
;;
;;    3. From the Bookmark+ group customization buffer:
;;       `M-x customize-group bookmark-plus', then click link
;;       `Commentary'.
;;
;;    (The commentary links in #1 and #3 work only if you have library
;;    `bookmark+-doc.el' in your `load-path'.)
 
;;(@> "Index")
;;
;;  Index
;;  -----
;;
;;  If you have library `linkd.el' and Emacs 22 or later, load
;;  `linkd.el' and turn on `linkd-mode' now.  It lets you easily
;;  navigate around the sections of this doc.  Linkd mode will
;;  highlight this Index, as well as the cross-references and section
;;  headings throughout this file.  You can get `linkd.el' here:
;;  http://dto.freeshell.org/notebook/Linkd.html.
;;
;;  (@> "Things Defined Here")
;;  (@> "Faces (Customizable)")
;;  (@> "User Options (Customizable)")
;;  (@> "Internal Variables")
;;  (@> "Functions")
;;    (@> "Menu-List (`*-bmenu-*') Commands")
;;    (@> "General Highlight Commands")
;;    (@> "Other Functions")
 
;;(@* "Things Defined Here")
;;
;;  Things Defined Here
;;  -------------------
;;
;;  Commands defined here:
;;
;;
;;    `bmkp-bmenu-light', `bmkp-bmenu-light-marked',
;;    `bmkp-bmenu-set-lighting', `bmkp-bmenu-set-lighting-for-marked',
;;    `bmkp-bmenu-show-only-lighted-bookmarks', `bmkp-bmenu-unlight',
;;    `bmkp-bmenu-unlight-marked', `bmkp-bookmarks-lighted-at-point',
;;    `bmkp-cycle-lighted-this-buffer',
;;    `bmkp-cycle-lighted-this-buffer-other-window',
;;    `bmkp-light-autonamed-this-buffer', `bmkp-light-bookmark',
;;    `bmkp-light-bookmark-this-buffer', `bmkp-light-bookmarks',
;;    `bmkp-light-bookmarks-in-region',
;;    `bmkp-light-navlist-bookmarks',
;;    `bmkp-light-non-autonamed-this-buffer',
;;    `bmkp-light-this-buffer', `bmkp-lighted-jump',
;;    `bmkp-lighted-jump-other-window',
;;    `bmkp-next-lighted-this-buffer',
;;    `bmkp-next-lighted-this-buffer-repeat',
;;    `bmkp-previous-lighted-this-buffer',
;;    `bmkp-previous-lighted-this-buffer-repeat',
;;    `bmkp-set-lighting-for-bookmark',
;;    `bmkp-set-lighting-for-buffer',
;;    `bmkp-set-lighting-for-this-buffer',
;;    `bmkp-toggle-auto-light-when-jump',
;;    `bmkp-toggle-auto-light-when-set',
;;    `bmkp-unlight-autonamed-this-buffer', `bmkp-unlight-bookmark',
;;    `bmkp-unlight-bookmark-here',
;;    `bmkp-unlight-bookmark-this-buffer', `bmkp-unlight-bookmarks',
;;    `bmkp-unlight-non-autonamed-this-buffer',
;;    `bmkp-unlight-this-buffer'.
;;
;;  User options defined here:
;;
;;    `bmkp-auto-light-relocate-when-jump-flag',
;;    `bmkp-auto-light-when-jump', `bmkp-auto-light-when-set',
;;    `bmkp-light-left-fringe-bitmap' (Emacs 22+),
;;    `bmkp-light-priorities', `bmkp-light-right-fringe-bitmap' (Emacs
;;    22+), `bmkp-light-style-autonamed',
;;    `bmkp-light-style-non-autonamed', `bmkp-light-threshold'.
;;
;;  Faces defined here:
;;
;;    `bmkp-light-autonamed', `bmkp-light-fringe-autonamed' (Emacs
;;    22+), `bmkp-light-fringe-non-autonamed' (Emacs 22+),
;;    `bmkp-light-mark', `bmkp-light-non-autonamed'.
;;
;;  Non-interactive functions defined here:
;;
;;    `bmkp-a-bookmark-lighted-at-pos',
;;    `bmkp-a-bookmark-lighted-on-this-line',
;;    `bmkp-bookmark-data-from-record',
;;    `bmkp-bookmark-name-from-record', `bmkp-bookmark-overlay-p',
;;    `bmkp-default-lighted', `bmkp-fringe-string' (Emacs 22+),
;;    `bmkp-get-lighting', `bmkp-lighted-p', `bmkp-light-face',
;;    `bmkp-light-style', `bmkp-light-style-choices',
;;    `bmkp-light-when', `bmkp-lighted-alist-only',
;;    `bmkp-lighting-attribute', `bmkp-lighting-face',
;;    `bmkp-lighting-style', `bmkp-lighting-when',
;;    `bmkp-make/move-fringe' (Emacs 22+),
;;    `bmkp-make/move-overlay-of-style', `bmkp-number-lighted',
;;    `bmkp-overlay-of-bookmark', `bmkp-read-set-lighting-args',
;;    `bmkp-set-lighting-for-bookmarks',
;;    `bmkp-this-buffer-lighted-alist-only',
;;    `bookmark-name-from-full-record', `bookmark-name-from-record'.
;;
;;  Internal variables defined here:
;;
;;    `bmkp-autonamed-overlays', `bmkp-last-auto-light-when-jump',
;;    `bmkp-last-auto-light-when-set', `bmkp-light-styles-alist',
;;    `bmkp-non-autonamed-overlays'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;

(eval-when-compile (require 'cl)) ;; case (plus, for Emacs 20: push)

(require 'bookmark)
;; bookmark-alist, bookmark-bmenu-bookmark, bookmark-completing-read, bookmark-get-bookmark,
;; bookmark-get-position, bookmark-handle-bookmark, bookmark-maybe-load-default-file,
;; bookmark-name-from-full-record, bookmark-name-from-record, bookmark-prop-get, bookmark-prop-set


;; Some general Renamings.
;;
;; 1. Fix incompatibility introduced by gratuitous Emacs name change.
;;
(cond ((and (fboundp 'bookmark-name-from-record)  (not (fboundp 'bookmark-name-from-full-record)))
       (defalias 'bookmark-name-from-full-record 'bookmark-name-from-record))
      ((and (fboundp 'bookmark-name-from-full-record)  (not (fboundp 'bookmark-name-from-record)))
       (defalias 'bookmark-name-from-record 'bookmark-name-from-full-record)))

;; 2. The vanilla name of the first is misleading, as it returns only the cdr of the record.
;;    The second is for consistency.
;;
(defalias 'bmkp-bookmark-data-from-record 'bookmark-get-bookmark-record)
(defalias 'bmkp-bookmark-name-from-record 'bookmark-name-from-full-record)


;; (eval-when-compile (require 'bookmark+-bmu))
;; bmkp-bmenu-barf-if-not-in-menu-list, bmkp-bmenu-filter-function,
;; bmkp-bmenu-title

;; (eval-when-compile (require 'bookmark+-1))
;; bmkp-autonamed-bookmark-p, bmkp-autonamed-this-buffer-alist-only,
;; bmkp-autoname-format, bmkp-current-nav-bookmark,
;; bmkp-current-sort-order, bmkp-cycle-1, bmkp-default-bookmark-name,
;; bmkp-function-bookmark-p, bmkp-get-bookmark-in-alist, bmkp-get-buffer-name, bmkp-jump-1,
;; bmkp-latest-bookmark-alist, bmkp-marked-bookmarks-only,
;; bmkp-msg-about-sort-order, bmkp-nav-alist, bmkp-refresh-menu-list,
;; bmkp-remove-if, bmkp-remove-if-not, bmkp-repeat-command,
;; bmkp-sequence-bookmark-p, bmkp-sort-omit,
;; bmkp-specific-buffers-alist-only, bmkp-this-buffer-alist-only,
;; bmkp-this-file/buffer-cycle-sort-comparer, bmkp-this-buffer-p

(require 'pp+ nil t) ;; pp-read-expression-map

;;;;;;;;;;;;;;;;;;;;;;;

;; Quiet the byte-compiler
;;
(defvar bmkp-autoname-format)           ; In `bookmark+-1.el'.
(defvar bmkp-current-nav-bookmark)      ; In `bookmark+-1.el'.
(defvar bmkp-latest-bookmark-alist)     ; In `bookmark+-1.el'.
(defvar bmkp-light-left-fringe-bitmap)  ; Defined in this file for Emacs 22+.
(defvar bmkp-light-right-fringe-bitmap) ; Defined in this file for Emacs 22+.
(defvar bmkp-nav-alist)                 ; In `bookmark+-1.el'.
(defvar bmkp-this-file/buffer-cycle-sort-comparer) ; In `bookmark+-1.el'.
(defvar fringe-bitmaps)                 ; Built-in for Emacs 22+.

 
;;(@* "Faces (Customizable)")
;;; Faces (Customizable) ---------------------------------------------

(defface bmkp-light-autonamed
    '((((background dark)) (:background "#00004AA652F1")) ; a dark cyan
      (t (:background "misty rose")))   ; a light pink
  "*Face used to highlight an autonamed bookmark (except in the fringe)."
  :group 'bookmark-plus :group 'faces)

(when (fboundp 'fringe-columns)
  (defface bmkp-light-fringe-autonamed
      '((((background dark)) (:background "#B19E6A64B19E")) ; a dark magenta
        (t (:background "#691DC8A2691D"))) ; a medium green
    "*Face used to highlight an autonamed bookmark in the fringe."
    :group 'bookmark-plus :group 'faces)
  (defface bmkp-light-fringe-non-autonamed
      '((((background dark)) (:background "#691DC8A2691D")) ; a medium green
        (t (:foreground "Black" :background "Plum"))) ; a light magenta
    "*Face used to highlight a non-autonamed bookmark in the fringe."
    :group 'bookmark-plus :group 'faces))

(defface bmkp-light-mark '((t (:background "Plum")))
  "*Face used to mark highlighted bookmarks in the bookmark list.
This face must be combinable with face `bmkp-t-mark'."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-light-non-autonamed
    '((((background dark)) (:background "#B19E6A64B19E")) ; a dark magenta
      (t (:background "DarkSeaGreen1"))) ; a light green
  "*Face used to highlight a non-autonamed bookmark (except in the fringe)."
  :group 'bookmark-plus :group 'faces)
 
;;(@* "User Options (Customizable)")
;;; User Options (Customizable) --------------------------------------

;;;###autoload (autoload 'bmkp-auto-light-relocate-when-jump-flag "bookmark+")
(defcustom bmkp-auto-light-relocate-when-jump-flag t
  "*Non-nil means highlight the relocated, instead of the recorded, position.
This has an effect only when the highlighting style for the bookmark
is `point'."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-auto-light-when-jump "bookmark+")
(defcustom bmkp-auto-light-when-jump nil
  "*Which bookmarks to automatically highlight when jumped to.
NOTE: The values that specify highlighting in the current buffer
highlight bookmarks in the buffer that is current after jumping.  If
the bookmark does not really have an associated buffer, for example a
bookmark with a handler such as `w32-browser' that just invokes a
separate, non-Emacs program, then the current buffer after jumping
will be the buffer before jumping."
  :type '(choice
          (const :tag "Autonamed bookmark"                 autonamed-bookmark)
          (const :tag "Non-autonamed bookmark"             non-autonamed-bookmark)
          (const :tag "Any bookmark"                       any-bookmark)
          (const :tag "Autonamed bookmarks in buffer"      autonamed-in-buffer)
          (const :tag "Non-autonamed bookmarks in buffer"  non-autonamed-in-buffer)
          (const :tag "All bookmarks in buffer"            all-in-buffer)
          (const :tag "None (no automatic highlighting)"   nil))
  :group 'bookmark-plus)

;; The value is not correct if user customizes `bmkp-auto-light-when-jump' to non-nil.
;; So must compensate in `bmkp-toggle-auto-light-when-jump'.
(defvar bmkp-last-auto-light-when-jump (and (not bmkp-auto-light-when-jump)  'all-in-buffer)
  "Last value of `bmkp-auto-light-when-jump'.")

;;;###autoload (autoload 'bmkp-auto-light-when-set "bookmark+")
(defcustom bmkp-auto-light-when-set nil
  "*Which bookmarks to automatically highlight when set."
  :type '(choice
          (const :tag "Autonamed bookmark"                 autonamed-bookmark)
          (const :tag "Non-autonamed bookmark"             non-autonamed-bookmark)
          (const :tag "Any bookmark"                       any-bookmark)
          (const :tag "Autonamed bookmarks in buffer"      autonamed-in-buffer)
          (const :tag "Non-autonamed bookmarks in buffer"  non-autonamed-in-buffer)
          (const :tag "All bookmarks in buffer"            all-in-buffer)
          (const :tag "None (no automatic highlighting)"   nil))
  :group 'bookmark-plus)

;; The value is not correct if user customizes `bmkp-auto-light-when-set' to non-nil.
;; So must compensate in `bmkp-toggle-auto-light-when-set'.
(defvar bmkp-last-auto-light-when-set (and (not bmkp-auto-light-when-set)  'all-in-buffer)
  "Last value of `bmkp-auto-light-when-set'.")

;;;###autoload (autoload 'bmkp-light-priorities "bookmark+")
(defcustom bmkp-light-priorities '((bmkp-autonamed-overlays        . 160)
                                   (bmkp-non-autonamed-overlays    . 150))
  "*Priorities of bookmark highlighting overlay types.
As an idea, `ediff' uses 100+, `isearch' uses 1001."
  :group 'bookmark-plus :type '(alist :key-type symbol :value-type integer))

;; Not used for Emacs 20-21.
(when (fboundp 'fringe-columns)
  (defcustom bmkp-light-left-fringe-bitmap 'left-triangle
    "*Symbol for the left fringe bitmap to use to highlight a bookmark.
This option is not used for Emacs versions before Emacs 22."
    :type (cons 'choice (mapcar (lambda (bb) (list 'const bb)) fringe-bitmaps))
    :group 'bookmark-plus)

  ;; Not used for Emacs 20-21.
  (defcustom bmkp-light-right-fringe-bitmap 'right-triangle
    "*Symbol for the right fringe bitmap to use to highlight a bookmark.
This option is not used for Emacs versions before Emacs 22."
    :type (cons 'choice (mapcar (lambda (bb) (list 'const bb)) fringe-bitmaps))
    :group 'bookmark-plus))

;; Must be before any options that use it.
(defvar bmkp-light-styles-alist (append '(("Line Beginning"      . bol)
                                          ("Position"            . point)
                                          ("Line"                . line)
                                          ("None"                . none))
                                        (and (fboundp 'fringe-columns)
                                             '(("Left Fringe"         . lfringe)
                                               ("Right Fringe"        . rfringe)
                                               ("Left Fringe + Line"  . line+lfringe)
                                               ("Right Fringe + Line" . line+rfringe))))
  "Alist of highlighting styles.  Key: string description.  Value: symbol.")

;; Must be before options that use it.
(defun bmkp-light-style-choices ()
  "Return custom `:type' used for bookmark highlighting style choices."
  (cons 'choice
        (mapcar (lambda (xx) (list 'const :tag (car xx) (cdr xx))) bmkp-light-styles-alist)))

;;;###autoload (autoload 'bmkp-light-style-autonamed "bookmark+")
(defcustom bmkp-light-style-autonamed (if (not (fboundp 'fringe-columns)) ; Emacs 20-21.
                                          'line
                                        'line+lfringe)
  "*Default highlight style for autonamed bookmarks."
  :group 'bookmark-plus :type (bmkp-light-style-choices))

;;;###autoload (autoload 'bmkp-light-style-non-autonamed "bookmark+")
(defcustom bmkp-light-style-non-autonamed (if (not (fboundp 'fringe-columns)) ; Emacs 20-21.
                                              'line
                                            'line+rfringe)
  "*Default highlight style for non-autonamed bookmarks."
  :group 'bookmark-plus :type (bmkp-light-style-choices))

;;;###autoload (autoload 'bmkp-light-threshold "bookmark+")
(defcustom bmkp-light-threshold 100000
  "*Maximum number of bookmarks to highlight."
  :type 'integer :group 'bookmark-plus)
 
;;(@* "Internal Variables")
;;; Internal Variables -----------------------------------------------

(defvar bmkp-autonamed-overlays nil
  "Overlays used to highlight autonamed bookmarks.")

(defvar bmkp-non-autonamed-overlays nil
  "Overlays used to highlight non-autonamed bookmarks.")
 
;;(@* "Functions")
;;; Functions --------------------------------------------------------


;;(@* "Menu-List (`*-bmenu-*') Commands")
;;  *** Menu-List (`*-bmenu-*') Commands ***

;;;###autoload (autoload 'bmkp-bmenu-show-only-lighted-bookmarks "bookmark+")
(bmkp-define-show-only-command lighted "Display (only) the highlighted bookmarks." ; `H S' in bookmark list
                               bmkp-lighted-alist-only)

;;;###autoload (autoload 'bmkp-bmenu-light "bookmark+")
(defun bmkp-bmenu-light ()              ; `H H' in bookmark list
  "Highlight the location of this line's bookmark."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-light-bookmark (bookmark-bmenu-bookmark) nil nil 'MSG))

;;;###autoload (autoload 'bmkp-bmenu-light-marked "bookmark+")
(defun bmkp-bmenu-light-marked (&optional parg msgp) ; `H > H' in bookmark list
  "Highlight the marked bookmarks."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when msgp (message "Highlighting marked bookmarks..."))
  (let ((marked  (bmkp-marked-bookmarks-only)))
    (unless marked (error "No marked bookmarks"))
    (dolist (bmk  marked) (bmkp-light-bookmark bmk)))
  (when msgp (message "Highlighting marked bookmarks...done")))

;;;###autoload (autoload 'bmkp-bmenu-unlight "bookmark+")
(defun bmkp-bmenu-unlight ()            ; `H U' in bookmark list
  "Unhighlight the location of this line's bookmark."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-unlight-bookmark (bookmark-bmenu-bookmark) 'NOERROR))

;;;###autoload (autoload 'bmkp-bmenu-unlight-marked "bookmark+")
(defun bmkp-bmenu-unlight-marked (&optional parg msgp) ; `H > U' in bookmark list
  "Unhighlight the marked bookmarks."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when msgp (message "Unhighlighting marked bookmarks..."))
  (let ((marked  (bmkp-marked-bookmarks-only)))
    (unless marked (error "No marked bookmarks"))
    (dolist (bmk  marked) (bmkp-unlight-bookmark bmk t)))
  (when msgp (message "Unhighlighting marked bookmarks...done")))

;;;###autoload (autoload 'bmkp-bmenu-set-lighting "bookmark+")
(defun bmkp-bmenu-set-lighting (style face when &optional msgp) ; `H +' in bookmark list
  "Set the `lighting' property for this line's bookmark.
You are prompted for the highlight style, face, and condition (when)."
  (interactive
   (let* ((bmk        (bookmark-bmenu-bookmark))
          (bmk-style  (bmkp-lighting-style bmk))
          (bmk-face   (bmkp-lighting-face bmk))
          (bmk-when   (bmkp-lighting-when bmk)))
     (append (bmkp-read-set-lighting-args
              (and bmk-style  (format "%s" (car (rassq bmk-style bmkp-light-styles-alist))))
              (and bmk-face   (format "%S" bmk-face))
              (and bmk-when   (format "%S" bmk-when)))
             '(MSG))))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-set-lighting-for-bookmark (bookmark-bmenu-bookmark) style face when 'MSG))

;;;###autoload (autoload 'bmkp-bmenu-set-lighting-for-marked "bookmark+")
(defun bmkp-bmenu-set-lighting-for-marked (style face when &optional msgp) ; `H > +' in bookmark list
  "Set the `lighting' property for the marked bookmarks.
You are prompted for the highlight style, face, and condition (when)."
  (interactive (append (bmkp-read-set-lighting-args) '(MSG)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when msgp (message "Setting highlighting..."))
  (let ((marked    (bmkp-marked-bookmarks-only))
        (curr-bmk  (bookmark-bmenu-bookmark)))
    (unless marked (error "No marked bookmarks"))
    (dolist (bmk  marked)
      (bookmark-prop-set bmk 'lighting (if (or face  style  when)
                                           `(,@(and face   (not (eq face 'auto))   `(:face ,face))
                                             ,@(and style  (not (eq style 'none))  `(:style ,style))
                                             ,@(and when   (not (eq when 'auto))   `(:when ,when)))
                                         ())))
    (when (get-buffer-create "*Bookmark List*") (bmkp-refresh-menu-list curr-bmk)))
  (when msgp (message "Setting highlighting...done")))


;;(@* "General Highlight Commands")
;;  *** General Highlight Commands ***

;;;###autoload (autoload 'bmkp-bookmarks-lighted-at-point "bookmark+")
(defun bmkp-bookmarks-lighted-at-point (&optional position fullp msgp) ; `C-x p ='
  "Return a list of the bookmarks highlighted at point.
Include only those in the current bookmark list (`bookmark-alist').
With no prefix arg, return the bookmark names.
With a prefix arg, return the full bookmark data.
Interactively, display the info.
Non-interactively:
 Use the bookmarks at optional arg POSITION (default: point).
 Optional arg FULLP means return full bookmark data.
 Optional arg MSGP means display the info."
  (interactive (list (point) current-prefix-arg 'MSG))
  (unless position (setq position  (point)))
  (let ((bmks  ())
        bmk)
    (dolist (ov  (overlays-at position))
      (when (setq bmk  (overlay-get ov 'bookmark))
        (when (setq bmk  (bmkp-get-bookmark-in-alist bmk 'NOERROR)) ; Ensure it's in current bookmark list.
          (push (if fullp bmk (bmkp-bookmark-name-from-record bmk)) bmks))))
    (if (not fullp)
        (when msgp (message "%s" bmks))
      (setq bmks  (mapcar #'bookmark-get-bookmark bmks))
      (when msgp (pp-eval-expression 'bmks)))
    bmks))

;;;###autoload (autoload 'bmkp-toggle-auto-light-when-jump "bookmark+")
(defun bmkp-toggle-auto-light-when-jump (&optional msgp) ; Not bound.
  "Toggle automatic bookmark highlighting when a bookmark is jumped to.
Set option `bmkp-auto-light-when-jump' to nil if non-nil, and to its
last non-nil value if nil."
  (interactive "p")
  (when (and bmkp-auto-light-when-jump  bmkp-last-auto-light-when-jump) ; Compensate for wrong default
    (setq bmkp-last-auto-light-when-jump  nil))
  (setq bmkp-last-auto-light-when-jump
        (prog1 bmkp-auto-light-when-jump ; Swap
          (setq bmkp-auto-light-when-jump  bmkp-last-auto-light-when-jump)))
  (when msgp (message "Automatic highlighting of bookmarks when jumping is now %s"
                      (if bmkp-auto-light-when-jump
                          (upcase (symbol-value bmkp-auto-light-when-jump))
                        "OFF"))))
                                        
;;;###autoload (autoload 'bmkp-lighted-jump "bookmark+")
(defun bmkp-lighted-jump (bookmark-name &optional flip-use-region-p) ; `C-x j h'
  "Jump to a highlighted bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-lighted-alist-only)))
     (unless alist  (error "No highlighted bookmarks"))
     (list (bookmark-completing-read "Jump to highlighted bookmark" nil alist) current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-lighted-jump-other-window "bookmark+")
(defun bmkp-lighted-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j h'
  "Jump to a highlighted bookmark in another window.
See `bmkp-lighted-jump'."
  (interactive
   (let ((alist  (bmkp-lighted-alist-only)))
     (unless alist  (error "No highlighted bookmarks"))
     (list (bookmark-completing-read "Jump to highlighted bookmark in another window" nil alist)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-unlight-bookmark "bookmark+")
(defun bmkp-unlight-bookmark (bookmark &optional noerrorp msgp)
  "Unhighlight BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (interactive
   (let ((lighted-bmks  (bmkp-lighted-alist-only)))
     (unless lighted-bmks (error "No highlighted bookmarks"))
     (list (bookmark-completing-read "UNhighlight bookmark" (bmkp-default-lighted) lighted-bmks)
           nil
           'MSG)))
  (let* ((bmk         (bookmark-get-bookmark bookmark 'NOERROR))
         (bmk-name    (bmkp-bookmark-name-from-record bmk))
         (autonamedp  (and bmk  (bmkp-autonamed-bookmark-p bmk))))
    (when bmk                           ; Skip bad bookmark, but not already highlighted bookmark.
      (unless (or noerrorp  (bmkp-lighted-p bmk-name)) (error "Bookmark `%s' is not highlighted" bmk-name))
      (dolist (ov  (if autonamedp bmkp-autonamed-overlays bmkp-non-autonamed-overlays))
        (when (eq bmk (overlay-get ov 'bookmark))  (delete-overlay ov)))) ; Check full bookmark, not name.
    (when msgp (message "UNhighlighted bookmark `%s'" bmk-name))))

;;;###autoload (autoload 'bmkp-unlight-bookmark-here "bookmark+")
(defun bmkp-unlight-bookmark-here (&optional noerrorp msgp) ; `C-x p C-u'
  "Unhighlight a bookmark at point or the same line (in that order)."
  (interactive (list nil 'MSG))
  (let ((bmk  (or (bmkp-a-bookmark-lighted-at-pos)  (bmkp-a-bookmark-lighted-on-this-line))))
    (unless bmk (error "No highlighted bookmark on this line"))
    (bmkp-unlight-bookmark bmk noerrorp msgp)))

;;;###autoload (autoload 'bmkp-unlight-bookmark-this-buffer "bookmark+")
(defun bmkp-unlight-bookmark-this-buffer (bookmark &optional noerrorp msgp) ; `C-x p u'
  "Unhighlight a BOOKMARK in this buffer.
BOOKMARK is a bookmark name or a bookmark record.
With a prefix arg, choose from all bookmarks, not just those in this
buffer."
  (interactive
   (let ((lighted-bmks  (if current-prefix-arg
                            (bmkp-lighted-alist-only)
                          (bmkp-this-buffer-lighted-alist-only)))
         (msg-suffix    (if current-prefix-arg "" " in this buffer")))
     (unless lighted-bmks (error "No highlighted bookmarks%s" msg-suffix))
     (list (bookmark-completing-read (format "UNhighlight bookmark%s in this buffer" msg-suffix)
                                     (bmkp-default-lighted)
                                     lighted-bmks)
           nil
           'MSG)))
  (bmkp-unlight-bookmark bookmark noerrorp msgp))

;;;###autoload (autoload 'bmkp-unlight-bookmarks "bookmark+")
(defun bmkp-unlight-bookmarks (&optional overlays-symbols this-buffer-p msgp) ; `C-x p U'
  "Unhighlight bookmarks.
A prefix argument determines which bookmarks to unhighlight:
 none    - Current buffer, all bookmarks.
 >= 0    - Current buffer, autonamed bookmarks only.
 < 0     - Current buffer, non-autonamed bookmarks only.
 C-u     - All buffers (all bookmarks)."
  (interactive (list (cond ((or (not current-prefix-arg)  (consp current-prefix-arg))
                            '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays))
                           ((natnump current-prefix-arg) '(bmkp-autonamed-overlays))
                           (current-prefix-arg           '(bmkp-non-autonamed-overlays)))
                     (or (not current-prefix-arg)  (atom current-prefix-arg))
                     'MSG))
  (unless overlays-symbols
    (setq overlays-symbols  '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays)))
  (let ((count           0)
        (count-auto      0)
        (count-non-auto  0)
        (this-buf        (current-buffer)))
    (dolist (ov-symb  overlays-symbols)
      (dolist (ov  (symbol-value ov-symb))
        (let ((ov-buf  (overlay-buffer ov)))
          (when (and ov-buf  (or (not this-buffer-p)  (eq ov-buf this-buf)))
            (when (eq 'bmkp-autonamed-overlays ov-symb)
              (setq count-auto  (1+ count-auto)
                    count       (1+ count)))
            (when (eq 'bmkp-non-autonamed-overlays ov-symb)
              (setq count-non-auto  (1+ count-non-auto)
                    count           (1+ count)))
            (delete-overlay ov)))))
    (when msgp (message "UNhighlighted %d bookmarks %s: %d autonamed, %d other"
                        count (if this-buffer-p "in this buffer" "(all buffers)")
                        count-auto count-non-auto))))

;;;###autoload (autoload 'bmkp-unlight-autonamed-this-buffer "bookmark+")
(defun bmkp-unlight-autonamed-this-buffer (&optional everywherep)
  "Unhighlight autonamed bookmarks.
No prefix arg: unhighlight them only in the current buffer.
Prefix arg, unhighlight them everywhere."
  (interactive "P")
  (bmkp-unlight-bookmarks '(bmkp-autonamed-overlays) (not everywherep)))

;;;###autoload (autoload 'bmkp-unlight-non-autonamed-this-buffer "bookmark+")
(defun bmkp-unlight-non-autonamed-this-buffer (&optional everywherep)
  "Unhighlight non-autonamed bookmarks.
No prefix arg: unhighlight them only in the current buffer.
Prefix arg, unhighlight them everywhere."
  (interactive "P")
  (bmkp-unlight-bookmarks '(bmkp-non-autonamed-overlays) (not everywherep)))

;;;###autoload (autoload 'bmkp-unlight-this-buffer "bookmark+")
(defun bmkp-unlight-this-buffer ()
  "Unhighlight all bookmarks in the current buffer."
  (interactive)
  (bmkp-unlight-bookmarks))

;;;###autoload (autoload 'bmkp-toggle-auto-light-when-set "bookmark+")
(defun bmkp-toggle-auto-light-when-set (&optional msgp) ; Not bound.
  "Toggle automatic bookmark highlighting when a bookmark is set.
Set option `bmkp-auto-light-when-set' to nil if non-nil, and to its
last non-nil value if nil."
  (interactive "p")
  (when (and bmkp-auto-light-when-set  bmkp-last-auto-light-when-set) ; Compensate for wrong default
    (setq bmkp-last-auto-light-when-set  nil))
  (setq bmkp-last-auto-light-when-set  (prog1 bmkp-auto-light-when-set ; Swap
                                         (setq bmkp-auto-light-when-set  bmkp-last-auto-light-when-set)))
  (when msgp (message "Automatic highlighting of bookmarks when setting is now %s"
                      (if bmkp-auto-light-when-set
                          (upcase (symbol-value bmkp-auto-light-when-set))
                        "OFF"))))
                                        
;;;###autoload (autoload 'bmkp-set-lighting-for-bookmark "bookmark+")
(defun bmkp-set-lighting-for-bookmark (bookmark-name style face when &optional msgp light-now-p)
  "Set the `lighting' property for bookmark BOOKMARK-NAME.
You are prompted for the bookmark, highlight style, face, and condition.
With a prefix argument, do not highlight now.

Non-interactively:
STYLE, FACE, and WHEN are as for a bookmark's `lighting' property
 entries, or nil if no such entry.
Non-nil MSGP means display a highlighting progress message.
Non-nil LIGHT-NOW-P means apply the highlighting now."
  (interactive
   (let* ((bmk        (bookmark-completing-read "Highlight bookmark"
                                                (or (bmkp-default-lighted)  (bmkp-default-bookmark-name))))
          (bmk-style  (bmkp-lighting-style bmk))
          (bmk-face   (bmkp-lighting-face bmk))
          (bmk-when   (bmkp-lighting-when bmk)))
     (append (list bmk)
             (bmkp-read-set-lighting-args
              (and bmk-style  (format "%s" (car (rassq bmk-style bmkp-light-styles-alist))))
              (and bmk-face   (format "%S" bmk-face))
              (and bmk-when   (format "%S" bmk-when)))
             (list 'MSGP (not current-prefix-arg)))))
  (when msgp (message "Setting highlighting..."))
  (bookmark-prop-set bookmark-name 'lighting (if (or face  style  when)
                                                 `(,@(and face   (not (eq face 'auto))   `(:face ,face))
                                                   ,@(and style  (not (eq style 'none))  `(:style ,style))
                                                   ,@(and when   (not (eq when 'auto))   `(:when ,when)))
                                               ()))
  (when (get-buffer-create "*Bookmark List*") (bmkp-refresh-menu-list bookmark-name))
  (when msgp (message "Setting highlighting...done"))
  (when light-now-p (bmkp-light-bookmark bookmark-name nil nil msgp))) ; This msg is more informative.

;;;###autoload (autoload 'bmkp-set-lighting-for-buffer "bookmark+")
(defun bmkp-set-lighting-for-buffer (buffer style face when &optional msgp light-now-p)
  "Set the `lighting' property for each of the bookmarks for BUFFER.
You are prompted for the highlight style, face, and condition (when).
With a prefix argument, do not highlight now.

Non-interactively:
STYLE, FACE, and WHEN are as for a bookmark's `lighting' property
 entries, or nil if no such entry.
Non-nil MSGP means display a highlighting progress message.
Non-nil LIGHT-NOW-P means apply the highlighting now."
  (interactive (append (list (bmkp-completing-read-buffer-name))
                       (bmkp-read-set-lighting-args)
                       (list 'MSGP (not current-prefix-arg))))
  (bmkp-set-lighting-for-bookmarks
   (let ((bmkp-last-specific-buffer  buffer)) (bmkp-last-specific-buffer-alist-only))
   style face when msgp light-now-p))

;;;###autoload (autoload 'bmkp-set-lighting-for-this-buffer "bookmark+")
(defun bmkp-set-lighting-for-this-buffer (style face when &optional msgp light-now-p)
  "Set the `lighting' property for each of the bookmarks for this buffer.
You are prompted for the highlight style, face, and condition (when).
With a prefix argument, do not highlight now.

Non-interactively:
STYLE, FACE, and WHEN are as for a bookmark's `lighting' property
 entries, or nil if no such entry.
Non-nil MSGP means display a highlighting progress message.
Non-nil LIGHT-NOW-P means apply the highlighting now."
  (interactive (append (bmkp-read-set-lighting-args) (list 'MSGP (not current-prefix-arg))))
  (bmkp-set-lighting-for-bookmarks (bmkp-this-buffer-alist-only) style face when msgp light-now-p))

(defun bmkp-set-lighting-for-bookmarks (alist style face when &optional msgp light-now-p)
  "Set the `lighting' property for each of the bookmarks in ALIST.
STYLE, FACE, and WHEN are as for a bookmark's `lighting' property
 entries, or nil if no such entry.
Non-nil MSGP means display a highlighting progress message.
Non-nil LIGHT-NOW-P means apply the highlighting now."
  (when msgp (message "Setting highlighting..."))
  (dolist (bmk  alist) (bmkp-set-lighting-for-bookmark bmk style face when)) ; No MSGP arg here.
  (when msgp (message "Setting highlighting...done"))
  (when light-now-p (bmkp-light-bookmarks alist nil msgp))) ; Do separately so we get its message.

;;;###autoload (autoload 'bmkp-light-bookmark "bookmark+")
(defun bmkp-light-bookmark (bookmark &optional style face msgp pointp)
  "Highlight BOOKMARK.
With a prefix arg you are prompted for the style and/or face to use:
 Plain prefix arg (`C-u'): prompt for both style and face.
 Numeric non-negative arg: prompt for face.
 Numeric negative arg: prompt for style.

Non-interactively:
 BOOKMARK is a bookmark name or a bookmark record, or it is ignored.
 STYLE and FACE override the defaults.
 POINT-P non-nil means highlight point rather than the recorded
  bookmark position."
  (interactive
   (let* ((bmk  (bookmark-completing-read "Highlight bookmark" (bmkp-default-bookmark-name)))
          (sty  (and current-prefix-arg  (or (consp current-prefix-arg)
                                             (<= (prefix-numeric-value current-prefix-arg) 0))
                     (cdr (assoc (let ((completion-ignore-case  t))
                                   (completing-read
                                    "Style: " bmkp-light-styles-alist nil t nil nil
                                    (and (bmkp-lighting-style bmk)
                                         (format "%s" (car (rassq (bmkp-lighting-style bmk)
                                                                  bmkp-light-styles-alist))))))
                                 bmkp-light-styles-alist))))
          (fac  (and current-prefix-arg  (or (consp current-prefix-arg)
                                             (natnump (prefix-numeric-value current-prefix-arg)))
                     (not (member sty '(lfringe rfringe none))) ; No face possible for these.
                     (condition-case nil ; Emacs 22+ accepts a default.
                         (read-face-name "Face: " (format "%S" (bmkp-lighting-face  bmk)))
                       (wrong-number-of-arguments (read-face-name "Face: "))))))
     (list bmk sty fac 'MSG)))
  (let* ((bmkp-use-region  nil)         ; Inhibit region handling.
         (bmk              (bookmark-get-bookmark bookmark (not msgp))) ; Error if interactive.
         (bmk-name         (bmkp-bookmark-name-from-record bmk))
         (pos              (and bmk  (bookmark-get-position bmk)))
         (buf              (and bmk  (bmkp-get-buffer-name bmk)))
         (autonamedp       (and bmk  (bmkp-autonamed-bookmark-p bmk)))
         (styl             (or style  (and bmk  (bmkp-light-style bmk))))
         (fac              (or face   (and bmk
                                           (not (member styl '(lfringe rfringe none)))
                                           (bmkp-light-face  bmk))))
         (passes-when-p    (and bmk  (or face
                                         style ; Always highlight if changed face or style.
                                         (bmkp-light-when bmk))))
         (nb-lit           (bmkp-number-lighted))
         bmk-ov)
    (catch 'bmkp-light-bookmark
      (when bmk                         ; Just skip bad bookmark if not interactive.
        (cond ((setq bmk-ov  (bmkp-overlay-of-bookmark bmk)) ; Already highlighted.
               (if (not (or style  face))
                   (when msgp           ; No-op batch.
                     (error "Already highlighted - use prefix arg to change"))
                 (when style (bmkp-make/move-overlay-of-style style pos autonamedp bmk-ov))
                 (when (and face  (not (memq styl '(lfringe rfringe none))))
                   (overlay-put bmk-ov 'face face)))
               (when msgp (message "%sighlighted bookmark `%s'" (if bmk-ov "H" "UNh") bmk-name)))
              (passes-when-p
               (save-excursion

                 ;; See note in comments of `bmkp-light-bookmarks' - same considerations here.
                 ;; (let ((bmkp-jump-display-function  nil)) (bookmark-handle-bookmark bmk))
                 ;;
                 (with-current-buffer (or (and buf  (get-buffer buf))
                                          (current-buffer))

                   ;; POINTP is non-nil when `bmkp-light-bookmark' is called from
                   ;; `bookmark--jump-via'.
                   (when (and pointp  bmkp-auto-light-relocate-when-jump-flag)
                     (setq pos  (point)))
                   (when (and pos  (< pos (point-max)))
                     (let ((ov  (bmkp-make/move-overlay-of-style styl pos autonamedp)))
                       (when ov         ; nil means `none' style.
                         (let ((ovs  (if autonamedp
                                         'bmkp-autonamed-overlays
                                       'bmkp-non-autonamed-overlays)))
                           (push ov (symbol-value ovs)))
                         (when (and (not (bmkp-lighted-p bmk))
                                    (> (setq nb-lit  (1+ nb-lit)) bmkp-light-threshold))
                           (setq nb-lit  (1- nb-lit))
                           (throw 'bmkp-light-bookmark bmk))
                         (overlay-put ov 'priority
                                      (or (cdr (assoc (if autonamedp
                                                          'bmkp-autonamed-overlays
                                                        'bmkp-non-autonamed-overlays)
                                                      bmkp-light-priorities))
                                          (apply #'min (mapcar #'cdr bmkp-light-priorities))))
                         (unless (memq styl '(lfringe rfringe none)) (overlay-put ov 'face fac))
                         (overlay-put ov 'evaporate  t)
                         (overlay-put ov 'category   'bookmark-plus)
                         (overlay-put ov 'bookmark   bmk)) ; Use full bookmark, because name can change.
                       (when msgp
                         (message "%sighlighted bookmark `%s'" (if ov "H" "UNh") bmk-name)))))))
              (t
               (when msgp (message "Bookmark's condition canceled highlighting"))))))))

;;;###autoload (autoload 'bmkp-light-bookmark-this-buffer "bookmark+")
(defun bmkp-light-bookmark-this-buffer (bookmark &optional style face msgp) ; `C-x p h'
  "Highlight a BOOKMARK in the current buffer.
With a prefix arg you are prompted for the style and/or face to use:
 Plain prefix arg (`C-u'): prompt for both style and face.
 Numeric non-negative arg: prompt for face.
 Numeric negative arg: prompt for style.
See `bmkp-light-boookmark' for argument descriptions."
  (interactive
   (let* ((bmk  (bookmark-completing-read "Highlight bookmark" nil (bmkp-this-buffer-alist-only)))
          (sty  (and current-prefix-arg  (or (consp current-prefix-arg)
                                             (<= (prefix-numeric-value current-prefix-arg) 0))
                     (cdr (assoc (let ((completion-ignore-case  t))
                                   (completing-read
                                    "Style: " bmkp-light-styles-alist nil t nil nil
                                    (and (bmkp-lighting-style bmk)
                                         (format "%s" (car (rassq (bmkp-lighting-style bmk)
                                                                  bmkp-light-styles-alist))))))
                                 bmkp-light-styles-alist))))
          (fac  (and current-prefix-arg  (or (consp current-prefix-arg)
                                             (natnump (prefix-numeric-value current-prefix-arg)))
                     (not (member sty '(lfringe rfringe none))) ; No face possible for these.
                     (condition-case nil ; Emacs 22+ accepts a default.
                         (read-face-name "Face: " (format "%S" (bmkp-lighting-face  bmk)))
                       (wrong-number-of-arguments (read-face-name "Face: "))))))
     (list bmk sty fac 'MSG)))
  (bmkp-light-bookmark bookmark style face msgp))

;;;###autoload (autoload 'bmkp-light-bookmarks "bookmark+")
(defun bmkp-light-bookmarks (&optional alist overlays-symbols msgp) ; `C-x p H'
  "Highlight bookmarks.
A prefix argument determines which bookmarks to highlight:
 none    - Current buffer, all bookmarks.
 = 0     - Current buffer, highlighted bookmarks only (rehighlight).
 > 0     - Current buffer, autonamed bookmarks only.
 < 0     - Current buffer, non-autonamed bookmarks only.
 C-u     - All buffers (all bookmarks) - after confirmation.
 C-u C-u - Navlist (all bookmarks).

Non-interactively, ALIST is the alist of bookmarks to highlight.
It must be provided: if nil then do not highlight any bookmarks."
  (interactive
   (list (cond ((not current-prefix-arg)     (bmkp-this-buffer-alist-only))
               ((consp current-prefix-arg)   (if (> (prefix-numeric-value current-prefix-arg) 4)
                                                 bmkp-nav-alist
                                               (unless (y-or-n-p
                                                        "Confirm highlighting bookmarks in ALL buffers ")
                                                 (error "Canceled highlighting"))
                                               (bmkp-specific-buffers-alist-only
                                                (mapcar #'buffer-name (buffer-list)))))
               ((> current-prefix-arg 0)     (bmkp-autonamed-this-buffer-alist-only))
               ((< current-prefix-arg 0)     (bmkp-remove-if #'bmkp-autonamed-bookmark-p
                                                             (bmkp-this-buffer-alist-only)))
               ((= current-prefix-arg 0)     (bmkp-this-buffer-lighted-alist-only)))
         (cond ((or (not current-prefix-arg)  (consp current-prefix-arg))
                '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays))
               ((natnump current-prefix-arg) '(bmkp-autonamed-overlays))
               (current-prefix-arg           '(bmkp-non-autonamed-overlays)))
         'MSG))
  (unless overlays-symbols
    (setq overlays-symbols  '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays)))
  (let ((bmkp-use-region  nil)          ; Inhibit region handling.
        (total            0)
        (nb-auto          0)
        (nb-non-auto      0)
        (new-auto         0)
        (new-non-auto     0)
        (nb-lit           (bmkp-number-lighted))
        bmk bmk-name autonamedp face style pos buf bmk-ov passes-when-p)
    (catch 'bmkp-light-bookmarks
      (dolist (bookmark  alist)
        (setq bmk            (bookmark-get-bookmark bookmark 'NOERROR) ; Should be a no-op.
              bmk-name       (and bmk  (bmkp-bookmark-name-from-record bmk))
              autonamedp     (and bmk  (bmkp-autonamed-bookmark-p bmk-name))
              face           (and bmk  (bmkp-light-face bmk))
              style          (and bmk  (bmkp-light-style bmk))
              bmk-ov         (bmkp-overlay-of-bookmark bmk)
              passes-when-p  (and bmk  (or bmk-ov ; Always highlight if already highlighted.
                                           (bmkp-light-when bmk))))
        (when (and bmk  passes-when-p)  ; Skip bad bookmark and respect `:when' (unless highlighted).
          (setq pos  (bookmark-get-position bmk)
                buf  (bmkp-get-buffer-name bmk))
          (save-excursion
            ;; An alternative here would be to call the handler at let it do the highlighting.
            ;; In that case, we would need at least to bind the display function to nil while
            ;; handling, so we don't also do the jump.  In particular, we don't want to pop to
            ;; the bookmark in a new window or frame.
            ;; Calling the handler would be good for some cases, such as Info, where the
            ;; highlighting is not really specific to the buffer but to a narrowed part of it.
            ;;
            ;; (let ((bmkp-jump-display-function  nil)) (bookmark-handle-bookmark bmk))
            ;;
            ;; But calling the handler is in general the wrong thing.  We don't want highlighting
            ;; all Dired bookmarks in a given directory to also do all the file marking and
            ;; subdir hiding associated with each of the bookmarks.  So we do just the
            ;; highlighting, no handling, putting the code in side `with-current-buffer'.
            (with-current-buffer (or (and buf  (get-buffer buf))
                                     (current-buffer))
              (when (and pos  (< pos (point-max)))
                (dolist (ov-symb  overlays-symbols)
                  (when (or (and (eq 'bmkp-autonamed-overlays     ov-symb)  autonamedp)
                            (and (eq 'bmkp-non-autonamed-overlays ov-symb)  (not autonamedp)))
                    (let ((ov  (bmkp-make/move-overlay-of-style style pos autonamedp bmk-ov)))
                      (when ov          ; nil means `none' style.
                        (add-to-list ov-symb ov)
                        (when (eq 'bmkp-autonamed-overlays ov-symb)
                          (unless bmk-ov (setq new-auto  (1+ new-auto)))
                          (setq nb-auto  (1+ nb-auto)))
                        (when (eq 'bmkp-non-autonamed-overlays ov-symb)
                          (unless bmk-ov (setq new-non-auto  (1+ new-non-auto)))
                          (setq nb-non-auto  (1+ nb-non-auto)))
                        (when (and (not bmk-ov)  (> (setq nb-lit  (1+ nb-lit)) bmkp-light-threshold))
                          (setq nb-lit  (1- nb-lit))
                          (throw 'bmkp-light-bookmarks bmk))
                        (setq total  (1+ total))
                        (overlay-put ov 'priority ; > ediff's 100+, < isearch-overlay's 1001.
                                     (or (cdr (assoc ov-symb bmkp-light-priorities))
                                         (apply #'min (mapcar #'cdr bmkp-light-priorities))))
                        (unless (memq style '(lfringe rfringe none)) (overlay-put ov 'face face))
                        (overlay-put ov 'evaporate  t)
                        (overlay-put ov 'category  'bookmark-plus)
                        (overlay-put ov 'bookmark  bmk))))))))))) ; Use full bookmark - name can change.
    (when msgp (message "%s New: %d auto + %d other,  Total: %d auto + %d other = %d"
                        (if (consp current-prefix-arg)
                            (if (> (prefix-numeric-value current-prefix-arg) 4)
                                "[Navlist]"
                              "[All buffers]")
                          "[This buffer]")
                        new-auto new-non-auto nb-auto nb-non-auto total))))

;;;###autoload (autoload 'bmkp-light-navlist-bookmarks "bookmark+")
(defun bmkp-light-navlist-bookmarks (&optional overlays-symbols msgp)
  "Highlight bookmarks in the navigation list.
No prefix arg:   all bookmarks.
Prefix arg >= 0: autonamed bookmarks only.
Prefix arg < 0:  non-autonamed bookmarks only."
  (interactive
   (list (cond ((not current-prefix-arg) '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays))
               ((natnump (prefix-numeric-value current-prefix-arg)) '(bmkp-autonamed-overlays))
               (current-prefix-arg '(bmkp-non-autonamed-overlays)))
         'MSG))
  (bmkp-light-bookmarks bmkp-nav-alist overlays-symbols msgp))

;;;###autoload (autoload 'bmkp-light-this-buffer "bookmark+")
(defun bmkp-light-this-buffer (&optional overlays-symbols msgp)
  "Highlight bookmarks in the current buffer.
No prefix arg:   all bookmarks.
Prefix arg >= 0: autonamed bookmarks only.
Prefix arg < 0:  non-autonamed bookmarks only."
  (interactive
   (list (cond ((not current-prefix-arg) '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays))
               ((natnump (prefix-numeric-value current-prefix-arg)) '(bmkp-autonamed-overlays))
               (current-prefix-arg '(bmkp-non-autonamed-overlays)))
         'MSG))
  (bmkp-light-bookmarks (bmkp-this-buffer-alist-only) overlays-symbols msgp))

;;;###autoload (autoload 'bmkp-light-bookmarks-in-region "bookmark+")
(defun bmkp-light-bookmarks-in-region (start end &optional overlays-symbols msgp)
  "Highlight bookmarks in the region.
No prefix arg:   all bookmarks.
Prefix arg >= 0: autonamed bookmarks only.
Prefix arg < 0:  non-autonamed bookmarks only."
  (interactive
   (list (region-beginning)
         (region-end)
         (cond ((not current-prefix-arg) '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays))
               ((natnump (prefix-numeric-value current-prefix-arg)) '(bmkp-autonamed-overlays))
               (current-prefix-arg '(bmkp-non-autonamed-overlays)))
         'MSG))
  (bmkp-light-bookmarks (bmkp-remove-if-not (lambda (bmk) (let ((pos  (bookmark-get-position bmk)))
                                                            (and (>= pos start)  (<= pos end))))
                                            (bmkp-this-buffer-alist-only))
                        overlays-symbols msgp))

;;;###autoload (autoload 'bmkp-light-autonamed-this-buffer "bookmark+")
(defun bmkp-light-autonamed-this-buffer (&optional msgp)
  "Highlight all autonamed bookmarks."
  (interactive (list 'MSG))
  (bmkp-light-bookmarks (bmkp-autonamed-this-buffer-alist-only) '(bmkp-autonamed-overlays) msgp))

;;;###autoload (autoload 'bmkp-light-non-autonamed-this-buffer "bookmark+")
(defun bmkp-light-non-autonamed-this-buffer (&optional msgp)
  "Highlight all non-autonamed bookmarks."
  (interactive (list 'MSG))
  (bmkp-light-bookmarks (bmkp-remove-if #'bmkp-autonamed-bookmark-p (bmkp-this-buffer-alist-only))
                        '(bmkp-non-autonamed-overlays) msgp))

;;;###autoload (autoload 'bmkp-cycle-lighted-this-buffer "bookmark+")
(defun bmkp-cycle-lighted-this-buffer (increment &optional other-window startoverp)
  "Cycle through highlighted bookmarks in this buffer by INCREMENT.
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value

To change the sort order, you can filter the `*Bookmark List*' to show
only highlighted bookmarks for this buffer, sort the bookmarks there,
and use `\\[bmkp-choose-navlist-from-bookmark-list]', choosing `CURRENT *Bookmark List*' as the
navigation list.

Then you can cycle the bookmarks using `bookmark-cycle'
\(`\\[bmkp-next-bookmark-repeat]' etc.), instead of `bookmark-cycle-lighted-this-buffer'.

In Lisp code:
 Non-nil OTHER-WINDOW means jump to the bookmark in another window.
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) nil startovr)))
  (bookmark-maybe-load-default-file)
  (let ((bmkp-sort-comparer  bmkp-this-file/buffer-cycle-sort-comparer))
    (setq bmkp-nav-alist  (bmkp-sort-omit (bmkp-this-buffer-lighted-alist-only))))
  (unless bmkp-nav-alist (error "No lighted bookmarks for cycling"))
  (unless (and bmkp-current-nav-bookmark
               (not startoverp)
               (bookmark-get-bookmark bmkp-current-nav-bookmark 'NOERROR)
               (bmkp-this-buffer-p bmkp-current-nav-bookmark)) ; Exclude desktops etc.
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist)))
  (if (bmkp-cycle-1 increment other-window startoverp)
      (unless (or (bmkp-sequence-bookmark-p bmkp-current-nav-bookmark)
                  (bmkp-function-bookmark-p bmkp-current-nav-bookmark))
        (message "Position: %9d, Bookmark: `%s'" (point) (bmkp-bookmark-name-from-record
                                                          bmkp-current-nav-bookmark)))
    (message "Invalid bookmark: `%s'" (bmkp-bookmark-name-from-record bmkp-current-nav-bookmark))))

;;;###autoload (autoload 'bmkp-cycle-lighted-this-buffer-other-window "bookmark+")
(defun bmkp-cycle-lighted-this-buffer-other-window (increment &optional startoverp)
  "Same as `bmkp-cycle-lighted-this-buffer' but uses another window."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-lighted-this-buffer increment 'OTHER-WINDOW startoverp))

;;;###autoload (autoload 'bmkp-next-lighted-this-buffer "bookmark+")
(defun bmkp-next-lighted-this-buffer (n &optional startoverp) ; Repeatable key, e.g. `S-f2'
  "Jump to the Nth-next highlighted bookmark in the current buffer.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle-lighted-this-buffer'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-lighted-this-buffer n nil startoverp))

;;;###autoload (autoload 'bmkp-previous-lighted-this-buffer "bookmark+")
(defun bmkp-previous-lighted-this-buffer (n &optional startoverp) ; Repeatable key, e.g. `f2'
  "Jump to the Nth-previous highlighted bookmark in the current buffer.
See `bmkp-next-lighted-this-buffer'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-lighted-this-buffer (- n) nil startoverp))

;;;###autoload (autoload 'bmkp-next-lighted-this-buffer-repeat "bookmark+")
(defun bmkp-next-lighted-this-buffer-repeat (arg) ; `C-x p C-down'
  "Jump to the Nth next highlighted bookmark in the current buffer.
This is a repeatable version of `bmkp-next-bookmark-this-buffer'.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-next-lighted-this-buffer))

;;;###autoload (autoload 'bmkp-previous-lighted-this-buffer-repeat "bookmark+")
(defun bmkp-previous-lighted-this-buffer-repeat (arg) ; `C-x p C-up'
  "Jump to the Nth previous highlighted bookmark in the current buffer.
See `bmkp-next-lighted-this-buffer-repeat'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-previous-lighted-this-buffer))


;;(@* "Other Functions")
;;  *** Other Functions ***

(defun bmkp-light-face (bookmark)
  "Return the face to use to highlight BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Returns:
 nil if BOOKMARK is not a valid bookmark;
 the `:face' specified by BOOKMARK's `lighting' property, if any;
 `bmkp-light-autonamed' if BOOKMARK is an autonamed bookmark;
 or `bmkp-light-non-autonamed' otherwise."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (or (bmkp-lighting-face bookmark)
      (and bookmark  (if (bmkp-string-match-p (format bmkp-autoname-format ".*")
                                              (bmkp-bookmark-name-from-record bookmark))
                         'bmkp-light-autonamed
                       'bmkp-light-non-autonamed))))

(defun bmkp-light-style (bookmark)
  "Return the style to use to highlight BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Returns:
 nil if BOOKMARK is not a valid bookmark;
 the `:style' specified by BOOKMARK's `lighting' property, if any;
 the value of `bmkp-light-style-autonamed' if autonamed;
 or the value of `bmkp-light-style-non-autonamed' otherwise."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (or (bmkp-lighting-style bookmark)
      (and bookmark  (if (bmkp-string-match-p (format bmkp-autoname-format ".*")
                                              (bmkp-bookmark-name-from-record bookmark))
                         bmkp-light-style-autonamed
                       bmkp-light-style-non-autonamed))))

(defun bmkp-light-when (bookmark)
  "Return non-nil if BOOKMARK should be highlighted.
BOOKMARK's  `:when' condition is used to determine this.
BOOKMARK is a bookmark name or a bookmark record."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (let ((this-bookmark       bookmark)
        (this-bookmark-name  (bmkp-bookmark-name-from-record bookmark))
        (when-sexp           (bmkp-lighting-when bookmark)))
    (not (eq :no-light (eval when-sexp)))))

(defun bmkp-lighting-face (bookmark)
  "`:face' specified by BOOKMARK's `lighting', or nil if no `:face' entry.
BOOKMARK is a bookmark name or a bookmark record.

The `:face' entry is the face (a symbol) used to highlight BOOKMARK.
Alternatively, it can be `auto' or nil, which both mean the same as
having no `:face' entry: do not override automatic face choice."
  (bmkp-lighting-attribute bookmark :face))

(defun bmkp-lighting-style (bookmark)
  "`:style' specified by BOOKMARK's `lighting', or nil if no `:style' entry.
BOOKMARK is a bookmark name or a bookmark record.

The `:style' entry is the style used to highlight BOOKMARK.
It is a value acceptable for `bmkp-light-style-non-autonamed'.
Alternatively, it can be `auto' or nil, which both mean the same as
having no `:style' entry: do not override automatic style choice."
  (bmkp-lighting-attribute bookmark :style))

(defun bmkp-lighting-when (bookmark)
  "`:when' specified by BOOKMARK's `lighting', or nil if no `:when' entry.
BOOKMARK is a bookmark name or a bookmark record.

The `:when' entry is a sexp that is eval'd when you try to highlight
BOOKMARK.  If the result is the symbol `:no-light', then do not
highlight.  Otherwise, highlight.  (Note that highlighting happens if
the value is nil or there is no `:when' entry.)"
  (bmkp-lighting-attribute bookmark :when))

(defun bmkp-lighting-attribute (bookmark attribute)
  "ATTRIBUTE specified by BOOKMARK's `lighting', or nil if no such attribute.
BOOKMARK is a bookmark name or a bookmark record.
ATTRIBUTE is `:style' or `:face'."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (let* ((lighting  (and bookmark  (bmkp-get-lighting bookmark)))
         (attr      (and (consp lighting)  (plist-get lighting attribute))))
    (when (and (eq 'auto attr)  (not (eq :when attribute)))
      (setq attr  nil))
    attr))

(defun bmkp-get-lighting (bookmark)
  "Return the `lighting' property list for BOOKMARK.
This is the cdr of the `lighting' entry (i.e. with `lighting' removed).
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'lighting))

(defun bmkp-bookmark-overlay-p (overlay)
  "Return non-nil if OVERLAY is a bookmark overlay.
The non-nil value returned is in fact the full bookmark."
  (and (overlayp overlay)  (overlay-get overlay 'bookmark)))

(defun bmkp-default-lighted ()
  "Return a highlighted bookmark at point or on this line, or nil if none.
For Emacs 23+, if there is a highlighted bookmark at point, return a
 list of all such."
  (or (if (> emacs-major-version 22) (bmkp-bookmarks-lighted-at-point) (bmkp-a-bookmark-lighted-at-pos))
      (bmkp-a-bookmark-lighted-on-this-line)))

(defun bmkp-a-bookmark-lighted-on-this-line (&optional fullp msgp)
  "Return a bookmark highlighted on the current line or nil if none.
The search for a highlighted bookmark moves left to bol from point,
 then right to eol from point.
Return the bookmark name or, if FULLP non-nil, the full bookmark data."
  (let ((pos  (point))
        (bol  (1+ (line-beginning-position)))
        (eol  (1- (line-end-position)))
        bmk)
    (catch 'bmkp-a-bookmark-lighted-on-this-line
      (while (>= pos bol)
        (when (setq bmk  (bmkp-a-bookmark-lighted-at-pos pos))
          (throw 'bmkp-a-bookmark-lighted-on-this-line bmk))
        (setq pos  (1- pos)))
      (while (<= pos eol)
        (when (setq bmk  (bmkp-a-bookmark-lighted-at-pos pos))
          (throw 'bmkp-a-bookmark-lighted-on-this-line bmk))
        (setq pos  (1+ pos)))
      nil)
    (when (and bmk  fullp)  (setq bmk  (bookmark-get-bookmark bmk)))
    bmk))

(defun bmkp-a-bookmark-lighted-at-pos (&optional position fullp)
  "Return a bookmark (in current bookmark list) highlighted at POSITION.
Return nil if there is none such.
POSITION defaults to point.
Return the bookmark name or, if FULLP non-nil, the full bookmark data."
  (unless position (setq position  (point)))
  (let (bmk)
    (catch 'bmkp-a-bookmark-lighted-at-pos
      (dolist (ov  (overlays-at position))
        (when (setq bmk  (overlay-get ov 'bookmark))
          (throw 'bmkp-a-bookmark-lighted-at-pos bmk)))
      nil)
    (let ((b-in-list  (bmkp-get-bookmark-in-alist bmk 'NOERROR)))
      (and b-in-list                    ; Must be in current bookmark list.
           (if fullp b-in-list (bmkp-bookmark-name-from-record bmk))))))

(defun bmkp-read-set-lighting-args (&optional default-style default-face default-when)
  "Read args STYLE, FACE, and WHEN for commands that set `lighting' prop.
Optional args are the default values (strings) for reading new values."
  (let* ((icicle-unpropertize-completion-result-flag  t)
         (style       (cdr (assoc (let ((completion-ignore-case  t))
                                    (completing-read "Style: " bmkp-light-styles-alist
                                                     nil t nil nil default-style))
                                  bmkp-light-styles-alist)))
         (face        (and (not (member style '(lfringe rfringe none))) ; No face possible for these.
                           (y-or-n-p "Change face? ") ; Allow nil, for `auto'.
                           (condition-case nil ; Emacs 22+ accepts a default.
                               (read-face-name "Face: " default-face)
                             (wrong-number-of-arguments (read-face-name "Face: ")))))
         (when-cands  `(("auto" . nil)
                        ("conditionally (read sexp)")
                        ("never"  . :no-light)))
         (when         (completing-read "When: " when-cands nil t nil nil
                                        (if default-when "conditionally (read sexp)" "auto")))
         (evald       (if (bmkp-string-match-p "^con" when)
                          (read-from-minibuffer "Highlight when (sexp): " nil
                                                (if (boundp 'pp-read-expression-map)
                                                    pp-read-expression-map
                                                  read-expression-map)
                                                t 'read-expression-history default-when)
                        (cdr (assoc when when-cands)))))
    (list style face evald)))

(defun bmkp-lighted-alist-only ()
  "`bookmark-alist', with only highlighted bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (bmkp-lighted-p bmk)) bookmark-alist))

(defun bmkp-this-buffer-lighted-alist-only ()
  "`bookmark-alist', with only highlighted bookmarks for the current buffer.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (and (bmkp-this-buffer-p bmk)  (bmkp-lighted-p bmk)))
                      bookmark-alist))

(defun bmkp-number-lighted (&optional overlays-symbols)
  "Number of bookmarks highlighted."
  (unless overlays-symbols
    (setq overlays-symbols  '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays)))
  (let ((count  0))
    (dolist (ov-symb  overlays-symbols)
      (dolist (ov  (symbol-value ov-symb)) (when (overlay-buffer ov) (setq count  (1+ count)))))
    count))

(defalias 'bmkp-lighted-p 'bmkp-overlay-of-bookmark)
(defun bmkp-overlay-of-bookmark (bookmark &optional overlays)
  "Return the overlay for BOOKMARK in OVERLAYS, or nil if none.
BOOKMARK is a bookmark name or a bookmark record.
Optional arg OVERLAYS is the list of overlays to check.
If nil, check overlays for both autonamed and non-autonamed bookmarks."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (and bookmark                         ; Return nil for no such bookmark.
       (catch 'bmkp-overlay-of-bookmark
         (dolist (ov  (if overlays
                          (apply #'append (mapcar #'symbol-value overlays))
                        (append bmkp-autonamed-overlays bmkp-non-autonamed-overlays)))
           (when (and (overlay-buffer ov)  (eq bookmark (overlay-get ov 'bookmark)))
             (throw 'bmkp-overlay-of-bookmark ov)))
         nil)))

(defun bmkp-make/move-overlay-of-style (style pos autonamedp &optional overlay)
  "Return a bookmark overlay of STYLE at bookmark position POS.
AUTONAMEDP non-nil means the bookmark is autonamed.
If OVERLAY is non-nil it is the overlay to use - change to STYLE.
 Otherwise, create a new overlay.
If STYLE is `none' then:
 If OVERLAY is non-nil, delete it.
 Return nil."
  (let ((ov  overlay))
    (when (and (< emacs-major-version 22)  (not (rassq style bmkp-light-styles-alist)))
      (message "Fringe styles not supported before Emacs 22 - changing to `line' style")
      (setq style 'line))
    (case style
      (line          (if (not ov)
                         (setq ov  (save-excursion
                                     (make-overlay
                                      (progn (goto-char pos) (line-beginning-position 1))
                                      (progn (goto-char pos) (line-beginning-position 2))
                                      nil
                                      'FRONT-ADVANCE)))
                       (overlay-put ov 'before-string nil) ; Remove any fringe highlighting.
                       (save-excursion
                         (move-overlay ov
                                       (progn (goto-char pos) (line-beginning-position 1))
                                       (progn (goto-char pos) (line-beginning-position 2))))))
      (lfringe       (setq ov  (bmkp-make/move-fringe 'left  pos autonamedp ov)))
      (rfringe       (setq ov  (bmkp-make/move-fringe 'right pos autonamedp ov)))
      (line+lfringe  (setq ov  (bmkp-make/move-fringe 'left  pos autonamedp ov 'LINEP)))
      (line+rfringe  (setq ov  (bmkp-make/move-fringe 'right pos autonamedp ov 'LINEP)))
      (bol           (if (not ov)
                         (setq ov  (save-excursion (goto-char pos)
                                                   (make-overlay (line-beginning-position)
                                                                 (1+ (line-beginning-position))
                                                                 nil
                                                                 'FRONT-ADVANCE)))
                       (overlay-put ov 'before-string nil) ; Remove any fringe highlighting.
                       (save-excursion (goto-char pos)
                                       (move-overlay ov (line-beginning-position)
                                                     (1+ (line-beginning-position))))))
      (point         (if (not ov)
                         (setq ov  (make-overlay pos (1+ pos) nil 'FRONT-ADVANCE))
                       (overlay-put ov 'before-string nil) ; Remove any fringe highlighting.
                       (move-overlay ov pos (1+ pos))))
      (none          (when ov (delete-overlay ov))  (setq ov nil)))
    ov))

;; Not used for Emacs 20-21.
(defun bmkp-make/move-fringe (side pos autonamedp &optional overlay linep)
  "Return an overlay that uses the fringe.
If SIDE is `right' then use the right fringe, otherwise left.
POS is the overlay position.
AUTONAMEDP: non-nil means use face `bmkp-light-fringe-autonamed'.
            nil means use face `bmkp-light-fringe-non-autonamed'.
If OVERLAY is non-nil it is the overlay to use.
 Otherwise, create a new overlay.
Non-nil LINEP means also highlight the line containing POS."
  (unless (> emacs-major-version 21) (error "Fringe styles not supported before Emacs 22"))
  (let ((ov  overlay))
    (if ov
        (save-excursion (move-overlay overlay (progn (goto-char pos)
                                                     (goto-char (line-beginning-position)))
                                      (1+ (point))))
      (setq ov  (save-excursion (make-overlay (progn (goto-char pos)
                                                     (goto-char (line-beginning-position)))
                                              (1+ (point))
                                              nil
                                              'FRONT-ADVANCE))))
    (overlay-put ov 'before-string (bmkp-fringe-string side autonamedp))
    (if linep
        (move-overlay ov (save-excursion (goto-char pos) (line-beginning-position 1))
                      (save-excursion (goto-char pos) (line-beginning-position 2)))
      (overlay-put ov 'face nil))       ; Remove any non-fringe highlighting.
    ov))

;; Not used for Emacs 20-21.
(defun bmkp-fringe-string (side autonamedp)
  "Return a fringe string for a bookmark overlay.
If SIDE is `right' then use the right fringe, otherwise left.
AUTONAMEDP: non-nil means use face `bmkp-light-fringe-autonamed'.
            nil means use face `bmkp-light-fringe-non-autonamed'."
  (unless (> emacs-major-version 21) (error "Fringe styles not supported before Emacs 22"))
  (let ((fringe-string  (copy-sequence (if autonamedp "*AUTO*" "*NONAUTO*"))))
    (put-text-property 0         (length fringe-string)
                       'display  (if (eq side 'right)
                                     (list 'right-fringe
                                           bmkp-light-right-fringe-bitmap
                                           (if autonamedp
                                               'bmkp-light-fringe-autonamed
                                             'bmkp-light-fringe-non-autonamed))
                                   (list 'left-fringe
                                         bmkp-light-left-fringe-bitmap
                                         (if autonamedp
                                             'bmkp-light-fringe-autonamed
                                           'bmkp-light-fringe-non-autonamed)))
                       fringe-string)
    fringe-string))

;;;;;;;;;;;;;;;;;;;

(provide 'bookmark+-lit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-lit.el ends here
