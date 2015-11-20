;;; bookmark+-mac.el --- Macros for Bookmark+.
;;
;; Filename: bookmark+-mac.el
;; Description: Macros for Bookmark+.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2000-2015, Drew Adams, all rights reserved.
;; Created: Sun Aug 15 11:12:30 2010 (-0700)
;; Last-Updated: Sun Feb 22 14:35:41 2015 (-0800)
;;           By: dradams
;;     Update #: 182
;; URL: http://www.emacswiki.org/bookmark+-mac.el
;; Doc URL: http://www.emacswiki.org/BookmarkPlus
;; Keywords: bookmarks, bookmark+, placeholders, annotations, search, info, url, w3m, gnus
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `bookmark', `pp'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Macros for Bookmark+.
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) library
;;    `bookmark+-mac.el' - Lisp macros (this file)
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (bmenu)
;;    `bookmark+-1.el'   - other (non-bmenu) required code
;;    `bookmark+-lit.el' - (optional) code for highlighting bookmarks
;;    `bookmark+-key.el' - key and menu bindings
;;
;;    `bookmark+-doc.el' - documentation (comment-only file)
;;    `bookmark+-chg.el' - change log (comment-only file)
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
;;
;;
;;    ****** NOTE ******
;;
;;      WHENEVER you update Bookmark+ (i.e., download new versions of
;;      Bookmark+ source files), I recommend that you do the
;;      following:
;;
;;      1. Delete ALL existing BYTE-COMPILED Bookmark+ files
;;         (bookmark+*.elc).
;;      2. Load Bookmark+ (`load-library' or `require').
;;      3. Byte-compile the source files.
;;
;;      In particular, ALWAYS LOAD `bookmark+-mac.el' (not
;;      `bookmark+-mac.elc') BEFORE YOU BYTE-COMPILE new versions of
;;      the files, in case there have been any changes to Lisp macros
;;      (in `bookmark+-mac.el').
;;
;;      (This is standard procedure for Lisp: code that depends on
;;      macros needs to be byte-compiled anew after loading the
;;      updated macros.)
;;
;;    ******************
 
;;(@> "Index")
;;
;;  If you have library `linkd.el' and Emacs 22 or later, load
;;  `linkd.el' and turn on `linkd-mode' now.  It lets you easily
;;  navigate around the sections of this doc.  Linkd mode will
;;  highlight this Index, as well as the cross-references and section
;;  headings throughout this file.  You can get `linkd.el' here:
;;  http://dto.freeshell.org/notebook/Linkd.html.
;;
;;  (@> "Things Defined Here")
;;  (@> "Functions")
;;  (@> "Macros")
 
;;(@* "Things Defined Here")
;;
;;  Things Defined Here
;;  -------------------
;;
;;  Macros defined here:
;;
;;    `bmkp-define-cycle-command',
;;    `bmkp-define-next+prev-cycle-commands',
;;    `bmkp-define-show-only-command', `bmkp-define-sort-command',
;;    `bmkp-define-file-sort-predicate', `bmkp-menu-bar-make-toggle',
;;    `bmkp-with-bookmark-dir', `bmkp-with-help-window',
;;    `bmkp-with-output-to-plain-temp-buffer'.
;;
;;  Non-interactive functions defined here:
;;
;;    `bmkp-bookmark-data-from-record',
;;    `bmkp-bookmark-name-from-record',
;;    `bookmark-name-from-full-record', `bookmark-name-from-record'.
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

(require 'bookmark)
;; bookmark-bmenu-bookmark, bookmark-bmenu-ensure-position,
;; bookmark-bmenu-surreptitiously-rebuild-list, bookmark-get-bookmark,
;; bookmark-get-filename


;; Some general Renamings.
;;
;; 1. Fix incompatibility introduced by gratuitous Emacs name change.
;;
(cond ((and (fboundp 'bookmark-name-from-record) (not (fboundp 'bookmark-name-from-full-record)))
       (defalias 'bookmark-name-from-full-record 'bookmark-name-from-record))
      ((and (fboundp 'bookmark-name-from-full-record) (not (fboundp 'bookmark-name-from-record)))
       (defalias 'bookmark-name-from-record 'bookmark-name-from-full-record)))

;; 2. The vanilla name of the first is misleading, as it returns only the cdr of the record.
;;    The second is for consistency.
;;
(defalias 'bmkp-bookmark-data-from-record 'bookmark-get-bookmark-record)
(defalias 'bmkp-bookmark-name-from-record 'bookmark-name-from-full-record)


;; (eval-when-compile (require 'bookmark+-bmu))
;; bmkp-bmenu-barf-if-not-in-menu-list,
;; bmkp-bmenu-goto-bookmark-named, bmkp-sort-orders-alist

;; (eval-when-compile (require 'bookmark+-1))
;; bmkp-file-bookmark-p, bmkp-float-time, bmkp-local-file-bookmark-p,
;; bmkp-msg-about-sort-order, bmkp-reverse-sort-p, bmkp-sort-comparer
 
;;(@* "Macros")

;;; Macros -----------------------------------------------------------

;; Same as `icicle-with-help-window' in `icicles-mac.el'.
;;;###autoload (autoload 'bmkp-with-help-window "bookmark+")
(defmacro bmkp-with-help-window (buffer &rest body)
  "`with-help-window', if available; else `with-output-to-temp-buffer'."
  (if (fboundp 'with-help-window)
      `(with-help-window ,buffer ,@body)
    `(with-output-to-temp-buffer ,buffer ,@body)))

(put 'bmkp-with-help-window 'common-lisp-indent-function '(4 &body))


;;;###autoload (autoload 'bmkp-with-output-to-plain-temp-buffer "bookmark+")
(defmacro bmkp-with-output-to-plain-temp-buffer (buf &rest body)
  "Like `with-output-to-temp-buffer', but with no `*Help*' navigation stuff."
  `(unwind-protect
    (progn
      (remove-hook 'temp-buffer-setup-hook 'help-mode-setup)
      (remove-hook 'temp-buffer-show-hook  'help-mode-finish)
      (with-output-to-temp-buffer ,buf ,@body))
    (add-hook 'temp-buffer-setup-hook 'help-mode-setup)
    (add-hook 'temp-buffer-show-hook  'help-mode-finish)))

(put 'bmkp-with-output-to-plain-temp-buffer 'common-lisp-indent-function '(4 &body))


;;;###autoload (autoload 'bmkp-define-cycle-command "bookmark+")
(defmacro bmkp-define-cycle-command (type &optional otherp)
  "Define a cycling command for bookmarks of type TYPE.
Non-nil OTHERP means define a command that cycles in another window."
  `(defun ,(intern (format "bmkp-cycle-%s%s" type (if otherp "-other-window" "")))
    (increment &optional startoverp)
    ,(if otherp
         (format "Same as `bmkp-cycle-%s', but use other window." type)
         (format "Cycle through %s bookmarks by INCREMENT (default: 1).
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value

Plain `C-u' also means start over at first bookmark.

In Lisp code:
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist." type))
    (interactive (let ((startovr  (consp current-prefix-arg)))
                   (list (if startovr 1 (prefix-numeric-value current-prefix-arg))
                         startovr)))
    (let ((bmkp-nav-alist  (bmkp-sort-omit (,(intern (format "bmkp-%s-alist-only" type))))))
      (bmkp-cycle increment ,otherp startoverp))))

;;;###autoload (autoload 'bmkp-define-next+prev-cycle-commands "bookmark+")
(defmacro bmkp-define-next+prev-cycle-commands (type)
  "Define `next' and `previous' commands for bookmarks of type TYPE."
  `(progn
    ;; `next' command.
    (defun ,(intern (format "bmkp-next-%s-bookmark" type)) (n &optional startoverp)
      ,(format "Jump to the Nth-next %s bookmark.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle-%s'." type type)
      (interactive (let ((startovr  (consp current-prefix-arg)))
                     (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
      (,(intern (format "bmkp-cycle-%s" type)) n startoverp))

    ;; `previous' command.
    (defun ,(intern (format "bmkp-previous-%s-bookmark" type)) (n &optional startoverp)
      ,(format "Jump to the Nth-previous %s bookmark.
See `bmkp-next-%s-bookmark'." type type)
      (interactive (let ((startovr  (consp current-prefix-arg)))
                     (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
      (,(intern (format "bmkp-cycle-%s" type)) (- n) startoverp))

    ;; `next' repeating command.
    (defun ,(intern (format "bmkp-next-%s-bookmark-repeat" type)) (arg)
      ,(format "Jump to the Nth-next %s bookmark.
This is a repeatable version of `bmkp-next-%s-bookmark'.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one (and no repeat)." type type)
      (interactive "P")
      (require 'repeat)
      (bmkp-repeat-command ',(intern (format "bmkp-next-%s-bookmark" type))))

    ;; `previous repeating command.
    (defun ,(intern (format "bmkp-previous-%s-bookmark-repeat" type)) (arg)
      ,(format "Jump to the Nth-previous %s bookmark.
See `bmkp-next-%s-bookmark-repeat'." type type)
      (interactive "P")
      (require 'repeat)
      (bmkp-repeat-command ',(intern (format "bmkp-previous-%s-bookmark" type))))))

;; We don't bother making this hygienic.  Presumably only the Bookmark+ code will call it.
;;;###autoload (autoload 'bmkp-define-show-only-command "bookmark+")
(defmacro bmkp-define-show-only-command (type doc-string filter-function)
  "Define a command to show only bookmarks of TYPE in *Bookmark List*.
TYPE is a short string or symbol describing the type of bookmarks.

The new command is named `bmkp-bmenu-show-only-TYPED-bookmarks', where
TYPED is TYPE, but with any spaces replaced by hyphens (`-').
Example: `bmkp-bmenu-show-only-tagged-bookmarks', for TYPE `tagged'.

DOC-STRING is the doc string of the new command.

The command shows only the bookmarks allowed by FILTER-FUNCTION.

In case of error, variables `bmkp-bmenu-filter-function',
`bmkp-bmenu-title', and `bmkp-latest-bookmark-alist' are reset to
their values before the command was invoked."
  (unless (stringp type) (setq type  (symbol-name type)))
  (let* ((type--   (bmkp-replace-regexp-in-string "\\s-+" "-" type))
         (command  (intern (format "bmkp-bmenu-show-only-%s-bookmarks" type--))))
    `(progn
      (defun ,command ()
        ,doc-string
        (interactive)
        (bmkp-bmenu-barf-if-not-in-menu-list)
        (let ((orig-filter-fn      bmkp-bmenu-filter-function)
              (orig-title          bmkp-bmenu-title)
              (orig-latest-alist   bmkp-latest-bookmark-alist))
          (condition-case err
              (progn (setq bmkp-bmenu-filter-function  ',filter-function
                           bmkp-bmenu-title            ,(format "%s Bookmarks" (capitalize type)))
                     (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
                       (setq bmkp-latest-bookmark-alist  bookmark-alist)
                       (bookmark-bmenu-list 'filteredp))
                     (when (interactive-p)
                       (bmkp-msg-about-sort-order (bmkp-current-sort-order)
                                                  ,(format "Only %s bookmarks are shown" type))))
            (error (progn (setq bmkp-bmenu-filter-function  orig-filter-fn
                                bmkp-bmenu-title            orig-title
                                bmkp-latest-bookmark-alist  orig-latest-alist)
                          (error "%s" (error-message-string err))))))))))

;;;###autoload (autoload 'bmkp-define-sort-command "bookmark+")
(defmacro bmkp-define-sort-command (sort-order comparer doc-string)
  "Define a command to sort bookmarks in the bookmark list by SORT-ORDER.
SORT-ORDER is a short string or symbol describing the sorting method.
Examples: \"by last access time\", \"by bookmark name\".

The new command is named by replacing any spaces in SORT-ORDER with
hyphens (`-') and then adding the prefix `bmkp-bmenu-sort-'.  Example:
`bmkp-bmenu-sort-by-bookmark-name', for SORT-ORDER `by bookmark name'.

COMPARER compares two bookmarks, returning non-nil if and only if the
first bookmark sorts before the second.  It must be acceptable as a
value of `bmkp-sort-comparer'.  That is, it is either nil, a
predicate, or a list ((PRED...) FINAL-PRED).  See the doc for
`bmkp-sort-comparer'.

DOC-STRING is the doc string of the new command."
  (unless (stringp sort-order) (setq sort-order  (symbol-name sort-order)))
  (let ((command  (intern (concat "bmkp-bmenu-sort-" (bmkp-replace-regexp-in-string
                                                      "\\s-+" "-" sort-order)))))
    `(progn
      (setq bmkp-sort-orders-alist  (bmkp-assoc-delete-all ,sort-order (copy-sequence
                                                                        bmkp-sort-orders-alist)))
      (setq bmkp-sort-orders-alist  (cons (cons ,sort-order ',comparer) bmkp-sort-orders-alist))
      (defun ,command ()
        ,(concat doc-string "\nRepeating this command cycles among normal sort, reversed \
sort, and unsorted.")
        (interactive)
        (bmkp-bmenu-barf-if-not-in-menu-list)
        (cond (;; Not this sort order - make it this sort order.
               (not (equal bmkp-sort-comparer ',comparer))
               (setq bmkp-sort-comparer   ',comparer
                     bmkp-reverse-sort-p  nil))
              (;; Not this sort order reversed - make it reversed.
               (not bmkp-reverse-sort-p)
               (setq bmkp-reverse-sort-p  t))
              (t;; This sort order reversed.  Change to unsorted.
               (setq bmkp-sort-comparer   nil)))
        (message "Sorting...")
        (bookmark-bmenu-ensure-position)
        (let ((current-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list)
          (when current-bmk             ; Should be non-nil, but play safe.
            (bmkp-bmenu-goto-bookmark-named current-bmk))) ; Put cursor back on right line.
        (when (interactive-p)
          (bmkp-msg-about-sort-order
           ,sort-order
           nil
           (cond ((and (not bmkp-reverse-sort-p)
                       (equal bmkp-sort-comparer ',comparer)) "(Repeat: reverse)")
                 ((equal bmkp-sort-comparer ',comparer)       "(Repeat: unsorted)")
                 (t                                           "(Repeat: sort)"))))))))

;;;###autoload (autoload 'bmkp-define-file-sort-predicate "bookmark+")
(defmacro bmkp-define-file-sort-predicate (att-nb)
  "Define a predicate for sorting bookmarks by file attribute ATT-NB.
See function `file-attributes' for the meanings of the various file
attribute numbers.

String attribute values sort alphabetically; numerical values sort
numerically; nil sorts before t.

For ATT-NB 0 (file type), a file sorts before a symlink, which sorts
before a directory.

For ATT-NB 2 or 3 (uid, gid), a numerical value sorts before a string
value.

A bookmark that has file attributes sorts before a bookmark that does
not.  A file bookmark sorts before a non-file bookmark.  Only local
files are tested for attributes - remote-file bookmarks are treated
here like non-file bookmarks."
  `(defun ,(intern (format "bmkp-file-attribute-%d-cp" att-nb)) (b1 b2)
    ,(format "Sort file bookmarks by attribute %d.
Sort bookmarks with file attributes before those without attributes
Sort file bookmarks before non-file bookmarks.
Treat remote file bookmarks like non-file bookmarks.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
             att-nb)
    (setq b1  (bookmark-get-bookmark b1))
    (setq b2  (bookmark-get-bookmark b2))
    (let (a1 a2)
      (cond (;; Both are file bookmarks.
             (and (bmkp-file-bookmark-p b1) (bmkp-file-bookmark-p b2))
             (setq a1  (file-attributes (bookmark-get-filename b1))
                   a2  (file-attributes (bookmark-get-filename b2)))
             (cond (;; Both have attributes.
                    (and a1 a2)
                    (setq a1  (nth ,att-nb a1)
                          a2  (nth ,att-nb a2))
                    ;; Convert times and maybe inode number to floats.
                    ;; The inode conversion is kludgy, but is probably OK in practice.
                    (when (consp a1) (setq a1  (bmkp-float-time a1)))
                    (when (consp a2) (setq a2  (bmkp-float-time a2)))
                    (cond (;; (1) links, (2) maybe uid, (3) maybe gid, (4, 5, 6) times
                           ;; (7) size, (10) inode, (11) device.
                           (numberp a1)
                           (cond ((< a1 a2)  '(t))
                                 ((> a1 a2)  '(nil))
                                 (t          nil)))
                          ((= 0 ,att-nb) ; (0) file (nil) < symlink (string) < dir (t)
                           (cond ((and a2 (not a1))               '(t)) ; file vs (symlink or dir)
                                 ((and a1 (not a2))               '(nil))
                                 ((and (eq t a2) (not (eq t a1))) '(t)) ; symlink vs dir
                                 ((and (eq t a1) (not (eq t a2))) '(t))
                                 ((and (stringp a1) (stringp a2))
                                  (if (string< a1 a2) '(t) '(nil)))
                                 (t                               nil)))
                          ((stringp a1) ; (2, 3) string uid/gid, (8) modes
                           (cond ((string< a1 a2)  '(t))
                                 ((string< a2 a1)  '(nil))
                                 (t                nil)))
                          ((eq ,att-nb 9) ; (9) gid would change if re-created. nil < t
                           (cond ((and a2 (not a1))  '(t))
                                 ((and a1 (not a2))  '(nil))
                                 (t                  nil)))))
                   (;; First has attributes, but not second.
                    a1
                    '(t))
                   (;; Second has attributes, but not first.
                    a2
                    '(nil))
                   (;; Neither has attributes.
                    t
                    nil)))
            (;; First is a file, second is not.
             (bmkp-local-file-bookmark-p b1)
             '(t))
            (;; Second is a file, first is not.
             (bmkp-local-file-bookmark-p b2)
             '(nil))
            (t;; Neither is a file.
             nil)))))

;; This is compatible with Emacs 20 and later.
;;;###autoload (autoload 'bmkp-menu-bar-make-toggle "bookmark+")
(defmacro bmkp-menu-bar-make-toggle (command variable item-name message help
                                     &optional setting-sexp &rest keywords)
  "Define a menu-bar toggle command.
COMMAND (a symbol) is the toggle command to define.
VARIABLE (a symbol) is the variable to set.
ITEM-NAME (a string) is the menu-item name.
MESSAGE is a format string for the toggle message, with %s for the new
 status.
HELP (a string) is the `:help' tooltip text and the doc string first
 line (minus final period) for the command.
SETTING-SEXP is a Lisp sexp that sets VARIABLE, or it is nil meaning
 set it according to its `defcustom' or using `set-default'.
KEYWORDS is a plist for `menu-item' for keywords other than `:help'."
  `(progn
    (defun ,command (&optional interactively)
      ,(concat help ".
In an interactive call, record this option as a candidate for saving
by \"Save Options\" in Custom buffers.")
      (interactive "p")
      (if ,(if setting-sexp
               `,setting-sexp
               `(progn
		 (custom-load-symbol ',variable)
		 (let ((set (or (get ',variable 'custom-set) 'set-default))
		       (get (or (get ',variable 'custom-get) 'default-value)))
		   (funcall set ',variable (not (funcall get ',variable))))))
          (message ,message "enabled globally")
        (message ,message "disabled globally"))
      ;; `customize-mark-as-set' must only be called when a variable is set interactively,
      ;; because the purpose is to mark the variable as a candidate for `Save Options', and we
      ;; do not want to save options that the user has already set explicitly in the init file.
      (when (and interactively  (fboundp 'customize-mark-as-set))
        (customize-mark-as-set ',variable)))
    '(menu-item ,item-name ,command
      :help ,help
      :button (:toggle . (and (default-boundp ',variable) (default-value ',variable)))
      ,@keywords)))

;;; Not used currently.  Provided so you can use it in your own code, if appropriate.
;;;###autoload (autoload 'bmkp-with-bookmark-dir "bookmark+")
(defmacro bmkp-with-bookmark-dir (bookmark &rest body)
  "Evaluate BODY forms with BOOKMARK location as `default-directory'.
If BOOKMARK has no location then use nil as `default-directory'."
  `(let* ((loc                (bookmark-location ,bookmark))
          (default-directory  (and (stringp loc)  (not (member loc (list bmkp-non-file-filename
                                                                    "-- Unknown location --")))
                               (if (file-directory-p loc) loc (file-name-directory loc)))))
    ,@body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'bookmark+-mac)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-mac.el ends here
