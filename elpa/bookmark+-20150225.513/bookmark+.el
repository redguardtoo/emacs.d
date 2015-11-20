;;; bookmark+.el --- Bookmark+: extensions to standard library `bookmark.el'.
;;
;; Filename: bookmark+.el
;; Description: Bookmark+: extensions to standard library `bookmark.el'.
;; Author: Drew Adams, Thierry Volpiatto
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2015, Drew Adams, all rights reserved.
;; Copyright (C) 2009, Thierry Volpiatto, all rights reserved.
;; Created: Fri Sep 15 07:58:41 2000
;; Version: 2015.02.22
;; Last-Updated: Sun Feb 22 14:36:43 2015 (-0800)
;;           By: dradams
;;     Update #: 15030
;; URL: http://www.emacswiki.org/bookmark+.el
;; Doc URL: http://www.emacswiki.org/BookmarkPlus
;; Keywords: bookmarks, bookmark+, projects, placeholders, annotations, search, info, url, w3m, gnus
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `apropos', `apropos+', `avoid', `bookmark', `bookmark+-1',
;;   `bookmark+-bmu', `bookmark+-key', `bookmark+-lit', `cmds-menu',
;;   `ffap', `fit-frame', `frame-fns', `help+20', `info', `info+20',
;;   `menu-bar', `menu-bar+', `misc-cmds', `misc-fns', `naked', `pp',
;;   `pp+', `second-sel', `strings', `thingatpt', `thingatpt+',
;;   `unaccent', `w32browser-dlgopen', `wid-edit', `wid-edit+',
;;   `widget'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Bookmark+: extensions to standard library `bookmark.el'.
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) library (this file)
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit.el' - (optional) code for highlighting bookmarks
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (bmenu)
;;    `bookmark+-1.el'   - other required code (non-bmenu)
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
;;    To report Bookmark+ bugs: `M-x customize-group bookmark-plus'
;;    and then follow (e.g. click) the link `Send Bug Report', which
;;    helps you prepare an email to me.
;;
;;
;;    ****** NOTE ******
;;
;;      Whenever you update Bookmark+ (i.e., download new versions of
;;      Bookmark+ source files), I recommend that you do the
;;      following:
;;
;;      1. Delete all existing byte-compiled Bookmark+ files
;;         (bookmark+*.elc).
;;      2. Load Bookmark+ (`load-library' or `require').
;;      3. Byte-compile the source files.
;;
;;      In particular, always load `bookmark+-mac.el' (not
;;      `bookmark+-mac.elc') before you byte-compile new versions of
;;      the files, in case there have been any changes to Lisp macros
;;      (in `bookmark+-mac.el').
;;
;;    ******************
;;
;;
;;    ****** NOTE ******
;;
;;      On 2010-06-18, I changed the prefix used by package Bookmark+
;;      from `bookmarkp-' to `bmkp-'.  THIS IS AN INCOMPATIBLE CHANGE.
;;      I apologize for the inconvenience, but the new prefix is
;;      preferable for a number of reasons, including easier
;;      distinction from standard `bookmark.el' names.
;;
;;      This change means that YOU MUST MANUALLY REPLACE ALL
;;      OCCURRENCES of `bookmarkp-' by `bmkp-' in the following
;;      places, if you used Bookmark+ prior to this change:
;;
;;      1. In your init file (`~/.emacs') or your `custom-file', if
;;         you have one.  This is needed if you customized any
;;         Bookmark+ features.
;;
;;      2. In your default bookmark file, `bookmark-default-file'
;;         (`~/.emacs.bmk'), and in any other bookmark files you might
;;         have.
;;
;;      3. In your `*Bookmark List*' state file,
;;         `bmkp-bmenu-state-file' (`~/.emacs-bmk-bmenu-state.el').
;;
;;      4. In your `*Bookmark List*' commands file,
;;         `bmkp-bmenu-commands-file' (`~/.emacs-bmk-bmenu-commands.el'),
;;         if you have one.
;;
;;      You can do this editing in a virgin Emacs session (`emacs
;;      -Q'), that is, without loading Bookmark+.
;;
;;      Alternatively, you can do this editing in an Emacs session
;;      where Bookmark+ has been loaded, but in that case you must
;;      TURN OFF AUTOMATIC SAVING of both your default bookmark file
;;      and your `*Bookmark List*' state file.  Otherwise, when you
;;      quit Emacs your manually edits will be overwritten.
;;
;;      To turn off this automatic saving, you can use `M-~' and `M-l'
;;      in buffer `*Bookmark List*' (commands
;;      `bmkp-toggle-saving-bookmark-file' and
;;      `bmkp-toggle-saving-menu-list-state' - they are also in the
;;      `Bookmark+' menu).
;;
;;
;;      Again, sorry for this inconvenience.
;;
;;    ******************
;;
;;
;;  Commands defined here:
;;
;;    `bmkp-version'.
;;
;;  Internal variables defined here:
;;
;;    `bmkp-version-number'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;

(require 'bookmark)                     ; Vanilla Emacs.

;;;###autoload (autoload 'bmkp-version-number "bookmark+")
(defconst bmkp-version-number "2013.04.13")

;;;###autoload (autoload 'bmkp-version "bookmark+")
(defun bmkp-version ()
  "Show version number of library `bookmark+.el'."
  (interactive)
  (message "Bookmark+, version %s" bmkp-version-number))


;; Load Bookmark+ libraries.
;;
(eval-when-compile
 (or (condition-case nil
         (load-library "bookmark+-mac") ; Lisp macros.
       (error nil))                     ; Use load-library to ensure latest .elc.
     (require 'bookmark+-mac)))         ; Require, so can load separately if not on `load-path'.

(require 'bookmark+-lit nil t)          ; Optional (soft require) - no error if not found.  If you do
                                        ; not want to use `bookmark+-lit.el' then simply do not put
                                        ; that file in your `load-path'.
(require 'bookmark+-bmu)                ; `*Bookmark List*' (aka "menu list") stuff.
(require 'bookmark+-1)                  ; Rest of Bookmark+, except keys & menus.
(require 'bookmark+-key)                ; Keys & menus.

;;;;;;;;;;;;;;;;;;;;;;;

(provide 'bookmark+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+.el ends here
