;;; bookmark+-bmu.el --- Bookmark+ code for the `*Bookmark List*' (bmenu).
;;
;; Filename: bookmark+-bmu.el
;; Description: Bookmark+ code for the `*Bookmark List*' (bmenu).
;; Author: Drew Adams, Thierry Volpiatto
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2017, Drew Adams, all rights reserved.
;; Copyright (C) 2009, Thierry Volpiatto, all rights reserved.
;; Created: Mon Jul 12 09:05:21 2010 (-0700)
;; Last-Updated: Fri Oct 27 14:06:30 2017 (-0700)
;;           By: dradams
;;     Update #: 3957
;; URL: https://www.emacswiki.org/emacs/download/bookmark%2b-bmu.el
;; Doc URL: http://www.emacswiki.org/BookmarkPlus
;; Keywords: bookmarks, bookmark+, placeholders, annotations, search, info, url, eww, w3m, gnus
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `apropos', `apropos+', `avoid', `bookmark', `fit-frame',
;;   `frame-fns', `help+20', `info', `info+20', `menu-bar',
;;   `menu-bar+', `misc-cmds', `misc-fns', `naked', `pp',
;;   `second-sel', `strings', `thingatpt', `thingatpt+', `unaccent',
;;   `w32browser-dlgopen', `wid-edit', `wid-edit+', `widget'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    This library contains code for buffer `*Bookmark List*' (mode
;;    `bookmark-bmenu-mode').
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) library
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit.el' - (optional) code for highlighting bookmarks
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (this file)
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
;;  http://www.emacswiki.org/emacs/download/linkd.el.
;;
;;  (@> "Things Defined Here")
;;  (@> "Utility Functions")
;;  (@> "Faces (Customizable)")
;;  (@> "User Options (Customizable)")
;;  (@> "Internal Variables")
;;  (@> "Compatibility Code for Older Emacs Versions")
;;  (@> "Menu List Replacements (`bookmark-bmenu-*')")
;;  (@> "Bookmark+ Functions (`bmkp-*')")
;;    (@> "Menu-List (`*-bmenu-*') Filter Commands")
;;    (@> "Menu-List (`*-bmenu-*') Commands Involving Marks")
;;    (@> "Omitted Bookmarks")
;;    (@> "Search-and-Replace Locations of Marked Bookmarks")
;;    (@> "Tags")
;;    (@> "General Menu-List (`-*bmenu-*') Commands and Functions")
;;    (@> "Sorting - Commands")
;;    (@> "Other Bookmark+ Functions (`bmkp-*')")
;;  (@> "Keymaps")
 
;;(@* "Things Defined Here")
;;
;;  Things Defined Here
;;  -------------------
;;
;;  Commands defined here:
;;
;;    `bmkp-bmenu-add-tags', `bmkp-bmenu-add-tags-to-marked',
;;    `bmkp-bmenu-change-sort-order',
;;    `bmkp-bmenu-change-sort-order-repeat',
;;    `bmkp-bmenu-copy-marked-to-bookmark-file',
;;    `bmkp-bmenu-copy-tags',
;;    `bmkp-bmenu-create-bookmark-file-from-marked',
;;    `bmkp-bmenu-define-command',
;;    `bmkp-bmenu-define-full-snapshot-command',
;;    `bmkp-bmenu-define-jump-marked-command',
;;    `bmkp-bmenu-delete-marked', `bmkp-bmenu-describe-marked',
;;    `bmkp-bmenu-describe-this+move-down',
;;    `bmkp-bmenu-describe-this+move-up',
;;    `bmkp-bmenu-describe-this-bookmark',`bmkp-bmenu-dired-marked',
;;    `bmkp-bmenu-edit-bookmark-name-and-location',
;;    `bmkp-bmenu-filter-annotation-incrementally',
;;    `bmkp-bmenu-filter-bookmark-name-incrementally',
;;    `bmkp-bmenu-filter-file-name-incrementally',
;;    `bmkp-bmenu-filter-tags-incrementally',
;;    `bmkp-bmenu-flag-for-deletion',
;;    `bmkp-bmenu-flag-for-deletion-backwards',
;;    `bmkp-bmenu-isearch-marked-bookmarks' (Emacs 23+),
;;    `bmkp-bmenu-isearch-marked-bookmarks-regexp' (Emacs 23+),
;;    `bmkp-bmenu-jump-to-marked',
;;    `bmkp-bmenu-make-sequence-from-marked', `bmkp-bmenu-mark-all',
;;    `bmkp-bmenu-mark-autofile-bookmarks',
;;    `bmkp-bmenu-mark-bookmark-file-bookmarks',
;;    `bmkp-bmenu-mark-bookmark-list-bookmarks',
;;    `bmkp-bmenu-mark-bookmarks-satisfying',
;;    `bmkp-bmenu-mark-bookmarks-tagged-all',
;;    `bmkp-bmenu-mark-bookmarks-tagged-none',
;;    `bmkp-bmenu-mark-bookmarks-tagged-not-all',
;;    `bmkp-bmenu-mark-bookmarks-tagged-regexp',
;;    `bmkp-bmenu-mark-bookmarks-tagged-some',
;;    `bmkp-bmenu-mark-desktop-bookmarks',
;;    `bmkp-bmenu-mark-dired-bookmarks',
;;    `bmkp-bmenu-mark-eww-bookmarks' (Emacs 25+),
;;    `bmkp-bmenu-mark-file-bookmarks',
;;    `bmkp-bmenu-mark-function-bookmarks',
;;    `bmkp-bmenu-mark-gnus-bookmarks',
;;    `bmkp-bmenu-mark-icicles-search-hits-bookmarks',
;;    `bmkp-bmenu-mark-image-bookmarks',
;;    `bmkp-bmenu-mark-info-bookmarks',
;;    `bmkp-bmenu-mark-lighted-bookmarks',
;;    `bmkp-bmenu-mark-man-bookmarks',
;;    `bmkp-bmenu-mark-non-file-bookmarks',
;;    `bmkp-bmenu-mark-non-invokable-bookmarks',
;;    `bmkp-bmenu-mark-orphaned-local-file-bookmarks',
;;    `bmkp-bmenu-mark-region-bookmarks',
;;    `bmkp-bmenu-mark-snippet-bookmarks',
;;    `bmkp-bmenu-mark-specific-buffer-bookmarks',
;;    `bmkp-bmenu-mark-specific-file-bookmarks',
;;    `bmkp-bmenu-mark-url-bookmarks',
;;    `bmkp-bmenu-mark-variable-list-bookmarks',
;;    `bmkp-bmenu-mark-w3m-bookmarks', `bmkp-bmenu-mouse-3-menu',
;;    `bmkp-bmenu-mode-status-help',
;;    `bmkp-bmenu-move-marked-to-bookmark-file',
;;    `bmkp-bmenu-nb-marked-in-mode-name', `bmkp-bmenu-omit',
;;    `bmkp-bmenu-omit-marked', `bmkp-bmenu-omit/unomit-marked',
;;    `bmkp-bmenu-paste-add-tags',
;;    `bmkp-bmenu-paste-add-tags-to-marked',
;;    `bmkp-bmenu-paste-replace-tags',
;;    `bmkp-bmenu-paste-replace-tags-for-marked',
;;    `bmkp-bmenu-query-replace-marked-bookmarks-regexp',
;;    `bmkp-bmenu-quit', `bmkp-bmenu-refresh-menu-list',
;;    `bmkp-bmenu-regexp-mark', `bookmark-bmenu-relocate' (Emacs 20,
;;    21), `bmkp-bmenu-relocate-marked', `bmkp-bmenu-remove-all-tags',
;;    `bmkp-bmenu-remove-tags', `bmkp-bmenu-remove-tags-from-marked',
;;    `bmkp-bmenu-search-marked-bookmarks-regexp',
;;    `bmkp-bmenu-set-bookmark-file-bookmark-from-marked',
;;    `bmkp-bmenu-set-tag-value',
;;    `bmkp-bmenu-set-tag-value-for-marked', `bmkp-bmenu-show-all',
;;    `bmkp-bmenu-show-only-autofile-bookmarks',
;;    `bmkp-bmenu-show-only-autonamed-bookmarks',
;;    `bmkp-bmenu-show-only-bookmark-file-bookmarks',
;;    `bmkp-bmenu-show-only-bookmark-list-bookmarks',
;;    `bmkp-bmenu-show-only-desktop-bookmarks',
;;    `bmkp-bmenu-show-only-dired-bookmarks',
;;    `bmkp-bmenu-show-only-eww-bookmarks' (Emacs 25+),
;;    `bmkp-bmenu-show-only-file-bookmarks',
;;    `bmkp-bmenu-show-only-function-bookmarks',
;;    `bmkp-bmenu-show-only-gnus-bookmarks',
;;    `bmkp-bmenu-show-only-icicles-search-hits-bookmarks.',
;;    `bmkp-bmenu-show-only-image-bookmarks',
;;    `bmkp-bmenu-show-only-info-bookmarks',
;;    `bmkp-bmenu-show-only-man-bookmarks',
;;    `bmkp-bmenu-show-only-non-file-bookmarks',
;;    `bmkp-bmenu-show-only-non-invokable-bookmarks',
;;    `bmkp-bmenu-show-only-omitted-bookmarks',
;;    `bmkp-bmenu-show-only-orphaned-local-file-bookmarks',
;;    `bmkp-bmenu-show-only-region-bookmarks',
;;    `bmkp-bmenu-show-only-snippet-bookmarks',
;;    `bmkp-bmenu-show-only-specific-buffer-bookmarks',
;;    `bmkp-bmenu-show-only-specific-file-bookmarks',
;;    `bmkp-bmenu-show-only-temporary-bookmarks',
;;    `bmkp-bmenu-show-only-tagged-bookmarks',
;;    `bmkp-bmenu-show-only-untagged-bookmarks',
;;    `bmkp-bmenu-show-only-url-bookmarks',
;;    `bmkp-bmenu-show-only-variable-list-bookmarks',
;;    `bmkp-bmenu-show-only-w3m-bookmarks',
;;    `bmkp-bmenu-show-this-annotation+move-down',
;;    `bmkp-bmenu-show-this-annotation+move-up',
;;    `bmkp-bmenu-sort-by-bookmark-name',
;;    `bmkp-bmenu-sort-by-bookmark-visit-frequency',
;;    `bmkp-bmenu-sort-by-bookmark-type',
;;    `bmkp-bmenu-sort-by-creation-time',
;;    `bmkp-bmenu-sort-by-file-name',
;;    `bmkp-bmenu-sort-by-Gnus-thread',
;;    `bmkp-bmenu-sort-by-Info-node-name',
;;    `bmkp-bmenu-sort-by-Info-position',
;;    `bmkp-bmenu-sort-by-last-bookmark-access',
;;    `bmkp-bmenu-sort-by-last-buffer-or-file-access',
;;    `bmkp-bmenu-sort-by-last-local-file-access',
;;    `bmkp-bmenu-sort-by-last-local-file-update',
;;    `bmkp-bmenu-sort-by-local-file-size',
;;    `bmkp-bmenu-sort-by-local-file-type', `bmkp-bmenu-sort-by-url',
;;    `bmkp-bmenu-sort-flagged-before-unflagged',
;;    `bmkp-bmenu-sort-marked-before-unmarked',
;;    `bmkp-bmenu-sort-modified-before-unmodified',
;;    `bmkp-bmenu-sort-tagged-before-untagged',
;;    `bmkp-bmenu-toggle-marked-temporary/savable',
;;    `bmkp-bmenu-toggle-marks', `bmkp-bmenu-toggle-show-only-marked',
;;    `bmkp-bmenu-toggle-show-only-unmarked',
;;    `bmkp-bmenu-toggle-temporary', `bmkp-bmenu-unmark-all',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-all',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-none',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-not-all',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-regexp',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-some',
;;    `bmkp-bmenu-unomit-marked', `bmkp-bmenu-w32-open',
;;    `bmkp-bmenu-w32-open-select', `bmkp-bmenu-w32-open-with-mouse',
;;    `bmkp-define-tags-sort-command'.
;;
;;  Faces defined here:
;;
;;    `bmkp-*-mark', `bmkp->-mark', `bmkp-a-mark',
;;    `bmkp-bad-bookmark', `bmkp-bookmark-file', `bmkp-bookmark-list',
;;    `bmkp-buffer', `bmkp-D-mark', `bmkp-desktop',
;;    `bmkp-file-handler', `bmkp-function', `bmkp-gnus',
;;    `bmkp-heading', `bmkp-info', `bmkp-local-directory',
;;    `bmkp-local-file-with-region', `bmkp-local-file-without-region',
;;    `bmkp-man', `bmkp-no-jump', `bmkp-no-local', `bmkp-non-file',
;;    `bmkp-remote-file', `bmkp-sequence', `bmkp-snippet',
;;    `bmkp-su-or-sudo', `bmkp-t-mark', `bmkp-url',
;;    `bmkp-variable-list', `bmkp-X-mark'.
;;
;;  User options defined here:
;;
;;    `bmkp-bmenu-commands-file',
;;    `bmkp-bmenu-image-bookmark-icon-file',
;;    `bmkp-bmenu-omitted-bookmarks', `bmkp-bmenu-state-file',
;;    `bmkp-propertize-bookmark-names-flag', `bmkp-sort-orders-alist',
;;    `bmkp-sort-orders-for-cycling-alist'.
;;
;;  Non-interactive functions defined here:
;;
;;    `bmkp-assoc-delete-all', `bmkp-bmenu-barf-if-not-in-menu-list',
;;    `bmkp-bmenu-cancel-incremental-filtering',
;;    `bmkp-bmenu-filter-alist-by-annotation-regexp',
;;    `bmkp-bmenu-filter-alist-by-bookmark-name-regexp',
;;    `bmkp-bmenu-filter-alist-by-file-name-regexp',
;;    `bmkp-bmenu-filter-alist-by-tags-regexp',
;;    `bmkp-bmenu-get-marked-files', `bmkp-bmenu-goto-bookmark-named',
;;    `bmkp-bmenu-kill-annotation', `bmkp-bmenu-list-1',
;;    `bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none',
;;    `bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all',
;;    `bmkp-bmenu-mode-line', `bmkp-bmenu-mode-line-string',
;;    `bmkp-bmenu-propertize-item', `bmkp-bmenu-read-filter-input',
;;    `bmkp-bmenu-store-org-link' (Emacs 24.4+),
;;    `bmkp-bookmark-data-from-record',
;;    `bmkp-bookmark-name-from-record', `bmkp-face-prop',
;;    `bmkp-bmenu-marked-or-this-or-all', `bmkp-looking-at-p',
;;    `bmkp-maybe-unpropertize-bookmark-names',
;;    `bmkp-maybe-unpropertize-string', `bmkp-remap',
;;    `bmkp-replace-regexp-in-string',
;;    `bmkp-reverse-multi-sort-order', `bmkp-reverse-sort-order',
;;    `bmkp-string-match-p', `bookmark-name-from-full-record',
;;    `bookmark-name-from-record',
;;
;;  Internal variables defined here:
;;
;;    `bmkp-bmenu-before-hide-marked-alist',
;;    `bmkp-bmenu-before-hide-unmarked-alist',
;;    `bmkp-bmenu-bookmark-file-menu',
;;    `bmkp-bmenu-define-command-history',
;;    `bmkp-bmenu-define-command-menu', `bmkp-bmenu-delete-menu',
;;    `bmkp-bmenu-filter-function', `bmkp-bmenu-filter-pattern',
;;    `bmkp-bmenu-filter-timer', `bmkp-bmenu-first-time-p',
;;    `bmkp-bmenu-header-lines', `bmkp-bmenu-highlight-menu',
;;    `bmkp-bmenu-line-overlay', `bmkp-bmenu-mark-menu',
;;    `bmkp-bmenu-marked-bookmarks', `bmkp-bmenu-marks-width',
;;    `bmkp-bmenu-mark-types-menu', `bmkp-bmenu-menubar-menu',
;;    `bmkp-bmenu-omit-menu', `bmkp-bmenu-search-menu',
;;    `bmkp-bmenu-show-menu',
;;    `bmkp-bmenu-show-types-menu',`bmkp-bmenu-sort-menu',
;;    `bmkp-bmenu-tags-menu', `bmkp-bmenu-title',
;;    `bmkp-bmenu-toggle-menu', `bmkp-flagged-bookmarks',
;;    `bmkp-last-bmenu-bookmark'.
;;
;;
;;  ***** NOTE: The following commands defined in `bookmark.el'
;;              have been REDEFINED HERE:
;;
;;    `bookmark-bmenu-execute-deletions', `bookmark-bmenu-list',
;;    `bookmark-bmenu-mark', `bookmark-bmenu-1-window',
;;    `bookmark-bmenu-2-window', `bookmark-bmenu-other-window',
;;    `bookmark-bmenu-other-window-with-mouse',
;;    `bookmark-bmenu-rename', `bookmark-bmenu-show-annotation',
;;    `bookmark-bmenu-switch-other-window',
;;    `bookmark-bmenu-this-window', `bookmark-bmenu-toggle-filenames',
;;    `bookmark-bmenu-unmark'.
;;
;;
;;  ***** NOTE: The following non-interactive functions and macros
;;              defined in `bookmark.el' have been REDEFINED HERE:
;;
;;    `bookmark-bmenu-bookmark', `bookmark-bmenu-check-position',
;;    `bookmark-bmenu-delete', `bookmark-bmenu-delete-backwards',
;;    `bookmark-bmenu-ensure-position' (Emacs 23.2+),
;;    `bookmark-bmenu-hide-filenames', `bookmark-bmenu-mode',
;;    `bookmark-bmenu-show-filenames',
;;    `bookmark-bmenu-surreptitiously-rebuild-list',
;;    `with-buffer-modified-unmodified' (Emacs < 23.2).
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

(eval-when-compile (require 'cl)) ;; case (plus, for Emacs 20: dolist, push)
(eval-when-compile (require 'easymenu)) ;; easy-menu-create-menu
(eval-when-compile (require 'org nil t)) ;; org-add-link-type

(require 'bookmark)
;; bookmark-alist, bookmark-bmenu-file-column,
;; bookmark-bmenu-hidden-bookmarks, bookmark-bmenu-mode-map,
;; bookmark-bmenu-select, bookmark-get-annotation,
;; bookmark-get-filename, bookmark-get-handler, bookmark-kill-line,
;; bookmark-maybe-load-default-file, bookmark-name-from-full-record,
;; bookmark-name-from-record, bookmark-prop-get


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


(eval-when-compile
 (or (condition-case nil
         (load-library "bookmark+-mac") ; Use load-library to ensure latest .elc.
       (error nil))
     (require 'bookmark+-mac)))         ; Require, so can load separately if not on `load-path'.
;; bmkp-define-show-only-command, bmkp-define-sort-command, bmkp-menu-bar-make-toggle,
;; bmkp-with-help-window, bmkp-with-output-to-plain-temp-buffer

(put 'bmkp-with-output-to-plain-temp-buffer 'common-lisp-indent-function '(4 &body))


;;; These functions are used in macro `bmkp-define-sort-command'.  The first is used in the macro code
;;; that produces the function code, so its definition is also in `bookmark+-mac.el'.
;;;
(defun bmkp-replace-regexp-in-string (regexp rep string &optional fixedcase literal subexp start)
  "Replace all matches for REGEXP with REP in STRING and return STRING."
  (if (fboundp 'replace-regexp-in-string) ; Emacs > 20.
      (replace-regexp-in-string regexp rep string fixedcase literal subexp start)
    (if (string-match regexp string) (replace-match rep nil nil string) string))) ; Emacs 20

(defun bmkp-assoc-delete-all (key alist)
  "Delete from ALIST all elements whose car is `equal' to KEY.
Return the modified alist.
Elements of ALIST that are not conses are ignored."
  (while (and (consp (car alist)) (equal (car (car alist)) key))  (setq alist  (cdr alist)))
  (let ((tail  alist)
        tail-cdr)
    (while (setq tail-cdr  (cdr tail))
      (if (and (consp (car tail-cdr))  (equal (car (car tail-cdr)) key))
          (setcdr tail (cdr tail-cdr))
        (setq tail  tail-cdr))))
  alist)


;; (eval-when-compile (require 'bookmark+-1))
;; bmkp-add-tags, bmkp-alpha-p, bmkp-bookmark-creation-cp,
;; bmkp-bookmark-description, bmkp-bookmark-file-bookmark-p,
;; bmkp-bookmark-last-access-cp, bmkp-bookmark-list-bookmark-p,
;; bmkp-buffer-last-access-cp, bmkp-completing-read-buffer-name,
;; bmkp-completing-read-file-name, bmkp-current-bookmark-file,
;; bmkp-current-sort-order, bmkp-describe-bookmark,
;; bmkp-describe-bookmark-internals, bmkp-desktop-bookmark-p,
;; bmkp-edit-bookmark-name-and-location, bmkp-file-alpha-cp,
;; bmkp-file-remote-p, bmkp-function-bookmark-p,
;; bookmark-get-bookmark, bmkp-get-buffer-name, bmkp-get-tags,
;; bmkp-gnus-bookmark-p, bmkp-gnus-cp, bmkp-handler-cp,
;; bmkp-incremental-filter-delay, bmkp-image-bookmark-p,
;; bmkp-info-bookmark-p, bmkp-info-node-name-cp,
;; bmkp-info-position-cp, bmkp-isearch-bookmarks,
;; bmkp-isearch-bookmarks-regexp, bmkp-jump-1,
;; bmkp-last-bookmark-file, bmkp-last-specific-buffer,
;; bmkp-last-specific-file, bmkp-latest-bookmark-alist,
;; bmkp-local-file-bookmark-p, bmkp-local-file-type-cp,
;; bmkp-local-file-accessed-more-recently-cp,
;; bmkp-local-file-updated-more-recently-cp,
;; bmkp-set-sequence-bookmark, bmkp-man-bookmark-p,
;; bmkp-marked-bookmark-p, bmkp-marked-bookmarks-only, bmkp-marked-cp,
;; bmkp-msg-about-sort-order, bmkp-non-file-filename,
;; bmkp-read-tag-completing, bmkp-read-tags-completing,
;; bmkp-refresh-menu-list, bmkp-region-bookmark-p,
;; bmkp-remove-all-tags, bmkp-remove-if, bmkp-remove-tags,
;; bmkp-repeat-command, bmkp-reverse-multi-sort-p,
;; bmkp-reverse-sort-p, bmkp-root-or-sudo-logged-p, bmkp-same-file-p,
;; bmkp-save-menu-list-state, bmkp-sequence-bookmark-p,
;; bmkp-set-tag-value, bmkp-set-tag-value-for-bookmarks,
;; bmkp-set-union, bmkp-snippet-alist-only, bmkp-snippet-bookmark-p,
;; bmkp-some, bmkp-some-marked-p, bmkp-some-unmarked-p,
;; bmkp-sort-omit, bmkp-sort-comparer, bmkp-sorted-alist,
;; bmkp-su-or-sudo-regexp, bmkp-tag-name, bmkp-tags-list,
;; bmkp-url-bookmark-p, bmkp-url-cp, bmkp-unmarked-bookmarks-only,
;; bmkp-variable-list-bookmark-p, bmkp-visited-more-cp

;; (eval-when-compile (require 'bookmark+-lit nil t))
;; bmkp-get-lighting

;;;;;;;;;;;;;;;;;;;;;;;

;; Quiet the byte-compiler
(defvar bookmark-file-coding-system)    ; In `bookmark.el' (Emacs 25.2+)
(defvar bmkp-bmenu-highlight-menu)      ; Defined in this file (conditionally).
(defvar bmkp-copied-tags)               ; In `bookmark+-1.el'.
(defvar bmkp-count-multi-mods-as-one-flag) ; In `bookmark+-1.el'.
(defvar bmkp-current-bookmark-file)     ; In `bookmark+-1.el'.
(defvar bmkp-edit-bookmark-orig-record) ; In `bookmark+-1.el'.
(defvar bmkp-incremental-filter-delay)  ; In `bookmark+-1.el'.
(defvar bmkp-edit-bookmark-records-number) ; In `bookmark+-1.el'.
(defvar bmkp-last-bookmark-file)        ; In `bookmark+-1.el'.
(defvar bmkp-last-specific-buffer)      ; In `bookmark+-1.el'.
(defvar bmkp-last-specific-file)        ; In `bookmark+-1.el'.
(defvar bmkp-latest-bookmark-alist)     ; In `bookmark+-1.el'.
(defvar bmkp-modified-bookmarks)        ; In `bookmark+-1.el'.
(defvar bmkp-non-file-filename)         ; In `bookmark+-1.el'.
(defvar bmkp-reverse-multi-sort-p)      ; In `bookmark+-1.el'.
(defvar bmkp-reverse-sort-p)            ; In `bookmark+-1.el'.
(defvar bmkp-sort-comparer)             ; In `bookmark+-1.el'.
(defvar bmkp-sorted-alist)              ; In `bookmark+-1.el'.
(defvar bmkp-sort-orders-alist)         ; Here.
(defvar bmkp-su-or-sudo-regexp)         ; In `bookmark+-1.el'.
(defvar bmkp-temporary-bookmarking-mode) ; In `bookmark+-1.el'.
(defvar dired-re-mark)                  ; In `dired.el'.
(defvar icicle-candidate-properties-alist) ; In `icicles-var.el'.
(defvar minibuffer-prompt-properties)   ; Emacs 22+.
(defvar tramp-file-name-regexp)         ; In `tramp.el'.

 
;;(@* "Utility Functions")
;;; Utility Functions ------------------------------------------------

;; Same as `tap-string-match-p' in `thingatpt+.el' and `icicle-string-match-p' in `icicles-fn.el'.
(if (fboundp 'string-match-p)
    (defalias 'bmkp-string-match-p 'string-match-p) ; Emacs 23+
  (defun bmkp-string-match-p (regexp string &optional start)
    "Like `string-match', but this saves and restores the match data."
    (save-match-data (string-match regexp string start))))

;; Same as `tap-looking-at-p' in `thingatpt+.el' and `icicle-looking-at-p' in `icicles-mcmd.el'.
;; Do not `defalias' to Emacs `looking-at-p' because that is a `defsubst'.
(defun bmkp-looking-at-p (regexp)
  "Like `looking-at', but this saves and restores the match data."
  (save-match-data (looking-at regexp)))

;; Same as `icicle-remap' in `icicles-opt.el'.  Not used yet.
(defun bmkp-remap (old new map &optional oldmap)
  "Bind command NEW in MAP to all keys currently bound to OLD.
If command remapping is available, use that.  Otherwise, bind NEW to
whatever OLD is bound to in MAP, or in OLDMAP, if provided."
  (if (fboundp 'command-remapping)
      (define-key map (vector 'remap old) new) ; Ignore OLDMAP for Emacs 22.
    (substitute-key-definition old new map oldmap)))
 
;;(@* "Faces (Customizable)")
;;; Faces (Customizable) ---------------------------------------------

(defgroup bookmark-plus nil
  "Bookmark enhancements."
  :prefix "bmkp-" :group 'bookmark
  :link `(url-link :tag "Send Bug Report"
          ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
Bookmark+ bug: \
&body=Describe bug here, starting with `emacs -Q'.  \
Don't forget to mention your Emacs and library versions."))
  :link '(url-link :tag "Download" "http://www.emacswiki.org/bookmark+.el")
  :link '(url-link :tag "Description" "http://www.emacswiki.org/BookmarkPlus")
  :link '(emacs-commentary-link :tag "Commentary" "bookmark+"))

(defface bmkp->-mark '((((background dark)) (:foreground "Yellow"))
                       (t (:foreground "Blue")))
  ;; (:foreground "Magenta2" :box (:line-width 1 :style pressed-button))))
  "*Face used for a `>' mark in the bookmark list."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-a-mark '((((background dark)) (:background "SaddleBrown"))
                       (t (:background "SkyBlue")))
  "*Face used for an annotation indicator (`a') in the bookmark list."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-bad-bookmark '((t (:foreground "Red" :background "Chartreuse1")))
  "*Face used for a bookmark that seems to be bad: e.g., nonexistent file."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-bookmark-file
    '((((background dark))
       (:foreground "#00005A5AFFFF" :background "#FFFF9B9BFFFF")) ; ~ blue, ~ pink
      (t (:foreground "Orange" :background "DarkGreen")))
  "*Face used for a bookmark-file bookmark."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-bookmark-list
    '((((background dark)) (:foreground "#7474FFFFFFFF" :background "DimGray")) ; ~ cyan
      (t (:foreground "DarkRed" :background "LightGray")))
  "*Face used for a bookmark-list bookmark."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-buffer
    '((((background dark)) (:foreground "#FFFF9B9BFFFF")) ; ~ pink
      (t (:foreground "DarkGreen")))
  "*Face used for a bookmarked existing buffer not associated with a file."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-D-mark '((t (:foreground "Yellow" :background "Red")))
  "*Face used for a deletion mark (`D') in the bookmark list."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-desktop
    '((((background dark)) (:foreground "Orange" :background "DarkSlateBlue"))
      (t (:foreground "DarkBlue" :background "PaleGoldenrod")))
  "*Face used for a bookmarked desktop."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-file-handler
    '((((background dark)) (:background "#272740402727")) ; ~ dark green
      (t (:background "Thistle")))
  "*Face used for a bookmark that has a `file-handler' attribute."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-function
    '((((background dark)) (:foreground "#0000EBEB6C6C")) ; ~ green
      (t (:foreground "DeepPink1")))
  "*Face used for a function bookmark: a bookmark that invokes a function."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-gnus
    '((((background dark)) (:foreground "Gold"))
      (t (:foreground "DarkBlue")))
  "*Face used for a Gnus bookmark."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-info
    '((((background dark)) (:foreground "#7474FFFFFFFF")) ; ~ light cyan
      (t (:foreground "DarkRed")))
  "*Face used for a bookmarked Info node."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-local-directory
    '((((background dark))
       (:foreground "Pink" :background "DarkBlue"))
      (t (:foreground "DarkBlue" :background "HoneyDew2")))
  "*Face used for a bookmarked local directory."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-local-file-without-region
    '((((background dark)) (:foreground "White"))
      (t (:foreground "Black")))
  "*Face used for a bookmarked local file (without a region)."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-local-file-with-region
    '((((background dark)) (:foreground "Yellow"))
      (t (:foreground "Blue")))
  "*Face used for a region bookmark in a local file."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-man
    '((((background dark)) (:foreground "Orchid"))
      (t (:foreground "Orange4")))
  "*Face used for a `man' page bookmark."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-*-mark '((t (:foreground "Red" :background "Yellow")))
  "*Face used for a modification mark (`*') in the bookmark list."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-no-jump
    '((t (:foreground "gray50")))
  "*Face used for a bookmark you cannot jump to from `*Bookmark List*'."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-no-local
    '((t (:foreground "yellow")))
  "*Face used for a local file bookmark whose target file does not exist."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-non-file
    '((t (:foreground "MediumSeaGreen")))
  "*Face used for a bookmark not associated with an existing buffer."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-remote-file
    '((((background dark)) (:foreground "#6B6BFFFF2C2C")) ; ~ green
      (t (:foreground "DarkViolet")))
  "*Face used for a bookmarked tramp remote file (/ssh:)."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-sequence
    '((((background dark)) (:foreground "DeepSkyBlue"))
      (t (:foreground "DarkOrange2")))
  "*Face used for a sequence bookmark: one composed of other bookmarks."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-snippet
    (if (> emacs-major-version 21)
        '((t (:inherit region)))
      '((t (:background "MediumAquamarine"))))
  "*Face used for a bookmarked snippet."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-su-or-sudo '((t (:foreground "Red")))
  "*Face used for a bookmarked tramp file (/su: or /sudo:)."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-t-mark '((((background dark)) (:foreground "Magenta"))
                       (t (:foreground "#000093F402A2"))) ; a medium green
  "*Face used for a tags mark (`t') in the bookmark list."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-url
    '((((background dark)) (:foreground "#7474FFFF7474")) ; ~ green
      (t (:foreground "DarkMagenta")))
  "*Face used for a bookmarked URL."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-variable-list
    '((((background dark)) (:foreground "#FFFF8D947477")) ; ~ salmon
      (t (:foreground "#0000726B8B8B")))     ; ~dark cyan
  "*Face used for a bookmarked list of variables."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-X-mark '((t (:foreground "Red")))
  "*Face used for a temporary-bookmark indicator (`X') in the bookmark list."
  :group 'bookmark-plus :group 'faces)

;; $$$$$$ Not used now - using `bmkp-url' instead.
;; (defface bmkp-w3m
;;     '((((background dark)) (:foreground "yellow"))
;;       (t (:foreground "DarkMagenta")))
;;   "*Face used for a bookmarked w3m url."
;;   :group 'bookmark-plus :group 'faces)

;; Instead of vanilla `bookmark-menu-heading' (defined in Emacs 22+), to use a better default.
(defface bmkp-heading '((((background dark)) (:foreground "Yellow"))
                        (t (:foreground "Blue")))
  "*Face used to highlight the headings in various Bookmark+ buffers."
  :group 'bookmark-plus :version "22.1" :group 'faces)
 
;;(@* "User Options (Customizable)")
;;; User Options (Customizable) --------------------------------------

;;;###autoload (autoload 'bmkp-bmenu-omitted-bookmarks "bookmark+")
(defcustom bmkp-bmenu-omitted-bookmarks ()
  "*List of names of omitted bookmarks.
They are generally not available for display in the bookmark list.
You can, however, use \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-show-only-omitted-bookmarks]' to see them.
You can then mark some of them and use `\\[bmkp-bmenu-omit/unomit-marked]'
 to make those that are marked available again for the bookmark list."
  ;; $$$$$$ TODO: Create a customize :type `bookmark-name'
  ;;              and provide completion for filling out the field.
  :type '(repeat (string :tag "Bookmark name")) :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-bmenu-commands-file "bookmark+")
(defcustom bmkp-bmenu-commands-file (convert-standard-filename "~/.emacs-bmk-bmenu-commands.el")
  "*File for saving user-defined bookmark-list commands.
This must be an absolute file name (possibly containing `~') or nil
\(it is not expanded).

You can use `\\[bmkp-list-defuns-in-commands-file]' to list the
commands defined in the file and how many times each is defined.

NOTE: Each time you define a command using \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-define-command]', `\\[bmkp-bmenu-define-full-snapshot-command]', \
`\\[bmkp-bmenu-define-jump-marked-command], or `\\[bmkp-define-tags-sort-command]',
it is saved in the file.  The new definition is simply appended to the
file - old definitions of the same command are not overwritten.  So
you might want to clean up the file occasionally, to remove any old,
unused definitions.  This is especially advisable if you used \
`\\[bmkp-bmenu-define-full-snapshot-command]',
because such command definitions can be very large."
  :type '(file  :tag "File for saving menu-list state") :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-bmenu-state-file "bookmark+")
(defcustom bmkp-bmenu-state-file (convert-standard-filename "~/.emacs-bmk-bmenu-state.el")
  "*File for saving `*Bookmark List*' state when you quit bookmark list.
This must be an absolute file name (possibly containing `~') or nil
\(it is not expanded).

The state is also saved when you quit Emacs, even if you don't quit
the bookmark list first (using \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-quit]').

Set this to nil if you do not want to restore the bookmark list as it
was the last time you used it."
  :type '(choice
          (const :tag "Do not save and restore menu-list state" nil)
          (file  :tag "File for saving menu-list state"))
  :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-bmenu-image-bookmark-icon-file "bookmark+")
(defcustom bmkp-bmenu-image-bookmark-icon-file
  (and (fboundp 'display-images-p)  (display-images-p)
       (let ((bmk-img    (convert-standard-filename "~/.emacs-bmk-bmenu-image-file-icon.png"))
             (emacs-img  (convert-standard-filename (concat data-directory "images/gnus/exit-gnus.xpm"))))
         (or (and (file-readable-p bmk-img)    bmk-img)
             (and (file-readable-p emacs-img)  emacs-img))))
  "*Iconic image file to show next to image-file bookmarks.
If nil, show no image.  Otherwise, this is an absolute file name,
possibly containing `~', (the value is not expanded).

Use any image file that Emacs can display, but you probably want to
use a small, iconic image - say 16x16 pixels.

The default image, which you are sure to have in any Emacs version
that supports images, is 24x24 pixels.  That wastes vertical space, so
you probably want to use something smaller.

If you don't have another image that you prefer, try this one (16x16):
http://www.emacswiki.org/emacs/BookmarkPlusImageFileDefaultIcon"
  :type '(choice
          (file  :tag "Use iconic image file")
          (const :tag "Show no image"))
  :group 'bookmark-plus)

;; This is a general option.  It is in this file because it is used mainly by the bmenu code.
(when (> emacs-major-version 20)
  (defcustom bmkp-sort-orders-alist ()
    "*Alist of all available sort functions.
This is a pseudo option - you probably do NOT want to customize this.
Instead:

 * To add a new sort function to this list, use macro
   `bmkp-define-sort-command'.  It defines a new sort function
   and automatically adds it to this list.

 * To have fewer sort orders available for cycling by \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-change-sort-order-repeat]'...,
   customize option `bmkp-sort-orders-for-cycling-alist'.

Each alist element has the form (SORT-ORDER . COMPARER):

 SORT-ORDER is a short string or symbol describing the sort order.
 Examples: \"by last access time\", \"by bookmark name\".

 COMPARER compares two bookmarks.  It must be acceptable as a value of
 `bmkp-sort-comparer'."
    :type '(alist
            :key-type (choice :tag "Sort order" string symbol)
            :value-type (choice
                         (const    :tag "None (do not sort)" nil)
                         (function :tag "Sorting Predicate")
                         (list     :tag "Sorting Multi-Predicate"
                          (repeat (function :tag "Component Predicate"))
                          (choice
                           (const    :tag "None" nil)
                           (function :tag "Final Predicate")))))
    :group 'bookmark-plus))

(unless (> emacs-major-version 20)      ; Emacs 20: custom type `alist' doesn't exist.
  (defcustom bmkp-sort-orders-alist ()
    "*Alist of all available sort functions.
This is a pseudo option - you probably do NOT want to customize this.
Instead:

 * To add a new sort function to this list, use macro
   `bmkp-define-sort-command'.  It defines a new sort function
   and automatically adds it to this list.

 * To have fewer sort orders available for cycling by \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-change-sort-order-repeat]'...,
   customize option `bmkp-sort-orders-for-cycling-alist'.

Each alist element has the form (SORT-ORDER . COMPARER):

 SORT-ORDER is a short string or symbol describing the sort order.
 Examples: \"by last access time\", \"by bookmark name\".

 COMPARER compares two bookmarks.  It must be acceptable as a value of
 `bmkp-sort-comparer'."
    :type '(repeat
            (cons
             (choice :tag "Sort order" string symbol)
             (choice
              (const    :tag "None (do not sort)" nil)
              (function :tag "Sorting Predicate")
              (list     :tag "Sorting Multi-Predicate"
               (repeat (function :tag "Component Predicate"))
               (choice
                (const    :tag "None" nil)
                (function :tag "Final Predicate"))))))
    :group 'bookmark-plus))

(defcustom bmkp-propertize-bookmark-names-flag (> emacs-major-version 20)
  "*Non-nil means to propertize bookmark names to hold full bookmark data.
This means that you can effectively have more than one bookmark with
the same name.

Emacs 20 users: If you need to use your bookmarks with Emacs 20 then
set this to nil.  In particular, if your bookmark file was written
with this as non-nil, then it contains propertized strings which are
unreadable by Emacs 20.  To convert the file to be usable with Emacs
20 you must, in Emacs 21 or later, set this to nil and then do `M-x
bookmark-save'."
  :type 'boolean :group 'bookmark-plus)
 
;;(@* "Internal Variables")
;;; Internal Variables -----------------------------------------------

(defconst bmkp-bmenu-header-lines 5
  "Number of lines used for the `*Bookmark List*' header.")

(defconst bmkp-bmenu-marks-width 4
  "Number of columns (chars) used for the `*Bookmark List*' marks columns.
Bookmark names thus begin in this column number (since zero-based).")


(defvar bmkp-bmenu-before-hide-marked-alist ()
  "Copy of `bookmark-alist' made before hiding marked bookmarks.")

(defvar bmkp-bmenu-before-hide-unmarked-alist ()
  "Copy of `bookmark-alist' made before hiding unmarked bookmarks.")

(defvar bmkp-bmenu-define-command-history ()
  "History of names of commands you have defined for `*Bookmark List*'.")

(defvar bmkp-bmenu-filter-function  nil "Latest filtering function for `*Bookmark List*' display.")

(defvar bmkp-bmenu-filter-pattern "" "Regexp for incremental filtering.")

(defvar bmkp-bmenu-filter-timer nil "Timer used for incremental filtering.")

(defvar bmkp-bmenu-first-time-p t
  "Non-nil means bookmark list has not yet been shown after quitting it.
Quitting the list or the Emacs session resets this to t.
The first time the list is displayed, it is set to nil.")

(defvar bmkp-bmenu-marked-bookmarks ()
  "Names of the marked bookmarks.
This includes possibly omitted bookmarks, that is, bookmarks listed in
`bmkp-bmenu-omitted-bookmarks'.")

(defvar bmkp-bmenu-title "" "Latest title for `*Bookmark List*' display.")

(defvar bmkp-flagged-bookmarks ()
  "Alist of bookmarks that are flagged for deletion in `*Bookmark List*'.")

;; This is a general variable.  It is in this file because it is used only in the bmenu code.
(defvar bmkp-last-bmenu-bookmark nil "The name of the last bookmark current in the bookmark list.")
 
;;(@* "Compatibility Code for Older Emacs Versions")
;;; Compatibility Code for Older Emacs Versions ----------------------

(when (or (< emacs-major-version 23)  (and (= emacs-major-version 23)  (= emacs-minor-version 1)))
  (defmacro with-buffer-modified-unmodified (&rest body)
    "Save and restore `buffer-modified-p' state around BODY."
    (let ((was-modified  (make-symbol "was-modified")))
      `(let ((,was-modified  (buffer-modified-p)))
        (unwind-protect (progn ,@body)
          (set-buffer-modified-p ,was-modified))))))

(when (< emacs-major-version 22)
  (defun bookmark-bmenu-relocate ()
    "Change the file path of the bookmark on the current line,
prompting with completion for the new path."
    (interactive)
    (let ((bmk        (bookmark-bmenu-bookmark))
          (thispoint  (point)))
      (bookmark-relocate bmk)
      (goto-char thispoint))))
 
;;(@* "Menu List Replacements (`bookmark-bmenu-*')")
;;; Menu List Replacements (`bookmark-bmenu-*') ----------------------



;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Return t.  Value doesn't mean anything (didn't anyway), but must be non-nil for vanilla Emacs.
;; 2. Do not count lines.  Just make sure we're on a bookmark line.
;;
(defalias 'bookmark-bmenu-check-position 'bookmark-bmenu-ensure-position)
(defun bookmark-bmenu-ensure-position ()
  "Move to the beginning of the nearest bookmark line."
  (beginning-of-line)
  (unless (bookmark-bmenu-bookmark)
    (if (and (bolp)  (eobp))
        (beginning-of-line 0)
      (goto-char (point-min))
      (forward-line bmkp-bmenu-header-lines)))
  t)                                    ; Older vanilla bookmark code depends on non-nil value.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Add bookmark to `bmkp-bmenu-marked-bookmarks'.  Delete it from `bmkp-flagged-bookmarks'.
;; 2. Don't call `bookmark-bmenu-ensure-position' again at end.
;; 3. Raise error if not in `*Bookmark List*'.
;; 4. Narrower scope for `with-buffer-modified-unmodified' and `let'.
;; 5. If current sort is `s >' (marked first or last), and it was unmarked before, then re-sort.
;; 6. Added optional arg NO-RE-SORT-P to inhibit #5.
;; 7. Added optional arg MSG-P.
;; 8. Call `bmkp-bmenu-mode-line'.
;;
;;;###autoload (autoload 'bookmark-bmenu-mark "bookmark+")
(defun bookmark-bmenu-mark (&optional no-re-sort-p msg-p) ; Bound to `m' in bookmark list
  "Mark the bookmark on this line, using mark `>'.
Add its name to `bmkp-bmenu-marked-bookmarks', after propertizing it
with the full bookmark as `bmkp-full-record'.

If the bookmark was unmarked before, and if the sort order is marked
first or last (`s >'), then re-sort.

Non-interactively:
* Non-nil optional arg NO-RE-SORT-P inhibits re-sorting.
* Non-nil optional arg MSG-P means display a status message."
  (interactive (list nil 'MSG-P))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (beginning-of-line)
  (with-buffer-modified-unmodified
      (let ((inhibit-read-only  t))
        (delete-char 1) (insert ?>) (put-text-property (1- (point)) (point) 'face 'bmkp->-mark)))
  (let* ((bname           (bookmark-bmenu-bookmark))
         (bmk             (bmkp-bookmark-record-from-name bname))
         (was-unmarked-p  nil))
    ;; Put full bookmark on BNAME as property `bmkp-full-record'.
    (put-text-property 0 (length bname) 'bmkp-full-record bmk bname)
    ;; This is the same as `add-to-list' with `eq' (not available for Emacs 20-21).
    (unless (memq bname bmkp-bmenu-marked-bookmarks)
      (setq bmkp-bmenu-marked-bookmarks  (cons bname bmkp-bmenu-marked-bookmarks)
            was-unmarked-p               t))
    (setq bmkp-flagged-bookmarks  (delq bmk bmkp-flagged-bookmarks))
    (unless no-re-sort-p
      ;; If it was unmarked but now is marked, and if sort order is `s >', then re-sort.
      (when (and was-unmarked-p  (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p)))
        (let ((curr-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list (not msg-p))
          (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk))))))
  (forward-line 1)
  (when (fboundp 'bmkp-bmenu-mode-line) (bmkp-bmenu-mode-line)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Remove bookmark from `bmkp-bmenu-marked-bookmarks' and `bmkp-flagged-bookmarks'.
;; 2. Use `bmkp-delete-bookmark-name-from-list', not `delete'.
;; 3. Don't call `bookmark-bmenu-ensure-position' again at end.
;; 4. Raise error if not in `*Bookmark List*'.
;; 5. Narrower scope for `with-buffer-modified-unmodified' and `let'.
;; 6. If current sort is `s >' (marked first or last), and it was marked before, then re-sort.
;; 7. Added optional arg NO-RE-SORT-P to inhibit #6.
;; 8. Added optional arg MSG-P.
;; 9. Call `bmkp-bmenu-mode-line'.
;;
;;;###autoload (autoload 'bookmark-bmenu-unmark "bookmark+")
(defun bookmark-bmenu-unmark (&optional backup no-re-sort-p msg-p) ; Bound to `u' in bookmark list
  "Unmark the bookmark on this line, then move down to the next.
With a prefix argument, move up instead.

If the bookmark was marked before, and if the sort order is marked
first or last (`s >'), then re-sort.

Non-interactively:
* Non-nil optional arg BACKUP (prefix arg) means move up.
* Non-nil optional arg NO-RE-SORT-P inhibits re-sorting.
* Non-nil optional arg MSG-P means display a status message."
  (interactive (list current-prefix-arg nil 'MSG-P))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (beginning-of-line)
  (with-buffer-modified-unmodified
      (let ((inhibit-read-only  t))
        (delete-char 1) (insert " ")))
  (let ((was-marked-p  (memq (bookmark-bmenu-bookmark) bmkp-bmenu-marked-bookmarks)))
    (setq bmkp-bmenu-marked-bookmarks  (bmkp-delete-bookmark-name-from-list
                                        (bookmark-bmenu-bookmark) bmkp-bmenu-marked-bookmarks)
          bmkp-flagged-bookmarks       (delq (bmkp-bookmark-record-from-name (bookmark-bmenu-bookmark))
                                             bmkp-flagged-bookmarks))
    (unless no-re-sort-p
      ;; If it was marked but now is unmarked, and if sort order is `s >', then re-sort.
      (when (and was-marked-p  (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p)))
        (let ((curr-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list (not msg-p))
          (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk))))))
  (forward-line (if backup -1 1))
  (when (fboundp 'bmkp-bmenu-mode-line) (bmkp-bmenu-mode-line)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Do not use `bookmark-bmenu-ensure-position' as a test - it always returns non-nil anyway.
;;    And don't call it again the end.
;; 2. Use `bmkp-delete-bookmark-name-from-list', not `delete'.
;; 3. Use face `bmkp-D-mark' on the `D' flag.
;; 4. Raise error if not in buffer `*Bookmark List*'.
;; 5. Remove bookmark from `bmkp-bmenu-marked-bookmarks'.  Add it to `bmkp-flagged-bookmarks'.
;; 6. Call `bmkp-bmenu-mode-line'.
;;
;;;###autoload (autoload 'bmkp-bmenu-flag-for-deletion "bookmark+")
(defalias 'bmkp-bmenu-flag-for-deletion 'bookmark-bmenu-delete) ; A better name.
;;;###autoload (autoload 'bookmark-bmenu-delete "bookmark+")
(defun bookmark-bmenu-delete ()         ; Bound to `d', `k' in bookmark list
  "Flag this bookmark for deletion, using mark `D'.
Use `\\<bookmark-bmenu-mode-map>\\[bookmark-bmenu-execute-deletions]' to carry out \
the deletions."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (beginning-of-line)
  (bookmark-bmenu-ensure-position)
  (with-buffer-modified-unmodified
      (let ((inhibit-read-only  t))
        (delete-char 1) (insert ?D) (put-text-property (1- (point)) (point) 'face 'bmkp-D-mark)))
  (when (bookmark-bmenu-bookmark)       ; Should never be nil, but just to be safe.
    (setq bmkp-bmenu-marked-bookmarks  (bmkp-delete-bookmark-name-from-list
                                        (bookmark-bmenu-bookmark) bmkp-bmenu-marked-bookmarks))
    ;; This is the same as `add-to-list' with `eq' (not available for Emacs 20-21).
    (let ((bmk  (bmkp-bookmark-record-from-name (bookmark-bmenu-bookmark))))
      (unless (memq bmk bmkp-flagged-bookmarks)
        (setq bmkp-flagged-bookmarks  (cons bmk bmkp-flagged-bookmarks)))))
  (forward-line 1)
  (when (fboundp 'bmkp-bmenu-mode-line) (bmkp-bmenu-mode-line)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Do not move forward another line at end.  Leave point above flagged bookmark.
;;
;;;###autoload (autoload 'bmkp-bmenu-flag-for-deletion-backwards "bookmark+")
(defalias 'bmkp-bmenu-flag-for-deletion-backwards 'bookmark-bmenu-delete-backwards) ; A better name.
;;;###autoload (autoload 'bookmark-bmenu-delete-backwards "bookmark+")
(defun bookmark-bmenu-delete-backwards ()
  "Mark bookmark on this line to be deleted, then move up one line.
To carry out the deletions that you've marked, use \\<bookmark-bmenu-mode-map>\
\\[bookmark-bmenu-execute-deletions]."
  (interactive)
  (bookmark-bmenu-delete)
  (forward-line -2)
  (bookmark-bmenu-ensure-position))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg NO-MSG-P.
;; 2. Rebuild the menu list using the last filtered alist in use, `bmkp-latest-bookmark-alist'.
;; 3. Update the menu-list title.
;;
(defun bookmark-bmenu-surreptitiously-rebuild-list (&optional no-msg-p)
  "Rebuild the bookmark list, if it exists.
Non-nil optional arg NO-MSG-P means do not show progress messages."
  (when (get-buffer "*Bookmark List*")
    (unless no-msg-p (message "Updating bookmark-list display..."))
    (save-excursion (save-window-excursion (let ((bookmark-alist  bmkp-latest-bookmark-alist))
                                             (bookmark-bmenu-list 'filteredp))))
    (unless no-msg-p (message "Updating bookmark-list display...done"))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added arg FILTEREDP.
;; 2. Handles also region bookmarks and buffer (non-file) bookmarks.
;; 3. Uses `pop-to-buffer', not `switch-to-buffer', so we respect `special-display-*'
;;    (but keep `one-window-p' if that's the case).
;; 4. If option `bmkp-bmenu-state-file' is non-nil, then the first time since the last quit
;;     (or the last Emacs session) restores the last menu-list state.
;; 5. If option `bmkp-bmenu-commands-file' is non-nil, then read that file, which contains
;;    user-defined `*Bookmark List*' commands.
;; 6. Many differences in the display itself - see the doc.
;;
;;;###autoload (autoload 'list-bookmarks "bookmark+")
(defalias 'list-bookmarks 'bookmark-bmenu-list)
;;;###autoload (autoload 'bookmark-bmenu-list "bookmark+")
(defun bookmark-bmenu-list (&optional filteredp msg-p) ; Bound to `C-x p e', `C-x r l'
  "Display a list of existing bookmarks, in buffer `*Bookmark List*'.
The leftmost column of a bookmark entry shows `D' if the bookmark is
 flagged for deletion, or `>' if it is marked normally.
The second column shows `t' if the bookmark has tags.
The third  column shows `a' if the bookmark has an annotation.

The following faces are used for the list entries.
Use `customize-face' if you want to change the appearance.

 `bmkp-bad-bookmark', `bmkp-bookmark-file', `bmkp-bookmark-list',
 `bmkp-buffer', `bmkp-desktop', `bmkp-file-handler', `bmkp-function',
 `bmkp-gnus', `bmkp-info', `bmkp-local-directory',
 `bmkp-local-file-without-region', `bmkp-local-file-with-region',
 `bmkp-man', `bmkp-no-jump', `bmkp-no-local', `bmkp-non-file',
 `bmkp-remote-file', `bmkp-sequence', `bmkp-snippet',
 `bmkp-su-or-sudo', `bmkp-url', `bmkp-variable-list'

If option `bmkp-bmenu-state-file' is non-nil then the state of the
displayed bookmark-list is saved when you quit it, and it is restored
when you next use this command.  That saved state is not restored,
however, if it represents a different file from the current bookmark
file.

If you call this interactively when buffer `*Bookmark List*' exists,
that buffer is refreshed to show all current bookmarks, and any
markings are removed.  If you instead want to show the buffer in its
latest state then just do that: use `C-x b' or similar.  If you want
to refresh the displayed buffer, to show the latest state, reflecting
any additions, deletions, renamings, and so on, use \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-refresh-menu-list]'.


Non-interactively:

 - Non-nil optional argument FILTEREDP means the bookmark list has
   been filtered, which means:

   * Use `bmkp-bmenu-title' not the default menu-list title.
   * Do not reset `bmkp-latest-bookmark-alist' to `bookmark-alist'.

 - Non-nil optional arg MSG-P means display progress messages."
  (interactive "i\np")
  (bookmark-maybe-load-default-file)
  (when msg-p (message "Gathering bookmarks to display..."))
  (when (and bmkp-bmenu-first-time-p  bmkp-bmenu-commands-file
             (file-readable-p bmkp-bmenu-commands-file))
    (when (file-directory-p bmkp-bmenu-commands-file)
      (error "`%s' is a directory, not a file" bmkp-bmenu-commands-file))
    (with-current-buffer (let ((enable-local-variables  ())
                               (emacs-lisp-mode-hook    nil))
                           (find-file-noselect bmkp-bmenu-commands-file))
      (goto-char (point-min))
      (while (not (eobp)) (condition-case nil (eval (read (current-buffer))) (error nil)))
      (kill-buffer (current-buffer))))
  (cond ((and bmkp-bmenu-first-time-p  bmkp-bmenu-state-file ; Restore from state file.
              (file-readable-p bmkp-bmenu-state-file))
         (when (file-directory-p bmkp-bmenu-state-file)
           (error "`%s' is a directory, not a file" bmkp-bmenu-state-file))
         (let ((state  ()))
           (with-current-buffer (let ((enable-local-variables  nil)
                                      (emacs-lisp-mode-hook    nil))
                                  (find-file-noselect bmkp-bmenu-state-file))
             (goto-char (point-min))
             (setq state  (condition-case nil (read (current-buffer)) (error nil)))
             (kill-buffer (current-buffer)))
           (let ((last-bookmark-file-from-state  (cdr (assq 'last-bookmark-file state))))
             (when (and (consp state)
                        ;; If bookmark file has changed, then do not use state saved from other file.
                        (or (not last-bookmark-file-from-state)
                            (bmkp-same-file-p last-bookmark-file-from-state
                                              bmkp-current-bookmark-file)))
               (setq bmkp-sort-comparer                (cdr (assq 'last-sort-comparer           state))
                     bmkp-reverse-sort-p               (cdr (assq 'last-reverse-sort-p          state))
                     bmkp-reverse-multi-sort-p         (cdr (assq 'last-reverse-multi-sort-p    state))
                     bmkp-latest-bookmark-alist        (cdr (assq 'last-latest-bookmark-alist   state))
                     bmkp-bmenu-omitted-bookmarks      (cdr (assq 'last-bmenu-omitted-bookmarks state))
                     bmkp-bmenu-marked-bookmarks       (cdr (assq 'last-bmenu-marked-bookmarks  state))
                     bmkp-bmenu-filter-function        (cdr (assq 'last-bmenu-filter-function   state))
                     bmkp-bmenu-filter-pattern         (or (cdr (assq 'last-bmenu-filter-pattern state))
                                                           "")
                     bmkp-bmenu-title                  (cdr (assq 'last-bmenu-title             state))
                     bmkp-last-bmenu-bookmark          (cdr (assq 'last-bmenu-bookmark          state))
                     bmkp-last-specific-buffer         (cdr (assq 'last-specific-buffer         state))
                     bmkp-last-specific-file           (cdr (assq 'last-specific-file           state))
                     bookmark-bmenu-toggle-filenames   (cdr (assq 'last-bmenu-toggle-filenames  state))
                     bmkp-last-bookmark-file           bmkp-current-bookmark-file
                     bmkp-current-bookmark-file        last-bookmark-file-from-state
                     bmkp-bmenu-before-hide-marked-alist
                     (cdr (assq 'last-bmenu-before-hide-marked-alist   state))
                     bmkp-bmenu-before-hide-unmarked-alist
                     (cdr (assq 'last-bmenu-before-hide-unmarked-alist state))))))
         (setq bmkp-bmenu-first-time-p  nil)
         (let ((bookmark-alist  (bmkp-refresh-latest-bookmark-list))) ; This sets *-latest-* also.
           (bmkp-bmenu-list-1 'filteredp nil msg-p))
         ;; Propertize bookmark names if not already propertized (lists saved with Emacs 20 or
         ;; not `bmkp-propertize-bookmark-names-flag').  Check only the first, to guess propertized.
         (when (and (consp bmkp-bmenu-marked-bookmarks)
                    (not (get-text-property 0 'bmkp-full-record (car bmkp-bmenu-marked-bookmarks))))
           (setq bmkp-bmenu-marked-bookmarks
                 (condition-case nil
                     (mapcar (lambda (bname)
                               (if (get-text-property 0 'bmkp-full-record bname)
                                   bname
                                 (put-text-property 0 (length bname) 'bmkp-full-record
                                                    (bmkp-bookmark-record-from-name bname) bname)
                                 bname))
                             bmkp-bmenu-marked-bookmarks)
                   (error ()))))        ; Reset to () if any name is not a current bookmark.
         (when (and (consp bmkp-bmenu-omitted-bookmarks)
                    (not (get-text-property 0 'bmkp-full-record (car bmkp-bmenu-omitted-bookmarks))))
           (setq bmkp-bmenu-omitted-bookmarks
                 (condition-case nil
                     (mapcar (lambda (bname)
                               (if (get-text-property 0 'bmkp-full-record bname)
                                   bname
                                 (put-text-property 0 (length bname) 'bmkp-full-record
                                                    (bmkp-bookmark-record-from-name bname) bname)
                                 bname))
                             bmkp-bmenu-omitted-bookmarks)
                   (error ()))))        ; Reset to () if any name is not a current bookmark.
         (when bmkp-last-bmenu-bookmark
           (with-current-buffer (get-buffer "*Bookmark List*")
             (bmkp-bmenu-goto-bookmark-named bmkp-last-bmenu-bookmark))))
        (t
         (setq bmkp-bmenu-first-time-p  nil)
         (bmkp-bmenu-list-1 filteredp (or msg-p  (not (get-buffer "*Bookmark List*"))) msg-p))))

(defun bmkp-bmenu-list-1 (filteredp reset-p interactivep)
  "Helper for `bookmark-bmenu-list'.
See `bookmark-bmenu-list' for the description of FILTEREDP.
Reset `bmkp-modified-bookmarks' and `bmkp-flagged-bookmarks'.
Non-nil RESET-P means reset `bmkp-bmenu-marked-bookmarks' also.
Non-nil INTERACTIVEP means `bookmark-bmenu-list' was called
 interactively, so pop to bookmark list and communicate sort order."
  (setq bmkp-modified-bookmarks  ()
        bmkp-flagged-bookmarks   ())
  (when reset-p (setq bmkp-bmenu-marked-bookmarks  ()))
;; $$$$$$ Took out 2015/01/22. (unless filteredp (setq bmkp-latest-bookmark-alist  bookmark-alist))
  (if interactivep
      (let ((one-win-p  (one-window-p)))
        (pop-to-buffer (get-buffer-create "*Bookmark List*"))
        (when one-win-p (delete-other-windows)))
    (set-buffer (get-buffer-create "*Bookmark List*")))
  (let* ((inhibit-read-only       t)
         (title                   (if (and filteredp bmkp-bmenu-title  (not (equal "" bmkp-bmenu-title)))
                                      bmkp-bmenu-title
                                    "All Bookmarks"))
         (show-image-file-icon-p  (and (fboundp 'display-images-p)  (display-images-p)
                                       bmkp-bmenu-image-bookmark-icon-file
                                       (file-readable-p bmkp-bmenu-image-bookmark-icon-file))))
    (erase-buffer)
    (when (fboundp 'remove-images) (remove-images (point-min) (point-max)))
    (insert (format "%s\n%s\n" title (make-string (length title) ?-)))
    (add-text-properties (point-min) (point) (bmkp-face-prop 'bmkp-heading))
    (goto-char (point-min))
    (insert (format "Bookmark file:\n%s\n\n" bmkp-current-bookmark-file))
    (forward-line bmkp-bmenu-header-lines)
    (let ((max-width  0)
          name markedp flaggedp tags annotation temporaryp start)
      (setq bmkp-sorted-alist  (bmkp-sort-omit bookmark-alist
                                               (and (not (eq bmkp-bmenu-filter-function
                                                             'bmkp-omitted-alist-only))
                                                    bmkp-bmenu-omitted-bookmarks)))
      (dolist (bmk  bmkp-sorted-alist)
        (setq max-width  (max max-width (string-width (bmkp-bookmark-name-from-record bmk)))))
      (setq max-width  (+ max-width bmkp-bmenu-marks-width))
      (dolist (bmk  bmkp-sorted-alist)
        (setq name        (bmkp-bookmark-name-from-record bmk)
              markedp     (bmkp-marked-bookmark-p bmk)
              flaggedp    (bmkp-flagged-bookmark-p bmk)
              tags        (bmkp-get-tags bmk)
              annotation  (bookmark-get-annotation bmk)
              start       (+ bmkp-bmenu-marks-width (point)))
        (cond (flaggedp (insert "D") (put-text-property (1- (point)) (point) 'face 'bmkp-D-mark))
              (markedp  (insert ">") (put-text-property (1- (point)) (point) 'face 'bmkp->-mark))
              (t        (insert " ")))
        (if (null tags)
            (insert " ")
          (insert "t") (put-text-property (1- (point)) (point) 'face 'bmkp-t-mark))
        (cond ((bmkp-temporary-bookmark-p bmk)
               (insert "X") (put-text-property (1- (point)) (point) 'face 'bmkp-X-mark))
              ((and annotation  (not (string-equal annotation "")))
               (insert "a") (put-text-property (1- (point)) (point) 'face 'bmkp-a-mark))
              (t (insert " ")))
        (if (not (memq bmk bmkp-modified-bookmarks))
            (insert " ")
          (insert "*")
          (put-text-property (1- (point)) (point) 'face 'bmkp-*-mark))
        (when (and (featurep 'bookmark+-lit)  (bmkp-get-lighting bmk)) ; Highlight highlight overrides.
          (put-text-property (1- (point)) (point) 'face 'bmkp-light-mark))
        (when (and (bmkp-image-bookmark-p bmk)  show-image-file-icon-p)
          (let ((image  (create-image bmkp-bmenu-image-bookmark-icon-file nil nil :ascent 95)))
            (when image (put-image image (point)))))
        (insert name)
        (move-to-column max-width t)
        (bmkp-bmenu-propertize-item bmk start (point))
        (insert "\n")))
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (bookmark-bmenu-mode)
    (when (and bookmark-alist  bookmark-bmenu-toggle-filenames)
      (bookmark-bmenu-toggle-filenames t 'NO-MSG-P))
    (when (and (fboundp 'fit-frame-if-one-window)
               (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
      (fit-frame-if-one-window)))
  (when (fboundp 'bmkp-bmenu-mode-line) (bmkp-bmenu-mode-line))
  (when (and interactivep  bmkp-sort-comparer) (bmkp-msg-about-sort-order (bmkp-current-sort-order))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Redefined.
;; 1. Get name of the current bookmark from text property `bmkp-bookmark-name'.
;; 2. Added optional arg FULL, to return full bookmark record.
;; 3. Use `condition-case' in case we're at eob (so cannot advance).
;;
(defun bookmark-bmenu-bookmark (&optional full)
  "Return the name of the bookmark on this line.
Normally, the string returned is propertized with property
`bmkp-full-record', which records the full bookmark record.
Non-nil optional FULL means return the bookmark record, not the name."
  (condition-case nil
      (let ((name  (save-excursion (forward-line 0) (forward-char bmkp-bmenu-marks-width)
                                   (get-text-property (point) 'bmkp-bookmark-name))))
        (if full (get-text-property 0 'bmkp-full-record name) name))
    (error nil)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Mode-line major-mode name is different, and indicates whether in temporary bookmarking minor mode.
;; 2. Doc string is different.
;;
(defun bookmark-bmenu-mode ()
  "Major mode for editing a list of bookmarks.

Each line represents an Emacs bookmark.  Keys without prefix `C-x' are
available only here (in `*Bookmark List*').  Other keys are available
everywhere.

Remember that you can see all bindings for a prefix key by hitting it,
then `C-h'.  E.g., `s C-h' to see keys with prefix `s' (sorting keys).

More bookmarking help below.


Help - Bookmark Info
--------------------

\\<bookmark-bmenu-mode-map>\
\\[bookmark-bmenu-toggle-filenames]\t- Toggle showing filenames next to bookmarks
\\[bmkp-bmenu-describe-this-bookmark]\t- Show information about bookmark       (`C-u': internal form)
\\[bmkp-bmenu-describe-this+move-down]\t- Show the info, then move to next bookmark
\\[bmkp-bmenu-describe-this+move-up]\t- Show the info, then move to previous bookmark
\\[bmkp-bmenu-describe-marked]\t- Show info about the marked bookmarks  (`C-u': internal form)
\\[bookmark-bmenu-locate]\t- Show location of bookmark (in minibuffer)
\\[bmkp-bmenu-show-or-edit-annotation]\t- Show bookmark's annotation            (`C-u': edit it)
\\[bookmark-bmenu-show-all-annotations]\t- Show the annotations of all annotated bookmarks

\\[bmkp-list-defuns-in-commands-file]
\t- List the commands defined in `bmkp-bmenu-commands-file'


Bookmark-List Display (`*Bookmark List*')
-----------------------------------------

\\[bmkp-toggle-saving-menu-list-state]\t- Toggle autosaving bookmark-list display state
\\[bmkp-save-menu-list-state]\t- Save bookmark-list display state

\\[bmkp-bmenu-refresh-menu-list]\t- Refresh display to current bookmark list  (`C-u': from file)
\\[bmkp-bmenu-show-all]\t- Show all bookmarks
\\[bmkp-toggle-bookmark-set-refreshes]
\t- Toggle whether `bookmark-set' refreshes the bookmark list
\\[bmkp-bmenu-mode-status-help]\t- Show this help
\\[bmkp-bmenu-quit]\t- Quit (`*Bookmark List*')


Bookmark Files
--------------

\\[bmkp-toggle-saving-bookmark-file]\t- Toggle autosaving to the current bookmark file
\\[bookmark-bmenu-save]\t- Save bookmarks now     (`C-u': Save As... - prompt for file)

C-u \\[bmkp-bmenu-refresh-menu-list]\t- Revert to bookmarks in the bookmark file    (overwrite load)
\\[bmkp-switch-bookmark-file-create]\t- Switch to a different bookmark file         (overwrite load)
C-u \\[bmkp-switch-bookmark-file-create]\t- Switch back to the previous bookmark file   (overwrite load)
\\[bookmark-bmenu-load]\t- Add bookmarks from a different bookmark file    (extra load)
\\[bmkp-bmenu-load-marked-bookmark-file-bookmarks]\t- Load marked bookmark-file bookmarks             \
\(extra load)

\\[bmkp-bmenu-move-marked-to-bookmark-file]\t- Move the marked bookmarks to a bookmark file
\\[bmkp-bmenu-copy-marked-to-bookmark-file]\t- Copy the marked bookmarks to a bookmark file
\\[bmkp-bmenu-create-bookmark-file-from-marked]\t- Copy the marked bookmarks to a new bookmark file
C-u \\[bmkp-bmenu-create-bookmark-file-from-marked]\t- Same, plus create bookmark-file bookmark for it
\\[bmkp-empty-file]\t- Empty a bookmark file or create a new, empty bookmark file


General
-------

Here:

\\[bmkp-bmenu-dired-marked]\t- Open Dired for the marked file and directory bookmarks
\\[bmkp-bmenu-make-sequence-from-marked]
\t- Create a sequence bookmark from the marked bookmarks
\\[bmkp-temporary-bookmarking-mode]\t- Toggle temporary-only bookmarking (new, empty bookmark file)

Anywhere:

\\<global-map>\
\\[bmkp-toggle-autotemp-on-set]\t- Toggle making bookmarks temporary when setting them
\\[bmkp-set-bookmark-file-bookmark]\t- Create a bookmark to a bookmark file (`j y' to load it)
\\[bmkp-delete-bookmarks]\t- Delete some bookmarks at point or all in buffer
\\[bmkp-make-function-bookmark]\t- Create a function bookmark
\\[bmkp-choose-navlist-of-type]\t- Set the navlist to the bookmarks of a type you choose
\\[bmkp-choose-navlist-from-bookmark-list]\t- Set the navlist to the bookmarks of a \
bookmark-list bookmark
\\[bmkp-navlist-bmenu-list]\t- Open `*Bookmark List*' for bookmarks in navlist
\\[bmkp-this-file/buffer-bmenu-list]\t- Open `*Bookmark List*' for bookmarks in current file/buffer
\\<bookmark-bmenu-mode-map>


Create/Set Bookmarks (anywhere)
--------------------

\\[bmkp-toggle-autonamed-bookmark-set/delete]\t- Set/delete an autonamed bookmark here
\\[bmkp-autofile-set]\t- Set and autoname a bookmark for a file
\\[bmkp-file-target-set]\t- Set a bookmark for a file
\\[bmkp-url-target-set]\t- Set a bookmark for a URL
\\[bmkp-bookmark-set-confirm-overwrite]\t\t- Set a bookmark here
\\[bmkp-set-desktop-bookmark]\t\t- Set a bookmark for the current desktop
\\[bmkp-set-bookmark-file-bookmark]\t\t- Set a bookmark for a bookmark file
\\[bmkp-set-snippet-bookmark]\t- Save the region text as a snippet bookmark


Jump to (Visit) Bookmarks
-------------------------

\\[bookmark-bmenu-this-window]\t- This bookmark in the same window
\\[bookmark-bmenu-other-window]\t- This bookmark in another window
\\[bookmark-bmenu-switch-other-window]\t- This bookmark in other window, without selecting it
\\[bookmark-bmenu-1-window]\t- This bookmark in a full-frame window
\\[bookmark-bmenu-2-window]\t- This bookmark and last-visited bookmark

\\[bmkp-bmenu-jump-to-marked]\t- Bookmarks marked `>', in other windows

Prefix `j' uses another window; prefix `J' reuses this window:

\\[bookmark-jump-other-window]\t- Bookmark by name
\\[bmkp-jump-in-navlist-other-window]\t- Bookmark in the navigation list
\\[bmkp-lighted-jump-other-window]\t- Highlighted bookmark

\\[bmkp-jump-to-type-other-window]\t- Bookmark by type
\\[bmkp-autonamed-jump-other-window]\t- Autonamed bookmark
\\[bmkp-autonamed-this-buffer-jump-other-window]\t- Autonamed bookmark in this buffer
\\[bmkp-temporary-jump-other-window]\t- Temporary bookmark

\\[bmkp-autofile-jump-other-window]\t- Autofile bookmark
\\[bmkp-dired-jump-other-window]\t- Dired bookmark
\\[bmkp-file-jump-other-window]\t- File or directory bookmark
\\[bmkp-dired-this-dir-jump-other-window]\t- Dired bookmark for this dir
\\[bmkp-file-this-dir-jump-other-window]\t- Bookmark for a file or subdir in this dir
\\[bmkp-local-file-jump-other-window]\t- Local-file bookmark
\\[bmkp-remote-file-jump-other-window]\t- Remote-file bookmark
\\[bmkp-non-file-jump-other-window]\t- Non-file (buffer) bookmark

\\[bmkp-desktop-jump]\t- Desktop bookmark
\\[bmkp-bookmark-list-jump]\t- Bookmark-list bookmark
\\[bmkp-bookmark-file-jump]\t- Bookmark-file bookmark

\\[bmkp-region-jump-other-window]\t- Region bookmark (restore region)
\\[bmkp-snippet-to-kill-ring]\t- Snippet bookmark (copy to `kill-ring')
\\[bmkp-image-jump-other-window]\t- Image-file bookmark
\\[bmkp-info-jump-other-window]\t- Info bookmark
\\[bmkp-man-jump-other-window]\t- `man'-page bookmark
\\[bmkp-gnus-jump-other-window]\t- Gnus bookmark
\\[bmkp-url-jump-other-window]\t- URL bookmark
\\[bmkp-variable-list-jump]\t- Variable-list bookmark

\\[bmkp-some-tags-jump-other-window]\t- Bookmark having some tags you specify
\\[bmkp-all-tags-jump-other-window]\t- Bookmark having each tag you specify
\\[bmkp-some-tags-regexp-jump-other-window]\t- Bookmark having a tag that matches a regexp
\\[bmkp-all-tags-regexp-jump-other-window]\t- Bookmark having all its tags match a regexp
\\[bmkp-file-some-tags-jump-other-window]\t- File bookmark having some tags you specify
\\[bmkp-file-all-tags-jump-other-window]\t- File bookmark having each tag you specify
\\[bmkp-file-some-tags-regexp-jump-other-window]\t- File bookmark having a tag that matches a regexp
\\[bmkp-file-all-tags-regexp-jump-other-window]\t- File bookmark having all its tags match a regexp
\\[bmkp-file-this-dir-some-tags-jump-other-window]\t- File in this dir having some tags you specify
\\[bmkp-file-this-dir-all-tags-jump-other-window]\t- File in this dir having each tag you specify
\\[bmkp-file-this-dir-some-tags-regexp-jump-other-window]\t- \
File in this dir having a tag that matches a regexp
\\[bmkp-file-this-dir-all-tags-regexp-jump-other-window]\t- \
File in this dir having all its tags match a regexp


Autonamed Bookmarks
-------------------

\\[bmkp-toggle-autonamed-bookmark-set/delete]\t- Create/delete autonamed bookmark at point
C-u \\[bmkp-toggle-autonamed-bookmark-set/delete]\t- Delete all autonamed bookmarks in current buffer
\\[bmkp-autonamed-jump-other-window]\t\t- Jump to an autonamed bookmark
\\[bmkp-autonamed-this-buffer-jump-other-window]\t\t- Jump to an autonamed bookmark in a given buffer


Cycle Bookmarks (anywhere)
---------------

\\[bmkp-next-bookmark-this-file/buffer-repeat] ...\t- Next bookmark in buffer         (C-x p n, C-x p C-n)
\\[bmkp-previous-bookmark-this-file/buffer-repeat] ...\t- Prev bookmark in buffer         (C-x p p, \
C-x p C-p)
\\[bmkp-next-bookmark-repeat] ...\t- Next bookmark in navlist        (C-x p f, C-x p C-f)
\\[bmkp-previous-bookmark-repeat] ...\t- Prev bookmark in navlist        (C-x p b, C-x p C-b)
\\[bmkp-next-bookmark-w32-repeat] ...\t- MS Windows `Open' next     bookmark in navlist
\\[bmkp-next-bookmark-w32-repeat] ...\t- MS Windows `Open' previous bookmark in navlist
\\[bmkp-next-lighted-this-buffer-repeat]...\t- Next highlighted bookmark in buffer
\\[bmkp-previous-lighted-this-buffer-repeat] ...\t- Prev highlighted bookmark in buffer


Search-and-Replace in Bookmark Targets (here, in sort order)
--------------------------------------

\\[bmkp-bmenu-isearch-marked-bookmarks]\t- Isearch the marked bookmarks            (`C-u': all)
\\[bmkp-bmenu-isearch-marked-bookmarks-regexp]\t- Regexp-isearch the marked bookmarks     (`C-u': all)
\\[bmkp-bmenu-search-marked-bookmarks-regexp]\t- Regexp-search the marked file bookmarks (`C-u': all)
\\[bmkp-bmenu-query-replace-marked-bookmarks-regexp]\t\t- Query-replace the marked file bookmarks


Mark/Unmark Bookmarks
---------------------

\(Mark means `>'.  Flag means `D'.   See also `Tags', below.)

\\[bmkp-bmenu-flag-for-deletion]\t- Flag bookmark `D' for deletion, then move down
\\[bmkp-bmenu-flag-for-deletion-backwards]\t- Flag bookmark `D' for deletion, then move up

\\[bookmark-bmenu-mark]\t- Mark bookmark
\\[bookmark-bmenu-unmark]\t- Unmark bookmark                    (`C-u': move up one line)
\\[bookmark-bmenu-backup-unmark]\t- Unmark previous bookmark (move up, then unmark)

\\[bmkp-bmenu-mark-all]\t- Mark all bookmarks
\\[bmkp-bmenu-regexp-mark]\t- Mark all bookmarks whose names match a regexp
\\[bmkp-bmenu-unmark-all]\t- Unmark all bookmarks              (`C-u': interactive query)
\\[bmkp-bmenu-toggle-marks]\t- Toggle marks: unmark the marked and mark the unmarked

\\[bmkp-bmenu-mark-autofile-bookmarks]\t- Mark autofile bookmarks
\\[bmkp-bmenu-mark-autonamed-bookmarks]\t- Mark autonamed bookmarks
\\[bmkp-bmenu-mark-temporary-bookmarks]\t- Mark temporary bookmarks
\\[bmkp-bmenu-mark-lighted-bookmarks]\t- Mark highlighted bookmarks (requires `bookmark+-lit.el)

\\[bmkp-bmenu-mark-non-file-bookmarks]\t- Mark non-file (i.e. buffer) bookmarks
\\[bmkp-bmenu-mark-dired-bookmarks]\t- Mark Dired bookmarks
\\[bmkp-bmenu-mark-file-bookmarks]\t- Mark file & directory bookmarks          (`C-u': local only)
\\[bmkp-bmenu-mark-gnus-bookmarks]\t- Mark Gnus bookmarks
\\[bmkp-bmenu-mark-info-bookmarks]\t- Mark Info bookmarks
\\[bmkp-bmenu-mark-icicles-search-hits-bookmarks]\t- Mark Icicles search-hits bookmarks
\\[bmkp-bmenu-mark-non-invokable-bookmarks]\t- Mark non-invokable bookmarks
\\[bmkp-bmenu-mark-image-bookmarks]\t- Mark image-file bookmarks
\\[bmkp-bmenu-mark-desktop-bookmarks]\t- Mark desktop bookmarks
\\[bmkp-bmenu-mark-man-bookmarks]\t- Mark `man' page bookmarks (that's `M' twice, not Meta-M)
\\[bmkp-bmenu-mark-orphaned-local-file-bookmarks]\t- Mark orphaned local file/dir bookmarks  (`C-u': \
remote also)
\\[bmkp-bmenu-mark-region-bookmarks]\t- Mark region bookmarks
\\[bmkp-bmenu-mark-function-bookmarks]\t- Mark function bookmarks
\\[bmkp-bmenu-mark-url-bookmarks]\t- Mark URL bookmarks
\\[bmkp-bmenu-mark-variable-list-bookmarks]\t- Mark variable-list bookmarks
\\[bmkp-bmenu-mark-w3m-bookmarks]\t- Mark W3M (URL) bookmarks
\\[bmkp-bmenu-mark-snippet-bookmarks]\t- Mark snippet bookmarks
\\[bmkp-bmenu-mark-bookmark-file-bookmarks]\t- Mark bookmark-file bookmarks
\\[bmkp-bmenu-mark-bookmark-list-bookmarks]\t- Mark bookmark-list bookmarks


Modify, Delete Bookmarks
------------------------

\(See also `Tags', next.)

\\[bmkp-bmenu-edit-bookmark-name-and-location]\t- Rename or relocate bookmark
\\[bookmark-bmenu-relocate]\t- Relocate bookmark
\\[bmkp-bmenu-relocate-marked]\t- Relocate marked bookmarks
\\[bmkp-bmenu-edit-tags]\t- Edit bookmark's tags
C-u \\[bmkp-bmenu-show-or-edit-annotation]\t- Edit bookmark's annotation
\\[bmkp-bmenu-edit-bookmark-record]\t- Edit internal Lisp record for bookmark
\\[bmkp-bmenu-edit-marked]\t- Edit internal Lisp records of marked bookmarks  (`C-u': all)
\\[bmkp-bmenu-toggle-temporary]\t- Toggle temporary/savable status of bookmark
\\[bmkp-bmenu-toggle-marked-temporary/savable]\t- Toggle temporary/savable status of marked bookmarks
\\[bmkp-delete-all-temporary-bookmarks]\t- Delete all temp bookmarks
\\[bookmark-bmenu-execute-deletions]\t- Delete (visible) bookmarks flagged `D'
\\[bmkp-bmenu-delete-marked]\t- Delete (visible) bookmarks marked `>'


Bookmark Tags
-------------

Here:

\\[bmkp-bmenu-copy-tags]\t- Copy tags from this bookmark (for subsequent pasting)
\\[bmkp-bmenu-paste-add-tags]\t- Paste tags (copied from another) to this bookmark
\\[bmkp-bmenu-paste-replace-tags]\t- Replace tags for this bookmark (with those copied)
\\[bmkp-add-tags]\t- Add some tags to a bookmark
\\[bmkp-remove-tags]\t- Remove some tags from a bookmark (`C-u': from all bookmarks)
\\[bmkp-remove-all-tags]\t- Remove all tags from a bookmark
\\[bmkp-remove-tags-from-all]\t- Remove some tags from all bookmarks
\\[bmkp-rename-tag]\t- Rename a tag in all bookmarks
\\[bmkp-list-all-tags]\t- List all tags used in any bookmarks (`C-u': show tag values)
\\[bmkp-bmenu-list-tags-of-marked]\t- List tags used in marked bookmarks  (`C-u': show tag values)
\\[bmkp-bmenu-edit-tags]\t- Edit bookmark's tags
\\[bmkp-bmenu-set-tag-value]\t- Set the value of a tag (as attribute)

\\[bmkp-bmenu-set-tag-value-for-marked]\t- Set value of a tag, for each marked bookmark    (`C-u': all)
\\[bmkp-bmenu-paste-add-tags-to-marked]\t- Add tags copied from a bookmark to those marked (`C-u': all)
\\[bmkp-bmenu-paste-replace-tags-for-marked]\t- Replace tags of marked with copied tags \
        (`C-u': all)
\\[bmkp-bmenu-add-tags-to-marked]\t- Add some tags to the marked bookmarks           (`C-u': all)
\\[bmkp-bmenu-remove-tags-from-marked]\t- Remove some tags from the marked bookmarks      (`C-u': all)

\\[bmkp-bmenu-mark-bookmarks-tagged-regexp]\t- Mark bookmarks having at least one \
tag that matches a regexp
\\[bmkp-bmenu-mark-bookmarks-tagged-some]\t- Mark bookmarks having at least one tag \
in a set    (OR)
\\[bmkp-bmenu-mark-bookmarks-tagged-all]\t- Mark bookmarks having all of the tags \
in a set     (AND)
\\[bmkp-bmenu-mark-bookmarks-tagged-none]\t- Mark bookmarks not having any of the tags \
in a set (NOT OR)
\\[bmkp-bmenu-mark-bookmarks-tagged-not-all]\t- Mark bookmarks not having all of the \
tags in a set (NOT AND)

\\[bmkp-bmenu-unmark-bookmarks-tagged-regexp]\t- Unmark bookmarks having a \
tag that matches a regexp
\\[bmkp-bmenu-unmark-bookmarks-tagged-some]\t- Unmark bookmarks having at least one \
tag in a set  (OR)
\\[bmkp-bmenu-unmark-bookmarks-tagged-all]\t- Unmark bookmarks having all of the tags \
in a set   (AND)
\\[bmkp-bmenu-unmark-bookmarks-tagged-none]\t- Unmark bookmarks not having any tags \
in a set      (NOT OR)
\\[bmkp-bmenu-unmark-bookmarks-tagged-not-all]\t- Unmark bookmarks not having all tags \
in a set      (NOT AND)

Anywhere:

\\<global-map>\
\\[bmkp-list-all-tags]\t- List all tags
\\[bmkp-edit-tags]\t- Edit the tags of a bookmark
\\[bmkp-rename-tag]\t- Rename a tag (everywhere)
\\[bmkp-copy-tags]\t- Copy tags from a bookmark (for subsequent pasting)
\\[bmkp-paste-add-tags]\t- Add (paste) tags copied from a bookmark
\\[bmkp-paste-replace-tags]\t- Replace (paste) a bookmark's tags with copied tags
\\[bmkp-add-tags]\t- Add some tags to a bookmark
\\[bmkp-remove-tags]\t- Remove some tags from a bookmark
\\[bmkp-remove-all-tags]\t- Remove ALL tags from a bookmark
\\[bmkp-remove-tags-from-all]\t- Remove some tags from ALL bookmarks
\\[bmkp-tag-a-file]\t- Add tags to a file (create/update autofile bookmark)
\\[bmkp-untag-a-file]\t- Remove tags from a file (an autofile bookmark)
\\[bmkp-set-tag-value]\t- Set a tag value for a bookmark
\\[bmkp-set-tag-value-for-navlist]\t- Set a tag value for each bookmark in navlist
\\<bookmark-bmenu-mode-map>


Bookmark Highlighting
---------------------

\\[bmkp-bmenu-show-only-lighted-bookmarks]\t- Show only the highlighted bookmarks
\\[bmkp-bmenu-set-lighting]\t- Set highlighting for bookmark
\\[bmkp-bmenu-set-lighting-for-marked]\t- Set highlighting for marked bookmarks
\\[bmkp-bmenu-light]\t- Highlight bookmark
\\[bmkp-bmenu-unlight]\t- Unhighlight bookmark
\\[bmkp-bmenu-mark-lighted-bookmarks]\t- Mark the highlighted bookmarks
\\[bmkp-bmenu-light-marked]\t- Highlight the marked bookmarks
\\[bmkp-bmenu-unlight-marked]\t- Unhighlight the marked bookmarks
\\[bmkp-light-bookmark-this-buffer]\t- Highlight a bookmark in current buffer
\\[bmkp-unlight-bookmark-this-buffer]\t- Unhighlight a bookmark in current buffer
\\[bmkp-light-bookmarks]\t- Highlight bookmarks (see prefix arg)
\\[bmkp-unlight-bookmarks]\t- Unhighlight bookmarks (see prefix arg)
\\[bmkp-bookmarks-lighted-at-point]\t- List bookmarks highlighted at point
\\[bmkp-unlight-bookmark-here]\t- Unhighlight a bookmark at point or on same line
\\[bmkp-lighted-jump-other-window]\t- Jump to a highlighted bookmark (other window)


Sort `*Bookmark List*' (`s C-h' to see this)
----------------------

\(Repeat to cycle normal/reversed/off, except as noted.)

\\[bmkp-reverse-sort-order]\t- Reverse current sort direction       (repeat to toggle)
\\[bmkp-reverse-multi-sort-order]\t- Complement sort predicate decisions  (repeat \
to toggle)
\\[bmkp-bmenu-change-sort-order-repeat]\t- Cycle sort orders                    (repeat \
to cycle)

\\[bmkp-bmenu-sort-marked-before-unmarked]\t- Sort marked (`>') bookmarks first
\\[bmkp-bmenu-sort-flagged-before-unflagged]\t- Sort flagged (`D') bookmarks first
\\[bmkp-bmenu-sort-modified-before-unmodified]\t- Sort modified (`*') bookmarks first
\\[bmkp-bmenu-sort-tagged-before-untagged]\t- Sort tagged (`t') bookmarks first

\\[bmkp-bmenu-sort-by-creation-time]\t- Sort by bookmark creation time
\\[bmkp-bmenu-sort-by-last-buffer-or-file-access]\t- Sort by last buffer or file \
access
\\[bmkp-bmenu-sort-by-last-bookmark-access]\t- Sort by last bookmark access time
\\[bmkp-bmenu-sort-by-Gnus-thread]\t- Sort by Gnus thread: group, article, message
\\[bmkp-bmenu-sort-by-Info-node-name]\t- Sort by Info manual, node, position in node
\\[bmkp-bmenu-sort-by-Info-position]\t- Sort by Info manual, position in manual
\\[bmkp-bmenu-sort-by-bookmark-type]\t- Sort by bookmark type
\\[bmkp-bmenu-sort-by-bookmark-name]\t- Sort by bookmark name
\\[bmkp-bmenu-sort-by-url]\t- Sort by URL
\\[bmkp-bmenu-sort-by-bookmark-visit-frequency]\t- Sort by bookmark visit frequency

\\[bmkp-bmenu-sort-by-last-local-file-access]\t- Sort by last local file access
\\[bmkp-bmenu-sort-by-local-file-type]\t- Sort by local file type: file, symlink, dir
\\[bmkp-bmenu-sort-by-file-name]\t- Sort by file name
\\[bmkp-bmenu-sort-by-local-file-size]\t- Sort by local file size
\\[bmkp-bmenu-sort-by-last-local-file-update]\t- Sort by last local file update (edit)


Hide/Show (`*Bookmark List*')
-----------------------------

\\[bmkp-bmenu-show-all]\t- Show all bookmarks
\\[bmkp-bmenu-toggle-show-only-marked]\t- Toggle showing only marked bookmarks
\\[bmkp-bmenu-toggle-show-only-unmarked]\t- Toggle showing only unmarked bookmarks

\\[bmkp-bmenu-show-only-autonamed-bookmarks]\t- Show only autonamed bookmarks
\\[bmkp-bmenu-show-only-autofile-bookmarks]\t- Show only autofile bookmarks
\\[bmkp-bmenu-show-only-temporary-bookmarks]\t- Show only temporary bookmarks

\\[bmkp-bmenu-show-only-non-file-bookmarks]\t- Show only non-file (i.e. buffer) bookmarks
\\[bmkp-bmenu-show-only-dired-bookmarks]\t- Show only Dired bookmarks
\\[bmkp-bmenu-show-only-file-bookmarks]\t- Show only file & directory bookmarks     (`C-u': local only)
\\[bmkp-bmenu-show-only-gnus-bookmarks]\t- Show only Gnus bookmarks
\\[bmkp-bmenu-show-only-info-bookmarks]\t- Show only Info bookmarks
\\[bmkp-bmenu-show-only-icicles-search-hits-bookmarks]\t- Show only Icicles search-hits bookmarks
\\[bmkp-bmenu-show-only-non-invokable-bookmarks]\t- Show only non-invokable bookmarks
\\[bmkp-bmenu-show-only-image-bookmarks]\t- Show only image-file bookmarks
\\[bmkp-bmenu-show-only-orphaned-local-file-bookmarks]\t- Show only orphaned local file \
bookmarks (`C-u': remote also)
\\[bmkp-bmenu-show-only-desktop-bookmarks]\t- Show only desktop bookmarks
\\[bmkp-bmenu-show-only-man-bookmarks]\t- Show only `man' page bookmarks
\\[bmkp-bmenu-show-only-region-bookmarks]\t- Show only region bookmarks
\\[bmkp-bmenu-show-only-function-bookmarks]\t- Show only function bookmarks
\\[bmkp-bmenu-show-only-url-bookmarks]\t- Show only URL bookmarks
\\[bmkp-bmenu-show-only-eww-bookmarks]\t- Show only EWW (URL) bookmarks
\\[bmkp-bmenu-show-only-w3m-bookmarks]\t- Show only W3M (URL) bookmarks
\\[bmkp-bmenu-show-only-variable-list-bookmarks]\t- Show only variable-list bookmarks
\\[bmkp-bmenu-show-only-tagged-bookmarks]\t- Show only tagged bookmarks
\\[bmkp-bmenu-show-only-untagged-bookmarks]\t- Show only untagged bookmarks
\\[bmkp-bmenu-show-only-snippet-bookmarks]\t- Show only snippet bookmarks
\\[bmkp-bmenu-show-only-bookmark-file-bookmarks]\t- Show only bookmark-file bookmarks
\\[bmkp-bmenu-show-only-bookmark-list-bookmarks]\t- Show only bookmark-list bookmarks

\\[bmkp-bmenu-filter-annotation-incrementally]\t- Incrementally show bookmarks whose \
annotations match regexp
\\[bmkp-bmenu-filter-bookmark-name-incrementally]\t- Incrementally show only bookmarks \
whose names match a regexp
\\[bmkp-bmenu-filter-file-name-incrementally]\t- Incrementally show only bookmarks whose \
files match a regexp
\\[bmkp-bmenu-filter-tags-incrementally]\t- Incrementally show only bookmarks whose tags \
match a regexp


Omit/Un-omit (`*Bookmark List*')
--------------------------------

\\[bmkp-bmenu-show-only-omitted-bookmarks]\t- Show (only) the omitted bookmarks
\\[bmkp-bmenu-show-all]\t- Show the un-omitted bookmarks (all)
\\[bmkp-bmenu-omit/unomit-marked]\t- Omit the marked bookmarks; un-omit them if after \
`\\[bmkp-bmenu-show-only-omitted-bookmarks]'
\\[bmkp-unomit-all]\t- Un-omit all omitted bookmarks


Define Commands for `*Bookmark List*'
-------------------------------------

\\[bmkp-bmenu-define-command]\t- Define a command to restore the current sort order & filter
\\[bmkp-bmenu-define-full-snapshot-command]\t- Define a command to restore current bookmark list
\\[bmkp-define-tags-sort-command]\t- Define a command to sort bookmarks by tags
\\[bmkp-bmenu-define-jump-marked-command]\t- Define a command to jump to a bookmark that is \
now marked


Options for `*Bookmark List*'
-----------------------------

bookmark-bmenu-file-column       - Bookmark width if files are shown
bookmark-bmenu-toggle-filenames  - Show filenames initially?

bmkp-bmenu-omitted-bookmarks     - List of omitted bookmarks
bmkp-bmenu-state-file            - File to save bookmark-list state
                                   (\"home\") nil: do not save/restore
bmkp-sort-comparer               - Initial sort
bmkp-sort-orders-for-cycling-alist - Sort orders that `\\[bmkp-bmenu-change-sort-order-repeat]' ... cycles


Other Options
-------------

bookmark-automatically-show-annotations  - Show annotation when visit?
bookmark-completion-ignore-case  - Case-sensitive completion?
bookmark-default-file            - File to save bookmarks in
bookmark-menu-length             - Max size of bookmark-name menu item
bookmark-save-flag               - Whether and when to save
bookmark-use-annotations         - Query for annotation when saving?
bookmark-version-control         - Numbered backups of bookmark file?

bmkp-autoname-format        - Format of autonamed bookmark name
bmkp-last-as-first-bookmark-file - Whether to start with last b. file
bmkp-crosshairs-flag        - Highlight position when visit?
bmkp-menu-popup-max-length  - Use menus to choose bookmarks?
bmkp-save-new-location-flag - Save if bookmark relocated?
bmkp-sequence-jump-display-function - How to display a sequence
bmkp-sort-comparer          - Predicates for sorting bookmarks
bmkp-su-or-sudo-regexp      - Bounce-show each end of region?
bmkp-this-file/buffer-cycle-sort-comparer -  cycling sort for here
bmkp-use-region             - Activate saved region when visit?"
  (kill-all-local-variables)
  (use-local-map bookmark-bmenu-mode-map)
  (setq truncate-lines    t
        buffer-read-only  t
        major-mode        'bookmark-bmenu-mode
        mode-name         (if bmkp-temporary-bookmarking-mode "TEMPORARY Bookmarking" "Bookmarks"))
  (if (fboundp 'run-mode-hooks)
      (run-mode-hooks 'bookmark-bmenu-mode-hook)
    (run-hooks 'bookmark-bmenu-mode-hook)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Corrected (rewrote).  Toggle var first (unless SHOW).  Call fn according to the var (& to SHOW).
;; 2. Added optional arg NO-MSG-P.
;;
(defun bookmark-bmenu-toggle-filenames (&optional show no-msg-p)
  "Toggle whether filenames are shown in the bookmark list.
Toggle the value of `bookmark-bmenu-toggle-filenames', unless SHOW is
non-nil.
Optional argument SHOW means show them unconditionally.

Non-nil optional arg NO-MSG-P means do not show progress messages."
  (interactive)
  (unless show  (setq bookmark-bmenu-toggle-filenames  (not bookmark-bmenu-toggle-filenames)))
  (let ((bookmark-bmenu-toggle-filenames  (or show  bookmark-bmenu-toggle-filenames)))
    (if bookmark-bmenu-toggle-filenames
        (bookmark-bmenu-show-filenames nil no-msg-p)
      (bookmark-bmenu-hide-filenames nil no-msg-p))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Put `mouse-face' on whole line, with the same help-echo as for the bookmark name.
;; 2. Correct FORCE behavior.
;; 3. Correct doc string.
;; 4. Added optional arg NO-MSG-P and progress message.
;; 5. Fit one-window frame.
;;
(defun bookmark-bmenu-show-filenames (&optional force no-msg-p)
  "Show file names if `bookmark-bmenu-toggle-filenames' is non-nil.
Otherwise do nothing, except non-nil optional argument FORCE has the
same effect as non-nil `bookmark-bmenu-toggle-filenames'.  FORCE is
mainly for debugging.
Non-nil optional arg NO-MSG-P means do not show progress messages."
  (when (or force  bookmark-bmenu-toggle-filenames)
    (unless no-msg-p (message "Showing file names..."))
    (with-buffer-modified-unmodified
        (save-excursion
          (save-window-excursion
            (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
            (setq bookmark-bmenu-hidden-bookmarks  ())
            (let ((inhibit-read-only  t))
              (while (< (point) (point-max))
                (let ((bmk  (bookmark-bmenu-bookmark)))
                  (setq bookmark-bmenu-hidden-bookmarks  (cons bmk bookmark-bmenu-hidden-bookmarks))
                  (move-to-column bookmark-bmenu-file-column t)
                  (delete-region (point) (line-end-position))
                  (insert "  ")
                  (bookmark-insert-location bmk t) ; Pass the NO-HISTORY arg.
                  (when (if (fboundp 'display-color-p) ; Emacs 21+.
                            (and (display-color-p)  (display-mouse-p))
                          window-system)
                    (let ((help  (get-text-property (+ bmkp-bmenu-marks-width (line-beginning-position))
                                                    'help-echo)))
                      (put-text-property (+ bmkp-bmenu-marks-width (line-beginning-position))
                                         (point) 'mouse-face 'highlight)
                      (when help  (put-text-property (+ bmkp-bmenu-marks-width (line-beginning-position))
                                                     (point) 'help-echo help))))
                  (forward-line 1)))))))
    (unless no-msg-p (message "Showing file names...done"))
    (when (and (fboundp 'fit-frame-if-one-window)
               (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
      (fit-frame-if-one-window))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Add text properties when hiding filenames.
;; 2. Do not set or use `bookmark-bmenu-bookmark-column' - use `bmkp-bmenu-marks-width' always.
;; 3. Correct FORCE behavior.
;; 4. Correct doc string.
;; 5. Added optional arg NO-MSG-P and progress message.
;; 6. Fit one-window frame.
;;
(defun bookmark-bmenu-hide-filenames (&optional force no-msg-p)
  "Hide filenames if `bookmark-bmenu-toggle-filenames' is nil.
Otherwise do nothing, except non-nil optional argument FORCE has the
same effect as nil `bookmark-bmenu-toggle-filenames'.  FORCE is mainly
for debugging.
Non-nil optional arg NO-MSG-P means do not show progress messages."
  (when (or force  (not bookmark-bmenu-toggle-filenames))
    (unless no-msg-p (message "Hiding file names..."))
    (with-buffer-modified-unmodified
        (save-excursion
          (save-window-excursion
            (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
            (setq bookmark-bmenu-hidden-bookmarks  (nreverse bookmark-bmenu-hidden-bookmarks))
            (let ((max-width  0))
              (dolist (name  bookmark-bmenu-hidden-bookmarks)
                (setq max-width  (max max-width (string-width name))))
              (setq max-width  (+ max-width bmkp-bmenu-marks-width))
              (save-excursion
                (let ((inhibit-read-only  t))
                  (while bookmark-bmenu-hidden-bookmarks
                    (move-to-column bmkp-bmenu-marks-width t)
                    (bookmark-kill-line)
                    (let ((name   (car bookmark-bmenu-hidden-bookmarks))
                          (start  (point))
                          end)
                      (insert name)
                      (move-to-column max-width t)
                      (setq end  (point))
                      (bmkp-bmenu-propertize-item name start end))
                    (setq bookmark-bmenu-hidden-bookmarks  (cdr bookmark-bmenu-hidden-bookmarks))
                    (forward-line 1))))))))
    (unless no-msg-p (message "Hiding file names...done"))
    (when (and (fboundp 'fit-frame-if-one-window)
               (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
      (fit-frame-if-one-window))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload (autoload 'bookmark-bmenu-1-window "bookmark+")
(defun bookmark-bmenu-1-window (&optional flip-use-region-p) ; Bound to `1' in bookmark list
  "Select this line's bookmark, alone, in full frame.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-jump-1 (bookmark-bmenu-bookmark) 'pop-to-buffer flip-use-region-p)
  (bury-buffer (other-buffer))
  (delete-other-windows))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload (autoload 'bookmark-bmenu-2-window "bookmark+")
(defun bookmark-bmenu-2-window (&optional flip-use-region-p) ; Bound to `2' in bookmark list
  "Select this line's bookmark, with previous buffer in second window.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark-name   (bookmark-bmenu-bookmark))
        (menu            (current-buffer))
        (pop-up-windows  t))
    (delete-other-windows)
    (switch-to-buffer (other-buffer))
    ;; (let ((bookmark-automatically-show-annotations nil)) ; $$$$$$ Needed?
    (bmkp-jump-1 bookmark-name 'pop-to-buffer flip-use-region-p)
    (bury-buffer menu)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload (autoload 'bookmark-bmenu-this-window "bookmark+")
(defun bookmark-bmenu-this-window (&optional flip-use-region-p) ; Bound to `RET' in bookmark list
  "Select this line's bookmark in this window.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark-name  (bookmark-bmenu-bookmark)))
    (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Use `pop-to-buffer', not `switch-to-buffer-other-window'.
;; 2. Prefix arg reverses `bmkp-use-region'.
;; 3. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload (autoload 'bookmark-bmenu-other-window "bookmark+")
(defun bookmark-bmenu-other-window (&optional flip-use-region-p) ; Bound to `o' in bookmark list
  "Select this line's bookmark in other window.  Show `*Bookmark List*' still.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark-name  (bookmark-bmenu-bookmark)))
    ;; (bookmark-automatically-show-annotations  t)) ; $$$$$$ Needed?
    (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload (autoload 'bookmark-bmenu-switch-other-window "bookmark+")
(defun bookmark-bmenu-switch-other-window (&optional flip-use-region-p) ; Bound to `C-o' in bookmark list
  "Make the other window select this line's bookmark.
The current window remains selected.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark-name             (bookmark-bmenu-bookmark))
        (pop-up-windows            t)
        (same-window-buffer-names  ())
        (same-window-regexps       ()))
    ;; (bookmark-automatically-show-annotations t)) ; $$$$$$ Needed?
    (bmkp-jump-1 bookmark-name 'display-buffer flip-use-region-p)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload (autoload 'bookmark-bmenu-other-window-with-mouse "bookmark+")
(defun bookmark-bmenu-other-window-with-mouse (event &optional flip-use-region-p)
  "Select clicked bookmark in other window.  Show `*Bookmark List*' still.
See `bookmark-jump' for info about the prefix arg."
  (interactive "e\nP")
  (with-current-buffer (window-buffer (posn-window (event-end event)))
    (save-excursion (goto-char (posn-point (event-end event)))
                    (bookmark-bmenu-other-window flip-use-region-p))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg MSG-P.
;; 2. Call `bookmark-show-annotation' with arg MSG-P.
;; 3. Raise error if not in buffer `*Bookmark List*'.
;; 4. Doc string reflects enhanced behavior of `bookmark-show-annotation'.
;;
;;;###autoload (autoload 'bookmark-bmenu-show-annotation "bookmark+")
(defun bookmark-bmenu-show-annotation (msg-p) ; Only in `mouse-3' menu.
  "Show the annotation for the current bookmark, or follow it if external.
If the annotation is external then jump to its destination.
Non-interactively, non-nil MSG-P means display messages."
  (interactive "p")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark  (bookmark-bmenu-bookmark))) (bookmark-show-annotation bookmark msg-p)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;;  1. Added optional arg MARKEDP: handle bookmarks marked `>', not just those flagged `D'.
;;  2. Added optional arg NO-CONFIRM-P.
;;  3. Delete bookmark on current line (after confirmation) if none are flagged/marked.
;;  4. Inhibit saving until all are deleted, then save all.  This is because the Bookmark+ version of
;;     `bookmark-save' refreshes the bookmark list display, and that removes `D' flags.
;;  5. Use `bookmark-bmenu-surreptitiously-rebuild-list', instead of using
;;     `bookmark-bmenu-list', updating the modification count, and saving.
;;  6. Update `bmkp-latest-bookmark-alist' to reflect the deletions.
;;  7. Pass full bookmark, not name, to `delete' (and do not use `assoc').
;;  8. Use `bmkp-bmenu-goto-bookmark-named'.
;;  9. Added status messages.
;; 10. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload (autoload 'bookmark-bmenu-execute-deletions "bookmark+")
(defun bookmark-bmenu-execute-deletions (&optional markedp no-confirm-p) ; Bound to `x' in bookmark list
  "Delete (visible) bookmarks flagged `D', without confirmation.
With a prefix argument, delete the bookmarks marked `>' instead, but
only after confirmation.

If NO bookmarks are flagged or marked (depending on whether a prefix
arg was used), then delete the bookmark on this line, but only after
confirmation.

Non-interactively, optional arg NO-CONFIRM-P non-nil means do not ask
for confirmation."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (if (and (null (if markedp bmkp-bmenu-marked-bookmarks bmkp-flagged-bookmarks))
           (bookmark-bmenu-bookmark))
      (if (progn (let ((visible-bell                  t)
                       (minibuffer-prompt-properties  (append minibuffer-prompt-properties
                                                              '(face bmkp-*-mark))))
                   (ding) (ding)
                   (yes-or-no-p "DELETE THIS bookmark ")))
          (bookmark-delete (bookmark-bmenu-bookmark))
        (message "OK, not deleted"))
    (if (or (not markedp)
            no-confirm-p
            (yes-or-no-p "Delete bookmarks marked `>' (not `D') "))
        (let* ((mark-type  (if markedp "^>" "^D"))
               (o-str      (and (not (bmkp-looking-at-p mark-type))  (bookmark-bmenu-bookmark)))
               (o-point    (point))
               (count      0))
          (message "Deleting bookmarks...")
          (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
          (while (re-search-forward mark-type (point-max) t)
            (let* ((bmk-name  (bookmark-bmenu-bookmark))
                   (bmk       (bookmark-get-bookmark bmk-name)))
              ;; Inhibit saving until all are deleted, then do it once.  Otherwise, some might not be
              ;; deleted, because `bookmark-save' refreshes the list, which removes `D' flags.
              (let ((bookmark-save-flag  nil))  (bookmark-delete bmk-name 'BATCHP))
              ;; Count is misleading if the bookmark is not really in `bookmark-alist'.
              (setq count                       (1+ count)
                    bmkp-latest-bookmark-alist  (delete bmk bmkp-latest-bookmark-alist))))
          (bmkp-maybe-save-bookmarks)   ; Do it now.
          (if (<= count 0)
              (message (if markedp "No marked bookmarks" "No bookmarks flagged for deletion"))
            (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
            (message "Deleted %d bookmarks" count))
          (if o-str
              (bmkp-bmenu-goto-bookmark-named o-str)
            (goto-char o-point)
            (beginning-of-line)))
      (message "OK, nothing deleted"))))



;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Do not call `bookmark-bmenu-list' (it was already called).
;; 2. Raise error if not in buffer `*Bookmark List*'.
;; 3. Use `bmkp-bmenu-goto-bookmark-named' instead of just searching for name.
;;
;;;###autoload (autoload 'bookmark-bmenu-rename "bookmark+")
(defun bookmark-bmenu-rename ()         ; Bound to `r' in bookmark list
  "Rename bookmark on current line.  Prompts for a new name."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((newname  (bookmark-rename (bookmark-bmenu-bookmark)))) (bmkp-bmenu-goto-bookmark-named newname)))
 
;;(@* "Bookmark+ Functions (`bmkp-*')")
;;; Bookmark+ Functions (`bmkp-*') -----------------------------------


;;(@* "Menu-List (`*-bmenu-*') Filter Commands")
;;  *** Menu-List (`*-bmenu-*') Filter Commands ***

;; `bmkp-bmenu-show-only-autonamed-bookmarks',
;; `bmkp-bmenu-show-only-non-file-bookmarks',
;; `bmkp-bmenu-show-only-dired-bookmarks',
;; `bmkp-bmenu-show-only-eww-bookmarks' (Emacs 25+),
;; `bmkp-bmenu-show-only-function-bookmarks',
;; `bmkp-bmenu-show-only-gnus-bookmarks',
;; `bmkp-bmenu-show-only-icicles-search-hits-bookmarks',
;; `bmkp-bmenu-show-only-non-invokable-bookmarks',
;; `bmkp-bmenu-show-only-image-bookmarks',
;; `bmkp-bmenu-show-only-info-bookmarks',
;; `bmkp-bmenu-show-only-desktop-bookmarks',
;; `bmkp-bmenu-show-only-man-bookmarks',
;; `bmkp-bmenu-show-only-region-bookmarks',
;; `bmkp-bmenu-show-only-tagged-bookmarks',
;; `bmkp-bmenu-show-only-untagged-bookmarks',
;; `bmkp-bmenu-show-only-url-bookmarks',
;; `bmkp-bmenu-show-only-variable-list-bookmarks',
;; `bmkp-bmenu-show-only-snippet-bookmarks',
;; `bmkp-bmenu-show-only-w3m-bookmarks',
;; `bmkp-bmenu-show-only-temporary-bookmarks',
;; `bmkp-bmenu-show-only-bookmark-file-bookmarks',
;; `bmkp-bmenu-show-only-bookmark-list-bookmarks',


;; The simple ones are defined using macro `bmkp-define-show-only-command'.
;;
;;;###autoload (autoload 'bmkp-bmenu-show-only-autonamed-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-non-file-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-dired-bookmarks "bookmark+")

;; ;;;###autoload (autoload 'bmkp-bmenu-show-only-eww-bookmarks "bookmark+")

;;;###autoload (autoload 'bmkp-bmenu-show-only-function-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-gnus-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-icicles-search-hits-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-non-invokable-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-image-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-info-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-desktop-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-man-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-region-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-tagged-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-untagged-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-url-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-variable-list-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-snippet-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-w3m-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-temporary-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-bookmark-file-bookmarks "bookmark+")
;;;###autoload (autoload 'bmkp-bmenu-show-only-bookmark-list-bookmarks "bookmark+")

;; Bindings indicated are in `*Bookmark List*'.
(bmkp-define-show-only-command autonamed "Display (only) the autonamed bookmarks."
                               bmkp-autonamed-alist-only)                                     ; `# S'
(bmkp-define-show-only-command non-file "Display (only) the non-file (buffer) bookmarks."
                               bmkp-non-file-alist-only)                                      ; `B S'
(bmkp-define-show-only-command dired "Display (only) the Dired bookmarks."
                               bmkp-dired-alist-only)                                         ; `M-d M-s'
(bmkp-define-show-only-command gnus "Display (only) the gnus bookmarks."
                               bmkp-gnus-alist-only)                                          ; `G S'
(bmkp-define-show-only-command "icicles search-hits" "Display (only) the Icicles search-hits bookmarks."
                               bmkp-icicles-search-hits-alist-only)                           ; `i S'
(bmkp-define-show-only-command image "Display (only) the image-file bookmarks."
                               bmkp-image-alist-only)                                         ; `M-I M-S'
(bmkp-define-show-only-command info "Display (only) the Info bookmarks."
                               bmkp-info-alist-only)                                          ; `I S'
(bmkp-define-show-only-command desktop  "Display (only) the desktop bookmarks."
                               bmkp-desktop-alist-only)                                       ; `K S'
(bmkp-define-show-only-command man-page "Display (only) the `man' page bookmarks."
                               bmkp-man-alist-only)                                           ; `M S'
(bmkp-define-show-only-command function "Display (only) the function bookmarks."
                               bmkp-function-alist-only)                                      ; `Q S'
(bmkp-define-show-only-command region "Display (only) the bookmarks that record a region."
                               bmkp-region-alist-only)                                        ; `R S'
(bmkp-define-show-only-command tagged "Display (only) the bookmarks that have tags."
                               bmkp-tagged-alist-only)                                        ; `T S'
(bmkp-define-show-only-command untagged "Display (only) the bookmarks that do not have tags."
                               bmkp-untagged-alist-only)                                      ; Not bound
(bmkp-define-show-only-command url "Display (only) the url bookmarks."
                               bmkp-url-alist-only)                                           ; `M-u M-s'
(bmkp-define-show-only-command variable-list "Display (only) the variable-list bookmarks."
                               bmkp-variable-list-alist-only)                                 ; `V S'
(bmkp-define-show-only-command snippet "Display (only) the snippet bookmarks."
                               bmkp-snippet-alist-only)                                       ; `w S'
(when (fboundp 'bmkp-eww-bookmark-p)    ; Emacs 25+
  (bmkp-define-show-only-command eww "Display (only) the EWW URL bookmarks."
                                 bmkp-eww-alist-only))                                        ; `W E S'
(bmkp-define-show-only-command w3m "Display (only) the W3M URL bookmarks."
                               bmkp-w3m-alist-only)                                           ; `W 3 S'
(bmkp-define-show-only-command temporary "Display (only) the temporary bookmarks."
                               bmkp-temporary-alist-only)                                     ; `X S'
(bmkp-define-show-only-command bookmark-file "Display (only) the bookmark-file bookmarks."
                               bmkp-bookmark-file-alist-only)                                 ; `Y S'
(bmkp-define-show-only-command bookmark-list  "Display (only) the bookmark-list bookmarks."
                               bmkp-bookmark-list-alist-only)                                 ; `Z S'

;;;###autoload (autoload 'bmkp-bmenu-show-all "bookmark+")
(defun bmkp-bmenu-show-all ()           ; Bound to `.' in bookmark list
  "Show all bookmarks known to the bookmark list (aka \"menu list\").
Omitted bookmarks are not shown, however.
Also, this does not revert the bookmark list, to bring it up to date.
To revert the display from the current list, use `\\<bookmark-bmenu-mode-map>\
\\[bmkp-bmenu-refresh-menu-list]'.
To revert the list and display from the bookmark file, use `C-u \\[bmkp-bmenu-refresh-menu-list]'."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  nil
        bmkp-bmenu-title            "All Bookmarks"
        bmkp-latest-bookmark-alist  bookmark-alist)
  (bookmark-bmenu-list)
  (when (interactive-p) (bmkp-msg-about-sort-order (bmkp-current-sort-order) "All bookmarks are shown")))

;;;###autoload (autoload 'bmkp-bmenu-show-only-autofile-bookmarks "bookmark+")
(defun bmkp-bmenu-show-only-autofile-bookmarks (&optional arg) ; Bound to `A S' in bookmark list
  "Display (only) the autofile bookmarks.
This means bookmarks whose names are the same as their (non-directory)
file names.  But with a prefix arg you are prompted for a prefix that
each bookmark name must have."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  (if (not arg)
                                        'bmkp-autofile-alist-only
                                      (let ((prefix  (read-string "Prefix for bookmark names: "
                                                                  nil nil "")))
                                        `(lambda () (bmkp-autofile-alist-only ,prefix))))
        bmkp-bmenu-title            "Autofile Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only autofile bookmarks are shown")))

;;;###autoload (autoload 'bmkp-bmenu-show-only-file-bookmarks "bookmark+")
(defun bmkp-bmenu-show-only-file-bookmarks (&optional arg) ; Bound to `F S' in bookmark list
  "Display a list of file and directory bookmarks (only).
With a prefix argument, do not include remote files or directories."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  (if arg 'bmkp-local-file-alist-only 'bmkp-file-alist-only)
        bmkp-bmenu-title            (if arg
                                        "Local File and Directory Bookmarks"
                                      "File and Directory Bookmarks"))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only file bookmarks are shown")))

;;;###autoload (autoload 'bmkp-bmenu-show-only-orphaned-local-file-bookmarks "bookmark+")
(defun bmkp-bmenu-show-only-orphaned-local-file-bookmarks (&optional arg) ; `O S' in bookmark list
  "Display a list of orphaned local file and directory bookmarks (only).
With a prefix argument, include remote orphans as well."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  (if arg
                                        'bmkp-orphaned-file-alist-only
                                      'bmkp-orphaned-local-file-alist-only)
        bmkp-bmenu-title            (if arg
                                        "Orphaned File and Directory Bookmarks"
                                      "Local Orphaned File and Directory Bookmarks"))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only orphaned file bookmarks are shown")))

;;;###autoload (autoload 'bmkp-bmenu-show-only-specific-buffer-bookmarks "bookmark+")
(defun bmkp-bmenu-show-only-specific-buffer-bookmarks (&optional buffer) ; `= b S' in bookmark list
  "Display (only) the bookmarks for BUFFER.
Interactively, read the BUFFER name.
If BUFFER is non-nil, set `bmkp-last-specific-buffer' to it."
  (interactive (list (bmkp-completing-read-buffer-name)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when buffer (setq bmkp-last-specific-buffer  buffer))
  (setq bmkp-bmenu-filter-function  'bmkp-last-specific-buffer-alist-only
        bmkp-bmenu-title            (format "Buffer `%s' Bookmarks" bmkp-last-specific-buffer))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order)
                               (format "Only bookmarks for buffer `%s' are shown"
                                       bmkp-last-specific-buffer))))

;;;###autoload (autoload 'bmkp-bmenu-show-only-specific-file-bookmarks "bookmark+")
(defun bmkp-bmenu-show-only-specific-file-bookmarks (&optional file) ; Bound to `= f S' in bookmark list
  "Display (only) the bookmarks for FILE, an absolute file name.
Interactively, read the FILE name.
If FILE is non-nil, set `bmkp-last-specific-file' to it."
  (interactive (list (bmkp-completing-read-file-name)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((orig-last-spec-file  bmkp-last-specific-file)
        (orig-filter-fn       bmkp-bmenu-filter-function)
        (orig-title           bmkp-bmenu-title)
        (orig-latest-alist    bmkp-latest-bookmark-alist))
    (condition-case err
        (progn
          (when file (setq bmkp-last-specific-file  file))
          (setq bmkp-bmenu-filter-function  'bmkp-last-specific-file-alist-only
                bmkp-bmenu-title            (format "File `%s' Bookmarks" bmkp-last-specific-file))
          (let ((bookmark-alist         (funcall bmkp-bmenu-filter-function))
                (bmkp-bmenu-state-file  nil)) ; Prevent restoring saved state.
            (setq bmkp-latest-bookmark-alist  bookmark-alist)
            (bookmark-bmenu-list 'filteredp))
          (when (interactive-p)
            (bmkp-msg-about-sort-order (bmkp-current-sort-order)
                                       (format "Only bookmarks for file `%s' are shown"
                                               bmkp-last-specific-file)))
          (raise-frame))
      (error (progn (setq bmkp-last-specific-file     orig-last-spec-file
                          bmkp-bmenu-filter-function  orig-filter-fn
                          bmkp-bmenu-title            orig-title
                          bmkp-latest-bookmark-alist  orig-latest-alist)
                    (error "%s" (error-message-string err)))))))


;;;###autoload (autoload 'bmkp-bmenu-refresh-menu-list "bookmark+")
(defun bmkp-bmenu-refresh-menu-list (&optional parg msg-p) ; Bound to `g' in bookmark list
  "Refresh (revert) the bookmark list display (aka \"menu list\").
This brings the displayed list up to date with respect to the current
bookmark list.  It does not change the filtering or sorting of the
displayed list.

With a prefix argument and upon confirmation, refresh the bookmark
list and its display from the current bookmark file.  IOW, it reloads
the file, overwriting the current bookmark list.  This also removes
any markings and omissions.

You can use command `bmkp-toggle-bookmark-set-refreshes' to toggle
whether setting a bookmark in any way should automatically refresh the
list.

From Lisp, non-nil optional arg MSG-P means show progress messages."
  (interactive "P\np")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((msg  "Refreshing from bookmark "))
    (cond ((and parg  (yes-or-no-p (format "Refresh list to bookmarks saved in file `%s'? "
                                           bmkp-current-bookmark-file)))
           (when msg-p (message (setq msg  (concat msg "file..."))))
           (bookmark-load bmkp-current-bookmark-file 'OVERWRITE 'BATCH-NO-SAVE)
           (setq bmkp-bmenu-marked-bookmarks   () ; Start from scratch.
                 bmkp-modified-bookmarks       ()
                 bmkp-flagged-bookmarks        ()
                 bmkp-bmenu-omitted-bookmarks  (condition-case nil
                                                   (eval (car (get 'bmkp-bmenu-omitted-bookmarks
                                                                   'saved-value)))
                                                 (error nil)))
           (let ((bmkp-bmenu-filter-function  nil)) ; Remove any filtering.
             (bmkp-refresh-menu-list (bookmark-bmenu-bookmark) (not msg-p))))
          (t
           (when msg-p (message (setq msg  (concat msg "list in memory..."))))
           (bmkp-refresh-menu-list (bookmark-bmenu-bookmark) (not msg-p))))
    (when msg-p (message (concat msg "done")))))

;;;###autoload (autoload 'bmkp-bmenu-filter-bookmark-name-incrementally "bookmark+")
(defun bmkp-bmenu-filter-bookmark-name-incrementally () ; Bound to `P B' in bookmark list
  "Incrementally filter bookmarks by bookmark name using a regexp."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bmkp-bmenu-filter-timer
                    (run-with-idle-timer bmkp-incremental-filter-delay 'REPEAT
                                    #'bmkp-bmenu-filter-alist-by-bookmark-name-regexp))
              (bmkp-bmenu-read-filter-input))
    (bmkp-bmenu-cancel-incremental-filtering)))

(defun bmkp-bmenu-filter-alist-by-bookmark-name-regexp ()
  "Filter bookmarks by bookmark name, then refresh the bookmark list."
  (setq bmkp-bmenu-filter-function  'bmkp-regexp-filtered-bookmark-name-alist-only
        bmkp-bmenu-title            (format "Bookmarks with Names Matching Regexp `%s'"
                                            bmkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

;;;###autoload (autoload 'bmkp-bmenu-filter-file-name-incrementally "bookmark+")
(defun bmkp-bmenu-filter-file-name-incrementally () ; Bound to `P F' in bookmark list
  "Incrementally filter bookmarks by file name using a regexp."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bmkp-bmenu-filter-timer
                    (run-with-idle-timer bmkp-incremental-filter-delay 'REPEAT
                                    #'bmkp-bmenu-filter-alist-by-file-name-regexp))
              (bmkp-bmenu-read-filter-input))
    (bmkp-bmenu-cancel-incremental-filtering)))

(defun bmkp-bmenu-filter-alist-by-file-name-regexp ()
  "Filter bookmarks by file name, then refresh the bookmark list."
  (setq bmkp-bmenu-filter-function  'bmkp-regexp-filtered-file-name-alist-only
        bmkp-bmenu-title            (format "Bookmarks with File Names Matching Regexp `%s'"
                                            bmkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

;;;###autoload (autoload 'bmkp-bmenu-filter-annotation-incrementally "bookmark+")
(defun bmkp-bmenu-filter-annotation-incrementally () ; Bound to `P A' in bookmark list
  "Incrementally filter bookmarks by their annotations using a regexp."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bmkp-bmenu-filter-timer
                    (run-with-idle-timer bmkp-incremental-filter-delay 'REPEAT
                                    #'bmkp-bmenu-filter-alist-by-annotation-regexp))
              (bmkp-bmenu-read-filter-input))
    (bmkp-bmenu-cancel-incremental-filtering)))

(defun bmkp-bmenu-filter-alist-by-annotation-regexp ()
  "Filter bookmarks by annoation, then refresh the bookmark list."
  (setq bmkp-bmenu-filter-function  'bmkp-regexp-filtered-annotation-alist-only
        bmkp-bmenu-title            (format "Bookmarks with Annotations Matching Regexp `%s'"
                                            bmkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

;;;###autoload (autoload 'bmkp-bmenu-filter-tags-incrementally "bookmark+")
(defun bmkp-bmenu-filter-tags-incrementally () ; Bound to `P T' in bookmark list
  "Incrementally filter bookmarks by tags using a regexp."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bmkp-bmenu-filter-timer
                    (run-with-idle-timer bmkp-incremental-filter-delay 'REPEAT
                                    #'bmkp-bmenu-filter-alist-by-tags-regexp))
              (bmkp-bmenu-read-filter-input))
    (bmkp-bmenu-cancel-incremental-filtering)))

(defun bmkp-bmenu-filter-alist-by-tags-regexp ()
  "Filter bookmarks by tags, then refresh the bookmark list."
  (setq bmkp-bmenu-filter-function  'bmkp-regexp-filtered-tags-alist-only
        bmkp-bmenu-title            (format "Bookmarks with Tags Matching Regexp `%s'"
                                            bmkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

(defun bmkp-bmenu-read-filter-input ()
  "Read input and add it to `bmkp-bmenu-filter-pattern'."
  (setq bmkp-bmenu-filter-pattern  "")
  (let ((curr-bmk  (bookmark-bmenu-bookmark)))
    (when (eq 'QUIT
              (let ((tmp-list                    ())
                    (bmkp-bmenu-title            bmkp-bmenu-title)
                    (bmkp-bmenu-filter-function  bmkp-bmenu-filter-function)
                    (inhibit-quit                t)
                    char)
                (catch 'bmkp-bmenu-read-filter-input
                  (while (condition-case nil
                             (setq char  (read-char (concat "Pattern: " bmkp-bmenu-filter-pattern)))
                           ;; `read-char' raises an error for non-char event.
                           (error (throw 'bmkp-bmenu-read-filter-input nil)))
                    (case char
                      ((?\e ?\r)  (throw 'bmkp-bmenu-read-filter-input nil)) ; Break and exit.
                      (?\C-g      (setq inhibit-quit  nil)
                                  (throw 'bmkp-bmenu-read-filter-input 'QUIT)) ; Quit.
                      (?\d        (or (null tmp-list) ; No-op if no chars to delete.
                                      (pop tmp-list)
                                      t)) ; Delete last char of `bmkp-bmenu-filter-pattern'.
                      (t          (push (text-char-description char) tmp-list))) ; Accumulate CHAR.
                    (setq bmkp-bmenu-filter-pattern  (mapconcat #'identity (reverse tmp-list) ""))))))
      (message "Restoring display prior to incremental filtering...")
      (bookmark-bmenu-list 'FILTEREDP)
      (bmkp-bmenu-goto-bookmark-named curr-bmk)
      (message "Restoring display prior to incremental filtering...done"))))

(defun bmkp-bmenu-cancel-incremental-filtering ()
  "Cancel timer used for incrementally filtering bookmarks."
  (cancel-timer bmkp-bmenu-filter-timer)
  (setq bmkp-bmenu-filter-timer  nil))

;;;###autoload (autoload 'bmkp-bmenu-toggle-show-only-unmarked "bookmark+")
(defun bmkp-bmenu-toggle-show-only-unmarked () ; Bound to `<' in bookmark list
  "Hide all marked bookmarks.  Repeat to toggle, showing all."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  ;; Save display, to be sure `bmkp-bmenu-before-hide-marked-alist' is up-to-date.
  (bmkp-save-menu-list-state)
  (if (or (bmkp-some-marked-p bmkp-latest-bookmark-alist)
          (bmkp-some-marked-p bmkp-bmenu-before-hide-marked-alist))
      (let ((bookmark-alist  bmkp-latest-bookmark-alist)
            status)
        (if bmkp-bmenu-before-hide-marked-alist
            (setq bookmark-alist                       bmkp-bmenu-before-hide-marked-alist
                  bmkp-bmenu-before-hide-marked-alist  ()
                  bmkp-latest-bookmark-alist           bookmark-alist
                  status                               'shown)
          (setq bmkp-bmenu-before-hide-marked-alist  bmkp-latest-bookmark-alist
                bookmark-alist                       (bmkp-unmarked-bookmarks-only)
                bmkp-latest-bookmark-alist           bookmark-alist
                status                               'hidden))
        (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
        (cond ((eq status 'hidden)
               (bookmark-bmenu-ensure-position)
               (message "Marked bookmarks are now hidden"))
              (t
               (goto-char (point-min))
               (when (re-search-forward "^>" (point-max) t)  (forward-line 0))
               (message "Marked bookmarks no longer hidden"))))
    (message "No marked bookmarks to hide"))
  (when (and (fboundp 'fit-frame-if-one-window)
             (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
    (fit-frame-if-one-window)))

;;;###autoload (autoload 'bmkp-bmenu-toggle-show-only-marked "bookmark+")
(defun bmkp-bmenu-toggle-show-only-marked () ; Bound to `>' in bookmark list
  "Hide all unmarked bookmarks.  Repeat to toggle, showing all."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  ;; Save display, to be sure `bmkp-bmenu-before-hide-unmarked-alist' is up-to-date.
  (bmkp-save-menu-list-state)
  (if (or (bmkp-some-unmarked-p bmkp-latest-bookmark-alist)
          (bmkp-some-unmarked-p bmkp-bmenu-before-hide-unmarked-alist))
      (let ((bookmark-alist  bmkp-latest-bookmark-alist)
            status)
        (if bmkp-bmenu-before-hide-unmarked-alist
            (setq bookmark-alist                         bmkp-bmenu-before-hide-unmarked-alist
                  bmkp-bmenu-before-hide-unmarked-alist  ()
                  bmkp-latest-bookmark-alist             bookmark-alist
                  status                                 'shown)
          (setq bmkp-bmenu-before-hide-unmarked-alist  bmkp-latest-bookmark-alist
                bookmark-alist                         (bmkp-marked-bookmarks-only)
                bmkp-latest-bookmark-alist             bookmark-alist
                status                                 'hidden))
        (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
        (cond ((eq status 'hidden)
               (bookmark-bmenu-ensure-position)
               (message "Unmarked bookmarks are now hidden"))
              (t
               (goto-char (point-min))
               (when (re-search-forward "^>" (point-max) t)  (forward-line 0))
               (message "Unmarked bookmarks no longer hidden"))))
    (message "No unmarked bookmarks to hide"))
  (when (and (fboundp 'fit-frame-if-one-window)
             (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
    (fit-frame-if-one-window)))


;;(@* "Menu-List (`*-bmenu-*') Commands Involving Marks")
;;  *** Menu-List (`*-bmenu-*') Commands Involving Marks ***

;;;###autoload (autoload 'bmkp-bmenu-mark-all "bookmark+")
(defun bmkp-bmenu-mark-all (&optional no-re-sort-p msg-p) ; Bound to `M-m' in bookmark list
  "Mark all bookmarks, using mark `>'.
If any bookmark was unmarked before, and if the sort order is marked
first or last (`s >'), then re-sort.

Non-interactively:
* Non-nil optional arg NO-RE-SORT-P inhibits re-sorting.
* Non-nil optional arg MSG-P means display a status message."
  (interactive "i\np")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((count      0)
        (nb-marked  (length bmkp-bmenu-marked-bookmarks)))
    (save-excursion
      (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
      (when msg-p (message "Updating bookmark-list display..."))
      (while (not (eobp)) (bookmark-bmenu-mark 'NO-RE-SORT-P) (setq count  (1+ count))))
    (unless no-re-sort-p
      ;; If some were unmarked before, and if sort order is `s >' then re-sort.
      (when (and (/= nb-marked count)  (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p)))
        (let ((curr-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
          (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk)))))
    (when msg-p (message "Marked: %d" count))))

;; This is similar to `dired-unmark-all-files'.
;;;###autoload (autoload 'bmkp-bmenu-unmark-all "bookmark+")
(defun bmkp-bmenu-unmark-all (mark &optional arg no-re-sort-p msg-p) ; Bound to `M-DEL', `U' in bmk list
  "Remove a mark from each bookmark.
Hit the mark character (`>' or `D') to remove those marks,
 or hit `RET' to remove all marks (both `>' and `D').
With a prefix arg, you are queried to unmark each marked bookmark.
Use `\\[help-command]' during querying for help.

If any bookmark was marked before, and if the sort order is marked
first or last (`s >'), then re-sort.

Non-interactively:
* MARK is the mark character or a carriage-return character (`?\r').
* Non-nil ARG (prefix arg) means query.
* Non-nil optional arg NO-RE-SORT-P inhibits re-sorting.
* Non-nil optional arg MSG-P means display a status message."
  (interactive "cRemove marks (RET means all): \nP\ni\np")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (require 'dired-aux)
  (let* ((count              0)
         (some-marked-p      bmkp-bmenu-marked-bookmarks)
         (inhibit-read-only  t)
         (case-fold-search   nil)
         (query              nil)
         (string             (format "\n%c" mark))
         (help-form          "Type SPC or `y' to unmark one bookmark, DEL or `n' to skip to next,
`!' to unmark all remaining bookmarks with no more questions."))
    (save-excursion
      (goto-char (point-min))
      (forward-line (if (eq mark ?\r)
                        bmkp-bmenu-header-lines
                      (1- bmkp-bmenu-header-lines))) ; Because STRING starts with a newline.
      (while (and (not (eobp))
                  (if (eq mark ?\r)
                      (re-search-forward dired-re-mark nil t)
                    (let ((case-fold-search  t)) ; Treat `d' the same as `D'.
                      (search-forward string nil t))))
        (when (or (prog1 (not arg) (when msg-p (message "Updating bookmark-list display...")))
                  (let ((bmk  (bookmark-bmenu-bookmark)))
                    (and bmk  (dired-query 'query "Unmark bookmark `%s'? " bmk))))
          (bookmark-bmenu-unmark nil 'NO-RE-SORT-P) (forward-line -1)
          (setq count  (1+ count)))))
    (unless no-re-sort-p
      ;; If some were marked before, and if sort order is `s >', then re-sort.
      (when (and some-marked-p  (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p)))
        (let ((curr-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
          (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk)))))
    (when msg-p (if (= 1 count) (message "1 mark removed") (message "%d marks removed" count)))))

;;;###autoload (autoload 'bmkp-bmenu-regexp-mark "bookmark+")
(defun bmkp-bmenu-regexp-mark (regexp &optional no-re-sort-p msg-p) ; Bound to `% m' in bookmark list
  "Mark bookmarks that match REGEXP.
The entire bookmark line is tested: bookmark name and possibly file name.
Note too that if file names are not shown currently then the bookmark
name is padded at the right with spaces.

If any bookmark was unmarked before, and if the sort order is marked
first or last (`s >'), then re-sort.

Non-interactively:
* Non-nil optional arg NO-RE-SORT-P inhibits re-sorting.
* Non-nil optional arg MSG-P means display a status message."
  (interactive (list (bmkp-read-regexp "Regexp: ") (prefix-numeric-value current-prefix-arg)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((count      0)
        (nb-marked  (length bmkp-bmenu-marked-bookmarks)))
    (save-excursion
      (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
      (when msg-p (message "Updating bookmark-list display..."))
      (while (and (not (eobp))  (re-search-forward regexp (point-max) t))
        (bookmark-bmenu-mark 'NO-RE-SORT-P)
        (setq count  (1+ count))))
    (unless no-re-sort-p
      ;; If some were unmarked before, and if sort order is `s >', then re-sort.
      (when (and (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p))
                 (< nb-marked (length bmkp-bmenu-marked-bookmarks)))
        (let ((curr-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
          (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk)))))
    (when msg-p (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload (autoload 'bmkp-bmenu-mark-autofile-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-autofile-bookmarks (&optional arg msgp) ; Bound to `A M' in bookmark list
  "Mark autofile bookmarks: those whose names are the same as their files.
With a prefix arg you are prompted for a prefix that each bookmark
name must have."
  (interactive "P\np")
  (if (not arg)
      (bmkp-bmenu-mark-bookmarks-satisfying #'bmkp-autofile-bookmark-p nil msgp)
    (let ((prefix  (read-string "Prefix for bookmark names: " nil nil "")))
      (bmkp-bmenu-mark-bookmarks-satisfying
       #'(lambda (bb) (bmkp-autofile-bookmark-p bb prefix)) nil msgp))))

;;;###autoload (autoload 'bmkp-bmenu-mark-autonamed-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-autonamed-bookmarks (&optional msgp) ; Bound to `# M' in bookmark list
  "Mark autonamed bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying #'bmkp-autonamed-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-bookmark-file-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-bookmark-file-bookmarks (&optional msgp) ; Bound to `Y M' in bookmark list
  "Mark bookmark-file bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-bookmark-file-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-bookmark-list-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-bookmark-list-bookmarks (&optional msgp) ; Bound to `Z M' in bookmark list
  "Mark bookmark-list bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-bookmark-list-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-desktop-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-desktop-bookmarks (&optional msgp) ; Bound to `K M' in bookmark list
  "Mark desktop bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-desktop-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-dired-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-dired-bookmarks (&optional msgp) ; Bound to `M-d M-m' in bookmark list
  "Mark Dired bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-dired-bookmark-p nil msgp))

(when (fboundp 'bmkp-eww-bookmark-p)    ; Emacs 25+

  ;; ;;;###autoload (autoload 'bmkp-bmenu-mark-eww-bookmarks "bookmark+")
  (defun bmkp-bmenu-mark-eww-bookmarks (&optional msgp) ; Bound to `W E M' in bookmark list
    "Mark EWW (URL) bookmarks."
    (interactive "p")
    (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-eww-bookmark-p nil msgp))

  )

;;;###autoload (autoload 'bmkp-bmenu-mark-file-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-file-bookmarks (&optional arg msgp) ; Bound to `F M' in bookmark list
  "Mark file bookmarks.
With a prefix argument, do not mark remote files or directories."
  (interactive "P\np")
  (bmkp-bmenu-mark-bookmarks-satisfying
   (if arg 'bmkp-local-file-bookmark-p 'bmkp-file-bookmark-p nil msgp)))

;;;###autoload (autoload 'bmkp-bmenu-mark-function-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-function-bookmarks (&optional msgp) ; Bound to `Q M' in bookmark list
  "Mark function bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying #'bmkp-function-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-gnus-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-gnus-bookmarks (&optional msgp) ; Bound to `G M' in bookmark list
  "Mark Gnus bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-gnus-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-icicles-search-hits-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-icicles-search-hits-bookmarks (&optional msgp) ; Bound to `i M' in bookmark list
  "Mark Icicles search-hit bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-icicles-search-hits-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-image-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-image-bookmarks (&optional msgp) ; Bound to `M-I M-M' in bookmark list
  "Mark image-file bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-image-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-info-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-info-bookmarks (&optional msgp) ; Bound to `I M' in bookmark list
  "Mark Info bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-info-bookmark-p nil msgp))

(when (featurep 'bookmark+-lit)
  (defun bmkp-bmenu-mark-lighted-bookmarks (&optional msgp) ; Bound to `H M' in bookmark list
    "Mark the highlighted bookmarks."
    (interactive "p")
    (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-lighted-p nil msgp)))

;;;###autoload (autoload 'bmkp-bmenu-mark-man-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-man-bookmarks (&optional msgp) ; Bound to `M M' in bookmark list
  "Mark `man' page bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-man-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-non-file-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-non-file-bookmarks (&optional msgp) ; Bound to `B M' in bookmark list
  "Mark non-file bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-non-file-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-non-invokable-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-non-invokable-bookmarks (&optional msgp) ; Bound to `N M' in bookmark list
  "Mark non-invokable bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-non-invokable-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-orphaned-local-file-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-orphaned-local-file-bookmarks (&optional arg msgp) ; Bound to `O M' in bookmark list
  "Mark orphaned local-file bookmarks (their recorded files are not readable).
With a prefix argument, mark also remote orphaned files or directories."
  (interactive "P\np")
  (bmkp-bmenu-mark-bookmarks-satisfying
   (if arg 'bmkp-orphaned-file-bookmark-p 'bmkp-orphaned-local-file-bookmark-p nil msgp)))

;;;###autoload (autoload 'bmkp-bmenu-mark-region-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-region-bookmarks (&optional msgp) ; Bound to `R M' in bookmark list
  "Mark bookmarks that record a region."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-region-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-snippet-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-snippet-bookmarks (&optional msgp) ; Bound to `w M' in bookmark list
  "Mark snippet bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-snippet-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-specific-buffer-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-specific-buffer-bookmarks (&optional buffer msgp) ; `= b M' in bookmark list
  "Mark bookmarks for BUFFER.
Interactively, read the name of the buffer.
If BUFFER is non-nil, set `bmkp-last-specific-buffer' to it."
  (interactive (list (bmkp-completing-read-buffer-name) t))
  (when buffer (setq bmkp-last-specific-buffer  buffer))
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-last-specific-buffer-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-specific-file-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-specific-file-bookmarks (&optional file msgp) ; Bound to `= f M' in bookmark list
  "Mark bookmarks for FILE, an absolute file name.
Interactively, read the file name.
If FILE is non-nil, set `bmkp-last-specific-file' to it."
  (interactive (list (bmkp-completing-read-file-name) t))
  (when file (setq bmkp-last-specific-file  file))
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-last-specific-file-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-temporary-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-temporary-bookmarks (&optional msgp) ; Bound to `X M' in bookmark list
  "Mark temporary bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-temporary-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-variable-list-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-variable-list-bookmarks (&optional msgp) ; Bound to `V M' in bookmark list
  "Mark variable-list bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-variable-list-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-url-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-url-bookmarks (&optional msgp) ; Bound to `M-u M-m' in bookmark list
  "Mark URL bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-url-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-w3m-bookmarks "bookmark+")
(defun bmkp-bmenu-mark-w3m-bookmarks (&optional msgp) ; Bound to `W 3 M' in bookmark list
  "Mark W3M (URL) bookmarks."
  (interactive "p")
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-w3m-bookmark-p nil msgp))

;;;###autoload (autoload 'bmkp-bmenu-mark-bookmarks-satisfying "bookmark+")
(defun bmkp-bmenu-mark-bookmarks-satisfying (pred &optional no-re-sort-p msg-p) ; Not bound
  "Mark bookmarks that satisfy predicate PRED.
If you use this interactively, you are responsible for entering a
symbol that names a unnary predicate.  The function you provide is not
checked - it is simply applied to each bookmark to test it.

If any bookmark was unmarked before, and if the sort order is marked
first or last (`s >'), then re-sort.

Non-interactively:
* Non-nil optional arg NO-RE-SORT-P inhibits re-sorting.
* Non-nil optional arg MSG-P means display a status message."
  (interactive "aPredicate: \ni\np")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((count      0)
        (nb-marked  (length bmkp-bmenu-marked-bookmarks))
        bmk)
    (save-excursion
      (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
      (when msg-p (message "Updating bookmark-list display..."))
      (while (not (eobp))
        (setq bmk  (bookmark-bmenu-bookmark))
        (if (not (funcall pred bmk))
            (forward-line 1)
          (bookmark-bmenu-mark 'NO-RE-SORT-P)
          (setq count  (1+ count)))))
    (unless no-re-sort-p
      ;; If some were unmarked before, and if sort order is `s >', then re-sort.
      (when (and (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p))
                 (< nb-marked (length bmkp-bmenu-marked-bookmarks)))
        (let ((curr-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
          (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk)))))
    (when msg-p (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload (autoload 'bmkp-bmenu-toggle-marks "bookmark+")
(defun bmkp-bmenu-toggle-marks (&optional backup no-re-sort-p msg-p) ; Bound to `t' in bookmark list
  "Toggle marks: Unmark all marked bookmarks; mark all unmarked bookmarks.
This affects only the `>' mark, not the `D' flag.

Interactively or with nil optional arg NO-RE-SORT-P, if the current
sort order is marked first or last (`s >'), then re-sort.

Non-interactively, non-nil optional arg MSG-P means display a status
message."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((marked-count    0)
        (unmarked-count  0))
    (save-excursion
      (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
      (if (not (bmkp-some-marked-p bmkp-latest-bookmark-alist))
          (bmkp-bmenu-mark-all no-re-sort-p)
        (when msg-p (message "Updating bookmark-list display..."))
        (while (not (eobp))
          (cond ((bmkp-bookmark-name-member (bookmark-bmenu-bookmark) bmkp-bmenu-marked-bookmarks)
                 (bookmark-bmenu-unmark nil 'NO-RE-SORT-P)
                 (setq unmarked-count  (1+ unmarked-count)))
                (t
                 (bookmark-bmenu-mark 'NO-RE-SORT-P)
                 (setq marked-count  (1+ marked-count)))))))
    ;; If sort order is `s >' then re-sort.
    (when (and (not no-re-sort-p)  (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p)))
      (let ((curr-bmk  (bookmark-bmenu-bookmark)))
        (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
        (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk))))
    (when msg-p (message "Marked: %d, unmarked: %d" marked-count unmarked-count))))

;;;###autoload (autoload 'bmkp-bmenu-toggle-marked-temporary/savable "bookmark+")
(defun bmkp-bmenu-toggle-marked-temporary/savable () ; Bound to `M-X' in bookmark list
  "Toggle the temporary/savable status of each marked bookmark.
If none are marked, toggle status of the bookmark of the current line."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((o-str       (and (not (bmkp-looking-at-p "^>"))  (bookmark-bmenu-bookmark)))
        (o-point     (point))
        (count-temp  0)
        (count-save  0)
        bmk)
    (message "Toggling temporary status of marked bookmarks...")
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (while (re-search-forward "^>" (point-max) t)
      (bmkp-toggle-temporary-bookmark (setq bmk  (bookmark-bmenu-bookmark)))
      (if (bmkp-temporary-bookmark-p bmk)
          (setq count-temp  (1+ count-temp))
        (setq count-save  (1+ count-save))))
    (cond ((and (<= count-temp 0)  (<= count-save 0))
           (if o-str
               (bmkp-bmenu-goto-bookmark-named o-str)
             (goto-char o-point)
             (beginning-of-line))
           (bmkp-toggle-temporary-bookmark (bookmark-bmenu-bookmark) 'MSG)
           (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P))
          (t
           (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
           (message "%d made temporary; %d made savable" count-temp count-save)))
    (if o-str
        (bmkp-bmenu-goto-bookmark-named o-str)
      (goto-char o-point)
      (beginning-of-line)))
  (when (and (fboundp 'fit-frame-if-one-window)
             (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
    (fit-frame-if-one-window)))

;;;###autoload (autoload 'bmkp-bmenu-toggle-temporary "bookmark+")
(defun bmkp-bmenu-toggle-temporary ()   ; Bound to `C-M-X' in bookmark list
  "Toggle whether bookmark of current line is temporary (not saved to disk)."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((o-str    (bookmark-bmenu-bookmark))
        (o-point  (point)))
    (bmkp-toggle-temporary-bookmark (bookmark-bmenu-bookmark) 'MSG)
    (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
    (if o-str
        (bmkp-bmenu-goto-bookmark-named o-str)
      (goto-char o-point)
      (beginning-of-line))))

;;;###autoload (autoload 'bmkp-bmenu-dired-marked "bookmark+")
(defun bmkp-bmenu-dired-marked (dirbufname &optional include-omitted-p)
                                        ; Bound to `M-d >' in bookmark list
  "Dired in another window for the marked file and directory bookmarks.
Absolute file names are used for the entries in the Dired buffer.
The only entries are for the marked files and directories.  These can
be located anywhere.  (In Emacs versions prior to release 23.2, remote
bookmarks are ignored, because of Emacs bug #5478.)

You are prompted for the Dired buffer name.  The `default-directory'
of the buffer is the same as that of buffer `*Bookmark List*'.

Omitted bookmarks are excluded, by default.  With a prefix arg, any
that are marked are included."
  (interactive (list (read-string "Dired buffer name: ") current-prefix-arg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((files  ())
        file)
    (dolist (bmk  (bmkp-sort-omit (bmkp-bmenu-marked-or-this-or-all nil include-omitted-p)))
      (when (or (bmkp-local-file-bookmark-p bmk)
                (> emacs-major-version 23)
                (and (= emacs-major-version 23)  (> emacs-minor-version 1)))
        (setq file  (bookmark-get-filename bmk))
        (unless (file-name-absolute-p file) (setq file (expand-file-name file))) ; Should not happen.
        (push file files)))
    (dired-other-window (cons dirbufname files))))

;;;###autoload (autoload 'bmkp-bmenu-delete-marked "bookmark+")
(defun bmkp-bmenu-delete-marked (&optional no-confirm-p)      ; Bound to `D' in bookmark list
  "Delete all (visible) bookmarks that are marked `>', after confirmation.
Optional arg NO-CONFIRM-P non-nil means do not ask for confirmation."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-execute-deletions 'MARKED 'NO-CONFIRM))

;;;###autoload (autoload 'bmkp-bmenu-move-marked-to-bookmark-file "bookmark+")
(defun bmkp-bmenu-move-marked-to-bookmark-file (file &optional duplicates-ok include-omitted-p batchp)
                                        ; Bound to `Y > -' in bookmark list
  "Move the marked bookmarks to bookmark file FILE.
You are prompted for FILE.
The marked bookmarks are removed from the current bookmark list and
appended to those in FILE.  If any of them has the same name as a
bookmark already in FILE then it is renamed by appending a numeric
suffix \"<N>\" (N=2,3...).

Normally, any of the marked bookmarks that are already present in FILE
are ignored, rather than duplicating them under a new, suffixed name.
But if you use a non-negative prefix arg then such duplication is
allowed.

If no bookmark is marked then move the bookmark of the current line.

Omitted bookmarks are excluded, by default.  With a non-positive
prefix arg, any that are marked are included.

The bookmarks are removed from the currently displayed bookmark list,
but the bookmark file associated with it is not saved automatically.
To save it, use \\<bookmark-bmenu-mode-map>`\\[bookmark-bmenu-save]' (as usual).

Non-interactively, non-nil optional arg BATCHP means do not prompt to
confirm moving to new, empty file if no existing file."
  (interactive
   (list (let* ((_IGNORE      (bmkp-bmenu-barf-if-not-in-menu-list))
                (std-default  (bmkp-default-bookmark-file))
                (default      (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                                  (if (bmkp-same-file-p bmkp-current-bookmark-file std-default)
                                      (and (not (bmkp-same-file-p bmkp-current-bookmark-file
                                                                  bookmark-default-file))
                                           bookmark-default-file)
                                    std-default)
                                bmkp-last-bookmark-file)))
           (bmkp-read-bookmark-file-name "Move marked bookmarks to bookmark file: "
                                         (or (and default  (file-name-directory default))  "~/")
                                         default))
         (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
         (and current-prefix-arg  (<= (prefix-numeric-value current-prefix-arg) 0))))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when (and (not (file-readable-p file))
             (not batchp)
             (not (y-or-n-p (format "Move to NEW, EMPTY bookmark file `%s'? " file))))
    (error "OK - canceled"))
  (bmkp-bmenu-copy-marked-to-bookmark-file file duplicates-ok include-omitted-p 'MOVE 'BATCH))

;;;###autoload (autoload 'bmkp-bmenu-copy-marked-to-bookmark-file "bookmark+")
(defun bmkp-bmenu-copy-marked-to-bookmark-file (file &optional duplicates-ok include-omitted-p movep batchp)
                                        ; Bound to `Y > +' in bookmark list
  "Copy the marked bookmarks to bookmark file FILE.
You are prompted for FILE.
The marked bookmarks are appended to those already in FILE.
If any of them has the same name as a bookmark already in FILE then it
is renamed by appending a numeric suffix \"<N>\" (N=2,3...).

Normally, any of the marked bookmarks that are already present in FILE
are ignored, rather than duplicating them under a new, suffixed name.
But if you use a non-negative prefix arg then such duplication is
allowed.  Use this, for example, to duplicate a bookmark in the
current bookmark file (use that file as FILE).

If no bookmark is marked then copy the bookmark of the current line.

Omitted bookmarks are excluded, by default.  With a non-positive
prefix arg, any that are marked are included.

Non-interactively:
* Non-nil MOVEP means delete the bookmarks copied.
* Non-nil BATCHP means do not prompt to confirm moving to a new, empty
  file if there is no existing file."
  (interactive
   (list (let* ((_IGNORE      (bmkp-bmenu-barf-if-not-in-menu-list))
                (std-default  (bmkp-default-bookmark-file))
                (default      (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                                  (if (bmkp-same-file-p bmkp-current-bookmark-file std-default)
                                      (and (not (bmkp-same-file-p bmkp-current-bookmark-file
                                                                  bookmark-default-file))
                                           bookmark-default-file)
                                    std-default)
                                bmkp-last-bookmark-file)))
           (bmkp-read-bookmark-file-name "Copy marked bookmarks to bookmark file: "
                                         (or (and default  (file-name-directory default))  "~/")
                                         default))
         (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
         (and current-prefix-arg  (<= (prefix-numeric-value current-prefix-arg) 0))))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when (file-directory-p file) (error "`%s' is a directory, not a file" file))
  (when (and (not (file-readable-p file))
             (not batchp)
             (not (y-or-n-p (format "Copy to NEW, EMPTY bookmark file `%s'? " file))))
    (error "OK - canceled"))
  (let ((bookmark-save-flag  nil)       ; Inhibit auto-saving for the duration.
        imported)
    (let ((marked-bmks                        (bmkp-sort-omit
                                               (bmkp-bmenu-marked-or-this-or-all nil include-omitted-p)))
          (bookmark-alist                     bookmark-alist)
          (bookmark-alist-modification-count  bookmark-alist-modification-count))
      (when (and (not (zerop bookmark-alist-modification-count)) ; Unsaved changes.
                 (yes-or-no-p "Unsaved changes.  Save bookmarks before copying? "))
        (bookmark-save))
      (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect file))
        (goto-char (point-min))
        (if (file-exists-p file)
            (bookmark-maybe-upgrade-file-format)
          (delete-region (point-min) (point-max)) ; In case a find-file hook inserted a header etc.
          (if (boundp 'bookmark-file-coding-system) ; Insert timestamp and an empty bookmark list.
              (bookmark-insert-file-format-version-stamp bookmark-file-coding-system) ; Emacs 25.2+
            (bookmark-insert-file-format-version-stamp))
          (insert "(\n)"))
        (let ((blist  (bookmark-alist-from-buffer)))
          (unless (listp blist) (error "Invalid bookmark list in file `%s'" file))
          (setq bookmark-alist  blist)  ; Bookmarks in FILE
          (setq imported  (bookmark-import-new-list marked-bmks duplicates-ok 'RETURN-BMKS))
          (if (and (zerop (nth 0 imported))  (zerop (nth 1 imported)))
              (unless batchp (message "No changes"))
            (unless batchp (message "%d added, %d renamed" (nth 1 imported) (nth 0 imported)))
            (bookmark-write-file file)))))
    ;; (Exit `let', to restore `bookmark-alist'.)
    (cond (movep
           ;; Moved.  Delete moved bookmarks.  Refresh from memory w/o asking.
           (dolist (bmk  (nth 2 imported)) (bookmark-delete bmk 'BATCHP))
           (bmkp-bmenu-refresh-menu-list nil 'MSGP))
          ((not (zerop (nth 0 imported)))
           ;; Copied, and some were renamed.  Refresh from file w/o asking.
           (bookmark-load bmkp-current-bookmark-file 'OVERWRITE 'BATCH-NO-SAVE)
           (bmkp-refresh-menu-list (bookmark-bmenu-bookmark))))))

;;;###autoload (autoload 'bmkp-bmenu-create-bookmark-file-from-marked "bookmark+")
(defun bmkp-bmenu-create-bookmark-file-from-marked (file create-b-f-bookmark-p
                                                    &optional include-omitted-p batchp)
                                        ; Bound to `Y > 0' in bookmark list
  "Create bookmark file FILE by copying the marked bookmarks.
You are prompted for FILE.
They are not deleted from the current bookmark file.  To delete them, use \
\\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-delete-marked]'.

With a non-negative prefix arg, create also a bookmark-file bookmark
for FILE.  You are prompted for the bookmark name.

If no bookmark is marked then copy the bookmark of the current line.

Omitted bookmarks are excluded, by default.  With a non-positive
prefix arg, any that are marked are included.

Non-interactively, non-nil optional arg BATCHP means do not prompt to
confirm moving to new, empty file if no existing file."
  (interactive
   (list (let* ((_IGNORE      (bmkp-bmenu-barf-if-not-in-menu-list))
                (std-default  (bmkp-default-bookmark-file))
                (default      (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                                  (if (bmkp-same-file-p bmkp-current-bookmark-file std-default)
                                      (and (not (bmkp-same-file-p bmkp-current-bookmark-file
                                                                  bookmark-default-file))
                                           bookmark-default-file)
                                    std-default)
                                bmkp-last-bookmark-file)))
           (bmkp-read-bookmark-file-name "Create bookmark file from marked: "
                                         (or (and default  (file-name-directory default))  "~/")
                                         default))
         (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
         (and current-prefix-arg  (<= (prefix-numeric-value current-prefix-arg) 0))))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when (and (file-readable-p file)
             (not (file-directory-p file))
             (not batchp)
             (not (y-or-n-p (format "File `%s' already exists.  Overwrite? " file))))
    (error "OK - canceled"))
  (bmkp-empty-file file)
  (bmkp-bmenu-copy-marked-to-bookmark-file file nil include-omitted-p nil 'BATCH)
  (when create-b-f-bookmark-p (bmkp-set-bookmark-file-bookmark file)))

;;;###autoload (autoload 'bmkp-bmenu-set-bookmark-file-bookmark-from-marked "bookmark+")
(defun bmkp-bmenu-set-bookmark-file-bookmark-from-marked (file &optional include-omitted-p batchp)
                                        ; Same as `C-u Y > 0' in bookmark list (but not bound).
  "Set a bookmark-file bookmark for the marked bookmarks.
You are prompted for the names of the new bookmark file and the
bookmark-file bookmark.

This is the same as using a non-negative prefix arg with
`bmkp-bmenu-create-bookmark-file-from-marked'.

If no bookmark is marked then use the bookmark of the current line.

Omitted bookmarks are excluded, by default.  With a prefix arg, any
that are marked are included.

Non-interactively, non-nil optional arg BATCHP means do not prompt to
confirm moving to new, empty file if no existing file."
  (interactive
   (list (let* ((_IGNORE      (bmkp-bmenu-barf-if-not-in-menu-list))
                (std-default  (bmkp-default-bookmark-file))
                (default      (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                                  (if (bmkp-same-file-p bmkp-current-bookmark-file std-default)
                                      (and (not (bmkp-same-file-p bmkp-current-bookmark-file
                                                                  bookmark-default-file))
                                           bookmark-default-file)
                                    std-default)
                                bmkp-last-bookmark-file)))
           (bmkp-read-bookmark-file-name "Create a bookmark file from marked: "
                                         (or (and default  (file-name-directory default))  "~/")
                                         default))
         current-prefix-arg))
  (bmkp-bmenu-create-bookmark-file-from-marked file 'CREATE-B-F-BMK include-omitted-p batchp))

;;;###autoload (autoload 'bmkp-bmenu-load-marked-bookmark-file-bookmarks "bookmark+")
(defun bmkp-bmenu-load-marked-bookmark-file-bookmarks (&optional msg-p) ; Bound to `M-l' in bookmark list
  "Load the bookmark-file bookmarks that are marked, in display order.
Non bookmark-file bookmarks that are marked are ignored.
You can sort the bookmark-list display to change the load order.

NOTE: Automatically saving the current bookmark list is turned OFF
before loading, and it remains turned off until you explicitly turn it
back on.  Bookmark+ does not assume that you want to automatically
save all of the newly loaded bookmarks in the same bookmark file.  If
you do, just use \\<bookmark-bmenu-mode-map>`\\[bmkp-toggle-saving-bookmark-file]' \
to turn saving back on."
  (interactive "p")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((bmks  (bmkp-remove-if-not #'bmkp-bookmark-file-bookmark-p
                                   (bmkp-remove-if-not 'bmkp-marked-bookmark-p bmkp-sorted-alist)))
        (bmk   (bookmark-bmenu-bookmark)))
    (unless bmks (error "No marked bookmark-file bookmarks"))
    ;; Maybe save bookmarks first.
    (when (or (not msg-p)
              (and (> bookmark-alist-modification-count 0)
                   (condition-case err
                       (yes-or-no-p "Save current bookmarks? (`C-g': cancel load too) ")
                     (quit  (error "OK - canceled"))
                     (error (error (error-message-string err))))))
      (bookmark-save))
    (when (or (not msg-p)
              (yes-or-no-p "Load the marked bookmark-file bookmarks? ")
              (error "OK - canceled"))
      (when bookmark-save-flag          ; Turn off autosaving.
        (bmkp-toggle-saving-bookmark-file) ; No MSG-P arg - issue message below.
        (when bookmark-save-flag  (setq bookmark-save-flag  nil)) ; Be sure it's off.
        (when msg-p (message "Autosaving of current bookmark file is now OFF")))
      (when msg-p (message "Loading marked bookmark files..."))
      (dolist (bmk  bmks)               ; Load.
        ;; USE BATCHP: Do not refresh list or display messages here - do that after iterate.
        (bookmark-load (bookmark-get-filename bmk) nil 'BATCHP))
      ;; $$$$$$ Should we do (bmkp-tags-list) here to update the tags cache?
      (bmkp-refresh-menu-list bmk (not msg-p)) ; Refresh after iterate.
      (when msg-p (message "Autosaving is now OFF.  Loaded: %s"
                           (mapconcat (lambda (bmk) (format "`%s'" (bmkp-bookmark-name-from-record bmk)))
                                      bmks
                                      ", "))))))

;;;###autoload (autoload 'bmkp-bmenu-make-sequence-from-marked "bookmark+")
(defun bmkp-bmenu-make-sequence-from-marked (seqname &optional dont-omit-p) ; Not bound
  "Create or update a sequence bookmark from the visible marked bookmarks.
The bookmarks that are currently marked are recorded as a sequence, in
their current order in buffer `*Bookmark List*'.
When you \"jump\" to the sequence bookmark, the bookmarks in the
sequence are processed in order.

By default, omit the marked bookmarks, after creating the sequence.
With a prefix arg, do not omit them.

If a bookmark with the specified name already exists, it is
overwritten.  If a sequence bookmark with the name already exists,
then you are prompted whether to add the marked bookmarks to the
beginning of the existing sequence (or simply replace it).

Note that another existing sequence bookmark can be marked, and thus
included in the sequence bookmark created or updated.  That is, you
can include other sequences within a sequence bookmark.

Returns the bookmark (internal record) created or updated."
  (interactive "sName of sequence bookmark: \nP")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked-bmks  ())
        (count        0))
    (message "Making sequence from marked bookmarks...")
    (save-excursion (with-current-buffer "*Bookmark List*"
                      (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
                      (while (re-search-forward "^>" (point-max) t)
                        (push (bookmark-bmenu-bookmark) marked-bmks)
                        (setq count  (1+ count)))))
    (when (zerop count) (error "No marked bookmarks"))
    (bmkp-set-sequence-bookmark seqname (nreverse marked-bmks)))
  (let ((new  (bookmark-get-bookmark seqname 'NOERROR)))
    (unless (memq new bmkp-latest-bookmark-alist)
      (setq bmkp-latest-bookmark-alist  (cons new bmkp-latest-bookmark-alist)))
    (unless dont-omit-p
      (bmkp-bmenu-omit-marked)
      (message (substitute-command-keys "Marked bookmarks now OMITTED - use \
\\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-show-only-omitted-bookmarks]' to show")))
    (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
    (bmkp-bmenu-goto-bookmark-named seqname)
    new))


;;(@* "Omitted Bookmarks")
;;  *** Omitted Bookmarks ***

;;;###autoload (autoload 'bmkp-bmenu-omit "bookmark+")
(defun bmkp-bmenu-omit ()               ; Not bound
  "Omit this bookmark."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (push (bookmark-bmenu-bookmark) bmkp-bmenu-omitted-bookmarks)
  (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
  (message "Omitted 1 bookmark"))

;;;###autoload (autoload 'bmkp-bmenu-omit/unomit-marked "bookmark+")
(defun bmkp-bmenu-omit/unomit-marked () ; Bound to `- >' in bookmark list
  "Omit all marked bookmarks or, if showing only omitted ones, unomit."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (if (eq bmkp-bmenu-filter-function  'bmkp-omitted-alist-only)
      (bmkp-bmenu-unomit-marked)
    (bmkp-bmenu-omit-marked)))

;;;###autoload (autoload 'bmkp-bmenu-omit-marked "bookmark+")
(defun bmkp-bmenu-omit-marked ()        ; Bound to `- >' in bookmark list
  "Omit all marked bookmarks.
They will henceforth be invisible to the bookmark list.
You can, however, use \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-show-only-omitted-bookmarks]' \
to see them.
You can then mark some of them and use `\\[bmkp-bmenu-omit/unomit-marked]' to make those marked
 available again for the bookmark list."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((o-str    (and (not (bmkp-looking-at-p "^>"))  (bookmark-bmenu-bookmark)))
        (o-point  (point))
        (count    0))
    (message "Omitting marked bookmarks...")
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (while (re-search-forward "^>" (point-max) t)
      (setq bmkp-bmenu-omitted-bookmarks  (cons (bookmark-bmenu-bookmark) bmkp-bmenu-omitted-bookmarks)
            count                         (1+ count)))
    (if (<= count 0)
        (message "No marked bookmarks")
      (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
      (message "Omitted %d bookmarks" count))
    (if o-str
        (bmkp-bmenu-goto-bookmark-named o-str)
      (goto-char o-point)
      (beginning-of-line)))
  (when (and (fboundp 'fit-frame-if-one-window)
             (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
    (fit-frame-if-one-window)))

;;;###autoload (autoload 'bmkp-bmenu-unomit-marked "bookmark+")
(defun bmkp-bmenu-unomit-marked ()      ; `- >' in bookmark list when showing omitted bookmarks
  "Remove all marked bookmarks from the list of omitted bookmarks.
They will henceforth be available for display in the bookmark list.
\(In order to see and then mark omitted bookmarks you must use \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-show-only-omitted-bookmarks]'.)"
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unless bmkp-bmenu-omitted-bookmarks (error "No omitted bookmarks to UN-omit"))
  (unless (eq bmkp-bmenu-filter-function  'bmkp-omitted-alist-only)
    (error "You must use command `bmkp-bmenu-show-only-omitted-bookmarks' first"))
  (let ((count    0))
    (message "UN-omitting marked bookmarks...")
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (while (re-search-forward "^>" (point-max) t)
      (let ((bmk-name  (bookmark-bmenu-bookmark)))
        (when (bmkp-bookmark-name-member bmk-name bmkp-bmenu-omitted-bookmarks)
          (setq bmkp-bmenu-omitted-bookmarks  (bmkp-delete-bookmark-name-from-list
                                               bmk-name bmkp-bmenu-omitted-bookmarks)
                count                         (1+ count)))))
    (if (<= count 0)
        (message "No marked bookmarks")
      (setq bmkp-bmenu-filter-function  nil
            bmkp-bmenu-title            "All Bookmarks"
            bmkp-latest-bookmark-alist  bookmark-alist)
      (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
      (message "UN-omitted %d bookmarks" count)))
  (when (and (fboundp 'fit-frame-if-one-window)
             (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
    (fit-frame-if-one-window)))

;;;###autoload (autoload 'bmkp-bmenu-show-only-omitted-bookmarks "bookmark+")
(defun bmkp-bmenu-show-only-omitted-bookmarks ()  ; Bound to `- S' in bookmark list to show only omitted
  "Show only the omitted bookmarks.
You can then mark some of them and use `\\<bookmark-bmenu-mode-map>\\[bmkp-bmenu-omit/unomit-marked]' to
 make those that are marked available again for the bookmark list."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unless bmkp-bmenu-omitted-bookmarks (error "No omitted bookmarks")) ; Cannot use macro for this.
  (setq bmkp-bmenu-filter-function  'bmkp-omitted-alist-only
        bmkp-bmenu-title            "Omitted Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only omitted bookmarks are shown now")))


;;(@* "Search-and-Replace Locations of Marked Bookmarks")
;;  *** Search-and-Replace Locations of Marked Bookmarks ***

(when (> emacs-major-version 22)
  (defun bmkp-bmenu-isearch-marked-bookmarks (&optional allp include-omitted-p)
                                        ; Bound to `M-s a C-s' in bookmark list
    "Isearch the marked bookmark locations, in their current order.
If no bookmark is marked, search the bookmark of the current line.

With a non-negative prefix arg, search all bookmarks.

Omitted bookmarks are excluded, by default.  With a negative prefix
arg, any that are marked are included."
    (interactive (list (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                       (and current-prefix-arg  (<  (prefix-numeric-value current-prefix-arg) 0))))
    (bmkp-bmenu-barf-if-not-in-menu-list)
    (let ((bookmarks        (mapcar #'car (bmkp-sort-omit
                                           (bmkp-bmenu-marked-or-this-or-all allp include-omitted-p))))
          (bmkp-use-region  nil))       ; Suppress region handling.
      (bmkp-isearch-bookmarks bookmarks))) ; Defined in `bookmark+-1.el'.

  (defun bmkp-bmenu-isearch-marked-bookmarks-regexp (&optional allp include-omitted-p)
                                        ; `M-s a M-C-s' in bookmark list
    "Regexp Isearch the marked bookmark locations, in their current order.
If no bookmark is marked, search the bookmark of the current line.

With a non-negative prefix arg, search all bookmarks.

Omitted bookmarks are excluded, by default.  With a negative prefix
arg, any that are marked are included."
    (interactive (list (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                       (and current-prefix-arg  (<  (prefix-numeric-value current-prefix-arg) 0))))
    (bmkp-bmenu-barf-if-not-in-menu-list)
    (let ((bookmarks        (mapcar #'car (bmkp-sort-omit
                                           (bmkp-bmenu-marked-or-this-or-all allp include-omitted-p))))
          (bmkp-use-region  nil))       ; Suppress region handling.
      (bmkp-isearch-bookmarks-regexp bookmarks)))) ; Defined in `bookmark+-1.el'.

;;;###autoload (autoload 'bmkp-bmenu-search-marked-bookmarks-regexp "bookmark+")
(defun bmkp-bmenu-search-marked-bookmarks-regexp (regexp &optional allp include-omitted-p)
                                        ; `M-s a M-s' in bookmark list
  "Search the marked file bookmarks, in their current order, for REGEXP.
Use `\\[tags-loop-continue]' to advance among the search hits.
Marked directory and non-file bookmarks are ignored.

If no bookmark is marked, search the bookmark of the current line.

With a non-negative prefix arg, search all bookmarks.

Omitted bookmarks are excluded, by default.  With a negative prefix
arg, any that are marked are included."
  (interactive (list (bmkp-read-regexp "Search marked file bookmarks (regexp): ")
                     (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                     (and current-prefix-arg  (<  (prefix-numeric-value current-prefix-arg) 0))))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (tags-search regexp '(let ((files  ())
                             file)
                        (dolist (bmk  (bmkp-sort-omit
                                       (bmkp-bmenu-marked-or-this-or-all allp include-omitted-p)))
                          (setq file  (bookmark-get-filename bmk))
                          (when (and (not (equal bmkp-non-file-filename file))
                                     (not (file-directory-p file)))
                            (push file files)))
                        (setq files  (nreverse files)))))

;;;###autoload (autoload 'bmkp-bmenu-query-replace-marked-bookmarks-regexp "bookmark+")
(defun bmkp-bmenu-query-replace-marked-bookmarks-regexp (from to ; Bound to `M-q' in bookmark list
                                                         &optional delimited include-omitted-p)
  "`query-replace-regexp' FROM with TO, for all marked file bookmarks.
If you exit (`\\[keyboard-quit]', `RET' or `q'), you can use `\\[tags-loop-continue]' to resume where
you left off.

If no bookmark is marked, act on the bookmark of the current line.

A non-negative prefix arg means replace only word-delimited matches.

Omitted bookmarks are excluded, by default.  With a non-positive
prefix arg, any that are marked are included."
  (interactive (let ((common  (query-replace-read-args "Query replace regexp in marked files" t t)))
                 (list (nth 0 common)
                       (nth 1 common)
                       (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                       (and current-prefix-arg  (<= (prefix-numeric-value current-prefix-arg) 0)))))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (tags-query-replace from to delimited
		      '(let ((files  ())
                             file)
                        (dolist (bmk  (bmkp-sort-omit
                                       (bmkp-bmenu-marked-or-this-or-all nil include-omitted-p)))
                          (setq file  (bookmark-get-filename bmk))
                          (let ((buffer  (get-file-buffer file)))
                            (when (and buffer  (with-current-buffer buffer buffer-read-only))
                              (error "File `%s' is visited read-only" file)))
                          (when (and (not (equal bmkp-non-file-filename file))
                                     (not (file-directory-p file)))
                            (push file files)))
                        (setq files  (nreverse files)))))


;;(@* "Tags")
;;  *** Tags ***

;; Not bound, but `T 0' is `bmkp-remove-all-tags'.
;;;###autoload (autoload 'bmkp-bmenu-remove-all-tags "bookmark+")
(defun bmkp-bmenu-remove-all-tags (&optional must-confirm-p)
  "Remove all tags from this bookmark.
Interactively, you are required to confirm."
  (interactive "p")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark  (bookmark-bmenu-bookmark)))
    (when (and must-confirm-p  (null (bmkp-get-tags bookmark)))
      (error "Bookmark has no tags to remove"))
    (when (or (not must-confirm-p)  (y-or-n-p "Remove all tags from this bookmark? "))
      (bmkp-remove-all-tags bookmark))))

;;;###autoload (autoload 'bmkp-bmenu-add-tags "bookmark+")
(defun bmkp-bmenu-add-tags ()           ; Only on `mouse-3' menu in bookmark list.
  "Add some tags to this bookmark."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((nb-added  (bmkp-add-tags (bookmark-bmenu-bookmark) (bmkp-read-tags-completing))))
    (when (and (< nb-added 0)           ; It was untagged but is now tagged.  If `s t' then re-sort.
               (equal bmkp-sort-comparer '((bmkp-tagged-cp) bmkp-alpha-p))) ; Hardcoded value, for now.
      (bmkp-bmenu-sort-tagged-before-untagged))
    nb-added))

;;;###autoload (autoload 'bmkp-bmenu-set-tag-value "bookmark+")
(defun bmkp-bmenu-set-tag-value ()      ; Bound to `T v' in bookmark list
  "Set the value of one of this bookmark's tags."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((this-bmk  (bookmark-bmenu-bookmark)))
    (bmkp-set-tag-value
     this-bmk
     (bmkp-read-tag-completing "Tag: " (mapcar 'bmkp-full-tag (bmkp-get-tags this-bmk)))
     (read (read-string "Value: "))
     nil
     'MSG)))

;;;###autoload (autoload 'bmkp-bmenu-set-tag-value-for-marked "bookmark+")
(defun bmkp-bmenu-set-tag-value-for-marked (tag value &optional allp include-omitted-p msg-p)
                                        ; Bound to `T > v' in bookmark list
  "Set the value of TAG to VALUE, for each of the marked bookmarks.
If any of the bookmarks has no tag named TAG, then add one with VALUE.

If no bookmark is marked, act on the bookmark of the current line.

With a non-negative prefix arg, act on all bookmarks.

Omitted bookmarks are excluded, by default.  With a negative prefix
arg, any that are marked are included.

Non-interactively, non-nil MSG-P means display messages."
  (interactive (list (bmkp-read-tag-completing)
                     (read (read-string "Value: "))
                     (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                     (and current-prefix-arg  (<  (prefix-numeric-value current-prefix-arg) 0))
                     'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when msg-p (message "Setting tag values..."))
  (let ((marked  (bmkp-bmenu-marked-or-this-or-all allp include-omitted-p)))
    (unless marked (error "No marked bookmarks"))
    (when msg-p (message "Setting tag values..."))
    (bmkp-set-tag-value-for-bookmarks marked tag value))
  (when (and msg-p  tag) (message "Setting tag values...done")))

;;;###autoload (autoload 'bmkp-bmenu-remove-tags "bookmark+")
(defun bmkp-bmenu-remove-tags (&optional msg-p) ; Only on `mouse-3' menu in bookmark list.
  "Remove some tags from this bookmark.
Non-interactively, non-nil MSG-P means display messages."
  (interactive "p")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let* ((bmk         (bookmark-bmenu-bookmark))
         (nb-removed  (bmkp-remove-tags bmk
                                        (bmkp-read-tags-completing
                                         (mapcar 'bmkp-full-tag (bmkp-get-tags bmk)) t)
                                        nil
                                        msg-p)))
    (when (and (< nb-removed 0)         ; It was tagged but is now untagged.  If `s t' then re-sort.
               (equal bmkp-sort-comparer '((bmkp-tagged-cp) bmkp-alpha-p))) ; Hardcoded value, for now.
      (bmkp-bmenu-sort-tagged-before-untagged))
    nb-removed))

;;;###autoload (autoload 'bmkp-bmenu-add-tags-to-marked "bookmark+")
(defun bmkp-bmenu-add-tags-to-marked (tags &optional allp include-omitted-p msg-p)
                                        ; Bound to `T > +' in bookmark list
  "Add TAGS to each of the marked bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag, but you are not limited to
choosing existing tags.

If no bookmark is marked, act on the bookmark of the current line.

With a non-negative prefix arg, act on all bookmarks.

Omitted bookmarks are excluded, by default.  With a negative prefix
arg, any that are marked are included.

Non-interactively:
 TAGS is a list of strings.
 Non-nil MSG-P means display messages."
  (interactive (list (bmkp-read-tags-completing)
                     (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                     (and current-prefix-arg  (<  (prefix-numeric-value current-prefix-arg) 0))
                     'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked                (bmkp-bmenu-marked-or-this-or-all allp include-omitted-p))
        (curr-bmk              (bookmark-bmenu-bookmark))
        (some-were-untagged-p  nil))
    (unless marked (error "No marked bookmarks"))
    (when msg-p (message "Adding tags..."))
    (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                    bookmark-save-flag))) ; Save at most once, after `dolist'.
      (dolist (bmk  (mapcar #'car marked))
        (when (< (bmkp-add-tags bmk tags 'NO-UPDATE-P) 0)  (setq some-were-untagged-p  t))))
    (bmkp-tags-list)                    ; Update the tags cache now, after iterate.
    (bmkp-maybe-save-bookmarks)         ; Increments `bookmark-alist-modification-count'.
    (bmkp-refresh-menu-list curr-bmk (not msg-p)) ; Refresh after iterate.
    (when (and some-were-untagged-p  (equal bmkp-sort-comparer '((bmkp-tagged-cp) bmkp-alpha-p)))
      (bmkp-bmenu-sort-tagged-before-untagged))
    (when (and msg-p  tags) (message "Tags added: %S" tags))))

;;;###autoload (autoload 'bmkp-bmenu-remove-tags-from-marked "bookmark+")
(defun bmkp-bmenu-remove-tags-from-marked (tags &optional allp include-omitted-p msg-p)
                                        ; Bound to `T > -' in bookmark list
  "Remove TAGS from each of the marked bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag.

If no bookmark is marked, act on the bookmark of the current line.

With a non-negative prefix arg, act on all bookmarks.

Omitted bookmarks are excluded, by default.  With a negative prefix
arg, any that are marked are included.

Non-interactively, non-nil MSG-P means display messages."
  (interactive
   (let ((tgs  ())
         (all  (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0)))
         (omt  (and current-prefix-arg  (<  (prefix-numeric-value current-prefix-arg) 0))))
           
     (dolist (bmk  (bmkp-bmenu-marked-or-this-or-all all omt))
       (setq tgs  (bmkp-set-union tgs (bmkp-get-tags bmk))))
     (unless tgs (error "No tags to remove"))
     (list (bmkp-read-tags-completing tgs t) all omt 'MSG)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked    (if allp
                       bookmark-alist
                     (or (if include-omitted-p
                             (bmkp-marked-bookmarks-only)
                           (bmkp-remove-if #'bmkp-omitted-bookmark-p (bmkp-marked-bookmarks-only)))
                         (and (bookmark-bmenu-bookmark)
                              (list (bookmark-get-bookmark (bookmark-bmenu-bookmark)))))))
        (curr-bmk  (bookmark-bmenu-bookmark))
        (some-are-now-untagged-p  nil))
    (unless marked (error "No marked bookmarks"))
    (when msg-p (message "Removing tags..."))
    (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                    bookmark-save-flag))) ; Save at most once, after `dolist'.
      (dolist (bmk  (mapcar #'car marked))
        (when (< (bmkp-remove-tags bmk tags 'NO-UPDATE-P) 0)  (setq some-are-now-untagged-p  t))))
    (bmkp-tags-list)                    ; Update the tags cache now, after iterate.
    (bmkp-maybe-save-bookmarks)         ; Increments `bookmark-alist-modification-count'.
    (bmkp-refresh-menu-list curr-bmk (not msg-p)) ; Refresh after iterate.
    (when (and some-are-now-untagged-p  (equal bmkp-sort-comparer '((bmkp-tagged-cp) bmkp-alpha-p)))
      (bmkp-bmenu-sort-tagged-before-untagged))
    (when (and msg-p  tags) (message "Tags removed: %S" tags))))

;;;###autoload (autoload 'bmkp-bmenu-list-tags-of-marked "bookmark+")
(defun bmkp-bmenu-list-tags-of-marked (fullp &optional msg-p)
                                        ; Bound to `T > l' in bookmark list
  "List the tags used in the marked bookmarks.
Show the list in the minibuffer or, if not enough space, in buffer
`*All Tags*'.  The tags are listed alphabetically, respecting option
`case-fold-search'.

With no prefix arg, list only the tag names.  With a prefix arg, list
the full alist of tags.  Note that when the full tags alist is shown,
the same tag name appears once for each of its different values.

Non-interactively, non-nil MSG-P means display a status message."
  (interactive "P\np")
  (require 'pp)
  (when msg-p (message "Gathering tags..."))
  (pp-display-expression (sort (let ((bookmark-alist  (bmkp-marked-bookmarks-only))
                                     bmkp-tags-alist) ; Prevent updating it.
                                 (bmkp-tags-list (not fullp) t))
                               (if fullp
                                   (lambda (t1 t2) (bmkp-string-less-case-fold-p (car t1) (car t2)))
                                 'bmkp-string-less-case-fold-p))
                         "*Tags of Marked Bookmarks*"))

;;;###autoload (autoload 'bmkp-bmenu-mark-bookmarks-tagged-regexp "bookmark+")
(defun bmkp-bmenu-mark-bookmarks-tagged-regexp (regexp &optional notp no-re-sort-p msg-p)
                                        ; `T m %' in bookmark list
  "Mark bookmarks any of whose tags match REGEXP.
With a prefix arg, mark all that are tagged but have no matching tags.

If any bookmark was unmarked before, and if the sort order is marked
first or last (`s >'), then re-sort.

Non-interactively:
* Non-nil NOTP: see prefix arg, above.
* Non-nil optional arg NO-RE-SORT-P inhibits re-sorting.
* Non-nil optional arg MSG-P means display a status message."
  (interactive (list (bmkp-read-regexp "Regexp: ") current-prefix-arg nil
                     (prefix-numeric-value current-prefix-arg)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((count      0)
        (nb-marked  (length bmkp-bmenu-marked-bookmarks))
        tags anyp)
    (save-excursion
      (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
      (when msg-p (message "Updating bookmark-list display..."))
      (while (not (eobp))
        (setq tags  (bmkp-get-tags (bookmark-bmenu-bookmark))
              anyp  (and tags  (bmkp-some (lambda (tag) (bmkp-string-match-p regexp (bmkp-tag-name tag)))
                                          tags)))
        (if (not (and tags  (if notp (not anyp) anyp)))
            (forward-line 1)
          (bookmark-bmenu-mark 'NO-RE-SORT-P)
          (setq count  (1+ count)))))
    (unless no-re-sort-p
      ;; If some were unmarked before, and if sort order is `s >', then re-sort.
      (when (and (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p))
                 (/= nb-marked (length bmkp-bmenu-marked-bookmarks)))
        (let ((curr-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
          (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk)))))
    (when msg-p (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload (autoload 'bmkp-bmenu-mark-bookmarks-tagged-all "bookmark+")
(defun bmkp-bmenu-mark-bookmarks-tagged-all (tags &optional nonep msg-p) ; `T m *' in bookmark list
  "Mark all visible bookmarks that are tagged with *each* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
any tags at all (i.e., at least one tag).

With a prefix arg, mark all that are *not* tagged with *any* TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags nonep nil nil msg-p))

;;;###autoload (autoload 'bmkp-bmenu-mark-bookmarks-tagged-none "bookmark+")
(defun bmkp-bmenu-mark-bookmarks-tagged-none (tags &optional allp msg-p) ; `T m ~ +' in bookmark list
  "Mark all visible bookmarks that are not tagged with *any* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all.

With a prefix arg, mark all that are tagged with *each* tag in TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags (not allp) nil nil msg-p))

;;;###autoload (autoload 'bmkp-bmenu-mark-bookmarks-tagged-some "bookmark+")
(defun bmkp-bmenu-mark-bookmarks-tagged-some (tags &optional somenotp msg-p) ; `T m +' in bookmark list
  "Mark all visible bookmarks that are tagged with *some* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
any tags at all.

With a prefix arg, mark all that are *not* tagged with *all* TAGS.

Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags somenotp nil nil msg-p))

;;;###autoload (autoload 'bmkp-bmenu-mark-bookmarks-tagged-not-all "bookmark+")
(defun bmkp-bmenu-mark-bookmarks-tagged-not-all (tags &optional somep msg-p) ; `T m ~ *' in bmk list
  "Mark all visible bookmarks that are *not* tagged with *all* TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all.

With a prefix arg, mark all that are tagged with *some* tag in TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags (not somep) nil nil msg-p))

;;;###autoload (autoload 'bmkp-bmenu-unmark-bookmarks-tagged-regexp "bookmark+")
(defun bmkp-bmenu-unmark-bookmarks-tagged-regexp (regexp &optional notp no-re-sort-p msg-p)
                                        ; `T u %' in bookmark list
  "Unmark bookmarks any of whose tags match REGEXP.
With a prefix arg, mark all that are tagged but have no matching tags.

If any bookmark was marked before, and if the sort order is marked
first or last (`s >'), then re-sort.

Non-interactively:
* Non-nil NOTP: see prefix arg, above.
* Non-nil optional arg NO-RE-SORT-P inhibits re-sorting.
* Non-nil optional arg MSG-P means display a status message."
  (interactive (list (bmkp-read-regexp "Regexp: ") current-prefix-arg nil
                     (prefix-numeric-value current-prefix-arg)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((count      0)
        (nb-marked  (length bmkp-bmenu-marked-bookmarks))
        tags anyp)
    (save-excursion
      (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
      (when msg-p (message "Updating bookmark-list display..."))
      (while (not (eobp))
        (setq tags  (bmkp-get-tags (bookmark-bmenu-bookmark))
              anyp  (and tags  (bmkp-some (lambda (tag) (bmkp-string-match-p regexp (bmkp-tag-name tag)))
                                          tags)))
        (if (not (and tags  (if notp (not anyp) anyp)))
            (forward-line 1)
          (bookmark-bmenu-unmark nil 'NO-RE-SORT-P)
          (setq count  (1+ count)))))
    (unless no-re-sort-p
      ;; If some were marked before, and if sort order is `s >', then re-sort.
      (when (and (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p))
                 (/= nb-marked (length bmkp-bmenu-marked-bookmarks)))
        (let ((curr-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
          (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk)))))
    (when msg-p (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload (autoload 'bmkp-bmenu-unmark-bookmarks-tagged-all "bookmark+")
(defun bmkp-bmenu-unmark-bookmarks-tagged-all (tags &optional nonep msg-p) ; `T u *' in bookmark list
  "Unmark all visible bookmarks that are tagged with *each* tag in TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
any tags at all.

With a prefix arg, unmark all that are *not* tagged with *any* TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags nonep 'UNMARK nil msg-p))

;;;###autoload (autoload 'bmkp-bmenu-unmark-bookmarks-tagged-none "bookmark+")
(defun bmkp-bmenu-unmark-bookmarks-tagged-none (tags &optional allp msg-p) ; `T u ~ +' in bookmark list
  "Unmark all visible bookmarks that are *not* tagged with *any* TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
no tags at all.

With a prefix arg, unmark all that are tagged with *each* tag in TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags (not allp) 'UNMARK nil msg-p))

;;;###autoload (autoload 'bmkp-bmenu-unmark-bookmarks-tagged-some "bookmark+")
(defun bmkp-bmenu-unmark-bookmarks-tagged-some (tags &optional somenotp msg-p) ; `T u +' in bmk list
  "Unmark all visible bookmarks that are tagged with *some* tag in TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
any tags at all.

With a prefix arg, unmark all that are *not* tagged with *all* TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags somenotp 'UNMARK nil msg-p))

;;;###autoload (autoload 'bmkp-bmenu-unmark-bookmarks-tagged-not-all "bookmark+")
(defun bmkp-bmenu-unmark-bookmarks-tagged-not-all (tags &optional somep msg-p) ; `T u ~ *' in bmk list
  "Unmark all visible bookmarks that are *not* tagged with *all* TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
no tags at all.

With a prefix arg, unmark all that are tagged with *some* TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags (not somep) 'UNMARK nil msg-p))

(defun bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none (tags &optional nonep unmarkp no-re-sort-p msg-p)
  "Mark or unmark visible bookmarks tagged with all or none of TAGS.
TAGS is a list of strings, the tag names.
Non-nil NONEP means mark/unmark bookmarks that have none of the TAGS.
Non-nil UNMARKP means unmark; nil means mark.
Non-nil NO-RE-SORT-P inhibits re-sorting.
Non-nil MSG-P means display a status message.

As a special case, if TAGS is empty, then mark or unmark the bookmarks
that have any tags at all, or if NONEP is non-nil then mark or unmark
those that have no tags at all.

If any bookmark was (un)marked before but is not afterward, and if the
sort order is marked first or last (`s >'), then re-sort."
  (with-current-buffer "*Bookmark List*"
    (let ((count      0)
          (nb-marked  (length bmkp-bmenu-marked-bookmarks))
          bmktags presentp)
      (save-excursion
        (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
        (when msg-p (message "Updating bookmark-list display..."))
        (while (not (eobp))
          (setq bmktags  (bmkp-get-tags (bookmark-bmenu-bookmark)))
          (if (not (if (null tags)
                       (if nonep (not bmktags) bmktags)
                     (and bmktags  (catch 'bmkp-b-mu-b-t-an
                                     (dolist (tag  tags)
                                       (setq presentp  (assoc-default tag bmktags nil t))
                                       (unless (if nonep (not presentp) presentp)
                                         (throw 'bmkp-b-mu-b-t-an nil)))
                                     t))))
              (forward-line 1)
            (if unmarkp (bookmark-bmenu-unmark nil 'NO-RE-SORT-P) (bookmark-bmenu-mark 'NO-RE-SORT-P))
            (setq count  (1+ count)))))
      (unless no-re-sort-p
        ;; If some were (un)marked before but not afterward, and if sort order is `s >', then re-sort.
        (when (and (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p))
                   (/= nb-marked (length bmkp-bmenu-marked-bookmarks)))
          (let ((curr-bmk  (bookmark-bmenu-bookmark)))
            (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
            (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk)))))
      (when msg-p
        (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count))))))

(defun bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all (tags &optional notallp unmarkp
                                                             no-re-sort-p msg-p)
  "Mark or unmark visible bookmarks tagged with any or not all of TAGS.
TAGS is a list of strings, the tag names.
Non-nil NOTALLP means mark/unmark bookmarks that do not have all TAGS.
Non-nil UNMARKP means unmark; nil means mark.
Non-nil NO-RE-SORT-P inhibits re-sorting.
Non-nil MSG-P means display a status message.

As a special case, if TAGS is empty, then mark or unmark the bookmarks
that have any tags at all, or if NOTALLP is non-nil then mark or
unmark those that have no tags at all.

If any bookmark was (un)marked before but is not afterward, and if the
sort order is marked first or last (`s >'), then re-sort."
  (with-current-buffer "*Bookmark List*"
    (let ((count      0)
          (nb-marked  (length bmkp-bmenu-marked-bookmarks))
          bmktags presentp)
      (save-excursion
        (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
        (when msg-p (message "Updating bookmark-list display..."))
        (while (not (eobp))
          (setq bmktags  (bmkp-get-tags (bookmark-bmenu-bookmark)))
          (if (not (if (null tags)
                       (if notallp (not bmktags) bmktags)
                     (and bmktags  (catch 'bmkp-b-mu-b-t-sna
                                     (dolist (tag  tags)
                                       (setq presentp  (assoc-default tag bmktags nil t))
                                       (when (if notallp (not presentp) presentp)
                                         (throw 'bmkp-b-mu-b-t-sna t)))
                                     nil))))
              (forward-line 1)
            (if unmarkp (bookmark-bmenu-unmark nil 'NO-RE-SORT-P) (bookmark-bmenu-mark 'NO-RE-SORT-P))
            (setq count  (1+ count)))))
      (unless no-re-sort-p
        ;; If some were (un)marked before but not afterward, and if sort order is `s >', then re-sort.
        (when (and (equal bmkp-sort-comparer '((bmkp-marked-cp) bmkp-alpha-p))
                   (/= nb-marked (length bmkp-bmenu-marked-bookmarks)))
          (let ((curr-bmk  (bookmark-bmenu-bookmark)))
            (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
            (when curr-bmk (bmkp-bmenu-goto-bookmark-named curr-bmk)))))
      (when msg-p
        (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count))))))

;;;###autoload (autoload 'bmkp-bmenu-copy-tags "bookmark+")
(defun bmkp-bmenu-copy-tags (&optional msg-p) ; `T c', `T M-w', `mouse-3' menu in bookmark list.
  "Copy tags from this bookmark, so you can paste them to another bookmark.
NOTE: It is by design that you can *remove all* tags from a bookmark
by copying an empty set of tags and then pasting to that bookmark
using replacement.  So be careful pasting with replacement.  If you
want to be sure that you do not replace tags with an empty list of
tags, you can check the value of variable `bmkp-copied-tags' before
pasting."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-copy-tags (bookmark-bmenu-bookmark) msg-p))

;;;###autoload (autoload 'bmkp-bmenu-paste-add-tags "bookmark+")
(defun bmkp-bmenu-paste-add-tags (&optional msg-p) ; `T p', `T C-y', `mouse-3' menu in bookmark list.
  "Add tags to this bookmark that were copied from another bookmark."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-paste-add-tags (bookmark-bmenu-bookmark) nil msg-p))

;;;###autoload (autoload 'bmkp-bmenu-paste-replace-tags "bookmark+")
(defun bmkp-bmenu-paste-replace-tags (&optional msg-p) ; `T q', `mouse-3' menu.
  "Replace tags for this bookmark with those copied from another bookmark.
NOTE: It is by design that you can *remove all* tags from a bookmark
by copying an empty set of tags and then pasting to that bookmark
using this command.  So be careful using it.  If you want to be sure
that you do not replace tags with an empty list of tags, you can check
the value of variable `bmkp-copied-tags' before pasting."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-paste-replace-tags (bookmark-bmenu-bookmark) nil msg-p))

;;;###autoload (autoload 'bmkp-bmenu-paste-add-tags-to-marked "bookmark+")
(defun bmkp-bmenu-paste-add-tags-to-marked (&optional allp include-omitted-p msg-p)
                                        ; Bound to `T > p', `T > C-y' in bookmark list
  "Add tags that were copied from another bookmark to the marked bookmarks.
If no bookmark is marked, act on the bookmark of the current line.

With a non-negative prefix arg, act on all bookmarks.

Omitted bookmarks are excluded, by default.  With a negative prefix
arg, any that are marked are included.

Non-interactively, non-nil MSG-P means display messages."
  (interactive (list (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                     (and current-prefix-arg  (<  (prefix-numeric-value current-prefix-arg) 0))
                     'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked  (bmkp-bmenu-marked-or-this-or-all allp include-omitted-p))
        (bmk     (bookmark-bmenu-bookmark)))
    (unless marked (error "No marked bookmarks"))
    (when msg-p (message "Adding tags..."))
    (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                    bookmark-save-flag))) ; Save at most once, after `dolist'.
      (dolist (bmk  marked) (bmkp-paste-add-tags bmk 'NO-UPDATE-P)))
    (bmkp-tags-list)                    ; Update the tags cache now, after iterate.
    (bmkp-maybe-save-bookmarks)         ; Increments `bookmark-alist-modification-count'.
    (bmkp-refresh-menu-list bmk (not msg-p)) ; Refresh after iterate.
    (when msg-p (message "Tags added: %S" bmkp-copied-tags))))

;;;###autoload (autoload 'bmkp-bmenu-paste-replace-tags-for-marked "bookmark+")
(defun bmkp-bmenu-paste-replace-tags-for-marked (&optional allp include-omitted-p msg-p) ; `T > q'
  "Replace tags for the marked bookmarks with tags copied previously.
NOTE: It is by design that you can *remove all* tags from a bookmark
by copying an empty set of tags and then pasting to that bookmark
using this command.  So be careful using it.  If you want to be sure
that you do not replace tags with an empty list of tags, you can check
the value of variable `bmkp-copied-tags' before pasting.

If no bookmark is marked, act on the bookmark of the current line.

With a non-negative prefix arg, act on all bookmarks.

Omitted bookmarks are excluded, by default.  With a negative prefix
arg, any that are marked are included.

Non-interactively, non-nil MSG-P means display messages."
  (interactive (list (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                     (and current-prefix-arg  (<  (prefix-numeric-value current-prefix-arg) 0))
                     'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked  (bmkp-bmenu-marked-or-this-or-all allp include-omitted-p))
        (bmk     (bookmark-bmenu-bookmark)))
    (unless marked (error "No marked bookmarks"))
    (when msg-p (message "Replacing tags..."))
    (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                    bookmark-save-flag))) ; Save at most once, after `dolist'.
      (dolist (bmk  marked) (bmkp-paste-replace-tags bmk 'NO-UPDATE-P)))
    (bmkp-tags-list)                    ; Update the tags cache now, after iterate.
    (bmkp-maybe-save-bookmarks)         ; Increments `bookmark-alist-modification-count'.
    (bmkp-refresh-menu-list bmk (not msg-p)) ; Refresh after iterate.
    (when msg-p (message "Replacement tags: %S" bmkp-copied-tags))))


;;(@* "General Menu-List (`-*bmenu-*') Commands and Functions")
;;  *** General Menu-List (`-*bmenu-*') Commands and Functions ***

;;;###autoload (autoload 'bmkp-bmenu-show-or-edit-annotation "bookmark+")
(defun bmkp-bmenu-show-or-edit-annotation (editp msg-p) ; Bound to `a' in bookmark list.
  "Show annotation for current bookmark in another window.  `C-u': Edit.
With no prefix arg, show the annotation.  With a prefix arg, edit it."
  (interactive "P\np")
  (if editp (bookmark-bmenu-edit-annotation) (bookmark-bmenu-show-annotation msg-p)))

;;;###autoload (autoload 'bmkp-bmenu-jump-to-marked "bookmark+")
(defun bmkp-bmenu-jump-to-marked ()
  "Jump to each bookmark marked `>', in another window.
Unlike `bookmark-bmenu-select', this command:
* does not bury buffer `*Bookmark List*' or replace it in its window
* does not unmark the marked bookmarks
* does not include the current bookmark - only the marked are accessed"
  (interactive)
  (dolist (bmk  bmkp-bmenu-marked-bookmarks)
    (bookmark-jump-other-window bmk)))

;;;###autoload (autoload 'bmkp-bmenu-w32-open "bookmark+")
(defun bmkp-bmenu-w32-open ()           ; Bound to `M-RET' in bookmark list.
  "Use `w32-browser' to open this bookmark."
  (interactive) (let ((bmkp-use-w32-browser-p  t))  (bookmark-bmenu-this-window)))

;; $$$$$$ FIXME?: If `Open' action opens a window-manager window, it might be behind all Emacs frames.
;;;###autoload (autoload 'bmkp-bmenu-w32-open-with-mouse "bookmark+")
(defun bmkp-bmenu-w32-open-with-mouse (event) ; Bound to `M-mouse-2' in bookmark list.
  "Use `w32-browser' to open the bookmark clicked."
  (interactive "e")
  (let ((bmkp-use-w32-browser-p  t)
        (bmk                     (with-current-buffer (window-buffer (posn-window (event-end event)))
                                   (bmkp-bmenu-barf-if-not-in-menu-list)
                                   (save-excursion (goto-char (posn-point (event-end event)))
                                                   (bookmark-bmenu-bookmark)))))
    (bookmark-handle-bookmark bmk)
    ;; Probably do not want this.  Users can use `jump-fn' tag if need be.
    ;; (let ((orig-buff  (current-buffer))) ; Used by `crosshairs-highlight'.
    ;;   (run-hooks 'bookmark-after-jump-hook))
    (let ((jump-fn  (bmkp-get-tag-value bmk "bmkp-jump")))
      (when jump-fn (funcall jump-fn)))
    (when bookmark-automatically-show-annotations (bookmark-show-annotation bmk))))

;;;###autoload (autoload 'bmkp-bmenu-w32-jump-to-marked "bookmark+")
(defun bmkp-bmenu-w32-jump-to-marked ()    ; Bound to `M-o' in bookmark-list.
  "Use `w32-browser' to open this bookmark and all marked bookmarks."
  (interactive) (let ((bmkp-use-w32-browser-p  t))  (bmkp-bmenu-jump-to-marked)))

;;;###autoload (autoload 'bmkp-bmenu-mode-status-help "bookmark+")
(defun bmkp-bmenu-mode-status-help ()   ; Bound to `C-h m' and `?' in bookmark list
  "`describe-mode' + current status of `*Bookmark List*' + face legend."
  (interactive)
  (unless (string= (buffer-name) "*Help*") (bmkp-bmenu-barf-if-not-in-menu-list))
  (with-current-buffer (get-buffer-create "*Help*")
    (bmkp-with-help-window "*Help*"
      (let ((buffer-read-only  nil)
            top)
        (erase-buffer)
        (save-excursion
          (let ((standard-output  (current-buffer)))
            (if (> emacs-major-version 21)
                (describe-function-1 'bookmark-bmenu-mode)
              (describe-function-1 'bookmark-bmenu-mode nil t)))
          (help-setup-xref (list #'bmkp-bmenu-mode-status-help) (interactive-p))
          (goto-char (point-min))
          (search-forward               ; This depends on the text written by `bookmark-bmenu-mode'.
           "More bookmarking help below." nil t)
          (delete-region (point-min) (point)) ; Get rid of intro from `describe-function'.
          (insert "*************************** Bookmark List ***************************\n\n")
          (insert "Major mode for editing a list of bookmarks.\n")
          (insert "Each line in `*Bookmark List*' represents an Emacs bookmark.\n")
          (setq top  (copy-marker (point)))
          ;; Add buttons to access help and Customize.
          ;; Not for Emacs 21.3 - its `help-insert-xref-button' signature is different.
          (when (and (> emacs-major-version 21) ; In `help-mode.el'.
                     (condition-case nil (require 'help-mode nil t) (error nil))
                     (fboundp 'help-insert-xref-button))
            (goto-char (point-min))
            (help-insert-xref-button "[Doc in Commentary]" 'bmkp-commentary-button)
            (insert "           ")
            (help-insert-xref-button "[Doc on the Web]" 'bmkp-help-button)
            (insert "           ")
            (help-insert-xref-button "[Customize]" 'bmkp-customize-button)
            (insert "\n\n")
            (goto-char (point-max))
            (insert (substitute-command-keys
                     "\nSend a Bookmark+ bug report: `\\[bmkp-send-bug-report]'.\n\n"))
            (help-insert-xref-button "[Doc in Commentary]" 'bmkp-commentary-button)
            (insert "           ")
            (help-insert-xref-button "[Doc on the Web]" 'bmkp-help-button)
            (insert "           ")
            (help-insert-xref-button "[Customize]" 'bmkp-customize-button)
            (insert "\n\n")
            (goto-char (point-min))
            (forward-line 2))
          (goto-char top)
          (insert (format
                   "\n\nCurrent Status\n--------------\n
Bookmark file:\t%s\nSorted:\t\t\t%s\nFiltering:\t\t%s\nMarked:\t\t\t%d\nOmitted:\t\t%d\n\
Autosave bookmarks:\t%s\nAutosave list display:\t%s\n\n\n"
                   bmkp-current-bookmark-file
                   (if (not bmkp-sort-comparer)
                       "no"
                     (format "%s%s" (or (bmkp-current-sort-order)  "")
                             ;; Code essentially the same as found in `bmkp-msg-about-sort-order'.
                             (if (not (and (consp bmkp-sort-comparer) ; Ordinary single predicate
                                           (consp (car bmkp-sort-comparer))))
                                 (if bmkp-reverse-sort-p "; reversed" "")
                               (if (not (cadr (car bmkp-sort-comparer)))
                                   ;; Single PRED.
                                   (if (or (and bmkp-reverse-sort-p  (not bmkp-reverse-multi-sort-p))
                                           (and bmkp-reverse-multi-sort-p  (not bmkp-reverse-sort-p)))
                                       "; reversed"
                                     "")
                                 ;; In case we want to distinguish:
                                 ;; (if (and bmkp-reverse-sort-p
                                 ;;          (not bmkp-reverse-multi-sort-p))
                                 ;;     "; reversed"
                                 ;;   (if (and bmkp-reverse-multi-sort-p
                                 ;;            (not bmkp-reverse-sort-p))
                                 ;;       "; reversed +"
                                 ;;     ""))

                                 ;; At least two PREDs.
                                 (cond ((and bmkp-reverse-sort-p  (not bmkp-reverse-multi-sort-p))
                                        "; reversed")
                                       ((and bmkp-reverse-multi-sort-p  (not bmkp-reverse-sort-p))
                                        "; each predicate group reversed")
                                       ((and bmkp-reverse-multi-sort-p  bmkp-reverse-sort-p)
                                        "; order of predicate groups reversed")
                                       (t ""))))))
                   (or (and bmkp-bmenu-filter-function  (downcase bmkp-bmenu-title))  "none")
                   (length bmkp-bmenu-marked-bookmarks)
                   (length bmkp-bmenu-omitted-bookmarks)
                   (if bookmark-save-flag "yes" "no")
                   (if bmkp-bmenu-state-file "yes" "no")))

          ;; Add markings legend.
          (let ((mm   "  >")
                (DD   "  D")
                (tt   "  t")
                (aa   "  a")
                (XX   "  X")
                (mod  "  *"))
            (put-text-property 2 3 'face 'bmkp->-mark mm)
            (put-text-property 2 3 'face 'bmkp-D-mark DD)
            (put-text-property 2 3 'face 'bmkp-t-mark tt)
            (put-text-property 2 3 'face 'bmkp-a-mark aa)
            (put-text-property 2 3 'face 'bmkp-X-mark XX)
            (put-text-property 2 3 'face 'bmkp-*-mark mod)
            (insert "Legend for Markings\n-------------------\n\n")
            (insert (concat mm  "  marked\n"))
            (insert (concat DD  "  flagged for deletion                     (`x' to delete all such)\n"))
            (insert (concat tt  "  tagged                                   (`C-h C-RET' to see)\n"))
            (insert (concat aa  "  annotated                                (`C-h C-RET' to see)\n"))
            (insert (concat mod "  modified (not saved)\n"))
            (insert (concat XX  "  temporary (will not be saved)\n"))
            (insert "\n\n"))

          ;; Add face legend.
          (let ((gnus             "Gnus\n")
                (no-jump          "Bookmarks you cannot jump to from `*Bookmark List*'\n")
                (info             "Info node\n")
                (man              "Man page\n")
                (url              "URL\n")
                (local-no-region  "Local file with no region\n")
                (local-w-region   "Local file with a region\n")
                (no-file          "No such local file\n")
                (buffer           "Buffer\n")
                (no-buf           "No such buffer now\n")
                (bad              "Possibly invalid bookmark\n")
                (remote           "Remote file/directory or Dired buffer (could have wildcards)\n")
                (sudo             "Remote accessed by `su' or `sudo'\n")
                (local-dir        "Local directory or Dired buffer (could have wildcards)\n")
                (file-handler     "Bookmark with entry `file-handler'\n")
                (bookmark-list    "*Bookmark List*\n")
                (bookmark-file    "Bookmark file\n")
                (snippet          "Snippet\n")
                (desktop          "Desktop\n")
                (sequence         "Sequence\n")
                (variable-list    "Variable list\n")
                (function         "Function\n"))
            (put-text-property 0 (1- (length gnus))          'face 'bmkp-gnus         gnus)
            (put-text-property 0 (1- (length info))          'face 'bmkp-info         info)
            (put-text-property 0 (1- (length man))           'face 'bmkp-man          man)
            (put-text-property 0 (1- (length url))           'face 'bmkp-url          url)
            (put-text-property 0 (1- (length local-no-region))
                               'face 'bmkp-local-file-without-region                  local-no-region)
            (put-text-property 0 (1- (length local-w-region))
                               'face 'bmkp-local-file-with-region                     local-w-region)
            (put-text-property 0 (1- (length no-file))       'face 'bmkp-no-local     no-file)
            (put-text-property 0 (1- (length buffer))        'face 'bmkp-buffer       buffer)
            (put-text-property 0 (1- (length no-buf))        'face 'bmkp-non-file     no-buf)
            (put-text-property 0 (1- (length remote))        'face 'bmkp-remote-file  remote)
            (put-text-property 0 (1- (length sudo))          'face 'bmkp-su-or-sudo   sudo)
            (put-text-property 0 (1- (length local-dir))
                               'face 'bmkp-local-directory                            local-dir)
            (put-text-property 0 (1- (length file-handler))  'face 'bmkp-file-handler file-handler)
            (put-text-property 0 (1- (length bookmark-list))
                               'face 'bmkp-bookmark-list                               bookmark-list)
            (put-text-property 0 (1- (length bookmark-file))
                               'face 'bmkp-bookmark-file                               bookmark-file)
            (put-text-property 0 (1- (length snippet))       'face 'bmkp-snippet       snippet)
            (put-text-property 0 (1- (length desktop))       'face 'bmkp-desktop       desktop)
            (put-text-property 0 (1- (length sequence))      'face 'bmkp-sequence      sequence)
            (put-text-property 0 (1- (length variable-list)) 'face 'bmkp-variable-list variable-list)
            (put-text-property 0 (1- (length function))      'face 'bmkp-function      function)
            (put-text-property 0 (1- (length no-jump))       'face 'bmkp-no-jump       no-jump)
            (put-text-property 0 (1- (length bad))           'face 'bmkp-bad-bookmark  bad)
            (insert "Legend for Bookmark Types\n-------------------------\n\n")
            (when (and (fboundp 'display-images-p)  (display-images-p)
                       bmkp-bmenu-image-bookmark-icon-file
                       (file-readable-p bmkp-bmenu-image-bookmark-icon-file))
              (let ((image  (create-image bmkp-bmenu-image-bookmark-icon-file nil nil :ascent 95)))
                (when image (insert "  ")  (insert-image image)  (insert " Image file\n"))))
            (insert "  " gnus) (insert "  " info) (insert "  " man) (insert "  " url)
            (insert "  " local-no-region) (insert "  " local-w-region) (insert "  " no-file)
            (insert "  " buffer) (insert "  " no-buf) (insert "  " remote) (insert "  " sudo)
            (insert "  " local-dir) (insert "  " file-handler) (insert "  " bookmark-list)
            (insert "  " bookmark-file) (insert "  " snippet) (insert "  " desktop)
            (insert "  " sequence) (insert "  " variable-list) (insert "  " function)
            (insert "  " no-jump) (insert "  " bad)
            (insert "\n\nKeys without prefix `C-x' are available only here (`*Bookmark List*').\n")
            (insert "Keys with prefix `C-x' are available everywhere.\n\n")
            (insert "Remember that you can see all bindings for a prefix key by hitting it,\n")
            (insert "then `C-h'.  E.g., `s C-h' to see keys with prefix `s' (sorting).")))))))

(when (and (> emacs-major-version 21)
           (condition-case nil (require 'help-mode nil t) (error nil))
           (get 'help-xref 'button-category-symbol)) ; In `button.el'
  (define-button-type 'bmkp-help-button
      :supertype 'help-xref
      'help-function #'(lambda () (browse-url "http://www.emacswiki.org/emacs/BookmarkPlus"))
      'help-echo
      (purecopy "mouse-2, RET: Bookmark+ documentation on the Emacs Wiki (requires Internet access)"))
  (define-button-type 'bmkp-commentary-button
      :supertype 'help-xref
      'help-function #'(lambda ()
                         (message "Getting Bookmark+ doc from file commentary...")
                         (finder-commentary "bookmark+-doc")
                         (when (condition-case nil (require 'linkd nil t) (error nil)) (linkd-mode 1))
                         (when (condition-case nil (require 'fit-frame nil t) (error nil))
                           (fit-frame)))
      'help-echo (purecopy "mouse-2, RET: Bookmark+ documentation (no Internet needed)"))
  (define-button-type 'bmkp-customize-button
      :supertype 'help-xref
      'help-function #'(lambda () (customize-group-other-window 'bookmark-plus))
      'help-echo (purecopy "mouse-2, RET: Customize/Browse Bookmark+ Options & Faces")))

;;;###autoload (autoload 'bmkp-bmenu-define-jump-marked-command "bookmark+")
(defun bmkp-bmenu-define-jump-marked-command () ; Bound to `C-c C-j' in bookmark list
  "Define a command to jump to a bookmark that is one of those now marked.
The bookmarks marked now will be those that are completion candidates
for the command (but omitted bookmarks are excluded).
Save the command definition in `bmkp-bmenu-commands-file'."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let* ((cands  (mapcar #'list
                         (bmkp-maybe-unpropertize-bookmark-names
                          (bmkp-remove-if #'(lambda (bmk)
                                              (bmkp-bookmark-name-member bmk bmkp-bmenu-omitted-bookmarks))
                                          bmkp-bmenu-marked-bookmarks))))
         (fn     (intern (read-string "Define command to jump to a bookmark now marked: " nil
                                      bmkp-bmenu-define-command-history)))
         (def    `(defun ,fn (bookmark-name &optional flip-use-region-p)
                   (interactive (list (bmkp-read-bookmark-for-type nil ',cands t) current-prefix-arg))
                   (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))))
    (eval def)
    (with-current-buffer (find-file-noselect bmkp-bmenu-commands-file)
      (goto-char (point-max))
      (let ((print-length           nil)
            (print-level            nil)
            (print-circle           bmkp-propertize-bookmark-names-flag)
            (version-control        (case bookmark-version-control
                                      ((nil)      nil)
                                      (never      'never)
                                      (nospecial  version-control)
                                      (t          t)))
            (require-final-newline  t)
            (errorp                 nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-file bmkp-bmenu-commands-file)
          (file-error (setq errorp  t) (error "CANNOT WRITE FILE `%s'" bmkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))
        (unless errorp (message "Command `%s' defined and saved in file `%s'"
                                fn bmkp-bmenu-commands-file))))))

;;;###autoload (autoload 'bmkp-bmenu-define-command "bookmark+")
(defun bmkp-bmenu-define-command ()     ; Bound to `C-c C-c' in bookmark list
  "Define a command to use the current sort order, filter, and omit list.
Prompt for the command name.  Save the command definition in
`bmkp-bmenu-commands-file'.

The current sort order, filter function, omit list, and title for
buffer `*Bookmark List*' are encapsulated as part of the command.
Use the command at any time to restore them."
  (interactive)
  (let* ((fn   (intern (read-string "Define sort+filter command: " nil
                                    bmkp-bmenu-define-command-history)))
         (def  `(defun ,fn ()
                 (interactive)
                 (setq
                  bmkp-sort-comparer               ',bmkp-sort-comparer
                  bmkp-reverse-sort-p              ',bmkp-reverse-sort-p
                  bmkp-reverse-multi-sort-p        ',bmkp-reverse-multi-sort-p
                  bmkp-bmenu-filter-function       ',bmkp-bmenu-filter-function
                  bmkp-bmenu-filter-pattern        ',bmkp-bmenu-filter-pattern
                  bmkp-bmenu-omitted-bookmarks     ',(bmkp-maybe-unpropertize-bookmark-names
                                                      bmkp-bmenu-omitted-bookmarks)
                  bmkp-bmenu-title                 ',bmkp-bmenu-title
                  bookmark-bmenu-toggle-filenames  ',bookmark-bmenu-toggle-filenames)
                 (bmkp-bmenu-refresh-menu-list)
                 (when (interactive-p)
                   (bmkp-msg-about-sort-order
                    (car (rassoc bmkp-sort-comparer bmkp-sort-orders-alist)))))))
    (eval def)
    (with-current-buffer (find-file-noselect bmkp-bmenu-commands-file)
      (goto-char (point-max))
      (let ((print-length           nil)
            (print-level            nil)
            (print-circle           bmkp-propertize-bookmark-names-flag)
            (version-control        (case bookmark-version-control
                                      ((nil)      nil)
                                      (never      'never)
                                      (nospecial  version-control)
                                      (t          t)))
            (require-final-newline  t)
            (errorp                 nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-file bmkp-bmenu-commands-file)
          (file-error (setq errorp  t) (error "CANNOT WRITE FILE `%s'" bmkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))
        (unless errorp (message "Command `%s' defined and saved in file `%s'"
                                fn bmkp-bmenu-commands-file))))))

;;;###autoload (autoload 'bmkp-bmenu-define-full-snapshot-command "bookmark+")
(defun bmkp-bmenu-define-full-snapshot-command () ; Bound to `C-c C-S-c' (aka `C-c C-C') in bookmark list
  "Define a command to restore the current bookmark-list state.
Prompt for the command name.  Save the command definition in
`bmkp-bmenu-commands-file'.

Be aware that the command definition can be quite large, since it
copies the current bookmark list and accessory lists (hidden
bookmarks, marked bookmarks, etc.).  For a lighter weight command, use
`bmkp-bmenu-define-full-snapshot-command' instead.  That records only
the omit list and the sort & filter information."
  (interactive)
  (let* ((fn   (intern (read-string "Define restore-snapshot command: " nil
                                    bmkp-bmenu-define-command-history)))
         (def  `(defun ,fn ()
                 (interactive)
                 (setq
                  bmkp-sort-comparer                     ',bmkp-sort-comparer
                  bmkp-reverse-sort-p                    ',bmkp-reverse-sort-p
                  bmkp-reverse-multi-sort-p              ',bmkp-reverse-multi-sort-p
                  bmkp-latest-bookmark-alist             ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-latest-bookmark-alist)
                  bmkp-bmenu-omitted-bookmarks           ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-bmenu-omitted-bookmarks 'COPY)
                  bmkp-bmenu-marked-bookmarks            ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-bmenu-marked-bookmarks 'COPY)
                  bmkp-bmenu-filter-function             ',bmkp-bmenu-filter-function
                  bmkp-bmenu-filter-pattern              ',bmkp-bmenu-filter-pattern
                  bmkp-bmenu-title                       ',bmkp-bmenu-title
                  bmkp-last-bmenu-bookmark               ',(and (get-buffer "*Bookmark List*")
                                                                (with-current-buffer
                                                                    (get-buffer "*Bookmark List*")
                                                                  (bmkp-maybe-unpropertize-string
                                                                   (bookmark-bmenu-bookmark) 'COPY)))
                  ;; Use `copy-sequence' here just in case, to avoid circular references when
                  ;; `bmkp-propertize-bookmark-names-flag' is nil.
                  bmkp-last-specific-buffer              ',(copy-sequence bmkp-last-specific-buffer)
                  bmkp-last-specific-file                ',(copy-sequence bmkp-last-specific-file)
                  bookmark-bmenu-toggle-filenames        ',bookmark-bmenu-toggle-filenames
                  bmkp-bmenu-before-hide-marked-alist    ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-bmenu-before-hide-marked-alist 'COPY)
                  bmkp-bmenu-before-hide-unmarked-alist  ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-bmenu-before-hide-unmarked-alist 'COPY)
                  bmkp-last-bookmark-file                ',(copy-sequence
                                                            (convert-standard-filename
                                                             (expand-file-name bmkp-last-bookmark-file)))
                  bmkp-current-bookmark-file             ',(copy-sequence
                                                            (convert-standard-filename
                                                             (expand-file-name
                                                              bmkp-current-bookmark-file))))
                 (let ((bookmark-alist  (bmkp-refresh-latest-bookmark-list))) ; Sets *-latest-* also.
                   (bmkp-bmenu-list-1 'filteredp nil (interactive-p)))
                 (when bmkp-last-bmenu-bookmark
                   (with-current-buffer (get-buffer "*Bookmark List*")
                     (bmkp-bmenu-goto-bookmark-named bmkp-last-bmenu-bookmark)))
                 (when (interactive-p)
                   (bmkp-msg-about-sort-order (car (rassoc bmkp-sort-comparer bmkp-sort-orders-alist)))))))
    (eval def)
    (with-current-buffer (find-file-noselect bmkp-bmenu-commands-file)
      (goto-char (point-max))
      (let ((print-length           nil)
            (print-level            nil)
            (print-circle           bmkp-propertize-bookmark-names-flag)
            (version-control        (case bookmark-version-control
                                      ((nil)      nil)
                                      (never      'never)
                                      (nospecial  version-control)
                                      (t          t)))
            (require-final-newline  t)
            (errorp                 nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-file bmkp-bmenu-commands-file)
          (file-error (setq errorp  t) (error "CANNOT WRITE FILE `%s'" bmkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))
        (unless errorp (message "Command `%s' defined and saved in file `%s'"
                                fn bmkp-bmenu-commands-file))))))

;; We use this because Emacs 20 has no `print-circle'. and otherwise
;; property `bmkp-full-record' would make the state file unreadable.
;;
(defun bmkp-maybe-unpropertize-bookmark-names (list &optional copy)
  "Strip properties from the bookmark names in a copy of LIST.
LIST is a bookmark alist or a list of bookmark names (strings).
Return the updated copy.

Note, however, that this is a shallow copy, so the names are also
stripped within any alist elements of the original LIST.

Non-nil optional arg COPY means copy also each element of LIST.  Use
this if, for example, you have bookmark lists that share bookmarks and
you want to treat the shared bookmarks separately.

Always strip property `face' and internal Icicles properties.  Remove
other text properties only if using Emacs 20 or if option
`bmkp-propertize-bookmark-names-flag' is non-nil."
  (let ((new-list   (copy-sequence list))
        (rem-all-p  (or (not bmkp-propertize-bookmark-names-flag)
                        (< emacs-major-version 21)))) ; Cannot just use (not (boundp 'print-circle)).
    (dolist (bmk  new-list)
      (when (and (consp bmk)  (stringp (car bmk))) (setq bmk  (car bmk)))
      (when (stringp bmk)
        (let ((len  (length bmk)))
          (if rem-all-p
              (set-text-properties 0 len nil bmk)
            (remove-text-properties     ; Remove property `face' and any Icicles internal properties.
             0 len '(face                     nil
                     display                  nil
                     help-echo                nil
                     rear-nonsticky           nil
                     icicle-fancy-candidates  nil
                     icicle-mode-line-help    nil
                     icicle-special-candidate nil
                     icicle-user-plain-dot    nil
                     icicle-whole-candidate   nil
                     invisible                nil)
             bmk)
            (when (boundp 'icicle-candidate-properties-alist) ; Multi-completion indexes + text props.
              (dolist (entry  icicle-candidate-properties-alist)
                (put-text-property 0 len (car (cadr entry)) nil bmk)))))))
    (if copy (mapcar #'copy-sequence new-list) new-list)))

(defun bmkp-maybe-unpropertize-string (string &optional copy)
  "Strip properties from STRING.
Return the unpropertized STRING.
Non-nil optional arg COPY means return a copy of the unpropertized
STRING.  (STRING is modified before the copy is made.)

Do nothing in Emacs 21 or later or if
`bmkp-propertize-bookmark-names-flag' is non-nil.  In these cases,
just return STRING unmodified."
  (unless (and (> emacs-major-version 20) ; Emacs 21+.  Cannot just use (boundp 'print-circle).
               bmkp-propertize-bookmark-names-flag)
    (set-text-properties 0 (length string) nil string)
    (when copy (setq string  (copy-sequence string))))
  string)

;; This is a general command.  It is in this file because it uses macro `bmkp-define-sort-command'
;; and it is used mainly in the bookmark list display.
;;;###autoload (autoload 'bmkp-define-tags-sort-command "bookmark+")
(defun bmkp-define-tags-sort-command (tags &optional msg-p) ; Bound to `T s' in bookmark list
  "Define a command to sort bookmarks in the bookmark list by tags.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.

The new command sorts first by the first tag in TAGS, then by the
second, and so on.

Besides sorting for these specific tags, any bookmark that has a tag
sorts before one that has no tags.  Otherwise, sorting is by bookmark
name, alphabetically.

The name of the new command is `bmkp-bmenu-sort-' followed by the
specified tags, in order, separated by hyphens (`-').  E.g., for TAGS
\(\"alpha\" \"beta\"), the name is `bmkp-bmenu-sort-alpha-beta'.

If you use this function non-interactively, be sure to load library
`bookmark+-mac.el' first."
  (interactive
   (progn (or (condition-case nil       ; Load `bookmark+-mac.el' when called interactively.
                  (load-library "bookmark+-mac") ; Use load-library to ensure latest .elc.
                (error nil))
              (require 'bookmark+-mac))
          (list (bmkp-read-tags-completing) 'MSG)))
  (let ((sort-order  (concat "tags-" (mapconcat #'identity tags "-")))
        (doc-string  (read-string "Doc string for command: "))
        (comparer    ())
        def)
    (dolist (tag  tags)
      (push `(lambda (b1 b2)
              (let ((tags1  (bmkp-get-tags b1))
                    (tags2  (bmkp-get-tags b2)))
                (cond ((and (assoc-default ,tag tags1 nil t)
                            (assoc-default ,tag tags2 nil t))  nil)
                      ((assoc-default ,tag tags1 nil t)        '(t))
                      ((assoc-default ,tag tags2 nil t)        '(nil))
                      ((and tags1  tags2)                      nil)
                      (tags1                                   '(t))
                      (tags2                                   '(nil))
                      (t                                       nil))))
            comparer))
    (setq comparer  (nreverse comparer)
          comparer  (list comparer 'bmkp-alpha-p))
    (eval (setq def  (macroexpand `(bmkp-define-sort-command ,sort-order ,comparer ,doc-string))))
    (with-current-buffer (find-file-noselect bmkp-bmenu-commands-file)
      (goto-char (point-max))
      (let ((print-length           nil)
            (print-level            nil)
            (print-circle           bmkp-propertize-bookmark-names-flag)
            (version-control        (case bookmark-version-control
                                      ((nil)      nil)
                                      (never      'never)
                                      (nospecial  version-control)
                                      (t          t)))
            (require-final-newline  t)
            (errorp                 nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-file bmkp-bmenu-commands-file)
          (file-error (setq errorp  t) (error "CANNOT WRITE FILE `%s'" bmkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))
        (when (and msg-p  (not errorp))
          (message "Defined and saved command `%s'" (concat "bmkp-bmenu-sort-" sort-order)))))))

;;;###autoload (autoload 'bmkp-bmenu-relocate-marked "bookmark+")
(defun bmkp-bmenu-relocate-marked (directory &optional include-omitted-p msgp)
                                        ; Bound to `M-R' in bookmark list
  "Relocate target files of all (visible) bookmarks that are marked `>'.
You are prompted for the relocation target directory.
Return the number of bookmarks relocated to DIRECTORY.

Omitted bookmarks are excluded, by default.  With a prefix arg, any
that are marked are included.

Non-interactively, non-nil MSG-P means display messages."
  (interactive (list (funcall (if (fboundp 'read-directory-name)
                                  #'read-directory-name
                                #'read-file-name)
                              "Relocate targets of marked bookmarks to directory: "
                              default-directory default-directory)
                     current-prefix-arg
                     'MSGP))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((count  0)
        file)
    (dolist (bmk  (bmkp-sort-omit (bmkp-bmenu-marked-or-this-or-all nil include-omitted-p)))
      (when (and (setq file  (bookmark-get-filename bmk))
                 (not (equal file bmkp-non-file-filename)))
        (setq file   (file-name-nondirectory file)
              count  (1+ count))
        (bookmark-set-filename bmk (expand-file-name file directory))
        (setq bookmark-alist-modification-count
              (1+ bookmark-alist-modification-count))))
    (when (bookmark-time-to-save-p) (bookmark-save))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (when msgp
      (if (> count 0)
          (message "Relocated %d bookmark%s" count (if (= 1 count) "" "s"))
        (message "No bookmarks relocated")))
    count))

;;;###autoload (autoload 'bmkp-bmenu-edit-bookmark-name-and-location "bookmark+")
(defun bmkp-bmenu-edit-bookmark-name-and-location (&optional internalp) ; Bound to `r' in bookmark list
  "Edit the bookmark under the cursor: its name and location.
With a prefix argument, edit the complete bookmark record (the
internal, Lisp form)."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bmk-name  (bookmark-bmenu-bookmark)))
    (if internalp
        (bmkp-edit-bookmark-record bmk-name)
      (let* ((new-data  (bmkp-edit-bookmark-name-and-location bmk-name))
             (new-name  (car new-data)))
        (if (not new-data) (message "No changes made") (bmkp-refresh-menu-list new-name))))))

;;;###autoload (autoload 'bmkp-bmenu-edit-tags "bookmark+")
(defun bmkp-bmenu-edit-tags ()          ; Bound to `T e' in bookmark list
  "Edit the tags of the bookmark under the cursor.
The edited value must be a list each of whose elements is either a
string or a cons whose key is a string."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-edit-tags (bookmark-bmenu-bookmark)))

;;;###autoload (autoload 'bmkp-bmenu-edit-bookmark-record "bookmark+")
(defun bmkp-bmenu-edit-bookmark-record () ; Bound to `e' in bookmark list
  "Edit the full record (the Lisp sexp) for the bookmark under the cursor.
When you finish editing, use `\\[bmkp-edit-bookmark-record-send]'.
The current bookmark list is then updated to reflect your edits."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-edit-bookmark-record (setq bmkp-edit-bookmark-orig-record  (bookmark-bmenu-bookmark))))

;;;###autoload (autoload 'bmkp-bmenu-edit-marked "bookmark+")
(defun bmkp-bmenu-edit-marked (&optional allp include-omitted-p) ; Bound to `E' in bookmark list
  "Edit the full records (the Lisp sexps) of the marked bookmarks.
When you finish editing, use `\\[bmkp-edit-bookmark-records-send]'.
The current bookmark list is then updated to reflect your edits.

If no bookmark is marked, edit the bookmark of the current line.

With a non-negative prefix arg, edit all bookmark records.

Omitted bookmarks are excluded, by default.  With a negative prefix
arg, any that are marked are included."
  (interactive (list (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                     (and current-prefix-arg  (<  (prefix-numeric-value current-prefix-arg) 0))))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-last-bmenu-bookmark  (bookmark-bmenu-bookmark))
  ;; No marked bookmarks.  Mark this bookmark, so that `C-c C-c' in edit buffer will find it.
  ;; Do this before we copy and strip full-bookmark property from name, because `bookmark-bmenu-mark'
  ;; propertizes the name.
  (unless bmkp-bmenu-marked-bookmarks (bookmark-bmenu-mark))
  (let ((bufname      "*Edit Marked Bookmarks*")
        (copied-bmks  (mapcar (lambda (bmk)
                                (setq bmk  (copy-sequence bmk)) ; Shallow copy
                                (let ((bname  (bmkp-bookmark-name-from-record bmk)))
                                  ;; Strip properties from name.
                                  (set-text-properties 0 (length bname) nil bname))
                                bmk)
                              (bmkp-bmenu-marked-or-this-or-all allp include-omitted-p))))
    (unless copied-bmks (error "No marked bookmarks"))
    (setq bmkp-edit-bookmark-records-number  (length copied-bmks))
    (bmkp-with-output-to-plain-temp-buffer bufname
      (princ
       (substitute-command-keys
        (concat ";; Edit the Lisp records for the marked bookmarks.\n;;\n"
                ";; DO NOT CHANGE THE ORDER of the bookmarks in this buffer.\n"
                ";; DO NOT DELETE any of them.\n;;\n"
                ";; Type \\<bmkp-edit-bookmark-records-mode-map>\
`\\[bmkp-edit-bookmark-records-send]' when done.\n;;\n")))
      ;; $$$$$$ (let ((print-circle  t)) (pp copied-bmks)) ; $$$$$$ Should not really be needed now.
      (pp copied-bmks)
      (with-current-buffer bufname (goto-char (point-min))))
    (pop-to-buffer bufname)
    (buffer-enable-undo)
    (with-current-buffer (get-buffer bufname) (bmkp-edit-bookmark-records-mode))))

(defun bmkp-bmenu-propertize-item (bookmark start end)
  "Propertize text in buffer from START to END, indicating bookmark type.
This propertizes the name of BOOKMARK.
Also give this region the property `bmkp-bookmark-name' with as value
the name of BOOKMARK as a propertized string.

The propertized string has property `bmkp-full-record' with value
BOOKMARK, which is the full bookmark record, with the string as its
car.

Return the propertized string (the bookmark name)."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (let* ((bookmark-name   (bmkp-bookmark-name-from-record bookmark))
         (buffp           (bmkp-get-buffer-name bookmark))

         (filep           (bookmark-get-filename bookmark))
         (sudop           (and filep  (boundp 'tramp-file-name-regexp)
                               (bmkp-string-match-p tramp-file-name-regexp filep)
                               (bmkp-string-match-p bmkp-su-or-sudo-regexp filep))))
    ;; Put the full bookmark itself on string `bookmark-name' as property `bmkp-full-record'.
    ;; Then put that string on the name in the buffer text as property `bmkp-bookmark-name'.
    (put-text-property 0 (length bookmark-name) 'bmkp-full-record bookmark bookmark-name)
    (put-text-property start end 'bmkp-bookmark-name bookmark-name)
    ;; Add faces, mouse face, and tooltips, to characterize the bookmark type.
    (add-text-properties
     start  end
     (cond ((bookmark-prop-get bookmark 'file-handler) ; `file-handler' bookmark
            (append (bmkp-face-prop 'bmkp-file-handler)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Invoke the `file-handler' for this bookmark")))
           ((bmkp-sequence-bookmark-p bookmark)                                     ; Sequence bookmark
            (append (bmkp-face-prop 'bmkp-sequence)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Invoke the bookmarks in this sequence")))
           ((bmkp-function-bookmark-p bookmark)                                     ; Function bookmark
            (append (bmkp-face-prop 'bmkp-function)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Invoke this function bookmark")))
           ((bmkp-variable-list-bookmark-p bookmark)                           ; Variable-list bookmark
            (append (bmkp-face-prop 'bmkp-variable-list)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Invoke this variable-list bookmark")))
           ((bmkp-bookmark-list-bookmark-p bookmark)                           ; Bookmark-list bookmark
            (append (bmkp-face-prop 'bmkp-bookmark-list)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Invoke this bookmark-list bookmark")))
           ((bmkp-snippet-bookmark-p bookmark)                                       ; Snippet bookmark
            (append (bmkp-face-prop 'bmkp-snippet)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Jump to this snippet bookmark")))
           ((bmkp-desktop-bookmark-p bookmark)                                       ; Desktop bookmark
            (append (bmkp-face-prop 'bmkp-desktop)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Jump to this desktop bookmark")))
           ((bmkp-bookmark-file-bookmark-p bookmark)                           ; Bookmark-file bookmark
            (append (bmkp-face-prop 'bmkp-bookmark-file)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Load this bookmark's bookmark file")))
           ((bmkp-non-invokable-bookmark-p bookmark)                           ; Non-invokable bookmark
            (append (bmkp-face-prop 'bmkp-no-jump)
                    '(help-echo "You CANNOT JUMP to this bookmark")))
           ((bmkp-icicles-search-hits-bookmark-p bookmark)               ; Icicles search hits bookmark
            (append (bmkp-face-prop 'bmkp-no-jump)
                    '(help-echo "You can use this only during Icicles search, NOT HERE")))
           ((bmkp-info-bookmark-p bookmark)                                             ; Info bookmark
            (append (bmkp-face-prop 'bmkp-info)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Jump to this Info bookmark")))
           ((bmkp-man-bookmark-p bookmark)                                               ; Man bookmark
            (append (bmkp-face-prop 'bmkp-man)
                    '(mouse-face highlight follow-link t
                      help-echo (format "mouse-2 Goto `man' page"))))
           ((bmkp-gnus-bookmark-p bookmark)                                             ; Gnus bookmark
            (append (bmkp-face-prop 'bmkp-gnus)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Jump to this Gnus bookmark")))
           ((bmkp-url-bookmark-p bookmark)                                               ; URL bookmark
            (append (bmkp-face-prop 'bmkp-url)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to URL `%s'" ,filep))))
           ((and sudop  (not (bmkp-root-or-sudo-logged-p)))                   ; Root/sudo not logged in
            (append (bmkp-face-prop 'bmkp-su-or-sudo)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to (visit) file `%s'" ,filep))))
           ;; Test for remoteness before any other tests of the file itself
           ;; (e.g. `file-exists-p'), so Tramp does not prompt for a password etc.
           ((and filep  (bmkp-file-remote-p filep)  (not sudop)) ; Remote file (ssh, ftp)
            (append (bmkp-face-prop 'bmkp-remote-file)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to (visit) remote file `%s'" ,filep))))
           ((and filep                  ; Local directory or local Dired buffer (could be wildcards)
                 (or (file-directory-p filep)  (bmkp-dired-bookmark-p bookmark)))
            (append (bmkp-face-prop 'bmkp-local-directory)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Dired directory `%s'" ,filep))))
           ((and filep  (file-exists-p filep) ; Local file with region
                 (bmkp-region-bookmark-p bookmark))
            (append (bmkp-face-prop 'bmkp-local-file-with-region)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Activate region in file `%s'" ,filep))))
           ((and filep  (file-exists-p filep)) ; Local file without region
            (append (bmkp-face-prop 'bmkp-local-file-without-region)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to (visit) file `%s'" ,filep))))
           ; Existing buffer, including for a file bookmark if the file buffer has not yet been saved.
           ((and buffp  (get-buffer buffp))
            (append (bmkp-face-prop 'bmkp-buffer)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to buffer `%s'" ,buffp))))
           ((or (not filep)  (equal filep bmkp-non-file-filename)) ; Non-file, and no existing buffer.
            (append (bmkp-face-prop 'bmkp-non-file)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Create buffer `%s' and jump to it" ,buffp))))
           ((and filep  (not (file-exists-p filep))) ; Local-file bookmark, but no such file exists.
            (bmkp-face-prop 'bmkp-no-local))
           (t (append (bmkp-face-prop 'bmkp-bad-bookmark)
                      `(mouse-face highlight follow-link t
                        help-echo (format "BAD BOOKMARK (maybe): `%s'" ,filep))))))
    bookmark-name))

;;;###autoload (autoload 'bmkp-bmenu-quit "bookmark+")
(defun bmkp-bmenu-quit ()               ; Bound to `q' in bookmark list
  "Quit the bookmark list (aka \"menu list\").
If `bmkp-bmenu-state-file' is non-nil, then save the state, to be
restored the next time the bookmark list is shown.  Otherwise, reset
the internal lists that record menu-list markings."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (if (not bmkp-bmenu-state-file)
      (setq bmkp-bmenu-marked-bookmarks            ()
            bmkp-bmenu-before-hide-marked-alist    ()
            bmkp-bmenu-before-hide-unmarked-alist  ())
    (when (interactive-p) (message "Saving bookmark-list display state..."))
    (bmkp-save-menu-list-state)
    (when (interactive-p) (message "Saving bookmark-list display state...done"))
    (setq bmkp-bmenu-first-time-p  t))
  (quit-window))

(defun bmkp-bmenu-goto-bookmark-named (name)
  "Go to the first bookmark whose name matches NAME (a string).
If NAME has non-nil property `bmkp-full-record' then go to the
bookmark it indicates.  Otherwise, just go to the first bookmark with
the same name."
  (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
  (let ((full  (get-text-property 0 'bmkp-full-record name)))
    (while (and (not (eobp))
                (not (if full
                         (equal full (get-text-property 0 'bmkp-full-record (bookmark-bmenu-bookmark)))
                       (equal name (bookmark-bmenu-bookmark)))))
      (forward-line 1)))
  (bookmark-bmenu-ensure-position))     ; Just in case we fall off the end.

;; This is a general function.  It is in this file because it is used only by the bmenu code.
(defun bmkp-bmenu-barf-if-not-in-menu-list ()
  "Raise an error if current buffer is not `*Bookmark List*'."
  (unless (equal (buffer-name (current-buffer)) "*Bookmark List*")
    (error "You can only use this command in buffer `*Bookmark List*'")))

(defun bmkp-face-prop (value)
  "Return a list with elements `face' or `font-lock-face' and VALUE.
Starting with Emacs 22, the first element is `font-lock-face'."
  (list (if (> emacs-major-version 21) 'font-lock-face 'face) value))

(when (or (> emacs-major-version 24)    ; Emacs bug #12867 was partially fixed for Emacs 24.3+.
          (and (= emacs-major-version 24)  (> emacs-minor-version 2)))
  (defun bmkp-bmenu-mode-line-string ()
    "Show, in mode line, information about the current bookmark-list display.
The information includes the sort order and the number of marked,
flagged (for deletion), tagged, temporary, annotated, and modified
bookmarks currently shown.

For each number indication:
 If the current line has the indicator (e.g. mark, flag) and there are
 others with the same indicator listed after it, then show `N/M',
 where N is the number indicated through the current line and M is the
 total number indicated."
    (let* ((regexp->   "^>")
           (regexp-D   "^D")
           (regexp-t   "^.t")
           (regexp-X   "^..X")
           (regexp-a   "^..a")
           (regexp-*   "^...\\*")
           (nb->       (count-matches regexp-> (point-min) (point-max)))
           (nb-D       (count-matches regexp-D (point-min) (point-max)))
           (nb-t       (count-matches regexp-t (point-min) (point-max)))
           (nb-X       (count-matches regexp-X (point-min) (point-max)))
           (nb-a       (count-matches regexp-a (point-min) (point-max)))
           (nb-*       (count-matches regexp-* (point-min) (point-max)))
           (text-sort  (propertize
                        (concat "sorting " (bmkp-sorting-description (bmkp-current-sort-order)))
                        'face 'bmkp-heading))
           regexp)
      (let ((desc  "")
            nb)
        (dolist (mk  '(?> ?D ?t ?a ?X ?*))
          (setq nb      (symbol-value (intern (format "nb-%c" mk)))
                regexp  (symbol-value (intern (format "regexp-%c" mk)))
                desc    (concat
                         desc
                         (and (> nb 0)
                              (propertize
                               (format
                                "%s%d%c"
                                (save-excursion
                                  (forward-line 0)
                                  (if (bmkp-looking-at-p (concat regexp ".*"))
                                      (format "%d/" (1+ (count-matches regexp (point-min) (point))))
                                    ""))
                                nb  mk)
                               'face (intern (format "bmkp-%c-mark" mk))))
                         (and (> nb 0)  " "))))
        (format "%s%s" desc text-sort))))

  (defun bmkp-bmenu-mode-line ()        ; This works, but it shows the line number also.
    "Set the mode line for buffer `*Bookmark List*'."
    (condition-case nil
        (progn
          (set (make-local-variable 'mode-name) '(:eval (bmkp-bmenu-mode-line-string)))
          ;; It seems that the line number must be present, and not invisible, for dynamic updating
          ;; of the mode line when you move the cursor among lines.  Moving it way off to the right
          ;; effectively gets rid of it (ugly hack).  See Emacs bug #12867.
          (set (make-local-variable 'mode-line-position) '("%360l (line)")) ; Move it off the screen.
          (set (make-local-variable 'mode-line-format)
               '(("" mode-name "\t" mode-line-buffer-identification mode-line-position))))
      (error nil))))

(when (fboundp 'org-add-link-type)
  (org-add-link-type "bookmark"           'bookmark-jump)
  (org-add-link-type "bookmark-other-win" 'bookmark-jump-other-window)
  (add-hook 'org-store-link-functions 'bmkp-bmenu-store-org-link 'APPEND)
  (defun bmkp-bmenu-store-org-link ()
    "Store a link to this bookmark for insertion in an Org-mode buffer.
If you use a numeric prefix arg with `\\[org-store-link]' then the
bookmark will be jumped to in the same window.  Without a numeric
prefix arg, the link will use another window.  The link type is
`bookmark' or `bookmark-other-win', respectively."
    (require 'org)
    (and (derived-mode-p 'bookmark-bmenu-mode)
         (let* ((other-win  (and current-prefix-arg  (not (consp current-prefix-arg))))
                (bmk        (bookmark-bmenu-bookmark))
                (link       (format "bookmark%s:%s" (if other-win "-other-win" "") bmk))
                (bmk-desc   (format "Bookmark: %s" bmk)))
           (org-store-link-props :type "bookmark" :link link :description bmk-desc)))))


;;(@* "Sorting - Commands")
;;  *** Sorting - Commands ***

;;;###autoload (autoload 'bmkp-bmenu-change-sort-order-repeat "bookmark+")
(defun bmkp-bmenu-change-sort-order-repeat (arg) ; Bound to `s s'... in bookmark list
  "Cycle to the next sort order.
With a prefix arg, reverse current sort order.
This is a repeatable version of `bmkp-bmenu-change-sort-order'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-bmenu-change-sort-order))

;;;###autoload (autoload 'bmkp-bmenu-change-sort-order "bookmark+")
(defun bmkp-bmenu-change-sort-order (&optional arg)
  "Cycle to the next sort order.
With a prefix arg, reverse the current sort order."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-sort-orders-for-cycling-alist  (delq nil bmkp-sort-orders-for-cycling-alist))
  (if arg
      (bmkp-reverse-sort-order)
    (let ((curr-bmk  (bookmark-bmenu-bookmark))
          next-order)
      (let ((orders  (mapcar #'car bmkp-sort-orders-for-cycling-alist)))
        (setq next-order          (or (cadr (member (bmkp-current-sort-order) orders))  (car orders))
              bmkp-sort-comparer  (cdr (assoc next-order bmkp-sort-orders-for-cycling-alist))))
      (message "Sorting...")
      (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
      (when curr-bmk                 ; Put cursor back on the right line.
        (bmkp-bmenu-goto-bookmark-named curr-bmk))
      (when (interactive-p) (bmkp-msg-about-sort-order next-order)))))

;; This is a general command.  It is in this file because it is used only by the bmenu code.
;;;###autoload (autoload 'bmkp-reverse-sort-order "bookmark+")
(defun bmkp-reverse-sort-order ()       ; Bound to `s r' in bookmark list
  "Reverse the current bookmark sort order.
If you combine this with \\<bookmark-bmenu-mode-map>\
`\\[bmkp-reverse-multi-sort-order]', then see the doc for that command."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-reverse-sort-p  (not bmkp-reverse-sort-p))
  (let ((curr-bmk  (bookmark-bmenu-bookmark)))
    (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
    (when curr-bmk                   ; Put cursor back on the right line.
      (bmkp-bmenu-goto-bookmark-named curr-bmk)))
  (when (interactive-p) (bmkp-msg-about-sort-order (bmkp-current-sort-order))))

;; This is a general command.  It is in this file because it is used only by the bmenu code.
;;;###autoload (autoload 'bmkp-reverse-multi-sort-order "bookmark+")
(defun bmkp-reverse-multi-sort-order () ; Bound to `s C-r' in bookmark list
  "Reverse the application of multi-sorting predicates.
These are the PRED predicates described for option
`bmkp-sort-comparer'.

This reverses the order in which the predicates are tried, and it
also complements the truth value returned by each predicate.

For example, if the list of multi-sorting predicates is (p1 p2 p3),
then the predicates are tried in the order: p3, p2, p1.  And if a
predicate returns true, `(t)', then the effect is as if it returned
false, `(nil)', and vice versa.

The use of multi-sorting predicates tends to group bookmarks, with the
first predicate corresponding to the first bookmark group etc.

The effect of \\<bookmark-bmenu-mode-map>`\\[bmkp-reverse-multi-sort-order]' is \
roughly as follows:

 - without also `\\[bmkp-reverse-sort-order]', it reverses the bookmark order in each \
group

 - combined with `\\[bmkp-reverse-sort-order]', it reverses the order of the bookmark
   groups, but not the bookmarks within a group

This is a rough description.  The actual behavior can be complex,
because of how each predicate is defined.  If this description helps
you, fine.  If not, just experiment and see what happens. \;-)

Remember that ordinary `\\[bmkp-reverse-sort-order]' reversal on its own is \
straightforward.
If you find `\\[bmkp-reverse-multi-sort-order]' confusing or not helpful, then do not \
use it."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-reverse-multi-sort-p  (not bmkp-reverse-multi-sort-p))
  (let ((curr-bmk  (bookmark-bmenu-bookmark)))
    (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
    (when curr-bmk                   ; Put cursor back on the right line.
      (bmkp-bmenu-goto-bookmark-named curr-bmk)))
  (when (interactive-p) (bmkp-msg-about-sort-order (bmkp-current-sort-order))))



;; The ORDER of the macro calls here defines the REVERSE ORDER of
;; `bmkp-sort-orders-alist'.  The first here is thus also the DEFAULT sort order.
;; Entries are traversed by `s s'..., in `bmkp-sort-orders-alist' order.

(bmkp-define-sort-command               ; Bound to `s k' in bookmark list (`k' for "kind")
 "by bookmark type"                     ; `bmkp-bmenu-sort-by-bookmark-type'
 ((bmkp-info-node-name-cp bmkp-url-cp bmkp-gnus-cp bmkp-local-file-type-cp bmkp-handler-cp)
  bmkp-alpha-p)
 "Sort bookmarks by type: Info, URL, Gnus, files, other (by handler name).")

(bmkp-define-sort-command               ; Bound to `s u' in bookmark list
 "by url"                           ; `bmkp-bmenu-sort-by-url'
 ((bmkp-url-cp) bmkp-alpha-p)
 "Sort URL bookmarks alphabetically by their URL/filename.
When two bookmarks are not comparable this way, compare them by
bookmark name.")

;; $$$$$$ Not used now.
;; (bmkp-define-sort-command               ; Bound to `s w 3' in bookmark list
;;  "by W3M url"                           ; `bmkp-bmenu-sort-by-w3m-url'
;;  ((bmkp-w3m-cp) bmkp-alpha-p)
;;  "Sort W3M bookmarks alphabetically by their URL/filename.
;; When two bookmarks are not comparable this way, compare them by
;; bookmark name.")

;; (when (fboundp 'bmkp-eww-cp)
;;   ;; $$$$$$ Not used now.
;;   ;; (bmkp-define-sort-command               ; Bound to `s w e' in bookmark list
;;   ;;  "by EWW url"                           ; `bmkp-bmenu-sort-by-w3m-url'
;;   ;;  ((bmkp-eww-cp) bmkp-alpha-p)
;;   ;;  "Sort EWW bookmarks alphabetically by their URL/filename.
;;   ;; When two bookmarks are not comparable this way, compare them by
;;   ;; bookmark name.")
;;   )

(bmkp-define-sort-command               ; Bound to `s g' in bookmark list
 "by Gnus thread"                       ; `bmkp-bmenu-sort-by-Gnus-thread'
 ((bmkp-gnus-cp) bmkp-alpha-p)
 "Sort Gnus bookmarks by group, then by article, then by message.
When two bookmarks are not comparable this way, compare them by
bookmark name.")

(bmkp-define-sort-command               ; Bound to `s i' in bookmark list
 "by Info node name"                    ; `bmkp-bmenu-sort-by-Info-node-name'
 ((bmkp-info-node-name-cp) bmkp-alpha-p)
 "Sort Info bookmarks by manual (file) name, then node name, then position.
When two bookmarks are not comparable this way, compare them by
bookmark name.")

(bmkp-define-sort-command               ; Bound to `s I' in bookmark list
 "by Info position"                     ; `bmkp-bmenu-sort-by-Info-position'
 ((bmkp-info-position-cp) bmkp-alpha-p)
 "Sort Info bookmarks by manual (file) name, then position (order in book).
When two bookmarks are not comparable this way, compare them by
bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f u' in bookmark list
 "by last local file update"            ; `bmkp-bmenu-sort-by-last-local-file-update'
 ((bmkp-local-file-updated-more-recently-cp) bmkp-alpha-p)
 "Sort bookmarks by last local file update time.
Sort a local file before a remote file, and a remote file before other
bookmarks.  Otherwise, sort by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f d' in bookmark list
 "by last local file access"            ; `bmkp-bmenu-sort-by-last-local-file-access'
 ((bmkp-local-file-accessed-more-recently-cp) bmkp-alpha-p)
 "Sort bookmarks by last local file access time.
A local file sorts before a remote file, which sorts before other
bookmarks.  Otherwise, sort by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f s' in bookmark list
 "by local file size"                   ; `bmkp-bmenu-sort-by-local-file-size'
 ((bmkp-local-file-size-cp) bmkp-alpha-p)
 "Sort bookmarks by local file size.
A local file sorts before a remote file, which sorts before other
bookmarks.  Otherwise, sort by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f n' in bookmark list
 "by file name"                         ; `bmkp-bmenu-sort-by-file-name'
 ((bmkp-file-alpha-cp) bmkp-alpha-p)
 "Sort bookmarks by file name.
When two bookmarks are not comparable by file name, compare them by
bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f k' in bookmark list (`k' for "kind")
 "by local file type"                   ; `bmkp-bmenu-sort-by-local-file-type'
 ((bmkp-local-file-type-cp) bmkp-alpha-p)
 "Sort bookmarks by local file type: file, symlink, directory.
A local file sorts before a remote file, which sorts before other
bookmarks.  Otherwise, sort by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s D' in bookmark list
 "flagged before unflagged"             ; `bmkp-bmenu-sort-flagged-before-unflagged'
 ((bmkp-flagged-cp) bmkp-alpha-p)
 "Sort bookmarks by putting flagged for deletion before unflagged.
Otherwise alphabetize by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s *' in bookmark list
 "modified before unmodified"           ; `bmkp-bmenu-sort-modified-before-unmodified'
 ((bmkp-modified-cp) bmkp-alpha-p)
 "Sort bookmarks by putting modified before unmodified (saved).
Otherwise alphabetize by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s >' in bookmark list
 "marked before unmarked"               ; `bmkp-bmenu-sort-marked-before-unmarked'
 ((bmkp-marked-cp) bmkp-alpha-p)
 "Sort bookmarks by putting marked before unmarked.
Otherwise alphabetize by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s 0' (zero) in bookmark list
 "by creation time"                     ; `bmkp-bmenu-sort-by-creation-time'
 ((bmkp-bookmark-creation-cp) bmkp-alpha-p)
 "Sort bookmarks by the time of their creation.
When one or both of the bookmarks does not have a `created' entry),
compare them by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s b' in bookmark list
 "by last buffer or file access"        ; `bmkp-bmenu-sort-by-last-buffer-or-file-access'
 ((bmkp-buffer-last-access-cp bmkp-local-file-accessed-more-recently-cp)
  bmkp-alpha-p)
 "Sort bookmarks by last buffer access or last local file access.
Sort a bookmark accessed more recently before one accessed less
recently or not accessed.  Sort a bookmark to an existing buffer
before a local file bookmark.  When two bookmarks are not comparable
by such critera, sort them by bookmark name.  (In particular, sort
remote-file bookmarks by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s v' in bookmark list
 "by bookmark visit frequency"          ; `bmkp-bmenu-sort-by-bookmark-visit-frequency'
 ((bmkp-visited-more-cp) bmkp-alpha-p)
 "Sort bookmarks by the number of times they were visited as bookmarks.
When two bookmarks are not comparable by visit frequency, compare them
by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s d' in bookmark list
 "by last bookmark access"              ; `bmkp-bmenu-sort-by-last-bookmark-access'
 ((bmkp-bookmark-last-access-cp) bmkp-alpha-p)
 "Sort bookmarks by the time of their last visit as bookmarks.
When two bookmarks are not comparable by visit time, compare them
by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s n' in bookmark list
 "by bookmark name"                     ; `bmkp-bmenu-sort-by-bookmark-name'
 bmkp-alpha-p
 "Sort bookmarks by bookmark name, respecting `case-fold-search'.")

(bmkp-define-sort-command               ; Bound to `s t' in bookmark list
 "tagged before untagged"               ; `bmkp-bmenu-sort-tagged-before-untagged'
 ((bmkp-tagged-cp) bmkp-alpha-p)
 "Sort bookmarks by putting tagged before untagged.
Otherwise alphabetize by bookmark name.")

;; This is a general option.  It is in this file because it is used mainly by the bmenu code.
;; Its definitions MUST COME AFTER the calls to macro `bmkp-define-sort-command'.
;; Otherwise, they won't pick up a populated `bmkp-sort-orders-alist'.
(when (> emacs-major-version 20)
  (defcustom bmkp-sort-orders-for-cycling-alist (copy-sequence bmkp-sort-orders-alist)
    "*Alist of sort orders used for cycling via `s s'...
This is a subset of the complete list of available sort orders,
`bmkp-sort-orders-alist'.  This lets you cycle among fewer sort
orders, if there are some that you do not use often.

See the doc for `bmkp-sort-orders-alist', for the structure of
this value."
    :type '(alist
            :key-type (choice :tag "Sort order" string symbol)
            :value-type (choice
                         (const :tag "None (do not sort)" nil)
                         (function :tag "Sorting Predicate")
                         (list :tag "Sorting Multi-Predicate"
                          (repeat (function :tag "Component Predicate"))
                          (choice
                           (const :tag "None" nil)
                           (function :tag "Final Predicate")))))
    :group 'bookmark-plus))

(unless (> emacs-major-version 20)      ; Emacs 20: custom type `alist' doesn't exist.
  (defcustom bmkp-sort-orders-for-cycling-alist (copy-sequence bmkp-sort-orders-alist)
    "*Alist of sort orders used for cycling via `s s'...
This is a subset of the complete list of available sort orders,
`bmkp-sort-orders-alist'.  This lets you cycle among fewer sort
orders, if there are some that you do not use often.

See the doc for `bmkp-sort-orders-alist', for the structure of this
value."
    :type '(repeat
            (cons
             (choice :tag "Sort order" string symbol)
             (choice
              (const :tag "None (do not sort)" nil)
              (function :tag "Sorting Predicate")
              (list :tag "Sorting Multi-Predicate"
               (repeat (function :tag "Component Predicate"))
               (choice
                (const :tag "None" nil)
                (function :tag "Final Predicate"))))))
    :group 'bookmark-plus))


;;(@* "Other Bookmark+ Functions (`bmkp-*')")
;;  *** Other Bookmark+ Functions (`bmkp-*') ***

;;;###autoload (autoload 'bmkp-bmenu-show-this-annotation+move-down "bookmark+")
(defun bmkp-bmenu-show-this-annotation+move-down (&optional n) ; Bound to `M-down' in bookmark list
  "Move down N lines in bookmark-list display and show annotation, if any."
  (interactive "p")
  (bmkp-bmenu-kill-annotation)
  (forward-line n)
  (bookmark-bmenu-show-annotation 'MSGP))

;;;###autoload (autoload 'bmkp-bmenu-show-this-annotation+move-up "bookmark+")
(defun bmkp-bmenu-show-this-annotation+move-up (&optional n) ; Bound to `M-up' in bookmark list
  "Move up N lines in bookmark-list display and show annotation, if any."
  (interactive "p")
  (bmkp-bmenu-kill-annotation)
  (forward-line (- n))
  (bookmark-bmenu-show-annotation 'MSGP))

(defun bmkp-bmenu-kill-annotation (&optional bookmark-name)
  "Kill annotation buffer, if any, for BOOKMARK-NAME.
If BOOKMARK-NAME is nil, use the bookmark of the current line.
Return non-nil only if there was such an annotation buffer."
  (let ((ann-buf  (get-buffer (format "*`%s' Annotation*"
                                      (or bookmark-name  (bookmark-bmenu-bookmark))))))
    (when ann-buf (kill-buffer ann-buf))))

;;;###autoload (autoload 'bmkp-bmenu-describe-this+move-down "bookmark+")
(defun bmkp-bmenu-describe-this+move-down (&optional defn) ; Bound to `C-down' in bookmark list
  "Move to next line in bookmark-list display and describe the bookmark.
With a prefix argument, show the internal definition of the bookmark."
  (interactive "P")
  (forward-line 1)
  (bmkp-bmenu-describe-this-bookmark))

;;;###autoload (autoload 'bmkp-bmenu-describe-this+move-up "bookmark+")
(defun bmkp-bmenu-describe-this+move-up (&optional defn) ; Bound to `C-up' in bookmark list
  "Move to previous line in bookmark-list display and describe the bookmark.
With a prefix argument, show the internal definition of the bookmark."
  (interactive "P")
  (forward-line -1)
  (bmkp-bmenu-describe-this-bookmark))

;;;###autoload (autoload 'bmkp-bmenu-describe-this-bookmark "bookmark+")
(defun bmkp-bmenu-describe-this-bookmark (&optional defn) ; Bound to `C-h RET' in bookmark list
  "Describe bookmark of current line.
With a prefix argument, show the internal definition of the bookmark."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (save-selected-window (if defn
                            (bmkp-describe-bookmark-internals (bookmark-bmenu-bookmark))
                          (bmkp-describe-bookmark (bookmark-bmenu-bookmark)))))

;;;###autoload (autoload 'bmkp-bmenu-describe-marked "bookmark+")
(defun bmkp-bmenu-describe-marked (&optional defn include-omitted-p) ; Bound to `C-h >' in bookmark list
  "Describe the marked bookmarks, in the current sort order.
If no bookmark is marked, act on the bookmark of the current line.

With a non-negative prefix argument, show the internal definitions.

Omitted bookmarks are excluded, by default.  With a non-positive
prefix arg, any that are marked are included."
  (interactive (list (and current-prefix-arg  (>= (prefix-numeric-value current-prefix-arg) 0))
                     (and current-prefix-arg  (<= (prefix-numeric-value current-prefix-arg) 0))))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (help-setup-xref (list #'bmkp-describe-bookmark-marked) (interactive-p))
  (bmkp-with-help-window "*Help*"
    (dolist (bmk  (bmkp-sort-omit (bmkp-bmenu-marked-or-this-or-all nil include-omitted-p)))
      (if defn
          (let* ((bname         (bmkp-bookmark-name-from-record bmk))
                 (print-circle  bmkp-propertize-bookmark-names-flag) ; For `pp-to-string'
                 (print-length  nil)    ; For `pp-to-string'
                 (print-level   nil)    ; For `pp-to-string'
                 (help-text     (format "%s\n%s\n\n%s"
                                        bname (make-string (length bname) ?-) (pp-to-string bmk))))
            (princ help-text) (terpri))
        (princ (bmkp-bookmark-description bmk)) (terpri)))))

(defun bmkp-bmenu-get-marked-files ()
  "Return a list of the file names of the marked bookmarks.
Marked bookmarks that have no associated file are ignored."
  (let ((files  ()))
    (dolist (bmk  bmkp-bmenu-marked-bookmarks)
      (when (bmkp-file-bookmark-p bmk) (push (bookmark-get-filename bmk) files)))
    files))

(defun bmkp-bmenu-marked-or-this-or-all (&optional allp include-omitted-p)
  "Return the marked bookmarks or the current-line bookmark if none marked.
Non-nil ALLP means return all bookmarks: `bookmark-alist'.
Do not include marked bookmarks that are omitted, unless optional arg
INCLUDE-OMITTED-P is non-nil.  INCLUDE-OMITTED-P has no effect if none
are marked or ALLP is non-nil."
  (if allp
      bookmark-alist
    (or (if include-omitted-p
            (bmkp-marked-bookmarks-only)
          (bmkp-remove-if #'bmkp-omitted-bookmark-p (bmkp-marked-bookmarks-only)))
        (and (bookmark-bmenu-bookmark)  (list (bookmark-get-bookmark (bookmark-bmenu-bookmark)))))))
 
;;(@* "Keymaps")
;;; Keymaps ----------------------------------------------------------

;; `bookmark-bmenu-mode-map'

(when (< emacs-major-version 21)
  (define-key bookmark-bmenu-mode-map (kbd "RET")          'bookmark-bmenu-this-window))
(define-key bookmark-bmenu-mode-map "\M-~"                 'bmkp-toggle-saving-bookmark-file)
(define-key bookmark-bmenu-mode-map (kbd "C-M-~")          'bmkp-toggle-saving-menu-list-state)
(define-key bookmark-bmenu-mode-map "."                    'bmkp-bmenu-show-all)
(define-key bookmark-bmenu-mode-map ">"                    'bmkp-bmenu-toggle-show-only-marked)
(define-key bookmark-bmenu-mode-map "<"                    'bmkp-bmenu-toggle-show-only-unmarked)
(define-key bookmark-bmenu-mode-map (kbd "M-<DEL>")        'bmkp-bmenu-unmark-all)
(define-key bookmark-bmenu-mode-map "-"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "->"                   'bmkp-bmenu-omit/unomit-marked)
(define-key bookmark-bmenu-mode-map "-S"                   'bmkp-bmenu-show-only-omitted-bookmarks)
(define-key bookmark-bmenu-mode-map "-U"                   'bmkp-unomit-all)
(define-key bookmark-bmenu-mode-map "="                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "=bM"                  'bmkp-bmenu-mark-specific-buffer-bookmarks)
(define-key bookmark-bmenu-mode-map "=fM"                  'bmkp-bmenu-mark-specific-file-bookmarks)
(define-key bookmark-bmenu-mode-map "=bS"                  'bmkp-bmenu-show-only-specific-buffer-bookmarks)
(define-key bookmark-bmenu-mode-map "=fS"                  'bmkp-bmenu-show-only-specific-file-bookmarks)
(define-key bookmark-bmenu-mode-map "%"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "%m"                   'bmkp-bmenu-regexp-mark)
(define-key bookmark-bmenu-mode-map "*"                    nil) ; For Emacs 20
(when (< emacs-major-version 21)
  (define-key bookmark-bmenu-mode-map "*m"                 'bookmark-bmenu-mark))
(define-key bookmark-bmenu-mode-map "#"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "#M"                   'bmkp-bmenu-mark-autonamed-bookmarks)
(define-key bookmark-bmenu-mode-map "#S"                   'bmkp-bmenu-show-only-autonamed-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-a"                 'bookmark-bmenu-show-all-annotations)
;; `a' is `bookmark-bmenu-show-annotation' in vanilla Emacs.
(define-key bookmark-bmenu-mode-map "a"                    'bmkp-bmenu-show-or-edit-annotation)
;; `A' is `bookmark-bmenu-show-all-annotations' in vanilla Emacs (unbound in Bookmark+).
(define-key bookmark-bmenu-mode-map "A"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "AM"                   'bmkp-bmenu-mark-autofile-bookmarks)
(define-key bookmark-bmenu-mode-map "AS"                   'bmkp-bmenu-show-only-autofile-bookmarks)
(define-key bookmark-bmenu-mode-map "B"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "BM"                   'bmkp-bmenu-mark-non-file-bookmarks)
(define-key bookmark-bmenu-mode-map "BS"                   'bmkp-bmenu-show-only-non-file-bookmarks)
(define-key bookmark-bmenu-mode-map (kbd "C-c C-c")        'bmkp-bmenu-define-command)
(define-key bookmark-bmenu-mode-map (kbd "C-c C-S-c")      'bmkp-bmenu-define-full-snapshot-command)
(define-key bookmark-bmenu-mode-map (kbd "C-c C-j")        'bmkp-bmenu-define-jump-marked-command)
(define-key bookmark-bmenu-mode-map "d"                    'bmkp-bmenu-flag-for-deletion)
(define-key bookmark-bmenu-mode-map "D"                    'bmkp-bmenu-delete-marked)
(define-key bookmark-bmenu-mode-map "\C-d"                 'bmkp-bmenu-flag-for-deletion-backwards)
(define-key bookmark-bmenu-mode-map "\M-d"                 nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "\M-d>"                'bmkp-bmenu-dired-marked)
(define-key bookmark-bmenu-mode-map "\M-d\M-m"             'bmkp-bmenu-mark-dired-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-d\M-s"             'bmkp-bmenu-show-only-dired-bookmarks)
;; `e' is `bookmark-bmenu-edit-annotation' in vanilla Emacs.
(define-key bookmark-bmenu-mode-map "e"                    'bmkp-bmenu-edit-bookmark-record)
(define-key bookmark-bmenu-mode-map "E"                    'bmkp-bmenu-edit-marked)
(define-key bookmark-bmenu-mode-map "F"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "FM"                   'bmkp-bmenu-mark-file-bookmarks)
(define-key bookmark-bmenu-mode-map "FS"                   'bmkp-bmenu-show-only-file-bookmarks)
(define-key bookmark-bmenu-mode-map "g"                    'bmkp-bmenu-refresh-menu-list)
(define-key bookmark-bmenu-mode-map "G"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "GM"                   'bmkp-bmenu-mark-gnus-bookmarks)
(define-key bookmark-bmenu-mode-map "GS"                   'bmkp-bmenu-show-only-gnus-bookmarks)
(if (fboundp 'command-remapping)
    (define-key bookmark-bmenu-mode-map [remap describe-mode] 'bmkp-bmenu-mode-status-help)
  ;; In Emacs < 22, the `substitute-...' affects only `?', not `C-h m', so we add it separately.
  (substitute-key-definition 'describe-mode 'bmkp-bmenu-mode-status-help bookmark-bmenu-mode-map)
  (define-key bookmark-bmenu-mode-map "\C-hm"              'bmkp-bmenu-mode-status-help))
(define-key bookmark-bmenu-mode-map (kbd "C-h >")          'bmkp-bmenu-describe-marked)
(define-key bookmark-bmenu-mode-map (kbd "C-h RET")        'bmkp-bmenu-describe-this-bookmark)
(define-key bookmark-bmenu-mode-map (kbd "C-h C-<return>") 'bmkp-bmenu-describe-this-bookmark)
(define-key bookmark-bmenu-mode-map (kbd "C-<down>")       'bmkp-bmenu-describe-this+move-down)
(define-key bookmark-bmenu-mode-map (kbd "C-<up>")         'bmkp-bmenu-describe-this+move-up)
(define-key bookmark-bmenu-mode-map (kbd "M-<down>")       'bmkp-bmenu-show-this-annotation+move-down)
(define-key bookmark-bmenu-mode-map (kbd "M-<up>")         'bmkp-bmenu-show-this-annotation+move-up)
(define-key bookmark-bmenu-mode-map (kbd "M-<return>")     'bmkp-bmenu-w32-open)
(define-key bookmark-bmenu-mode-map [M-mouse-2]            'bmkp-bmenu-w32-open-with-mouse)
(when (featurep 'bookmark+-lit)
  (define-key bookmark-bmenu-mode-map "H"                  nil) ; For Emacs 20
  (define-key bookmark-bmenu-mode-map "H+"                 'bmkp-bmenu-set-lighting)
  (define-key bookmark-bmenu-mode-map "H>+"                'bmkp-bmenu-set-lighting-for-marked)
  (define-key bookmark-bmenu-mode-map "H>H"                'bmkp-bmenu-light-marked)
  (define-key bookmark-bmenu-mode-map "HH"                 'bmkp-bmenu-light)
  (define-key bookmark-bmenu-mode-map "HM"                 'bmkp-bmenu-mark-lighted-bookmarks)
  (define-key bookmark-bmenu-mode-map "HS"                 'bmkp-bmenu-show-only-lighted-bookmarks)
  (define-key bookmark-bmenu-mode-map "H>U"                'bmkp-bmenu-unlight-marked)
  (define-key bookmark-bmenu-mode-map "HU"                 'bmkp-bmenu-unlight))
(define-key bookmark-bmenu-mode-map "i"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "iM"                  'bmkp-bmenu-mark-icicles-search-hits-bookmarks)
(define-key bookmark-bmenu-mode-map "iS"                'bmkp-bmenu-show-only-icicles-search-hits-bookmarks)
(define-key bookmark-bmenu-mode-map "I"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "IM"                   'bmkp-bmenu-mark-info-bookmarks)
(define-key bookmark-bmenu-mode-map "IS"                   'bmkp-bmenu-show-only-info-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-I"                 nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "\M-I\M-M"             'bmkp-bmenu-mark-image-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-I\M-S"             'bmkp-bmenu-show-only-image-bookmarks)

;; Prefix `j' and `J' bindings are made in `bookmark+-key.el', by binding `bmkp-jump(-other-window)-map'.

(define-key bookmark-bmenu-mode-map "k"                    'bmkp-bmenu-flag-for-deletion)
(define-key bookmark-bmenu-mode-map "K"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "KM"                   'bmkp-bmenu-mark-desktop-bookmarks)
(define-key bookmark-bmenu-mode-map "KS"                   'bmkp-bmenu-show-only-desktop-bookmarks)
(define-key bookmark-bmenu-mode-map "L"                    'bmkp-switch-bookmark-file-create)
(define-key bookmark-bmenu-mode-map [(control shift ?l)]   'bookmark-bmenu-locate) ; `C-L' (aka `C-S-l')
(define-key bookmark-bmenu-mode-map "\M-l"
  'bmkp-bmenu-load-marked-bookmark-file-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-L"                 'bmkp-temporary-bookmarking-mode)
(define-key bookmark-bmenu-mode-map "M"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "MM"                   'bmkp-bmenu-mark-man-bookmarks)
(define-key bookmark-bmenu-mode-map "MS"                   'bmkp-bmenu-show-only-man-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-m"                 'bmkp-bmenu-mark-all)
(define-key bookmark-bmenu-mode-map "N"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "NM"                   'bmkp-bmenu-mark-non-invokable-bookmarks)
(define-key bookmark-bmenu-mode-map "NS"                   'bmkp-bmenu-show-only-non-invokable-bookmarks)
(define-key bookmark-bmenu-mode-map "O"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "OM"                 'bmkp-bmenu-mark-orphaned-local-file-bookmarks)
(define-key bookmark-bmenu-mode-map "OS"                'bmkp-bmenu-show-only-orphaned-local-file-bookmarks)
(define-key bookmark-bmenu-mode-map "P"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "PA"                  'bmkp-bmenu-filter-annotation-incrementally)
(define-key bookmark-bmenu-mode-map "PB"                 'bmkp-bmenu-filter-bookmark-name-incrementally)
(define-key bookmark-bmenu-mode-map "PF"                   'bmkp-bmenu-filter-file-name-incrementally)
(define-key bookmark-bmenu-mode-map "PT"                   'bmkp-bmenu-filter-tags-incrementally)
(define-key bookmark-bmenu-mode-map "q"                    'bmkp-bmenu-quit)
(define-key bookmark-bmenu-mode-map "\M-q"                'bmkp-bmenu-query-replace-marked-bookmarks-regexp)
(define-key bookmark-bmenu-mode-map "Q"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "QM"                   'bmkp-bmenu-mark-function-bookmarks)
(define-key bookmark-bmenu-mode-map "QS"                   'bmkp-bmenu-show-only-function-bookmarks)
(define-key bookmark-bmenu-mode-map "r"                    'bmkp-bmenu-edit-bookmark-name-and-location)
(define-key bookmark-bmenu-mode-map "R"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "RM"                   'bmkp-bmenu-mark-region-bookmarks)
(define-key bookmark-bmenu-mode-map "RS"                   'bmkp-bmenu-show-only-region-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-r"                 'bookmark-bmenu-relocate) ; `R' in Emacs
(define-key bookmark-bmenu-mode-map "\M-R"                 'bmkp-bmenu-relocate-marked)
(define-key bookmark-bmenu-mode-map "S"                    'bookmark-bmenu-save) ; `s' in Emacs
(define-key bookmark-bmenu-mode-map "s"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "s>"                   'bmkp-bmenu-sort-marked-before-unmarked)
(define-key bookmark-bmenu-mode-map "s*"                   'bmkp-bmenu-sort-modified-before-unmodified)
(define-key bookmark-bmenu-mode-map "s0"                   'bmkp-bmenu-sort-by-creation-time)
(define-key bookmark-bmenu-mode-map "sb"                   'bmkp-bmenu-sort-by-last-buffer-or-file-access)
(define-key bookmark-bmenu-mode-map "sd"                   'bmkp-bmenu-sort-by-last-bookmark-access)
(define-key bookmark-bmenu-mode-map "sD"                   'bmkp-bmenu-sort-flagged-before-unflagged)
(define-key bookmark-bmenu-mode-map "sfd"                  'bmkp-bmenu-sort-by-last-local-file-access)
(define-key bookmark-bmenu-mode-map "sfk"                  'bmkp-bmenu-sort-by-local-file-type)
(define-key bookmark-bmenu-mode-map "sfn"                  'bmkp-bmenu-sort-by-file-name)
(define-key bookmark-bmenu-mode-map "sfs"                  'bmkp-bmenu-sort-by-local-file-size)
(define-key bookmark-bmenu-mode-map "sfu"                  'bmkp-bmenu-sort-by-last-local-file-update)
(define-key bookmark-bmenu-mode-map "sg"                   'bmkp-bmenu-sort-by-Gnus-thread)
(define-key bookmark-bmenu-mode-map "si"                   'bmkp-bmenu-sort-by-Info-node-name)
(define-key bookmark-bmenu-mode-map "sI"                   'bmkp-bmenu-sort-by-Info-position)
(define-key bookmark-bmenu-mode-map "sk"                   'bmkp-bmenu-sort-by-bookmark-type)
(define-key bookmark-bmenu-mode-map "sn"                   'bmkp-bmenu-sort-by-bookmark-name)
(define-key bookmark-bmenu-mode-map "sr"                   'bmkp-reverse-sort-order)
(define-key bookmark-bmenu-mode-map "s\C-r"                'bmkp-reverse-multi-sort-order)
(define-key bookmark-bmenu-mode-map "ss"                   'bmkp-bmenu-change-sort-order-repeat)
(define-key bookmark-bmenu-mode-map "st"                   'bmkp-bmenu-sort-tagged-before-untagged)
(define-key bookmark-bmenu-mode-map "su"                   'bmkp-bmenu-sort-by-url)
(define-key bookmark-bmenu-mode-map "sv"                   'bmkp-bmenu-sort-by-bookmark-visit-frequency)

;; Not done yet.
;; ;; (define-key bookmark-bmenu-mode-map "sw"                    nil) ; For Emacs20
;; ;; (define-key bookmark-bmenu-mode-map "swe"                   'bmkp-bmenu-sort-by-eww-url)
;; ;; (define-key bookmark-bmenu-mode-map "sw3"                   'bmkp-bmenu-sort-by-w3m-url)

(when (> emacs-major-version 22)        ; Emacs 23+
 (define-key bookmark-bmenu-mode-map (kbd "M-s a C-s")     'bmkp-bmenu-isearch-marked-bookmarks)
 (define-key bookmark-bmenu-mode-map (kbd "M-s a M-C-s")   'bmkp-bmenu-isearch-marked-bookmarks-regexp))
(define-key bookmark-bmenu-mode-map (kbd "M-s a M-s")      'bmkp-bmenu-search-marked-bookmarks-regexp)
(define-key bookmark-bmenu-mode-map "T"                    nil) ; For Emacs20
(define-key bookmark-bmenu-mode-map "T>+"                  'bmkp-bmenu-add-tags-to-marked)
(define-key bookmark-bmenu-mode-map "T>-"                  'bmkp-bmenu-remove-tags-from-marked)
(define-key bookmark-bmenu-mode-map "T>e"                  'bmkp-bmenu-edit-marked)
(define-key bookmark-bmenu-mode-map "T>l"                  'bmkp-bmenu-list-tags-of-marked)
(define-key bookmark-bmenu-mode-map "T>p"                  'bmkp-bmenu-paste-add-tags-to-marked)
(define-key bookmark-bmenu-mode-map "T>q"                  'bmkp-bmenu-paste-replace-tags-for-marked)
(define-key bookmark-bmenu-mode-map "T>v"                  'bmkp-bmenu-set-tag-value-for-marked)
(define-key bookmark-bmenu-mode-map "T>\C-y"               'bmkp-bmenu-paste-add-tags-to-marked)
(define-key bookmark-bmenu-mode-map "T0"                   'bmkp-remove-all-tags)
(define-key bookmark-bmenu-mode-map "T+"                   'bmkp-add-tags)
(define-key bookmark-bmenu-mode-map "T-"                   'bmkp-remove-tags)
(define-key bookmark-bmenu-mode-map "Tc"                   'bmkp-bmenu-copy-tags)
(define-key bookmark-bmenu-mode-map "Td"                   'bmkp-remove-tags-from-all)
(define-key bookmark-bmenu-mode-map "Te"                   'bmkp-bmenu-edit-tags)
(define-key bookmark-bmenu-mode-map "Tl"                   'bmkp-list-all-tags)
(define-key bookmark-bmenu-mode-map "Tm*"                  'bmkp-bmenu-mark-bookmarks-tagged-all)
(define-key bookmark-bmenu-mode-map "Tm%"                  'bmkp-bmenu-mark-bookmarks-tagged-regexp)
(define-key bookmark-bmenu-mode-map "Tm+"                  'bmkp-bmenu-mark-bookmarks-tagged-some)
(define-key bookmark-bmenu-mode-map "Tm~*"                 'bmkp-bmenu-mark-bookmarks-tagged-not-all)
(define-key bookmark-bmenu-mode-map "Tm~+"                 'bmkp-bmenu-mark-bookmarks-tagged-none)
(define-key bookmark-bmenu-mode-map "Tp"                   'bmkp-bmenu-paste-add-tags)
(define-key bookmark-bmenu-mode-map "Tq"                   'bmkp-bmenu-paste-replace-tags)
(define-key bookmark-bmenu-mode-map "Tr"                   'bmkp-rename-tag)
(define-key bookmark-bmenu-mode-map "Ts"                   'bmkp-define-tags-sort-command)
(define-key bookmark-bmenu-mode-map "TS"                   'bmkp-bmenu-show-only-tagged-bookmarks)
(define-key bookmark-bmenu-mode-map "TU"                   'bmkp-bmenu-show-only-untagged-bookmarks)
(define-key bookmark-bmenu-mode-map "Tu*"                  'bmkp-bmenu-unmark-bookmarks-tagged-all)
(define-key bookmark-bmenu-mode-map "Tu%"                  'bmkp-bmenu-unmark-bookmarks-tagged-regexp)
(define-key bookmark-bmenu-mode-map "Tu+"                  'bmkp-bmenu-unmark-bookmarks-tagged-some)
(define-key bookmark-bmenu-mode-map "Tu~*"                 'bmkp-bmenu-unmark-bookmarks-tagged-not-all)
(define-key bookmark-bmenu-mode-map "Tu~+"                 'bmkp-bmenu-unmark-bookmarks-tagged-none)
(define-key bookmark-bmenu-mode-map "Tv"                   'bmkp-bmenu-set-tag-value)
(define-key bookmark-bmenu-mode-map "T\M-w"                'bmkp-bmenu-copy-tags)
(define-key bookmark-bmenu-mode-map "T\C-y"                'bmkp-bmenu-paste-add-tags)
(define-key bookmark-bmenu-mode-map "\M-t"                 'bookmark-bmenu-toggle-filenames) ; `t' in Emacs
(define-key bookmark-bmenu-mode-map "t"                    'bmkp-bmenu-toggle-marks)
(define-key bookmark-bmenu-mode-map "U"                    'bmkp-bmenu-unmark-all)
(define-key bookmark-bmenu-mode-map "\M-u"                 nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "\M-u\M-m"             'bmkp-bmenu-mark-url-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-u\M-s"             'bmkp-bmenu-show-only-url-bookmarks)
(define-key bookmark-bmenu-mode-map "v"                    'bmkp-bmenu-w32-jump-to-marked)
(define-key bookmark-bmenu-mode-map "V"                    nil) ; For Emacs20
(define-key bookmark-bmenu-mode-map "VM"                   'bmkp-bmenu-mark-variable-list-bookmarks)
(define-key bookmark-bmenu-mode-map "VS"                   'bmkp-bmenu-show-only-variable-list-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-o"                 'bmkp-bmenu-w32-jump-to-marked)
(define-key bookmark-bmenu-mode-map "W"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "W3"                   nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "W3M"                  'bmkp-bmenu-mark-w3m-bookmarks)
(define-key bookmark-bmenu-mode-map "W3S"                  'bmkp-bmenu-show-only-w3m-bookmarks)

(when (fboundp 'bmkp-bmenu-mark-eww-bookmarks) ; Emacs 25+
  (define-key bookmark-bmenu-mode-map "WEM"                'bmkp-bmenu-mark-eww-bookmarks)
  (define-key bookmark-bmenu-mode-map "WES"                'bmkp-bmenu-show-only-eww-bookmarks)
  )
(define-key bookmark-bmenu-mode-map "w"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "wM"                   'bmkp-bmenu-mark-snippet-bookmarks)
(define-key bookmark-bmenu-mode-map "wS"                   'bmkp-bmenu-show-only-snippet-bookmarks)
(define-key bookmark-bmenu-mode-map "X"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "XM"                   'bmkp-bmenu-mark-temporary-bookmarks)
(define-key bookmark-bmenu-mode-map "XS"                   'bmkp-bmenu-show-only-temporary-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-X"                 'bmkp-bmenu-toggle-marked-temporary/savable)
(define-key bookmark-bmenu-mode-map "\C-\M-X"              'bmkp-bmenu-toggle-temporary)
(define-key bookmark-bmenu-mode-map "Y"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "YM"                   'bmkp-bmenu-mark-bookmark-file-bookmarks)
(define-key bookmark-bmenu-mode-map "YS"                   'bmkp-bmenu-show-only-bookmark-file-bookmarks)
(define-key bookmark-bmenu-mode-map "Y>"                   nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "Y>+"                  'bmkp-bmenu-copy-marked-to-bookmark-file)
(define-key bookmark-bmenu-mode-map "Y>-"                  'bmkp-bmenu-move-marked-to-bookmark-file)
(define-key bookmark-bmenu-mode-map "Y>0"                  'bmkp-bmenu-create-bookmark-file-from-marked)
(define-key bookmark-bmenu-mode-map "Z"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "ZM"                   'bmkp-bmenu-mark-bookmark-list-bookmarks)
(define-key bookmark-bmenu-mode-map "ZS"                   'bmkp-bmenu-show-only-bookmark-list-bookmarks)


;;; `Bookmark+' menu-bar menu in `*Bookmark List*'

(defvar bmkp-bmenu-menubar-menu (make-sparse-keymap "Bookmark+") "`Boomark+' menu-bar menu.")
(define-key bookmark-bmenu-mode-map [menu-bar bmkp]
  (cons "Bookmark+" bmkp-bmenu-menubar-menu))

;; Top level
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-quit]
  '(menu-item "Quit" bmkp-bmenu-quit
    :help "Quit the bookmark list, saving its state and the current set of bookmarks"))
(define-key bmkp-bmenu-menubar-menu [bmkp-list-defuns-in-commands-file]
  '(menu-item "List User-Defined Bookmark Commands" bmkp-list-defuns-in-commands-file
    :help "List the functions defined in `bmkp-bmenu-commands-file'"))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-describe-marked]
  '(menu-item "Describe Marked Bookmarks" bmkp-bmenu-describe-marked
    :help "Describe the marked bookmarks.  With `C-u' show internal format."))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-describe-this-bookmark]
  '(menu-item "Describe This Bookmark" bmkp-bmenu-describe-this-bookmark
    :help "Describe this line's bookmark.  With `C-u' show internal format."))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-mode-status-help]
  '(menu-item "Current Status, Mode Help" bmkp-bmenu-mode-status-help :keys "?"
    :help "Describe `*Bookmark List*' and show its current status"))

(define-key bmkp-bmenu-menubar-menu [top-sep7] '("--")) ; ------------
(define-key bmkp-bmenu-menubar-menu [bmkp-revert-bookmark-file]
  '(menu-item "Revert to Saved..." bmkp-revert-bookmark-file
    :help "Revert to bookmarks in current bookmark file, as last saved" :keys "C-u g"))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-refresh-menu-list]
  '(menu-item "Refresh to Current" bmkp-bmenu-refresh-menu-list
    :help "Update display to reflect current bookmark list (`C-u': revert from file)"))

(define-key bmkp-bmenu-menubar-menu [top-sep6] '("--")) ; ------------
(define-key bmkp-bmenu-menubar-menu [bmkp-save-menu-list-state]
  '(menu-item "Save Display State..." bmkp-save-menu-list-state
    :help "Save the current bookmark-list display state to `bmkp-bmenu-state-file'"
    :enable (and (not bmkp-bmenu-first-time-p)  bmkp-bmenu-state-file)))
(define-key bmkp-bmenu-menubar-menu [bookmark-write]
  '(menu-item "Save As..." bookmark-write
    :help "Write the current set of bookmarks to a file whose name you enter"))
(define-key bmkp-bmenu-menubar-menu [bookmark-bmenu-save]
  '(menu-item "Save" bookmark-bmenu-save
    :help "Save the current set of bookmarks to the current bookmark file"
    :enable (> bookmark-alist-modification-count 0)))

(define-key bmkp-bmenu-menubar-menu [top-sep5] '("--")) ; ----------
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-edit-marked]
  '(menu-item "Edit Internal Records of Marked (Lisp)..." bmkp-bmenu-edit-marked
    :help "Edit the internal records of the marked bookmarks" :keys "E"))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-relocate-marked]
  '(menu-item "Relocate Marked..." bmkp-bmenu-relocate-marked
    :help "Relocate the marked bookmarks to a directory"))

(define-key bmkp-bmenu-menubar-menu [top-sep4] '("--")) ; ----------
(define-key bmkp-bmenu-menubar-menu [bmkp-make-function-bookmark]
  '(menu-item "New Function Bookmark..." bmkp-make-function-bookmark
    :help "Create a bookmark that will invoke FUNCTION when \"jumped\" to"))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-make-sequence-from-marked]
  '(menu-item "New Sequence Bookmark from Marked..." bmkp-bmenu-make-sequence-from-marked
    :help "Create or update a sequence bookmark from the visible marked bookmarks"))

(define-key bmkp-bmenu-menubar-menu [top-sep3] '("--")) ; ----------
(define-key bmkp-bmenu-menubar-menu [bmkp-choose-navlist-from-bookmark-list]
  '(menu-item "Set Navlist from Bookmark-List Bookmark..." bmkp-choose-navlist-from-bookmark-list
    :help "Set the navigation list from a bookmark-list bookmark"))
(define-key bmkp-bmenu-menubar-menu [bmkp-choose-navlist-of-type]
  '(menu-item "Set Navlist to Bookmarks of Type..." bmkp-choose-navlist-of-type
    :help "Set the navigation list to the bookmarks of a certain type"))

(define-key bmkp-bmenu-menubar-menu [top-sep2] '("--")) ; ----------

(defvar bmkp-bmenu-define-command-menu (make-sparse-keymap "Define Command")
    "`Define Command' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [define-command]
  (cons "Define Command" bmkp-bmenu-define-command-menu))

(defvar bmkp-bmenu-bookmark-file-menu (make-sparse-keymap "Bookmark File")
    "`Bookmark File' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [bookmark-file] (cons "Bookmark File" bmkp-bmenu-bookmark-file-menu))

(when (or (featurep 'bookmark+-lit)
          (and (fboundp 'diredp-highlight-autofiles-mode)  (featurep 'highlight)))
  (defvar bmkp-bmenu-highlight-menu (make-sparse-keymap "Highlight")
    "`Highlight' submenu for menu-bar `Bookmark+' menu.")
  (define-key bmkp-bmenu-menubar-menu [highlight] (cons "Highlight" bmkp-bmenu-highlight-menu)))

(defvar bmkp-bmenu-tags-menu (make-sparse-keymap "Tags")
    "`Tags' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [tags] (cons "Tags" bmkp-bmenu-tags-menu))

(defvar bmkp-bmenu-search-menu (make-sparse-keymap "Search")
    "`Search' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [search] (cons "Search" bmkp-bmenu-search-menu))

(defvar bmkp-bmenu-sort-menu (make-sparse-keymap "Sort")
    "`Sort' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [sort] (cons "Sort" bmkp-bmenu-sort-menu))

(defvar bmkp-bmenu-show-menu (make-sparse-keymap "Show")
    "`Show' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [show] (cons "Show" bmkp-bmenu-show-menu))

(defvar bmkp-bmenu-omit-menu (make-sparse-keymap "Omit")
  "`Omit' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [omitting] (cons "Omit" bmkp-bmenu-omit-menu))

(defvar bmkp-bmenu-mark-menu (make-sparse-keymap "Mark")
    "`Mark' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [marking] (cons "Mark" bmkp-bmenu-mark-menu))

(defvar bmkp-bmenu-delete-menu (make-sparse-keymap "Delete")
    "`Delete' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [delete] (cons "Delete" bmkp-bmenu-delete-menu))

(defvar bmkp-bmenu-toggle-menu (make-sparse-keymap "Toggle")
    "`Toggle' submenu for menu-bar menus `Bookmark+' and `Bookmarks'.")
(define-key bmkp-bmenu-menubar-menu [toggle] (cons "Toggle" bmkp-bmenu-toggle-menu))


;;; `Define Command' submenu -----------------------------------------
(define-key bmkp-bmenu-define-command-menu [bmkp-bmenu-define-full-snapshot-command]
  '(menu-item "To Restore Full Bookmark-List State..." bmkp-bmenu-define-full-snapshot-command
    :help "Define a command to restore the current bookmark-list state"))
(define-key bmkp-bmenu-define-command-menu [bmkp-bmenu-define-command]
  '(menu-item "To Restore Current Order and Filter..." bmkp-bmenu-define-command
    :help "Define a command to use the current sort order, filter, and omit list"))
(define-key bmkp-bmenu-define-command-menu [bmkp-define-tags-sort-command]
  '(menu-item "To Sort by Specific Tags..." bmkp-define-tags-sort-command
    :help "Define a command to sort bookmarks in the bookmark list by certain tags"))
(define-key bmkp-bmenu-define-command-menu [bmkp-bmenu-define-jump-marked-command]
  '(menu-item "To Jump to a Bookmark Now Marked..." bmkp-bmenu-define-jump-marked-command
    :help "Define a command to jump to one of the bookmarks that is now marked"
    :enable bmkp-bmenu-marked-bookmarks))


;;; `Bookmark File' submenu ------------------------------------------
(define-key bmkp-bmenu-bookmark-file-menu [bmkp-empty-file]
  '(menu-item "Empty Bookmark File..." bmkp-empty-file
    :help "Empty an existing bookmark file or create a new, empty bookmark file"))
(define-key bmkp-bmenu-bookmark-file-menu [bmkp-bmenu-set-bookmark-file-bookmark-from-marked]
  '(menu-item "Set Bookmark-File Bookmark from Marked..."
    bmkp-bmenu-set-bookmark-file-bookmark-from-marked
    :help "Create a bookmark file and a bookmark for it, from the marked bookmarks"
    :keys "C-u Y > 0"))
(define-key bmkp-bmenu-bookmark-file-menu [bmkp-bmenu-create-bookmark-file-from-marked]
  '(menu-item "Copy Marked to New Bookmark File..." bmkp-bmenu-create-bookmark-file-from-marked
    :help "Create a bookmark file by copying the marked bookmarks (or current bookmark)"))
(define-key bmkp-bmenu-bookmark-file-menu [bmkp-bmenu-copy-marked-to-bookmark-file]
  '(menu-item "Copy Marked to Bookmark File..." bmkp-bmenu-copy-marked-to-bookmark-file
    :help "Copy the marked bookmarks (or current bookmark) to a bookmark file"))
(define-key bmkp-bmenu-bookmark-file-menu [bmkp-bmenu-move-marked-to-bookmark-file]
  '(menu-item "Move Marked to Bookmark File..." bmkp-bmenu-move-marked-to-bookmark-file
    :help "Move the marked bookmarks (or current bookmark) to a different bookmark file"))

(define-key bmkp-bmenu-bookmark-file-menu [sep] '("--")) ; ------------
(define-key bmkp-bmenu-bookmark-file-menu [bmkp-bmenu-load-marked-bookmark-file-bookmarks]
  '(menu-item "Load Marked Bookmark-File Bookmarks..." bmkp-bmenu-load-marked-bookmark-file-bookmarks
    :help "Load the marked bookmark-file bookmarks, in order"))
(define-key bmkp-bmenu-bookmark-file-menu [bookmark-bmenu-load]
  '(menu-item "Add Bookmarks from File..." bookmark-bmenu-load
    :help "Load additional bookmarks from a bookmark file"))
(define-key bmkp-bmenu-bookmark-file-menu [bmkp-switch-bookmark-file-create]
  '(menu-item "Switch to Bookmark File..." bmkp-switch-bookmark-file-create
    :help "Switch to a different bookmark file, *replacing* the current set of bookmarks"))
(define-key bmkp-bmenu-bookmark-file-menu [bmkp-revert-bookmark-file]
  '(menu-item "Revert to Saved Bookmark File..." bmkp-revert-bookmark-file
    :help "Revert to bookmarks in current bookmark file, as last saved" :keys "C-u g"))


;;; `Toggle' submenu -------------------------------------------------

(define-key bmkp-bmenu-toggle-menu [diredp-highlight-autofiles-mode]
  (bmkp-menu-bar-make-toggle diredp-highlight-autofiles-mode
                             diredp-highlight-autofiles-mode
                             "Autofile Highlighting in Dired"
                             "Whether to highlight autofile bookmarks in Dired us biw %s"
                             "Toggle the value of option `diredp-highlight-autofiles-mode'"
                             nil
                             :visible (and (fboundp 'diredp-highlight-autofiles-mode)
                                           (featurep 'highlight))))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-guess-default-file-handler]
  (bmkp-menu-bar-make-toggle bmkp-toggle-guess-default-file-handler
                             bmkp-guess-default-handler-for-file-flag
                             "Guessing Default File Handler"
                             "Guessing the default handler when creating a file bookmark is now %s"
                             "Toggle the value of option `bmkp-guess-default-handler-for-file-flag'"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-auto-light-when-jump-menu]
  (bmkp-menu-bar-make-toggle bmkp-toggle-auto-light-when-jump-menu bmkp-auto-light-when-jump
                             "Automatic Highlighting When Jumping"
                             "Bookmark highlighting when you jump to a bookmark is now %s"
                             "Toggle the value of option `bmkp-auto-light-when-jump'"
                             (bmkp-toggle-auto-light-when-jump)
                             :visible (featurep 'bookmark+-lit)))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-auto-light-when-set-menu]
  (bmkp-menu-bar-make-toggle bmkp-toggle-auto-light-when-set-menu bmkp-auto-light-when-set
                             "Automatic Highlighting When Setting"
                             "Bookmark highlighting when you set a bookmark is now %s"
                             "Toggle the value of option `bmkp-auto-light-when-set'"
                             (bmkp-toggle-auto-light-when-set)
                             :visible (featurep 'bookmark+-lit)))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-prompt-for-tags]
  (bmkp-menu-bar-make-toggle bmkp-toggle-prompt-for-tags bmkp-prompt-for-tags-flag
                             "Prompting for Tags When Setting"
                             "Prompting for tags when you set a bookmark is now %s"
                             "Toggle the value of option `bmkp-prompt-for-tags-flag'"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-propertize-bookmark-names]
  (bmkp-menu-bar-make-toggle bmkp-toggle-propertize-bookmark-names bmkp-propertize-bookmark-names-flag
                             "Allowing Identical Bookmark Names"
                             "Allowing multiple bookmarks with the same name is now %s"
                             "Toggle the value of option `bmkp-propertize-bookmark-names-flag'"
                             nil
                             :visible (> emacs-major-version 20)))

(define-key bmkp-bmenu-toggle-menu [sep4] '("--")) ; ------------ Jumping-behavior stuff
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-w3m-allow-multiple-buffers]
  (bmkp-menu-bar-make-toggle bmkp-toggle-w3m-allow-multiple-buffers bmkp-w3m-allow-multiple-buffers-flag
                             "Using Multiple Buffers for W3M"
                             "Using a new buffer when jumping to a W3M bookmark is now %s"
                             "Toggle the value of option `bmkp-w3m-allow-multiple-buffers-flag'"))
(when (boundp 'bmkp-eww-allow-multiple-buffers-flag) ; Emacs 25+
  (define-key bmkp-bmenu-toggle-menu [bmkp-toggle-eww-allow-multiple-buffers]
    (bmkp-menu-bar-make-toggle bmkp-toggle-eww-allow-multiple-buffers bmkp-eww-allow-multiple-buffers-flag
                               "Using Multiple Buffers for EWW"
                               "Using a new buffer when jumping to an EWW bookmark is now %s"
                               "Toggle the value of option `bmkp-eww-allow-multiple-buffers-flag'"))
  )
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-showing-region-end]
  (bmkp-menu-bar-make-toggle bmkp-toggle-showing-region-end bmkp-show-end-of-region-flag
                             "Showing Region End"
                             "Showing the end of the region when activating is now %s"
                             "Toggle the value of option `bmkp-show-end-of-region-flag'"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-pop-to]
  (bmkp-menu-bar-make-toggle bmkp-toggle-pop-to bmkp-other-window-pop-to-flag
                             "Using `pop-to-buffer'"
                             "Using `pop-to-buffer' instead of `switch-to-buffer-other-window' is now %s"
                             "Toggle the value of option `bmkp-other-window-pop-to-flag'"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-auto-light-when-jump-menu]
  (bmkp-menu-bar-make-toggle bmkp-toggle-auto-light-when-jump-menu bmkp-auto-light-when-jump
                             "Automatic Highlighting When Jumping"
                             "Bookmark highlighting when you jump to a bookmark is now %s"
                             "Toggle the value of option `bmkp-auto-light-when-jump'"
                             (progn (bmkp-toggle-auto-light-when-jump) bmkp-auto-light-when-jump)
                             :visible (featurep 'bookmark+-lit)))
(when (> emacs-major-version 21)
  (define-key bmkp-bmenu-toggle-menu [bmkp-toggle-crosshairs]
    (bmkp-menu-bar-make-toggle bmkp-toggle-crosshairs bmkp-crosshairs-flag
                               "Crosshairs Highlighting"
                               "Highlighting bookmark location with crosshairs is now %s"
                               "Toggle the value of option `bmkp-crosshairs-flag'"
                               nil
                               :visible (featurep 'crosshairs))))

(define-key bmkp-bmenu-toggle-menu [sep3] '("--")) ; ------------ Temporary bookmark stuff
(define-key bmkp-bmenu-toggle-menu [bmkp-bmenu-toggle-marked-temporary/savable]
  '(menu-item "Temporary/Savable (`X') for Marked" bmkp-bmenu-toggle-marked-temporary/savable
    :help "Toggle the temporary (`X') vs. savable status of the marked bookmarks"))
(define-key bmkp-bmenu-toggle-menu [bmkp-temporary-bookmarking-mode]
  (bmkp-menu-bar-make-toggle bmkp-temporary-bookmarking-mode bmkp-temporary-bookmarking-mode
                             "Temporary Bookmarking"
                             "Temporary bookmarking mode is now %s"
                             "Toggle automatically saving bookmark changes"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-autotemp-on-set]
  (bmkp-menu-bar-make-toggle bmkp-toggle-autotemp-on-set bmkp-autotemp-all-when-set-p
                             "Making Bookmarks Temporary When Set"
                             "Automatically making bookmarks temporary when you set them is now %s"
                             "Toggle automatically making a bookmark temporary when you set it"))

(define-key bmkp-bmenu-toggle-menu [sep2] '("--")) ; ------------ List display stuff
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-bookmark-set-refreshes]
  '(menu-item "Autorefresh for `bmkp-latest-bookmark-alist'" bmkp-toggle-bookmark-set-refreshes
    :help "Toggle whether `bookmark-set' refreshes `bmkp-latest-bookmark-alist'"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-count-multi-mods-as-one]
  (bmkp-menu-bar-make-toggle bmkp-toggle-count-multi-mods-as-one bmkp-count-multi-mods-as-one-flag
                             "Counting Multiple Modifications As One"
                             "Counting multiple modifications as one is now %s"
                             "Toggle the value of option `bmkp-count-multi-mods-as-one-flag'"))
(define-key bmkp-bmenu-toggle-menu [bmkp-bmenu-toggle-marks]
  '(menu-item "Marked/Unmarked" bmkp-bmenu-toggle-marks
    :help "Unmark all marked bookmarks; mark all unmarked bookmarks"))
(define-key bmkp-bmenu-toggle-menu [bmkp-reverse-sort-order]
  '(menu-item "Sort Direction" bmkp-reverse-sort-order
    :help "Toggle the current bookmark sort direction"
    :enable (bmkp-current-sort-order)))
(define-key bmkp-bmenu-toggle-menu [bmkp-bmenu-toggle-show-only-unmarked]
  '(menu-item "Showing Only Unmarked" bmkp-bmenu-toggle-show-only-unmarked
    :help "Alternately show unmarked or all bookmarks"))
(define-key bmkp-bmenu-toggle-menu [bmkp-bmenu-toggle-show-only-marked]
  '(menu-item "Showing Only Marked" bmkp-bmenu-toggle-show-only-marked
    :help "Alternately show unmarked or all bookmarks"))
(define-key bmkp-bmenu-toggle-menu [bmkp-bmenu-toggle-filenames]
  (bmkp-menu-bar-make-toggle bmkp-bmenu-toggle-filenames bookmark-bmenu-toggle-filenames
                             "Showing File Names"
                             "Showing file names is now %s"
                             "Toggle the value of option `bookmark-bmenu-toggle-filenames'"
                             (progn
                               (custom-load-symbol 'bookmark-bmenu-toggle-filenames)
                               (let ((set  (or (get 'bookmark-bmenu-toggle-filenames 'custom-set)
                                               'set-default))
                                     (get  (or (get 'bookmark-bmenu-toggle-filenames 'custom-get)
                                               'default-value)))
                                 (funcall set 'bookmark-bmenu-toggle-filenames
                                          (not (funcall get 'bookmark-bmenu-toggle-filenames))))
                               (if bookmark-bmenu-toggle-filenames
                                   (bookmark-bmenu-show-filenames)
                                 (bookmark-bmenu-hide-filenames))
                               bookmark-bmenu-toggle-filenames)
                             :keys "M-t"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-saving-menu-list-state]
  (bmkp-menu-bar-make-toggle bmkp-toggle-saving-menu-list-state bmkp-bmenu-state-file
                             "Saving Display State"
                             "Ability to save bookmark list state, and autosaving, are now %s"
                             "Toggle the value of option `bmkp-bmenu-state-file'"))

(define-key bmkp-bmenu-toggle-menu [sep1] '("--")) ; ------------ Automatic stuff
(define-key bmkp-bmenu-toggle-menu [bmkp-auto-idle-bookmark-mode]
  '(menu-item "Automatically Creating Bookmarks" bmkp-auto-idle-bookmark-mode
    :help "Toggle the periodic automatic creation of bookmarks"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-save-desktop-before-switching]
  (bmkp-menu-bar-make-toggle bmkp-toggle-save-desktop-before-switching bmkp-desktop-jump-save-before-flag
                             "Autosaving the Desktop Before Switching"
                             "Autosaving the desktop before jumping to a desktop bookmark is now %s"
                             "Toggle the value of option `bmkp-desktop-jump-save-before-flag'"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-saving-relocated]
  (bmkp-menu-bar-make-toggle bmkp-toggle-saving-relocated bmkp-save-new-location-flag
                             "Autosaving Relocated Bookmarks"
                             "Automatically saving relocated bookmarks is now %s"
                             "Toggle the value of option `bmkp-save-new-location-flag'"))
(define-key bmkp-bmenu-toggle-menu [bmkp-toggle-saving-bookmark-file]
  (bmkp-menu-bar-make-toggle bmkp-toggle-saving-bookmark-file bookmark-save-flag
                             "Autosaving Bookmark File"
                             "Automatically saving the bookmark file (`bookmark-save-flag') is now %s"
                             "Toggle the value of option `bookmark-save-flag'"))


;;; `Highlight' submenu ----------------------------------------------
(when (boundp 'bmkp-bmenu-highlight-menu)
  (define-key bmkp-bmenu-highlight-menu [diredp-highlight-autofiles-mode]
    (bmkp-menu-bar-make-toggle diredp-highlight-autofiles-mode
                               diredp-highlight-autofiles-mode
                               "Toggle Autofile Highlighting in Dired"
                               "Whether to highlight autofile bookmarks in Dired us biw %s"
                               "Toggle `diredp-highlight-autofiles-mode'"
                               nil
                               :visible (and (fboundp 'diredp-highlight-autofiles-mode)
                                             (featurep 'highlight))))
  (when (featurep 'bookmark+-lit)
    (define-key bmkp-bmenu-highlight-menu [bmkp-bmenu-show-only-lighted-bookmarks]
      '(menu-item "Show Only Highlighted" bmkp-bmenu-show-only-lighted-bookmarks
        :help "Display (only) highlighted bookmarks"))
    (define-key bmkp-bmenu-highlight-menu [bmkp-bmenu-set-lighting-for-marked]
      '(menu-item "Set Highlighting for Marked" bmkp-bmenu-set-lighting-for-marked
        :help "Set specific highlighting for the marked bookmarks"
        :enable bmkp-bmenu-marked-bookmarks))
    (define-key bmkp-bmenu-highlight-menu [bmkp-bmenu-unlight-marked]
      '(menu-item "Unhighlight Marked" bmkp-bmenu-unlight-marked
        :help "Unhighlight the marked bookmarks"
        :enable bmkp-bmenu-marked-bookmarks))
    (define-key bmkp-bmenu-highlight-menu [bmkp-bmenu-light-marked]
      '(menu-item "Highlight Marked" bmkp-bmenu-light-marked
        :help "Highlight the marked bookmarks"
        :enable bmkp-bmenu-marked-bookmarks))))


;;; `Tags' submenu ---------------------------------------------------
(define-key bmkp-bmenu-tags-menu [bmkp-list-all-tags]
  '(menu-item "List All Tags" bmkp-list-all-tags
    :help "List all tags used for any bookmarks (`C-u': show full, internal form)"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-list-tags-of-marked]
  '(menu-item "List Tags of Marked" bmkp-bmenu-list-tags-of-marked
    :help "List all tags used in the marked bookmarks (`C-u': show full, internal form)"))
(define-key bmkp-bmenu-tags-menu [bmkp-purge-notags-autofiles]
  '(menu-item "Purge Autofiles with No Tags..." bmkp-purge-notags-autofiles
    :help "Delete all autofile bookmarks that have no tags"))
(define-key bmkp-bmenu-tags-menu [bmkp-untag-a-file]
  '(menu-item "Untag a File (Remove Some)..." bmkp-untag-a-file
    :help "Remove some tags from autofile bookmark for a file"))
(define-key bmkp-bmenu-tags-menu [bmkp-tag-a-file]
  '(menu-item "Tag a File (Add Some)..." bmkp-tag-a-file
    :help "Add some tags to the autofile bookmark for a file"))

(define-key bmkp-bmenu-tags-menu [tags-sep] '("--")) ; ---------------
(define-key bmkp-bmenu-tags-menu [bmkp-rename-tag]
  '(menu-item "Rename Tag..." bmkp-rename-tag
    :help "Rename a tag in all bookmarks, even those not showing"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-edit-marked]
  '(menu-item "Edit Tags of Marked (Lisp)..." bmkp-bmenu-edit-marked
    :help "Edit internal records of marked bookmarks (which include their tags)"
    :keys "T > e"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-set-tag-value-for-marked]
  '(menu-item "Set Tag Value for Marked..." bmkp-bmenu-set-tag-value-for-marked
    :help "Set the value of a tag, for each of the marked bookmarks"))
(define-key bmkp-bmenu-tags-menu [bmkp-remove-tags-from-all]
  '(menu-item "Remove Some Tags from All..." bmkp-remove-tags-from-all
    :help "Remove a set of tags from all bookmarks"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-remove-tags-from-marked]
  '(menu-item "Remove Some Tags from Marked..." bmkp-bmenu-remove-tags-from-marked
    :help "Remove a set of tags from each of the marked bookmarks"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-add-tags-to-marked]
  '(menu-item "Add Some Tags to Marked..." bmkp-bmenu-add-tags-to-marked
    :help "Add a set of tags to each of the marked bookmarks"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-paste-replace-tags-for-marked]
  '(menu-item "Paste Tags to Marked (Replace)..." bmkp-bmenu-paste-replace-tags-for-marked
    :help "Replace tags for the marked bookmarks with set of tags copied previously"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-paste-add-tags-to-marked]
  '(menu-item "Paste Tags to Marked (Add)..." bmkp-bmenu-paste-add-tags-to-marked
    :help "Add tags copied from another bookmark to the marked bookmarks"
    :enable bmkp-copied-tags))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-copy-tags]
  '(menu-item "Copy Tags from This Bookmark" bmkp-bmenu-copy-tags
    :help "Copy tags from this bookmark, so you can paste them to other bookmarks"))


;;; `Search' submenu -------------------------------------------------
(define-key bmkp-bmenu-search-menu [bmkp-bmenu-query-replace-marked-bookmarks-regexp]
  '(menu-item "Query-Replace Marked..." bmkp-bmenu-query-replace-marked-bookmarks-regexp
    :help "`query-replace-regexp' over all files whose bookmarks are marked"))
(when (fboundp 'bmkp-bmenu-isearch-marked-bookmarks)
  (define-key bmkp-bmenu-search-menu [bmkp-bmenu-isearch-marked-bookmarks-regexp]
    '(menu-item "Regexp-Isearch Marked..." bmkp-bmenu-isearch-marked-bookmarks-regexp
      :help "Regexp Isearch the marked bookmark locations, in their current order"))
  (define-key bmkp-bmenu-search-menu [bmkp-bmenu-isearch-marked-bookmarks]
    '(menu-item "Isearch Marked..." bmkp-bmenu-isearch-marked-bookmarks
      :help "Isearch the marked bookmark locations, in their current order")))
(define-key bmkp-bmenu-search-menu [bmkp-bmenu-search-marked-bookmarks-regexp]
  '(menu-item "Search Marked..." bmkp-bmenu-search-marked-bookmarks-regexp
    :help "Regexp-search the files whose bookmarks are marked, in their current order"))


;;; `Sort' submenu ---------------------------------------------------
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-url]
  '(menu-item "By URL" bmkp-bmenu-sort-by-url
    :help "Sort URL bookmarks alphabetically by their URL/filename"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-Gnus-thread]
  '(menu-item "By Gnus Thread" bmkp-bmenu-sort-by-Gnus-thread
    :help "Sort Gnus bookmarks by group, then by article, then by message"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-Info-node-name]
  '(menu-item "By Info Node Name" bmkp-bmenu-sort-by-Info-node-name
    :help "Sort Info bookmarks by manual (file) name, then node name, then position"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-Info-position]
  '(menu-item "By Info Book Order" bmkp-bmenu-sort-by-Info-position
    :help "Sort Info bookmarks by manual (file) name, then position (order in book)"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-last-local-file-update]
  '(menu-item "By Last Local File Update" bmkp-bmenu-sort-by-last-local-file-update
    :help "Sort bookmarks by last local file update time"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-last-buffer-or-file-access]
  '(menu-item "By Last Buffer/File Access" bmkp-bmenu-sort-by-last-buffer-or-file-access
    :help "Sort bookmarks by time of last buffer access or local-file access"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-local-file-size]
  '(menu-item "By Local File Size" bmkp-bmenu-sort-by-local-file-size
    :help "Sort bookmarks by local file size"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-local-file-type]
  '(menu-item "By Local File Type" bmkp-bmenu-sort-by-local-file-type
    :help "Sort bookmarks by local file type: file, symlink, directory"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-bookmark-type]
  '(menu-item "By Type" bmkp-bmenu-sort-by-bookmark-type
    :help "Sort bookmarks by type: Info, URL, Gnus, files, other"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-file-name]
  '(menu-item "By File Name" bmkp-bmenu-sort-by-file-name :help "Sort bookmarks by file name"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-bookmark-name]
  '(menu-item "By Bookmark Name" bmkp-bmenu-sort-by-bookmark-name
    :help "Sort bookmarks by bookmark name, respecting `case-fold-search'"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-creation-time]
  '(menu-item "By Creation Time" bmkp-bmenu-sort-by-creation-time
    :help "Sort bookmarks by the time of their creation"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-last-bookmark-access]
  '(menu-item "By Last Bookmark Access" bmkp-bmenu-sort-by-last-bookmark-access
    :help "Sort bookmarks by the time of their last visit as bookmarks"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-bookmark-visit-frequency]
  '(menu-item "By Bookmark Use" bmkp-bmenu-sort-by-bookmark-visit-frequency
    :help "Sort bookmarks by the number of times they were visited as bookmarks"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-marked-before-unmarked]
  '(menu-item "Marked Before Unmarked" bmkp-bmenu-sort-marked-before-unmarked
    :help "Sort bookmarks by putting marked before unmarked"))
(define-key bmkp-bmenu-sort-menu [bmkp-reverse-sort-order]
  '(menu-item "Reverse" bmkp-reverse-sort-order :help "Reverse the current bookmark sort order"))


;;; `Show' submenu ---------------------------------------------------
(define-key bmkp-bmenu-show-menu [bookmark-bmenu-show-all-annotations]
  '(menu-item "Show Annotations" bookmark-bmenu-show-all-annotations
    :help "Show the annotations for all bookmarks (in another window)"))
(define-key bmkp-bmenu-show-menu [bookmark-bmenu-toggle-filenames]
  '(menu-item "Show/Hide File Names" bookmark-bmenu-toggle-filenames
    :help "Toggle whether filenames are shown in the bookmark list"))

(define-key bmkp-bmenu-show-menu [show-sep5] '("--")) ; --------------
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-filter-tags-incrementally]
  '(menu-item "Show Only Tag Matches..." bmkp-bmenu-filter-tags-incrementally
    :help "Incrementally filter bookmarks by tags using a regexp"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-filter-annotation-incrementally]
  '(menu-item "Show Only Annotation Matches..." bmkp-bmenu-filter-annotation-incrementally
    :help "Incrementally filter bookmarks by annotation using a regexp"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-filter-file-name-incrementally]
  '(menu-item "Show Only File Name Matches..." bmkp-bmenu-filter-file-name-incrementally
    :help "Incrementally filter bookmarks by file name using a regexp"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-filter-bookmark-name-incrementally]
  '(menu-item "Show Only Name Matches..." bmkp-bmenu-filter-bookmark-name-incrementally
    :help "Incrementally filter bookmarks by bookmark name using a regexp"))

(define-key bmkp-bmenu-show-menu [show-sep3] '("--")) ; --------------
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-specific-file-bookmarks]
  '(menu-item "Show Only for Specific File" bmkp-bmenu-show-only-specific-file-bookmarks
    :help "Display (only) the bookmarks for a specific file"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-specific-buffer-bookmarks]
  '(menu-item "Show Only for Specific Buffer" bmkp-bmenu-show-only-specific-buffer-bookmarks
    :help "Display (only) the bookmarks for a specific buffer"))

(define-key bmkp-bmenu-show-menu [show-sep2] '("--")) ; --------------
(when (featurep 'bookmark+-lit)
  (define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-lighted-bookmarks]
    '(menu-item "Show Only Highlighted" bmkp-bmenu-show-only-lighted-bookmarks
      :help "Display (only) highlighted bookmarks")))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-temporary-bookmarks]
  '(menu-item "Show Only Temporaries" bmkp-bmenu-show-only-temporary-bookmarks
    :help "Display (only) the temporary bookmarks (`X')"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-autonamed-bookmarks]
  '(menu-item "Show Only Autonamed" bmkp-bmenu-show-only-autonamed-bookmarks
    :help "Display (only) the autonamed bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-autofile-bookmarks]
  '(menu-item "Show Only Autofiles" bmkp-bmenu-show-only-autofile-bookmarks
    :help "Display (only) the autofile bookmarks: those named the same as their files"))

(define-key bmkp-bmenu-show-menu [show-sep1] '("--")) ; --------------
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-toggle-show-only-unmarked]
  '(menu-item "Show Only Unmarked" bmkp-bmenu-toggle-show-only-unmarked
    :help "Hide all marked bookmarks.  Repeat to toggle, showing all"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-toggle-show-only-marked]
  '(menu-item "Show Only Marked" bmkp-bmenu-toggle-show-only-marked
    :help "Hide all unmarked bookmarks.  Repeat to toggle, showing all"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-all]
  '(menu-item "Show All" bmkp-bmenu-show-all
    :help "Show all bookmarks currently known to the bookmark list"))


;;; `Show' > `Only Bookmarks of Type' submenu -----------------------------

(defvar bmkp-bmenu-show-types-menu (make-sparse-keymap "Only Bookmarks of Type")
    "`Only Bookmarks of Type' submenu for `Show' submenu of `Bookmark+' menu.")
(define-key bmkp-bmenu-show-menu [type] (cons "Only Bookmarks of Type" bmkp-bmenu-show-types-menu))

(define-key bmkp-bmenu-show-types-menu [show-sep4] '("--")) ; --------------
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-w3m-bookmarks]
  '(menu-item "W3M URLs" bmkp-bmenu-show-only-w3m-bookmarks
    :help "Display (only) the W3M URL bookmarks"))
(when (fboundp 'bmkp-bmenu-show-only-eww-bookmarks) ; Emacs 25+
  (define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-eww-bookmarks]
    '(menu-item "EWW URLs" bmkp-bmenu-show-only-eww-bookmarks
      :help "Display (only) the EWW URL bookmarks")))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-url-bookmarks]
  '(menu-item "URLs" bmkp-bmenu-show-only-url-bookmarks
    :help "Display (only) the URL bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-man-bookmarks]
  '(menu-item "UNIX Manual Pages" bmkp-bmenu-show-only-man-bookmarks
    :help "Display (only) the `man' page bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-untagged-bookmarks]
  '(menu-item "Untagged" bmkp-bmenu-show-only-untagged-bookmarks
    :help "Display (only) the bookmarks that do not have tags"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-tagged-bookmarks]
  '(menu-item "Tagged" bmkp-bmenu-show-only-tagged-bookmarks
    :help "Display (only) the bookmarks that have tags"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-variable-list-bookmarks]
  '(menu-item "Variable Lists" bmkp-bmenu-show-only-variable-list-bookmarks
    :help "Display (only) the variable-list bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-function-bookmarks]
  '(menu-item "Functions" bmkp-bmenu-show-only-function-bookmarks
    :help "Display (only) the function bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-snippet-bookmarks]
  '(menu-item "Snippets" bmkp-bmenu-show-only-snippet-bookmarks
    :help "Display (only) the snippet bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-region-bookmarks]
  '(menu-item "Regions" bmkp-bmenu-show-only-region-bookmarks
    :help "Display (only) the bookmarks that record a region"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-orphaned-local-file-bookmarks]
  '(menu-item "Orphaned Local Files" bmkp-bmenu-show-only-orphaned-local-file-bookmarks
    :help "Display (only) orphaned local-file bookmarks (`C-u': show remote also)"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-non-invokable-bookmarks]
  '(menu-item "Non-Invokable" bmkp-bmenu-show-only-non-invokable-bookmarks
    :help "Display (only) the non-invokable bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-non-file-bookmarks]
  '(menu-item "Non-Files (Buffers)" bmkp-bmenu-show-only-non-file-bookmarks
    :help "Display (only) the non-file bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-image-bookmarks]
  '(menu-item "Image Files" bmkp-bmenu-show-only-image-bookmarks
    :help "Display (only) image-file bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-icicles-search-hits-bookmarks]
  '(menu-item "Icicles Search-Hits" bmkp-bmenu-show-only-icicles-search-hits-bookmarks
    :help "Display (only) Icicles search-hits bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-info-bookmarks]
  '(menu-item "Info Nodes" bmkp-bmenu-show-only-info-bookmarks
    :help "Display (only) the Info bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-gnus-bookmarks]
  '(menu-item "Gnus Messages" bmkp-bmenu-show-only-gnus-bookmarks
    :help "Display (only) the Gnus bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-file-bookmarks]
  '(menu-item "Files" bmkp-bmenu-show-only-file-bookmarks
    :help "Display (only) the file and directory bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-dired-bookmarks]
  '(menu-item "Dired Buffers" bmkp-bmenu-show-only-dired-bookmarks
    :help "Display (only) the Dired bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-desktop-bookmarks]
  '(menu-item "Desktops" bmkp-bmenu-show-only-desktop-bookmarks
    :help "Display (only) the desktop bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-bookmark-list-bookmarks]
  '(menu-item "Bookmark Lists" bmkp-bmenu-show-only-bookmark-list-bookmarks
    :help "Display (only) the bookmark-list bookmarks"))
(define-key bmkp-bmenu-show-types-menu [bmkp-bmenu-show-only-bookmark-file-bookmarks]
  '(menu-item "Bookmark Files" bmkp-bmenu-show-only-bookmark-file-bookmarks
    :help "Display (only) the bookmark-file bookmarks"))


;;; `Omit' submenu ---------------------------------------------------
(define-key bmkp-bmenu-omit-menu [bmkp-bmenu-show-all]
  '(menu-item "Show All" bmkp-bmenu-show-all
    :visible (eq bmkp-bmenu-filter-function 'bmkp-omitted-alist-only)
    :help "Show all bookmarks (except omitted)"))
(define-key bmkp-bmenu-omit-menu [bmkp-bmenu-show-only-omitted-bookmarks]
  '(menu-item "Show Only Omitted" bmkp-bmenu-show-only-omitted-bookmarks
    :visible (not (eq bmkp-bmenu-filter-function 'bmkp-omitted-alist-only))
    :enable bmkp-bmenu-omitted-bookmarks :help "Show only the omitted bookmarks"))
(define-key bmkp-bmenu-omit-menu [bmkp-unomit-all]
  '(menu-item "Un-Omit All" bmkp-unomit-all
    :visible bmkp-bmenu-omitted-bookmarks :help "Un-omit all omitted bookmarks"))
(define-key bmkp-bmenu-omit-menu [bmkp-bmenu-unomit-marked]
  '(menu-item "Un-Omit Marked" bmkp-bmenu-unomit-marked
    :visible (eq bmkp-bmenu-filter-function 'bmkp-omitted-alist-only)
    :enable (and bmkp-bmenu-omitted-bookmarks
             (save-excursion (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
                             (re-search-forward "^>" (point-max) t)))
    :help "Un-omit the marked bookmarks" :keys "\\[bmkp-bmenu-omit/unomit-marked]"))
(define-key bmkp-bmenu-omit-menu [bmkp-bmenu-omit-marked]
  '(menu-item "Omit Marked" bmkp-bmenu-omit-marked
    :visible (not (eq bmkp-bmenu-filter-function 'bmkp-omitted-alist-only))
    :enable (save-excursion (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
                            (re-search-forward "^>" (point-max) t))
    :help "Omit the marked bookmarks" :keys "\\[bmkp-bmenu-omit/unomit-marked]"))


;;; `Mark' submenu ---------------------------------------------------
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-not-all]
  '(menu-item "Unmark If Not Tagged with All..." bmkp-bmenu-unmark-bookmarks-tagged-not-all
    :help "Unmark all visible bookmarks that are tagged with *some* tag in a set you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-none]
  '(menu-item "Unmark If Tagged with None..." bmkp-bmenu-unmark-bookmarks-tagged-none
    :help "Unmark all visible bookmarks that are *not* tagged with *any* tag you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-all]
  '(menu-item "Unmark If Tagged with All..." bmkp-bmenu-unmark-bookmarks-tagged-all
    :help "Unmark all visible bookmarks that are tagged with *each* tag you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-some]
  '(menu-item "Unmark If Tagged with Some..." bmkp-bmenu-unmark-bookmarks-tagged-some
    :help "Unmark all visible bookmarks that are tagged with *some* tag in a set you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-regexp]
  '(menu-item "Unmark If Tagged Matching Regexp..." bmkp-bmenu-unmark-bookmarks-tagged-regexp
    :help "Unmark bookmarks any of whose tags match a regexp you enter"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-not-all]
  '(menu-item "Mark If Not Tagged with All..." bmkp-bmenu-mark-bookmarks-tagged-not-all
    :help "Mark all visible bookmarks that are *not* tagged with *all* tags you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-none]
  '(menu-item "Mark If Tagged with None..." bmkp-bmenu-mark-bookmarks-tagged-none
    :help "Mark all visible bookmarks that are not tagged with *any* tag you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-all]
  '(menu-item "Mark If Tagged with All..." bmkp-bmenu-mark-bookmarks-tagged-all
    :help "Mark all visible bookmarks that are tagged with *each* tag you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-some]
  '(menu-item "Mark If Tagged with Some..." bmkp-bmenu-mark-bookmarks-tagged-some
    :help "Mark all visible bookmarks that are tagged with *some* tag in a set you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-regexp]
  '(menu-item "Mark If Tagged Matching Regexp..." bmkp-bmenu-mark-bookmarks-tagged-regexp
    :help "Mark bookmarks any of whose tags match a regexp you enter"))

(define-key bmkp-bmenu-mark-menu [mark-sep3] '("--")) ; --------------
(when (featurep 'bookmark+-lit)
  (define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-lighted-bookmarks]
    '(menu-item "Mark Highlighted" bmkp-bmenu-mark-lighted-bookmarks
      :help "Mark highlighted bookmarks")))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-temporary-bookmarks]
  '(menu-item "Mark Temporaries" bmkp-bmenu-mark-temporary-bookmarks
    :help "Mark temporary bookmarks (those with `X')"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-autonamed-bookmarks]
  '(menu-item "Mark Autonamed" bmkp-bmenu-mark-autonamed-bookmarks
    :help "Mark autonamed bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-autofile-bookmarks]
  '(menu-item "Mark Autofiles" bmkp-bmenu-mark-autofile-bookmarks
    :help "Mark autofile bookmarks: those whose names are the same as their files"))

(define-key bmkp-bmenu-mark-menu [mark-sep2] '("--")) ; --------------
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-all]
  '(menu-item "Unmark All" bmkp-bmenu-unmark-all
    :help "Remove a mark you specify (> or D) from each bookmark (RET to remove both kinds)"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-all]
  '(menu-item "Mark All" bmkp-bmenu-mark-all :help "Mark all bookmarks, using mark `>'"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-toggle-marks]
  '(menu-item "Toggle Marked/Unmarked" bmkp-bmenu-toggle-marks
    :help "Unmark all marked bookmarks; mark all unmarked bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-regexp-mark]
  '(menu-item "Mark Regexp Matches..." bmkp-bmenu-regexp-mark
    :help "Mark bookmarks that match a regexp that you enter"))

(define-key bmkp-bmenu-mark-menu [mark-sep4] '("--")) ; --------------
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-specific-file-bookmarks]
  '(menu-item "Mark for Specific File" bmkp-bmenu-mark-specific-file-bookmarks
    :help "Mark bookmarks for a specific file"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-specific-buffer-bookmarks]
  '(menu-item "Mark for Specific Buffer" bmkp-bmenu-mark-specific-buffer-bookmarks
    :help "Mark bookmarks for a specific buffer"))


;; `Mark' > `Bookmarks of Type' submenu ------------------------------
(defvar bmkp-bmenu-mark-types-menu (make-sparse-keymap "Bookmarks of Type")
  "`Bookmarks of Type' submenu for `Mark' submenu of m`Bookmark+' menu.")
(define-key bmkp-bmenu-mark-menu [type] (cons "Bookmarks of Type" bmkp-bmenu-mark-types-menu))

(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-w3m-bookmarks]
  '(menu-item "W3M URLs" bmkp-bmenu-mark-w3m-bookmarks :help "Mark W3M URL bookmarks"))
(when (fboundp 'bmkp-bmenu-mark-eww-bookmarks) ; Emacs 25+
  (define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-eww-bookmarks]
    '(menu-item "EWW URLs" bmkp-bmenu-mark-eww-bookmarks :help "Mark Eww URL bookmarks")))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-url-bookmarks]
  '(menu-item "URLs" bmkp-bmenu-mark-url-bookmarks :help "Mark URL bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-variable-list-bookmarks]
  '(menu-item "Variable Lists" bmkp-bmenu-mark-variable-list-bookmarks
    :help "Mark the variable-list bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-man-bookmarks]
  '(menu-item "UNIX Manual Pages" bmkp-bmenu-mark-man-bookmarks
    :help "Mark `man' page bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-snippet-bookmarks]
  '(menu-item "Snippets" bmkp-bmenu-mark-snippet-bookmarks
    :help "Mark snippet bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-region-bookmarks]
  '(menu-item "Regions" bmkp-bmenu-mark-region-bookmarks
    :help "Mark bookmarks that record a region"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-orphaned-local-file-bookmarks]
  '(menu-item "Orphaned Local Files" bmkp-bmenu-mark-orphaned-local-file-bookmarks
    :help "Mark orphaned local-file bookmarks (`C-u': remote also)"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-non-invokable-bookmarks]
  '(menu-item "Non-Invokable" bmkp-bmenu-mark-non-invokable-bookmarks
    :help "Mark non-invokable bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-non-file-bookmarks]
  '(menu-item "Non-Files (Buffers)" bmkp-bmenu-mark-non-file-bookmarks
    :help "Mark non-file bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-image-bookmarks]
  '(menu-item "Images" bmkp-bmenu-mark-image-bookmarks :help "Mark image-file bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-icicles-search-hits-bookmarks]
  '(menu-item "Icicle Search Hits" bmkp-bmenu-mark-icicles-search-hits-bookmarks
    :help "Mark Icicles search-hit bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-info-bookmarks]
  '(menu-item "Info Nodes" bmkp-bmenu-mark-info-bookmarks :help "Mark Info bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-gnus-bookmarks]
  '(menu-item "Gnus Messages" bmkp-bmenu-mark-gnus-bookmarks :help "Mark Gnus bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-file-bookmarks]
  '(menu-item "Files" bmkp-bmenu-mark-file-bookmarks :help "Mark file bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-dired-bookmarks]
  '(menu-item "Dired Buffers" bmkp-bmenu-mark-dired-bookmarks :help "Mark Dired bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-desktop-bookmarks]
  '(menu-item "Desktops" bmkp-bmenu-mark-desktop-bookmarks
    :help "Mark desktop bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-bookmark-list-bookmarks]
  '(menu-item "Bookmark Lists" bmkp-bmenu-mark-bookmark-list-bookmarks
    :help "Mark the bookmark-list bookmarks"))
(define-key bmkp-bmenu-mark-types-menu [bmkp-bmenu-mark-bookmark-file-bookmarks]
  '(menu-item "Bookmark Files" bmkp-bmenu-mark-bookmark-file-bookmarks
    :help "Mark the bookmark-file bookmarks"))


;;; `Delete' submenu -------------------------------------------------
(define-key bmkp-bmenu-delete-menu [bookmark-bmenu-execute-deletions]
  '(menu-item "Delete Flagged (D)..." bookmark-bmenu-execute-deletions
    :help "Delete the (visible) bookmarks flagged `D'"))
(define-key bmkp-bmenu-delete-menu [bmkp-bmenu-delete-marked]
  '(menu-item "Delete Marked (>)..." bmkp-bmenu-delete-marked
    :help "Delete all (visible) bookmarks marked `>', after confirmation"))
(define-key bmkp-bmenu-delete-menu [bmkp-delete-all-temporary-bookmarks]
  '(menu-item "Delete All Temporaries..." bmkp-delete-all-temporary-bookmarks
    :help "Delete the temporary bookmarks, (`X') whether visible here or not"))


;;; `Edit' menu-bar menu

(require 'menu-bar+ nil t)              ; It redefines `menu-bar-edit-menu'.
(define-key-after menu-bar-edit-menu [separator-snippet] '("--")  'mark-whole-buffer)
(define-key-after menu-bar-edit-menu [bmkp-set-snippet-bookmark]
  '(menu-item "Region to Snippet..." bmkp-set-snippet-bookmark
    :help "Save the region text to a snippet bookmark"
    :enable (and mark-active (not buffer-read-only))) 'separator-snippet)
(define-key-after menu-bar-edit-menu [bmkp-snippet-to-kill-ring]
  '(menu-item "Snippet to Kill Ring..." bmkp-snippet-to-kill-ring
    :help "Copy the text saved in a snippet bookmark to the `kill-ring'")
  'bmkp-set-snippet-bookmark)



;;;---------------------------------------------------------------------------------------

;;; Mouse-3 menu binding.

(defvar bmkp-bmenu-line-overlay nil
  "Overlay to highlight the current line for `bmkp-bmenu-mouse-3-menu'.")
(define-key bookmark-bmenu-mode-map [down-mouse-3] 'bmkp-bmenu-mouse-3-menu)
(define-key bookmark-bmenu-mode-map [mouse-3]      'ignore)

;;;###autoload (autoload 'bmkp-bmenu-mouse-3-menu "bookmark+")
(defun bmkp-bmenu-mouse-3-menu (event)
  "Pop-up menu on `mouse-3' for a bookmark listed in `*Bookmark List*'."
  (interactive "e")
  (let* ((mouse-pos                  (event-start event))
         (inhibit-field-text-motion  t) ; Just in case.
         bol eol bmk-name)
    (with-current-buffer (window-buffer (posn-window mouse-pos))
      (save-excursion
        (goto-char (posn-point mouse-pos))
        (setq bol  (line-beginning-position)
              eol  (line-end-position))
        (unwind-protect
             (progn
               (if bmkp-bmenu-line-overlay ; Don't re-create.
                   (move-overlay bmkp-bmenu-line-overlay bol eol (current-buffer))
                 (setq bmkp-bmenu-line-overlay  (make-overlay bol eol))
                 (overlay-put bmkp-bmenu-line-overlay 'face 'region))
               (setq bmk-name (bookmark-bmenu-bookmark))
               (when bmk-name
                 (sit-for 0)
                 (let* ((map     (easy-menu-create-menu
                                  "This Bookmark"
                                  `(,(if (bmkp-bookmark-name-member bmk-name bmkp-bmenu-marked-bookmarks)
                                         ["Unmark" bookmark-bmenu-unmark]
                                         ["Mark" bookmark-bmenu-mark])
                                    ,(save-excursion
                                      (goto-char (posn-point mouse-pos))
                                      (beginning-of-line)
                                      (if (bmkp-looking-at-p "^D")
                                          ["Unmark" bookmark-bmenu-unmark]
                                        ["Flag for Deletion" bmkp-bmenu-flag-for-deletion]))
                                    ["Omit" bmkp-bmenu-omit]
                                    ["Jump To" bookmark-bmenu-this-window]
                                    ["Jump To in Other Window" bookmark-bmenu-other-window]

                                    "--" ; ----------------------------------------------------
                                    ["Edit Tags..." bmkp-bmenu-edit-tags
                                     :active (bmkp-get-tags bmk-name)]
                                    ["Copy Tags" bmkp-bmenu-copy-tags
                                     ;; You can copy an empty list of tags and paste-replace with it.
                                     ;; :active (bmkp-get-tags bmk-name)
                                     ]
                                    ["Paste Tags (Add)" bmkp-bmenu-paste-add-tags
                                     :active bmkp-copied-tags]
                                    ["Paste Tags (Replace)" bmkp-bmenu-paste-replace-tags
                                     ;; You can paste an empty list of tags to replace tags.
                                     ;; :active bmkp-copied-tags
                                     ]
                                    ["Add Some Tags..." bmkp-bmenu-add-tags]
                                    ["Remove Some Tags..." bmkp-bmenu-remove-tags
                                     :active (bmkp-get-tags bmk-name)]
                                    ["Remove All Tags..." bmkp-bmenu-remove-all-tags
                                     :active (bmkp-get-tags bmk-name)]
                                    ["Set Tag Value..." bmkp-bmenu-set-tag-value
                                     :active (bmkp-get-tags bmk-name)]
                                    ["Rename Tag..." bmkp-rename-tag
                                     :active (bmkp-get-tags bmk-name)]

                                    ["--" 'ignore :visible (featurep 'bookmark+-lit)] ; ---------------
                                    ["Highlight" bmkp-bmenu-light
                                     :visible (featurep 'bookmark+-lit)
                                     :active (not (bmkp-lighted-p bmk-name))]
                                    ["Unhighlight" bmkp-bmenu-unlight
                                     :visible (featurep 'bookmark+-lit)
                                     :active (bmkp-lighted-p bmk-name)]
                                    ["Set Lighting" bmkp-bmenu-set-lighting
                                     :visible (featurep 'bookmark+-lit)]

                                    "--" ; ----------------------------------------------------
                                    ["Toggle Temporary/Savable" bmkp-bmenu-toggle-temporary]
                                    ,@(and (fboundp 'org-add-link-type)
                                           '(["Store Org Link" org-store-link]))
                                    ["Rename or Relocate..." bmkp-bmenu-edit-bookmark-name-and-location]
                                    ["Edit Internal Record (Lisp)..." bmkp-bmenu-edit-bookmark-record]
                                    ["Show Annotation" bookmark-bmenu-show-annotation
                                     :active (bookmark-get-annotation bmk-name)]
                                    ["Add/Edit Annotation..." bookmark-bmenu-edit-annotation]

                                    "--" ; ----------------------------------------------------
                                    ["Describe" bmkp-bmenu-describe-this-bookmark])))
                        (choice  (x-popup-menu event map)))
                   (when choice
                     (call-interactively (lookup-key map (apply 'vector choice)))))))
          (when bmkp-bmenu-line-overlay (delete-overlay bmkp-bmenu-line-overlay)))))))

;;;;;;;;;;;;;;;;;;;;;

(provide 'bookmark+-bmu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-bmu.el ends here
