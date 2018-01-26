;;; bookmark+-chg.el - Change logs for Bookmark+ libraries.
;;
;; Filename: bookmark+-chg.el
;; Description: Change logs for Bookmark+ libraries.
;; Author: Drew Adams
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2017, Drew Adams, all rights reserved.
;; Created: Fri Sep 15 07:58:41 2000
;; Last-Updated: Mon Nov 27 15:04:44 2017 (-0800)
;;           By: dradams
;;     Update #: 16364
;; URL: https://www.emacswiki.org/emacs/download/bookmark%2b-chg.el
;; Doc URL: http://www.emacswiki.org/BookmarkPlus
;; Keywords: bookmarks, bookmark+
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Change log for the Bookmark+ libraries, which extend standard
;;    library `bookmark.el'.  This file contains no code, so you need
;;    not load it.
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) code library
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit'    - (optional) code for highlighting bookmarks
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (bmenu)
;;    `bookmark+-1.el'   - other (non-bmenu) required code
;;    `bookmark+-key.el' - key and menu bindings
;;
;;    `bookmark+-doc'    - documentation (comment-only file)
;;    `bookmark+-chg'    - change log (this file)
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
;;    (The commentary links in #1 and #3 work only if you put library
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
;;         (`.emacs.bmk'), and in any other bookmark files you might
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
 
;;(@> "Index")
;;
;;  If you have library `linkd.el' and Emacs 22 or later, load
;;  `linkd.el' and turn on `linkd-mode' now.  It lets you easily
;;  navigate around the sections of this doc.  Linkd mode will
;;  highlight this Index, as well as the cross-references and section
;;  headings throughout this file.  You can get `linkd.el' here:
;;  http://www.emacswiki.org/emacs/download/linkd.el.
;;
;;  (@> "CHANGE LOG FOR `bookmark+-1.el'")
;;  (@> "CHANGE LOG FOR `bookmark+-bmu.el'")
;;  (@> "CHANGE LOG FOR `bookmark+-key.el'")
;;  (@> "CHANGE LOG FOR `bookmark+-lit.el'")
;;  (@> "CHANGE LOG FOR `bookmark+-mac.el'")
;;  (@> "CHANGE LOG FOR `bookmark+.el'")
 
;;;(@* "CHANGE LOG FOR `bookmark+-1.el'")
;;
;; 2017/11/27 dadams
;;     bookmark-write-file:
;;       Corrected change made on 2017/01/10 (fix for bug #25365).
;;       Bind Lisp mode hooks to nil, to avoid inserting a Lisp file header for existing empty file.
;; 2017/10/31 dadams
;;     bookmark-send-edited-annotation: test using following-char, not bmkp-looking-at-p.
;;     bookmark-save: Non-nil FILE now means use FILE, regardless of PARG value.
;; 2017/10/08 dadams
;;     bmkp-bookmark-description, bmkp-describe-bookmark-internals:
;;       Bind print-(circle|length|level) so pp-to-string prints all.
;; 2017/07/31 dadams
;;     bmkp-find-file-invoke-bookmark-if-autofile:
;;       Bind bmkp-autofile-access-invokes-bookmark-flag to nil while jumping to the bookmark.
;; 2017/07/30 dadams
;;     Added: bmkp-autofile-access-invokes-bookmark-flag, bmkp-find-file-invoke-bookmark-if-autofile.
;;     bmkp-get-bookmark-in-alist: Use arg ALIST (was neglected).
;; 2017/07/19 dadams
;;     Put back bmkp-info-cp, as an obsolete alias, temporarily.
;; 2017/07/03 dadams
;;     Added: bmkp-info-position-cp, bmkp-info-sort-ignores-directories-flag.
;;     Renamed: bmkp-info-cp to bmkp-info-node-name-cp.
;;     bmkp-sort-comparer: Applied renaming of bmkp-info-cp.
;;     bmkp-info-node-name-cp: Respect bmkp-info-sort-ignores-directories-flag (default: manual names)
;; 2017/06/26 dadams
;;     Added: bmkp-kmacro-list-bookmark-p.
;;     bmkp-bookmark-description: Handle bmkp-kmacro-list-bookmark-p.
;; 2017/06/25 dadams
;;     Added: bmkp-set-kmacro-bookmark, bmkp-set-kmacro-list-bookmark, bmkp-jump-kmacro-list,
;;            bmkp-make-kmacro-list-record.
;; 2017/05/12 dadams
;;     Added: bmkp-eww-auto-bookmark-mode, bmkp-set-eww-bookmark-here, bmkp-toggle-eww-auto-type,
;;            bmkp-eww-auto-type.  Thx to Charles Roelli.
;; 2017/03/31 dadams
;;     Added other-window versions of: bmkp-(next|previous)(TYPE)-bookmark(-repeat).
;;     bmkp-autonamed-bookmark-p:
;;       If BUFFER is nil then let ?B match any name - do not use current buffer for nil case.
;;     bmkp-goto-position: Error now mentions buffer name, not just file.
;;     bmkp-cycle: If empty bmkp-nav-alist ask before setting it to bookmark-alist.
;; 2017/02/26 dadams
;;     Added:
;;       bmkp-eww-rename-buffer, bmkp-eww-new-buffer-name, bmkp-eww-sans-pop-to-buffer,
;;       bmkp-eww-buffer-handling (was ~bmkp-eww-allow-multiple-buffers-flag), 
;;       bmkp-get-eww-mode-buffer, bmkp-eww-jumping-p, bmkp-eww-new-buf-name,
;;       bmkp-jump-eww-in-buffer-*eww* (was ~bmkp-jump-eww-only-one-buffer),
;;       bmkp-jump-eww-renaming-buffer (was ~bmkp-jump-eww-new-buffer), bmkp-info-auto-type,
;;       bmkp-info-auto-bookmark-mode, bmkp-set-info-bookmark-with-node-name,
;;       bmkp-toggle-info-auto-type.
;;     Removed: bmkp-eww-allow-multiple-buffers-flag, bmkp-eww-set-new-buffer-name,
;;              bmkp-jump-eww-new-buffer, bmkp-jump-eww-only-one-buffer.
;;     bmkp-edit-bookmark-name-and-location: Don't consider changed-buffname-p if EWW bookmark.
;;     bmkp-make-eww-record: Use bmkp-eww-new-buffer-name for buffer-name field.
;;     Add bmkp-eww-rename-buffer to hooks eww-after-render-hook and eww-restore-history.
;;     Support EWW only for Emacs 25+, not for 24.4+.  (E.g., bmkp-eww-title, bmkp-eww-url).
;;     bookmark-show-all-annotations:
;;       Use bookmark-maybe-load-default-file, to load bookmark file.
;;       For Emacs 24+, call view-mode-enter with no args.  Thx to Alan Wehmann for bug report
;;           and Martin Rudalics for info about the new signature.
;;     bmkp-completing-read-1: Use single default, not list, for Emacs 20-22.
;;     bmkp-default-bookmark-name:
;;       Ensure use a single bname, not a list of names returned by bmkp-default-lighted.
;; 2017/01/29 dadams
;;     Added: bmkp-eww-title, bmkp-eww-url.
;;     bookmark-set, bmkp-this-buffer-p, bmkp-make-eww-record: Use bmkp-eww-title, bmkp-eww-url.
;; 2017/01/10 dadams
;;     Added:
;;       bmkp-eww-allow-multiple-buffers-flag, bmkp-eww-set-new-buffer-name, bmkp-jump-eww-new-buffer,
;;       bmkp-jump-eww-only-one-buffer.
;;     Renamed: bmkp-replace-eww-keys-flag     to bmkp-eww-replace-keys-flag,
;;              bmkp-w3m-allow-multi-tabs-flag to bmkp-w3m-allow-multiple-buffers-flag,
;;              bmkp-jump-w3m-new-session      to bmkp-jump-w3m-new-buffer,
;;              bmkp-jump-w3m-only-one-tab     to bmkp-jump-w3m-only-one-buffer.  Keep old as aliases.
;;     bmkp-jump-eww: Dispatch to bmkp-jump-eww-(new|only-one)-buffer
;;     bmkp-jump-w3m-new-buffer, bmkp-jump-w3m-only-one-buffer: Use get-buffer-create, just in case.
;;     bookmark-write-file:
;;       Updated per latest fix for bug #25365: insert version stamp after writing bmks.  UNTESTED.
;; 2017/01/08 dadams
;;     Use the term "entry", not "property" everywhere, for bookmark entries (fields).
;; 2017/01/07 dadams
;;     bookmark-write-file, bookmark-load, bmkp-temporary-bookmarking-mode:
;;       Use bookmark-file-coding-system (Emacs bug #25365).  UNTESTED.
;; 2017/01/03 dadams
;;     bookmark-location: Corrected doc string to reflect code: buffer before file.
;; 2016/12/31 dadams
;;     Added: bmkp-non-invokable-bookmark-p, bmkp-non-invokable-alist-only.
;;     bmkp-bookmark-description: Include non-invokable.
;; 2016/12/21 dadams
;;     Added: bmkp-ffap-max-region-size, bmkp-ffap-guesser.
;;     bmkp-file-target-set, bmkp-autofile-set, bmkp-autofile-(add|remove)-tags:
;;       Use bmkp-ffap-guesser.bmkp-ffap-guesser, not ffap-guesser.
;; 2016/12/11 dadams
;;     Added: bmkp-convert-eww-bookmarks, bmkp-replace-eww-keys-flag.
;; 2016/11/25 dadams
;;     bmkp-make-function-bookmark: Added bookmark-make-record-default, to include creation date.
;;     bmkp-make-sequence-record: Use 0 as position, in record.
;;     bookmark-sort-flag: Replace doc string with mention that it is not used.
;; 2016/11/23 dadams
;;     bookmark-save, bookmark-write-file, bookmark-load, bmkp-empty-file, bmkp-tags-in-bookmark-file,
;;       bmkp-list-defuns-in-commands-file, bmkp-set-bookmark-file-bookmark, bmkp-desktop-read:
;;         Raise an error if we have a directory, not a file.
;; 2016/11/18 dadams
;;     Support Emacs 24.[45] too.
;;     bookmark-set, bmkp-this-buffer-p, bmkp-make-eww-record: Update for Emacs 24.[45].
;;     bmkp-edit-bookmark-name-and-location: Add support for EWW.
;;     bmkp-jump-eww: Create buffer *eww* if it does not exist.
;;     bmkp-crosshairs-highlight: Respect bmkp-crosshairs-highlight (not really needed).
;;     bmkp-eww-cp: typos: w3m -> eww.
;; 2016/11/15 dadams
;;     bmkp-*eww-*, bookmark-set, bmkp-this-buffer-p, bmkp-url-bookmark-p, bmkp-url-target-set,
;;       bmkp-bookmark-description: Ensure that EWW code is only for Emacs 25+.
;; 2016/11/14 dadams
;;     Added: bmkp-eww-jump, bmkp-eww-jump-other-window, bmkp-eww-alist-only, bmkp-eww-bookmark-p,
;;            bmkp-eww-cp, bmkp-jump-eww, bmkp-make-eww-record, bmkp-eww-history.
;;     bmkp-non-file-filename: Added EWW entry.
;;     bookmark-set, bmkp-this-buffer-p, bmkp-url-bookmark-p, bmkp-url-target-set,
;;       bmkp-bookmark-description: Support eww-mode.
;;     bmkp-url-jump(-other-window): Just use bmkp-url-alist-only.
;; 2016/10/27 dadams
;;     bmkp-end-position-post-context: Typo: (point) -> ereg.
;; 2016/09/21 dadams
;;     Added: bmkp-desktop-default-directory.
;;     Added: desktop-full-file-name, for Emacs < 22.
;;     bmkp-set-desktop-bookmark, bmkp-desktop-change-dir, bmkp-desktop-read:
;;       Use bmkp-desktop-default-directory when reading or expanding file name.
;;     bmkp-desktop-change-dir: Error in interactive spec too, if cannot load desktop.el.
;; 2016/09/10 dadams
;;     Added: bmkp-format-spec.
;;     bmkp-autoname-format: Use %B in default value.  Update doc string, allowing %B.
;;     bmkp-autonamed-bookmark-p: Added optional arg BUFFER.  Use bmkp-format-spec.
;;     bmkp-autonamed-bookmark-for-buffer-p, bmkp-autonamed-this-buffer-bookmark-p:
;;       Use bmkp-autonamed-bookmark-p.
;; 2016/09/06 dadams
;;     Added: bmkp-read-from-whole-string.
;;     bmkp-make-function-bookmark, bmkp-set-sequence-bookmark: Use bmkp-read-from-whole-string.
;; 2016/06/23 dadams
;;     bmkp-remove-all-tags, bmkp-add-tags, bmkp-set-tag-value, bmkp-remove-tags,
;;       bmkp-paste-(add|paste)-tags, bmkp-autofile-add-tags:
;;         Corrected doc string to say also that NO-UPDATE-P does not update mod count.
;;     bookmark-store, bookmark-set, bookmark-relocate, bmkp-(url|file)-target-set,
;;       bmkp-autofile-set, bmkp-autofile-remove-tags:
;;         Renamed arg NO-UPDATE-P to NO-REFRESH-P.
;; 2016/06/21 dadams
;;     bmkp-edit-bookmark-records-send, bmkp-set-tag-value-for-bookmarks, bmkp-rename-tag,
;;       bmkp-delete-bookmarks:
;;         Put bookmark-save-flag let-binding around iteration only, so modification is recorded etc.
;; 2016/05/30 dadams
;;     bmkp-not-near-other-auto-idle-bmks: Corrected typo: test distance for POSITION, not point.
;; 2016/04/23 dadams
;;     Added: bmkp-set-dired-bookmark-for-files.
;; 2015/10/31 dadams
;;     bookmark-import-new-list: Added arg RETURN-BMKS: Return bookmarks added, if non-nil.
;; 2015/09/07 dadams
;;     bmkp-some: Return cons (ELEMENT . VALUE).
;; 2015/08/16 dadams
;;     Renamed bmkp-set-restrictions-bookmark to bmkp-set-izones-bookmark.
;;     Renamed wide-n.el stuff to zones.el stuff.
;; 2015/08/13 dadams
;;     Removed: bmkp-readable-marker.
;;     bmkp-set-restrictions-bookmark:
;;       Added optional args.  A prefix arg prompts for VARIABLE.  Use wide-n-readable-marker.
;; 2015/08/12 dadams
;;     bmkp-set-restrictions-bookmark: Update for new wide-n format.
;; 2015/08/10 dadams
;;     bmkp-set-restrictions-bookmark:
;;       Added missing comma, to eval end marker.  Corrected END: caddr now, not cddr.
;; 2015/08/06 dadams
;;     bmkp-some: Fixed yesterday's fix. ;-)
;; 2015/08/05 dadams
;;     bmkp-some: Fixed so it returns the first list element for which the predicate is true.
;; 2015/07/31 dadams
;;     bmkp-set-restrictions-bookmark: Use new wide-n-restrictions format: (NUM BEG END).
;; 2015/06/26 dadams
;;     Added: bmkp-function-alist-only.
;; 2015/06/18 dadams
;;     bmkp-bookmark-description: Print location, if present, for non-file bmk.  Thx Martin Oppegaard.
;;     bookmark-location: Reordered - prefer buffer name to file name.
;; 2015/06/17 dadams
;;     bmkp-bookmark-description: Added another \t for URL:.
;; 2015/06/15 dadams
;;     Allow for POSITION in bookmarks to be nil or absent - updated bookmark-default-handler,
;;       bmkp-region-bookmark-p, bmkp-handle-region-default, bmkp-goto-position, bmkp-jump-dired,
;;       bmkp-not-near-other-auto-idle-bmks.
;; 2015/05/23 dadams
;;     bookmark-load: Reset bmenu stuff: bmkp-bmenu-marked-bookmarks, bmkp-modified-bookmarks,
;;       bmkp-flagged-bookmarks, bmkp-bmenu-omitted-bookmarks, bmkp-bmenu-filter-function.
;; 2015/04/24 dadams
;;     bookmark-set: Clarified doc string wrt bookmarks that have the same name.
;; 2015/04/13 dadams
;;     bmkp-temporary-bookmarking-mode:
;;       Have to do bookmark-insert-file-format-version-stamp here, because make-temp-file creates the
;;       file, so it satisfies file-exists-p for bookmark-write-file.
;; 2015/04/10 dadams
;;     bmkp-remove-all-tags, bmkp-add-tags, bmkp-remove-tags:
;;       Do not call bmkp-maybe-save-bookmarks if NO-UPDATE-P.
;;     bmkp-set-tag-value-for-(navlist|bookmarks): Added optional arg MSG-P.
;;     bmkp-set-tag-value-for-bookmarks:
;;       Call bmkp-tags-list, bmkp-maybe-save-bookmarks, and bmkp-refresh/rebuild-menu-list.
;;     bmkp-set-tag-value:
;;       Pass non-nil NO-UPDATE-P to bmkp-add-tags.  Unless NO-UPDATE-P, call bmkp-tags-list,
;;       bmkp-maybe-save-bookmarks, and bmkp-refresh/rebuild-menu-list.
;;     bmkp-remove-tags-from-all: Call bmkp-maybe-save-bookmarks and bmkp-refresh/rebuild-menu-list.
;;     bmkp-rename-tag, bmkp-purge-notags-autofiles: Call bmkp-maybe-save-bookmarks.
;; 2015/03/23 dadams
;;     bookmark-show-all-annotations: When in Bookmark List buffer, respect the sort order.
;; 2015/02/24 dadams
;;     bmkp-get-autofile-bookmark: Corrected 2015-02-15 fix - ensure BDIR is non-nil too, before test.
;; 2015/02/22 dadams
;;     Moved here from bookmark+-bmu.el:
;;       bmkp-reset-bmkp-store-org-link-checking-p, bmkp-store-org-link-checking-p.
;;       Advice of org-store-link (not needed for bmkp-bmenu-store-org-link).
;;     bmkp-store-org-link(-1): Link type changed from bookmark-other-window to bookmark-other-win.
;;     bookmark-prop-set: Added optional arg DONT-UPDATE-NAME.
;;                        Update bmkp-full-record property on bookmark name, unless DONT-UPDATE-NAME.
;;     bmkp-record-visit, bmkp-save-new-region-location, bmkp-goto-position:
;;       Use arg DONT-UPDATE-NAME in sequence of calls to bookmark-prop-set.
;; 2015/02/21 dadams
;;     Added: bmkp-store-org-link, bmkp-store-org-link-1.
;; 2015/02/15 dadams
;;     bmkp-get-autofile-bookmark: Corrected test for same file to use absolute file names.
;;     bmkp-read-bookmark-file-default: .emacs.bmk -> ~/.emacs.bmk.
;; 2015/02/11 dadams
;;     Added (redefinition of) bookmark-insert-current-bookmark for Emacs 24.3+.
;; 2015/02/08 dadams
;;     Added: bmkp-properties-to-keep, bmkp-tagged-alist-only, bmkp-untagged-alist-only.
;;     Renamed: bmkp-icicle-* to bmkp-icicles-*.
;;     bmkp-this-buffer-bmenu-list, bmkp-navlist-bmenu-list: Restore original values in case of error.
;;     bookmark-set: Do not overwrite properties listed in option bmkp-properties-to-keep.
;;     bmkp-prompt-for-tags-flag: Updated doc string wrt adding, not replacing.
;;     bmkp-autofile-filecache: Corrected autoload cookie (typo).
;; 2015/02/05 dadams
;;     bookmark-insert-annotation: BOOKMARK can be a bookmark or its name.
;; 2015/02/03 dadams
;;     bmkp-occur-target-set: Removed unused let-binding.
;; 2015/01/28 dadams
;;     Added: bookmark-automatically-show-annotations, bmkp-show-this-annotation-read-only,
;;            bmkp-edit-this-annotation.
;;     Soft-require font-lock+.el.
;;     bookmark-insert-annotation: Convert BOOKMARK input to its name.
;;     bookmark-edit-annotation-mode: Bind key C-x C-q to bmkp-show-this-annotation-read-only.
;;     bookmark-show-annotation-mode: Bind key C-x C-q to bmkp-edit-this-annotation.
;;     bookmark-show-annotation:
;;       If bookmark-automatically-show-annotations = edit then just call bookmark-edit-annotation.
;;       Fix title highlighting (need font-lock+.el) and buffer-modified-p.
;;       Set bookmark-annotation-name.  Use `, not ', in title.
;;     bookmark-edit-annotation: Manage buffer-modified-p.
;; 2015/01/17 dadams
;;     Added bmkp-annotate-bookmark.
;;     bookmark-show-annotation, bookmark-show-all-annotations: Made it interactive.
;; 2015/01/01 dadams
;;     bookmark-default-handler, bmkp-goto-position:
;;       Do not bind enable-local-variables to nil - the visit is not hidden and temporary.
;; 2014/12/18 dadams
;;     bmkp-this-file-bmenu-list: Restore vars if error.
;; 2014/12/16 dadams
;;     bmkp-last-specific-file-p: Use bmkp-same-file-p, not string=.
;; 2014/12/15 dadams
;;     Added: bmkp-non-dir-file-jump, bmkp-non-dir-file-jump-other-window,
;;            bmkp-local-non-dir-file-jump, bmkp-local-non-dir-file-jump-other-window,
;;            bmkp-remote-non-dir-file-jump, bmkp-remote-non-dir-file-jump-other-window,
;;            bmkp-non-dir-file-alist-only, bmkp-non-dir-file-bookmark-p,
;;            bmkp-local-non-dir-file-alist-only, bmkp-local-non-dir-file-bookmark-p,
;;            bmkp-remote-non-dir-file-alist-only, bmkp-remote-non-dir-file-bookmark-p.
;;     bmkp-autotemp-bookmark-predicates: Added bmkp(-local|-remote)-non-dir-file-bookmark-p.
;; 2014/11/15 dadams
;;     Added: bmkp-region-jump-narrow-indirect-other-window, bmkp-handle-region+narrow-indirect.
;;     bmkp-jump-man: Updated for Emacs 24+, where Man-getpage-in-background returns process buffer.
;; 2014/11/14 dadams
;;     bmkp-jump-1: Made arg FLIP-USE-REGION-P optional.  Corrected doc string for it: it flips.
;;     bmkp-snippet-to-kill-ring, bmkp-autonamed-*jump*, bmkp-temporary-jump*, bmkp-w32-browser-jump,
;;       bmkp-variable-list-jump, bmkp-autofile-jump*: Removed FLIP arg (optional).
;;     bmkp-region-jump*: Bind bmkp-use-region to t, and don't pass FLIP arg to bmkp-jump-1.
;; 2014/11/10 dadams
;;     Added: bookmark-show-annotation-mode, (redefinition of) bookmark-default-annotation-text.
;;     Renamed: bmkp-edit-annotation-mode-inherit-from to bmkp-annotation-modes-inherit-from.
;;     bookmark-show-annotation: Call bookmark-show-annotation-mode, not view-mode-enter.
;;     bookmark-edit-annotation-mode:
;;       Use literal C-c C-M-c, since bookmark-send-edited-annotation is also bound to C-c C-c.
;; 2014/11/09/dadams
;;     Added: bmkp-get-external-annotation, bmkp-visit-external-annotation.
;;     bookmark-show-annotation: If the annotation is external then jump to its destination.
;; 2014/11/08 dadams
;;     bmkp-bookmark-description: Corrected formatting for search-hits-p.
;; 2014/10/28 dadams
;;     Added: option bmkp-edit-annotation-mode-inherit-from.
;;     bookmark-edit-annotation-mode: Redefined to use define-derived-mode (per Emacs 25).
;;                                    Use new option bmkp-edit-annotation-mode-inherit-from.
;;     bookmark-send-edited-annotation: Allow derived mode (per Emacs 25).
;;     bookmark-edit-annotation:
;;       Call bookmark-insert-annotation.  Set local var bookmark-annotation-name to arg (per E25).
;; 2014/10/27 dadams
;;     Added: Redefinition of bookmark-insert-annotation.
;;     bookmark-edit-annotation-mode: Use bookmark-insert-annotation.
;; 2014/08/22 dadams
;;     bmkp-desktop-file-p: Redefined to not visit the file: use insert-file-contents-literally.
;;                          Added (not (file-directory-p filename)) condition.
;; 2014/08/21 dadams
;;     Added: bmkp-annotated-bookmark-p.
;;     bmkp-autofile-alist-only: Use bmkp-annotated-bookmark-p.
;;     bmkp-completing-read-1: Bind icicle-bookmark-completing-p.
;;     bmkp-file-this-dir-bookmark-p: Return nil if BOOKMARK is not a bookmark.
;;                                    Use bmkp-same-file-p, not equal.
;; 2014/08/19 dadams
;;     Added: bmkp-dired-wildcards-alist-only, bmkp-navlist-bookmark-p.
;; 2014/08/18 dadams
;;     bmkp-this-file-p: Return nil (instead of raising error) if THIS-FILE is nil.
;; 2014/07/11 dadams
;;     bookmark-load: Do not customize-save-variable if no change to bmkp-last-as-first-bookmark-file.
;;     bmkp-new-bookmark-default-names: Use setq, not push, for Emacs 20.
;; 2014/07/06 dadams
;;     Renamed: bmkp-show-end-of-region, bmkp-w3m-allow-multi-tabs to *-flag.
;; 2014/07/05 dadams
;;     bookmark-write-file: List in file could be (), in which case cannot search backward for \n).
;;     bmkp-read-bookmark-for-type: Added optional PROMPT arg.
;;     bmkp-jump-snippet: Provide PROMPT to bmkp-read-bookmark-for-type.  Better msg.
;; 2014/07/03 dadams
;;     Added: bmkp-read-bookmark-file-default.
;;     Added redefinition of bookmark-import-new-list, bookmark-maybe-rename.
;;     bookmark-load: Do not set blist to value of bookmark-import-new-list.
;;     bookmark-alist-from-buffer: Added optional arg do-not-propertize-p.  (Not used anywhere yet.)
;;     bookmark-save: Use bmkp-read-bookmark-file-default.
;;     bookmark-write-file:
;;       Added optional arg ADD.  Do not kill FILE buffer if it existed prior to invoking function.
;;       Promoted inner let-bindings print-length etc.
;;       Delete contents only if file does not exist (just in case). Else *-maybe-upgrade-file-format.
;;       Do not delete region if ADD.  Position point depending on ADD.
;;     bookmark-write-file, bookmark-default-handler, bmkp-save-menu-list-state, bmkp-goto-position,
;;       bmkp-compilation-target-set:
;;         Let-bind enable-local-variables around find-file-noselect.
;;     bmkp-read-bookmark-file-name: Just pass DEFAULT-FILENAME to read-file-name.
;;     bmkp-empty-file: Pass nil ADD arg to bookmark-write-file.
;; 2014/06/29 dadams
;;     Added: bmkp-before-jump-hook, bmkp-desktop-save, bmkp-desktop-save-as-last,
;;            bmkp-desktop-current-file, bmkp-desktop-jump-save-before-flag.
;;     bmkp-jump-1: Run bmkp-before-jump-hook.
;;     bmkp-set-desktop-bookmark: Use bmkp-desktop-save.
;;     bmkp-desktop-jump: If bmkp-desktop-jump-save-before-flag then bmkp-desktop-save-as-last.
;;     bmkp-desktop-kill: Updated for Emacs 24.4+.
;; 2014/06/21 dadams
;;     Added: bmkp-icicle-search-hits-alist-only, bmkp-icicle-search-hits-bookmark-p,
;;       bmkp-icicle-search-hits-retrieve-more, bmkp-jump-icicle-search-hits,
;;       bmkp-retrieve-icicle-search-hits, bmkp-retrieve-more-icicle-search-hits,
;;       bmkp-retrieve-icicle-search-hits-1, bmkp-set-icicle-search-hits-bookmark,
;;       bmkp-make-icicle-search-hits-record, bmkp-unpropertized-string.
;;     bmkp-bookmark-description: Handle Icicles search hits.
;; 2014/05/30 dadams
;;     bmkp-set-restrictions-bookmark: Updated for new restrictions format (wide-n.el).
;; 2014/05/27 dadams
;;     bmkp-describe-bookmark(-internals), bmkp-list-defuns-in-commands-file:
;;       Use bmkp-with-help-window, not with-output-to-temp-buffer (Emacs 24.4+ silliness).
;; 2014/04/05 dadams
;;     Removed bmkp-create-dired-bookmarks-recursive: 
;;      Moved to dired+.el and renamed diredp-do-bookmark-dirs-recursive.
;; 2014/04/02 dadams
;;     bmkp-paste-replace-tags: Added Note to doc string about pasting an empty list of tags.
;; 2014/03/23 dadams
;;     bmkp-file-target-set: Fix interactive spec (parens).
;;     bmkp-file-target-set, bmkp-autofile-set, bmkp-autofile-(add|remove)-tags:
;;       Soft-require ffap.el before using ffap-guesser.
;; 2014/03/10 dadams
;;     bookmark-write-file:
;;       Remove prop face & Icicles props, anyway (but not bothering for sequence entry of seq bmks).
;;     bookmark-write-file, bmkp-edit-tags, bmkp-save-menu-list-state, bmkp-readable-p:
;;       Bind print-circle to bmkp-propertize-bookmark-names-flag, not t, to avoid string reuse.
;; 2014/03/07 dadams
;;     bookmark-exit-hook-internal: Do not raise error, since this is on kill-emacs-hook.
;;     Bug reported: http://superuser.com/q/726057/250462.
;; 2014/01/02 dadams
;;     Reverted yesterday's change.  Just use cond instead of case.
;; 2014/01/01 dadams
;;     Added bmkp-file-cache-ad-hack, as workaround for macro case not getting byte-compiled.
;;     file-cache-add-file: Use bmkp-file-cache-ad-hack.  Thx to Michael Heerdegen.
;; 2013/11/21 dadams
;;    bmkp-url-target-set: Added argument NO-OVERWRITE-P.
;;    bmkp-(url|file)-target-set: Numeric prefix arg means do not overwrite.  N<0 means use full name.
;; 2013/11/05 dadams
;;     Added: bmkp-create-dired-bookmarks-recursive.
;;     bookmark-set: Added optional arg NO-UPDATE-P - pass it to bookmark-store.
;; 2013/10/29 dadams
;;     Added: bmkp-pop-to-readable-marker, bmkp-readable-marker, bmkp-bookmark-set-confirm-overwrite,
;;            bmkp-bookmark-set-confirms-overwrite-p.
;;     bookmark-set: Ask for overwrite confirmation if plain prefix arg and bookmark exists.
;;     bmkp-menu-bar-set-bookmark: Use bmkp-bookmark-set-confirm-overwrite, not bookmark-set.
;; 2013/10/07 dadams
;;     bmkp-edit-bookmark-records-send: Move to line of current bmk, if only one.
;; 2013/08/09 dadams
;;     Added: bmkp-read-bookmark-file-hook, bmkp-desktop-file-p.
;;     Renamed: bmkp-printable-p to bmkp-readable-p.
;;     bmkp-readable-p: Treat string with no text props separately.
;;     bookmark-alist: Updated doc string.
;;     bookmark-send-edited-annotation: looking-at -> bmkp-looking-at-p (new).
;;     bookmark-load: Update blist with bookmark-import-new-list.
;;                    Run bmkp-read-bookmark-file-hook after reading the bookmark file.
;;     bmkp-set-desktop-bookmark: Added prefix arg: sets bookmark without saving desktop file.
;; 2013/07/24 dadams
;;     bmkp-new-bookmark-default-names, bookmark-make-record-default:
;;       Test using (region-beginning|end), not mark function (C code and simpler).
;; 2013/07/11 dadams
;;     bmkp-url-target-set: Use let* with backquote lambda instead of lexical-let*.
;; 2013/07/02 dadams
;;     bmkp-snippet-bookmark-p: Typo: bmkp-snippet-to-kill-ring -> bmkp-jump-snippet.
;;     bmkp-bookmark-description: Include snippet text in bookmark description (help).
;; 2013/07/01 dadams
;;     bookmark-make-record-default: Fixed typo for end-position (listify).
;;     bmkp-set-snippet-bookmark: Prefix arg now prompts for bookmark name.
;; 2013/06/30 dadams
;;     Added: bmkp-set-snippet-bookmark, bmkp-snippet-to-kill-ring, bmkp-jump-snippet,
;;            bmkp-snippet-alist-only, bmkp-snippet-bookmark-p, bmkp-snippet-history.
;;     bmkp-autotemp-bookmark-predicates, bmkp-types-alist, bmkp-bookmark-type,
;;       bmkp-bookmark-description:
;;         Cover snippet bookmarks too.
;;     bookmark-make-record-default:
;;       Added optional arg NO-REGION.  If non-nil then do not include end-position.
;;       Set NO-CONTEXT to nil for Emacs < 24.  Do not calculate FCS, RCS, FCRS, ECRS if NO-CONTEXT.
;;     bmkp-make-(gnus|sequence|desktop|bookmark-file|variable-list)-record:
;;       Pass NO-REGION to bookmark-make-record-default.
;; 2013/06/29 dadams
;;     Added: bmkp-read-regexp, bmkp-find-tag-default-as-regexp.
;;     Use bmkp-read-regexp, not read-string, everywhere for reading a regexp.
;;     bmkp-bookmark-description: Ensure FILE is non-nil before using it.
;; 2013/06/10 dadams
;;     bmkp-set-sequence-bookmark: Typo - bookmark-get-bookmarkp -> bookmark-get-bookmark.
;; 2013/06/02 dadams
;;     bmkp-set-sequence-bookmark: Forgot to bind FUN.  Thx to Michael Heerdegen.
;; 2013/05/31 dadams
;;     bmkp-save-menu-list-state: Display warning, do not raise error, if write-file fails.
;;     bookmark-write-file: Use display-warning, if fboundp.
;; 2013/05/28 dadams
;;     Renamed: bmkp-edit-bookmark-name-and-file to bmkp-edit-bookmark-name-and-location.
;;     bmkp-edit-bookmark-name-and-location: Handle location property, urls.
;;     bmkp-jump-w3m-new-session, bmkp-jump-w3m-only-one-tab: Use location property, not filename.
;;     Thx to Michael Heerdegen.
;; 2013/05/15 dadams
;;     bmkp-*-alist-only: Make sure we call bookmark-maybe-load-default-file.
;;     Moved bmkp-string-match-p to bookmark+-bmu.el.
;;     Use bmkp-string-match-p instead of string-match wherever appropriate.
;; 2013/05/12 dadams
;;     Added: bmkp-write-bookmark-file-hook.
;;     bookmark-write-file: Run bmkp-bookmark-write-file-hook functions after writing.
;; 2013/04/19 dadams
;;     bookmark-exit-hook-internal: Removed test for non-empty bookmark-alist (Emacs bug #13972).
;; 2013/04/15 dadams
;;     bmkp-set-sequence-bookmark: Corrected case of adding one sequence to another.
;;     bookmark-write-file: Corrected write-out of sequence bookmarks.
;;     bookmark-alist-from-buffer: Better error message if read error.
;; 2013/04/14 dadams
;;     Added: bmkp-wrap-bookmark-with-last-kbd-macro, bmkp-dired-remember-*-marks.
;;     bookmark-write-file: If not saving propertized, remove text props for bmks in sequence bmk.
;;     bmkp-edit-bookmark-record-send:
;;       Raise error if bmkp-edit-bookmark-record-send was somehow reset to nil.
;;       Do not reset bmkp-edit-bookmark-orig-record if read error.
;;     bmkp-make-function-bookmark:
;;       Prefix arg means use last-kbd-macro instead of prompting for FUNCTION.
;;       Use read-from-whole-string, not read, to convert name to symbol.
;;       If FUNCTION is a function or vector, do not convert it.
;;     bmkp-bookmark-description: For sequence-p, remove properties from each bmk name in sequence.
;;     Define bmkp-bookmark-name-from-record (no longer a defalias) with an optional UNPROPERTIZE arg.
;;     bmkp-make-dired-record: Use bmkp-dired-remember-*-marks, not dired-remember-marks.
;;       FUNCTION can now be a vector (a keyboard macro).  Use read-from-whole-string, not read.
;;     bmkp-jump-function: If function property is a vector, invoke it as a keyboard macro.
;;     bmkp-set-sequence-bookmark:
;;       Prefix ARG now allows for replace, in addition to append and prepend.  No replace question.
;;       A BOOKMARK-NAMES item can now be a bookmark, a function, or keyboard macro - or its name.
;;       A BOOKMARK-NAMES item that is itself a sequence has its bookmarks spliced in.
;;       Use lax as value of NAMES-ONLY-P to bmkp-completing-read-bookmarks.
;; 2013/04/12 dadams
;;     Added: bmkp-sequence-alist-only.
;;     bmkp-set-sequence-bookmark: Added prefix arg PREPENDP.  Use bmkp-completing-read-lax.
;;     Use \\<bmkp-edit-bookmark-record-mode-map> in doc strings with *-record-send.
;;     bookmark-get-bookmark: A cons must also have a string car, to tell a bmk from a list of bmks.
;;     bmkp-make-function-bookmark: Use bmkp-completing-read-lax for BOOKMARK-NAME.
;; 2013/04/10 dadams
;;     Added: bmkp-set-sequence-bookmark, bmkp-make-sequence-record, bmkp-completing-read-bookmarks.
;;     bmkp-completing-read-1:
;;       Do not put DEFAULT in PROMPT if DEFAULT is "".  Removed useless let-binding of DEFAULT.
;;       Removed unnecessary final massaging of STR.
;;     bookmark-completing-read: Mention in doc string that nil DEFAULT means return "".
;; 2013/03/29 dadams
;;     bmkp-toggle-saving-bookmark-file: If neither is nil, set *-last-* to nil before toggling.
;; 2013/03/17 dadams
;;     bmkp-bmenu-list-1: Do not toggle filenames unless bookmark-alist is defined (Emacs bug #13972).
;; 2013/01/07 dadams
;;     bmkp-remove-all-tags, bmkp(-autofile)-(add|remove)-tags, bmkp-set-tag-value,
;;       bmkp-paste-(add|replace)-tags, bmkp-(url|file)-target-set, bmkp-autofile-set:
;;         Added missing NO-UPDATE-P arg for interactive spec.
;;     bmkp-remove-all-tags: Moveed msg to the end.
;;     bmkp-paste-replace-tags: Added sleep-for after first msg.
;; 2012/11/13 dadams
;;     bmkp-sorting-description: Fixed 1st case: use ORDER only if bmkp-sort-comparer is also non-nil.
;; 2012/11/11 dadams
;;     Added: bmkp-sorting-description (factored out from bmkp-msg-about-sort-order).
;;     bmkp-msg-about-sort-order: Use bmkp-sorting-description.
;;     bmkp-current-sort-order: Return nil if bmkp-sort-comparer is not in bmkp-sort-orders-alist.
;; 2012/11/09 dadams
;;     Added: bmkp-autofile-filecache.
;;     Added defadvice for file-cache-add-file.
;;     bookmark-store, bmkp-url-target-set: Added optional arg NO-UPDATE-P.
;;     bookmark-set, bmkp-make-function-bookmark, bmkp-url-target-set, bmkp-file-target-set:
;;       Adjusted calls to bookmark-store to accommodate NO-UPDATE-P arg.
;;     bmkp-make-record-for-target-file:
;;       Add CREATED property for all bookmark types.  Factor out the common stuff.
;;       Remove any text properties from FILE arg before using it.
;; 2012/10/09 dadams
;;     Made all autoload cookies explicitly load bookmark+.el(c).  Should help ELPA (e.g. MELPA).
;; 2012/10/01 dadams
;;     bmkp-thing-at-point: Updated per icicle-thing-at-point.  Thx to Joe Bloggs.
;; 2012/09/29 dadams
;;     Added redefinition of bookmark-version-control.
;;     bookmark--jump-via:
;;       When bmkp-use-w32-browser-p, just handle, do after-jump hook & jump-fn, and show annotation.
;;     bookmark-handle-bookmark:
;;       When bmkp-use-w32-browser-p, just invoke w32-browser and throw to bookmark--jump-via.
;;     bookmark-write-file: Use find-file-noselect.
;;     bmkp-save-menu-list-state:
;;       Bind print-circle, version-control, require-final-new-line.  Use find-file-noselect.
;;       Copy shared bookmark lists and single strings, to avoid circular refs.
;;       Raise error, not just msg, if file-error.
;;     bookmark-write-file: Bind require-final-newline.
;; 2012/09/26 dadams
;;     bmkp-save-menu-list-state: Use write-file, not write-region, so backups are made.
;; 2012/09/24 dadams
;;     bookmark-write-file: Use write-file, not write-region, so backups are made.  Emacs bug #12507.
;; 2012/09/22 dadams
;;     bookmark-set: Updated handling of bmkp-auto-light-when-set for (non-)autonamed-in-buffer.
;;     bmkp-autonamed-this-buffer-bookmark-p: Require that the buffer name part match also.
;;     bmkp-autonamed-this-buffer-alist-only: Corrected to use bmkp-autonamed-this-buffer-bookmark-p.
;; 2012/09/11 dadams
;;     bmkp-set-autonamed-bookmark-at-line: Use prefix arg for line no.  Use line-beginning-position.
;; 2012/09/06 dadams
;;     Added: bmkp-string-match-p.
;; 2012/08/28 dadams
;;     bookmark-send-edited-annotation: Record an empty annotation as nil, not "".
;; 2012/08/21 dadams
;;     Call tap-put-thing-at-point-props after load thingatpt+.el.
;; 2012/08/18 dadams
;;     Invoke tap-define-aliases-wo-prefix if thingatpt+.el is loaded.
;;     Added: bmkp-thing-at-point.
;;     thing-at-point -> bmkp-thing-at-point, everywhere.
;; 2012/08/10 dadams
;;     Info-bookmark-make-record: Updated wrt Emacs 24.
;;     Renamed: old-bookmark-insert to bmkp-ORIG-bookmark-insert.
;; 2012/07/04 dadams
;;     bmkp-create-variable-list-bookmark: Removed INTERACTIVEP arg to bookmark-set.
;;     #'(lambda...) -> (lambda...).
;; 2012/07/02 dadams
;;     bmkp-default-handler-for-file:
;;       Reverted 2012/05/04 change to use lexical-let.  Byte code in saved bookmark was problematic.
;; 2012/06/26 dadams
;;     Wrapped require of bookmark+-mac.el in eval-when-compile.
;; 2012/06/21 dadams
;;     Try to load-library bookmark+-mac.  Require it only if cannot load-library.
;; 2012/06/12 dadams
;;     bmkp-new-bookmark-default-names: 1. Test for DEFS at end is listp, not consp. 2. Return FNS.
;;     bmkp-completing-read-1: Removed empty-input loop - caller must provide a default or handle "".
;; 2012/06/1 dadams
;;     bookmark-make-record: Replace an empty bookmark name with <EMPTY NAME>.
;;     bookmark-set, bmkp-completing-read-1: Require user to input a non-empty bookmark name.
;;     bmkp-bookmark-name-member: If NAME is null, just use member.  Skip any in NAMES that is null.
;; 2012/05/16 dadams
;;     Added: bmkp-string-less-case-fold-p.
;;     bmkp-list-all-tags: List tags alphabetically.  Thx to Anders Johansson for the suggestion.
;; 2012/05/05 dadams
;;     bookmark-store, bmkp-make-function-bookmark, bmkp-unomit-all, bmkp-url-target-set:
;;       Added optional arg NO-MSG-P.
;;     bookmark-store, bookmark-set, bmkp-record-visit, bmkp-make-function-bookmark,
;;       bmkp-current-bookmark-list-state, bmkp-unomit-all, bmkp-url-target-set, bmkp-file-target-set,
;;       bmkp-replace-existing-bookmark:
;;         Pass NO-MSG-P to *-refresh/rebuild-menu-list, *-surreptitiously-rebuild-list, *-store.
;; 2012/05/04 dadams
;;     bmkp-remove-tags, bmkp-all-tags(-regexp)-alist-only
;;       bmkp(-(auto)file(-this-dir))(-(all|some)-tags)(-regexp)-alist-only,
;;       bmkp-specific-(buffers|files)-alist-only, bmkp-sort-omit, bmkp-url-target-set,
;;       bmkp-autofile-remove-tags. bmkp-default-handler-for-file, bmkp-set-bookmark-file-bookmark,
;;       bmkp-set-desktop-bookmark, bmkp-set-variable-list-bookmark,
;;       bmkp-create-variable-list-bookmark, bmkp-jump-dired,
;;       bmkp-find-file-(all|some)-tags(-regexp)(-other-window):
;;         Use lexical-let(*), to get closures for free vars in lambdas.
;;     bmkp-regexp-filtered-(file-name|tags)-alist-only: Moved let inside lambda.
;;     bmkp-make-dired-record: Use car instead of (lambda (x) (car x)).
;; 2012/05/01 dadams
;;     Added: bmkp-tagged-bookmark-p (alias), bmkp-tagged-cp.
;;     bmkp-(add|remove)-tags: Return negative nb-* if changed from (un)tagged to not (un)tagged.
;;     bmkp-paste-replace-tags: Do not call bmkp-remove-all-tags unless there are tags to remove.
;; 2012/04/27 dadams
;;     bmkp-edit-(tags|bookmark-record): Use bmkp-with-output-to-plain-temp-buffer.
;; 2012/04/18 dadams
;;     Do not try to define bmkp-global-auto-idle-bookmark-mode for Emacs 21 (no define-globalized*).
;; 2012/04/16 dadams
;;     bmkp-bookmark-description: List tags as strings on separate lines.
;;                                Add newline after annotation.
;; 2012/04/13 dadams
;;     Added: bmkp-(flagged|modified)-bookmark-p, bmkp-(flagged|modified)-cp.
;;     bookmark-store, bookmark-set-name, bookmark-prop-set, bmkp-edit-bookmark-record(s)-send,
;;       bmkp-replace-existing-bookmark, bmkp-delete-bookmarks:
;;         Use (equivalent of) eq version of add-to-list.
;; 2012/04/10 dadams
;;     Added: bmkp-count-multi-mods-as-one-flag.
;;     bmkp-edit-bookmark-records-send, bmkp-set-tag-value-for-bookmarks, bmkp-remove-tags-from-all,
;;       bmkp-rename-tag, bmkp-purge-notags-autofiles,
;;       bmkp-delete(-all)-autonamed(-for)(-this-buffer)(-no-confirm), bmkp-delete-bookmarks,
;;       bmkp-delete(-all)-temporary(-bookmarks|-no-confirm):
;;         Corrected bookmark-save to bookmark-save-flag in bindings to nil.
;;         Use bmkp-count-multi-mods-as-one-flag for the binding.
;; 2012/04/09 dadams
;;     bookmark-relocate, bmkp-edit-bookmark-records-send, bmkp-set-tag-value, bmkp-file-target-set,
;;       bmkp-autofile-set:
;;         Added optional arg NO-UPDATE-P.  Use it to inhibit display refreshing.
;;     bmkp-edit-bookmark-records-send, bmkp-set-tag-value-for-bookmarks, bmkp-remove-tags-from-all,
;;       bmkp-rename-tag, bmkp-purge-notags-autofiles, delete-all-autonamed-for-this-buffer
;;       bmkp-delete(-all)-temporary-(bookmarks|no-confirm), bmkp-delete-bookmarks,
;;       bmkp-delete-autonamed(-this-buffer)(-no-confirm):
;;         Bind bookmark-save to nil around iteration, to inhibit saving until finished.
;;     bmkp-(add|remove)(-all)-tags, bmkp-paste-(add|replace)-tags, bmkp-autofile-(add|remove)-tags:
;;       Swapped order of args MSGP and NO-UPDATE-P (put MSGP last).
;;     bmkp-(add|remove)(-all)-tags, bmkp-autofile-(add|remove)-tags:
;;       Use NO-UPDATE-P also to inhibit display refreshing.
;;     bmkp-remove-tags-from-all: Pass non-nil NO-UPDATE-P arg to bmkp-remove-tags.
;; 2012/04/07 dadams
;;     Added: bmkp-new-bookmark-default-names (option & function).
;;     Redefine bookmark-make-record (for all Emacs versions) to use bmkp-new-bookmark-default-names.
;;     bookmark-set: Use bmkp-new-bookmark-default-names (multiple defaults).
;;                   Moved the region-text default value stuff to fn bmkp-new-bookmark-default-names.
;;     bmkp-completing-read-1: Handle a cons DEFAULT.
;;     Added soft require of thingatpt+.el.
;; 2012/04/06 dadams
;;     Added: bmkp-auto-idle-bookmark-min-distance, bmkp-not-near-other-auto-idle-bmks,
;;            bmkp-auto-idle-bookmarks.
;;     bmkp-autotemp-bookmark-predicates:
;;       Changed default value to include bmkp-autonamed-bookmark(-this-buffer)-p.
;;     bookmark-store: Add the bookmark to bmkp-auto-idle-bookmarks (if appropriate).
;;     bookmark-delete: Remove the bookmark from bmkp-auto-idle-bookmarks.
;;     bmkp-auto-idle-bookmark-mode:
;;       Bind bmkp-setting-auto-idle-bmk-p.  Do nothing if bmkp-not-near-other-auto-idle-bmks says so.
;; 2012/04/05 dadams
;;     Added (Emacs 21+): bmkp-global-auto-idle-bookmark-mode, bmkp-turn-on-auto-idle-bookmark-mode.
;;     bmkp-auto-idle-bookmark-mode (Emacs 21+):
;;       Made it local:
;;         Removed keyword :global, added keyword :require.
;;         Timer function does nothing if the mode is not enabled (i.e., for the current buffer).
;;     bmkp-auto-idle-bookmark-mode (Emacs 20):
;;       Changed interactive spec to handle toggle symbol.
;;       Timer function does nothing if the mode is not enabled (for the current buffer, if local).
;;       Change message to mention buffer when the mode is local.
;;     Removed: bmkp-auto-idle-bookmark-mode-hook.
;;     Added autoload cookie for Emacs 20 defcustom for bmkp-auto-idle-bookmark-mode.
;;     bmkp-auto-idle-bookmark-mode-timer: Use nil as default value.
;;     bmkp-auto-idle-bookmark-mode: If timer is non-nil, set it to nil (and cancel it).
;; 2012/04/04 dadams
;;     Added: bmkp-auto-idle-bookmark-mode(-delay|-hook|-lighter|-set-function),
;;            bmkp-temporary-bookmarking-mode-lighter, bmkp-auto-idle-bookmark-mode-timer.
;;     bmkp-temporary-bookmarking-mode: Added lighter.
;;     bookmark-set: Pass INTERACTIVEP arg, not constant MSGP, to bmkp-light-(bookmarks|this-buffer).
;; 2012/04/03 dadams
;;     Moved to bookmark+-bmu.el: bmkp-face-prop.
;; 2012/04/02 dadams
;;     bmkp-toggle-autonamed-bookmark-set/delete, bmkp-set-autonamed-bookmark(-at-line),
;;       bmkp-delete-bookmarks:
;;         Made POSITION, NUMBER, ALLP optional.
;; 2012/03/18 dadams
;;     Added: bmkp-modified-bookmarks, redefinition of bookmark-set-name.
;;     bookmark-store, bookmark-set-name, bookmark-prop-set, bmkp-replace-existing-bookmark:
;;       Add the bookmark to bmkp-modified-bookmarks.
;;     bookmark-rename: Call bmkp-rename-for-marked-and-omitted-lists _after_ set new name w/ prop.
;;     bookmark-save: Reset bmkp-modified-bookmarks.  Call bmkp-refresh/rebuild-menu-list.
;;     bmkp-rename-for-marked-and-omitted-lists: Fixed typo: marked -> omitted.
;;     bmkp-edit-bookmark-name-and-file:
;;       Save each of bmk name and file name only if changed (bug fix).  Provide default file name.
;;       If no automatic save, and modifications, ask user whether to save.
;;     bmkp-edit-bookmark-records-send:
;;       Add updated bookmarks to bmkp-modified-bookmarks.
;;       Merge sanity-check dolist with main dolist.
;;       Set bmkp-bmenu-marked-bookmarks to names in bmkp-modified-bookmarks, not in edited-bookmarks.
;;     bmkp-edit-bookmark-record: Use (shallow) copy of bmkp-edit-bookmark-orig-record, not original.
;;     bmkp-edit-bookmark-record-send: Add updated bookmark to bmkp-modified-bookmarks.
;;     bmkp-record-visit: Let-bind bmkp-modified-bookmarks to itself, so will be restored.
;;     bmkp-refresh-menu-list: Pass no FILTEREDP if no current filter (start anew).
;;     bmkp-bookmark-name-member: If a name in NAMES is unpropertized, don't try to match property.
;;     bmkp-replace-existing-bookmark: For propertize bookmark-current-bookmark with bmkp-full-record.
;; 2012/03/13 dadams
;;     bmkp-incremental-filter-delay:
;;       Use bookmark-search-delay as default value, if available.  Else use 0.2 (not 0.6).
;; 2012/03/11 dadams
;;     bmkp-revert-bookmark-file: Added p to interactive spec (forgot).
;; 2012/03/06 dadams
;;     Added: bmkp-revert-bookmark-file.
;;     bookmark-load: If bookmark-file buffer already existed, do not kill it after loading.
;; 2012/03/04 dadams
;;     Added: bmkp-refresh/rebuild-menu-list.
;;     bookmark-store, bookmark-send-edited-annotation, bookmark-delete,
;;       bmkp-edit-bookmark-record(s)-send, bmkp-edit-tags-send, bmkp-update-autonamed-bookmark,
;;       bmkp-remove(-all)-tags, bmkp-add-tags, bmkp-file-target-set, bmkp-refresh/rebuild-menu-list:
;;         Use bmkp-refresh/rebuild-menu-list.
;;     bookmark-load:
;;       Use bmkp-refresh/rebuild-menu-list only if interactive.  Do not call *-surreptitiously-*.
;;     bmkp-edit-bookmark-record(s)-send: Added optional arg MSGP.  Raise read error if batch.
;;     bmkp-record-visit:
;;       Added optional arg BATCHP.  Do not bookmark-bmenu-surreptitiously-rebuild-list if BATCHP.
;;     bmkp-edit-tags-send: Added optional arg BATCHP, and pass it to bmkp-record-visit.
;;     bmkp-refresh-menu-list: Use bmkp-bookmark-name-from-record only when BOOKMARK is non-nil.
;;     bmkp-paste-replace-tags, bmkp-(compilation|occur)-target-set-all:
;;       Raise error with OK message if user cancels.
;;     bmkp-purge-notags-autofiles, bmkp-delete-all-temporary-bookmarks: Added optional arg MSGP.
;;     bmkp-purge-notags-autofiles, bmkp-delete-all-temporary-bookmarks,
;;       bmkp-delete-temporary-no-confirm:
;;         Call bmkp-refresh/rebuild-menu-list after the dolist.  Inhibit refresh for bookmark-delete.
;;     bmkp-jump-bookmark-file: Removed reference to current-prefix-arg: prompt only if SWITCHP.
;;     bmkp-delete-all-autonamed-for-this-buffer:
;;       Added optional arg MSGP.  Prompt for confirmation only if MSGP.
;;     bmkp-delete-autonamed-this-buffer-no-confirm:
;;       Added optional arg NO-REFRESH-P.  Inhibit refresh for bookmark-delete.
;;       Unless  NO-REFRESH-P, call bmkp-refresh/rebuild-menu-list after the dolist.
;;     bmkp-delete-autonamed-no-confirm:
;;       Call bmkp-delete-autonamed-this-buffer-no-confirm with NO-REFRESH-P.
;;       Call bmkp-refresh/rebuild-menu-list after the dolist.
;;     bmkp-delete-bookmarks:
;;       Added optional arg MSGP.  Prompt for confirmation only if MSGP.
;;       Raise error with OK message if user cancels.
;;       Call bmkp-refresh/rebuild-menu-list after the dolist.  Inhibit refresh for bookmark-delete.
;;       Use bmkp-this-buffer-alist-only, not bookmark-alist, for selecting bookmarks.
;;       Use `...', etc. when echoing deleted bookmarks.
;; 2012/03/02 dadams
;;     bookmark-load:
;;       Changed last arg from NO-MSG-P to BATCHP.  If non-nil, act with no prompt, saving or not.
;;       If nil, prompt user whether to save before loading.  If user quits with C-g, do not load.
;;     bookmark-maybe-load-default-file: Pass symbol nosave, not t, as last arg to bookmark-load.
;;     bmkp-switch-bookmark-file-create: Last arg is now the complement: BATCHP, not INTERACTIVEP.
;;     bmkp-temporary-bookmarking-mode: Pass nosave as last arg to bookmark-load, since do save here.
;;     bmkp-default-handlers-for-file-types: Added eval-when-compile to require cl.el for Emacs 20.
;;     bmkp-maybe-save-bookmarks: Added optional arg SAME-COUNT-P.
;;     bmkp-record-visit: Pass non-nil arg to bmkp-maybe-save-bookmarks to prevent changing mod count.
;;     bookmark-store: Call bmkp-refresh-menu-list if Bookmark List is displayed.
;;     bmkp-toggle-saving-bookmark-file: Added optional arg MSGP - show message only if non-nil.
;;     bmkp-find-file(-other-window): Added missing FIL arg for error format string.
;;     bmkp-temporary-bookmarking-mode: Pass a MSGP arg to bmkp-toggle-saving-bookmark-file.
;; 2012/02/29 dadams
;;     bmkp-completing-read-lax: Bind & restore C-M-w, C-M-u, SPC, and ? (so can insert SPC, ? etc.).
;; 2012/02/28 dadams
;;     bmkp-file-target-set: Call bmkp-refresh-menu-list if Bookmark List is displayed.
;;     Renamed option bmkp-default-handler-associations to bmkp-default-handlers-for-file-types.
;;       bmkp-default-handler-associations is NOW OBSOLETE - RENAME IT IF YOU HAVE CUSTOMIZED IT.
;;     bmkp-same-file-p: Take advantage of Emacs 24 function, file-equal-p.  Thx to Michael Albinus.
;;     bmkp-find-file(-other-window):
;;       Added optional args CREATE-AUTOFILE-P & MSGP (new arg order).  Prefix arg creates bookmark.
;;       Use bmkp-default-handlers-for-file-types even for files not bookmarked.
;; 2012/02/26 dadams
;;     Added: bmkp-(autofile|autonamed)-history, bmkp-autofile-(all|some)-tags(-regexp)-alist-only,
;;            bmkp-autofile(-(all|some)-tags(-regexp))-jump(-other-window).
;;     bmkp-types-alist: Added entries for (autofile|autonamed).
;;     Everywhere that read-file-name is used:
;;       Bind icicle-unpropertize-completion-result-flag to t, for read-file-name.
;;     No longer alias bmkp-autofile*-jump to bmkp-find-file.  The *-autofile-*jump commands use
;;       bmkp-read-bookmark-for-type and bmkp-jump-1, not read-file-name and find-file.
;;     bmkp-find-file(-other-window):
;;       Added optional args FILE MUST-EXIST-P.
;;       Use read-file-name and either bookmark-jump or find-file, not just find-file (and no PRED).
;;     bmkp-find-file-*-tags(-regexp)(-other-window):
;;       Added optional FILE arg.
;;       Use bookmark-jump, not find-file - so only autofiles with the tags are candidates.
;;       Bind icicle-must-pass-after-match-predicate.  Use PRED for read-file-name only if no Icicles.
;;     The new bmkp-find-file* commands are bound to ... C-f, not ... a.
;;     bmkp-default-handler-associations: Correct docstring: double backslashes.
;; 2012/02/21 dadams
;;     bmkp-jump-to-type(-other-window): Corrected ALIST: If no HISTORY do not call *-alist-only.
;; 2012/02/20 dadams
;;     bookmark-handle-bookmark: Handle, in priority, new property file-handler.
;;     bookmark-default-handler: Handle new property file-handler.
;;     bmkp-make-record-for-target-file:
;;       Use new property file-handler, not handler, for default handler.
;;       Use file-handler with play-sound-file, not handler with bmkp-sound-jump (deprecated).
;;     bmkp-default-handler-for-file: Return function bmkp-user, not a lambda that applies it to file.
;;     bmkp-handler-pred:
;;       Return t if TYPE is handler or file-handler.  Do not match a lambda that applies the handler.
;;     bmkp-default-handler-associations, bookmark-alist, bmkp-jump-to-type:
;;       Updated doc string to reflect new implementation of file handlers using prop file-handler.
;; 2012/02/19 dadams
;;     Added: bmkp-handler-pred, bmkp-temporary-history, bmkp-w32-browser-jump.
;;     bmkp-types-alist: Added bmkp-temporary-history.
;;     bmkp-read-bookmark-for-type: Prepend a space before "bookmark" in prompt.
;;     bmkp-jump-to-type:
;;       Use lax completion.
;;       When call bmkp-read-bookmark-for-type:
;;        Do not append a space to TYPE name passed.
;;        Pass a predicate arg returned by bmkp-handler-pred when TYPE is not a known type.
;;     bmkp-*-jump(-other-window): Remove space after TYPE name passed to bmkp-read-bookmark-for-type.
;;     bmkp-(specific-(buffers|files)|temporary)-jump(-other-window):
;;       Pass specific HIST arg to bmkp-read-bookmark-for-type.
;; 2012/02/16 dadams
;;     Updated for Emacs 24+:
;;       bookmark-set: Do not set bookmark-(yank-point|current-buffer) if set.
;;       bmkp-make-gnus-record: Be able to bookmark from article buffer, as well as summary buffer.
;;       bmkp-jump-gnus: Go to article buffer if location field says to.
;;     Use bmkp-make-gnus-record (not gnus-summary-bookmark-make-record) for Emacs 24+ also.
;; 2012/02/14 dadams
;;     bmkp-set-desktop-bookmark: Provide default for read-file-name.  Thx to Markus Grunwald.
;;                                Provide all bookmarked desktop files as Icicles proxy candidates.
;; 2012/02/08 dadams
;;     bmkp-autofile-set: Use MSGP also for the case where the bookmark already exists.
;;     bmkp-remove-dups: Redefined to use a hash table.
;; 2012/02/07 dadams
;;     bmkp-same-file-p: Test compare-strings result using t, not non-nil.  Thx to Michael Heerdegen.
;; 2012/02/04 dadams
;;     Added: bmkp-tags-for-completion, bmkp-tags-in-bookmark-file.
;;     Use bmkp-tags-for-completion for tags completing everywhere - updated doc strings.
;;     bmkp-list-all-tags: Added args current-only-p and (optional) msgp.
;;                         Different prefix arg values for different behaviors.
;;     bmkp-tags-list: Added optional arg current-only-p.  Use bmkp-tags-for-completion by default.
;; 2012/01/20 dadams
;;     bmkp(-autofile)-(add|remove)-tags(-from-all), bmkp-find-file-(all|some)-tags(-other-window),
;;       bmkp(-file(-this-dir))-(all|some)-tags-jump(-other-window):
;;         Let user use a prefix arg to refresh tags list.  Add this info to doc string.
;; 2012/01/14 dadams
;;     Corrected bmkp-same-file-p: call to compare-strings.
;; 2012/01/13 dadams
;;     bmkp-same-file-p: Handle case-sensitivity for local files, at least (not yet done for remote).
;; 2012/01/08 dadams
;;     Added: bmkp-autonamed-this-buffer-bookmark-p.
;;     bmkp-autotemp-bookmark-predicates: Updated doc string for *-autonamed-this-buffer-bookmark-p.
;;     bmkp-autonamed-bookmark-for-buffer-p: Updated doc string to mention it just checks the name.
;;     bmkp-autonamed-this-buffer-alist-only:
;;       Use bmkp-this-buffer-p, not bmkp-autonamed-bookmark-for-buffer-p.
;; 2011/12/30 dadams
;;     Renamed bmkp-edit-bookmark to bmkp-edit-bookmark-name-and-file.
;;     Added aliases: bmkp-bookmark-(data|name)-from-record.
;;     Added: bmkp-get-bookmark-in-alist, bmkp-bookmark-record-from-name,
;;            bmkp-edit-bookmark-records-(number|send|mode(-map)),
;;            bookmark-alist-from-buffer (redefinition), bmkp-edit-bookmark-orig-record,
;;            bmkp-rename-for-marked-and-omitted-lists.
;;     Use new names (aliases) bmkp-bookmark-(data|name)-from-record.
;;     bookmark-get-bookmark-record: Use redefinition for all Emacs versions (updated doc string).
;;     bookmark-get-bookmark: Use bmkp-bookmark-record-from-name, with no MEMP check.
;;     bookmark-store: Use bmkp-get-bookmark-in-alist to test whether bookmark exists.
;;                     Set the bookmark name also, not just the data, for an existing bookmark.
;;                     Unconditionally always put full bookmark on name as property bmkp-full-record.
;;     bookmark-send-edited-annotation, bookmark-rename:
;;       Do bookmark-bmenu-surreptitiously-rebuild-list only if no bmenu display window.
;;     bookmark-rename:
;;       Return OLD if if BATCHP is non-nil and NEW is nil.  Do not prompt for name if BATCHP.
;;       Use bmkp-rename-for-marked-and-omitted-lists (rename in those lists too).
;;       Unconditionally always put full bookmark on name as property bmkp-full-record.
;;       Use bmkp-bookmark-record-from-name, not bookmark-get-bookmark, to get full record.
;;     bookmark-delete, bmkp-edit-bookmark-name-and-file, bmkp-edit-bookmark-record,
;;       bmkp-edit-tags(-send), bmkp-toggle-autonamed-bookmark-set/delete:
;;         Use bmkp-get-bookmark-in-alist, not bookmark-get-bookmark.
;;     bookmark-load: Call bmkp-refresh-menu-list only if display is visible, and with NO-MSG-P arg.
;;     bookmark-show-annotation: Do not raise error if not a valid bookmark.
;;     bmkp-edit-bookmark-record: Record bmkp-edit-bookmark-orig-record.  Strip properties from name.
;;                                Updated edit-buffer text.
;;     bmkp-edit-bookmark-record-send: Rewrote similarly to bmkp-edit-bookmark-records-send.  No args.
;;     bmkp-default-bookmark-name:
;;       Use bmkp-bookmark-record-from-name, not bookmark-get-bookmark, requiring membership in ALIST.
;;     bmkp-save-menu-list-state, bmkp-get-tag-value: Added optional arg MSGP, and status messages.
;;     bmkp-make-function-bookmark: Use bmkp-bookmark-record-from-name, not bookmark-get-bookmark.
;;     bmkp-autonamed-bookmark(-for-buffer)-p:
;;       Use bmkp-bookmark-name-from-record, not bookmark-get-bookmark and bookmark-name-from-*.
;;     bmkp-get-tag-value, bmkp-has-tag-p: Removed unused arg MSGP.
;;     bmkp-delete-bookmark-name-from-list:
;;       For unpropertized DELNAME, Set BNAMES to result of delete call.
;;       For propertized DELNAME, delete also unpropertized matches.
;;     bmkp-(compilation|occur)-target-set-all: Do not prompt or show message unless MSGP.
;;     bmkp-describe-bookmark-internals: Use a copy of the bookmark.  Strip properties from name.
;;     bmkp-set-autonamed-regexp-buffer: Pass MSGP, do not hardcode.n
;;     Doc string improvements.
;; 2011/12/24 dadams
;;     bmkp-refresh-menu-list: Added progress message.
;;     bmkp-jump-bookmark-file: Pass NO-MSG-P arg to bookmark-load.
;; 2011/12/21 dadams
;;     Added: bmkp-orphaned(-local|-remote)-file-(alist-only|bookmark-p),
;;            bmkp-dired-wildcards-bookmark-p.
;;     bookmark-load:
;;       Call (bmkp-refresh-menu-list (bookmark-bmenu-bookmark)), not (bmkp-bmenu-refresh-menu-list).
;; 2011/12/19 dadams
;;     bookmark-set, bmkp-handle-region-default:  Use line-end-position, not end-of-line + point.
;; 2011/12/17 dadams
;;     bmkp-remote-file-p:
;;       If file-remote-p not available, match /...: (same as ffap-ftp-regexp).  Return match.
;;     bmkp-same-file-p: Redefined to use new bmkp-remote-file-p.  Thx to M. Heerdegen & M. Albinus.
;; 2011/12/15 dadams
;;     bmkp-dired-this-dir-bookmark-p: Use file-name-directory, in case filename has wildcards.
;; 2011/12/13 dadams
;;     bmkp-handle-region-default: Limit buffer-substring-no-properties positions to point-min/max.
;; 2011/12/06 dadams
;;     bmkp-last-as-first-bookmark-file:
;;       Removed autoload cookie to avoid void-variable error for bookmark-default-file.
;;     bmkp-edit-bookmark, bookmark-rename: Use bmkp-completing-read-lax, not read-from-minibuffer.
;; 2011/12/05 dadams
;;     bmkp-this-buffer-p:
;;       Do not use buffer-file-name (for Dired).  Wrap bookmark-buffer-file-name with condition-case.
;;     bookmark-save: Swap write order, so last message is about the bookmark file, not customize.
;; 2011/12/03 dadams
;;     Renamed: bmkp-use-bookmark-file-create to bmkp-switch-bookmark-file-create.
;;     Added: bmkp-last-as-first-bookmark-file, bookmark-maybe-load-default-file (redefinition),
;;            bookmarks-already-loaded (redefinition), bmkp-default-bookmark-file.
;;     bookmark-save: Update and save bmkp-last-as-first-bookmark-file.
;;     bookmark-load: New default for reading file name, and require an existing file (match).
;;                    Update and save bmkp-last-as-first-bookmark-file.  Update bmkp-sorted-alist.
;;     bmkp-switch-bookmark-file (no longer used): New default for reading file name.
;;     bmkp-switch-bookmark-file-create: Added optional arg INTERACTIVEP.  New default for reading
;;       file name.  Use bookmark-load, not bmkp-switch-bookmark-file.  Require confirmation only for
;;       new, empty file.  Added final message.
;;     bmkp-switch-to-last-bookmark-file: Use bmkp-last-as-first-bookmark-file as first fallback.
;;     bmkp-set-bookmark-file-bookmark: Use bmkp-read-bookmark-file-name, not read-file-name.
;;                                      New default for reading file name.
;;     bmkp-temporary-bookmarking-mode: Use bookmark-load, not bmkp-switch-bookmark-file.
;;     Removed: bookmark-maybe-message.  Use only message now, not bookmark-maybe-message.
;;     bmkp-autofile-set: For Emacs 23.3+, provide multiple defaults for file name.
;; 2011/11/30 dadams
;;     bmkp-same-file-p: Avoid having Tramp prompt for passwords, when possible.  Thx to M. Heerdegen.
;;     bmkp-toggle-autotemp-on-set: Removed ARG (copy/paste typos).
;; 2011/11/28 dadams
;;     bmkp-set-bookmark-file-bookmark: Prompt user for bookmark name here, to make clear what it is.
;; 2011/11/27 dadams
;;     bookmark-write-file: If write error, do not overwrite message.  And show error msg for 4 sec.
;; 2011/11/18 dadams
;;     Renamed: bmkp-bookmark-image-bookmark-p to bmkp-image-bookmark-p.
;;     Added: bmkp-image-alist-only, bmkp-image-jump(-other-window), bmkp-image-history.
;;     bookmark-handle-bookmark: If bmk has handler but it's not a function, use default handler.
;;     bmkp-autotemp-bookmark-predicates: Update doc string to include bmkp-image-bookmark-p.
;;     bmkp-types-alist: Added entry for images.
;; 2011/11/15 dadams
;;     bookmark-relocate: Redefine without using old-*.  Update Dired location too.
;;     Added: bmkp-cycle-this-file(/buffer)(-other-window),
;;            bmkp-(next|previous)-bookmark-this-file(/buffer)(-repeat),
;;            bmkp-this-file(/buffer)-bmenu-list, bmkp-this-file/buffer-alist-only.
;;     Renamed bmkp-this-buffer-cycle-sort-comparer to bmkp-this-file/buffer-cycle-sort-comparer.
;;     bmkp-this-buffer-p: Return nil if bookmark has a file diff from buffer.
;;     bmkp-this-file-p:
;;       Ensure bmkp-file-bookmark-p and bookmark-buffer-file-name.  Use bmkp-same-file-p.
;; 2011/11/09 dadams
;;     bmkp-jump-dired, bmkp-jump-man: Added bmkp-select-buffer-other-window to other-window fns.
;; 2011/11/08 dadams
;;     bmkp-edit-bookmark: For new file name, use read-file-name, not read-from-minibuffer.
;; 2011/11/03 dadams
;;     Renamed: bmkp-autoname-bookmark to bmkp-autoname-bookmark-function-default.
;; 2011/11/01 dadams
;;     Added: bmkp-temporary-jump(-other-window).
;;     bmkp-bookmark-description: Title now indicates whether temporary.
;; 2011/10/31 dadams
;;     Added: bmkp-toggle-autotemp-on-set, bmkp-autotemp-all-when-set-p.
;;     bookmark-set: If bmkp-autotemp-all-when-set-p call bmkp-make-bookmark-temporary.
;; 2011/10/28 dadams
;;     Added: bmkp-delete-temporary-no-confirm.
;;     bmkp-delete-all-temporary-bookmarks: Rewrote (it was just a stub).
;;     bmkp-bmenu-menubar-menu:
;;       Added: bmkp-temporary-bookmarking-mode, bmkp-delete-all-temporary-bookmarks,
;;              bmkp-bmenu-toggle-marked-temporary/savable.
;;     bmkp-bmenu-show-menu: Added: bmkp-bmenu-show-only-temporary.
;;     bmkp-bmenu-mark-menu:
;;       Added: bmkp-bmenu-mark-temporary-bookmarks, bmkp-bmenu-mark-autonamed-bookmarks.
;;     bmkp-bmenu-mouse-3-menu: Added: bmkp-bmenu-toggle-temporary.
;;     bookmark-bmenu-mode: Updated doc string.
;; 2011/10/27 dadams
;;     Added: bmkp-autotemp-bookmark-predicates, bmkp-temporary-bookmarking-mode(-hook),
;;            bmkp-delete-all-temporary-bookmarks, bmkp-make-bookmark-(savable|temporary),
;;            bmkp-toggle-temporary-bookmark, bmkp-temporary-alist-only, bmkp-temporary-bookmark-p.
;;     bookmark-set: Make bookmark temporary, if bmkp-autotemp-bookmark-predicates says to.
;;     bookmark-write-file: Do not save temporary bookmarks (bmkp-temporary-bookmark-p).
;; 2011/10/25 dadams
;;     bmkp-empty-file: Added optional arg CONFIRMP.  By default, no confirmation if not interactive.
;; 2011/08/09 dadams
;;     Bind icicle-unpropertize-completion-result-flag to t for all calls to completing-read.
;; 2011/08/07 dadams
;;     Added: bmkp-guess-default-handler-for-file-flag, bmkp-file-bookmark-handlers.
;;     bmkp-file-bookmark-p: Use bmkp-file-bookmark-handlers, which means also image-bookmark-jump.
;;     bmkp-make-record-for-target-file (need to keep in sync with diredp-bookmark):
;;       Instead of image-bookmark-make-record, use explicit function that includes file and type.
;;     bmkp-default-handler-for-file:
;;       Use bmkp-guess-default only if bmkp-guess-default-handler-for-file-flag is non-nil.
;;     bmkp-default-handler-associations: Updated doc string.
;; 2011/08/05 dadams
;;     bmkp-file-bookmark-p: Allow handler to be bmkp-default-handler-for-file, e.g. for image files.
;;     bmkp-all-tags-alist-only: Corrected.
;;     bmkp-refresh-menu-list: Ensure BOOKMARK is a string.
;;     bmkp-every: Removed unused binding.
;; 2011/05/08 dadams
;;     Just put some definitions in alphabetic order - no real change.
;; 2011/04/25 dadams
;;     bmkp-bookmark-description: Added optional arg NO-IMAGE.
;;     bmkp-url-target-set: Protect url-get-url-at-point with fboundp.
;;     bmkp-(file-target|autofile)-set, bmkp-autofile-(add|remove)-tags:
;;       Added buffer-file-name as a default possibility.  Removed URL functions for that purpose.
;; 2011/04/24 dadams
;;     Added: bmkp-purge-notags-autofiles.
;;     bookmark-delete: Redefined to accept either bookmark or name as arg.
;;     bmkp-(url|file|compilation|occur)-target-set(-all), bmkp-autofile-(set|(add|remove)-tags):
;;       Removed optional args when read prefix.
;;     bmkp-occur-target-set-all: Made PREFIX arg optional too.
;;     Added some missing autoload cookies.  Removed some from non-def sexps.
;; 2011/04/21 dadams
;;     Added: bmkp-copied-tags, bmkp-copy-tags, bmkp-paste-add-tags, bmkp-paste-replace-tags..
;; 2011/04/20 dadams
;;     bmkp-remove-all-tags: Added optional arg no-cache-update-p.
;; 2011/04/19 dadams
;;     bmkp-make-record-for-target-file: Fixed backquotes on lambdas.
;; 2011/04/17 dadams
;;     bmkp-edit-tags: Do not apply bmkp-full-tag to the tags.
;; 2011/04/16 dadams
;;     Added: bmkp-edit-tags(-send|-mode(-map)), bmkp-return-buffer.
;;     bookmark-(rename|relocate|send-edited-annotation), bmkp-update-autonamed-bookmark,
;;       bmkp-(add|remove(-all)-tags:
;;         Wrap with-current-buffer around bmkp-refresh-menu-list.
;;     bookmark-(store|rename|write-file): Test emacs-major-version, not just (boundp 'print-circle).
;;     bmkp-autofile-add-tags: Fix interactive args - forgot to include DIR arg (= nil).
;; 2011/04/15 dadams
;;     Added: bmkp-autofile-alist-only, bmkp-autofile-bookmark-p.
;; 2011/04/13 dadams
;;     Added: bmkp-autofile-jump(-other-window) (aliases), bmkp-find-file(-other-window).
;;     bmkp-find-file-(all|some)-tags(-regexp)(-other-window): Bind use-file-dialog to nil.
;; 2011/04/12
;;     Added: bmkp-bookmark-name-member, bmkp-names-same-bookmark-p, bmkp-sort-omit,
;;            bmkp-remove-omitted, bmkp-delete-bookmark-name-from-list, bmkp-bookmark-a-file (alias),
;;            bmkp-autofile-(add|remove)-tags, bmkp-(un)tag-a-file (aliases),
;;            bmkp-get-autofile-bookmark, bmkp-find-file-(all|some)-tags(-regexp)(-other-window).
;;     Removed: bmkp-remove-assoc-dups, bmkp-sort-and-remove-dups.
;;     Applied renaming: bmkp-bmenu-omitted-list to bmkp-bmenu-omitted-bookmarks.
;;     bookmark-store: Redefine for all Emacs versions now:
;;       Put the bookmark on the name as property bmkp-full-record.  Use bmkp-maybe-save-bookmarks.
;;       Return the bookmark.
;;     bookmark-get-bookmark: Redefine for all Emacs versions now:
;;       If BOOKMARK is a bookmark-name string that has property bmkp-full-record, return that value.
;;     bookmark-send-edited-annotation: Make sure it's the annotation buffer that gets killed.
;;     bookmark-default-handler: Return nil, like vanilla (but why?).
;;     bookmark-location: Pass full bookmark to the various "get" functions.
;;     bookmark-rename: Put bmkp-full-record property on new name.
;;     bookmark-delete:
;;       Use bmkp-delete-bookmark-name-from-list: If name has bmkp-full-record property, use that
;;         with name to find bookmark to delete.
;;       Pass full bookmark to unlight.
;;     bmkp-edit-bookmark: Save if either is non-empty, not if both are.  Thx to Michael Heerdegen.
;;     bmkp-edit-bookmark-record: Bind print-circle to t around pp.
;;     bmkp-default-bookmark-name:
;;       Use bookmark-name-from-full-record plus bookmark-get-bookmark, not assoc.
;;       If BNAME is nil (no default) then do not try to look it up in alist.
;;     bookmark-write-file: Unpropertize only for Emacs 20 or nil bmkp-propertize-bookmark-names-flag.
;;                          Bind print-circle to t around pp.
;;     bmkp-save-menu-list-state: Make it interactive (a command).  Bind print-circle.
;;                                Use bmkp-maybe-unpropertize-bookmark-names on alists and name lists.
;;                                Bind print-circle to t around pp.
;;     bmkp-unomit-all: Use bmkp-delete-bookmark-name-from-list, not delete.
;;     bmkp-dired-this-dir-bookmark-p: Use bmkp-same-file-p, not string=.
;;     bmkp-url-target-set, bmkp-replace-existing-bookmark:: Return the bookmark.
;;     bmkp-file-target-set:  Return bookmark.  Added arg MSGP: msg if no file yet.
;;     bmkp-autofile-set:
;;       Added DIR arg and MSGP arg: msg if no file yet.  Return the bookmark.
;;       If read absolute file name, create bmk in its dir, not in default-directory.  Else use DIR.
;;       Use bmkp-get-autofile-bookmark, so uses bmkp-same-file-p for each file part (not equal).
;;     bmkp-marked-bookmark-p, bmkp-omitted-bookmark-p: Use bmkp-bookmark-name-member, not member.
;;     bookmark-location: Pass full bookmark to the various "get" functions.
;;     bmkp-choose-navlist-from-bookmark-list, bmkp-cycle-this-buffer:
;;       Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;;     bmkp-bookmark-description, bmkp-describe-bookmark-internals: Add Bookmark `' to title.
;;     bmkp-make-bookmark-list-record: Use bmkp-maybe-unpropertize-bookmark-names on lists.
;;     bmkp-printable-p: Bind print-circle to t around prin1.
;;     bmkp-delete-autonamed(-this-buffer)-no-confirm:
;;       Do nothing if bookmarks not loaded.  Thx to Christoph Scholtes.
;; 2011/04/03 dadams
;;     Added: bmkp-make-record-for-target-file, bmkp-replace-existing-bookmark (not used).
;;     bmkp-file-this-dir-bookmark-p: Corrected it to compare directory to default-directory.
;;     bmkp-file-target-set: Added arg NO-OVERWRITE (pass to bookmark-store).
;;                           Use (new) bmkp-make-record-for-target-file.
;;     bmkp-autofile-set: Do nothing if bookmark with same name, file and dir exists.
;;                        Else create one, even if the bookmark name is the same.
;;                        You can have multiple autofile bookmarks with the same name (diff files).
;; 2011/04/02 dadams
;;     Added: bmkp-autofile-set, bmkp-file-this-dir-(all|some)-tags(-regexp)-jump(-other-window),
;;            bmkp-file-this-dir-(all|some)-tags(-regexp)-alist-only.
;; 2011/04/01 dadams
;;     Moved key and menu bindings to (new) bookmark+-key.el.
;;     Added: bmkp-(dired|file)-this-dir-alist-only, bmkp-(dired|file)-this-dir-bookmark-p,
;;            bmkp-file-this-dir-jump(-other-window).
;;     Renamed: bmkp-dired-jump-current(*) to bmkp-dired-this-dir-jump(*).
;;     bmkp-dired-this-dir-jump(-other-window): Use bmkp-dired-this-dir-alist-only.
;;     bmkp-types-alist: Added (dired|file)-this-dir.
;;     Bound bmkp-(dired|file)-this-dir-jump to C-d and C-f in bookmark-jump(-other-window)-map.
;;     bmkp-jump-dired, bmkp-jump-man: Treat null bmkp-jump-display-function as display-buffer.
;; 2011/03/26 dadams
;;     Added: bmkp-file-(all|some)-tags(-regexp)-(alist-only|jump(-other-window)).
;;     bmkp-jump-menu: Added the new commands, but not Emacs 20, to avoid crash if byte-compiled.
;;     bmkp-bookmark-jump*-other-window: Simplified doc strings - refer to same-window version.
;; 2011/03/17 dadams
;;     bmkp-describe-bookmark: Added 10-pixel margin around thumbnail image.
;; 2011/03/11 dadams
;;     Protect use of mouse-wheel-*-event with boundp.  Thx to Chris Poole.
;; 2011/03/04 dadams
;;     bmkp-bookmark-description, bmkp-describe-bookmark: Added clickable thumbnail to the help.
;;     bmkp-bookmark-description: Split file name into dir & relname, so shorter line, in help.
;; 2011/03/03 dadams
;;     Added: bmkp-all-exif-data, bmkp-bookmark-image-bookmark-p.
;;     bmkp-bookmark-description: Handle image EXIF data.
;; 2011/01/03 dadams
;;     Removed autoload cookies from non def* sexps and from define-key and define-prefix-command.
;;     Added some missing autoload cookies for commands, in particular redefined standard commands.
;; 2010/12/10 dadams
;;     Added defalias for bookmark-name-from(-full)-record, to fix gratuitous Emacs name change.
;; 2010/10/22 dadams
;;     Uncommented key bindings for mouse wheel, since Emacs bug #6256 has now been fixed.
;;     bmkp-repeat-command: Don't bother to let-bind repeat-previous-repeated-command,
;;                          and use setq, not let, for last-repeatable-command. Thx to Stefan Monnier.
;; 2010/09/28 dadams
;;     Added: bmkp-delete-autonamed(-this-buffer)-no-confirm.
;; 2010/09/25 dadams
;;     Added: option bmkp-default-bookmark-name, bmkp-annotated-alist-only.
;;     Added: bmkp-(next|previous)-*(-repeat), using macro bmkp-define-next+prev-cycle-commands.
;;     bmkp-default-bookmark-name: Respect option.
;;     bookmark-edit-annotation-mode, bookmark-edit-annotation:
;;       Use bmkp-annotated-alist-only (and new bmkp-default-bookmark-name).
;;     bookmark-send-edited-annotation:
;;       End in orig buffer, not bmenu buffer.  Delete edit window.  Thx to Joe Bloggs.
;; 2010/09/24 dadams
;;     Added: bmkp-autonamed(-this-buffer)-jump(-other-window).  Bound to C-x j # (#|.) and menus.
;;     Added, using bmkp-define-cycle-command:
;;       bmkp-cycle-(autonamed|bookmark-list|desktop|dired|gnus|info|lighted|(local-|remote-)file|
;;                   man|non-file|remote-file|specific-(buffers|files)|variable-list|url)
;;                   (-other-window).
;;     Added redefinitions: bookmark-edit-annotation(-mode).
;;     Renamed: *varlist* to *variable-list*.
;;     bmkp-autoname-format: Added ^ to anchor numeral at beginning.
;;     bookmark--jump-via: Don't update autonamed if using w32 association.
;;     bmkp-update-autonamed-bookmark: bmkp-refresh-menu-list only if buffer list is displayed.
;;     *-(relocate|rename), *-update-autonamed-bookmark, *-remove-all-tags, *-(add|remove)-tags:
;;       Don't create bookmark-list buffer if doesn't exist.
;;     bookmark-show-(annotation|all-annotations): Restore selected window and frame focus.
;;     bmkp-completing-read-(buffer|file)-name: Added optional NO-DEFAULT-P arg.
;;     bmkp-describe-bookmark: Default to highlighted bookmarks on line, if there are any.
;;     bmkp-specific-(buffers|files)-jump(-other-window): Allow empty input, to end loop.
;;     bmkp-cycle: Ensure bmkp-current-nav-bookmark is a bookmark, else redefine.  Use %9d, not %d.
;;     bmkp-cycle-other-window: Added optional STARTOVERP arg here too.
;; 2010/09/20 dadams
;;     bmkp-choose-navlist-of-type: Empty input means "any".
;; 2010/09/16 dadams
;;     bmkp-read-bookmark-file-name:
;;       Removed extra default-filename in call to read-file-name.  Thx to Pedro Insua.
;; 2010/08/22 dadams
;;     Added: bmkp-regexp-filtered-annotation-alist-only.
;; 2010/08/20 dadams
;;     Added: bmkp-read-bookmark-file-name.
;;     bookmark-save, bookmark-load, bmkp-switch-bookmark-file, bmkp-use-bookmark-file-create:
;;       Use bmkp-read-bookmark-file-name.
;; 2010/08/19 dadams
;;     Require gnus-sum.el when compile (for macro).  Thx to S. Nemec.
;; 2010/08/18 dadams
;;     Removed eval-when-compile for bookmark+-lit.el.
;;     Replaced defvar of bmkp-edit-bookmark-record-mode-map with a define-key after derived mode.
;; 2010/08/17 dadams
;;     bmkp-edit-bookmark: Made interactive.  Bound to C-x p E.  Added optional INTERNALP arg.
;;     bmkp-info-bookmark-p: Return nil if a different handler.
;; 2010/08/15 dadams
;;     Moved bmkp-define-file-sort-predicate, bmkp-menu-bar-make-toggle to bookmark+-mac.el.
;;     Require: bookmark.el, bookmark+-mac.el.
;;     Require for compile: bookmark+-bmu.el, bookmark+-lit.el (soft).
;;     Ensure this file is loaded before compiling.
;;     bmkp-set-bookmark-file-bookmark: Added missing arg for error format string.
;; 2010/08/08 dadams
;;     bookmark-jump: Added optional arg DISPLAY-FUNCTION (Emacs 24).
;;     bookmark-handle-bookmark:
;;       Move non-default handler call outside condition-case.
;;       Updated for Emacs 24: Use error condition bookmark-error-no-filename.  Added props for it.
;;     bookmark-default-handler: Updated for Emacs 24:
;;       Signal condition bookmark-error-no-filename, not file-error, and pass (stringp FILE).
;;     bookmark-make-record-default: Added optional args NO-CONTEXT, POSITION (Emacs 24), and VISITS.
;;     bookmark-load: Updated for Emacs 24: Wrap with abbreviate-file-name.
;;     bmkp-jump-1: Allow arg to be a bookmark or its name.
;;     bmkp-gnus-bookmark-p: Updated for Emacs 24: Added gnus-summary-bookmark-jump.
;;     bmkp-jump-gnus: Different gnus-fetch-group call for Emacs 20, 21.
;;     bmkp-make-(desktop|varlist|bookmark-(file|list))-record: Call *-record-default with NO-CONTEXT.
;;     w3m-current-title: Use w3m-current-title as bookmark name.
;;     bmkp-w3m-set-new-buffer-name, bmkp-jump-w3m*: Require w3m.
;;     bmkp-make-gnus-record: Get bookmark name from gnus-summary-article-header.
;;     Update for Emacs 24: Bypass bmkp specific Gnus, man, and woman code.
;; 2010/08/06 dadams
;;     Added (and bound the commands):
;;       bmkp-(compilation|occur)-target-set(-all), bmkp-(file|url)-target-set,
;;       bmkp-default-handler-associations, bmkp-compilation-file+line-at,
;;       bmkp-default-handler-(for-file|user), bmkp-sound-jump.
;;     bmkp-occur-create-autonamed-bookmarks: Do not define it  for Emacs < 22.  Protect wrt POS, BUF.
;;     Added to Bookmark menu: bmkp-(file|url)-target-set, bmkp-set-(bookmark-file|desktop)-bookmark.
;; 2010/08/04 dadams
;;     bmkp-edit-bookmark: Use new bookmark name for update of dired-directory.  Thx to Kai Tetzlaff.
;; 2010/08/03 dadams
;;     bmkp-make-url-browse-record: Remove text properties from URL arg.
;; 2010/07/17 dadams
;;     Added: bmkp-url-jump-(other-window), bmkp-url(-browse)-(alist-only|bookmark-p), bmkp-url-cp,
;;            bmkp-url-history, bmkp-make-url-browse-record, bmkp-jump-url-browse.
;;     bmkp-sort-comparer: Use bmkp-url-cp, not bmkp-w3m-cp.
;;     bmkp-types-alist: w3m -> url.
;;     bookmark-alist: Updated doc string to mention LOCATION.  W3M -> URL.
;;     bmkp-bookmark-description: Treat URL.  Set no-position-p depending on start.
;;     Bind bmkp-url-jump*.  Replace W3M by URL in menu items.
;; 2010/07/14 dadams
;;     Created from bookmark+.el code.
 
;;;(@* "CHANGE LOG FOR `bookmark+-bmu.el'")
;;
;; 2017/10/27 dadams
;;     bookmark-bmenu-mode: Added to doc string: bmkp-bmenu-paste-(add|replace)-tags.
;; 2017/10/14 dadams
;;     All EWW stuff is for Emacs 25+, not Emacs 24.4+.
;; 2017/10/08 dadams
;;     bmkp-bmenu-describe-marked: Bind print-(circle|length|level) so pp-to-string prints all.
;; 2017/07/03 dadams
;;     Added: bmkp-bmenu-sort-by-Info-position.
;;     Renamed bmkp-bmenu-sort-by-Info-location to bmkp-bmenu-sort-by-Info-node-name.
;;     bookmark-bmenu-mode: Updated doc string for Info-bookmark sorting.
;;     bmkp-bmenu-sort-by-bookmark-type, bmkp-bmenu-sort-by-Info-node-name:
;;       Applied renaming of bmkp-info-cp to bmkp-info-node-name-cp.
;;     Bind bmkp-bmenu-sort-by-Info-position to s I.
;;     bmkp-bmenu-sort-menu:
;;       Added bmkp-bmenu-sort-by-Info-position.  Renamed By Info Node to By Info Node Name.
;; 2017/03/30 dadams
;;     bmkp-bmenu-mark-*-bookmarks:
;;       Added optional arg MSGP.  Pass it to bmkp-bmenu-mark-bookmarks-satisfying.
;;     bmkp-bmenu-mark-(orphaned-local-)file-bookmarks: Made argument ARG optional.
;;     bmkp-bmenu-mark-bookmarks-satisfying: Added missing \ni to interactive spec.
;; 2017/01/10 dadams
;;     Renamed bmkp-toggle-allow-multi-tabs-for-w3m to bmkp-toggle-w3m-allow-multiple-buffers.
;;     bmkp-bmenu-toggle-menu: Added bmkp-toggle-eww-allow-multiple-buffers.
;; 2017/01/08 dadams
;;     Use the term "entry", not "property" everywhere, for bookmark entries (fields).
;; 2017/01/07 dadams
;;     bmkp-bmenu-copy-marked-to-bookmark-file: Use bookmark-file-coding-system (Emacs bug #25365).
;; 2017/01/02 dadams
;;     bmkp-bmenu-mouse-3-menu: Added menu item Store Org Link.
;; 2016/12/31 dadams
;;     Added: bmkp-bmenu-mark-non-invokable-bookmarks, bmkp-bmenu-show-only-non-invokable-bookmarks.
;;       Bound them to nM and nS.  Added them to menus bmkp-bmenu-(mark|show)-types-menu.
;;     bookmark-bmenu-mode: Include non-invokable bookmarks in doc string.
;;     bmkp-bmenu-propertize-item: Handle non-invokable bookmarks.
;; 2016/11/23 dadams
;;     bookmark-bmenu-mode: Doc string cleanup.
;;     bookmark-bmenu-list, bmkp-bmenu-copy-marked-to-bookmark-file:
;;       Raise an error if we have a directory, not a file.
;;     bmkp-bmenu-create-bookmark-file-from-marked: Ensure that FILE is not a directory.
;; 2016/11/18 dadams
;;     Support Emacs 24.[45] too.
;; 2016/11/15 dadams
;;     bmkp-*eww-*: Ensure that EWW code is only for Emacs 25+.
;; 2016/11/14 dadams
;;     Added: bmkp-bmenu-mark-eww-bookmarks, bmkp-bmenu-show-only-eww-bookmarks.
;;     bookmark-bmenu-mode: Added EWW to doc.
;;     Bound bmkp-bmenu-mark-eww-bookmarks to WEM, bmkp-bmenu-show-only-eww-bookmarks to WES.
;;     Change bmkp-bmenu-mark-w3m-bookmarks to W3M, bmkp-bmenu-show-only-w3m-bookmarks binding to W3S.
;;     bmkp-bmenu-mark-types-menu, bmkp-bmenu-show-types-menu: Support EWW.
;; 2016/06/24 dadams
;;     bookmark-bmenu-execute-deletions: Delete bookmark on the current line if none flagged/marked.
;; 2016/06/23 dadams
;;     bmkp-bmenu-(add|remove)-tags-(to|from)-marked, bmkp-bmenu-paste-(add|replace)-tags-for-marked:
;;       Call bmkp-maybe-save-bookmarks (after the iteration).  Thx to Alan Wehmann.
;; 2016/06/21 dadams
;;     bmkp-bmenu-add-tags-to-marked, bmkp-bmenu-remove-tags-from-marked,
;;       bmkp-bmenu-paste-(add|replace)-tags-to-marked:
;;         Put bookmark-save-flag let-binding around iteration only, so modification is recorded etc.
;; 2016/06/11 dadams
;;     bmkp-bmenu-list-1, bookmark-bmenu-hide-filenames:
;;       Use string-width, not length.  Thx to Toshikazu Nakamura.
;; 2015/11/07 dadams
;;     bmkp-bmenu-copy-marked-to-bookmark-file: Added missing zerop test for No-changes case.
;;     bmkp-bmenu-create-bookmark-file-from-marked:
;;       Added missing MOVEP arg in call to bmkp-bmenu-copy-marked-to-bookmark-file.
;; 2015/11/02 dadams
;;     bmkp-bmenu-copy-marked-to-bookmark-file:
;;       If modified, prompt to save bookmark file copied from, before copying.
;;       For copy (not move): reload the original bookmark file, then refresh display from it.
;; 2015/10/31 dadams
;;     bmkp-bmenu-move-marked-to-bookmark-file:
;;       Just call bmkp-bmenu-copy-marked-to-bookmark-file.  It now deletes moved and refreshes list.
;;     bmkp-bmenu-copy-marked-to-bookmark-file:
;;       Added arg MOVEP.  If move, delete before refresh list (deletes bmks returned in IMPORTED). 
;; 2015/06/26 dadams
;;     Added: bmkp-bmenu-mark-function-bookmarks, bmkp-bmenu-show-only-function-bookmarks.
;;            Bound the to Q M and Q S.  Added to bmkp-bmenu-show-types-menu.
;;     bookmark-bmenu-mode: Updated the doc string for them.
;;     bmkp-bmenu-show-only(-orphaned-local)-file-bookmarks: Made ARG optional.
;; 2015/05/15 dadams
;;     Fixed typo: bmkp-bmenu-show-only-lighted -> bmkp-bmenu-show-only-lighted-bookmarks everywhere.
;; 2015/04/15 dadams
;;     bmkp-bmenu-describe-this-bookmark: save-selected-frame -> save-selected-window.
;; 2015/03/20 dadams
;;     Added: bmkp-bmenu-show-this-annotation+move-down, bmkp-bmenu-show-this-annotation+move-up,
;;            bmkp-bmenu-kill-annotation, bmkp-remap.
;;     Bind bmkp-bmenu-show-this-annotation+move-(down|up) to M-down, M-up.
;;     bmkp-bmenu-describe-this+move-(down|up): Move first, then describe, not reverse.
;;     bmkp-bmenu-describe-this-bookmark: Wrap with save-selected-frame.
;; 2015/02/22 dadams
;;     Moved to bookmark+-1.el from here:
;;       bmkp-reset-bmkp-store-org-link-checking-p, bmkp-store-org-link-checking-p.
;;       Advice of org-store-link (not needed for bmkp-bmenu-store-org-link).
;;     Soft-require org.el when compile, for org-add-link-type.
;;     bmkp-bmenu-store-org-link:
;;       Removed bmkp-store-org-link-checking-p (needed only for bmkp-store-org-link).
;;       Link type changed from bookmark-other-window to bookmark-other-win.
;;     Fix for lost annotation etc. edit the first time after showing display list:
;;       bookmark-bmenu-list, bmkp-bmenu-define-full-snapshot-command:
;;         Bind bookmark-alist to result of bmkp-refresh-latest-bookmark-list - do not just bind it to
;;           bmkp-latest-bookmark-alist if available.  (NOT SURE THIS IS RIGHT.)
;;       bmkp-bmenu-list-1:
;;         Removed update of bmkp-latest-bookmark-alist when not filteredp.  (NOT SURE THIS IS RIGHT.)
;;     bmkp-bmenu-menubar-menu:
;;       Toggle menu:
;;         Moved Toggle menu higher.
;;         Moved bmkp-toggle-save-desktop-before-switching with other autosaving menu items.
;;         Added bmkp-toggle-auto-light-when-jump-menu.  
;;         Moved temporary bookmark stuff lower, after display-list stuff.
;;         bmkp-toggle-saving-menu-list-state: Corrected help text - affects also being able to save.
;;       Moved bmkp-list-defuns-in-commands-file with other help stuff.
;; 2015/02/21 dadams
;;     Added: bmkp-bmenu-store-org-link, bmkp-reset-bmkp-store-org-link-checking-p,
;;            bmkp-store-org-link-checking-p.
;;     Add bmkp-bmenu-store-org-link to org-store-link-functions.
;;     Advise org-store-link with bmkp-reset-bmkp-store-org-link-checking-p.
;;     Added bookmark(-other-window) link types via org-add-link-type.
;; 2015/02/08 dadams
;;     Added: bmkp-bmenu-show-only-untagged-bookmarks.  Added it to bmkp-bmenu-show-types-menu.
;;     Renamed: bmkp-bmenu-*icicle-* to bmkp-bmenu-icicles-*,
;;              bmkp-bmenu-show-only-*- to bmkp-bmenu-show-only-*-bookmarks.
;;     Use new macro bmkp-define-show-only-command for the simple bmkp-bmenu-show-only-* commands.
;; 2014/12/18 dadams
;;     bmkp-bmenu-show-only-specific-file: Restore vars if error.
;; 2014/12/04 dadams
;;     *-dired-marked, *-move-marked-to-bookmark-file, *-copy-marked-to-bookmark-file,
;;       *-create-bookmark-file-from-marked, *-set-bookmark-file-bookmark-from-marked,
;;       *-(i)search-marked-bookmarks(-regexp), *-query-replace-marked-bookmarks-regexp,
;;       *-set-tag-value-for-marked, *-add-tags-to-marked, *-remove-tags-from-marked,
;;       *-paste-(add|replace)-tags-to-marked, *-relocate-marked, *-edit-marked, *-describe-marked:
;;         Added arg INCLUDE-OMITTED-P.
;; 2014/11/09 dadams
;;     bookmark-bmenu-show-annotation: Updated doc string to reflect updated bookmark-show-annotation.
;; 2014/08/22 dadams
;;     bmkp-looking-at-p: Do not defalias to Emacs looking-at-p because that is a defsubst.
;; 2014/07/20 dadams
;;     Protect key bindings for bmkp-bmenu-highlight-menu by boundp.
;; 2014/07/12 dadams
;;     Added: bmkp-bmenu-relocate-marked.  Bound to M-R.  Added it to bmkp-bmenu-menubar-menu.
;; 2014/07/11 dadams
;;     bmkp-bmenu-highlight-menu: Added item Toggle Autofile Highlighting in Dired.
;;     bmkp-bmenu-toggle-menu: Added item Autofile Highlighting in Dired.
;; 2014/07/06 dadams
;;     Toggle submenu: added lots, improved.
;; 2014/07/05 dadams
;;     Added: bmkp-bmenu-create-bookmark-file-from-marked (bound to Y > 0),
;;            bmkp-bmenu-set-bookmark-file-bookmark-from-marked, bmkp-bmenu-bookmark-file-menu.
;;     Moved bookmark-file stuff to Bookmark File submenu.
;;     bookmark-bmenu-mode: Updated doc string.
;;     bmkp-bmenu-dired-marked: Use bmkp-bmenu-marked-or-this-or-all, not bmkp-marked-bookmarks-only.
;;     bmkp-bmenu-marked-or-this-or-all: Added optional arg INCLUDE-OMITTED-P - else removed omitted.
;; 2014/07/04 dadams
;;     Added to Bookmark+ menu: bmkp-bmenu-(copy|move)-marked-to-bookmark-file.
;; 2014/07/03 dadams
;;     Added: bmkp-bmenu-copy-marked-to-bookmark-file, bmkp-bmenu-move-marked-to-bookmark-file.
;;            Bound to Y > + and Y > -.
;;     bookmark-bmenu-mode: Mention bmkp-bmenu-(copy|move)-marked-to-bookmark-file in doc string.
;;     bookmark-bmenu-execute-deletions, bmkp-bmenu-delete-marked:: Added optional arg NO-CONFIRM-P.
;;     bmkp-bmenu-define(-full-snapshot|jump)-command: Changed to C-c C-c, C-c C-S-c, C-c C-j.
;;     bmkp-bmenu-show-all: Mention C-u g in doc string.
;; 2014/06/30 dadams
;;     bmkp-bmenu-mouse-3-menu:
;;       Bind bmkp-bmenu-flag-for-deletion, not bookmark-bmenu-delete.  See Emacs bug #17888.
;; 2014/06/26 dadams
;;     bmkp-bmenu-show-only-omitted:
;;       Use bmkp-bmenu-omit/unomit-marked, not bmkp-bmenu-unomit-marked, in doc string.
;;     bmkp-bmenu-remove-tags-from-marked:
;;       Typo in interactive spec: allp -> current-prefix-arg.  Thx to Alan Wehmann.
;; 2014/06/21 dadams
;;     Added: bmkp-no-jump, bmkp-bmenu-mark-bookmark-list-bookmarks,
;;       bmkp-bmenu-mark-icicle-search-hits-bookmarks, bmkp-bmenu-show-only-bookmark-lists,
;;       bmkp-bmenu-show-only-icicle-search-hits.
;;     bookmark-bmenu-list, bookmark-bmenu-mode: Updated doc string, for additions.
;;     bmkp-bmenu-mode-status-help: Updated for no-jump (used for Icicles search hits bookmarks).
;;     bmkp-bmenu-propertize-item: Handle Icicles search hits bookmarks.
;;     Bind *-bmenu-mark-icicle-search-hits-bookmarks, *-bmenu-show-only-icicle-search-hits: i M, i S.
;;     Bind bmkp-bmenu-mark-bookmark-list-bookmarks, bmkp-bmenu-show-only-bookmark-lists: Z M, Z S.
;;     bmkp-bmenu-mark-types-menu:
;;       Added bmkp-bmenu-mark-icicle-search-hits-bookmarks, bmkp-bmenu-mark-bookmark-list-bookmarks.
;;     bmkp-bmenu-show-types-menu:
;;       Added bmkp-bmenu-show-only-icicle-search-hits, bmkp-bmenu-show-only-bookmark-lists.
;; 2014/06/20 dadams
;;     bmkp-define-tags-sort-command: Load bookmark+-mac.el(c) in interactive spec.
;; 2014/05/27 dadams
;;     bmkp-bmenu-mode-status-help, bmkp-bmenu-describe-marked:
;;       Use bmkp-with-help-window, not with-output-to-temp-buffer (Emacs 24.4+ silliness).
;; 2014/04/02 dadams
;;     bmkp-bmenu-copy-tags, bmkp-bmenu-paste-replace-tags(for-marked):
;;       Added Note to doc string about pasting an empty list of tags.
;;     bmkp-bmenu-tags-menu: Added item Copy Tags from This Bookmark for bmkp-bmenu-copy-tags.
;;     bmkp-bmenu-mouse-3-menu: Added :active bmkp-copied-tags for bmkp-bmenu-paste-add-tags.
;; 2014/04/01 dadams
;;     Added: bmkp-bmenu-list-tags-of-marked.
;;       Bind it to T > l in bookmark-bmenu-mode-map.
;;       Add it to bmkp-bmenu-tags-menu.
;;     bookmark-bmenu-mode: List bmkp-bmenu-list-tags-of-marked in doc string.
;; 2014/03/29 dadams
;;     Added variable bmkp-bmenu-define-command-history.
;;     bmkp-bmenu-define(-jump-marked|-full-snapshot)-command:
;;       Removed quote before bmkp-bmenu-define-command-history.
;;     Toggle submenu: Use bmkp-menu-bar-make-toggle.
;; 2014/03/28 dadams
;;     bmkp-bmenu-describe-marked: Apply bmkp-sort-omit, to show bookmarks in the current sort order.
;; 2014/03/23 dadams
;;     Added: bmkp-bmenu-delete-menu, bmkp-bmenu-mark-types-menu, bmkp-bmenu-search-menu,
;;            bmkp-bmenu-show-types-menu, bmkp-bmenu-toggle-menu.  Move menu items there from top.
;;     bookmark-bmenu-mode-map:
;;       Bind jump commands to j prefix and J prefix (like C-x 4 j and C-x j).
;;       Bind bookmark-bmenu-locate to C-S-l, since w is used as a prefix key now.
;;     bookmark-bmenu-mode: New jump bindings.  Added bmkp-bmenu-copy-tags.
;; 2014/03/21 dadams
;;     bookmark-bmenu-mode: List also global bindings for tag commands.
;; 2014/03/10 dadams
;;     bmkp-maybe-unpropertize-bookmark-names: Remove prop face & Icicles props, in any case.
;;     bmkp-bmenu-define(-jump-marked|-full-snapshot)-command, bmkp-define-tags-sort-command:
;;       Bind print-circle to bmkp-propertize-bookmark-names-flag, not t, to avoid string reuse.
;; 2013/12/13 dadams
;;     bmkp-bmenu-mode-line:
;;       To avoid Emacs crashes from bug #12867: Do not define it for Emacs 22-23, and wrap
;;                                               condition-case around the whole function body.
;; 2013/12/11 dadams
;;     bmkp-bmenu-mode-line: Protect %360l (line) hack with condition-case.
;; 2013/10/07 dadams
;;     bmkp-bmenu-edit-marked: If no marked bmks, mark the current line bmk, to start with.
;;                             Use correct buffer when go to point-min.
;; 2013/08/09 dadams
;;     Added: bmkp-looking-at-p.  Use it instead of looking-at, everywhere.
;; 2013/07/02 dadams
;;     Added to menu-bar Edit menu: bmkp-set-snippet-bookmark, bmkp-snippet-to-kill-ring.
;; 2013/06/30 dadams
;;     Added: bmkp-snippet, bmkp-bmenu-show-only-snippets, bmkp-bmenu-mark-snippet-bookmarks.
;;     bookmark-bmenu-list: Added snippet info to doc string.
;;     bmkp-bmenu-mode-status-help: Cover snippets too.
;;     Bind bmkp-bmenu-(mark-snippet-bookmarks|show-only-snippets) to w M, w S.  Add to menus.
;; 2013/06/29 dadams
;;     bmkp-bmenu-regexp-mark, bmkp-bmenu-search-marked-bookmarks-regexp,
;;       bmkp-bmenu-(un)mark-bookmarks-tagged-regexp:
;;         Use bmkp-read-regexp in interactive spec.
;;     bmkp-bmenu-mode-status-help: Ensure that we have a supported image before calling insert-image.
;; 2013/06/09 dadams
;;     bmkp-bmenu-mode-line-string: Added missing let-binding for REGEXP.
;;     Added vacuous defvars to suppress free-var warnings.
;; 2013/05/28 dadams
;;     Renamed: bmkp-bmenu-edit-bookmark-name-and-file to bmkp-bmenu-edit-bookmark-name-and-location.
;; 2013/05/28 dadams
;;     bmkp-bmenu-list-1: Do not call put-image if create-image returns nil.
;; 2013/05/15 dadams
;;     Moved here from bookmark+-1.el: bmkp-string-match-p.
;;     Use bmkp-string-match-p instead of string-match wherever appropriate.
;; 2013/04/10 dadams
;;     bmkp-bmenu-make-sequence-from-marked: Redefine using bmkp-set-sequence-bookmark (new).
;; 2013/01/07 dadams
;;     bookmark-bmenu-mode:
;;       Added: bmkp-bmenu-set-tag-value-for-marked, bmkp-bmenu-paste-(add|replace)-tags-for-marked.
;;       Mention C-u = all, for marked.
;; 2013/01/04 dadams
;;     bmkp-bmenu-show-only-tagged: Corrected filter function.
;; 2012/11/14 dadams
;;     bmkp-bmenu-mode-line: Added mode-line-buffer-identification.
;; 2012/11/12 dadams
;;     Added: bmkp-bmenu-marked-or-this-or-all.
;;     bmkp-bmenu-isearch-marked-bookmarks(-regexp), bmkp-bmenu-search-marked-bookmarks-regexp,
;;       bmkp-bmenu-query-replace-marked-bookmarks-regexp, bmkp-bmenu-set-tag-value-for-marked,
;;       bmkp-bmenu-add-tags-to-marked, bmkp-bmenu-remove-tags-from-marked,
;;       bmkp-bmenu-paste-(add|replace)-tags-(to|for)-marked, bmkp-bmenu-edit-marked,
;;       bmkp-bmenu-describe-marked:
;;         Make it work for current bookmark if none marked.
;;     bmkp-bmenu-isearch-marked-bookmarks(-regexp), bmkp-bmenu-search-marked-bookmarks-regexp,
;;       bmkp-bmenu-set-tag-value-for-marked, bmkp-bmenu-add-tags-to-marked,
;;       bmkp-bmenu-remove-tags-from-marked, bmkp-bmenu-paste-(add|replace)-tags-(to|for)-marked,
;;       bmkp-bmenu-edit-marked:
;;         Make it work for all bookmarks if use prefix arg.
;;     Protect all calls to bmkp-bmenu-mode-line with fboundp, for Emacs 20.
;; 2012/11/11 dadams
;;     Added: bmkp-bmenu-mode-line, bmkp-bmenu-mode-line-string.
;;     Removed: bmkp-bmenu-nb-marked-in-mode-name (replaced by bmkp-bmenu-mode-line - shows more).
;;     Removed faces bmkp-mode-line-marked, bmkp-mode-line-flagged.
;;     bookmark-bmenu-(delete|(un)mark), bmkp-bmenu-list-1: Call bmkp-bmenu-mode-line.
;;     bookmark-bmenu-execute-deletions: Inhibit saving until all are deleted, then save.
;;     bmkp-bmenu-mode-status-help: Show > and D using their faces, bmkp->-mark, bmkp-D-mark.
;;                                  Use "" if bmkp-current-sort-order (new version) returns nil.
;; 2012/10/09 dadams
;;     Made all autoload cookies explicitly load bookmark+.el(c).  Should help ELPA (e.g. MELPA).
;; 2012/09/29 dadams
;;     Added: bmkp-maybe-unpropertize-string.
;;     bmkp-maybe-unpropertize-bookmark-names: Added optional arg COPY.
;;     bmkp-bmenu-define(-jump-marked|-full-snapshot|-tags-sort)-command:
;;       Bind print-circle, version-control, require-final-newline.
;;       Use find-file-noselect & write-file, not write-region.
;;     bmkp-bmenu-define-jump-marked-command: Use bmkp-maybe-unpropertize-bookmark-names on bookmarks.
;;     bmkp-bmenu-define-full-snapshot-command:
;;       Copy shared bookmark lists and single strings, to avoid circular refs.
;;       Expand file names and use convert-standard-filename, for bookmark file names.
;; 2012/09/28 dadams
;;     Added: bmkp-bmenu-jump-to-marked.
;;     Renamed: bmkp-bmenu-w32-open-select to bmkp-bmenu-w32-jump-to-marked.
;;     Replace bookmark-bmenu-select with bmkp-bmenu-jump-to-marked, everywhere.
;;     bmkp-bmenu-w32-open-with-mouse:
;;       Rewrote to directly call bookmark-handle-bookmark, jump-fn, and show annotations.
;; 2012/09/03 dadams
;;     bookmark-bmenu-toggle-filenames: Added missing nil FORCE arg.
;;     bmkp-bmenu-list-1: Call bookmark-bmenu-toggle-filenames with NO-MSGP arg.
;;     Removed: bmkp-bmenu-filter-prompt.  bmkp-bmenu-read-filter-input: hard-code the prompt.
;; 2012/06/26 dadams
;;     Moved here from bookmark+-mac.el: bmkp-assoc-delete-all, bmkp-replace-regexp-in-string.
;;     Wrapped require of bookmark+-mac.el in eval-when-compile.
;; 2012/06/21 dadams
;;     Added: bmkp-bmenu-nb-marked-in-mode-name.  Added to bookmark-bmenu-mode-hook.
;;     Try to load-library bookmark+-mac.  Require it only if cannot load-library.
;; 2012/06/15 dadams
;;     bookmark-bmenu-mode, bmkp-bmenu-mode-status-help: Improved doc string.
;;     bmkp-bmenu-show-or-edit-annotation: Corrected doc string: bookmark, not buffer.
;; 2012/06/14 dadams
;;     Added face bmkp-no-local.
;;     Redefined defaults for faces bmkp-non-file and bmkp-variable-list.
;;     bmkp-bmenu-mode-status-help: Added legend for no such local file.
;;     bmkp-bmenu-propertize-item: Distinguish no such local file from no such existing buffer.
;; 2012/06/13 dadams
;;     bookmark-bmenu-bookmark: forward-char bmkp-bmenu-marks-width, not 1+ that.
;;     bmkp-bmenu-propertize-item: Allow a file bookmark to get buffer prop if file not yet saved.
;;                                 Do not require buffer-name attribute for bmkp-non-file face.
;; 2012/06/11 dadams
;;     bmkp-bmenu-propertize-item: Use bmkp-non-file-filename also if filename is missing from bmk.
;; 2012/05/05 dadams
;;     bookmark-bmenu-(un)mark(-all), bmkp-bmenu-regexp-mark, bmkp-bmenu-toggle-marks,
;;       bmkp-bmenu-mark-bookmarks-satisfying, bmkp-bmenu-toggle-marked-temporary/savable,
;;       bmkp-bmenu-(un)mark-bookmarks-tagged-regexp:
;;         Added optional arg MSG-P.
;;     bookmark-bmenu-(un)mark(-all), bookmark-bmenu-execute-deletions, bmkp-bmenu-regexp-mark,
;;       bmkp-bmenu-toggle-show-only-(un)marked, bmkp-bmenu-mark-bookmarks-satisfying,
;;       bmkp-bmenu-toggle-marks, bmkp-bmenu-toggle-marked-temporary/savable,
;;       bmkp-bmenu-toggle-temporary, bmkp-bmenu-make-sequence-from-marked,
;;       bmkp-bmenu-(un)omit(-marked), bmkp-bmenu-(un)mark-bookmarks-tagged-regexp,
;;       bmkp-bmenu-mark/unmark-bookmarks-tagged-*, bmkp-bmenu-change-sort-order,
;;       bmkp-reverse(-multi)-sort-order:
;;         Pass NO-MSG-P to *-refresh/rebuild-menu-list, *-surreptitiously-rebuild-list, *-store.
;;     bmkp-bmenu-mark/unmark-bookmarks-tagged-(all/none|some/not-all):
;;       Swapped last two args, so consistent order.
;;     bmkp-bmenu-(un)mark-bookmarks-tagged-*: Updated arg order in calls to b-b-m/u-b-t-(a/n|s/n-a).
;;     bmkp-bmenu-(un)mark-bookmarks-tagged-regexp, bmkp-bmenu-mark/unmark-bookmarks-tagged-*:
;;       Added status message.
;; 2012/05/01 dadams
;;     Added redefinition of bookmark-bmenu-delete-backwards (they broke its movement).
;;     Added aliases: bmkp-bmenu-flag-for-deletion(-backwards).  Bind to d, k, C-d (same as aliases).
;;     bmkp-bmenu-(add|remove)-tags, bmkp-bmenu-(add|remove)-tags-(to|from)-marked:
;;         Automatically re-sort if # tagged bmks changed and sort order is tagged first/last (s t).
;;     Added: bmkp-bmenu-sort-tagged-before-untagged.
;;     Bind bmkp-bmenu-sort-tagged-before-untagged to s t.
;;     Bind bmkp-bmenu-sort-by-last-bookmark-access to s d, not s t.
;;     Bind bmkp-bmenu-sort-by-last-local-file-access to s f d, not s f t.
;;     Bind bmkp-bmenu-sort-by-local-file-type to s f k, not s f d.
;; 2012/04/28 dadams
;;     bookmark-bmenu-(un)mark(-all), bmkp-bmenu-regexp-mark, bmkp-bmenu-mark-bookmarks-satisfying,
;;       bmkp-bmenu-toggle-marks, bmkp-bmenu-(un)mark-bookmarks-tagged-regexp,
;;       bmkp-bmenu-mark/unmark-bookmarks-tagged-(all/none|some/not-all):
;;         Added optional arg NO-RE-SORT-P.
;;         Automatically re-sort if marks changed and if sort order is marked first/last (s >).
;;     Changed all non-interactive calls of bookmark-bmenu-(un)mark to pass non-nil NO-RE-SORT-P.
;;     bmkp-bmenu-toggle-marks: Call bookmark-bmenu-ensure-position at start.
;; 2012/04/27 dadams
;;     bmkp-bmenu-edit-marked: Use bmkp-with-output-to-plain-temp-buffer.
;; 2012/04/13 dadams
;;     Added: bmkp-bmenu-sort-(flagged|modified)-before-un(flagged|modified), bmkp-flagged-bookmarks.
;;     Bound bmkp-bmenu-sort-(flagged|modified)-before-un(flagged|modified) to s D, s *.
;;     bookmark-bmenu-(un)mark: Delete bookmark from bmkp-flagged-bookmarks.
;;     bookmark-bmenu-mark: Use (equivalent of) eq version of add-to-list.
;;     bookmark-bmenu-delete: Add bookmark to bmkp-flagged-bookmarks.
;;     bmkp-bmenu-list-1: Always reset bmkp-(flagged|modified)-bookmarks.
;;                        Flag bookmarks if bmkp-flagged-bookmark-p.
;;     bmkp-bmenu-refresh-menu-list: C-u resets bmkp-flagged-bookmarks too.
;; 2012/04/10 dadams
;;     bmkp-bmenu-load-marked-bookmark-file-bookmarks:
;;       Use bmkp-refresh-menu-list, not bmkp-refresh/rebuild-menu-list.
;;     bmkp-bmenu-(add|remove)-tags-(to|from)-marked, bmkp-bmenu-paste-(add|replace)-tags-to-marked:
;;       Corrected bookmark-save to bookmark-save-flag in bindings to nil.
;;       Use bmkp-count-multi-mods-as-one-flag for the binding.
;;       Call bmkp-refresh-menu-list.
;; 2012/04/09 dadams
;;     bmkp-bmenu-set-tag-value, bmkp-bmenu-remove-tags, bmkp-bmenu-paste-(add|replace)-tags:
;;       Added nil NO-UPDATE-P arg in calls to bmkp-set-tag-value, bmkp-remove-tags,
;;       bmkp-paste-(add|replace)-tags.
;;     bmkp-bmenu-add-tags-to-marked, bmkp-bmenu-remove-tags-from-marked,
;;       bmkp-bmenu-paste-(add|replace)-tags-to-marked:
;;         Bind bookmark-save to nil around iteration, to inhibit saving until finished.
;;         New arg order for calls to bmkp-(add|remove)-tags.
;;         Pass non-nil NO-UPDATE-P arg to bmkp-paste-(add|replace)-tags.
;; 2012/04/03 dadams
;;     Moved here from bookmark+-1.el: bmkp-face-prop.
;; 2012/03/19 dadams
;;     Added: bmkp-*-mark.
;;     bmkp-bmenu-list-1, bmkp-bmenu-mode-status-help: Use bmkp-*-mark for *.
;; 2012/03/18 dadams
;;     bookmark-bmenu-delete: Remove bookmark from bmkp-modified-bookmarks also.
;;     bmkp-bmenu-list-1: RESET-P resets bmkp-modified-bookmarks also.  Insert modified marks (*).
;;     bmkp-bmenu-refresh-menu-list:
;;       When revert from file: Reset *-marked-bookmarks, *-modified-bookmarks, *-omitted-bookmarks.
;;                              Bind bmkp-bmenu-filter-function to nil for bmkp-refresh-menu-list.
;;     bmkp-bmenu-toggle-show-only-(un)marked:
;;       Save display, so bmkp-bmenu-before-hide-marked-alist is up-to-date.
;;     bmkp-bmenu-mode-status-help: Added legend for markings.
;;     bmkp-bmenu-edit-marked: Use (shallow) copies of bookmarks, not originals.
;;     Added bmkp-save-menu-list-state to Bookmark+ menu.
;; 2012/03/13 dadams
;;     bmkp-bmenu-read-filter-input:
;;       If C-g then restore previous display.
;;       Use only one catch and test while condition.
;;       Do not try to pop an empty list.
;;     bmkp-bmenu-filter-((bookmark|file)-name|annotation|tags)-incrementally:
;;       Use run-with-idle-timer, not run-with-timer
;; 2012/03/11 dadams
;;     Added Revert to Saved (bmkp-revert-bookmark-file) to menu.
;; 2012/03/07 dadams
;;     bmkp-bmenu-load-marked-bookmark-file-bookmarks: Use bmkp-sorted-alist to load in display order.
;; 2012/03/06 dadams
;;     bookmark-bmenu-mode: Reorg.
;;     bmkp-bmenu-refresh-menu-list:
;;       Call bmkp-refresh-menu-list also when revert file.  Use yes-or-no-p, not y-or-n-p.
;; 2012/03/05 dadams
;;     bmkp-bmenu-mode-status-help: Added Autosave bookmarks and Autosave list display to info at top.
;; 2012/03/04 dadams
;;     Added: bmkp-bmenu-load-marked-bookmark-file-bookmarks.
;;     Bind bmkp-toggle-saving-menu-list-state to C-M-~, not M-l.
;;     Bind bmkp-bmenu-load-marked-bookmark-file-bookmarks to M-l.  Add it to menu.
;; 2012/03/02 dadams
;;     bookmark-bmenu-list: Reset marked and omitted lists to () if a name is not a current bmk.
;; 2012/02/28 dadams
;;     Added face bmkp-file-handler.
;;     bmkp-bmenu-mode-status-help: Added bmkp-file-handler to face legend.
;;     bmkp-bmenu-propertize-item: Propertize file-handler bookmarks, with bmkp-file-handler.
;; 2011/12/31 dadams
;;     Define macro with-buffer-modified-unmodified for Emacs 23.1, in addition to Emacs < 23.
;; 2011/12/30 dadams
;;     Added aliases: bmkp-bookmark-(data|name)-from-record.
;;     Added: bmkp-bmenu-show-or-edit-annotation, bmkp-bmenu-edit-bookmark-record,
;;            bmkp-bmenu-edit-marked.
;;     Renamed bmkp-bmenu-edit-bookmark to bmkp-bmenu-edit-bookmark-name-and-file.
;;     bookmark-bmenu-mark: Propertize bookmark name with bmkp-full-record before adding to list.
;;     bookmark-bmenu-list:
;;       Added optional arg MSGP.  Show status messages.
;;       Propertize bookmark names if not already propertized, in marked and omitted lists.
;;     bookmark-bmenu-mode: Updated doc string.
;;     bmkp-bmenu-make-sequence-from-marked:
;;       Use bmkp-get-bookmark-in-alist, not bookmark-get-bookmark.
;;     Bind bmkp-bmenu-show-or-edit-annotation (not *-show-annotation) to a.
;;     Bind bmkp-bmenu-edit-bookmark-name-and-file to r now, not E.
;;     Bind bmkp-bmenu-edit-marked to E and T > e.
;;     Bind bmkp-bmenu-edit-bookmark-record to e.
;;     bmkp-bmenu-quit: Show progress messages.
;;     bmkp-bmenu-tags-menu: Added bmkp-bmenu-edit-marked.
;;     bmkp-bmenu-mouse-3-menu:
;;       Added: bmkp-bmenu-edit-tags.
;;       Replaced *-rename and *-relocate with bmkp-bmenu-edit-bookmark-name-and-file.
;; 2011/12/24 dadams
;;     Added: bookmark-bmenu-toggle-filenames, with optional arg NO-MSG-P.
;;     bookmark-bmenu-surreptitiously-rebuild-list, bookmark-bmenu-(show|hide)-filenames:
;;       Added progress messages and optional arg NO-MSG-P.
;;     bookmark-bmenu-(show|hide)-filenames, bookmark-bmenu-toggle-filenames:
;;       Correct FORCE behavior and doc strings.
;;     bmkp-bmenu-refresh-menu-list: Pass (not) MSG-P to bmkp-refresh-menu-list.
;; 2011/12/21 dadams
;;     Added: bmkp-bmenu-mark-orphaned-local-file-bookmarks,
;;            bmkp-bmenu-show-only-orphaned-local-files, bmkp-bmenu-mark-variable-list-bookmarks.
;;     bmkp-bmenu-refresh-menu-list: Added optional args ARG and MSGP, so you can revert from file.
;;     bookmark-bmenu-mode: Updated and reordered doc string.
;;     Bind O M, O S to orphaned commands, not omit commands.  Changed omit bindings to use -, not O.
;;     Bind bmkp-bmenu-mark-variable-list-bookmarks to V M.
;;     bmkp-bmenu-show-menu: Reordered.  Added: *-w3m-urls, *-variable-lists, *-orphaned-local-files.
;;     bmkp-bmenu-mark-menu: Reordered.  Added: *-w3m-*, *-variable-list-*, *-orphaned-local-file-*.
;; 2011/12/19 dadams
;;     Added: with-buffer-modified-unmodified.
;;     bookmark-bmenu-((un)mark|delete), bookmark-bmenu-(show|hide)-filenames:
;;       Use with-buffer-modified-unmodified.
;;     bookmark-bmenu-show-filenames, bmkp-bmenu-mouse-3-menu: Use line-(beginning|end)-position.
;; 2011/12/15 dadams
;;     bmkp-bmenu-propertize-item: Use bmkp-local-directory face also for Dired (e.g. with wildcards).
;;     bmkp-bmenu-mode-status-help: Clarify legend for remote and local dirs/Dired.
;; 2011/12/08 dadams
;;     bmkp-bmenu-mouse-3-menu: Use easymenu to build the menu.  Conditionalize some items.
;;     Bind down-mouse-3, not mouse-3, to bmkp-bmenu-mouse-3-menu.  (bind mouse-3 to ignore).
;;     Added eval-when-compile for easymenu.el.
;; 2011/12/05 dadams
;;     bmkp-bmenu-menubar-menu: Reordered items regarding bookmark files.
;;     bmkp-bmenu-mode-status-help: Correct intro text, reorder, use marker for position TOP.
;;     bookmark-bmenu-mode: Changed intro text slightly.
;; 2011/12/03 dadams
;;     bmkp-bmenu-list-1: Print current bookmark file at top of display.
;;     Increased bmkp-bmenu-header-lines to 5.
;;     bookmark-bmenu-mode: Updated doc string for binding changes and new option.
;;     bmkp-bmenu-regexp-mark: Mention right-padding of bookmark names in doc string.
;;     bmkp-bmenu-mode-status-help: Reorder Current Status items, to put bookmark file first.
;;     Bind L to bmkp-switch-bookmark-file-create, not bmkp-switch-bookmark-file.
;; 2011/11/19 dadams
;;     bmkp-bmenu-image-bookmark-icon-file: Default to an existing Emacs image file, not nil.
;; 2011/11/18 dadams
;;     Added: bmkp-bmenu-mark-image-bookmarks, bmkp-bmenu-show-only-image-files,
;;            bmkp-bmenu-image-bookmark-icon-file.
;;     bmkp-bmenu-list-1: Show icon image for image-file bookmarks.
;;     bookmark-bmenu-mode: Add to doc string: bmkp-image-jump, bmkp-bmenu-mark-image-bookmarks,
;;                                             bmkp-bmenu-show-only-image-files.
;;     bmkp-bmenu-mode-status-help: Added image icon to legend.
;;     Bound keys: M-I M-M, M-I M-S to *-mark-image-bookmarks *-show-only-image-files.
;;     Added to menus (Mark, Show): bmkp-bmenu-mark-image-bookmarks, bmkp-bmenu-show-only-image-files.
;; 2011/11/01 dadams
;;     bookmark-bmenu-mode: Changed mode-name var for mode line: Bookmarks, not Bookmark Menu.
;;                          Updated doc string for autofile & temporary jump commands.
;; 2011/10/31 dadams
;;     bookmark-bmenu-mode: Updated doc string with bmkp-toggle-autotemp-on-set.
;;     bmkp-bmenu-menubar-menu: Added: bmkp-toggle-autotemp-on-set.
;; 2011/10/27 dadams
;;     Added: bmkp-X-mark, bmkp-bmenu-toggle-marked-temporary/savable, bmkp-bmenu-toggle-temporary,
;;            bmkp-bmenu-mark-autonamed-bookmarks, bmkp-bmenu-show-only-temporary,
;;            bmkp-bmenu-mark-temporary-bookmarks.
;;     bmkp-bmenu-list-1: Mark with X in place of a, if bookmark is temporary.
;;     bookmark-bmenu-mode: Mode-line major-mode name indicates when in temporary bookmarking mode.
;;                          Updated doc string with temporary bookmark commands.
;;     bmkp-t-mark: Changed default attributes.
;;     Bind: M-L to bmkp-temporary-bookmarking-mode, M-X to bmkp-bmenu-toggle-marked-temporary/savable
;;           X M to bmkp-bmenu-mark-temporary-bookmarks, X S to bmkp-bmenu-show-only-temporary,
;;           C-M-X to bmkp-bmenu-toggle-temporary.
;;     bmkp-bmenu-show-only-bookmark-files: Bind to Y S, not X S.
;;     bmkp-bmenu-mark-bookmark-file-bookmarks: Bind to Y M, not X M.
;; 2011/07/01 dadams
;;     bmkp-bmenu-change-sort-order, bmkp(-multi)-reverse-sort-order: Handle null CURRENT-BMK.
;; 2011/04/24 dadams
;;     Added to Tags menu: Purge Autofiles with No Tags.
;; 2011/04/23 dadams
;;     Bound bmkp-bmenu-set-tag-value-for-marked to T > v and added to bmkp-bmenu-tags-menu.
;;     bmkp-bmenu-mouse-3-menu: Added bmkp-rename-tag.
;; 2011/04/22 dadams
;;     Bound *-copy-tags to T c, T M-w, *-paste(-add|replace)-tags to T p, T C-y, T q.
;; 2011/04/21 dadams
;;     Added:  bmkp-bmenu-copy-tags, bmkp-bmenu-paste-add-tags(-to-marked),
;;             bmkp-bmenu-paste-replace-tags(-for-marked).
;;     Bound and added to menus: bmkp-bmenu-paste-add-tags-to-marked,
;;                               bmkp-bmenu-paste-replace-tags-for-marked.
;;     Added to This Bookmark menu: bmkp-bmenu-copy-tags, bmkp-bmenu-paste(-add|replace)-tags.
;; 2011/04/19 dadams
;;     Added: bmkp-bmenu-unmark-bookmarks-tagged-regexp.  Bound it to T u %.  Added it to menu.
;; 2011/04/16 dadams
;;     Added: bmkp-edit-tags-send.  Bound it to T e in bookmark-bmenu-mode-map.
;;     bookmark-bmenu-mode: Updated help text for tags editing.
;;     bmkp-maybe-unpropertize-bookmark-names:
;;       Test emacs-major-version, not just (boundp 'print-circle).
;; 2011/04/15 dadams
;;     Added: bmkp-bmenu-mark-autofile-bookmarks, bmkp-bmenu-show-only-autofiles.
;;       And added them to menus.
;;     bookmark-bmenu-mode-map:
;;       Bind bmkp-bmenu-mark-autofile-bookmarks, bmkp-bmenu-show-only-autofiles to A M, A S.
;;       Bind bookmark-bmenu-show-all-annotations to M-a, not A.
;;       Bind bmkp-bmenu-search-marked-bookmarks-regexp to M-s a M-s, not M-a.
;;       Bind *-mark-url-bookmarks, *-show-only-urls to M-u M-m, M-u M-s, not M-u M, M-u S.
;;     bookmark-bmenu-mode: Updated help to reflect latest bindings.
;; 2011/04/13 dadams
;;     bmkp-bmenu-tags-menu: Added: bmkp-(un)tag-a-file.
;; 2011/04/12
;;     Added: bmkp-propertize-bookmark-names-flag, bmkp-maybe-unpropertize-bookmark-names,
;;            bmkp-bmenu-get-marked-files.
;;     Renamed: bmkp-bmenu-omitted-list to bmkp-bmenu-omitted-bookmarks.
;;     bmkp-bmenu-define-full-snapshot-command:
;;       Bind print-circle to t around pp.  Use bmkp-maybe-unpropertize-bookmark-names on lists.
;;     bookmark-bmenu-(show|hide)-filenames, bmkp-bmenu-toggle-show-only-(un)marked,
;;       bmkp-bmenu-(un)omit-marked:
;;         Fit one-window frame only if selected window is *Bookmark List*.
;;     bookmark-bmenu-bookmark: Added optional arg FULL.  Non-nil means return full bookmark record.
;;     bookmark-bmenu-unmark, bookmark-bmenu-delete, bmkp-bmenu-unomit-marked:
;;       Use bmkp-delete-bookmark-name-from-list, not delete.
;;     bookmark-bmenu-execute-deletions: Pass full bookmark, not name, to delete, and don't use assoc.
;;     bookmark-bmenu-rename: Use bmkp-bmenu-goto-bookmark-named instead of just searching for name.
;;     bmkp-bmenu-toggle-marks, bmkp-bmenu-unomit-marked, bmkp-bmenu-define-jump-marked-command,
;;       bmkp-bmenu-mouse-3-menu:
;;         Use bmkp-bookmark-name-member, not member.
;;     bmkp-bmenu-make-sequence-from-marked: Do not invoke bookmark-bmenu-list when no displayed list.
;;     bmkp-bmenu-define-command: Use bmkp-maybe-unpropertize-bookmark-names on *-omitted-bookmarks.
;;     bmkp-bmenu-list-1: Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;;                        Pass full bookmark to bmkp-bmenu-propertize-item.
;;     bmkp-bmenu-propertize-item:
;;       First arg is now a full bookmark, not a bookmark name.  Get bookmark name from it.
;;       Put prop bmkp-bookmark-name on buffer text with propertized bookmark-name string as value.
;;       String has property bmkp-full-record with value the full bookmark record, with string as car.
;;       Return propertized bookmark-name string.
;;     bmkp-bmenu-isearch-marked-bookmarks(-regexp), bmkp-bmenu-dired-marked,
;;       bmkp-bmenu-(search|query-replace)-marked-bookmarks-regexp:
;;         Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;;     bmkp-bmenu-goto-bookmark-named:
;;       If NAME has property bmkp-full-record then go to the bookmark it indicates.  Otherwise, just
;;       go to the first bookmark with the same name.
;;     bookmark-bmenu-mode: Added bmkp-save-menu-list-state (now a command) to the mode help.
;; 2011/04/02 dadams
;;     bookmark-bmenu-mode: Added to mode help: bmkp-file-this-dir-(all|some)-tags(-regexp)-jump.,
;;                                              Create/Set section, with bmkp-autofile-set.
;; 2011/04/01 dadams
;;     bookmark-bmenu-mode: Added to mode help: bmkp-(dired|file)-this-dir-jump.
;; 2011/03/26 dadams
;;     bookmark-bmenu-mode: Added new file-with-tags jump commands to the help.
;; 2011/03/05 dadams
;;     bmkp-bmenu-edit-bookmark: Use bmkp-refresh-menu-list, not *-surreptitiously-rebuild-list.
;; 2011/02/11 dadams
;;     Faces: Better defaults for dark background.
;; 2011/01/03 dadams
;;     Removed autoload cookies from non def* sexps and from define-key.
;;     Added missing autoload cookies for commands, in particular redefined std commands & defalias.
;; 2010/12/10 dadams
;;     Added defalias for bookmark-name-from(-full)-record, to fix gratuitous Emacs name change.
;; 2010/09/24 dadams
;;     Added: bmkp-bmenu-show-only-autonamed.  Bound to # S.  Added to bmkp-bmenu-show-menu.
;;     bookmark-bmenu-mode: Updated doc string for autonamed jumps, show.
;;     Renamed varlist to variable-list everywhere.
;; 2010/08/22 dadams
;;     Added: bmkp-bmenu-filter-annotation-incrementally, bookmark-bmenu-relocate (Emacs 20, 21),
;;            bmkp-bmenu-filter-alist-by-annotation-regexp.  Bound, added to menus and help.
;; 2010/08/18 dadams
;;     Removed eval-when-compile for bookmark+-(lit|1).el.
;;     bmkp-bmenu-propertize-item: Inconsequential simplification.
;; 2010/08/17 dadams
;;     bmkp-bmenu-edit-bookmark: Added optional arg INTERNALP (prefix arg), for editing record.
;; 2010/08/15 dadams
;;     Moved to bookmark+-mac.el:
;;       bmkp-define-sort-command, bmkp-replace-regexp-in-string, bmkp-assoc-delete-all.
;;     Renamed: bmkp-barf-if-not-in-menu-list to bmkp-bmenu-barf-if-not-in-menu-list.
;;     Require bookmark.el, bookmark+-mac.el.
;;     Require when compile: bookmark+-1.el, bookmark+-lit.el (soft).
;; 2010/07/17 dadams
;;     Added: bmkp-bmenu-mark-url-bookmarks, bmkp-bmenu-show-only-urls, bmkp-bmenu-sort-by-url.
;;     Removed: bmkp-bmenu-sort-by-w3m-url.
;;     Replaced face bmkp-w3m by bmkp-url.
;;     bookmark-bmenu-mode: Added mark and show URL commands.
;;     bookmark-bmenu-mode, *-status-help, *-sort-by-bookmark-type, *-define-sort-command: w3m -> url.
;;     Bind bmkp-bmenu-sort-by-url, not bmkp-bmenu-sort-by-w3m-url.
;;     Bind bmkp-bmenu-mark-url-bookmarks, bmkp-bmenu-show-only-urls.
;;     Replace W3M by URL in menu items.
;; 2010/07/14 dadams
;;     Created from bookmark+.el code.
 
;;;(@* "CHANGE LOG FOR `bookmark+-key.el'")
;;
;; 2017/10/14 dadams
;;     All EWW stuff is for Emacs 25+, not Emacs 24.4+.
;; 2017/01/10 dadams
;;     Applied renaming: bmkp-replace-eww-keys-flag to bmkp-eww-replace-keys-flag.
;; 2017/01/02 dadams
;;     menu-bar-bookmark-map: Added menu item Store Org Link To....
;;     Typo: bmkp-replace-EWW-keys-flag -> bmkp-replace-eww-keys-flag.
;; 2016/12/11 dadams
;;     Remap EWW keys to bmkp- keys.
;; 2016/11/23 dadams
;;     Put :advertised-binding on several keys.
;; 2016/11/15 dadams
;;     bmkp-eww-jump(-other-window): Ensure that EWW code is only for Emacs 25+.
;; 2016/11/14 dadams
;;     Added bindings for bmkp-eww-jump(-other-window), including in eww-mode-map.
;;     Bind bmkp-delete-bookmarks to kill-line keys (C-x p C-k, C-x p deleteline).
;; 2016/06/24 dadams
;;     Added bmkp-delete-bookmarks binding for <deletechar> and <kp-delete>.
;; 2016/05/15 dadams
;;     dired-mode-hook:
;;       If diredp-bookmark-menu is defined then use that.
;;       Rename menu item: Show This Dir Using a Bookmark -> Jump to a Dired Bookmark For This Dir.
;; 2016/05/08 dadams
;;     Added: bmkp-bookmark-map-prefix-key, bmkp-jump-map-prefix-key,
;;            bmkp-jump-other-window-map-prefix-key, bmkp-set-map-prefix-key.
;;     Removed hard-coded bindings for keymaps in ctl-x-map, ctl-x-4-map.
;;     (eval-when-compile (require 'cl)) ;; case
;; 2015/01/04 dadams
;;     Bind bmkp-region-jump-narrow-indirect-other-window to C-x 4 j R.
;; 2014/07/11 dadams
;;     bmkp-highlight-menu: Added item Toggle Autofile Highlighting in Dired.
;; 2014/07/06 dadams
;;     Removed: bmkp-options-menu.  Use bmkp-bmenu-toggle-menu, and rename Toggle, not Toggle Option.
;;     Removed individual toggle commands from menu-bar-bookmark-map (Bookmarks).
;;     Reuse bmkp-bmenu-toggle-menu for menu-bar-bookmark-map [options].
;; 2014/07/05 dadams
;;     Moved submenu bmkp-jump-tags-menu before individual menu items.
;; 2014/03/23 dadams
;;     Bind j and J in bookmark-bmenu-mode-map.  Bind also j > there.
;;     Add bmkp-bmenu-jump-to-marked to bmkp-jump-menu when in bookmark-list display.
;; 2013/10/29 dadams
;;     Bind bookmark-set's previous keys to bmkp-bookmark-set-confirm-overwrite.
;;     Bind bookmark-set to C-x r M, not C-x r m.
;;     bmkp-menu-bar-set-bookmark: Use bmkp-bookmark-set-confirm-overwrite, not bookmark-set.
;; 2013/07/20 dadams
;;     Moved items to new submenus: New/Update and Delete.
;; 2013/06/30 dadams
;;     Bind bmkp-set-snippet-bookmark to C-x p M-w, bmkp-snippet-to-kill-ring to C-x j M-w.
;; 2013/05/28 dadams
;;     Applied renaming of bmkp-edit-bookmark-name-and-file to bmkp-edit-bookmark-name-and-location.
;; 2013/04/15 dadams
;;     In bmkp-set-map: Bind F to bmkp-make-function-bookmark (C-x p c F).
;;                      Bind C-k to bmkp-wrap-bookmark-with-last-kbd-macro (C-x p c C-k).
;;                      Bind s to bmkp-set-sequence (C-x p c s).
;; 2012/08/31 dadams
;;     Do not bind bmkp-compilation-target-set(-all) unless defined.
;; 2012/06/26 dadams
;;     Wrapped require of bookmark+-mac.el in eval-when-compile.
;; 2012/06/21 dadams
;;     Try to load-library bookmark+-mac, for bmkp-menu-bar-make-toggle.
;; 2012/02/26 dadams
;;     Bind:
;;       bmkp-this-file/buffer-bmenu-list to C-x p , not C-x p ..
;;       bmkp-(file|dired)-this-dir-jump* to C-x j . f|d not C-x j C-f|C-d.
;;       bmkp-file-this-dir-*-tags(-regexp)-jump* to C-x j t . [%][*+] not C-x j t C-f [%][*+].
;;       bmkp-this-buffer-jump* to C-x j , , not C-x j ..
;;       bmkp-autonamed-this-buffer-jump* to C-x j , # not C-x j # ..
;;       bmkp-autonamed-jump* to C-x j # not C-x j # #.
;;       bmkp-autofile-jump* in all Emacs versions.
;;       bmkp-find-file(-other-window), which is new, to C-x j C-f.
;;       new autofile tags jump commands bmkp-autofile-(all|some)-tags(-regexp)-jump* to
;;         C-x j t a [%][*+], which was for bmkp-find-file-*-tags*.
;;       bmkp-find-file-(all|some)-tags(-regexp)* to C-x j t C-f [%] [*+] not C-x j t a [%] [*+].
;;     Add to menus: bmkp-autofile-*.  Rename menu items for bmkp-find-file: Find Autofile....
;;     Rename menu Bookmarked File to Find File or Autofile.  For Emacs 20-21, make it a single item.
;;     bmkp-jump-tags-menu, bmkp-find-file-menu: Do not add Autofile tags items for Emacs 20.
;; 2012/02/21 dadams
;;     Added bindings for: bmkp-autofile-(all|some)-tags(-regexp)-jump(-other-window),
;;                         bmkp-find-file(-other-window) (was same as *autofile*).
;;     Changed bindings:
;;       *-this-dir*: . [df] (was C-d/C-f), *this-buffer*: , (was .), *find-file*tags*: C-f (was a).
;;     Define *autofile* for all Emacs versions.  Separate bindings from *find-file* cmds.
;; 2011/12/30 dadams
;;     Added aliases: bmkp-bookmark-(data|name)-from-record.
;;     Bind E to bmkp-edit-bookmark-record, not bmkp-edit-bookmark.
;;     Bind r to bmkp-edit-bookmark-name-and-file, not bookmark-rename.  Ditto in menu.
;;     Use bmkp-get-bookmark-in-alist, not bookmark-get-bookmark in :visible conditions.
;;     menu-bar-bookmark-map: Added bmkp-edit-bookmark-record.
;;     bmkp-tags-menu: Added bmkp-edit-tags.
;; 2011/12/14 dadams
;;     Removed conditions :enable bookmark-alist.
;; 2011/12/09 dadams
;;     Commented out menu items with complex :enable conditions, replacing them with simple ones.
;;       Reason: too slow, especially in Emacs 20.
;; 2011/12/05 dadams
;;     menu-bar-bookmark-map: Reordered items regarding bookmark files.
;; 2011/12/03 dadams
;;     Bind C-x p L to bmkp-switch-bookmark-file-create, not bmkp-switch-bookmark-file.
;;     Reordered bookmark-file items in menu-bar-bookmark-map.
;; 2011/11/18 dadams
;;     Bind bmkp-image-jump(-other-window) to C-x (4) j M-i.
;;     bmkp-jump-menu: Add bmkp-image-jump-other-window.
;; 2011/11/15 dadams
;;     Bind *-this-file/buffer*, not *-this-buffer*.
;; 2011/11/01 dadams
;;     Bind alias bmkp-autofile-jump(-*), not bmkp-find-file(-*) to C-x j a, so Icicles picks up key.
;;     Bind bmkp-bookmark-file-jump to C-x j y, not C-x j x.  Bind bmkp-temporary-jump(-*) to C-x j x.
;;     bmkp-jump-menu: Bind bmkp-(autofile|temporary)-jump-other-window.
;; 2011/10/31 dadams
;;     Bind bmkp-toggle-autotemp-on-set to C-x p x.  Move bmkp-set-bookmark-file-bookmark to C-x p y.
;;     menu-bar-bookmark-map: Added: bmkp-toggle-autotemp-on-set.
;; 2011/10/28 dadams
;;     menu-bar-bookmark-map:
;;       Added: bmkp-delete-all-temporary-bookmarks, bmkp-temporary-bookmarking-mode.  Reordered.
;;     bmkp-options-menu: Added: bmkp-toggle-saving-menu-list-state, bmkp-toggle-saving-bookmark-file.
;; 2011/04/24 dadams
;;     Added to Bookmarks menu and its Tags submenu: Purge Autofiles with No Tags.
;; 2011/04/23 dadams
;;     bmkp-tags-menu:
;;       Added bmkp-set-tag-value, bmkp-(add|remove|copy)-tags, bmkp-paste-(add|replace)-tags.
;; 2011/04/21 dadams
;;     Bound: bmkp-copy-tags, bmkp-paste-add-tags, bmkp-paste-replace-tags.
;; 2011/04/16 dadams
;;     Added: bmkp-tags-map.  Bound tag commands to prefix C-x p t.
;; 2011/04/14 dadams
;;     Renamed menu Jump To Bookmark to just Jump To, in menu-bar-bookmark-map.
;; 2011/04/13 dadams
;;     Added:
;;       bmkp-find-file-menu (bmkp-find-file(-(all|some)-tags(-regexp)(-other-window)),
;;       bmkp-jump-tags-menu (what was in main, plus bmkp-find-file-*-tags-regexp*),
;;       bmkp-tags-menu (list all, rename, remove from all, (un)tag a file).
;;     bmkp-jump(-other-window)-map:
;;       Added bmkp-find-file(-other-window) to menu.
;;       Bound keys for bmkp-find-file-(all|some)-tags(-regexp)(-other-window): C-x (4) j t a...
;; 2011/04/02 dadams
;;     Added bindings for (new) bmkp-autofile-set,
;;                              bmkp-file-this-dir-(all|some)-tags(-regexp)-jump(-other-window).
;; 2011/04/01 dadams
;;     Added to bmkp-jump-menu: bmkp-(dired|file)-this-dir-jump-other-window.
;;     Created from code in bookmark+-1.el.
 
;;;(@* "CHANGE LOG FOR `bookmark+-lit.el'")
;;
;; 2017/01/08 dadams
;;     Use the term "entry", not "property" everywhere, for bookmark entries (fields).
;; 2016/10/25 dadams
;;     Added: Faces bmkp-light-autonamed-region, bmkp-light-non-autonamed-region.
;;            Options bmkp-light-style-autonamed-region, bmkp-light-style-non-autonamed-region.
;;     bmkp-light-styles-alist: Added Region style.
;;     bmkp-make/move-overlay-of-style:
;;       Added required arg BOOKMARK.  Put overlay on region if region bookmark.
;;     bmkp-light-bookmark, bmkp-light-bookmarks:
;;       Include newly added bookmark arg in calls to bmkp-make/move-overlay-of-style.
;;     bmkp-light-face: Use face bmkp-light(-non)-autonamed-region for region bookmarks.
;;     bmkp-light-style: Use style bmkp-light-style(-non)-autonamed-region for region bookmarks.
;; 2016/09/10 dadams
;;     bmkp-light-face, bmkp-light-style: Use bmkp-autonamed-bookmark-p.
;; 2016/06/18 dadams
;;     Protected use of fringe-bitmaps with boundp (should not be necessary though).
;; 2015/04/02 dadams
;;     eval-when-compile require of bookmark+-mac, for bmkp-define-show-only-command.
;; 2015/02/08 dadams
;;     Renamed: bmkp-bmenu-show-only-lighted to bmkp-bmenu-show-only-lighted-bookmarks.
;;     bmkp-bmenu-show-only-lighted-bookmarks: Use macro bmkp-define-show-only-command to define it.
;; 2014/07/06 dadams
;;     Added: bmkp-last-auto-light-when-jump, bmkp-last-auto-light-when-set,
;;            bmkp-toggle-auto-light-when-jump, bmkp-toggle-auto-light-when-set.
;; 2013/06/09 dadams
;;     Added vacuous defvars to suppress free-var warnings.
;; 2013/05/15 dadams
;;     Use bmkp-string-match-p instead of string-match wherever appropriate.
;; 2012/10/09 dadams
;;     Made all autoload cookies explicitly load bookmark+.el(c).  Should help ELPA (e.g. MELPA).
;; 2012/09/22 dadams
;;     bmkp-light-bookmark(s): Put full bookmark, not name, on overlay as its bookmark property.
;;     bmkp-unlight-bookmark: Test using eq against full bookmark, not using equal against name.
;;     bmkp-a-bookmark-lighted-at-pos: overlay-get now returns full bookmark, so get name if needed.
;;     bmkp-overlay-of-bookmark: Use bookmark, not its name, like overlay-get does now.  Test with eq.
;;     bmkp-light-bookmarks: Use add-to-list instead of unconditionally adding ov to ov-symb.
;; 2012/04/28 dadams
;;     bmkp-make/move-overlay-of-style, bmkp-make/move-fringe: Use FRONT-ADVANCE arg for make-overlay.
;; 2011/12/30 dadams
;;     Added aliases: bmkp-bookmark-(data|name)-from-record.
;;     bmkp-bookmarks-lighted-at-point: Include only bookmarks in bookmark-alist.
;;     bmkp-light-bookmark: Do nothing if BOOKMARK is not a bookmark or bookmark name.
;;     bmkp-a-bookmark-lighted-at-pos: Return nil if no bookmark (at POS) in bookmark-alist.
;; 2011/11/15 dadams
;;     Applied renaming: bmkp-this-buffer-cycle-sort-comparer to *-this-file/buffer*.
;; 2011/08/09 dadams
;;     Bind icicle-unpropertize-completion-result-flag to t for all calls to completing-read.
;; 2011/04/12
;;     bmkp-cycle-lighted-this-buffer: Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;; 2011/04/01 dadams
;;     bmkp-light-bookmark(s): Don't call bookmark-handle-bookmark.  Wrap with with-current-buffer.
;; 2011/01/03 dadams
;;     Added autoload cookies: defcustoms and commands.
;; 2010/12/10 dadams
;;     Added defalias for bookmark-name-from(-full)-record, to fix gratuitous Emacs name change.
;; 2010/09/25 dadams
;;     Added: bmkp-set-lighting-for(bookmarks|(-this)-buffer).  Requested by Joe Bloggs.
;;     bmkp-set-lighting-for-bookmark: Added LIGHT-NOW-P arg (from prefix arg).
;; 2010/09/11 dadams
;;     Removed eval-when-compile for bookmark+-bmu, bookmark+-1.
;; 2010/08/15 dadams
;;     Require: bookmark.el.
;;     Require when compile: bookmark+-bmu.el, bookmark+-1.el, pp+.el (soft).
;;     Applied renaming of bmkp-barf-if-not-in-menu-list to bmkp-bmenu-barf-if-not-in-menu-list.
;;     bmkp-light-bookmark(s): Added missing arg to throw call.
;;     bmkp-light-bookmarks: Use bmkp-remove-if, not remove-if.
;;     bmkp-light-bookmarks-in-region, bmkp-light-non-autonamed-this-buffer:
;;       Use bmkp-remove-if-not, not remove-if-not.
;;     bmkp-read-set-lighting-args: Use pp-read-expression-map only if bound (pp+.el).
;; 2010/07/03 dadams
;;     bmkp-set-lighting-for-bookmark, bmkp-bmenu-set-lighting-for-marked:
;;       Use *-refresh-menu-list, not *-surreptitiously-*.
;; 2010/07/01 dadams
;;     Created.
 
;;;(@* "CHANGE LOG FOR `bookmark+-mac.el'")
;;
;; **************************************************************************************************
;; NOTE: If you byte-compile Bookmark+ (recommended), then WHENEVER `bookmark+-mac.el' is updated,
;;       you      must load `bookmark+-mac.el' (not just `bookmark+-mac.elc'), then compile it, then
;;       RECOMPILE *ALL* of the other Bookmark+ source files as well.  This is normal for Lisp: code
;;       that depends on macros needs to be byte-compiled anew after loading the updated macros.
;; **************************************************************************************************
;;
;; 2017/03/31 dadams
;;     bmkp-define-next+prev-cycle-commands: Added optional arg OTHERP.
;; 2015/04/03 dadams
;;     bmkp-replace-regexp-in-string: Copied defn here - used to produce the macro code for
;;       bmkp-define-show-only-command and bmkp-define-sort-command.
;; 2015/02/22 dadams
;;     bmkp-menu-bar-make-toggle: Corrected doc string - just start with HELP.
;; 2015/02/08 dadams
;;     Added: bmkp-define-show-only-command.
;; 2014/07/11 dadams
;;     bmkp-define-sort-command: Use setq, not push, for Emacs 20.
;; 2014/07/06 dadams
;;     bmkp-menu-bar-make-toggle: Redefined - no longer use menu-bar-make-toggle.  Support keywords.
;; 2014/05/27 dadams
;;     Added: bmkp-with-help-window.
;; 2013/04/26 dadams
;;     Added: bmkp-with-bookmark-dir.  (Not used currently.  For user code.)
;; 2012/10/09 dadams
;;     Made all autoload cookies explicitly load bookmark+.el(c).  Should help ELPA (e.g. MELPA).
;; 2012/06/26 dadams
;;     Moved bmkp-assoc-delete-all, bmkp-replace-regexp-in-string to bookmark+-bmu.el.
;; 2012/04/27
;;     Added: bmkp-with-output-to-plain-temp-buffer.
;; 2012/04/12 dadams
;;     bmkp-define-sort-command: Do not bmkp-bmenu-goto-bookmark-named unless current-bmk (play safe).
;; 2012/04/11 dadams
;;     bmkp-define-sort-command: In function def, change order to: fn, reverse-fn, unsorted.
;; 2011/12/30 dadams
;;     bmkp-define-cycle-command: Applied renaming of bmkp-sort-and-remove-dups to bmkp-sort-omit.
;;     bmkp-define-file-sort-predicate: Updated doc string of generated functions.
;;     Added renamings of bookmark-name-from(-full)-record, bookmark-get-bookmark-record.
;; 2011/04/12
;;     bmkp-define-cycle-command: Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;; 2011/01/03 dadams
;;     Added autoload cookies: defmacro.
;; 2010/09/25 dadams
;;     Added: bmkp-define-next+prev-cycle-commands.
;; 2010/09/24 dadams
;;     Added: bmkp-define-cycle-command.
;; 2010/08/18 dadams
;;     Removed eval-when-compile for bookmark+-(bmu|1).el.
;; 2010/08/15 dadams
;;     Created, from code in other Bookmark+ files.
 
;;;(@* "CHANGE LOG FOR `bookmark+.el'")
;;
;; 2017/03/31 dadams
;;     Version 2017.03.31.  Fixed cycling bookmarks across buffers.  Added other-window cycling cmds.
;; 2017/02/26 dadams
;;     Version 2017.02.26.  Added auto-bookmarking for Info.  Better EWW - thx to Charles Roelli.
;; 2016/11/14 dadams
;;     Version 2016.11.14.  Added support for EWW bookmarks.  Thx to Charles Roelli.
;; 2015/02/22 dadams
;;     Version 2015.02.22.
;; 2015/02/08 dadams
;;     Version 2015.02.08
;; 2015/01/04 dadams
;;     Version 2015.01.04.
;; 2013/04/14 dadams
;;     Added Version entry to header.  Updated bmkp-version-number to the same thing.
;; 2012/10/09 dadams
;;     Made all autoload cookies explicitly load bookmark+.el(c).  Should help ELPA (e.g. MELPA).
;; 2012/06/26 dadams
;;     Wrapped require of bookmark+-mac.el in eval-when-compile.
;; 2012/06/21 dadams
;;     Try to load-library bookmark+-mac.  Require it only if cannot load-library.
;; 2012/02/26 dadams
;;     Version 3.4.0.
;; 2011/12/30 dadams
;;     Version 3.3.0.
;; 2011/04/12 dadams
;;     Version 3.2.2.
;; 2011/04/01 dadams
;;     Require bookmark+-key.el (new).  Version 3.2.1.
;; 2011/01/03 dadams
;;     Added autoload cookies: defconst, command.
;; 2010/08/19
;;     bmkp-version-number: Version 3.2.0.
;; 2010/08/15 dadams
;;     Require bookmark+-mac.el.
;;     Do not ensure loaded before compile (not needed here now).
;; 2010/07/14 dadams
;;     Version 3.1.1.
;;     Moved main content of bookmark+.el to new files bookmark+-1.el and bookmark+-bmu.el.
;; 2010/07/13 dadams
;;     Version 3.1.0.
;;     Added redefinitions: bookmark-bmenu-(1|2)-window, bookmark-bmenu-other-window-with-mouse,
;;                          bookmark-bmenu-this-window, bookmark-bmenu-switch-other-window.
;;     Added: bmkp-last-bookmark-file, bmkp-switch-to-last-bookmark-file.
;;     Removed pre-23 version of bookmark-bmenu-switch-other-window.
;;     bookmark-load: Use bmkp-last-bookmark-file when read file name.  Added missing prefix arg.
;;                    Save old current as bmkp-last-bookmark-file.
;;     bookmark-bmenu-list: If bookmark file has changed do not restore state saved from other file.
;;                          Save old current as bmkp-last-bookmark-file.
;;     bmkp-bmenu-list-1: Do not use bmkp-bmenu-title if it is empty ("").
;;     bookmark-bmenu-mode: Added to doc string: bmkp-switch-bookmark-file.
;;     bookmark-bmenu-other-window: Do not bind bookmark-automatically-show-annotations (per vanilla).
;;     bookmark-bmenu-show-annotation: Ensure in bmenu list and on a bookmark line.
;;     bmkp-switch-bookmark-file: Use bmkp-last-bookmark-file when read file name.
;;     bmkp-bmenu-define-full-snapshot-command: Set bmkp-last-bookmark-file.
;;     bmkp-bookmark-description: Fixed typo: bmkp-bookmark-file-bookmark-p (not desktop).
;;     bmkp-make-bookmark-file-record: Use arg file (not bmkp-non-file-filename) as filename entry.
;;
;;     Added more autoload cookies.
;; 2010/07/09 dadams
;;     Added: bmkp-bmenu-mark-bookmark-file-bookmarks, bmkp-bmenu-show-only-bookmark-files,
;;            bmkp-bookmark-file-jump, bmkp-set-bookmark-file-bookmark, bmkp-bookmark-file-history,
;;            bmkp-use-bookmark-file-create, bmkp-bookmark-file, bmkp-bookmark-file-alist-only,
;;            bmkp-bookmark-file-bookmark-p, bmkp-jump-bookmark-file, bmkp-make-bookmark-file-record.
;;     bmkp-types-alist, bmkp-buffer-names, bmkp-bmenu-mode-status-help, bmkp-bmenu-propertize-item,
;;       bmkp-this-buffer-p, bmkp-last-specific-buffer-p, bmkp-specific-buffers-alist-only,
;;       bmkp-bookmark-description, bookmark-bmenu-mode:   Updated for bookmark-file bookmarks.
;;     bookmark--jump-via: Added a catch, so a handler can skip all other processing when it's done.
;;     bookmark-load: Final msg says whether overwritten.
;;     Bound and added to menus: bmkp-set-bookmark-file-bookmark,
;;                               bmkp-bmenu-mark-bookmark-file-bookmarks,
;;                               bmkp-bmenu-show-only-bookmark-files, bmkp-bookmark-file-jump.
;; 2010/07/07 dadams
;;     bookmark-handle-bookmark: Bind use-dialog-box, use-file-dialog to nil.
;;     bookmark-location: From Emacs 23: Use location property and -- Unknown location --.
;;     bmkp-switch-bookmark-file: Bind insert-default-directory to nil.
;;     bmkp-empty-file: Expand FILE.  Return FILE.
;; 2010/07/03 dadams
;;     Added: bmkp-bmenu-describe-marked, bmkp-bookmark-description.
;;     bmkp-describe-bookmark: Rewrote to use bmkp-bookmark-description.
;;     Bound bmkp-bmenu-describe-marked to C-h >.
;;     bmkp-bmenu-menubar-menu: Added bmkp-bmenu-describe-(marked|bookmark).
;;     Updated doc string of bookmark-alist.
;; 2010/07/01 dadams
;;     Added: bmkp-bmenu-mark-lighted-bookmarks, bmkp-bmenu-set-tag-value-for-marked,
;;            bmkp-bmenu-show-only-tagged, bmkp-occur-create-autonamed-bookmarks,
;;            bmkp-set-autonamed-bookmark, bmkp-set-autonamed-bookmark-at-line,
;;            bmkp-set-autonamed-regexp-buffer, bmkp-set-autonamed-regexp-region,
;;            bmkp-set-tag-value-for-navlist, bmkp-prompt-for-tags-flag, bmkp-menu-bar-make-toggle,
;;            bmkp-same-creation-time-p, bmkp-set-tag-value-for-bookmarks,
;;            bmkp(-bmenu)-highlight-menu, bmkp-options-menu.
;;     Renamed: bmkp-use-region-flag to bmkp-use-region,
;;              bmkp-bmenu-jump-menu to bmkp-jump-menu.
;;     Removed: bmkp-cycle-this-buffer-buff (unused).
;;     Soft-require new library bookmark+-lit.el.
;;     Split off new file bookmark+-chg.el from bookmark+-doc.el.
;;     Changed default values of faces bmkp->-mark, bmkp-t-mark.
;;     bmkp-crosshairs-flag: Added :set instead of add-hook at top level.
;;     bmkp-use-region: Changed from boolean to choice - added cycling-too value.
;;     bookmark-set: Added INTERACTIVEP arg.  Prompt for tags when bmkp-prompt-for-tags-flag.
;;                   Auto-highlight when set, per bmkp-auto-light-when-set.
;;     bookmark--jump-via: Auto-highlight when jump, per bmkp-auto-light-when-jump.
;;                         Set BOOKMARK to result of bmkp-update-autonamed-bookmark.
;;                         Bind orig-buff when running hook.
;;     bookmark-default-handler: Pass the bookmark too as an arg to bmkp-goto-position.
;;     bookmark-relocate, bookmark-rename, bmkp-bmenu-list-1, bmkp-remove(-all)-tags, bmkp-add-tags:
;;       Add 0 as FRAME arg to get-buffer-window.
;;     bookmark-delete: Remove any highlighting on bookmark.
;;     bmkp-bmenu-list-1: Add highlight-overrides indicator.
;;     bmkp-completing-read-1: Added (not laxp) guard for first branch of main if.
;;     bmkp-crosshairs-highlight: Assign a priority.  Make the cmd a no-op for Emacs 20-21.
;;     bmkp-choose-navlist-*, bmkp-navlist-bmenu-list, bmkp-jump-in-navlist*,
;;       bmkp-cycle(-this-buffer*):
;;         Set bmkp-current-nav-bookmark to bookmark, not to its name.
;;     bmkp-update-autonamed-bookmark: Do not set bmkp-current-nav-bookmark to the name.
;;                                     Call bmkp-refresh-menu-list even if menu list is not displayed.
;;                                     Pass the bookmark name to bmkp-refresh-menu-list.
;;                                     Return the updated BOOKMARK.
;;     bmkp-refresh-menu-list: Set window point also.
;;     bmkp-goto-position:
;;       Added BOOKMARK arg.  When bmkp-save-new-location-flag, update BOOKMARK.  Return indicator.
;;     bmkp-create-varlist-bookmark: Call bookmark-set with INTERACTIVEP arg.
;;     bmkp-cycle(-this-buffer*): Added STARTOVERP arg. Pass OTHER-WINDOW, STARTOVERP to bmkp-cycle-1.
;;     bmkp-cycle-1: Added STARTOVERP arg.  If non-nil pop-up-frames, then inhibit showing annotation.
;;                   Use region only if bmkp-use-region value is cycling-too.
;;                   Use eq for *-list-position test.  If *-list-position returns nil, then reset.
;;                   Use save-selected-window, unlesl OTHER-WINDOW.
;;     bmkp-(next|previous)-bookmark(-this-buffer|-w32): Added STARTOVERP arg.  C-u: start over at 1.
;;     Bind highlight cmds: *-map: h,H,u,U,C-u,=,C-up|down.  *-bmenu-*map: H+,H>+,H>H,HH,HS,H>U,HU.
;;                          *-jump-map: h.  Bind TS in *-bmenu-*map.
;;     Add bmkp-occur-create-autonamed-bookmarks to occur-mode-map as C-c b.
;;     Menus: Added Highlight, Toggle Option.  Added light to Jump To, Show, Mark, mouse.  Reorder.
;; 2010/06/23 dadams
;;     Split the change log off from file bookmark+-doc.el to new file bookmark+-chg.el.
;; 2010/06/21 dadams
;;     Renamed: bmkp-toggle-autoname-bookmark-set/delete to bmkp-toggle-autonamed-bookmark-set/delete,
;;              bmkp-autonamed-bookmarks-alist-only to bmkp-autonamed-this-buffer-alist-only,
;;              bmkp-bookmark-autoname-p to bmkp-autonamed-bookmark-for-buffer-p,
;;     Added: bmkp-autonamed-alist-only, bmkp-non-autonamed-alist-only, bmkp-autonamed-bookmark-p,
;;     bmkp-completing-read-1: Use DEFAULT as default.  Use just (not lax) - no non-t.
;;                             Use DEFAULT if empty input only if DEFAULT is non-nil.
;;     bmkp-choose-navlist-of-type: Added pseudo-type "any".
;;     bmkp-specific-buffers-alist-only: Exclude desktop etc. bookmarks.
;;     bmkp-update-autonamed-bookmark: Arg can be a bookmark (not just name).
;; 2010/06/19 dadams
;;     RENAMED bookmarkp* TO bmkp*.  ***** THIS IS AN INCOMPATIBLE CHANGE ******
;;
;;       If you have existing customizations, or if you have bookmarks that have the (internal) tag
;;       "bmkp-jump", then YOU MUST REPLACE occurrences of "bookmarkp" by "bmkp" EVERYWHERE.  This
;;       includes replacing occurrences in (1) your bookmarks file (bookmark-default-file), (2) your
;;       state file (bmkp-bmenu-state-file), and (3) your command file (bmkp-bmenu-commands-file).
;;
;;     Changed *-bmenu-w32-open-select binding to M-o from M-v.
;; 2010/06/11 dadams
;;     Wrap all (require '* nil t) in condition-case.
;; 2010/06/07 dadams
;;     Fix deskstop bookmarks for Emacs < 22.  Protect:
;;       *-release-lock with fboundp, *-buffer-args-list with boundp, *-dir with Emacs version #,
;; 2010/05/30 dadams
;;     Added: bookmarkp-(next|previous)-bookmark-w32(-repeat).  Bound to C-x p (next|prior).
;; 2010/05/29 dadams
;;     *-bmenu-list, *-choose-navlist-from-bookmark-list, *-bmenu-define(-full-snapshot)-command,
;;       *-save-menu-list-state, -make-bookmark-list-record:
;;         Add/restore bookmarkp-bmenu-filter-pattern to/from state.
;;     *-jump-bookmark-list: Set bookmarkp-latest-bookmark-alist to  bookmark-alist.
;;     Reordered Bookmark menu and added items:
;;       Set Bookmark, Delete Autonamed Bookmark, Delete All Autonamed Bookmarks Here,
;;       Delete Bookmarks Here, Delete Bookmark, Rename Bookmark, Bookmark List for This Buffer,
;;       Bookmark List for Navlist, Set Navlist to Bookmarks of Type,
;;       Set Navlist from Bookmark-List Bookmark, Insert Bookmark Contents, Insert Bookmark Location.
;;     Added to Bookmark+ menu: Set Navlist *.
;;     Added to bookmarkp-bmenu-jump-menu: In Navigation List.
;;     Added :enable entries for menu items.
;;     Updated bookmark-bmenu-mode doc string for cycling, navlist, and options.
;;     Corrected bindings of bookmarkp-jump-in-navlist(-other-window).
;; 2010/05/26 dadams
;;     Added:
;;       bookmarkp-choose-navlist-(from-bookmark-list|of-type), bookmarkp-crosshairs-highlight,
;;       bookmarkp-cycle(-this-buffer)(-other-window), bookmarkp-delete-bookmarks,
;;       bookmarkp-jump-in-navlist(-other-window), bookmarkp-navlist-bmenu-list,
;;       bookmarkp-(next|previous)-bookmark(-this-buffer)(-repeat),
;;       bookmarkp-toggle-autoname-bookmark-set/delete, bookmarkp-autoname-bookmark(-function),
;;       bookmarkp-autonamed-bookmarks-alist-only, bookmarkp-autoname-format,
;;       bookmarkp-bookmark-autoname-p, bookmarkp-crosshairs-flag,
;;       bookmarkp-this-buffer-cycle-sort-comparer, bookmarkp-current-bookmark-list-state,
;;       bookmarkp-cycle-1, bookmarkp-list-position, bookmarkp-position-cp,
;;       bookmarkp-current-nav-bookmark, bookmarkp-cycle-this-buffer-buff, bookmarkp-nav-alist,
;;       bookmarkp-update-autonamed-bookmark, bookmarkp-delete-all-autonamed-for-this-buffer.
;;    Bound:
;;       bookmarkp-choose-navlist-from-bookmark-list, bookmark-insert-location,
;;       bookmarkp-navlist-bmenu-list, bookmarkp-choose-navlist-of-type, bookmarkp-delete-bookmarks,
;;       bookmarkp-toggle-autoname-bookmark-set/delete, bookmarkp-jump-in-navlist(-other-window),
;;       bookmarkp-(next|previous)-bookmark(-this-buffer)-repeat.
;;    bookmark--jump-via: Update the name and position of an autonamed bookmark.
;; 2010/05/22 dadams
;;     *-this-buffer-p: Return nil for bookmarks not really associated with a buffer.
;;     *-default-handler, *-goto-position: Forgot comma to eval file-name when no-such-file error.
;;     *-show-annotation: Bind buffer-read-only to nil for updating.
;; 2010/05/19 dadams
;;     Added: bookmarkp-this-buffer-bmenu-list.  Bound to `C-x p .'.
;;     menu-bar-bookmark-map:
;;       Added bookmarkp-this-buffer-bmenu-list.  Added separators.
;;       Added vanilla items edit, write, load, to impose order.  Renamed item edit.
;; 2010/05/16 dadams
;;     bookmark-set: Quoted history arg.  Thx to S. Nemec.
;;     bookmarkp-bmenu-define-full-snapshot-command: Use quote comma, not quote, for *-specific-*.
;; 2010/05/15 dadams
;;     Replace *same-(buffer|file)-jump* by *specific-(buffers|files)-jump*: read multiple buff/files.
;;     Renamed: *same-(buffer|file)* to *-last-specific-(buffer|file)* for pred, alist, and var.
;;     Renamed: *same-(buffer|file)* to *specific-(buffer|file)* for hist, *types*, mark/show cmds.
;;     Renamed: *-selected-buffers-alist* to *-specific-buffers-alist*.
;;     Added: *-specific-files-alist*, *-(all|some)-tags(-regexp)-alist-only.
;;     *-completing-read-(buffer|file)-name: Use (buffer|file)-name-history, not *-same-*-history.
;;     *-read-tags-completing: Rewrote to correctly handle cons and string tags, error handling, etc.
;;     *-bmenu-(add|remove)-tags-*-marked: Error handling.
;;     *(all|some)-tags(-regexp)-jump*: Use *-(all|some)-tags(-regexp)-alist-only.
;; 2010/05/11 dadams
;;     Added: bookmarkp-bmenu-mark-same-(buffer|file)-bookmarks, bookmarkp-this-(buffer|file)-p,
;;            bookmarkp-this-(buffer|file)-alist-only, bookmarkp-bmenu-show-only-same-(buffer|file),
;;            bookmarkp-completing-read-(buffer|file)-name, bookmarkp-same-(buffer|file)-history,
;;            bookmarkp-(same|this)-(buffer|file)-alist-only, bookmarkp-last-same-(buffer|file),
;;            bookmarkp-(same|this)-(buffer|file)-jump(-other-window), bookmarkp-(buffer|file)-names,
;;            bookmarkp-same-(buffer|file)-as-last-p, bookmarkp-other-window-pop-to-flag,
;;            bookmarkp-select-buffer-other-window.
;;     Use bookmarkp-select-buffer-other-window instead of switch-to-buffer-other-window everywhere.
;;     Bound = (b|f) (M|S), C-x j (=|.) (b|f) to (same|current)-(buffer|file) commands.
;;     *-types-alist: Handle same-(buffer|file) too.
;;     *-bmenu-list, *-bmenu-define-full-snapshot-command, *-save-menu-list-state:
;;       Handle bookmarkp-last-same-(buffer|file) as part of state.
;; 2010/05/05 dadams
;;     bookmarkp-create-varlist-bookmark, bookmarkp-make-varlist-record:
;;       Added optional arg BUFFER-NAME.
;;     bookmark-alist: Corrected doc string wrt BUFFER-NAME and region context strings.
;; 2010/05/04 dadams
;;     Added: bookmarkp-create-varlist-bookmark.
;;     bookmarkp-jump-varlist: If bookmark's buffer doesn't exist, use current buffer and show msg.
;; 2010/04/24 adams
;;     Added: bookmarkp-bmenu-show-only-varlists, bookmarkp-set-restrictions-bookmark,
;;            bookmarkp-set-varlist-bookmark, bookmarkp-varlist-jump, bookmarkp-varlist,
;;            bookmarkp-jump-varlist, bookmarkp-make-varlist-record, bookmarkp-printable-p,
;;            bookmarkp-printable-vars+vals, bookmarkp-read-variables-completing,
;;            bookmarkp-read-variable, bookmarkp-varlist-alist-only, bookmarkp-varlist-bookmark-p,
;;            bookmarkp-varlist-history.
;;     Bound bookmarkp-bmenu-show-only-varlists to V S, bookmarkp-varlist-jump to C-x j v (and menu).
;;     *-types-alist: Added bookmarkp-varlist-history.
;;     *-bmenu-mode-status-help, *-bmenu-propertize-item, *-describe-bookmark: Handle varlist bmks.
;;     *-bmenu-w32-open-select: Changed binding to M-v from V.
;;     *-bmenu-mode: Updated doc string.
;; 2010/04/17 dadams
;;     bookmark-set: Numeric prefix arg means use all bookmarks as completion candidates.
;;                   Simplified the prompt.
;;     bookmarkp-completing-read-1:
;;       Use icicle-transform-multi-completion in icicle-delete-candidate-object
;;     Ensure loaded before byte-compile (put a require after provide).
;;     Move bookmarkp-replace-regexp-in-string before macro bookmarkp-define-sort-command (uses it).
;;     bookmarkp-bmenu-w32-open-with-mouse, bookmarkp-bmenu-mouse-3-menu:
;;       Use with-current-buffer, not save-excursion of set-buffer.
;;     bookmarkp-make-dired-record, bookmarkp-jump-dired: Use dolist, not mapcar (just side effect).
;;     bookmarkp-(some|all)-tags-jump(-other-window): Removed extraneous arg in error call.
;; 2010/04/16 dadams
;;     Added: bookmarkp-completing-read-1, bookmarkp-completing-read-lax,
;;            bookmarkp-selected-buffers-alist-only.
;;     bookmark-set: Use bookmark-completing-read-lax w/ buffer's bookmarks, not read-from-minibuffer.
;;     bookmark-completing-read: Define using bookmarkp-completing-read-1.
;; 2010/04/09 dadams
;;     bookmarkp-edit-bookmark: Update dired-directory property along with filename property.
;; 2010/03/28 dadams
;;     bookmarkp-goto-position: Don't funcall bookmarkp-jump-display-function if it is nil.
;; 2010/03/28 dadams
;;     bookmark-default-handler: Don't funcall bookmarkp-jump-display-function if it is nil.
;; 2010/03/27 dadams
;;     Changed the customization group from bookmarkp to bookmark-plus.
;;     Moved doc and change history from bookmark+.el to this new file, bookmark+-doc.el.
;;     bookmarkp-commentary-button: Use bookmark+-doc.el, not bookmark+.el.
;; 2010/03/17 dadams
;;     Added: bookmarkp-toggle-bookmark-set-refreshes, bookmarkp-refresh-latest-bookmark-list,
;;            bookmarkp-after-set-hook.
;; 2010/03/16 dadams
;;     Fixed parens placement (typo) for last change to define *-jump-woman for Emacs 20.
;; 2010/03/11 dadams
;;     Define bookmarkp-jump-woman also for Emacs 20 (just raise an error).
;;     *-show-annotation: Typo: bookmark -> bmk-name.
;; 2010/03/10 dadams
;;     Added: bookmarkp-bookmark-creation-cp, bookmarkp-bmenu-sort-by-creation-time (bind: s0, menu).
;;     *-make-record-default: Add entry: created.
;;     *-describe-bookmark: Add creation time to description.
;; 2010/03/03 dadams
;;     *-sort-and-remove-dups: Do not set bookmarkp-sorted-alist to the result.
;;     *-bmenu-list-1: Set bookmarkp-sorted-alist to the result of calling *-sort-and-remove-dups.
;; 2010/03/02 dadams
;;     Added: bookmarkp-sorted-alist.
;;     *-bmenu-list-1: Use bookmarkp-sorted-alist.
;;     *-sort-and-remove-dups: Set bookmarkp-sorted-alist to the result.
;;     All *-cp (and hence *-define-file-sort-predicate):
;;       Accept bookmark names as args, in addition to bookmarks.
;;     bookmark-alpha-p: Don't use bookmarkp-make-plain-predicate, to avoid infinite recursion.
;; 2010/02/28 dadams
;;     Added: bookmarkp-send-bug-report.
;;     bookmarkp-bmenu-mode-status-help: Rewrote to provide only Bookmark+ help.  Added help buttons.
;;     Fixed Commentary typos.
;; 2010/02/26 dadams
;;     Added: bookmarkp-desktop-change-dir, bookmarkp-desktop-kill, bookmarkp-desktop-delete.
;;     *-jump-desktop: Call *-desktop-change-dir.
;;     *-read-bookmark-for-type: Added optional arg ACTION.
;; 2010/02/24 dadams
;;     *-bmenu-list: Handle case null last-bookmark-file (due to old file format).  Thx to Seb Luque.
;;     *-make-record-default: protect dired-buffers with boundp.  Thx to Janek Schwarz.
;; 2010/02/16 dadams
;;     bookmarkp-define-sort-command: Add msg suffix about repeating.
;;     bookmarkp-msg-about-sort-order: Added optional arg SUFFIX-MSG.
;; 2010/02/15 dadams
;;     Added: bookmark-bmenu-switch-other-window (redefinition for Emacs 20-22).
;;     *-bmenu-mode: Added redefinition, instead of advising.
;;     *-send-edited-annotation, *-relocate, *-rename, *-bmenu-refresh-menu-list,
;;       *-remove(-all)-tags, *-add-tags:
;;         Refresh the menu list, to pick up changes.
;;     *-refresh-menu-list: Added optional arg BOOKMARK: go to it.
;;     Do not bind bookmark-bmenu-relocate unless it's defined.
;;     *-handler-cp: Respect case-fold-search.
;; 2010/02/14 dadams
;;     Renamed bookmark-bmenu-list-1 to bookmarkp-bmenu-list-1.
;;     Added faces: bookmarkp-(a|t|>|D)-mark, bookmarkp-heading (don't use bookmark-menu-heading).
;;     Added redefinitions: bookmark-send-edited-annotation, bookmark(-bmenu)-show-annotation,
;;                          bookmark-show-all-annotations.
;;     *-bmenu-mark, *-bmenu-delete, *-bmenu-list-1: Add faces to marks.
;;     *-bmenu-list-1 and everywhere: Get rid of "% " before menu-list title.
;;     *-bmenu-list-1: Use "a", not "*", as annotation mark.
;;                     Add "t" mark for tags.  Add an extra space before bookmark name.
;;     *-bmenu-marks-width: change value from 2 to 4, for the tags column and the extra space.
;; 2010/02/13 dadams
;;     Added: bookmarkp-desktop-history,
;;            bookmarkp-desktop-jump (bound to C-x j K; added to menu),
;;            bookmarkp-bookmark-list-jump (bound to C-x j B; added to menu),
;;            bookmarkp-bookmark-list-alist-only, bookmarkp-bookmark-list-history.
;;     *-types-alist: Added entries for desktops and bookmark-lists.
;;     *-describe-bookmark: Added optional arg, to show full (internal) info.
;;                          Bind it to ? in bookmark-map.
;;     *-jump-bookmark-list: Pop to the bookmark-list (to show it).
;;     *-bmenu-mark-w3m-bookmarks: Typo: wrong predicate.
;;     *(-bmenu)-remove-all-tags: Raise error if no tags to remove.
;;     *-bmenu-remove-all-tags: Require confirmation if interactive.
;;     *-bmenu-remove-tags: Added optional arg MSGP.
;;     Menus: Added "..." as needed.
;;     *-bmenu-mouse-3-menu: Guard bookmark-bmenu-relocate with fboundp.
;; 2010/02/12 dadams
;;     Added: bookmarkp-bmenu-define-jump-marked-command.  Bound to M-c and added to menu.
;;     Changed bookmarkp-toggle-saving-bookmark-file binding to M-~ (M-s conflicts w isearch-multi).
;;     Updated bookmark-bmenu-mode doc string.
;; 2010/02/11 dadams
;;     Added: bookmarkp-types-alist,
;;            bookmarkp-(dired|gnus|info|man|region|w3m|(non-|local-|remote-)file)-history.
;;     bookmark-completing-read: Added optional HIST arg.
;;     *-(relocate|rename|insert(-location)): Added bookmark default for interactive use.
;;     *-jump-dired: Handle bookmarkp-jump-display-function.
;;     *-read-bookmark-for-type: Added optional HIST arg.
;;     *-jump-to-type(-other-window),
;;       *-(dired|file|gnus|info|man|region|w3m|(local-|non-|remote-)file)-jump*(-other-window):
;;         Use type-specific history var.
;; 2010/02/09 dadams
;;     Added: bookmarkp-get-tag-value.
;;     bookmark--jump-via: Handle special bookmark tag bookmarkp-jump.
;; 2010/02/08 dadams
;;     Renamed: bookmarkp-bmenu-dired-marked-local to bookmarkp-bmenu-dired-marked.
;;     bookmarkp-bmenu-dired-marked: Handle remote bookmarks if Emacs > 23.1.
;;     Support tags with values.
;;       Added: bookmarkp-tag-name, bookmarkp-full-tag, bookmarkp(-bmenu)-set-tag-value.
;;       Renamed variable (not fn) bookmarkp-tags-list to bookmarkp-tags-alist.
;;       Use bookmarkp-full-tag everywhere for tag completion.
;;       *-has-tag-p: Use assoc-default, not member.
;;       *-read-tag(s)-completing: CANDIDATE-TAGS is now an alist.
;;       *-list-all-tags: Added optional arg FULLP (prefix arg).
;;       *-tags-list: Added optional arg NAMES-ONLY-P.
;;       *-(add|remove|rename)-tags: Use copy-alist, not copy-sequence.  Alist, not list, membership.
;;       *-rename-tag: Raise error if no tag with old name.
;;       *-bmenu-mark-bookmarks-tagged-regexp, *-regexp-filtered-tags-alist-only, *-describe-bookmark,
;;         *-(all|some)-tags-regexp-jump(-other-window):
;;           Use bookmarkp-tag-name.
;;       *-bmenu-mark/unmark-bookmarks-tagged-(all|some)/(none|not-all), *-define-tags-sort-command:
;;         Use assoc-default, not member.
;;     Added: bookmarkp-bmenu-add-tags, bookmarkp-bmenu-remove(-all)-tags.
;;     *-bmenu-mouse-3-menu: Use bookmarkp-bmenu-add-tags, bookmarkp-bmenu-remove(-all)-tags.
;;                           Added bookmarkp-bmenu-set-tag-value.
;;     *-bmenu-mark-bookmarks-satisfying: Made it a command (interactive).
;; 2010/02/07 dadams
;;     *-write-file: Corrected handling of ALT-MSG.
;;     Cleanup.
;;       *-remove-tags: Don't call *-get-tags twice.
;;       *-bmenu-(un)mark-bookmarks-tagged(-not)-(all|none|some):
;;         Don't duplicate what bookmarkp-read-tags-completing does.
;;       *-add-tags, *-remove-tags(-from-all): TAGS arg must be a list from the beginning.
;;       *-remove-tags-from-all, *-rename-tag: Use bookmark-all-names - don't mapcar car over alist.
;;       *-all-tags-regexp-jump: Corrected to use same pred as *-all-tags-regexp-jump-other-window.
;;       *-(some|all)-tags-jump(-other-window): Use bookmarkp-has-tag-p - don't repeat the definition.
;;       *-read-tag(s)-completing: Removed unnecessary or.
;; 2010/02/06 dadams
;;     *-write-file, *-empty-file: Corrected handling of ALT-MSG.
;; 2010/02/05 dadams
;;     Added: bookmarkp-same-file-p, bookmarkp-empty-file.
;;     Bound bookmarkp-empty-file to C-x p 0, and added it to menus.
;;     *-bmenu-list, *-switch-bookmark-file: Use bookmarkp-same-file-p.
;;     bookmark-write-file: Added optional ALT-MSG arg.
;; 2010/02/04 dadams
;;     Added: bookmarkp-bmenu-omit, bookmarkp-list-all-tags.  Added to mouse-3 menu, Tags menus.
;; 2010/02/01 dadams
;;     Added: bookmarkp-current-bookmark-file, bookmarkp-switch-bookmark-file,
;;            (redefinition of) bookmark-load, (redefinition of) bookmark-save,
;;            bookmarkp-toggle-saving-bookmark-file, bookmarkp-last-save-flag-value.
;;     *-bmenu-list: Restore bookmarkp-current-bookmark-file if appropriate.
;;     *-bmenu-mode-status-help: Show bookmarkp-current-bookmark-file.
;;     *-bmenu-define-full-snapshot-command, *-save-menu-list-state:
;;       Save bookmarkp-current-bookmark-file.
;;     Bound bookmarkp-switch-bookmark-file to L and C-x r L.  Added both load commands to both menus.
;;     *-toggle-saving-menu-list-state: Changed binding to M-l.  Error if init value is nil.
;;     Bound *-toggle-saving-bookmark-file to M-s and added to menu.
;;     Added bookmark-write to bookmarkp-bmenu-menubar-menu (Save As).
;;     bookmarkp-bmenu-menubar-menu: Added :help strings everywhere.
;;     bookmarkp-bmenu-mode-status-help: Added face legend.
;; 2010/01/31 dadams
;;     Added: bookmarkp-tags-list, bookmarkp-read-tag-completing, bookmarkp-use-w32-browser-p,
;;            bookmarkp-bmenu-w32-open(-select|-with-mouse).  Bind *-w32* to M-RET, V, M-mouse-2.
;;     *-default-handler: Call w32-browser if bookmarkp-use-w32-browser-p.
;;     *-bmenu-unomit-marked: Don't try to return to original position (duh).
;;     *-bmenu-goto-bookmark-named: Use eobp as loop condition.  Call bookmark-bmenu-ensure-position.
;;     *-read-tags-completing:
;;       Added arg UPDATE-TAGS-LIST-P.  Call bookmark-maybe-load-default-file.
;;       Use bookmarkp-tags-list if CANDIDATE-TAGS is nil.  Update that var if UPDATE-TAGS-LIST-P.
;;     *-(add|remove)-tags: Added arg NO-CACHE-UPDATE-P.  If nil, call bookmarkp-tags-list.
;;     *-remove-tags-from-all, *-rename-tag, *-bmenu-(add|remove)-tags-(to|from)-marked:
;;       Call bookmarkp-tags-list.
;;     *-remove-tags-from-all: Pass nil as tags arg to bookmarkp-read-tags-completing.
;;     *-rename-tag: Use bookmarkp-read-tag-completing, not read-string.
;; 2010/01/29 dadams
;;     bookmarkp-describe-bookmark: Handle desktop bookmarks specifically.
;;     Added: bookmarkp-menu-popup-max-length.
;;     bookmark-completing-read: Use bookmarkp-menu-popup-max-length.
;;     bookmarkp-bmenu-state-file: Added missing default value for const.
;;     Don't add jump-other entry to menu-bar-bookmark-map (just use Jump To submenu).
;; 2010/01/28 dadams
;;     bookmarkp-(all|some)-tags(-regexp)-jump(-other-window): Error if no bookmarks with the tags.
;;     bookmarkp-(all|some)-tags-jump(-other-window): Handle case where user enters no tags.
;;     Use :advertised-binding property for bookmark-jump(-other-window).
;;     Added: bookmarkp-bmenu-jump-menu.
;;     Added bookmarkp-bmenu-jump-menu to menu-bar-bookmark-map and bookmarkp-bmenu-menubar-menu.
;; 2010/01/27 dadams
;;     Added: bookmarkp-every, bookmarkp-(all|some)-tags(-regexp)-jump(-other-window).
;; 2010/01/26 dadams
;;     Added: bookmarkp-bmenu-dired-marked-local.  Bound to M-d >.
;; 2010/01/23 dadams
;;     Added: bookmarkp-handler-cp, bookmarkp-desktop-no-save-vars, bookmarkp-set-desktop-bookmark,
;;            bookmarkp-make-desktop-record, bookmarkp-jump-desktop, bookmarkp-desktop-read,
;;            bookmarkp-desktop-alist-only, bookmarkp-desktop-bookmark-p,
;;            bookmarkp-bmenu-mark-desktop-bookmarks, bookmarkp-bmenu-show-only-desktops,
;;            face bookmarkp-desktop.
;;     bookmarkp-bmenu-sort-by-bookmark-type: Add bookmarkp-handler-cp to the list (last).
;;     bookmarkp-bmenu-propertize-item: Add face bookmarkp-desktop for desktop bookmarks.
;;     Bound: bookmarkp-set-desktop-bookmark to C-x p K, C-x r K,
;;            bookmarkp-bmenu-mark-desktop-bookmarks to K M (and Mark menu),
;;            bookmarkp-bmenu-show-only-desktops to K S (and Show menu).
;;     bookmark-bmenu-mode doc string: Updated for new commands.
;;     Added autoload cookies for all defcustoms.
;; 2010/01/20 dadams
;;     Added: bookmarkp-bmenu-mode-status-help.  Bound to C-h m, ?.
;; 2010/01/19 dadams
;;     bookmarkp-remote-file-bookmark-p: Include remote Dired bookmarks.  Thx to Simon Harrison.
;;     Added: bookmarkp-describe-bookmark-internals, bookmarkp-bmenu-describe-this+move-(down|up),
;;            defalias for list-bookmarks.
;;     bookmarkp-describe-bookmark: Reformatted help output.  Added more info about Dired bookmarks.
;;     bookmarkp-bmenu-describe-this-bookmark:
;;       C-u calls bookmarkp-describe-bookmark-internals.  Bound also to C-h C-RET.
;; 2010/01/18 dadams
;;     Added: bookmarkp-dired-subdirs.
;;     bookmarkp-make-dired-record, bookmarkp-jump-dired: Handle inserted and hidden dirs.
;;     bookmarkp-jump-dired: Use expand-file-name, not concat.
;; 2010/01/17 dadams
;;     Added:
;;       bookmarkp-jump(-other-window)-map, bookmarkp-jump-1, bookmark-all-names (redefined),
;;       bookmarkp-read-bookmark-for-type, bookmarkp-dired-jump-current(-other-window),
;;       bookmarkp-(dired|(local-|remote-|non-)file|gnus|info|man|region|w3m)-jump(-other-window),
;;       bookmarkp-jump-to-type(-other-window).
;;     bookmark-jump(-other-window): Use bookmarkp-jump-1.
;;     bookmark-completing-read: Added optional args ALIST and PRED.
;;     bookmarkp-default-bookmark-name: Added optional arg ALIST.
;; 2010/01/14 dadams
;;     bookmark-bmenu-surreptitiously-rebuild-list: Put back save-excursion & save-window-excursion.
;; 2010/01/02 dadams
;;     Renamed *-bmenu-check-position to *-bmenu-ensure-position, per Emacs 23.2.  Added defalias.
;; 2010/01/01 dadams
;;     *-bmenu-(un)mark, *-bmenu-other-window, *-bmenu-rename: Call bookmark-bmenu-check-position.
;;     *-bmenu-delete: Don't call bookmark-bmenu-check-position again at end.
;;     *-bmenu-edit-bookmark: Call bookmark-bmenu-check-position at beginning, not end.
;; 2009/12/30 dadams
;;     Added: bookmarkp-bmenu-header-lines, bookmarkp-bmenu-marks-width.  Use everywhere.
;; 2009/12/29 dadams
;;     Added: bookmarkp-make-bookmark-list-record, bookmarkp-jump-bookmark-list, face
;;            bookmarkp-bookmark-list.
;;     *-bmenu-propertize-item: Highlight bookmark-list bookmarks.
;;     *-bmenu-refresh-menu-list: Set bookmarkp-latest-bookmark-alist to refreshed list.
;;     Face *-local-directory: Made dark background version the inverse of light.
;;     *-bmenu-list-1: Use eq, not equal, test for bookmarkp-omitted-alist-only as filter fn.
;;     *-bmenu-define(-full-snapshot)-command: Include bookmarkp-bmenu-omitted-list in saved state.
;; 2009/12/26 dadams
;;     Added: bookmarkp-bmenu-omitted-list, bookmarkp-bmenu-show-only-omitted, bookmarkp-unomit-all,
;;            bookmarkp-bmenu-omit/unomit-marked, bookmarkp-bmenu-(un-)omit-marked,
;;            bookmarkp-omitted-alist-only.
;;            Bind *-bmenu-omit/unomit-marked, *-bmenu-show-only-omitted, *-unomit-all to O>,OS,OU.
;;     Added omit/un-omit stuff to Bookmark+ menu.
;;     bookmarkp-remove-assoc-dups, bookmarkp-sort-and-remove-dups: Added optional arg OMIT.
;;     bookmark-delete: Update bookmarkp-bmenu-omitted-list.
;;     bookmarkp-save-menu-list-state, bookmark-bmenu-list:
;;       Save/restore bookmarkp-bmenu-omitted-list as part of state.
;;     bookmark-bmenu-list-1: Treat omitted list when bookmarkp-omitted-alist-only.
;;     bookmarkp-marked-bookmark-p: Arg can now be a bookmark (or a bookmark name).
;;     bookmarkp-bmenu-unmark-all: Start by going forward 2 lines, not 1, if user hit RET.
;;     bookmarkp-bmenu-make-sequence-from-marked:
;;       Added optional arg DONT-OMIT-P.  If nil, omit marked bookmarks.
;;       If the seq bookmark already exists, prompt to add to it or replace it.
;;       Go to the new bookmark in the menu list.
;; 2009/12/15 dadams
;;     Added: bookmarkp-sequence-jump-display-function, bookmarkp-sequence, bookmarkp-function,
;;            bookmarkp-bmenu-make-sequence-from-marked, bookmarkp-jump-sequence,
;;            bookmarkp-sequence-bookmark-p, bookmarkp-make-function-bookmark,
;;            bookmarkp-jump-function, bookmarkp-function-bookmark-p.
;;     bookmarkp-describe-bookmark: Update for sequence and function bookmarks.
;;     bookmark-bmenu-list: Use condition-case when read from bookmarkp-bmenu-state-file.
;;                          Bind emacs-lisp-mode-hook to nil.
;;     bookmark-bmenu-surreptitiously-rebuild-list: Use save-current-buffer.
;;     bookmarkp-bmenu-propertize-item: Add faces to function and sequence bookmarks.
;;     bookmarkp-bmenu-menubar-menu: Add *-make-sequence-*-from-marked, *-make-function-bookmark.
;;     bookmark--jump-via: Call *-record-visit with BATCH arg, to preserver point in menu list.
;;     bookmark-bmenu-list-1: fit-frame only if buffer is *Bookmark List*.
;; 2009/12/13 dadams
;;     *-alist-only: Call bookmark-maybe-load-default-file.
;; 2009/12/11 dadams
;;     Added: bookmarkp-list-defuns-in-commands-file, bookmarkp-remove-dups.
;; 2009/12/06 dadams
;;     Added: bookmarkp-bmenu-mouse-3-menu (bound to mouse-3),
;;            bookmarkp-bmenu-(menubar|define-command|sort|show|tags|mark)-menu.
;;     bookmark-bmenu-delete: Remove newly flagged bookmark from bookmarkp-bookmark-marked-list.
;;     bookmarkp-define-tags-sort-command: Save macroexpanded definition in
;;                                         bookmarkp-bmenu-commands-file.
;; 2009/12/04 dadams
;;     Added: bookmarkp-bmenu-define-full-snapshot-command (bound to C),
;;            bookmarkp-define-tags-sort-command.
;;     bookmarkp-bmenu-mark-bookmarks-tagged-regexp: Removed extra forward-line if we mark line.
;; 2009/12/03 dadams
;;     Added: bookmarkp-bmenu-define-command (bound to c), bookmarkp-bmenu-commands-file.
;;     bookmark-bmenu-list: Read bookmarkp-bmenu-commands-file.
;;     bookmarkp-sort-and-remove-dups: Bug fix - return the list even when null sort function.
;; 2009/11/01 dadams
;;     Added: *-bmenu-check-position (redefinition), bmkext-jump-* defaliases.
;;     *-(w3m|man|gnus)-bookmark-p: Recognize the aliases.
;;     *-jump-man: Bind Man-notify-method.
;;     *-bmenu-goto-bookmark-named: Check the text property, instead of searching.
;;     *-bmenu-bookmark: Wrap in condition-case.
;; 2009/10/31 dadams
;;     Added: bookmark-bmenu-list-1. bookmarkp-toggle-saving-menu-list-state (C-t),
;;            bookmarkp-bmenu-state-file, bookmarkp-bmenu-first-time-p,
;;            bookmarkp-last-bmenu-(bookmark|state-file), bookmark-exit-hook-internal
;;            (redefinition), bookmarkp-save-menu-list-state.
;;     bookmark-bmenu-list: Restore menu-list state if appropriate.  Call bookmark-bmenu-list-1.
;;     bookmarkp-bmenu-quit: If *-bmenu-state-file is non-nil, save the state.
;;     bookmark-write-file: Use case, not cond.
;;     bookmark-set: Use command name as default for man-page bookmark name.
;;     bookmark-delete: Update bookmarkp-latest-bookmark-alist.
;; 2009/10/28 dadams
;;     Renamed: bookmarkp-bookmark-marked-p to bookmarkp-marked-bookmark-p
;;              bookmarkp-bmenu-sort-by-gnus-thread to bookmarkp-bmenu-sort-by-Gnus-thread.
;;     Added: bookmarkp-man, bookmarkp-make-(wo)man-record, bookmarkp-jump-(wo)man,
;;            bookmarkp-man-bookmark-p, bookmarkp-bmenu-mark-man-bookmarks,
;;            bookmarkp-bmenu-show-only-man-pages, bookmarkp-man-alist-only.
;;     *-bmenu-propertize-item: Handle (wo)man bookmarks.  Use bookmarkp-info-bookmark-p.
;;     *-regexp-filtered-*: Use bookmarkp-remove-if-not.
;;     *-write-file: Remove text properties from file name also.
;;     *-regexp-filtered-(tags|(bookmark|file)-name)-alist-only: Use *-remove-if-not.
;; 2009/10/26 dadams
;;     Added: bookmarkp-bmenu-mark-*-bookmarks, bmenu-mark-bookmarks-satisfying.
;;     Bound those and *-show-only-* accordingly.
;;     bookmarkp-file-alist-only: Redefined to just use *-file-bookmark-p.
;; 2009/10/25 dadams
;;     bookmarkp-bmenu-propertize-item: Put bookmark name on line as text property.
;;     bookmark-bmenu-bookmark: Get bookmark name from text property bookmarkp-bookmark-name.
;;     Removed: bookmarkp-latest-sorted-alist.
;;     bookmark-bmenu-list: Use bookmarkp-bmenu-title only if defined.
;; 2009/10/21 dadams
;;     Added: bookmarkp-barf-if-not-in-menu-list.  Use in place of its body.
;;     Added: bookmarkp-bmenu-mark-bookmarks-tagged-regexp.  Bound to T m %.
;;     Added: bookmarkp-record-visit.  Use in *--jump-via.  Replaces next two removals.
;;     Removed: bookmarkp-add-or-update-time, bookmarkp-increment-visits.
;;     Renamed: *-record-(end|front|rear)-context(-region)-string'.
;;              New names: bookmarkp-(end-)position-(pre|post)-context(-region).
;;     *-bmenu-describe-this-bookmark: Added *-barf-if-not-in-menu-list.
;;     *-bmenu-(un)mark-all, *-bmenu-regexp-mark, *-bmenu-toggle-marks:
;;       Removed with-current-buffer.
;; 2009/10/20 dadams
;;     Added: bookmarkp-bmenu-filter-function, bookmarkp-bmenu-title.
;;     Removed: bookmarkp-bmenu-called-from-inside-p.
;;     *-bmenu-list:
;;       Removed TITLE arg.  Get title from bookmarkp-bmenu-title or default.
;;       Use interactive-p and absence of menu list, not *-bmenu-called-from-inside-p, as the
;;         criterion for removing marks.  Fixes bugs such as bookmark creation removing marks.
;;     *-define-sort-command, *-bmenu-execute-deletions, *-increment-visits,
;;       *-add-or-update-time, *-bmenu-show-only-*, *-bmenu-show-all,
;;       *-bmenu-refresh-menu-list, *-bmenu-toggle-show-only-(un)marked,
;;       *-bmenu-filter-alist-by-regexp, *-bmenu-reverse(-multi-sort)-order,
;;       *-bmenu-change-sort-order:
;;         Do not bind or set *-called-from-inside-p.
;;     *-bmenu-show-only-*, *-bmenu-show-all, *-bmenu-filter-alist-by-regexp:
;;       Set *-bmenu-filter-function, *-bmenu-title.
;;     *-bmenu-show-all:
;;       Set *-latest-bookmark-alist to bookmark-alist.
;;     *-bmenu-refresh-menu-list: Fix so that it in fact refreshes.
;;       Do not use *-bmenu-surreptitiously-rebuild-list and *-bmenu-check-position.
;;       Bind bookmark-alist to last alist (filtered or not), and call *-bmenu-list.
;;     *-bmenu-surreptitiously-rebuild-list:
;;       Do not use save*-excursion.  Do not get current title and pass it to *-bmenu-list.
;;     *-file-alist-only:
;;       Removed optional arg.  We have *-local-file-alist-only for that.
;;     *-regexp-filtered-alist-only, *-bmenu-filter-alist-by-regexp:
;;       Remove REGEXP arg - use bookmarkp-bmenu-filter-pattern.
;;     *-bmenu-filter-incrementally:
;;       Raise error if not in *Bookmark List*.
;;       Use just bookmarkp-bmenu-filter-alist-by-regexp in timer - pass no regexp arg.
;;     Added: bookmarkp-some, *-bmenu-filter-(file-name|tags)-incrementally,
;;            *-bmenu-filter-alist-by-(file-name|tags)-regexp,
;;            *-regexp-filtered-(file-name|tags)-alist-only.
;;     Renamed: *-bmenu-filter-incrementally to *-bmenu-filter-bookmark-name-incrementally,
;;              *-bmenu-filter-alist-by-regexp to *-bmenu-filter-alist-by-bookmark-name-regexp,
;;              *-regexp-filtered-alist-only to *-regexp-filtered-bookmark-name-alist-only.
;;     Bound these commands to P B, P F, and P T.  Updated bookmark-bmenu-mode doc string.
;; 2009/10/18 dadams
;;     Added: *-bmenu-filter-(incrementally|delay|prompt|pattern|timer|alist-by-regexp),
;;            *-bmenu-read-filter-input, *-regexp-filtered-alist-only,
;;            *-bmenu-cancel-incremental-filtering.
;;     *-bmenu-execute-deletions: Don't update menu list if this is a no-op.
;;     Updated Commentary.
;;     Thx to Thierry Volpiatto.
;;     Added: *-marked-cp, *-bmenu-sort-marked-before-unmarked.  Bound to s >.
;;     *-define-sort-command: Use copy-sequence for default value.
;; 2009/10/17 dadams
;;     Added: *-read-tags-completing, *-set-union, *-tag-history, *-describe-bookmark,
;;            *-bmenu-describe-this-bookmark.  Bound *-bmenu-describe-this-bookmark to C-h RET.
;;     Use *-read-tags-completing instead of *-read-tags.
;;     *-sort-orders-for-cycling-alist: Use copy-sequence.
;;     *-bmenu-change-sort-order: Use member, not memq.
;;     *-get-bookmark: Handle case of non-string, non-cons. Document NOERROR in doc string.
;;     *-bmenu-execute-deletions: Fix so marks aren't removed if when delete.  Thx to Thierry.
;;     Convert recorded time to an Emacs time spec:
;;       *-make-record-default, -add-or-update-time: Use current-time, not bookmark-float-time.
;;       *-get-visit-time: Convert a deprecated time entry to an Emacs time spec.
;;       *-bookmark-last-access-cp: Convert recorded time to a number for comparison.
;;     Added: *-bmenu-show-filenames (redef of vanilla: put props on whole line, fit frame).
;;     Removed: old-bookmark-insert-location.
;;     *-insert-location: Do not call original.  Redefined: do not add text properties.
;;     *-bmenu-list, *-bmenu-hide-filenames: Put properties on line up to max width.
;;     *-bmenu-goto-bookmark-named: Allow trailing whitespace, since we use the whole line now.
;;     *-bmenu-list: Use pop-to-buffer, not switch-to-buffer.  Use do-list, not mapcar.
;;     *-bmenu-hide-filenames: fit-frame-if-one-window.
;;     *-bmenu-propertize-item: Better help-echo text.
;;     Updated bookmark-alist doc string to mention visits, time, and tags entries.
;; 2009/10/16 dadams
;;     Added tags feature.
;;       Added: *-(get|read)-tags, *-has-tag-p, *-remove(-all)-tags(-from-all),
;;              *-bmenu-remove-tags-from-marked, *-add-tags(-to-marked), *-rename-tag,
;;              *-bmenu-(un)mark-bookmarks-tagged-(all|none|some|not-all),
;;              *-bmenu-mark/unmark-bookmarks-tagged-(all/none|some/not-all).
;;       Bound to prefix key T.
;;       *-bmenu-mode: Updated doc string.
;;     Added: bookmarkp-default-bookmark-name.  Use as default instead of *-current-bookmark.
;;     Renamed: *-maybe-save-bookmark to *-maybe-save-bookmarks.
;;     Menu-list commands: Raise an error if command is used outside the menu list.
;; 2009/10/15 dadams
;;     Added: *-bmenu-(search|query-replace)-marked-bookmarks-regexp.  Bound to M-a, M-q.
;;     Renamed: *-non-marked-bookmarks-only to *-unmarked-bookmarks-only,
;;              *-bookmark-marked-alist to *-bmenu-marked-bookmarks.
;;     *-increment-visits, *-add-or-update-time:
;;       Set *-bmenu-called-from-inside-p to t, so we don't remove marks.
;;     Redefined *-bmenu-bookmark to get name from *-latest-sorted-alist.  Thx to Thierry V.
;;       *-bmenu-surreptitiously-rebuild-list, *-bmenu-list:
;;         Removed optional arg DONT-TOGGLE-FILENAMES-P.
;;       *-bmenu-execute-deletions, *-bmenu-toggle-show-only-(un)marked, *-bmenu-(un)mark-all,
;;         *-bmenu-regexp-mark, *-bmenu-toggle-marks:
;;           Do not bother with *-bmenu-toggle-filenames and rebuilding the menu list.
;; 2009/10/14 dadams
;;     Added: *-bmenu-delete (redefinition), *-isearch-bookmarks,
;;            *-bmenu-isearch(-marked)-bookmarks(-regexp), *-isearch-next-bookmark-buffer.
;;            Bound multi-isearch commands to M-s a C(-M)-s.
;; 2009/10/13 dadams
;;     Added: *-make-dired-record, *-jump-dired, *-dired-bookmark-p, *-dired-alist-only,
;;            *-bmenu-show-only-dired.  Bound *-bmenu-show-only-dired to M-d.
;;     bookmarkp-file-bookmark-p: Include bookmarks that have the Dired handler.
;;     Moved *-sort-orders-for-cycling-alist defcustoms after *-define-sort-command calls.
;;     Call bookmarkp-msg-about-sort-order only when interactive.
;;     *-add-or-update-time, *-increment-visits: Do not save each time we access a bookmark.
;;     Updated doc string of bookmark-alist and Commentary.
;; 2009/10/09 dadams
;;     Added: bookmarkp-bmenu-delete-marked.  Bound it to D.
;;            bookmarkp-sort-orders-for-cycling-alist.
;;     Renamed: bookmarkp-sort-functions-alist to bookmarkp-sort-orders-alist,
;;              bookmarkp-sort-function to bookmarkp-sort-comparer.
;;     bookmark-bmenu-execute-deletions: Added optional arg, for *-bmenu-delete-marked.
;;     *-sort-function: Changed default value to sorting by bookmark type (`s k').
;;     *-bmenu-change-sort-order: Use *-sort-orders-for-cycling-alist, not all sort orders.
;;     Updated Commentary and doc string (bookmark-bmenu-mode).
;; 2009/10/08 dadams
;;     Added: *-bmenu-sort-by-(w3m-url|gnus-thread), *-(gnus|w3m)-cp, *-cp-not,
;;            *-local-file-(accessed|updated)-more-recently-cp, *-bmenu-sort-by-bookmark-type.
;;     Renamed: *-bmenu-sort-by(-last)-file-(size|type|access|update) to
;;              *-bmenu-sort-by(-last)-local-file-(size|typeaccess|update),
;;              *-file-visited-more-recently-cp to *-local-file-accessed-more-recently-cp,
;;              *-file-(size|type)-cp to *-local-file-(size|type)-cp.
;;     Removed: *-file-(device|gid(-chg)|inode|last-(access|update|status-change)|links|modes
;;                            |uid)-cp.
;;     Bound *-bmenu-sort-by-bookmark-type to `s k'.
;;     *-define-file-sort-predicate: Use *-file-bookmark-p, not *-local-file-bookmark-p.
;;     *-msg-about-sort-order: Added optional arg PREFIX-ARG.  Use in: *-show-(all|only-*).
;; 2009/10/07 dadams
;;     Renamed: *-bmenu-sort-by-last-visit-time to *-bmenu-sort-by-last-bookmark-access,
;;              *-bmenu-sort-by-visit-frequency to *-bmenu-sort-by-bookmark-visit-frequency,
;;              *-visited-more-recently-cp to *-bookmark-last-access-cp.
;; 2009/10/06 dadams
;;     Added: bookmarkp-msg-about-sort-order.
;;     bookmark-completing-read: Simple sort when use menu-bar menu.
;; 2009/10/05 dadams
;;     Added: *-make-plain-predicate, *-reverse-multi-sort-order, *-multi-sort,
;;            *-define-file-sort-predicate, *-bmenu-sort-by-file-*, *-file-attribute-*-cp,
;;            and aliases *-file-*-cp, *-current-sort-order.
;;     Redefined sorting to allow multi-predicates:
;;       Redefined: *-sort-function, *-sort-and-remove-dups, *-define-sort-command,
;;                  *-sort-functions-alist.
;;     Bound keys with `s f' prefix to file-sorting commands
;;     *-current-sort-order: Use rassoc instead of rassq now.
;;     Swap keys s and S.  S is now bookmark-bmenu-save.  s is not the sorting prefix key.
;;     bookmark-bmenu-mode: Mention S key explicitly here (even though it is also
;;                          mentioned in the vanilla part of the doc string).
;; 2009/10/04 dadams
;;     *-bmenu-change-sort-order-repeat: Require repeat.el.
;;     Renamed: bookmarkp-current-sec-time to bookmarkp-float-time.
;;     *-float-time: Added arg, so it's the same as float-time (for Emacs 20).
;;     Bind *-reverse-sort-order to `S R'.
;;     *-remote-file-bookmark-p: Removed extra rem-file in last and.
;;     *-non-file-bookmark-p: Ensure it's not a remote file, before calling file-exists-p.
;; 2009/10/03 dadams
;;     Added: bookmarkp-file-remote-p, bookmarkp-buffer (face).
;;     bookmarkp-non-file (face): Changed to gray.
;;     *-default-handler, *-bmenu-propertize-item, *-(info|file)-bookmark-p:
;;       Support Emacs 20-21 Info-node bookmarks.
;;     bookmarkp-bmenu-propertize-item: Use different face for existing buffers.
;;                                      Use bookmarkp-non-file-filename.
;;     bookmarkp-non-file-bookmark-p: Include buffer bookmarks for nonexistent buffers.
;;     bookmarkp-remote-file-bookmark-p: Use bookmarkp-file-remote-p.
;;     bookmark-handle-bookmark:
;;       Redefine for all Emacs versions.  Handle buffer (non-file) bookmarks.
;;     Reordered some function definitions.
;; 2009/10/02 dadams
;;     Added: bookmarkp-bmenu-goto-bookmark-named, bookmarkp-latest-sorted-alist.
;;     *-sort-and-remove-dups: Set *-latest-sorted-alist (not used yet).
;;     *-define-sort-command, *-bmenu-change-sort-order, *-reverse-sort-order:
;;       Bind *-bmenu-called-from-inside-p to t, to prevent losing marks.
;;       Restore cursor position to same bookmark after sorting - use *-goto-bookmark-named.
;;     *-bmenu-surreptitiously-rebuild-list, *-bmenu-list: Added arg DONT-TOGGLE-FILENAMES-P.
;;     *-bmenu-execute-deletions, *-bmenu-toggle-show-only-(un)marked:
;;       Call *-surreptitiously-* with arg DONT-TOGGLE-FILENAMES-P.
;;     *-bmenu-hide-filenames: Simplify - don't get to position by searching backward.
;;     *-handle-region-default: Use forward-line, not goto-line.
;;     Thx to Thierry V.
;; 2009/10/01 dadams
;;     Added: bookmarkp-some-unmarked-p.
;;     Renamed: *-bmenu-toggle-show-only-<TYPE> to *-bmenu-show-only-<TYPE>,
;;              *-bmenu-called-from-inside-flag to *-bmenu-called-from-inside-p.
;;     bookmarkp-some-marked-p: Do not test bookmarkp-bookmark-marked-alist.
;;                              Arg must be required (explicit).  Changed calls accordingly.
;;     bookmark-bmenu-mode: Cleaned up doc string.
;;     bookmark-bmenu-((un)mark|rename|edit-*|toggle-marks|surreptitiously-rebuild-list),
;;       bookmarkp-root-or-sudo-logged-p, bookmarkp-jump-w3m-(new-session|only-one-tab),
;;       bookmarkp-some-marked-p:
;;         Inline let vars used only once.
;;     bookmarkp-bmenu-toggle-show-only-marked:
;;       Test bookmarkp-some-unmarked-p, not bookmarkp-some-marked-p,
;;            and include *-before-hide-unmarked in the test.
;;     bookmarkp-bmenu(-toggle)-show-only-*: Display status message.
;;     bookmarkp-bmenu-toggle-show-only-(un)marked: Fit frame.
;;     bookmark-prop-set: Fixed, so it handles old bookmark format also.
;; 2009/10/01 Thierry Volpiatto
;;     Removed: bookmarkp-bmenu-restore-marks.
;;     bookmark-bmenu-list:
;;       Do the mark restoration in line, at the same time as the annotation * restoration.
;;       Simplify use of START and END.
;; 2009/09/30 dadams
;;     bookmarkp-bmenu-regexp-mark: Remove binding of bookmark-alist.
;;     bookmark-bmenu-(un)mark, bookmarkp-bmenu-edit-bookmark (remove first call only),
;;       bookmark-bmenu-other-window, bookmark-bmenu-rename, bookmarkp-bmenu-restore-marks:
;;         Remove bookmark-bmenu-check-position (done by bookmark-bmenu-bookmark anyway).
;;     bookmark-insert-location: Fix interactive spec for Emacs < 22.
;;     bookmark-location: Return "" instead of raising error, if no location found.
;;     bookmarkp-current-sec-time: Move the let: do not call current-time unless we need to.
;;     bookmarkp-bmenu-unmark-all: forward-line only 1, not 2.  Thx to Thierry.
;;     bookmark-bmenu-mode: Updated doc string - bindings and mention options.
;;     bookmarkp-bmenu-propertize-item: For buffer, check also against "   - no file -".
;; 2009/09/29 dadams
;;     bookmark-bmenu-unmark: Use delete, not remove.
;;     Removed: bookmark-bmenu-check-position, bookmarkp-maybe-sort.
;;     Added: bookmarkp-sort-and-remove-dups, bookmarkp-remove-assoc-dups,
;;            bookmarkp-face-prop, bookmarkp-bad-bookmark, bookmark-menu-heading (Emacs 20,21),
;;            bookmark-bmenu-bookmark (redefinition).
;;     *-bmenu-toggle-show-only-*: Do not call-interactively.
;;     bookmarkp-bmenu-(un)mark-all:
;;       Handle bookmark-bmenu-toggle-filenames (wrapper).
;;       Remove bookmark-bmenu-check-position - just ensure within menu list.
;;     bookmarkp-bmenu-mark-all: Move save-excursion so it applies to all movements.
;;                               Message stating number marked.
;;     bookmarkp-bmenu-unmark-all: Use with-current-buffer ensure in menu list.
;;                                 Use bookmark-bmenu-unmark.
;;     Fixed U bindings for bookmarkp-bmenu-unmark-all.
;;     bookmarkp-bmenu-regexp-mark:
;;       Remove bookmark-bmenu-check-position - just ensure in menu list.
;;     bookmarkp-bmenu-toggle-marks: Use forward-line 2, to ensure in menu list.
;;                                   Message stating number marked.
;;     bookmark-bmenu-list, bookmarkp-bmenu-propertize-item: Use bookmarkp-face-prop.
;;     bookmark-bmenu-list: Don't start applying the faces until column 2.
;;     Removed key bindings in bookmark-map for *-toggle-show-only-*.
;;     Redefined faces, esp. for a light background.
;;     Use font-lock-face or face property, depending on Emacs version.
;;
;; 2009-06-09 to 2009-09-27 Thierry Volpiatto and dadams
;;     New features, as follows.
;;       See also the change log at
;;         http://mercurial.intuxication.org/hg/bookmark-icicle-region/.
;;       2090-09-27 Rewrote sorting and unmarking code.  (+ Updates to doc, names.)
;;                    Unmarking is now like Dired & query-replace.
;;                    Sorting is via one sort function; sort predicates do all the sorting.
;;                    Can now cycle sort orders with S S S...
;;                    Sort cmds now cycle among normal, reverse, off.
;;                    Add: *-define-sort-command (macro), *-assoc-delete-all, *-upcase,
;;                         *-get-visits-count, *-get-visit-time, *-sort-functions-alist.
;;                  Remove docstring from defalias (for Emacs 20).
;;       2009-09-26 Fix *-bmenu-mode doc (defadvice).
;;       2009-09-25 *-bmenu-edit, *-bmenu-sort-1: Fix bmk retrieval code.
;;                  Redefine *-bmenu-unmark.  Add: *-bmenu-toggle-marks.
;;                  Bind *-bmenu-unmark-all-bookmarks to M-DEL.  Reorder code.
;;                  Rename: *-bmenu-unmark-all-(bookmarks|(delete|mark)-flag)',
;;                          *-bmenu-unmark-all-bookmarks-1.
;;                  Change sort predicates in defalias.  Rename bmk entry visit to visits.
;;                  Remove: *-bmenu-show-number-of-visit.
;;       2009-09-22 Rewrote sorting code.  Renamed unmarking fns.
;;       2009-09-21 Rename mark/unmark cmds to have -bmenu.
;;                  Add: *-bmenu-called-from-inside-flag - set it in (un)hide marks fns.
;;       2009-09-20 *-write-file: Remove text properties before saving.
;;                  Remove all marks only in current display.
;;       2009-09-19 *-current-sec-time: Protect with fboundp for Emacs 20.
;;                  *-bmenu-sort-1: Add msg showing sort method.
;;                  Change key S-A to S-S (A is annotations).
;;       2009-09-18 Improve sorting by visit frequency.  Always increment when jump.
;;                  Fix increment visit fn.  Allow sorting by last visited.
;;                  When visit values are equal, sort with string-lessp.
;;                  Add TIME bookmark-alist entry.  *-make-record-default: Add time entry.
;;                  Fix: bad parens, errors in sorting predicate.  Rename fns.  
;;                  Use single fn to sort using diff methods.
;;                  Add: *-bmenu-refresh-alist (bind to g).
;;       2009-09-16 Add: *-toggle-sorting-by-most-visited, *-reset-visit-flag,
;;                       *-bmenu-show-number-of-visit.
;;                  Redefine *-prop-set.  Improve *-toggle-sorting-by-most-visited.
;;                  Add auto-doc to header.  *-bmenu-mode: Add missing key.
;;                  Update menu-list after jumping.
;;                  Increment save counter when jump with visit flag.
;;       2009-09-15 Record number of visits.  Added sorting by most visits.
;;       2009-09-14 Add doc string.  Update defadvice doc string wrt keys.
;;       2009-09-12 Add: fns to mark all, unmark D or > or all, *-bmenu-reset-alist.
;;                  Fix keymap (Emacs 20).  *-unmark-all-bookmarks1: Move the save-excursion.
;;       2009-09-11 Add: *-bmenu-check-position (redef to improve performance),
;;                       *-unmark-all-bookmarks, *-current-list-have-marked-p,
;;                       *-bookmark-marked-p, *-(non-)marked-bookmarks-only.
;;                  *-bmenu-hide-unmarked: Add toggling.  Restore lost fn.
;;                  Reorder code.  Bind cmds in *-bmenu-mode-map.
;;                  *-bmenu-hide-marked: Do not hide if no marked in current filter.
;;                  Improve: *-bmenu-hide(-not)-marked-bookmark, (un)hide marked fns.
;;       2009-09-10 Fix *--restore-all-mark, *-bmenu-regexp-mark.
;;                  *-bmenu-list: Add *-restore-all-mark.
;;                  *-bmenu-mark: Push marked bmk to marked list.
;;                  Add: bookmarkp-bookmark-marked-list, *-bmenu-quit.
;;       2009-09-09 *-maybe-sort-alist: Use copy-sequence.
;;                  So remove fixes for *-rename, *-edit-bookmark.
;;                  *-yank, *-rename', *-set: Fix yanking.
;;                  Remove non-file bmks from file-only list.
;;                  Add: *-bmenu-list-only-non-file-bookmarks, *-maybe-message (Emacs 20),
;;                       *-bmenu-mark-bookmark-matching-regexp, *-bmenu-hide-marked-bookmark,
;;                       *-bmenu-hide-not-marked-bookmark, *-bmenu-mark (redefinition).
;;                  *-write-file: Improve performance.
;;                  *-non-file-alist-only: Remove unused def.
;;                  Fix: hide marked/unmarked with toggle-filenames, keymap for Emacs 20.
;;                  Improve comments, doc strings.
;;                  *-bmenu-mark-bookmark-matching-regexp: Fix while loop.
;;       2009-09-08 bookmark-store: Remove duplicate setq of *-current-bookmark.
;;       2009-09-07 Reorganize (reorder), add comments, improve doc strings.
;;                  Change binding of *-bmenu-relocate from R to M-r.
;;       2009-09-06 bookmark-rename: Redefine with new arg BATCH.
;;                  *-bmenu-rename: Go to new pos, not old.
;;                  *-edit-bookmark, bookmark-rename: Fix display update for Emacs 20.
;;       2009-09-05 Add: *-edit-bookmark, *-bmenu-edit-bookmark, *-maybe-save-bookmark.
;;       2009-09-04 Require cl.  Allow RET in Emacs 20.  Add doc string.
;;                  *-fix-bookmark-alist-and-save:
;;       2009-09-03 Fix *-fix-bookmark-alist-and-save:
;;                    Use error, not message.  Change value for setcdr.
;;                    Do not use push with non-var (cl).
;;                  bookmark-delete:
;;                    Redefine, to fix vanilla bug: increment count even when BATCHP is non-nil.
;;                  *-non-file-name: Change to - no file -.  *-bmenu-list: Add arg FILTER-ON.
;;                  *-bmenu-execute-deletions: Use delete, not remove.
;;                  Add: *-replace-regexp-in-string.
;;                  bookmark-set: Fix *-yank-point for region case.  Fix bad parens.
;;       2009-09-02 Add: *-non-file-filename.  *-fix-bookmark-alist-and-save: Fix msg.
;;                  Require cl (gensym).  *-at-bol/eol' -> line-*-position (for Emacs 20).
;;                  Redefine *-bmenu-execute-deletions,
;;                           *-bmenu-surreptitiously-rebuild-list. 
;;                  Update current filtered display - do not reload & display all bmks.
;;                  Add redefinitions of *-bmenu-rename', *-yank-word to fix vanilla bugs:
;;                    *-bmenu-rename: Do not call *-bmenu-list twice.
;;                  *-yank-word: Do not insert whitespace.
;;                  Rename *-last-bookmark-alist-in-use to *-latest-bookmark-alist.
;;       2009-09-01 Fix: Loading of new doc for bookmark-alist (add vacuous defvar).
;;                       *-bmenu-(list|hide-filenames): start -> end, end -> start.
;;                  Removed extraneous quote mark that caused problems.
;;                  Save only if condition-case exits OK.
;;       2009-08-31 Fixes: Test for non-file bmk.  Filename for Gnus bmks.
;;                         Compatibility of bookmark-alist with vanilla Emacs.
;;                         Require info.el and ffap.el when needed.
;;                  Add: *-line-number-at-pos (for Emacs 20),
;;                       *-bmenu-other-window (redefinition).
;;                  Rename *-propertize-bookmark-list to *-propertize-bmenu-item.
;;       2009-08-30 Fix: Increment *-alist-modification-count when relocate region,
;;                       and maybe save.
;;                  Move code adding properties to bookmarks out of *-bmenu-list.
;;                  mapc -> mapcar.  *-bmenu-hide-filenames: Redefine.
;;       2009-08-29 Remove refresh code.
;;       2009-08-27 Added: *-local-directory-bookmark-p, *-local-file-alist-only,
;;                         *-non-file-alist-only.
;;                  *-file-bookmark-p: Redefined to exclude bmks with handlers.
;;                  Renamed fns and faces.
;;       2009-08-25 Fit frame after display menu list.
;;                  Refresh list when toggle filename visibility.
;;       2009-08-24 Fix: *-bmenu-list for remote files, bookmark-set, *-remote-file-bookmark-p.
;;                  Ensure arg to file-remote-p is not nil.
;;                  Recenter region only if it is visible.
;;       2009-08-23 Remove old *-location.  *-bmenu-list: Add isw3m.
;;                  bookmark-set:
;;                    Redefine for older Emacs. Use a default prompt for gnus, w3m.
;;                    Use *-name-length-max for title when region is active.
;;                    Ensure bookmark is on one line.
;;       2009-08-22 Try to handle tramp ftp files.
;;                  Do not fail if bookmark has empty filename entry.
;;                  Show region end pos using exchange-point-and-mark.
;;       2009-08-21 Remove all cl stuff (list*, loop, etc.).  Add *-remove-if(-not).
;;                  Remove compile-time require of cl.
;;                  Add predicates *-(region|gnus|w3m|info|(remote-|local-)file)-bookmark-p.
;;                  Redefine alist-only functions to optimize and use new preds.
;;       2009-08-20 *--jump-via: Fix to show relocated region before ask whether to save.
;;                  *-relocate-region: Fix ar-str.  Rename a var.  Add: *-region-activated-p.
;;                  Revert chgs.
;;       2009-08-19 Update/fix commentary: bookmark-alist, linkd.
;;                  *-default-handler, *-handle-region-default:
;;                    Get bmk record from name only once.
;;                  *-save-new-region-location: Move t inside progn.
;;       2009-08-16 Use prefix bookmarkp where appropriate.
;;       2009-08-15 Improve comments, doc strings.  Rename fns, vars.
;;                  Add :group with prefix bookmarkp.
;;       2009-08-09 Fix doc strings.
;;       2009-08-08 bookmark-set: Update doc string.  Show keys in C-h m.
;;       2009-08-07 *-jump: Fix to jump in same window (thx to Henry Atting).
;;                  *-at-bol/eol' -> line-*-position.
;;       2009-08-01 bookmark-store: Fix for Emacs 20.
;;       2009-07-27 Ensure we start on an empty w3m buffer.  Add: *-w3m-allow-multi-tabs.
;;       2009-07-24 *-bmenu-mode-map: Define some new keys.
;;       2009-07-23 *-bmenu-list: Add path to file in help-echo.
;;       2009-07-19 Fix title underline.  Highlight bookmark if root logged with tramp.
;;                  Add face for sudo.
;;       2009-07-18 Add: filter functions, option for bookmark-bmenu-list.
;;                  Remove toggle region.
;;                  *-bmenu-list-only-files-entries: Add prefix arg to show remote.
;;       2009-07-14 Add a forgotten test.
;;       2009-07-13 Fix errors.  Give pos in msg even if no search.
;;                  *-from-bob/eob: Fixed like old strict.
;;                  Remove *-relocate-region-(method|from-limits).
;;                  Remove unused code in record fns.  Add: *-relocate-region-function.
;;       2009-07-12 Do not pass args to relocation routines.  Remove use of flet.
;;                  Use skip-chars-*ward.  Use forward-line, not beginning-of-line.
;;                  Remove save-excursion around message.  Correct typo f(ree var BMK).
;;       2009-07-11 Fix *-relocate-region-strict.  Rename fns, adjust defcustom.
;;                  Save relocated region after pushing mark.  Add comments.
;;       2009-07-10 New retrieve fn.  Add looking-* fns.
;;       2009-07-08 Simplify record fns.  Add doc strings.  Add: *-save-relocated-position.
;;                  Fix: updating when relocate (wrt new record fns), string closing,
;;                       free vars, parens, names.
;;       2009-07-06 Fix: *-bmenu-list wrt windows, Info colors.
;;       2009-07-04 Rename fns to record, vars, args of retrieve fns.  Big changes, fixes.
;;       2009-07-01 Fix comments.  *-retrieve-region-strict: improve when out of context.
;;       2009-06-30 Fix: free vars, *-retrieve-region, provide (name).
;;       2009-06-29 Fix: w3m handler, file name for non-file, *-simple-retrieve-position.
;;                  Add: *-retrieve-region-strict.
;;       2009-06-28 Add: *-retrieve-region-method-is, *-retrieve-region-lax,
;;                       fns to retrieve regions.
;;                  Use buffer again, not buffer-name.
;;       2009-06-27 Fix wrong-type error no such file.  Renamed faces.  Add: *-prop-set.
;;                  Load gnus at compile time.  Protect tramp-file-name-regexp with boundp.
;;       2009-06-25 Fixes for older Emacs compatibility.
;;       2009-06-24 Improve *-default-handler.
;;                  Add: *-always-save-relocated-position, *-prop-get.
;;       2009-06-23 Use search-regexp, not re-search-regexp.  Add Gnus bmks.  Add doc.
;;                  Fix *-bmenu-list.
;;       2009-06-21 Fix: *-default-handler for Info.  Improve doc strings, commentary.
;;                  Fixes to be compatible with Emacs 20-22.
;;                  Use defcustom for *-list-only-regions-flag.
;;                  *jump: Put prefix arg in interactive spec.  Use buffer-name, not buffer.
;;                  Remove require of Tramp and inline Tramp fns.
;;                  Remove tests for display-(color|mouse)-p.
;;                  w3m-bookmark-(jump|make-record): require w3m.
;;       2009-06-20 Update context strings when relocate.
;;                  Fix: bookmark-get-*: search from point-min.
;;       2009-06-19 Fix: *-make-record-default, *-toggle-use-only-regions, *-default-handler,
;;                       bookmarking Dired.
;;                  Handle 4 positions in *-default-handler.
;;       2009-06-17 Fix: case where some bookmarked text was removed, *-use-region.
;;       2009-06-15 Fix *-region-alist-only, *-get-buffername, *-location,
;;                      non-file (buffer) bookmarks.
;;                  Support w3m similar to Info.
;;       2009-06-14 Fix bookmark+version, region relocation.  Info support.  Error handling.
;;       2009-06-13 Fix: *-list-only-regions, *-region-handler, *-make-record, keymap, faces.
;;                  Put region & info handling in *-default-handler, not separate handlers.
;;                  Merge *-make-record-region to *-make-record-default.
;;                  *-jump now negates *-use-region if prefix arg.  Raise error if bad bmk.
;;       2009-06-12 Add: *-get-endposition, *-region-alist-only-names.
;;                  Add filter to show only region bookmarks.
;;                  Faces for menu list.  Change region color.
;;       2009-06-11 Add: *-region-search-size, *-get-buffername, *-use-region.
;;                  Redefine *-handle-bookmark, *-jump, to fit bookmark-use-region.
;;                  Add condtions to bookmark-make-record.  Support w3m.  Support t command.
;;       2009-06-10 Fix search regexp.  Fix region in Info. Save bookmark if region moves.
;;       2009-06-09 Added: bookmark-make-record(-region), bookmark-region-handler.
;;                  Relocation.
;; 2009/05/25 dadams
;;     Added redefinition of bookmark-get-bookmark-record.
;; 2008/10/16 dadams
;;     bookmark-jump-other-window: Don't define it for Emacs 23+ (not needed).
;; 2008/04/04 dadams
;;     bookmark-jump-other-window: Updated wrt Emacs 22.2.
;; 2007/10/07 dadams
;;     Added: bookmark-completing-read, bookmark-delete, bookmark-insert(-location),
;;            bookmark-jump, bookmark-relocate, bookmark-rename.
;;     bookmark-jump-other-window: Use new bookmark-completing-read.
;; 2007/07/13 dadams
;;     Replaced Emacs version tests to reflect Emacs 22 release.
;; 2006/03/08 dadams
;;     bookmark-jump-other-window: Handle nil arg.
;; 2005/05/17 dadams
;;     Updated to work with Emacs 22.x.
;; 2004/11/20 dadams
;;     Refined to deal with Emacs 21 < 21.3.50 (soon to be 22.x)
;; 2004/10/26 dadams
;;     Different menu-bar command, depending on Emacs version.
;; 2004/09/21 dadams
;;     Only define bookmark-menu-jump-other-window if < Emacs 22.
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

;; You need not load this file.  It contains only documentation.

(provide 'bookmark+-chg)                ; Not used.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-chg.el ends here

