;;; bookmark+-1.el - First part of package Bookmark+.
;;
;; Filename: bookmark+-1.el
;; Description: First part of package Bookmark+.
;; Author: Drew Adams, Thierry Volpiatto
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2017, Drew Adams, all rights reserved.
;; Copyright (C) 2009, Thierry Volpiatto.
;; Created: Mon Jul 12 13:43:55 2010 (-0700)
;; Last-Updated: Sun Dec  3 15:54:34 2017 (-0800)
;;           By: dradams
;;     Update #: 8583
;; URL: https://www.emacswiki.org/emacs/download/bookmark%2b-1.el
;; Doc URL: http://www.emacswiki.org/BookmarkPlus
;; Keywords: bookmarks, bookmark+, placeholders, annotations, search, info, url, eww, w3m, gnus
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `bookmark', `bookmark+-1', `ffap', `kmacro', `pp', `thingatpt',
;;   `thingatpt+'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) library
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit.el' - (optional) code for highlighting bookmarks
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (bmenu)
;;    `bookmark+-1.el'   - other (non-bmenu) required code (this file)
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
;;  (@> "User Options (Customizable)")
;;  (@> "Internal Variables")
;;  (@> "Compatibility Code for Older Emacs Versions")
;;  (@> "Core Replacements (`bookmark-*' except `bookmark-bmenu-*')")
;;  (@> "Bookmark+ Functions (`bmkp-*')")
;;    (@> "Search-and-Replace Locations of Marked Bookmarks")
;;    (@> "Tags")
;;    (@> "Bookmark Predicates")
;;    (@> "Filter Functions")
;;    (@> "General Utility Functions")
;;    (@> "Bookmark Entry Access Functions")
;;    (@> "Sorting - General Functions")
;;    (@> "Sorting - Commands")
;;    (@> "Sorting - General Predicates")
;;    (@> "Sorting - File-Name Predicates")
;;    (@> "Indirect Bookmarking Functions")
;;    (@> "Other Bookmark+ Functions (`bmkp-*')")
;;  (@> "Keymaps")
 
;;(@* "Things Defined Here")
;;
;;  Things Defined Here
;;  -------------------
;;
;;  Commands defined here:
;;
;;    `bmkp-add-tags', `bmkp-all-tags-jump',
;;    `bmkp-all-tags-jump-other-window', `bmkp-all-tags-regexp-jump',
;;    `bmkp-all-tags-regexp-jump-other-window',
;;    `bmkp-annotate-bookmark', `bmkp-autofile-add-tags',
;;    `bmkp-autofile-all-tags-jump',
;;    `bmkp-autofile-all-tags-jump-other-window',
;;    `bmkp-autofile-all-tags-regexp-jump',
;;    `bmkp-autofile-all-tags-regexp-jump-other-window',
;;    `bmkp-autofile-jump', `bmkp-autofile-jump-other-window',
;;    `bmkp-autofile-remove-tags', `bmkp-autofile-set',
;;    `bmkp-autofile-some-tags-jump',
;;    `bmkp-autofile-some-tags-jump-other-window',
;;    `bmkp-autofile-some-tags-regexp-jump',
;;    `bmkp-autofile-some-tags-regexp-jump-other-window',
;;    `bmkp-auto-idle-bookmark-mode', `bmkp-autonamed-jump',
;;    `bmkp-autonamed-jump-other-window',
;;    `bmkp-autonamed-this-buffer-jump',
;;    `bmkp-autonamed-this-buffer-jump-other-window',
;;    `bmkp-bookmark-a-file' `bmkp-bookmark-file-jump',
;;    `bmkp-bookmark-linked-at' (Emacs 22+),
;;    `bmkp-bookmark-linked-at-mouse' (Emacs 22+),
;;    `bmkp-bookmark-list-jump',
;;    `bmkp-bookmark-set-confirm-overwrite',
;;    `bmkp-choose-navlist-from-bookmark-list',
;;    `bmkp-choose-navlist-of-type', `bmkp-compilation-target-set',
;;    `bmkp-compilation-target-set-all', `bmkp-convert-eww-bookmarks'
;;    (Emacs 25+), `bmkp-copy-tags', `bmkp-crosshairs-highlight',
;;    `bmkp-cycle', `bmkp-cycle-autonamed',
;;    `bmkp-cycle-autonamed-other-window', `bmkp-cycle-bookmark-list',
;;    `bmkp-cycle-bookmark-list-other-window', `bmkp-cycle-desktop',
;;    `bmkp-cycle-dired', `bmkp-cycle-dired-other-window',
;;    `bmkp-cycle-file', `bmkp-cycle-file-other-window',
;;    `bmkp-cycle-gnus', `bmkp-cycle-gnus-other-window',
;;    `bmkp-cycle-info', `bmkp-cycle-info-other-window',
;;    `bmkp-cycle-lighted', `bmkp-cycle-lighted-other-window',
;;    `bmkp-cycle-local-file', `bmkp-cycle-local-file-other-window',
;;    `bmkp-cycle-man', `bmkp-cycle-man-other-window',
;;    `bmkp-cycle-non-file', `bmkp-cycle-non-file-other-window',
;;    `bmkp-cycle-other-window', `bmkp-cycle-remote-file',
;;    `bmkp-cycle-remote-file-other-window',
;;    `bmkp-cycle-specific-buffers',
;;    `bmkp-cycle-specific-buffers-other-window',
;;    `bmkp-cycle-specific-files',
;;    `bmkp-cycle-specific-files-other-window',
;;    `bmkp-cycle-this-buffer', `bmkp-cycle-this-buffer-other-window',
;;    `bmkp-cycle-this-file', `bmkp-cycle-this-file/buffer',
;;    `bmkp-cycle-this-file/buffer-other-window',
;;    `bmkp-cycle-this-file-other-window', `bmkp-cycle-variable-list',
;;    `bmkp-cycle-url', `bmkp-cycle-url-other-window',
;;    `bmkp-delete-all-autonamed-for-this-buffer',
;;    `bmkp-delete-all-temporary-bookmarks', `bmkp-delete-bookmarks',
;;    `bmkp-describe-bookmark', `bmkp-describe-bookmark-internals',
;;    `bmkp-desktop-change-dir', `bmkp-desktop-delete',
;;    `bmkp-desktop-jump', `bmkp-desktop-read', `bmkp-dired-jump',
;;    `bmkp-dired-jump-other-window', `bmkp-dired-this-dir-jump',
;;    `bmkp-dired-this-dir-jump-other-window',
;;    `bmkp-edit-bookmark-name-and-location',
;;    `bmkp-edit-bookmark-record', `bmkp-edit-bookmark-record-send',
;;    `bmkp-edit-bookmark-records-send', `bmkp-edit-tags',
;;    `bmkp-edit-tags-send', `bmkp-edit-this-annotation',
;;    `bmkp-empty-file', `bmkp-eww-jump' (Emacs 25+),
;;    `bmkp-eww-jump-other-window' (Emacs 25+),
;;    `bmkp-eww-auto-bookmark-mode' (Emacs 25+),
;;    `bmkp-ffap-max-region-size', `bmkp-file-target-set',
;;    `bmkp-file-all-tags-jump',
;;    `bmkp-file-all-tags-jump-other-window',
;;    `bmkp-file-all-tags-regexp-jump',
;;    `bmkp-file-all-tags-regexp-jump-other-window', `bmkp-file-jump',
;;    `bmkp-file-jump-other-window', `bmkp-file-some-tags-jump',
;;    `bmkp-file-some-tags-jump-other-window',
;;    `bmkp-file-some-tags-regexp-jump',
;;    `bmkp-file-some-tags-regexp-jump-other-window',
;;    `bmkp-file-this-dir-all-tags-jump',
;;    `bmkp-file-this-dir-all-tags-jump-other-window',
;;    `bmkp-file-this-dir-all-tags-regexp-jump',
;;    `bmkp-file-this-dir-all-tags-regexp-jump-other-window',
;;    `bmkp-file-this-dir-jump',
;;    `bmkp-file-this-dir-jump-other-window',
;;    `bmkp-file-this-dir-some-tags-jump',
;;    `bmkp-file-this-dir-some-tags-jump-other-window',
;;    `bmkp-file-this-dir-some-tags-regexp-jump',
;;    `bmkp-file-this-dir-some-tags-regexp-jump-other-window',
;;    `bmkp-find-file', `bmkp-find-file-other-window',
;;    `bmkp-find-file-all-tags',
;;    `bmkp-find-file-all-tags-other-window',
;;    `bmkp-find-file-all-tags-regexp',
;;    `bmkp-find-file-all-tags-regexp-other-window',
;;    `bmkp-find-file-some-tags',
;;    `bmkp-find-file-some-tags-other-window',
;;    `bmkp-find-file-some-tags-regexp',
;;    `bmkp-find-file-some-tags-regexp-other-window',
;;    `bmkp-get-external-annotation',
;;    `bmkp-global-auto-idle-bookmark-mode' (Emacs 21+),
;;    `bmkp-gnus-jump', `bmkp-gnus-jump-other-window',
;;    `bmkp-image-jump', `bmkp-image-jump-other-window',
;;    `bmkp-info-auto-bookmark-mode' (Emacs 22+), `bmkp-info-jump',
;;    `bmkp-info-jump-other-window', `bmkp-insert-bookmark-link'
;;    (Emacs 22+), `bmkp-jump-in-navlist',
;;    `bmkp-jump-in-navlist-other-window',
;;    `bmkp-jump-to-bookmark-linked-at' (Emacs 22+),
;;    `bmkp-jump-to-bookmark-linked-at-mouse' (Emacs 22+),
;;    `bmkp-jump-to-type', `bmkp-jump-to-type-other-window',
;;    `bmkp-list-all-tags', `bmkp-list-defuns-in-commands-file',
;;    `bmkp-local-file-jump', `bmkp-local-file-jump-other-window',
;;    `bmkp-local-non-dir-file-jump',
;;    `bmkp-local-non-dir-file-jump-other-window',
;;    `bmkp-make-bookmark-savable', `bmkp-make-bookmark-temporary',
;;    `bmkp-make-function-bookmark', `bmkp-man-jump',
;;    `bmkp-man-jump-other-window', `bmkp-menu-jump-other-window'
;;    (Emacs 20, 21), `bmkp-navlist-bmenu-list',
;;    `bmkp-next-autonamed-bookmark',
;;    `bmkp-next-autonamed-bookmark-repeat', `bmkp-next-bookmark',
;;    `bmkp-next-bookmark-list-bookmark',
;;    `bmkp-next-bookmark-list-bookmark-repeat',
;;    `bmkp-next-bookmark-repeat', `bmkp-next-bookmark-this-buffer',
;;    `bmkp-next-bookmark-this-buffer-repeat',
;;    `bmkp-next-bookmark-this-file',
;;    `bmkp-next-bookmark-this-file/buffer',
;;    `bmkp-next-bookmark-this-file/buffer-repeat',
;;    `bmkp-next-bookmark-this-file-repeat', `bmkp-next-bookmark-w32',
;;    `bmkp-next-bookmark-w32-repeat', `bmkp-next-desktop-bookmark',
;;    `bmkp-next-desktop-bookmark-repeat', `bmkp-next-dired-bookmark',
;;    `bmkp-next-dired-bookmark-repeat', `bmkp-next-file-bookmark',
;;    `bmkp-next-file-bookmark-repeat', `bmkp-next-gnus-bookmark',
;;    `bmkp-next-gnus-bookmark-repeat', `bmkp-next-info-bookmark',
;;    `bmkp-next-info-bookmark-repeat', `bmkp-next-lighted-bookmark',
;;    `bmkp-next-lighted-bookmark-repeat',
;;    `bmkp-next-local-file-bookmark',
;;    `bmkp-next-local-file-bookmark-repeat',
;;    `bmkp-next-man-bookmark', `bmkp-next-man-bookmark-repeat',
;;    `bmkp-next-non-file-bookmark',
;;    `bmkp-next-non-file-bookmark-repeat',
;;    `bmkp-next-remote-file-bookmark',
;;    `bmkp-next-remote-file-bookmark-repeat',
;;    `bmkp-next-specific-buffers-bookmark',
;;    `bmkp-next-specific-buffers-bookmark-repeat',
;;    `bmkp-next-specific-files-bookmark',
;;    `bmkp-next-specific-files-bookmark-repeat',
;;    `bmkp-next-variable-list-bookmark',
;;    `bmkp-next-variable-list-bookmark-repeat',
;;    `bmkp-next-url-bookmark', `bmkp-next-url-bookmark-repeat',
;;    `bmkp-non-dir-file-jump', `bmkp-non-dir-file-jump-other-window',
;;    `bmkp-non-file-jump', `bmkp-non-file-jump-other-window',
;;    `bmkp-occur-create-autonamed-bookmarks',
;;    `bmkp-ORIG-bookmark-insert', `bmkp-occur-target-set',
;;    `bmkp-occur-target-set-all', `bmkp-paste-add-tags',
;;    `bmkp-paste-replace-tags', `bmkp-previous-bookmark',
;;    `bmkp-previous-autonamed-bookmark',
;;    `bmkp-previous-autonamed-bookmark-repeat',
;;    `bmkp-previous-bookmark-list-bookmark',
;;    `bmkp-previous-bookmark-list-bookmark-repeat',
;;    `bmkp-previous-bookmark-repeat',
;;    `bmkp-previous-bookmark-this-buffer',
;;    `bmkp-previous-bookmark-this-buffer-repeat',
;;    `bmkp-previous-bookmark-this-file',
;;    `bmkp-previous-bookmark-this-file/buffer',
;;    `bmkp-previous-bookmark-this-file/buffer-repeat',
;;    `bmkp-previous-bookmark-this-file-repeat',
;;    `bmkp-previous-bookmark-this-buffer-repeat',
;;    `bmkp-previous-bookmark-this-file',
;;    `bmkp-previous-bookmark-this-file/buffer',
;;    `bmkp-previous-bookmark-this-file/buffer-repeat',
;;    `bmkp-previous-bookmark-this-file-repeat',
;;    `bmkp-previous-desktop-bookmark',
;;    `bmkp-previous-desktop-bookmark-repeat',
;;    `bmkp-previous-dired-bookmark',
;;    `bmkp-previous-dired-bookmark-repeat',
;;    `bmkp-previous-file-bookmark',
;;    `bmkp-previous-file-bookmark-repeat',
;;    `bmkp-previous-gnus-bookmark',
;;    `bmkp-previous-gnus-bookmark-repeat',
;;    `bmkp-previous-info-bookmark',
;;    `bmkp-previous-info-bookmark-repeat',
;;    `bmkp-previous-lighted-bookmark',
;;    `bmkp-previous-lighted-bookmark-repeat',
;;    `bmkp-previous-local-file-bookmark',
;;    `bmkp-previous-local-file-bookmark-repeat',
;;    `bmkp-previous-man-bookmark',
;;    `bmkp-previous-man-bookmark-repeat',
;;    `bmkp-previous-non-file-bookmark',
;;    `bmkp-previous-non-file-bookmark-repeat',
;;    `bmkp-previous-remote-file-bookmark',
;;    `bmkp-previous-remote-file-bookmark-repeat',
;;    `bmkp-previous-specific-buffers-bookmark',
;;    `bmkp-previous-specific-buffers-bookmark-repeat',
;;    `bmkp-previous-specific-files-bookmark',
;;    `bmkp-previous-specific-files-bookmark-repeat',
;;    `bmkp-previous-variable-list-bookmark',
;;    `bmkp-previous-variable-list-bookmark-repeat',
;;    `bmkp-previous-url-bookmark',
;;    `bmkp-previous-url-bookmark-repeat',
;;    `bmkp-previous-bookmark-w32',
;;    `bmkp-previous-bookmark-w32-repeat',
;;    `bmkp-purge-notags-autofiles', `bmkp-read-bookmark-for-type',
;;    `bmkp-region-jump',
;;    `bmkp-region-jump-narrow-indirect-other-window',
;;    `bmkp-region-jump-other-window', `bmkp-remote-file-jump',
;;    `bmkp-remote-file-jump-other-window',
;;    `bmkp-remote-non-dir-file-jump',
;;    `bmkp-temote-non-dir-file-jump-other-window',
;;    `bmkp-remove-all-tags', `bmkp-remove-tags',
;;    `bmkp-remove-tags-from-all', `bmkp-rename-tag',
;;    `bmkp-retrieve-icicle-search-hits',
;;    `bmkp-retrieve-more-icicle-search-hits',
;;    `bmkp-revert-bookmark-file', `bmkp-save-menu-list-state',
;;    `bmkp-send-bug-report', `bmkp-set-autonamed-bookmark',
;;    `bmkp-set-autonamed-bookmark-at-line',
;;    `bmkp-set-autonamed-regexp-buffer',
;;    `bmkp-set-autonamed-regexp-region',
;;    `bmkp-set-bookmark-file-bookmark', `bmkp-set-desktop-bookmark',
;;    `bmkp-set-dired-bookmark-for-files',
;;    `bmkp-set-eww-bookmark-here' (Emacs 25+),
;;    `bmkp-set-icicle-search-hits-bookmark',
;;    `bmkp-set-info-bookmark-with-node-name' (Emacs 22+),
;;    `bmkp-set-izones-bookmark', `bmkp-set-kmacro-bookmark' (Emacs
;;    22+), `bmkp-set-kmacro-list-bookmark' (Emacs 22+),
;;    `bmkp-set-sequence-bookmark', `bmkp-set-snippet-bookmark',
;;    `bmkp-set-tag-value', `bmkp-set-tag-value-for-navlist',
;;    `bmkp-set-variable-list-bookmark',
;;    `bmkp-show-this-annotation-read-only',
;;    `bmkp-snippet-to-kill-ring', `bmkp-some-tags-jump',
;;    `bmkp-some-tags-jump-other-window',
;;    `bmkp-some-tags-regexp-jump',
;;    `bmkp-some-tags-regexp-jump-other-window',
;;    `bmkp-specific-buffers-jump',
;;    `bmkp-specific-buffers-jump-other-window',
;;    `bmkp-specific-files-jump',
;;    `bmkp-specific-files-jump-other-window', `bmkp-store-org-link'
;;    (Emacs 24.4+), `bmkp-switch-bookmark-file',
;;    `bmkp-switch-bookmark-file-create',
;;    `bmkp-switch-to-last-bookmark-file', `bmkp-tag-a-file',
;;    `bmkp-temporary-bookmarking-mode', `bmkp-temporary-jump',
;;    `bmkp-temporary-jump-other-window',
;;    `bmkp-this-buffer-bmenu-list', `bmkp-this-buffer-jump',
;;    `bmkp-this-buffer-jump-other-window',
;;    `bmkp-this-file-bmenu-list', `bmkp-this-file/buffer-bmenu-list',
;;    `bmkp-toggle-autonamed-bookmark-set/delete',
;;    `bmkp-toggle-autotemp-on-set',
;;    `bmkp-toggle-bookmark-set-refreshes',
;;    `bmkp-toggle-eww-auto-type' (Emacs 25+),
;;    `bmkp-toggle-info-auto-type' (Emacs 22+),
;;    `bmkp-toggle-saving-bookmark-file',
;;    `bmkp-toggle-saving-menu-list-state',
;;    `bmkp-toggle-temporary-bookmark',
;;    `bmkp-turn-on-auto-idle-bookmark-mode' (Emacs 21+),
;;    `bmkp-unomit-all', `bmkp-untag-a-file', `bmkp-url-target-set',
;;    `bmkp-url-jump', `bmkp-url-jump-other-window',
;;    `bmkp-variable-list-jump', `bmkp-version',
;;    `bmkp-visit-external-annotation', `bmkp-w32-browser-jump',
;;    `bmkp-w3m-jump', `bmkp-w3m-jump-other-window',
;;    `bmkp-wrap-bookmark-with-last-kbd-macro'.
;;
;;  User options defined here:
;;
;;    `bmkp-annotation-modes-inherit-from', `bmkp-autofile-filecache',
;;    `bmkp-auto-idle-bookmark-min-distance',
;;    `bmkp-auto-idle-bookmark-mode-delay',
;;    `bmkp-auto-idle-bookmark-mode-lighter',
;;    `bmkp-auto-idle-bookmark-mode-set-function',
;;    `bmkp-autoname-bookmark-function', `bmkp-autoname-format',
;;    `bmkp-autotemp-bookmark-predicates',
;;    `bmkp-bookmark-name-length-max',
;;    `bmkp-count-multi-mods-as-one-flag', `bmkp-crosshairs-flag',
;;    `bmkp-default-bookmark-name',
;;    `bmkp-default-handlers-for-file-types',
;;    `bmkp-desktop-default-directory',
;;    `bmkp-desktop-jump-save-before-flag.',
;;    `bmkp-desktop-no-save-vars', `bmkp-eww-auto-type' (Emacs 25+),
;;    `bmkp-eww-buffer-handling' (Emacs 25+),
;;    `bmkp-eww-replace-keys-flag' (Emacs 25+),
;;    `bmkp-guess-default-handler-for-file-flag',
;;    `bmkp-handle-region-function', `bmkp-incremental-filter-delay',
;;    `bmkp-info-auto-type' (Emacs 22+),
;;    `bmkp-info-sort-ignores-directories-flag',
;;    `bmkp-last-as-first-bookmark-file',
;;    `bmkp-menu-popup-max-length', `bmkp-new-bookmark-default-names',
;;    `bmkp-other-window-pop-to-flag', `bmkp-prompt-for-tags-flag',
;;    `bmkp-properties-to-keep', `bmkp-read-bookmark-file-hook',
;;    `bmkp-region-search-size', `bmkp-save-new-location-flag',
;;    `bmkp-sequence-jump-display-function',
;;    `bmkp-show-end-of-region-flag', `bmkp-sort-comparer',
;;    `bmkp-su-or-sudo-regexp', `bmkp-tags-for-completion',
;;    `bmkp-temporary-bookmarking-mode',
;;    `bmkp-temporary-bookmarking-mode-hook',
;;    `bmkp-temporary-bookmarking-mode-lighter',
;;    `bmkp-this-file/buffer-cycle-sort-comparer', `bmkp-use-region',
;;    `bmkp-w3m-allow-multiple-buffers-flag',
;;    `bmkp-write-bookmark-file-hook'.
;;
;;  Non-interactive functions defined here:
;;
;;    `bmkext-jump-gnus', `bmkext-jump-man', `bmkext-jump-w3m',
;;    `bmkext-jump-woman', `bmkp-all-exif-data',
;;    `bmkp-all-tags-alist-only', `bmkp-all-tags-regexp-alist-only',
;;    `bmkp-alpha-cp', `bmkp-alpha-p', `bmkp-annotated-alist-only',
;;    `bmkp-annotated-bookmark-p', `bmkp-autofile-alist-only',
;;    `bmkp-autofile-all-tags-alist-only',
;;    `bmkp-autofile-all-tags-regexp-alist-only',
;;    `bmkp-autofile-bookmark-p',
;;    `bmkp-autofile-some-tags-alist-only',
;;    `bmkp-autofile-some-tags-regexp-alist-only',
;;    `bmkp-autoname-bookmark-function-default',
;;    `bmkp-autonamed-alist-only',
;;    `bmkp-autonamed-bookmark-for-buffer-p',
;;    `bmkp-autonamed-bookmark-p',
;;    `bmkp-autonamed-this-buffer-alist-only',
;;    `bmkp-autonamed-this-buffer-bookmark-p',
;;    `bmkp-bookmark-creation-cp', `bmkp-bookmark-data-from-record',
;;    `bmkp-bookmark-description', `bmkp-bookmark-last-access-cp',
;;    `bmkp-bookmark-file-alist-only',
;;    `bmkp-bookmark-file-bookmark-p',
;;    `bmkp-bookmark-list-alist-only',
;;    `bmkp-bookmark-list-bookmark-p', `bmkp-bookmark-name-member',
;;    `bmkp-bookmark-record-from-name', `bmkp-bookmark-type',
;;    `bmkp-buffer-last-access-cp', `bmkp-buffer-names',
;;    `bmkp-compilation-file+line-at', `bmkp-completing-read-1',
;;    `bmkp-completing-read-bookmarks',
;;    `bmkp-completing-read-buffer-name',
;;    `bmkp-completing-read-file-name', `bmkp-completing-read-lax',
;;    `bmkp-cp-not', `bmkp-create-variable-list-bookmark',
;;    `bmkp-current-bookmark-list-state', `bmkp-current-sort-order',
;;    `bmkp-cycle-1', `bmkp-default-bookmark-file',
;;    `bmkp-default-bookmark-name', `bmkp-default-handler-for-file',
;;    `bmkp-default-handler-user', `bmkp-delete-autonamed-no-confirm',
;;    `bmkp-delete-autonamed-this-buffer-no-confirm',
;;    `bmkp-delete-bookmark-name-from-list',
;;    `bmkp-delete-temporary-no-confirm', `bmkp-desktop-alist-only',
;;    `bmkp-desktop-bookmark-p',
;;    `bmkp-desktop-file-p',`bmkp-desktop-kill', `bmkp-desktop-save',
;;    `bmkp-desktop-save-as-last', `bmkp-dired-alist-only',
;;    `bmkp-dired-bookmark-p', `bmkp-dired-remember-*-marks',
;;    `bmkp-dired-subdirs', `bmkp-dired-this-dir-alist-only',
;;    `bmkp-dired-wildcards-alist-only',
;;    `bmkp-dired-this-dir-bookmark-p',
;;    `bmkp-dired-wildcards-bookmark-p',
;;    `bmkp-edit-bookmark-record-mode',
;;    `bmkp-edit-bookmark-records-mode', `bmkp-edit-tags-mode',
;;    `bmkp-end-position-post-context',
;;    `bmkp-end-position-pre-context', `bmkp-every',
;;    `bmkp-eww-alist-only' (Emacs 25+), `bmkp-eww-bookmark-p' (Emacs
;;    25+), `bmkp-eww-cp' (Emacs 25+), `bmkp-eww-new-buffer-name'
;;    (Emacs 25+), `bmkp-eww-sans-pop-to-buffer' (Emacs 25+),
;;    `bmkp-eww-rename-buffer' (Emacs 25+), `bmkp-eww-title' (Emacs
;;    25+), `bmkp-eww-url' (Emacs 25+), `bmkp-ffap-guesser',
;;    `bmkp-file-alist-only', `bmkp-file-all-tags-alist-only',
;;    `bmkp-file-all-tags-regexp-alist-only', `bmkp-file-alpha-cp',
;;    `bmkp-file-attribute-0-cp', `bmkp-file-attribute-1-cp',
;;    `bmkp-file-attribute-2-cp', `bmkp-file-attribute-3-cp',
;;    `bmkp-file-attribute-4-cp', `bmkp-file-attribute-5-cp',
;;    `bmkp-file-attribute-6-cp', `bmkp-file-attribute-7-cp',
;;    `bmkp-file-attribute-8-cp', `bmkp-file-attribute-9-cp',
;;    `bmkp-file-attribute-10-cp', `bmkp-file-attribute-11-cp',
;;    `bmkp-file-bookmark-p', `bmkp-file-names', `bmkp-file-remote-p',
;;    `bmkp-file-some-tags-alist-only',
;;    `bmkp-file-some-tags-regexp-alist-only',
;;    `bmkp-file-this-dir-alist-only',
;;    `bmkp-file-this-dir-all-tags-alist-only',
;;    `bmkp-file-this-dir-all-tags-regexp-alist-only',
;;    `bmkp-file-this-dir-bookmark-p',
;;    `bmkp-file-this-dir-some-tags-alist-only',
;;    `bmkp-file-this-dir-some-tags-regexp-alist-only',
;;    `bmkp-find-tag-default-as-regexp' (Emacs 22-24.2),
;;    `bmkp-flagged-bookmark-p', `bmkp-flagged-cp', `bmkp-float-time',
;;    `bmkp-format-spec', `bmkp-full-tag', `bmkp-function-alist-only',
;;    `bmkp-function-bookmark-p', `bmkp-get-autofile-bookmark',
;;    `bmkp-get-bookmark-in-alist', `bmkp-get-buffer-name',
;;    `bmkp-get-end-position', `bmkp-get-eww-mode-buffer' (Emacs 25+),
;;    `bmkp-get-tag-value', `bmkp-get-tags', `bmkp-get-visit-time',
;;    `bmkp-get-visits-count', `bmkp-gnus-alist-only',
;;    `bmkp-gnus-bookmark-p', `bmkp-gnus-cp', `bmkp-goto-position',
;;    `bmkp-handle-region-default',
;;    `bmkp-handle-region+narrow-indirect', `bmkp-handler-cp',
;;    `bmkp-handler-pred', `bmkp-has-tag-p',
;;    `bmkp-icicles-search-hits-alist-only',
;;    `bmkp-icicles-search-hits-bookmark-p', `bmkp-image-alist-only',
;;    `bmkp-image-bookmark-p', `bmkp-info-alist-only',
;;    `bmkp-info-bookmark-p', `bmkp-info-node-name-cp',
;;    `bmkp-info-position-cp', `bmkp-isearch-bookmarks' (Emacs 23+),
;;    `bmkp-isearch-bookmarks-regexp' (Emacs 23+),
;;    `bmkp-isearch-next-bookmark-buffer' (Emacs 23+), `bmkp-jump-1',
;;    `bmkp-jump-bookmark-file', `bmkp-jump-bookmark-list',
;;    `bmkp-jump-desktop', `bmkp-jump-dired', `bmkp-jump-eww' (Emacs
;;    25+), `bmkp-jump-eww-in-buffer-*eww*' (Emacs 25+),
;;    `bmkp-jump-eww-renaming-buffer' (Emacs 25+),
;;    `bmkp-jump-function', `bmkp-jump-gnus',
;;    `bmkp-jump-icicle-search-hits', `bmkp-jump-kmacro-list' (Emacs
;;    22+), `bmkp-jump-man', `bmkp-jump-sequence',
;;    `bmkp-jump-snippet', `bmkp-jump-url-browse',
;;    `bmkp-jump-variable-list', `bmkp-jump-w3m',
;;    `bmkp-jump-w3m-new-buffer', `bmkp-jump-w3m-new-buffer',
;;    `bmkp-jump-w3m-only-one-buffer',
;;    `bmkp-jump-w3m-only-one-buffer', `bmkp-jump-woman',
;;    `bmkp-kmacro-list-bookmark-p',
;;    `bmkp-last-specific-buffer-alist-only',
;;    `bmkp-last-specific-buffer-p',
;;    `bmkp-last-specific-file-alist-only',
;;    `bmkp-last-specific-file-p', `bmkp-line-number-at-pos',
;;    `bmkp-list-position', `bmkp-local-directory-bookmark-p',
;;    `bmkp-local-file-accessed-more-recently-cp',
;;    `bmkp-local-file-alist-only', `bmkp-local-file-bookmark-p',
;;    `bmkp-local-file-size-cp', `bmkp-local-file-type-cp',
;;    `bmkp-local-non-dir-file-alist-only',
;;    `bmkp-local-non-dir-file-bookmark-p',
;;    `bmkp-local-file-updated-more-recently-cp',
;;    `bmkp-make-bookmark-file-record',
;;    `bmkp-make-bookmark-list-record', `bmkp-make-desktop-record',
;;    `bmkp-make-dired-record', `bmkp-make-eww-record' (Emacs 25+),
;;    `bmkp-make-gnus-record', `bmkp-make-icicle-search-hits-record',
;;    `bmkp-make-kmacro-list-record' (Emacs 22+),
;;    `bmkp-make-man-record', `bmkp-make-plain-predicate',
;;    `bmkp-make-record-for-target-file', `bmkp-make-sequence-record',
;;    `bmkp-make-url-browse-record', `bmkp-make-variable-list-record',
;;    `bmkp-make-w3m-record', `bmkp-make-woman-record' (Emacs 21+),
;;    `bmkp-man-alist-only', `bmkp-man-bookmark-p',
;;    `bmkp-marked-bookmark-p', `bmkp-marked-bookmarks-only',
;;    `bmkp-marked-cp', `bmkp-maybe-save-bookmarks',
;;    `bmkp-modified-bookmark-p', `bmkp-modified-cp',
;;    `bmkp-msg-about-sort-order', `bmkp-multi-sort',
;;    `bmkp-names-same-bookmark-p', `bmkp-navlist-bookmark-p',
;;    `bmkp-new-bookmark-default-names',
;;    `bmkp-non-autonamed-alist-only', `bmkp-non-dir-file-alist-only',
;;    `bmkp-non-dir-file-bookmark-p', `bmkp-non-file-alist-only',
;;    `bmkp-non-file-bookmark-p', `bmkp-non-invokable-alist-only',
;;    `bmkp-non-invokable-bookmark-p',
;;    `bmkp-not-near-other-auto-idle-bmks', `bmkp-omitted-alist-only',
;;    `bmkp-orphaned-file-alist-only',
;;    `bmkp-orphaned-file-bookmark-p',
;;    `bmkp-orphaned-local-file-alist-only',
;;    `bmkp-orphaned-local-file-bookmark-p',
;;    `bmkp-orphaned-remote-file-alist-only',
;;    `bmkp-orphaned-remote-file-bookmark-p',
;;    `bmkp-pop-to-readable-marker', `bmkp-position-after-whitespace',
;;    `bmkp-position-before-whitespace', `bmkp-position-cp',
;;    `bmkp-position-post-context',
;;    `bmkp-position-post-context-region',
;;    `bmkp-position-pre-context', `bmkp-position-pre-context-region',
;;    `bmkp-printable-vars+vals', `bmkp-readable-p',
;;    `bmkp-read-bookmark-file-default',
;;    `bmkp-read-bookmark-file-name', `bmkp-read-from-whole-string',
;;    `bmkp-read-regexp', `bmkp-read-tag-completing',
;;    `bmkp-read-tags', `bmkp-read-tags-completing',
;;    `bmkp-read-variable', `bmkp-read-variables-completing',
;;    `bmkp-record-visit', `bmkp-refresh-latest-bookmark-list',
;;    `bmkp-refresh-menu-list', `bmkp-refresh/rebuild-menu-list',
;;    `bmkp-regexp-filtered-annotation-alist-only',
;;    `bmkp-regexp-filtered-bookmark-name-alist-only',
;;    `bmkp-regexp-filtered-file-name-alist-only',
;;    `bmkp-regexp-filtered-tags-alist-only',
;;    `bmkp-region-alist-only', `bmkp-region-bookmark-p',
;;    `bmkp-remote-file-alist-only', `bmkp-remote-file-bookmark-p',
;;    `bmkp-remote-non-dir-file-alist-only',
;;    `bmkp-remote-non-dir-file-bookmark-p', `bmkp-remove-dups',
;;    `bmkp-remove-if', `bmkp-remove-if-not', `bmkp-remove-omitted',
;;    `bmkp-rename-for-marked-and-omitted-lists',
;;    `bmkp-repeat-command', `bmkp-replace-existing-bookmark',
;;    `bmkp-reset-bmkp-store-org-link-checking-p' (Emacs 24.4+),
;;    `bmkp-retrieve-icicle-search-hits-1',
;;    `bmkp-root-or-sudo-logged-p', `bmkp-same-creation-time-p',
;;    `bmkp-same-file-p', `bmkp-save-new-region-location',
;;    `bmkp-select-buffer-other-window', `bmkp-sequence-alist-only',
;;    `bmkp-sequence-bookmark-p', `bmkp-set-tag-value-for-bookmarks',
;;    `bmkp-set-union', `bmkp-snippet-alist-only',
;;    `bmkp-snippet-bookmark-p', `bmkp-some', `bmkp-some-marked-p',
;;    `bmkp-some-tags-alist-only', `bmkp-some-tags-regexp-alist-only',
;;    `bmkp-some-unmarked-p', `bmkp-sorting-description',
;;    `bmkp-sort-omit', `bmkp-sound-jump',
;;    `bmkp-specific-buffers-alist-only',
;;    `bmkp-specific-files-alist-only', `bmkp-store-org-link-1',
;;    `bmkp-string-less-case-fold-p', `bmkp-tagged-alist-only',
;;    `bmkp-tagged-bookmark-p', `bmkp-tagged-cp', `bmkp-tag-name',
;;    `bmkp-tags-in-bookmark-file', `bmkp-tags-list',
;;    `bmkp-temporary-alist-only', `bmkp-temporary-bookmark-p',
;;    `bmkp-thing-at-point', `bmkp-this-buffer-alist-only',
;;    `bmkp-this-buffer-p', `bmkp-this-file-alist-only',
;;    `bmkp-this-file/buffer-alist-only', `bmkp-this-file-p',
;;    `bmkp-unmarked-bookmarks-only', `bmkp-unpropertized-string',
;;    `bmkp-untagged-alist-only', `bmkp-upcase',
;;    `bmkp-update-autonamed-bookmark', `bmkp-url-alist-only',
;;    `bmkp-url-bookmark-p', `bmkp-url-browse-alist-only',
;;    `bmkp-url-browse-bookmark-p', `bmkp-url-cp',
;;    `bmkp-variable-list-alist-only',
;;    `bmkp-variable-list-bookmark-p', `bmkp-visited-more-cp',
;;    `bmkp-w3m-alist-only', `bmkp-w3m-bookmark-p', `bmkp-w3m-cp',
;;    `bmkp-w3m-set-new-buffer-name'.
;;
;;  Internal variables defined here:
;;
;;    `bmkp-after-set-hook', `bmkp-autofile-history',
;;    `bmkp-auto-idle-bookmark-mode-timer',
;;    `bmkp-auto-idle-bookmarks', `bmkp-autonamed-history',
;;    `bmkp-autotemp-all-when-set-p', `bmkp-before-jump-hook',
;;    `bmkp-bookmark-file-history', `bmkp-bookmark-list-history',
;;    `bmkp-bookmark-set-confirms-overwrite-p',
;;    `bmkp-current-bookmark-file', `bmkp-current-nav-bookmark',
;;    `bmkp-desktop-current-file', `bmkp-desktop-history',
;;    `bmkp-dired-history', `bmkp-edit-bookmark-record-mode-map',
;;    `bmkp-edit-bookmark-records-mode-map',
;;    `bmkp-edit-bookmark-records-number', `bmkp-edit-tags-mode-map',
;;    `bmkp-eww-history' (Emacs 25+), `bmkp-eww-jumping-p' (Emacs
;;    25+), `bmkp-eww-new-buf-name' (Emacs 25+),
;;    `bmkp-file-bookmark-handlers', `bmkp-file-history',
;;    `bmkp-gnus-history', `bmkp-icicles-search-hits-retrieve-more',
;;    `bmkp-image-history', `bmkp-info-history',
;;    `bmkp-isearch-bookmarks' (Emacs 23+),
;;    `bmkp-jump-display-function', `bmkp-jump-other-window-map',
;;    `bmkp-last-bmenu-state-file', `bmkp-last-bookmark-file',
;;    `bmkp-last-save-flag-value', `bmkp-last-specific-buffer',
;;    `bmkp-last-specific-file', `bmkp-latest-bookmark-alist',
;;    `bmkp-local-file-history', `bmkp-man-history',
;;    `bmkp-modified-bookmarks', `bmkp-nav-alist',
;;    `bmkp-non-file-filename', `bmkp-non-file-history',
;;    `bmkp-region-history', `bmkp-remote-file-history',
;;    `bmkp-return-buffer', `bmkp-reverse-multi-sort-p',
;;    `bmkp-reverse-sort-p', `bmkp-snippet-history',
;;    `bmkp-sorted-alist', `bmkp-specific-buffers-history',
;;    `bmkp-specific-files-history', `bmkp-store-org-link-checking-p',
;;    `bmkp-tag-history', `bmkp-tags-alist', `bmkp-temporary-history',
;;    `bmkp-types-alist', `bmkp-url-history',
;;    `bmkp-use-w32-browser-p', `bmkp-variable-list-history',
;;    `bmkp-version-number', `bmkp-w3m-history'.
;;
;;
;;  ***** NOTE: The following commands defined in `bookmark.el'
;;              have been REDEFINED HERE:
;;
;;    `bookmark-default-annotation-text', `bookmark-delete',
;;    `bookmark-edit-annotation-mode', `bookmark-insert',
;;    `bookmark-insert-annotation',
;;    `bookmark-insert-current-bookmark', `bookmark-insert-location',
;;    `bookmark-jump', `bookmark-jump-other-window', `bookmark-load',
;;    `bookmark-relocate', `bookmark-rename', `bookmark-save',
;;    `bookmark-send-edited-annotation', `bookmark-set',
;;    `bookmark-set-name', `bookmark-yank-word'.
;;
;;
;;  ***** NOTE: The following user options defined in `bookmark.el'
;;              have been REDEFINED HERE:
;;
;;    `bookmark-automatically-show-annotations', `bookmark-sort-flag'
;;    (document non-use), `bookmark-version-control'.
;;
;;
;;  ***** NOTE: The following non-interactive functions defined in
;;              `bookmark.el' have been REDEFINED HERE:
;;
;;    `bookmark--jump-via', `bookmark-alist-from-buffer',
;;    `bookmark-all-names', `bookmark-completing-read',
;;    `bookmark-default-handler', `bookmark-edit-annotation' (command
;;    here), `bookmark-exit-hook-internal', `bookmark-get-bookmark',
;;    `bookmark-get-bookmark-record' (Emacs 20-22),
;;    `bookmark-get-handler' (Emacs 20-22),
;;    `bookmark-handle-bookmark', `bookmark-import-new-list',
;;    `bookmark-jump-noselect' (Emacs 20-22), `bookmark-location',
;;    `bookmark-make-record', `bookmark-make-record-default',
;;    `bookmark-maybe-load-default-file', `bookmark-maybe-rename',
;;    `bookmark-prop-get' (Emacs 20-22), `bookmark-prop-set',
;;    `bookmark-show-annotation' (command here),
;;    `bookmark-show-all-annotations' (command here), `bookmark-store'
;;    (Emacs 20-22), `bookmark-write-file'.
;;
;;
;;  ***** NOTE: The following internal variables defined in
;;              `bookmark.el' have been REDEFINED HERE:
;;
;;    `bookmark-alist' (doc string only),
;;    `bookmark-make-record-function' (Emacs 20-22),
;;    `bookmarks-already-loaded' (doc string only).
;;
;;
;;  ***** NOTE: The following functions defined in `info.el'
;;              have been REDEFINED HERE:
;;
;;    `Info-bookmark-jump' (Emacs 20-22), `Info-bookmark-make-record'
;;    (Emacs 20-22).
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
;;
;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;

(unless (fboundp 'file-remote-p) (require 'ffap)) ;; ffap-file-remote-p
(eval-when-compile (require 'gnus)) ;; mail-header-id (really in `nnheader.el')
(eval-when-compile (require 'gnus-sum)) ;; gnus-summary-article-header
(eval-when-compile (require 'cl)) ;; case, multiple-value-bind, typecase (plus, for Emacs 20: dolist, push)

(when (and (require 'thingatpt+ nil t) ;; (no error if not found):
           (fboundp 'tap-put-thing-at-point-props)) ; >= 2012-08-21
  (tap-define-aliases-wo-prefix)
  (tap-put-thing-at-point-props))
;; region-or-non-nil-symbol-name-nearest-point, symbol-nearest-point

(when (> emacs-major-version 21) (require 'font-lock+ nil t)) ;; font-lock-ignore (text property)

(require 'bookmark)
;; bookmark-alist, bookmark-alist-modification-count, bookmark-annotation-name,
;; bookmark-automatically-show-annotations, bookmark-bmenu-bookmark,
;; bookmark-bmenu-surreptitiously-rebuild-list, bookmark-buffer-file-name, bookmark-buffer-name,
;; bookmark-completion-ignore-case, bookmark-current-bookmark, bookmark-default-file,
;; bookmark-edit-annotation, bookmark-get-annotation, bookmark-get-bookmark-record, bookmark-get-filename,
;; bookmark-get-front-context-string, bookmark-get-handler, bookmark-get-position,
;; bookmark-get-rear-context-string, bookmark-insert-file-format-version-stamp, bookmark-kill-line,
;; bookmark-make-record, bookmark-maybe-historicize-string, bookmark-maybe-upgrade-file-format,
;; bookmark-menu-popup-paned-menu, bookmark-name-from-full-record, bookmark-name-from-record,
;; bookmark-popup-menu-and-apply-function, bookmark-prop-get, bookmark-save-flag, bookmark-search-size,
;; bookmark-set-annotation, bookmark-set-filename, bookmark-set-position, bookmark-time-to-save-p,
;; bookmark-use-annotations, bookmark-yank-point


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
;; bmkp-define-cycle-command, bmkp-define-file-sort-predicate, bmkp-define-next+prev-cycle-commands,
;; bmkp-with-help-window, bmkp-with-output-to-plain-temp-buffer

(eval-when-compile (require 'bookmark+-bmu))
;; bmkp-bmenu-before-hide-marked-alist, bmkp-bmenu-before-hide-unmarked-alist, bmkp-bmenu-commands-file,
;; bmkp-replace-regexp-in-string, bmkp-bmenu-filter-function, bmkp-bmenu-filter-pattern,
;; bmkp-bmenu-first-time-p, bmkp-flagged-bookmarks, bmkp-bmenu-goto-bookmark-named,
;; bmkp-bmenu-marked-bookmarks, bmkp-bmenu-omitted-bookmarks, bmkp-bmenu-refresh-menu-list,
;; bmkp-bmenu-show-all, bmkp-bmenu-state-file, bmkp-bmenu-title, bmkp-looking-at-p,
;; bmkp-maybe-unpropertize-bookmark-names, bmkp-sort-orders-alist, bookmark-bmenu-toggle-filenames


;; (eval-when-compile (require 'bookmark+-lit nil t))
;; bmkp-light-bookmark, bmkp-light-bookmarks, bmkp-light-this-buffer


;; For the redefinition of `bookmark-get-bookmark'.
(provide 'bookmark+-1)                  ; Ensure this library is loaded before we compile it.
(require 'bookmark+-1)                  ; So be sure to put this library in your `load-path' before
                                        ; trying to byte-compile it.

;;;;;;;;;;;;;;;;;;;;;;;

;; Quiet the byte-compiler

(defvar bmkp-auto-light-when-set)       ; In `bookmark+-lit.el'
(defvar bmkp-auto-light-when-jump)      ; In `bookmark+-lit.el'
(defvar bmkp-edit-bookmark-record-mode-map) ; Here, via `define-derived-mode'
(defvar bmkp-edit-bookmark-records-mode-map) ; Here, via `define-derived-mode'
(defvar bmkp-edit-tags-mode-map)        ; Here, via `define-derived-mode'
(defvar bmkp-eww-auto-type)             ; Here (Emacs 25+)
(defvar bmkp-eww-buffer-handling)       ; Here (Emacs 25+)
(defvar bmkp-eww-jumping-p)             ; Here (Emacs 25+)
(defvar bmkp-eww-new-buf-name)          ; Here (Emacs 25+)
(defvar bmkp-eww-replace-keys-flag)     ; Here (Emacs 25+)
(defvar bmkp-info-auto-type)            ; Here (Emacs 22+)
(defvar bmkp-light-priorities)          ; In `bookmark+-lit.el'
(defvar bmkp-temporary-bookmarking-mode) ;  Here
(defvar bmkp-global-auto-idle-bookmark-mode) ; Here, via `define-globalized-minor-mode'
(defvar bookmark-current-point)         ; In `bookmark.el', but not in Emacs 23+
(defvar bookmark-edit-annotation-text-func) ; In `bookmark.el'
(defvar bookmark-file-coding-system)    ; In `bookmark.el' (Emacs 25.2+)
(defvar bookmark-read-annotation-text-func) ; In `bookmark.el', but not in Emacs 23+
(defvar bookmark-make-record-function)  ; In `bookmark.el'
(defvar desktop-basefilename)           ; In `desktop.el' (Emacs < 22)
(defvar desktop-base-file-name)         ; In `desktop.el'
(defvar desktop-buffer-args-list)       ; In `desktop.el'
(defvar desktop-delay-hook)             ; In `desktop.el'
(defvar desktop-dirname)                ; In `desktop.el'
(defvar desktop-file-modtime)           ; In `desktop.el'
(defvar desktop-globals-to-save)        ; In `desktop.el'
(defvar desktop-save-mode)              ; In `desktop.el'
(defvar desktop-save)                   ; In `desktop.el'
(defvar dired-actual-switches)          ; In `dired.el'
(defvar dired-buffers)                  ; In `dired.el'
(defvar dired-directory)                ; In `dired.el'
(defvar dired-guess-shell-case-fold-search) ; In `dired-x.el'
(defvar dired-subdir-alist)             ; In `dired.el'
(defvar eww-data)                       ; In `eww.el' (Emacs 25+)
(defvar eww-local-regex)                ; In `eww.el' (Emacs 25+)
(defvar eww-search-prefix)              ; In `eww.el' (Emacs 25+)
(defvar gnus-article-current)           ; In `gnus-sum.el'
(defvar icicle-candidate-properties-alist) ; In `icicles-var.el'
(defvar icicle-completion-candidates)   ; In `icicles-var.el'
(defvar icicle-mode)                    ; In `icicle-mode.el'
(defvar icicle-multi-completing-p)      ; In `icicles-var.el'
(defvar icicle-saved-completion-candidates) ; In `icicles-var.el'
(defvar icicle-searching-p)             ; In `icicles-var.el'
(defvar Info-current-node)              ; In `info.el'
(defvar Info-current-file)              ; In `info.el'
(defvar kmacro-counter)                 ; In `kmacro.el'
(defvar kmacro-counter-format-start)    ; In `kmacro.el'
(defvar kmacro-ring)                    ; In `kmacro.el'
(defvar Man-arguments)                  ; In `man.el'
(defvar org-store-link-functions)       ; In `org.el'
(defvar read-file-name-completion-ignore-case) ; Emacs 23+
(defvar last-repeatable-command)        ; In `repeat.el'
(defvar w3m-current-title)              ; In `w3m.el'
(defvar w3m-current-url)                ; In `w3m.el'
(defvar w3m-mode-map)                   ; In `w3m.el'
(defvar zz-izones)                      ; In `zones.el'
(defvar zz-izones-var)                  ; In `zones.el'
(defvar woman-last-file-name)           ; In `woman.el'
 
;;(@* "User Options (Customizable)")
;;; User Options (Customizable) --------------------------------------

;;;###autoload (autoload 'bmkp-autofile-access-invokes-bookmark-flag "bookmark+")
(defcustom bmkp-autofile-access-invokes-bookmark-flag nil
  "*Non-nil means invoke the bookmark when you access an autofile.
That is, if a file has an associated autofile bookmark then functions
such as `find-file' will automatically jump to the bookmark.  The
buffer position of an autofile bookmark is not important, but this can
be useful to update the bookmark data, such as the number of visits.

If you change the option value in Lisp code without using a Customize
function, then add/remove `bmkp-find-file-invoke-bookmark-if-autofile'
to/from `find-file-hook'."
  :set (lambda (sym new-val)
         (custom-set-default sym new-val)
         (let ((hook-var  (if (< emacs-major-version 22) 'find-file-hooks 'find-file-hook)))
           (if bmkp-autofile-access-invokes-bookmark-flag
               (add-hook hook-var 'bmkp-find-file-invoke-bookmark-if-autofile)
             (remove-hook hook-var 'bmkp-find-file-invoke-bookmark-if-autofile))))
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-autofile-filecache "bookmark+")
(defcustom bmkp-autofile-filecache 'cache-only
  "*Whether Emacs filecache commands create/set an autofile bookmark.
The possible values:
`autofile+cache' - Whenever a file is added to the file cache, also
                   create/set an autofile bookmark for the file.
`autofile-only'  - Create/set an autofile instead of caching the file.
`cache-only'     - Add the file to the file cache.  No autofile."
  :type '(choice
          (const :tag "Create/set an autofile bookmark instead of adding to file cache"  autofile-only)
          (const :tag "Create/set an autofile bookmark and add to file cache"            autofile+cache)
          (const :tag "Add to file cache only - do not create/set an autofile bookmark"  cache-only))
  :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-auto-idle-bookmark-min-distance "bookmark+")
(defcustom bmkp-auto-idle-bookmark-min-distance 1000
  "*Minimum number of chars between automatic bookmark positions."
  :type '(choice
          (const   :tag "No minumum distance" nil)
          (integer :tag "At least this many chars" :value 1000))
  :group 'bookmark-plus)

;; Emacs 20 only.
;;;###autoload (autoload 'bmkp-auto-idle-bookmark-mode "bookmark+")
(unless (fboundp 'define-minor-mode)
  (defcustom bmkp-auto-idle-bookmark-mode nil
    "*Non-nil means that bookmarks are created periodically automatically.
Setting this variable directly does not take effect;
use either \\[customize] or command `bmkp-auto-idle-bookmark-mode'."
    :set        (lambda (symbol value) (bmkp-auto-idle-bookmark-mode (if value 1 -1)))
    :initialize 'custom-initialize-default
    :type 'boolean :group 'bookmark-plus :require 'bookmark+))

;;;###autoload (autoload 'bmkp-auto-idle-bookmark-mode-delay "bookmark+")
(defcustom bmkp-auto-idle-bookmark-mode-delay 60
  "*Number of seconds delay before automatically setting a bookmark.
Such automatic bookmarking is controlled by
`bmkp-temporary-bookmarking-mode'."
  :type 'integer :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-auto-idle-bookmark-mode-lighter "bookmark+")
(defcustom bmkp-auto-idle-bookmark-mode-lighter " Auto-Bmk"
  "*Lighter for `bmkp-auto-idle-bookmark-mode'.
This string shows in the mode line when `bmkp-auto-idle-bookmark-mode'
is enabled.  Set this to nil or \"\" if you do not want any lighter."
  :type 'string :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-auto-idle-bookmark-mode-set-function "bookmark+")
(defcustom bmkp-auto-idle-bookmark-mode-set-function #'bmkp-set-autonamed-bookmark-at-line
  "*Function used to set an automatic bookmark.
Used by `bmkp-temporary-bookmarking-mode'.
The default value, `bmkp-set-autonamed-bookmark-at-line', sets an
autonamed bookmark at the start of the current line.  To bookmark the
current position, so you can have more than one automatic bookmark per
line, use `bmkp-set-autonamed-bookmark' instead."
  :type 'function :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-autoname-bookmark-function "bookmark+")
(defcustom bmkp-autoname-bookmark-function 'bmkp-autoname-bookmark-function-default
  "*Function to automatically name a bookmark at point (cursor position).
It should accept a buffer position as its (first) argument.
The name returned should match the application of
`bmkp-autoname-format' to the buffer name."
  :type 'function :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-autoname-format "bookmark+")
(defcustom bmkp-autoname-format (if (> emacs-major-version 21) "^[0-9]\\{9\\} %B" "^[0-9]+ %B")
  "*Format string to match an autonamed bookmark name.
You can use `%B' instead of `%s' to accept the buffer name.  This has
the advantage that commands and other functions that check for a
buffer-specific bookmark can tell more accurately whether a bookmark
name matches the given buffer.  This applies to functions such as
`bmkp-autonamed-this-buffer-jump' and
`bmkp-autonamed-this-buffer-bookmark-p'."
  :type 'string :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-autotemp-bookmark-predicates "bookmark+")
(defcustom bmkp-autotemp-bookmark-predicates '(bmkp-autonamed-bookmark-p
                                               bmkp-autonamed-this-buffer-bookmark-p)
  "*Predicates for bookmarks to be set (created) as temporary bookmarks.
Each is typically a type predicate, but it can be any function that
accepts as its (first) argument a bookmark or bookmark name.

These are the predefined type predicates:

`bmkp-autofile-bookmark-p', `bmkp-annotated-bookmark-p',
`bmkp-autonamed-bookmark-for-buffer-p', `bmkp-autonamed-bookmark-p',
`bmkp-autonamed-this-buffer-bookmark-p','
`bmkp-bookmark-file-bookmark-p', `bmkp-bookmark-list-bookmark-p',
`bmkp-desktop-bookmark-p', `bmkp-dired-bookmark-p',
`bmkp-dired-this-dir-bookmark-p', `bmkp-dired-wildcards-bookmark-p',
`bmkp-eww-bookmark-p' (Emacs 25+), `bmkp-file-bookmark-p',
`bmkp-file-remote-p', `bmkp-file-this-dir-bookmark-p',
`bmkp-flagged-bookmark-p', `bmkp-function-bookmark-p',
`bmkp-gnus-bookmark-p', `bmkp-icicles-search-hits-bookmark-p',
`bmkp-image-bookmark-p', `bmkp-info-bookmark-p',
`bmkp-last-specific-buffer-p', `bmkp-last-specific-file-p',
`bmkp-local-directory-bookmark-p', `bmkp-local-file-bookmark-p',
`bmkp-local-non-dir-file-bookmark-p', `bmkp-man-bookmark-p',
`bmkp-marked-bookmark-p', `bmkp-modified-bookmark-p',
`bmkp-navlist-bookmark-p', `bmkp-non-dir-file-bookmark-p',
`bmkp-non-file-bookmark-p', `bmkp-non-invokable-bookmark-p',
`bmkp-omitted-bookmark-p', `bmkp-orphaned-file-bookmark-p',
`bmkp-orphaned-local-file-bookmark-p',
`bmkp-orphaned-remote-file-bookmark-p', `bmkp-region-bookmark-p',
`bmkp-remote-file-bookmark-p', `bmkp-remote-non-dir-file-bookmark-p',
`bmkp-sequence-bookmark-p', `bmkp-snippet-bookmark-p',
`bmkp-temporary-bookmark-p', `bmkp-this-buffer-p', `bmkp-this-file-p',
`bmkp-url-bookmark-p', `bmkp-url-browse-bookmark-p',
`bmkp-variable-list-bookmark-p', `bmkp-w3m-bookmark-p'"
  :type '(repeat symbol) :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-bookmark-name-length-max "bookmark+")
(defcustom bmkp-bookmark-name-length-max 70
  "*Max number of chars for default name for a bookmark with a region."
  :type 'integer :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-count-multi-mods-as-one-flag "bookmark+")
(defcustom bmkp-count-multi-mods-as-one-flag t
  "*Non-nil means count multiple modifications as one.
This is for `bookmark-alist-modification-count'.  Non-nil means that
when you invoke a command that acts on multiple bookmarks or acts in
multiple ways on one bookmark, all of changes together count as only
one modification.  That can prevent automatic saving of your bookmark
file during the sequence of modifications, so that when the command is
done you can choose not to save (i.e., to quit) if you like."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-crosshairs-flag "bookmark+")
(defcustom bmkp-crosshairs-flag (> emacs-major-version 21)
  "*Non-nil means highlight with crosshairs when you visit a bookmark.
The highlighting is temporary - until your next action.
You need library `crosshairs.el' for this feature, and you need Emacs
22 or later.

NOTE: Crosshairs highlighting is shown in the buffer that is current
after jumping.  If the bookmarked jumped to does not really have an
associated buffer, for example a bookmark with a handler such as
`w32-browser' that just invokes a separate, non-Emacs program, then
the current buffer after jumping will be the buffer before jumping.

If you use this option in Lisp code, you will want to add/remove
`bmkp-crosshairs-highlight' to/from `bookmark-after-jump-hook'."
  :set (lambda (sym new-val)
         (custom-set-default sym new-val)
         (if (and bmkp-crosshairs-flag  (> emacs-major-version 21)
                  (condition-case nil (require 'crosshairs nil t) (error nil)))
             (add-hook 'bookmark-after-jump-hook 'bmkp-crosshairs-highlight)
           (remove-hook 'bookmark-after-jump-hook 'bmkp-crosshairs-highlight)))
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-default-bookmark-name "bookmark+")
(defcustom bmkp-default-bookmark-name 'highlighted
  "*Default bookmark name preference for accessing existing bookmarks.
\(The default name for a *new* bookmark is obtained using option
`bmkp-new-bookmark-default-names'.)

In `*Bookmark List*' use the name of the current line's bookmark.
Otherwise, if `bookmark+-lit.el' is not loaded then use the name of
the last-used bookmark in the current file.

Otherwise, use this option to determine the default, by preferring one
of the following, if available:

* a highlighted bookmark at point
* the last-used bookmark in the current file"
  :type '(choice
          (const :tag "Highlighted bookmark at point"    highlighted)
          (const :tag "Last used bookmark in same file"  last-used))
  :group 'bookmark-plus)


;; We do not use `define-obsolete-variable-alias' so that byte-compilation in older Emacs
;; works for newer Emacs too.
(when (fboundp 'defvaralias)            ; Emacs 22+
  (defvaralias 'bmkp-default-handler-associations 'bmkp-default-handlers-for-file-types)
  (make-obsolete-variable 'bmkp-default-handler-associations 'bmkp-default-handlers-for-file-types
                          "2012-02-27"))

;;;###autoload (autoload 'bmkp-default-handlers-for-file-types "bookmark+")
(defcustom bmkp-default-handlers-for-file-types
  (and (require 'dired-x)               ; It in turn requires `dired-aux.el'
       (eval-when-compile (when (< emacs-major-version 21) (require 'cl))) ;; `dolist', for Emacs 20
       (let ((assns  ()))
         (dolist (shell-assn  dired-guess-shell-alist-user)
           (push (cons (car shell-assn)
                       `(lambda (bmk)
                         (dired-run-shell-command
                          (dired-shell-stuff-it ,(cadr shell-assn) (list (bookmark-get-filename bmk))
                           nil nil))))
                 assns))
         assns))
  "*File associations for bookmark handlers used for indirect bookmarks.
Each element of the alist is (REGEXP . COMMAND).
REGEXP matches a file name.
COMMAND is a sexp that evaluates to either a shell command (a string)
 or an Emacs function (a symbol or a lambda form).  The shell command
 or Lisp function must accept a file-name argument.

Example value:

 ((\"\\\\.pdf$\"   . \"AcroRd32.exe\") ; Adobe Acrobat Reader
  (\"\\\\.ps$\"    . \"gsview32.exe\") ; Ghostview (PostScript viewer)
  (\"\\\\.html?$\" . browse-url)       ; Use Lisp function `browse-url'
  (\"\\\\.doc$\"   . w32-browser))     ; Use Lisp function `w32-browser'

When you change this option using Customize, if you want to use a
literal string as COMMAND then you must double-quote the text:
\"...\".  (But do not use double-quotes for the REGEXP.)  If you want
to use a symbol as COMMAND, just type the symbol name (no quotes).

This option is used by `bmkp-default-handler-for-file' to determine
the default `file-handler' property for a given file bookmark.  If a
given file name does not match this option, and if
`bmkp-guess-default-handler-for-file-flag' is non-nil, then
`bmkp-default-handler-for-file' tries to guess a shell command to use
in the default handler.  For that it uses `dired-guess-default' and
\(Emacs 23+ only) mailcap entries, in that order."
  :type '(alist :key-type
          regexp :value-type
          (sexp :tag "Shell command (string) or Emacs function (symbol or lambda form)"))
  :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-desktop-default-directory "bookmark+")
(defcustom bmkp-desktop-default-directory nil
  "*Default directory used when reading the name of a desktop file.
If nil then use the current directory (value of `default-directory')."
  :type 'directory :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-desktop-jump-save-before-flag "bookmark+")
(defcustom bmkp-desktop-jump-save-before-flag nil
  "*Non-nil means `bmkp-desktop-jump' saves the desktop file before switching."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-desktop-no-save-vars "bookmark+")
(defcustom bmkp-desktop-no-save-vars '(search-ring regexp-search-ring kill-ring)
  "*List of variables not to save when creating a desktop bookmark.
They are removed from `desktop-globals-to-save' for the duration of
the save (only)."
  :type '(repeat (variable :tag "Variable")) :group 'bookmark-plus)


;; EWW support
(when (> emacs-major-version 24)        ; Emacs 25+

  (defcustom bmkp-eww-auto-type 'update-only
    "How `bmkp-eww-auto-bookmark-mode' behaves when enabled.
You can toggle this option using `\\[bmkp-toggle-eww-auto-type]'."
    :type '(choice
            (const :tag "Create EWW bookmark or update existing EWW bookmark" create-or-update)
            (const :tag "Update existing EWW bookmark (only)" update-only))
    :group 'bookmark-plus)

  (defcustom bmkp-eww-buffer-handling nil
    "How to handle an EWW buffer.
A nil value means always use buffer `*eww*' for EWW, and do not rename
the buffer.  This value makes no change to the behavior of EWW.

Non-nil means rename the buffer using the web-page title.  This
affects EWW behavior even when bookmarks are not used.

The particular non-nil value defines whether and when a
separate (e.g. new) buffer is used, and whether a reused existing
buffer is renamed, as follows:

 `one'         - Use one buffer for all EWW visits, renaming it.

 `url'         - Use a separate buffer for each URL.

 other non-nil - Use a separate buffer for each web-page visit.

Except for a value of (nil or) `url', the buffer is renamed to
`*eww*-' followed by the web-page title.

For `url', the buffer is renamed to `*eww*-' followed by the page
title, followed by a `SPC' char and the last 20 chars of the URL.
This generally means that different pages with the same title use
different buffers."
    :type '(choice
            (const :tag "One buffer for all EWW visits, never renamed"                    nil)
            (const :tag "One buffer for all EWW visits, renamed for each title in turn"   one)
            (const :tag "Separate buffer per web page, named for its title"               page)
            (const :tag "Separate buffer per URL, named for page title + URL (last part)" url))
    :group 'bookmark-plus)

  ;; We do not use `define-obsolete-function-alias' so that byte-compilation in older Emacs
  ;; works for newer Emacs too.
  (defalias 'bmkp-replace-eww-keys-flag 'bmkp-eww-replace-keys-flag)
  (make-obsolete 'bmkp-replace-eww-keys-flag 'bmkp-eww-replace-keys-flag "2017-01-10")
  (defcustom bmkp-eww-replace-keys-flag t
    "Non-nil means replace EWW bookmarking keys and menus with Bookmark+ ones.
If you change the value of this option then you must restart Emacs for
it to take effect."
    :type 'boolean :group 'bookmark-plus)
  )

;;;###autoload (autoload 'bmkp-annotation-modes-inherit-from "bookmark+")
(defcustom bmkp-annotation-modes-inherit-from (if (fboundp 'org-mode) 'org-mode 'text-mode)
  "Symbol for mode that bookmark annotation modes are to inherit from.
Or nil if no parent mode.  The annotation modes are
`bmkp-edit-annotation-mode' and `bmkp-show-annotation-mode'.

You must restart Emacs after changing the value of this option, for
the change to take effect."
  :type  'symbol :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-handle-region-function "bookmark+")
(defcustom bmkp-handle-region-function 'bmkp-handle-region-default
  "*Function to handle a bookmarked region."
  :type 'function :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-info-sort-ignores-directories-flag "bookmark+")
(defcustom bmkp-info-sort-ignores-directories-flag t
  "*Non-nil means Info-bookmark sorting uses manual names, not file locations.
If nil, the absolute file names of the manuals are used.  This can be
useful if you have bookmarks for multiple Emacs releases, and you want
the bookmarks for a given release to appear together."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-incremental-filter-delay "bookmark+")
(defcustom bmkp-incremental-filter-delay (if (boundp 'bookmark-search-delay)
                                             bookmark-search-delay
                                           0.2)
  "*Seconds to wait before updating display when filtering bookmarks."
  :type 'number :group 'bookmark-plus)


(when (> emacs-major-version 21)        ; Emacs 22+ (need also `Info-selection-hook').

  (defcustom bmkp-info-auto-type 'create-or-update
    "How `bmkp-info-auto-bookmark-mode' behaves when enabled.
You can toggle this option using `\\[bmkp-toggle-info-auto-type]'."
    :type '(choice
            (const :tag "Create Info bookmark or update existing Info bookmark" create-or-update)
            (const :tag "Update existing Info bookmark (only)" update-only))
    :group 'bookmark-plus)

  )

;; Removed autoload cookie, to avoid (void-variable bookmark-default-file) ;;;###autoload
(defcustom bmkp-last-as-first-bookmark-file bookmark-default-file
  "*Whether to use the last-used bookmark file as the first used.
If nil then Emacs always uses the value of `bookmark-default-file' as
the initial bookmark file, in any given session.

If non-nil, Emacs uses the last bookmark file you used, in the last
Emacs session.  If none was recorded then it uses
`bookmark-default-file'.  The particular non-nil value must be an
absolute file name \(possibly containing `~') - it is not expanded).

NOTE: A non-nil option value is overwritten by Bookmark+, so that it
becomes the last-used bookmark file.  A nil value is never
overwritten."
  :type '(choice
          (const :tag "Use `bookmark-default-file' as initial bookmark file" nil)
          (file  :tag "Use last-used bookmark file as initial bookmark file"
           :value "~/.emacs.bmk"))
  :group 'bookmark)

;;;###autoload (autoload 'bmkp-menu-popup-max-length "bookmark+")
(defcustom bmkp-menu-popup-max-length 20
  "*Max number of bookmarks for `bookmark-completing-read' to use a menu.
When choosing a bookmark from a list of bookmarks using
`bookmark-completing-read', this controls whether to use a menu or
minibuffer input with completion.
If t, then always use a menu.
If nil, then never use a menu.
If an integer, then use a menu only if there are fewer bookmark
 choices than the value."
  :type '(choice
          (integer :tag "Use a menu if there are fewer bookmark choices than this" 20)
          (const   :tag "Always use a menu to choose a bookmark" t)
          (const   :tag "Never use a menu to choose a bookmark" nil))
  :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-new-bookmark-default-names "bookmark+")
(defcustom bmkp-new-bookmark-default-names
  (let ((fns  '((lambda () (let ((ff  (function-called-at-point)))
                             (and ff  (symbolp ff)  (symbol-name ff)))))))
    (when (fboundp 'region-or-non-nil-symbol-name-nearest-point) ; Defined in `thingatpt+.el'.
      (setq fns  (cons 'region-or-non-nil-symbol-name-nearest-point fns)))
    fns)
  "Functions to produce the default name for a new bookmark.
\(The default name for an *existing* bookmark is obtained using
`bmkp-default-bookmark-name'.)

The option value is a list of functions that do not require an
argument and return a string (or nil).  They are invoked, in order, to
produce the default names.

The following names are also provided, after the names described
above: The value of variable `bookmark-current-bookmark' and the
return value of function `bookmark-buffer-name', in that order.

These latter names are the defaults provided by vanilla Emacs
`bookmark.el', so if you want the vanilla behavior then set the option
value to nil.

For non-interactive use of a default bookmark name, and for Emacs
prior to Emacs 23 even for interactive use, only the first default
name is used.

Some functions you might want to use in the option value:

 * `region-or-non-nil-symbol-name-nearest-point'
 * (lambda () (let ((ff  (function-called-at-point)))
      (and (symbolp ff)  (symbol-name ff))))
 * (lambda () (let ((vv  (variable-at-point))) ; `variable-at-point'
      (and (symbolp vv)  (symbol-name vv))))   ;  returns 0 if no var
 * `word-at-point'
 * (lambda () (let ((ss  (symbol-at-point)))
     (and ss  (symbol-name ss))))

The first of these is defined in library `thingatpt+.el'.  It returns
the text in the region, if it is active and not empty.  Otherwise it
returns the name of the (non-`nil') symbol nearest point, within
maximum search distances `tap-near-point-x-distance' (left and right)
and `tap-near-point-y-distance' (up and down)."
  :type '(repeat function) :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-other-window-pop-to-flag "bookmark+")
(defcustom bmkp-other-window-pop-to-flag t
  "*Non-nil means other-window bookmark jumping uses `pop-to-buffer'.
Use nil if you want the vanilla Emacs behavior, which uses
`switch-to-buffer-other-window'.  That creates a new window even if
there is already another window showing the buffer."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-prompt-for-tags-flag "bookmark+")
(defcustom bmkp-prompt-for-tags-flag nil
  "*Non-nil means setting bookmarks interactively prompts for tags to add.
For an existing bookmark, if option `bmkp-properties-to-keep' includes
`tags' (which it does by default), then the tags you enter are added
to any that the bookmark already has - none are removed."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-properties-to-keep "bookmark+")
(defcustom bmkp-properties-to-keep '(tags annotation)
  "*List of properties to keep when you set an existing bookmark.
When you set a bookmark that already exists, its properties are
updated (overwritten), with the exception of those listed here."
  :type '(repeat symbol) :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-region-search-size "bookmark+")
(defcustom bmkp-region-search-size 40
  "*Same as `bookmark-search-size', but specialized for bookmark regions."
  :type 'integer :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-save-new-location-flag "bookmark+")
(defcustom bmkp-save-new-location-flag t
  "*Non-nil means save automatically relocated bookmarks.
If nil, then the new bookmark location is visited, but it is not saved
as part of the bookmark definition."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-sequence-jump-display-function "bookmark+")
(defcustom bmkp-sequence-jump-display-function 'pop-to-buffer
  "*Function used to display the bookmarks in a bookmark sequence."
  :type 'function :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-show-end-of-region-flag "bookmark+")
(defcustom bmkp-show-end-of-region-flag t
  "*Show end of region with `exchange-point-and-mark' when activating a region.
If nil show only beginning of region."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-sort-comparer "bookmark+")
(defcustom bmkp-sort-comparer '((bmkp-info-node-name-cp bmkp-gnus-cp bmkp-url-cp bmkp-local-file-type-cp)
                                bmkp-alpha-p) ; This corresponds to `s k'.
  ;; $$$$$$ An alternative default value: `bmkp-alpha-p', which corresponds to `s n'.
  "*Predicate or predicates for sorting (comparing) bookmarks.
This defines the default sort for bookmarks in the bookmark list.

Various sorting commands, such as \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-sort-by-bookmark-visit-frequency]', change the value of this
option dynamically (but they do not save the changed value).

The value must be one of the following:

* nil, meaning do not sort

* a predicate that takes two bookmarks as args

* a list of the form ((PRED...) FINAL-PRED), where each PRED and
  FINAL-PRED are predicates that take two bookmarks as args

If the value is a list of predicates, then each PRED is tried in turn
until one returns a non-nil value.  In that case, the result is the
car of that value.  If no non-nil value is returned by any PRED, then
FINAL-PRED is used and its value is the result.

Each PRED should return `(t)' for true, `(nil)' for false, or nil for
undecided.  A nil value means that the next PRED decides (or
FINAL-PRED, if there is no next PRED).

Thus, a PRED is a special kind of predicate that indicates either a
boolean value (as a singleton list) or \"I cannot decide - let the
next guy else decide\".  (Essentially, each PRED is a hook function
that is run using `run-hook-with-args-until-success'.)

Examples:

 nil           - No sorting.

 string-lessp  - Single predicate that returns nil or non-nil.

 ((p1 p2))     - Two predicates `p1' and `p2', which each return
                 (t) for true, (nil) for false, or nil for undecided.

 ((p1 p2) string-lessp)
               - Same as previous, except if both `p1' and `p2' return
                 nil, then the return value of `string-lessp' is used.

Note that these two values are generally equivalent, in terms of their
effect (*):

 ((p1 p2))
 ((p1) p2-plain) where p2-plain is (bmkp-make-plain-predicate p2)

Likewise, these three values generally act equivalently (*):

 ((p1))
 (() p1-plain)
 p1-plain        where p1-plain is (bmkp-make-plain-predicate p1)

The PRED form lets you easily combine predicates: use `p1' unless it
cannot decide, in which case try `p2', and so on.  The value ((p2 p1))
tries the predicates in the opposite order: first `p2', then `p1' if
`p2' returns nil.

Using a single predicate or FINAL-PRED makes it easy to reuse an
existing predicate that returns nil or non-nil.

You can also convert a PRED-type predicate (which returns (t), (nil),
or nil) into an ordinary predicate, by using function
`bmkp-make-plain-predicate'.  That lets you reuse elsewhere, as
ordinary predicates, any PRED-type predicates you define.

For example, this defines a plain predicate to compare by URL:
 (defalias 'bmkp-url-p (bmkp-make-plain-predicate 'bmkp-url-cp))

Note: As a convention, predefined Bookmark+ PRED-type predicate names
have the suffix `-cp' (for \"component predicate\") instead of `-p'.

--
* If you use `\\[bmkp-reverse-multi-sort-order]', then there is a difference in \
behavior between

   (a) using a plain predicate as FINAL-PRED and
   (b) using the analogous PRED-type predicate (and no FINAL-PRED).

  In the latter case, `\\[bmkp-reverse-multi-sort-order]' affects when the predicate \
is tried and
  its return value.  See `bmkp-reverse-multi-sort-order'."
  :type '(choice
          (const    :tag "None (do not sort)" nil)
          (function :tag "Sorting Predicate")
          (list     :tag "Sorting Multi-Predicate"
           (repeat (function :tag "Component Predicate"))
           (choice
            (const    :tag "None" nil)
            (function :tag "Final Predicate"))))
  :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-su-or-sudo-regexp "bookmark+")
(defcustom bmkp-su-or-sudo-regexp "\\(/su:\\|/sudo:\\)"
  "*Regexp to recognize `su' or `sudo' Tramp bookmarks."
  :type 'regexp :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-tags-for-completion "bookmark+")
(defcustom bmkp-tags-for-completion 'current
  "*List of strings used as tags for completion (not an alist).
The tags can be specified here individually or taken from (a) the
current bookmark list or (b) one or more bookmark files or both.

\(In Emacs 20 and 21, you cannot choose (b) when customizing, but if
\(b) was chosen using a later Emacs version then the option value can
still be used in Emacs 20 and 21.)

If a relative file name is specified for a bookmark file then the
current value of `default-directory' is used to find the file."
  :type (if (> emacs-major-version 21)
            '(choice
              (const :tag "From current bookmarks only" current)
              (list :tag "From current bookmarks and other sources"
               (const  :tag "" current)
               (repeat :inline t :tag "Additional sources or specific tags"
                (choice
                 (string :tag "Specific tag")
                 (cons   :tag "All tags from a bookmark file"
                  (const :tag "" bmkfile) (file :must-match t)))))
              (repeat :tag "Choose sources or specific tags"
               (choice
                (string :tag "Specific tag")
                (cons   :tag "All tags from a bookmark file"
                 (const :tag "" bmkfile) (file :must-match t)))))
          ;; A bug in Emacs 20-21 means we must sacrifice the user choice of current plus other sources.
          '(choice
            (const :tag "From current bookmarks only" current)
            (repeat :tag "Choose sources or specific tags" ; A 2nd Emacs 20-21 bug ignores `:tag' for menu.
             (choice
              (string :tag "Specific tag")
              (cons   :tag "All tags from a bookmark file"
               (const :tag "" bmkfile) (file :must-match t))))))
  :group 'bookmark-plus)

;; Emacs 20 only.
(unless (fboundp 'define-minor-mode)
  (defcustom bmkp-temporary-bookmarking-mode nil
    "*Non-nil means that bookmarks are temporary (not recorded on disk).
Setting this variable directly does not take effect;
use either \\[customize] or command `bmkp-temporary-bookmarking-mode'."
    :set (lambda (symbol value) (bmkp-temporary-bookmarking-mode (if value 1 -1)))
    :initialize 'custom-initialize-default
    :type 'boolean :group 'bookmark-plus :require 'bookmark+))

;;;###autoload (autoload 'bmkp-temporary-bookmarking-mode-hook "bookmark+")
(defcustom bmkp-temporary-bookmarking-mode-hook ()
  "*Functions run after entering and exiting temporary-bookmarking mode."
  :type 'hook :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-this-file/buffer-cycle-sort-comparer "bookmark+")
(defcustom bmkp-this-file/buffer-cycle-sort-comparer '((bmkp-position-cp))
  "*`bmkp-sort-comparer' value for cycling this-file/buffer bookmarks.
Use bookmarks for the currently visited file or (non-file) buffer.
Some values you might want to use: ((bmkp-position-cp)),
 ((bmkp-bookmark-creation-cp)), ((bmkp-visited-more-cp)).
See `bmkp-sort-comparer'."
  :type '(choice
          (const    :tag "None (do not sort)" nil)
          (function :tag "Sorting Predicate")
          (list     :tag "Sorting Multi-Predicate"
           (repeat (function :tag "Component Predicate"))
           (choice
            (const    :tag "None" nil)
            (function :tag "Final Predicate"))))
  :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-guess-default-handler-for-file-flag "bookmark+")
(defcustom bmkp-guess-default-handler-for-file-flag nil
  "*Non-nil means guess the default handler when creating a file bookmark.
This is ignored if a handler can be found using option
`bmkp-default-handlers-for-file-types'.  Otherwise, this is used by
function `bmkp-default-handler-for-file' to determine the default
handler for a given file."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-read-bookmark-file-hook "bookmark+")
(defcustom bmkp-read-bookmark-file-hook ()
  "*List of functions called, in order, after reading a bookmark file.
Each function should accept the list of bookmarks read from the file
as first argument and the bookmark file name as second argument."
  :type 'hook :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-temporary-bookmarking-mode-lighter "bookmark+")
(defcustom bmkp-temporary-bookmarking-mode-lighter " Temp-Bmk"
  "*Lighter for `bmkp-temporary-bookmarking-mode'.
This string shows in the mode line when `bmkp-temporary-bookmarking-mode'
is enabled.  Set this to nil or \"\" if you do not want any lighter."
  :type 'string :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-use-region "bookmark+")
(defcustom bmkp-use-region t
  "*Non-nil means visiting a bookmark activates its recorded region."
  :type '(choice
          (const :tag "Activate bookmark region (except during cycling)"  t)
          (const :tag "Do not activate bookmark region"                   nil)
          (const :tag "Activate bookmark region even during cycling"      cycling-too))
  :group 'bookmark-plus)

;; We do not use `define-obsolete-function-alias' so that byte-compilation in older Emacs
;; works for newer Emacs too.
;;;###autoload (autoload 'bmkp-w3m-allow-multiple-buffers-flag "bookmark+")
(defalias 'bmkp-w3m-allow-multi-tabs-flag 'bmkp-w3m-allow-multiple-buffers-flag)
(make-obsolete 'bmkp-w3m-allow-multi-tabs-flag 'bmkp-w3m-allow-multiple-buffers-flag)
(defcustom bmkp-w3m-allow-multiple-buffers-flag t
  "*Non-nil means jump to a W3M bookmark in a new buffer."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload (autoload 'bmkp-write-bookmark-file-hook "bookmark+")
(defcustom bmkp-write-bookmark-file-hook ()
  "*List of functions called, in order, after writing a bookmark file.
Each function should accept the bookmark file name as first argument.
Used after `after-save-hook'."
  :type 'hook :group 'bookmark-plus)
 
;;(@* "Internal Variables")
;;; Internal Variables -----------------------------------------------

(defconst bmkp-non-file-filename "   - no file -"
  "Name to use for `filename' entry, for non-file bookmarks.")

(defconst bmkp-types-alist (delq nil `(("autofile"         . bmkp-autofile-history)
                                       ("autonamed"        . bmkp-autonamed-history)
                                       ("bookmark-file"    . bmkp-bookmark-file-history)
                                       ("bookmark-list"    . bmkp-bookmark-list-history)
                                       ("desktop"          . bmkp-desktop-history)
                                       ("dired"            . bmkp-dired-history)
                                       ("dired-this-dir"   . bmkp-dired-history)
                                       ,@(and (> emacs-major-version 24)
                                              `(("eww"     . bmkp-eww-history)))
                                       ("file"             . bmkp-file-history)
                                       ("file-this-dir"    . bmkp-file-history)
                                       ("gnus"             . bmkp-gnus-history)
                                       ("image"            . bmkp-image-history)
                                       ("info"             . bmkp-info-history)
                                       ("local-file"       . bmkp-local-file-history)
                                       ("man"              . bmkp-man-history)
                                       ("non-file"         . bmkp-non-file-history)
                                       ("region"           . bmkp-region-history)
                                       ("remote-file"      . bmkp-remote-file-history)
                                       ("snippet"          . bmkp-snippet-history)
                                       ("specific-buffers" . bmkp-specific-buffers-history)
                                       ("specific-files"   . bmkp-specific-files-history)
                                       ("temporary"        . bmkp-temporary-history)
                                       ("url"              . bmkp-url-history)
                                       ("variable-list"    . bmkp-variable-list-history)))
  "Alist of bookmark types used by `bmkp-jump-to-type'.
Keys are bookmark type names.  Values are corresponding history variables.")

(defvar bmkp-autofile-history ()         "History for autofile bookmarks.")
(defvar bmkp-autonamed-history ()        "History for autonamed bookmarks.")
(defvar bmkp-bookmark-file-history ()    "History for bookmark-file bookmarks.")
(defvar bmkp-bookmark-list-history ()    "History for bookmark-list bookmarks.")
(defvar bmkp-desktop-history ()          "History for desktop bookmarks.")
(defvar bmkp-dired-history ()            "History for Dired bookmarks.")
(when (> emacs-major-version 24)
  (defvar bmkp-eww-history ()            "History for EWW bookmarks."))
(defvar bmkp-file-history ()             "History for file bookmarks.")
(defvar bmkp-gnus-history ()             "History for Gnus bookmarks.")
(defvar bmkp-image-history ()            "History for image-file bookmarks.")
(defvar bmkp-info-history ()             "History for Info bookmarks.")
(defvar bmkp-last-bmenu-state-file nil   "Last value of option `bmkp-bmenu-state-file'.")
(defvar bmkp-local-file-history ()       "History for local-file bookmarks.")
(defvar bmkp-man-history ()              "History for `man'-page bookmarks.")
(defvar bmkp-non-file-history ()         "History for buffer (non-file) bookmarks.")
(defvar bmkp-region-history ()           "History for bookmarks that activate the region.")
(defvar bmkp-remote-file-history ()      "History for remote-file bookmarks.")
(defvar bmkp-snippet-history ()          "History for snippet bookmarks.")
(defvar bmkp-specific-buffers-history () "History for specific-buffers bookmarks.")
(defvar bmkp-specific-files-history ()   "History for specific-files bookmarks.")
(defvar bmkp-temporary-history ()        "History for temporary bookmarks.")
(defvar bmkp-url-history ()              "History for URL bookmarks.")
(defvar bmkp-variable-list-history ()    "History for variable-list bookmarks.")
(defvar bmkp-w3m-history ()              "History for W3M bookmarks.")

(defvar bmkp-after-set-hook nil "Hook run after `bookmark-set' sets a bookmark.")

(defvar bmkp-auto-idle-bookmarks ()
  "Alist of bookmarks that were created automatically during this session.")

(defvar bmkp-auto-idle-bookmark-mode-timer nil
  "Timer for `bmkp-auto-idle-bookmark-mode'.
This variable is buffer-local, which means that there is a separate
timer for each buffer where automatic bookmarking is enabled.

NOTE: For Emacs 20, the variable is not buffer-local, by default.  To
make it so, do this:

  (make-variable-buffer-local 'bmkp-auto-idle-bookmark-mode-timer)")

(unless (< emacs-major-version 21) (make-variable-buffer-local 'bmkp-auto-idle-bookmark-mode-timer))


(defvar bmkp-autotemp-all-when-set-p nil "Non-nil means make any bookmark temporary whenever it is set.")

;;; $$$$$$ No - don't bother.
;;; (defconst bmkp-bookmark-modifier-functions  '(bookmark-prop-set bmkp-replace-existing-bookmark
;;;                                               bookmark-set-name bookmark-store)
;;;   "List of functions that modify bookmarks.
;;; Used to mark modified, unsaved bookmarks, in `*Bookmark List*'.
;;; Should not include any function that calls another in the list.")


;; `defvar' Provided for older Emacs versions.
(defvar bookmark-after-jump-hook nil
  "Hook run after `bookmark-jump' jumps to a bookmark.
Useful for example to unhide text in `outline-mode'.")

(defvar bmkp-before-jump-hook nil
  "Hook run before `bookmark-jump' jumps to a bookmark.")

(defvar bmkp-copied-tags ()
  "List of tags copied from a bookmark, for pasting to other bookmarks.")

(defvar bmkp-bookmark-set-confirms-overwrite-p nil
  "Non-nil means `bookmark-set' requires confirmation about overwriting.")

(defvar bmkp-current-bookmark-file bookmark-default-file
  "Current bookmark file.
When you start Emacs, this is initialized according to
`bmkp-last-as-first-bookmark-file'.

When you load bookmarks using `\\[bmkp-switch-bookmark-file-create]', this is set to the file you
load.  When you save bookmarks using `bookmark-save' with no prefix
arg, they are saved to this file.

Loading a bookmark file does not change the value of
`bookmark-default-file', but it might change the value of
`bmkp-last-as-first-bookmark-file' (which see).  The value of
`bookmark-default-file' is never changed, except by your
customizations.")

(defvar bmkp-desktop-current-file nil
  "Desktop file from last desktop bookmark jumped to.")

(defvar bmkp-edit-bookmark-orig-record nil
  "Record of bookmark being edited.")

(defvar bmkp-ffap-max-region-size 1024 ; See also Emacs bug #25243.
  "Max size of active region used to obtain file-name defaults.
An active region larger than this many characters prevents
`bmkp-ffap-guesser' from calling `ffap-guesser'.")

(defvar bmkp-file-bookmark-handlers '(bmkp-jump-dired image-bookmark-jump)
  "List of functions that handle file or directory bookmarks.
This is used to determine `bmkp-file-bookmark-p'.")

(defvar bmkp-icicles-search-hits-retrieve-more nil
  "Non-nil means add hits recorded in bookmark to current search hits.
Otherwise, replace current with bookmark hits.")

(defvar bmkp-last-bookmark-file bookmark-default-file
  "Last bookmark file used in this session (or default bookmark file).
This is a backup for `bmkp-current-bookmark-file'.")

(defvar bmkp-current-nav-bookmark nil "Current bookmark for navigation.")

(defvar bmkp-jump-display-function nil "Function used currently to display a bookmark.")

(defvar bmkp-last-specific-buffer ""
  "Name of buffer used by `bmkp-last-specific-buffer-p'.")

(defvar bmkp-last-specific-file ""
  "(Absolute) file name used by `bmkp-last-specific-file-p'.")

(defvar bmkp-modified-bookmarks ()
  "Alist of bookmarks that have been modified and not saved.")

(defvar bmkp-nav-alist () "Current bookmark alist used for navigation.")

(defvar bmkp-return-buffer nil "Name of buffer to return to.")

(defvar bmkp-reverse-sort-p nil "Non-nil means the sort direction is reversed.")

(defvar bmkp-reverse-multi-sort-p nil
  "Non-nil means the truth values returned by predicates are complemented.
This changes the order of the sorting groups, but it does not in
general reverse that order.  The order within each group is unchanged
\(not reversed).")

(defvar bmkp-use-w32-browser-p nil
  "Non-nil means use `w32-browser' in the default bookmark handler.
That is, use the default Windows application for the bookmarked file.
This has no effect if function `w32-browser' is not defined.")

(defvar bmkp-latest-bookmark-alist () "Copy of `bookmark-alist' as last filtered.")

(defvar bmkp-last-save-flag-value nil "Last value of option `bookmark-save-flag'.")

(defvar bmkp-sorted-alist ()
  "Copy of current bookmark alist, as sorted for buffer `*Bookmark List*'.
Has the same structure as `bookmark-alist'.")

(defvar bmkp-tag-history () "History of tags read from the user.")

(defvar bmkp-tags-alist ()
  "Alist of all bookmark tags, per option `bmkp-tags-for-completion'.
Each entry is a full tag: a cons whose car is a tag name, a string.
This is set by function `bmkp-tags-list'.
Use that function to update the value.")


;; REPLACES ORIGINAL DOC STRING in `bookmark.el'.
;;
;; Doc string does not say that the file that was loaded is `bookmark-default-file'.
;;
(defvar bookmarks-already-loaded nil
  "Non-nil means some bookmarks have been loaded during this Emacs session.")


;; REPLACES ORIGINAL DOC STRING in `bookmark.el'.
;;
;; Doc string reflects `Bookmark+' enhancements.
;;
(put 'bookmark-alist 'variable-documentation
     "Current list of bookmarks (bookmark records).
Bookmark functions update the value automatically.
You probably do not want to change the value yourself.

The value is an alist with entries of the form
 (BOOKMARK-NAME . PARAM-ALIST)
or the deprecated form (BOOKMARK-NAME PARAM-ALIST).

 BOOKMARK-NAME is the name you gave to the bookmark when creating it.
 PARAM-ALIST is an alist of bookmark data.  The order of the entries
  in PARAM-ALIST is not important.  The possible entries are described
  below.

Bookmarks created using vanilla Emacs (`bookmark.el'):

 (filename . FILENAME)
 (location . LOCATION)
 (position . POS)
 (front-context-string . STR-AFTER-POS)
 (rear-context-string  . STR-BEFORE-POS)
 (handler . HANDLER)
 (annotation . ANNOTATION)

 FILENAME names the bookmarked file.
 LOCATION names the bookmarked file, URL, or other place (Emacs 23+).
  FILENAME or LOCATION is what is shown in the bookmark list
  (`C-x r l') when you use `M-t'.
 POS is the bookmarked buffer position (position in the file).
 STR-AFTER-POS is buffer text that immediately follows POS.
 STR-BEFORE-POS is buffer text that immediately precedes POS.
 ANNOTATION is a string that you can provide to identify the bookmark.
  See options `bookmark-use-annotations' and
  `bookmark-automatically-show-annotations'.
 HANDLER is a function that provides the bookmark-jump behavior
  for a specific kind of bookmark.  This is the case for Info
  bookmarks, for instance (starting with Emacs 23).

Bookmarks created using Bookmark+ are the same as for vanilla Emacs,
except for the following differences.

1. Visit information is recorded, using entries `visits' and `time':

 (visits . NUMBER-OF-VISITS)
 (time . TIME-LAST-VISITED)

 NUMBER-OF-VISITS is a whole-number counter.

 TIME-LAST-VISITED is an Emacs time representation, such as is
 returned by function `current-time'.

2. The buffer name is recorded, using entry `buffer-name'.  It need
not be associated with a file.

3. If no file is associated with the bookmark, then FILENAME is
   `   - no file -'.

4. Bookmarks can be tagged by users.  The tag information is recorded
using entry `tags':

 (tags . TAGS-ALIST)

 TAGS-ALIST is an alist with string keys.

5. A bookmark can be simply a wrapper for a file, in which case it has
entry `file-handler' instead of `handler'.  When you \"jump\" to such
a bookmark, the `file-handler' function or shell-command is applied to
the `filename' entry.  Any `handler' entry present is ignored, as are
entries such as `position'.  It is only the target file that is
important.

6. Bookmarks can have individual highlighting, provided by users.
This overrides any default highlighting.

 (lighting . HIGHLIGHTING)

 HIGHLIGHTING is a property list that contain any of these keyword
 pairs:

   `:style' - Highlighting style.  Cdrs of `bmkp-light-styles-alist'
              entries are the possible values.
   `:face'  - Highlighting face, a symbol.
   `:when'  - A sexp to be evaluated.  Return value of `:no-light'
              means do not highlight.

7. The following additional entries are used to record region
information.  When a region is bookmarked, POS represents the region
start position.

 (end-position . END-POS)
 (front-context-region-string . STR-BEFORE-END-POS)
 (rear-context-region-string . STR-AFTER-END-POS))

 END-POS is the region end position.
 STR-BEFORE-END-POS is buffer text that precedes END-POS.
 STR-AFTER-END-POS is buffer text that follows END-POS.

The two context region strings are non-nil only when a region is
bookmarked.

 NOTE: The relative locations of `front-context-region-string' and
 `rear-context-region-string' are reversed from those of
 `front-context-string' and `rear-context-string'.  For example,
 `front-context-string' is the text that *follows* `position', but
 `front-context-region-string' *precedes* `end-position'.

8. The following additional entries are used for a Dired bookmark.

 (dired-marked . MARKED-FILES)
 (dired-subdirs . INSERTED-SUBDIRS)
 (dired-hidden-dirs . HIDDEN-SUBDIRS)
 (dired-switches . SWITCHES)

 MARKED-FILES is the list of files that were marked `*'.
 INSERTED-SUBDIRS is the list of subdirectores that were inserted.
 HIDDEN-SUBDIRS is the list of inserted subdirs that were hidden.
 SWITCHES is the string of `dired-listing-switches'.

9. The following additional entries are used for a Gnus bookmark.

 (group . GNUS-GROUP-NAME)
 (article . GNUS-ARTICLE-NUMBER)
 (message-id . GNUS-MESSAGE-ID)

 GNUS-GROUP-NAME is the name of a Gnus group.
 GNUS-ARTICLE-NUMBER is the number of a Gnus article.
 GNUS-MESSAGE-ID is the identifier of a Gnus message.

10. For a URL bookmark, FILENAME or LOCATION is a URL.

11. A sequence bookmark has this additional entry:

 (sequence . COMPONENT-BOOKMARKS)

 COMPONENT-BOOKMARKS is the list of component bookmark names.

12. A function bookmark has this additional entry, which records the
FUNCTION:

 (function . FUNCTION)

13. A bookmark-list bookmark has this additional entry, which records
the state of buffer `*Bookmark List*' at the time it is created:

 (bookmark-list . STATE)

 STATE records the sort order, filter function, omit list, and title.")
 
;;(@* "Compatibility Code for Older Emacs Versions")
;;; Compatibility Code for Older Emacs Versions ----------------------

(when (< emacs-major-version 23)

  ;; These definitions are for Emacs versions prior to Emacs 23.
  ;; They are the same as the vanilla Emacs 24+ definitions, except as noted.
  ;; They let older versions of Emacs handle bookmarks created with Emacs 23+.
  ;; (Emacs < 23 also needs a compatible `bookmark-make-record' version,
  ;; but I redefine it for all versions, in any case.)

  (defun Info-bookmark-make-record ()
    "Create a bookmark record for the current Info node (and point).
Implements `bookmark-make-record-function' for Info nodes."
    (let* ((file           (and (stringp Info-current-file)  (file-name-nondirectory Info-current-file)))
           (bookmark-name  (if file
                               (concat "(" file ") " Info-current-node)
                             Info-current-node))
           (defaults       (delq nil (list bookmark-name file Info-current-node))))
      `(,bookmark-name
        ,@(bookmark-make-record-default 'NO-FILE)
        (filename . ,Info-current-file)
        (info-node . ,Info-current-node)
        (handler . Info-bookmark-jump)
        (defaults . ,defaults))))

  ;; Requires `info.el' explicitly (not autoloaded for `Info-find-node'.
  (defun Info-bookmark-jump (bookmark)
    "Jump to Info bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
    (require 'info)
    ;; Implements the `handler' for the record type returned by `Info-bookmark-make-record'.
    (let* ((file       (bookmark-prop-get bookmark 'filename))
           (info-node  (bookmark-prop-get bookmark 'info-node))
           (buf        (save-window-excursion ; VANILLA EMACS FIXME: doesn't work with frames!
                         (Info-find-node file info-node)
                         (current-buffer))))
      ;; Use `bookmark-default-handler' to move to appropriate location within Info node.
      (bookmark-default-handler
       `("" (buffer . ,buf) . ,(bmkp-bookmark-data-from-record bookmark)))))

  (add-hook 'Info-mode-hook (lambda () (set (make-local-variable 'bookmark-make-record-function)
                                            'Info-bookmark-make-record)))

  (defvar bookmark-make-record-function 'bookmark-make-record-default
    "Function called with no arguments, to create a bookmark record.
Modes can set this buffer-locally to enable bookmarking of locations
that should be treated specially for the mode.  Global commands can
bind this and then create a bookmark, to get special treatment
anywhere.

The function value should return a new bookmark record, which should
be a cons cell of the form (NAME . ALIST) or just ALIST, where ALIST
is as described in `bookmark-alist'.  If it cannot construct the
record, then it should raise an error.

NAME is a string that names the new bookmark.  NAME can be nil, in
which case a default name is used.

ALIST can contain an entry (handler . FUNCTION) which sets the handler
to FUNCTION, which is then used instead of `bookmark-default-handler'.
FUNCTION must accept the same arguments as `bookmark-default-handler'.")

  (defun bookmark-prop-get (bookmark prop)
    "Return entry (property) PROP of BOOKMARK, or nil if no such entry.
BOOKMARK is a bookmark name or a bookmark record."
    (cdr (assq prop (bmkp-bookmark-data-from-record bookmark))))

  (defun bookmark-get-handler (bookmark)
    "Return the `handler' entry for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
    (bookmark-prop-get bookmark 'handler))

  (defun bookmark-jump-noselect (bookmark)
    "Return the location recorded for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
The return value has the form (BUFFER . POINT), where BUFFER is a
buffer and POINT is the location within BUFFER."
    (save-excursion (bookmark-handle-bookmark bookmark) (cons (current-buffer) (point)))))

(when (< emacs-major-version 22)

  ;; These definitions are for Emacs versions prior to Emacs 22.
  ;; They are the same as the vanilla Emacs 22+ definitions, except as noted.

;;;   ;; Bookmark+ doesn't use this, but `bookmark.el' still does.  Who has a slow `baud-rate' now?
;;;   (defun bookmark-maybe-message (fmt &rest args)
;;;     "Apply `message' to FMT and ARGS, but only if the display is fast enough."
;;;     (when (>= baud-rate 9600) (apply 'message fmt args)))

  ;; Emacs 22+ just uses `bookmark-jump-other-window' for the menu also.
  (defun bmkp-menu-jump-other-window (event)
    "Jump to BOOKMARK (a point in some file) in another window.
See `bookmark-jump-other-window'."
    (interactive "e")
    (bookmark-popup-menu-and-apply-function 'bookmark-jump-other-window
                                            "Jump to Bookmark (Other Window)" event)))
 
;;(@* "Core Replacements (`bookmark-*' except `bookmark-bmenu-*')")
;;; Core Replacements (`bookmark-*' except `bookmark-bmenu-*') -------



;; REPLACES DOCUMENTATION of ORIGINAL in `bookmark.el'.
;;
;; Doc now just says that this option is ignored by Bookmark+.
(put 'bookmark-sort-flag 'variable-documentation
     "Ignored by Bookmark+, which uses option `bmkp-sort-comparer' instead.")


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Changed default value to t.
;; Added `:tag' strings for clarity.
;; Doc string says that it applies to all Bookmark+ files, and recommends that you back up your files.
;;
(defcustom bookmark-version-control t
  "Whether to make numbered backups of your bookmarking files.
This includes bookmark files such as `bookmark-default-file' and also
Bookmark+ files `bmkp-bmenu-commands-file' and
`bmkp-bmenu-state-file'.

The option can have value `nospecial', `t', `nil', or `never' .  Value
`nospecial' means to use the `version-control' value.  The others have
the same meanings as for option `version-control'.

Use value `t' if your bookmarks are important to you.  Consider also
using numeric backups.  See also nodes `Backup Names' and `Backup
Deletion' in the Emacs manual."
  :type '(choice :tag "When to make numbered backups"
          (const :tag "Use value of option `version-control'" nospecial)
          (const :tag "Never"                                 never)
          (const :tag "If existing already"                   nil)
          (other :tag "Always"                                t))
  :group 'bookmark :group 'bookmark-plus)


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Added value `edit'.
;;
(defcustom bookmark-automatically-show-annotations t
  "*Non-nil means show annotations when jumping to a bookmark.
If the value is `edit' then open the annotation buffer in edit mode.
 This has the same effect as using command `bookmark-edit-annotation'.
Any other non-nil value opens it in read-only mode.
 This has the same effect as using command `bookmark-show-annotation'."
  :type '(choice
          (const :tag "Show annotation read-only"               t)
          (const :tag "Edit annotation"                         edit)
          (const :tag "Do not show annotation automatically"    nil))
  :group 'bookmark :group 'bookmark-plus)


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Doc string does not mention `bookmark-alist': does NOT test whether BOOKMARK is in `bookmark-alist'.
;;
(defun bookmark-get-bookmark-record (bookmark)
  "Return the data part of BOOKMARK, that is, all but the name.
BOOKMARK is a bookmark name or a bookmark record.
If it is a bookmark name then it is looked up in `bookmark-alist'.
If it is a record then it is NOT looked up (need not belong)."
  (let ((data  (cdr (bookmark-get-bookmark bookmark))))
    ;; A bookmark record is either (NAME ALIST) or (NAME . ALIST).
    (if (and (null (cdr data))  (consp (caar data)))
        (car data)
      data)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. If BOOKMARK is a bookmark-name string that has non-nil property `bmkp-full-record'
;;    then look up the bookmark that is the value of that property in `bookmark-alist', and
;;    if found return it.
;; 2. Handle the should-not-happen case of non-string, non-cons.
;; 3. Document NOERROR in doc string.
;;
(defun bookmark-get-bookmark (bookmark &optional noerror)
  "Return the full bookmark (record) that corresponds to BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Non-nil optional arg NOERROR means return nil if BOOKMARK is not a
valid bookmark.  If NOERROR is nil then raise an error in this case.

If BOOKMARK is a bookmark name instead of a full bookmark then return
what `bmkp-bookmark-record-from-name' (with no MEMP check) returns.

This function is like `bmkp-get-bookmark-in-alist', except that
`bmkp-get-bookmark-in-alist' always tests whether BOOKMARK is in
`bookmark-alist', regardless of whether BOOKMARK is a string (a
bookmark name) or a full bookmark.  `bmkp-get-bookmark-in-alist' is
thus a real test for bookmark existence.  Use `bookmark-get-bookmark'
only when you do NOT want to look up the bookmark in
`bookmark-alist'."
  ;; The first test means that any cons with a string car is considered a bookmark.
  ;; We test for the string (the name) so that you can distinguish, for example, a list of bookmarks
  ;; from a single bookmark - just consp is not enough for that.
  (cond ((and (consp bookmark)  (stringp (car bookmark))) bookmark) ; No test of alist membership.
        ((stringp bookmark) (bmkp-bookmark-record-from-name bookmark noerror)) ; No MEMP check.
        (t (and (not noerror)  (error "Invalid bookmark: `%s'" bookmark)))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Use option `bmkp-new-bookmark-default-names' to obtain the default name.
;;
(defun bookmark-make-record ()
  "Return a new bookmark record (NAME . ALIST) for the current location.
Start with `bookmark-make-record-function'.  If it does not provide a
bookmark name, then use option `bmkp-new-bookmark-default-names' to
provide it.  If that does not provide it then use
`bookmark-current-bookmark' or `bookmark-buffer-name', in that order."
  (let ((record  (funcall bookmark-make-record-function))
        defname)
    (if (stringp (car record))
        record
      (when (car record) (push nil record))
      (setq defname  (catch 'bookmark-make-record
                       (dolist (fn  bmkp-new-bookmark-default-names)
                         (when (functionp fn) ; Be sure it is defined and is a function.
                           (let ((val  (funcall fn)))
                             (when (and (stringp val)  (not (string= "" val)))
                               (throw 'bookmark-make-record val)))))
                       (or bookmark-current-bookmark (bookmark-buffer-name))))
      (when (and defname  (not (stringp defname))) (setq defname  (format "%s" defname))) ; Just in case.
      (when (string= "" defname) (setq defname "<EMPTY NAME>")) ; You never know.
      (setcar record  defname)
      record)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional args NO-REFRESH-P and NO-MSG-P.
;; 2. Update the bookmark name also, not just the data, for an existing bookmark.
;; 3. Use `bmkp-get-bookmark-in-alist' to test whether the bookmark already exists.
;; 4. Put full bookmark record on bookmark name (inside record) as property `bmkp-full-record'.
;; 5. Use `bmkp-maybe-save-bookmarks'.
;; 6. Add the bookmark to `bmkp-modified-bookmarks', and to `bmkp-auto-idle-bookmarks' if appropriate.
;; 7. Use `bmkp-refresh/rebuild-menu-list', not `bookmark-bmenu-surreptitiously-rebuild-list'.
;; 8. Return the bookmark.
;;
(defun bookmark-store (bookmark-name data no-overwrite &optional no-refresh-p no-msg-p)
  "Store the bookmark named BOOKMARK-NAME, giving it DATA.
Return the new bookmark.

DATA is the bookmark record without its name, i.e., what
`bmkp-bookmark-data-from-record' returns.

If NO-OVERWRITE is non-nil and bookmark BOOKMARK-NAME already exists
in the current bookmark list (`bookmark-alist') then record the new
bookmark but do not discard the old one.  The check for existence uses
`bmkp-get-bookmark-in-alist'.

Non-nil optional arg NO-REFRESH-P means do not refresh/rebuild the
bookmark-list display.

Non-nil optional arg NO-MSG-P means do not show progress messages.

Note: In spite of the function name, like all functions that define or
change bookmarks, this function does not necessarily save your
bookmark file.  Saving the file depends on `bookmark-save-flag'."
  (bookmark-maybe-load-default-file)
  (let ((bname  (copy-sequence bookmark-name))
        bmk)
    (unless (featurep 'xemacs)
      ;; XEmacs's `set-text-properties' does not work on free-standing strings, apparently.
      (set-text-properties 0 (length bname) () bname))
    (if (or no-overwrite  (not (setq bmk  (bmkp-get-bookmark-in-alist bname 'NOERROR))))
        (push (setq bmk  (cons bname data)) bookmark-alist) ; Add new bookmark.
      (bookmark-set-name bmk bname)     ; Overwrite existing bookmark.
      (setcdr bmk data))
    ;; Put the full bookmark on its name as property `bmkp-full-record'.
    ;; Do this regardless of Emacs version and `bmkp-propertize-bookmark-names-flag'.
    ;; If it needs to be stripped, that will be done when saving.
    (put-text-property 0 (length bname) 'bmkp-full-record bmk bname)
    (bmkp-maybe-save-bookmarks)
    ;; These two are the same as `add-to-list' with `EQ' (not available for Emacs 20-21).
    (unless (memq bmk bmkp-modified-bookmarks)
      (setq bmkp-modified-bookmarks  (cons bmk bmkp-modified-bookmarks)))
    (when (and (boundp 'bmkp-setting-auto-idle-bmk-p)
               (not (memq bmk bmkp-auto-idle-bookmarks)))
      (setq bmkp-auto-idle-bookmarks  (cons bmk bmkp-auto-idle-bookmarks)))
    (setq bookmark-current-bookmark  bname)
    (unless no-refresh-p (bmkp-refresh/rebuild-menu-list bmk no-msg-p))
    bmk))                               ; Return the bookmark.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Mention `C-c C-M-c', not `C-c C-c'.
;;
;;;###autoload (autoload 'bookmark-default-annotation-text "bookmark+")
(defun bookmark-default-annotation-text (bookmark-name)
  "Return default annotation text for BOOKMARK-NAME.
The default annotation text is simply some text explaining how to use
annotations."
  (concat "#  Type the annotation for bookmark `" bookmark-name "' here.\n"
          "#  All lines that start with a `#' will be deleted.\n"
          "#  Type `C-c C-M-c' when done.\n#\n"
          "#  Author: " (user-full-name) " <" (user-login-name) "@"
          (system-name) ">\n"
          "#  Date:    " (current-time-string) "\n"))


;; REPLACES ORIGINAL in `bookmark.el' (Emacs 24.4+).
;;
;; Usable for older Emacs versions also.
;;
;;;###autoload (autoload 'bookmark-insert-annotation "bookmark+")
(defun bookmark-insert-annotation (bookmark)
  "Insert annotation for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (setq bookmark  (bmkp-bookmark-name-from-record (bmkp-get-bookmark-in-alist bookmark)))
  (insert (funcall (if (boundp 'bookmark-edit-annotation-text-func)
                       bookmark-edit-annotation-text-func
                     bookmark-read-annotation-text-func)
                   bookmark))
  (let ((annotation  (bookmark-get-annotation bookmark)))
    (when (and annotation  (not (string-equal annotation ""))) (insert annotation))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Derive from value of option `bmkp-annotation-modes-inherit-from'.
;; 2. First, remove parent map from `bookmark-edit-annotation-mode-map', so it is derived anew.
;; 3. Corrected typo in doc string: *send-EDITED-*.
;; 4. Need to use `eval', to pick up option value and reset parent keymap.
;; 5. Bind `C-x C-q' to `bmkp-show-this-annotation-read-only'.
;;
;;;###autoload (autoload 'bookmark-edit-annotation-mode "bookmark+")
(eval
 `(progn
   ;; Get rid of default parent, so `bmkp-annotation-modes-inherit-from' is used for the map.
   (when (keymapp bookmark-edit-annotation-mode-map)
     (set-keymap-parent bookmark-edit-annotation-mode-map nil))
   (define-derived-mode bookmark-edit-annotation-mode ,bmkp-annotation-modes-inherit-from
       "Edit Bookmark Annotation"
     "Mode for editing the annotation of a bookmark.
When you have finished composing, use `C-c C-M-c'.

\\{bookmark-edit-annotation-mode-map}")
    (define-key bookmark-edit-annotation-mode-map "\C-x\C-q"    'bmkp-show-this-annotation-read-only)
    ;; Define this key because Org mode co-opts `C-c C-c' as a prefix key.
    (define-key bookmark-edit-annotation-mode-map "\C-c\C-\M-c" 'bookmark-send-edited-annotation)))

(define-derived-mode bookmark-show-annotation-mode bookmark-edit-annotation-mode
    "Show Bookmark Annotation"
  "Mode for displaying the annotation of a bookmark.

\\{bookmark-show-annotation-mode-map}"
  (setq buffer-read-only  t)
  (define-key bookmark-show-annotation-mode-map "\C-x\C-q" 'bmkp-edit-this-annotation))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Record an empty annotation as nil, not "".
;; 2. BUG fix: Put point back where it was (on the bookmark just annotated).
;; 3. Refresh menu list, to pick up the `a' marker.
;; 4. Make sure it's the annotation buffer that gets killed.
;; 5. Delete window also, if `misc-cmds.el' loaded.
;;
;;;###autoload (autoload 'bookmark-send-edited-annotation "bookmark+")
(defun bookmark-send-edited-annotation () ; Bound to `C-c C-M-c' in `bookmark-edit-annotation-mode'.
  "Use buffer contents as annotation for a bookmark.
Lines beginning with `#' are ignored."
  (interactive)
  (unless (derived-mode-p 'bookmark-edit-annotation-mode)
    (error "Not in mode derived from `bookmark-edit-annotation-mode'"))
  (goto-char (point-min))
  (while (< (point) (point-max)) (if (= (following-char) ?#) (bookmark-kill-line t) (forward-line 1)))
  (let ((annotation      (buffer-substring-no-properties (point-min) (point-max)))
        (bookmark        bookmark-annotation-name)
        (annotation-buf  (current-buffer)))
    (when (string= annotation "") (setq annotation  nil))
    (bookmark-set-annotation bookmark annotation)
    (setq bookmark-alist-modification-count  (1+ bookmark-alist-modification-count))
    (bmkp-refresh/rebuild-menu-list bookmark) ; So display `a' and `*' markers (updated).
    (if (fboundp 'kill-buffer-and-its-windows)
        (kill-buffer-and-its-windows annotation-buf) ; Defined in `misc-cmds.el'.
      (kill-buffer annotation-buf))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Make it a command (added `interactive' spec).  Prefix arg means add or edit (choose any bookmark).
;; 2. Manage buffer-modified-p.
;;
;;;###autoload (autoload 'bookmark-edit-annotation "bookmark+")
(defun bookmark-edit-annotation (bookmark)
  "Pop up a buffer for editing bookmark BOOKMARK's annotation.
Interactively, you are prompted for the bookmark name.  With a prefix
arg, you can choose any bookmark.  Otherwise, only annotated bookmarks
are candidates.

Non-interactively, BOOKMARK is a bookmark name or a bookmark record."
  (interactive
   (let ((alist  (and (not current-prefix-arg)  (bmkp-annotated-alist-only))))
     (list (bookmark-completing-read (format "%s annotation for bookmark"
                                             (if current-prefix-arg "Add or edit" "Edit"))
                                     (bmkp-default-bookmark-name alist)
                                     alist))))
  (pop-to-buffer (generate-new-buffer-name "*Bookmark Annotation Compose*"))
  (bookmark-insert-annotation bookmark)
  (bookmark-edit-annotation-mode)
  (set (make-local-variable 'bookmark-annotation-name) bookmark))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Added optional arg ALIST.
;;
(defun bookmark-all-names (&optional alist)
  "Return a list of all bookmark names.
The names are those of the bookmarks in ALIST or, if nil,
`bookmark-alist'."
  (bookmark-maybe-load-default-file)
  (mapcar (lambda (bmk) (bmkp-bookmark-name-from-record bmk)) (or alist  bookmark-alist)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional args ALIST, PRED, and HIST.
;; 2. Use helper function `bmkp-completing-read-1', which does this:
;;    (a) binds `icicle-delete-candidate-object' to (essentially) `bookmark-delete'.
;;    (b) forces you to enter a non-empty name, if DEFAULT is nil or "".
;;
(defun bookmark-completing-read (prompt &optional default alist pred hist)
  "Read a bookmark name, prompting with PROMPT.
PROMPT is automatically suffixed with \": \", so do not include that.

DEFAULT is a string or a list of strings.  If the user input is empty
then return the string (or the first string in the list).  If DEFAULT
is nil (absent) then return \"\" for empty input.

The alist argument used for completion is ALIST or, if nil,
`bookmark-alist'.

Optional arg PRED is a predicate used for completion.

Optional arg HIST is a history variable for completion.  Default is
 `bookmark-history'.

If you access this function from a menu, then, depending on the value
of option `bmkp-menu-popup-max-length' and the number of
bookmarks in ALIST, you choose the bookmark using a menu or using
completion.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (bmkp-completing-read-1 prompt default alist pred hist nil))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Handles also regions and non-file buffers.
;; 2. Do not use NO-CONTEXT or POSN if < Emacs 24.
;;
(defun bookmark-make-record-default (&optional no-file no-context position visits no-region)
  "Return the record describing the location of a new bookmark.
Point must be where the bookmark is to be set.

Non-nil NO-FILE means return only the subset of the record that
 pertains to the location within the buffer (not also the file name).

Non-nil NO-CONTEXT means do not include the front and rear context
strings in the record enough.

Non-nil POSITION means record it, not point, as the `position' entry.

Non-nil VISITS means record it as the `visits' entry.

Non-nil NO-REGION means do not include the region end, `end-position'."
  (unless (> emacs-major-version 23) (setq no-context  nil))
  (let* ((dired-p  (and (boundp 'dired-buffers)  (car (rassq (current-buffer) dired-buffers))))
         (buf      (buffer-name))
         (ctime    (current-time))

         ;; Begin `let*' dependencies.
         (regionp  (and transient-mark-mode  mark-active  (> (region-end) (region-beginning))))
         (beg      (if regionp (region-beginning) (or position  (point))))
         (end      (if regionp (region-end) (point)))
         (fcs      (and (not no-context)  (if regionp
                                              (bmkp-position-post-context-region beg end)
                                            (bmkp-position-post-context beg))))
         (rcs      (and (not no-context)  (if regionp
                                              (bmkp-position-pre-context-region beg)
                                            (bmkp-position-pre-context beg))))
         (fcrs     (and (not no-context)  regionp  (bmkp-end-position-pre-context beg end)))
         (ecrs     (and (not no-context)  regionp  (bmkp-end-position-post-context end))))
    `(,@(unless no-file
                `((filename . ,(cond ((buffer-file-name) (bookmark-buffer-file-name))
                                     (dired-p            nil)
                                     (t                  bmkp-non-file-filename)))))
      (buffer-name . ,buf)
      ,@(unless no-context `((front-context-string . ,fcs)))
      ,@(unless no-context `((rear-context-string . ,rcs)))
      ,@(unless no-context `((front-context-region-string . ,fcrs)))
      ,@(unless no-context `((rear-context-region-string  . ,ecrs)))
      (visits       . ,(or visits 0))
      (time         . ,ctime)
      (created      . ,ctime)
      (position     . ,beg)
      ,@(when (and regionp  (not no-region)) `((end-position . ,end))))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Unless non-nil arg DO-NOT-PROPERTIZE-P, put full bookmark record on bookmark name (inside record),
;; as property `bmkp-full-record'.
;;
(defun bookmark-alist-from-buffer (&optional do-not-propertize-p)
  "Read and return a bookmark list (in any format) from the current buffer.
Unless optional arg DO-NOT-PROPERTIZE-P is non-nil, put the full
bookmark record on the bookmark name (in the record), as a text
property.  Point is irrelevant and unaffected."
  (let ((bmks  (save-excursion
                 (goto-char (point-min))
                 (if (search-forward bookmark-end-of-version-stamp-marker nil t)
                     (condition-case err
                         (read (current-buffer))
                       (error (error "Cannot read definitions in bookmark file:  %s"
                                     (error-message-string err))))
                   ;; Else we're dealing with format version 0
                   (if (search-forward "(" nil t)
                       (progn (forward-char -1)
                              (condition-case err
                                  (read (current-buffer))
                                (error (error "Cannot read definitions in bookmark file:  %s"
                                              (error-message-string err)))))
                     ;; Else no hope of getting information here.
                     (error "Buffer is not in bookmark-list format"))))))
    ;; Put full bookmark on bookmark names as property `bmkp-full-record'.
    ;; Do this regardless of Emacs version and `bmkp-propertize-bookmark-names-flag'.
    ;; If property needs to be stripped, that will be done when saving.
    (unless do-not-propertize-p
      (dolist (bmk  bmks)
        (put-text-property 0 (length (car bmk)) 'bmkp-full-record bmk (car bmk))))
    bmks))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;;  1. Use `bookmark-make-record'.
;;  2. Use special default prompts for active region, EWW, W3M, and Gnus.
;;  3. Use function `bmkp-new-bookmark-default-names', in addition to the name that
;;     `bookmark-make-record' comes up with, as the list of default values.
;;  4. Use `bmkp-completing-read-lax', choosing from current buffer's bookmarks.
;;  5. Numeric prefix arg (diff from plain): all bookmarks as completion candidates.
;;  6. Ask for confirmation if (a) not plain `C-u' and (b) NAME names an existing bookmark.
;;  7. Do not overwrite properties listed in option `bmkp-properties-to-keep'.
;;  8. Added optional args INTERACTIVEP and NO-REFRESH-P.
;;  9. Prompt for tags if `bmkp-prompt-for-tags-flag' is non-nil.
;; 10. Possibly highlight bookmark and other bookmarks in buffer, per `bmkp-auto-light-when-set'.
;; 11. Make bookmark temporary, if `bmkp-autotemp-bookmark-predicates' says to.
;; 12. Run `bmkp-after-set-hook'.
;;
;;;###autoload (autoload 'bookmark-set "bookmark+")
(defun bookmark-set (&optional name parg interactivep no-refresh-p) ; `C-x r M', `C-x p c M'
  "Set a bookmark named NAME, then run `bmkp-after-set-hook'.
If the region is active (`transient-mark-mode') and nonempty, then
record the region limits in the bookmark.

If NAME is nil, then prompt for the bookmark name.  The default names
for prompting are as follows (in order of priority):

 * If in W3M mode, then the current W3M title.

 * If in a Gnus mode, then the Gnus summary article header.

 * If on a `man' page, then the page name (command and section).

 * If the region is active and nonempty, then the buffer name followed
   by \": \" and the region prefix (up to
   `bmkp-bookmark-name-length-max' chars).

 * The names defined by option `bmkp-new-bookmark-default-names'.

 * The value of variable `bookmark-current-bookmark', the name of the
   last-used bookmark for the current file.

 * The value returned by function `bookmark-buffer-name'.

For Emacs 23+, all of the names described above are available as
default values, by repeating `M-n'.  For older Emacs versions, the
first name provided is the only default value.

While entering a bookmark name at the prompt:

 * You can use (lax) completion against bookmarks in the same buffer.
   If there are no bookmarks in the current buffer, then all bookmarks
   are completion candidates.  (See also below, about a numeric prefix
   argument.)

 * You can use `C-M-w' to yank words from the buffer to the
   minibuffer.  Repeating `C-M-w' yanks successive words (newlines
   between yanked words are stripped out).

 * You can use `C-M-u' to insert the name of the last bookmark used in
   the buffer.  This can be useful as an aid to track your progress
   through a large file.  (If no bookmark has yet been used, then
   `C-M-u' inserts the name of the visited file.)

A prefix argument changes the behavior as follows:

 * Numeric prefix arg: Use all bookmarks as completion candidates,
   instead of just the bookmarks for the current buffer.

 * Plain prefix arg (`C-u'): Do not overwrite a bookmark that has the
   same name as NAME, if such a bookmark already exists.  Instead,
   push the new bookmark onto the bookmark alist.

   For use by vanilla Emacs, only the most recently set bookmark named
   NAME is in effect at any given time, but any others named NAME can
   become available, should you decide to delete the most recent one.

   For Bookmark+, if option `bmkp-propertize-bookmark-names-flag' is
   non-`nil' then you can use any number of bookmarks that have the
   same name.  If that option is `nil' then the behavior is the same
   as for vanilla Emacs.

Bookmark properties listed in option `bmkp-properties-to-keep' are not
overwritten when you set an existing bookmark.  Their existing values
are kept.  Other properties may be updated.  Properties such as
`position' and `visit' are typically updated, for example, to record
the new position and the number of visits.

Use `\\[bookmark-delete]' to remove bookmarks (you give it a name, and it removes
only the first instance of a bookmark with that name from the list of
bookmarks).

From Lisp code:

* Non-nil INTERACTIVEP means the user can be prompted for
  confirmation, tags, etc., and it is used for the call to
  `bookmark-store'.

* Non-nil NO-REFRESH-P is also passed to `bookmark-store'.  It means
  do not refresh/rebuild the bookmark-list display."
  (interactive (list nil current-prefix-arg t))
  (unwind-protect
       (progn
         (bookmark-maybe-load-default-file)
         (setq bookmark-current-point   (point)) ; `bookmark-current-point' is a free var here.
         ;; Do not set these if they are already set in some other buffer (e.g gnus-art).
         (unless (and bookmark-yank-point  bookmark-current-buffer)
           (save-excursion (skip-chars-forward " ") (setq bookmark-yank-point  (point)))
           (setq bookmark-current-buffer  (current-buffer)))
         (let* ((record   (bookmark-make-record))
                (defname  (cond ((and (eq major-mode 'eww-mode)
                                      (fboundp 'bmkp-make-eww-record) ; Emacs 25+
                                      (bmkp-eww-title)))
                                ((eq major-mode 'w3m-mode) w3m-current-title)
                                ((eq major-mode 'gnus-summary-mode) (elt (gnus-summary-article-header) 1))
                                ((memq major-mode '(Man-mode woman-mode))
                                 (buffer-substring (point-min) (save-excursion (goto-char (point-min))
                                                                               (skip-syntax-forward "^ ")
                                                                               (point))))
                                (t nil)))
                (defname  (and defname  (bmkp-replace-regexp-in-string "\n" " " defname)))
                (bname    (or name  (bmkp-completing-read-lax
                                     "Set bookmark"
                                     (bmkp-new-bookmark-default-names defname)
                                     (and (or (not parg)  (consp parg)) ; No numeric PARG: all bookmarks.
                                          (bmkp-specific-buffers-alist-only))
                                     nil 'bookmark-history))))
           ;; BNAME should not be "" now, since `bmkp-new-bookmark-default-names' should provide default(s)
           ;; and empty input to `bmkp-completing-read-lax' returns the default.  But just in case...
           (when (and (string= bname "")  defname) (setq bname  defname))
           (while (string= "" bname)
             (message "Enter a NON-EMPTY bookmark name") (sit-for 2)
             (setq bname  (bmkp-completing-read-lax
                           "Set bookmark"
                           (bmkp-new-bookmark-default-names defname)
                           (and (or (not parg)  (consp parg)) ; No numeric PARG: all bookmarks.
                                (bmkp-specific-buffers-alist-only))
                           nil 'bookmark-history)))
           (let ((old-bmk  (bmkp-get-bookmark-in-alist bname 'NOERROR))
                 old-prop)
             (when (and interactivep  bmkp-bookmark-set-confirms-overwrite-p  (atom parg)  old-bmk
                        (not (y-or-n-p (format "Overwrite bookmark `%s'? " bname))))
               (error "OK, canceled"))
             (when old-bmk              ; Restore props of existing bookmark per `bmkp-properties-to-keep'.
               (dolist (prop  bmkp-properties-to-keep)
                 (bookmark-prop-set record prop (bookmark-prop-get old-bmk prop)))))
           (bookmark-store bname (cdr record) (consp parg) no-refresh-p (not interactivep))
           (when (and interactivep  bmkp-prompt-for-tags-flag)
             (bmkp-add-tags bname (bmkp-read-tags-completing) 'NO-UPDATE-P)) ; Do not update here.
           (case (and (boundp 'bmkp-auto-light-when-set)  bmkp-auto-light-when-set)
             (autonamed-bookmark       (when (bmkp-autonamed-bookmark-p bname)
                                         (bmkp-light-bookmark bname)))
             (non-autonamed-bookmark   (unless (bmkp-autonamed-bookmark-p bname)
                                         (bmkp-light-bookmark bname)))
             (any-bookmark             (bmkp-light-bookmark bname))
             (autonamed-in-buffer      (bmkp-light-bookmarks (bmkp-autonamed-this-buffer-alist-only)
                                                             nil interactivep))
             (non-autonamed-in-buffer  (bmkp-light-bookmarks
                                        (bmkp-remove-if #'bmkp-autonamed-this-buffer-bookmark-p
                                                        (bmkp-this-buffer-alist-only))
                                        nil interactivep))
             (all-in-buffer            (bmkp-light-this-buffer nil interactivep)))
           ;; Maybe make bookmark temporary.
           (if bmkp-autotemp-all-when-set-p
               (bmkp-make-bookmark-temporary bname)
             (catch 'bookmark-set
               (dolist (pred  bmkp-autotemp-bookmark-predicates)
                 (when (and (functionp pred)  (funcall pred bname))
                   (bmkp-make-bookmark-temporary bname)
                   (throw 'bookmark-set t)))))
           (run-hooks 'bmkp-after-set-hook)
           (if bookmark-use-annotations
               (bookmark-edit-annotation bname)
             (goto-char bookmark-current-point)))) ; `bookmark-current-point' is a free var here.
    (setq bookmark-yank-point     nil
          bookmark-current-buffer nil)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Put full bookmark record on the name as property `bmkp-full-record'.
;; Add BOOKMARK to `bmkp-modified-bookmarks'.
;;
(defun bookmark-set-name (bookmark newname)
  "Set name of BOOKMARK to NEWNAME.
BOOKMARK is a bookmark name or a bookmark record."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (setcar bookmark newname)
  ;; Put the full bookmark on its name as property `bmkp-full-record'.
  ;; Do this regardless of Emacs version and `bmkp-propertize-bookmark-names-flag'.
  ;; If it needs to be stripped, that will be done when saving.
  (put-text-property 0 (length newname) 'bmkp-full-record bookmark newname)
  ;; This is the same as `add-to-list' with `EQ' (not available for Emacs 20-21).
  (unless (memq bookmark bmkp-modified-bookmarks)
    (setq bmkp-modified-bookmarks  (cons bookmark bmkp-modified-bookmarks))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Prevent adding a newline in a bookmark name when yanking.
;;
;;;###autoload (autoload 'bookmark-yank-word "bookmark+")
(defun bookmark-yank-word ()            ; Bound to `C-M-w' in minibuffer when setting bookmark.
  "Yank the word at point in `bookmark-current-buffer'.
Repeat to yank consecutive words from the current buffer, appending
them to the minibuffer.  However, newline characters between yanked
words are stripped out."
  (interactive)
  (let ((string  (with-current-buffer bookmark-current-buffer
                   (goto-char bookmark-yank-point)
                   (buffer-substring-no-properties (point)
                                                   (progn (forward-word 1)
                                                          (setq bookmark-yank-point  (point)))))))
    (setq string  (bmkp-replace-regexp-in-string "\n" "" string))
    (insert string)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Separate renaming of obsolete default bookmark name (do it even if not loading the default file).
;; 2. Load `bmkp-last-as-first-bookmark-file' if it is non-nil.
;;
(defun bookmark-maybe-load-default-file ()
  "If bookmarks have not yet been loaded, load them.
If `bmkp-last-as-first-bookmark-file' is non-nil, load it.
Otherwise, load `bookmark-default-file'."
  ;; If there is no file at `bookmark-default-file' but there is a file with the obsolete default
  ;; name, then rename that file to the value of `bookmark-default-file'.
  ;; Do this regardless of whether it is `bookmark-default-file' that we load here.
  (when (and (file-exists-p bookmark-old-default-file)  (not (file-exists-p bookmark-default-file)))
    (rename-file bookmark-old-default-file bookmark-default-file))
  (let ((file-to-load  (bmkp-default-bookmark-file)))
    (and (not bookmarks-already-loaded)
         (null bookmark-alist)
         (file-readable-p file-to-load)
         (bookmark-load file-to-load t 'nosave)
         (setq bookmarks-already-loaded  t))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Save DISPLAY-FUNCTION to `bmkp-jump-display-function' before calling `bookmark-handle-bookmark'.
;; 2. Update the name and position of an autonamed bookmark, in case it moved.
;; 3. Possibly highlight bookmark and other bookmarks in buffer, per `bmkp-auto-light-when-jump'.
;; 4. Added `catch', so a handler can throw to skip the rest of the processing if it wants.
;;
(defun bookmark--jump-via (bookmark display-function)
  "Display BOOKMARK using DISPLAY-FUNCTION.
Then run `bookmark-after-jump-hook' and show annotations for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bmkp-record-visit bookmark 'BATCHP)
  (setq bmkp-jump-display-function  display-function)
  (catch 'bookmark--jump-via
    (bookmark-handle-bookmark bookmark)
    (unless (and bmkp-use-w32-browser-p  (fboundp 'w32-browser)  (bookmark-get-filename bookmark))
      (let ((win  (get-buffer-window (current-buffer) 0)))
        (when win (set-window-point win (point))))
      ;; If this is an autonamed bookmark, update its name and position, in case it moved.
      ;; But don't do this if we're using w32, since we might not have moved to the bookmark position.
      (when (and (bmkp-autonamed-bookmark-for-buffer-p bookmark (buffer-name))
                 (not bmkp-use-w32-browser-p))
        (setq bookmark  (bmkp-update-autonamed-bookmark bookmark)))
      (case (and (boundp 'bmkp-auto-light-when-jump)  bmkp-auto-light-when-jump)
        (autonamed-bookmark       (when (bmkp-autonamed-bookmark-p bookmark)
                                    (bmkp-light-bookmark bookmark nil nil nil 'USE-POINT)))
        (non-autonamed-bookmark   (unless (bmkp-autonamed-bookmark-p bookmark)
                                    (bmkp-light-bookmark bookmark nil nil nil 'USE-POINT)))
        (any-bookmark             (bmkp-light-bookmark bookmark nil nil nil 'USE-POINT))
        (autonamed-in-buffer      (bmkp-light-bookmarks
                                   (bmkp-remove-if-not #'bmkp-autonamed-bookmark-p
                                                       (bmkp-this-buffer-alist-only))
                                   nil 'MSG))
        (non-autonamed-in-buffer  (bmkp-light-bookmarks (bmkp-remove-if #'bmkp-autonamed-bookmark-p
                                                                        (bmkp-this-buffer-alist-only))
                                                        nil 'MSG))
        (all-in-buffer            (bmkp-light-this-buffer nil 'MSG))))
    (let ((orig-buff  (current-buffer))) ; Used by `crosshairs-highlight'.
      (run-hooks 'bookmark-after-jump-hook))
    (let ((jump-fn  (bmkp-get-tag-value bookmark "bmkp-jump")))
      (when jump-fn (funcall jump-fn)))
    (when bookmark-automatically-show-annotations (bookmark-show-annotation bookmark))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Add to beginning, not end, of bookmark record.
;; 2. Do not use `nconc'.
;; 3. Respect both old and newer bookmark formats.
;; 4. Add BOOKMARK to `bmkp-modified-bookmarks'.
;;
(defun bookmark-prop-set (bookmark prop val)
  "Set the entry (property) PROP of BOOKMARK to VAL.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let* ((bmk   (bookmark-get-bookmark bookmark))
         (cell  (assq prop (bmkp-bookmark-data-from-record bmk))))
    (if cell
        (setcdr cell val)
      (setcdr bmk (if (consp (car (cadr bmk)))
                      (list (cons (cons prop val) (cadr bmk))) ; Old format: ("name" ((filename . "f")...))
                    (cons (cons prop val) (cdr bmk))))) ; New format:        ("name" (filename . "f")...)
    ;; This is the same as `add-to-list' with `EQ' (not available for Emacs 20-21).
    (unless (memq bmk bmkp-modified-bookmarks)
      (setq bmkp-modified-bookmarks  (cons bmk bmkp-modified-bookmarks)))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg FLIP-USE-REGION-P.
;; 2. Use `bmkp-default-bookmark-name' as default when interactive.
;; 3. Use `bmkp-jump-1'.
;; 4. Added note about Icicles `S-delete' to doc string.
;;
;;;###autoload (autoload 'bookmark-jump "bookmark+")
(defun bookmark-jump (bookmark          ; Bound to `C-x j j', `C-x r b', `C-x p g'
                      &optional display-function flip-use-region-p)
  "Jump to bookmark BOOKMARK.
You may have a problem using this function if the value of variable
`bookmark-alist' is nil.  If that happens, you need to load in some
bookmarks.  See function `bookmark-load' for more about this.

If the file pointed to by BOOKMARK no longer exists, you are asked if
you wish to give the bookmark a new location.  If so, `bookmark-jump'
jumps to the new location and saves it.

If the bookmark defines a region, then the region is activated if
`bmkp-use-region' is not-nil or it is nil and you use a prefix
argument.  A prefix arg temporarily flips the value of
`bmkp-use-region'.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.

In Lisp code:
BOOKMARK is a bookmark name or a bookmark record.
Non-nil DISPLAY-FUNCTION is a function to display the bookmark.  By
 default, `switch-to-buffer' is used.
Non-nil FLIP-USE-REGION-P flips the value of `bmkp-use-region'."
  (interactive (list (bookmark-completing-read "Jump to bookmark" (bmkp-default-bookmark-name))
                     nil
                     current-prefix-arg))
  (bmkp-jump-1 bookmark (or display-function 'switch-to-buffer) flip-use-region-p))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg FLIP-USE-REGION-P.
;; 2. Use `bmkp-default-bookmark-name' as default when interactive.
;; 3. Use `bmkp-jump-1'.
;;
;;;###autoload (autoload 'bookmark-jump-other-window "bookmark+")
(defun bookmark-jump-other-window (bookmark &optional flip-use-region-p)
                                        ; Bound to `C-x 4 j j', `C-x p j', `C-x p o', `C-x p q'
  "Jump to bookmark BOOKMARK in another window.
See `bookmark-jump', in particular for info about using a prefix arg."
  (interactive (list (bookmark-completing-read "Jump to bookmark (in another window)"
                                               (bmkp-default-bookmark-name))
                     current-prefix-arg))
  (bmkp-jump-1 bookmark 'bmkp-select-buffer-other-window flip-use-region-p))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Invoke MS Windows `Open' action if `bmkp-use-w32-browser-p' and if `w32-browser' is defined.
;;
;; 2. Favor entry `file-handler' over entry `handler'.  If the former is available, apply it to the file.
;;
;; 3. If BOOKMARK has its own handler but that is not a defined function, then use the default handler.
;;    This lets Emacs 22, for instance, handle Emacs 23+ image bookmarks.
;;
;; 4. Different relocation message for non-file bookmark.
;;
(defun bookmark-handle-bookmark (bookmark)
  "Call BOOKMARK's handler, or `bookmark-default-handler' if it has none.
Return nil or raise an error.

BOOKMARK is a bookmark name or a bookmark record.

More precisely:

  If `bmkp-use-w32-browser-p' is non-`nil' and `w32-browser' is
  defined then invoke the MS Windows `Open' action.

  Else, if BOOKMARK has both `file-handler' and `filename' entries
  then apply the former to the latter.

  Else, if BOOKMARK has a `handler' entry whose value is a defined
  function then apply it to BOOKMARK.

  Else, apply the default bookmark handler,
  `bookmark-default-handler', to BOOKMARK.

The default handler changes the current buffer and point.

If the default handler is used and a file error is raised, the error
is handled as follows:
 If BOOKMARK has no `filename' entry, do nothing.
 Else prompt to relocate the file.
   If relocated, then try again to handle.  Else raise a file error."
  (cond ((and bmkp-use-w32-browser-p  (fboundp 'w32-browser)  (bookmark-get-filename bookmark))
         (w32-browser (bookmark-get-filename bookmark))
         ;; This `throw' is only for the case where this handler is called from `bookmark--jump-via'.
         ;; It tells `bookmark--jump-via' to skip the rest of what it does after calling the handler.
         (condition-case nil (throw 'bookmark--jump-via 'BOOKMARK-HANDLE-BOOKMARK) (no-catch nil)))
        ((functionp (bookmark-prop-get bookmark 'file-handler))
         (funcall (bookmark-prop-get bookmark 'file-handler) (bookmark-get-filename bookmark)))
        ((functionp (bookmark-get-handler bookmark))
         (funcall (bookmark-get-handler bookmark) (bookmark-get-bookmark bookmark)))
        (t
         (condition-case err
             (funcall 'bookmark-default-handler (bookmark-get-bookmark bookmark))
           (bookmark-error-no-filename  ; `file-error'
            ;; BOOKMARK can be either a bookmark name or a bookmark record.
            ;; If a record, do nothing - assume it is a bookmark used internally by some other package.
            (when (stringp bookmark)
              (let ((file             (bookmark-get-filename bookmark))
                    (use-dialog-box   nil)
                    (use-file-dialog  nil))
                (when file
                  ;; Ask user whether to relocate the file.  If no, signal the file error.
                  (unless (string= file bmkp-non-file-filename) (setq file  (expand-file-name file)))
                  (ding)
                  (cond ((y-or-n-p (if (and (string= file bmkp-non-file-filename)
                                            (bmkp-get-buffer-name bookmark))
                                       "Bookmark's buffer does not exist.  Re-create it? "
                                     (concat (file-name-nondirectory file) " nonexistent.  Relocate \""
                                             bookmark "\"? ")))
                         (if (string= file bmkp-non-file-filename)
                             ;; This is probably not the right way to get the correct buffer, but it's
                             ;; better than nothing, and it gives the user a chance to DTRT.
                             (pop-to-buffer (bmkp-get-buffer-name bookmark)) ; Create buffer.
                           (bookmark-relocate bookmark)) ; Relocate to file.
                         (funcall (or (bookmark-get-handler bookmark) 'bookmark-default-handler)
                                  (bookmark-get-bookmark bookmark))) ; Try again
                        (t
                         (message "Bookmark not relocated: `%s'" bookmark)
                         (signal (car err) (cdr err)))))))))))
  (when (stringp bookmark) (setq bookmark-current-bookmark  bookmark))
  ;; $$$$$$ The vanilla code returns nil, but there is no explanation of why and no code seems
  ;; to use the return value.  Perhaps we should return the bookmark instead?
  nil)                                  ; Return nil if no error.

(put 'bookmark-error-no-filename 'error-conditions
     '(error bookmark-errors bookmark-error-no-filename))
(put 'bookmark-error-no-filename 'error-message "Bookmark has no associated file (or directory)")


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Support regions, buffer names, and entry `file-handler'.
;; 2. Handle MS Windows `Open' command if `bmkp-use-w32-browser-p' and if `w32-browser' is defined.
;;
(defun bookmark-default-handler (bookmark)
  "Default handler to jump to the location of BOOKMARK.
Return nil (or raise an error).

BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'.

If `bmkp-use-w32-browser-p' is non-nil and function `w32-browser' is
defined, then call `w32-browser'.  That is, use the default MS Windows
application for the bookmarked file.

If BOOKMARK has entries `file-handler' and `filename', then apply the
value of the former to the latter.

If BOOKMARK is an old-style Info bookmark, then go to the Info node.

If BOOKMARK records a nonempty region and `bmkp-use-region' is
 non-nil then activate the region.

Otherwise, call `bmkp-goto-position' to go to the recorded position."
  (let* ((bmk            (bookmark-get-bookmark bookmark))
         (file           (bookmark-get-filename bmk))
         (buf            (bookmark-prop-get bmk 'buffer))
         (bufname        (bmkp-get-buffer-name bmk))
         (pos            (bookmark-get-position bmk))
         (end-pos        (bmkp-get-end-position bmk))
         (old-info-node  (and (not (bookmark-get-handler bookmark))  (bookmark-prop-get bmk 'info-node))))

    (cond ((and bmkp-use-w32-browser-p  (fboundp 'w32-browser)  file)  (w32-browser file))
          ((and (bookmark-prop-get bookmark 'file-handler)  file)
           (funcall (bookmark-prop-get bookmark 'file-handler) file))
          (old-info-node                ; Emacs 20-21 Info bookmarks - no handler entry.
           (progn (require 'info)
                  (Info-find-node file old-info-node)
                  (when pos (goto-char pos))))
          ((not (and bmkp-use-region  pos  end-pos  (/= pos end-pos)))
           ;; Single-position bookmark (no region).  Go to it.
           (bmkp-goto-position bmk file buf bufname pos
                               (bookmark-get-front-context-string bmk)
                               (bookmark-get-rear-context-string bmk)))
          (t
           ;; Bookmark with a region.  Go to it and activate the region.
           (if (and file  (file-readable-p file)  (not (buffer-live-p buf)))
;;; $$$$$$$    (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect file))
               (with-current-buffer (find-file-noselect file) (setq buf  (buffer-name)))
             ;; No file found.  If no buffer either, then signal that file doesn't exist.
             (unless (or (and buf  (get-buffer buf))
                         (and bufname  (get-buffer bufname)  (not (string= buf bufname))))
               (signal 'bookmark-error-no-filename (list 'stringp file))))
           (set-buffer (or buf  bufname))
           (when bmkp-jump-display-function
             (save-current-buffer (funcall bmkp-jump-display-function (current-buffer)))
             (raise-frame))
           (goto-char (if pos (min pos (point-max)) (point-max)))
           (when (and pos  (> pos (point-max))) (error "Bookmark position is beyond buffer end"))
           ;; Activate region.  Relocate it if it moved.  Save relocated bookmark if confirm.
           (funcall bmkp-handle-region-function bmk)))
    ;; $$$$$$ The vanilla code returns nil, but there is no explanation of why and no code seems
    ;; to use the return value.  Perhaps we should return the bookmark instead?
    nil))                               ; Return nil if no file error.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg NO-REFRESH-P.
;; 2. Added bookmark default for interactive use.
;; 3. Added note about `S-delete' to doc string.
;; 4. Changed arg name: BOOKMARK -> BOOKMARK-NAME.
;; 5. Update Dired location too, for Dired bookmark.
;; 6. Refresh menu list, to show new location.
;;
;;;###autoload (autoload 'bookmark-relocate "bookmark+")
(defun bookmark-relocate (bookmark-name &optional no-refresh-p) ; Not bound
  "Relocate the bookmark named BOOKMARK-NAME to another file.
You are prompted for the new file name.
Non-nil optional arg NO-REFRESH-P means do not refresh/rebuild the
bookmark-list display.

Changes the file associated with the bookmark.
Useful when a file has been renamed after a bookmark was set in it.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (list (bookmark-completing-read "Bookmark to relocate" (bmkp-default-bookmark-name))))
  (bookmark-maybe-historicize-string bookmark-name)
  (bookmark-maybe-load-default-file)
  (let* ((icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
         (bookmark-filename                           (bookmark-get-filename bookmark-name))
         (new-filename                                (abbreviate-file-name
                                                       (expand-file-name
                                                        (read-file-name
                                                         (format "Relocate %s to: " bookmark-name)
                                                         (file-name-directory bookmark-filename))))))
    (bookmark-set-filename bookmark-name new-filename)
    ;; Change location for Dired too, but not if different from original file name (e.g. a cons).
    (let ((dired-dir  (bookmark-prop-get bookmark-name 'dired-directory)))
      (when (and dired-dir  (equal dired-dir bookmark-filename))
        (bookmark-prop-set bookmark-name 'dired-directory new-filename))))
  (bmkp-maybe-save-bookmarks)
  (when (and bookmark-bmenu-toggle-filenames  (get-buffer "*Bookmark List*")
             (get-buffer-window (get-buffer "*Bookmark List*") 0)
             (not no-refresh-p))
    (with-current-buffer (get-buffer "*Bookmark List*") ; Do NOT just use `bmkp-refresh/rebuild-menu-list'.
      (bmkp-refresh-menu-list bookmark-name)))) ; So display new location and `*' marker.


;; REPLACES ORIGINAL in `bookmark.el' (it was removed from `bookmark.el' in Emacs 24.3 - Emacs bug #19838).
;;
;; No change from original, except provide a better doc string.
;;
;;;###autoload (autoload 'bookmark-insert-current-bookmark "bookmark+")
(unless (fboundp 'bookmark-insert-current-bookmark)
  (defun bookmark-insert-current-bookmark () ; Emacs 24.3+
    "Insert current-bookmark name or buffer file name, if none.
That is, if `bookmark-current-bookmark' in `bookmark-current-buffer'
is not nil then insert that."
    (interactive)
    (let ((str  (with-current-buffer bookmark-current-buffer
                  (or bookmark-current-bookmark  (bookmark-buffer-name)))))
      (insert str))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added bookmark default for interactive use.
;; 2. Do not add any text properties here.  That's done in `bmkp-bmenu-propertize-item'.
;; 3. Added note about `S-delete' to doc string.
;; 4. Changed arg name: BOOKMARK -> BOOKMARK-NAME.
;;
;;;###autoload (autoload 'bookmark-insert-location "bookmark+")
(defun bookmark-insert-location (bookmark-name &optional no-history) ; `C-x p I' (original: `C-x p f')
  "Insert file or buffer name for the bookmark named BOOKMARK-NAME.
If a file is bookmarked, insert the recorded file name.
If a non-file buffer is bookmarked, insert the recorded buffer name.

Optional arg NO-HISTORY means do not record BOOKMARK-NAME in
`bookmark-history'.

If you use Icicles then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive
   (let ((bmk  (bookmark-completing-read "Insert bookmark location" (bmkp-default-bookmark-name))))
     (if (> emacs-major-version 21) (list bmk) bmk)))
  (unless no-history (bookmark-maybe-historicize-string bookmark-name))
  (insert (bookmark-location bookmark-name))) ; Return the line inserted.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Pass full bookmark to the various "get" functions.
;; 2. Location returned can be a buffer name.
;;
(defun bookmark-location (bookmark)
  "Return a description of the location of BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'.

Look first for entry `location', then for entry `buffer-name' or
`buffer', then for entry `filename'.  Return the first such entry
found, or \"-- Unknown location --\" if none is found."
  (bookmark-maybe-load-default-file)
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (or (bookmark-prop-get bookmark 'location)
      (bmkp-get-buffer-name bookmark)   ; Entry `buffer-name'.
      (bookmark-prop-get bookmark 'buffer) ; Entry `buffer'.
      (bookmark-get-filename bookmark)
      "-- Unknown location --"))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added BATCHP arg.  Return OLD if BATCHP is non-nil and NEW is nil.
;; 2. Rename also in marked and omitted lists.
;; 3. Use `bmkp-bookmark-record-from-name', not `bookmark-get-bookmark'.
;; 4. Use `bmkp-completing-read-lax', not `read-from-minibuffer'.
;; 5. Put `bmkp-full-record' property on new name.
;; 3. Use `bmkp-bookmark-record-from-name', not `bookmark-get-bookmark'.
;; 4. Added note about `S-delete' to doc string.
;; 6. Refresh menu list, to show new name.
;;
;;;###autoload (autoload 'bookmark-rename "bookmark+")
(defun bookmark-rename (old &optional new batchp) ; Not bound in Bookmark+
  "Change bookmark's name from OLD to NEW.
Interactively:
 If called from the keyboard, then prompt for OLD.
 If called from the menubar, select OLD from a menu.
If NEW is nil, then prompt for its string value (unless BATCH).

When entering the NEW name you can use completion against existing
bookmark names.  This completion is lax, so you can easily edit an
existing name.  See `bookmark-set' for particular keys available
during this input.

If BATCHP is non-nil, then do not rebuild the bookmark list.  (NEW
should be non-nil if BATCH is non-nil.)

If you use Icicles then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (list (bookmark-completing-read "Old bookmark name" (bmkp-default-bookmark-name))))
  (bookmark-maybe-historicize-string old)
  (bookmark-maybe-load-default-file)
  (setq bookmark-current-point  (point)) ; `bookmark-current-point' is a free var here.
  (save-excursion (skip-chars-forward " ") (setq bookmark-yank-point  (point)))
  (setq bookmark-current-buffer  (current-buffer))
  (let ((newname  (or new  (and (not batchp)  (bmkp-completing-read-lax "New name" old)))))
;;; $$$$$$  (read-from-minibuffer "New name: " nil
;;;           (let ((now-map  (copy-keymap minibuffer-local-map)))
;;;             (define-key now-map  "\C-w" 'bookmark-yank-word)
;;;             now-map)
;;;           nil 'bookmark-history))))

    (when newname
      (bookmark-set-name old newname)
      ;; Put the bookmark on the name as property `bmkp-full-record'.
      ;; Do this regardless of Emacs version and `bmkp-propertize-bookmark-names-flag'.
      ;; If it needs to be stripped, that will be done when saving.
      (put-text-property 0 (length newname) 'bmkp-full-record (bmkp-bookmark-record-from-name newname)
                         newname)
      (bmkp-rename-for-marked-and-omitted-lists old newname) ; Rename in marked & omitted lists, if present.
      (setq bookmark-current-bookmark  newname)
      (unless batchp
        (if (and (get-buffer "*Bookmark List*")  (get-buffer-window (get-buffer "*Bookmark List*") 0))
            (with-current-buffer (get-buffer "*Bookmark List*")
              (bmkp-refresh-menu-list newname)) ; So the new name is displayed.
          (bookmark-bmenu-surreptitiously-rebuild-list)))
      (bmkp-maybe-save-bookmarks))
    (or newname old)))                  ; NEWNAME is nil only if BATCHP is non-nil and NEW was nil.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added bookmark default for interactive use.
;; 2. Added note about `S-delete' to doc string.
;; 3. Changed arg name: BOOKMARK -> BOOKMARK-NAME.
;;
(or (fboundp 'bmkp-ORIG-bookmark-insert)
(fset 'bmkp-ORIG-bookmark-insert (symbol-function 'bookmark-insert)))

;;;###autoload (autoload 'bookmark-insert "bookmark+")
(defun bookmark-insert (bookmark-name)  ; Bound to `C-x p i'
  "Insert the text of a bookmarked file.
BOOKMARK-NAME is the name of the bookmark.
You may have a problem using this function if the value of variable
`bookmark-alist' is nil.  If that happens, you need to load in some
bookmarks.  See function `bookmark-load' for more about this.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (list (bookmark-completing-read "Insert bookmark contents" (bmkp-default-bookmark-name))))
  (bmkp-ORIG-bookmark-insert bookmark-name))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Accept a bookmark or a bookmark name as arg.
;; 2. Use `bmkp-default-bookmark-name' as default when interactive.
;; 3. Use `bmkp-get-bookmark-in-alist', not `bookmark-get-bookmark'.
;; 4. Remove highlighting for the bookmark.
;; 5. Doc string includes note about `S-delete' for Icicles.
;; 6. Update `bmkp-latest-bookmark-alist', `bmkp-bmenu-omitted-bookmarks', and `bmkp-auto-idle-bookmarks'.
;; 7. Increment `bookmark-alist-modification-count' even when BATCHP is non-nil.
;;
;;;###autoload (autoload 'bookmark-delete "bookmark+")
(defun bookmark-delete (bookmark &optional batchp) ; Bound to `C-x p d'
  "Delete the BOOKMARK from the bookmark list.
BOOKMARK is a bookmark name or a bookmark record.
Interactively, default to the \"current\" bookmark (that is, the one
most recently used in this file), if it exists.

If BOOKMARK is a name and it has property `bmkp-full-record' then use
that property along with the name to find the bookmark to delete.
If it is a name without property `bmkp-full-record' then delete (only)
the first bookmark in `bookmark-alist' with that name.

Optional arg BATCHP means do not update buffer `*Bookmark List*'.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.  In this way, you can delete multiple bookmarks."
  (interactive (list (bookmark-completing-read "Delete bookmark" (bmkp-default-bookmark-name))))

  ;; $$$$$$ Instead of loading unconditionally, maybe we should just try to delete conditionally?
  ;; IOW, why not (when bookmarks-already-loaded BODY) instead of `bookmark-maybe-load-default-file'?
  ;; If it gets called on a hook that gets run before ever loading, then should probably do nothing.
  ;; Leaving it as is for now (2011-04-06).
  (bookmark-maybe-load-default-file)

  (let* ((bmk    (bookmark-get-bookmark bookmark 'NOERROR))
         (bname  (bmkp-bookmark-name-from-record bmk))) ; BOOKMARK might have been a bookmark.
    (when bname                         ; Do nothing if BOOKMARK does not represent a bookmark.
      (bookmark-maybe-historicize-string bname)
      (when (fboundp 'bmkp-unlight-bookmark) (bmkp-unlight-bookmark bmk 'NOERROR))
      (setq bookmark-alist                (delq bmk bookmark-alist)
            bmkp-latest-bookmark-alist    (delq bmk bmkp-latest-bookmark-alist)
            bmkp-auto-idle-bookmarks      (delq bmk bmkp-auto-idle-bookmarks)
            bmkp-bmenu-omitted-bookmarks  (bmkp-delete-bookmark-name-from-list
                                           bname bmkp-bmenu-omitted-bookmarks))
      (unless (bmkp-get-bookmark-in-alist bookmark-current-bookmark 'NOERROR)
        (setq bookmark-current-bookmark  nil)) ; Make this nil if last occurrence of BMK was deleted.
       ;; Do NOT refresh/rebuild if BATCHP.  Caller must do that if batching deletions.
      (unless batchp (bmkp-refresh/rebuild-menu-list))
      (bmkp-maybe-save-bookmarks))))    ; Increments `bookmark-alist-modification-count'.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Use `bmkp-current-bookmark-file', not `bookmark-default-file'.
;; 2. Update `bmkp-last-as-first-bookmark-file' if it is non-nil.
;; 3. Reset `bmkp-modified-bookmarks' to ().
;; 4. Call `bmkp-refresh/rebuild-menu-list'.
;;
;;;###autoload (autoload 'bookmark-save "bookmark+")
(defun bookmark-save (&optional parg file) ; Bound to `C-x p s'
  "Save currently defined bookmarks.
Save by default in the file named by variable
`bmkp-current-bookmark-file'.  With a prefix arg, you are prompted for
the file to save to.

If `bmkp-last-as-first-bookmark-file' is non-nil, update its value to
the file being saved.

To load bookmarks from a specific file, use `\\[bookmark-load]'
\(`bookmark-load').

If called from Lisp:
 With nil PARG and nil FILE, use file `bmkp-current-bookmark-file'.
 With non-nil FILE, use file FILE.
 With non-nil PARG, prompt the user for the file to use."
  (interactive "P")
  (bookmark-maybe-load-default-file)
  (let ((file-to-save
         (cond (file)                   ; Use FILE provided.
               (parg        (bmkp-read-bookmark-file-name
                             "File to save bookmarks in: " nil
                             (bmkp-read-bookmark-file-default)))
               ((not parg)  bmkp-current-bookmark-file))))
    (when (file-directory-p file-to-save) (error "`%s' is a directory, not a file" file-to-save))
    (when (and bmkp-last-as-first-bookmark-file
               bookmark-save-flag)      ; nil if temporary bookmarking mode.
      (customize-save-variable 'bmkp-last-as-first-bookmark-file file-to-save))
    (bookmark-write-file file-to-save))
  ;; Indicate by the count that we have synced the current bookmark file.
  ;; If an error has already occurred somewhere, the count will not be set, which is what we want.
  (setq bookmark-alist-modification-count  0
        bmkp-modified-bookmarks            ())
  (bmkp-refresh/rebuild-menu-list))     ; $$$$$$ Should this be done only when interactive?


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Use `write-file', not `write-region', so backup files are made.
;; 2. Do not save temporary bookmarks (`bmkp-temporary-bookmark-p').
;; 3. Added optional arguments ADD and ALT-MSG.
;;    Do not delete region if ADD.  Position point depending on ADD.
;; 4. Delete contents only if file does not exist (just in case).  Else `bookmark-maybe-upgrade-file-format'.
;; 5. Insert code piecewise, to improve performance when saving `bookmark-alist'.
;;    (Do not let `pp' parse all of `bookmark-alist' at once.)
;; 6. Unless `bmkp-propertize-bookmark-names-flag', remove text properties from bookmark name and file name.
;;    Remove them also from bookmark names in a sequence bookmark `sequence' entry.
;; 7. Bind `print-circle' around `pp', to record bNAME with `bmkp-full-record' prop, when appropriate.
;; 8. Use `case', not `cond'.
;; 9. Run `bmkp-write-bookmark-file-hook' functions after writing the bookmark file.
;;
(defun bookmark-write-file (file &optional add alt-msg)
  "Write `bookmark-alist' to FILE.
Bookmarks that have a non-nil `bmkp-temp' entry are not saved.
They are removed from the bookmark file, but not from the current
bookmark list.

Non-nil optional arg ADD means do not replace the bookmarks in FILE.
If the value is `append' then append `bookmark-list' to them.  Any
other non-nil value means prepend `bookmark-list' to them.  Prepending
means that for some operations the copied bookmarks take precedence
over existing ones with the same name (since an alist is used).

Non-nil ALT-MSG is a message format string to use in place of the
default, \"Saving bookmarks to file `%s'...\".  The string must
contain a `%s' construct, so that it can be passed along with FILE to
`format'.  At the end, \"done\" is appended to the message."
  (let ((msg                      (or alt-msg "Saving bookmarks to file `%s'..."))
        (coding-system-for-write  (if (boundp 'bookmark-file-coding-system) ; Emacs 25.2+.
                                      (or coding-system-for-write  bookmark-file-coding-system  'utf-8-emacs)
                                    coding-system-for-write))
        (print-length             nil)
        (print-level              nil)
        (rem-all-p                (or (not (> emacs-major-version 20)) ; Cannot: (not (boundp 'print-circle)).
                                      (not bmkp-propertize-bookmark-names-flag)))
        (existing-buf             (get-file-buffer file))
        (emacs-lisp-mode-hook     nil)  ; Avoid inserting automatic file header if existing empty file, so
        (lisp-mode-hook           nil)  ; better chance `bookmark-maybe-upgrade-file-format' signals error.
        bname fname last-fname start end)
    (when (file-directory-p file) (error "`%s' is a directory, not a file" file))
    (message msg (abbreviate-file-name file))
    (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect file))
      (goto-char (point-min))
      (if (file-exists-p file)
          (bookmark-maybe-upgrade-file-format)
        (delete-region (point-min) (point-max)) ; In case a find-file hook inserted a header, etc.
        (unless (boundp 'bookmark-file-coding-system) ; Emacs < 25.2.
          (bookmark-insert-file-format-version-stamp))
        (insert "(\n)"))
      (setq start  (and (file-exists-p file)
                        (or (save-excursion (goto-char (point-min))
                                            (search-forward (concat bookmark-end-of-version-stamp-marker "(")
                                                            nil t))
                            (error "Invalid bookmark-file")))
            end    (and start
                        (or (save-excursion (goto-char start) (and (looking-at ")") start)) ; Empty bmk list: ().
                            (save-excursion (goto-char (point-max)) (re-search-backward "^)" nil t))
                            (error "Invalid bookmark-file"))))
      (if (not start)                   ; New file, no header yet.
          (goto-char 2)
        ;;  Existing file - delete old bookmarks unless ADD.
        (unless add (delete-region start end))
        (goto-char (if (eq add 'append) end start)))
      (dolist (bmk  bookmark-alist)
        (unless (bmkp-temporary-bookmark-p bmk)
          (setq bname  (car bmk)
                fname  (bookmark-get-filename bmk))
          (cond (rem-all-p              ; Remove text properties from bookmark name and file name.
                 (set-text-properties 0 (length bname) () bname)
                 (when fname (set-text-properties 0 (length fname) () fname)))
                (t                      ; Remove property `face' and any Icicles internal properties.
                 (remove-text-properties 0 (length bname) '(face                     nil
                                                            display                  nil
                                                            help-echo                nil
                                                            rear-nonsticky           nil
                                                            icicle-fancy-candidates  nil
                                                            icicle-mode-line-help    nil
                                                            icicle-special-candidate nil
                                                            icicle-user-plain-dot    nil
                                                            icicle-whole-candidate   nil
                                                            invisible                nil)
                                         bname)
                 (when (boundp 'icicle-candidate-properties-alist) ; Multi-completion indexes + text props.
                   (dolist (entry  icicle-candidate-properties-alist)
                     (put-text-property 0 (length bname) (car (cadr entry)) nil bname)))))
          (setcar bmk bname)
          (when (setq last-fname  (assq 'filename bmk)) (setcdr last-fname fname))
          (let ((print-circle  bmkp-propertize-bookmark-names-flag))
            (if (not (and rem-all-p  (bmkp-sequence-bookmark-p bmk)))
                (pp bmk (current-buffer))
              ;; Remove text properties from bookmark names in the `sequence' entry of sequence bookmark.
              (insert "(\"" (let ((sname  (copy-sequence (car bmk))))
                              (set-text-properties 0 (length sname) () sname)
                              sname)
                      "\"\n")
              (dolist (prop  (cdr bmk))
                (if (not (eq 'sequence (car prop)))
                    (insert " " (pp-to-string prop))
                  (insert " (sequence " (mapconcat (lambda (bname)
                                                     (let ((name  (copy-sequence bname)))
                                                       (set-text-properties 0 (length name) () name)
                                                       (concat "\"" name "\"")))
                                                   (cdr prop) " ")
                          ")\n")))
              (insert " )\n")))))
      (when (boundp 'bookmark-file-coding-system) ; Emacs 25.2+.  See bug #25365
        ;; Make sure specified encoding can encode the bookmarks.  If not, suggest utf-8-emacs as default.
        (with-coding-priority '(utf-8-emacs)
          (setq coding-system-for-write  (select-safe-coding-system (point-min) (point-max)
                                                                    (list t coding-system-for-write))))
        (when start (delete-region 1 (1- start))) ; Delete old header.
        (goto-char 1)
        (bookmark-insert-file-format-version-stamp coding-system-for-write))
      (let ((version-control        (case bookmark-version-control
                                      ((nil)      nil)
                                      (never      'never)
                                      (nospecial  version-control)
                                      (t          t)))
            (require-final-newline  t)
            (errorp                 nil))
        (condition-case nil
            (write-file file)
          (file-error (setq errorp  t)
                      ;; Do NOT raise error.  (Need to be able to exit.)
                      (let ((msg  (format "CANNOT WRITE FILE `%s'" file)))
                        (if (fboundp 'display-warning)
                            (display-warning 'bookmark-plus msg)
                          (message msg)
                          (sit-for 4)))))
        (when (boundp 'bookmark-file-coding-system) ; Emacs 25.2+
          (setq bookmark-file-coding-system  coding-system-for-write))
        (unless existing-buf (kill-buffer (current-buffer)))
        (run-hook-with-args 'bmkp-write-bookmark-file-hook file)
        (unless errorp (message (concat msg "done") file))))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg DUPLICATES-OK.
;;
;; 2. Unless DUPLICATES-OK is non-nil, if a bookmark in NEW-LIST is `equal' to a bookmark in `bookmark-alist'
;;    then do not rename it and do not add it - just ignore it.
;;
;; 3. Return value includes how many bookmarks were added and renamed.
;;    If RETURN-BMKS is non-nil then it also includes which bookmarks were added.
;;
(defun bookmark-import-new-list (new-list &optional duplicates-ok return-bmks)
  "Add NEW-LIST of bookmarks to `bookmark-alist'.
Unless optional arg DUPLICATES-OK is non-nil, ignore bookmarks that
are `equal' to bookmarks in `bookmark-alist'.  (This means that all of
their information is `equal', not just their names.  This includes
their tags and annotations.)

Rename new bookmarks that are not ignored, as needed, using suffix
\"<N>\" (N=2,3...) when they conflict with existing bookmark names.

Return a list (NB-RENAMED NB-ADDED BMKS-ADDED) of the number renamed,
the number added, and the full bookmarks that were added.  If
RETURN-BMKS is nil then BMKS-ADDED is just nil (the bookmarks are not
returned)."
  (let ((names       (bookmark-all-names))
        (nb-added    0)
        (nb-renamed  0)
        (bmks-added  ()))
    (dolist (full-bmk  new-list)
      (when (or (and (not (member full-bmk bookmark-alist)) ; Check even if DUPLICATES-OK, to update ADDEDP.
                     (setq nb-added  (1+ nb-added)))
                duplicates-ok)
        (when (bookmark-maybe-rename full-bmk names) (setq nb-renamed  (1+ nb-renamed)))
        (setq bookmark-alist  (nconc bookmark-alist (list full-bmk)))
        (push (bookmark-name-from-full-record full-bmk) names)
        (when return-bmks (push full-bmk bmks-added))))
    (list nb-renamed nb-added bmks-added)))

;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Return non-nil iff bookmark was renamed.
;;
(defun bookmark-maybe-rename (full-record names)
  "Rename bookmark FULL-RECORD if its current name is already used.
This is a helper for `bookmark-import-new-list'.
Return non-nil if the bookmark was renamed, nil otherwise."
  (let ((found-name  (bookmark-name-from-full-record full-record)))
    (when (member found-name names)
      (let ((count     2)
            (new-name  found-name))
        (while (member new-name names)
          (setq new-name  (concat found-name (format "<%d>" count))
                count     (1+ count)))
        (bookmark-set-name full-record new-name)
        (not (string= found-name new-name))))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg means OVERWRITE.
;; 2. Use `bmkp-read-bookmark-file-name', not `read-file-name', and use different default.
;; 3. If OVERWRITE is non-nil:
;;    * Update `bmkp-last-bookmark-file' to `bmkp-current-bookmark-file'.
;;    * Update `bmkp-current-bookmark-file' to FILE.
;;    * Reset bmenu stuff: `bmkp-bmenu-marked-bookmarks', `bmkp-modified-bookmarks',
;;      `bmkp-flagged-bookmarks', `bmkp-bmenu-omitted-bookmarks', `bmkp-bmenu-filter-function'.
;;    * If `bmkp-last-as-first-bookmark-file', then update it to FILE and save it to disk.
;; 4. If the bookmark-file buffer already existed, do not kill it after loading.
;; 5. Set `bookmarks-already-loaded' regardless of FILE (not just `bookmark-default-file').
;; 6. Update `bmkp-sorted-alist' (it's a cache).
;; 7. Final msg says whether overwritten.
;; 8. Run `bmkp-read-bookmark-file-hook' after reading the bookmark file.
;; 9. Call `bmkp-bmenu-refresh-menu-list' at end, if interactive.
;;
;;;###autoload (autoload 'bookmark-load "bookmark+")
(defun bookmark-load (file &optional overwrite batchp) ; Bound to `C-x p l'
  "Load bookmarks from FILE (which must be in the standard format).
Without a prefix argument (argument OVERWRITE is nil), add the newly
loaded bookmarks to those already current.  They are saved to the
current bookmark file when bookmarks are saved.

If you do not use a prefix argument, then no existing bookmarks are
overwritten.  If you load some bookmarks that have the same names as
bookmarks already defined in your Emacs session, numeric suffixes
\"<2>\", \"<3>\",... are appended as needed to the names of those new
bookmarks to distinguish them.

With a prefix argument, switch the bookmark file currently used,
*replacing* all currently existing bookmarks with the newly loaded
bookmarks.  In this case, the value of `bmkp-current-bookmark-file'is
backed up to `bmkp-last-bookmark-file' and then changed to FILE, so
bookmarks will subsequently be saved to FILE.

If `bmkp-last-as-first-bookmark-file' is non-nil and is not FILE then
it is changed to FILE and saved persistently, so that the next Emacs
session will start with it as the bookmark file.  (The value of
`bookmark-default-file' is unaffected.)

Interactively, if any bookmarks have been modified since last saved
then you are asked whether you want to first save them before loading
FILE.  If you hit `C-g' then both saving and loading are canceled.

`bookmark-load' runs `bmkp-read-bookmark-file-hook' after reading the
bookmark file.

When called from Lisp, non-nil optional arg BATCHP means this is not
an interactive call.  In this case, do not interact with the user: do
not ask whether to save the current (unsaved) bookmark list before
loading; do not display any load progress messages; and do not
update/refresh buffer `*Bookmark List*'.

If BATCHP is `save' and bookmarks have been modified since the
bookmark list was last saved, then save the bookmark list before
loading.

If BATCHP is any other non-nil value besides `save', do not save the
bookmark list.

Your initial bookmark file, either `bmkp-last-as-first-bookmark-file'
or `bookmark-default-file', is loaded automatically by Emacs the first
time you use bookmarks in a session - you do not need to load it
manually.  Use `bookmark-load' only to load extra bookmarks (with no
prefix arg) or an alternative set of bookmarks (with a prefix arg).

If you use `bookmark-load' to load a file that does not contain a
proper bookmark alist, then when bookmarks are saved the current
bookmark file will likely become corrupted.  You should load only
bookmark files that were created using the bookmark functions."
  (interactive
   (list (let ((default  (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                             (bmkp-default-bookmark-file)
                           bmkp-last-bookmark-file)))
           (bmkp-read-bookmark-file-name
            (if current-prefix-arg "Switch to bookmark file: " "Add bookmarks from file: ")
            (or (file-name-directory default) "~/")
            default
            t))
         current-prefix-arg))
  ;; Maybe save first.
  (when (or (eq batchp 'save)
            (and (not batchp)  (> bookmark-alist-modification-count 0)
                 (condition-case err
                     (yes-or-no-p "Save current bookmarks before loading? (`C-g': cancel load) ")
                   (quit  (error "OK, canceled"))
                   (error (error (error-message-string err))))))
    (bookmark-save))
  ;; Load.
  (setq file  (abbreviate-file-name (expand-file-name file)))
  (when (file-directory-p file) (error "`%s' is a directory, not a file" file))
  (unless (file-readable-p file) (error "Cannot read bookmark file `%s'" file))
  (unless batchp (message "Loading bookmarks from `%s'..." file))
  (let ((existing-buf  (get-file-buffer file)))
    (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect file))
      (goto-char (point-min))
      (bookmark-maybe-upgrade-file-format)
      (let ((blist  (bookmark-alist-from-buffer)))
        (unless (listp blist) (error "Invalid bookmark list in `%s'" file))
        (cond (overwrite
               (setq bmkp-last-bookmark-file            bmkp-current-bookmark-file
                     bmkp-current-bookmark-file         file
                     bookmark-alist                     blist
                     bookmark-alist-modification-count  0)
               (setq bmkp-bmenu-marked-bookmarks        () ; Start from scratch.
                     bmkp-modified-bookmarks            ()
                     bmkp-flagged-bookmarks             ()
                     bmkp-bmenu-omitted-bookmarks       (condition-case nil
                                                            (eval (car (get 'bmkp-bmenu-omitted-bookmarks
                                                                            'saved-value)))
                                                          (error nil))
                     bmkp-bmenu-filter-function         nil)
               (when (and bmkp-last-as-first-bookmark-file
                          (not (bmkp-same-file-p bmkp-last-as-first-bookmark-file file)))
                 (customize-save-variable 'bmkp-last-as-first-bookmark-file file)))
              (t
               (bookmark-import-new-list blist)
               (setq bookmark-alist-modification-count  (1+ bookmark-alist-modification-count))))
        (setq bookmarks-already-loaded  t ; Systematically, whenever any file is loaded.
              bmkp-sorted-alist         (bmkp-sort-omit bookmark-alist))
        (when (boundp 'bookmark-file-coding-system) ; Emacs 25.2+
          (setq bookmark-file-coding-system  buffer-file-coding-system))
        (run-hook-with-args 'bmkp-read-bookmark-file-hook blist file))
      (unless (eq existing-buf (current-buffer)) (kill-buffer (current-buffer)))))
  (unless batchp                        ; If appropriate, *CALLER* MUST refresh/rebuild, if BATCHP.
    (bmkp-refresh/rebuild-menu-list)
    (message "%s bookmarks in `%s'" (if overwrite "Switched to" "Added") file)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;;  1. Make it a command (added `interactive' spec).
;;  2. Handle external annotations (jump to their destinations).
;;  3. Added optional arg MSG-P.  Show message if no annotation.
;;  4. If `bookmark-automatically-show-annotations' is `edit' then this is `bookmark-edit-annotation'.
;;  5. Name buffer after the bookmark.
;;  6. Highlight the title, using face `bmkp-heading'.
;;  7. MSG-P means message if no annotation.
;;  8. Set `bookmark-annotation-name'.
;;  9. Manage `buffer-modified-p'.
;; 10. Use `, not ', in title.  (Both are tolerated.)
;; 11. Fit frame to buffer if `one-windowp'.
;; 12. Restore frame selection.
;;
;;;###autoload (autoload 'bookmark-show-annotation "bookmark+")
(defun bookmark-show-annotation (bookmark &optional msg-p)
  "Show the annotation for BOOKMARK, or follow it if external.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'.
If the annotation is external then jump to its destination.
If no annotation and MSG-P is non-nil, show a no-annotation message.

Opens in read-only or edit mode, as chosen by option
`bookmark-automatically-show-annotations'.  You can toggle between
read-only and edit mode using `C-x C-q'."
  (interactive (list (bookmark-completing-read "Show annotation of bookmark"
                                               (bmkp-default-bookmark-name)
                                               (bmkp-annotated-alist-only))))
  (let* ((bmk       (bookmark-get-bookmark bookmark 'NOERROR))
         (bname     (bmkp-bookmark-name-from-record bmk))
         (ann       (and bmk  (bookmark-get-annotation bmk)))
         (external  (and ann  (bmkp-get-external-annotation ann))))
    (if external
        (bmkp-visit-external-annotation external msg-p)
      (if (not (and ann  (not (string-equal ann ""))))
          (when msg-p (message "Bookmark has no annotation"))
        (if (eq 'edit bookmark-automatically-show-annotations)
            (bookmark-edit-annotation bookmark)
          (let ((oframe  (selected-frame)))
            (save-selected-window
              (pop-to-buffer (get-buffer-create (format "*`%s' Annotation*" bname)))
              (let ((buffer-read-only  nil) ; Because buffer might already exist, in view mode.
                    (buf-modified-p    (buffer-modified-p)))
                (delete-region (point-min) (point-max))
                (insert (concat "Annotation for bookmark `" bname "':\n\n"))
                ;; Use `font-lock-ignore' property from library `font-lock+.el', because Org mode
                ;; uses font-lock, which would otherwise wipe out the highlighting added here.
                (add-text-properties (line-beginning-position -1) (line-end-position 1)
                                     '(face              bmkp-heading
                                       font-lock-ignore  t))
                (insert ann)
                (set-buffer-modified-p buf-modified-p))
              (goto-char (point-min))
              (bookmark-show-annotation-mode)
              (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window))
              (set (make-local-variable 'bookmark-annotation-name) bmk))
            (select-frame-set-input-focus oframe)))))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Make it a command (added `interactive' spec).
;; 2. Use `bookmark-maybe-load-default-file', to ensure bookmarks are loaded.
;; 3. Use name `*Bookmark Annotations*', not `*Bookmark Annotation*'.
;; 4. Don't list bookmarks that have no annotation.
;; 5. Highlight bookmark names.  Don't indent annotations.  Add a blank line after each annotation.
;; 6. Use `view-mode'.  `q' uses `quit-window'.
;; 7. Fit frame to buffer if `one-windowp'.
;; 8. Restore frame selection.
;;
;;;###autoload (autoload 'bookmark-show-all-annotations "bookmark+")
(defun bookmark-show-all-annotations ()
  "Display the annotations for all bookmarks.
If called from buffer `*Bookmark List*' then the annotations are shown
in the current sort order."
  (interactive)
  (bookmark-maybe-load-default-file)
  (let ((obuf    (current-buffer))
        (oframe  (selected-frame)))
    (save-selected-window
      (pop-to-buffer (get-buffer-create "*Bookmark Annotations*"))
      (let ((buffer-read-only  nil))    ; Because buffer might already exist, in view mode.
        (delete-region (point-min) (point-max))
        ;; (Could use `bmkp-annotated-alist-only' here instead.)
        (dolist (full-record  (if (equal (buffer-name obuf) "*Bookmark List*")
                                  (bmkp-sort-omit bookmark-alist
                                                  (and (not (eq bmkp-bmenu-filter-function
                                                                'bmkp-omitted-alist-only))
                                                       bmkp-bmenu-omitted-bookmarks))
                                bookmark-alist))
          (let ((ann  (bookmark-get-annotation full-record)))
            (when (and ann  (not (string-equal ann "")))
              (insert (concat (bmkp-bookmark-name-from-record full-record) ":\n"))
              (put-text-property (line-beginning-position 0) (line-end-position 0) 'face 'bmkp-heading)
              (insert ann) (unless (bolp) (insert "\n\n")))))
        (goto-char (point-min))
        (if (> emacs-major-version 23)  ; Incompatible change introduced in Emacs 24.1
            (view-mode-enter)
          (view-mode-enter (cons (selected-window) (cons nil 'quit-window))))
        (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window))))
    (select-frame-set-input-focus oframe)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Save menu-list state to `bmkp-bmenu-state-file'.
;;
(defun bookmark-exit-hook-internal ()   ; This goes on `kill-emacs-hook'.
  "Save currently defined bookmarks and perhaps bookmark menu-list state.
Run `bookmark-exit-hook', then save bookmarks if they were updated.
Then save menu-list state to file `bmkp-bmenu-state-file', but only if
that option is non-nil."
  (run-hooks 'bookmark-exit-hook)
  (when (bookmark-time-to-save-p t)
    (condition-case err                 ; Do NOT raise error.  (Need to be able to exit.)
        (bookmark-save)
      (error (if (fboundp 'display-warning)
                 (display-warning 'bookmark-plus (error-message-string err))
               (message (error-message-string err))
               (sit-for 4))
             nil)))
  (bmkp-save-menu-list-state))
 
;;(@* "Bookmark+ Functions (`bmkp-*')")
;;; Bookmark+ Functions (`bmkp-*') -----------------------------------

(if (fboundp 'find-tag-default-as-regexp)
    (defalias 'bmkp-read-regexp 'read-regexp) ; Emacs 24.3+

  ;; Same as `icicle-find-tag-default-as-regexp' in `icicles-fn.el'.
  (defun bmkp-find-tag-default-as-regexp () ; Emacs < 24.3
    "Return a regexp that matches the default tag at point.
If there is no tag at point, return nil.

When in a major mode that does not provide its own
`find-tag-default-function', return a regexp that matches the
symbol at point exactly."
    (let* ((tagf  (or find-tag-default-function
                      (get major-mode 'find-tag-default-function)
                      'find-tag-default))
           (tag   (funcall tagf)))
      (and tag  (if (eq tagf 'find-tag-default)
                    (format "\\_<%s\\_>" (regexp-quote tag))
                  (regexp-quote tag)))))

  ;; Same as `icicle-read-regexp' in `icicles-fn.el'.
  (if (fboundp 'find-tag-default)
      (defun bmkp-read-regexp (prompt &optional default history) ; Emacs 22-24.2
        "Read and return a regular expression as a string.
If PROMPT does not end with a colon and possibly whitespace then
append \": \" to it.

Optional argument DEFAULT is a string or a list of the form
\(DEFLT . SUGGESTIONS), where DEFLT is a string or nil.

The string DEFAULT or DEFLT is added to the prompt and is returned as
the default value if the user enters empty input.  The empty string is
returned if DEFAULT or DEFLT is nil and the user enters empty input.

SUGGESTIONS is used only for Emacs 23 and later.  It is a list of
strings that can be inserted into the minibuffer using `\\<minibuffer-local-map>\\[next-history-element]'.
The values supplied in SUGGESTIONS are prepended to the list of
standard suggestions, which include the tag at point, the last isearch
regexp, the last isearch string, and the last replacement regexp.

Optional argument HISTORY is a symbol to use for the history list.
If nil then use `regexp-history'."
        (let* ((deflt                  (if (consp default) (car default) default))
               (suggestions            (and (> emacs-major-version 22)
                                            (if (listp default) default (list default))))
               (suggestions            (and (> emacs-major-version 22)
                                            (append
                                             suggestions
                                             (list (bmkp-find-tag-default-as-regexp)
                                                   (car regexp-search-ring)
                                                   (regexp-quote (or (car search-ring)  ""))
                                                   (car (symbol-value
                                                         query-replace-from-history-variable))))))
               (suggestions            (and (> emacs-major-version 22)
                                            (delete-dups (delq nil (delete "" suggestions)))))
               (history-add-new-input  nil) ; Do not automatically add default to history for empty input.
               (input                  (read-from-minibuffer
                                        (cond ((bmkp-string-match-p ":[ \t]*\\'" prompt) prompt)
                                              (deflt (format "%s (default %s): " prompt
                                                             (query-replace-descr deflt)))
                                              (t (format "%s: " prompt)))
                                        nil nil nil (or history  'regexp-history) suggestions t)))
          (if (equal input "")
              (or deflt  input)         ; Return the default value when the user enters empty input.
            (prog1 input                ; Add non-empty input to the history and return input.
              (add-to-history (or history  'regexp-history) input)))))

    (defun bmkp-read-regexp (prompt &optional default history) ; Emacs 20-21
      "Read and return a string.
Optional arg DEFAULT is a string that is returned when the user enters
empty input.  It can also be a list of strings, of which only the
first is used.
Optional arg HISTORY is a symbol to use for the history list.  If nil,
use `regexp-history'."
      (when (consp default) (setq default  (car default)))
      (read-string (cond ((bmkp-string-match-p ":[ \t]*\\'" prompt) prompt)
                         (default (format "%s (default %s): " prompt
                                          (mapconcat #'isearch-text-char-description default "")))
                         (t (format "%s: " prompt)))
                   nil (or history  'regexp-history) default))))

(defun bmkp-new-bookmark-default-names (&optional first-def)
  "Return a list of default names (strings) for a new bookmark.
A non-nil optional arg FIRST-DEF is prepended to the list of names
described below.

If the region is active and non-empty, then the first default name
\(other than FIRST-DEF) is the current buffer name followed by \": \"
and the region prefix (up to `bmkp-bookmark-name-length-max' chars).
The other names are as described below.

Uses option `bmkp-new-bookmark-default-names' to come up with the
other names.  To these names, `bookmark-current-bookmark' and
`bookmark-buffer-name' are appended, if available (non-nil).

NOTE: For Emacs versions prior to Emacs 23, return only a single
default name, not a list of names.  The name is the first in the list
of names described above for Emacs 23+."
  (let ((defs  (and first-def  (list first-def)))
        val)
    (unless (and (< emacs-major-version 23)  defs) ; Just use FIRST-DEF for Emacs < 23.
      ;; If region is active, first default is its text, with buffer name prepended.
      (when (and transient-mark-mode  mark-active  (> (region-end) (region-beginning)))
        (let* ((regname  (concat (buffer-name) ": " (buffer-substring (region-beginning) (region-end))))
               (defname  (bmkp-replace-regexp-in-string
                          "\n" " "
                          (progn (save-excursion (goto-char (region-beginning))
                                                 (skip-chars-forward " ")
                                                 (setq bookmark-yank-point  (point)))
                                 (substring regname 0 (min bmkp-bookmark-name-length-max
                                                           (length regname)))))))
          (if (< emacs-major-version 23) (setq defs  defname) (add-to-list 'defs defname))))
      ;; Names provided by option `bmkp-new-bookmark-default-names',
      ;; plus `bookmark-current-bookmark' and `bookmark-buffer-name'.
      (unless (and (< emacs-major-version 23)  defs)
        (catch 'bmkp-new-bookmark-default-names
          (dolist (fn  bmkp-new-bookmark-default-names)
            (when (functionp fn)        ; Be sure it is defined and is a function.
              (setq val  (funcall fn))
              (when (and (stringp val)  (not (string= "" val)))
                (setq val  (bmkp-replace-regexp-in-string "\n" " " val))
                (if (> emacs-major-version 22)
                    (add-to-list 'defs val)
                  (throw 'bmkp-new-bookmark-default-names (setq defs  val)))))))
        (when (and (< emacs-major-version 23)  (null defs))
          (setq defs  (or bookmark-current-bookmark  (bookmark-buffer-name))))
        (when (listp defs)
          (when bookmark-current-bookmark (push bookmark-current-bookmark defs))
          (let ((buf  (bookmark-buffer-name))) (when buf (push buf defs)))
          (setq defs  (nreverse defs)))))
    defs))

(defun bmkp-bookmark-record-from-name (bookmark-name &optional noerror memp alist)
  "Return the full bookmark (record) that corresponds to BOOKMARK-NAME.
BOOKMARK-NAME must be a string.  If it has non-nil text property
`bmkp-full-record' then use that.  Otherwise, look for the first
bookmark in ALIST that has the given name.

Non-nil optional arg NOERROR means return nil if BOOKMARK-NAME does
not name a valid bookmark or is valid but is not in ALIST.  If NOERROR
is nil then raise an error in this case.

Non-nil optional arg MEMP means that if property `bmkp-full-record' is
available then look up its value (the full bookmark) in ALIST, testing
with `eq'.  If that record is not in ALIST, return nil.

Optional arg ALIST defaults to `bookmark-alist'."
  (unless alist (setq alist  bookmark-alist))
  (let ((full  (get-text-property 0 'bmkp-full-record bookmark-name)))
    (or (and full
             (or (not memp)  (memq full alist))
             full)
        ;; Punt: return first matching bookmark in ALIST.
        (if (fboundp 'assoc-string)     ; Emacs 22+.  Use `assoc-string' for its CASE-FOLD arg.
            (assoc-string bookmark-name alist bookmark-completion-ignore-case)
          (assoc bookmark-name alist))
        (and (not noerror)  (error "No such bookmark in bookmark list: `%s'" bookmark-name)))))

(defun bmkp-rename-for-marked-and-omitted-lists (old new)
  "Replace OLD bookmark name with NEW in marked and omitted lists."
  (when (bmkp-marked-bookmark-p old)
    (setq bmkp-bmenu-marked-bookmarks  (bmkp-delete-bookmark-name-from-list old
                                                                            bmkp-bmenu-marked-bookmarks))
    (push new bmkp-bmenu-marked-bookmarks))
  (when (bmkp-omitted-bookmark-p old)
    (setq bmkp-bmenu-omitted-bookmarks  (bmkp-delete-bookmark-name-from-list old
                                                                             bmkp-bmenu-omitted-bookmarks))
    (push new bmkp-bmenu-omitted-bookmarks)))

(defun bmkp-get-bookmark-in-alist (bookmark &optional noerror alist)
  "Return the full bookmark in ALIST that corresponds to BOOKMARK.
Return nil if there is none.
BOOKMARK is a bookmark name or a bookmark record.

Non-nil optional arg NOERROR means return nil if BOOKMARK does not
represent a valid bookmark or is valid but is not in ALIST.  If
NOERROR is nil then raise an error in this case.

Optional arg ALIST defaults to `bookmark-alist'.

Bookmark membership in ALIST is tested using `eq'.

If BOOKMARK is a bookmark name instead of a full bookmark then return
what `bmkp-bookmark-record-from-name' with non-nil arg MEMP returns.

This function is like `bookmark-get-bookmark', except that
`bookmark-get-bookmark' tests whether BOOKMARK is in `bookmark-alist'
only when it is a string (a bookmark name, not a full bookmark).  When
BOOKMARK is a full bookmark `bookmark-get-bookmark' is thus not a test
for its existence, as is `bmkp-get-bookmark-in-alist'."
  (cond ((consp bookmark) (and (memq bookmark (or alist  bookmark-alist))  bookmark))
        ((stringp bookmark) (bmkp-bookmark-record-from-name bookmark noerror 'MEMP alist))
        (t (and (not noerror)  (error "Invalid bookmark: `%s'" bookmark)))))

(defun bmkp-default-bookmark-file ()
  "`bmkp-last-as-first-bookmark-file', or `bookmark-default-file' if nil."
  (or bmkp-last-as-first-bookmark-file bookmark-default-file))

(defun bmkp-completing-read-bookmarks (&optional alist pred hist names-only-p)
  "Read bookmark names and return the bookmarks named as a list.
You are prompted for each bookmark name.  Hit `RET' with empty input
to end.

ALIST is the bookmark alist to use.  If nil, use `bookmark-alist'.
NAMES-ONLY-P non-nil means return bookmark names, not full bookmarks.
If NAMES-ONLY-P is `lax' then completion is lax."
  (let ((bmks  ())
        (bmk   t))
    (while bmk
      (setq bmk  (bmkp-completing-read-1 "Bookmark (RET for each, empty input to finish)"
                                         "" alist pred hist (eq names-only-p 'lax)))
      (when (equal "" bmk) (setq bmk  nil))
      (when (and bmk  (not names-only-p)) (setq bmk (bmkp-get-bookmark-in-alist bmk 'NO-ERROR alist)))
      (when bmk (push bmk bmks)))
    (setq bmks  (nreverse bmks))
    bmks))

(defun bmkp-completing-read-lax (prompt &optional default alist pred hist)
  "Read a bookmark name, prompting with PROMPT.
Like `bookmark-completing-read', but completion is lax: your input
need not match any existing bookmark name.

In addition:
 * You can use `SPC' and `?' freely when typing the name.
 * You can use `C-M-w' repeatedly to yank consecutive words from the
   current buffer (see `bookmark-yank-word')."
  (let ((orig-C-M-w  (lookup-key minibuffer-local-completion-map (kbd "C-M-w")))
        (orig-C-M-u  (lookup-key minibuffer-local-completion-map (kbd "C-M-u")))
        (orig-SPC    (lookup-key minibuffer-local-completion-map (kbd "SPC")))
        (orig-qmark  (lookup-key minibuffer-local-completion-map (kbd "?"))))
    (unwind-protect
         (progn (define-key minibuffer-local-completion-map (kbd "C-M-w") 'bookmark-yank-word)
                (define-key minibuffer-local-completion-map (kbd "C-M-u") 'bookmark-insert-current-bookmark)
                (unless (and (boundp 'icicle-mode)  icicle-mode
                             (eq orig-SPC 'icicle-self-insert))
                  (define-key minibuffer-local-completion-map (kbd "SPC") 'self-insert-command))
                (unless (and (boundp 'icicle-mode)  icicle-mode
                             (eq orig-qmark 'icicle-self-insert))
                  (define-key minibuffer-local-completion-map   (kbd "?") 'self-insert-command))
                (bmkp-completing-read-1 prompt default alist pred hist t))
      (define-key minibuffer-local-completion-map (kbd "C-M-w") orig-C-M-w)
      (define-key minibuffer-local-completion-map (kbd "C-M-u") orig-C-M-u)
      (define-key minibuffer-local-completion-map (kbd "SPC")   orig-SPC)
      (define-key minibuffer-local-completion-map (kbd "?")     orig-qmark))))

(defun bmkp-completing-read-1 (prompt default alist pred hist laxp)
  "Helper for `bookmark-completing-read' and `bmkp-completing-read-lax'.
LAXP non-nil means use lax (non-strict) completion."
  (bookmark-maybe-load-default-file)
  (setq alist  (or alist bookmark-alist))
  (if (and (not laxp)
           (listp last-nonmenu-event)
           (or (eq t bmkp-menu-popup-max-length)
               (and (integerp bmkp-menu-popup-max-length)
                    (< (length alist) bmkp-menu-popup-max-length))))
      (bookmark-menu-popup-paned-menu
       t prompt
       (if bmkp-sort-comparer           ; Test whether to sort, but always use `string-lessp'.
           (sort (bookmark-all-names alist) 'string-lessp)
         (bookmark-all-names alist)))
    (let* ((icicle-delete-candidate-object  (lambda (cand) ; For `S-delete' in Icicles.
                                              (bookmark-delete (icicle-transform-multi-completion cand))))
           (icicle-bookmark-completing-p    t)
           (completion-ignore-case          bookmark-completion-ignore-case)
           (default                         (and (not (equal "" default))  default)) ; Treat "" like nil.
           (default                         (if (and (consp default)  (< emacs-major-version 23))
                                                (car default)
                                              default))
           (prompt                          (concat prompt (if default
                                                               (format " (%s): " (if (consp default)
                                                                                     (car default)
                                                                                   default))
                                                             ": ")))
           (str                             (completing-read prompt alist pred (not laxp) nil
                                                             (or hist 'bookmark-history) default)))
      str)))

(defun bmkp-jump-1 (bookmark display-function &optional flip-use-region-p)
  "Helper function for `bookmark-jump' commands.
BOOKMARK is a bookmark name or a bookmark record.
DISPLAY-FUNCTION is passed to `bookmark--jump-via'.
Non-nil optional arg FLIP-USE-REGION-P means temporarily flip the
 value of `bmkp-use-region'."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (unless bookmark (error "No bookmark specified"))
  (run-hooks 'bmkp-before-jump-hook)
  (bookmark-maybe-historicize-string (bmkp-bookmark-name-from-record bookmark))
  (let ((bmkp-use-region  (if flip-use-region-p (not bmkp-use-region) bmkp-use-region)))
    (bookmark--jump-via bookmark display-function)))

(defun bmkp-select-buffer-other-window (buffer)
  "Select BUFFER in another window.
If `bmkp-other-window-pop-to-flag' is non-nil, then use
`pop-to-buffer'.  Otherwise, use `switch-to-buffer-other-window'."
  (if bmkp-other-window-pop-to-flag (pop-to-buffer buffer t) (switch-to-buffer-other-window buffer)))

(defun bmkp-maybe-save-bookmarks (&optional same-count-p)
  "Increment save counter and maybe save `bookmark-alist'.
Non-nil optional arg SAME-COUNT-P means do not increment
`bookmark-alist-modification-count'."
  (unless same-count-p (setq bookmark-alist-modification-count  (1+ bookmark-alist-modification-count)))
  (when (bookmark-time-to-save-p) (bookmark-save)))

;;;###autoload (autoload 'bmkp-annotate-bookmark "bookmark+")
(defun bmkp-annotate-bookmark (bookmark)
  "Annotate BOOKMARK.  Pop up a buffer to add or edit the annotation.
Interactively, this is the same as using command
`bookmark-edit-annotation' with a prefix arg.  You are prompted for
the bookmark name.  Command `bookmark-edit-annotation' can be more
convenient for editing an existing annotation, because you choose
among only the already annotated bookmarks, not all bookmarks.

Non-interactively, BOOKMARK is a bookmark name or a bookmark record."
  (interactive (list (bookmark-completing-read "Annotate bookmark" (bmkp-default-bookmark-name))))
  (pop-to-buffer (generate-new-buffer-name "*Bookmark Annotation Compose*"))
  (bookmark-insert-annotation bookmark)
  (bookmark-edit-annotation-mode)
  (set (make-local-variable 'bookmark-annotation-name) bookmark))

;;;###autoload (autoload 'bmkp-show-this-annotation-read-only "bookmark+")
(defun bmkp-show-this-annotation-read-only ()
  "Switch to `Show Bookmark Annotation' mode for this annotation.
That is, switch from edit mode to read-only mode."
  (interactive)
  (unless (eq major-mode 'bookmark-edit-annotation-mode)
    (error "Buffer is not in `Edit Bookmark Annotation' mode"))
  (if (not (or (not (buffer-modified-p)) (y-or-n-p "Annotation was modified.  Lose changes?")))
      (message "OK, canceled - use `C-c C-c' if you want to save changes")
    (let* ((bmk    (bookmark-get-bookmark bookmark-annotation-name 'NOERROR))
           (bname  (bookmark-name-from-full-record bmk))
           (ann    (and bmk  (bookmark-get-annotation bmk)))
           (obuf   (current-buffer)))
      (unless bname (error "No such bookmark: `%s'" bmk))
      (switch-to-buffer (format "*`%s' Annotation*" bname))
      (let ((buffer-read-only  nil)     ; Because buffer might already exist, in view mode.
            (buf-modified-p    (buffer-modified-p)))
        (delete-region (point-min) (point-max))
        (insert (concat "Annotation for bookmark '" bname "':\n\n"))
        ;; Use `font-lock-ignore' property from library `font-lock+.el', because Org mode
        ;; uses font-lock, which would otherwise wipe out the highlighting added here.
        (add-text-properties (line-beginning-position -1) (line-end-position 1)
                             '(face              bmkp-heading
                               font-lock-ignore  t))
        (insert ann)
        (set-buffer-modified-p buf-modified-p))
      (goto-char (point-min))
      (bookmark-show-annotation-mode)
      (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window))
      (set (make-local-variable 'bookmark-annotation-name) bmk)
      (kill-buffer obuf))))

;;;###autoload (autoload 'bmkp-edit-this-annotation "bookmark+")
(defun bmkp-edit-this-annotation ()
  "Switch to `Edit Bookmark Annotation' mode for this annotation.
That is, switch from read-only mode to edit mode."
  (interactive)
  (unless (eq major-mode 'bookmark-show-annotation-mode)
    (error "Buffer is not in `Show Bookmark Annotation' mode"))
  (let* ((bmk    (bookmark-get-bookmark bookmark-annotation-name 'NOERROR))
         (bname  (bookmark-name-from-full-record bmk))
         (obuf   (current-buffer)))
    (unless bname (error "No such bookmark: `%s'" bmk))
    (switch-to-buffer (generate-new-buffer-name "*Bookmark Annotation Compose*"))
    (let ((buf-modified-p  (buffer-modified-p)))
      (bookmark-insert-annotation bname)
      (set-buffer-modified-p buf-modified-p))
    (bookmark-edit-annotation-mode)
    (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window))
    (set (make-local-variable 'bookmark-annotation-name) bmk)
    (kill-buffer obuf)))

;;;###autoload (autoload 'bmkp-edit-bookmark-name-and-location "bookmark+")
(defun bmkp-edit-bookmark-name-and-location (bookmark &optional edit-record-p)
                                        ; Bound to `C-x p r' (`r' in bookmark list)
  "Edit BOOKMARK's name and location, and maybe save them.
Return a list of the new bookmark name and new location.
BOOKMARK is a bookmark name or a bookmark record.

Without a prefix arg, you are prompted for the new bookmark name and
 the new location name.  When entering the new names you can use
 completion against existing names.  This completion is lax, so you
 can easily edit an existing name.  See `bookmark-set' for particular
 keys available during this input.

With a prefix arg, edit the complete bookmark record (the
 internal, Lisp form)."
  (interactive
   (list (bookmark-completing-read (concat "Edit " (and current-prefix-arg  "internal record for ")
                                           "bookmark")
                                   (bmkp-default-bookmark-name))
         current-prefix-arg))
  (setq bookmark  (bmkp-get-bookmark-in-alist bookmark))
  (if edit-record-p
      (bmkp-edit-bookmark-record bookmark)
    (let* ((bmk-name                                    (bmkp-bookmark-name-from-record bookmark))
           (bmk-location                                (bookmark-prop-get bookmark 'location))
           (bmk-urlp                                    (and bmk-location
                                                             (require 'ffap nil t)
                                                             (ffap-url-p bmk-location)))
           (bmk-filename                                (bookmark-get-filename bmk-name))
           (bmk-buffname                                (or (bmkp-get-buffer-name bookmark)
                                                            (bookmark-prop-get bookmark 'buffer)))
           (new-bmk-name                                (bmkp-completing-read-lax
                                                         "New bookmark name" bmk-name))
           (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
           (new-location
            (cond (bmk-location
                   (cond ((not bmk-urlp) (read-string "New location: "))
                         ((and (featurep 'w3m)  (bmkp-w3m-bookmark-p bmk-name))
                          (w3m-input-url "New URL: " bmk-location))
                         ((and (fboundp 'bmkp-eww-bookmark-p)  (bmkp-eww-bookmark-p bmk-name))
                          (read-string "New URL: "))
                         ((require 'ffap) (ffap-read-file-or-url "New URL: " bmk-location))
                         (t (read-string "New location: "))))
                  (bmk-filename
                   (if (and (featurep 'w3m)
                            (bmkp-w3m-bookmark-p bmk-name))
                       (w3m-input-url "New url: " bmk-filename)
                     (read-file-name
                      "New file name (location): "
                      (and bmk-filename
                           (file-name-directory  bmk-filename))
                      bmk-filename)))
                  (bmk-buffname
                   (read-buffer "New location: " bmk-buffname))
                  (t                    ; No current location.
                   (read-string "New location: "))))
           ;; $$$$$$ Should we change a W3M bookmark that uses `filename' to use `location' instead?
           (changed-bmk-name-p                          (and (not (equal new-bmk-name ""))
                                                             (not (equal new-bmk-name bmk-name))))
           (changed-location-p                          (and bmk-location
                                                             (not (equal new-location ""))
                                                             (not (equal new-location bmk-location))))
           (changed-filename-p                          (and bmk-filename
                                                             (not (equal new-location ""))
                                                             (not (equal new-location bmk-filename))))
           (changed-buffname-p                          (and bmk-buffname
                                                             (not (equal new-location ""))
                                                             (not (equal new-location bmk-buffname))
                                                             (not (and (fboundp 'bmkp-eww-bookmark-p)
                                                                       (bmkp-eww-bookmark-p bookmark))))))
      (when (or changed-bmk-name-p  changed-location-p  changed-filename-p  changed-buffname-p)
        (when changed-bmk-name-p (bookmark-rename bmk-name new-bmk-name 'BATCHP))
        (when changed-location-p (bookmark-prop-set new-bmk-name 'location new-location))
        (when changed-filename-p (bookmark-set-filename new-bmk-name new-location))
        (when changed-buffname-p (bookmark-prop-set new-bmk-name 'buffer-name new-location))
        ;; Change location for Dired too, but not if different from original file name (e.g. a cons).
        (let ((dired-dir  (bookmark-prop-get new-bmk-name 'dired-directory)))
          (when (and dired-dir  (equal dired-dir bmk-filename))
            (bookmark-prop-set new-bmk-name 'dired-directory new-location)))
        (bmkp-maybe-save-bookmarks)     ; Maybe save automatically.
        (when (and bookmark-alist-modification-count ; Did not save automatically.  Ask user.
                   (y-or-n-p "Save changes? "))
          (bookmark-save))
        (list new-bmk-name new-location)))))

(define-derived-mode bmkp-edit-bookmark-records-mode emacs-lisp-mode
    "Edit Bookmark Records"
  "Mode for editing a list of bookmark records, as in `bookmark-alist'.
When you finish editing, use \\<bmkp-edit-bookmark-record-mode-map>\
`\\[bmkp-edit-bookmark-record-send]' in the record-editing buffer."
  :group 'bookmark-plus)

;; This binding must be defined *after* the mode, so `bmkp-edit-bookmark-records-mode-map' is defined.
;; (Alternatively, we could use a `defvar' to define `bmkp-edit-bookmark-records-mode-map' before
;; calling `define-derived-mode'.)
(define-key bmkp-edit-bookmark-records-mode-map "\C-c\C-c" 'bmkp-edit-bookmark-records-send)

(defvar bmkp-edit-bookmark-records-number 0
  "NUmber of bookmard records being edited.")

;;;###autoload (autoload 'bmkp-edit-bookmark-records-send "bookmark+")
(defun bmkp-edit-bookmark-records-send (&optional msg-p) ; Bound to `C-c C-c' in records-editing buffer.
  "Update `bookmark-alist' with buffer contents: a bookmark alist.
Lines beginning with `;;' are ignored.
Non-interactively, optional arg MSG-P means display progress messages.

This assumes that the bookmarks in the buffer are the marked bookmarks
in `*Bookmark List*'.  That is, it assumes that the buffer was created
by `bmkp-bmenu-edit-marked' (`\\<bookmark-bmenu-mode-map>\\[bmkp-bmenu-edit-marked]' in `*Bookmark List*')."
  (interactive "p")
  (unless (eq major-mode 'bmkp-edit-bookmark-records-mode)
    (error "Not in `bmkp-edit-bookmark-records-mode'"))
  (when msg-p (message "Reading edited bookmarks..."))
  (let* ((editbuf             (current-buffer))
         (orig-bmks           (bmkp-marked-bookmarks-only))
         (edited-bookmarks    ())
         (read-error-msg
          (catch 'bmkp-edit-bookmark-records-send
            (setq edited-bookmarks  (condition-case err
                                        (save-excursion (goto-char (point-min))  (read (current-buffer)))
                                      (error (throw 'bmkp-edit-bookmark-records-send
                                               (error-message-string err)))))
            (unless orig-bmks (error "No marked bookmarks now - edits must correspond to currently marked"))
            (cond ((not (listp edited-bookmarks))
                   (throw 'bmkp-edit-bookmark-records-send "Not a list of bookmarks"))
                  ((not (= (length edited-bookmarks) bmkp-edit-bookmark-records-number))
                   (throw 'bmkp-edit-bookmark-records-send
                     (format "Need %d bookmarks, but there seem to be %d"
                             bmkp-edit-bookmark-records-number (length edited-bookmarks)))))
            (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                            bookmark-save-flag))) ; Save only after `dolist' and update.
              (dolist (edited-bmk  edited-bookmarks)
                (unless (and (consp edited-bmk)  (stringp (car edited-bmk))) ; Sanity check.
                  (throw 'bmkp-edit-bookmark-records-send (format "Invalid bookmark: `%s'" edited-bmk)))
                (let ((bname  (bmkp-bookmark-name-from-record edited-bmk))
                      (data   (bmkp-bookmark-data-from-record edited-bmk)))
                  ;; Put the full bookmark on its name as property `bmkp-full-record'.
                  ;; Do this regardless of Emacs version and `bmkp-propertize-bookmark-names-flag'.
                  ;; If it needs to be stripped, that will be done when saving.
                  (put-text-property 0 (length bname) 'bmkp-full-record edited-bmk bname)
                  ;; Update the original bookmark (same cons cell) with what's in the edited version.
                  (setcar (car orig-bmks) bname)
                  (setcdr (car orig-bmks) data)
                  ;; This is the same as `add-to-list' with `EQ' (not available for Emacs 20-21).
                  (unless (memq (car orig-bmks) bmkp-modified-bookmarks)
                    (setq bmkp-modified-bookmarks  (cons (car orig-bmks) bmkp-modified-bookmarks)))
                  (setq orig-bmks  (cdr orig-bmks))))
              ;; Update using modified ORIG-BMKS.
              (setq bmkp-bmenu-marked-bookmarks        (mapcar #'bmkp-bookmark-name-from-record
                                                               bmkp-modified-bookmarks)
                    bmkp-sorted-alist                  (bmkp-sort-omit bookmark-alist)
                    bookmark-alist-modification-count  (1+ bookmark-alist-modification-count)))
            nil)))
    (if (stringp read-error-msg)
        (if msg-p  (message "%s  --> edit and try again" read-error-msg)  (error read-error-msg))
      (when (get-buffer editbuf) (kill-buffer editbuf))
      (bmkp-refresh/rebuild-menu-list
       (and (= 1 (length edited-bookmarks))  (car edited-bookmarks)) ; Only one, so we belong on its line.
       (not msg-p)))))

(define-derived-mode bmkp-edit-bookmark-record-mode emacs-lisp-mode
    "Edit Bookmark Record"
  "Mode for editing an internal bookmark record.
When you finish editing, use \\<bmkp-edit-bookmark-record-mode-map>\
`\\[bmkp-edit-bookmark-record-send]' in the record-editing buffer."
  :group 'bookmark-plus)

;; This binding must be defined *after* the mode, so `bmkp-edit-bookmark-record-mode-map' is defined.
;; (Alternatively, we could use a `defvar' to define `bmkp-edit-bookmark-record-mode-map' before
;; calling `define-derived-mode'.)
(define-key bmkp-edit-bookmark-record-mode-map "\C-c\C-c" 'bmkp-edit-bookmark-record-send)

;;;###autoload (autoload 'bmkp-edit-bookmark-record "bookmark+")
(defun bmkp-edit-bookmark-record (bookmark) ; Bound to `C-x p e'.
  "Edit the full record (the Lisp sexp) for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
When you finish editing, use \\<bmkp-edit-bookmark-record-mode-map>\
`\\[bmkp-edit-bookmark-record-send]' in the record-editing buffer.
The current bookmark list is then updated to reflect your edits."
  (interactive (list (bookmark-completing-read "Edit Lisp record for bookmark"
                                               (bmkp-default-bookmark-name))))
  (bookmark-maybe-load-default-file)
  (setq bmkp-edit-bookmark-orig-record  (bmkp-get-bookmark-in-alist bookmark))
  (let* ((bmk-copy  (copy-sequence bmkp-edit-bookmark-orig-record)) ; Shallow copy
         (bname     (bmkp-bookmark-name-from-record bmk-copy))
         (bufname   (format "*Edit Record for Bookmark `%s'*" bname)))
    (set-text-properties 0 (length bname) nil bname) ; Strip properties from (copied) name string.
    (bookmark-maybe-historicize-string bname)
    (bmkp-with-output-to-plain-temp-buffer bufname
      (princ
       (substitute-command-keys
        (concat ";; Edit the Lisp record for bookmark\n;;\n"
                ";; `" bname "'\n;;\n"
                ";; Type \\<bmkp-edit-bookmark-record-mode-map>\
`\\[bmkp-edit-bookmark-record-send]' when done.\n;;\n")))
      ;; (let ((print-circle  t)) (pp bmk)) ; $$$$$$ Binding should not really be needed now.
      (pp bmk-copy)
      (goto-char (point-min)))
    (pop-to-buffer bufname)
    (buffer-enable-undo)
    (with-current-buffer (get-buffer bufname) (bmkp-edit-bookmark-record-mode))))

;;;###autoload (autoload 'bmkp-edit-bookmark-record-send "bookmark+")
(defun bmkp-edit-bookmark-record-send (&optional msg-p) ; Bound to `C-c C-c' in record-editing buffer.
  "Update `bookmark-alist' with buffer contents: a bookmark record.
Lines beginning with `;;' are ignored.
Non-interactively, optional arg MSG-P means display progress messages."
  (interactive "p")
  (unless (eq major-mode 'bmkp-edit-bookmark-record-mode)
    (error "Not in `bmkp-edit-bookmark-record-mode'"))
  (unless (and (boundp 'bmkp-edit-bookmark-orig-record)  (consp bmkp-edit-bookmark-orig-record))
    (error "Lost original bookmark record - try edit command again"))
  (when msg-p (message "Reading edited bookmark..."))
  (let* ((editbuf     (current-buffer))
         (bmk-name    nil)
         (read-error-msg
          (catch 'bmkp-edit-bookmark-record-send
            (let ((edited-bmk
                   (condition-case err
                       (save-excursion (goto-char (point-min))  (read (current-buffer)))
                     (error (throw 'bmkp-edit-bookmark-record-send (error-message-string err))))))
              (unless (and (consp edited-bmk)  (stringp (car edited-bmk)))
                (throw 'bmkp-edit-bookmark-record-send (format "Invalid bookmark: `%s'" edited-bmk)))
              (let ((bname  (bmkp-bookmark-name-from-record edited-bmk))
                    (data   (bmkp-bookmark-data-from-record edited-bmk)))
                ;; Put the full bookmark on its name as property `bmkp-full-record'.
                ;; Do this regardless of Emacs version and `bmkp-propertize-bookmark-names-flag'.
                ;; If it needs to be stripped, that will be done when saving.
                (put-text-property 0 (length bname) 'bmkp-full-record edited-bmk bname)
                ;; Update the original bookmark with what's in the edited version.
                (setcar bmkp-edit-bookmark-orig-record bname)
                (setcdr bmkp-edit-bookmark-orig-record data)
                ;; This is the same as `add-to-list' with `EQ' (not available for Emacs 20-21).
                (unless (memq bmkp-edit-bookmark-orig-record bmkp-modified-bookmarks)
                  (setq bmkp-modified-bookmarks  (cons bmkp-edit-bookmark-orig-record
                                                       bmkp-modified-bookmarks)))
                (setq bmk-name  bname)) ; Save for bookmark-list display, below.
              (setq bmkp-sorted-alist                  (bmkp-sort-omit bookmark-alist)
                    bookmark-alist-modification-count  (1+ bookmark-alist-modification-count)))
            nil)))
    (if (stringp read-error-msg)
        (if msg-p (message "%s  --> edit and try again" read-error-msg) (error read-error-msg))
      (when (get-buffer editbuf) (kill-buffer editbuf))
      (bmkp-refresh/rebuild-menu-list bmk-name (not msg-p)))
    (unless read-error-msg
      (setq bmkp-edit-bookmark-orig-record  nil)))) ; Reset it, but keep it if error so can try again.

(define-derived-mode bmkp-edit-tags-mode emacs-lisp-mode
    "Edit Bookmark Tags"
  "Mode for editing bookmark tags.
When you have finished composing, type \\[bmkp-edit-tags-send]."
  :group 'bookmark-plus)

;; This binding must be defined *after* the mode, so `bmkp-edit-tags-mode-map' is defined.
;; (Alternatively, we could use a `defvar' to define `bmkp-edit-tags-mode-map' before
;; calling `define-derived-mode'.)
(define-key bmkp-edit-tags-mode-map "\C-c\C-c" 'bmkp-edit-tags-send)

;;;###autoload (autoload 'bmkp-edit-tags "bookmark+")
(defun bmkp-edit-tags (bookmark)        ; Bound to `C-x p t e'
  "Edit BOOKMARK's tags, and maybe save the result.
The edited value must be a list each of whose elements is either a
 string or a cons whose key is a string.
BOOKMARK is a bookmark name or a bookmark record."
  (interactive (list (bookmark-completing-read "Edit tags for bookmark" (bmkp-default-bookmark-name))))
  (setq bookmark  (bmkp-get-bookmark-in-alist bookmark))
  (let* ((btags    (bmkp-get-tags bookmark))
         (bmkname  (bmkp-bookmark-name-from-record bookmark))
         (edbuf    (format "*Edit Tags for Bookmark `%s'*" bmkname)))
    (setq bmkp-return-buffer  (current-buffer))
    (bmkp-with-output-to-plain-temp-buffer edbuf
      (princ
       (substitute-command-keys
        (concat ";; Edit tags for bookmark\n;;\n;; \"" bmkname "\"\n;;\n"
                ";; The edited value must be a list each of whose elements is\n"
                ";; either a string or a cons whose key is a string.\n;;\n"
                ";; DO NOT MODIFY THESE COMMENTS.\n;;\n"
                ";; Type \\<bmkp-edit-tags-mode-map>`\\[bmkp-edit-tags-send]' when done.\n\n")))
      (let ((print-circle  bmkp-propertize-bookmark-names-flag)) (pp btags))
      (goto-char (point-min)))
    (pop-to-buffer edbuf)
    (buffer-enable-undo)
    (with-current-buffer (get-buffer edbuf) (bmkp-edit-tags-mode))))

;;;###autoload (autoload 'bmkp-edit-tags-send "bookmark+")
(defun bmkp-edit-tags-send (&optional batchp)
  "Use buffer contents as the internal form of a bookmark's tags.
DO NOT MODIFY the header comment lines, which begin with `;;'."
  (interactive)
  (unless (eq major-mode 'bmkp-edit-tags-mode) (error "Not in `bmkp-edit-tags-mode'"))
  (let (bname)
    (unwind-protect
         (let (tags bmk)
           (goto-char (point-min))
           (unless (search-forward ";; Edit tags for bookmark\n;;\n;; ")
             (error "Missing header in edit buffer"))
           (unless (stringp (setq bname  (read (current-buffer))))
             (error "Bad bookmark name in edit-buffer header"))
           (unless (setq bmk  (bmkp-get-bookmark-in-alist bname 'NOERROR))
             (error "No such bookmark: `%s'" bname))
           (unless (bmkp-bookmark-type bmk) (error "Invalid bookmark"))
           (goto-char (point-min))
           (setq tags  (read (current-buffer)))
           (unless (listp tags) (error "Tags sexp is not a list of strings or an alist with string keys"))
           (bookmark-prop-set bmk 'tags tags)
           (setq bname  (bmkp-bookmark-name-from-record bmk))
           (bmkp-record-visit bmk batchp)
           (bmkp-refresh/rebuild-menu-list bname batchp)
           (bmkp-maybe-save-bookmarks)
           (unless batchp (message "Updated bookmark file with edited tags")))
      (kill-buffer (current-buffer)))
    (when bmkp-return-buffer
      (pop-to-buffer bmkp-return-buffer)
      (when (equal (buffer-name (current-buffer)) "*Bookmark List*")
        (bmkp-bmenu-goto-bookmark-named bname)))))

(defun bmkp-bookmark-type (bookmark)
  "Return the type of BOOKMARK or nil if no type is recognized.
Return nil if the bookmark record is not recognized (invalid).
See the code for the possible non-nil return values.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (condition-case nil
      (progn
        ;; If BOOKMARK is already a bookmark record, not a bookmark name, then we must use it.
        ;; If we used the name instead, then tests such as `bookmark-get-filename' would fail,
        ;; because they call `bookmark-get-bookmark', which, for a string, checks whether the
        ;; bookmark exists in `bookmark-alist'.  But we want to be able to use `bmkp-bookmark-type'
        ;; to get the type of any bookmark record, not necessarily one that is in `bookmark-alist'.
        (when (stringp bookmark) (setq bookmark  (bookmark-get-bookmark bookmark)))
        (let ((filep  (bookmark-get-filename bookmark)))
          (cond ((bmkp-sequence-bookmark-p bookmark)             'bmkp-sequence-bookmark-p)
                ((bmkp-function-bookmark-p bookmark)             'bmkp-function-bookmark-p)
                ((bmkp-variable-list-bookmark-p bookmark)        'bmkp-variable-list-bookmark-p)
                ((bmkp-url-bookmark-p bookmark)                  'bmkp-url-bookmark-p)
                ((bmkp-gnus-bookmark-p bookmark)                 'bmkp-gnus-bookmark-p)
                ((bmkp-desktop-bookmark-p bookmark)              'bmkp-desktop-bookmark-p)
                ((bmkp-bookmark-file-bookmark-p bookmark)        'bmkp-bookmark-file-bookmark-p)
                ((bmkp-bookmark-list-bookmark-p bookmark)        'bmkp-bookmark-list-bookmark-p)
                ((bmkp-snippet-bookmark-p bookmark)              'bmkp-snippet-bookmark-p)
                ((bmkp-man-bookmark-p bookmark)                  'bmkp-man-bookmark-p)
                ((bmkp-info-bookmark-p bookmark)                 'bmkp-info-bookmark-p)
                ((bookmark-get-handler bookmark)                 'bookmark-get-handler)
                ((bmkp-region-bookmark-p bookmark)               'bmkp-region-bookmark-p)
                ;; Make sure we test for remoteness before any other tests of the file itself
                ;; (e.g. `file-exists-p'). We do not want to prompt for a password etc.
                ((and filep  (bmkp-file-remote-p filep))         'remote-file)
                ((and filep  (file-directory-p filep))           'local-directory)
                (filep                                           'local-file)
                ((and (bmkp-get-buffer-name bookmark)
                      (or (not filep)
                          (equal filep bmkp-non-file-filename)))
                 'buffer)
                (t                                               nil))))
    (error nil)))

(defun bmkp-record-visit (bookmark &optional batchp)
  "Update the data recording a visit to BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
This increments the `visits' entry and sets the `time' entry to the
current time.  If either an entry is not present, it is added (with 0
value for `visits').
With non-nil optional arg BATCHP, do not rebuild the menu list.

Although this function modifies BOOKMARK, it does not increment
`bookmark-alist-modification-count', and it does not add BOOKMARK to
`bmkp-modified-bookmarks'.  This is so that simply recording the visit
does not count toward needing to save or showing BOOKMARK as modified."
  (let ((vis                      (bookmark-prop-get bookmark 'visits))
        (bmkp-modified-bookmarks  bmkp-modified-bookmarks))
    (bookmark-prop-set bookmark 'visits (if vis (1+ vis) 0))
    (bookmark-prop-set bookmark 'time   (current-time))
    (unless batchp (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P))
    (let ((bookmark-save-flag  nil))  (bmkp-maybe-save-bookmarks 'SAME-COUNT-P))))

(defun bmkp-default-bookmark-name (&optional alist)
  "Default bookmark name.  See option `bmkp-default-bookmark-name'.
Non-nil ALIST means return nil unless the default names a bookmark in
ALIST."
  (let ((bname  (if (equal (buffer-name (current-buffer)) "*Bookmark List*")
                    (bookmark-bmenu-bookmark)
                  (if (fboundp 'bmkp-default-lighted)
                      (if (eq 'highlighted bmkp-default-bookmark-name)
                          (or (bmkp-default-lighted) bookmark-current-bookmark)
                        (or bookmark-current-bookmark (bmkp-default-lighted)))
                    bookmark-current-bookmark))))
    (when (consp bname) (setq bname  (car bname))) ; Since `bmkp-default-lighted' can return a list of names.
    (when (and bname  alist)
      (setq bname  (bmkp-bookmark-name-from-record (bmkp-bookmark-record-from-name
                                                    bname 'NOERROR 'MEMP alist))))
    bname))

(defun bmkp-buffer-names ()
  "Buffer names used by existing bookmarks that really have buffers.
This excludes buffers for bookmarks such as desktops that are not
really associated with a buffer."
  (let ((bufs  ())
        buf)
    (dolist (bmk  bookmark-alist)
      (when (and (not (bmkp-desktop-bookmark-p        bmk))
                 (not (bmkp-bookmark-file-bookmark-p  bmk))
                 (not (bmkp-sequence-bookmark-p       bmk))
                 (not (bmkp-function-bookmark-p       bmk))
                 (not (bmkp-variable-list-bookmark-p  bmk))
                 (setq buf  (bmkp-get-buffer-name     bmk)))
        (add-to-list 'bufs buf)))
    bufs))

(defun bmkp-file-names ()
  "The absolute file names used by the existing bookmarks.
This excludes the pseudo file name `bmkp-non-file-filename'."
  (let ((files  ())
        file)
    (dolist (bmk  bookmark-alist)
      (when (and (setq file  (bookmark-get-filename bmk))  (not (equal file bmkp-non-file-filename)))
        (add-to-list 'files file)))
    files))

;;;###autoload (autoload 'bmkp-bookmark-set-confirm-overwrite "bookmark+")
(defun bmkp-bookmark-set-confirm-overwrite (&optional name parg interactivep) ; Bound `C-x r m', `C-x p c m'.
  "Set a bookmark named NAME, then run `bmkp-after-set-hook'.
This is the same as `bookmark-set', except that with no prefix arg you
are asked to confirm overwriting an existing bookmark of the same
NAME."
  (interactive (list nil current-prefix-arg t))
  (let ((bmkp-bookmark-set-confirms-overwrite-p  t))
    (call-interactively #'bookmark-set)))

;;;###autoload (autoload 'bmkp-send-bug-report "bookmark+")
(defun bmkp-send-bug-report ()          ; Not bound
  "Send a bug report about a Bookmark+ problem."
  (interactive)
  (browse-url (format (concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
Bookmark+ bug: \
&body=Describe bug below, using a precise recipe that starts with `emacs -Q' or `emacs -q'.  \
Be sure to mention the `Update #' from header of the particular Bookmark+ file header.\
%%0A%%0AEmacs version: %s")
                      (emacs-version))))

;;;###autoload (autoload 'bmkp-toggle-bookmark-set-refreshes "bookmark+")
(defun bmkp-toggle-bookmark-set-refreshes () ; Not bound
  "Toggle whether `bookmark-set' refreshes `bookmark-alist' as last filtered.
Add/remove `bmkp-refresh-latest-bookmark-list' to/from
`bmkp-after-set-hook'.
\(Applies also to command `bmkp-bookmark-set-confirm-overwrite'.)"
  (interactive)
  (if (member 'bmkp-refresh-latest-bookmark-list bmkp-after-set-hook)
      (remove-hook 'bmkp-after-set-hook 'bmkp-refresh-latest-bookmark-list)
    (add-hook 'bmkp-after-set-hook 'bmkp-refresh-latest-bookmark-list)))

(defun bmkp-refresh-latest-bookmark-list ()
  "Refresh `bmkp-latest-bookmark-alist' to reflect `bookmark-alist'."
  (setq bmkp-latest-bookmark-alist  (if bmkp-bmenu-filter-function
                                        (funcall bmkp-bmenu-filter-function)
                                      bookmark-alist)))

;;;###autoload (autoload 'bmkp-toggle-saving-menu-list-state "bookmark+")
(defun bmkp-toggle-saving-menu-list-state () ; Bound to `C-M-~' in bookmark list
  "Toggle the value of option `bmkp-bmenu-state-file'.
Tip: You can use this before quitting Emacs, to not save the state.
If the initial value of `bmkp-bmenu-state-file' is nil, then this
command has no effect."
  (interactive)
  (unless (or bmkp-last-bmenu-state-file bmkp-bmenu-state-file)
    (error "Cannot toggle: initial value of `bmkp-bmenu-state-file' is nil"))
  (setq bmkp-last-bmenu-state-file  (prog1 bmkp-bmenu-state-file
                                      (setq bmkp-bmenu-state-file  bmkp-last-bmenu-state-file)))
  (message (if bmkp-bmenu-state-file
               "Autosaving of bookmark list state is now ON"
             "Autosaving of bookmark list state is now OFF")))

;;;###autoload (autoload 'bmkp-save-menu-list-state "bookmark+")
(defun bmkp-save-menu-list-state (&optional msg-p) ; Used in `bookmark-exit-hook-internal'.
  "Save menu-list state, unless not saving or list has not yet been shown.
The state is saved to the value of `bmkp-bmenu-state-file'.
Non-interactively, optional arg MSG-P means display progress messages."
  (interactive "p")
  (when (and (not bmkp-bmenu-first-time-p)  bmkp-bmenu-state-file)
    (when msg-p (message "Saving bookmark-list display state..."))
    (let ((config-list
           `((last-sort-comparer                    . ,bmkp-sort-comparer)
             (last-reverse-sort-p                   . ,bmkp-reverse-sort-p)
             (last-reverse-multi-sort-p             . ,bmkp-reverse-multi-sort-p)
             (last-latest-bookmark-alist            . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-latest-bookmark-alist))
             (last-bmenu-omitted-bookmarks          . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-bmenu-omitted-bookmarks 'COPY))
             (last-bmenu-marked-bookmarks           . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-bmenu-marked-bookmarks 'COPY))
             (last-bmenu-filter-function            . ,bmkp-bmenu-filter-function)
             (last-bmenu-filter-pattern             . ,bmkp-bmenu-filter-pattern)
             (last-bmenu-title                      . ,bmkp-bmenu-title)
             (last-bmenu-bookmark                   . ,(and (get-buffer "*Bookmark List*")
                                                            (with-current-buffer
                                                                (get-buffer "*Bookmark List*")
                                                              (bmkp-maybe-unpropertize-string
                                                               (bookmark-bmenu-bookmark) 'COPY))))
             ;; Use `copy-sequence' here just in case, to avoid circular references when
             ;; `bmkp-propertize-bookmark-names-flag' is nil.
             (last-specific-buffer                  . ,(copy-sequence bmkp-last-specific-buffer))
             (last-specific-file                    . ,(copy-sequence bmkp-last-specific-file))
             (last-bmenu-toggle-filenames           . ,bookmark-bmenu-toggle-filenames)
             (last-bmenu-before-hide-marked-alist   . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-bmenu-before-hide-marked-alist 'COPY))
             (last-bmenu-before-hide-unmarked-alist . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-bmenu-before-hide-unmarked-alist 'COPY))
             (last-bookmark-file                    . ,(copy-sequence
                                                        (convert-standard-filename
                                                         (expand-file-name
                                                          bmkp-current-bookmark-file)))))))
      (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect bmkp-bmenu-state-file))
        (goto-char (point-min))
        (delete-region (point-min) (point-max))
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
          (pp config-list (current-buffer))
          (condition-case nil
              (write-file bmkp-bmenu-state-file)
            (file-error
             (setq errorp  t)
             ;; Do NOT raise error - used in `bookmark-exit-hook-internal'.  (Need to be able to exit.)
             (let ((msg  (format "CANNOT WRITE FILE `%s'" bmkp-bmenu-state-file)))
               (if (fboundp 'display-warning)
                   (display-warning 'bookmark-plus msg)
                 (message msg)
                 (sit-for 4)))))
          (kill-buffer (current-buffer))
          (when (and msg-p  (not errorp)) (message "Saving bookmark-list display state...done")))))))

;;;###autoload (autoload 'bmkp-toggle-saving-bookmark-file "bookmark+")
(defun bmkp-toggle-saving-bookmark-file (&optional msg-p) ; Bound to `M-~' in bookmark list
  "Toggle the value of option `bookmark-save-flag'.
If the initial value of `bookmark-save-flag' is nil, then this
command has no effect.
Non-interactively, non-nil MSG-P means display a status message."
  (interactive "p")
  (unless (or bmkp-last-save-flag-value  bookmark-save-flag)
    (error "Cannot toggle: initial value of `bookmark-save-flag' is nil"))
  ;; One of the two vars should be nil.  If both are non-nil, set `*-last-*' to nil before toggling.
  (when (and bmkp-last-save-flag-value  bookmark-save-flag) (setq bmkp-last-save-flag-value  nil))  
  (setq bmkp-last-save-flag-value  (prog1 bookmark-save-flag
                                     (setq bookmark-save-flag  bmkp-last-save-flag-value)))
  (when msg-p (message (if bookmark-save-flag
                           "Autosaving of current bookmark file is now ON"
                         "Autosaving of current bookmark file is now OFF"))))

;; Same as `read-from-whole-string' (called `thingatpt--read-from-whole-string' starting with Emacs 25)
;; in library `thingatpt.el'.
;;
(defun bmkp-read-from-whole-string (string)
  "Read a Lisp expression from STRING.
Raise an error if the entire string was not used."
  (let* ((read-data  (read-from-string string))
         (more-left (condition-case nil
                        ;; The call to `ignore' suppresses a compiler warning.
                        (progn (ignore (read-from-string (substring string (cdr read-data))))
                               t)
                      (end-of-file nil))))
    (if more-left (error "Can't read whole string") (car read-data))))

;;;###autoload (autoload 'bmkp-make-function-bookmark "bookmark+")
(defun bmkp-make-function-bookmark (bookmark-name function &optional msg-p) ; Bound globally to `C-x p c F'.
  "Create a bookmark that invokes FUNCTION when \"jumped\" to.
You are prompted for the bookmark name and the name of the function.
But with a prefix arg the last keyboard macro defined is used instead
of prompting you for a function.

Returns the new bookmark (internal record).

Non-interactively, non-nil optional arg MSG-P means display a status
message."
  (interactive (let ((icicle-unpropertize-completion-result-flag  t))
                 (list (bmkp-completing-read-lax "Bookmark")
                       (if (and current-prefix-arg  last-kbd-macro)
                           (read-kbd-macro last-kbd-macro 'NEED-VECTOR)
                         (completing-read "Function: " obarray 'functionp))
                       'MSG)))
  (unless (or (functionp function)  (vectorp function))
    (setq function (bmkp-read-from-whole-string function))) ; Convert name to symbol.
  (bookmark-store bookmark-name `(,@(bookmark-make-record-default 'NO-FILE 'NO-CONTEXT 0 nil 'NO-REGION)
                                  (function . ,function)
                                  (handler  . bmkp-jump-function))
                  nil nil (not msg-p))
  (let ((new  (bmkp-bookmark-record-from-name bookmark-name 'NOERROR)))
    (unless (memq new bmkp-latest-bookmark-alist)
      (setq bmkp-latest-bookmark-alist  (cons new bmkp-latest-bookmark-alist)))
    (bookmark-bmenu-surreptitiously-rebuild-list (not msg-p))
    new))

;;;###autoload (autoload 'bmkp-set-dired-bookmark-for-files "bookmark+")
(defun bmkp-set-dired-bookmark-for-files (bookmark-name dired-name to-add &optional switches msg-p)
  "Create a Dired bookmark for a set of files and directories.
You are prompted for the Dired buffer name and the file or directory
entries to include.  With a prefix arg, you are also prompted for the
`ls' switches.

Use `C-g' when done choosing file and directory names.  Any directory
names you choose this way are included as single entries in the
listing - the directory contents are not included.  To instead include
the contents of a directory, use a glob pattern: put `/*' after the
directory name.

You need library `Dired+' for this command."
  (interactive
   (let* ((_IGNORE             (unless (require 'dired+ nil t)
                                 (error "You need library `Dired+' for this command")))
          (current-prefix-arg  (if current-prefix-arg 0 -1))
          (all                 (diredp-dired-union-interactive-spec
                                "add files/dirs "
                                'NO-DIRED-BUFS
                                'READ-EXTRA-FILES-P)))
     (list (bmkp-completing-read-lax "Bookmark") (nth 0 all) (nth 3 all) (nth 2 all) 'MSG)))
  (bmkp-make-function-bookmark
   bookmark-name
   `(lambda () (diredp-add-to-dired-buffer ',dired-name ',to-add ',switches))
   msg-p))

;;;###autoload (autoload 'bmkp-revert-bookmark-file "bookmark+")
(defun bmkp-revert-bookmark-file (&optional msg-p) ; Same as `C-u g' in bookmark list (but not bound).
  "Revert to the bookmarks in the current bookmark file.
You are asked for confirmation.

This DISCARDS all modifications to bookmarks and the bookmark list
\(e.g. added/deleted bookmarks) since the last bookmark-file save.
IOW, it reloads the bookmark file, overwriting the current bookmark
list.  This also removes any markings and omissions.

This has the same effect as using `C-u \\<bookmark-bmenu-mode-map>\\[bmkp-bmenu-refresh-menu-list]' in \
buffer `*Bookmark List*'.
To refresh the display from the current bookmark list instead of the
bookmark file, use just `\\[bmkp-bmenu-refresh-menu-list]' (no `C-u').

Non-interactively, non-nil MSG-P means display a status message."
  (interactive "p")
  (when (and msg-p  (not (yes-or-no-p (format "Revert to bookmarks saved in file `%s'? "
                                              bmkp-current-bookmark-file))))
    (error "OK - canceled"))
  (bookmark-load bmkp-current-bookmark-file 'OVERWRITE msg-p) ; Do not let `bookmark-load' ask to save.
  (bmkp-refresh/rebuild-menu-list nil (not msg-p)))

;;;###autoload (autoload 'bmkp-switch-bookmark-file "bookmark+")
(defun bmkp-switch-bookmark-file (file &optional batchp) ; Not bound and not used in the code now.
  "Switch to a different bookmark file, FILE.
Return FILE.  Interactively, you are prompted for FILE.
Replace all bookmarks in the current bookmark list with those from the
newly loaded FILE.  Bookmarks are subsequently saved to FILE.

Optional arg BATCHP is passed to `bookmark-load'."
  (interactive
   (list  (let* ((std-default  (bmkp-default-bookmark-file))
                 (default      (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                                   (if (bmkp-same-file-p bmkp-current-bookmark-file std-default)
                                       bookmark-default-file
                                     std-default)
                                 bmkp-last-bookmark-file)))
            (bmkp-read-bookmark-file-name "Switch to bookmark file: "
                                          (or (file-name-directory default)  "~/")
                                          default
                                          t)))) ; Require that the file exist.
  (bookmark-load file t batchp))        ; Treat it interactively, if this command is called interactively.

;;;###autoload (autoload 'bmkp-switch-to-last-bookmark-file "bookmark+")
(defun bmkp-switch-to-last-bookmark-file (&optional batchp) ; Not bound to any key, by default
  "Switch back to the last-used bookmark file.
Replace all currently existing bookmarks with those newly loaded from
the last-used file.  Swap the values of `bmkp-last-bookmark-file' and
`bmkp-current-bookmark-file'.

Optional arg BATCHP is passed to `bookmark-load'."
  (interactive)
  (bookmark-load (or bmkp-last-bookmark-file  (bmkp-default-bookmark-file))
                 t batchp))             ; Treat it interactively, if this command is called interactively.

;;;###autoload (autoload 'bmkp-switch-bookmark-file-create "bookmark+")
(defun bmkp-switch-bookmark-file-create (file &optional batchp)
                                        ; Bound to `C-x p L', (`L' in bookmark list)
  "Switch to bookmark file FILE, creating it as empty if it does not exist.
Return FILE.  Interactively, you are prompted for FILE.
Replace all bookmarks in the current bookmark list with those from the
newly loaded FILE.  Bookmarks are subsequently saved to FILE.

If there is no file with the name you provide (FILE), then create a
new, empty bookmark file with that name and use that from now on.
This empties the bookmark list.  Interactively, you are required to
confirm this.

Non-nil BATCHP is passed to `bookmark-load'."
  (interactive
   (list (let* ((std-default  (bmkp-default-bookmark-file))
                (default      (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                                  (if (bmkp-same-file-p bmkp-current-bookmark-file std-default)
                                      bookmark-default-file
                                    std-default)
                                bmkp-last-bookmark-file)))
           (bmkp-read-bookmark-file-name "Switch to bookmark file: "
                                         (or (file-name-directory default)  "~/")
                                         default))))
  (let ((empty-p  nil))
    (if (file-readable-p file)
;;;     (if (or batchp  (y-or-n-p (format "CONFIRM: `%s' as the current bookmark file? " file)))
;;;         (bookmark-load file t batchp)
;;;       (error "OK, canceled"))
        (bookmark-load file t batchp)   ; Treat it interactively, if this command is called interactively.
      (setq empty-p  t)
      (when (and (not batchp)
                 (not (y-or-n-p (format "Create and use NEW, EMPTY bookmark file `%s'? " file))))
        (error "OK - canceled"))
      (bmkp-empty-file file)
      (bookmark-load file t batchp))    ; Treat it interactively, if this command is called interactively.
    (unless batchp (message "Bookmark file is now %s`%s'" (if empty-p "EMPTY file " "") file)))
  file)

(defun bmkp-read-bookmark-file-name (&optional prompt dir default-filename require-match)
  "Read and return an (absolute) bookmark file name.
PROMPT is the prompt to use (default: \"Use bookmark file: \").
The other args are the same as for `read-file-name'."
  (let ((insert-default-directory                    t)
        (icicle-unpropertize-completion-result-flag  t)) ; For `read-file-name'.
    (expand-file-name
     (read-file-name (or prompt "Use bookmark file: ") dir default-filename require-match))))

(defun bmkp-read-bookmark-file-default ()
  "A default value for `bmkp-read-bookmark-file-name' DEFAULT-FILENAME arg.
A value to use if you want a default and there is none better."
  (if (and (> emacs-major-version 22)
           (not (bmkp-same-file-p "~/.emacs.bmk" bookmark-default-file)))
      (list "~/.emacs.bmk" bookmark-default-file)
    "~/.emacs.bmk"))

;;;###autoload (autoload 'bmkp-empty-file "bookmark+")
(defun bmkp-empty-file (file &optional confirmp) ; Bound to `C-x p 0'
  "Empty the bookmark file FILE, or create FILE (empty) if it does not exist.
In either case, FILE will become an empty bookmark file.  Return FILE.

NOTE: If FILE already exists and you confirm emptying it, no check is
      made that it is in fact a bookmark file before emptying it.
      It is simply replaced by an empty bookmark file and saved.

This does NOT also make FILE the current bookmark file.  To do that,
use `\\[bmkp-switch-bookmark-file-create]' (`bmkp-switch-bookmark-file-create').

Interactively, and non-interactively if optional arg CONFIRMP is
non-nil, require confirmation if the file already exists."
  (interactive (list (let ((icicle-unpropertize-completion-result-flag  t))
                       (read-file-name "Create empty bookmark file: " "~/"))
                     t))
  (setq file  (expand-file-name file))
  (when (file-directory-p file) (error "`%s' is a directory, not a file" file))
  (bookmark-maybe-load-default-file)
  (when (and confirmp  (file-exists-p file)
             (not (y-or-n-p (format "CONFIRM: Empty the existing file `%s'? " file))))
    (error "OK - canceled"))
  (let ((bookmark-alist  ()))
    (bookmark-write-file file nil (if (file-exists-p file)
                                      "Emptying bookmark file `%s'..."
                                    "Creating new, empty bookmark file `%s'...")))
  file)

;;;###autoload (autoload 'bmkp-crosshairs-highlight "bookmark+")
(defun bmkp-crosshairs-highlight ()     ; Not bound
  "Highlight point with crosshairs temporarily.
Do not highlight if either the region is active or
`bmkp-crosshairs-flag' is nil.

You can add this to hook `bookmark-after-jump-hook'.
You need library `crosshairs.el' to use this command."
  (interactive)
  (when (and bmkp-crosshairs-flag  (> emacs-major-version 21)) ; No-op for Emacs 20-21.
    (unless (condition-case nil (require 'crosshairs nil t) (error nil))
      (error "You need library `crosshairs.el' to use this command"))
    (unless mark-active
      (let ((crosshairs-overlay-priority  (and (boundp 'bmkp-light-priorities)
                                               (1+ (apply #'max
                                                          (mapcar #'cdr bmkp-light-priorities))))))
        (crosshairs-highlight)))))

;;;###autoload (autoload 'bmkp-choose-navlist-from-bookmark-list "bookmark+")
(defun bmkp-choose-navlist-from-bookmark-list (bookmark-name &optional alist) ; Bound to `C-x p B'
  "Choose a bookmark-list bookmark and set the bookmark navigation list.
The navigation-list variable, `bmkp-nav-alist', is set to the list of
bookmarks that would be displayed by `bookmark-bmenu-list' (`C-x r l')
for the chosen bookmark-list bookmark, sorted and filtered as
appropriate.

Instead of choosing a bookmark-list bookmark, you can choose the
pseudo-bookmark `CURRENT *Bookmark List*'.  The bookmarks used for the
navigation list are those that would be currently shown in the
`*Bookmark List*' (even if the list is not currently displayed)."
  (interactive
   (let ((bookmark-alist  (cons (bmkp-current-bookmark-list-state) (bmkp-bookmark-list-alist-only))))
     (list (bmkp-read-bookmark-for-type "bookmark-list" bookmark-alist nil nil
                                        'bmkp-bookmark-list-history "Choose ")
           bookmark-alist)))
  (let ((state  (let ((bookmark-alist  (or alist (cons (bmkp-current-bookmark-list-state)
                                                       (bmkp-bookmark-list-alist-only)))))
                  (bookmark-prop-get bookmark-name 'bookmark-list))))
    (let ((bmkp-sort-comparer               (cdr (assq 'last-sort-comparer              state)))
          (bmkp-reverse-sort-p              (cdr (assq 'last-reverse-sort-p             state)))
          (bmkp-reverse-multi-sort-p        (cdr (assq 'last-reverse-multi-sort-p       state)))
          (bmkp-bmenu-omitted-bookmarks     (cdr (assq 'last-bmenu-omitted-bookmarks    state)))
          (bmkp-bmenu-filter-function       (cdr (assq 'last-bmenu-filter-function      state)))
          (bmkp-bmenu-filter-pattern        (or (cdr (assq 'last-bmenu-filter-pattern   state)) ""))
          (bmkp-bmenu-title                 (cdr (assq 'last-bmenu-title                state)))
          (bookmark-bmenu-toggle-filenames  (cdr (assq 'last-bmenu-toggle-filenames     state))))
      (setq bmkp-nav-alist             (bmkp-sort-omit
                                        (if bmkp-bmenu-filter-function
                                            (funcall bmkp-bmenu-filter-function)
                                          (if (string= "CURRENT *Bookmark List*" bookmark-name)
                                              (or bmkp-latest-bookmark-alist bookmark-alist)
                                            bookmark-alist))
                                        (and (not (eq bmkp-bmenu-filter-function
                                                      'bmkp-omitted-alist-only))
                                             bmkp-bmenu-omitted-bookmarks))
            bmkp-current-nav-bookmark  (car bmkp-nav-alist))))
  (message "Bookmark navigation list is now %s"
           (if (and (string= "CURRENT *Bookmark List*" bookmark-name)  (not (get-buffer "*Bookmark List*")))
               "the global bookmark list"
             (format "`%s'" bookmark-name))))

(defun bmkp-current-bookmark-list-state ()
  "Pseudo-bookmark for the current `*Bookmark List*' state."
  (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P)
  (cons "CURRENT *Bookmark List*" (bmkp-make-bookmark-list-record)))

;;;###autoload (autoload 'bmkp-choose-navlist-of-type "bookmark+")
(defun bmkp-choose-navlist-of-type (type) ; Bound to `C-x p :'
  "Set the bookmark navigation list to the bookmarks of a type you choose.
The pseudo-type `any' sets the navigation list to all bookmarks.
This sets variable `bmkp-nav-alist'."
  (interactive
   (let* ((completion-ignore-case                      t)
          (icicle-unpropertize-completion-result-flag  t)
          (type                                        (completing-read "Type: "
                                                                        (cons '("any" . bookmark-history)
                                                                              bmkp-types-alist)
                                                                        nil t nil nil "any")))
     (list type)))
  (setq bmkp-nav-alist  (if (equal "any" type)
                            bookmark-alist
                          (funcall (intern (format "bmkp-%s-alist-only" type)))))
  (unless bmkp-nav-alist (error "No bookmarks"))
  (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist))
  (message "Bookmark navigation list is now %s"
           (if (equal "any" type) "all bookmarks" (format "for type `%s'" type))))

(defun bmkp-autonamed-bookmark-p (bookmark &optional buffer)
  "Return non-nil if BOOKMARK is an autonamed bookmark for BUFFER.
If BUFFER is nil then any buffer is OK.
BOOKMARK is a bookmark name or a bookmark record.
BUFFER, if non-nil, is a buffer or a buffer name."
  (unless (stringp bookmark) (setq bookmark  (bmkp-bookmark-name-from-record bookmark)))
  (when (bufferp buffer) (setq buffer  (buffer-name buffer)))
  (let ((nargs  0)
        (start  0))
    (save-match-data
      (while (string-match "%\\([+ #-0]+\\)?\\([0-9]+\\)?\\([.][0-9]+\\)?[BsSdoxXefgc]"
                           bmkp-autoname-format
                           start)
        (setq nargs  (1+ nargs)
              start  (match-end 0))))
    (bmkp-string-match-p
     (apply #'format
            (bmkp-format-spec bmkp-autoname-format `((?B . ,(if buffer (regexp-quote buffer) ".*"))))
            (make-list nargs ".*"))
     bookmark)))

(defun bmkp-format-spec (format specification)
  "Like `format-spec', but respect standard `format' %-sequences.
%-sequences specified in SPECIFICATION are handled per `format-spec'
Any standard `format' %-sequences not specified in SPECIFICATION are
left as is.

This is also more general than `format-spec', in that the full format
of a %-sequence is supported: `%<flags><width><precision>character'.
`format-spec' does not support precision>, and it supports only the
flags `-' and `0'."
  (with-temp-buffer
    (insert format)
    (goto-char (point-min))
    (while (search-forward "%" nil t)
      (cond ((eq (char-after) ?%) (delete-char 1)) ; Quoted percent sign.
            ((looking-at "\\([+ #-0]+\\)?\\([0-9]+\\)?\\([.][0-9]+\\)?\\([a-zA-Z]\\)")
             (let* ((num   (match-string 2))
                    (spec  (string-to-char (match-string 4)))
                    (val   (assq spec specification)))
               (if (not val)
                   ;; Ignore standard format chars that are not redefined by SPECIFICATION.
                   (unless (memq (string-to-char (match-string 4)) '(?s ?S ?d ?o ?x ?X ?e ?f ?g ?c))
                     (error "Invalid format character: `%%%c'" spec))
                 (setq val  (cdr val))
                 (let ((text  (format (concat "%" num "s") val))) ; Pad result to desired length.
                   (insert-and-inherit text) ; Insert first, to preserve text properties.
                   (delete-region (+ (match-beginning 0) (length text)) ; Delete specifier body.
                                  (+ (match-end 0) (length text)))
                   (delete-region (1- (match-beginning 0)) ; Delete percent sign.
                                  (match-beginning 0))))))
            (t (error "Invalid format string"))))
    (buffer-string)))

(defun bmkp-autonamed-this-buffer-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an autonamed bookmark for this buffer."
  (unless (stringp bookmark) (setq bookmark  (bmkp-bookmark-name-from-record bookmark)))
  (bmkp-autonamed-bookmark-p bookmark (buffer-name)))

(defun bmkp-autonamed-bookmark-for-buffer-p (bookmark buffer-name)
  "Return non-nil if BOOKMARK is an autonamed bookmark for BUFFER.
BOOKMARK is a bookmark name or a bookmark record.
BUFFER-NAME is a string matching the buffer-name part of an autoname.
This does not check the `buffer-name' entry of BOOKMARK.  It checks
only the buffer indicated by the bookmark name."
  (unless (stringp bookmark) (setq bookmark  (bmkp-bookmark-name-from-record bookmark)))
  (bmkp-autonamed-bookmark-p bookmark buffer-name))

(defun bmkp-update-autonamed-bookmark (bookmark)
  "Update the name and position of the autonamed BOOKMARK at point.
Return the updated BOOKMARK: If input was a bookmark name, then return
 then new name, else the new (full) bookmark.
It is a good idea to set BOOKMARK to the result of this call.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((namep  (stringp bookmark)))
    (setq bookmark  (bookmark-get-bookmark bookmark))
    (bookmark-set-position bookmark (point))
    ;; Autonamed bookmarks do not have regions.  Update `end-position' to be the same as `position'.
    (when (bmkp-get-end-position bookmark)
      (bookmark-prop-set bookmark 'end-position (point)))
    (let ((newname  (funcall bmkp-autoname-bookmark-function (point))))
      (bookmark-rename (bmkp-bookmark-name-from-record bookmark) newname 'BATCHP)
      (bmkp-refresh/rebuild-menu-list (bmkp-bookmark-name-from-record bookmark)) ; So display new name.
      (bmkp-maybe-save-bookmarks))
    (if namep (bmkp-bookmark-name-from-record bookmark) bookmark))) ; Return updated bookmark or name.

;;;###autoload (autoload 'bmkp-this-file/buffer-bmenu-list "bookmark+")
(defun bmkp-this-file/buffer-bmenu-list () ; Bound to `C-x p ,'
  "Show the bookmark list just for bookmarks for the current file/buffer.
If visiting a file, this is `bmkp-this-file-bmenu-list'.  Otherwise,
this is `bmkp-this-buffer-bmenu-list'."
  (interactive)
  (if (buffer-file-name) (bmkp-this-file-bmenu-list) (bmkp-this-buffer-bmenu-list)))

;;;###autoload (autoload 'bmkp-this-file-bmenu-list "bookmark+")
(defun bmkp-this-file-bmenu-list ()
  "Show the bookmark list just for bookmarks for the current file.
Set `bmkp-last-specific-file' to the current file name.
If the current buffer is not visiting a file, prompt for the file name."
  (interactive)
  (unless bookmark-alist (bookmark-maybe-load-default-file)) ; Just to be sure.
  (let ((orig-last-spec-file  bmkp-last-specific-file)
        (orig-filter-fn       bmkp-bmenu-filter-function)
        (orig-title           bmkp-bmenu-title)
        (orig-latest-alist    bmkp-latest-bookmark-alist))
    (condition-case err
        (progn
          (setq bmkp-last-specific-file     (or (buffer-file-name)
                                                (let ((icicle-unpropertize-completion-result-flag  t))
                                                  (read-file-name "File: ")))
                bmkp-bmenu-filter-function  'bmkp-last-specific-file-alist-only
                bmkp-bmenu-title            (format "File `%s' Bookmarks" bmkp-last-specific-file))
          (let ((bookmark-alist         (funcall bmkp-bmenu-filter-function))
                (bmkp-bmenu-state-file  nil)) ; Prevent restoring saved state.
            (unless bookmark-alist (error "No bookmarks for file `%s'" bmkp-last-specific-file))
            (setq bmkp-latest-bookmark-alist  bookmark-alist)
            (pop-to-buffer (get-buffer-create "*Bookmark List*"))
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

;;;###autoload (autoload 'bmkp-this-buffer-bmenu-list "bookmark+")
(defun bmkp-this-buffer-bmenu-list ()
  "Show the bookmark list just for bookmarks for the current buffer.
Set `bmkp-last-specific-buffer' to the current buffer name."
  (interactive)
  (let ((orig-last-spec-buf  bmkp-last-specific-buffer)
        (orig-filter-fn      bmkp-bmenu-filter-function)
        (orig-title          bmkp-bmenu-title)
        (orig-latest-alist   bmkp-latest-bookmark-alist))
    (condition-case err
        (progn
          (setq bmkp-last-specific-buffer   (buffer-name)
                bmkp-bmenu-filter-function  'bmkp-last-specific-buffer-alist-only
                bmkp-bmenu-title            (format "Buffer `%s' Bookmarks"
                                                    bmkp-last-specific-buffer))
          (let ((bookmark-alist         (funcall bmkp-bmenu-filter-function))
                (bmkp-bmenu-state-file  nil)) ; Prevent restoring saved state.
            (unless bookmark-alist (error "No bookmarks for buffer `%s'"
                                          bmkp-last-specific-buffer))
            (setq bmkp-latest-bookmark-alist  bookmark-alist)
            (pop-to-buffer (get-buffer-create "*Bookmark List*"))
            (bookmark-bmenu-list 'filteredp))
          (when (interactive-p)
            (bmkp-msg-about-sort-order (bmkp-current-sort-order)
                                       (format "Only bookmarks for buffer `%s' are shown"
                                               bmkp-last-specific-buffer)))
          (raise-frame))
      (error (progn (setq bmkp-last-specific-buffer   orig-last-spec-buf
                          bmkp-bmenu-filter-function  orig-filter-fn
                          bmkp-bmenu-title            orig-title
                          bmkp-latest-bookmark-alist  orig-latest-alist)
                    (error "%s" (error-message-string err)))))))

;;;###autoload (autoload 'bmkp-navlist-bmenu-list "bookmark+")
(defun bmkp-navlist-bmenu-list ()       ; Bound to `C-x p N'
  "Show the bookmark list just for bookmarks from the navigation list."
  (interactive)
  (unless bmkp-nav-alist
    (bookmark-maybe-load-default-file)
    (setq bmkp-nav-alist  bookmark-alist)
    (unless bmkp-nav-alist (error "No bookmarks"))
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist))
    (message "Bookmark navigation list is now the GLOBAL bookmark list") (sit-for 2))
  (let ((orig-title         bmkp-bmenu-title)
        (orig-latest-alist  bmkp-latest-bookmark-alist))
    (condition-case err
        (progn
          (setq bmkp-bmenu-title  "Current Navlist Bookmarks")
          (let ((bookmark-alist         bmkp-nav-alist)
                (bmkp-bmenu-state-file  nil)) ; Prevent restoring saved state.
            (unless bookmark-alist (error "No bookmarks"))
            (setq bmkp-latest-bookmark-alist  bookmark-alist)
            (pop-to-buffer (get-buffer-create "*Bookmark List*"))
            (bookmark-bmenu-list 'filteredp))
          (when (interactive-p)
            (bmkp-msg-about-sort-order (bmkp-current-sort-order)
                                       "Only bookmarks for the navigation list are shown"))
          (raise-frame))
      (error (progn (setq bmkp-bmenu-title            orig-title
                          bmkp-latest-bookmark-alist  orig-latest-alist)
                    (error "%s" (error-message-string err)))))))

(defun bmkp-completing-read-buffer-name (&optional no-default-p)
  "Read the name of a buffer associated with a bookmark.
The candidates are the buffers in `bmkp-buffer-names'.
Non-nil NO-DEFAULT-P means provide no default value.  Used when
 called in a loop, to let the user exit using empty input.
If NO-DEFAULT-P is nil, then the default is the current buffer's name,
 or the value of `bmkp-last-specific-buffer' if the current buffer has
 no bookmarks."
  (bookmark-maybe-load-default-file)
  (let ((icicle-unpropertize-completion-result-flag  t))
    (completing-read "Buffer: " (mapcar #'list (bmkp-buffer-names)) nil t nil 'buffer-name-history
                     (and (not no-default-p)
                          (if (member (buffer-name) (bmkp-buffer-names))
                              (buffer-name)
                            bmkp-last-specific-buffer)))))

(defun bmkp-completing-read-file-name (&optional no-default-p)
  "Read the name of a file associated with a bookmark.
The candidates are the absolute file names in `bmkp-file-names'.
Non-nil NO-DEFAULT-P means provide no default value.  Used when
 called in a loop, to let the user exit using empty input.
If NO-DEFAULT-P is nil, then the default is the current buffer's file
 name, if any, or the value of `bmkp-last-specific-file' if the
 current buffer has no associated file or the file has no bookmarks."
  (bookmark-maybe-load-default-file)
  (let ((completion-ignore-case                      (if (boundp 'read-file-name-completion-ignore-case)
                                                         read-file-name-completion-ignore-case
                                                       (memq system-type
                                                             '(ms-dos windows-nt darwin cygwin))))
        (icicle-unpropertize-completion-result-flag  t))
    (completing-read "File: " (mapcar #'list (bmkp-file-names)) nil t nil 'file-name-history
                     (and (not no-default-p)
                          (let ((file  (buffer-file-name)))
                            (if (and file  (member file (bmkp-file-names)))
                                file
                              bmkp-last-specific-file))))))

(defun bmkp-refresh/rebuild-menu-list (&optional bookmark no-msg-p)
  "Refresh or rebuild buffer `*Bookmark List*'.
If the buffer is already displayed, call `bmkp-refresh-menu-list'.
Otherwise, call `bookmark-bmenu-surreptitiously-rebuild-list'.
Args are the same as for `bmkp-refresh-menu-list'."
  (let ((bmklistbuf  (get-buffer "*Bookmark List*")))
    (if (and bmklistbuf  (get-buffer-window bmklistbuf 0))
        (with-current-buffer bmklistbuf (bmkp-refresh-menu-list bookmark no-msg-p))
      (bookmark-bmenu-surreptitiously-rebuild-list no-msg-p))))

(defun bmkp-refresh-menu-list (&optional bookmark no-msg-p)
  "Refresh (revert) the bookmark list (\"menu list\").
This brings the displayed list up to date.  It does not change the
current filtering or sorting of the displayed list.
Non-nil optional arg BOOKMARK means move cursor to BOOKMARK's line.
BOOKMARK is a bookmark name or a bookmark record.
Non-nil optional arg NO-MSG-P means do not show progress messages."
  (let ((bookmark-alist  (if bmkp-bmenu-filter-function
                             (funcall bmkp-bmenu-filter-function)
                           bookmark-alist)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (unless no-msg-p  (message "Updating bookmark list..."))
    (bookmark-bmenu-list bmkp-bmenu-filter-function) ; No filter function means start anew.
    (when bookmark
      (unless (stringp bookmark) (setq bookmark  (bmkp-bookmark-name-from-record bookmark)))
      (with-current-buffer (get-buffer "*Bookmark List*")
        (bmkp-bmenu-goto-bookmark-named bookmark)
        (let ((bmenu-win  (get-buffer-window (current-buffer) 0)))
          (when bmenu-win (set-window-point bmenu-win (point))))))
    (unless no-msg-p  (message "Updating bookmark list...done"))))

;;;###autoload (autoload 'bmkp-unomit-all "bookmark+")
(defun bmkp-unomit-all (&optional msg-p) ; Bound to `O U' in bookmark list
  "Remove all bookmarks from the list of omitted bookmarks.
After this, all bookmarks are available for display.
Non-interactively, non-nil optional arg MSG-P means display a status
message."
  (interactive "p")
  (unless bmkp-bmenu-omitted-bookmarks (error "No omitted bookmarks to UN-omit"))
  (when msg-p (message "UN-omitting ALL omitted bookmarks..."))
  (let ((count  0))
    (dolist (bmk-name  bmkp-bmenu-omitted-bookmarks)
      (setq bmkp-bmenu-omitted-bookmarks  (bmkp-delete-bookmark-name-from-list
                                           bmk-name bmkp-bmenu-omitted-bookmarks)
            count                         (1+ count)))
    (bookmark-bmenu-surreptitiously-rebuild-list (not msg-p))
    (when msg-p (message "UN-omitted %d bookmarks" count)))
  (when (equal (buffer-name (current-buffer)) "*Bookmark List*") (bmkp-bmenu-show-all))
  (when (and (fboundp 'fit-frame-if-one-window)  (equal (buffer-name (current-buffer)) "*Bookmark List*"))
    (fit-frame-if-one-window)))

(defun bmkp-omitted-alist-only ()
  "`bookmark-alist', filtered to retain only the omitted bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-omitted-bookmark-p bookmark-alist))

(defun bmkp-omitted-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an omitted bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (unless (stringp bookmark) (setq bookmark  (bmkp-bookmark-name-from-record bookmark)))
  (bmkp-bookmark-name-member bookmark bmkp-bmenu-omitted-bookmarks))


;;(@* "Search-and-Replace Locations of Marked Bookmarks")
;;  *** Search-and-Replace Locations of Marked Bookmarks ***

(when (> emacs-major-version 22)
  (defvar bmkp-isearch-bookmarks nil
    "Bookmarks whose locations are to be incrementally searched.")

  (defun bmkp-isearch-next-bookmark-buffer (&optional bookmark wrap)
    "Return the next buffer in a series of bookmark buffers.
Used as a value for `multi-isearch-next-buffer-function', for Isearch
of multiple bookmarks.

Variable `bmkp-isearch-bookmarks' is a list of bookmarks.  Each
bookmark in the list is visited by `bookmark--jump-via', and the
corresponding bookmark buffer is returned."
    (let ((bookmarks  (if isearch-forward bmkp-isearch-bookmarks (reverse bmkp-isearch-bookmarks))))
      (bookmark--jump-via
       (if wrap
           (car bookmarks)
         (let ((this-bmk  (catch 'bmkp-isearch-next-bookmark-buffer
                            (dolist (bmk  bookmarks)
                              (when (if (bmkp-get-buffer-name bmk)
                                        (equal (bmkp-get-buffer-name bmk) (buffer-name))
                                      (equal (bookmark-get-filename bmk) (buffer-file-name)))
                                (throw 'bmkp-isearch-next-bookmark-buffer bmk)))
                            (car bookmarks))))
           (cadr (member this-bmk bookmarks))))
       'ignore)
      (current-buffer)))

  (defun bmkp-isearch-bookmarks (bookmarks)
    "Start multi-bookmark Isearch on BOOKMARKS."
    (let ((multi-isearch-next-buffer-function  'bmkp-isearch-next-bookmark-buffer)
          (bmkp-isearch-bookmarks              bookmarks))
      (bookmark-jump (car bookmarks))
      (goto-char (if isearch-forward (point-min) (point-max)))
      (isearch-forward)))

  (defun bmkp-isearch-bookmarks-regexp (bookmarks)
    "Start multi-bookmark regexp Isearch on BOOKMARKS."
    (let ((multi-isearch-next-buffer-function  'bmkp-isearch-next-bookmark-buffer)
          (bmkp-isearch-bookmarks              bookmarks))
      (bookmark-jump (car bookmarks))
      (goto-char (if isearch-forward (point-min) (point-max)))
      (isearch-forward-regexp))))


;;(@* "Tags")
;;  *** Tags ***

(defun bmkp-get-tags (bookmark)
  "Return the `tags' entry for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'tags))

(defalias 'bmkp-tagged-bookmark-p 'bmkp-get-tags)

(defun bmkp-get-tag-value (bookmark tag)
  "Return value of BOOKMARK's tag TAG.
BOOKMARK is a bookmark name or a bookmark record.
TAG is a string.
Return nil if BOOKMARK has no such TAG or if TAG has no value."
  (assoc-default tag (bmkp-get-tags bookmark)))

(defun bmkp-has-tag-p (bookmark tag)
  "Return non-nil if BOOKMARK is tagged with TAG.
BOOKMARK is a bookmark name or a bookmark record.
TAG is a string."
  (assoc-default tag (bmkp-get-tags bookmark) nil t))

;; NOT USED currently - we use `bmkp-read-tags-completing' instead.
(defun bmkp-read-tags ()
  "Read tags one by one, and return them as a list."
  (let ((tag    (read-string "Tag (RET for each, empty input to finish): "))
        (btags  ()))
    (while (not (string= "" tag))
      (push tag btags)
      (setq tag  (read-string "Tag: ")))
    btags))

(defun bmkp-read-tag-completing (&optional prompt candidate-tags require-match update-tags-alist-p)
  "Read a tag with completion, and return it as a string.
The candidate tags available are determined by option
`bmkp-tags-for-completion'.

PROMPT is the prompt string.  If nil, then use \"Tag: \".
CANDIDATE-TAGS is an alist of tags to use for completion.
 If nil, then all tags from all bookmarks are used for completion.
 The set of all tags is taken from variable `bmkp-tags-alist'.
REQUIRE-MATCH is passed to `completing-read'.
Non-nil UPDATE-TAGS-ALIST-P means update var `bmkp-tags-alist'."
  (bookmark-maybe-load-default-file)
  (let ((cand-tags                                   (copy-sequence
                                                      (or candidate-tags
                                                          (and (not update-tags-alist-p)
                                                               bmkp-tags-alist) ; Use cached list.
                                                          (bmkp-tags-list)))) ; Update the cache.
        (icicle-unpropertize-completion-result-flag  t))
    (completing-read (or prompt "Tag: ") cand-tags nil require-match nil 'bmkp-tag-history)))

(defun bmkp-read-tags-completing (&optional candidate-tags require-match update-tags-alist-p)
  "Read tags with completion, and return them as a list of strings.
Read tags one by one, until you hit `RET' twice consecutively.

CANDIDATE-TAGS is an alist of tags to use for completion.
 If nil then the candidate tags are taken from variable
 `bmkp-tags-alist'.
REQUIRE-MATCH is passed to `completing-read'.
Non-nil UPDATE-TAGS-ALIST-P means update var `bmkp-tags-alist',
determining the tags to use per option `bmkp-tags-for-completion'."
  (bookmark-maybe-load-default-file)
  (let ((cands                                       ())
        (btags                                       ())
        (prompt1                                     "Tag (RET for each, empty input to finish): ")
        (prompt2                                     "Tag: ")
        (icicle-unpropertize-completion-result-flag  t)
        tag old-tag)
    ;; Make a new candidates alist, with just one entry per tag name.  The original cdr is discarded.
    (dolist (full-tag  (or candidate-tags
                           (and (not update-tags-alist-p)  bmkp-tags-alist) ; Use cached list.
                           (bmkp-tags-list)))
      (add-to-list 'cands (list (if (consp full-tag) (car full-tag) full-tag))))
    (setq tag    (completing-read prompt1 cands nil require-match nil 'bmkp-tag-history)
          cands  (delete (assoc tag cands) cands)) ; Tag read is no longer a candidate.
    (while (not (string= "" tag))
      (if (member tag btags)            ; User can enter it more than once, if not REQUIRE-MATCH.
          (message "Tag `%s' already included" tag)
        (push tag btags))               ; But we only add it once.
      (setq tag    (completing-read prompt2 cands nil require-match nil 'bmkp-tag-history)
            cands  (delete (assoc tag cands) cands)))
    (nreverse btags)))

;;;###autoload (autoload 'bmkp-list-all-tags "bookmark+")
(defun bmkp-list-all-tags (fullp current-only-p &optional msg-p)
                                        ; Bound to `C-x p t l', (`T l' in bookmark list)
  "List bookmark tags.
Show the list in the minibuffer or, if not enough space, in buffer
`*All Tags*'.  The tags are listed alphabetically, respecting option
`case-fold-search'.

With no prefix arg or with a plain prefix arg (`C-u'), the tags listed
are those defined by option `bmkp-tags-for-completion'.  Otherwise
\(i.e., with a numeric prefix arg), the tags listed are those from the
current list of bookmarks only.

With no prefix arg or with a negative prefix arg (e.g. `C--'), list
only the tag names.  With a non-negative prefix arg (e.g. `C-1' or
plain `C-u'), list the full alist of tags.

Note that when the full tags alist is shown, the same tag name appears
once for each of its different values.

Non-interactively, non-nil MSG-P means display a status message."
  (interactive (list (and current-prefix-arg  (> (prefix-numeric-value current-prefix-arg) 0))
                     (and current-prefix-arg  (not (consp current-prefix-arg)))
                     'MSG))
  (require 'pp)
  (when msg-p (message "Gathering tags..."))
  (pp-display-expression  (sort (bmkp-tags-list (not fullp) current-only-p)
                                (if fullp
                                    (lambda (t1 t2) (bmkp-string-less-case-fold-p (car t1) (car t2)))
                                  'bmkp-string-less-case-fold-p))
                          "*All Tags*"))

(defun bmkp-tags-list (&optional names-only-p current-only-p)
  "List of all bookmark tags, per option `bmkp-tags-for-completion'.
Non-nil NAMES-ONLY-P means return a list of only the tag names.
Otherwise, return an alist of the full tags and set variable
`bmkp-tags-alist' to that alist, as a cache.

Non-nil CURRENT-ONLY-P means ignore option `bmkp-tags-for-completion'
and return only the tags for the currently loaded bookmarks."
  (let ((tags      ())
        (opt-tags  bmkp-tags-for-completion)
        bmk-tags)
    (when (or (eq opt-tags 'current)  current-only-p)  (setq opt-tags '(current)))
    (dolist (entry  opt-tags)
      (typecase entry
        (cons                           ; A bookmark file
         (when (eq 'bmkfile (car entry))
           (setq entry  (cdr entry)
                 tags   (append tags (bmkp-tags-in-bookmark-file entry names-only-p)))))
        (string (add-to-list 'tags (if names-only-p entry (list entry))))
        (symbol (when (eq entry 'current)
                  (bookmark-maybe-load-default-file)
                  (dolist (bmk  bookmark-alist)
                    (setq bmk-tags  (bmkp-get-tags bmk))
                    (dolist (tag  bmk-tags)
                      (add-to-list 'tags (if names-only-p (bmkp-tag-name tag) (bmkp-full-tag tag)))))))))
    (unless names-only-p (setq bmkp-tags-alist  tags))
    tags))

(defun bmkp-tags-in-bookmark-file (file &optional names-only-p)
  "Return the list of tags from all bookmarks in bookmark-file FILE.
If FILE is a relative file name, it is expanded in `default-directory.
If FILE does not name a valid, bookmark file then nil is returned.
Non-nil NAMES-ONLY-P means return a list of only the tag names.
Otherwise, return an alist of the full tags."
  (setq file  (expand-file-name file))
  (when (file-directory-p file) (error "`%s' is a directory, not a file" file))
  (let ((bookmark-save-flag  nil)       ; Just to play safe.
        (bmk-alist           ())
        (tags                ())
        bmk-tags)
    (if (not (file-readable-p file))
        (message "Cannot read bookmark file `%s'" file)
      (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect file))
        (goto-char (point-min))
        (condition-case nil             ; Check whether it's a valid bookmark file.
            (progn (bookmark-maybe-upgrade-file-format)
                   (unless (listp (setq bmk-alist  (bookmark-alist-from-buffer))) (error "")))
          (error (message "Not a valid bookmark file: `%s'" file))))
      (dolist (bmk  bmk-alist)
        (setq bmk-tags  (bmkp-get-tags bmk))
        (dolist (tag  bmk-tags)
          (add-to-list 'tags (if names-only-p (bmkp-tag-name tag) (bmkp-full-tag tag))))))
    tags))

(defun bmkp-tag-name (tag)
  "Name of TAG.  If TAG is an atom, then TAG, else (car TAG)."
  (if (atom tag) tag (car tag)))

(defun bmkp-full-tag (tag)
  "Full cons entry for TAG.  If TAG is a cons, then TAG, else (list TAG)."
  (if (consp tag) tag (list tag)))

;;;###autoload (autoload 'bmkp-remove-all-tags "bookmark+")
(defun bmkp-remove-all-tags (bookmark &optional no-update-p msg-p)
                                        ; Bound to `C-x p t 0', (`T 0' in bookmark list)
  "Remove all tags from BOOKMARK.
Non-interactively:
 - Non-nil NO-UPDATE-P means do not update `bmkp-tags-alist', do not
   update the modification count and maybe save bookmarks, and do not
   refresh/rebuild the bookmark-list display
 - Non-nil optional arg MSG-P means show a message about the removal."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) nil 'MSG))
  (when (and msg-p  (null (bmkp-get-tags bookmark)))  (error "Bookmark has no tags to remove"))
  (let ((nb-removed  (and (interactive-p)  (length (bmkp-get-tags bookmark)))))
    (bookmark-prop-set bookmark 'tags ())
    (unless no-update-p
      (bmkp-tags-list)                  ; Update the tags cache.
      (bmkp-maybe-save-bookmarks)       ; Increments `bookmark-alist-modification-count'.
      (bmkp-refresh/rebuild-menu-list bookmark (not msg-p))) ; So remove `t' marker and add `*' marker.
    (when (and msg-p  nb-removed)  (message "%d tags removed" nb-removed)))) ; Do after msg from refreshing.


;;;###autoload (autoload 'bmkp-add-tags "bookmark+")
(defun bmkp-add-tags (bookmark tags &optional no-update-p msg-p)
                                        ; `C-x p t + b' (`b' for bookmark), (`T +' in bookmark list)
  "Add TAGS to BOOKMARK.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
Completion for the bookmark name is strict.
Completion for tags is lax: you are not limited to existing tags.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them.

Non-interactively:
 - TAGS is a list of strings.
 - Non-nil MSG-P means display a message about the addition.
 - Non-nil NO-UPDATE-P means do not update `bmkp-tags-alist', do not
   update the modification count and maybe save bookmarks, and do not
   refresh/rebuild the bookmark-list display

The absolute value of the return value is the number of tags added.
If BOOKMARK was untagged before the operation, then the return value
is negative."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name))
                     (bmkp-read-tags-completing nil nil current-prefix-arg)
                     nil
                     'MSG))
  (let* ((newtags  (copy-alist (bmkp-get-tags bookmark)))
         (olen     (length newtags)))
    (dolist (tag  tags)  (unless (or (assoc tag newtags) (member tag newtags))  (push tag newtags)))
    (bookmark-prop-set bookmark 'tags newtags)
    (unless no-update-p
      (bmkp-tags-list) ; Update the tags cache.
      (bmkp-maybe-save-bookmarks)  ; Increments `bookmark-alist-modification-count'.
      (bmkp-refresh/rebuild-menu-list bookmark (not msg-p))) ; So display `t' and `*' markers for BOOKMARK.
    (let ((nb-added  (- (length newtags) olen)))
      (when msg-p (message "%d tags added. Now: %S" nb-added ; Echo just the tag names.
                           (let ((tgs  (mapcar #'bmkp-tag-name newtags))) (setq tgs (sort tgs #'string<)))))
      (when (and (zerop olen)  (> (length newtags) 0)) (setq nb-added  (- nb-added)))
      nb-added)))

;; $$$$$$ Not yet used
;;;###autoload (autoload 'bmkp-set-tag-value-for-navlist "bookmark+")
(defun bmkp-set-tag-value-for-navlist (tag value &optional msg-p) ; Bound to `C-x p t V'
  "Set the value of TAG to VALUE, for each bookmark in the navlist.
If any of the bookmarks has no tag named TAG, then add one with VALUE."
  (interactive (list (bmkp-read-tag-completing) (read (read-string "Value: ")) 'msg))
  (bmkp-set-tag-value-for-bookmarks bmkp-nav-alist tag value msg-p))

;; $$$$$$ Not yet used
(defun bmkp-set-tag-value-for-bookmarks (bookmarks tag value &optional msg-p) ; Not bound
  "Set the value of TAG to VALUE, for each of the BOOKMARKS.
If any of the BOOKMARKS has no tag named TAG, then add one with VALUE."
  (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                  bookmark-save-flag))) ; Save only after `dolist'.
    (dolist (bmk  bookmarks) (bmkp-set-tag-value bmk tag value 'NO-UPDATE-P)))
  (bmkp-tags-list)                      ; Update the tags cache.
  (bmkp-maybe-save-bookmarks)           ; Increments `bookmark-alist-modification-count'.
  (bmkp-refresh/rebuild-menu-list nil (not msg-p)))

;;;###autoload (autoload 'bmkp-set-tag-value "bookmark+")
(defun bmkp-set-tag-value (bookmark tag value &optional no-update-p msg-p) ; Bound to `C-x p t v'
  "For BOOKMARK's TAG, set the value to VALUE.
If BOOKMARK has no tag named TAG, then add one with value VALUE.
Non-interactively:
 - Non-nil NO-UPDATE-P means do not update `bmkp-tags-alist', do not
   update the modification count and maybe save bookmarks, and do not
   refresh/rebuild the bookmark-list display
 - Non-nil MSG-P means display a message about the updated value."
  (interactive
   (let* ((bmk  (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)))
          (tag  (bmkp-read-tag-completing "Tag: " (mapcar 'bmkp-full-tag (bmkp-get-tags bmk)))))
     (list bmk tag (read (read-string "Value: ")) nil 'MSG)))
  (unless (bmkp-has-tag-p bookmark tag) (bmkp-add-tags bookmark (list tag) 'NO-UPDATE-P)) ; No update yet.
  (let* ((newtags     (copy-alist (bmkp-get-tags bookmark)))
         (assoc-tag   (assoc tag newtags))
         (member-tag  (and (not assoc-tag)  (member tag newtags))))
    (if assoc-tag (setcdr assoc-tag value) (setcar member-tag (cons (car member-tag) value)))
    (bookmark-prop-set bookmark 'tags newtags))
  (unless no-update-p
    (bmkp-tags-list)                    ; Update the tags cache.
    (bmkp-maybe-save-bookmarks)         ; Increments `bookmark-alist-modification-count'.
    (bmkp-refresh/rebuild-menu-list bookmark (not msg-p))) ; So display `t' and `*' markers for BOOKMARK.
  (when msg-p "Tag value set"))

;;;###autoload (autoload 'bmkp-remove-tags "bookmark+")
(defun bmkp-remove-tags (bookmark tags &optional no-update-p msg-p)
                                        ; `C-x p t - b' (`b' for bookmark), (`T -' in bookmark list)
  "Remove TAGS from BOOKMARK.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them.

Non-interactively:
 - TAGS is a list of strings.  The corresponding tags are removed.
 - Non-nil MSG-P means display status messages.
 - Non-nil NO-UPDATE-P means do not update `bmkp-tags-alist', do not
   update the modification count and maybe save bookmarks, and do not
   refresh/rebuild the bookmark-list display

The absolute value of the return value is the number of tags removed.
If BOOKMARK is untagged after the operation, then the return value
is negative."
  (interactive (let ((bmk  (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name))))
                 (list bmk
                       (bmkp-read-tags-completing (mapcar 'bmkp-full-tag (bmkp-get-tags bmk))
                                                  t current-prefix-arg)
                       nil
                       'MSG)))
  (let* ((remtags  (copy-alist (bmkp-get-tags bookmark)))
         (olen     (length remtags)))
    (if (null remtags)
        (when msg-p (message "Bookmark has no tags to remove")) ; Do nothing if bookmark has no tags.
      (setq remtags  (bmkp-remove-if (lexical-let ((tgs  tags))
                                       (lambda (tag)
                                         (if (atom tag) (member tag tgs) (member (car tag) tgs))))
                                     remtags))
      (bookmark-prop-set bookmark 'tags remtags)
      (unless no-update-p
        (bmkp-tags-list)                ; Update the tags cache.
        (bmkp-maybe-save-bookmarks)     ; Increments `bookmark-alist-modification-count'.
        (bmkp-refresh/rebuild-menu-list bookmark (not msg-p))) ; So remove `t' marker if no tags.
      (let ((nb-removed  (- olen (length remtags))))
        (when msg-p (message "%d tags removed. Now: %S" nb-removed ; Echo just the tag names.
                             (let ((tgs  (mapcar #'bmkp-tag-name remtags)))
                               (setq tgs (sort tgs #'string<)))))
        (when (and (zerop (length remtags))  (> olen 0)) (setq nb-removed  (- nb-removed)))
        nb-removed))))

;;;###autoload (autoload 'bmkp-remove-tags-from-all "bookmark+")
(defun bmkp-remove-tags-from-all (tags &optional msg-p) ; Bound to `C-x p t d', (`T d' in bookmark list)
  "Remove TAGS from all bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag.
This affects all bookmarks, even those not showing in bookmark list.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them.

Non-interactively:
* TAGS is a list of strings.  The corresponding tags are removed.
* Non-nil optional arg MSG-P means show a message about the deletion."
  (interactive
   (if (not (y-or-n-p "Delete the tags you specify from ALL bookmarks? "))
       (error "OK - deletion canceled")
     (list (bmkp-read-tags-completing nil t current-prefix-arg) 'MSG)))
  (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                  bookmark-save-flag))) ; Save only after `dolist'.
    (dolist (bmk  (bookmark-all-names)) (bmkp-remove-tags bmk tags 'NO-UPDATE-P)))
  (bmkp-tags-list)                      ; Update the tags cache (only once, at end).
  (bmkp-maybe-save-bookmarks)           ; Increments `bookmark-alist-modification-count'.
  (bmkp-refresh/rebuild-menu-list nil (not msg-p)) ; So remove `t' markers when no tags anymore.
  (when msg-p (message "Tags removed from all bookmarks: %S" tags)))

;;;###autoload (autoload 'bmkp-rename-tag "bookmark+")
(defun bmkp-rename-tag (tag newname &optional msg-p) ; Bound to `C-x p t r', (`T r' in bookmark list)
  "Rename TAG to NEWNAME in all bookmarks, even those not showing.
Non-interactively, non-nil MSG-P means display a message about the
deletion."
  (interactive (list (bmkp-read-tag-completing "Tag (old name): ")
                     (bmkp-read-tag-completing "New name: ")
                     'MSG))
  (let ((tag-exists-p        nil)
        (bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                  bookmark-save-flag))) ; Save only after `dolist'.
    (dolist (bmk  (bookmark-all-names))
      (let ((newtags  (copy-alist (bmkp-get-tags bmk))))
        (when newtags
          (let* ((assoc-tag   (assoc tag newtags))
                 (member-tag  (and (not assoc-tag)  (member tag newtags))))
            (cond (assoc-tag  (setcar assoc-tag newname))
                  (member-tag (setcar member-tag newname)))
            (when (or assoc-tag member-tag)
              (setq tag-exists-p  t)
              (bookmark-prop-set bmk 'tags newtags))))))
    (unless tag-exists-p (error "No such tag: `%s'" tag)))
  (bmkp-tags-list)                      ; Update the tags cache now, after iterating.
  (bmkp-maybe-save-bookmarks)           ; Increments `bookmark-alist-modification-count'.
  ;; (bmkp-refresh/rebuild-menu-list nil (not msg-p)) ; $$$$$$ No need to redisplay
  (when msg-p (message "Renamed")))

;;;###autoload (autoload 'bmkp-copy-tags "bookmark+")
(defun bmkp-copy-tags (bookmark &optional msg-p) ; Bound to `C-x p t c', `C-x p t M-w'
  "Copy tags from BOOKMARK, so you can paste them to another bookmark.
Note that you can copy from a BOOKMARK that has no tags or has an
empty tags list.  In that case, the copied-tags list is empty, so if
you paste it as a replacement then the recipient bookmark will end up
with no tags.

Non-interactively, non-nil MSG-P means display a message about the
number of tags copied."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) 'MSG))
  (let ((btags  (bmkp-get-tags bookmark)))
    (setq bmkp-copied-tags  (copy-alist btags))
    (when msg-p (message "%d tags now available for pasting" (length btags)))))

;;;###autoload (autoload 'bmkp-paste-add-tags "bookmark+")
(defun bmkp-paste-add-tags (bookmark &optional no-update-p msg-p) ; Bound to `C-x p t p', `C-x p t C-y'
  "Add tags to BOOKMARK that were previously copied from another bookmark.
Return the number of tags added.
The tags are copied from `bmkp-copied-tags'.
Non-interactively:
 - Non-nil NO-UPDATE-P means do not update `bmkp-tags-alist', do not
   update the modification count and maybe save bookmarks, and do not
   refresh/rebuild the bookmark-list display
 - Non-nil MSG-P means display a message about the addition."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) nil 'MSG))
  (unless (listp bmkp-copied-tags) (error "`bmkp-paste-add-tags': `bmkp-copied-tags' is not a list"))
  (bmkp-add-tags bookmark bmkp-copied-tags no-update-p msg-p))

;;;###autoload (autoload 'bmkp-paste-replace-tags "bookmark+")
(defun bmkp-paste-replace-tags (bookmark &optional no-update-p msg-p) ; Bound to `C-x p t q'
  "Replace tags for BOOKMARK with those copied from another bookmark.
Return the number of tags for BOOKMARK.
The tags are copied from `bmkp-copied-tags'.
Any previously existing tags for BOOKMARK are *lost*.

NOTE: It is by design that you can *remove all* tags from a bookmark
by copying an empty set of tags and then pasting to that bookmark
using this command.  So be careful using it.  If you want to be sure
that you do not replace tags with an empty list of tags, you can check
the value of variable `bmkp-copied-tags' before pasting.

Non-interactively:
 - Non-nil NO-UPDATE-P means do not update `bmkp-tags-alist', do not
   update the modification count and maybe save bookmarks, and do not
   refresh/rebuild the bookmark-list display
 - Non-nil MSG-P means display a message about the addition."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) nil 'MSG))
  (unless (listp bmkp-copied-tags)
    (error "`bmkp-paste-replace-tags': `bmkp-copied-tags' is not a list"))
  (let ((has-tags-p  (bmkp-get-tags bookmark)))
    (when (and msg-p  has-tags-p
               (not (y-or-n-p "Existing tags will be LOST - really replace them? ")))
      (error "OK - paste-replace tags canceled"))
    (when has-tags-p (bmkp-remove-all-tags bookmark no-update-p msg-p) (sleep-for 0.5)))
  (bmkp-add-tags bookmark bmkp-copied-tags no-update-p msg-p))


;;(@* "Bookmark Predicates")
;;  *** Bookmark Predicates ***

(defun bmkp-annotated-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK has an annotation.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (let ((annotation  (bookmark-get-annotation bookmark)))
    (and annotation  (not (string-equal annotation "")))))

(defun bmkp-autofile-bookmark-p (bookmark &optional prefix)
  "Return non-nil if BOOKMARK is an autofile bookmark.
That means that it is `bmkp-file-bookmark-p' and also its
non-directory file name is the same as the bookmark name.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'.

Non-interactively, non-nil optional arg PREFIX means that the bookmark
name is actually expected to be the file name prefixed by PREFIX (a
string)."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (and (bmkp-file-bookmark-p bookmark)
       (let ((fname  (file-name-nondirectory (bookmark-get-filename bookmark))))
         (string= (if prefix (concat prefix fname) fname) (bmkp-bookmark-name-from-record bookmark)))))

(defun bmkp-bookmark-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a bookmark-file bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-bookmark-file))

(defun bmkp-bookmark-list-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a bookmark-list bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-bookmark-list))

(defun bmkp-desktop-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a desktop bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-desktop))

;; Note: To avoid remote access, if bookmark does not have the Dired handler, then we insist
;; that it be for a local directory.  IOW, we do not include remote directories that were not
;; bookmarked by Bookmark+ (and so do not have the Dired handler).
(defun bmkp-dired-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a Dired bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (or (eq (bookmark-get-handler bookmark) 'bmkp-jump-dired)
      (bmkp-local-directory-bookmark-p bookmark)))

(defun bmkp-dired-this-dir-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a Dired bookmark for the `default-directory'.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (and (bmkp-dired-bookmark-p bookmark)
       (let ((dir  (file-name-directory (bookmark-get-filename bookmark))))
         (bmkp-same-file-p dir default-directory))))

(defun bmkp-dired-wildcards-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a Dired buffer with wildcards.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (and (bmkp-dired-bookmark-p bookmark)
       (let ((file  (bookmark-get-filename bookmark)))
         (and (stringp file)  (bmkp-string-match-p (regexp-quote "*") file)))))

(when (> emacs-major-version 24)        ; Emacs 25+

  (defun bmkp-eww-bookmark-p (bookmark)
    "Return non-nil if BOOKMARK is an EWW bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
    (eq (bookmark-get-handler bookmark) 'bmkp-jump-eww))

  )

(defun bmkp-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a file or directory.
This excludes bookmarks of a more specific kind (e.g. Info, Gnus).
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let* ((filename   (bookmark-get-filename bookmark))
         (nonfile-p  (equal filename bmkp-non-file-filename))
         (handler    (bookmark-get-handler bookmark)))
    (and filename  (not nonfile-p)
         (or (not handler)
             (memq handler bmkp-file-bookmark-handlers)
             (equal handler (bmkp-default-handler-for-file filename)))
         (not (bookmark-prop-get bookmark 'info-node))))) ; Emacs 20-21 Info: no handler.

(defun bmkp-file-this-dir-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks file/subdir in `default-directory'.
This excludes bookmarks of a more specific kind (e.g. Info, Gnus).
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (and bookmark
       (bmkp-file-bookmark-p bookmark)
       (bmkp-same-file-p (file-name-directory (bookmark-get-filename bookmark)) default-directory)))

(defun bmkp-flagged-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is flagged for deletion in `*Bookmark List*'.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (memq bookmark bmkp-flagged-bookmarks))

(defun bmkp-function-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a function bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-function))

(defun bmkp-gnus-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a Gnus bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (memq (bookmark-get-handler bookmark)
        '(gnus-summary-bookmark-jump bmkp-jump-gnus bmkext-jump-gnus)))

(defun bmkp-icicles-search-hits-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK records a list of Icicles search hits.
BOOKMARK is a bookmark name or a bookmark record.

An Icicles search-hits bookmark is shown in the bookmark-list display
with face `bmkp-no-jump', because you cannot jump to it from there."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-icicle-search-hits))

(defun bmkp-image-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an image-file bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (or (eq (bookmark-get-handler bookmark) 'image-bookmark-jump)
      (and (fboundp 'image-file-name-regexp) ; In `image-file.el' (Emacs 22+).
           (bmkp-file-bookmark-p bookmark)
           (not (bmkp-dired-bookmark-p bookmark))
           (bmkp-string-match-p (image-file-name-regexp) (bookmark-get-filename bookmark)))))

(defun bmkp-info-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an Info bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (or (eq (bookmark-get-handler bookmark) 'Info-bookmark-jump)
      (and (not (bookmark-get-handler bookmark))
           (or (string= "*info*" (bmkp-get-buffer-name bookmark))
               (bookmark-prop-get bookmark 'info-node))))) ; Emacs 20-21 - no `buffer-name' entry.

(defun bmkp-kmacro-list-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a kmacro-list bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-kmacro-list))

(defun bmkp-local-directory-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a local directory.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let ((file  (bookmark-get-filename bookmark)))
    (and (bmkp-local-file-bookmark-p bookmark)  (file-directory-p file))))

(defun bmkp-local-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a local file or directory.
This excludes bookmarks of a more specific kind (e.g. Info, Gnus).
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (and (bmkp-file-bookmark-p bookmark)  (not (bmkp-remote-file-bookmark-p bookmark))))

(defun bmkp-local-non-dir-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a local non-directory file.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let ((file  (bookmark-get-filename bookmark)))
    (and (bmkp-local-file-bookmark-p bookmark)  (not (file-directory-p file)))))

(defun bmkp-man-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a `man' page bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (memq (bookmark-get-handler bookmark) '(bmkp-jump-man bmkp-jump-woman
                                          bmkext-jump-man bmkext-jump-woman)))

(defun bmkp-marked-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a marked bookmark in `*Bookmark List*'.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (unless (stringp bookmark) (setq bookmark  (bmkp-bookmark-name-from-record bookmark)))
  (bmkp-bookmark-name-member bookmark bmkp-bmenu-marked-bookmarks))

(defun bmkp-modified-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a modified bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (memq bookmark bmkp-modified-bookmarks))

(defun bmkp-navlist-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is in the current navigation list.
BOOKMARK is a bookmark name or a bookmark record."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (memq bookmark bmkp-nav-alist))

(defun bmkp-non-dir-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a non-directory file.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let ((file  (bookmark-get-filename bookmark)))
    (and (bmkp-file-bookmark-p bookmark)  (not (file-directory-p file)))))

(defun bmkp-non-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a non-file bookmark (e.g *scratch*).
This excludes bookmarks of a more specific kind (e.g. Info, Gnus).
It includes bookmarks to existing buffers, as well as bookmarks
defined for buffers that do not currently exist.

BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let* ((filename   (bookmark-get-filename bookmark))
         (nonfile-p  (equal filename bmkp-non-file-filename)))
    (and (bmkp-get-buffer-name bookmark)
         (or (not filename)  nonfile-p
             ;; Ensure not remote before calling `file-exists-p'.  (Do not prompt for password.)
             (and (not (bmkp-file-remote-p filename))  (not (file-exists-p filename))))
         (not (bookmark-get-handler bookmark)))))

(defun bmkp-non-invokable-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a non-invokable bookmark.
That is, jumping to it has no effect, because its handler is `ignore'.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'.

A non-invokable bookmark is shown in the bookmark-list display with
face `bmkp-no-jump', because you cannot jump to it."
  (eq (bookmark-get-handler bookmark) 'ignore))

(defun bmkp-orphaned-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an orphaned file or directory bookmark.
This means that the file recorded for BOOKMARK does not exist or is
not readable.  But a Dired bookmark with wildcards in the file name is
assumed to be readable.

BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (and (bmkp-file-bookmark-p bookmark)
       (if (bmkp-dired-bookmark-p bookmark)
           (and (not (bmkp-dired-wildcards-bookmark-p bookmark))
                (not (file-readable-p (bookmark-get-filename bookmark))))
         (not (file-readable-p (bookmark-get-filename bookmark))))))

(defun bmkp-orphaned-local-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an orphaned local-file bookmark.
This means that the file name recorded for BOOKMARK is not remote, and
the file does not exist or is not readable.  But a Dired bookmark with
wildcards in the file name is assumed to be readable.

BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (and (bmkp-local-file-bookmark-p bookmark)
       (if (bmkp-dired-bookmark-p bookmark)
           (and (not (bmkp-dired-wildcards-bookmark-p bookmark))
                (not (file-readable-p (bookmark-get-filename bookmark))))
         (not (file-readable-p (bookmark-get-filename bookmark))))))

(defun bmkp-orphaned-remote-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an orphaned remote-file bookmark.
This means that the file name recorded for BOOKMARK is remote, and the
file does not exist or is not readable.  But a Dired bookmark with
wildcards in the file name is assumed to be readable.

BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (and (bmkp-remote-file-bookmark-p bookmark)
       (if (bmkp-dired-bookmark-p bookmark)
           (and (not (bmkp-dired-wildcards-bookmark-p bookmark))
                (not (file-readable-p (bookmark-get-filename bookmark))))
         (not (file-readable-p (bookmark-get-filename bookmark))))))

(defun bmkp-region-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK has region information.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (and (bmkp-get-end-position bookmark)
       (bookmark-get-position bookmark)
       (/= (bookmark-get-position bookmark) (bmkp-get-end-position bookmark))))

(defun bmkp-remote-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a remote file or directory.
This includes remote Dired bookmarks, but otherwise excludes bookmarks
with handlers (e.g. Info, Gnus).

BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let* ((handler   (bookmark-get-handler bookmark))
         (file      (bookmark-get-filename bookmark))
         (rem-file  (and file  (bmkp-file-remote-p file))))
    (and rem-file  (or (not handler)  (eq handler 'bmkp-jump-dired)))))

(defun bmkp-remote-non-dir-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a remote non-directory file.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let ((file  (bookmark-get-filename bookmark)))
    (and (bmkp-remote-file-bookmark-p bookmark)  (not (file-directory-p file)))))

(defun bmkp-snippet-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a snippet bookmark.
This means that it records a snippet of text and that jumping to it
copies that text to the `kill-ring'.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-snippet))

(defun bmkp-temporary-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is temporary.
This means that it has a non-nil `bmkp-temp' entry.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (and bookmark  (bookmark-prop-get bookmark 'bmkp-temp)))

(defun bmkp-this-buffer-p (bookmark)
  "Return non-nil if BOOKMARK's buffer is the current buffer.
But return nil if BOOKMARK has an associated file, but it is not the
 buffer's file.
And return nil for bookmarks, such as desktops, that are not really
 associated with a buffer, even if they have a `buffer-name' entry.

BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (and (let ((this-file  (condition-case nil (bookmark-buffer-file-name) (error nil)))
             (bmk-file   (and (bmkp-file-bookmark-p bookmark)  (bookmark-get-filename bookmark))))
         ;; Two possibilities:
         ;; * Neither buffer nor bookmark has a file, and the buffer names are the same.
         ;; * Both have files, and they are the same file.
         (or (and (not this-file)  (not bmk-file)  (equal (bmkp-get-buffer-name bookmark) (buffer-name)))
             (and this-file  bmk-file  (bmkp-same-file-p this-file bmk-file))))
       ;; If the buffer to check is from EWW, the buffer URL must match the bookmark URL.
       (or (not (eq major-mode 'eww-mode))
           (and (fboundp 'bmkp-eww-url)  (equal (bookmark-location bookmark) (bmkp-eww-url)))) ; Emacs 25+
       (not (bmkp-desktop-bookmark-p        bookmark))
       (not (bmkp-bookmark-file-bookmark-p  bookmark))
       (not (bmkp-sequence-bookmark-p       bookmark))
       (not (bmkp-function-bookmark-p       bookmark))
       (not (bmkp-variable-list-bookmark-p  bookmark))))

(defun bmkp-this-file-p (bookmark)
  "Return non-nil if BOOKMARK's file is the visited file.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let ((bmk-file   (and (bmkp-file-bookmark-p bookmark)  (bookmark-get-filename bookmark)))
        (this-file  (or (and (buffer-file-name)  (bookmark-buffer-file-name))
                        (and (eq major-mode 'dired-mode)  (if (consp dired-directory)
                                                              (car dired-directory)
                                                            dired-directory)))))
    (and bmk-file  this-file  (bmkp-same-file-p this-file bmk-file))))

(defun bmkp-last-specific-buffer-p (bookmark)
  "Return t if BOOKMARK's `buffer-name' is `bmkp-last-specific-buffer'.
But return nil for bookmarks, such as desktops, that are not really
associated with a buffer, even if they have a `buffer-name' entry.
It does not matter whether the buffer exists.

BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let ((buf  (bmkp-get-buffer-name bookmark)))
    (and buf  (string= buf bmkp-last-specific-buffer)
         (not (bmkp-desktop-bookmark-p        bookmark))
         (not (bmkp-bookmark-file-bookmark-p  bookmark))
         (not (bmkp-sequence-bookmark-p       bookmark))
         (not (bmkp-function-bookmark-p       bookmark))
         (not (bmkp-variable-list-bookmark-p  bookmark)))))

(defun bmkp-last-specific-file-p (bookmark)
  "Return t if BOOKMARK's `filename' is `bmkp-last-specific-file'.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (let ((file  (bookmark-get-filename bookmark)))
    (and file  (bmkp-same-file-p file bmkp-last-specific-file))))

(defun bmkp-sequence-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a sequence bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-sequence))

(defun bmkp-url-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a URL bookmark.
This means that it satifies `bmkp-eww-bookmark-p' (Emacs 25+),
`bmkp-w3m-bookmark-p', or `bmkp-url-browse-bookmark-p'.

BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (or (and (fboundp 'bmkp-eww-bookmark-p)  (bmkp-eww-bookmark-p bookmark))
      (bmkp-w3m-bookmark-p bookmark)
      (bmkp-url-browse-bookmark-p bookmark)))

(defun bmkp-url-browse-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a `browse-url' bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-url-browse))

(defun bmkp-variable-list-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a variable-list bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-variable-list))

(defun bmkp-w3m-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a W3M bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (memq (bookmark-get-handler bookmark) '(bmkp-jump-w3m bmkext-jump-w3m)))


;;(@* "Filter Functions")
;;  *** Filter Functions ***

(defun bmkp-all-tags-alist-only (tags)
  "`bookmark-alist', but with only bookmarks having all their tags in TAGS.
Does not include bookmarks that have no tags.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lambda (bmk)
     (lexical-let* ((tgs       tags)
                    (bmk-tags  (bmkp-get-tags bmk)))
       (and bmk-tags  (bmkp-every (lambda (tag) (member (bmkp-tag-name tag) tgs)) bmk-tags))))
   bookmark-alist))

(defun bmkp-all-tags-regexp-alist-only (regexp)
  "`bookmark-alist', but with only bookmarks having all tags match REGEXP.
Does not include bookmarks that have no tags.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((rg  regexp))
     (lambda (bmk)
       (let ((bmk-tags  (bmkp-get-tags bmk)))
         (and bmk-tags
              (bmkp-every (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag))) bmk-tags)))))
   bookmark-alist))

(defun bmkp-annotated-alist-only ()
  "`bookmark-alist', but only for bookmarks with non-empty annotations.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-annotated-bookmark-p bookmark-alist))

(defun bmkp-autofile-alist-only (&optional prefix)
  "`bookmark-alist', filtered to retain only autofile bookmarks.
With non-nil arg PREFIX, the bookmark names must all have that PREFIX."
  (bookmark-maybe-load-default-file)
  (if (not prefix)
      (bmkp-remove-if-not #'bmkp-autofile-bookmark-p bookmark-alist)
    (bmkp-remove-if-not (lexical-let ((pref  prefix)) (lambda (bmk) (bmkp-autofile-bookmark-p bmk pref)))
                        bookmark-alist)))

(defun bmkp-autofile-all-tags-alist-only (tags)
  "`bookmark-alist', with only autofiles having all tags in TAGS.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((tgs  tags))
     (lambda (bmk)
       (and (bmkp-autofile-bookmark-p bmk)  (bmkp-get-tags bmk)
            (bmkp-every (lexical-let ((bk  bmk)) (lambda (tag) (bmkp-has-tag-p bk tag))) tgs))))
   bookmark-alist))

(defun bmkp-autofile-all-tags-regexp-alist-only (regexp)
  "`bookmark-alist', with only autofiles having all tags match REGEXP.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((rg  regexp))
     (lambda (bmk)
       (and (bmkp-autofile-bookmark-p bmk)
            (let ((bmk-tags  (bmkp-get-tags bmk)))
              (and bmk-tags
                   (bmkp-every (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag))) bmk-tags))))))
   bookmark-alist))

(defun bmkp-autofile-some-tags-alist-only (tags)
  "`bookmark-alist', with only autofiles having some tags in TAGS.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lambda (bmk) (and (bmkp-autofile-bookmark-p bmk)
                      (bmkp-some (lexical-let ((bk  bmk)) (lambda (tag) (bmkp-has-tag-p bk tag)))  tags)))
   bookmark-alist))

(defun bmkp-autofile-some-tags-regexp-alist-only (regexp)
  "`bookmark-alist', with only autofiles having some tags match REGEXP.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((rg  regexp))
     (lambda (bmk) (and (bmkp-autofile-bookmark-p bmk)
                        (bmkp-some (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag)))
                                   (bmkp-get-tags bmk)))))
   bookmark-alist))
(defun bmkp-autonamed-alist-only ()
  "`bookmark-alist', with only autonamed bookmarks (from any buffers).
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-autonamed-bookmark-p bookmark-alist))

(defun bmkp-autonamed-this-buffer-alist-only ()
  "`bookmark-alist', with only autonamed bookmarks for the current buffer.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (bmkp-autonamed-this-buffer-bookmark-p bmk)) bookmark-alist))

(defun bmkp-bookmark-file-alist-only ()
  "`bookmark-alist', filtered to retain only bookmark-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-bookmark-file-bookmark-p bookmark-alist))

(defun bmkp-bookmark-list-alist-only ()
  "`bookmark-alist', filtered to retain only bookmark-list bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-bookmark-list-bookmark-p bookmark-alist))

(defun bmkp-desktop-alist-only ()
  "`bookmark-alist', filtered to retain only desktop bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-desktop-bookmark-p bookmark-alist))

(defun bmkp-dired-alist-only ()
  "`bookmark-alist', filtered to retain only Dired bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-dired-bookmark-p bookmark-alist))

(defun bmkp-dired-this-dir-alist-only ()
  "`bookmark-alist', with only Dired bookmarks for the current directory.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-dired-this-dir-bookmark-p bookmark-alist))

(defun bmkp-dired-wildcards-alist-only ()
  "`bookmark-alist', with only bookmarks for a Dired buffer with wildcards.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-dired-wildcards-bookmark-p bookmark-alist))

(when (fboundp 'bmkp-eww-bookmark-p)    ; Emacs 25+

  (defun bmkp-eww-alist-only ()
    "`bookmark-alist', filtered to retain only EWW bookmarks.
A new list is returned (no side effects)."
    (bookmark-maybe-load-default-file)
    (bmkp-remove-if-not #'bmkp-eww-bookmark-p bookmark-alist))

  )

(defun bmkp-file-alist-only ()
  "`bookmark-alist', filtered to retain only file and directory bookmarks.
This excludes bookmarks that might contain file information but are
particular in some way - for example, Info bookmarks or Gnus bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-file-bookmark-p bookmark-alist))

(defun bmkp-file-all-tags-alist-only (tags)
  "`bookmark-alist', with only file bookmarks having all tags in TAGS.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((tgs  tags))
     (lambda (bmk)
       (and (bmkp-file-bookmark-p bmk)  (bmkp-get-tags bmk)
            (bmkp-every (lexical-let ((bk  bmk)) (lambda (tag) (bmkp-has-tag-p bk tag)))  tgs))))
   bookmark-alist))

(defun bmkp-file-all-tags-regexp-alist-only (regexp)
  "`bookmark-alist', with only file bookmarks having all tags match REGEXP.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((rg  regexp))
     (lambda (bmk)
       (and (bmkp-file-bookmark-p bmk)
            (let ((bmk-tags  (bmkp-get-tags bmk)))
              (and bmk-tags
                   (bmkp-every (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag))) bmk-tags))))))
   bookmark-alist))

(defun bmkp-file-some-tags-alist-only (tags)
  "`bookmark-alist', with only file bookmarks having some tags in TAGS.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((tgs  tags))
     (lambda (bmk) (and (bmkp-file-bookmark-p bmk)
                        (bmkp-some (lexical-let ((bk  bmk)) (lambda (tag) (bmkp-has-tag-p bk tag)))  tgs))))
   bookmark-alist))

(defun bmkp-file-some-tags-regexp-alist-only (regexp)
  "`bookmark-alist', with only file bookmarks having some tags match REGEXP.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((rg  regexp))
     (lambda (bmk) (and (bmkp-file-bookmark-p bmk)
                        (bmkp-some (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag)))
                                   (bmkp-get-tags bmk)))))
   bookmark-alist))

(defun bmkp-file-this-dir-alist-only ()
  "`bookmark-alist', filtered with `bmkp-file-this-dir-bookmark-p'.
Include only files and subdir that are in `default-directory'.
This excludes bookmarks that might contain file information but are
particular in some way - for example, Info bookmarks or Gnus bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-file-this-dir-bookmark-p bookmark-alist))

(defun bmkp-file-this-dir-all-tags-alist-only (tags)
  "`bookmark-alist', for files in this dir having all tags in TAGS.
Include only files and subdir that are in `default-directory'.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((tgs  tags))
     (lambda (bmk)
       (and (bmkp-file-this-dir-bookmark-p bmk)  (bmkp-get-tags bmk)
            (bmkp-every (lexical-let ((bk  bmk)) (lambda (tag) (bmkp-has-tag-p bk tag)))  tgs))))
   bookmark-alist))

(defun bmkp-file-this-dir-all-tags-regexp-alist-only (regexp)
  "`bookmark-alist', for files in this dir having all tags match REGEXP.
Include only files and subdir that are in `default-directory'.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((rg  regexp))
     (lambda (bmk)
       (and (bmkp-file-this-dir-bookmark-p bmk)
            (let ((bmk-tags  (bmkp-get-tags bmk)))
              (and bmk-tags
                   (bmkp-every (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag)))  bmk-tags))))))
   bookmark-alist))

(defun bmkp-file-this-dir-some-tags-alist-only (tags)
  "`bookmark-alist', for files in this dir having some tags in TAGS.
Include only files and subdir that are in `default-directory'.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((tgs  tags))
     (lambda (bmk) (and (bmkp-file-this-dir-bookmark-p bmk)
                        (bmkp-some (lexical-let ((bk  bmk)) (lambda (tag) (bmkp-has-tag-p bk tag)))  tgs))))
   bookmark-alist))

(defun bmkp-file-this-dir-some-tags-regexp-alist-only (regexp)
  "`bookmark-alist', for files in this dir having some tags match REGEXP.
Include only files and subdir that are in `default-directory'.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lexical-let ((rg  regexp))
     (lambda (bmk) (and (bmkp-file-this-dir-bookmark-p bmk)
                        (bmkp-some (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag)))
                                   (bmkp-get-tags bmk)))))
   bookmark-alist))

(defun bmkp-function-alist-only ()
  "`bookmark-alist', filtered to retain only function bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-function-bookmark-p bookmark-alist))

(defun bmkp-gnus-alist-only ()
  "`bookmark-alist', filtered to retain only Gnus bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-gnus-bookmark-p bookmark-alist))

(defun bmkp-icicles-search-hits-alist-only ()
  "`bookmark-alist', but only for Icicles search hits bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-icicles-search-hits-bookmark-p bookmark-alist))

(defun bmkp-image-alist-only ()
  "`bookmark-alist', filtered to retain only image-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-image-bookmark-p bookmark-alist))

(defun bmkp-info-alist-only ()
  "`bookmark-alist', filtered to retain only Info bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-info-bookmark-p bookmark-alist))

(defun bmkp-last-specific-buffer-alist-only ()
  "`bookmark-alist', but only for `bmkp-last-specific-buffer'.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-last-specific-buffer-p bookmark-alist))

(defun bmkp-last-specific-file-alist-only ()
  "`bookmark-alist', but only for `bmkp-last-specific-file'.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-last-specific-file-p bookmark-alist))

(defun bmkp-man-alist-only ()
  "`bookmark-alist', filtered to retain only `man' page bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-man-bookmark-p bookmark-alist))

(defun bmkp-local-file-alist-only ()
  "`bookmark-alist', filtered to retain only local-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-local-file-bookmark-p bookmark-alist))

(defun bmkp-local-non-dir-file-alist-only ()
  "`bookmark-alist', filtered to retain only local non-dir file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-local-non-dir-file-bookmark-p bookmark-alist))

(defun bmkp-non-autonamed-alist-only ()
  "`bookmark-alist', with only non-autonamed bookmarks (from any buffers).
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (not (bmkp-autonamed-bookmark-p bmk))) bookmark-alist))

(defun bmkp-non-dir-file-alist-only ()
  "`bookmark-alist', filtered to retain only non-directory file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-non-dir-file-bookmark-p bookmark-alist))

(defun bmkp-non-file-alist-only ()
  "`bookmark-alist', filtered to retain only non-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-non-file-bookmark-p bookmark-alist))

(defun bmkp-non-invokable-alist-only ()
  "`bookmark-alist', filtered to retain only non-invokable bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-non-invokable-bookmark-p bookmark-alist))

(defun bmkp-orphaned-file-alist-only ()
  "`bookmark-alist', filtered to retain only orphaned file bookmarks."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-orphaned-file-bookmark-p bookmark-alist))

(defun bmkp-orphaned-local-file-alist-only ()
  "`bookmark-alist', but retaining only orphaned local-file bookmarks."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-orphaned-local-file-bookmark-p bookmark-alist))

(defun bmkp-orphaned-remote-file-alist-only ()
  "`bookmark-alist', but retaining only orphaned remote-file bookmarks."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-orphaned-remote-file-bookmark-p bookmark-alist))

(defun bmkp-regexp-filtered-annotation-alist-only ()
  "`bookmark-alist' for annotations matching `bmkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   (lambda (bmk)
     (let ((annot  (bookmark-get-annotation bmk)))
       (and (stringp annot)  (not (string= "" annot))
            (bmkp-string-match-p bmkp-bmenu-filter-pattern annot))))
   bookmark-alist))                     ; (Could use `bmkp-annotated-alist-only' here instead.)

(defun bmkp-regexp-filtered-bookmark-name-alist-only ()
  "`bookmark-alist' for bookmarks matching `bmkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (bmkp-string-match-p bmkp-bmenu-filter-pattern (car bmk)))
                      bookmark-alist))

(defun bmkp-regexp-filtered-file-name-alist-only ()
  "`bookmark-alist' for files matching `bmkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (let ((fname  (bookmark-get-filename bmk)))
                                      (and fname  (bmkp-string-match-p bmkp-bmenu-filter-pattern fname))))
                      bookmark-alist))

(defun bmkp-regexp-filtered-tags-alist-only ()
  "`bookmark-alist' for tags matching `bmkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk)
                        (let ((bmk-tags  (bmkp-get-tags bmk)))
                          (and bmk-tags  (bmkp-some (lambda (tag)
                                                      (bmkp-string-match-p bmkp-bmenu-filter-pattern
                                                                           (bmkp-tag-name tag)))
                                                    bmk-tags))))
                      bookmark-alist))

(defun bmkp-region-alist-only ()
  "`bookmark-alist', filtered to retain only bookmarks that have regions.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-region-bookmark-p bookmark-alist))

(defun bmkp-remote-file-alist-only ()
  "`bookmark-alist', filtered to retain only remote-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-remote-file-bookmark-p bookmark-alist))

(defun bmkp-remote-non-dir-file-alist-only ()
  "`bookmark-alist', filtered to retain only remote non-dir file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-remote-non-dir-file-bookmark-p bookmark-alist))

(defun bmkp-sequence-alist-only ()
  "`bookmark-alist', filtered to retain only sequence bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-sequence-bookmark-p bookmark-alist))  

(defun bmkp-snippet-alist-only ()
  "`bookmark-alist', filtered to retain only snippet bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-snippet-bookmark-p bookmark-alist))

(defun bmkp-some-tags-alist-only (tags)
  "`bookmark-alist', but with only bookmarks having some tags in TAGS.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lexical-let ((tgs  tags))
                        (lambda (bmk)
                          (bmkp-some (lexical-let ((bk  bmk)) (lambda (tag) (bmkp-has-tag-p bk tag)))
                                     tgs)))
                      bookmark-alist))

(defun bmkp-some-tags-regexp-alist-only (regexp)
  "`bookmark-alist', but with only bookmarks having some tags match REGEXP.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lexical-let ((rg  regexp))
                        (lambda (bmk)
                          (bmkp-some (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag)))
                                     (bmkp-get-tags bmk))))
                      bookmark-alist))

(defun bmkp-specific-buffers-alist-only (&optional buffers)
  "`bookmark-alist', filtered to retain only bookmarks to buffers BUFFERS.
BUFFERS is a list of buffer names.
It defaults to a singleton list with the current buffer's name.
A new list is returned (no side effects).

Note: Bookmarks created by vanilla Emacs do not record the buffer
name.  They are therefore excluded from the returned alist."
  (unless buffers  (setq buffers  (list (buffer-name))))
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lexical-let ((bufs  buffers))
                        (lambda (bmk)
                          (and (not (bmkp-desktop-bookmark-p       bmk)) ; Exclude these
                               (not (bmkp-bookmark-file-bookmark-p bmk))
                               (not (bmkp-sequence-bookmark-p      bmk))
                               (not (bmkp-function-bookmark-p      bmk))
                               (not (bmkp-variable-list-bookmark-p bmk))
                               (member (bmkp-get-buffer-name bmk) bufs))))
                      bookmark-alist))

(defun bmkp-specific-files-alist-only (&optional files)
  "`bookmark-alist', filtered to retain only bookmarks to files FILES.
FILES is a list of absolute file names.
It defaults to a singleton list with the current buffer's file name.
A new list is returned (no side effects)."
  (unless files  (setq files  (list (buffer-file-name))))
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lexical-let ((ff  files)) (lambda (bmk) (member (bookmark-get-filename bmk) ff)))
                      bookmark-alist))

(defun bmkp-tagged-alist-only ()
  "`bookmark-alist', with only bookmarks that have tags.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-get-tags bookmark-alist))

(defun bmkp-temporary-alist-only ()
  "`bookmark-alist', filtered to retain only temporary bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-temporary-bookmark-p bookmark-alist))

(defun bmkp-this-file/buffer-alist-only ()
  "`bookmark-alist', with only bookmarks for the current file/buffer.
A new list is returned (no side effects).
If visiting a file, this is `bmkp-this-file-alist-only'.
Otherwise, this is `bmkp-this-buffer-alist-only'."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (if (buffer-file-name) #'bmkp-this-file-p #'bmkp-this-buffer-p) bookmark-alist))

(defun bmkp-this-buffer-alist-only ()
  "`bookmark-alist', with only bookmarks for the current buffer.
A new list is returned (no side effects).
See `bmkp-this-buffer-p'."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-this-buffer-p bookmark-alist))

(defun bmkp-this-file-alist-only ()
  "`bookmark-alist', with only bookmarks for the current file.
A new list is returned (no side effects).
See `bmkp-this-file-p'."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-this-file-p bookmark-alist))

(defun bmkp-untagged-alist-only ()
  "`bookmark-alist', with only bookmarks that do not have tags.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if #'bmkp-get-tags bookmark-alist))

(defun bmkp-url-alist-only ()
  "`bookmark-alist', filtered to retain only URL bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-url-bookmark-p bookmark-alist))

(defun bmkp-url-browse-alist-only ()
  "`bookmark-alist', but with only URL bookmarks that are non-W3M, non-EWW.
\(The bookmarks satisfy `bmkp-url-browse-bookmark-p'.)
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-url-browse-bookmark-p bookmark-alist))

(defun bmkp-variable-list-alist-only ()
  "`bookmark-alist', filtered to retain only variable-list bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-variable-list-bookmark-p bookmark-alist))

(defun bmkp-w3m-alist-only ()
  "`bookmark-alist', filtered to retain only W3M bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-w3m-bookmark-p bookmark-alist))


;;; Marked bookmarks

(defun bmkp-marked-bookmarks-only ()
  "Return the list of marked bookmarks."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-marked-bookmark-p bookmark-alist))

(defun bmkp-unmarked-bookmarks-only ()
  "Return the list of unmarked bookmarks."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if #'bmkp-marked-bookmark-p bookmark-alist))

(defun bmkp-some-marked-p (alist)
  "Return non-nil if ALIST is nonempty and includes a marked bookmark."
  (catch 'break (dolist (i  alist)  (and (bmkp-marked-bookmark-p i)  (throw 'break t)))))

(defun bmkp-some-unmarked-p (alist)
  "Return non-nil if ALIST is nonempty and includes an unmarked bookmark."
  (catch 'break (dolist (i  alist)  (and (not (bmkp-marked-bookmark-p i))  (throw 'break t)))))


;;(@* "General Utility Functions")
;;  *** General Utility Functions ***

(when (and (fboundp 'cl-puthash)  (not (fboundp 'puthash))) ; Emacs 20 with `cl-extra.el' loaded.
  (defalias 'puthash 'cl-puthash))

(if (fboundp 'puthash)                  ; Emacs 21+, or Emacs 20 with `cl-extra.el' loaded.
    (defun bmkp-remove-dups (sequence &optional test)
      "Copy of SEQUENCE with duplicate elements removed.
Optional arg TEST is the test function.  If nil, test with `equal'.
See `make-hash-table' for possible values of TEST."
      (setq test  (or test #'equal))
      (let ((htable  (make-hash-table :test test)))
        (loop for elt in sequence
              unless (gethash elt htable)
              do     (puthash elt elt htable)
              finally return (loop for i being the hash-values in htable collect i))))

  (defun bmkp-remove-dups (list &optional use-eq)
    "Copy of LIST with duplicate elements removed.
Test using `equal' by default, or `eq' if optional USE-EQ is non-nil."
    (let ((tail  list)
          new)
      (while tail
        (unless (if use-eq (memq (car tail) new) (member (car tail) new))
          (push (car tail) new))
        (pop tail))
      (nreverse new))))

(defun bmkp-unpropertized-string (string)
  "Return a copy of STRING, but with properties removed.
Does not change the original STRING."
  (let ((strg  (copy-sequence string)))
    (set-text-properties 0 (length strg) () strg)
    strg))

;; For a name propertized with `bmkp-full-record', this is similar to `bmkp-assoc-delete-all'.
(defun bmkp-delete-bookmark-name-from-list (delname bnames)
  "Delete names that represent the same bookmark as DELNAME from BNAMES.
This means that they are `string=' and they either have no property
`bmkp-full-record' or that property has the same value.
Return the modified list BNAMES."
  ;; $$$$$$ Can we change `equal' to `eq' everywhere here?
  (let ((delprop  (get-text-property 0 'bmkp-full-record delname))
        bmkprop)
    (if (not delprop)
        (setq bnames  (delete delname bnames)) ; Unpropertized - just use `delete'.
      ;; Propertized.  Delete names that are `string=' and have the same property value or none.
      (while (and bnames  (string= delname (car bnames)) ; Delete those at list beginning.
                  (or (not (setq bmkprop  (get-text-property 0 'bmkp-full-record (car bnames))))
                      (equal delprop bmkprop)))
        (setq bnames  (cdr bnames)))
      (let ((tail  bnames)              ; Delete those not at list beginning.
            tail-cdr)
        (while (setq tail-cdr  (cdr tail))
          (if (and (car tail-cdr)
                   (string= delname (car tail-cdr))
                   (or (not (setq bmkprop  (get-text-property 0 'bmkp-full-record (car tail-cdr))))
                       (equal delprop bmkprop)))
              (setcdr tail  (cdr tail-cdr))
            (setq tail  tail-cdr))))
      bnames)))

(defun bmkp-bookmark-name-member (name names)
  "Like `member', but tests also bookmark NAME's `bmkp-full-record' property.
Return the tail of NAMES whose car is NAME with the property match.
If NAME has no `bmkp-full-record' property then this is just `member'.
If NAME has property `bmkp-full-record', then test whether both:
 a. NAME is a member of NAMES and
 b. NAME has the same `bmkp-full-record' value as an element of NAMES."
  ;; $$$$$$ Can we change `equal' to `eq' here?
  (let ((prop  (get-text-property 0 'bmkp-full-record name)))
    (if (or (null name)  (not prop))
        (member name names)             ; Unpropertized - just use `member'.
      (while (and names  (not (and (stringp (car names))
                                   (string= name (car names)) ; = `bmkp-names-same-bookmark-p'.
                                   ;; If unpropertized in NAMES, then assume it's the one.
                                   (or (not (get-text-property 0 'bmkp-full-record (car names)))
                                       (equal prop (get-text-property 0 'bmkp-full-record (car names)))))))
        (setq names  (cdr names)))
      names)))

(defun bmkp-names-same-bookmark-p (name1 name2)
  "Return non-nil if the two strings name the same bookmark.
The strings are `string=' and their `bmkp-full-record' property values
for the first character are `equal'."

  ;; $$$$$$ Can we change `equal' to `eq' here?
  (and (string= name1 name2)
       (equal (get-text-property 0 'bmkp-full-record name1)
              (get-text-property 0 'bmkp-full-record name2))))

(defun bmkp-remove-if (pred xs)
  "A copy of list XS with no elements that satisfy predicate PRED."
  (let ((result  ()))
    (dolist (x  xs)  (unless (funcall pred x) (push x result)))
    (nreverse result)))

(defun bmkp-remove-if-not (pred xs)
  "A copy of list XS with only elements that satisfy predicate PRED."
  (let ((result  ()))
    (dolist (x  xs)  (when (funcall pred x) (push x result)))
    (nreverse result)))

;; Similar to `every' in `cl-extra.el', without non-list sequences and multiple sequences.
(defun bmkp-every (predicate list)
  "Return t if PREDICATE is true for all elements of LIST; else nil."
  (while (and list  (funcall predicate (car list)))  (setq list  (cdr list)))
  (null list))

;; Same as `zz-some' in `zones.el'.
;; This is NOT the same as `some' in `cl-extra.el', even without non-list sequences and multiple sequences.
;;
;; If PREDICATE is satisfied by a list element ELEMENT, so that it returns a non-nil value VALUE for ELEMENT,
;; then this returns the cons (ELEMENT . VALUE).  It does not return just VALUE.
(defun bmkp-some (predicate list)
  "Return non-nil if PREDICATE applied to some element of LIST is true.
The value returned is a cons, (ELEMENT . VALUE), where ELEMENT is the
first list element that satisfies PREDICATE and VALUE is the value of
PREDICATE applied to ELEMENT."
  (let (elt val)
    (catch 'bmkp-some
      (while list
        (when (setq val  (funcall predicate (setq elt  (pop list))))
          (throw 'bmkp-some (cons elt val))))
      nil)))

;; From `cl-seq.el', function `union', without keyword treatment.
;; (Same as `icicle-set-union' in `icicles-fn.el'.)
(defun bmkp-set-union (list1 list2)
  "Combine LIST1 and LIST2 using a set-union operation.
The result list contains all items that appear in either LIST1 or
LIST2.  Comparison is done using `equal'.  This is a non-destructive
function; it copies the data if necessary."
  (cond ((null list1)         list2)
        ((null list2)         list1)
        ((equal list1 list2)  list1)
        (t
         (unless (>= (length list1) (length list2))
           (setq list1  (prog1 list2 (setq list2  list1)))) ; Swap them.
         (while list2
           (unless (member (car list2) list1)  (setq list1  (cons (car list2) list1)))
           (setq list2  (cdr list2)))
         list1)))

(defun bmkp-upcase (string)
  "`upcase', but in case of error, return original STRING.
This works around an Emacs 20 problem that occurs if STRING contains
binary data (weird chars)."
  (condition-case nil (upcase string) (error string)))

;; Thx to Michael Heerdegen and Michael Albinus for help with this one.
(defun bmkp-same-file-p (file1 file2)
  "Return non-nil if FILE1 and FILE2 name the same file.
If either name is not absolute, then it is expanded relative to
`default-directory' for the test."
  (let* ((remote1        (bmkp-file-remote-p file1))
         (remote2        (bmkp-file-remote-p file2))
         (ignore-case-p  (and (not remote1)  (not remote2) ; Assume case-sensitive if remote.
                              (if (boundp 'read-file-name-completion-ignore-case)
                                  (eval (car (get 'read-file-name-completion-ignore-case
                                                  'standard-value)))
                                ;; From the Emacs 24 definition of `read-file-name-completion-ignore-case'.
                                (memq system-type '(ms-dos windows-nt darwin cygwin))))))
    (and (equal remote1 remote2)
         (if (fboundp 'file-equal-p)
             (file-equal-p file1 file2)
           (let ((ft1  (file-truename (expand-file-name file1)))
                 (ft2  (file-truename (expand-file-name file2))))
             (eq t (compare-strings ft1 0 (length ft1) ft2 0 (length ft2) ignore-case-p)))))))

;;; $$$$$$
;;; (defun bmkp-same-file-p (file1 file2)
;;;   "Return non-nil if FILE1 and FILE2 name the same file.
;;; If either name is not absolute, then it is expanded relative to
;;; `default-directory' for the test."
;;;   (and (equal (bmkp-file-remote-p file1) (bmkp-file-remote-p file2))
;;;        (string= (file-truename (expand-file-name file1))
;;;                 (file-truename (expand-file-name file2)))))

;;; $$$$$$
;;; (defun bmkp-file-remote-p (file-name)
;;;   "Returns non-nil if string FILE-NAME is likely to name a remote file."
;;;   (if (fboundp 'file-remote-p)
;;;       (file-remote-p file-name)
;;;     (and (fboundp 'ffap-file-remote-p)  (ffap-file-remote-p file-name))))

(defun bmkp-file-remote-p (file)
  "Test whether FILE specifies a location on a remote system.
Return nil or a string identifying the remote connection (ideally a
prefix of FILE).

A file is considered remote if accessing it is likely to be slower or
less reliable than accessing local files.

This is `file-remote-p', if that function is available.  If not, use a
simple match against rough remote file syntax: `/...:'.

Unless `file-remote-p' is available and FILE has a `file-remote-p'
handler that opens a remote connection, `bmkp-file-remote-p' does not
open a remote connection."
  (if (fboundp 'file-remote-p)
      (file-remote-p file)
    (and (stringp file)  (string-match "\\`/[^/]+:" file)  (match-string 0 file))))

(defun bmkp-float-time (&optional specified-time)
  "Same as `float-time'.  (Needed for Emacs 20.)"
  (if (fboundp 'float-time)
      (float-time specified-time)
    (unless specified-time (setq specified-time  (current-time)))
    (+ (* (float (nth 0 specified-time)) (expt 2 16))  (nth 1 specified-time))))

(defun bmkp-string-less-case-fold-p (s1 s2)
  "Like `string-lessp', but respect `case-fold-search'."
  (when case-fold-search (setq s1  (bmkp-upcase s1)
                               s2  (bmkp-upcase s2)))
  (string-lessp s1 s2))

(defun bmkp-make-plain-predicate (pred &optional final-pred)
  "Return a plain predicate that corresponds to component-predicate PRED.
PRED and FINAL-PRED correspond to their namesakes in
`bmkp-sort-comparer' (which see).

PRED should return `(t)', `(nil)', or nil.

Optional arg FINAL-PRED is the final predicate to use if PRED cannot
decide (returns nil).  If FINAL-PRED is nil, then `bmkp-alpha-p', the
plain-predicate equivalent of `bmkp-alpha-cp' is used as the final
predicate."
  `(lambda (b1 b2) (let ((res  (funcall ',pred b1 b2)))
                     (if res (car res) (funcall ',(or final-pred 'bmkp-alpha-p) b1 b2)))))

(defun bmkp-repeat-command (command)
  "Repeat COMMAND."
  (let ((repeat-message-function  'ignore))
    (setq last-repeatable-command  command)
    (repeat nil)))


;;; If you need this for some reason, uncomment it.
;;; (defun bmkp-fix-bookmark-alist-and-save ()
;;;   "Update format of `bookmark-default-file' created in summer of 2009.
;;; You DO NOT NEED THIS, unless you happen to have used `bookmark+.el' in
;;; the summer of 2009 to create non-file bookmarks.  If you did that,
;;; then some of those bookmarks might cause vanilla Emacs (emacs -Q) to
;;; raise an error.  You can use this command to fix that problem: it
;;; modifies your existing `bookmark-default-file' (`~/.emacs.bmk'), after
;;; backing up that file (suffixing the name with \"_saveNUMBER\")."
;;;   (interactive)
;;;   (require 'cl)                         ; For `gensym'
;;;   (if (not (yes-or-no-p
;;;              "This will modify your bookmark file, after backing it up.  OK? "))
;;;       (message "OK, nothing done")
;;;     (bookmark-maybe-load-default-file)
;;;     (let ((bkup-file  (concat bookmark-default-file "_" (symbol-name (gensym "save")))))
;;;       (when (condition-case err
;;;                 (progn
;;;                   (with-current-buffer (let ((enable-local-variables  ()))
;;;                                          (find-file-noselect bookmark-default-file))
;;;                     (write-file bkup-file))
;;;                   (dolist (bmk  bookmark-alist)
;;;                     (let ((fn-tail  (member '(filename) bmk))
;;;                           (hdlr     (bookmark-get-handler (car bmk))))
;;;                       (cond (fn-tail
;;;                              (setcar fn-tail (cons 'filename bmkp-non-file-filename)))
;;;                             ((and (eq hdlr 'bmkp-jump-gnus)
;;;                                   (not (assoc 'filename bmk)))
;;;                              (setcdr bmk (cons (cons 'filename bmkp-non-file-filename)
;;;                                                (cdr bmk)))))))
;;;                   t)                    ; Be sure `dolist' exit with t to allow saving.
;;;               (error (error "No changes made. %s" (error-message-string err))))
;;;         (bookmark-save)
;;;         (message "Bookmarks file fixed.  Old version is `%s'" bkup-file)))))


;;(@* "Bookmark Entry Access Functions")
;;  *** Bookmark Entry Access Functions ***

(defun bmkp-get-buffer-name (bookmark)
  "Return the `buffer-name' entry for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'buffer-name))

(defun bmkp-get-end-position (bookmark)
  "Return the `end-position' entry for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'end-position))

(defun bmkp-get-visits-count (bookmark)
  "Return the `visits' count for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'visits))

(defun bmkp-get-visit-time (bookmark)
  "Return the `time' value for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  ;; Should just be a prop-get, but when first implemented, we used a float
  ;; instead of a time cons, so we need to convert any such obsolete recorded times.
  (let ((vt  (bookmark-prop-get bookmark 'time)))
    (when (numberp vt)                  ; Convert mid-2009 time values (floats) to cons form.
      (setq vt  (if (boundp 'seconds-to-time)
                    (seconds-to-time vt)
                  (list (floor vt 65536) ; Inlined `seconds-to-time', for Emacs 20-21.
                        (floor (mod vt 65536))
                        (floor (* (- vt (ffloor vt)) 1000000))))))
    vt))


;;(@* "Sorting - General Functions")
;;  *** Sorting - General Functions ***

(defun bmkp-sort-omit (alist &optional omit)
  "Sort a copy of ALIST, omitting any elements whose keys are in OMIT.
Return the copy.
Do not sort if `bmkp-sort-comparer' is nil.
This is a non-destructive operation: ALIST is not modified.

Sorting is done using using `bmkp-sort-comparer'.
If `bmkp-reverse-sort-p' is non-nil, then reverse the sort order.
Keys are compared for sorting using `equal'.

If optional arg OMIT is non-nil, then it is a list of keys.  Omit from
the return value any elements with keys in the list."
  (lexical-let ((new-alist  (bmkp-remove-omitted alist omit))
                (sort-fn    (and bmkp-sort-comparer  (if (and (not (functionp bmkp-sort-comparer))
                                                              (consp bmkp-sort-comparer))
                                                         'bmkp-multi-sort
                                                       bmkp-sort-comparer))))
    (when sort-fn
      (setq new-alist  (sort new-alist (if bmkp-reverse-sort-p
                                           (lambda (a b) (not (funcall sort-fn a b)))
                                         sort-fn))))
    new-alist))

(defun bmkp-remove-omitted (alist &optional omit)
  "Copy of bookmark ALIST without bookmarks whose names are in list OMIT.
Name comparison is done using `bmkp-bookmark-name-member'.
If optional arg OMIT is non-nil, then omit from the return value any
elements with keys in list OMIT."
  (let ((new  ()))
    (dolist (ii  alist)  (unless (bmkp-bookmark-name-member (car ii) omit)  (push ii new)))
    (nreverse new)))

;;; $$$$$$ No longer used.
;;; (defun bmkp-sort-and-remove-dups (alist &optional omit)
;;;   "Remove duplicates from a copy of ALIST, then sort it and return it.
;;; Do not sort if `bmkp-sort-comparer' is nil.
;;; Always remove duplicates.  Keep only the first element with a given
;;; key.  This is a non-destructive operation: ALIST is not modified.

;;; Sorting is done using using `bmkp-sort-comparer'.
;;; If `bmkp-reverse-sort-p' is non-nil, then reverse the sort order.
;;; Keys are compared for sorting using `equal'.
;;; If optional arg OMIT is non-nil, then omit from the return value any
;;; elements with keys in list OMIT."
;;;   (lexical-let ((new-alist  (bmkp-remove-assoc-dups alist omit))
;;;                (sort-fn  (and bmkp-sort-comparer  (if (and (not (functionp bmkp-sort-comparer))
;;;                                                     (consp bmkp-sort-comparer))
;;;                                                            'bmkp-multi-sort
;;;                                                    bmkp-sort-comparer))))
;;;     (when sort-fn
;;;       (setq new-alist  (sort new-alist (if bmkp-reverse-sort-p
;;;                                            (lambda (a b) (not (funcall sort-fn a b)))
;;;                                          sort-fn))))
;;;     new-alist))

;;; KEEP this simpler version also.  This uses `run-hook-with-args-until-success', but it
;;; does not respect `bmkp-reverse-multi-sort-p'.
;;; (defun bmkp-multi-sort (b1 b2)
;;;   "Try predicates in `bmkp-sort-comparer', in order, until one decides.
;;; See the description of `bmkp-sort-comparer'."
;;;   (let* ((preds   (append (car bmkp-sort-comparer) (cdr bmkp-sort-comparer)))
;;;          (result  (run-hook-with-args-until-success 'preds b1 b2)))
;;;     (if (consp result)
;;;         (car result)
;;;       result)))

;;; $$$$$$ No longer used.
;;; (defun bmkp-remove-assoc-dups (alist &optional omit)
;;;   "Shallow copy of ALIST without elements that have duplicate keys.
;;; Only the first element of those with the same key is kept.
;;; Keys are compared using `equal'.
;;; If optional arg OMIT is non-nil, then omit from the return value any
;;; elements with keys in list OMIT."
;;;   (let ((new  ()))
;;;     (dolist (ii  alist)  (unless (or (assoc (car ii) new) (member (car ii) omit))  (push ii new)))
;;;     (nreverse new)))


;; This Lisp definition respects `bmkp-reverse-multi-sort-p', and can be extended.
(defun bmkp-multi-sort (b1 b2)
  "Try predicates in `bmkp-sort-comparer', in order, until one decides.
See the description of `bmkp-sort-comparer'.
If `bmkp-reverse-multi-sort-p' is non-nil, then reverse the order for
using multi-sorting predicates."
  (let ((preds       (car bmkp-sort-comparer))
        (final-pred  (cadr bmkp-sort-comparer))
        (result      nil))
    (when bmkp-reverse-multi-sort-p (setq preds  (reverse preds)))
    (catch 'bmkp-multi-sort
      (dolist (pred  preds)
        (setq result  (funcall pred b1 b2))
        (when (consp result)
          (when bmkp-reverse-multi-sort-p (setq result  (list (not (car result)))))
          (throw 'bmkp-multi-sort (car result))))
      (and final-pred  (if bmkp-reverse-multi-sort-p
                           (not (funcall final-pred b1 b2))
                         (funcall final-pred b1 b2))))))


;; The description returned is only approximate.  The effect of `bmkp-reverse-multi-sort-p' is not
;; always intuitive, but it can often be useful.  What's not always intuitive is the placement
;; (the order) of bookmarks that are not sorted by the predicates.
;;
(defun bmkp-sorting-description (order)
  "Return a string describing sort ORDER."
  (concat
   (if (and order  bmkp-sort-comparer)
       order
     (concat (and order  (format "(%s) " order)) "turned OFF"))
   (cond ((not bmkp-sort-comparer) nil)
         ((not (and (consp bmkp-sort-comparer)  (consp (car bmkp-sort-comparer)))) ; Ordinary single pred.
          (if bmkp-reverse-sort-p " (REVERSED)" ""))
         ((not (cadr (car bmkp-sort-comparer))) ; Single predicate.
          (if (or (and bmkp-reverse-sort-p  (not bmkp-reverse-multi-sort-p))
                  (and bmkp-reverse-multi-sort-p  (not bmkp-reverse-sort-p)))
              " (REVERSED)"
            "")
          ;; If we wanted to distinguish the two:
          ;; (if (and bmkp-reverse-sort-p  (not bmkp-reverse-multi-sort-p))
          ;;     "; REVERSED"
          ;;   (if (and bmkp-reverse-multi-sort-p  (not bmkp-reverse-sort-p))
          ;;       "; REVERSED +"
          ;;     ""))
          )
         ;; At least two predicates.
         ((and bmkp-reverse-sort-p  (not bmkp-reverse-multi-sort-p)) " (REVERSED)")
         ((and bmkp-reverse-multi-sort-p  (not bmkp-reverse-sort-p)) " (each pred group reversed)")
         ((and bmkp-reverse-multi-sort-p  bmkp-reverse-sort-p)       " (order of pred groups reversed)")
         (t ""))))

(defun bmkp-msg-about-sort-order (order &optional prefix-msg suffix-msg)
  "Display a message mentioning sort ORDER and direction.
Optional arg PREFIX-MSG is prepended to the constructed message, and
terminated with a period.
Similarly, SUFFIX-MSG is appended, after appending \".  \"."
  (let ((msg  (concat "Sorting " (bmkp-sorting-description order))))
    (when prefix-msg (setq msg  (concat prefix-msg ".  " msg)))
    (when suffix-msg (setq msg  (concat msg ".  " suffix-msg)))
    (message msg)))


;;(@* "Sorting - Commands")
;;  *** Sorting - Commands ***

(defun bmkp-current-sort-order ()
  "Current sort order or sort function, as a string, or nil if none."
  (car (rassoc bmkp-sort-comparer bmkp-sort-orders-alist)))


;;(@* "Sorting - General Predicates")
;;  *** Sorting - General Predicates ***

(defun bmkp-flagged-cp (b1 b2)
  "True if bookmark B1 is flagged for deletion and bookmark B2 is not.
Return nil if incomparable as described.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((m1  (bmkp-flagged-bookmark-p b1))
        (m2  (bmkp-flagged-bookmark-p b2)))
    (cond ((and m1 m2)  nil)
          (m1           '(t))
          (m2           '(nil))
          (t            nil))))

(defun bmkp-marked-cp (b1 b2)
  "True if bookmark B1 is marked and bookmark B2 is not.
Return nil if incomparable as described.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((m1  (bmkp-marked-bookmark-p b1))
        (m2  (bmkp-marked-bookmark-p b2)))
    (cond ((and m1 m2)  nil)
          (m1           '(t))
          (m2           '(nil))
          (t            nil))))

(defun bmkp-modified-cp (b1 b2)
  "True if bookmark B1 is modified and bookmark B2 is not.
Return nil if incomparable as described.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((m1  (bmkp-modified-bookmark-p b1))
        (m2  (bmkp-modified-bookmark-p b2)))
    (cond ((and m1 m2)  nil)
          (m1           '(t))
          (m2           '(nil))
          (t            nil))))

(defun bmkp-tagged-cp (b1 b2)
  "True if bookmark B1 is tagged and bookmark B2 is not.
Return nil if incomparable as described.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((m1  (bmkp-tagged-bookmark-p b1))
        (m2  (bmkp-tagged-bookmark-p b2)))
    (cond ((and m1 m2)  nil)
          (m1           '(t))
          (m2           '(nil))
          (t            nil))))

(defun bmkp-visited-more-cp (b1 b2)
  "True if bookmark B1 was visited more often than B2.
Return nil if incomparable as described.

True also if B1 was visited but B2 was not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((v1  (bmkp-get-visits-count b1))
        (v2  (bmkp-get-visits-count b2)))
    (cond ((and v1 v2)
           (cond ((> v1 v2)  '(t))
                 ((> v2 v1)  '(nil))
                 (t          nil)))
          (v1                '(t))
          (v2                '(nil))
          (t                 nil))))

(defun bmkp-bookmark-creation-cp (b1 b2)
  "True if bookmark B1 was created more recently than B2.
Return nil if incomparable as described.

True also if B1 has a `created' entry but B2 has none.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((t1  (bookmark-prop-get b1 'created))
        (t2  (bookmark-prop-get b2 'created)))
    (cond ((and t1 t2)
           (setq t1  (bmkp-float-time t1)
                 t2  (bmkp-float-time t2))
           (cond ((> t1 t2)  '(t))
                 ((> t2 t1)  '(nil))
                 (t          nil)))
          (t1                '(t))
          (t2                '(nil))
          (t                 nil))))

;; Not used currently.
(defun bmkp-same-creation-time-p (b1 b2)
  "Return non-nil if `B1 and B2 have same `created' entry.
If neither has a `created' entry (vanilla bookmarks), then return
non-nil if the full bookmarks are `equal'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (let ((time1  (bookmark-prop-get b1 'created))
        (time2  (bookmark-prop-get b2 'created)))
    (if (or time1  time2) (equal time1 time2) (equal b1 b2))))

(defun bmkp-bookmark-last-access-cp (b1 b2)
  "True if bookmark B1 was visited more recently than B2.
Return nil if incomparable as described.

True also if B1 was visited but B2 was not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((t1  (bmkp-get-visit-time b1))
        (t2  (bmkp-get-visit-time b2)))
    (cond ((and t1 t2)
           (setq t1  (bmkp-float-time t1)
                 t2  (bmkp-float-time t2))
           (cond ((> t1 t2)  '(t))
                 ((> t2 t1)  '(nil))
                 (t          nil)))
          (t1                '(t))
          (t2                '(nil))
          (t                 nil))))

(defun bmkp-buffer-last-access-cp (b1 b2)
  "True if bookmark B1's buffer or file was visited more recently than B2's.
Return nil if incomparable as described.

A bookmark to an existing buffer sorts before a file bookmark, even if
the buffer has not been visited during this session.

True also if B1 has a buffer but B2 does not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((buf1  (bmkp-get-buffer-name b1))
        (buf2  (bmkp-get-buffer-name b2))
        f1 f2 t1 t2)
    (setq buf1  (and buf1  (get-buffer buf1))
          buf2  (and buf2  (get-buffer buf2)))
    (cond ((and buf1 buf2)              ; Both buffers exist.   See whether they were accessed.
           (when buf1 (setq buf1  (member buf1 (buffer-list))
                            buf1  (length buf1)))
           (when buf2 (setq buf2  (member buf2 (buffer-list))
                            buf2  (length buf2)))
           (cond ((and buf1 buf2)       ; Both were accessed.  Priority to most recent access.
                  (cond ((< buf1 buf2)  '(t))
                        ((< buf2 buf1)  '(nil))
                        (t              nil)))
                 (buf1                  '(t)) ; Only buf1 was accessed.
                 (buf2                  '(nil)) ; Only buf2 was accessed.
                 (t                     nil))) ; Neither was accessed.

          (buf1                         '(t)) ; Only buf1 exists.
          (buf2                         '(nil)) ; Only buf2 exists.
          (t                            nil)))) ; Neither buffer exists

;; EWW.  Not used yet.
(when (> emacs-major-version 24)        ; Emacs 25

  (defun bmkp-eww-cp (b1 b2)
    "True if bookmark B1 sorts as an EWW URL bookmark before B2.
Return nil if neither sorts before the other.

Two EWW URL bookmarks are compared alphabetically, by their URLs.
True also if B1 is a EWW bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
    (setq b1  (bookmark-get-bookmark b1)
          b2  (bookmark-get-bookmark b2))
    (let ((e1  (bmkp-eww-bookmark-p b1))
          (e2  (bmkp-eww-bookmark-p b2)))
      (cond ((and e1 e2)
             (setq e1  (bookmark-get-filename b1)
                   e2  (bookmark-get-filename b2))
             (cond ((string-lessp e1 e2)  '(t))
                   ((string-lessp e2 e1)  '(nil))
                   (t                     nil)))
            (e1                           '(t))
            (e2                           '(nil))
            (t                            nil))))

  )

(defun bmkp-handler-cp (b1 b2)
  "True if bookmark B1's handler name sorts alphabetically before B2's.
Return nil if neither sorts before the other.

Two bookmarks with handlers are compared alphabetically, by their
handler-function names, respecting `case-fold-search'.
True also if B1 has a handler but B2 has not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((h1  (bookmark-get-handler b1))
        (h2  (bookmark-get-handler b2)))
    (cond ((and h1 h2 (symbolp h1) (symbolp h2))
           ;; Pretend woman bookmarks are man bookmarks, to keep them together.
           (when (eq h1 'bmkp-jump-woman) (setq h1  'bmkp-jump-man))
           (when (eq h2 'bmkp-jump-woman) (setq h2  'bmkp-jump-man))
           (setq h1  (symbol-name h1)
                 h2  (symbol-name h2))
           (when case-fold-search (setq h1  (bmkp-upcase h1)
                                        h2  (bmkp-upcase h2)))
           (cond ((string-lessp h1 h2)  '(t))
                 ((string-lessp h2 h1)  '(nil))
                 (t                     nil)))
          (h1                           '(t))
          (h2                           '(nil))
          (t                            nil))))

;; Keep the alias for a while, in case someone has it referenced in a state file.
(defalias 'bmkp-info-cp 'bmkp-info-node-name-cp)
(make-obsolete 'bmkp-info-cp 'bmkp-info-node-name-cp)

(defun bmkp-info-node-name-cp (b1 b2)
  "True if bookmark B1 sorts as an Info bookmark before B2.
Return nil if neither sorts before the other.

Two Info bookmarks are compared first by manual name, then by node
name, then by position.

If `bmkp-info-sort-ignores-directories-flag' is non-nil then manual
names are used.  If it is nil then absolute file names for the manuals
are used.

True also if B1 is an Info bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((i1  (bmkp-info-bookmark-p b1))
        (i2  (bmkp-info-bookmark-p b2))
        (fn  (if bmkp-info-sort-ignores-directories-flag #'file-name-nondirectory #'abbreviate-file-name)))
    (cond ((and i1 i2)
           (setq i1  (funcall fn (bookmark-get-filename b1))
                 i2  (funcall fn (bookmark-get-filename b2)))
           (when case-fold-search (setq i1  (bmkp-upcase i1)
                                        i2  (bmkp-upcase i2)))
           (cond ((string-lessp i1 i2)                  '(t)) ; Compare manuals (file names).
                 ((string-lessp i2 i1)                  '(nil))
                 (t                     ; Compare node names.
                  (setq i1  (bookmark-prop-get b1 'info-node)
                        i2  (bookmark-prop-get b2 'info-node))
                  (cond ((string-lessp i1 i2)           '(t))
                        ((string-lessp i2 i1)           '(nil))
                        (t
                         (setq i1  (bookmark-get-position b1)
                               i2  (bookmark-get-position b2))
                         (cond ((or (not i1) (not i2))  '(t)) ; Fallback if no `position' entry.
                               ((<= i1 i2)              '(t))
                               ((< i2 i1)               '(nil))))))))
          (i1                                           '(t))
          (i2                                           '(nil))
          (t                                            nil))))

(defun bmkp-info-position-cp (b1 b2)
  "True if bookmark B1 sorts as Info bookmark before B2 in book order.
Return nil if neither sorts before the other.

Two Info bookmarks are compared first by manual name, then by position
in the file.

If `bmkp-info-sort-ignores-directories-flag' is non-nil then manual
names are used.  If it is nil then absolute file names for the manuals
are used.

True also if B1 is an Info bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((i1  (bmkp-info-bookmark-p b1))
        (i2  (bmkp-info-bookmark-p b2))
        (fn  (if bmkp-info-sort-ignores-directories-flag #'file-name-nondirectory #'abbreviate-file-name)))
    (cond ((and i1 i2)
           (setq i1  (funcall fn (bookmark-get-filename b1))
                 i2  (funcall fn (bookmark-get-filename b2)))
           (when case-fold-search (setq i1  (bmkp-upcase i1)
                                        i2  (bmkp-upcase i2)))
           (cond ((string-lessp i1 i2)                  '(t)) ; Compare manuals (file names).
                 ((string-lessp i2 i1)                  '(nil))
                 (t                     ; Compare positions.
                  (setq i1  (bookmark-get-position b1)
                        i2  (bookmark-get-position b2))
                  (cond ((or (not i1) (not i2))  '(t)) ; Fallback if no `position' entry.
                        ((<= i1 i2)              '(t))
                        ((< i2 i1)               '(nil))))))
          (i1                                           '(t))
          (i2                                           '(nil))
          (t                                            nil))))

(defun bmkp-gnus-cp (b1 b2)
  "True if bookmark B1 sorts as a Gnus bookmark before B2.
Return nil if neither sorts before the other.

Two Gnus bookmarks are compared first by Gnus group name, then by
article number, then by message ID.
True also if B1 is a Gnus bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((g1  (bmkp-gnus-bookmark-p b1))
        (g2  (bmkp-gnus-bookmark-p b2)))
    (cond ((and g1 g2)
           (setq g1  (bookmark-prop-get b1 'group)
                 g2  (bookmark-prop-get b2 'group))
           (cond ((string-lessp g1 g2)                '(t)) ; Compare groups.
                 ((string-lessp g2 g1)                '(nil))
                 (t                     ; Compare article numbers.
                  (setq g1  (bookmark-prop-get b1 'article)
                        g2  (bookmark-prop-get b2 'article))
                  (cond ((< g1 g2)                    '(t))
                        ((< g2 g1)                    '(nil))
                        (t
                         (setq g1  (bookmark-prop-get b1 'message-id)
                               g2  (bookmark-prop-get b2 'message-id))
                         (cond ((string-lessp g1 g2)  '(t)) ; Compare message IDs.
                               ((string-lessp g2 g1)  '(nil))
                               (t                     nil)))))))
          (g1                                         '(t))
          (g2                                         '(nil))
          (t                                          nil))))

(defun bmkp-url-cp (b1 b2)
  "True if bookmark B1 sorts as a URL bookmark before B2.
Return nil if neither sorts before the other.

Two URL bookmarks are compared alphabetically, by their URLs.
True also if B1 is a URL bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((u1  (bmkp-url-bookmark-p b1))
        (u2  (bmkp-url-bookmark-p b2)))
    (cond ((and u1 u2)
           (setq u1  (or (bookmark-prop-get b1 'location) (bookmark-get-filename b1))
                 u2  (or (bookmark-prop-get b2 'location) (bookmark-get-filename b2)))
           (cond ((string-lessp u1 u2)  '(t))
                 ((string-lessp u2 u1)  '(nil))
                 (t                     nil)))
          (u1                           '(t))
          (u2                           '(nil))
          (t                            nil))))

;; Not used now.
(defun bmkp-w3m-cp (b1 b2)
  "True if bookmark B1 sorts as a W3M URL bookmark before B2.
Return nil if neither sorts before the other.

Two W3M URL bookmarks are compared alphabetically, by their URLs.
True also if B1 is a W3M bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((w1  (bmkp-w3m-bookmark-p b1))
        (w2  (bmkp-w3m-bookmark-p b2)))
    (cond ((and w1 w2)
           (setq w1  (bookmark-get-filename b1)
                 w2  (bookmark-get-filename b2))
           (cond ((string-lessp w1 w2)  '(t))
                 ((string-lessp w2 w1)  '(nil))
                 (t                     nil)))
          (w1                           '(t))
          (w2                           '(nil))
          (t                            nil))))

(defun bmkp-position-cp (b1 b2)
  "True if the `position' of B1 is not greater than that of B2.
Return nil if B1 and B2 do not bookmark the same buffer or they have
the same `position' value.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((buf1  (bmkp-get-buffer-name b1))
        (buf2  (bmkp-get-buffer-name b2)))
    (and buf1 buf2 (equal buf1 buf2)
         (let ((i1  (bookmark-get-position b1))
               (i2  (bookmark-get-position b2)))
           (cond ((or (not i1) (not i2))  '(t)) ; Fallback if no `position' entry.
                 ((<= i1 i2)              '(t))
                 ((< i2 i1)               '(nil)))))))

(defun bmkp-alpha-cp (b1 b2)
  "True if bookmark B1's name sorts alphabetically before B2's.
Return nil if neither sorts before the other.

The bookmark names are compared, respecting `case-fold-search'.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((s1  (car b1))
        (s2  (car b2)))
    (when case-fold-search (setq s1  (bmkp-upcase s1)
                                 s2  (bmkp-upcase s2)))
    (cond ((string-lessp s1 s2)  '(t))
          ((string-lessp s2 s1)  '(nil))
          (t                     nil))))

;; Do not use `bmkp-make-plain-predicate', because it falls back on `bookmark-alpha-p'.
;; Return nil if `bookmark-alpha-cp' cannot decide.
(defun bmkp-alpha-p (b1 b2)
  "True if bookmark B1's name sorts alphabetically before B2's.
The bookmark names are compared, respecting `case-fold-search'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (car (bmkp-alpha-cp b1 b2)))


;;(@* "Sorting - File-Name Predicates")
;;  *** Sorting - File-Name Predicates ***

(defun bmkp-file-alpha-cp (b1 b2)
  "True if bookmark B1's file name sorts alphabetically before B2's.
Return nil if neither sorts before the other.

The file names are shortened using `abbreviate-file-name', then they
are compared respecting `case-fold-search'.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((f1  (bmkp-file-bookmark-p b1))
        (f2  (bmkp-file-bookmark-p b2)))
    (cond ((and f1 f2)
           ;; Call `abbreviate-file-name' mainly to get letter case right per platform.
           (setq f1  (abbreviate-file-name (bookmark-get-filename b1))
                 f2  (abbreviate-file-name (bookmark-get-filename b2)))
           (when case-fold-search (setq f1  (bmkp-upcase f1)
                                        f2  (bmkp-upcase f2)))
           (cond ((string-lessp f1 f2)  '(t))
                 ((string-lessp f2 f1)  '(nil))
                 (t                     nil)))
          (f1                           '(t))
          (f2                           '(nil))
          (t                            nil))))

;; We define all file-attribute predicates, in case you want to use them.
;;
;; `bmkp-file-attribute-0-cp'  - type
;; `bmkp-file-attribute-1-cp'  - links
;; `bmkp-file-attribute-2-cp'  - uid
;; `bmkp-file-attribute-3-cp'  - gid
;; `bmkp-file-attribute-4-cp'  - last access time
;; `bmkp-file-attribute-5-cp'  - last update time
;; `bmkp-file-attribute-6-cp'  - last status change
;; `bmkp-file-attribute-7-cp'  - size
;; `bmkp-file-attribute-8-cp'  - modes
;; `bmkp-file-attribute-9-cp'  - gid change
;; `bmkp-file-attribute-10-cp' - inode
;; `bmkp-file-attribute-11-cp' - device
;;
(bmkp-define-file-sort-predicate 0) ; Type: file, symlink, dir
(bmkp-define-file-sort-predicate 1) ; Links
(bmkp-define-file-sort-predicate 2) ; Uid
(bmkp-define-file-sort-predicate 3) ; Gid
(bmkp-define-file-sort-predicate 4) ; Last access time
(bmkp-define-file-sort-predicate 5) ; Last modification time
(bmkp-define-file-sort-predicate 6) ; Last status-change time
(bmkp-define-file-sort-predicate 7) ; Size
(bmkp-define-file-sort-predicate 8) ; Modes
(bmkp-define-file-sort-predicate 9) ; Gid would change if re-created
(bmkp-define-file-sort-predicate 10) ; Inode
(bmkp-define-file-sort-predicate 11) ; Device

(defun bmkp-local-file-accessed-more-recently-cp (b1 b2)
  "True if bookmark B1's local file was accessed more recently than B2's.
Return nil if neither sorts before the other.

A local file sorts before a remote file, which sorts before other
bookmarks.  Two remote files are considered incomparable - their
access times are not examined.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (cond ((and (bmkp-local-file-bookmark-p b1)  (bmkp-local-file-bookmark-p b2))
         (bmkp-cp-not (bmkp-file-attribute-4-cp b1 b2)))
        ((bmkp-local-file-bookmark-p b1)         '(t))
        ((bmkp-local-file-bookmark-p b2)         '(nil))
        ((and (bmkp-remote-file-bookmark-p b1)
              (bmkp-remote-file-bookmark-p b2))  nil)
        ((bmkp-remote-file-bookmark-p b1)        '(t))
        ((bmkp-remote-file-bookmark-p b2)        '(nil))
        (t                                       nil)))

(defun bmkp-local-file-updated-more-recently-cp (b1 b2)
  "True if bookmark B1's local file was updated more recently than B2's.
Return nil if neither sorts before the other.

A local file sorts before a remote file, which sorts before other
bookmarks.  Two remote files are considered incomparable - their
update times are not examined.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (cond ((and (bmkp-local-file-bookmark-p b1)  (bmkp-local-file-bookmark-p b2))
         (bmkp-cp-not (bmkp-file-attribute-5-cp b1 b2)))
        ((bmkp-local-file-bookmark-p b1)         '(t))
        ((bmkp-local-file-bookmark-p b2)         '(nil))
        ((and (bmkp-remote-file-bookmark-p b1)
              (bmkp-remote-file-bookmark-p b2))  nil)
        ((bmkp-remote-file-bookmark-p b1)        '(t))
        ((bmkp-remote-file-bookmark-p b2)        '(nil))
        (t                                       nil)))

(defun bmkp-local-file-size-cp (b1 b2)
  "True if bookmark B1's local file is larger than B2's.
Return nil if neither sorts before the other.

A local file sorts before a remote file, which sorts before other
bookmarks.  Two remote files are considered incomparable - their
sizes are not examined.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (cond ((and (bmkp-local-file-bookmark-p b1)  (bmkp-local-file-bookmark-p b2))
         (bmkp-cp-not (bmkp-file-attribute-7-cp b1 b2)))
        ((bmkp-local-file-bookmark-p b1)         '(t))
        ((bmkp-local-file-bookmark-p b2)         '(nil))
        ((and (bmkp-remote-file-bookmark-p b1)
              (bmkp-remote-file-bookmark-p b2))  nil)
        ((bmkp-remote-file-bookmark-p b1)        '(t))
        ((bmkp-remote-file-bookmark-p b2)        '(nil))
        (t                                       nil)))

(defun bmkp-local-file-type-cp (b1 b2)
  "True if bookmark B1 sorts by local file type before B2.
Return nil if neither sorts before the other.

For two local files, a file sorts before a symlink, which sorts before
a directory.

A local file sorts before a remote file, which sorts before other
bookmarks.  Two remote files are considered incomparable - their file
types are not examined.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.

B1 and B2 are full bookmarks (records) or bookmark names.
If either is a record then it need not belong to `bookmark-alist'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (cond ((and (bmkp-local-file-bookmark-p b1)  (bmkp-local-file-bookmark-p b2))
         (bmkp-file-attribute-0-cp b1 b2))
        ((bmkp-local-file-bookmark-p b1)         '(t))
        ((bmkp-local-file-bookmark-p b2)         '(nil))
        ((and (bmkp-remote-file-bookmark-p b1)
              (bmkp-remote-file-bookmark-p b2))  nil)
        ((bmkp-remote-file-bookmark-p b1)        '(t))
        ((bmkp-remote-file-bookmark-p b2)        '(nil))
        (t                                       nil)))

(defun bmkp-cp-not (truth)
  "Return the negation of boolean value TRUTH.
If TRUTH is (t), return (nil), and vice versa.
If TRUTH is nil, return nil."
  (and truth  (if (car truth) '(nil) '(t))))


;;(@* "Indirect Bookmarking Functions")
;;  *** Indirect Bookmarking Functions ***

;;;###autoload (autoload 'bmkp-url-target-set "bookmark+")
(defun bmkp-url-target-set (url &optional arg name/prefix no-overwrite-p no-refresh-p msg-p)
                                        ; Bound globally to `C-x p c u'.
  "Set a bookmark for a URL.  Return the bookmark.
Interactively you are prompted for the URL.  Completion is available.
Use `M-n' to pick up the url at point as the default.

You are also prompted for the bookmark name.  But with a non-negative
prefix arg, you are prompted only for a bookmark-name prefix.  In that
case, the bookmark name is the prefix followed by the URL.

When entering a bookmark name you can use completion against existing
names.  This completion is lax, so you can easily edit an existing
name.  See `bookmark-set' for particular keys available during this
input.

If you use a numeric prefix arg, such as `C-1', instead of plain
`C-u', then a new bookmark is created if a bookmark of the same name
already exists: an existing bookmark is not overwritten.  You can thus
have multiple bookmarks with the same name, which target different
URLs.

Summary of prefix argument behavior:

* None:        Provide full bookmark name. Overwrite existing bookmark
* Plain `C-u': Provide name prefix only.   Overwrite existing bookmark
* N >= 0:      Provide name prefix only.   Do not overwrite.
* N < 0:       Provide full bookmark name. Do not overwrite.

Non-interactively:
* Numeric ARG >= 0 means NAME/PREFIX is a bookmark-name prefix.
* NAME/PREFIX is the bookmark name or its prefix (the suffix = URL).
* Non-nil NO-OVERWRITE-P means do not overwrite an existing bookmark.
* Non-nil NO-REFRESH-P means do not refresh/rebuild the bookmark-list
  display.
* Non-nil MSG-P means display a status message."
  (interactive
   (let* ((icicle-unpropertize-completion-result-flag  t)
          (default-url                                 (or (bmkp-thing-at-point 'url)
                                                           (and (fboundp 'url-get-url-at-point)
                                                                (url-get-url-at-point))))
          (parg                                        current-prefix-arg)
          (prefix-only                                 (and parg  (natnump (prefix-numeric-value parg))))
          (no-overw                                    (and parg  (atom current-prefix-arg))))
     (list (if (require 'ffap nil t)
               (ffap-read-file-or-url "URL: " default-url)
             (read-file-name "URL: " nil default-url))
           prefix-only
           (if prefix-only
               (read-string "Prefix for bookmark name: ")
             (bmkp-completing-read-lax "Bookmark name"))
           no-overw
           nil
           'MSG)))
  (unless name/prefix (setq name/prefix  ""))
  (let ((bookmark-make-record-function  (cond ((and (eq major-mode 'eww-mode)
                                                    (fboundp 'bmkp-make-eww-record)) ; Emacs 25+
                                               'bmkp-make-eww-record)
                                              ((eq major-mode 'w3m-mode) 'bmkp-make-w3m-record)
                                              (t `(lambda () (bmkp-make-url-browse-record ',url)))))
        bmk failure)
    (condition-case err
        (setq bmk  (bookmark-store (if arg (concat name/prefix url) name/prefix)
                                   (cdr (bookmark-make-record))  no-overwrite-p  no-refresh-p  (not msg-p)))
      (error (setq failure  err)))
    (when failure (error "Failed to create bookmark for `%s':\n%s\n" url failure))
    bmk))                               ; Return the bookmark.

;;;###autoload (autoload 'bmkp-file-target-set "bookmark+")
(defun bmkp-file-target-set (file &optional arg name/prefix no-overwrite no-refresh-p msg-p)
                                        ; Bound to `C-x p c f'
  "Set a bookmark for FILE.  Return the bookmark.
The bookmarked position is the beginning of the file.
Interactively you are prompted for FILE.  Completion is available.
You can use `M-n' to pick up the file name at point, or if none then
the visited file.

You are also prompted for the bookmark name.  But with a non-negative
prefix arg, you are prompted only for a bookmark-name prefix.  In that
case, the bookmark name is the prefix followed by the non-directory
part of FILE.

When entering a bookmark name you can use completion against existing
names.  This completion is lax, so you can easily edit an existing
name.  See `bookmark-set' for particular keys available during this
input.

If you use a numeric prefix arg, such as `C-1', instead of plain
`C-u', then a new bookmark is created if a bookmark of the same name
already exists: an existing bookmark is not overwritten.  You can thus
have multiple bookmarks with the same name, which target different
URLs.

Summary of prefix argument behavior:

* None:        Provide full bookmark name. Overwrite existing bookmark
* Plain `C-u': Provide name prefix only.   Overwrite existing bookmark
* N >= 0:      Provide name prefix only.   Do not overwrite.
* N < 0:       Provide full bookmark name  Do not overwrite.

Non-interactively:
* Numeric ARG >= 0 means NAME/PREFIX is a bookmark-name prefix.
* NAME/PREFIX is the bookmark name or its prefix.
* Non-nil NO-OVERWRITE-P means do not overwrite an existing bookmark.
* Non-nil NO-REFRESH-P means do not refresh/rebuild the bookmark-list
  display.
* Non-nil MSG-P means show a warning message if file does not exist."
  (interactive
   (let* ((icicle-unpropertize-completion-result-flag  t)
          (parg                                        current-prefix-arg)
          (prefix-only                                 (and parg  (natnump (prefix-numeric-value parg))))
          (no-overw                                    (and parg  (atom current-prefix-arg))))
     (list (read-file-name "File: " nil
                           (or (if (boundp 'file-name-at-point-functions) ; In `files.el', Emacs 23.2+.
                                   (run-hook-with-args-until-success 'file-name-at-point-functions)
                                 (bmkp-ffap-guesser))
                               (bmkp-thing-at-point 'filename)
                               (buffer-file-name)))
           prefix-only
           (if prefix-only
               (read-string "Prefix for bookmark name: ")
             (bmkp-completing-read-lax "Bookmark name"))
           no-overw
           nil
           'MSG)))
  (unless name/prefix (setq name/prefix  ""))
  (let ((bookmark-make-record-function  (bmkp-make-record-for-target-file file))
        bmk failure)
    (condition-case err
        (setq bmk  (bookmark-store (if arg
                                       (concat name/prefix (file-name-nondirectory file))
                                     name/prefix)
                                   (cdr (bookmark-make-record))  no-overwrite  no-refresh-p  (not msg-p)))
      (error (setq failure  (error-message-string err))))
    (when failure (error "Failed to create bookmark for `%s':\n%s\n" file failure))
    (unless no-refresh-p (bmkp-refresh/rebuild-menu-list bmk (not msg-p)))
    (when (and msg-p  (not (file-exists-p file)))
      (message "File name is now bookmarked, but no such file yet: `%s'" (expand-file-name file)))
    bmk))                               ; Return the bookmark.

(defun bmkp-make-record-for-target-file (file)
  "Return a function that creates a bookmark record for FILE.
The bookmarked position will be the beginning of the file."
  ;; $$$$$$ Maybe need a way to bypass default handler, at least for autofiles.
  ;;        Doesn't seem to make much sense to use a handler such as a shell cmd in this context. (?)
  (set-text-properties 0 (length file) () file)
  (let ((default-handler  (condition-case nil (bmkp-default-handler-for-file file) (error nil)))
        (common           `((filename     . ,file)
                            (position     . 0)
                            (created      . ,(current-time)))))
    (cond (default-handler              ; User default handler
              `(lambda () ',(append common `((file-handler . ,default-handler)))))
          ;; Non-user defaults.
          ((and (require 'image nil t)  (require 'image-mode nil t) ; Image
                (condition-case nil (image-type file) (error nil)))
           ;; Last two lines of function are from `image-bookmark-make-record'.
           ;; But don't use that directly, because it uses
           ;; `bookmark-make-record-default', which gets nil for `filename'.

           ;; NEED TO KEEP THIS CODE SYNC'D WITH `diredp-bookmark'.
           `(lambda ()
             ',(append common `((image-type . ,(image-type file)) (handler . image-bookmark-jump)))))
          ((let ((case-fold-search  t))  (bmkp-string-match-p "\\([.]au$\\|[.]wav$\\)" file)) ; Sound
           ;; Obsolete: `(lambda () '((filename . ,file) (handler . bmkp-sound-jump))))
           `(lambda () ',(append common '((file-handler . play-sound-file)))))
          (t
           `(lambda () ',common)))))

(when (fboundp 'file-cache-add-file)
  (defadvice file-cache-add-file (around bmkp-autofile-filecache activate)
    "Respect option `bmkp-autofile-filecache'."
    (cond ((eq bmkp-autofile-filecache  'autofile-only)
           (bmkp-autofile-set
            (ad-get-arg 0) nil nil
            'NO-REFRESH-P))
          ((eq bmkp-autofile-filecache  'autofile+cache)
           (progn
             ad-do-it
             (bmkp-autofile-set
              (ad-get-arg 0) nil nil
              'NO-REFRESH-P 'MSG-P)))
          ((eq bmkp-autofile-filecache  'cache-only)
           ad-do-it))))

(defun bmkp-find-file-invoke-bookmark-if-autofile ()
  "Invoke the autofile bookmark associated with the visited file.
This is added to `find-file-hook' when option
`bmkp-autofile-access-invokes-bookmark-flag' is non-nil.  When invoked
it causes regular file access to invoke the associated bookmark.  This
has the effect of updating the bookmark data, such as the number of
visits."
  (let* ((buf-file  (buffer-file-name))
         (bmk       (bmkp-get-bookmark-in-alist (file-name-nondirectory buf-file)
                                                t
                                                (bmkp-autofile-alist-only)))
         (bmk-file  (and bmk  (bookmark-get-filename bmk))))
    (when (and bmk-file  (bmkp-same-file-p buf-file bmk-file))
      (let ((bmkp-autofile-access-invokes-bookmark-flag  nil)) ; Just to be sure.
        (bookmark--jump-via bmk 'ignore)))))

;;;###autoload (autoload 'bmkp-bookmark-a-file "bookmark+")
(defalias 'bmkp-bookmark-a-file 'bmkp-autofile-set)
;;;###autoload (autoload 'bmkp-autofile-set "bookmark+")
(defun bmkp-autofile-set (file &optional dir prefix no-refresh-p msg-p) ; Bound to `C-x p c a'
  "Set a bookmark for FILE, autonaming the bookmark for the file.
Return the bookmark.
Interactively, you are prompted for FILE.  You can use `M-n' to pick
up the file name at point or the visited file.

The bookmark name is the non-directory part of FILE, but with a prefix
arg you are also prompted for a PREFIX string to prepend to the
bookmark name.  The bookmarked position is the beginning of the file.

Note that if you provide PREFIX then the bookmark will not satisfy
`bmkp-autofile-bookmark-p' unless you provide the same PREFIX to that
predicate.

The bookmark's file name is FILE if absolute.  If relative then it is
FILE expanded in DIR, if non-nil, or in the current directory
\(`default-directory').

If a bookmark with the same name already exists for the same file name
then do nothing.

Otherwise, create a new bookmark for the file, even if a bookmark with
the same name already exists.  This means that you can have more than
one autofile bookmark with the same bookmark name and the same
relative file name (non-directory part), but with different absolute
file names.

Non-interactively:
 - Non-nil NO-REFRESH-P means do not refresh/rebuild the bookmark-list
   display.
 - Non-nil optional arg MSG-P means display status messages."
  (interactive
   (list (let ((icicle-unpropertize-completion-result-flag  t))
           (read-file-name "File: " nil
                           (if (or (> emacs-major-version 23)
                                   (and (= emacs-major-version 23)  (> emacs-minor-version 1)))
                               (let ((deflts  ())
                                     def)
                                 (when (setq def  (buffer-file-name)) (push def deflts))
                                 (when (setq def  (bmkp-thing-at-point 'filename)) (push def deflts))
                                 (when (setq def  (bmkp-ffap-guesser)) (push def deflts))
                                 (when (and (boundp 'file-name-at-point-functions)
                                            (setq def  (run-hook-with-args-until-success
                                                        'file-name-at-point-functions)))
                                   (push def deflts))
                                 deflts)
                             (or (if (boundp 'file-name-at-point-functions) ; In `files.el', Emacs 23.2+.
                                     (run-hook-with-args-until-success 'file-name-at-point-functions)
                                   (bmkp-ffap-guesser))
                                 (bmkp-thing-at-point 'filename)
                                 (buffer-file-name)))))
         nil
         (and current-prefix-arg  (read-string "Prefix for bookmark name: "))
         nil
         'MSG))
  (let* ((dir-to-use  (if (file-name-absolute-p file)
                          (file-name-directory file)
                        (or dir default-directory)))
         ;; Look for existing bookmark with same name, same file, in `dir-to-use'.
         (bmk         (bmkp-get-autofile-bookmark file dir-to-use prefix)))
    ;; If BMK was found, then instead of doing nothing we could replace the existing BMK with a new
    ;; one, as follows:
    ;; (let ((bookmark-make-record-function (bmkp-make-record-for-target-file file)))
    ;;   (bmkp-replace-existing-bookmark bmk)) ; Update the existing bookmark.
    (if (not bmk)
        ;; Create a new bookmark, and return it.
        (bmkp-file-target-set (expand-file-name file dir-to-use) t prefix 'NO-OVERWRITE no-refresh-p msg-p)
      (when msg-p (message "Autofile bookmark set for `%s'" file))
      bmk)))                            ; Return the bookmark.

(defun bmkp-get-autofile-bookmark (file &optional dir prefix)
  "Return an existing autofile bookmark for FILE, or nil if there is none.
The bookmark name is the non-directory part of FILE, but if PREFIX is
non-nil then it is PREFIX prepended to the non-directory part of FILE.

The directory part of entry `filename' is the directory part of FILE,
if FILE is absolute.  Otherwise, it is DIR, if non-nil, or
`default-directory' otherwise.

FILE and the `filename' entry of the bookmark returned are the same,
except possibly for their directory parts (see previous)."
  (let* ((fname       (file-name-nondirectory file))
         (bname       (if prefix (concat prefix fname) fname))
         (dir-to-use  (if (file-name-absolute-p file)
                          (file-name-directory file)
                        (or dir default-directory))))
    ;; Look for existing bookmark with same name, same file, in `dir-to-use'.
    (catch 'bmkp-get-autofile-bookmark
      (dolist (bmk  bookmark-alist)
        (when (string= bname (bmkp-bookmark-name-from-record bmk))
          (let* ((bfil  (bookmark-get-filename bmk))
                 (bdir  (and bfil  (file-name-directory bfil))))
            (when (and bfil  bdir  (bmkp-same-file-p bdir  dir-to-use)  (bmkp-same-file-p bfil file))
              (throw 'bmkp-get-autofile-bookmark bmk))))) ; Return the bookmark.
      nil)))

;;;###autoload (autoload 'bmkp-tag-a-file "bookmark+")
(defalias 'bmkp-tag-a-file 'bmkp-autofile-add-tags) ; Bound to `C-x p t + a'
;;;###autoload (autoload 'bmkp-autofile-add-tags "bookmark+")
(defun bmkp-autofile-add-tags (file tags &optional dir prefix no-update-p msg-p)
  "Add TAGS to the autofile bookmark for FILE.
Return the number of tags added.

If there is no autofile bookmark for FILE, create one.
Interactively, you are prompted for FILE and then TAGS.
When prompted for FILE you can use `M-n' to pick up the file name at
point, or if none then the visited file.

With a non-negative prefix argument, you are prompted for a file-name
prefix, as in `bmkp-autofile-set'.

When prompted for tags, hit `RET' to enter each tag, then hit `RET'
again after the last tag.  You can use completion to enter each tag.
Completion is lax: you are not limited to existing tags.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a non-positive prefix argument if you want to refresh them.

Non-interactively:
 - TAGS is a list of strings.
 - DIR and PREFIX are as for `bmkp-autofile-set'.
 - Non-nil NO-UPDATE-P means do not update `bmkp-tags-alist', do not
   update the modification count and maybe save bookmarks, and do not
   refresh/rebuild the bookmark-list display
 - Non-nil MSG-P means display a message about the addition."
  (interactive
   (list (let ((icicle-unpropertize-completion-result-flag  t))
           (read-file-name "File: " nil
                           (or (if (boundp 'file-name-at-point-functions) ; In `files.el', Emacs 23.2+.
                                   (run-hook-with-args-until-success 'file-name-at-point-functions)
                                 (bmkp-ffap-guesser))
                               (bmkp-thing-at-point 'filename)
                               (buffer-file-name))))
         (bmkp-read-tags-completing nil nil (and current-prefix-arg
                                                 (<= (prefix-numeric-value current-prefix-arg) 0)))
         nil
         (and current-prefix-arg  (wholenump (prefix-numeric-value current-prefix-arg))
              (read-string "Prefix for bookmark name: "))
         nil
         'MSG))
  (bmkp-add-tags (bmkp-autofile-set file dir prefix no-update-p) tags no-update-p msg-p))

;;;###autoload (autoload 'bmkp-untag-a-file "bookmark+")
(defalias 'bmkp-untag-a-file 'bmkp-autofile-remove-tags) ; Bound to `C-x p t - a'
;;;###autoload (autoload 'bmkp-autofile-remove-tags "bookmark+")
(defun bmkp-autofile-remove-tags (file tags &optional dir prefix no-update-p msg-p)
  "Remove TAGS from autofile bookmark for FILE.
Return the number of tags removed.

Interactively, you are prompted for TAGS and then FILE.
With Emacs 22 and later, only files with at least one of the given
tags are candidates.

When prompted for FILE you can use `M-n' to pick up the file name at
point, or if none then the visited file.

With a non-negative prefix argument, you are prompted for a file-name
prefix, as in `bmkp-autofile-set'.


When prompted for tags, hit `RET' to enter each tag to be removed,
then hit `RET' again after the last tag.  You can use completion to
enter each tag.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a non-positive prefix argument if you want to refresh them.

Non-interactively:
 - TAGS is a list of strings.
 - DIR and PREFIX are as for `bmkp-autofile-set'.
 - Non-nil NO-UPDATE-P means do not update `bmkp-tags-alist', do not
   update the modification count and maybe save bookmarks, and do not
   refresh/rebuild the bookmark-list display
 - Non-nil MSG-P means display a message about the removal."
  (interactive
   (lexical-let* ((pref
                   (and current-prefix-arg  (wholenump (prefix-numeric-value current-prefix-arg))
                        (read-string "Prefix for bookmark name: ")))
                  (tgs
                   (bmkp-read-tags-completing nil nil (and current-prefix-arg
                                                           (<= (prefix-numeric-value current-prefix-arg) 0))))
                  (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
                  (fil   (condition-case nil
                             (read-file-name
                              "File: " nil
                              (or (if (boundp 'file-name-at-point-functions) ; In `files.el', Emacs 23.2+.
                                      (run-hook-with-args-until-success 'file-name-at-point-functions)
                                    (bmkp-ffap-guesser))
                                  (bmkp-thing-at-point 'filename)
                                  (buffer-file-name))
                              t nil (lambda (ff) ; PREDICATE - only for Emacs 22+.
                                      (let* ((bmk   (bmkp-get-autofile-bookmark ff nil pref))
                                             (btgs  (and bmk  (bmkp-get-tags bmk))))
                                        (and btgs  (catch 'bmkp-autofile-remove-tags-pred
                                                     (dolist (tag  tgs)
                                                       (when (not (member tag btgs))
                                                         (throw 'bmkp-autofile-remove-tags-pred nil)))
                                                     t)))))
                           (error (read-file-name "File: " nil (or (bmkp-ffap-guesser)
                                                                   (bmkp-thing-at-point 'filename)
                                                                   (buffer-file-name)))))))
     (list fil tgs nil pref nil 'MSG)))
  (bmkp-remove-tags (bmkp-autofile-set file dir prefix no-update-p) tags no-update-p msg-p))

;;;###autoload (autoload 'bmkp-purge-notags-autofiles "bookmark+")
(defun bmkp-purge-notags-autofiles (&optional prefix msg-p) ; Not bound to a key by default
  "Delete all autofile bookmarks that have no tags.
With a prefix arg, you are prompted for a PREFIX for the bookmark name.
Non-interactively, non-nil MSG-P means display a status message."
  (interactive (if (not (y-or-n-p "Delete all autofile bookmarks that do not have tags? "))
                   (error "OK - deletion canceled")
                 (list (and current-prefix-arg  (read-string "Prefix for bookmark name: ")) 'MSG)))
  (let ((bmks                (bmkp-autofile-alist-only prefix))
        (bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                  bookmark-save-flag)) ; Save only after `dolist'.
        record tags)
    ;; Needs Bookmark+ version of `bookmark-delete', which accepts a bookmark, not just its name.
    (dolist (bmk  bmks)
      (when (and (setq tags  (assq 'tags (bmkp-bookmark-data-from-record bmk)))
                 (or (not tags) (null (cdr tags))))
        (bookmark-delete bmk 'BATCHP)))) ; Do not refresh list here - do it after iterate.
  (bmkp-tags-list)                      ; Update the tags cache now, after iterate.
  (bmkp-maybe-save-bookmarks)           ; Increments `bookmark-alist-modification-count'.
  (bmkp-refresh/rebuild-menu-list nil (not msg-p))) ; Refresh now, after iterate.


;; $$$$$$ Not used currently.
(defun bmkp-replace-existing-bookmark (bookmark)
  "Replace existing BOOKMARK with a new one of the same name.
Return the new bookmark.
BOOKMARK is a full bookmark record, not a bookmark name.

This replaces the existing bookmark data with the data for a new
bookmark, based on `bookmark-make-record-function'.  It also updates
the `bmkp-full-record' on the bookmark name (without otherwise
changing the name)."
  (let (failure)
    (condition-case err
        (progn                          ; Code similar to `bookmark-store'.
          (setcdr bookmark (cdr (bookmark-make-record)))
          (bmkp-maybe-save-bookmarks)
          ;; Put the full bookmark on its name as property `bmkp-full-record'.
          ;; Do this regardless of Emacs version and `bmkp-propertize-bookmark-names-flag'.
          ;; If it needs to be stripped, that will be done when saving.
          (let ((bname  (bmkp-bookmark-name-from-record bookmark)))
            (put-text-property 0 (length bname) 'bmkp-full-record bookmark bname)
            ;; This is the same as `add-to-list' with `EQ' (not available for Emacs 20-21).
            (unless (memq bookmark bmkp-modified-bookmarks)
              (setq bmkp-modified-bookmarks  (cons bookmark bmkp-modified-bookmarks)))
            (setq bookmark-current-bookmark  bname))
          (bookmark-bmenu-surreptitiously-rebuild-list 'NO-MSG-P))
      (error (setq failure  (error-message-string err))))
    (if (not failure)
        bookmark                        ; Return the bookmark.
      (error "Failed to update bookmark `%s':\n%s\n"
             (bmkp-bookmark-name-from-record bookmark) failure))))

(defun bmkp-default-handler-for-file (filename)
  "Return a default bookmark handler for FILENAME, or nil.
If non-nil, it is a Lisp function, determined as follows:

1. Match FILENAME against `bmkp-default-handlers-for-file-types'.  If
it matches a Lisp function, return that function.  If it matches a
shell command, return a Lisp function that invokes that shell command.

2. If no match is found and `bmkp-guess-default-handler-for-file-flag'
is non-nil, then try to find an appropriate shell command using, in
order, `dired-guess-default' and `mailcap-file-default-commands'
\(Emacs 23+ only).  If a match is found then return a Lisp function
that invokes that shell command."
  (let* ((bmkp-user  (bmkp-default-handler-user filename))
         (shell-cmd  (if (stringp bmkp-user)
                         bmkp-user
                       (and (not bmkp-user)
                            bmkp-guess-default-handler-for-file-flag
                            (or (and (require 'dired-x nil t)
                                     (let* ((case-fold-search
                                             (or (and (boundp 'dired-guess-shell-case-fold-search)
                                                      dired-guess-shell-case-fold-search)
                                                 case-fold-search))
                                            (default  (dired-guess-default (list filename))))
                                       (if (consp default) (car default) default)))
                                (and (require 'mailcap nil t) ; Emacs 23+
                                     (car (mailcap-file-default-commands (list filename)))))))))
    (cond ((stringp shell-cmd) `(lambda (bmk) (dired-do-shell-command ',shell-cmd nil ',(list filename))))
          ((or (functionp bmkp-user)  (and bmkp-user  (symbolp bmkp-user)))
           bmkp-user)
          (t nil))))

(defun bmkp-default-handler-user (filename)
  "Return default handler for FILENAME.
The value is based on `bmkp-default-handlers-for-file-types'."
  (catch 'bmkp-default-handler-user
    (dolist (assn  bmkp-default-handlers-for-file-types)
      (when (bmkp-string-match-p (car assn) filename) (throw 'bmkp-default-handler-user (cdr assn))))
    nil))

;; Keep this only for compatibility with existing bookmarks that have `bmkp-sound-jump' as `handler' prop.
(defun bmkp-sound-jump (bookmark)
  "Handler for sound files: play the sound file that is BOOKMARK's file.
This is deprecated.  It is kept only for old bookmarks that already
use this as the `handler' entry.  New sound bookmarks use
`play-sound-file' as entry `file-handler'."
  (play-sound-file (bookmark-get-filename bookmark)))

(when (> emacs-major-version 21)
  (defun bmkp-compilation-target-set (&optional prefix) ; Bound to `C-c C-b' in compilation mode
    "Set a bookmark at the start of the line for this compilation hit.
The bookmark is set in the indicated file at the indicated line.
You are prompted for the bookmark name.  But with a prefix arg, you
are prompted only for a PREFIX string.  In that case, and in Lisp
code, the bookmark name is PREFIX followed by the (relative) file name
of the hit, followed by the line number of the hit."
    (interactive "P")
    (let* ((file+line  (bmkp-compilation-file+line-at (line-beginning-position)))
           (file       (car file+line))
           (line       (cdr file+line)))
      (unless (and file  line)  (error "Cursor is not on a compilation hit"))
      (save-excursion
        (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect file))
          (goto-char (point-min)) (forward-line (1- line))
          (if (not prefix)
              (call-interactively #'bookmark-set)
            (when (interactive-p)
              (setq prefix  (read-string "Prefix for bookmark name: ")))
            (unless (stringp prefix) (setq prefix  ""))
            (bookmark-set (format "%s%s, line %s" prefix (file-name-nondirectory file) line)
                          99 'INTERACTIVEP))))))

  (defun bmkp-compilation-file+line-at (&optional pos)
    "Return the file and position indicated by this compilation message.
These are returned as a cons: (FILE . POSITION).
POSITION is the beginning of the line indicated by the message."
    (unless pos (setq pos  (point)))
    (let* ((loc        (car (get-text-property pos 'message)))
           (line       (cadr loc))
           (filename   (caar (nth 2 loc)))
           (directory  (cadr (car (nth 2 loc))))
           (spec-dir   (if directory (expand-file-name directory) default-directory)))
      (cons (expand-file-name filename spec-dir) line))))

(when (> emacs-major-version 21)
  (defun bmkp-compilation-target-set-all (prefix &optional msg-p) ; Bound to `C-c C-M-b' in compilation mode
    "Set a bookmark for each hit of a compilation buffer.
NOTE: You can use `C-x C-q' to make the buffer writable and then
      remove any hits that you do not want to bookmark.  Only the hits
      remaining in the buffer are bookmarked.

Interactively, you are prompted for a PREFIX string to prepend to each
bookmark name, the rest of which is the file name of the hit followed
by its line number.
Non-interactively, non-nil optional arg MSG-P means prompt and display
status messages."
    (interactive (list (read-string "Prefix for bookmark name: ") 'MSG))
    (when (and msg-p  (not (y-or-n-p "This will bookmark *EACH* hit in the buffer.  Continue? ")))
      (error "OK - canceled"))
    (let ((count  0))
      (save-excursion
        (goto-char (point-min))
        (when (get-text-property (point) 'message) ; Visible part of buffer starts with a hit
          (condition-case nil           ; because buffer is narrowed or header text otherwise removed.
              (bmkp-compilation-target-set prefix) ; Ignore error here (e.g. killed buffer).
            (error nil))
          (setq count  (1+ count)))
        (while (and (condition-case nil (progn (compilation-next-error 1) t) (error nil))
                    (not (eobp)))
          (condition-case nil
              (bmkp-compilation-target-set prefix) ; Ignore error here (e.g. killed buffer).
            (error nil))
          (setq count  (1+ count)))
        (when msg-p (message "Set %d bookmarks" count))))))


;; We could make the `occur' code work for Emacs 20 & 21 also, but you would not be able to
;; delete some occurrences and bookmark only the remaining ones.

(when (> emacs-major-version 21)
  (defun bmkp-occur-target-set (&optional prefix) ; Bound to `C-c C-b' in Occur mode
    "Set a bookmark at the start of the line for this `(multi-)occur' hit.
You are prompted for the bookmark name.  But with a prefix arg, you
are prompted only for a PREFIX string.  In that case, and in Lisp
code, the bookmark name is PREFIX followed by the buffer name of the
hit, followed by the line number of the hit.

You can use this only in `Occur' mode (commands such as `occur' and
`multi-occur')."
    (interactive "P")
    (unless (eq major-mode 'occur-mode) (error "You must be in `occur-mode'"))
    (let* ((line  (and prefix
                       (save-excursion
                         (forward-line 0)
                         ;; We could use [: ] here, to handle `moccur', but that loses anyway for
                         ;; `occur-mode-find-occurrence', so we would need other hoops too.
                         (re-search-forward "^\\s-+\\([0-9]+\\):" (line-end-position) 'NOERROR)
                         (or (format "%5d" (string-to-number (match-string 1))) ""))))
           (mkr   (occur-mode-find-occurrence))
           (buf   (marker-buffer mkr)))
      (save-excursion (with-current-buffer buf
                        (goto-char mkr)
                        (if (not prefix)
                            (call-interactively #'bookmark-set)
                          (when (interactive-p)
                            (setq prefix  (read-string "Prefix for bookmark name: ")))
                          (unless (stringp prefix) (setq prefix  ""))
                          (bookmark-set (format "%s%s, line %s" prefix buf line) 99 'INTERACTIVEP)))))))

(when (> emacs-major-version 21)
  (defun bmkp-occur-target-set-all (&optional prefix msg-p) ; Bound to `C-c C-M-b' in Occur mode
    "Set a bookmark for each hit of a `(multi-)occur' buffer.
NOTE: You can use `C-x C-q' to make the buffer writable and then
      remove any hits that you do not want to bookmark.  Only the hits
      remaining in the buffer are bookmarked.

Interactively, you are prompted for a PREFIX string to prepend to each
bookmark name, the rest of which is the buffer name of the hit
followed by its line number.

You can use this only in `Occur' mode (commands such as `occur' and
`multi-occur').

See also command `bmkp-occur-create-autonamed-bookmarks', which
creates autonamed bookmarks to all `occur' and `multi-occur' hits.

Non-interactively, non-nil MSG-P means prompt and show status
messages."
    (interactive (list (read-string "Prefix for bookmark name: ") 'MSG))
    (when (and msg-p  (not (y-or-n-p "This will bookmark *EACH* hit in the buffer.  Continue? ")))
      (error "OK - canceled"))
    (let ((count  0))
      (save-excursion
        (goto-char (point-min))
        (while (condition-case nil
                   (progn (occur-next) t) ; "No more matches" ends loop.
                 (error nil))
          (condition-case nil
              (bmkp-occur-target-set prefix) ; Ignore error here (e.g. killed buffer).
            (error nil))
          (setq count  (1+ count)))
        (when msg-p (message "Set %d bookmarks" count))))))


;;(@* "Bookmark Links")
;;  *** Bookmark Links ***

(when (> emacs-major-version 21)

  (defun bmkp-bookmark-linked-at (&optional position msgp)
    "Return the bookmark linked at POSITION (default: point), or nil if none."
    (interactive "d\np")
    (unless position (setq position  (point)))
    (let ((bmk  (get-text-property position 'bmkp-bookmark)))
      (prog1 bmk (when msgp (if bmk (bmkp-describe-bookmark bmk) (message "No bookmark here"))))))

  (defun bmkp-bookmark-linked-at-mouse (event)
    "Return the bookmark linked at the mouse position."
    (interactive "e")
    (bmkp-bookmark-linked-at (posn-point (event-end event)) 'MSG))

  (defun bmkp-jump-to-bookmark-linked-at (&optional position)
    "Jump to the bookmark linked at POSITION (default: point).
If a bookmark is linked at POSITION then jump to it.  Else raise an error."
    (interactive "d")
    (let ((bmk  (bmkp-bookmark-linked-at position)))
      (unless bmk (error "No bookmark here"))
      (bookmark-jump-other-window bmk)))

  (defun bmkp-jump-to-bookmark-linked-at-mouse (event)
    "Jump to the bookmark linked at the mouse position."
    (interactive "e")
    (bmkp-jump-to-bookmark-linked-at (posn-point (event-end event))))

  (defun bmkp-insert-bookmark-link (bookmark text &optional position)
    "Put a link to BOOKMARK on the active region or at point.
You are prompted for the bookmark name.
If the region is active and nonempty then put the link on its text.

Otherwise, you are prompted for the link text, which is inserted at
point.  The default text for this is the BOOKMARK name.  An unlinked
`SPC' char is inserted after the link, unless it is at the end of a
line.

Using `?' or double-clicking `mouse-1' on the link describes the
BOOKMARK.  Using `RET' or `mouse-2' on it jumps to BOOKMARK in another
window.

BOOKMARK is a bookmark name or a bookmark record.

Non-interactively, if the region is inactive or empty then TEXT is the
link text, and it is inserted at POSITION (point if POSITION is nil)."
    (interactive
     (let* ((bmk  (bookmark-completing-read "Bookmark"))
            (txt  (if (and transient-mark-mode  mark-active  (> (region-end) (region-beginning)))
                      (buffer-substring-no-properties (region-end) (region-beginning))
                    (read-string "Insert text: " nil nil bmk))))
       (list bmk txt)))
    (with-buffer-modified-unmodified
        (let* ((regionp  (and transient-mark-mode  mark-active  (> (region-end) (region-beginning))))
               (beg      (if regionp (region-beginning) (or position  (point))))
               (end      (and regionp  (region-end)))
               (bmk      (bookmark-get-bookmark bookmark))
               (map      (make-sparse-keymap)))
          (unless bmk (error "No such bookmark"))
          ;; Use `copy-sequence'.  The bookmark name in the bookmark might change.
          (setq bookmark  (copy-sequence (bmkp-bookmark-name-from-record bmk)))
          (put-text-property 0 (length bookmark) 'bmkp-bookmark bmk bookmark)
          (define-key map "?"              'bmkp-bookmark-linked-at)
          (define-key map "\r"             'bmkp-jump-to-bookmark-linked-at)
          (define-key map [double-mouse-1] 'bmkp-bookmark-linked-at-mouse)
          (define-key map [mouse-2]        'bmkp-jump-to-bookmark-linked-at-mouse)
          (define-key map [follow-link]    'mouse-face)
          (unless regionp (insert text))
          (add-text-properties beg (or end  (point))
                               `(bmkp-bookmark     ,bookmark
                                 keymap            ,map
                                 font-lock-ignore  t ; Prevent font-lock from changing the face.
                                 face              link
                                 mouse-face        highlight
                                 help-echo
                                 "RET, mouse-2: jump to bookmark; ?, double-mouse-1: describe bookmark"))
          (unless (or regionp  (eolp)) (insert " ")))))

  )


;;(@* "Other Bookmark+ Functions (`bmkp-*')")
;;  *** Other Bookmark+ Functions (`bmkp-*') ***

;;;###autoload (autoload 'bmkp-describe-bookmark "bookmark+")
(defun bmkp-describe-bookmark (bookmark &optional defn) ; Bound to `C-x p ?'
  "Describe BOOKMARK.
With a prefix argument, show the internal definition of the bookmark.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'.

Starting with Emacs 22, if the file is an image file then:
* Show a thumbnail of the image as well.
* If you have command-line tool `exiftool' installed and in your
  `$PATH' or `exec-path', then show EXIF data (metadata) about the
  image.  See standard Emacs library `image-dired.el' for more
  information about `exiftool'"
  (interactive (list (bookmark-completing-read "Describe bookmark"
                                               (or (and (fboundp 'bmkp-default-lighted)
                                                        (bmkp-default-lighted))
                                                   (bmkp-default-bookmark-name)))
                     current-prefix-arg))
  (if defn
      (bmkp-describe-bookmark-internals bookmark)
    (setq bookmark  (bookmark-get-bookmark bookmark))
    (help-setup-xref (list #'bmkp-describe-bookmark bookmark) (interactive-p))
    (let ((help-text  (bmkp-bookmark-description bookmark)))
      (bmkp-with-help-window "*Help*" (princ help-text))
      (with-current-buffer "*Help*"
        (save-excursion
          (goto-char (point-min))
          (when (re-search-forward "@#%&()_IMAGE-HERE_()&%#@\\(.+\\)" nil t)
            (let* ((image-file        (match-string 1))
                   (image-string      (save-match-data
                                        (apply #'propertize "X"
                                               `(display
                                                 ,(append (image-dired-get-thumbnail-image image-file)
                                                          '(:margin 10))
                                                 rear-nonsticky (display)
                                                 mouse-face highlight
                                                 follow-link t
                                                 help-echo "`mouse-2' or `RET': Show full image"
                                                 keymap
                                                 (keymap
                                                  (mouse-2
                                                   . (lambda (e) (interactive "e")
                                                             (find-file ,image-file)))
                                                  (13
                                                   . (lambda () (interactive)
                                                             (find-file ,image-file))))))))
                   (buffer-read-only  nil))
              (replace-match image-string)))))
      help-text)))

(defun bmkp-bookmark-description (bookmark &optional no-image)
  "Help-text description of BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'.

Starting with Emacs 22 and unless optional arg NO-IMAGE is non-nil, if
the file is an image file then the description includes the following:
* A placeholder for a thumbnail image: \"@#%&()_IMAGE-HERE_()&%#@\"
* EXIF data (metadata) about the image, provided you have command-line
  tool `exiftool' installed and in your `$PATH' or `exec-path'.  See
  standard Emacs library `image-dired.el' for more information about
  `exiftool'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (let ((print-circle     bmkp-propertize-bookmark-names-flag) ; For `pp-to-string'
        (print-length     nil)          ; For `pp-to-string'
        (print-level      nil)          ; For `pp-to-string'
        (bname            (bmkp-bookmark-name-from-record bookmark))
        (buf              (bmkp-get-buffer-name bookmark))
        (file             (bookmark-get-filename bookmark))
        (image-p          (bmkp-image-bookmark-p bookmark))
        (location         (bookmark-prop-get bookmark 'location))
        (start            (bookmark-get-position bookmark))
        (end              (bmkp-get-end-position bookmark))
        (created          (bookmark-prop-get bookmark 'created))
        (time             (bmkp-get-visit-time bookmark))
        (visits           (bmkp-get-visits-count bookmark))
        (tags             (mapcar #'bmkp-tag-name (bmkp-get-tags bookmark)))
        (sequence-p       (bmkp-sequence-bookmark-p bookmark))
        (function-p       (bmkp-function-bookmark-p bookmark))
        (kmacro-p         (bmkp-kmacro-list-bookmark-p bookmark))
        (variable-list-p  (bmkp-variable-list-bookmark-p bookmark))
        (search-hits-p    (bmkp-icicles-search-hits-bookmark-p bookmark))
        (non-invokable-p  (bmkp-non-invokable-bookmark-p bookmark))
        (desktop-p        (bmkp-desktop-bookmark-p bookmark))
        (bookmark-file-p  (bmkp-bookmark-file-bookmark-p bookmark))
        (snippet-p        (bmkp-snippet-bookmark-p bookmark))
        (dired-p          (bmkp-dired-bookmark-p bookmark))
        (gnus-p           (bmkp-gnus-bookmark-p bookmark))
        (info-p           (bmkp-info-bookmark-p bookmark))
        (man-p            (bmkp-man-bookmark-p bookmark))
        (url-p            (bmkp-url-bookmark-p bookmark))
        (eww-p            (and (fboundp 'bmkp-eww-bookmark-p)  (bmkp-eww-bookmark-p bookmark))) ; Emacs 25+
        (w3m-p            (bmkp-w3m-bookmark-p bookmark))
        (temp-p           (bmkp-temporary-bookmark-p bookmark))
        (annot            (bookmark-get-annotation bookmark))
        non-file-p no-position-p)
    (setq non-file-p     (equal file bmkp-non-file-filename)
          no-position-p  (not start))
    (when (or sequence-p  function-p  variable-list-p  kmacro-p  search-hits-p) (setq no-position-p  t))
    (let* ((temp-text  (if temp-p "TEMPORARY " ""))
           (help-text
            (concat
             (format "%sBookmark `%s'\n%s\n\n" temp-text bname
                     (make-string (+ 11 (length temp-text) (length bname)) ?-))
             (cond (sequence-p       (concat "Sequence:\n\t"
                                             (mapconcat (lambda (bname)
                                                          (let ((name  (copy-sequence bname)))
                                                            (set-text-properties 0 (length name) () name)
                                                            name))
                                                        (bookmark-prop-get bookmark 'sequence)
                                                        "\n\t")
                                             "\n"))
                   (function-p       (let ((fn            (bookmark-prop-get bookmark 'function)))
                                       (if (symbolp fn)
                                           (format "Function:\t\t%s\n" fn)
                                         (format "Function:\n%s\n"
                                                 (pp-to-string (bookmark-prop-get bookmark 'function))))))
                   (kmacro-p         (format "Keyboard Macro List (MACRO COUNT COUNT-FORMAT):\n\n%s\n"
                                             (pp-to-string (bookmark-prop-get bookmark 'kmacros))))
                   (variable-list-p  (format "Variable list:\n%s\n"
                                             (pp-to-string (bookmark-prop-get bookmark 'variables))))
                   (search-hits-p    (format "Icicles search hits:\n%s\n\n"
                                             (mapconcat (lambda (hit)
                                                          (let ((hit-copy  (copy-sequence hit)))
                                                            (set-text-properties 0 (length hit-copy) ()
                                                                                 hit-copy)
                                                            hit-copy))
                                                        (bookmark-prop-get bookmark 'hits)
                                                        "\n\t")))
                   (non-invokable-p  (format "Non-invokable:\n\n%s"
                                             (let ((desc  (bookmark-prop-get bookmark 'filter-description)))
                                               (if desc
                                                   (format "Isearch filter:\n%s\n" desc)
                                                 ""))))
                   (gnus-p           (format "Gnus, group:\t\t%s, article: %s, message-id: %s\n"
                                             (bookmark-prop-get bookmark 'group)
                                             (bookmark-prop-get bookmark 'article)
                                             (bookmark-prop-get bookmark 'message-id)))
                   (man-p            (format "UNIX `man' page for:\t`%s'\n"
                                             (or (bookmark-prop-get bookmark 'man-args)
                                                 ;; WoMan has no variable for the cmd name.
                                                 (bookmark-prop-get bookmark 'buffer-name))))
                   (info-p           (and file  (format "Info node:\t\t(%s) %s\n"
                                                        (file-name-nondirectory file)
                                                        (bookmark-prop-get bookmark 'info-node))))
                   (eww-p            (and file  (format "EWW URL:\t\t%s\n" file))) ; Emacs 25+
                   (w3m-p            (and file  (format "W3m URL:\t\t%s\n" file)))
                   (url-p            (format "URL:\t\t\t%s\n" location))
                   (desktop-p        (format "Desktop file:\t\t%s\n"
                                             (bookmark-prop-get bookmark 'desktop-file)))
                   (bookmark-file-p  (format "Bookmark file:\t\t%s\n"
                                             (bookmark-prop-get bookmark 'bookmark-file)))
                   (snippet-p        (format "Snippet for `kill-ring'.\n"))
                   (dired-p          (and file
                                          (let ((switches  (bookmark-prop-get bookmark 'dired-switches))
                                                (marked    (length (bookmark-prop-get bookmark
                                                                                      'dired-marked)))
                                                (inserted  (length (bookmark-prop-get bookmark
                                                                                      'dired-subdirs)))
                                                (hidden    (length (bookmark-prop-get bookmark
                                                                                      'dired-hidden-dirs))))
                                            (format "Dired%s:%s\t\t%s\nMarked:\t\t\t%s\n\
Inserted subdirs:\t%s\nHidden subdirs:\t\t%s\n"
                                                    (if switches (format " `%s'" switches) "")
                                                    (if switches "" (format "\t"))
                                                    (expand-file-name file)
                                                    marked inserted hidden))))
                   (non-file-p       (or (and location  (format "Location:\t\t%s\n" location))
                                         (and buf  (format "Buffer:\t\t\t%s\n" buf))))
                   (file             (concat (format "File:\t\t\t%s\n" (file-name-nondirectory file))
                                             (let ((dir  (file-name-directory (expand-file-name file))))
                                               (and dir  (format "Directory:\t\t%s\n" dir)))))
                   (t                "Unknown\n"))
             (unless no-position-p
               (if (bmkp-region-bookmark-p bookmark)
                   (format "Region:\t\t\t%d to %d (%d chars)\n" start end (- end start))
                 (format "Position:\t\t%d\n" start)))
             (and visits     (format "Visits:\t\t\t%d\n" visits))
             (and time       (format "Last visit:\t\t%s\n" (format-time-string "%c" time)))
             (and created    (format "Creation:\t\t%s\n" (format-time-string "%c" created)))
             (and tags       (format "Tags:\n \"%s\"\n" (mapconcat #'identity tags "\"\n \"")))
             (and annot      (format "\nAnnotation:\n%s\n" annot))
             (and snippet-p  (format "\nSnippet:\n%s\n" (bookmark-prop-get bookmark 'text)))
             (and (not no-image)
                  file
                  (fboundp 'image-file-name-regexp) ; In `image-file.el' (Emacs 22+).
                  (bmkp-string-match-p (image-file-name-regexp) file)
                  (if (fboundp 'display-graphic-p) (display-graphic-p) window-system)
                  (require 'image-dired nil t)
                  (image-dired-get-thumbnail-image file)
                  (concat "\n@#%&()_IMAGE-HERE_()&%#@" file "\n"))
             (and (not no-image)
                  file
                  (fboundp 'image-file-name-regexp) ; In `image-file.el' (Emacs 22+).
                  (bmkp-string-match-p (image-file-name-regexp) file)
                  (progn (message "Gathering image data...") t)
                  (condition-case nil
                      (let ((all  (bmkp-all-exif-data (expand-file-name file))))
                        (concat
                         (and all  (not (zerop (length all)))
                              (format "\nImage Data (EXIF)\n-----------------\n%s"
                                      all))))
                    (error nil))))))
      help-text)))

;; This is the same as `help-all-exif-data' in `help-fns+.el', but we avoid requiring that library.
(defun bmkp-all-exif-data (file)
  "Return all EXIF data from FILE, using command-line tool `exiftool'."
  (with-temp-buffer
    (delete-region (point-min) (point-max))
    (unless (eq 0 (call-process shell-file-name nil t nil shell-command-switch
                                (format "exiftool -All \"%s\"" file)))
      (error "Could not get EXIF data"))
    (buffer-substring (point-min) (point-max))))


;;;###autoload (autoload 'bmkp-describe-bookmark-internals "bookmark+")
(defun bmkp-describe-bookmark-internals (bookmark)
  "Show the internal definition of the bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
If it is a record then it need not belong to `bookmark-alist'."
  (interactive (list (bookmark-completing-read "Describe bookmark" (bmkp-default-bookmark-name))))
  ;; Work with a copy of the bookmark, so we can unpropertize the name.
  (setq bookmark  (copy-sequence (bookmark-get-bookmark bookmark)))
  (help-setup-xref (list #'bmkp-describe-bookmark-internals bookmark) (interactive-p))
  (let* ((bname         (copy-sequence (bmkp-bookmark-name-from-record bookmark)))
         (IGNORE        (set-text-properties 0 (length bname) nil bname)) ; Strip properties from name.
         (bmk           (cons bname (bmkp-bookmark-data-from-record bookmark))) ; Fake bmk with stripped name.
         (print-circle  bmkp-propertize-bookmark-names-flag) ; For `pp-to-string'
         (print-length  nil)            ; For `pp-to-string'
         (print-level   nil)            ; For `pp-to-string'
         (help-text     (format "Bookmark `%s'\n%s\n\n%s" bname (make-string (+ 11 (length bname)) ?-)
                                (pp-to-string bmk))))
    (bmkp-with-help-window "*Help*" (princ help-text))
    help-text))

;;;###autoload (autoload 'bmkp-list-defuns-in-commands-file "bookmark+")
(defun bmkp-list-defuns-in-commands-file ()
  "List the functions defined in `bmkp-bmenu-commands-file'.
Typically, these are all commands."
  (interactive)
  (when (and bmkp-bmenu-commands-file  (file-readable-p bmkp-bmenu-commands-file))
    (when (file-directory-p bmkp-bmenu-commands-file)
      (error "`%s' is a directory, not a file" bmkp-bmenu-commands-file))
    (let ((fns  ())
          (buf  (let ((enable-local-variables  nil))
                  (find-file-noselect bmkp-bmenu-commands-file))))
      (help-setup-xref (list #'bmkp-list-defuns-in-commands-file) (interactive-p))
      (with-current-buffer buf
        (goto-char (point-min))
        (while (not (eobp))
          (when (re-search-forward "\\s-*(defun \\([^ \t\n(\"]+\\)[ \t\n(]" nil 'move)
            (push (match-string 1) fns)))
        (setq fns  (nreverse fns)
              fns  (sort fns 'string-lessp)))
      (when (buffer-live-p buf) (kill-buffer buf))
      (bmkp-with-help-window "*Help*"
        (princ "Bookmark Commands You Defined (in `bmkp-bmenu-commands-file')") (terpri)
        (princ "------------------------------------------------------------------") (terpri)
        (terpri)
        (let ((non-dups  (bmkp-remove-dups fns)))
          (dolist (fn  non-dups)
            (if (and (fboundp (intern fn))  (fboundp 'help-insert-xref-button))
                (with-current-buffer "*Help*"
                  (goto-char (point-max))
                  (help-insert-xref-button fn 'help-function (intern fn) (commandp (intern fn))))
              (princ fn))
            (let ((dups   (member fn fns)) ; Sorted, so all dups are together.
                  (count  0))
              (while (equal fn (car dups))
                (setq count  (1+ count)
                      dups   (cdr dups)))
              (when (> count 1) (princ (format "  (%d times)" count))))
            (terpri)))
        (help-make-xrefs (current-buffer)))
      fns)))

(defun bmkp-root-or-sudo-logged-p ()
  "Return t if the user logged in using Tramp as `root' or `sudo'.
Otherwise, return nil."
  (catch 'break
    (dolist (ii  (mapcar #'buffer-name (buffer-list)))
      (when (bmkp-string-match-p "*tramp/\\(su\\|sudo\\) ." ii) (throw 'break t)))))

(defun bmkp-position-post-context (breg)
  "Return `bookmark-search-size' chars, starting at position BREG.
Return nil if there are not that many chars.
This is text that follows the bookmark's `position'.
This is used for a non-region bookmark."
  (and (>= (- (point-max) breg) bookmark-search-size)
       (buffer-substring-no-properties breg (+ breg bookmark-search-size))))

(defun bmkp-position-post-context-region (breg ereg)
  "Return the region prefix, at BREG.
Return at most `bmkp-region-search-size' or (- EREG BREG) chars.
This is text that follows the bookmark's `position'.
This is used for a region bookmark."
  (buffer-substring-no-properties breg (+ breg (min bmkp-region-search-size (- ereg breg)))))

(defun bmkp-position-pre-context (breg)
  "Return `bookmark-search-size' chars that precede BREG.
Return nil if there are not that many chars.
This is text that precedes the bookmark's `position'.
This is used for a non-region bookmark."
  (and (>= (- breg (point-min)) bookmark-search-size)
       (buffer-substring-no-properties breg (- breg bookmark-search-size))))

(defun bmkp-position-pre-context-region (breg)
  "Return the text preceding the region beginning, BREG.
Return at most `bmkp-region-search-size' chars.
This is text that precedes the bookmark's `position'.
This is used for a region bookmark."
  (buffer-substring-no-properties (max (- breg bmkp-region-search-size) (point-min)) breg))

(defun bmkp-end-position-pre-context (breg ereg)
  "Return the region suffix, ending at EREG.
Return at most `bmkp-region-search-size' or (- EREG BREG) chars.
This is text that precedes the bookmark's `end-position'."
  (buffer-substring-no-properties (- ereg (min bmkp-region-search-size (- ereg breg))) ereg))

(defun bmkp-end-position-post-context (ereg)
  "Return the text following the region end, EREG.
Return at most `bmkp-region-search-size' chars.
This is text that follows the bookmark's `end-position'."
  (buffer-substring-no-properties ereg (+ ereg (min bmkp-region-search-size (- (point-max) ereg)))))

(defun bmkp-position-after-whitespace (position)
  "Move forward from POSITION, skipping over whitespace.  Return point."
  (goto-char position)  (skip-chars-forward " \n\t" (point-max))  (point))

(defun bmkp-position-before-whitespace (position)
  "Move backward from POSITION, skipping over whitespace.  Return point."
  (goto-char position)  (skip-chars-backward " \n\t" (point-min))  (point))

(defun bmkp-save-new-region-location (bookmark beg end)
  "Update and save `bookmark-alist' for BOOKMARK, relocating its region.
Saving happens according to `bookmark-save-flag'.
BOOKMARK is a bookmark record.
BEG and END are the new region limits for BOOKMARK.
Do nothing and return nil if `bmkp-save-new-location-flag' is nil.
Otherwise, return non-nil if region was relocated."
  (and bmkp-save-new-location-flag
       (y-or-n-p "Region relocated.  Do you want to save new region limits? ")
       (progn
         (bookmark-prop-set bookmark 'front-context-string (bmkp-position-post-context-region beg end))
         (bookmark-prop-set bookmark 'rear-context-string (bmkp-position-pre-context-region beg))
         (bookmark-prop-set bookmark 'front-context-region-string (bmkp-end-position-pre-context beg end))
         (bookmark-prop-set bookmark 'rear-context-region-string (bmkp-end-position-post-context end))
         (bookmark-prop-set bookmark 'position beg)
         (bookmark-prop-set bookmark 'end-position end)
         (bmkp-maybe-save-bookmarks)
         t)))

(defun bmkp-handle-region-default (bookmark)
  "Default function to handle BOOKMARK's region.
BOOKMARK is a bookmark name or a bookmark record.
Relocate the region if necessary, then activate it.
If region was relocated, save it if user confirms saving."
  ;; Relocate by searching from the beginning (and possibly the end) of the buffer.
  (let* (;; Get bookmark object once and for all.
         ;; We should know BOOKMARK is a bookmark record (not a name), but play it safe.
         (bmk              (bookmark-get-bookmark bookmark))
         (bor-str          (bookmark-get-front-context-string bmk))
         (eor-str          (bookmark-prop-get bmk 'front-context-region-string))
         (br-str           (bookmark-get-rear-context-string bmk))
         (ar-str           (bookmark-prop-get bookmark 'rear-context-region-string))
         (pos              (bookmark-get-position bmk))
         (end-pos          (bmkp-get-end-position bmk))
         (reg-retrieved-p  t)
         (reg-relocated-p  nil))
    (unless (and end-pos
                 (string= bor-str (buffer-substring-no-properties
                                   (point) (min (point-max) (+ (point) (length bor-str)))))
                 (string= eor-str (buffer-substring-no-properties
                                   end-pos (max (point-min) (- end-pos (length bor-str))))))
      ;; Relocate region by searching from beginning (and possibly from end) of buffer.
      (let ((beg  nil)
            (end  nil))
        ;;  Go to bob and search forward for END.
        (goto-char (point-min))
        (if (search-forward eor-str (point-max) t) ; Find END, using `eor-str'.
            (setq end  (point))
          ;; Verify that region is not before context.
          (unless (search-forward br-str (point-max) t)
            (when (search-forward ar-str (point-max) t) ; Find END, using `ar-str'.
              (setq end  (match-beginning 0)
                    end  (and end  (bmkp-position-before-whitespace end))))))
        ;; If failed to find END, go to eob and search backward for BEG.
        (unless end (goto-char (point-max)))
        (if (search-backward bor-str (point-min) t) ; Find BEG, using `bor-str'.
            (setq beg  (point))
          ;; Verify that region is not after context.
          (unless (search-backward ar-str (point-min) t)
            (when (search-backward br-str (point-min) t) ; Find BEG, using `br-str'.
              (setq beg  (match-end 0)
                    beg  (and beg  (bmkp-position-after-whitespace beg))))))
        (setq reg-retrieved-p  (or beg  end)
              reg-relocated-p  reg-retrieved-p
              ;; If only one of BEG or END was found, the relocated region is only
              ;; approximate (keep the same length).  If both were found, it is exact.
              pos              (or beg  (and end  pos  end-pos  (- end (- end-pos pos)))  pos)
              end-pos          (or end  (and beg  pos  end-pos  (+ pos (- end-pos pos)))  end-pos))))
    ;; Region is available. Activate it and maybe save it.
    (cond (reg-retrieved-p
           (when pos (goto-char pos))
           (when end-pos (push-mark end-pos 'nomsg 'activate))
           (setq deactivate-mark  nil)
           (when bmkp-show-end-of-region-flag
             (let ((end-win  (save-excursion (forward-line (window-height)) (line-end-position))))
               ;; Bounce point and mark.
               (save-excursion (sit-for 0.6) (exchange-point-and-mark) (sit-for 1))
               ;; Recenter if region end is not visible.
               (when (and end-pos  (> end-pos end-win)) (recenter 1))))
           ;; Maybe save region.
           (if (and reg-relocated-p  (bmkp-save-new-region-location bmk pos end-pos))
               (message "Saved relocated region%s" (if (and pos  end-pos)
                                                       (format " (from %d to %d)" pos end-pos)
                                                     ""))
             (when (and pos  end-pos) (message "Region is from %d to %d" pos end-pos))))
          ((and pos  end-pos)           ; No region.  Go to old start.  Don't push-mark.
           (goto-char pos) (forward-line 0)
           (message "No region from %d to %d" pos end-pos)))))

;; Same as `line-number-at-pos', which is not available until Emacs 22.
(defun bmkp-line-number-at-pos (&optional pos)
  "Buffer line number at position POS. Current line number if POS is nil.
Counting starts at (point-min), so any narrowing restriction applies."
  (1+ (count-lines (point-min) (save-excursion (when pos (goto-char pos)) (forward-line 0) (point)))))

(defun bmkp-goto-position (bookmark file buf bufname pos forward-str behind-str)
  "Go to a bookmark that has no region.
Update the recorded position if POS and `bmkp-save-new-location-flag'
are non-nil.

Arguments are respectively the bookmark, its file, buffer, buffer
name, recorded position, and the context strings for the position."
  (if (and file  (file-readable-p file)  (not (buffer-live-p buf)))
;;; $$$$$$$ (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect file))
      (with-current-buffer (find-file-noselect file) (setq buf  (buffer-name)))
    ;; No file found.  See if a non-file buffer exists for this.  If not, raise error.
    (unless (or (and buf  (get-buffer buf))
                (and bufname  (get-buffer bufname)  (not (string= buf bufname))))
      (signal 'file-error `("Jumping to bookmark" ,(format "Cannot access file `%s' or buffer `%s'"
                                                           file bufname)))))
  (set-buffer (or buf  bufname))
  (when bmkp-jump-display-function
    (save-current-buffer (funcall bmkp-jump-display-function (current-buffer))))
  (setq deactivate-mark  t)
  (raise-frame)
  (when pos (goto-char pos))
  ;; Try to relocate position.
  ;; Search forward first.  Then, if FORWARD-STR exists and was found in the file, search
  ;; backward for BEHIND-STR.  The rationale is that if text was inserted between the two
  ;; in the file, then it's better to end up before point, so you can see the text, rather
  ;; than after it and not see it.
  (when (and forward-str  (search-forward forward-str (point-max) t))
    (goto-char (match-beginning 0)))
  (when (and behind-str  (search-backward behind-str (point-min) t))  (goto-char (match-end 0)))
  (when (and (not (equal pos (point)))  bmkp-save-new-location-flag)
    (bookmark-prop-set bookmark 'position     (point))
    (bookmark-prop-set bookmark 'end-position (point))
    ;; Perhaps we should treat the case of a bookmark that had position 0 changing to position 1 specially,
    ;; by passing non-nil SAME-COUNT-P arg to `bmkp-maybe-save-bookmarks'.  On the other hand, if initially
    ;; 0 then the bookmark does not claim that the file is non-empty.  If now set to 1 then we know it is.
    ;; Leave it this way, at least for now.  The consequence is that the user will see that bookmarks have
    ;; modified (e.g. `Save' is enabled in the menu), even though nothing much has changed.
    (bmkp-maybe-save-bookmarks))
  (not (equal pos (point))))            ; Return value indicates whether POS was accurate.

(defun bmkp-jump-sequence (bookmark)
  "Handle a sequence bookmark BOOKMARK.
Handler function for sequence bookmarks.
BOOKMARK is a bookmark name or a bookmark record."
  (dolist (bmk  (bookmark-prop-get bookmark 'sequence))
    (bookmark--jump-via bmk bmkp-sequence-jump-display-function))
  (message "Done invoking bookmarks in sequence `%s'"
           (if (stringp bookmark) bookmark (bmkp-bookmark-name-from-record bookmark))))

(defun bmkp-jump-function (bookmark)
  "Handle a function bookmark BOOKMARK.
Handler function for function bookmarks.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((fn  (bookmark-prop-get bookmark 'function)))
    (cond ((functionp fn) (funcall fn))
          ((vectorp fn)
           (execute-kbd-macro fn current-prefix-arg)))))

(defun bmkp-make-bookmark-list-record ()
  "Create and return a bookmark-list bookmark record.
This records the current state of buffer `*Bookmark List*': the sort
order, filter function, regexp pattern, title, and omit list."
  (let ((state  `((last-sort-comparer            . ,bmkp-sort-comparer)
                  (last-reverse-sort-p           . ,bmkp-reverse-sort-p)
                  (last-reverse-multi-sort-p     . ,bmkp-reverse-multi-sort-p)
                  (last-bmenu-filter-function    . ,bmkp-bmenu-filter-function)
                  (last-bmenu-filter-pattern     . ,bmkp-bmenu-filter-pattern)
                  (last-bmenu-omitted-bookmarks  . ,(bmkp-maybe-unpropertize-bookmark-names
                                                     bmkp-bmenu-omitted-bookmarks))
                  (last-bmenu-title              . ,bmkp-bmenu-title)
                  (last-bmenu-toggle-filenames   . ,bookmark-bmenu-toggle-filenames))))
    `(,@(bookmark-make-record-default 'NO-FILE 'NO-CONTEXT)
      (filename      . ,bmkp-non-file-filename)
      (bookmark-list . ,state)
      (handler       . bmkp-jump-bookmark-list))))

(add-hook 'bookmark-bmenu-mode-hook
          (lambda () (set (make-local-variable 'bookmark-make-record-function)
                          'bmkp-make-bookmark-list-record)))

(defun bmkp-jump-bookmark-list (bookmark)
  "Jump to bookmark-list bookmark BOOKMARK.
Handler function for record returned by
`bmkp-make-bookmark-list-record'.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((state  (bookmark-prop-get bookmark 'bookmark-list)))
    (setq bmkp-sort-comparer               (cdr (assq 'last-sort-comparer            state))
          bmkp-reverse-sort-p              (cdr (assq 'last-reverse-sort-p           state))
          bmkp-reverse-multi-sort-p        (cdr (assq 'last-reverse-multi-sort-p     state))
          bmkp-bmenu-filter-function       (cdr (assq 'last-bmenu-filter-function    state))
          bmkp-bmenu-filter-pattern        (or (cdr (assq 'last-bmenu-filter-pattern state)) "")
          bmkp-bmenu-omitted-bookmarks     (cdr (assq 'last-bmenu-omitted-bookmarks  state))
          bmkp-bmenu-title                 (cdr (assq 'last-bmenu-title              state))
          bookmark-bmenu-toggle-filenames  (cdr (assq 'last-bmenu-toggle-filenames   state))))
  (let ((bookmark-alist  (if bmkp-bmenu-filter-function
                             (funcall bmkp-bmenu-filter-function)
                           bookmark-alist)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)
    (when (get-buffer "*Bookmark List*") (pop-to-buffer "*Bookmark List*"))))

;; Bookmark-file bookmarks.
;;;###autoload (autoload 'bmkp-set-bookmark-file-bookmark "bookmark+")
(defun bmkp-set-bookmark-file-bookmark (file &optional msg-p) ; Bound to `C-x p y', `C-x p c y'
  "Create a bookmark that loads bookmark-file FILE when \"jumped\" to.
You are prompted for the names of the bookmark file and the bookmark.
When entering the bookmark name you can use completion against
existing names.  This completion is lax, so you can easily edit an
existing name.  See `bookmark-set' for particular keys available
during this input.

Non-interactively, non-nil MSG-P means display a status message."
  (interactive
   (list (let* ((insert-default-directory  t)
                (std-default  (bmkp-default-bookmark-file))
                (default      (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                                  (if (bmkp-same-file-p bmkp-current-bookmark-file std-default)
                                      bookmark-default-file
                                    std-default)
                                bmkp-last-bookmark-file)))
           (bmkp-read-bookmark-file-name "Create bookmark to load bookmark file: "
                                         (or (file-name-directory default) "~/")
                                         default
                                         'confirm)) ; Non-existing file is OK, but must confirm.
         'MSG))
  (setq file  (expand-file-name file))
  (when (file-directory-p file) (error "`%s' is a directory, not a file" file))
  (unless (file-readable-p file) (error "Unreadable bookmark file `%s'" file))
  (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect file))
    (goto-char (point-min))
    (condition-case nil                 ; Check whether it's a valid bookmark file.
        (progn (bookmark-maybe-upgrade-file-format)
               (unless (listp (bookmark-alist-from-buffer)) (error "")))
      (error (error "Not a valid bookmark file: `%s'" file))))
  (let ((bookmark-make-record-function  (lexical-let ((ff  file))
                                          (lambda () (bmkp-make-bookmark-file-record ff))))
        (bookmark-name                  (bmkp-completing-read-lax "Bookmark-file BOOKMARK name"
                                                                  file nil nil 'bookmark-history)))
    (bookmark-set bookmark-name 99 'INTERACTIVEP))
  (when msg-p (message "Set bookmark-file bookmark")))

(defun bmkp-make-bookmark-file-record (bookmark-file)
  "Create and return a bookmark-file bookmark record.
Records the BOOKMARK-FILE name.
Adds a handler that tests the prefix arg and loads the bookmark file
either as a replacement for the current bookmark file or as a
supplement to it."
  `(,@(bookmark-make-record-default 'NO-FILE 'NO-CONTEXT nil nil 'NO-REGION)
    (filename      . ,bookmark-file)
    (bookmark-file . ,bookmark-file)
    (handler       . bmkp-jump-bookmark-file)))

(defun bmkp-jump-bookmark-file (bookmark &optional switchp batchp)
  "Jump to bookmark-file bookmark BOOKMARK, which loads the bookmark file.
Handler function for record returned by
`bmkp-make-bookmark-file-record'.
BOOKMARK is a bookmark name or a bookmark record.
Non-nil optional arg SWITCHP means overwrite current bookmark list.
Non-nil optional arg BATCHP is passed to `bookmark-load'."
  (let ((file        (bookmark-prop-get bookmark 'bookmark-file))
        (overwritep  (and switchp  (y-or-n-p "SWITCH to new bookmark file, instead of just adding it? "))))
    (bookmark-load file overwritep batchp)) ; Treat load interactively, if no BATCHP.
  ;; This `throw' is only for the case where this handler is called from `bookmark--jump-via'.
  ;; It just tells `bookmark--jump-via' to skip the rest of what it does after calling the handler.
  (condition-case nil
      (throw 'bookmark--jump-via 'BOOKMARK-FILE-JUMP)
    (no-catch nil)))

;;;###autoload (autoload 'bmkp-bookmark-file-jump "bookmark+")
(defun bmkp-bookmark-file-jump (bookmark-name &optional switchp no-msg) ; `C-x j y'
  "Jump to a bookmark-file bookmark, which means load its bookmark file.
With a prefix argument, switch to the new bookmark file.
Otherwise, load it to supplement the current bookmark list."
  (interactive
   (let ((alist  (bmkp-bookmark-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "bookmark-file" alist nil nil 'bmkp-bookmark-file-history)
           current-prefix-arg)))
  (bmkp-jump-bookmark-file bookmark-name switchp no-msg))

;; Snippet bookmarks
;; Inspired by emacs-devel@gnu.org post from Masatake Yamato [yamato@redhat.com], 2012-01-06.
;;;###autoload (autoload 'bmkp-set-snippet-bookmark "bookmark+")
(defun bmkp-set-snippet-bookmark (beg end &optional promptp msgp)
                                        ; Bound globally to `C-x p c M-w'.
  "Save the text of the active region as a bookmark.
The bookmark is automatically named with the first line of the region
text.  With a prefix argument you are prompted for the name instead.

Jumping to the bookmark copies the saved text to the `kill-ring', so
you can yank it using `C-y'."
  (interactive "r\nP\np")
  (unless (and mark-active  transient-mark-mode) (error "No active region"))
  (when (equal beg end) (error "Region is empty"))
  (lexical-let ((text  (buffer-substring-no-properties beg end)))
    (let ((bookmark-make-record-function  (lambda ()
                                            `(,@(bookmark-make-record-default 'NO-FILE 'NO-CONTEXT)
                                              (text    . ,text)
                                              (handler . bmkp-jump-snippet))))
          (bname                          (and (not promptp)  (car (split-string text "[\n]")))))
      (bookmark-set bname 99 'INTERACTIVEP)
      ;; `bookmark-set does the prompting, providing default names.  
      (when msgp (message "Region text bookmarked%s" (if bname (format " as `%s'" bname) ""))))))

(defun bmkp-jump-snippet (bookmark)
  "Copy the text saved in BOOKMARK to the `kill-ring'.
Handler for snippet bookmarks."
  (kill-new (bookmark-prop-get bookmark 'text))
  (message "Snippet of bookmark `%s' copied to `kill-ring'" (bmkp-bookmark-name-from-record bookmark)))

;;;###autoload (autoload 'bmkp-snippet-to-kill-ring "bookmark+")
(defun bmkp-snippet-to-kill-ring (bookmark-name) ; `C-x j M-w'
  "Jump to a snippet bookmark: copy its saved text to the `kill-ring'.
This is a specialization of `bookmark-jump' for snippet bookmarks."
  (interactive
   (let ((alist  (bmkp-snippet-alist-only)))
     (list (bmkp-read-bookmark-for-type "snippet" alist nil nil 'bmkp-snippet-history nil
                                        "Copy snippet to kill ring"))))
  (bmkp-jump-1 bookmark-name 'ignore))

;; Desktop bookmarks
;;;###autoload (autoload 'bmkp-set-desktop-bookmark "bookmark+")
(defun bmkp-set-desktop-bookmark (desktop-file &optional nosavep)
                                        ; Bound globally to `C-x p K', `C-x r K', `C-x p c K'
  "Save the desktop as a bookmark.
You are prompted for the desktop-file location and the bookmark name.
The default value for the desktop-file location is the current value
of `desktop-base-file-name'.  As always, you can use `M-n' to retrieve
the default value.

With a prefix arg, set a bookmark to an existing desktop file - do not
save the current desktop.  Do not overwrite the file whose name you
enter, just use it to set the bookmark.

If you also use library Icicles, then the desktop files of all
existing desktop bookmarks are available during the desktop file-name
completion as proxy candidates.  To see them, use `C-M-_' to turn on
the display of proxy candidates."
  (interactive
   (progn (unless (condition-case nil (require 'desktop nil t) (error nil))
            (error "You must have library `desktop.el' to use this command"))
          (let ((icicle-proxy-candidates                     (and (boundp 'icicle-mode) icicle-mode
                                                                  (mapcar (lambda (bmk)
                                                                            (bookmark-prop-get
                                                                             bmk 'desktop-file))
                                                                          (bmkp-desktop-alist-only))))
                (icicle-unpropertize-completion-result-flag  t))
            (list (read-file-name
                   (if current-prefix-arg "Use existing desktop file: " "Save desktop in file: ")
                   bmkp-desktop-default-directory
                   (if (boundp 'desktop-base-file-name) desktop-base-file-name desktop-basefilename)
                   current-prefix-arg)
                  current-prefix-arg))))
  (unless (or nosavep  (condition-case nil (require 'desktop nil t) (error nil)))
    (error "You must have library `desktop.el' to use this command"))
  (unless (file-name-absolute-p desktop-file)
    (setq desktop-file  (expand-file-name desktop-file bmkp-desktop-default-directory)))
  (set-text-properties 0 (length desktop-file) nil desktop-file)
  (if nosavep
      (unless (bmkp-desktop-file-p desktop-file) (error "Not a desktop file: `%s'" desktop-file))
    (bmkp-desktop-save desktop-file))
  (let ((bookmark-make-record-function  (lexical-let ((df  desktop-file))
                                          (lambda () (bmkp-make-desktop-record df))))
        (current-prefix-arg             99)) ; Use all bookmarks for completion, for `bookmark-set'.
    (call-interactively #'bookmark-set)))

(defun bmkp-desktop-save (desktop-file)
  "Save current desktop in DESKTOP-FILE."
  (let ((desktop-basefilename     (file-name-nondirectory desktop-file)) ; Emacs < 22
        (desktop-base-file-name   (file-name-nondirectory desktop-file)) ; Emacs 23+
        (desktop-dir              (file-name-directory desktop-file))
        (desktop-restore-eager    t)    ; Don't bother with lazy restore.
        (desktop-globals-to-save  (bmkp-remove-if (lambda (elt) (memq elt bmkp-desktop-no-save-vars))
                                                  desktop-globals-to-save)))
    (cond ((< emacs-major-version 22)   ; Emacs 22 introduced `RELEASE' (locking).
           (desktop-save desktop-dir))
          ((or (< emacs-major-version 24) (and (= emacs-major-version 24)  (< emacs-minor-version 4)))
           (desktop-save desktop-dir 'RELEASE))
          (t                            ; Emacs 24.4 introduced `AUTOSAVE'.
           (desktop-save desktop-dir 'RELEASE 'AUTOSAVE)))
    (message "Desktop saved in `%s'" desktop-file)))

(unless (fboundp 'desktop-full-file-name) ; Emacs < 22.  (This is the vanilla definition.)
  (defun desktop-full-file-name (&optional dirname)
    "Return the full name of the desktop file in DIRNAME.
DIRNAME omitted or nil means use `desktop-dirname'."
    (expand-file-name desktop-basefilename (or dirname  desktop-dirname))))

(defun bmkp-desktop-save-as-last ()
  "Save desktop to the file that is the value of `bmkp-desktop-current-file'.
Do nothing if any of these are true:

 * `desktop-save-mode' is non-nil
 * `bmkp-desktop-current-file' is nil
 * `bmkp-desktop-current-file' does not seem to be current (a non-bookmark
   desktop was last made current)

You might want to use this on `kill-emacs-hook'."
  (when (and (not desktop-save-mode)  bmkp-desktop-current-file
             (bmkp-same-file-p (desktop-full-file-name) bmkp-desktop-current-file))
    (bmkp-desktop-save bmkp-desktop-current-file)))

;;; (defun bmkp-desktop-file-p (file)
;;;   "Return non-nil if FILE is readable and appears to be a desktop file.
;;; FILE is a file-name string."
;;;   (and (stringp file)
;;;        (file-readable-p file)
;;;        (with-current-buffer (let ((enable-local-variables nil)) (find-file-noselect file))
;;;          (goto-char (point-min))
;;;          (and (zerop (forward-line 2))
;;;               (bmkp-looking-at-p "^;; Desktop File for Emacs$")))))

;; Similar to `icicle-file-desktop-p' in `icicles-fn.el'.
;; This is better than using `find-file-noselect', which visits the file and leaves its buffer.
(defun bmkp-desktop-file-p (filename)
  "Return non-nil if FILENAME names a desktop file."
  (when (consp filename) (setq filename  (car filename)))
  (and (stringp filename)
       (file-readable-p filename)
       (not (file-directory-p filename))
       (with-temp-buffer
         (insert-file-contents-literally filename nil 0 1000)
         (goto-char (point-min))
         (and (zerop (forward-line 2))
              (bmkp-looking-at-p "^;; Desktop File for Emacs"))))) ; No $, because maybe eol chars (e.g. ^M).

(defun bmkp-make-desktop-record (desktop-file)
  "Create and return a desktop bookmark record.
DESKTOP-FILE is the absolute file name of the desktop file to use."
  `(,@(bookmark-make-record-default 'NO-FILE 'NO-CONTEXT nil nil 'NO-REGION)
    (filename     . ,bmkp-non-file-filename)
    (desktop-file . ,desktop-file)
    (handler      . bmkp-jump-desktop)))

(defun bmkp-jump-desktop (bookmark)
  "Jump to desktop bookmark BOOKMARK.
Handler function for record returned by `bmkp-make-desktop-record'.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((desktop-file  (bookmark-prop-get bookmark 'desktop-file)))
    (unless (condition-case nil (require 'desktop nil t) (error nil))
      (error "You must have library `desktop.el' to use this command"))
    ;; (unless desktop-file (error "Not a desktop-bookmark: %S" bookmark)) ; Shouldn't happen.
    (bmkp-desktop-change-dir desktop-file)
    (unless (bmkp-desktop-read desktop-file) (error "Could not load desktop file"))))

;; Derived from code in `desktop-change-dir'.
;;;###autoload (autoload 'bmkp-desktop-change-dir "bookmark+")
(defun bmkp-desktop-change-dir (desktop-file)
  "Change to desktop saved in DESKTOP-FILE.
Kill the desktop as specified by variables `desktop-save-mode' and
 `desktop-save' (starting with Emacs 22).
Clear the desktop and load DESKTOP-FILE."
  (interactive
   (progn (unless (condition-case nil (require 'desktop nil t) (error nil))
            (error "You must have library `desktop.el' to use this command"))
          (list (let ((icicle-unpropertize-completion-result-flag  t))
                  (read-file-name "Change to desktop file: " bmkp-desktop-default-directory)))))
  (unless (condition-case nil (require 'desktop nil t) (error nil))
    (error "You must have library `desktop.el' to use this command"))
  (unless (file-name-absolute-p desktop-file)
    (setq desktop-file  (expand-file-name desktop-file bmkp-desktop-default-directory)))
  (set-text-properties 0 (length desktop-file) nil desktop-file)
  (let ((desktop-basefilename     (file-name-nondirectory desktop-file)) ; Emacs < 22
        (desktop-base-file-name   (file-name-nondirectory desktop-file)) ; Emacs 23+
        (desktop-dir              (file-name-directory desktop-file))
        (desktop-restore-eager    t)    ; Don't bother with lazy restore.
        (desktop-globals-to-save  (bmkp-remove-if (lambda (elt) (memq elt bmkp-desktop-no-save-vars))
                                                  desktop-globals-to-save)))
    (bmkp-desktop-kill)
    (desktop-clear)
    (if (< emacs-major-version 22) (desktop-read) (desktop-read desktop-dir))))

;; Derived from code in `desktop-kill'.
(defun bmkp-desktop-kill ()
  "If `desktop-save-mode' is non-nil, do what `desktop-save' says to do.
In any case, release the lock on the desktop file.
This function does nothing in Emacs versions prior to Emacs 22."
  ;; We assume here: `desktop.el' has been loaded and `desktop-dirname' is defined.
  (when (and (boundp 'desktop-save-mode) ; Not defined in Emacs 20-21.
             desktop-save-mode
             (let ((exists  (file-exists-p (desktop-full-file-name))))
               (or (eq desktop-save t)
                   (and exists  (memq desktop-save '(ask-if-new if-exists)))
                   (and (or (memq desktop-save '(ask ask-if-new))
                            (and exists  (eq desktop-save 'ask-if-exists)))
                        (y-or-n-p "Save current desktop first? ")))))
    (condition-case err
        (if (or (< emacs-major-version 24)
                (and (= emacs-major-version 24)  (< emacs-minor-version 4)))
            (desktop-save desktop-dirname 'RELEASE)
          (desktop-save desktop-dirname 'RELEASE 'AUTOSAVE)) ; Emacs 24.4 introduced `AUTOSAVE'.
      (file-error (unless (yes-or-no-p "Error while saving the desktop.  IGNORE? ")
                    (signal (car err) (cdr err))))))
  ;; Just release lock, regardless of whether this Emacs process is the owner.
  (when (fboundp 'desktop-release-lock) (desktop-release-lock))) ; Not defined for Emacs 20.

;; Derived from code in `desktop-read'.
;;;###autoload (autoload 'bmkp-desktop-read "bookmark+")
(defun bmkp-desktop-read (file)
  "Load desktop-file FILE, then run `desktop-after-read-hook'.
Return t if FILE was loaded, nil otherwise."
  (interactive)
  (unless (file-name-absolute-p file) ; Should never happen.
    (setq file  (expand-file-name file bmkp-desktop-default-directory)))
  (when (file-directory-p file) (error "`%s' is a directory, not a file" file))
  (setq desktop-dirname  (file-name-directory file))
  (if (not (file-readable-p file))
      nil                               ; Return nil, meaning not loaded.
    (let ((desktop-restore-eager      t) ; Don't bother with lazy restore.
          (desktop-first-buffer       nil)
          (desktop-buffer-ok-count    0)
          (desktop-buffer-fail-count  0)
          (desktop-save               nil)) ; Prevent desktop saving during eval of desktop buffer.
      (when (fboundp 'desktop-lazy-abort) (desktop-lazy-abort)) ; Emacs 22+.
      (load file t t t)
      (when (boundp 'desktop-file-modtime) ; Emacs 22+
        (setq desktop-file-modtime  (nth 5 (file-attributes file))))
      ;; `desktop-create-buffer' puts buffers at end of the buffer list.
      ;; We want buffers existing prior to evaluating the desktop (and not reused) to be placed
      ;; at the end of the buffer list, so we move them here.
      (mapc 'bury-buffer (nreverse (cdr (memq desktop-first-buffer (nreverse (buffer-list))))))
      (switch-to-buffer (car (buffer-list)))
      (run-hooks 'desktop-delay-hook)
      (setq desktop-delay-hook  ())
      (run-hooks 'desktop-after-read-hook)
      (when (boundp 'desktop-buffer-ok-count) ; Emacs 22+
        (message "Desktop: %d buffer%s restored%s%s." desktop-buffer-ok-count
                 (if (= 1 desktop-buffer-ok-count) "" "s")
                 (if (< 0 desktop-buffer-fail-count)
                     (format ", %d failed to restore" desktop-buffer-fail-count)
                   "")
                 (if (and (boundp 'desktop-buffer-args-list)  desktop-buffer-args-list)
                     (format ", %d to be restored lazily" (length desktop-buffer-args-list))
                   "")))
      t)))                              ; Return t, meaning successfully loaded.

;;;###autoload (autoload 'bmkp-desktop-delete "bookmark+")
(defun bmkp-desktop-delete (bookmark-name)
  "Delete desktop bookmark BOOKMARK-NAME, and delete its desktop file.
Release the lock file in that desktop's directory.
\(This means that if you currently have locked a different desktop
in the same directory, then you will need to relock it.)"
  (interactive
   (let ((alist  (bmkp-desktop-alist-only)))
     (list (bmkp-read-bookmark-for-type "desktop" alist nil nil 'bmkp-desktop-history "Delete "))))
  (let ((desktop-file  (bookmark-prop-get bookmark-name 'desktop-file)))
    (unless desktop-file (error "Not a desktop-bookmark: `%s'" bookmark-name))
    ;; Release the desktop lock file in the same directory as DESKTOP-FILE.
    ;; This will NOT be the right thing to do if a desktop file different from DESKTOP-FILE
    ;; is currently locked in the same directory.
    (let ((desktop-dir  (file-name-directory desktop-file)))
      (when (fboundp 'desktop-release-lock) (desktop-release-lock))) ; Not defined for Emacs 20.
    (when (file-exists-p desktop-file) (delete-file desktop-file)))
  (bookmark-delete bookmark-name))

;; Icicle search-hits bookmarks
(defun bmkp-jump-icicle-search-hits (bookmark)
  "Handle an Icicles search-hits bookmark BOOKMARK."
  (unless (and (boundp 'icicle-mode)  icicle-mode  (icicle-completing-p)
               (condition-case nil (icicle-barf-if-outside-Completions-and-minibuffer) (error nil)))
    (error "You can use this bookmark only in Icicle mode, and only during completion"))
  (let ((raw-cands  (bookmark-prop-get bookmark 'hits)))
    (setq icicle-saved-completion-candidates
          (if icicle-multi-completing-p
              raw-cands                 ; But will not work if RAW-CANDS are not multi-completions.
            (mapcar #'icicle-transform-multi-completion raw-cands)))
    (if bmkp-icicles-search-hits-retrieve-more
        (icicle-candidate-set-retrieve-more)
      (icicle-candidate-set-retrieve))))

;;;###autoload (autoload 'bmkp-retrieve-icicle-search-hits "bookmark+")
(defun bmkp-retrieve-icicle-search-hits () ; Bound to `C-x C-M-<' during Icicles completion.
  "Replace the current set of Icicles search hits by those from a bookmark.
You are prompted for the bookmark name.
This makes sense only if the buffer(s) or file(s) currently being
searched correspond to the recorded search hits."
  (interactive)
  (when (interactive-p) (icicle-barf-if-outside-Completions-and-minibuffer))
  (bmkp-retrieve-icicle-search-hits-1))

;;;###autoload (autoload 'bmkp-retrieve-more-icicle-search-hits "bookmark+")
(defun bmkp-retrieve-more-icicle-search-hits () ; Bound to `C-x C-<' during Icicles completion.
  "Add the Icicles search hits from a bookmark to the current set of hits.
You are prompted for the bookmark name.
This makes sense only if the buffer(s) or file(s) currently being
searched correspond to the recorded search hits."
  (interactive)
  (when (interactive-p) (icicle-barf-if-outside-Completions-and-minibuffer))
  (bmkp-retrieve-icicle-search-hits-1 'MORE))

(defun bmkp-retrieve-icicle-search-hits-1 (&optional morep)
  "Helper for `bmkp-retrieve-(more-)icicle-search-hits'."
  (unless (and (boundp 'icicle-searching-p)  icicle-searching-p)
    (error "This command can be used only during Icicles search"))
  (let* ((hits-bmks                               (bmkp-icicles-search-hits-alist-only))
         (bmk                                     (let ((icicle-completion-candidates
                                                         icicle-completion-candidates)
                                                        (enable-recursive-minibuffers  t))
                                                    (bookmark-completing-read
                                                     "Bookmark name"
                                                     (mapcar #'bmkp-bookmark-name-from-record hits-bmks)
                                                     hits-bmks)))
         (bmkp-icicles-search-hits-retrieve-more  morep))
    (bookmark-jump bmk)))

;;;###autoload (autoload 'bmkp-set-icicle-search-hits-bookmark "bookmark+")
(defun bmkp-set-icicle-search-hits-bookmark () ; Bound to `C-x C-M->' during Icicles completion.
  "Record the current set of Icicles search-hit candidates as a bookmark."
  (interactive)
  (unless (and (boundp 'icicle-searching-p)  icicle-searching-p)
    (error "This command can be used only during Icicles search"))
  (unless icicle-completion-candidates (error "No search hits to record"))
  (when (interactive-p) (icicle-barf-if-outside-Completions-and-minibuffer))
  (let ((bookmark-make-record-function  'bmkp-make-icicle-search-hits-record)
        (enable-recursive-minibuffers   t))
    (call-interactively #'bookmark-set)))

(defun bmkp-make-icicle-search-hits-record ()
  "Create and return an Icicles search-hits bookmark record."
  `(,@(bookmark-make-record-default 'NO-FILE 'NO-CONTEXT nil nil 'NO-REGION)
      (filename    . ,bmkp-non-file-filename)
      (hits        . ,(mapcar #'bmkp-unpropertized-string icicle-completion-candidates))
      (handler     . bmkp-jump-icicle-search-hits)))

;; Variable-list bookmarks
(when (boundp 'zz-izones-var)           ; In `zones.el'.
  (defun bmkp-set-izones-bookmark (&optional variable msgp)
    "Save a ring of buffer zones as a bookmark.
The zones can use markers or readable-marker objects for any
buffers.  You need library `zones.el' to use the bookmark created.

By default, the zones are those defined by the variable that is the
current value of `zz-izones-var', which defaults to `zz-izones'.  With
a prefix arg you are prompted for a different variable to use.

Non-interactively, VARIABLE is the restrictions variable to use."
    (interactive (let ((var  (or (and current-prefix-arg  (zz-read-any-variable "Variable: " zz-izones-var))
                                 zz-izones-var)))
                   (list var t)))
    (unless variable (setq variable  zz-izones-var))
    (let ((bookmark-make-record-function
           (lambda ()
             (bmkp-make-variable-list-record
              `((,variable              ; Format: (NUM BEGM ENDM), BEGM and ENDM are readable-marker objects.
                 . ,(mapcar (lambda (xx)
                              (let ((num  (nth 0 xx))
                                    (beg  (nth 1 xx))
                                    (end  (nth 2 xx)))
                                `(,num ,(zz-readable-marker beg) ,(zz-readable-marker end))))
                            (symbol-value variable))))))))
      (call-interactively #'bookmark-set)
      (when (and msgp  (not (featurep 'zones))
                 (message "Bookmark created, but you need `zones.el' to use it")))))

  )

;;;###autoload (autoload 'bmkp-wrap-bookmark-with-last-kbd-macro "bookmark+")
(defun bmkp-wrap-bookmark-with-last-kbd-macro (sequence bookmark &optional arg msgp)
                                        ; Bound globally to `C-x p C-k'.
  "Return a SEQUENCE bookmark that invokes BOOKMARK plus `last-kbd-macro'.
If bookmark SEQUENCE does not yet exist, create it.  Else, update it.
You are prompted for the SEQUENCE and BOOKMARK names.

BOOKMARK can be any kind of bookmark.  A special case is when it is a
sequence bookmark:

 * If BOOKMARK is the same as SEQUENCE and is an existing sequence
   bookmark then it is updated only by appending the keyboard macro to
   the sequence.

 * If BOOKMARK is a sequence bookmark different from SEQUENCE then
   SEQUENCE is updated to invoke the sequence in BOOKMARK plus
   `last-kbd-macro' either before or after the other bookmarks of
   SEQUENCE, according to the prefix arg, which is passed to
   `bmkp-set-sequence-bookmark'."
  (interactive (list (bmkp-completing-read-lax "Sequence bookmark" (bmkp-new-bookmark-default-names))
                     (bmkp-completing-read-lax "Bookmark" (bmkp-new-bookmark-default-names))
                     current-prefix-arg
                     'MSGP))
  (unless last-kbd-macro (error "No keyboard macro defined"))
  (let ((kbd-macro-vec  (read-kbd-macro (format-kbd-macro last-kbd-macro) 'VECTOR)))
    (bmkp-set-sequence-bookmark sequence (if (equal bookmark sequence)
                                             (list kbd-macro-vec)
                                           (list bookmark kbd-macro-vec))
                                arg msgp)))

;; Not used yet.
(defun bmkp-pop-to-readable-marker (readable-marker)
  "Go to the marker recorded as persistent READABLE-MARKER.
The form of the input is (marker MARKER-BUFFER MARKER-POSITION."
  (pop-to-buffer (cadr readable-marker))
  (goto-char (cadr (cdr readable-marker))))

;;;###autoload (autoload 'bmkp-set-sequence-bookmark "bookmark+")
(defun bmkp-set-sequence-bookmark (seqname bookmark-names &optional arg msgp)
                                        ; Bound globally to `C-x p c s'.
  "Create or update a sequence bookmark named SEQNAME from BOOKMARK-NAMES.
If a sequence bookmark named SEQNAME does not exist then create one.
Else act on the existing bookmarks in bookmark SEQNAME as follows:

 * no prefix arg:    Append BOOKMARK-NAMES to those present.
 * prefix arg < 0:   Replace those present with BOOKMARK-NAMES.
 * other prefix arg: Prepend BOOKMARK-NAMES to those present.

You are prompted for SEQNAME and each of the BOOKMARK-NAMES.

When entering each item of BOOKMARK-NAMES you can enter an existing or
future bookmark name, or you can enter the name of a function or a
named keyboard macro (provided what you type does not match a bookmark
name).  If a function or keyboard macro, then a function bookmark is
created for it and that bookmark is included in the sequence.

When the sequence bookmark is invoked (\"jumped to\"), its bookmarks
are invoked in order.  In particular, any given bookmark is invoked
once for each of its occurrences in the sequence.

From Lisp code:

BOOKMARK-NAMES is generally a list of bookmarks or bookmark names
 \(strings).

 Each item in BOOKMARK-NAMES can alternatively be one of the
 following, in which case a function bookmark is created for it and is
 used in the sequence.

  * a keyboard macro as a vector
  * a function, which includes a lambda form or a symbol whose
    function value is a function or a keyboard macro.

 If an item in BOOKMARK-NAMES is a sequence bookmark then its
 bookmarks are used as if they were items of BOOKMARK-NAMES.

MSGP non-nil means possibly interact with the user, showing messages."
  (interactive (list
                (if (< (prefix-numeric-value current-prefix-arg) 0)
                    (bookmark-completing-read "Replace existing sequence bookmark" nil
                                              (bmkp-sequence-alist-only))
                  (bmkp-completing-read-lax "Create or update sequence bookmark"
                                            (bmkp-new-bookmark-default-names)
                                            (bmkp-sequence-alist-only)))
                (bmkp-completing-read-bookmarks nil nil nil 'lax)
                current-prefix-arg
                'MSGP))
  (let* ((seq        (bmkp-get-bookmark-in-alist seqname 'NOERROR))
         (exists     (and seq  (bmkp-sequence-bookmark-p seq)))
         (replacing  t)
         (bnames     ())
         fun)
    (dolist (bname  bookmark-names)
      (cond ((or (functionp (setq fun bname)) ; Function from Lisp.
                 (vectorp fun)          ; Keyboard macro.
                 (functionp (setq fun  (condition-case nil ; Function name from user
                                           (bmkp-read-from-whole-string bname)
                                         (error nil)))))
             (let ((fun-bmk-name
                    (cond ((symbolp fun) (symbol-name fun)) ; Named function.  Use its name.
                          ((vectorp fun) (format-kbd-macro fun)) ; Keyboard macro.  Use human-readable strg
                          ;; Lambda form.  Use as much as possible, but uniquify (no such symbol name).
                          (t (let ((ii     1)
                                   (len    (length bname))
                                   (trial  (make-string (1+ bmkp-bookmark-name-length-max) 88)))
                               (while (and (< ii len)  (> (length trial) bmkp-bookmark-name-length-max))
                                 (setq trial  (make-temp-name (substring bname 0 (- ii)))))
                               (while (intern-soft
                                       (setq trial  (make-temp-name (substring bname 0 (- ii))))))
                               trial)))))
               (push (bmkp-bookmark-name-from-record (bmkp-make-function-bookmark fun-bmk-name fun))
                     bnames)))
            ((bmkp-sequence-bookmark-p bname) ; Sequence bookmark.
             (setq bnames (append (reverse (bookmark-prop-get bname 'sequence)) bnames)))
            ((stringp bname) (push bname bnames)) ; Bookmark name.
            ((bookmark-get-bookmark bname 'NOERROR) ; Full bookmark.
             (push (bmkp-bookmark-name-from-record bname) bnames))
            (t (error "Bad BOOKMARK-NAMES arg to `bmkp-set-sequence-bookmark': `%S'"
                      bookmark-names)))) ; Punt.
    (setq bnames  (nreverse bnames))
    (if (not exists)
        (when msgp (message "Creating sequence bookmark..."))
      (if (< (prefix-numeric-value arg) 0)
          (when msgp (message "REPLACING existing sequence bookmark...") (sit-for 0.5))
        (when msgp (message "%sing to sequence bookmark..." (if arg "Prepend" "Append")) (sit-for 0.5))
        (setq replacing  nil
              bnames     (if arg
                             (nconc bnames (bookmark-prop-get seq 'sequence))
                           (nconc (bookmark-prop-get seq 'sequence) bnames)))))
    (let ((bookmark-make-record-function `(lambda () (bmkp-make-sequence-record ',bnames))))
      (bookmark-set seqname))
    (when msgp (message "Sequence `%s' %s" seqname (if exists
                                                       (if replacing "replaced" "updated")
                                                     "created")))))

(defun bmkp-make-sequence-record (bookmark-names)
  "Create and return a sequence bookmark record.
BOOKMARK-NAMES is a list of names of the bookmarks to be invoked in
sequence."
  (let ((record  `(,@(bookmark-make-record-default 'NO-FILE 'NO-CONTEXT 0 nil 'NO-REGION)
                   (sequence . ,bookmark-names)
                   (handler  . bmkp-jump-sequence))))
    record))

(when (require 'kmacro nil t)           ; Emacs 22+

  (defun bmkp-set-kmacro-bookmark (bookmark-name keyboard-macro &optional msg-p)
    "Create a function bookmark named BOOKMARK-NAME from KEYBOARD-MACRO.
Prompt for BOOKMARK-NAME and the name of the keyboard macro to use.
With a prefix arg, use `last-kbd-macro' as the keyboard macro."
    (interactive
     (let ((bname  (bmkp-completing-read-lax "Bookmark"))
           (kmac   (if current-prefix-arg
                       last-kbd-macro
                     (symbol-function (intern (completing-read "Keyboard macro name: "
                                                               obarray
                                                               (lambda (elt)
                                                                 (and (fboundp elt)
                                                                      (or (stringp (symbol-function elt))
                                                                          (vectorp (symbol-function elt))
                                                                          (get elt 'kmacro))))
                                                               t))))))
       (list bname kmac 'MSG)))
    (let* ((bmk     (bmkp-get-bookmark-in-alist bookmark-name 'NOERROR))
           (exists  (and bmk  (bmkp-function-bookmark-p bmk))))
      (bmkp-make-function-bookmark bookmark-name (read-kbd-macro keyboard-macro 'NEED-VECTOR) msg-p)
      (when msg-p
        (message "Function bookmark `%s' %s" bookmark-name (if exists "replaced" "created")))))

  (defun bmkp-set-kmacro-list-bookmark (bookmark-name)
    "Save all current keyboard macros as a kmacro-list bookmark."
    (interactive (list (bmkp-completing-read-lax "Bookmark")))
    (let ((bookmark-make-record-function  (lambda ()
                                            (bmkp-make-kmacro-list-record
                                             (cons (kmacro-ring-head) kmacro-ring)))))
      (bookmark-set bookmark-name)))

  (defun bmkp-make-kmacro-list-record (kmacros)
    "Create and return a kmacro-list bookmark record.
KMACROS is the list of kmacros to save.  It has the same form as
`kmacro-ring'.

Each entry in KMACROS thus has the form (MACRO COUNTER FORMAT)."
    (let ((record  `(,@(bookmark-make-record-default 'NO-FILE 'NO-CONTEXT nil nil 'NO-REGION)
                     (kmacros      . ,kmacros)
                     (handler      . bmkp-jump-kmacro-list))))
      record))

  )

;;;###autoload (autoload 'bmkp-set-variable-list-bookmark "bookmark+")
(defun bmkp-set-variable-list-bookmark (variables)
  "Save a list of variables as a bookmark.
Interactively, read the variables to save, using
`bmkp-read-variables-completing'."
  (interactive (list (bmkp-read-variables-completing)))
  (let ((bookmark-make-record-function  (lexical-let ((vars  variables))
                                          (lambda () (bmkp-make-variable-list-record vars)))))
    (call-interactively #'bookmark-set)))

;; Not used in the Bookmark+ code.  Available for users to create varlist bookmark non-interactively.
(defun bmkp-create-variable-list-bookmark (bookmark-name vars vals &optional buffer-name)
  "Create a variable-list bookmark named BOOKMARK-NAME from VARS and VALS.
VARS and VALS are corresponding lists of variables and their values.

Optional arg BUFFER-NAME is the buffer name to use for the bookmark (a
string).  This is useful if some of the variables are buffer-local.
If BUFFER-NAME is nil, the current buffer name is recorded."
  (eval `(multiple-value-bind ,vars ',vals
          (let ((bookmark-make-record-function  (lexical-let ((vs   vars)
                                                              (buf  buffer-name))
                                                  (lambda () (bmkp-make-variable-list-record vs buf)))))
            (bookmark-set ,bookmark-name)))))

(defun bmkp-read-variables-completing (&optional option)
  "Read variable names with completion, and return them as a list of symbols.
Reads names one by one, until you hit `RET' twice consecutively.
Non-nil argument OPTION means read only user option names."
  (bookmark-maybe-load-default-file)
  (let ((var   (bmkp-read-variable "Variable (RET for each, empty input to finish): " option))
        (vars  ())
        old-var)
    (while (not (string= "" var))
      (add-to-list 'vars var)
      (setq var  (bmkp-read-variable "Variable: " option)))
    (nreverse vars)))

(defun bmkp-read-variable (prompt &optional option default-value)
  "Read name of a variable and return it as a symbol.
Prompt with string PROMPT.
With non-nil OPTION, read the name of a user option.
The default value is DEFAULT-VALUE if non-nil, or the nearest symbol
to the cursor if it is a variable."
  (setq option  (if option 'user-variable-p 'boundp))
  (let ((symb                                        (cond ((fboundp 'symbol-nearest-point)
                                                            (symbol-nearest-point)) ; In `thingatpt+.el'.
                                                           ((fboundp 'symbol-at-point) (symbol-at-point))
                                                           (t nil)))
        (enable-recursive-minibuffers                t)
        (icicle-unpropertize-completion-result-flag  t))
    (when (and default-value  (symbolp default-value))
      (setq default-value  (symbol-name default-value)))
    (intern (completing-read prompt obarray option t nil 'minibuffer-history
                             (or default-value (and (funcall option symb)  (symbol-name symb)))
                             t))))

(defun bmkp-make-variable-list-record (variables &optional buffer-name)
  "Create and return a variable-list bookmark record.
VARIABLES is the list of variables to save.
Each entry in VARIABLES is either a variable (a symbol) or a cons
 whose car is a variable and whose cdr is the variable's value.

Optional arg BUFFER-NAME is the buffer to use for the bookmark.  This
is useful if some of the variables are buffer-local.  If BUFFER-NAME
is nil, the current buffer is used."
  (let ((record  `(,@(bookmark-make-record-default 'NO-FILE 'NO-CONTEXT nil nil 'NO-REGION)
                   (filename     . ,bmkp-non-file-filename)
                   (variables    . ,(or (bmkp-printable-vars+vals variables)
                                        (error "No variables to bookmark")))
                   (handler      . bmkp-jump-variable-list))))
    (when buffer-name  (let ((bname  (assq 'buffer-name record)))  (setcdr bname buffer-name)))
    record))

(defun bmkp-printable-vars+vals (variables)
  "Return an alist of printable VARIABLES paired with their values.
Display a message for any variables that are not printable.
VARIABLES is the list of variables.  Each entry in VARIABLES is either
 a variable (a symbol) or a cons whose car is a variable and whose cdr
 is the variable's value."
  (let ((vars+vals     ())
        (unprintables  ()))
    (dolist (var  variables)
      (let ((val  (if (consp var) (cdr var) (symbol-value var))))
        (if (bmkp-readable-p val)
            (add-to-list 'vars+vals (if (consp var) var (cons var val)))
          (add-to-list 'unprintables var))))
    (when unprintables (message "Unsavable (unreadable) vars: %S" unprintables)  (sit-for 3))
    vars+vals))

;; Same as `savehist-printable' in `savehist-20+.el', except added `print-circle' binding.
(defun bmkp-readable-p (value)
  "Return non-nil if VALUE is Lisp-readable if printed using `prin1'."
  (cond ((numberp value))
        ((symbolp value))
        ((and (stringp value)           ; String with no text properties.
              (if (fboundp 'equal-including-properties) ; Emacs 22+.
                  (equal-including-properties value (substring-no-properties value))
                (and (null (text-properties-at 0 value))
                     (= 0 (next-property-change 0 value))))))
        (t (with-temp-buffer
             (condition-case nil
                 (let ((print-readably  t)
                       (print-level     nil)
                       (print-circle    bmkp-propertize-bookmark-names-flag))
                   (prin1 value (current-buffer)) ; Print value into a buffer and try to read back.
                   (read (point-min-marker))
                   t)
               (error nil))))))         ; Could not print and read back.

(when (require 'kmacro nil t)           ; Emacs 22

  (defun bmkp-jump-kmacro-list (bookmark)
    "Jump to kmacro-list bookmark BOOKMARK, restoring the keyboard macros.
Handler function for record returned by
`bmkp-make-kmacro-list-record'.
BOOKMARK is a bookmark name or a bookmark record."
    (let ((buf       (bmkp-get-buffer-name bookmark))
          (kbd-macs  (bookmark-prop-get bookmark 'kmacros)))
      (unless (and buf  (get-buffer buf))
        (message "Bookmarked for non-existent buffer `%s', so using current buffer" buf) (sit-for 3)
        (setq buf (current-buffer)))
      (with-current-buffer buf
        (let ((kmacs  kbd-macs))
          (when last-kbd-macro
            (kmacro-push-ring (list last-kbd-macro kmacro-counter kmacro-counter-format-start)))
          (kmacro-split-ring-element (pop kmacs))
          (dolist (kmac  kmacs) (kmacro-push-ring kmac))))
      (message "Keyboard macros restored in buffer `%s': %S" buf (mapcar #'car kbd-macs))
      (sit-for 3)))

  )

(defun bmkp-jump-variable-list (bookmark)
  "Jump to variable-list bookmark BOOKMARK, restoring the recorded values.
Handler function for record returned by
`bmkp-make-variable-list-record'.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((buf        (bmkp-get-buffer-name bookmark))
        (vars+vals  (bookmark-prop-get bookmark 'variables)))
    (unless (get-buffer buf)
      (message "Bookmarked for non-existent buffer `%s', so using current buffer" buf) (sit-for 3)
      (setq buf (current-buffer)))
    (with-current-buffer buf
      (dolist (var+val  vars+vals)
        (set (car var+val)  (cdr var+val))))
    (message "Variables restored in buffer `%s': %S" buf (mapcar #'car vars+vals))
    (sit-for 3)))

;; URL browse support
(defun bmkp-make-url-browse-record (url)
  "Create and return a url bookmark for `browse-url' to visit URL.
The handler is `bmkp-jump-url-browse'."
  (require 'browse-url)
  (let ((url-0  (copy-sequence url)))
    (set-text-properties 0 (length url) () url-0)
    `((filename . ,bmkp-non-file-filename)
      (location . ,url-0)
      (handler  . bmkp-jump-url-browse))))

(defun bmkp-jump-url-browse (bookmark)
  "Handler function for record returned by `bmkp-make-url-browse-record'.
BOOKMARK is a bookmark name or a bookmark record."
  (require 'browse-url)
  (let ((url  (bookmark-prop-get bookmark 'location)))
    (browse-url url)))


;; EWW support
(when (> emacs-major-version 24)        ; Emacs 25+

  (defvar bmkp-eww-new-buf-name nil
    "If non-nil, the name of the EWW buffer to jump to.
This is set by `bmkp-eww-rename-buffer' and used by
`bmkp-jump-eww-renaming-buffer'.")

  (defvar bmkp-eww-jumping-p  nil
    "Non-nil only if in dynamic scope of `bmkp-jump-eww-renaming-buffer'.")

  (defun bmkp-eww-title ()
    "Return the web-page title of the current `eww-mode' buffer."
    (plist-get eww-data :title))

  (defun bmkp-eww-url ()
    "Return the URL of the current `eww-mode' buffer."
    (eww-current-url))

  (defun bmkp-make-eww-record ()
    "Make a record for EWW buffers."
    (require 'eww)
    (let ((eww-title  (bmkp-eww-title)))
      `(,eww-title
        (buffer-name . ,(bmkp-eww-new-buffer-name))
        ,@(bookmark-make-record-default 'NO-FILE)
        (location . ,(bmkp-eww-url))
        (handler . bmkp-jump-eww))))

  (defun bmkp-eww-new-buffer-name ()
    "Return a new buffer name for the current `eww-mode' buffer.
The name format is determined by option `bmkp-eww-buffer-handling'."
    (if bmkp-eww-buffer-handling
        (concat "*eww*-" (bmkp-eww-title) (let ((url  (bmkp-eww-url)))
                                            (and (eq 'url bmkp-eww-buffer-handling)
                                                 (concat " " (if (>= (length url) 20)
                                                                 (substring url -20)
                                                               url)))))
      "*eww*"))

  (add-hook 'eww-mode-hook (lambda () (set (make-local-variable 'bookmark-make-record-function)
                                           'bmkp-make-eww-record)))

  (defun bmkp-jump-eww (bookmark)
    "Handler function for record returned by `bmkp-make-eww-record'.
BOOKMARK is a bookmark name or a bookmark record."
    (require 'eww)
    (if bmkp-eww-buffer-handling
        (bmkp-jump-eww-renaming-buffer bookmark)
      (bmkp-jump-eww-in-buffer-*eww* bookmark)))

  (defun bmkp-jump-eww-in-buffer-*eww* (bookmark)
    "Jump to EWW bookmark BOOKMARK in buffer `*eww*'."
    (require 'eww)
    (bmkp-eww-sans-pop-to-buffer (bookmark-location bookmark))
    ;; Wait until buffer has real content.
    (with-current-buffer (get-buffer-create "*eww*")
      (while (= (count-lines (point-min) (point-max)) 1) (sit-for 1)))
    (bookmark-default-handler `("" (buffer . "*eww*") . ,(bmkp-bookmark-data-from-record bookmark))))

  ;; VAR `bmkp-eww-new-buf-name' is free here.  It is bound in `bmkp-eww-rename-buffer'.
  (defun bmkp-jump-eww-renaming-buffer (bookmark)
    "Jump to EWW bookmark BOOKMARK, handling it per `bmkp-eww-buffer-handling'."
    (require 'eww)
    (let ((bmkp-eww-jumping-p  t)
          (buf                 (if (eq 'one bmkp-eww-buffer-handling)
                                   (bmkp-get-eww-mode-buffer)
                                 (get-buffer (bmkp-get-buffer-name bookmark)))))
      (when (or (not buf)  (and (eq 'url bmkp-eww-buffer-handling)
                                (not (equal (bookmark-prop-get bookmark 'location)
                                            (with-current-buffer buf (bmkp-eww-url))))))
        (setq buf  (get-buffer-create " *temp-name*")))
      (with-current-buffer buf
        (eww-mode)
        (bmkp-eww-sans-pop-to-buffer (bookmark-location bookmark))
        (while (= (count-lines (point-min) (point-max)) 1) (sit-for 1)))
      (when bmkp-eww-new-buf-name
        (set-buffer bmkp-eww-new-buf-name)
        (setq buf                    (current-buffer)
              bmkp-eww-new-buf-name  nil))
      (bookmark-default-handler
       `("" (buffer . ,buf) . ,(bmkp-bookmark-data-from-record bookmark)))))

  ;; This is `eww' from emacs-25, redefined to remove the call to `pop-to-buffer-same-window'.
  ;; The forms that usually follow `pop-to-buffer-same-window' are enclosed in `with-current-buffer' instead.
  (defun bmkp-eww-sans-pop-to-buffer (url)
    "Fetch URL and render the page.
If the input doesn't look like an URL or a domain name, the
word(s) will be searched for via `eww-search-prefix'."
    (interactive
     (let* ((uris (eww-suggested-uris))
            (prompt (concat "Enter URL or keywords"
                            (if uris (format " (default %s)" (car uris)) "")
                            ": ")))
       (list (read-string prompt nil nil uris))))
    (require 'eww)
    (setq url (string-trim url))
    (cond ((string-match-p "\\`file:/" url))
          ;; Don't mangle file: URLs at all.
          ((string-match-p "\\`ftp://" url)
           (user-error "FTP is not supported"))
          (t
           ;; Anything that starts with something that vaguely looks
           ;; like a protocol designator is interpreted as a full URL.
           (if (or (string-match "\\`[A-Za-z]+:" url)
                   ;; Also try to match "naked" URLs like
                   ;; en.wikipedia.org/wiki/Free software
                   (string-match "\\`[A-Za-z_]+\\.[A-Za-z._]+/" url)
                   (and (= (length (split-string url)) 1)
                        (or (and (not (string-match-p "\\`[\"'].*[\"']\\'" url))
                                 (> (length (split-string url "[.:]")) 1))
                            (string-match eww-local-regex url))))
               (progn
                 (unless (string-match-p "\\`[a-zA-Z][-a-zA-Z0-9+.]*://" url)
                   (setq url (concat "http://" url)))
                 ;; Some sites do not redirect final /
                 (when (string= (url-filename (url-generic-parse-url url)) "")
                   (setq url (concat url "/"))))
             (setq url (concat eww-search-prefix
                               (replace-regexp-in-string " " "+" url))))))
    ;; Call to `pop-to-buffer-same-window' was here, with the following
    ;; sexp as argument.  We use that argument as the BUFFER argument to
    ;; `with-current-buffer', and enclose the rest of the forms.
    (with-current-buffer
        (if (eq major-mode 'eww-mode)
            (current-buffer)
          (get-buffer-create "*eww*"))
      (eww-setup-buffer)
      (plist-put eww-data :url url)
      (plist-put eww-data :title "")
      (eww-update-header-line-format)
      (let ((inhibit-read-only t))
        (insert (format "Loading %s..." url))
        (goto-char (point-min)))
      (url-retrieve url 'eww-render
                    (list url nil (current-buffer)))))

  (defun bmkp-get-eww-mode-buffer ()
    "Return a buffer that is in `eww-mode', or nil if there is none."
    (catch 'bmkp-get-eww-mode-buffer
      (dolist (buf  (buffer-list))
        (when (with-current-buffer buf (derived-mode-p 'eww-mode))
          (throw 'bmkp-get-eww-mode-buffer buf)))
      nil))

  ;; The EWW buffer is renamed on each visit, if `bmkp-eww-buffer-handling' is non-nil.
  (eval-after-load "eww"
    '(when (> emacs-major-version 24)   ; Emacs 25+
      (add-hook   'eww-after-render-hook      'bmkp-eww-rename-buffer)
      (advice-add 'eww-restore-history :after 'bmkp-eww-rename-buffer)))

  (defun bmkp-eww-rename-buffer (&rest _ignored)
    "Rename current buffer according to option `bmkp-eww-buffer-handling'.
If a buffer with the new name already exists and this function is
called within the dynamic scope of `bmkp-jump-eww-renaming-buffer'
then set variable `bmkp-eww-new-buf-name' to the buffer name, so that
`bmkp-jump-eww-renaming-buffer' uses that buffer."
    (when bmkp-eww-buffer-handling
      (let ((new-bname  (bmkp-eww-new-buffer-name)))
        (condition-case err
            (rename-buffer new-bname)
          (error (if (and (buffer-live-p (get-buffer new-bname))  bmkp-eww-jumping-p)
                     (setq bmkp-eww-new-buf-name  new-bname) ; Save name for `bmkp-jump-eww-renaming-buffer'.
                   (error "%s" (error-message-string err))))))))

  ;; Eval this so that even if the library is byte-compiled with Emacs 20,
  ;; loading it into Emacs 22+ will define variable `bmkp-eww-auto-bookmark-mode'.
  (eval '(define-minor-mode bmkp-eww-auto-bookmark-mode
          "Toggle automatically setting a bookmark when you visit a URL with EWW.
The bookmark name is the title of the web page.

If option `bmkp-eww-auto-type' is `create-or-update' then such a
bookmark is created for the node if none exists.  If the option value
is `update-only' then no new bookmark is created automatically, but an
existing bookmark is updated.  (Updating a bookmark increments the
recorded number of visits.)  You can toggle the option using
`\\[bmkp-toggle-eww-auto-type]'."
          :init-value nil :global t :group 'bookmark-plus :require 'bookmark+
          :lighter bmkp-auto-idle-bookmark-mode-lighter ; @@@@@ RENAME THIS?
          :link `(url-link :tag "Send Bug Report"
                  ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
Bookmark bug: \
&body=Describe bug here, starting with `emacs -Q'.  \
Don't forget to mention your Emacs and library versions."))
          :link '(url-link :tag "Download" "http://www.emacswiki.org/bookmark+.el")
          :link '(url-link :tag "Description" "http://www.emacswiki.org/BookmarkPlus")
          :link '(emacs-commentary-link :tag "Commentary" "bookmark+")
          (cond (bmkp-eww-auto-bookmark-mode
                 (add-hook   'eww-after-render-hook      'bmkp-set-eww-bookmark-here)
                 (advice-add 'eww-restore-history :after 'bmkp-set-eww-bookmark-here))
                (t
                 (remove-hook   'eww-after-render-hook   'bmkp-set-eww-bookmark-here)
                 (advice-remove 'eww-restore-history     'bmkp-set-eww-bookmark-here)))
          (when (interactive-p)
            (message "Automatic EWW bookmarking is now %s" (if bmkp-eww-auto-bookmark-mode "ON" "OFF")))))

  (defun bmkp-set-eww-bookmark-here (&optional nomsg)
    "Set an EWW bookmark for the URL of the current EWW buffer.
The current buffer is assumed to be in `eww-mode' and visiting a URL."
    (interactive)
    (let* ((bname   (bmkp-eww-title))
           (url     (bmkp-eww-url))
           (bmk     (bookmark-get-bookmark bname 'NO-ERROR))
           (visits  (and bmk  (bookmark-prop-get bmk 'visits))))
      (when bname
        (cond ((and (not visits)  (eq bmkp-eww-auto-type 'create-or-update))
               (bookmark-set bname)
               (unless nomsg (message "Created EWW bookmark `%s'" bname)))
              (visits
               (bmkp-record-visit bname 'BATCHP)
               (bmkp-refresh/rebuild-menu-list bname nil)
               (bmkp-maybe-save-bookmarks)
               (unless nomsg (message "Updated EWW bookmark `%s'" bname)))))))

  (defun bmkp-toggle-eww-auto-type (&optional msgp)
    "Toggle the value of option `bmkp-eww-auto-type'."
    (interactive "p")
    (setq bmkp-eww-auto-type  (if (eq bmkp-eww-auto-type 'create-or-update) 'update-only 'create-or-update))
    (when msgp (message "`bmkp-eww-auto-bookmark-mode' now %s"
                        (if (eq bmkp-eww-auto-type 'create-or-update)
                            "CREATES, as well as updates, EWW bookmarks"
                          "only UPDATES EXISTING EWW bookmarks"))))


  ;; You can use this to convert existing EWW bookmarks to Bookmark+ bookmarks.
  ;;
  (defun bmkp-convert-eww-bookmarks (eww-file bmk-file &optional msgp)
    "Add bookmarks from EWW-FILE to BMK-FILE.
EWW-FILE is a file of \"bookmarks\" created by EWW, which are not
compatible with Emacs bookmarks.  EWW-FILE is not modified.

BMK-FILE is a Bookmark+ bookmarks file, which is an ordinary Emacs
bookmarks file (possibly with Bookmark+-specific bookmarks).

If BMK-FILE exists then it is updated to include the converted
bookmarks.  If it does not exist then it is created."
    (interactive
     (let* ((std-default  (bmkp-default-bookmark-file))
            (default      (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                              (if (bmkp-same-file-p bmkp-current-bookmark-file std-default)
                                  bookmark-default-file
                                std-default)
                            bmkp-last-bookmark-file)))
       (list (bmkp-read-bookmark-file-name "EWW bookmark file: "
                                           nil
                                           (expand-file-name "eww-bookmarks" user-emacs-directory)
                                           t)
             (bmkp-read-bookmark-file-name "Emacs bookmark file to update: "
                                           (or (file-name-directory default)  "~/")
                                           (if (bmkp-same-file-p bmkp-current-bookmark-file
                                                                 bmkp-last-bookmark-file)
                                               (bmkp-default-bookmark-file)
                                             bmkp-last-bookmark-file))
             t)))
    (when (file-directory-p eww-file) (error "`%s' is a directory, not a file" eww-file))
    (unless (file-readable-p eww-file) (error "Cannot read bookmark file `%s'" eww-file))
    (when (file-directory-p bmk-file) (error "`%s' is a directory, not a file" bmk-file))
    (unless (file-readable-p bmk-file) (bmkp-empty-file bmk-file)) ; Create empty bookmark file.
    (with-temp-buffer
      (insert-file-contents eww-file)
      (let ((bookmark-alist  ())
            url title created bmk)
        (dolist (ebmk  (read (current-buffer)))
          (setq url      (plist-get ebmk :url)
                title    (plist-get ebmk :title)
                created  (date-to-time (plist-get ebmk :time))
                bmk      `(,title
                           ,@(bookmark-make-record-default 'NO-FILE)
                           (location . ,url)
                           (handler . bmkp-jump-eww)))
          (let ((buf-cell  (assq 'buffer-name bmk))) (setcdr buf-cell "*eww*"))
          (let ((created-cell  (assq 'created bmk))) (setcdr created-cell created))
          (push bmk bookmark-alist))
        (bookmark-write-file bmk-file 'ADD)))
    (when msgp (message "Wrote Bookmark file `%s'" bmk-file)))

  )

;; W3M support
(defun bmkp-make-w3m-record ()
  "Make a special entry for w3m buffers."
  (require 'w3m)                        ; For `w3m-current-url'.
  `(,w3m-current-title
    ,@(bookmark-make-record-default 'NO-FILE)
    (location . ,w3m-current-url)
    (handler . bmkp-jump-w3m)))

(add-hook 'w3m-mode-hook (lambda () (set (make-local-variable 'bookmark-make-record-function)
                                         'bmkp-make-w3m-record)))

(defun bmkp-w3m-set-new-buffer-name ()
  "Set the w3m buffer name according to the number of W3M buffers already open."
  (require 'w3m)                        ; For `w3m-list-buffers'.
  (let ((len  (length (w3m-list-buffers 'nosort))))
    (if (= len 0)  "*w3m*"  (format "*w3m*<%d>" (1+ len)))))

(defalias 'bmkp-jump-w3m-new-session 'bmkp-jump-w3m-new-buffer)
(defun bmkp-jump-w3m-new-buffer (bookmark)
  "Jump to W3M bookmark BOOKMARK in a new buffer (in a new W3M tab)."
  (require 'w3m)
  (let ((buf   (bmkp-w3m-set-new-buffer-name)))
    (w3m-browse-url (bookmark-location bookmark) 'newsession)
    (while (not (get-buffer buf)) (sit-for 1)) ; Be sure we have the W3M buffer.
    (with-current-buffer (get-buffer-create buf)
      (goto-char (point-min))
      ;; Wait until data arrives in buffer, before setting region.
      (while (eq (line-beginning-position) (line-end-position)) (sit-for 1)))
    (bookmark-default-handler `("" (buffer . ,buf) . ,(bmkp-bookmark-data-from-record bookmark)))))

(defalias 'bmkp-jump-w3m-only-one-tab 'bmkp-jump-w3m-only-one-buffer)
(defun bmkp-jump-w3m-only-one-buffer (bookmark)
  "Close all W3M sessions and jump to BOOKMARK in a new W3M buffer."
  (require 'w3m)
  (w3m-quit 'force)                     ; Be sure we start with an empty W3M buffer.
  (w3m-browse-url (bookmark-location bookmark))
  (with-current-buffer (get-buffer-create "*w3m*") (while (eq (point-min) (point-max)) (sit-for 1)))
  (bookmark-default-handler `("" (buffer . "*w3m*") . ,(bmkp-bookmark-data-from-record bookmark))))

(defalias 'bmkext-jump-w3m 'bmkp-jump-w3m)
(defun bmkp-jump-w3m (bookmark)
  "Handler function for record returned by `bmkp-make-w3m-record'.
BOOKMARK is a bookmark name or a bookmark record.
Use a new buffer (tab) if `bmkp-w3m-allow-multiple-buffers-flag' is
non-nil."
  (require 'w3m)
  (if bmkp-w3m-allow-multiple-buffers-flag
      (bmkp-jump-w3m-new-buffer bookmark)
    (bmkp-jump-w3m-only-one-buffer bookmark)))


;; GNUS support for Emacs < 24.  More or less the same as `gnus-summary-bookmark-make-record' in Emacs 24+.
;; But this:
;;
;; * Works for other Emacs versions as well.
;; * Requires `gnus.el'.
;; * Adds a `bmkp-non-file-filename' `filename' entry.
;; * Uses `bmkp-jump-gnus', not `gnus-summary-bookmark-jump' as the handler.
;;
(defun bmkp-make-gnus-record ()
  "Make a bookmark entry for a Gnus summary buffer.
Current buffer can be the article buffer or the summary buffer."
  (require 'gnus)
  (let ((pos  nil)
        buf)
    ;; If in article buffer, record point and buffer, then go to summary buffer
    ;; and record bookmark there.
    (unless (and (if (fboundp 'derived-mode-p)
                     (derived-mode-p 'gnus-summary-mode)
                   (eq major-mode 'gnus-summary-mode))
                 gnus-article-current)
      (setq buf                      "art"
            bookmark-yank-point      (point)
            bookmark-current-buffer  (current-buffer))
      (save-restriction (widen) (setq pos  (point))) ; Position in article buffer.
      (gnus-article-show-summary))
    (let* ((grp   (car gnus-article-current))
           (art   (cdr gnus-article-current))
           (head  (gnus-summary-article-header art))
           (id    (mail-header-id head)))
      (unless buf (setq buf  "sum"))
      `((elt (gnus-summary-article-header) 1) ; Subject.
        ,@(condition-case
           nil
           (bookmark-make-record-default ; POS = nil if started in summary buffer.
            'NO-FILE 'NO-CONTEXT pos nil 'NO-REGION)
           (wrong-number-of-arguments (bookmark-make-record-default 'POINT-ONLY)))
        (location . ,(format "Gnus-%s %s:%d:%s" buf grp art id))
        (filename . ,bmkp-non-file-filename) (group . ,grp) (article . ,art) (message-id . ,id)
        (handler . bmkp-jump-gnus)))))  ; Vanilla Emacs 24+ uses `gnus-summary-bookmark-jump'.


;; Vanilla Emacs 24+ uses `gnus-summary-bookmark-make-record' for these hooks.
;; Better to use `bmkp-make-gnus-record' even for Emacs 24+, because `bmkp-jump-gnus' is better than
;; `gnus-summary-bookmark-jump' (no `sit-for' if article buffer not needed).

;; $$$$$$ (unless (> emacs-major-version 23) ; Emacs 24 has `gnus-summary-bookmark-make-record'.
(add-hook 'gnus-summary-mode-hook (lambda ()
                                    (set (make-local-variable 'bookmark-make-record-function)
                                         'bmkp-make-gnus-record)))

;; $$$$$$ (unless (> emacs-major-version 23) ; Emacs 24 has `gnus-summary-bookmark-make-record'.
(add-hook 'gnus-article-mode-hook (lambda ()
                                    (set (make-local-variable 'bookmark-make-record-function)
                                         'bmkp-make-gnus-record)))

;; More or less the same as `gnus-summary-bookmark-jump' in Emacs 24+.
;; But this does not `sit-for' unless BUF is "Gnus-art".
;;
(defun bmkp-jump-gnus (bookmark)
  "Handler function for record returned by `bmkp-make-gnus-record'.
BOOKMARK is a bookmark name or a bookmark record."
  (let* ((group    (bookmark-prop-get bookmark 'group))
         (article  (bookmark-prop-get bookmark 'article))
         (id       (bookmark-prop-get bookmark 'message-id))
         (loc      (bookmark-prop-get bookmark 'location))
         (buf      (if loc (car (split-string loc)) (bookmark-prop-get bookmark 'buffer))))
    (if (< emacs-major-version 22) (gnus-fetch-group group) (gnus-fetch-group group (list article)))
    (gnus-summary-insert-cached-articles)
    (gnus-summary-goto-article id nil 'force)
    ;; Go to article buffer if appropriate.  Wait for it to be ready, so `bookmark-default-handler' has time
    ;; to set the right position.
    (when (equal buf "Gnus-art")  (sit-for 1) (other-window 1))
    (bookmark-default-handler `("" (buffer . ,buf) . ,(bmkp-bookmark-data-from-record bookmark)))))

(defun bmkext-jump-gnus (bookmark)      ; Compatibility code.
  "`gnus-summary-bookmark-jump' if defined, else `bmkp-jump-gnus'."
  (if (fboundp 'gnus-summary-bookmark-jump)
      (gnus-summary-bookmark-jump bookmark) ; Emacs 24
    (bmkp-jump-gnus bookmark)))


;; `man' and `woman' support for Emacs < 24.

(when (> emacs-major-version 20)
  (defun bmkp-make-woman-record ()
    "Create bookmark record for `man' page bookmark created by `woman'."
    `(,@(bookmark-make-record-default 'NO-FILE)
      (filename . ,woman-last-file-name) (handler . bmkp-jump-woman)))

  (unless (> emacs-major-version 23)
    (add-hook 'woman-mode-hook (lambda ()
                                 (set (make-local-variable 'bookmark-make-record-function)
                                      'bmkp-make-woman-record)))))

(defun bmkp-make-man-record ()
  "Create bookmark record for `man' page bookmark created by `man'."
  `(,@(bookmark-make-record-default 'NO-FILE)
    (filename . ,bmkp-non-file-filename)
    (man-args . ,Man-arguments) (handler . bmkp-jump-man)))

(unless (> emacs-major-version 23)
  (add-hook 'Man-mode-hook (lambda () (set (make-local-variable 'bookmark-make-record-function)
                                           'bmkp-make-man-record))))

(defun bmkext-jump-woman (bookmark)     ; Compatibility code.
  "`woman-bookmark-jump' if defined, else `bmkp-jump-woman'."
  (if (fboundp 'woman-bookmark-jump)
      (woman-bookmark-jump bookmark)    ; Emacs 24
    (bmkp-jump-woman bookmark)))

(defun bmkp-jump-woman (bookmark)
  "Handler function for `man' page bookmark created by `woman'.
BOOKMARK is a bookmark name or a bookmark record."
  (unless (> emacs-major-version 20)
    (error "`woman' bookmarks are not supported in Emacs prior to Emacs 21"))
  (bookmark-default-handler
   `("" (buffer . ,(save-window-excursion (woman-find-file (bookmark-get-filename bookmark))
                                          (current-buffer)))
     . ,(bmkp-bookmark-data-from-record bookmark))))

(defun bmkext-jump-man (bookmark)       ; Compatibility code.
  "`Man-bookmark-jump' if defined, else `bmkp-jump-man'."
  (if (fboundp 'Man-bookmark-jump)
      (Man-bookmark-jump bookmark)      ; Emacs 24
    (bmkp-jump-man bookmark)))

(defun bmkp-jump-man (bookmark)
  "Handler function for `man' page bookmark created by `man'.
BOOKMARK is a bookmark name or a bookmark record."
  (require 'man)
  (let* ((man-args           (bookmark-prop-get bookmark 'man-args))
         ;; `Man-notify-method' binding needs to be in effect during the calls to both
         ;; `Man-getpage-in-background' and `accept-process-output'.
         (Man-notify-method  (case bmkp-jump-display-function
                               ((nil display-buffer)  'quiet)
                               (switch-to-buffer      'pushy)
                               ((bmkp-select-buffer-other-window
                                 switch-to-buffer-other-window
                                 pop-to-buffer)
                                'friendly)
                               (t                     'quiet)))
         (buf                (Man-getpage-in-background man-args))
         (proc               (and (bufferp buf) ; Emacs 24+
                                  (get-buffer-process buf))))
    (if proc
        (while (and proc (eq (process-status proc) 'run)) (accept-process-output proc))
      (while (get-process "man") (sit-for 0.2)))
    (bookmark-default-handler (bookmark-get-bookmark bookmark))))

(defun bmkp-dired-remember-*-marks (beg end)
  "Return a list of the files and subdirs marked `*' in Dired."
  (when selective-display (let ((inhibit-read-only  t)) (subst-char-in-region beg end ?\r ?\n)))
  (let ((mfiles  ())
        fil)
    (save-excursion (goto-char beg)
                    (while (re-search-forward "^\\*" end t) ; Not `dired-re-mark' - match only `*' marks.
                      (when (setq fil  (dired-get-filename nil t)) (push fil mfiles))))
    (nreverse mfiles)))

(defun bmkp-make-dired-record ()
  "Create and return a Dired bookmark record."
  (let ((hidden-dirs  (save-excursion (dired-remember-hidden))))
    (unwind-protect
         (let ((dir      (expand-file-name (if (consp dired-directory)
                                               (file-name-directory (car dired-directory))
                                             dired-directory)))
               (subdirs  (bmkp-dired-subdirs))
               (mfiles   (bmkp-dired-remember-*-marks (point-min) (point-max))))
           `(,dir
             ,@(bookmark-make-record-default 'NO-FILE)
             (filename . ,dir) (dired-directory . ,dired-directory)
             (dired-marked . ,mfiles) (dired-switches . ,dired-actual-switches)
             (dired-subdirs . ,subdirs) (dired-hidden-dirs . ,hidden-dirs)
             (handler . bmkp-jump-dired)))
      (save-excursion                   ; Hide subdirs that were hidden.
        (dolist (dir  hidden-dirs)  (when (dired-goto-subdir dir) (dired-hide-subdir 1)))))))

;;;###autoload (autoload 'bmkp-dired-subdirs "bookmark+")
(defun bmkp-dired-subdirs ()
  "Alist of inserted subdirectories, without their positions (markers).
This is like `dired-subdir-alist' but without the top-level dir and
without subdir positions (markers)."
  (interactive)
  (let ((subdir-alist      (cdr (reverse dired-subdir-alist))) ; Remove top.
        (subdirs-wo-posns  ()))
    (dolist (sub  subdir-alist)  (push (list (car sub)) subdirs-wo-posns))
    subdirs-wo-posns))

(add-hook 'dired-mode-hook (lambda () (set (make-local-variable 'bookmark-make-record-function)
                                           'bmkp-make-dired-record)))

(defun bmkp-jump-dired (bookmark)
  "Jump to Dired bookmark BOOKMARK.
Handler function for record returned by `bmkp-make-dired-record'.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((dir          (bookmark-prop-get bookmark 'dired-directory))
        (mfiles       (bookmark-prop-get bookmark 'dired-marked))
        (switches     (bookmark-prop-get bookmark 'dired-switches))
        (subdirs      (bookmark-prop-get bookmark 'dired-subdirs))
        (hidden-dirs  (bookmark-prop-get bookmark 'dired-hidden-dirs)))
    (case bmkp-jump-display-function
      ((nil switch-to-buffer display-buffer)         (dired dir switches))
      ((bmkp-select-buffer-other-window pop-to-buffer switch-to-buffer-other-window)
       (dired-other-window dir switches))
      (t                                             (dired dir switches)))
    (let ((inhibit-read-only  t))
      (dired-insert-old-subdirs subdirs)
      (dired-mark-remembered (mapcar (lexical-let ((dd  dir))
                                       (lambda (mf) (cons (expand-file-name mf dd) 42)))
                                     mfiles))
      (save-excursion (dolist (dir  hidden-dirs) (when (dired-goto-subdir dir) (dired-hide-subdir 1)))))
    (let ((pos  (bookmark-get-position bookmark))) (when pos (goto-char pos)))))

(defun bmkp-read-bookmark-for-type (type alist &optional other-win pred hist action prompt)
  "Read the name of a bookmark of type TYPE, with completion.
TYPE is a string used in the prompt: \"Jump to TYPE bookmark: \".
ALIST is the alist used for completion.  If nil then raise an error to
 let the user know there are no bookmarks of type TYPE.
Non-nil OTHER-WIN means append \" in another window\" to the prompt.
Non-nil PRED is a predicate used for bookmark-name completion.
Non-nil HIST is a history symbol.  Default is `bookmark-history'.
Non-nil ACTION is the action mentioned in the prompt; nil: `Jump to '.
Non-nil PROMPT is an alternative prompt."
  (unless alist (error "No bookmarks of type %s" type))
  (bookmark-completing-read (or prompt  (concat (or action  "Jump to ") type " bookmark"
                                                (and other-win  " in another window")))
                            (bmkp-default-bookmark-name alist)
                            alist pred hist))

;;;###autoload (autoload 'bmkp-jump-to-type "bookmark+")
(defun bmkp-jump-to-type (bookmark-name &optional flip-use-region-p) ; `C-x j :'
  "Jump to a bookmark of a given type.  You are prompted for the type.
Otherwise, this is the same as `bookmark-jump' - see that, in
particular, for info about using a prefix argument.

When prompted for the type, you can use completion against the known
bookmark types (see `bmkp-types-alist').

Completion is lax, so you can also enter the name of a bookmark
`handler' or `file-handler' function, without completion.  Bookmarks
with that entry value are then the jump candidates."
  (interactive
   (let* ((completion-ignore-case                      t)
          (type-cands                                  bmkp-types-alist)
          (icicle-unpropertize-completion-result-flag  t)
          (type                                        (completing-read "Type of bookmark: " type-cands))
          (history                                     (assoc-default type type-cands))
          (alist                                       (if history
                                                           (funcall
                                                            (intern (format "bmkp-%s-alist-only" type)))
                                                         bookmark-alist))
          (bmk-name                                    (bmkp-read-bookmark-for-type
                                                        type alist nil
                                                        ;; PREDICATE if not a recognized type name.
                                                        (and (not history)
                                                             (bmkp-handler-pred (intern type)))
                                                        history)))
     (list bmk-name  (or (equal type "Region") current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-jump-to-type-other-window "bookmark+")
(defun bmkp-jump-to-type-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j :'
  "`bmkp-jump-to-type', but in another window."
  (interactive
   (let* ((completion-ignore-case                      t)
          (type-cands                                  bmkp-types-alist)
          (icicle-unpropertize-completion-result-flag  t)
          (type                                        (completing-read "Type of bookmark: " type-cands))
          (history                                     (assoc-default type type-cands))
          (alist                                       (if history
                                                           (funcall
                                                            (intern (format "bmkp-%s-alist-only" type)))
                                                         bookmark-alist))
          (bmk-name                                    (bmkp-read-bookmark-for-type
                                                        type alist t
                                                        ;; PREDICATE if not a recognized type name.
                                                        (and (not history)
                                                             (bmkp-handler-pred (intern type)))
                                                        history)))
     (list bmk-name (or (equal type "Region") current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

(defun bmkp-handler-pred (type)
  "Return a bookmark predicate that tests bookmarks with handler TYPE.
More precisely, the predicate returns non-nil if TYPE is either the
bookmark's `handler' or `file-handler' entry value."
  `(lambda (bmk)
    (member ',type `(,(bookmark-prop-get bmk 'file-handler) ,(bookmark-get-handler bmk)))))

;;;###autoload (autoload 'bmkp-autonamed-jump "bookmark+")
(defun bmkp-autonamed-jump (bookmark-name) ; `C-x j #'
  "Jump to an autonamed bookmark.
This is a specialization of `bookmark-jump'."
  (interactive
   (let ((alist  (bmkp-autonamed-alist-only)))
     (list (bmkp-read-bookmark-for-type "autonamed" alist nil nil 'bmkp-autonamed-history))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer))

;;;###autoload (autoload 'bmkp-autonamed-jump-other-window "bookmark+")
(defun bmkp-autonamed-jump-other-window (bookmark-name) ; `C-x 4 j # #'
  "`bmkp-autonamed-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-autonamed-alist-only)))
     (list (bmkp-read-bookmark-for-type "autonamed" alist t nil 'bmkp-autonamed-history))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window))

;;;###autoload (autoload 'bmkp-autonamed-this-buffer-jump "bookmark+")
(defun bmkp-autonamed-this-buffer-jump (bookmark-name) ; `C-x j , #'
  "Jump to an autonamed bookmark in the current buffer.
This is a specialization of `bookmark-jump'."
  (interactive
   (let ((alist  (bmkp-autonamed-this-buffer-alist-only)))
     (list (bmkp-read-bookmark-for-type "autonamed" alist nil nil 'bmkp-autonamed-history))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer))

;;;###autoload (autoload 'bmkp-autonamed-this-buffer-jump-other-window "bookmark+")
(defun bmkp-autonamed-this-buffer-jump-other-window (bookmark-name) ; `C-x 4 j # .'
  "`bmkp-autonamed-this-buffer-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-autonamed-this-buffer-alist-only)))
     (list (bmkp-read-bookmark-for-type "autonamed" alist t nil 'bmkp-autonamed-history))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window))

;;;###autoload (autoload 'bmkp-bookmark-list-jump "bookmark+")
(defun bmkp-bookmark-list-jump (bookmark-name &optional flip-use-region-p) ; `C-x j B'
  "Jump to a bookmark-list bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-bookmark-list-alist-only)))
     (list (bmkp-read-bookmark-for-type "bookmark-list" alist nil nil 'bmkp-bookmark-list-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-desktop-jump "bookmark+")
(defun bmkp-desktop-jump (bookmark-name &optional flip-use-region-p) ; `C-x j K'
  "Jump to a desktop bookmark.
If option `bmkp-desktop-jump-save-before-flag' is non-nil, and if the
current desktop was made current by jumping to a bookmark, then save
it before jumping to the next desktop.

This command is a specialization of `bookmark-jump' - see that, in
particular for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-desktop-alist-only)))
     (list (bmkp-read-bookmark-for-type "desktop" alist nil nil 'bmkp-desktop-history)
           current-prefix-arg)))
  (when bmkp-desktop-jump-save-before-flag (bmkp-desktop-save-as-last))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p)
  (setq bmkp-desktop-current-file  (bookmark-prop-get bookmark-name 'desktop-file)))

;;;###autoload (autoload 'bmkp-dired-jump "bookmark+")
(defun bmkp-dired-jump (bookmark-name &optional flip-use-region-p) ; `C-x j d', (`J' in Dired)
  "Jump to a Dired bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-dired-alist-only)))
     (list (bmkp-read-bookmark-for-type "Dired" alist nil nil 'bmkp-dired-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-dired-jump-other-window "bookmark+")
(defun bmkp-dired-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j d'
  "`bmkp-dired-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-dired-alist-only)))
     (list (bmkp-read-bookmark-for-type "Dired" alist t nil 'bmkp-dired-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-dired-this-dir-jump "bookmark+")
(defun bmkp-dired-this-dir-jump (bookmark-name &optional flip-use-region-p) ; `C-x j . d', (`C-j' in Dired)
  "Jump to a Dired bookmark for the `default-directory'.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-dired-this-dir-alist-only)))
     (list (bmkp-read-bookmark-for-type "Dired-for-this-dir " alist nil nil 'bmkp-dired-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-dired-this-dir-jump-other-window "bookmark+")
(defun bmkp-dired-this-dir-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j C-d'
  "`bmkp-dired-this-dir-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-dired-this-dir-alist-only)))
     (list (bmkp-read-bookmark-for-type "Dired-for-this-dir" alist t nil 'bmkp-dired-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

(when (fboundp 'bmkp-eww-alist-only)    ; Emacs 25+

  ;; ;;;###autoload (autoload 'bmkp-eww-jump "bookmark+")
  (defun bmkp-eww-jump (bookmark-name &optional flip-use-region-p) ; `C-x j e'
    "Jump to an EWW bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
    (interactive
     (let ((alist  (bmkp-eww-alist-only)))
       (list (bmkp-read-bookmark-for-type "EWW" alist nil nil 'bmkp-eww-history)
             current-prefix-arg)))
    (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

  ;; ;;;###autoload (autoload 'bmkp-eww-jump-other-window "bookmark+")
  (defun bmkp-eww-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j e'
    "`bmkp-eww-jump', but in another window."
    (interactive
     (let ((alist  (bmkp-eww-alist-only)))
       (list (bmkp-read-bookmark-for-type "EWW" alist t nil 'bmkp-eww-history)
             current-prefix-arg)))
    (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

  )

;;;###autoload (autoload 'bmkp-file-jump "bookmark+")
(defun bmkp-file-jump (bookmark-name &optional flip-use-region-p) ; `C-x j f'
  "Jump to a file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "file" alist nil nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-file-jump-other-window "bookmark+")
(defun bmkp-file-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j f'
  "`bmkp-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "file" alist t nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-file-this-dir-jump "bookmark+")
(defun bmkp-file-this-dir-jump (bookmark-name &optional flip-use-region-p) ; `C-x j . f'
  "Jump to a bookmark for a file or subdir in the `default-directory'.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-file-this-dir-alist-only)))
     (list (bmkp-read-bookmark-for-type "file-in-this-dir" alist nil nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-file-this-dir-jump-other-window "bookmark+")
(defun bmkp-file-this-dir-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j . f'
  "`bmkp-file-this-dir-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-file-this-dir-alist-only)))
     (list (bmkp-read-bookmark-for-type "file-in-this-dir" alist t nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-gnus-jump "bookmark+")
(defun bmkp-gnus-jump (bookmark-name &optional flip-use-region-p) ; `C-x j g', (`j' in Gnus summary mode)
  "Jump to a Gnus bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-gnus-alist-only)))
     (list (bmkp-read-bookmark-for-type "Gnus" alist nil nil 'bmkp-gnus-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-gnus-jump-other-window "bookmark+")
(defun bmkp-gnus-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j g'
  "`bmkp-gnus-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-gnus-alist-only)))
     (list (bmkp-read-bookmark-for-type "Gnus" alist t nil 'bmkp-gnus-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-image-jump "bookmark+")
(defun bmkp-image-jump (bookmark-name &optional flip-use-region-p) ; `C-x j M-i'
  "Jump to an image-file bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-image-alist-only)))
     (list (bmkp-read-bookmark-for-type "image" alist nil nil 'bmkp-image-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-image-jump-other-window "bookmark+")
(defun bmkp-image-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x j M-i'
  "`bmkp-image-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-image-alist-only)))
     (list (bmkp-read-bookmark-for-type "image" alist t nil 'bmkp-image-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-info-jump "bookmark+")
(defun bmkp-info-jump (bookmark-name &optional flip-use-region-p) ; `C-x j i', (`j' in Info)
  "Jump to an Info bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-info-alist-only)))
     (list (bmkp-read-bookmark-for-type "Info" alist nil nil 'bmkp-info-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-info-jump-other-window "bookmark+")
(defun bmkp-info-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j i'
  "`bmkp-info-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-info-alist-only)))
     (list (bmkp-read-bookmark-for-type "Info" alist t nil 'bmkp-info-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-local-file-jump "bookmark+")
(defun bmkp-local-file-jump (bookmark-name &optional flip-use-region-p) ; `C-x j l'
  "Jump to a local file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-local-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "local file" alist nil nil 'bmkp-local-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-local-file-jump-other-window "bookmark+")
(defun bmkp-local-file-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j l'
  "`bmkp-local-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-local-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "local file" alist t nil 'bmkp-local-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-local-non-dir-file-jump "bookmark+")
(defun bmkp-local-non-dir-file-jump (bookmark-name &optional flip-use-region-p) ; Not bound.
  "Jump to a local non-directory file bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-local-non-dir-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "local non-dir file" alist nil nil 'bmkp-local-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-local-non-dir-file-jump-other-window "bookmark+")
(defun bmkp-local-non-dir-file-jump-other-window (bookmark-name &optional flip-use-region-p) ; Not bound.
  "`bmkp-local-non-dir-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-local-non-dir-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "local non-dir file" alist t nil 'bmkp-local-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-man-jump "bookmark+")
(defun bmkp-man-jump (bookmark-name &optional flip-use-region-p) ; `C-x j m', (`j' in Man)
  "Jump to a `man'-page bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-man-alist-only)))
     (list (bmkp-read-bookmark-for-type "`man'" alist nil nil 'bmkp-man-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-man-jump-other-window "bookmark+")
(defun bmkp-man-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j m'
  "`bmkp-man-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-man-alist-only)))
     (list (bmkp-read-bookmark-for-type "`man'" alist t nil 'bmkp-man-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-non-dir-file-jump "bookmark+")
(defun bmkp-non-dir-file-jump (bookmark-name &optional flip-use-region-p) ; Not bound.
  "Jump to a non-directory file bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-non-dir-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "non-dir file" alist nil nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-non-dir-file-jump-other-window "bookmark+")
(defun bmkp-non-dir-file-jump-other-window (bookmark-name &optional flip-use-region-p) ; Not bound.
  "`bmkp-non-dir-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-non-dir-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "non-dir file" alist t nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-non-file-jump "bookmark+")
(defun bmkp-non-file-jump (bookmark-name &optional flip-use-region-p) ; `C-x j b', (`j' in Buffer Menu)
  "Jump to a non-file (buffer) bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-non-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "non-file (buffer)" alist nil nil 'bmkp-non-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-non-file-jump-other-window "bookmark+")
(defun bmkp-non-file-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j b'
  "`bmkp-non-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-non-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "non-file (buffer)" alist t nil 'bmkp-non-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-region-jump "bookmark+")
(defun bmkp-region-jump (bookmark-name) ; `C-x j r'
  "Jump to a region bookmark.  Select the region.
This is a specialization of `bookmark-jump', but without a prefix arg."
  (interactive (list (bmkp-read-bookmark-for-type "region" (bmkp-region-alist-only) nil nil
                                                  'bmkp-region-history)))
  (let ((bmkp-use-region  t)) (bmkp-jump-1 bookmark-name 'switch-to-buffer)))

;;;###autoload (autoload 'bmkp-region-jump-other-window "bookmark+")
(defun bmkp-region-jump-other-window (bookmark-name) ; `C-x 4 j r'
  "`bmkp-region-jump', but in another window."
  (interactive (list (bmkp-read-bookmark-for-type "region" (bmkp-region-alist-only) t nil
                                                  'bmkp-region-history)))
  (let ((bmkp-use-region  t)) (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window)))

;; This command accepts no argument.  It calls another command interactively, which reads the bookmark name.
;;
;;;###autoload (autoload 'bmkp-region-jump-narrow-indirect-other-window "bookmark+")
(defun bmkp-region-jump-narrow-indirect-other-window ()
  "Jump to a region bookmark and narrow to it in a cloned indirect buffer.
You are prompted for the region bookmark.

The region is selected as usual, in the bookmarked file/buffer.  A
separate window is opened on the region text, for the cloned indirect
buffer.

You need library `narrow-indirect.el' to use this command."
  (interactive)
  (unless (require 'narrow-indirect nil t)
    (error "You need library `narrow-indirect.el' for this command"))
  (let ((bmkp-handle-region-function  'bmkp-handle-region+narrow-indirect))
    (call-interactively
     (if (and (boundp 'icicle-mode)  icicle-mode) ; Icicles
         #'icicle-bookmark-region-other-window
       #'bmkp-region-jump-other-window))))

(defun bmkp-handle-region+narrow-indirect (bookmark)
  "`bmkp-handle-region-default', then narrow to region in cloned buffer."
  (let ((bmkp-handle-region-function  'bmkp-handle-region-default))
    (bookmark-handle-bookmark bookmark))
  (if (get major-mode 'no-clone-indirect) ; e.g., `Info-mode'
      (message "Cannot indirectly clone a buffer in `%s' mode" major-mode)
    (ni-narrow-to-region-indirect-other-window (region-beginning) (region-end) (point))))

;;;###autoload (autoload 'bmkp-remote-file-jump "bookmark+")
(defun bmkp-remote-file-jump (bookmark-name &optional flip-use-region-p) ; `C-x j n'
  "Jump to a remote file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-remote-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "remote file" alist nil nil 'bmkp-remote-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-remote-file-jump-other-window "bookmark+")
(defun bmkp-remote-file-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j n'
  "`bmkp-remote-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-remote-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "remote file" alist t nil 'bmkp-remote-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-remote-non-dir-file-jump "bookmark+")
(defun bmkp-remote-non-dir-file-jump (bookmark-name &optional flip-use-region-p) ; Not bound.
  "Jump to a remote non-directory file bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-remote-non-dir-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "remote non-dir file" alist nil nil 'bmkp-remote-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-remote-non-dir-file-jump-other-window "bookmark+")
(defun bmkp-remote-non-dir-file-jump-other-window (bookmark-name &optional flip-use-region-p) ; Not bound.
  "`bmkp-remote-non-dir-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-remote-non-dir-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "remote non-dir file" alist t nil 'bmkp-remote-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-specific-buffers-jump "bookmark+")
(defun bmkp-specific-buffers-jump (buffers bookmark-name &optional flip-use-region-p) ; `C-x j = b'
  "Jump to a bookmark for a buffer in list BUFFERS.
Interactively, read buffer names and bookmark name, with completion.

This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((buffs  ())
         buff)
     (while (and (setq buff  (bmkp-completing-read-buffer-name 'ALLOW-EMPTY))  (not (string= "" buff)))
       (add-to-list 'buffs buff))
     (let ((alist  (bmkp-specific-buffers-alist-only buffs)))
       (list buffs (bmkp-read-bookmark-for-type "specific-buffers" alist nil nil 'specific-buffers-history)
             current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-specific-buffers-jump-other-window "bookmark+")
(defun bmkp-specific-buffers-jump-other-window (buffers bookmark-name
                                                &optional flip-use-region-p) ; `C-x 4 j = b'
  "`bmkp-specific-buffers-jump', but in another window."
  (interactive
   (let ((buffs  ())
         buff)
     (while (and (setq buff  (bmkp-completing-read-buffer-name 'ALLOW-EMPTY))  (not (string= "" buff)))
       (add-to-list 'buffs buff))
     (let ((alist  (bmkp-specific-buffers-alist-only buffs)))
       (list buffs (bmkp-read-bookmark-for-type "specific-buffers" alist t nil 'specific-buffers-history)
             current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-specific-files-jump "bookmark+")
(defun bmkp-specific-files-jump (files bookmark-name &optional flip-use-region-p) ; `C-x j = f'
  "Jump to a bookmark for a file in list FILES.
Interactively, read file names and bookmark name, with completion.

This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((use-file-dialog  nil)
         (files            ())
         file)
     (while (and (setq file  (bmkp-completing-read-file-name 'ALLOW-EMPTY))  (not (string= "" file)))
       (add-to-list 'files file))
     (let ((alist  (bmkp-specific-files-alist-only files)))
       (list files (bmkp-read-bookmark-for-type "specific-files" alist nil nil 'specific-files-history)
             current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-specific-files-jump-other-window "bookmark+")
(defun bmkp-specific-files-jump-other-window (files bookmark-name
                                              &optional flip-use-region-p) ; `C-x 4 j = f'
  "`bmkp-specific-files-jump', but in another window."
  (interactive
   (let ((use-file-dialog  nil)
         (files            ())
         file)
     (while (and (setq file  (bmkp-completing-read-file-name 'ALLOW-EMPTY))  (not (string= "" file)))
       (add-to-list 'files file))
     (let ((alist  (bmkp-specific-files-alist-only files)))
       (list files (bmkp-read-bookmark-for-type "specific-files" alist t nil 'specific-files-history)
             current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-temporary-jump "bookmark+")
(defun bmkp-temporary-jump (bookmark-name) ; `C-x j x'
  "Jump to a temporary bookmark.
This is a specialization of `bookmark-jump', but without a prefix arg."
  (interactive (list (bmkp-read-bookmark-for-type "temporary" (bmkp-temporary-alist-only) nil nil
                                                  'bmkp-temporary-history)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer))

;;;###autoload (autoload 'bmkp-temporary-jump-other-window "bookmark+")
(defun bmkp-temporary-jump-other-window (bookmark-name) ; `C-x 4 j x'
  "`bmkp-temporary-jump', but in another window."
  (interactive (list (bmkp-read-bookmark-for-type "temporary" (bmkp-temporary-alist-only) t nil
                                                  'bmkp-temporary-history)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window))

;;;###autoload (autoload 'bmkp-this-buffer-jump "bookmark+")
(defun bmkp-this-buffer-jump (bookmark-name &optional flip-use-region-p) ; `C-x j , ,'
  "Jump to a bookmark for the current buffer.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-this-buffer-alist-only)))
     (unless alist  (error "No bookmarks for this buffer"))
     (list (bookmark-completing-read "Jump to bookmark for this buffer"
                                     (bmkp-default-bookmark-name alist) alist)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-this-buffer-jump-other-window "bookmark+")
(defun bmkp-this-buffer-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j , ,'
  "`bmkp-this-buffer-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-this-buffer-alist-only)))
     (unless alist  (error "No bookmarks for this buffer"))
     (list (bookmark-completing-read "Jump to bookmark for this buffer in another window"
                                     (bmkp-default-bookmark-name alist) alist)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;; ;;;###autoload
;;; (defun bmkp-this-file-jump (bookmark-name &optional flip-use-region-p)
;;;   "Jump to a bookmark for the current file (absolute file name).
;;; This is a specialization of `bookmark-jump' - see that, in particular
;;; for info about using a prefix argument."
;;;   (interactive
;;;    (progn (unless (or (buffer-file-name) (and (eq major-mode 'dired-mode)
;;;                                               (if (consp dired-directory)
;;;                                                   (car dired-directory)
;;;                                                 dired-directory)))
;;;             (error "This buffer is not associated with a file"))
;;;           (let ((alist  (bmkp-this-file-alist-only)))
;;;             (unless alist  (error "No bookmarks for this file"))
;;;             (list (bookmark-completing-read "Jump to bookmark for this file"
;;;                                             (bmkp-default-bookmark-name alist) alist)
;;;                   current-prefix-arg))))
;;;   (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;; ;;;###autoload
;;; (defun bmkp-this-file-jump-other-window (bookmark-name &optional flip-use-region-p)
;;;   "`bmkp-this-file-jump', but in another window."
;;;   (interactive
;;;    (progn (unless (or (buffer-file-name) (and (eq major-mode 'dired-mode)
;;;                                               (if (consp dired-directory)
;;;                                                   (car dired-directory)
;;;                                                 dired-directory)))
;;;             (error "This buffer is not associated with a file"))
;;;           (let ((alist  (bmkp-this-file-alist-only)))
;;;             (unless alist  (error "No bookmarks for this file"))
;;;             (list (bookmark-completing-read "Jump to bookmark for this file in another window"
;;;                                             (bmkp-default-bookmark-name alist) alist)
;;;                   current-prefix-arg))))
;;;   (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-variable-list-jump "bookmark+")
(defun bmkp-variable-list-jump (bookmark-name) ; `C-x j v'
  "Jump to a variable-list bookmark.
This is a specialization of `bookmark-jump'."
  (interactive
   (let ((alist  (bmkp-variable-list-alist-only)))
     (list (bmkp-read-bookmark-for-type "variable-list" alist nil nil 'bmkp-variable-list-history))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer))

;;;###autoload (autoload 'bmkp-url-jump "bookmark+")
(defun bmkp-url-jump (bookmark-name &optional flip-use-region-p) ; `C-x j u'
  "Jump to a URL bookmark.
It can be an EWW bookmark, a W3M bookmark, or a browse-URL bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-url-alist-only)))
     (list (bmkp-read-bookmark-for-type "URL" alist nil nil 'bmkp-url-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-url-jump-other-window "bookmark+")
(defun bmkp-url-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j u'
  "`bmkp-url-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-url-alist-only)))
     (list (bmkp-read-bookmark-for-type "URL" alist t nil 'bmkp-url-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-w32-browser-jump "bookmark+")
(defun bmkp-w32-browser-jump (bookmark-name) ; Not bound by default.
  "Jump to a bookmark whose handler applies `w32-browser' to its file.
This is a specialization of `bookmark-jump'."
  (interactive
   (list (bmkp-read-bookmark-for-type "w32-browser" bookmark-alist nil
                                      ;; Use a predicate, since `w32-browser' is a handler, not a type name.
                                      (bmkp-handler-pred 'w32-browser)
                                      'bmkp-w32-browser-history)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer))

;;;###autoload (autoload 'bmkp-w3m-jump "bookmark+")
(defun bmkp-w3m-jump (bookmark-name &optional flip-use-region-p) ; `C-x j w', (`j' in W3M)
  "Jump to a W3M bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-w3m-alist-only)))
     (list (bmkp-read-bookmark-for-type "W3M" alist nil nil 'bmkp-w3m-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-w3m-jump-other-window "bookmark+")
(defun bmkp-w3m-jump-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j w'
  "`bmkp-w3m-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-w3m-alist-only)))
     (list (bmkp-read-bookmark-for-type "W3M" alist t nil 'bmkp-w3m-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-all-tags-jump "bookmark+")
(defun bmkp-all-tags-jump (tags bookmark) ; `C-x j t *'
  "Jump to a BOOKMARK that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-all-tags-alist-only tgs)))
     (unless alist (error "No bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-all-tags-jump-other-window "bookmark+")
(defun bmkp-all-tags-jump-other-window (tags bookmark) ; `C-x 4 j t *'
  "`bmkp-all-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-all-tags-alist-only tgs)))
     (unless alist (error "No bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-all-tags-regexp-jump "bookmark+")
(defun bmkp-all-tags-regexp-jump (regexp bookmark) ; `C-x j t % *'
  "Jump to a BOOKMARK that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for all tags: "))
          (alist  (bmkp-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-all-tags-regexp-jump-other-window "bookmark+")
(defun bmkp-all-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t % *'
  "`bmkp-all-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for all tags: "))
          (alist  (bmkp-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-some-tags-jump "bookmark+")
(defun bmkp-some-tags-jump (tags bookmark) ; `C-x j t +'
  "Jump to a BOOKMARK that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-some-tags-jump-other-window "bookmark+")
(defun bmkp-some-tags-jump-other-window (tags bookmark) ; `C-x 4 j t +'
  "`bmkp-some-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-some-tags-regexp-jump "bookmark+")
(defun bmkp-some-tags-regexp-jump (regexp bookmark) ; `C-x j t % +'
  "Jump to a BOOKMARK that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-some-tags-regexp-jump-other-window "bookmark+")
(defun bmkp-some-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t % +'
  "`bmkp-some-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-file-all-tags-jump "bookmark+")
(defun bmkp-file-all-tags-jump (tags bookmark) ; `C-x j t f *'
  "Jump to a file or directory BOOKMARK that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-file-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-file-all-tags-jump-other-window "bookmark+")
(defun bmkp-file-all-tags-jump-other-window (tags bookmark) ; `C-x 4 j t f *'
  "`bmkp-file-all-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-file-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-file-all-tags-regexp-jump "bookmark+")
(defun bmkp-file-all-tags-regexp-jump (regexp bookmark) ; `C-x j t f % *'
  "Jump to a file or directory BOOKMARK that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-file-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-file-all-tags-regexp-jump-other-window "bookmark+")
(defun bmkp-file-all-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t f % *'
  "`bmkp-file-all-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-file-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-file-some-tags-jump "bookmark+")
(defun bmkp-file-some-tags-jump (tags bookmark) ; `C-x j t f +'
  "Jump to a file or directory BOOKMARK that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-file-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-file-some-tags-jump-other-window "bookmark+")
(defun bmkp-file-some-tags-jump-other-window (tags bookmark) ; `C-x 4 j t f +'
  "`bmkp-file-some-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-file-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-file-some-tags-regexp-jump "bookmark+")
(defun bmkp-file-some-tags-regexp-jump (regexp bookmark) ; `C-x j t f % +'
  "Jump to a file or directory BOOKMARK that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-file-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-file-some-tags-regexp-jump-other-window "bookmark+")
(defun bmkp-file-some-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t f % +'
  "`bmkp-file-some-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-file-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-file-this-dir-all-tags-jump "bookmark+")
(defun bmkp-file-this-dir-all-tags-jump (tags bookmark) ; `C-x j t . *'
  "Jump to a file BOOKMARK in this dir that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-file-this-dir-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-file-this-dir-all-tags-jump-other-window "bookmark+")
(defun bmkp-file-this-dir-all-tags-jump-other-window (tags bookmark) ; `C-x 4 j t . *'
  "`bmkp-file-this-dir-all-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-file-this-dir-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-file-this-dir-all-tags-regexp-jump "bookmark+")
(defun bmkp-file-this-dir-all-tags-regexp-jump (regexp bookmark) ; `C-x j t . % *'
  "Jump to a file BOOKMARK in this dir that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-file-this-dir-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-file-this-dir-all-tags-regexp-jump-other-window "bookmark+")
(defun bmkp-file-this-dir-all-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t . % *'
  "`bmkp-file-this-dir-all-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-file-this-dir-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-file-this-dir-some-tags-jump "bookmark+")
(defun bmkp-file-this-dir-some-tags-jump (tags bookmark) ; `C-x j t . +'
  "Jump to a file BOOKMARK in this dir that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-file-this-dir-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-file-this-dir-some-tags-jump-other-window "bookmark+")
(defun bmkp-file-this-dir-some-tags-jump-other-window (tags bookmark) ; `C-x 4 j t . +'
  "`bmkp-file-this-dir-some-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-file-this-dir-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-file-this-dir-some-tags-regexp-jump "bookmark+")
(defun bmkp-file-this-dir-some-tags-regexp-jump (regexp bookmark) ; `C-x j t . % +'
  "Jump to a file BOOKMARK in this dir that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-file-this-dir-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-file-this-dir-some-tags-regexp-jump-other-window "bookmark+")
(defun bmkp-file-this-dir-some-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t . % +'
  "`bmkp-file-this-dir-some-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-file-this-dir-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-autofile-jump "bookmark+")
(defun bmkp-autofile-jump (bookmark-name)    ; `C-x j a'
  "Jump to an autofile bookmark.
This is a specialization of `bookmark-jump'."
  (interactive
   (let ((alist  (bmkp-autofile-alist-only)))
     (list (bmkp-read-bookmark-for-type "autofile" alist nil nil 'bmkp-autofile-history))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer))

;;;###autoload (autoload 'bmkp-autofile-jump-other-window "bookmark+")
(defun bmkp-autofile-jump-other-window (bookmark-name) ; `C-x 4 j a'
  "`bmkp-autofile-jump' but in another window."
  (interactive
   (let ((alist  (bmkp-autofile-alist-only)))
     (list (bmkp-read-bookmark-for-type "autofile" alist t nil 'bmkp-autofile-history))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer))

;;;###autoload (autoload 'bmkp-autofile-all-tags-jump "bookmark+")
(defun bmkp-autofile-all-tags-jump (tags bookmark) ; `C-x j t a *'
  "Jump to an autofile BOOKMARK in this dir that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-autofile-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-autofile-all-tags-jump-other-window "bookmark+")
(defun bmkp-autofile-all-tags-jump-other-window (tags bookmark) ; `C-x 4 j t a *'
  "`bmkp-autofile-all-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-autofile-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-autofile-all-tags-regexp-jump "bookmark+")
(defun bmkp-autofile-all-tags-regexp-jump (regexp bookmark) ; `C-x j t a % *'
  "Jump to an autofile BOOKMARK in this dir that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-autofile-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-autofile-all-tags-regexp-jump-other-window "bookmark+")
(defun bmkp-autofile-all-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t a % *'
  "`bmkp-autofile-all-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-autofile-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-autofile-some-tags-jump "bookmark+")
(defun bmkp-autofile-some-tags-jump (tags bookmark) ; `C-x j t a +'
  "Jump to an autofile BOOKMARK in this dir that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-autofile-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-autofile-some-tags-jump-other-window "bookmark+")
(defun bmkp-autofile-some-tags-jump-other-window (tags bookmark) ; `C-x 4 j t a +'
  "`bmkp-autofile-some-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing nil nil current-prefix-arg))
          (alist  (bmkp-autofile-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload (autoload 'bmkp-autofile-some-tags-regexp-jump "bookmark+")
(defun bmkp-autofile-some-tags-regexp-jump (regexp bookmark) ; `C-x j t a % +'
  "Jump to an autofile BOOKMARK in this dir that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-autofile-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload (autoload 'bmkp-autofile-some-tags-regexp-jump-other-window "bookmark+")
(defun bmkp-autofile-some-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t a % +'
  "`bmkp-autofile-some-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (bmkp-read-regexp "Regexp for tags: "))
          (alist  (bmkp-autofile-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

(defun bmkp-find-file (&optional file create-autofile-p must-exist-p msg-p) ; `C-x j C-f'
  "Visit a file or directory, respecting any associated autofile handlers.
You are prompted for the file or directory name, FILE.

If FILE matches an entry in `bmkp-default-handlers-for-file-types'
then use the associated default handler to access the file.
Otherwise, just use `find-file'.

With a prefix arg, create an autofile bookmark if FILE does not
already have one.

Non-interactively:
* Non-nil MUST-EXIST-P means raise an error if FILE has no autofile
  bookmark.
* Non-nil MSG-P means display a status message."
  (interactive "i\nP\ni\np")
  (let* ((use-file-dialog                             nil)
         (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
         (fil                                         (or file  (read-file-name "Find file: " nil nil t)))
         (dir-to-use                                  (if (file-name-absolute-p fil)
                                                          (file-name-directory fil)
                                                        default-directory))
         (bmk                                         (bmkp-get-autofile-bookmark fil)))
    (if bmk
        (bookmark-jump bmk)
      (when must-exist-p (error "File `%s' is not an autofile (no bookmark)" fil))
      (when create-autofile-p           ; Create a new bookmark.
        (bmkp-file-target-set (expand-file-name fil dir-to-use) t nil 'NO-OVERWRITE msg-p)
        (when msg-p (message "Autofile bookmark set for `%s'" fil)))
      (let ((default-handler  (condition-case nil (bmkp-default-handler-for-file fil) (error nil))))
        (if default-handler (funcall default-handler fil) (find-file fil 'WILDCARDS))))))

(defun bmkp-find-file-other-window (&optional file create-autofile-p must-exist-p msg-p) ; `C-x 4 j C-f'
  "`bmkp-find-file', but in another window."
  (interactive "i\nP\ni\np")
  (let* ((use-file-dialog                             nil)
         (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
         (fil                                         (or file  (read-file-name "Find file: " nil nil t)))
         (dir-to-use                                  (if (file-name-absolute-p fil)
                                                          (file-name-directory fil)
                                                        default-directory))
         (bmk                                         (bmkp-get-autofile-bookmark fil dir-to-use)))
    (if bmk
        (bookmark-jump-other-window bmk)
      (when must-exist-p (error "File `%s' is not an autofile (no bookmark)" fil))
      (when create-autofile-p           ; Create a new bookmark.
        (bmkp-file-target-set (expand-file-name fil dir-to-use) t nil 'NO-OVERWRITE msg-p)
        (when msg-p (message "Autofile bookmark created for `%s'" fil)))
      (let ((default-handler  (condition-case nil (bmkp-default-handler-for-file fil) (error nil))))
        (if default-handler (funcall default-handler fil) (find-file-other-window fil 'WILDCARDS))))))


;;; We could allow these even for Emacs 20 for Icicles users,
;;; but the predicate would have no effect when not in Icicle mode.  So don't bother with Emacs 20.

(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-all-tags (tags &optional file) ; `C-x j t C-f *'
    "Visit a file or directory that has all of the TAGS.
You are prompted first for the tags.  Hit `RET' to enter each tag,
then hit `RET' again after the last tag.  You can use completion to
enter each tag.  This completion is lax: you are not limited to
existing tags.

You are then prompted for the file name.  This is read using
`read-file-name', so you can browse up and down the file hierarchy.
The completion candidates are file names, not bookmark names.
However, only files that are bookmarked as autofiles are candidates.

If you specify no tags, then every file that has some tags is a
candidate.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
    (interactive (list (bmkp-read-tags-completing nil nil current-prefix-arg)))
    (lexical-let* ((tgs              tags)
                   (use-file-dialog  nil)
                   (pred
                    (lambda (ff)
                      (lexical-let* ((bmk   (bmkp-get-autofile-bookmark ff))
                                     (btgs  (and bmk  (bmkp-get-tags bmk))))
                        (and btgs  (bmkp-every (lambda (tag) (bmkp-has-tag-p bmk tag))  tgs)))))
                   (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
                   (icicle-must-pass-after-match-predicate      pred)
                   (fil                                         (or (and file  (funcall pred file)  file)
                                                                    (read-file-name
                                                                     "Find file: " nil nil t nil
                                                                     (and (or (not (boundp 'icicle-mode))
                                                                              (not icicle-mode))
                                                                          pred))))
                   (bmk                                         (bmkp-get-autofile-bookmark fil)))
      (when bmk  (bookmark-jump bmk)))))

(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-all-tags-other-window (tags &optional file) ; `C-x 4 j t C-f *'
    "`bmkp-find-file-all-tags', but in another window."
    (interactive (list (bmkp-read-tags-completing nil nil current-prefix-arg)))
    (lexical-let* ((tgs              tags)
                   (use-file-dialog  nil)
                   (pred
                    (lambda (ff)
                      (lexical-let* ((bk    (bmkp-get-autofile-bookmark ff))
                                     (btgs  (and bk  (bmkp-get-tags bk))))
                        (and btgs  (bmkp-every (lambda (tag) (bmkp-has-tag-p bk tag))  tgs)))))
                   (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
                   (icicle-must-pass-after-match-predicate      pred)
                   (fil                                         (or (and file  (funcall pred file)  file)
                                                                    (read-file-name
                                                                     "Find file: " nil nil t nil
                                                                     (and (or (not (boundp 'icicle-mode))
                                                                              (not icicle-mode))
                                                                          pred))))
                   (bmk                                         (bmkp-get-autofile-bookmark fil)))
      (bookmark-jump-other-window bmk))))

(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-all-tags-regexp (regexp &optional file) ; `C-x j t C-f % *'
    "Visit a file or directory that has each tag matching REGEXP.
You are prompted for the REGEXP."
    (interactive (list (bmkp-read-regexp "Regexp for tags: ")))
    (lexical-let* ((rg               regexp)
                   (use-file-dialog  nil)
                   (pred
                    (lambda (ff)
                      (let* ((bk    (bmkp-get-autofile-bookmark ff))
                             (btgs  (and bk  (bmkp-get-tags bk))))
                        (and btgs  (bmkp-every (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag)))
                                               btgs)))))
                   (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
                   (icicle-must-pass-after-match-predicate      pred)
                   (fil                                         (or (and file  (funcall pred file)  file)
                                                                    (read-file-name
                                                                     "Find file: " nil nil t nil
                                                                     (and (or (not (boundp 'icicle-mode))
                                                                              (not icicle-mode))
                                                                          pred))))
                   (bmk                                         (bmkp-get-autofile-bookmark fil)))
      (bookmark-jump bmk))))

;;;###autoload (autoload 'bmkp-find-file-all-tags-regexp-other-window "bookmark+")
(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-all-tags-regexp-other-window (regexp &optional file) ; `C-x 4 j t C-f % *'
    "`bmkp-find-file-all-tags-regexp', but in another window."
    (interactive (list (bmkp-read-regexp "Regexp for tags: ")))
    (lexical-let* ((rg               regexp)
                   (use-file-dialog  nil)
                   (pred
                    (lambda (ff)
                      (let* ((bk    (bmkp-get-autofile-bookmark ff))
                             (btgs  (and bk  (bmkp-get-tags bk))))
                        (and btgs  (bmkp-every (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag)))
                                               btgs)))))
                   (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
                   (icicle-must-pass-after-match-predicate      pred)
                   (fil                                         (or (and file  (funcall pred file)  file)
                                                                    (read-file-name
                                                                     "Find file: " nil nil t nil
                                                                     (and (or (not (boundp 'icicle-mode))
                                                                              (not icicle-mode))
                                                                          pred))))
                   (bmk                                         (bmkp-get-autofile-bookmark fil)))
      (bookmark-jump-other-window bmk))))

;;;###autoload (autoload 'bmkp-find-file-some-tags "bookmark+")
(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-some-tags (tags &optional file) ; `C-x j t C-f +'
    "Visit a file or directory that has at least one of the TAGS.
You are prompted first for the tags.  Hit `RET' to enter each tag,
then hit `RET' again after the last tag.  You can use completion to
enter each tag.  This completion is lax: you are not limited to
existing tags.

You are then prompted for the file name.  This is read using
`read-file-name', so you can browse up and down the file hierarchy.
The completion candidates are file names, not bookmark names.
However, only files that are bookmarked as autofiles are candidates.

By default, the tag choices for completion are NOT refreshed, to save
time.  Use a prefix argument if you want to refresh them."
    (interactive (list (bmkp-read-tags-completing nil nil current-prefix-arg)))
    (lexical-let* ((tgs              tags)
                   (use-file-dialog  nil)
                   (pred
                    (lambda (ff)
                      (lexical-let* ((bk    (bmkp-get-autofile-bookmark ff))
                                     (btgs  (and bk  (bmkp-get-tags bk))))
                        (and btgs  (bmkp-some (lambda (tag) (bmkp-has-tag-p bk tag))  tgs)))))
                   (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
                   (icicle-must-pass-after-match-predicate      pred)
                   (fil                                         (or (and file  (funcall pred file)  file)
                                                                    (read-file-name
                                                                     "Find file: " nil nil t nil
                                                                     (and (or (not (boundp 'icicle-mode))
                                                                              (not icicle-mode))
                                                                          pred))))
                   (bmk                                         (bmkp-get-autofile-bookmark fil)))
      (bookmark-jump bmk))))

;;;###autoload (autoload 'bmkp-find-file-some-tags-other-window "bookmark+")
(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-some-tags-other-window (tags &optional file) ; `C-x 4 j t C-f +'
    "`bmkp-find-file-some-tags', but in another window."
    (interactive (list (bmkp-read-tags-completing nil nil current-prefix-arg)))
    (lexical-let* ((tgs              tags)
                   (use-file-dialog  nil)
                   (pred
                    (lambda (ff)
                      (lexical-let* ((bk    (bmkp-get-autofile-bookmark ff))
                                     (btgs  (and bk  (bmkp-get-tags bk))))
                        (and btgs  (bmkp-some (lambda (tag) (bmkp-has-tag-p bk tag))  tgs)))))
                   (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
                   (icicle-must-pass-after-match-predicate      pred)
                   (fil                                         (or (and file  (funcall pred file)  file)
                                                                    (read-file-name
                                                                     "Find file: " nil nil t nil
                                                                     (and (or (not (boundp 'icicle-mode))
                                                                              (not icicle-mode))
                                                                          pred))))
                   (bmk                                         (bmkp-get-autofile-bookmark fil)))
      (bookmark-jump-other-window bmk))))

;;;###autoload (autoload 'bmkp-find-file-some-tags-regexp "bookmark+")
(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-some-tags-regexp (regexp &optional file) ; `C-x j t C-f % +'
    "Visit a file or directory that has a tag matching REGEXP.
You are prompted for the REGEXP."
    (interactive (list (bmkp-read-regexp "Regexp for tags: ")))
    (lexical-let* ((rg               regexp)
                   (use-file-dialog  nil)
                   (pred
                    (lambda (ff)
                      (let* ((bk    (bmkp-get-autofile-bookmark ff))
                             (btgs  (and bk  (bmkp-get-tags bk))))
                        (and btgs  (bmkp-some (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag)))
                                              btgs)))))
                   (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
                   (icicle-must-pass-after-match-predicate      pred)
                   (fil                                         (or (and file  (funcall pred file)  file)
                                                                    (read-file-name
                                                                     "Find file: " nil nil t nil
                                                                     (and (or (not (boundp 'icicle-mode))
                                                                              (not icicle-mode))
                                                                          pred))))
                   (bmk                                         (bmkp-get-autofile-bookmark fil)))
      (bookmark-jump bmk))))

;;;###autoload (autoload 'bmkp-find-file-some-tags-regexp-other-window "bookmark+")
(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-some-tags-regexp-other-window (regexp &optional file) ; `C-x 4 j t C-f % +'
    "`bmkp-find-file-some-tags-regexp', but in another window."
    (interactive (list (bmkp-read-regexp "Regexp for tags: ")))
    (lexical-let* ((rg               regexp)
                   (use-file-dialog  nil)
                   (pred
                    (lambda (ff)
                      (let* ((bk    (bmkp-get-autofile-bookmark ff))
                             (btgs  (and bk  (bmkp-get-tags bk))))
                        (and btgs  (bmkp-some (lambda (tag) (bmkp-string-match-p rg (bmkp-tag-name tag)))
                                              btgs)))))
                   (icicle-unpropertize-completion-result-flag  t) ; For `read-file-name'.
                   (icicle-must-pass-after-match-predicate      pred)
                   (fil                                         (or (and file  (funcall pred file)  file)
                                                                    (read-file-name
                                                                     "Find file: " nil nil t nil
                                                                     (and (or (not (boundp 'icicle-mode))
                                                                              (not icicle-mode))
                                                                          pred))))
                   (bmk                                         (bmkp-get-autofile-bookmark fil)))
      (bookmark-jump-other-window bmk))))

;;;###autoload (autoload 'bmkp-jump-in-navlist "bookmark+")
(defun bmkp-jump-in-navlist (bookmark-name &optional flip-use-region-p) ; `C-x j N'
  "Jump to a bookmark, choosing from those in the navigation list."
  (interactive
   (progn (unless bmkp-nav-alist
            (bookmark-maybe-load-default-file)
            (setq bmkp-nav-alist  bookmark-alist)
            (unless bmkp-nav-alist (error "No bookmarks"))
            (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist))
            (message "Bookmark navigation list is now the global bookmark list") (sit-for 2))
          (let ((bookmark-alist  bmkp-nav-alist))
            (list (bookmark-completing-read "Jump to bookmark (in another window)"
                                            (bmkp-default-bookmark-name))
                  current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer flip-use-region-p))

;;;###autoload (autoload 'bmkp-jump-in-navlist-other-window "bookmark+")
(defun bmkp-jump-in-navlist-other-window (bookmark-name &optional flip-use-region-p) ; `C-x 4 j N'
  "Same as `bmkp-jump-in-navlist', but use another window."
  (interactive
   (progn (unless bmkp-nav-alist
            (bookmark-maybe-load-default-file)
            (setq bmkp-nav-alist  bookmark-alist)
            (unless bmkp-nav-alist (error "No bookmarks"))
            (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist))
            (message "Bookmark navigation list is now the global bookmark list") (sit-for 2))
          (let ((bookmark-alist  bmkp-nav-alist))
            (list (bookmark-completing-read "Jump to bookmark (in another window)"
                                            (bmkp-default-bookmark-name))
                  current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window flip-use-region-p))

;;;###autoload (autoload 'bmkp-cycle "bookmark+")
(defun bmkp-cycle (increment &optional other-window startoverp)
  "Cycle through bookmarks in the navlist by INCREMENT (default: 1).
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value

Plain `C-u' also means start over at first bookmark.

You can set the navigation list using commands
 `bmkp-choose-navlist-from-bookmark-list' and
 `bmkp-choose-navlist-of-type'.

You can cycle among bookmarks in the current buffer using
 `bmkp-cycle-this-buffer' and
 `bmkp-cycle-this-buffer-other-window.'

In Lisp code:
 Non-nil OTHER-WINDOW means jump to the bookmark in another window.
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) nil startovr)))
  (unless bmkp-nav-alist
    (bookmark-maybe-load-default-file)
    (when (and bookmark-alist  (y-or-n-p "No navigation list.  Use whole bookmark list? "))
      (setq bmkp-nav-alist  bookmark-alist)
      (message "Navigation list is now the global bookmark list") (sit-for 2))
    (unless bmkp-nav-alist (error "No bookmarks in navigation list"))
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist)))
  (unless (and bmkp-current-nav-bookmark  (not startoverp)
               (bookmark-get-bookmark bmkp-current-nav-bookmark 'NOERROR))
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist)))
  (if (bmkp-cycle-1 increment other-window startoverp)
      (unless (or (bmkp-sequence-bookmark-p bmkp-current-nav-bookmark)
                  (bmkp-function-bookmark-p bmkp-current-nav-bookmark))
        (message "Position: %9d, Bookmark: `%s'"
                 (point) (bmkp-bookmark-name-from-record bmkp-current-nav-bookmark)))
    (message "Invalid bookmark: `%s'" (bmkp-bookmark-name-from-record bmkp-current-nav-bookmark))))

;;;###autoload (autoload 'bmkp-cycle-other-window "bookmark+")
(defun bmkp-cycle-other-window (increment &optional startoverp)
  "Same as `bmkp-cycle' but uses another window."
  (interactive "p")
  (bmkp-cycle increment 'OTHER-WINDOW startoverp))

;;;###autoload (autoload 'bmkp-cycle-this-file/buffer "bookmark+")
(defun bmkp-cycle-this-file/buffer (increment &optional other-window startoverp)
  "Cycle through bookmarks for this file/buffer by INCREMENT (default: 1).
If visiting a file, this is `bmkp-cycle-this-file'.
Otherwise, this is `bmkp-cycle-this-buffer'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) nil startovr)))
  (if (buffer-file-name)
      (bmkp-cycle-this-file increment other-window startoverp)
    (bmkp-cycle-this-buffer increment other-window startoverp)))

;;;###autoload (autoload 'bmkp-cycle-this-file/buffer-other-window "bookmark+")
(defun bmkp-cycle-this-file/buffer-other-window (increment &optional startoverp)
  "Same as `bmkp-cycle-this-file/buffer' but use other window."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-file/buffer increment 'OTHER-WINDOW startoverp))

;;;###autoload (autoload 'bmkp-cycle-this-file "bookmark+")
(defun bmkp-cycle-this-file (increment &optional other-window startoverp)
  "Cycle through bookmarks for this file by INCREMENT (default: 1).
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value

Plain `C-u' also means start over at first bookmark.

You can cycle among bookmarks beyond the current file using
`bmkp-cycle' and `bmkp-cycle-other-window.'

You can set your preferred sort order for this-file bookmarks by
customizing option `bmkp-this-file/buffer-cycle-sort-comparer'.

To change the sort order without customizing, you can use \
`\\[bmkp-this-file-bmenu-list]' to
show the `*Bookmark List*' with only this file's bookmarks, sort
them there, and use `\\[bmkp-choose-navlist-from-bookmark-list]', choosing \
`CURRENT *Bookmark List*' as
the navigation list.

Then you can cycle the bookmarks using `bmkp-cycle'
\(`\\[bmkp-next-bookmark-repeat]' etc.), instead of `bmkp-cycle-this-file'.

In Lisp code:
 Non-nil OTHER-WINDOW means jump to the bookmark in another window.
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) nil startovr)))
  (bookmark-maybe-load-default-file)
  (let ((bmkp-sort-comparer  bmkp-this-file/buffer-cycle-sort-comparer))
    (setq bmkp-nav-alist  (bmkp-sort-omit (bmkp-this-file-alist-only))))
  (unless bmkp-nav-alist (error "No bookmarks for this file"))
  (unless (and bmkp-current-nav-bookmark  (not startoverp)
               (bookmark-get-bookmark bmkp-current-nav-bookmark 'NOERROR)
               (bmkp-this-file-p bmkp-current-nav-bookmark)) ; Exclude desktops etc.
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist)))
  (if (bmkp-cycle-1 increment other-window startoverp)
      (unless (or (bmkp-sequence-bookmark-p bmkp-current-nav-bookmark)
                  (bmkp-function-bookmark-p bmkp-current-nav-bookmark))
        (message "Position: %9d, Bookmark: `%s'"
                 (point) (bmkp-bookmark-name-from-record bmkp-current-nav-bookmark)))
    (message "Invalid bookmark: `%s'" (bmkp-bookmark-name-from-record bmkp-current-nav-bookmark))))

;;;###autoload (autoload 'bmkp-cycle-this-file-other-window "bookmark+")
(defun bmkp-cycle-this-file-other-window (increment &optional startoverp)
  "Same as `bmkp-cycle-this-file' but use other window."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-file increment 'OTHER-WINDOW startoverp))

;;;###autoload (autoload 'bmkp-cycle-this-buffer "bookmark+")
(defun bmkp-cycle-this-buffer (increment &optional other-window startoverp)
  "Cycle through bookmarks in this buffer by INCREMENT (default: 1).
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value

Plain `C-u' also means start over at first bookmark.

You can cycle among bookmarks beyond the current buffer using
`bmkp-cycle' and `bmkp-cycle-other-window.'

You can set your preferred sort order for this-buffer bookmarks by
customizing option `bmkp-this-file/buffer-cycle-sort-comparer'.

To change the sort order without customizing, you can use \
`\\[bmkp-this-buffer-bmenu-list]' to
show the `*Bookmark List*' with only this buffer's bookmarks, sort
them there, and use `\\[bmkp-choose-navlist-from-bookmark-list]', choosing \
`CURRENT *Bookmark List*' as
the navigation list.

Then you can cycle the bookmarks using `bmkp-cycle'
\(`\\[bmkp-next-bookmark-repeat]' etc.), instead of `bmkp-cycle-this-buffer'.

In Lisp code:
 Non-nil OTHER-WINDOW means jump to the bookmark in another window.
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) nil startovr)))
  (bookmark-maybe-load-default-file)
  (let ((bmkp-sort-comparer  bmkp-this-file/buffer-cycle-sort-comparer))
    (setq bmkp-nav-alist  (bmkp-sort-omit (bmkp-this-buffer-alist-only))))
  (unless bmkp-nav-alist (error "No bookmarks in this buffer"))
  (unless (and bmkp-current-nav-bookmark  (not startoverp)
               (bookmark-get-bookmark bmkp-current-nav-bookmark 'NOERROR)
               (bmkp-this-buffer-p bmkp-current-nav-bookmark)) ; Exclude desktops etc.
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist)))
  (if (bmkp-cycle-1 increment other-window startoverp)
      (unless (or (bmkp-sequence-bookmark-p bmkp-current-nav-bookmark)
                  (bmkp-function-bookmark-p bmkp-current-nav-bookmark))
        (message "Position: %9d, Bookmark: `%s'"
                 (point) (bmkp-bookmark-name-from-record bmkp-current-nav-bookmark)))
    (message "Invalid bookmark: `%s'" (bmkp-bookmark-name-from-record bmkp-current-nav-bookmark))))

;;;###autoload (autoload 'bmkp-cycle-this-buffer-other-window "bookmark+")
(defun bmkp-cycle-this-buffer-other-window (increment &optional startoverp)
  "Same as `bmkp-cycle-this-buffer' but use other window."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-buffer increment 'OTHER-WINDOW startoverp))

(defun bmkp-cycle-1 (increment &optional other-window startoverp)
  "Helper for `bmkp-cycle*' commands.
Do nothing if `bmkp-current-nav-bookmark' is an invalid bookmark.
Return `bmkp-current-nav-bookmark', or nil if invalid.

NOTE: If `pop-up-frames' is non-nil, then cycling inhibits automatic
showing of annotations (`bookmark-automatically-show-annotations').
This is to prevent change of frame focus, so cycling can continue
properly.

See `bmkp-cycle' for descriptions of the arguments."
  (let ((bookmark-alist   bmkp-nav-alist)
        (bookmark         (bookmark-get-bookmark bmkp-current-nav-bookmark 'NOERROR))
        (bmkp-use-region  (eq 'cycling-too bmkp-use-region)))
    (unless bookmark-alist (error "No bookmarks for cycling"))
    (when bookmark                      ; Skip bookmarks with bad names.
      (setq bmkp-current-nav-bookmark
            (if startoverp
                (car bookmark-alist)
              (let ((index  (bmkp-list-position bookmark bookmark-alist #'eq)))
                (if index
                    (nth (mod (+ increment index) (length bookmark-alist)) bookmark-alist)
                  (message "bmkp-cycle-1: Bookmark `%s' is not in navlist"
                           (bmkp-bookmark-name-from-record bmkp-current-nav-bookmark))
                  (car bookmark-alist)))))
      (let ((bookmark-automatically-show-annotations ; Prevent possible frame focus change.
             (and bookmark-automatically-show-annotations  (not pop-up-frames))))
        (if other-window
            (bookmark-jump-other-window (bmkp-bookmark-name-from-record bmkp-current-nav-bookmark))
          (save-selected-window (bmkp-bookmark-name-from-record (bookmark-jump bmkp-current-nav-bookmark))))))
    (and bookmark  bmkp-current-nav-bookmark))) ; Return nil if not a valid bookmark.

;; Same as `icicle-list-position' in `icicles-fn.el'.
;; Simple version of `cl-position' for all Emacs versions.
(defun bmkp-list-position (item items &optional test)
  "Find the first occurrence of ITEM in list ITEMS.
Return the index of the matching item, or nil if not found.
Items are compared using binary predicate TEST, or `equal' if TEST is
nil."
  (unless test (setq test  'equal))
  (let ((pos  0))
    (catch 'bmkp-list-position
      (dolist (itm  items)
        (when (funcall test item itm) (throw 'bmkp-list-position pos))
        (setq pos  (1+ pos)))
      nil)))

;;;###autoload (autoload 'bmkp-next-bookmark "bookmark+")
(defun bmkp-next-bookmark (n &optional startoverp) ; You can bind this to a repeatable key
  "Jump to the Nth next bookmark in the bookmark navigation list.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at first bookmark.
See also `bmkp-cycle'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle n nil startoverp))

;;;###autoload (autoload 'bmkp-previous-bookmark "bookmark+")
(defun bmkp-previous-bookmark (n &optional startoverp) ; You can bind this to a repeatable key
  "Jump to the Nth previous bookmark in the bookmark navigation list.
See `bmkp-next-bookmark'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle (- n) nil startoverp))

;;;###autoload (autoload 'bmkp-next-bookmark-other-window "bookmark+")
(defun bmkp-next-bookmark-other-window (n &optional startoverp) ; You can bind this to a repeatable key
  "Jump to Nth next bookmark in bookmark navlist in another window.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at first bookmark.
See also `bmkp-cycle'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle n 'OTHER-WINDOW startoverp))

;;;###autoload (autoload 'bmkp-previous-bookmark-other-window "bookmark+")
(defun bmkp-previous-bookmark-other-window (n &optional startoverp) ; You can bind this to a repeatable key
  "Jump to Nth previous bookmark in bookmark navlist in another window.
See `bmkp-next-bookmark'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle (- n) 'OTHER-WINDOW startoverp))

;;;###autoload (autoload 'bmkp-next-bookmark-repeat "bookmark+")
(defun bmkp-next-bookmark-repeat (arg)  ; `C-x p right', `C-x p f', `C-x p C-f'
  "Jump to the Nth-next bookmark in the bookmark navigation list.
This is a repeatable version of `bmkp-next-bookmark'.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at the first bookmark (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-next-bookmark))

;;;###autoload (autoload 'bmkp-previous-bookmark-repeat "bookmark+")
(defun bmkp-previous-bookmark-repeat (arg) ; `C-x p left', `C-x p b', `C-x p C-b'
  "Jump to the Nth-previous bookmark in the bookmark navigation list.
See `bmkp-next-bookmark-repeat'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-previous-bookmark))

;;;###autoload (autoload 'bmkp-next-bookmark-other-window-repeat "bookmark+")
(defun bmkp-next-bookmark-other-window-repeat (arg)  ; `C-x p right', `C-x p f', `C-x p C-f'
  "Jump to Nth-next bookmark in bookmark navlist in another window.
This is a repeatable version of `bmkp-next-bookmark'.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at the first bookmark (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-next-bookmark-other-window))

;;;###autoload (autoload 'bmkp-previous-bookmark-other-window-repeat "bookmark+")
(defun bmkp-previous-bookmark-other-window-repeat (arg) ; `C-x p left', `C-x p b', `C-x p C-b'
  "Jump to Nth-previous bookmark in bookmark navlist in another window.
See `bmkp-next-bookmark-repeat'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-previous-bookmark-other-window))

;;;###autoload (autoload 'bmkp-next-bookmark-this-file/buffer "bookmark+")
(defun bmkp-next-bookmark-this-file/buffer (n &optional startoverp) ; Bind to repeatable key, e.g. `S-f2'
  "Jump to the Nth-next bookmark for the current file/buffer.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle-this-file/buffer'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-file/buffer n nil startoverp))

;;;###autoload (autoload 'bmkp-previous-bookmark-this-file/buffer "bookmark+")
(defun bmkp-previous-bookmark-this-file/buffer (n &optional startoverp) ; Bind to repeatable key, e.g. `f2'
  "Jump to the Nth-previous bookmark for the current file/buffer.
See `bmkp-next-bookmark-this-file/buffer'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-file/buffer (- n) nil startoverp))

;;;###autoload (autoload 'bmkp-next-bookmark-this-file/buffer-repeat "bookmark+")
(defun bmkp-next-bookmark-this-file/buffer-repeat (arg)
                                        ; `C-x p down', `C-x p n', `C-x p C-n', `C-x p mouse-wheel-up'
  "Jump to the Nth next bookmark for the current file/buffer.
This is a repeatable version of `bmkp-next-bookmark-this-file/buffer'.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-next-bookmark-this-file/buffer))

;;;###autoload (autoload 'bmkp-previous-bookmark-this-file/buffer-repeat "bookmark+")
(defun bmkp-previous-bookmark-this-file/buffer-repeat (arg)
                                        ; `C-x p up', `C-x p p', `C-x p C-p', `C-x p mouse-wheel-down'
  "Jump to the Nth previous bookmark for the current file/buffer.
See `bmkp-next-bookmark-this-file/buffer-repeat'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-previous-bookmark-this-file/buffer))

;;;###autoload (autoload 'bmkp-next-bookmark-this-file "bookmark+")
(defun bmkp-next-bookmark-this-file (n &optional startoverp) ; Bind to repeatable key, e.g. `S-f2'
  "Jump to the Nth-next bookmark for the current file.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle-this-file'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-file n nil startoverp))

;;;###autoload (autoload 'bmkp-previous-bookmark-this-file "bookmark+")
(defun bmkp-previous-bookmark-this-file (n &optional startoverp) ; Bind to repeatable key, e.g. `f2'
  "Jump to the Nth-previous bookmark for the current file.
See `bmkp-next-bookmark-this-file'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-file (- n) nil startoverp))

;;;###autoload (autoload 'bmkp-next-bookmark-this-file-repeat "bookmark+")
(defun bmkp-next-bookmark-this-file-repeat (arg)
  "Jump to the Nth next bookmark for the current file.
This is a repeatable version of `bmkp-next-bookmark-this-file'.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-next-bookmark-this-file))

;;;###autoload (autoload 'bmkp-previous-bookmark-this-file-repeat "bookmark+")
(defun bmkp-previous-bookmark-this-file-repeat (arg)
  "Jump to the Nth previous bookmark for the current file.
See `bmkp-next-bookmark-this-file-repeat'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-previous-bookmark-this-file))


;;;###autoload (autoload 'bmkp-next-bookmark-this-buffer "bookmark+")
(defun bmkp-next-bookmark-this-buffer (n &optional startoverp) ; Bind to repeatable key, e.g. `S-f2'
  "Jump to the Nth-next bookmark in the current buffer.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle-this-buffer'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-buffer n nil startoverp))

;;;###autoload (autoload 'bmkp-previous-bookmark-this-buffer "bookmark+")
(defun bmkp-previous-bookmark-this-buffer (n &optional startoverp) ; Bind to repeatable key, e.g. `f2'
  "Jump to the Nth-previous bookmark in the current buffer.
See `bmkp-next-bookmark-this-buffer'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-buffer (- n) nil startoverp))

;;;###autoload (autoload 'bmkp-next-bookmark-this-buffer-repeat "bookmark+")
(defun bmkp-next-bookmark-this-buffer-repeat (arg)
  "Jump to the Nth next bookmark in the current buffer.
This is a repeatable version of `bmkp-next-bookmark-this-buffer'.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-next-bookmark-this-buffer))

;;;###autoload (autoload 'bmkp-previous-bookmark-this-buffer-repeat "bookmark+")
(defun bmkp-previous-bookmark-this-buffer-repeat (arg)
  "Jump to the Nth previous bookmark in the current buffer.
See `bmkp-next-bookmark-this-buffer-repeat'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-previous-bookmark-this-buffer))

;;;###autoload (autoload 'bmkp-next-bookmark-w32 "bookmark+")
(defun bmkp-next-bookmark-w32 (n &optional startoverp)       ; You can bind this to a repeatable key
  "Windows `Open' the Nth next bookmark in the bookmark navigation list.
MS Windows only.  Invokes the program associated with the file type.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (let ((bmkp-use-w32-browser-p  t))  (bmkp-cycle n nil startoverp)))

;;;###autoload (autoload 'bmkp-previous-bookmark-w32 "bookmark+")
(defun bmkp-previous-bookmark-w32 (n &optional startoverp)   ; You can bind this to a repeatable key
  "Windows `Open' the Nth previous bookmark in the bookmark navlist.
See `bmkp-next-bookmark-w32'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (let ((bmkp-use-w32-browser-p  t))  (bmkp-cycle (- n) nil startoverp)))

;;;###autoload (autoload 'bmkp-next-bookmark-w32-repeat "bookmark+")
(defun bmkp-next-bookmark-w32-repeat (arg) ; `C-x p next'
  "Windows `Open' the Nth next bookmark in the bookmark navigation list.
This is a repeatable version of `bmkp-next-bookmark'.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at the first one (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (let ((bmkp-use-w32-browser-p  t))  (bmkp-repeat-command 'bmkp-next-bookmark)))

;;;###autoload (autoload 'bmkp-previous-bookmark-w32-repeat "bookmark+")
(defun bmkp-previous-bookmark-w32-repeat (arg) ; `C-x p prior'
  "Windows `Open' the Nth previous bookmark in the bookmark navlist.
See `bmkp-next-bookmark-w32-repeat'."
  (interactive "P")
  (require 'repeat)
  (let ((bmkp-use-w32-browser-p  t))  (bmkp-repeat-command 'bmkp-previous-bookmark)))

;; In spite of their names, `bmkp-cycle-specific-(buffers|files)*' just cycle bookmarks in the
;; current buffer or file.  There is no way to choose multiple buffers or files.
;;
;; `bmkp-cycle-autonamed', `bmkp-cycle-autonamed-other-window',
;; `bmkp-cycle-bookmark-list', `bmkp-cycle-bookmark-list-other-window',
;; `bmkp-cycle-desktop',
;; `bmkp-cycle-dired', `bmkp-cycle-dired-other-window',
;; `bmkp-cycle-file', `bmkp-cycle-file-other-window',
;; `bmkp-cycle-gnus', `bmkp-cycle-gnus-other-window',
;; `bmkp-cycle-info', `bmkp-cycle-info-other-window',
;; `bmkp-cycle-lighted', `bmkp-cycle-lighted-other-window',
;; `bmkp-cycle-local-file', `bmkp-cycle-local-file-other-window',
;; `bmkp-cycle-man', `bmkp-cycle-man-other-window',
;; `bmkp-cycle-non-file', `bmkp-cycle-non-file-other-window',
;; `bmkp-cycle-remote-file', `bmkp-cycle-remote-file-other-window',
;; `bmkp-cycle-specific-buffers', `bmkp-cycle-specific-buffers-other-window',
;; `bmkp-cycle-specific-files', `bmkp-cycle-specific-files-other-window',
;; `bmkp-cycle-variable-list',
;; `bmkp-cycle-url', `bmkp-cycle-url-other-window',
;;
(bmkp-define-cycle-command "autonamed")
(bmkp-define-cycle-command "autonamed" 'OTHER-WINDOW)
(bmkp-define-cycle-command "bookmark-list") ; No other-window version needed
(bmkp-define-cycle-command "desktop")   ; No other-window version needed
(bmkp-define-cycle-command "dired")
(bmkp-define-cycle-command "dired" 'OTHER-WINDOW)
(bmkp-define-cycle-command "file")
(bmkp-define-cycle-command "file" 'OTHER-WINDOW)
(bmkp-define-cycle-command "gnus")
(bmkp-define-cycle-command "gnus" 'OTHER-WINDOW)
(bmkp-define-cycle-command "info")
(bmkp-define-cycle-command "info" 'OTHER-WINDOW)
(when (featurep 'bookmark+-lit)
  (bmkp-define-cycle-command "lighted")
  (bmkp-define-cycle-command "lighted" 'OTHER-WINDOW))
(bmkp-define-cycle-command "local-file")
(bmkp-define-cycle-command "local-file" 'OTHER-WINDOW)
(bmkp-define-cycle-command "man")
(bmkp-define-cycle-command "man" 'OTHER-WINDOW)
(bmkp-define-cycle-command "non-file")
(bmkp-define-cycle-command "non-file" 'OTHER-WINDOW)
(bmkp-define-cycle-command "remote-file")
(bmkp-define-cycle-command "remote-file" 'OTHER-WINDOW)
(bmkp-define-cycle-command "specific-buffers")
(bmkp-define-cycle-command "specific-buffers" 'OTHER-WINDOW)
(bmkp-define-cycle-command "specific-files")
(bmkp-define-cycle-command "specific-files" 'OTHER-WINDOW)
(bmkp-define-cycle-command "variable-list") ; No other-window version needed
(bmkp-define-cycle-command "url")
(bmkp-define-cycle-command "url" 'OTHER-WINDOW)

;; `bmkp-next-autonamed-bookmark', `bmkp-next-autonamed-bookmark-other-window',
;; `bmkp-next-autonamed-bookmark-repeat', `bmkp-next-autonamed-bookmark-other-window-repeat',
;; `bmkp-next-bookmark-list-bookmark',
;; `bmkp-next-bookmark-list-bookmark-repeat',
;; `bmkp-next-bookmark-list-bookmark-other-window',
;; `bmkp-next-bookmark-list-bookmark-other-window-repeat',
;; `bmkp-next-desktop-bookmark',
;; `bmkp-next-desktop-bookmark-repeat',
;; `bmkp-next-desktop-bookmark-other-window',
;; `bmkp-next-desktop-bookmark-other-window-repeat',
;; `bmkp-next-dired-bookmark',
;; `bmkp-next-dired-bookmark-repeat',
;; `bmkp-next-dired-bookmark-other-window',
;; `bmkp-next-dired-bookmark-other-window-repeat',
;; `bmkp-next-file-bookmark',
;; `bmkp-next-file-bookmark-repeat',
;; `bmkp-next-file-bookmark-other-window',
;; `bmkp-next-file-bookmark-other-window-repeat',
;; `bmkp-next-gnus-bookmark',
;; `bmkp-next-gnus-bookmark-repeat',
;; `bmkp-next-gnus-bookmark-other-window',
;; `bmkp-next-gnus-bookmark-other-window-repeat',
;; `bmkp-next-info-bookmark',
;; `bmkp-next-info-bookmark-repeat',
;; `bmkp-next-info-bookmark-other-window',
;; `bmkp-next-info-bookmark-other-window-repeat',
;; `bmkp-next-lighted-bookmark',
;; `bmkp-next-lighted-bookmark-repeat',
;; `bmkp-next-lighted-bookmark-other-window',
;; `bmkp-next-lighted-bookmark-other-window-repeat',
;; `bmkp-next-local-file-bookmark',
;; `bmkp-next-local-file-bookmark-repeat',
;; `bmkp-next-local-file-bookmark-other-window',
;; `bmkp-next-local-file-bookmark-other-window-repeat',
;; `bmkp-next-man-bookmark',
;; `bmkp-next-man-bookmark-repeat',
;; `bmkp-next-man-bookmark-other-window',
;; `bmkp-next-man-bookmark-other-window-repeat',
;; `bmkp-next-non-file-bookmark',
;; `bmkp-next-non-file-bookmark-repeat',
;; `bmkp-next-non-file-bookmark-other-window',
;; `bmkp-next-non-file-bookmark-other-window-repeat',
;; `bmkp-next-remote-file-bookmark',
;; `bmkp-next-remote-file-bookmark-repeat',
;; `bmkp-next-remote-file-bookmark-other-window',
;; `bmkp-next-remote-file-bookmark-other-window-repeat',
;; `bmkp-next-specific-buffers-bookmark',
;; `bmkp-next-specific-buffers-bookmark-repeat',
;; `bmkp-next-specific-buffers-bookmark-other-window',
;; `bmkp-next-specific-buffers-bookmark-other-window-repeat',
;; `bmkp-next-specific-files-bookmark',
;; `bmkp-next-specific-files-bookmark-repeat',
;; `bmkp-next-specific-files-bookmark-other-window',
;; `bmkp-next-specific-files-bookmark-other-window-repeat',
;; `bmkp-next-variable-list-bookmark',
;; `bmkp-next-variable-list-bookmark-repeat',
;; `bmkp-next-variable-list-bookmark-other-window',
;; `bmkp-next-variable-list-bookmark-other-window-repeat',
;; `bmkp-next-url-bookmark',
;; `bmkp-next-url-bookmark-repeat'.
;; `bmkp-next-url-bookmark-other-window',
;; `bmkp-next-url-bookmark-other-window-repeat'.
;;
;; `bmkp-previous-autonamed-bookmark',
;; `bmkp-previous-autonamed-bookmark-repeat',
;; `bmkp-previous-autonamed-bookmark-other-window',
;; `bmkp-previous-autonamed-bookmark-other-window-repeat',
;; `bmkp-previous-bookmark-list-bookmark',
;; `bmkp-previous-bookmark-list-bookmark-repeat',
;; `bmkp-previous-bookmark-list-bookmark-other-window',
;; `bmkp-previous-bookmark-list-bookmark-other-window-repeat',
;; `bmkp-previous-desktop-bookmark',
;; `bmkp-previous-desktop-bookmark-repeat',
;; `bmkp-previous-desktop-bookmark-other-window',
;; `bmkp-previous-desktop-bookmark--other-windowrepeat',
;; `bmkp-previous-dired-bookmark',
;; `bmkp-previous-dired-bookmark-repeat',
;; `bmkp-previous-dired-bookmark-other-window',
;; `bmkp-previous-dired-bookmark-other-window-repeat',
;; `bmkp-previous-file-bookmark',
;; `bmkp-previous-file-bookmark-repeat',
;; `bmkp-previous-file-bookmark-other-window',
;; `bmkp-previous-file-bookmark-other-window-repeat',
;; `bmkp-previous-gnus-bookmark',
;; `bmkp-previous-gnus-bookmark-repeat',
;; `bmkp-previous-gnus-bookmark-other-window',
;; `bmkp-previous-gnus-bookmark-other-window-repeat',
;; `bmkp-previous-info-bookmark',
;; `bmkp-previous-info-bookmark-repeat',
;; `bmkp-previous-info-bookmark-other-window',
;; `bmkp-previous-info-bookmark-other-window-repeat',
;; `bmkp-previous-lighted-bookmark',
;; `bmkp-previous-lighted-bookmark-repeat',
;; `bmkp-previous-lighted-bookmark-other-window',
;; `bmkp-previous-lighted-bookmark-other-window-repeat',
;; `bmkp-previous-local-file-bookmark',
;; `bmkp-previous-local-file-bookmark-repeat',
;; `bmkp-previous-local-file-bookmark-other-window',
;; `bmkp-previous-local-file-bookmark-other-window-repeat',
;; `bmkp-previous-man-bookmark',
;; `bmkp-previous-man-bookmark-repeat',
;; `bmkp-previous-man-bookmark-other-window',
;; `bmkp-previous-man-bookmark-other-window-repeat',
;; `bmkp-previous-non-file-bookmark',
;; `bmkp-previous-non-file-bookmark-repeat',
;; `bmkp-previous-non-file-bookmark-other-window',
;; `bmkp-previous-non-file-bookmark-other-window-repeat',
;; `bmkp-previous-remote-file-bookmark',
;; `bmkp-previous-remote-file-bookmark-repeat',
;; `bmkp-previous-remote-file-bookmark-other-window',
;; `bmkp-previous-remote-file-bookmark--other-windowrepeat',
;; `bmkp-previous-specific-buffers-bookmark',
;; `bmkp-previous-specific-buffers-bookmark-repeat',
;; `bmkp-previous-specific-buffers-bookmark-other-window',
;; `bmkp-previous-specific-buffers-bookmark-other-window-repeat',
;; `bmkp-previous-specific-files-bookmark',
;; `bmkp-previous-specific-files-bookmark-repeat',
;; `bmkp-previous-specific-files-bookmark-other-window',
;; `bmkp-previous-specific-files-bookmark-other-window-repeat',
;; `bmkp-previous-variable-list-bookmark',
;; `bmkp-previous-variable-list-bookmark-repeat',
;; `bmkp-previous-variable-list-bookmark-other-window',
;; `bmkp-previous-variable-list-bookmark-other-window-repeat',
;; `bmkp-previous-url-bookmark',
;; `bmkp-previous-url-bookmark-repeat'.
;; `bmkp-previous-url-bookmark-other-window',
;; `bmkp-previous-url-bookmark-other-window-repeat'.
;;
(bmkp-define-next+prev-cycle-commands "autonamed")
(bmkp-define-next+prev-cycle-commands "autonamed" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "bookmark-list")
(bmkp-define-next+prev-cycle-commands "desktop")
(bmkp-define-next+prev-cycle-commands "dired")
(bmkp-define-next+prev-cycle-commands "dired" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "file")
(bmkp-define-next+prev-cycle-commands "file" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "gnus")
(bmkp-define-next+prev-cycle-commands "gnus" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "info")
(bmkp-define-next+prev-cycle-commands "info" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "lighted")
(bmkp-define-next+prev-cycle-commands "lighted" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "local-file")
(bmkp-define-next+prev-cycle-commands "local-file" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "man")
(bmkp-define-next+prev-cycle-commands "man" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "non-file")
(bmkp-define-next+prev-cycle-commands "non-file" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "remote-file")
(bmkp-define-next+prev-cycle-commands "remote-file" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "specific-buffers")
(bmkp-define-next+prev-cycle-commands "specific-buffers" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "specific-files")
(bmkp-define-next+prev-cycle-commands "specific-files" 'OTHER-WINDOW)
(bmkp-define-next+prev-cycle-commands "variable-list")
(bmkp-define-next+prev-cycle-commands "url")
(bmkp-define-next+prev-cycle-commands "url" 'OTHER-WINDOW)

;;;###autoload (autoload 'bmkp-toggle-autonamed-bookmark-set/delete "bookmark+")
(defun bmkp-toggle-autonamed-bookmark-set/delete (&optional position allp)
                                        ; Bound globally to `C-x p RET', `C-x p c RET'
  "If there is an autonamed bookmark at point, delete it, else create one.
The bookmark created has no region.  Its name is formatted according
to option `bmkp-autoname-bookmark-function'.

With a prefix arg, delete *ALL* autonamed bookmarks for this buffer.

Non-interactively, act at POSITION, not point.  If nil, act at point."
  (interactive "d\nP")
  (unless position (setq position  (point)))
  (if allp
      (bmkp-delete-all-autonamed-for-this-buffer)
    (let ((bmk-name  (funcall bmkp-autoname-bookmark-function position)))
      (if (not (bmkp-get-bookmark-in-alist bmk-name 'NOERROR))
          (let ((mark-active  nil))     ; Do not set a region bookmark.
            (bookmark-set bmk-name)
            (message "Set bookmark `%s'" bmk-name))
        (bookmark-delete bmk-name)
        (message "Deleted bookmark `%s'" bmk-name)))))

;;;###autoload (autoload 'bmkp-set-autonamed-bookmark "bookmark+")
(defun bmkp-set-autonamed-bookmark (&optional position msg-p)
  "Set an autonamed bookmark at point.
The bookmark created has no region.  Its name is formatted according
to option `bmkp-autoname-bookmark-function'.
Non-interactively:
 - Act at POSITION, not point.  If nil, act at point.
 - Non-nil optional arg MSG-P means display a status message."
  (interactive (list (point) 'MSG))
  (unless position (setq position  (point)))
  (let ((bmk-name     (funcall bmkp-autoname-bookmark-function position))
        (mark-active  nil))             ; Do not set a region bookmark.
    (bookmark-set bmk-name)
    (when msg-p (message "Set bookmark `%s'" bmk-name))))

;;;###autoload (autoload 'bmkp-set-autonamed-bookmark-at-line "bookmark+")
(defun bmkp-set-autonamed-bookmark-at-line (&optional number)
  "Set an autonamed bookmark at the beginning of the current line.
With a prefix arg, set it at the line whose number is the numeric
prefix value."
  (interactive (list (and current-prefix-arg  (prefix-numeric-value current-prefix-arg))))
  (if (not number)
      (bmkp-set-autonamed-bookmark (line-beginning-position))
    (save-excursion
      (goto-char (point-min))
      (let ((inhibit-field-text-motion  t))
        (bmkp-set-autonamed-bookmark (line-beginning-position number))))))

(when (> emacs-major-version 21)
  (defun bmkp-occur-create-autonamed-bookmarks (&optional msg-p) ; Bound to `C-c C-M-B' (aka `C-c C-M-S-b')
    "Create an autonamed bookmark for each `occur' hit.
You can use this only in `Occur' mode (commands such as `occur' and
`multi-occur').
Non-interactively, non-nil MSG-P means display a status message."
    (interactive "p")
    (unless (eq major-mode 'occur-mode) (error "You must be in `occur-mode'"))
    (let ((count  0))
      (save-excursion
        (goto-char (point-min))
        (while (condition-case nil (progn (occur-next) t) (error nil))
          (let* ((pos   (get-text-property (point) 'occur-target))
                 (buf   (and pos  (marker-buffer pos))))
            (when buf
              (with-current-buffer buf
                (goto-char pos)
                (bmkp-set-autonamed-bookmark (point)))
              (setq count  (1+ count))))))
      (when msg-p (message "Created %d autonamed bookmarks" count)))))

;;;###autoload (autoload 'bmkp-set-autonamed-regexp-buffer "bookmark+")
(defun bmkp-set-autonamed-regexp-buffer (regexp &optional msg-p)
  "Set autonamed bookmarks at matches for REGEXP in the buffer.
Non-interactively, non-nil MSG-P means display a status message."
  (interactive (list (bmkp-read-regexp "Regexp: ") 'MSG))
  (bmkp-set-autonamed-regexp-region regexp (point-min) (point-max) msg-p))

;;;###autoload (autoload 'bmkp-set-autonamed-regexp-region "bookmark+")
(defun bmkp-set-autonamed-regexp-region (regexp beg end &optional msg-p)
  "Set autonamed bookmarks at matches for REGEXP in the region.
Non-interactively, non-nil MSG-P means display a status message."
  (interactive (list (bmkp-read-regexp "Regexp: ") (region-beginning) (region-end) 'MSG))
  (let ((count  0))
    (save-excursion
      (goto-char beg)
      (while (re-search-forward regexp end t)
        (bmkp-set-autonamed-bookmark (point))
        (setq count  (1+ count))
        (forward-line 1)))
    (when msg-p (message "Set %d autonamed bookmarks" count))))

(defun bmkp-autoname-bookmark-function-default (position)
  "Return a bookmark name using POSITION and the current buffer name.
The name is composed as follows:
 POSITION followed by a space and then the buffer name.
 The position value is prefixed with zeros to comprise 9 characters.
 For example, for POSITION value 31416 and current buffer `my-buffer',
 the name returned would be `000031416 my-buffer'"
  (format "%09d %s" (abs position) (buffer-name)))

;;;###autoload (autoload 'bmkp-delete-all-autonamed-for-this-buffer "bookmark+")
(defun bmkp-delete-all-autonamed-for-this-buffer (&optional msg-p)
  "Delete all autonamed bookmarks for the current buffer.
Interactively, or with non-nil arg MSG-P, require confirmation.
To be deleted, a bookmark name must be an autonamed bookmark whose
buffer part names the current buffer."
  (interactive "p")
  (let ((bmks-to-delete  (mapcar #'bmkp-bookmark-name-from-record
                                 (bmkp-autonamed-this-buffer-alist-only))))
    (if (null bmks-to-delete)
        (when msg-p (message "No autonamed bookmarks for buffer `%s'" (buffer-name)))
      (when (or (not msg-p)
                (y-or-n-p (format "Delete ALL autonamed bookmarks for buffer `%s'? " (buffer-name))))
        (let ((bookmark-save-flag   (and (not bmkp-count-multi-mods-as-one-flag)
                                         bookmark-save-flag))) ; Save at most once, after `dolist'.
          (dolist (bmk  bmks-to-delete)  (bookmark-delete bmk 'BATCHP))) ; No refresh yet.
        (bmkp-refresh/rebuild-menu-list nil (not msg-p)) ; Now refresh, after iterate.
        (when msg-p (message "Deleted all bookmarks for buffer `%s'" (buffer-name)))))))

;; You can use this in `kill-buffer-hook'.
(defun bmkp-delete-autonamed-this-buffer-no-confirm (&optional no-refresh-p)
  "Delete all autonamed bookmarks for this buffer, without confirmation.
Non-nil optional arg NO-REFRESH-P means do not refresh/rebuild the
bookmark-list."
  (when (and bookmarks-already-loaded  bookmark-alist)
    (let ((bmks-to-delete      (mapcar #'bmkp-bookmark-name-from-record
                                       (bmkp-autonamed-this-buffer-alist-only)))
          (bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                    bookmark-save-flag))) ; Save at most once, after `dolist'.
      (dolist (bmk  bmks-to-delete)  (bookmark-delete bmk 'BATCHP))) ; No refresh yet.
    (unless no-refresh-p
      (bmkp-refresh/rebuild-menu-list nil 'BATCHP)))) ; Now refresh, after iterate.


;; You can use this in `kill-emacs-hook'.
(defun bmkp-delete-autonamed-no-confirm ()
  "Delete all autonamed bookmarks for all buffers, without confirmation."
  (when (and bookmarks-already-loaded  bookmark-alist)
    (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                    bookmark-save-flag))) ; Save at most once, after `dolist'.
      (dolist (buf  (buffer-list))
        (with-current-buffer buf
          (bmkp-delete-autonamed-this-buffer-no-confirm 'NO-REFRESH-P)))) ; No refresh yet.
    (bmkp-refresh/rebuild-menu-list nil 'BATCHP))) ; Now refresh, after iterate.

(cond ((fboundp 'define-minor-mode)
       ;; Emacs 21 and later.  Eval this so that even if the library is byte-compiled with Emacs 20,
       ;; loading it into Emacs 21+ will define variable `bmkp-auto-idle-bookmark-mode'.
       (eval '(define-minor-mode bmkp-auto-idle-bookmark-mode
               "Toggle automatic setting of a bookmark when Emacs is idle.
Non-interactively, turn automatic bookmarking on for the current
buffer if and only if ARG is positive.

To enable or disable automatic bookmarking in all buffers, use
`bmkp-global-auto-idle-bookmark-mode'.

When the mode is enabled in the current buffer, a bookmark is
automatically set every `bmkp-auto-idle-bookmark-mode-delay' seconds,
using the setting function that is the value of option
`bmkp-auto-idle-bookmark-mode-set-function'.  Note that a buffer must
be current (selected) for an automatic bookmark to be created there -
it is not enough that the mode be enabled in the buffer.

Turning the mode on and off runs hooks
`bmkp-auto-idle-bookmark-mode-on-hook' and
`bmkp-auto-idle-bookmark-mode-off-hook', respectively.

If you want the automatic bookmarks to be temporary (not saved to your
bookmark file), then customize option
`bmkp-autotemp-bookmark-predicates' so that it includes the kind of
bookmarks that are set by `bmkp-auto-idle-bookmark-mode-set-function'.
For example, if automatic bookmarking sets autonamed bookmarks, then
`bmkp-autotemp-bookmark-predicates' should include
`bmkp-autonamed-bookmark-p' or
`bmkp-autonamed-this-buffer-bookmark-p'.

If you want the automatically created bookmarks to be highlighted,
then customize option `bmkp-auto-light-when-set' to highlight
bookmarks of the appropriate kind.  For example, to highlight
autonamed bookmarks set it to `autonamed-bookmark'.

NOTE: If you use Emacs 21 then there is no global version of the mode
- that is, there is no command `bmkp-global-auto-idle-bookmark-mode'."
               :init-value nil :group 'bookmark-plus :require 'bookmark+
               :lighter bmkp-auto-idle-bookmark-mode-lighter
               :link `(url-link :tag "Send Bug Report"
                       ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
Bookmark bug: \
&body=Describe bug here, starting with `emacs -Q'.  \
Don't forget to mention your Emacs and library versions."))
               :link '(url-link :tag "Download" "http://www.emacswiki.org/bookmark+.el")
               :link '(url-link :tag "Description" "http://www.emacswiki.org/BookmarkPlus")
               :link '(emacs-commentary-link :tag "Commentary" "bookmark+")
               (when bmkp-auto-idle-bookmark-mode-timer
                 (cancel-timer bmkp-auto-idle-bookmark-mode-timer)
                 (setq bmkp-auto-idle-bookmark-mode-timer  nil))
               (when bmkp-auto-idle-bookmark-mode
                 (setq bmkp-auto-idle-bookmark-mode-timer
                       (run-with-idle-timer bmkp-auto-idle-bookmark-mode-delay 'REPEAT
                                            (lambda ()
                                              (when (and bmkp-auto-idle-bookmark-mode
                                                         (bmkp-not-near-other-auto-idle-bmks))
                                                (let ((bmkp-setting-auto-idle-bmk-p  t))
                                                  (funcall bmkp-auto-idle-bookmark-mode-set-function)))))))
               (when (interactive-p)
                 (message "Automatic bookmarking is now %s in buffer `%s'"
                          (if bmkp-auto-idle-bookmark-mode "ON" "OFF") (buffer-name)))))

       (eval '(defun bmkp-turn-on-auto-idle-bookmark-mode ()
               "Turn on `bmkp-auto-idle-bookmark-mode'."
               (bmkp-auto-idle-bookmark-mode 1)))

       (when (fboundp 'define-globalized-minor-mode) ; Emacs 22+, not 21.
         (eval '(define-globalized-minor-mode bmkp-global-auto-idle-bookmark-mode
                 bmkp-auto-idle-bookmark-mode
                 bmkp-turn-on-auto-idle-bookmark-mode
                 :group 'bookmark-plus :require 'bookmark+))))
      (t                                ; Emacs 20.
       (defun bmkp-auto-idle-bookmark-mode (&optional arg)
         "Toggle automatic setting of a bookmark when Emacs is idle.
Non-interactively, turn automatic bookmarking on if and only if ARG is
positive.

When the mode is enabled, a bookmark is automatically set every
`bmkp-auto-idle-bookmark-mode-delay' seconds, using the setting
function that is the value of option
`bmkp-auto-idle-bookmark-mode-set-function'.  Note that a buffer must
be current (selected) for an automatic bookmark to be created there -
it is not enough that the mode be enabled in the buffer.

If you want these bookmarks to be temporary (not saved to your
bookmark file), then customize option
`bmkp-autotemp-bookmark-predicates' so that it includes the kind of
bookmarks that are set by `bmkp-auto-idle-bookmark-mode-set-function'.
For example, if automatic bookmarking sets autonamed bookmarks, then
`bmkp-autotemp-bookmark-predicates' should include
`bmkp-autonamed-bookmark-p'.

If you want the automatically created bookmarks to be highlighted,
then customize option `bmkp-auto-light-when-set' to highlight
bookmarks of the appropriate kind.  For example, to highlight
autonamed bookmarks set it to `autonamed-bookmark'.

NOTE: This is the Emacs 20 version of `bmkp-auto-idle-bookmark-mode',
which is global only, that is, all buffers are affected.  If you
instead want it to be local only, then do both of the following in
your init file:
  (make-variable-buffer-local 'bmkp-auto-idle-bookmark-mode)
  (make-variable-buffer-local 'bmkp-auto-idle-bookmark-mode-timer)"
         (interactive (list (or current-prefix-arg 'toggle)))
         (setq bmkp-auto-idle-bookmark-mode  (if (eq arg 'toggle)
                                                 (not bmkp-auto-idle-bookmark-mode)
                                               (> (prefix-numeric-value arg) 0)))
         (when bmkp-auto-idle-bookmark-mode-timer
           (cancel-timer bmkp-auto-idle-bookmark-mode-timer)
           (setq bmkp-auto-idle-bookmark-mode-timer  nil))
         (when bmkp-auto-idle-bookmark-mode
           (setq bmkp-auto-idle-bookmark-mode-timer
                 (run-with-idle-timer bmkp-auto-idle-bookmark-mode-delay 'REPEAT
                                      (lambda () ; This allows use as a local mode.
                                        (when (and bmkp-auto-idle-bookmark-mode
                                                   (bmkp-not-near-other-auto-idle-bmks))
                                          (let ((bmkp-setting-auto-idle-bmk-p  t))
                                            (funcall bmkp-auto-idle-bookmark-mode-set-function)))))))
         (when (interactive-p)
           (message "Automatic bookmarking is now %s%s"
                    (if bmkp-auto-idle-bookmark-mode "ON" "OFF")
                    (if (local-variable-if-set-p 'bmkp-auto-idle-bookmark-mode)
                        (format " in buffer `%s'" (current-buffer))
                      ""))))


       (add-to-list 'minor-mode-alist `(bmkp-auto-idle-bookmark-mode
                                        ,bmkp-auto-idle-bookmark-mode-lighter))))

(defun bmkp-not-near-other-auto-idle-bmks (&optional position)
  "Is POSITION far enough from automatic bookmarks to create a new one?
Return non-nil if `bmkp-auto-idle-bookmark-min-distance' is nil or if
POSITION is at least `bmkp-auto-idle-bookmark-min-distance' chars from
all other automatic bookmarks in the same buffer.  Else return nil."
  (unless position (setq position  (point)))
  (or (not bmkp-auto-idle-bookmark-min-distance)
      (catch 'bmkp-not-near-other-auto-idle-bmks
        (let (bmk-pos)
          (dolist (bmk  bmkp-auto-idle-bookmarks)
            (when (and (bmkp-this-buffer-p bmk)
                       (setq bmk-pos  (bookmark-get-position bmk))
                       (or (not bmk-pos)
                           (< (abs (- position bmk-pos)) bmkp-auto-idle-bookmark-min-distance)))
              (throw 'bmkp-not-near-other-auto-idle-bmks nil)))
          t))))

(when (> emacs-major-version 21)        ; Emacs 22+ (need also `Info-selection-hook').

  ;; Eval this so that even if the library is byte-compiled with Emacs 20,
  ;; loading it into Emacs 22+ will define variable `bmkp-info-auto-bookmark-mode'.
  (eval '(define-minor-mode bmkp-info-auto-bookmark-mode
          "Toggle automatically setting a bookmark when you visit an Info node.
The bookmark name is \"(MANUAL) `NODE'\", where:

 MANUAL is the name of the current manual (the base file name).
 NODE is the name of the current node.

If option `bmkp-info-auto-type' is `create-or-update' then such a
bookmark is created for the node if none exists.  If the option value
is `update-only' then no new bookmark is created automatically, but an
existing bookmark is updated.  (Updating a bookmark increments the
recorded number of visits.)  You can toggle the option using
`\\[bmkp-toggle-info-auto-type]'."
          :init-value nil :global t :group 'bookmark-plus :require 'bookmark+
          :lighter bmkp-auto-idle-bookmark-mode-lighter
          :link `(url-link :tag "Send Bug Report"
                  ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
Bookmark bug: \
&body=Describe bug here, starting with `emacs -Q'.  \
Don't forget to mention your Emacs and library versions."))
          :link '(url-link :tag "Download" "http://www.emacswiki.org/bookmark+.el")
          :link '(url-link :tag "Description" "http://www.emacswiki.org/BookmarkPlus")
          :link '(emacs-commentary-link :tag "Commentary" "bookmark+")
          (if bmkp-info-auto-bookmark-mode
              (add-hook 'Info-selection-hook 'bmkp-set-info-bookmark-with-node-name)
            (remove-hook 'Info-selection-hook 'bmkp-set-info-bookmark-with-node-name))
          (when (interactive-p)
            (message "Automatic Info bookmarking is now %s" (if bmkp-info-auto-bookmark-mode "ON" "OFF")))))

  (defun bmkp-set-info-bookmark-with-node-name (&optional nomsg)
    "Maybe bookmark the current Info node using name \"(MANUAL) `NODE'\".
MANUAL is the name of the current manual (the base file name).
NODE is the name of the current node.

If option `bmkp-info-auto-type' is `create-or-update' then a bookmark
is created for the node if none exists.  If it is `update-only' then
no new bookmark is created automatically, but an existing bookmark is
updated.  You can use toggle `bmkp-info-auto-type' using
`\\[bmkp-toggle-info-auto-type]'.

Non-nil optional arg NOMSG means do not display a message saying that
the node was bookmarked."
    (interactive)
    (when (and (derived-mode-p 'Info-mode)  Info-current-node)
      (save-excursion
        (goto-char (point-min))
        (let* ((bmk-name  (and (stringp Info-current-file)
                               (format "(%s) %s" (file-name-sans-extension
                                                  (file-name-nondirectory Info-current-file))
                                       Info-current-node)))
               (bmk       (bmkp-bookmark-record-from-name bmk-name 'NOERROR))
               (visits    (and bmk  (bookmark-prop-get bmk 'visits))))
          (when bmk-name
            (cond ((and (not visits)  (eq bmkp-info-auto-type 'create-or-update))
                   (bookmark-set bmk-name)
                   (unless nomsg (message "Created bookmark `%s' for Info node" bmk-name)))
                  (visits
                   (bmkp-record-visit bmk-name 'BATCHP)
                   (bmkp-refresh/rebuild-menu-list bmk-name nil)
                   (bmkp-maybe-save-bookmarks)
                   (unless nomsg (message "Updated bookmark `%s' for Info node" bmk-name)))))))))

  (defun bmkp-toggle-info-auto-type (&optional msgp)
    "Toggle the value of option `bmkp-info-auto-type'."
    (interactive "p")
    (setq bmkp-info-auto-type  (if (eq bmkp-info-auto-type 'create-or-update) 'update-only 'create-or-update))
    (when msgp (message "`bmkp-info-auto-bookmark-mode' now %s" 
                        (if (eq bmkp-info-auto-type 'create-or-update)
                            "CREATES, as well as updates, Info bookmarks"
                          "only UPDATES EXISTING Info bookmarks"))))

  )

(if (fboundp 'define-minor-mode)
    ;; Emacs 21 and later.  Eval this so that even if the library is byte-compiled with Emacs 20,
    ;; loading it into Emacs 21+ will define variable `bmkp-temporary-bookmarking-mode'.
    (eval '(define-minor-mode bmkp-temporary-bookmarking-mode ; `M-L' in `*Bookmark List*'.
            "Toggle temporary bookmarking.
Temporary bookmarking means that any bookmark changes (creation,
modification, deletion) are NOT automatically saved.

Interactively, you are required to confirm turning on the mode.

When the mode is turned ON:
 a. `bookmark-save-flag' is set to nil.
 b. `bmkp-current-bookmark-file' is set to a new, empty bookmark file
    in directory `temporary-file-directory' (via `make-temp-file').
 c. That file is not saved automatically.
 d. In the `*Bookmark List*' display, the major-mode mode-line
    indicator is set to `TEMPORARY ONLY'.

Non-interactively, turn temporary bookmarking on if and only if ARG is
positive.  Non-interactively there is no prompt for confirmation."
            :init-value nil :global t :group 'bookmark-plus :lighter bmkp-temporary-bookmarking-mode-lighter
            :link `(url-link :tag "Send Bug Report"
                    ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
Bookmark bug: \
&body=Describe bug here, starting with `emacs -Q'.  \
Don't forget to mention your Emacs and library versions."))
            :link '(url-link :tag "Download" "http://www.emacswiki.org/bookmark+.el")
            :link '(url-link :tag "Description" "http://www.emacswiki.org/BookmarkPlus")
            :link '(emacs-commentary-link :tag "Commentary" "bookmark+")
            (cond ((not bmkp-temporary-bookmarking-mode) ; Turn off.
                   (when (fboundp 'bmkp-unlight-bookmarks) ; In `bookmark+-lit.el'.
                     (bmkp-unlight-bookmarks ; Unhighlight the temporary (current) bookmarks.
                      '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays) nil))
                   (bmkp-switch-to-last-bookmark-file)
                   (setq bmkp-last-bookmark-file  bmkp-current-bookmark-file) ; Forget last (temp file).
                   (when (interactive-p)
                     (message "Bookmarking is NOT temporary now.  Restored previous bookmarks list")))
                  ((or (not (interactive-p))
                       (y-or-n-p (format "%switch to only temporary bookmarking? "
                                         (if bookmark-save-flag "Save current bookmarks, then s" "S"))))
                   (when (and (> bookmark-alist-modification-count 0)  bookmark-save-flag)
                     (bookmark-save))
                   (let ((new-file  (make-temp-file "bmkp-temp-")))
                     (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect new-file))
                       (goto-char (point-min))
                       (delete-region (point-min) (point-max)) ; In case a find-file hook inserted a header.
                       (if (boundp 'bookmark-file-coding-system) ; Emacs 25.2+
                           (bookmark-insert-file-format-version-stamp bookmark-file-coding-system)
                         (bookmark-insert-file-format-version-stamp))
                       (insert "(\n)"))
                     (bmkp-empty-file new-file)
                     (bookmark-load new-file t 'nosave) ; Saving was done just above.
                     (when bookmark-save-flag (bmkp-toggle-saving-bookmark-file (interactive-p))))
                   (when (interactive-p) (message "Bookmarking is now TEMPORARY")))
                  (t                    ; User refused to confirm.
                   (message "OK, canceled - bookmarking is NOT temporary")
                   (setq bmkp-temporary-bookmarking-mode  nil)))))

  ;; Emacs 20
  (defun bmkp-temporary-bookmarking-mode (&optional arg) ; `M-L' in `*Bookmark List*'.
    "Toggle temporary bookmarking.
Temporary bookmarking means that any bookmark changes (creation,
modification, deletion) are NOT automatically saved.

Interactively, you are required to confirm turning on the mode.

When the mode is turned ON:
 a. `bookmark-save-flag' is set to nil.
 b. `bmkp-current-bookmark-file' is set to a new, empty bookmark file
    in directory `temporary-file-directory' (via `make-temp-file').
 c. That file is not saved automatically.
 d. In the `*Bookmark List*' display, the major-mode mode-line
    indicator is set to `TEMPORARY ONLY'.

Non-interactively, turn temporary bookmarking on if and only if ARG is
positive.  Non-interactively there is no prompt for confirmation."
    (interactive "P")
    (setq bmkp-temporary-bookmarking-mode
          (if arg (> (prefix-numeric-value arg) 0) (not bmkp-temporary-bookmarking-mode)))
    (cond ((not bmkp-temporary-bookmarking-mode) ; Turn off.
           (when (fboundp 'bmkp-unlight-bookmarks) ; In `bookmark+-lit.el'.
             (bmkp-unlight-bookmarks    ; Unhighlight the temporary (current) bookmarks.
              '(bmkp-autonamed-overlays bmkp-non-autonamed-overlays) nil))
           (bmkp-switch-to-last-bookmark-file)
           (setq bmkp-last-bookmark-file  bmkp-current-bookmark-file) ; Forget last (temporary file).
           (run-hooks 'bmkp-temporary-bookmarking-mode-hook)
           (when (interactive-p)
             (message "Bookmarking is NOT temporary now.  Restored previous bookmarks list")))
          ((or (not (interactive-p))
               (y-or-n-p (format "%switch to only TEMPORARY bookmarking? "
                                 (if bookmark-save-flag "Save current bookmarks, then s" "S"))))
           (when (and (> bookmark-alist-modification-count 0)  bookmark-save-flag)
             (bookmark-save))
           (let ((new-file  (make-temp-file "bmkp-temp-")))
             (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect new-file))
               (goto-char (point-min))
               (delete-region (point-min) (point-max)) ; In case a find-file hook inserted a header, etc.
               (bookmark-insert-file-format-version-stamp)
               (insert "(\n)"))
             (bmkp-empty-file new-file)
             (bookmark-load new-file t 'nosave) ; Saving was done just above.
             (when bookmark-save-flag (bmkp-toggle-saving-bookmark-file (interactive-p))))
           (run-hooks 'bmkp-temporary-bookmarking-mode-hook)
           (when (interactive-p) (message "Bookmarking is now TEMPORARY")))
          (t                            ; User refused to confirm.
           (message "OK, canceled - bookmarking is NOT temporary")
           (setq bmkp-temporary-bookmarking-mode  nil))))


  (add-to-list 'minor-mode-alist `(bmkp-temporary-bookmarking-mode
                                   ,bmkp-temporary-bookmarking-mode-lighter)))

;;;###autoload (autoload 'bmkp-toggle-autotemp-on-set "bookmark+")
(defun bmkp-toggle-autotemp-on-set (&optional msg-p) ; Bound to `C-x p x'
  "Toggle automatically making any bookmark temporary whenever it is set.
Non-interactively, non-nil MSG-P means display a status message."
  (interactive "p")
  (setq bmkp-autotemp-all-when-set-p  (not bmkp-autotemp-all-when-set-p))
  (when msg-p (message "Automatically making bookmarks temporary when set is now %s"
                       (if bmkp-autotemp-all-when-set-p "ON" "OFF"))))

;;;###autoload (autoload 'bmkp-toggle-temporary-bookmark "bookmark+")
(defun bmkp-toggle-temporary-bookmark (bookmark &optional msg-p)
  "Toggle whether BOOKMARK is temporary (not saved to disk).
Return the full updated bookmark.
BOOKMARK is a bookmark name or a bookmark record.
Non-interactively, non-nil MSG-P means display a status message."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) 'MSG))
  (let ((was-temp  (bmkp-temporary-bookmark-p bookmark)))
    (bookmark-prop-set bookmark 'bmkp-temp (not was-temp))
    (when msg-p (message "Bookmark `%s' is now %s"
                         (if (stringp bookmark) bookmark (bmkp-bookmark-name-from-record bookmark))
                         (if was-temp "SAVABLE" "TEMPORARY"))))
  bookmark)

;;;###autoload (autoload 'bmkp-make-bookmark-temporary "bookmark+")
(defun bmkp-make-bookmark-temporary (bookmark &optional msg-p)
  "Make BOOKMARK temporary (not saved to disk).
Return the full updated bookmark.
BOOKMARK is a bookmark name or a bookmark record.
Non-interactively, non-nil MSG-P means display a status message."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) 'MSG))
  (bookmark-prop-set bookmark 'bmkp-temp t)
  (when msg-p (message "Bookmark `%s' is now TEMPORARY"
                       (if (stringp bookmark) bookmark (bmkp-bookmark-name-from-record bookmark))))
  bookmark)

;;;###autoload (autoload 'bmkp-make-bookmark-savable "bookmark+")
(defun bmkp-make-bookmark-savable (bookmark &optional msg-p)
  "Make BOOKMARK savable to disk (not temporary).
Return the full updated bookmark.
BOOKMARK is a bookmark name or a bookmark record.
Non-interactively, non-nil MSG-P means display a status message."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) 'MSG))
  (bookmark-prop-set bookmark 'bmkp-temp nil)
  (when msg-p (message "Bookmark `%s' is now SAVABLE"
                       (if (stringp bookmark) bookmark (bmkp-bookmark-name-from-record bookmark))))
  bookmark)

;;;###autoload (autoload 'bmkp-delete-all-temporary-bookmarks "bookmark+")
(defun bmkp-delete-all-temporary-bookmarks (&optional msg-p)
  "Delete all temporary bookmarks, after confirmation.
These are bookmarks that are `bmkp-temporary-bookmark-p'.  You can
make a bookmark temporary using `bmkp-make-bookmark-temporary' or
`bmkp-toggle-temporary-bookmark'.
Non-interactively, non-nil MSG-P means display a status message."
  (interactive "p")
  (let ((bmks-to-delete  (mapcar #'bmkp-bookmark-name-from-record (bmkp-temporary-alist-only))))
    (if (null bmks-to-delete)
        (when msg-p (message "No temporary bookmarks to delete"))
      (when (and msg-p  (not (y-or-n-p (format "Delete ALL temporary bookmarks? "))))
        (error "OK - delete canceled"))
      (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                      bookmark-save-flag))) ; Save at most once, after `dolist'.
        (dolist (bmk  bmks-to-delete)  (bookmark-delete bmk 'BATCHP))) ; No refresh yet.
      (bmkp-refresh/rebuild-menu-list nil (not msg-p)) ; Now refresh, after iterate.
      (when msg-p (message "Deleted all temporary bookmarks")))))

;; You can use this in `kill-emacs-hook'.
(defun bmkp-delete-temporary-no-confirm ()
  "Delete all temporary bookmarks, without confirmation."
  (when (and bookmarks-already-loaded  bookmark-alist)
    (let ((bmks-to-delete  (mapcar #'bmkp-bookmark-name-from-record (bmkp-temporary-alist-only)))
          (bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                    bookmark-save-flag))) ; Save at most once, after `dolist'.
      (dolist (bmk  bmks-to-delete)  (bookmark-delete bmk 'BATCHP))) ; No refresh yet.
    (bmkp-refresh/rebuild-menu-list nil 'BATCHP))) ; Now refresh, after iterate.

;;;###autoload (autoload 'bmkp-delete-bookmarks "bookmark+")
(defun bmkp-delete-bookmarks (&optional position allp alist msg-p) ; Bound to `C-x p delete'
  "Delete some bookmarks at point or all bookmarks in the buffer.
With no prefix argument, delete some bookmarks at point.
If there is more than one, require confirmation for each.

With a prefix argument, delete *ALL* bookmarks in the current buffer.

Non-interactively:
* Delete at POSITION, not point.  If nil, delete at point.
* Non-nil optional arg ALLP means delete all bookmarks in the buffer.
* ALIST is the alist of bookmarks.
  If nil, use the bookmarks in the current buffer.
* Non-nil MSG-P means display informative messages."
  (interactive "d\nP\ni\np")
  (unless position (setq position  (point)))
  (let ((bmks-to-delete  (and allp  (mapcar #'bmkp-bookmark-name-from-record (bmkp-this-buffer-alist-only))))
        (bmks-deleted    ())
        bmk-pos)
    (when (and msg-p  bmks-to-delete  (not (y-or-n-p (format "Delete ALL bookmarks in buffer `%s'? "
                                                             (buffer-name)))))
      (error "Canceled - no bookmarks deleted"))
    (cond (bmks-to-delete               ; Delete all.
           (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                           bookmark-save-flag))) ; Save at most once, after `dolist'.
             (dolist (bname  bmks-to-delete) (bookmark-delete bname 'BATCHP))) ; No refresh yet.
           (bmkp-refresh/rebuild-menu-list nil (not msg-p)) ; Refresh now, after iterate.
           (when msg-p (message "Deleted all bookmarks in buffer `%s'" (buffer-name))))

          (allp                         ; Requested ALLP, but there are none.  (No-op if not interactive.)
           (when msg-p (message "No bookmarks to delete in buffer `%s'" (buffer-name))))

          (t                            ; Delete selected bookmarks at point.
           (let (bname)
             (dolist (bmk  (or alist  (bmkp-this-buffer-alist-only)))
               (when (eq position (setq bmk-pos  (bookmark-get-position bmk)))
                 (setq bname  (bmkp-bookmark-name-from-record bmk))
                 ;; This is the same as `add-to-list' with `EQ' (not available for Emacs 20-21).
                 (unless (memq bname bmks-to-delete)
                   (setq bmks-to-delete  (cons bname bmks-to-delete)))))
             (cond ((cadr bmks-to-delete) ; More than one at point.
                    (let ((bookmark-save-flag  (and (not bmkp-count-multi-mods-as-one-flag)
                                                    bookmark-save-flag))) ; Save at most once, after `dolist'.
                      (dolist (bname  bmks-to-delete)
                        (when (or (not msg-p)  (y-or-n-p (format "Delete bookmark `%s'? " bname)))
                          (bookmark-delete bname 'BATCHP) ; No refresh yet.
                          ;; This is the same as `add-to-list' with `EQ' (not available for Emacs 20-21).
                          (unless (memq bname bmks-deleted) (setq bmks-deleted  (cons bname bmks-deleted))))))
                    (bmkp-refresh/rebuild-menu-list nil (not msg-p)) ; Refresh now.
                    (when msg-p
                      (message (if bmks-deleted
                                   (format "Deleted bookmarks: %s"
                                           (mapconcat (lambda (bname) (format "`%s'" bname)) bmks-deleted
                                                      ", "))
                                 "No bookmarks deleted"))))
                   (bmks-to-delete      ; Only one bookmark at point.
                    (bookmark-delete (car bmks-to-delete))
                    (when msg-p (message "Deleted bookmark `%s'" (car bmks-to-delete))))
                   (t
                    (when msg-p (message "No bookmarks at point to delete")))))))))

;; Because of Emacs bug #19915, we need to use `advice-add' for `org-store-link', so this feature
;; is available only for Emacs 24.4+.
(when (fboundp 'advice-add)
             
  (defvar bmkp-store-org-link-checking-p nil
    "Whether `bmkp-(bmenu-)store-org-link(-1)' call is checking applicability.")

  (defun bmkp-store-org-link (arg)
    "Store a link to a bookmark for insertion in an Org-mode buffer.
You are prompted for the bookmark name.

If you use a numeric prefix arg then the bookmark will be jumped to in
the same window.  Without a numeric prefix arg, the link will use
another window.  The link type is `bookmark' or `bookmark-other-win',
respectively."
    (interactive "P")
    (require 'org)
    (let ((org-store-link-functions  (append org-store-link-functions '(bmkp-store-org-link-1))))
      (call-interactively #'org-store-link)))

  (defun bmkp-store-org-link-1 ()
    "Store a link to a bookmark for insertion in an Org-mode buffer.
See command `bmkp-store-org-link'."
    (setq bmkp-store-org-link-checking-p  (not bmkp-store-org-link-checking-p))
    (require 'org)
    (or bmkp-store-org-link-checking-p  ; Non-nil return is all that is needed for checking.
        (let* ((other-win  (and current-prefix-arg  (not (consp current-prefix-arg))))
               (bmk        (bmkp-completing-read-lax
                            (format "Store %sOrg link for bookmark" (if other-win "other-window " ""))))
               (link       (format "bookmark%s:%s" (if other-win "-other-win" "") bmk))
               (bmk-desc   (format "Bookmark: %s" bmk)))
          (org-store-link-props :type "bookmark" :link link :description bmk-desc))))

  (advice-add 'org-store-link :before #'bmkp-reset-bmkp-store-org-link-checking-p)
  (defun bmkp-reset-bmkp-store-org-link-checking-p (&rest _IGNORE)
    "Reset `bmkp-store-org-link-checking-p' to nil."
    (setq bmkp-store-org-link-checking-p  nil)))

(defun bmkp-ffap-guesser ()
  "`ffap-guesser', but deactivate a large active region first."
  (and (require 'ffap nil t)
       ;; Prevent using a large active region to guess ffap: Emacs bug #25243.
       (let ((mark-active  (and mark-active  (< (buffer-size) bmkp-ffap-max-region-size))))
         (ffap-guesser))))

;; Same as `icicle-thing-at-point'.
(defun bmkp-thing-at-point (thing &optional syntax-table)
  "`thingatpt+.el' version of `thing-at-point', if possible.
`tap-thing-at-point' if defined, else `thing-at-point'.
if non-nil, set SYNTAX-TABLE for the duration."
  (if (fboundp 'tap-thing-at-point)
      (tap-thing-at-point thing syntax-table)
    (if (and (syntax-table-p syntax-table)  (fboundp 'with-syntax-table)) ; Emacs 21+.
        (with-syntax-table syntax-table (thing-at-point thing))
      (thing-at-point thing))))         ; Ignore any SYNTAX-TABLE arg for Emacs 20, for vanilla.

(defun bmkp-get-external-annotation (annotation)
  "Return a cons (DESTINATION . TYPE) for ANNOTATION.
DESTINATION is a string naming a file, a URL, or a bookmark.
TYPE is `FILE', `URL', or `BOOKMARK', accordingly."
  (cond ((string-match "\\`\\s-*bmkp-annot-file:\\s-*\"\\(\.+\\)\"" annotation)
         (cons (match-string 1 annotation) 'FILE))
        ((string-match "\\`\\s-*bmkp-annot-url:\\s-*\"\\(\.+\\)\"" annotation)
         (cons (match-string 1 annotation) 'URL))
        ((string-match "\\`\\s-*bmkp-annot-bmk:\\s-*\"\\(\.+\\)\"" annotation)
         (cons (match-string 1 annotation) 'BOOKMARK))
        (t nil)))

(defun bmkp-visit-external-annotation (annotation.type msg-p)
  "Visit the external annotation represented by ANNOTATION.TYPE.
The first arg is a cons as returned by `bmkp-get-external-annotation'.
I MSG-P is non-nil then echo the annotation type."
  (let ((ann   (car annotation.type))
        (type  (cdr annotation.type)))
    (case type
      (FILE       (find-file-other-window     ann))
      (URL        (browse-url                 ann))
      (BOOKMARK   (bookmark-jump-other-window ann))
      (otherwise  (error "`bmkp-visit-external-annotation': Bad annotation type: `%S'" type)))
    (message "Showing external annotation of type %s" type) (sit-for 1)))

;;;;;;;;;;;;;;;;;;;;;;;

(provide 'bookmark+-1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-1.el ends here
