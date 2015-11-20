;;; bookmark-w3m.el --- bridging between emacs's bookmark.el and emacs-w3m

;; Copyright (C) 2010 Masatake YAMATO
;;
;; Author: Masatake YAMATO <yamato@redhat.com>
;;

;;; Commentary:
;; From version 23.1 bookmark.el of GNU emacs supports the mode own
;; bookmark mechanism.  This is w3m.el side adapter to the mechanism.
;; This version of bookmark-w3m.el should work on Emacs 23 and greater.
;;
;; To enable the bookmark to work even when emacs-w3m is not loaded,
;; add the following snippet to the ~/.emacs file:
;;
;; (require 'w3m-load)

;;; About copyright:
;; Most of all codes are derived from man.el of GNU Emacs.
;; So the same license of man.el is applied to this software.
;; =========================================================================
;;; man.el --- browse UNIX manual pages -*- coding: iso-8859-1 -*-

;; Copyright (C) 1993, 1994, 1996, 1997, 2001, 2002, 2003, 2004, 2005,
;;   2006, 2007, 2008, 2009, 2010  Free Software Foundation, Inc.

;; Author: Barry A. Warsaw <bwarsaw@cen.com>
;; Maintainer: FSF
;; Keywords: help
;; Adapted-By: ESR, pot

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

(defvar bookmark-make-record-function)
(defvar w3m-current-title)
(defvar w3m-current-url)

(declare-function bookmark-default-handler "bookmark" (bmk-record))
(declare-function bookmark-get-bookmark-record "bookmark" (bookmark))
(declare-function bookmark-make-record-default
		  "bookmark" (&optional no-file no-context posn))
(declare-function bookmark-prop-get "bookmark" (bookmark prop))
(declare-function w3m-goto-url
		  "w3m" (url &optional reload charset post-data referer handler
			     element no-popup))

(defun bookmark-w3m-bookmark-make-record ()
  "Make a emacs bookmark entry for a w3m buffer."
  `(,w3m-current-title
    ,@(bookmark-make-record-default 'no-file)
    ;; if bookmark-bmenu-toggle-filenames is t and a bookmark record doesn't
    ;; have filename field, , Emacs23.2 raises an error.
    ;; Here is the workaround suggested by ARISAWA Akihiro.
    (filename . ,w3m-current-url)
    (url . ,w3m-current-url)
    (handler . bookmark-w3m-bookmark-jump)))

;;;###autoload
(defun bookmark-w3m-bookmark-jump (bookmark)
  "Default bookmark handler for w3m buffers."
  (let ((w3m-async-exec nil))
    (w3m-goto-url (bookmark-prop-get bookmark 'url))
    (let ((buf (current-buffer)))
      (bookmark-default-handler
       `("" (buffer . ,buf) . ,(bookmark-get-bookmark-record bookmark))))))


(defun bookmark-w3m-prepare ()
  (interactive)
  (set (make-local-variable 'bookmark-make-record-function)
       'bookmark-w3m-bookmark-make-record))
(add-hook 'w3m-mode-hook 'bookmark-w3m-prepare)

(provide 'bookmark-w3m)

;; bookmark-w3m.el ends here
