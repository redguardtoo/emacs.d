;;; groovy-electric.el --- Electric mode for Groovy
;; -*-Emacs-Lisp-*-

;; Author:  Jim Morris <morris@wolfman.com>
;; Created: 2009-12-11

;; Copyright (C) 2009 Jim Morris

;;  This program is free software; you can redistribute it and/or modify it under the terms of the GNU
;;  General Public License as published by the Free Software Foundation; either version 2 of the License, or
;;  (at your option) any later version.
;;
;;  This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even
;;  the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
;;  License for more details.
;;
;;  You should have received a copy of the GNU General Public License along with this program; if not, write
;;  to the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
;;
;; Based on ruby-electric.el Copyright (C) 2005 by Dee Zsombor <dee dot zsombor at gmail dot com>.
;; Due credit: original work was inspired by a code snippet posted by
;; Frederick Ros at http://rubygarden.org/ruby?EmacsExtensions.

;;; Commentary:
;;
;; By default automatically inserts closing delimiter for {[('"
;; Additionally when in a GString typing a $ will insert { } and place
;; cursor between the braces.  All these can be turned on or off
;; individually in the customization window for groovy-electric
;;
;;
;; Usage:
;;
;;    0) copy groovy-electric.el into directory where emacs can find it.
;;
;;    1) modify your startup file (.emacs or whatever) by adding
;;       following lines to load and enable the mode when groovy-mode loads
;;
;;        (add-hook 'groovy-mode-hook
;;                         '(lambda ()
;;                                (require 'groovy-electric)
;;                                (groovy-electric-mode)))
;;
;; or add this to your init file
;;
;;            (require 'groovy-electric)
;;
;;       note that you need to have font lock enabled beforehand.
;;
;;    2) toggle Groovy Electric Mode on/off with groovy-electric-mode.

;;; History:

;;; Code:
(require 'groovy-mode)
(defgroup groovy-electric nil
  "Minor mode providing electric editing commands for groovy files"
  :group 'groovy)

(defvar groovy-electric-matching-delimeter-alist
  '((?\[ . ?\])
    (?\( . ?\))
    (?\' . ?\')
    (?\" . ?\")))

(defcustom groovy-electric-expand-delimiters-list '(all)
  "*List of contexts where matching delimiter should be inserted.
The word 'all' will do all insertions."
  :type '(set :extra-offset 8
	      (const :tag "Everything" all )
	      (const :tag "Curly brace" ?\{ )
	      (const :tag "Square brace" ?\[ )
	      (const :tag "Round brace" ?\( )
	      (const :tag "Quote" ?\' )
	      (const :tag "Double quote" ?\" )
	      (const :tag "Dollar in GStrings" ?\$ ))
  :group 'groovy-electric)

(defcustom groovy-electric-newline-before-closing-bracket nil
  "*Controls whether a newline should be inserted before the
closing bracket or not."
  :type 'boolean :group 'groovy-electric)

;;;###autoload
(define-minor-mode groovy-electric-mode
  "Toggle Groovy Electric minor mode.
With no argument, this command toggles the mode.  Non-null prefix
argument turns on the mode.  Null prefix argument turns off the
mode.

When Groovy Electric mode is enabled, simple, double and back
quotes as well as braces are paired auto-magically. Expansion
does not occur inside comments and strings. Note that you must
have Font Lock enabled. ${ } is expanded when in a GString"
  ;; initial value.
  nil
  ;;indicator for the mode line.
  " Ge"
  ;;keymap
  groovy-mode-map
  (groovy-electric-setup-keymap))

(defun groovy-electric-setup-keymap()
  (define-key groovy-mode-map "{" 'groovy-electric-curlies)
  (define-key groovy-mode-map "(" 'groovy-electric-matching-char)
  (define-key groovy-mode-map "[" 'groovy-electric-matching-char)
  (define-key groovy-mode-map "\"" 'groovy-electric-matching-char)
  (define-key groovy-mode-map "\'" 'groovy-electric-matching-char)
  (define-key groovy-mode-map "\$" 'groovy-electric-pound)
  )

(defun groovy-electric-code-at-point-p()
  (and groovy-electric-mode
       (let* ((properties (text-properties-at (point))))
		 (and (null (memq 'font-lock-string-face properties))
			  (null (memq 'font-lock-comment-face properties))))))

(defun groovy-electric-string-at-point-p()
  (and groovy-electric-mode
       (consp (memq 'font-lock-string-face (text-properties-at (point))))))

;; This checks it is a GString ("...") not normal string '...'
(defun groovy-electric-gstring-at-point-p()
  (and groovy-electric-mode
       (consp (memq 'font-lock-string-face (text-properties-at (point))))
	   (save-excursion
		 (char-equal ?\" (char-after (car (c-literal-limits)))))))

(defun groovy-electric-is-last-command-event-expandable-punct-p()
  (or (memq 'all groovy-electric-expand-delimiters-list)
      (memq last-command-event groovy-electric-expand-delimiters-list)))

(defun groovy-electric-curlies(arg)
  (interactive "P")
  (self-insert-command (prefix-numeric-value arg))
  (when (and (groovy-electric-is-last-command-event-expandable-punct-p)
			 (groovy-electric-code-at-point-p))
	(insert " ")
	(save-excursion
	  (if groovy-electric-newline-before-closing-bracket
		  (newline))
	  (insert "}"))))

(defun groovy-electric-matching-char(arg)
  (interactive "P")
  (self-insert-command (prefix-numeric-value arg))
  (and (groovy-electric-is-last-command-event-expandable-punct-p)
       (groovy-electric-code-at-point-p)
       (save-excursion
		 (insert (cdr (assoc last-command-event
							 groovy-electric-matching-delimeter-alist))))))

(defun groovy-electric-pound(arg)
  (interactive "P")
  (self-insert-command (prefix-numeric-value arg))
  (when (and (groovy-electric-is-last-command-event-expandable-punct-p)
			 (groovy-electric-gstring-at-point-p)
			 (not (save-excursion ; make sure it is not escaped
					(backward-char 1)
					(char-equal ?\\ (preceding-char)))))
	(insert "{}")
	(backward-char 1)))


(provide 'groovy-electric)

;;; groovy-electric.el ends here
