;;; fic-mode.el --- Show FIXME/TODO/BUG(...) in special face only in comments and strings
;;--------------------------------------------------------------------
;;
;; Copyright (C) 2010, Trey Jackson <bigfaceworm(at)gmail(dot)com>
;; Copyright (C) 2010, Ivan Korotkov <twee(at)tweedle-dee(dot)org>
;; Copyright (C) 2012, Le Wang
;;
;; Homepage: https://github.com/lewang/fic-mode
;;
;; This file is NOT part of Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free
;; Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA
;;
;; To use, save fic-mode.el to a directory in your load-path.
;;
;;   (require 'fic-mode)
;;
;;   ;;; emacs 24
;;   (add-hook 'prog-mode-hook 'fic-mode)
;;
;;   ;;; emacs 23 needs to add this to all programming modes you want this to be
;;   ;;; enabled for.
;;   ;;;
;;   ;;; e.g.
;;   (add-hook 'c++-mode-hook 'fic-mode)
;;   (add-hook 'emacs-lisp-mode-hook 'fic-mode)
;;
;; or
;;
;; M-x fic-mode

(defgroup fic-mode nil
  "Highlight FIXME/TODO(...) in comments"
  :tag "FIC"
  :group 'tools
  :group 'font-lock
  :group 'faces)

(defcustom fic-highlighted-words '("FIXME" "TODO" "BUG")
  "Words to highlight."
  :group 'fic-mode)

(defcustom fic-author-name-regexp "[-a-zA-Z0-9_.]+"
  "Regexp describing FIXME/TODO author name"
  :group 'fic-mode)

(defcustom fic-activated-faces
  '(font-lock-doc-face font-lock-string-face font-lock-comment-face)
  "Faces to look for to highlight words."
  :group 'fic-mode)

(defface fic-face
  '((((class color))
     (:background "white" :foreground "red" :weight bold))
    (t (:weight bold)))
  "Face to fontify FIXME/TODO words"
  :group 'fic-mode)

(defface fic-author-face
  '((((class color))
     (:background "white" :foreground "orangered" :underline t))
    (t (:underline t)))
  "Face to fontify author/assignee of FIXME/TODO"
  :group 'fic-mode)

(defvar fic-mode-font-lock-keywords '((fic-search-for-keyword
                                       (1 'fic-face t)
                                       (2 'fic-author-face t t))) 
  "Font Lock keywords for fic-mode")

(defvar fic-saved-hash nil
  "(`fic-highlighted-words' . `fic-author-name-regexp')")
(defvar fic-saved-regexp nil
  "Regexp cache for `fic-saved-hash'")

(defun fic-search-re ()
  "Regexp to search for."
  (let ((hash (cons fic-highlighted-words fic-author-name-regexp)))
    (if (and fic-saved-hash
           (equal fic-saved-hash hash))
        fic-saved-regexp
      (let ((fic-words-re (concat "\\<"
                                  (regexp-opt fic-highlighted-words t)
                                  "\\>")))
        (setq fic-saved-hash hash
              fic-saved-regexp (concat fic-words-re "\\(?:(\\(" fic-author-name-regexp "\\))\\)?"))
        fic-saved-regexp))))

(defun fic-in-doc/comment-region (pos)
  (memq (get-char-property pos 'face)
        fic-activated-faces))

(defun fic-search-for-keyword (limit)
  (let ((match-data-to-set nil)
	found)
    (save-match-data
      (while (and (null match-data-to-set)
		  (re-search-forward (fic-search-re) limit t))
	(if (and (fic-in-doc/comment-region (match-beginning 0))
		 (fic-in-doc/comment-region (match-end 0)))
	    (setq match-data-to-set (match-data)))))
    (when match-data-to-set
      (set-match-data match-data-to-set)
      (goto-char (match-end 0))
      t)))

;;;###autoload
(define-minor-mode fic-mode
  "Fic mode -- minor mode for highlighting FIXME/TODO in comments"
  :lighter ""
  :group 'fic-mode
  (let ((kwlist fic-mode-font-lock-keywords))
    (if fic-mode
	(font-lock-add-keywords nil kwlist 'append)
      (font-lock-remove-keywords nil kwlist))
    (font-lock-fontify-buffer)))

(provide 'fic-mode)
