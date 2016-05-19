;;; evil-matchit-org.el --- org-mode plugin of evil-matchit

;; Copyright (C) 2014  Chen Bin <chenbin.sh@gmail.com>

;; Author: Chen Bin <chenbin.sh@gmail.com>

;; This file is not part of GNU Emacs.

;;; License:

;; This file is part of evil-matchit
;;
;; evil-matchit is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; evil-matchit is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.


;;; Code:

;; OPTIONAL, you don't need SDK to write a plugin for evil-matchit
;; but SDK don make you write less code, isn't it?
;; All you need to do is just define the match-tags for SDK algorithm to lookup.
(require 'evil-matchit-sdk)

(defvar evilmi-org-extract-keyword-howtos
  '(("^[ \t]*#\\+\\([a-zA-Z_]+\\).*$" 1)
    )
  "The list of HOWTO on extracting keyword from current line.
Each howto is actually a pair. The first element of pair is the regular
expression to match the current line. The second is the index of sub-matches
to extract the keyword which starts from one. The sub-match is the match defined
between '\\(' and '\\)' in regular expression.
"
  )
;; ruby/bash/lua/vimrc
(defvar evilmi-org-match-tags
  '((("begin_src") () ( "end_src") "MONOGAMY")
    (("begin_example") () ( "end_example") "MONOGAMY")
    (("begin_html") () ( "end_html") "MONOGAMY")
    ))

(defun evilmi--element-property (property element)
  "Extract the value from the PROPERTY of an ELEMENT."
  (unless (stringp element)
    ;; we don't use org-element-property because it's
    ;; available only in 24.4+
    (plist-get (nth 1 element) property)))

(defun evilmi--get-embedded-language-major-mode ()
  ;; org-element-at-point is available only at org7+
  (let ((lang (evilmi--element-property :language (org-element-at-point))))
    (when lang
      (intern (concat lang "-mode")))))

;;;###autoload
(defun evilmi-org-get-tag ()
  (let (rlt)
    (setq rlt (evilmi-sdk-get-tag evilmi-org-match-tags evilmi-org-extract-keyword-howtos))
    (if (not rlt)
        (setq rlt '(-1)) ;; evilmi-org-jump knows what -1 means
      )
    rlt
    ))

;;;###autoload
(defun evilmi-org-jump (rlt NUM)
  (if (< (car rlt) 0)
      (let (where-to-jump-in-theory
            jumped
            plugin
            info
            (lang-f (evilmi--get-embedded-language-major-mode)))
        (when lang-f
          (setq plugin (plist-get evilmi-plugins lang-f))
          (when plugin
              (mapc
               (lambda (elem)
                 (setq info (funcall (nth 0 elem)))
                 (when (and info (not jumped))
                   ;; before jump, we may need some operation
                   (setq where-to-jump-in-theory (funcall (nth 1 elem) info NUM))
                   ;; jump only once if the jump is successful
                   (setq jumped t)
                   ))
               plugin
               ))
          )
        )
      (evilmi-sdk-jump rlt NUM evilmi-org-match-tags evilmi-org-extract-keyword-howtos)
      ))

(provide 'evil-matchit-org)
