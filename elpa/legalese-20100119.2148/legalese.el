;;; legalese.el --- Add legalese to your program files

;; Copyright (C) 2004  Jorgen Schaefer <forcer@forcix.cx>

;; Author: Jorgen Schaefer <forcer@forcix.cx>
;; Keywords: convenience
;; Package-Version: 20100119.2148

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This file adds the sometimes necessary legalese to your files. That
;; is, it adds a license header. For most files, it tries to adhere to
;; a nice standard layout.

;; I recommend the following setup:

;; (setq comment-style 'extra-line)
;; (add-hook 'scheme-mode-hook
;;           (lambda ()
;;             (set (make-local-variable 'comment-add) 1)))

;;; Code:

(defvar legalese-version "1.0"
  "Version string of legalese.el")

(defgroup legalese nil
  "*Add legalese to your files."
  :prefix "legalese-"
  :group 'programming)

(defcustom legalese-default-copyright nil
  "*The string to use by default for the copyright holder. If this is
nil, the current users' mail address is used."
  :group 'legalese
  :type '(choice string
                 (const :tag "Default address" nil)))

(defcustom legalese-default-author nil
  "*The string to use by default for the author. If this is nil, the
current users' mail address is used."
  :group 'legalese
  :type '(choice string
                 (const :tag "Default address" nil)))

(defcustom legalese-default-license 'gpl
  "*The default license to use."
  :group 'legalese
  :type '(choice (const :tag "General Public License" gpl)
                 (const :tag "Lesser General Public License" lgpl)
                 (const :tag "Free Documentation License" fdl)))

(defcustom legalese-templates
  '((emacs-lisp-mode (nil ";;; " legalese-file-name " --- " _ "\n"
                          "\n"
                          ";; Copyright (C) " legalese-year "  " legalese-copyright "\n"
                          "\n"
                          ";; Author: " legalese-author "\n"
                          ;; This looks weird. Taken from autoinsert.
                          ;; *shrug* :-)
                          ";; Keywords: " ((legalese-elisp-keyword)
                                           str ", ") & -2 "\n"
                          "\n"
                          @
                          '(legalese-license)
                          @
                          "\n"
                          ";;; Commentary:\n"
                          "\n"
                          ";;; Code:\n"
                          "\n"
                          "\n"
                          "(provide '" legalese-file ")\n"
                          ";;; " legalese-file-name " ends here\n"))
    (scheme-mode (nil ";;; " legalese-file-name " --- " _ "\n"
                      "\n"
                      ";; Copyright (C) " legalese-year " " legalese-copyright "\n"
                      "\n"
                      ";; Author: " legalese-author "\n"
                      "\n"
                      @
                      '(legalese-license)
                      @
                      "\n"
                      ";;; Commentary:\n"
                      "\n"
                      ";;; Code:\n"
                      "\n"))
    (default (nil @
                  legalese-file-name " --- " _ "\n"
                  "\n"
                  "Copyright (C) " legalese-year " " legalese-copyright "\n"
                  "\n"
                  "Author: " legalese-author "\n"
                  "\n"
                  '(legalese-license)
                  @)))
  "*A list that associates a major mode with the appropriate skeleton
to use for this mode. The region between the last two @ marks will be
commented out using comment-region."
  :group 'legalese
  :type '(alist :key-type symbol
                :value-type (repeat sexp)))

(defcustom legalese-licenses
  '((gpl "This program is free software; you can redistribute it and/or"
         "modify it under the terms of the GNU General Public License"
         "as published by the Free Software Foundation; either version 3"
         "of the License, or (at your option) any later version."
         ""
         "This program is distributed in the hope that it will be useful,"
         "but WITHOUT ANY WARRANTY; without even the implied warranty of"
         "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the"
         "GNU General Public License for more details."
         ""
         "You should have received a copy of the GNU General Public License"
         "along with this program. If not, see <http://www.gnu.org/licenses/>.")
    (lgpl "This library is free software; you can redistribute it and/or"
          "modify it under the terms of the GNU Lesser General Public"
          "License as published by the Free Software Foundation; either"
          "version 3 of the License, or (at your option) any later version."
          ""
          "This library is distributed in the hope that it will be useful,"
          "but WITHOUT ANY WARRANTY; without even the implied warranty of"
          "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU"
          "Lesser General Public License for more details."
          ""
          "You should have received a copy of the GNU Lesser General Public"
          "License along with this library. If not, see"
	  "<http://www.gnu.org/licenses/>.")
    (fdl "Permission is granted to copy, distribute and/or modify this document"
         "under the terms of the GNU Free Documentation License, Version 1.1"
         "or any later version published by the Free Software Foundation;"
         "with the Invariant Sections being LIST THEIR TITLES, with the"
         "Front-Cover Texts being LIST, and with the Back-Cover Texts being LIST."
         "A copy of the license is included in the section entitled \"GNU"
         "Free Documentation License\".")
    (bsd "This program is free software, you can redistribute it and/or"
         "modify it under the terms of the new-style BSD license."
         ""
         "You should have received a copy of the BSD license along with this"
         "program. If not, see <http://www.debian.org/misc/bsd.license>.")
    (wtfpl "This program is free software. It comes without any warranty, to"
           "the extent permitted by applicable law. You can redistribute it"
           "and/or modify it under the terms of the WTFPL, version 2, as "
           "published by Sam Hocevar. See http://sam.zoy.org/wtfpl/COPYING"
           "for more details.")
    (mit
     "Permission is hereby granted, free of charge, to any person obtaining a"
     "copy of this software and associated documentation files (the \"Software\"),"
     "to deal in the Software without restriction, including without limitation"
     "the rights to use, copy, modify, merge, publish, distribute, sublicense,"
     "and/or sell copies of the Software, and to permit persons to whom the"
     "Software is furnished to do so, subject to the following conditions:"
     ""
     "The above copyright notice and this permission notice shall be included in"
     "all copies or substantial portions of the Software."
     ""
     "Except as contained in this notice, the name(s) of the above copyright"
     "holders shall not be used in advertising or otherwise to promote the sale,"
     "use or other dealings in this Software without prior written authorization."
     ""
     "THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR"
     "IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,"
     "FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL"
     "THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER"
     "LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING"
     "FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER"
     "DEALINGS IN THE SOFTWARE."))
  "*A definition of copyright boilerplates."
  :group 'legalese
  :type '(alist :key-type symbol
                :value-type (repeat string)))

(defun legalese (ask)
  "Add standard legalese prelude to the current buffer. With
prefix-argument ASK, ask for a license to use."
  (interactive "P")
  (let ((legalese-year (format-time-string "%Y"))
        (legalese-copyright (or legalese-default-copyright 
                                (concat user-full-name
                                        " <" user-mail-address ">")))
        (legalese-author (or legalese-default-author
                             (concat user-full-name
                                     " <" user-mail-address ">")))
        (legalese-file-name (file-name-nondirectory (buffer-file-name)))
        (legalese-file (file-name-nondirectory
                        (file-name-sans-extension
                         (buffer-file-name))))
        (legalese-license (if (car ask)
                              (intern
                               (completing-read "License: "
                                                (mapcar
                                                 (lambda (item)
                                                   (list
                                                    (symbol-name
                                                     (car item))))
                                                 legalese-licenses)
                                                nil
                                                t))
                            legalese-default-license)))
    (skeleton-insert (cadr (or (assq major-mode legalese-templates)
                               (assq 'default legalese-templates))))
    (let ((beg (cadr skeleton-positions))
          (end (car skeleton-positions)))
      (comment-region beg end)
      (setq skeleton-positions (cddr skeleton-positions)))))

(defun legalese-license ()
  "Add the license of `legalese-default-license' here."
  (insert (mapconcat #'identity
                     (cdr (assq legalese-license
                                legalese-licenses))
                     "\n"))
  (insert "\n"))

(defun legalese-elisp-keyword ()
  "Add emacs lisp keywords."
  (require 'finder)
  (let ((keywords (mapcar (lambda (x) (list (symbol-name (car x))))
                          finder-known-keywords))
	(minibuffer-help-form (mapconcat (lambda (x) (format "%10.0s:  %s"
                                                             (car x)
                                                             (cdr x)))
                                         finder-known-keywords
                                         "\n")))
    (completing-read "Keyword, C-h: " keywords nil t)))


(provide 'legalese)
;;; legalese.el ends here
