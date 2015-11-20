;;; haskell-yas.el --- Customization support for Luke Hoersten's yasnippets

;; Copyright (C) 2013  John Wiegley, Luke Hoersten

;; Author: John Wiegley <johnw@newartisans.com>
;;         Luke Hoersten <Luke@Hoersten.org>
;; Keywords: faces files Haskell

;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Provides customization variables for Luke Hoersten's yasnippet collection
;; to depend on.

;;; Code:

(eval-when-compile
  (require 'yasnippet nil t))

(defgroup haskell-yas nil
  "Customizations for Luke Hoersten's yasnippet collection for haskell-mode."
  :group 'haskell
  :prefix "haskell-yas-")

(defcustom haskell-yas-ghc-language-pragmas
  (split-string (shell-command-to-string "ghc --supported-extensions"))
  "List of language pragmas supported by the installed version of GHC."
  :group 'haskell-yas
  :type '(repeat string))

(defcustom haskell-yas-completing-function 'ido-completing-read
  "Function to use for completing among alternatives."
  :group 'haskell-yas
  :type 'function)

;;;###autoload
(defun haskell-yas-complete (&rest args)
  (apply haskell-yas-completing-function args))

(defconst haskell-snippets-dir
  (expand-file-name "snippets" (file-name-directory load-file-name)))

(defvar yas-snippet-dirs)
(declare-function yas-load-directory "ext:yasnippet"
                  (top-level-dir &optional use-jit interactive))

;;;###autoload
(defun haskell-snippets-initialize ()
  "Register haskell snippets with yasnippet."
  (add-to-list 'yas-snippet-dirs haskell-snippets-dir t)
  (yas-load-directory haskell-snippets-dir))

;;;###autoload
(eval-after-load 'yasnippet
  '(haskell-snippets-initialize))


;; Provide ourselves:

(provide 'haskell-yas)

;;; haskell-yas.el ends here
