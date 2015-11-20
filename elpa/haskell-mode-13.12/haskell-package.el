;;; haskell-package.el --- Interface for working with Cabal packages

;; Copyright (C) 2011  Chris Done

;; Author: Chris Done <chrisdone@gmail.com>

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
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; Todo:

;;; Code:

(require 'cl-lib)

;; Dynamically scoped variables.
;; TODO What actually sets this?
(defvar haskell-config-use-cabal-dev)

;; (defun haskell-package-conf-path-get (&optional project)
;;   "Gets the user conf or the cabal-dev conf. Get the global conf elsewhere."
;;   (if haskell-config-use-cabal-dev
;;       (if project
;;           (let* ((cabal-path (haskell-project-cabal-dir project)))
;;             (format "%scabal-dev/packages-%s.conf/"
;;                     (if (string-match "/$" cabal-path)
;;                         cabal-path
;;                       (concat cabal-path "/"))
;;                     (haskell-ghc-version)))
;;         (haskell-package-conf-user-path-get))
;;     (haskell-package-conf-user-path-get)))

(defun haskell-package-conf-user-path-get ()
  "Get the user conf path."
  (let ((out (shell-command-to-string "ghc-pkg --user list no-results-please")))
    (string-match "\n\\(.*\\):\n" out) (match-string 1 out)))

(defun haskell-package-conf-global-path-get ()
  "Get the global conf path."
  (let ((out (shell-command-to-string "ghc-pkg --global list no-results-please")))
    (string-match "\n\\(.*\\):\n" out) (match-string 1 out)))

(defun haskell-package-get-all (conf)
  "Get all package descriptions for the given `conf'."
  (let ((all (shell-command-to-string (format "ghc-pkg -f %s dump" conf))))
    (mapcar (lambda (text)
              (haskell-package-parse text))
            (split-string all "\n---\n"))))

(defun haskell-package-get (conf name version)
  "Get a package description for the given `name' and `version' in the given `conf'."
  (haskell-package-parse
   (shell-command-to-string
    (format "ghc-pkg -f %s describe %s-%s"
            conf
            name
            version))))

(cl-defstruct haskell-package "Haskell package object.")

(defun haskell-package-parse (text)
  "Parse a package into a package object."
  (let ((pkg (haskell-package-read-description text)))
    (make-haskell-package
     :name (cdr (assoc "name" pkg))
     :version (cdr (assoc "version" pkg))
     :id (cdr (assoc "id" pkg))
     :license (cdr (assoc "license" pkg))
     :copyright (cdr (assoc "copyright" pkg))
     :maintainer (cdr (assoc "maintainer" pkg))
     :stability (cdr (assoc "stability" pkg))
     :homepage (cdr (assoc "homepage" pkg))
     :package-url (cdr (assoc "package-url" pkg))
     :description (cdr (assoc "description" pkg))
     :categories (cdr (assoc "category" pkg))
     :authors (cdr (assoc "author" pkg))
     :is-exposed (equal "True" (cdr (assoc "exposed" pkg)))
     :exposed-modules (split-string (or (cdr (assoc "exposed-modules" pkg)) "")
                                    "[\n ]")
     :hidden-modules (split-string (or (cdr (assoc "hidden-modules" pkg)) "")
                                   "[\n ]")
     :imports-dirs (cdr (assoc "imports-dirs" pkg))
     :library-dirs (cdr (assoc "library-dirs" pkg))
     :haskell-libraries (cdr (assoc "haskell-libraries" pkg))
     :extra-libraries (cdr (assoc "extra-libraries" pkg))
     :extra-ghci-libraries (cdr (assoc "extra-ghci-libraries" pkg))
     :include-dirs (cdr (assoc "include-dirs" pkg))
     :includes (cdr (assoc "includes" pkg))
     :depends (cdr (assoc "depends" pkg))
     :hugs-options (cdr (assoc "hugs-options" pkg))
     :cc-options (cdr (assoc "cc-options" pkg))
     :ld-options (cdr (assoc "ld-options" pkg))
     :framework-dirs (cdr (assoc "framework-dirs" pkg))
     :frameworks (cdr (assoc "frameworks" pkg))
     :haddock-interfaces (cdr (assoc "haddock-interfaces" pkg))
     :haddock-html (cdr (assoc "haddock-html" pkg)))))

(defun haskell-package-read-description (text)
  "Return an association list of key-values from a pkg description string."
  (let* ((marked (replace-regexp-in-string
                  "\n\\([^ ]\\)"
                  (lambda (match)
                    (concat "\n:" (substring match 1)))
                  text))
         (alist (mapcar 'haskell-package-key-value
                        (split-string marked "\n:"))))
    alist))

(defun haskell-package-key-value (entry)
  "Return a (key . value) pair from an entry."
  (let ((key-values (split-string entry ": ")))
    (if (listp key-values)
        (cons (car key-values)
              (replace-regexp-in-string
               "\n[ ]*"
               " "
               (mapconcat 'identity (cdr key-values) ": ")))
      key-values)))

(defun haskell-package-list-get (conf)
  "Get the list of packages in the given config."
  (haskell-package-list-parse
   (shell-command-to-string
    (format "ghc-pkg -f %s list"
            conf))))

(defun haskell-package-list-parse (text)
  "Parse the list of installed packges."
  (let* ((lines (split-string text "\n    ")))
    (mapcar
     (lambda (line)
       (string-match "^{?\\([a-zA-Z0-9-_]+\\)-\\([0-9.]+\\)}?$" line)
       (cons (match-string 1 line) (match-string 2 line)))
     (cl-delete-if
      (lambda (line)
        (not (string-match "^{?[a-zA-Z0-9-_]+-[0-9.]+}?$" line)))
      lines))))

(provide 'haskell-package)

;;; haskell-package.el ends here
