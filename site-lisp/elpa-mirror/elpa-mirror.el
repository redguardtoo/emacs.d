;;; elpa-mirror.el --- Create local package repository

;; Copyright (C) 2014 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/elpa-mirror
;; Version: 2.1.0
;; Keywords: cloud mirror elpa
;;
;; This file is not part of GNU Emacs.

;;; License:

;; This file is part of elpa-mirror
;;
;; elpa-mirror is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; elpa-mirror is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Usage in Emacs,
;; `M-x elpamr-create-mirror-for-installed`
;;  If you use native Windows Emacs, install Cygwin or MSYS2.
;;
;; Usage in Shell,
;;   emacs --batch -l ~/.emacs.d/init.el
;;         -l ~/any-directory-you-prefer/elpa-mirror.el \
;;         --eval='(setq elpamr-default-output-directory "~/myelpa")' \
;;         --eval='(elpamr-create-mirror-for-installed)
;;
;; Make Emacs use the repository created by elpa-mirror,
;;   - Insert `(setq package-archives '(("myelpa" . "~/myelpa")))` into ~/.emacs
;;   - Restart Emacs
;;
;; You can also setup repositories on Dropbox and Github.
;; See https://github.com/redguardtoo/elpa-mirror for HOW.

;;; Code:
(require 'package)

(defvar elpamr-default-output-directory
  nil
  "The output directory.
If nil, you need provide one when `elpamr-create-mirror-for-installed'.")

(defvar elpamr-exclude-package-from-repositories
  '("myelpa")
  "Exclude packages from certain repositories.")

(defvar elpamr-debug nil "Show debug message.")

(defun elpamr--get-info-array (item)
  (if (elpamr--is-new-package)
      (cadr item)
    (cdr item)))

(defun elpamr--is-mac ()
  (eq system-type 'darwin))

(defun elpamr--create-one-item-for-archive-contents (pkg)
  "We can use package-alist directly.
This API will append some meta info into package-alist."
  (let* ((name (car pkg))
         item
         package-content
         repo
         found
         (i 0))

    ;; package-archive-contents is the list of ALL packages
    (while (and (not found)
                (< i (length package-archive-contents)))
      (setq package-content (nth i package-archive-contents))
      ;; well, all we need do is to write the actual version into package-content

      (when (equal name (car package-content))
        ;; real version used instead the one in archive-contents
        (if (arrayp (elpamr--get-info-array package-content))
            (elpamr--set-version
             package-content
             (elpamr--get-version pkg)))

        (setq item package-content)
        (setq found t)
        )
      (setq i (1+ i)))

    (unless found
      ;; make do with installed package, looks it's deleted in archive-contents
      (setq item pkg))

    (setq repo (elt (cdr package-content) 4))
    (if (listp repo)  (setq repo (elt (cdr package-content) 5)))
    (if (member repo elpamr-exclude-package-from-repositories)
        (setq item nil))

    item))


(defun elpamr--extract-info-from-dir (dirname)
  "Return `(list package-name integer-version-number)' or nil."
  (interactive)
  (if (string-match "\\(.*\\)-\\([0-9.]+\\)$" dirname)
      ;; (list name version)
      (list (match-string 1 dirname)
            (split-string (match-string 2 dirname) "\\."))))

(defun elpamr--is-new-package ()
  "Emacs 24+ has different structure from 23."
  (or (and (>= emacs-major-version 24)
           (>= emacs-minor-version 4))
      (>= emacs-major-version 25)))

(defun elpamr--win-executable-find (driver path exe)
  (if (executable-find (concat driver path exe))
      (concat driver path exe)))

(defun elpamr--executable-find (exe)
  (or (and (eq system-type 'windows-nt)
           (or
            ;; cygwin
            (elpamr--win-executable-find "c" ":\\\\cygwin64\\\\bin\\\\" exe)
            (elpamr--win-executable-find "d" ":\\\\cygwin64\\\\bin\\\\" exe)
            (elpamr--win-executable-find "e" ":\\\\cygwin64\\\\bin\\\\" exe)
            (elpamr--win-executable-find "c" ":\\\\cygwin\\\\bin\\\\" exe)
            (elpamr--win-executable-find "d" ":\\\\cygwin\\\\bin\\\\" exe)
            (elpamr--win-executable-find "e" ":\\\\cygwin\\\\bin\\\\" exe)
            ;; msys2
            (elpamr--win-executable-find "c" ":\\\\msys64\\\\usr\\\\bin\\\\" exe)
            (elpamr--win-executable-find "d" ":\\\\msys64\\\\usr\\\\bin\\\\" exe)
            (elpamr--win-executable-find "e" ":\\\\msys64\\\\usr\\\\bin\\\\" exe)
            (elpamr--win-executable-find "c" ":\\\\msys32\\\\usr\\\\bin\\\\" exe)
            (elpamr--win-executable-find "d" ":\\\\msys32\\\\usr\\\\bin\\\\" exe)
            (elpamr--win-executable-find "e" ":\\\\msys32\\\\usr\\\\bin\\\\" exe)))
      ;; *nix
      (executable-find exe)
      ;; well, `executable-find' failed
      exe))

(defun elpamr--fullpath (parent file &optional no-convertion)
  "Full path of 'parent/file'."
  (let* ((rlt (file-truename (concat (file-name-as-directory parent) file))))
    (if (and (eq system-type 'windows-nt) (not no-convertion))
        (let* ((cyg-cmd (format "%s -u \"%s\""
                                (elpamr--executable-find "cygpath")
                                rlt)))
          (setq rlt (replace-regexp-in-string "[\r\n]+"
                                              ""
                                              (shell-command-to-string cyg-cmd)))))
    (if elpamr-debug (message "elpamr--fullpath called => %s" rlt))
    rlt))

(defun elpamr--input-fullpath (file)
  (elpamr--fullpath package-user-dir file))

(defun elpamr--output-fullpath (file &optional no-convertion)
  "Return full path of output file, given the FILE."
  (elpamr--fullpath elpamr-default-output-directory file no-convertion))

(defun elpamr--clean-package-description (descr)
  (replace-regexp-in-string "-\*-.*-\*-" ""
                            (replace-regexp-in-string "\"" "" descr t)
                            t))

(defun elpamr--set-version (item version)
  (let* ((a (elpamr--get-info-array item)))
    (if (elpamr--is-new-package)
        (aset a 2 version)
      (aset a 0 version))))

(defun elpamr--get-dependency (item)
  (let* ((a (elpamr--get-info-array item)))
    (if (elpamr--is-new-package)
        (elt a 4)
      (elt a 1))))

(defun elpamr--get-version (item)
  (let* ((a (elpamr--get-info-array item)))
    (if (elpamr--is-new-package)
        (elt a 2)
      (elt a 0))))

(defun elpamr--get-repo (item)
  (let* ((a (elpamr--get-info-array item)))
    (if (elpamr--is-new-package)
        (if (> (length a) 6)
            (elt a 6) "legacy")
      (if (> (length a) 4)
          (elt a 4) "legacy"))))

(defun elpamr--get-type (item)
  (let* ((a (elpamr--get-info-array item))
         (rlt (if (elpamr--is-new-package)
                  (if (> (length a) 5)
                      (elt a 5) 'tar)
                (if (> (length a) 3)
                    (elt a 3) 'tar))))
    (if (not rlt) (setq rlt 'tar))
    rlt))

(defun elpamr--create-complete-package-name (item)
  (concat (symbol-name (car item))
          "-"
          (mapconcat (lambda (arg)
                       (format "%d" arg))
                     (elpamr--get-version item)  ".")))

(defun elpamr--is-single-el (item)
  (equal 'single (elpamr--get-type item)))

(defun elpamr--get-description (item)
  (let* ((a (elpamr--get-info-array item)) )
    (if (elpamr--is-new-package)
        (elt a 3)
      (elt a 2))))

(defun elpamr--is-single-el-by-name (name pkglist)
  (let* (rlt)
    (dolist (pkg pkglist)
      (if (string= (car pkg) name)
          (setq rlt (elpamr--is-single-el pkg))))
    rlt))

(defun elpamr--one-item-for-archive-contents (final-pkg)
  (let* ((a (elpamr--get-info-array final-pkg)))
    (format " (%s . [%S %S \"%s\" %S])\n"
            (car final-pkg)
            (elpamr--get-version final-pkg)
            (elpamr--get-dependency final-pkg)
            (elpamr--clean-package-description (elpamr--get-description final-pkg))
            (elpamr--get-type final-pkg))))

;;;###autoload
(defun elpamr-version ()
  "Current version."
  (interactive)
  (message "2.1.0"))

;;;###autoload
(defun elpamr-create-mirror-for-installed ()
  "Export INSTALLED packages into a new directory.
Create the html files for the mirror site.
`elpamr-default-output-directory' is output directory if non-nil.
Or else, user will be asked to provide the output directory."
  (interactive)
  (let* (item
         final-pkg-list
         pkg-info
         tar-cmd
         ;; package-user-dir is ~/.emacs.d/elpa by default
         (dirs (directory-files package-user-dir))
         (len (length dirs))
         (cnt 0))
    ;; quoted from manual:
    ;;   Alist of all packages available for activation.
    ;;   Each element has the form (PKG . DESCS), where PKG is a package
    ;;   name (a symbol) and DESCS is a non-empty list of `package-desc' structure,
    ;;   sorted by decreasing versions.
    (dolist (pkg package-alist)
      (setq item (elpamr--create-one-item-for-archive-contents pkg))
      (if item (push item final-pkg-list)))

    ;; set output directory
    (unless (and elpamr-default-output-directory (file-directory-p elpamr-default-output-directory))
      (setq elpamr-default-output-directory (read-directory-name "Output directory:")))

    (when (and (> (length final-pkg-list) 0)
               elpamr-default-output-directory
               (file-directory-p elpamr-default-output-directory))

      (dolist (dir dirs)
        (unless (or (member dir '("archives" "." ".."))
                    (not (setq pkg-info (elpamr--extract-info-from-dir dir))))
          (cond
           ;; copy single el
           ((elpamr--is-single-el-by-name (car pkg-info) final-pkg-list)
            (setq tar-cmd (concat (elpamr--executable-find "cp")
                                  " "
                                  (elpamr--input-fullpath (concat (file-name-as-directory dir) (car pkg-info) ".el"))
                                  " "
                                  (elpamr--output-fullpath (concat dir ".el")))))
           ;; create tar using GNU tar
           ;; BSD tar need set environment variable COPYFILE_DISABLE
           (t
            (setq tar-cmd (concat (if (elpamr--is-mac) "COPYFILE_DISABLE=\"\" " "")
                                  (elpamr--executable-find "tar")
                                  " cf "
                                  (elpamr--output-fullpath dir) ".tar --exclude=\"*.elc\" --exclude=\"*~\" "
                                  " -C "
                                  package-user-dir
                                  " "
                                  dir))))

          ;; for windows
          (if elpamr-debug (message "tar-cmd=%s" tar-cmd))
          (shell-command tar-cmd)
          (setq cnt (1+ cnt))
          (message "Creating *.tar and *.el ... %d%%" (/ (* cnt 100) len))))

      ;; output archive-contents
      (with-temp-buffer
        (let* ((print-level nil)
               (print-length nil))
          (insert "(1\n")
          (dolist (final-pkg final-pkg-list)
            ;; each package occupies one line
            (insert (elpamr--one-item-for-archive-contents final-pkg)))
          (insert ")"))
        (write-file (elpamr--output-fullpath "archive-contents" t)))
      (message "DONE! Output into %s" elpamr-default-output-directory))))

(provide 'elpa-mirror)
;;; elpa-mirror.el ends here
