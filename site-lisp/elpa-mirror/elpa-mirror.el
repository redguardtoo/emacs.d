;;; elpa-mirror.el --- ELPA mirror from locally installed packages is easy

;; Copyright (C) 2014 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/elpa-mirror
;; Version: 1.2.0
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

;; - `M-x elpamr-create-mirror-for-installed` to create local repository at "~/myelpa"
;; - Insert `(setq package-archives '(("myelpa" . "~/myelpa")))` into ~/.emacs
;;    to use that local repository
;;
;; You can also setup repositories on Dropbox and Github.
;; See https://github.com/redguardtoo/elpa-mirror for how.

;;; Code:
(require 'package)

(defvar elpamr-default-output-directory
  nil
  "The output directory.
If nil, you need provide one when `elpamr-create-mirror-for-installed'")

(defvar elpamr-repository-name
  "myelpa"
  "Repository name to be displayed in index.html.")

(defvar elpamr-repository-path
  "http://myelpa.mydomain.com"
  "Repository path to be displayed in index.html.")

(defvar elpamr-email
  "name@mydomain.com"
  "Email to be displayed in index.html.")

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
  (let ((name (car pkg))
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
  (let (rlt name version)
    (when (string-match "\\(.*\\)-\\([0-9.]+\\)$" dirname)
      (setq name (match-string 1 dirname))
      (setq version (split-string (match-string 2 dirname) "\\."))
      (setq rlt (list name version)))
    rlt))

(defun elpamr--is-new-package ()
  "Emacs 24 and Emacs 25 has different data structure from Emacs 23."
  (or (and (>= emacs-major-version 24)
           (>= emacs-minor-version 4))
      (>= emacs-major-version 25)))

(defun elpamr--output-fullpath (file)
  "Return full path of output file, given the FILE."
  (file-truename (concat
                  (file-name-as-directory elpamr-default-output-directory)
                  file)))

(defun elpamr--get-html-content ()
  "The output of `npm install -g minify; minify index.html | pclip'."
  (let (rlt)
    (setq rlt "<!DOCTYPE html><html lang=en><head><meta charset='utf-8'><meta name=viewport content='width=device-width,initial-scale=1'><meta name=description content><title>My Emacs packages</title><style>.clear{clear:both;width:100%}.code{background-color:#DCDCDC;border:1px solid #B5B5B5;border-radius:3px;display:inline-block;margin:0;max-width:100%;overflow:auto;padding:0;vertical-align:middle}.spacer{margin:10px 0}@media screen and (max-width:1024px){ul{list-style-type:none;padding-left:8px}#quickstart,#upgrade,.descr,.name{width:100%}.name{padding-top:5px}.descr{border-bottom:1px solid;padding-bottom:5px}}@media screen and (min-width:1025px){#quickstart{float:left;width:50%}#upgrade{float:right;width:50%}.name{float:left;width:50%}.descr{float:right;width:50%}}</style><body><div class=clear><div id=quickstart><h2>Quick Start</h2><ul id=usage><li><a href=http://repo.or.cz/w/emacs.git/blob_plain/1a0a666f941c99882093d7bd08ced15033bc3f0c:/lisp/emacs-lisp/package.el>First, if you are not using Emacs 24, install package.el</a>.</li><li>Add to your .emacs:<br><pre class='code spacer'>(require 'package)
(add-to-list 'package-archives
          '(\"elpamr-repository-name\" .
          \"elpamr-repository-path\"))
          (package-initialize)</pre><br>In above code, you can use full path of file directory instead of URL.</li><li><span class=code>M-x eval-buffer</span> to evaluate it, and then do <span class=code>M-x package-refresh-contents</span> to load in the package listing.</li><li>You're good to go!</li><li><strong>OPTIONAL</strong>, please see <a href=http://www.emacswiki.org/emacs/ELPA>EmacsWiki</a> for advanced stuff.</li><li><strong>OPTIONAL</strong>, to upgrade specific package, please download tar file and run <span class=code>M-x package-install-file</span>.</li></ul></div><div id=upgrade><h2>Upgrade package</h2><ul><li>Please email to elpamr-email for upgrading specific package.</li><li>The email subject <strong>should</strong> start with <span class=code>ELPA-PACKAGE-yyyymmdd</span> (yyyymmdd is the date string like '20140215').</li><li>The remaining part of subject should either be empty string or the full package name with version number like 'cl-lib-0.5.tar'.</li><li>If the package name is not in the subject, you should attach the package itself in email</li><li>You can explain why you need upgrade in email body or just leave it empty</li></ul></div></div><div class=clear><h2>List of Packages</h2><form method=post id=searchForm action><p><label for=filter>Filter:</label><input id=filter placeholder='Input package name here'> <input type=button value=reset id='reset'></p></form>elpamr-package-list-html</div><script>var dic=[elpamr-package-list-json];</script><script src=//cdnjs.cloudflare.com/ajax/libs/jquery/1.9.1/jquery.min.js></script><script>$(document).ready(function(){var e=function(){for(var e,i,n=$('#filter').val().replace(/^\s+|\s+$/g,''),c=1,r=dic.length;r>=c;c++)e=$('#n'+c),i=$('#d'+c),''!==n&&-1===dic[c-1].indexOf(n)?(e.hide(),i.hide()):(e.show(),i.show())};$('#filter').keyup(e),$('#reset').click(function(){$('#filter').val(''),e()})});</script>
")
    rlt))

(defun elpamr--clean-package-description (descr)
  (replace-regexp-in-string "-\*-.*-\*-" "" (replace-regexp-in-string "\"" "" descr t) t))

(defun elpamr--set-version (item version)
  (let ((a (elpamr--get-info-array item)))
    (if (elpamr--is-new-package)
        (aset a 2 version)
      (aset a 0 version))
    ))

(defun elpamr--get-dependency (item)
  (let ((a (elpamr--get-info-array item)))
    (if (elpamr--is-new-package)
        (elt a 4)
      (elt a 1))
    ))

(defun elpamr--get-version (item)
  (let ((a (elpamr--get-info-array item)))
    (if (elpamr--is-new-package)
        (elt a 2)
      (elt a 0))
    ))

(defun elpamr--get-repo (item)
  (let ((a (elpamr--get-info-array item)))
    (if (elpamr--is-new-package)
        (if (> (length a) 6)
            (elt a 6) "legacy")
      (if (> (length a) 4)
          (elt a 4) "legacy"))
    ))

(defun elpamr--get-type (item)
  (let ((a (elpamr--get-info-array item))
        rlt)
    (setq rlt
          (if (elpamr--is-new-package)
              (if (> (length a) 5)
                  (elt a 5) 'tar)
            (if (> (length a) 3)
                (elt a 3) 'tar)
            ))
    (if (not rlt) (setq rlt 'tar))
    rlt))

(defun elpamr--create-complete-package-name (item)
  (concat (symbol-name (car item))
          "-"
          (mapconcat (lambda (arg) (format "%d" arg)) (elpamr--get-version item)  ".")))

(defun elpamr--format-package-list-into-json (list)
  (let (pkg-name)
    (mapconcat
     (lambda (item)
       (setq pkg-name (elpamr--create-complete-package-name item))
       (format "'%s'" pkg-name)
       ) list ",\n")
    ))

(defun elpamr--is-single-el (item)
  (equal 'single (elpamr--get-type item)))

(defun elpamr--get-description (item)
  (let ((a (elpamr--get-info-array item)) )
    (if (elpamr--is-new-package)
        (elt a 3)
      (elt a 2))
    ))

(defun elpamr--format-package-list-into-html (list)
  (let (tar-name (cnt 0))
    (mapconcat
     (lambda (item)
       (setq cnt (1+ cnt))
       (setq tar-name (concat (elpamr--create-complete-package-name item)
                              (if (elpamr--is-single-el item) ".el" ".tar")
                              ))
       (format "<div id='n%d' class='name'><a href='%s'>%s</a></div><div id='d%d' class='descr'>%s</div>\n"
               cnt
               tar-name
               tar-name
               cnt
               (elpamr--clean-package-description (elpamr--get-description item)))
       ) list "\n")
    ))

(defun elpamr--format-email ()
  (format "<a href='mailto:%s'>%s</a>" elpamr-email elpamr-email))

(defun elpamr--output-html (rlt)
  (let ((js-file (elpamr--output-fullpath "elpa-mirror.js"))
        (js-tmpl (concat
                  (file-name-directory (if load-file-name load-file-name (symbol-file 'elpamr--output-html)))
                  "elpa-mirror.js"))
        (html-file (elpamr--output-fullpath "index.html"))
        ;; @see http://stackoverflow.com/questions/145291/smart-home-in-emacs/145359#145359
        (html-tmpl (concat
                    (file-name-directory (if load-file-name load-file-name (symbol-file 'elpamr--output-html)))
                    "index.html")))

    ;; index.html
    (with-temp-buffer
      (let ((print-level nil)  (print-length nil) str)
        (setq str (replace-regexp-in-string
                 "elpamr-package-list-html"
                 (elpamr--format-package-list-into-html rlt)
                 (elpamr--get-html-content)
                 t))
        (setq str (replace-regexp-in-string
                   "elpamr-package-list-json"
                   (elpamr--format-package-list-into-json rlt)
                   str
                   t))
        (setq str (replace-regexp-in-string
                   "elpamr-email"
                   (elpamr--format-email)
                   str
                   t))
        (setq str (replace-regexp-in-string
                   "elpamr-repository-name"
                   elpamr-repository-name
                   str
                   t))
        (setq str (replace-regexp-in-string
                   "elpamr-repository-path"
                   elpamr-repository-path
                   str
                   t))
        (insert str))
      (write-file html-file))
    ))

(defun elpamr--is-single-el-by-name (name pkglist)
  (let (rlt)
    (dolist (pkg pkglist)
      (if (string= (car pkg) name)
          (setq rlt (elpamr--is-single-el pkg))
        ))
    rlt))

(defun elpamr--one-item-for-archive-contents (final-pkg)
  (let ((a (elpamr--get-info-array final-pkg)) )
    (format " (%s . [%S %S \"%s\" %S])\n"
            (car final-pkg)
            (elpamr--get-version final-pkg)
            (elpamr--get-dependency final-pkg)
            (elpamr--clean-package-description (elpamr--get-description final-pkg))
            (elpamr--get-type final-pkg))))

;;;###autoload
(defun elpamr--version ()
  "Current version."
  (interactive)
  (message "1.2.0"))

;;;###autoload
(defun elpamr-create-mirror-for-installed ()
  "Export INSTALLED packages into a new directory.
Create the html files for the mirror site.
`elpamr-default-output-directory' is output directory if non-nil.
Or else, user will be asked to provide the output directory."
  (interactive)
  (let (item final-pkg-list pkg-dirname pkg-info tar-cmd len dirs cnt)
    ;; quoted from manual:
    ;;   Alist of all packages available for activation.
    ;;   Each element has the form (PKG . DESCS), where PKG is a package
    ;;   name (a symbol) and DESCS is a non-empty list of `package-desc' structure,
    ;;   sorted by decreasing versions.
    (dolist (pkg package-alist)
      (setq item (elpamr--create-one-item-for-archive-contents pkg))
      (if item (push item final-pkg-list))
      )

    ;; set output directory
    (unless (and elpamr-default-output-directory (file-directory-p elpamr-default-output-directory))
      (setq elpamr-default-output-directory (read-directory-name "Output directory:"))
      )

    (when (and (> (length final-pkg-list) 0)
               elpamr-default-output-directory
               (file-directory-p elpamr-default-output-directory))
      ;; package-user-dir is ~/.emacs.d/elpa by default
      (setq dirs (directory-files package-user-dir))
      ;; prepare to loop dirs
      (setq cnt 0)
      (setq len (length dirs))
      (dolist (dir dirs)
        (unless (or (member dir '("archives" "." ".."))
                    (not (setq pkg-info (elpamr--extract-info-from-dir dir))))

          (cond
           ;; copy single el
           ((elpamr--is-single-el-by-name (car pkg-info) final-pkg-list)
            (setq tar-cmd (concat "cd " package-user-dir
                                  "; cp "
                                  (file-name-as-directory dir) (car pkg-info) ".el"
                                  " "
                                  (elpamr--output-fullpath dir)
                                  ".el ")))
           ;; create tar using GNU tar or BSD tar
           (t
            (setq tar-cmd (concat "cd "
                                  package-user-dir
                                  "; "
                                  (if (elpamr--is-mac) "COPYFILE_DISABLE=\"\" " "")
                                  "tar cf "
                                  (elpamr--output-fullpath dir) ".tar --exclude=\"*.elc\" --exclude=\"*~\" "
                                  dir))
            ))

          (when elpamr-debug
            (message "elpamr-default-output-directory=%s" elpamr-default-output-directory)
            (message "package-alist=%s" package-alist)
            (message "package-user-dir=%s" package-user-dir)
            (message "tar-cmd=%s" tar-cmd))

          (shell-command tar-cmd)
          (setq cnt (1+ cnt))
          (message "Creating *.tar and *.el ... %d%%" (/ (* cnt 100) len))
          ))

      ;; output archive-contents
      (with-temp-buffer
        (let ((print-level nil)  (print-length nil))
          (insert "(1\n")
          (dolist (final-pkg final-pkg-list)
            ;; each package occupies one line
            (insert (elpamr--one-item-for-archive-contents final-pkg)))
          (insert ")"))
        (write-file (elpamr--output-fullpath "archive-contents")))
      (elpamr--output-html final-pkg-list)
      (message "DONE! Output into %s" elpamr-default-output-directory))
    ))

(provide 'elpa-mirror)
;;; elpa-mirror.el ends here
