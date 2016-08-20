;;; org-mime.el --- org html export for text/html MIME emails

;; Copyright (C) 2010-2015 Eric Schulte

;; Author: Eric Schulte
;; Maintainer: Chen Bin (redguardtoo)
;; Keywords: mime, mail, email, html
;; Homepage: http://github.com/redguardtoo/org-mime
;; Version: 0.0.3

;; This file is not part of GNU Emacs.

;;; License:

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
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; WYSWYG, html mime composition using org-mode
;;
;; For mail composed using the orgstruct-mode minor mode, this
;; provides a function for converting all or part of your mail buffer
;; to embedded html as exported by org-mode.  Call `org-mime-htmlize'
;; in a message buffer to convert either the active region or the
;; entire buffer to html.
;;
;; Similarly the `org-mime-org-buffer-htmlize' function can be called
;; from within an org-mode buffer to convert the buffer to html, and
;; package the results into an email handling with appropriate MIME
;; encoding.
;;
;; Quick start:
;; Write mail in message-mode, make sure the mail body follows org format.
;; Before sending mail, `M-x org-mime-htmlize'
;;
;; Setup (OPTIONAL):
;; you might want to bind this to a key with something like the
;; following message-mode binding
;;
;;   (add-hook 'message-mode-hook
;;             (lambda ()
;;               (local-set-key (kbd "C-c M-o") 'org-mime-htmlize)))
;;
;; and the following org-mode binding
;;
;;   (add-hook 'org-mode-hook
;;             (lambda ()
;;               (local-set-key (kbd "C-c M-o") 'org-mime-org-buffer-htmlize)))

;;; Code:
(eval-when-compile
  (require 'cl))

(require 'org)

(defcustom org-mime-default-header
  "#+OPTIONS: latex:t toc:nil H:3\n"
  "Default header to control html export options, and ensure
  first line isn't assumed to be a title line."
  :group 'org-mime
  :type 'string)

(defcustom org-mime-library 'mml
  "Library to use for marking up MIME elements."
  :group 'org-mime
  :type '(choice 'mml 'semi 'vm))

(defcustom org-mime-preserve-breaks t
  "Used as temporary value of `org-export-preserve-breaks' during
  mime encoding."
  :group 'org-mime
  :type 'boolean)

(defcustom org-mime-fixedwith-wrap
  "<pre style=\"font-family: courier, monospace;\">\n%s</pre>\n"
  "Format string used to wrap a fixedwidth HTML email."
  :group 'org-mime
  :type 'string)

(defvar org-mime-html-hook nil
  "Hook to run over the html buffer before attachment to email.
This could be used for example to post-process html elements.")

(defvar org-mime-pre-html-hook nil
  "Hook to run before html export.
Functions should take no arguments and will be run in a
buffer holding\nthe text to be exported.")

(defvar org-mime-send-buffer-hook nil
  "Hook to run in the Org-mode file before export.")

(defun org-mime--export-string (s)
  (if (fboundp 'org-export-string-as)
      ;; emacs24
      (org-export-string-as s 'html t)
    ;; emacs 23
    (org-export-string s "html")))

;; example hook, for setting a dark background in <pre style="background-color: #EEE;"> elements
(defun org-mime-change-element-style (element style)
  "Set new default htlm style for <ELEMENT> elements in exported html."
  (while (re-search-forward (format "<%s" element) nil t)
    (replace-match (format "<%s style=\"%s\"" element style))))

(defun org-mime-change-class-style (class style)
  "Set new default htlm style for objects with classs=CLASS in
exported html."
  (while (re-search-forward (format "class=\"%s\"" class) nil t)
    (replace-match (format "class=\"%s\" style=\"%s\"" class style))))

;; ;; example addition to `org-mime-html-hook' adding a dark background
;; ;; color to <pre> elements
;; (add-hook 'org-mime-html-hook
;;           (lambda ()
;;             (org-mime-change-element-style
;;              "pre" (format "color: %s; background-color: %s;"
;;                            "#E6E1DC" "#232323"))
;; 	    (org-mime-change-class-style
;;              "verse" "border-left: 2px solid gray; padding-left: 4px;")))

(defun org-mime-file (ext path id)
  "Markup a file for attachment."
  (case org-mime-library
    ('mml (format (concat "<#part type=\"%s\" filename=\"%s\" "
			  "disposition=inline id=\"<%s>\">\n<#/part>\n")
		  ext path id))
    ('semi (concat
            (format (concat "--[[%s\nContent-Disposition: "
			    "inline;\nContent-ID: <%s>][base64]]\n")
		    ext id)
            (base64-encode-string
             (with-temp-buffer
               (set-buffer-multibyte nil)
               (binary-insert-encoded-file path)
               (buffer-string)))))
    ('vm "?")))

(defun org-mime-multipart (plain html &optional images)
  "Markup a multipart/alternative with text/plain and text/html alternatives.
If the html portion of the message includes images wrap the html
and images in a multipart/related part."
  (case org-mime-library
    ('mml (concat "<#multipart type=alternative><#part type=text/plain>"
		  plain
		  (when images "<#multipart type=related>")
		  "<#part type=text/html>"
		  html
		  images
		  (when images "<#/multipart>\n")
		  "<#/multipart>\n"))
    ('semi (concat
            "--" "<<alternative>>-{\n"
            "--" "[[text/plain]]\n" plain
	    (when images (concat "--" "<<alternative>>-{\n"))
            "--" "[[text/html]]\n"  html
	    images
	    (when images (concat "--" "}-<<alternative>>\n"))
            "--" "}-<<alternative>>\n"))
    ('vm "?")))

(defun org-mime-replace-images (str current-file)
  "Replace images in html files with cid links."
  (let (html-images)
    (cons
     (replace-regexp-in-string ;; replace images in html
      "src=\"\\([^\"]+\\)\""
      (lambda (text)
        (format
         "src=\"cid:%s\""
         (let* ((url (and (string-match "src=\"\\([^\"]+\\)\"" text)
                          (match-string 1 text)))
                (path (expand-file-name
                       url (file-name-directory current-file)))
                (ext (file-name-extension path))
                (id (replace-regexp-in-string "[\/\\\\]" "_" path)))
           (add-to-list 'html-images
                        (org-mime-file (concat "image/" ext) path id))
           id)))
      str)
     html-images)))

(defun org-mime-htmlize (arg)
  "Export a portion of an email body composed using `mml-mode' to
html using `org-mode'.  If called with an active region only
export that region, otherwise export the entire body."
  (interactive "P")
  (let* ((region-p (org-region-active-p))
         (html-start (or (and region-p (region-beginning))
                         (save-excursion
                           (goto-char (point-min))
                           (search-forward mail-header-separator)
                           (+ (point) 1))))
         (html-end (or (and region-p (region-end))
                       ;; TODO: should catch signature...
                       (point-max)))
         (body (concat org-mime-default-header
			   (buffer-substring html-start html-end)))
         (tmp-file (make-temp-name (expand-file-name
				    "mail" temporary-file-directory)))
         ;; because we probably don't want to export a huge style file
         (org-export-htmlize-output-type 'inline-css)
         ;; makes the replies with ">"s look nicer
         (org-export-preserve-breaks org-mime-preserve-breaks)
	 ;; dvipng for inline latex because MathJax doesn't work in mail
	 (org-html-with-latex 'dvipng)
         ;; to hold attachments for inline html images
         (html-and-images
          (org-mime-replace-images
	   (org-mime--export-string body) tmp-file))
         (html-images (unless arg (cdr html-and-images)))
         (html (org-mime-apply-html-hook
                (if arg
                    (format org-mime-fixedwith-wrap body)
                  (car html-and-images)))))
    (delete-region html-start html-end)
    (save-excursion
      (goto-char html-start)
      (insert (org-mime-multipart
	       body html (mapconcat 'identity html-images "\n"))))))

(defun org-mime-apply-html-hook (html)
  (if org-mime-html-hook
      (with-temp-buffer
        (insert html)
        (goto-char (point-min))
        (run-hooks 'org-mime-html-hook)
        (buffer-string))
    html))

(defmacro org-mime-try (&rest body)
  `(condition-case nil ,@body (error nil)))

(defun org-mime-send-buffer ()
  (run-hooks 'org-mime-send-buffer-hook)
  (let* ((region-p (org-region-active-p))
	 (subject (org-export-grab-title-from-buffer))
         (file (buffer-file-name (current-buffer)))
         (body-start (or (and region-p (region-beginning))
                         (save-excursion (goto-char (point-min)))))
         (body-end (or (and region-p (region-end)) (point-max)))
	 (temp-body-file (make-temp-file "org-mime-export"))
	 (body (buffer-substring body-start body-end)))
    (org-mime-compose body file nil subject)))

(defun org-mime-compose (body file &optional to subject headers)
  (let* ((fmt 'html))
    (unless (featurep 'message)
      (require 'message))
    (message-mail to subject headers nil)
    (message-goto-body)
    (flet ((bhook (body fmt)
                  (let ((hook 'org-mime-pre-html-hook))
                    (if (> (eval `(length ,hook)) 0)
                        (with-temp-buffer
                          (insert body)
                          (goto-char (point-min))
                          (eval `(run-hooks ',hook))
                          (buffer-string))
                      body))))
      (let* ((org-link-file-path-type 'absolute)
             ;; we probably don't want to export a huge style file
             (org-export-htmlize-output-type 'inline-css)
             (html-and-images
              (org-mime-replace-images
               (org-mime--export-string (bhook body 'html)) file))
             (images (cdr html-and-images))
             (html (org-mime-apply-html-hook (car html-and-images))))
        (insert (org-mime-multipart (org-babel-trim body) html)
                (mapconcat 'identity images "\n"))))))

(defun org-mime-org-buffer-htmlize ()
  "Create an email buffer containing the current org-mode file
  exported to html and encoded in both html and in org formats as
  mime alternatives."
  (interactive)
  (org-mime-send-buffer))

(provide 'org-mime)
;;; org-mime.el ends here
