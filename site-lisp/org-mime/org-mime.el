;;; org-mime.el --- org html export for text/html MIME emails

;; Copyright (C) 2010-2015 Eric Schulte

;; Author: Eric Schulte
;; Maintainer: Chen Bin (redguardtoo)
;; Keywords: mime, mail, email, html
;; Homepage: http://github.com/org-mime/org-mime
;; Version: 0.0.9
;; Package-Requires: ((emacs "24.3") (cl-lib "0.5"))

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
;; `org-mime-org-subtree-htmlize' is similar to `org-mime-org-buffer-htmlize'
;; but works on subtree. It can also read subtree properties MAIL_SUBJECT,
;; MAIL_TO, MAIL_CC, and MAIL_BCC. Here is the sample of subtree:
;;
;; * mail one
;;   :PROPERTIES:
;;   :MAIL_SUBJECT: mail title
;;   :MAIL_TO: person1@gmail.com
;;   :MAIL_CC: person2@gmail.com
;;   :MAIL_BCC: person3@gmail.com
;;   :END:
;;
;; To avoid exporting TOC, you can setup `org-mime-export-options',
;;   (setq org-mime-export-options '(:section-numbers nil
;;                                   :with-author nil
;;                                   :with-toc nil))
;; Or just setup your export options in org buffer/subtree which is overrided
;; by `org-mime-export-options' when it's NOT nil.
;;
;; You can change `org-mime-up-subtree-heading' before exporting subtree.
;; heck its documentation.
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
;;
;; Extra Tips:
;; 1. In order to embed image into your mail, use below syntax,
;; [[/full/path/to/your.jpg]]
;;
;; 2. It's easy to add your own emphasis symbol.  For example, in order to render
;; text between "@" in red color, you can use `org-mime-html-hook':
;;   (add-hook 'org-mime-html-hook
;;             (lambda ()
;;               (while (re-search-forward "@\\([^@]*\\)@" nil t)
;;                 (replace-match "<span style=\"color:red\">\\1</span>"))))
;;
;; 3. Since v0.0.9, the quoted mail uses modern style (like Gmail).
;; So replyed mail looks clean and modern. If you prefer old style, please set
;; `org-mime-beautify-quoted-mail' to nil.

;;; Code:
(require 'cl-lib)
(require 'xml)
(require 'org)

(defcustom org-mime-beautify-quoted-mail t
  "Beautify quoted mail in more clean HTML, like Gmail."
  :group 'org-mime
  :type 'boolean)

(defcustom org-mime-use-property-inheritance nil
  "Non-nil means al MAIL_ properties apply also for sublevels."
  :group 'org-mime
  :type 'boolean)

(defcustom org-mime-default-header
  "#+OPTIONS: latex:t toc:nil H:3\n"
  "Default header to control html export options.
And ensure first line isn't assumed to be a title line."
  :group 'org-mime
  :type 'string)

(defcustom org-mime-library 'mml
  "Library to use for marking up MIME elements."
  :group 'org-mime
  :type '(choice 'mml 'semi 'vm))

(defcustom org-mime-preserve-breaks t
  "Temporary value of `org-export-preserve-breaks' during mime encoding."
  :group 'org-mime
  :type 'boolean)

(defcustom org-mime-fixedwith-wrap
  "<pre style=\"font-family: courier, monospace;\">\n%s</pre>\n"
  "Format string used to wrap a fixedwidth HTML email."
  :group 'org-mime
  :type 'string)

(defvar org-mime-export-options nil
  "Default export options which may overrides org buffer/subtree options.
You avoid exporting section-number/author/toc with below setup,
`(setq org-mime-export-options '(:section-numbers nil :with-author nil :with-toc nil))'")

(defvar org-mime-html-hook nil
  "Hook to run over the html buffer before attachment to email.
This could be used for example to post-process html elements.")

(defvar org-mime-pre-html-hook nil
  "Hook to run before html export.
Functions should take no arguments and will be run in a
buffer holding\nthe text to be exported.")

(defvar org-mime-send-buffer-hook nil
  "Hook to run in the Org-mode file before export.")

(defvar org-mime-debug nil
  "Enable debug logger.")

(defvar org-mime-up-subtree-heading 'org-up-heading-safe
  "Funtion to call before exporting subtree.
You could use either `org-up-heading-safe' or `org-back-to-heading'.")


(defun org-mime--chomp (str)
  "Chomp leading and tailing whitespace from STR."
  (while (string-match "\\`[\n\r]+\\|^\\s-+\\|\\s-+$\\|[\n\r]+\\'"
                       str)
    (setq str (replace-match "" t t str)))
  str)

(defun org-mime--export-string (s fmt &optional opts)
  "Export string S into HTML format.  OPTS is export options."
  (let* (rlt)
    (if org-mime-debug (message "org-mime--export-string called => %s" opts))
    ;; we won't export title from org file anyway
    (if opts (setq opts (plist-put opts 'title nil)))
    (if (fboundp 'org-export-string-as)
        ;; emacs24.4+
        (setq rlt (org-export-string-as s fmt t (if org-mime-export-options org-mime-export-options opts)))
      ;; emacs 24.3
      (setq rlt (org-export-string s (symbol-name fmt)))
      ;; manually remove the drawers, see https://github.com/org-mime/org-mime/issues/3
      ;; Only happens on Emacs 24.3
      (let* ((b (string-match ":END:" rlt)))
        (if (and b (> b 0))
            (setq rlt (substring-no-properties rlt
                                               (+ b (length ":END:"))
                                               (length rlt))))))
    rlt))

;; example hook, for setting a dark background in <pre style="background-color: #EEE;"> elements
(defun org-mime-change-element-style (element style)
  "Set <ELEMENT> elements in exported html with new default html STYLE."
  (while (re-search-forward (format "<%s" element) nil t)
    (replace-match (format "<%s style=\"%s\"" element style))))

(defun org-mime-change-class-style (class style)
  "CLASS is used for new default html STYLE in exported html."
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
  "Markup a file with EXT, PATH and ID for attachment."
  (if org-mime-debug (message "org-mime-file called => %s %s %s" ext path id))
  (cl-case org-mime-library
    (mml (format (concat "<#part type=\"%s\" filename=\"%s\" "
			  "disposition=inline id=\"<%s>\">\n<#/part>\n")
		  ext path id))
    (semi (concat
            (format (concat "--[[%s\nContent-Disposition: "
			    "inline;\nContent-ID: <%s>][base64]]\n")
		    ext id)
            (base64-encode-string
             (with-temp-buffer
               (set-buffer-multibyte nil)
               (insert-file-contents-literally path)
               (buffer-string)))))
    (vm "?")))

(defun org-mime-encode-quoted-mail-body ()
  "Please note quoted mail body could be with reply."
  (let* ((b (save-excursion
              (goto-char (point-min))
              (search-forward-regexp "^[^ ]*&gt; ")
              (search-backward-regexp "<p>")
              (line-beginning-position)))
         (e (save-excursion
              (goto-char (point-max))
              (search-backward-regexp "^[^ ]*&gt; ")
              (search-forward-regexp "</p>")
              (line-end-position)))
         (str (format "<div>%s</div>" (buffer-substring-no-properties b e)))
         (paragraphs (xml-node-children (car (with-temp-buffer
                                               (insert str)
                                               (xml--parse-buffer nil nil)))))
         (is-quoted t)
         lines
         (rlt "<blockquote class=\"gmail_quote\" style=\"margin:0 0 0 .8ex;border-left:1px #ccc solid;padding-left:1ex\">\n<p>\n"))
    (dolist (p paragraphs)
      (when (and p (> (length p) 2))
        (dolist (s p)
          (when (and s
                     (not (eq s 'p))
                     (not (consp s))
                     (not (string= s "\n")))
            ;; trim string
            (setq s (replace-regexp-in-string "\\`[ \t\n]*" "" (replace-regexp-in-string "[ \t\n]*\\'" "" s)))
            (setq lines (split-string s "\n"))
            (dolist (l lines)
              (cond
               ((string-match "^ *[^ ]*> \\(.*\\)" l)
                (when (not is-quoted)
                  (setq rlt (concat rlt "</p>\n<blockquote class=\"gmail_quote\" style=\"margin:0 0 0 .8ex;border-left:1px #ccc solid;padding-left:1ex\">\n<p>\n"))
                  (setq is-quoted t))
                (setq rlt (concat rlt (match-string 1 l) "<br />\n")))
               ((string= l "")
                (set rlt (concat rlt "<br />")))
               (t
                (when is-quoted
                  (setq rlt (concat rlt "</p>\n</blockquote>\n<p>\n"))
                  (setq is-quoted nil))
                (setq rlt (concat rlt l "\n")))))))))
    (setq rlt (concat rlt (if is-quoted "</p>\n</blockquote>\n" "</p>\n")))
    (list b e rlt )))

(defun org-mime-cleanup-quoted (html)
  "Clean up quoted mail in modern UI style."
  (cond
   (org-mime-beautify-quoted-mail
    (let* (info)
      (with-temp-buffer
        ;; clean title of quoted
        (insert (replace-regexp-in-string
                 "<p>[\n\r]*&gt;&gt;&gt;&gt;&gt; .* == \\([^\r\n]*\\)[\r\n]*</p>"
                 "<div class=\"gmail_quote\">\\1</div>"
                 html))
        (unwind-protect
            (let (retval)
              (condition-case ex
                  (setq info (org-mime-encode-quoted-mail-body))
                  (setq retval info)
                ('error (setq info nil)))
              retval))
        (cond
         (info
          (delete-region (nth 0 info) (nth 1 info))
          (goto-char (nth 0 info))
          (insert (nth 2 info))
          (buffer-substring-no-properties (point-min) (point-max)))
         (t
          html)))))
   (t
    html)))

(defun org-mime-multipart (plain html &optional images)
  "Markup a multipart/alternative PLAIN with PLAIN and HTML alternatives.
If html portion of message includes IMAGES they are wrapped in multipart/related part."
  (cl-case org-mime-library
    (mml (concat "<#multipart type=alternative><#part type=text/plain>"
                 plain
                 (when images "<#multipart type=related>")
                 "<#part type=text/html>"
                 (org-mime-cleanup-quoted html)
                 images
                 (when images "<#/multipart>\n")
                 "<#/multipart>\n"))
    (semi (concat
            "--" "<<alternative>>-{\n"
            "--" "[[text/plain]]\n" plain
	    (when images (concat "--" "<<alternative>>-{\n"))
            "--" "[[text/html]]\n"  html
	    images
	    (when images (concat "--" "}-<<alternative>>\n"))
            "--" "}-<<alternative>>\n"))
    (vm "?")))

(defun org-mime-replace-images (str current-file)
  "Replace images in STR with cid links.
CURRENT-FILE is used to calculate full path of images."
  (if org-mime-debug (message "org-mime-replace-images called => %s" current-file)
)  (let* (html-images)
    (cons
     (replace-regexp-in-string ;; replace images in html
      "src=\"\\([^\"]+\\)\""
      (lambda (text)
        (format
         "src=\"cid:%s\""
         (let* ((url (and (string-match "src=\"\\([^\"]+\\)\"" text)
                          (match-string 1 text)))
                (path (if (string-match-p "^file:///" url) (replace-regexp-in-string "^file://" "" url)
                        (expand-file-name url (file-name-directory current-file))))
                (ext (file-name-extension path))
                (id (replace-regexp-in-string "[\/\\\\]" "_" path)))
           (add-to-list 'html-images
                        (org-mime-file (concat "image/" ext) path id))
           id)))
      str)
     html-images)))

(defun org-mime-htmlize (arg)
  "Export a portion of an email to html using `org-mode'.
If called with an active region only export that region, otherwise entire body.
If ARG is not NIL, use `org-mime-fixedwith-wrap' to wrap the exported text."
  (interactive "P")
  (if org-mime-debug (message "org-mime-htmlize called"))
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
           (org-mime--export-string body
                                    'html
                                    (if (fboundp 'org-export--get-inbuffer-options)
                                        (org-export--get-inbuffer-options)))
           tmp-file))
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
  "Apply HTML hook."
  (if org-mime-html-hook
      (with-temp-buffer
        (insert html)
        (goto-char (point-min))
        (run-hooks 'org-mime-html-hook)
        (buffer-string))
    html))

(defun org-mime--get-buffer-title ()
  "Get buffer title."
  (let* ((tmp (if (fboundp 'org-export--get-inbuffer-options)
                  (plist-get (org-export--get-inbuffer-options) :title))))
    (when tmp
      (let ((txt (car tmp)))
        (set-text-properties 0 (length txt) nil txt)
        txt))))

(defun org-mime-compose (body file &optional to subject headers opts)
  "Create mail BODY in FILE with SUBJECT, HEADERS and OPTS."
  (if org-mime-debug (message "org-mime-compose called => %s %s" file opts))
  (let* ((fmt 'html))
    (unless (featurep 'message)
      (require 'message))
    (message-mail to subject headers nil)
    (message-goto-body)
    (cl-labels ((bhook (body fmt)
                       (let ((hook 'org-mime-pre-html-hook))
                         (if (> (eval `(length ,hook)) 0)
                             (with-temp-buffer
                               (insert body)
                               (goto-char (point-min))
                               (eval `(run-hooks ',hook))
                               (buffer-string))
                           body))))
      (let* ((org-link-file-path-type 'absolute)
             (plain (org-mime--export-string (org-mime--chomp body) 'ascii))
             ;; we probably don't want to export a huge style file
             (org-export-htmlize-output-type 'inline-css)
             (html-and-images
              (org-mime-replace-images
               (org-mime--export-string (bhook body 'html) 'html opts)
               file))
             (images (cdr html-and-images))
             (html (org-mime-apply-html-hook (car html-and-images))))
        (insert (org-mime-multipart plain html)
                (mapconcat 'identity images "\n"))))))

;;;###autoload
(defun org-mime-org-buffer-htmlize ()
  "Create buffer where text encoded in html&org formats as mime alternatives."
  (interactive)
  (run-hooks 'org-mime-send-buffer-hook)
  (let* ((region-p (org-region-active-p))
         (file (buffer-file-name (current-buffer)))
         (subject (or (org-mime--get-buffer-title)
                      (if (not file) (buffer-name (buffer-base-buffer))
                        (file-name-sans-extension
                         (file-name-nondirectory file)))))
         (body-start (or (and region-p (region-beginning))
                         (save-excursion (goto-char (point-min)))))
         (body-end (or (and region-p (region-end)) (point-max)))
         (temp-body-file (make-temp-file "org-mime-export"))
         (body (buffer-substring body-start body-end)))
    (org-mime-compose body
                      file
                      nil ; TO
                      subject
                      nil ; HEADERS (CC, BCC ...)
                      (if (fboundp 'org-export--get-inbuffer-options)
                          (org-export--get-inbuffer-options)))))

;;;###autoload
(defun org-mime-org-subtree-htmlize ()
  "Create an email buffer containing the current subtree of the
current org-mode file exported to html and encoded in both html
and in org formats as mime alternatives."
  (interactive)
  (save-excursion
    (funcall org-mime-up-subtree-heading)
    (cl-flet ((mp (p) (org-entry-get nil p org-mime-use-property-inheritance)))
      (let* ((file (buffer-file-name (current-buffer)))
             (subject (or (mp "MAIL_SUBJECT") (nth 4 (org-heading-components))))
             (to (mp "MAIL_TO"))
             (cc (mp "MAIL_CC"))
             (bcc (mp "MAIL_BCC"))
             ;; Thanks for Matt Price improving handling of cc & bcc headers
             (other-headers (cond
                             ((and cc bcc) `((cc . ,cc) (bcc . ,bcc)))
                             (cc `((cc . ,cc)))
                             (bcc `((bcc . ,bcc)))
                             (t nil)))
             (opts (if (fboundp 'org-export--get-subtree-options) (org-export--get-subtree-options)))
             (body (org-get-entry)))
        (org-mime-compose body file to subject other-headers opts)))))

(provide 'org-mime)
;;; org-mime.el ends here
