;;; elnode-wiki.el --- a wiki with Elnode  -*- lexical-binding: t -*-

;; Copyright (C) 2010, 2011, 2012  Nic Ferrier

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;; Maintainer: Nic Ferrier <nferrier@ferrier.me.uk>
;; Created: 5th October 2010
;; Keywords: lisp, http, hypermedia

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This is a Wiki Engine completely written in EmacsLisp, using Elnode
;; as a server.
;;
;;; Source code
;;
;; elnode's code can be found here:
;;   http://github.com/nicferrier/elnode

;;; Style note
;;
;; This codes uses the Emacs style of:
;;
;;    elnode-wiki--private-function
;;
;; for private functions.


;;; Code:

(require 'elnode)
(require 'db)
(eval-when-compile 'fakir)
(require 'creole nil 't)
;;(require 'vc)

(defgroup elnode-wikiserver nil
  "A Wiki server written with Elnode."
  :group 'elnode)

;;;###autoload
(defconst elnode-wikiserver-wikiroot-default
  (expand-file-name (concat elnode-config-directory "wiki/"))
  "The default location of the wiki root.

This is used to detect whether elnode needs to create this
directory or not.")

;;;###autoload
(defcustom elnode-wikiserver-wikiroot
  elnode-wikiserver-wikiroot-default
  "The root for the Elnode wiki files.

This is where elnode-wikiserver serves wiki files from."
  :type '(directory)
  :group 'elnode-wikiserver)

(defcustom elnode-wikiserver-body-header
  "<div id='top'></div>"
  "HTML BODY preamable of a rendered Wiki page."
  :type '(string)
  :group 'elnode-wikiserver)

(defcustom elnode-wikiserver-body-footer
  "<div id='footer'>
<form action='{{page}}' method='POST'>
<fieldset>
<legend>Edit this page</legend>
<textarea  cols='80' rows='20' name='wikitext'>
{{text}}
</textarea><br/>
<input type='text' name='comment' value=''/>
<input type='submit' name='save' value='save'/>
<input type='submit' name='preview' value='preview'/>
</fieldset>
</form>
</div>"
  "HTML BODY footter for a rendered Wiki page."
  :type '(string)
  :group 'elnode-wikiserver)

(defcustom elnode-wikiserver-body-footer-not-loggedin
  "<div id='footer'>
    <a href='/wiki/login/?redirect={{page}}'>login to edit</a>
  </div>"
  "HTML BODY footter for a rendered Wiki page."
  :type '(string)
  :group 'elnode-wikiserver)

(defun elnode-wiki--setup ()
  "Setup the wiki."
  (elnode--dir-setup elnode-wikiserver-wikiroot
                     elnode-wikiserver-wikiroot-default
                     "default-wiki-index.creole"
                     "index.creole"
                     "default-wiki-logo.gif"))

;; Internal wiki stuff

(defvar elnode-wiki-db
  (db-make
   `(db-hash
     :filename
     ,(expand-file-name
       (concat elnode-config-directory "elnode-wiki-auth")))))

;; Define the authentication scheme for the wiki
(elnode-defauth 'elnode-wiki-auth
  :auth-db elnode-wiki-db
  :redirect "/wiki/login/")

(defun elnode-wiki-page (httpcon wikipage &optional pageinfo)
  "Creole render a WIKIPAGE back to the HTTPCON."
  ;; Otherwise just do it
  (elnode-http-start httpcon 200 `("Content-type" . "text/html"))
  (with-stdout-to-elnode httpcon
      (let ((page-info (or pageinfo (elnode-http-pathinfo httpcon)))
            (header elnode-wikiserver-body-header)
            (footer (if-elnode-auth httpcon 'elnode-wiki-auth
                      elnode-wikiserver-body-footer
                      elnode-wikiserver-body-footer-not-loggedin)))
        (creole-wiki
         wikipage
         :destination t
         :variables (list (cons 'page page-info))
         :body-header header
         :body-footer footer))))

(defun elnode-wiki--text-param (httpcon)
  "Get the text param from HTTPCON and convert it."
  (replace-regexp-in-string
   "\r" "" ; browsers send text in DOS line ending format
   (elnode-http-param httpcon "wikitext")))

(defun elnode-wiki--save-request (httpcon wikiroot path text)
  "Process an update request."
  (let* ((page (if path
                   (save-match-data
                     (string-match "/wiki/\\(.*\\)$" path)
                     (match-string 1 path))))
         (comment (elnode-http-param httpcon "comment"))
         (file-name (if (equal page "")
                        (concat wikiroot "index.creole")
                      (concat (file-name-as-directory wikiroot) page)))
         (buffer (find-file-noselect file-name)))
    (with-current-buffer buffer
      (erase-buffer)
      (insert text)
      (save-buffer)
      (let ((git-buf
             (get-buffer-create
              (generate-new-buffer-name
               "* elnode wiki commit buf *"))))
        (shell-command
         (format "git commit -m '%s' %s" comment file-name)
         git-buf)
        (kill-buffer git-buf))
      (elnode-wiki-page httpcon file-name))))

(defun elnode-wiki-handler (httpcon wikiroot)
  "A low level handler for Wiki operations.

Send the Wiki page requested, which must be a file existing under
the WIKIROOT, back to the HTTPCON.

Update operations are protected by authentication."
  (elnode-method httpcon
    (GET
     (elnode-docroot-for wikiroot
       with target-path
       on httpcon
       do
       ;; Do we need to serve an index?
       (if (equal target-path (expand-file-name (concat wikiroot "/")))
           (elnode-wiki-page httpcon (concat wikiroot "/index.creole"))
           ;; Else it's a wiki page or some collateral
           (if (string-match "\\.creole$" target-path)
               ;; Serve a creole page
               (elnode-wiki-page httpcon target-path)
               ;; Else serve just content
               (elnode-send-file httpcon target-path)))))
    (POST
     (with-elnode-auth httpcon 'elnode-wiki-auth
       (let* ((path (elnode-http-pathinfo httpcon))
              (text (elnode-wiki--text-param httpcon)))
         (if (not (elnode-http-param httpcon "preview"))
             ;; A save request in which case save the new text and then
             ;; send the wiki text.
             (elnode-wiki--save-request httpcon wikiroot path text)
             ;; Might be a preview request in which case send back the WIKI
             ;; text that's been sent.
             (with-temp-file "/tmp/preview"
               (insert text))
             (elnode-wiki-page httpcon "/tmp/preview" path)))))))

;;;###autoload
(defun elnode-wikiserver-test ()
  "Test whether we should serve Wiki or not."
  (featurep 'creole))

;;;###autoload
(defun elnode-wikiserver (httpcon)
  "Serve Wiki pages from `elnode-wikiserver-wikiroot'.

HTTPCON is the request.

The Wiki server is only available if the `creole' package is
provided. Otherwise it will just error."
  (if (not (elnode-wikiserver-test))
      (elnode-send-500 httpcon "The Emacs feature 'creole is required.")
      (elnode-auth-dispatcher httpcon 'elnode-wiki-auth
        (elnode-wiki--setup)
        (elnode-wiki-handler httpcon elnode-wikiserver-wikiroot))))

(provide 'elnode-wiki)

;;; elnode-wiki.el ends here
