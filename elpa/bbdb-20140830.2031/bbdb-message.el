;;; bbdb-message.el --- BBDB interface to Mail Composition Packages.

;; Copyright (C) 2010-2014 Roland Winkler <winkler@gnu.org>

;; This file is part of the Insidious Big Brother Database (aka BBDB),

;; BBDB is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; BBDB is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with BBDB.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;; This file contains the BBDB interface to Mail Composition Packages.
;;; See the BBDB info manual for documentation.

(require 'bbdb)
(require 'message)
(require 'sendmail)

(defcustom bbdb/message-update-records-p 'bbdb-select-message
  "How `bbdb-mua-update-records' processes mail addresses in outgoing messages.
This MUA-specific variable is normally not used.  It is a fallback
if the generic (MUA-independent) variables `bbdb-mua-auto-update-p',
`bbdb-update-records-p' or `bbdb-mua-update-interactive-p' result
in a value of nil for the arg UPDATE-P of `bbdb-update-records'.

Allowed values are:
 nil          Do nothing.
 search       Search for existing records.
 update       Search for existing records, update if necessary.
 query        Update existing records or query for creating new ones.
 create or t  Update existing records or create new ones.
 a function   This functions will be called with no arguments.
                It should return one of the above values."
  :group 'bbdb-mua-message
  :type '(choice (const :tag "do nothing"
                        nil)
                 (const :tag "search for existing records"
                        (lambda () (let ((bbdb-update-records-p 'search))
                                     (bbdb-select-message))))
                 (const :tag "update existing records"
                        (lambda () (let ((bbdb-update-records-p 'update))
                                     (bbdb-select-message))))
                 (const :tag "query annotation of all messages"
                        (lambda () (let ((bbdb-update-records-p 'query))
                                     (bbdb-select-message))))
                 (const :tag "annotate all messages"
                        (lambda () (let ((bbdb-update-records-p 'create))
                                     (bbdb-select-message))))
                 (const :tag "accept messages" bbdb-accept-message)
                 (const :tag "ignore messages" bbdb-ignore-message)
                 (const :tag "select messages" bbdb-select-message)
                 (sexp  :tag "user defined function")))
(defvaralias 'bbdb/mail-update-records-p 'bbdb/message-update-records-p)



;;;###autoload
(defun bbdb-insinuate-message ()
  "Hook BBDB into Message Mode.
Do not call this in your init file.  Use `bbdb-initialize'."
  ;; Suggestions welcome: What are good keybindings for the following
  ;; commands that do not collide with existing bindings?
  ;; (define-key message-mode-map "'" 'bbdb-mua-display-recipients)
  ;; (define-key message-mode-map ";" 'bbdb-mua-edit-field-recipients)
  ;; (define-key message-mode-map "/" 'bbdb)
  (if bbdb-complete-mail
      (define-key message-mode-map "\M-\t" 'bbdb-complete-mail)))

;;;###autoload
(defun bbdb-insinuate-mail ()
  "Hook BBDB into Mail Mode.
Do not call this in your init file.  Use `bbdb-initialize'."
  ;; Suggestions welcome: What are good keybindings for the following
  ;; commands that do not collide with existing bindings?
  ;; (define-key mail-mode-map "'" 'bbdb-mua-display-recipients)
  ;; (define-key mail-mode-map ";" 'bbdb-mua-edit-field-recipients)
  ;; (define-key mail-mode-map "/" 'bbdb)
  (if bbdb-complete-mail
      (define-key mail-mode-map "\M-\t" 'bbdb-complete-mail)))

(provide 'bbdb-message)
