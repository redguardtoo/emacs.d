;;; bbdb-gnus.el --- BBDB interface to Gnus

;; Copyright (C) 1991, 1992, 1993 Jamie Zawinski <jwz@netscape.com>.
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
;;; This file contains the BBDB interface to Gnus.
;;; See the BBDB info manual for documentation.

(require 'bbdb)
(require 'bbdb-com)
(require 'bbdb-mua)
(require 'gnus)

(defcustom bbdb/gnus-update-records-p
  (lambda () (let ((bbdb-update-records-p 'query))
               (bbdb-select-message)))
  "How `bbdb-mua-update-records' processes mail addresses in Gnus.
This Gnus-specific variable is normally not used.  It is a fallback
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
  :group 'bbdb-mua-gnus
  :type '(choice (const :tag "do nothing" nil)
                 (const :tag "search for existing records"
                        (lambda () (let ((bbdb-update-records-p 'search))
                                     (bbdb-select-message))))
                 (const :tag "update existing records"
                        (lambda () (let ((bbdb-update-records-p 'update))
                                     (bbdb-select-message))))
                 (const :tag "query annotation of all messages"
                        (lambda () (let ((bbdb-update-records-p 'query))
                                     (bbdb-select-message))))
                 (const :tag "annotate (query) only new messages"
                        (if (equal "" (gnus-summary-article-mark
                                       (gnus-summary-article-number)))
                            (bbdb-select-message) 'search))
                 (const :tag "annotate all messages"
                        (lambda () (let ((bbdb-update-records-p 'create))
                                     (bbdb-select-message))))
                 (const :tag "accept messages" bbdb-accept-message)
                 (const :tag "ignore messages" bbdb-ignore-message)
                 (const :tag "select messages" bbdb-select-message)
                 (sexp  :tag "user defined")))

;;
;; Scoring
;;

(defcustom bbdb/gnus-score-field 'gnus-score
  "This variable contains the name of the BBDB field which should be
checked for a score to add to the mail addresses in the same record."
  :group 'bbdb-mua-gnus-scoring
  :type 'symbol)

(defcustom bbdb/gnus-score-default nil
  "If this is set, then every mail address in the BBDB that does not have
an associated score field will be assigned this score.  A value of nil
implies a default score of zero."
  :group 'bbdb-mua-gnus-scoring
  :type '(choice (const :tag "Do not assign default score")
                 (integer :tag "Assign this default score" 0)))

(defvar bbdb/gnus-score-default-internal nil
  "Internal variable for detecting changes to
`bbdb/gnus-score-default'.  You should not set this variable directly -
set `bbdb/gnus-score-default' instead.")

(defvar bbdb/gnus-score-alist nil
  "The text version of the scoring structure returned by
bbdb/gnus-score.  This is built automatically from the BBDB.")

(defvar bbdb/gnus-score-rebuild-alist t
  "Set to t to rebuild bbdb/gnus-score-alist on the next call to
bbdb/gnus-score.  This will be set automatically if you change a BBDB
record which contains a gnus-score field.")

(defun bbdb/gnus-score-invalidate-alist (record)
  "This function is called through `bbdb-after-change-hook',
and sets `bbdb/gnus-score-rebuild-alist' to t if the changed
record contains a gnus-score field."
  (if (bbdb-record-xfield record bbdb/gnus-score-field)
      (setq bbdb/gnus-score-rebuild-alist t)))

;;;###autoload
(defun bbdb/gnus-score (group)
  "This returns a score alist for Gnus.  A score pair will be made for
every member of the mail field in records which also have a gnus-score
field.  This allows the BBDB to serve as a supplemental global score
file, with the advantage that it can keep up with multiple and changing
addresses better than the traditionally static global scorefile."
  (list (list
         (condition-case nil
             (read (bbdb/gnus-score-as-text group))
           (error (setq bbdb/gnus-score-rebuild-alist t)
                  (message "Problem building BBDB score table.")
                  (ding) (sit-for 2)
                  nil)))))

(defun bbdb/gnus-score-as-text (group)
  "Returns a SCORE file format string built from the BBDB."
  (cond ((or (cond ((/= (or bbdb/gnus-score-default 0)
                        (or bbdb/gnus-score-default-internal 0))
                    (setq bbdb/gnus-score-default-internal
                          bbdb/gnus-score-default)
                    t))
             (not bbdb/gnus-score-alist)
             bbdb/gnus-score-rebuild-alist)
         (setq bbdb/gnus-score-rebuild-alist nil)
         (setq bbdb/gnus-score-alist
               (concat "((touched nil) (\"from\"\n"
                       (mapconcat
                        (lambda (record)
                          (let ((score (or (bbdb-record-xfield record bbdb/gnus-score-field)
                                           bbdb/gnus-score-default))
                                (mail (bbdb-record-mail record)))
                            (when (and score mail)
                              (mapconcat
                               (lambda (address)
                                 (format "(\"%s\" %s)\n" address score))
                               mail ""))))
                        (bbdb-records) "")
                       "))"))))
  bbdb/gnus-score-alist)

;;; from Brian Edmonds' gnus-bbdb.el
;;;
;;; Splitting / filing with gnus-folder
;;;
;;; To use this feature, you need to put this file somewhere in your
;;; load-path and add the following lines of code to your .gnus file:
;;;
;;; (setq nnmail-split-methods 'bbdb/gnus-split-method)
;;;
;;; You should also examine the variables defvar'd below and customize
;;; them to your taste.  They're listed roughly in descending likelihood
;;; of your wanting to change them.  Once that is done, you need to add
;;; filing information to your BBDB.  There are two fields of interest:
;;;
;;; 1. gnus-private.  This field contains the name of the group in which
;;;    mail to you from any of the addresses associated with this record
;;;    will be filed.  Also, any self-copies of mail you send any of the
;;;    same addresses will be filed here.
;;; 2. gnus-public.  This field is used to keep mail from mailing lists
;;;    out of the private mailboxes.  It should be added to a record for
;;;    the list submission address, and is formatted as follows:
;;;      "group regexp"
;;;    where group is where mail from the list should be filed, and
;;;    regexp is a regular expression which is checked against the
;;;    envelope sender (from the From_ header) to verify that this is
;;;    the copy which came from the list.  For example, the entry for
;;;    the ding mailing list might be:
;;;      "mail.emacs.ding ding-request@ifi.uio.no"
;;;    Yes, the second part *is* a regexp, so those dots may match
;;;    something other than dots.  Sue me.
;;;
;;; Note that you can also specify a gnus-private field for mailing list
;;; addresses, in which case self-copies of mail you send to the list
;;; will be filed there.  Also, the field names can be changed below if
;;; the defaults are not hip enough for you.  Lastly, if you specify a
;;; gnus-private field for your *own* BBDB record, then all self-copies
;;; of mail you send will be filed to that group.
;;;
;;; This documentation should probably be expanded and moved to a
;;; separate file, but it's late, and *I* know what I'm trying to
;;; say. :)

(defcustom bbdb/gnus-split-default-group "mail.misc"
  "If the BBDB does not indicate any group to spool a message to, it will
be spooled to this group.  If `bbdb/gnus-split-crosspost-default' is not
nil, and if the BBDB did not indicate a specific group for one or more
addresses, messages will be crossposted to this group in addition to any
group(s) which the BBDB indicated."
  :group 'bbdb-mua-gnus-splitting
  :type  'string)

(defcustom bbdb/gnus-split-nomatch-function nil
  "This function will be called after searching the BBDB if no place to
file the message could be found.  It should return a group name (or list
of group names) -- `nnmail-split-fancy' as provided with Gnus is an
excellent choice."
  :group 'bbdb-mua-gnus-splitting
  :type  'function)

(defcustom bbdb/gnus-split-myaddr-regexp
  (concat "^" (user-login-name) "$\\|^"
          (user-login-name) "@\\([-a-z0-9]+\\.\\)*"
          (or (message-make-domain) (system-name) "") "$")
  "This regular expression should match your address as found in the
From header of your mail."
  :group 'bbdb-mua-gnus-splitting
  :type  'string)

(defcustom bbdb/gnus-split-crosspost-default nil
  "If this variable is not nil, then if the BBDB could not identify a
group for every mail address, messages will be filed in
`bbdb/gnus-split-default-group' in addition to any group(s) which the BBDB
identified."
  :group 'bbdb-mua-gnus-splitting
  :type  'boolean)

(defcustom bbdb/gnus-split-private-field 'gnus-private
  "This variable is used to determine the xfield to reference to find the
associated group when saving private mail for a mail address known to
the BBDB.  The value of the xfield should be the name of a mail group."
  :group 'bbdb-mua-gnus-splitting
  :type  'string)

(defcustom bbdb/gnus-split-public-field 'gnus-public
  "This variable is used to determine the xfield to reference to find the
associated group when saving non-private mail (received from a mailing
list) for a mail address known to the BBDB.  The value of the xfield
should be the name of a mail group, followed by a space, and a regular
expression to match on the envelope sender to verify that this mail came
from the list in question."
  :group 'bbdb-mua-gnus-splitting
  :type  'string)

;; The split function works by assigning one of four spooling priorities
;; to each group that is associated with an address in the message.  The
;; priorities are assigned as follows:
;;
;; 0. This priority is assigned when crosspost-default is nil to To/Cc
;;    addresses which have no private group defined in the BBDB.  If the
;;    user's own address has no private group defined, then it will
;;    always be given this priority.
;; 1. This priority is assigned to To/Cc addresses which have a private
;;    group defined in the BBDB.  If crosspost-default is not nil, then
;;    To/Cc addresses which have no private group will also be assigned
;;    this priority.  This is also assigned to the user's own address in
;;    the From position if a private group is defined for it.
;; 2. This priority is assigned to From addresses which have a private
;;    group defined in the BBDB, except for the user's own address as
;;    described under priorities 0 and 1.
;; 3. This priority is assigned to To/Cc addresses which have a public
;;    group defined in the BBDB, and whose associated regular expression
;;    matches the envelope sender (found in the header From_).
;;
;; The split function evaluates the spool priority for each address in
;; the headers of the message, and returns as a list all the groups
;; associated with the addresses which share the highest calculated
;; priority.

;;;###autoload
(defun bbdb/gnus-split-method ()
  "This function expects to be called in a buffer which contains a mail
message to be spooled, and the buffer should be narrowed to the message
headers.  It returns a list of groups to which the message should be
spooled, using the addresses in the headers and information from BBDB."
  (let ((prq (list (list 0) (list 1) (list 2) (list 3))))
    ;; the From: header is special
    (let* ((hdr (or (mail-fetch-field "resent-from")
                    (mail-fetch-field "from")
                    (user-login-name)))
           (rv (bbdb/gnus-split-to-group hdr t)))
      (setcdr (nth (cdr rv) prq) (list (car rv))))
    ;; do the rest of the headers
    (let ((hdr (or (concat (or (mail-fetch-field "resent-to" nil t)
                               (mail-fetch-field "to" nil t))
                           ", "
                           (mail-fetch-field "cc" nil t)
                           ", "
                           (mail-fetch-field "apparently-to" nil t))
                   "")))
      (dolist (address (bbdb-extract-address-components hdr t))
        (let* ((rv (bbdb/gnus-split-to-group address))
               (pr (nth (cdr rv) prq)))
          (unless (member-ignore-case (car rv) pr)
            (setcdr pr (cons (car rv) (cdr pr)))))))
    ;; find the highest non-empty queue
    (setq prq (reverse prq))
    (while (and prq (not (cdr (car prq)))) (setq prq (cdr prq)))
    ;; and return...
    (if (not (or (not (cdr (car prq)))
                 (and (equal (cdr (car prq)) (list bbdb/gnus-split-default-group))
                      (symbolp bbdb/gnus-split-nomatch-function)
                      (fboundp bbdb/gnus-split-nomatch-function))))
        (cdr (car prq))
      (goto-char (point-min))
      (funcall bbdb/gnus-split-nomatch-function))))

(defun bbdb/gnus-split-to-group (address &optional source)
  "This function is called from `bbdb/gnus-split-method' in order to
determine the group and spooling priority for a single address."
  (condition-case nil
      (let* ((tmp (bbdb-extract-address-components address))
             (mail (cadr tmp))
             (record (car (bbdb-message-search (car tmp) mail)))
             public private rgx)
        (when record
          (setq private (bbdb-record-xfield record bbdb/gnus-split-private-field)
                public (bbdb-record-xfield record bbdb/gnus-split-public-field))
          (if (and public (not source) (string-match "^\\([^ ]+\\) \\(.*\\)$" public))
              (setq rgx (substring public (match-beginning 2) (match-end 2))
                    public (substring public (match-beginning 1) (match-end 1)))
            (setq public nil)))
        (cond
         ((and rgx public
               (goto-char (point-min))
               (re-search-forward "^From: \\([^ \n]+\\)[ \n]" nil t)
               (string-match rgx (buffer-substring (match-beginning 1)
                                                   (match-end 1))))
          (cons public 3))
         (private
          (cons private
                (- 1 (if source -1 0)
                   (if (string-match bbdb/gnus-split-myaddr-regexp mail) 1 0))))
         (t
          (cons bbdb/gnus-split-default-group
                (cond ((string-match bbdb/gnus-split-myaddr-regexp mail) 0)
                      (source 2)
                      (bbdb/gnus-split-crosspost-default 1)
                      (t 0))))))
    (error (cons bbdb/gnus-split-default-group 0))))

;;
;; Imap support (Uwe Brauer)
;;
(defun bbdb/gnus-nnimap-folder-list-from-bbdb ()
  "Return a list of \( \"From\" mail-regexp imap-folder-name\) tuples
based on the contents of the bbdb.

The folder-name is the value of the 'imap attribute of the BBDB record;
the mail-regexp consists of all the mail addresses for the BBDB record
concatenated with OR.  Records without an 'imap attribute are ignored.

Here  is an example of a relevant BBDB record:

Uwe Brauer
           mail: oub@mat.ucm.es
           imap: testimap

This function uses `regexp-opt' to generate the mail-regexp which automatically
`regexp-quote's its arguments.  Please note: in order that this will work
with the `nnimap-split-fancy' method you have to use macros, that is your setting
will look like:

\(setq nnimap-split-rule  'nnimap-split-fancy
       nnimap-split-inbox \"INBOX\"
       nnimap-split-fancy
       `\(| ,@\(bbdb/gnus-nnimap-folder-list-from-bbdb\)
            ... \)\)

Note that `\( is the backquote, NOT the quote '\(."

  (let (;; the value of the 'imap attribute of a bbdb record
        folder-attr
        ;; a regexp matching all the mail addresses from a bbdb record
        mail-regexp
        ;; the list of (folder mail) tuples to return
        new-elmnt-list)
    ;; Loop over BBDB records.  If an imap attribute exists for
    ;; the record, generate a regexp matching all the mail addresses
    ;; and add a tuple (folder mail-regexp) to the new-elmnt-list
    (dolist (record (bbdb-records))
      (when (setq folder-attr (bbdb-record-xfield record 'imap))
        (setq mail-regexp (regexp-opt (mapcar 'downcase
                                              (bbdb-record-mail record))))
        (unless (string= "" mail-regexp)
          (push (list "From" mail-regexp folder-attr)
                new-elmnt-list))))
    new-elmnt-list))

;;
;; Insinuation
;;

;;;###autoload
(defun bbdb-insinuate-gnus ()
  "Hook BBDB into Gnus.
Do not call this in your init file.  Use `bbdb-initialize'."
  ;; `bbdb-mua-display-sender' fails in *Article* buffers, where
  ;; `gnus-article-read-summary-keys' provides an additional wrapper
  ;; that restores the window configuration.
  (define-key gnus-summary-mode-map ":" 'bbdb-mua-display-sender)
  (define-key gnus-article-mode-map ":" 'bbdb-mua-display-sender)
  ;; For `bbdb-mua-edit-field-sender' it is probably OK if
  ;;`gnus-article-read-summary-keys' restores the window configuration.
  (define-key gnus-summary-mode-map ";" 'bbdb-mua-edit-field-sender)
  (define-key gnus-article-mode-map ";" 'bbdb-mua-edit-field-sender)
  ;; Do we need keybindings for more commands?  Suggestions welcome.
  ;; (define-key gnus-summary-mode-map ":" 'bbdb-mua-display-records)
  ;; (define-key gnus-summary-mode-map "'" 'bbdb-mua-display-recipients)
  ;; (define-key gnus-summary-mode-map ";" 'bbdb-mua-edit-field-recipients)

  ;; Set up user field for use in `gnus-summary-line-format'
  ;; (1) Big solution: use whole name
  (if bbdb-mua-summary-unify-format-letter
      (fset (intern (concat "gnus-user-format-function-"
                            bbdb-mua-summary-unify-format-letter))
            (lambda (header)
              (bbdb-mua-summary-unify (mail-header-from header)))))

  ;; (2) Small solution: a mark for messages whos sender is in BBDB.
  (if bbdb-mua-summary-mark-format-letter
      (fset (intern (concat "gnus-user-format-function-"
                            bbdb-mua-summary-mark-format-letter))
            (lambda (header)
              (bbdb-mua-summary-mark (mail-header-from header)))))

  ;; Scoring
  (add-hook 'bbdb-after-change-hook 'bbdb/gnus-score-invalidate-alist))
  ;; (setq gnus-score-find-score-files-function
  ;;  (if (boundp 'gnus-score-find-score-files-function)
  ;;      (cond ((functionp gnus-score-find-score-files-function)
  ;;             (list gnus-score-find-score-files-function 'bbdb/gnus-score))
  ;;            ((listp gnus-score-find-score-files-function)
  ;;             (append gnus-score-find-score-files-function 'bbdb/gnus-score))
  ;;            (t 'bbdb/gnus-score))
  ;;    'bbdb/gnus-score))

(provide 'bbdb-gnus)
