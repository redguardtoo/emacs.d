;;; bbdb-snarf.el -- convert free-form text to BBDB records

;; Copyright (C) 1997 John Heidemann <johnh@isi.edu>
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

;;; The commands `bbdb-snarf', `bbdb-snarf-yank' and `bbdb-snarf-paragraph'
;;; create BBDB records by picking the name, addresses, phones, etc.
;;; out of a (buffer) string.  Things are recognized by context (e.g., URLs
;;; start with http:// or www.).  See `bbdb-snarf-rule-alist' for details.
;;;
;;; Currently this code is much biased towards the US.  Hopefully,
;;; the concept of customizable rules allows you to develop new rules
;;; suitable for other parts of the world, too.  Please let me know
;;; if you get such rules working.
;;; `mail' is a simple rule that can pick a single address from, say,
;;; a long list of mail addresses in a message.
;;;
;;; RW: `bbdb-snarf' is an interesting proof of concept.  Yet I find
;;; its snarfing algorithms too simplistic to be useful in real life.
;;; How can this possibly be improved?  Suggestions welcome.

(require 'bbdb-com)

(defcustom bbdb-snarf-rule-alist
  '((us bbdb-snarf-surrounding-space bbdb-snarf-phone-nanp
        bbdb-snarf-url bbdb-snarf-mail bbdb-snarf-empty-lines
        bbdb-snarf-name bbdb-snarf-address-us bbdb-snarf-empty-lines
        bbdb-snarf-notes bbdb-snarf-name-mail)
    (mail bbdb-snarf-mail-address))
  "Alist of rules for snarfing.
Each rule is of the form (KEY FUNCTION FUNCTION ...).
The symbol KEY identifies the rule, see also `bbdb-snarf-rule-default'.

Snarfing is a cumulative process.  The text is copied to a snarf buffer
that becomes current during snarfing.
Each FUNCTION is called with one arg, the RECORD we are snarfing,
and with point at the beginning of the snarf buffer.  FUNCTION should populate
the fields of RECORD.  It may delete the part of the snarf buffer
that it has processed so that the remaining FUNCTIONs operate only
on those parts that were not yet snarfed.  The order of the FUNCTION calls
in a rule is then crucial.
Unlike other parts of BBDB, FUNCTIONs need not update the cache and
hash table for RECORD which is done at the end by `bbdb-snarf'."
  :group 'bbdb-utilities-snarf
  :type '(repeat (cons (symbol :tag "Key")
                       (repeat (function :tag "Snarf function")))))

(defcustom bbdb-snarf-rule-default 'us
  "Default rule for snarfing."
  :group 'bbdb-utilities-snarf
  :type 'symbol)

(defcustom bbdb-snarf-name-regexp
   "^[ \t'\"]*\\([- .,[:word:]]*[[:word:]]\\)"
  "Regexp matching a name.  Case is ignored.
The first subexpression becomes the name."
  :group 'bbdb-utilities-snarf
  :type 'regexp)

(defcustom bbdb-snarf-phone-nanp-regexp
  (concat "\\(([2-9][0-9][0-9])[-. ]?\\|[2-9][0-9][0-9][-. ]\\)?"
          "[0-9][0-9][0-9][-. ][0-9][0-9][0-9][0-9]"
          "\\( *\\(x\\|ext\\.?\\) *[0-9]+\\)?")
  "Regexp matching a NANP phone number.  Case is ignored.
NANP is the North American Numbering Plan used in North and Central America."
  :group 'bbdb-utilities-snarf
  :type 'regexp)

(defcustom bbdb-snarf-postcode-us-regexp
  (concat "\\<[0-9][0-9][0-9][0-9][0-9]"
          "\\(-[0-9][0-9][0-9][0-9]\\)?"
          "\\>$")
  "Regexp matching US postcodes."
  :group 'bbdb-utilities-snarf
  :type 'regexp)

(defcustom bbdb-snarf-default-label-alist
  '((phone . "work") (address . "work"))
  "Default labels for snarfing.
This is an alist where each element is a cons pair (FIELD . LABEL).
The symbol FIELD denotes a record field like `phone' or `address'.
The string LABEL denotes the default label for FIELD."
  :group 'bbdb-utilities-snarf
  :type '(repeat (cons (symbol :tag "Field")
                       (string :tag "Label"))))

(defcustom bbdb-snarf-url 'url
  "What xfield BBDB should use for URLs, or nil to not snarf URLs."
  :group 'bbdb-utilities-snarf
  :type 'symbol)

(defcustom bbdb-snarf-url-regexp  "\\(http://\\|www\.\\)[^ \t\n]+"
  "Regexp matching a URL.  Case is ignored."
  :group 'bbdb-utilities-snarf
  :type 'regexp)

(defun bbdb-snarf-surrounding-space (record)
  "Discard beginning and trailing space when snarfing RECORD."
  (while (re-search-forward "^[ \t]+" nil t)
    (replace-match ""))
  (goto-char (point-min))
  (while (re-search-forward "\\s-+$" nil t)
    (replace-match "")))

(defun bbdb-snarf-empty-lines (record)
  "Discard empty lines when snarfing RECORD."
  (while (re-search-forward "^[ \t]*\n" nil t)
    (replace-match "")))

(defun bbdb-snarf-name (record)
  "Snarf name for RECORD."
  (if (and (not (bbdb-record-lastname record))
           (let ((case-fold-search t))
             (re-search-forward bbdb-snarf-name-regexp nil t)))
      (let ((name (match-string 1)))
        (replace-match "")
        (setq name (bbdb-divide-name name))
        (bbdb-record-set-firstname record (car name))
        (bbdb-record-set-lastname record (cdr name)))))

(defun bbdb-snarf-name-mail (record)
  "Snarf name from mail address for RECORD."
  (let ((name (bbdb-record-lastname record)))
    (when (and (not name)
               (bbdb-record-mail record)
               (setq name (car (bbdb-extract-address-components
                                (car (bbdb-record-mail record)))))
               (setq name (bbdb-divide-name name)))
      (bbdb-record-set-firstname record (car name))
      (bbdb-record-set-lastname record (cadr name)))))

(defun bbdb-snarf-mail-address (record)
  "Snarf name and mail address for RECORD."
  ;; The voodoo of `mail-extract-address-components' makes
  ;; the following quite powerful.  If this function is used as part of
  ;; a more complex rule, the buffer should be narrowed appropriately.
  (let* ((data (bbdb-extract-address-components (buffer-string)))
         (name (and (car data) (bbdb-divide-name (car data)))))
    (bbdb-record-set-firstname record (car name))
    (bbdb-record-set-lastname  record (cdr name))
    (bbdb-record-set-mail record (list (cadr data)))
    (delete-region (point-min) (point-max))))

(defun bbdb-snarf-label (field)
  "Extract the label before point, or return default label for FIELD."
  (if (looking-back "[\n,:]\\([^\n,:]+\\):[ \t]*")
      (prog1 (match-string 1)
        (delete-region (match-beginning 1) (match-end 0)))
    (cdr (assq field bbdb-snarf-default-label-alist))))

(defun bbdb-snarf-phone-nanp (record)
  "Snarf NANP Phone Numbers for RECORD.
NANP is the North American Numbering Plan used in North and Central America."
  (let ((case-fold-search t) phones)
    (while (re-search-forward bbdb-snarf-phone-nanp-regexp nil t)
      (let ((begin (match-beginning 0))
            (end (match-end 0)))
        (goto-char begin)
        (forward-char -1)
        (if (looking-at "[0-9A-Z]") ;; not really a phone number
            (goto-char end)
          (let ((number (bbdb-parse-phone (buffer-substring begin end))))
            (delete-region begin end)
            (push (vconcat (list (bbdb-snarf-label 'phone)) number)
                  phones)))))
    (bbdb-record-set-phone record (nconc (bbdb-record-phone record) phones))))

(defun bbdb-snarf-mail (record)
  "Snarf mail addresses for RECORD."
  (let (mails)
    (while (re-search-forward "[^ \t\n<]+@[^ \t\n>]+" nil t)
      (push (match-string 0) mails)
      (replace-match ""))
    (bbdb-record-set-mail record (nconc (bbdb-record-mail record) mails))))

(defun bbdb-snarf-streets (address)
  "Snarf streets for ADDRESS.  This assumes a narrowed region."
  (bbdb-address-set-streets address (bbdb-split "\n" (buffer-string)))
  (delete-region (point-min) (point-max)))

(defun bbdb-snarf-address-us (record)
  "Snarf a US address for RECORD."
  (let ((address (make-vector bbdb-address-length nil)))
    (cond ((re-search-forward bbdb-snarf-postcode-us-regexp nil t)
           ;; Streets, City, State Postcode
           (save-restriction
             (narrow-to-region (point-min) (match-end 0))
             ;; Postcode
             (goto-char (match-beginning 0))
             (bbdb-address-set-postcode address
              (bbdb-parse-postcode (match-string 0)))
             ;; State
             (skip-chars-backward " \t")
             (let ((pos (point)))
               (skip-chars-backward "^ \t,")
               (bbdb-address-set-state address (buffer-substring (point) pos)))
             ;; City
             (skip-chars-backward " \t,")
             (let ((pos (point)))
               (beginning-of-line)
               (bbdb-address-set-city address (buffer-substring (point) pos)))
             ;; Toss it
             (forward-char -1)
             (delete-region (point) (point-max))
             ;; Streets
             (goto-char (point-min))
             (bbdb-snarf-streets address)))
          ;; Try for just Streets, City, State
          ((let (case-fold-search)
             (re-search-forward "^\\(.*\\), \\([A-Z][A-Za-z]\\)$" nil t))
           (bbdb-address-set-city address (match-string 1))
           (bbdb-address-set-state address (match-string 2))
           (replace-match "")
           (save-restriction
             (narrow-to-region (point-min) (match-beginning 0))
             (goto-char (point-min))
             (bbdb-snarf-streets address))))
    ;; Fixme: There are no labels anymore.  `bbdb-snarf-streets' snarfed
    ;; everything that was left!
    (bbdb-address-set-label address (bbdb-snarf-label 'address))
    (bbdb-record-set-address record
                             (nconc (bbdb-record-address record)
                                    (list address)))))

(defun bbdb-snarf-url (record)
  "Snarf URL for RECORD."
  (when (and bbdb-snarf-url
             (let ((case-fold-search t))
               (re-search-forward bbdb-snarf-url-regexp nil t)))
    (bbdb-record-set-xfields
     record
     (nconc (bbdb-record-xfields record)
            (list (cons bbdb-snarf-url (match-string 0)))))
    (replace-match "")))

(defun bbdb-snarf-notes (record)
  "Snarf notes for RECORD."
  (when (/= (point-min) (point-max))
    (bbdb-record-set-xfields
     record
     (nconc (bbdb-record-xfields record)
            (list (cons bbdb-default-xfield (buffer-string)))))
    (erase-buffer)))

(defsubst bbdb-snarf-rule-interactive ()
  "Read snarf rule interactively."
  (intern
   (completing-read
    (format "Rule: (default `%s') " bbdb-snarf-rule-default)
    bbdb-snarf-rule-alist nil t nil nil
    (symbol-name bbdb-snarf-rule-default))))

;;;###autoload
(defun bbdb-snarf-paragraph (pos &optional rule)
  "Snarf BBDB record from paragraph around position POS using RULE.
The paragraph is the one that contains POS or follows POS.
Interactively POS is the position of point.
RULE defaults to `bbdb-snarf-rule-default'.
See `bbdb-snarf-rule-alist' for details."
  (interactive (list (point) (bbdb-snarf-rule-interactive)))
  (bbdb-snarf (save-excursion
                (goto-char pos)
                ;; similar to `mark-paragraph'
                (let ((end (progn (forward-paragraph 1) (point))))
                  (buffer-substring-no-properties
                   (progn (backward-paragraph 1) (point))
                   end)))
              rule))

;;;###autoload
(defun bbdb-snarf-yank (&optional rule)
  "Snarf a BBDB record from latest kill using RULE.
The latest kill may also be a window system selection, see `current-kill'.
RULE defaults to `bbdb-snarf-rule-default'.
See `bbdb-snarf-rule-alist' for details."
  (interactive (list (bbdb-snarf-rule-interactive)))
  (bbdb-snarf (current-kill 0) rule))

;;;###autoload
(defun bbdb-snarf (string &optional rule)
  "Snarf a BBDB record in STRING using RULE.  Display and return this record.
Interactively, STRING is the current region.
RULE defaults to `bbdb-snarf-rule-default'.
See `bbdb-snarf-rule-alist' for details."
  (interactive
   (list (buffer-substring-no-properties (region-beginning) (region-end))
         (bbdb-snarf-rule-interactive)))

  (bbdb-editable)
  (let ((record (bbdb-empty-record)))
    (with-current-buffer (get-buffer-create " *BBDB Snarf*")
      (erase-buffer)
      (insert (substring-no-properties string))
      (mapc (lambda (fun)
              (goto-char (point-min))
              (funcall fun record))
            (cdr (assq (or rule bbdb-snarf-rule-default)
                       bbdb-snarf-rule-alist))))
    (let ((old-record (car (bbdb-message-search
                            (bbdb-concat 'name-first-last
                                         (bbdb-record-firstname record)
                                         (bbdb-record-lastname record))
                            (car (bbdb-record-mail record))))))
      ;; Install RECORD after searching for OLD-RECORD
      (bbdb-change-record record t t)
      (if old-record (bbdb-merge-records old-record record)))
    (bbdb-display-records (list record))
    record))

;; Some test cases
;;
;; another test person
;; 1234 Gridley St.
;; Los Angeles, CA 91342
;; 555-1212
;; test@person.net
;; http://www.foo.bar/
;; other stuff about this person
;;
;; test person
;; 1234 Gridley St.
;; St. Los Angeles, CA 91342-1234
;; 555-1212
;; test@person.net
;;
;; x test person
;; 1234 Gridley St.
;; Los Angeles, California 91342-1234
;; work: 555-1212
;; home: 555-1213
;; test@person.net
;;
;; y test person
;; 1234 Gridley St.
;; Los Angeles, CA
;; 555-1212
;; test@person.net

(provide 'bbdb-snarf)
