;;; db.el --- A database for EmacsLisp  -*- lexical-binding: t -*-

;; Copyright (C) 2012  Nic Ferrier

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;; Maintainer: Nic Ferrier <nferrier@ferrier.me.uk>
;; Keywords: data, lisp
;; Package-Version: 20140421.1411
;; Created: 23rd September 2012
;; Package-Requires: ((kv "0.0.11"))
;; Version: 0.0.6

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

;; This is a simple database interface and implementation.
;;
;; It should be possible to specify any kind of key/value database
;; with this interface.
;;
;; The supplied implementation is an Emacs hash-table implementation
;; backed with serializing objects.  It is NOT intended for anything
;; other than very simple use cases and will not scale very well at
;; all.

;; However, other implementations (mongodb, redis or PostgreSQL
;; hstore) would be easy to implement and fit in here.


;;; Code:

(eval-when-compile
  (require 'cl))
(require 'kv)

(defun db/make-type-store ()
  "Make the type store."
  (make-hash-table :test 'eq))

(defvar db/types (db/make-type-store)
  "Hash of database type ids against funcs?")

(defun* db-make (reference)
  "Make a DB based on the REFERENCE."
  (if (and (listp reference)
           (eq 'db-hash (car reference)))
      ;; this should be part of what we find when we look it up?
      (db-hash reference)
      ;; Otherwise look it up...
      (let ((db-func (gethash (car reference) db/types)))
        (if (functionp db-func)
            (funcall db-func reference)
            ;; there should be a specific db error
            (error "no such database implementation")))))

(defun db-get (key db)
  "Get the value from the DB with the KEY."
  (funcall (plist-get db :get) key db))

(defun db-put (key value db)
  "Put a new VALUE into the DB with the specified KEY.

Return the VALUE as it has been put into the DB."
  (funcall (plist-get db :put) key value db))

(defun db-map (func db &optional query filter)
  "Call FUNC for every record in DB optionally QUERY filter.

QUERY, if specified, should be a list of query terms as specified
by `kvquery->func'.

FUNC should take 2 arguments:

  KEY DB-VALUE

where the DB-VALUE is whatever the DB has attached to the
specified KEY.

This returns an alist of the KEY and the value the function
returned.  If FILTER is `t' then only pairs with a value are
returned."
  (let (retlist)
    (funcall (plist-get db :map)
             (lambda (key value)
               (when key
                 (setq
                  retlist
                  (cons
                   (funcall func key value)
                   retlist))))
             db query)
    (if filter
        (loop for p in retlist
           if (cdr p)
           collect p)
        retlist)))

(defun db-query (db query)
  "Do QUERY on DB and return the result.

The query is as specified by `kvquery->func'.

This is `db-map' with an identity function."
  (db-map 'kvidentity db query))


;;; Generic utility functions

(defun db-copy (src-db dest-db)
  "Copy the data from SRC-DB into DEST-DB."
  (db-map (lambda (key value)
            ;;(unless (db-get key dest-db)
            (progn
              (db-put key value dest-db))) src-db))


;;; Hash implementation

(defun db-hash (reference)
  "Make a db-hash database.

REFERENCE comes from the call to `db-make' and should
include a `:filename' key arg to point to a file:

  '(db-hash :filename \"/var/local/db/auth-db\")

If the filename exists then it is loaded into the database.

:from-filename let's you specify the source location the db will
be read from.  The first version of the hash db tied databases to
specific filenames so you could not easily load a db from one
file location into another.  This has been fixed but if you need
to work with a previous version's database you can use
the :from-filename to specify where the db file was located."
  (let* ((db-plist (cdr reference))
         (filename (plist-get db-plist :filename))
         (from-filename (plist-get db-plist :from-filename))
         (db (list
              :db (make-hash-table :test 'equal)
              :get 'db-hash-get
              :put 'db-hash-put
              :map 'db-hash-map
              :query-equal (or
                            (plist-get db-plist :query-equal)
                            'kvassoq=)
              :filename filename
              :from-filename from-filename)))
    (when (and filename
               (file-exists-p (concat filename ".elc")))
      (db-hash/read db))
    ;; Return the database
    db))

(defun db-hash/read (db)
  "Loads the DB."
  (let* ((filename (plist-get db :filename))
         (source-filename ; this is needed for the crappy old way of
                          ; saving with a unique filename based symbol
          (or
           (plist-get db :from-filename)
           filename)))
    (when filename
      (plist-put
       db :db
       (catch 'return
         (progn
           ;; The new saving mechanism causes that throw
           (load-file (concat filename ".elc"))
           ;; the old way used unique symbols
           (symbol-value (intern source-filename))))))))

(defvar db-hash-do-not-save nil
  "If `t' then do not save the database.

This is very useful for testing.")

(defun db-hash/save (db)
  "Saves the DB."
  (unless db-hash-do-not-save
    (let ((filename (plist-get db :filename)))
      (when filename
        ;; Make the parent directory for the db if it doesn't exist
        (let ((dir (file-name-directory filename)))
          (unless (file-exists-p dir)
            (make-directory dir t)))
        ;; Now store the data
        (with-temp-file (concat filename ".el")
          (erase-buffer)
          (let ((fmt-obj (format
                          "(throw 'return %S)"
                          (plist-get db :db))))
            (insert fmt-obj)))
        ;; And compile it and delete the original
        (byte-compile-file (concat filename ".el"))
        (delete-file (concat filename ".el"))))))


(defun db-hash-get (key db)
  (let ((v (gethash key (plist-get db :db))))
    v))

(defun db-hash-map (func db &optional query)
  "Run FUNC for every value in DB.

The QUERY is ignored.  We never filter."
  (let* ((equal-fn (plist-get db :query-equal))
         (filterfn (if query
                       (kvquery->func query :equal-func equal-fn)
                       'identity)))
    (maphash
     (lambda (key value)
       (when (funcall filterfn value)
         (funcall func key value)))
     (plist-get db :db))))

(defun db-hash-put (key value db)
  (let ((v (puthash key value (plist-get db :db))))
    ;; Instead of saving every time we could simply signal an update
    ;; and have a timer do the actual save.
    (db-hash/save db)
    v))

(defvar db/hash-clear-history nil
  "History variable for completing read.")

(defun db-hash-clear (db)
  "Clear the specified DB (a hash-db)."
  (interactive
   (list (symbol-value
          (intern
           (completing-read
            "Database: "
            obarray
            nil
            't
            nil
            'db/hash-clear-history)))))
  (clrhash (plist-get db :db))
  (if (file-exists-p (plist-get db :filename))
      (delete-file (plist-get db :filename))))


;; Filter db - let's you filter another db

(defun db-filter-get (key db)
  (let* ((filter-func (plist-get db :filter))
         (origin (plist-get db :source))
         (value (db-get key origin)))
    (funcall filter-func key value)))

(defun db-filter-put (key value db)
  (let* ((filter-func (plist-get db :filter))
         (origin (plist-get db :source))
         (ret (db-put key value origin)))
    (funcall filter-func key ret)))

(defun db-filter-map (key db &optional query)
  (let* ((filter-func (plist-get db :filter))
         (origin (plist-get db :source)))
    (mapcar
     filter-func
     (db-map key origin query))))

(defun db-filter (reference)
  "Make a database object that is a filter around another.

The reference should look something like:

 '(db-filter
    :source (db-hash :filename ....)
    :filter (lambda (value) ...)

The `:filter' function takes 2 arguments: KEY and VALUE with
VALUE being the returned value from the `:source' database."
  (let* ((ref-plist (cdr reference))
         (db (list
              :get 'db-filter-get
              :put 'db-filter-put
              :map 'db-filter-map
              :filter (plist-get ref-plist :filter)
              :source (plist-get ref-plist :source))))
    db))

(puthash 'db-filter 'db-filter db/types)

(defun db-change-timestamp ()
  "Place a timestamp in the kill-ring for a db change log."
  (interactive)
  (kill-new (format-time-string "\"%Y%M%d%H%M%S%N\""(current-time))))

(defmacro db-change (change-db timestamp &rest change)
  "Do CHANGE and make a record in the CHANGE-DB with TIMESTAMP."
  (declare (indent 2))
  (let ((cdbv (make-symbol "cdbv"))
        (tsv (make-symbol "tsv")))
  `(let ((,cdbv ,change-db)
         (,tsv ,timestamp))
     (unless (db-get ,tsv ,cdbv)
       (progn
         (progn ,@change)
         (db-put ,tsv (list (cons "timestamp" ,tsv)) ,cdbv))))))

(provide 'db)

;;; db.el ends here
