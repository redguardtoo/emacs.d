;;; fakir.el --- fakeing bits of Emacs -*- lexical-binding: t -*-
;; Copyright (C) 2012  Nic Ferrier

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;; Maintainer: Nic Ferrier <nferrier@ferrier.me.uk>
;; URL: http://github.com/nicferrier/emacs-fakir
;; Package-Version: 20140729.952
;; Created: 17th March 2012
;; Version: 0.1.9
;; Keywords: lisp, tools
;; Package-Requires: ((noflet "0.0.8")(dash "1.3.2")(kv "0.0.19"))

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

;;; Source code
;;
;; fakir's code can be found here:
;;   http://github.com/nicferrier/fakir

;;; Style note
;;
;; This codes uses the Emacs style of:
;;
;;    fakir--private-function
;;
;; for private functions and macros.

;;; Commentary:
;;
;; This is a collection of tools to make testing Emacs core functions
;; easier.

;;; Code:

(require 'ert)
(require 'dash)
(require 'noflet)
(require 'kv)
(eval-when-compile (require 'cl))


(defun fakir-make-unix-socket (&optional name)
  "Make a unix socket server process optionally based on NAME.

Returns a list of the processes socket file and the process object."
  (let* ((socket-file
          (concat "/tmp/" (apply 'make-temp-name
                                 (list (or name "fakir-make-unix-socket")))))
         (myproc (make-network-process
                  :name socket-file
                  :family 'local :server t
                  :service socket-file)))
    (list socket-file myproc)))

(defmacro* fakir-with-unix-socket ((socket-sym &optional socket-name) &rest body)
  "Execute BODY with a Unix socket server bound to SOCKET-SYM.

Optionally the socket is created with SOCKET-NAME which means
that the file used to back the socket is named after SOCKET-NAME.

The socket process is closed on completion and the associated
file is deleted."
  (declare (indent 1))
  (let ((spv (make-symbol "spv"))
        (sockfilev (make-symbol "sockfilev")))
    `(let* ((,spv (fakir-make-unix-socket ,socket-name))
            (,sockfilev (car ,spv))
            (,socket-sym (cadr ,spv)))
       (unwind-protect
            (progn
              ,@body)
         (delete-process ,socket-sym)
         (delete-file ,sockfilev)))))

(defmacro fakir-with-file-buffer (buffer-var &rest body)
  "Make a buffer visiting a file and assign it to BUFFER-VAR.

The file only exists for the scope of the macro.  Both the file
and the buffer visiting it are destroyed when the scope exits."
  (declare (indent 1))
  (let ((filev (make-symbol "filev")))
    `(let* ((,filev (make-temp-file  "filebuf"))
            (,buffer-var (find-file-noselect ,filev)))
       (unwind-protect
            (progn ,@body)
         (with-current-buffer ,buffer-var
           (set-buffer-modified-p nil))
         (kill-buffer ,buffer-var)
         (delete-file ,filev)))))

;; Mocking processes

(defvar fakir-mock-process-require-specified-buffer nil
  "Tell `fakir-mock-process' that you require a buffer to be set.

This is used, for example, to make `elnode--filter' testing work
properly. Normally, tests do not need to set the process-buffer
directly, they can just expect it to be there. `elnode--filter',
though, needs to set the process-buffer to work properly.")


(defun fakir/make-hash-table (alist) ; possible redundant now.
  "Make a hash table from the ALIST.

The ALIST looks like a let-list."
  (let ((bindings (make-hash-table :test 'equal)))
    (loop for f in (append
                    (list (list :fakir-mock-process t))
                    alist)
       do
         (cond
           ((and f (listp f))
            (puthash (car f) (cadr f) bindings))
           (t
            (puthash f nil bindings))))
    bindings))

(defun fakir/get-or-create-buf (pvbuf pv-alist &optional specified-buf)
  "Special get or create to support the process mocking.

PVBUF is a, possibly existing, buffer reference.  If nil then we
create the buffer.

PV-ALIST is an alist of properties, possibly containing the
`:buffer' property which specifies a string to be used as the
content of the buffer.

SPECIFIED-BUF is an optional buffer to use instead of a dummy
created one."
  (if (bufferp pvbuf)
      pvbuf
    (setq pvbuf
    (if fakir-mock-process-require-specified-buffer
        (if (bufferp specified-buf)
      specified-buf
    nil)
      (or specified-buf
    (get-buffer-create
     (generate-new-buffer-name
      "* fakir mock proc buf *")))))
    ;; If we've got a buffer value then insert it.
    (when (kva :buffer pv-alist)
      (with-current-buffer pvbuf
  (insert (kva :buffer pv-alist))))
    pvbuf))


(defmacro fakir-mock-proc-properties (process-obj &rest body)
  "Mock process property list functions.

Within BODY the functions `process-get', `process-put' and
`process-plist' and `set-process-plist' are all mocked to use a
hashtable if the process passed to them is `eq' to PROCESS-OBJ."
  (declare (indent 1)
           (debug (sexp &rest form)))
  (let ((proc-plist (make-symbol "procpropsv")))
    `(let (,proc-plist)
       (macrolet ((or-args (form &rest args)
                    `(if (eq proc ,,process-obj)
                         ,form
                         (apply this-fn ,@args))))
         (noflet ((process-get (proc name)
                    (or-args (plist-get ,proc-plist name) proc name))
                  (process-put (proc name value)
                    (or-args
                     (if ,proc-plist
                         (plist-put ,proc-plist name value)
                         (setq ,proc-plist (list name value)))
                     proc name value))
                  (process-plist (proc)
                    (or-args ,proc-plist proc))
                  (set-process-plist (proc props)
                    (or-args (setq ,proc-plist props) proc props)))
           ,@body)))))

(defun fakir/let-bindings->alist (bindings)
  "Turn let like BINDINGS into an alist.

Makes sure the resulting alist has `consed' pairs rather than
lists.

Generally useful macro helper should be elsewhere."
  (loop for p in bindings
     collect
       (if (and p (listp p))
           (list 'cons `(quote ,(car p)) (cadr p))
           (list 'cons `,p nil))))

(defmacro fakir-mock-process (process-symbol process-bindings &rest body)
  "Allow easier testing by mocking the process functions.

For example:

 (fakir-mock-process :fake
      (:elnode-http-params
       (:elnode-http-method \"GET\")
       (:elnode-http-query \"a=10\"))
   (should (equal 10 (elnode-http-param :fake \"a\"))))

Causes:

 (process-get :fake :elnode-http-method)

to always return \"GET\".

`process-put' is also remapped, to set any setting.

`process-buffer' is also remapped, to deliver the value of the
key `:buffer' if present and a dummy buffer otherwise.

`delete-process' is also remapped, to throw
`:mock-process-finished' to the catch called
`:mock-process-finished'.  You can implement your own catch to do
something with the `delete-process' event.

`process-send-string' is also remapped to send to a fake output
buffer.  The fake buffer can be returned with
`fakir-get-output-buffer'.

In normal circumstances, we return what the BODY returned."
  (declare
   (debug (sexp sexp &rest form))
   (indent defun))
  (let ((get-or-create-buf (make-symbol "get-or-create-buf"))
        (fakir-kill-buffer (make-symbol "fakir-kill-buffer"))
  (pvvar (make-symbol "pv"))
        (pvoutbuf (make-symbol "pvoutbuf"))
        (pvbuf (make-symbol "buf"))
        (result (make-symbol "result")))
    `(let ((,pvvar (list ,@(fakir/let-bindings->alist process-bindings)))
           ;; This is a buffer for the output
           (,pvoutbuf (get-buffer-create "*fakir-outbuf*"))
           ;; For assigning the result of the body
           ,result
           ;; Dummy buffer variable for the process - we fill this in
           ;; dynamically in 'process-buffer
           ,pvbuf)
       (fakir-mock-proc-properties ,process-symbol
         (flet ((fakir-get-output-buffer () ,pvoutbuf)
                (,get-or-create-buf (proc &optional specified-buf)
                  (setq ,pvbuf (fakir/get-or-create-buf
                                ,pvbuf
                                ,pvvar
                                specified-buf)))
                (,fakir-kill-buffer (buf)
                  (when (bufferp buf)
                    (with-current-buffer buf (set-buffer-modified-p nil))
                    (kill-buffer buf))))
           (unwind-protect
                (macrolet ((or-args (form &rest args)
                             `(if (eq proc ,,process-symbol)
                                  ,form
                                  (apply this-fn (list ,@args)))))
                  ;; Rebind the process function interface
                  (noflet
                      ((processp (proc) (or-args t proc))
                       (process-send-eof (proc) (or-args t proc))
                       (process-status (proc) (or-args 'fake proc))
                       (process-buffer (proc) (or-args (,get-or-create-buf proc) proc))
                       (process-contact (proc &optional arg) ; FIXME - elnode specific
                         (or-args (list "localhost" 8000) proc))
                       (process-send-string (proc str)
                         (or-args
                          (with-current-buffer ,pvoutbuf
                            (save-excursion
                              (goto-char (point-max))
                              (insert str)))
                          proc))
                       (delete-process (proc)
                         (or-args
                          (throw :mock-process-finished :mock-process-finished)
                          proc))
                       (set-process-buffer (proc buffer)
                         (or-args (,get-or-create-buf proc buffer) proc)))
                    (set-process-plist ,process-symbol (kvalist->plist ,pvvar))
                    (setq ,result
                          (catch :mock-process-finished
                            ,@body))))
             ;; Now clean up
             (,fakir-kill-buffer ,pvbuf)
             (,fakir-kill-buffer ,pvoutbuf)))))))


;; Time utils

(defun fakir-time-encode (time-str)
  "Encode the TIME-STR as an EmacsLisp time."
  ;; FIXME this should be part of Emacs probably; I've had to
  ;; implement this in Elnode as well
  (apply 'encode-time (parse-time-string time-str)))

;; A structure to represent a mock file

(defstruct fakir-file
  filename
  directory
  (content "")
  ;; obviously there should be all the state of the file here
  (mtime "Mon, Feb 27 2012 22:10:19 GMT")
  (directory-p nil))

(defun fakir-file (&rest args)
  "Make a fakir-file, a struct.

:FILENAME is the basename of the file

:DIRECTORY is the dirname of the file

:CONTENT is a string of content for the file

:MTIME is the modified time, with a default around the time fakir
was written.

:DIRECTORY-P specifies whether this file is a directory or a file."
  (apply 'make-fakir-file args))

(defun fakir--file-check (file)
  "Implements the type check for FILE is a `fakir--file'."
  (if (not (fakir-file-p file))
      (error "not an fakir--file")))

(defun fakir--file-fqn (file)
  "Return the fully qualified name of FILE, an `fakir--file'."
  (fakir--file-check file)
  (let* ((fqfn
          (concat
           (file-name-as-directory
            (fakir-file-directory file))
           (fakir-file-filename file))))
    fqfn))

(defun fakir--file-rename (src-file to-file-name)
  "Rename the `fakir-file' SRC-FILE."
  (fakir--file-check src-file)
  (let ((base-file-name (file-name-nondirectory to-file-name))
        (file-dir (file-name-directory to-file-name)))
    (setf (fakir-file-directory src-file) file-dir)
    (setf (fakir-file-filename src-file) base-file-name)))

(defun fakir--file-mod-time (file &optional raw)
  "Return the encoded mtime of FILE, an `fakir--file'.

If RAW is t then return the raw value, a string."
  (fakir--file-check file)
  (if raw
      (fakir-file-mtime file)
    (fakir-time-encode (fakir-file-mtime file))))

(defun fakir--file-attribs (file)
  "Return an answer as `file-attributes' for FILE.

Currently WE ONLY SUPPORT MODIFIED-TIME."
  (fakir--file-check file)
  (list (fakir-file-directory-p file)
        t t t t
        (fakir--file-mod-time file)))

(defun fakir--file-home (file)
  "Return the home part of FILE or nil.

The home part of FILE is the part that is the home directory of
the user. If it's not a user FILE then it won't have a home
part."
  (fakir--file-check file)
  (let* ((fqn (fakir--file-fqn file))
         (home-root
          (save-match-data
            (when
                (string-match
                 "^\\(/home/[A-Za-z][A-Za-z0-9-]+\\)\\(/.*\\)*"
                 fqn)
              (match-string 1 fqn)))))
    home-root))

(defun fakir--file-path (faked-file)
  "Make a path name from the FAKED-FILE."
  (concat
   (file-name-as-directory
    (fakir-file-directory faked-file))
   (fakir-file-filename faked-file)))

(defvar fakir--home-root "/home/fakir"
  "String to use as the home-root.")

(defun fakir--join (file-name &optional dir)
  "Join FILE-NAME to DIR or `fakir--home-root'."
  (concat
   (file-name-as-directory (or dir fakir--home-root))
   file-name))

(defun fakir--expand (file-name rooted-p)
  "Functional file-name expand."
  (let ((path
         (mapconcat
          'identity
          (let ((l
                 (-reduce
                  (lambda (a b)
                    (if (string= b "..")
                        (if (consp a)
                            (reverse (cdr (reverse a)))
                            (list a))
                        (if (consp a)
                            (append a (list b))
                            (list a b))))
                  (cdr (split-string file-name "/")))))
            (if (listp l) l (list l)))
          "/")))
    (if (and rooted-p (not (equal ?\/ (elt path 0))))
        (concat "/" path)
        path)))

(defun fakir--expand-file-name (file-name dir)
  "Implementation of ~ and .. handling for FILE-NAME."
  (let* ((fqfn
          (if (string-match "^\\(~/\\|/\\).*" file-name)
              file-name
              ;; Else it's both
              (fakir--join file-name dir)))
         (file-path
          ;; Replace ~/ with the home-root
          (replace-regexp-in-string
           "^~/\\(.*\\)"
           (lambda (m) (fakir--join (match-string 1 m)))
           fqfn))
         (new-path
          (fakir--expand
           file-path
           (equal ?\/ (elt file-path 0)))))
    new-path))

(defun fakir--find-file (fakir-file)
  "`find-file' implementation for FAKIR-FILE."
  (let ((buf (get-buffer (fakir-file-filename fakir-file))))
    (if (bufferp buf)
        buf
        ;; Else make one and put the content in it
        (with-current-buffer
            (get-buffer-create (fakir-file-filename fakir-file))
          (insert (fakir-file-content fakir-file))
          (current-buffer)))))

(defun fakir-file-path (fakir-file)
  "Make the path for FAKIR-FILE."
  (concat (fakir-file-directory fakir-file)
          (fakir-file-filename fakir-file)))


(defun fakir--file-parent-directories (faked-file)
  "Return the parent directories for a FAKED-FILE."
  (let ((directory-path (fakir-file-directory faked-file))
        (path "")
        (path-list '("/")))
    (dolist (path-part (split-string directory-path "/" t))
      (let ((current-path (concat path "/" path-part)))
        (push current-path path-list)
        (setq path current-path)))
    path-list))

(defun fakir--namespace-put (faked-file namespace)
  "Put given FAKED-FILE and its parent folders into the given NAMESPACE."
  (puthash (fakir--file-path faked-file) faked-file namespace)
  (dolist (parent-dir (fakir--file-parent-directories faked-file))
    (puthash
     parent-dir
     (fakir-file
      :filename (file-name-nondirectory parent-dir)
      :directory (file-name-directory parent-dir)
      :content ""
      :directory-p t)
     namespace)))

(defun fakir--namespace (faked-file &rest other-files)
  "Make a namespace with FAKED-FILE in it.

Also adds the directory for the FAKED-FILE.

If OTHER-FILES are specified they are added to."
  (let ((ns (make-hash-table :test 'equal)))
    (fakir--namespace-put faked-file ns)
    (dolist (other-file other-files)
      (fakir--namespace-put other-file ns))
    ns))

(defun fakir--namespace-lookup (file-name namespace)
  "Lookup FILE-NAME in NAMESPACE.

Looks up the FILE-NAME"
  (kvhash->alist namespace)
  (or
   (gethash file-name namespace)
   (gethash
    (file-name-as-directory file-name)
    namespace)))

(defvar fakir-file-namespace nil
  "Namespace used by `fakir--file-cond'.")

(defmacro fakir--file-cond (file-name then &rest else)
  "Do THEN or ELSE if FILE-NAME is a faked file.

Uses the `fakir-file-namepsace' to detect that.

The `fakir-file' for the FILE-NAME is locally bound in the THEN
clause to `this-fakir-file'."
  (declare (indent 1))
  (let ((file-name-v (make-symbol "file-namev"))
        (found-file (make-symbol "ff")))
    `(let* ((,file-name-v ,file-name)
            (,found-file
             (fakir--namespace-lookup
              ,file-name-v fakir-file-namespace)))
       (if (fakir-file-p ,found-file)
           (let ((this-fakir-file ,found-file))
             ,then)
           ,@else))))

(defun fakir--write-region (fakir-file start end file-name
                            &optional append visit lockname mustbenew)
  "Fake `write-region' function to write to FAKIR-FILE.

`fakir-fake-file' does not call this unless the FILE-NAME exists
as a declared fake-file.  Thus you cannot use this to save files
you have not explicitly declared as fake."
  (let ((to-write
         (cond
           ((equal start nil) (buffer-string))
           ((stringp start) start)
           (t (buffer-substring start end)))))
    (setf
     (fakir-file-content fakir-file)
     (if append
         (concat (fakir-file-content fakir-file) to-write)
         to-write))))

(defun fakir--parent-fakir-file (file)
  "Return the parent fakir-file for FILE from the current namespace."
  (fakir--file-check file)
  (let ((parent-file-name (directory-file-name
                           (fakir-file-directory file))))
    (fakir--namespace-lookup parent-file-name fakir-file-namespace)))

(defun fakir--directory-fakir-files (directory)
  "Return all fakir-files that are inside the given DIRECTORY."
  (let ((directory (file-name-as-directory directory))
        directory-fakir-files)

    (loop for fakir-file being the hash-value of fakir-file-namespace
          if (equal (file-name-as-directory
                     (fakir-file-directory fakir-file))
                    directory)
          collect fakir-file)))

(defun fakir--directory-files-and-attributes (directory &optional full match nosort id-format)
  "Return a list of faked files and their faked attributes in DIRECTORY.

There are four optional arguments:
If FULL is non-nil, return absolute file names.  Otherwise return names
 that are relative to the specified directory.
If MATCH is non-nil, mention only file names that match the regexp MATCH.
If NOSORT is non-nil, the list is not sorted--its order is unpredictable.
 NOSORT is useful if you plan to sort the result yourself.
ID-FORMAT is ignored.  Instead we use the fakir format (see `fakir--file-attribs')."
  (let* ((directory-fakir-file
          (fakir--namespace-lookup
           directory
           fakir-file-namespace))
         (parent-fakir-file (fakir--parent-fakir-file directory-fakir-file))
         (directory-fakir-files (fakir--directory-fakir-files directory))
         files-and-attributes)

    (if (or (not match) (string-match match "."))
        (push (cons (if full
                       (concat (file-name-as-directory directory) ".")
                     ".")
                   (fakir--file-attribs directory-fakir-file))
             files-and-attributes))

    (if (or (not match) (string-match match ".."))
        (push (cons (if full
                        (concat (file-name-as-directory directory) "..")
                      "..")
                    (fakir--file-attribs parent-fakir-file))
              files-and-attributes))

    (dolist (fakir-file directory-fakir-files)
      (if (or (not match) (string-match match (fakir-file-filename fakir-file)))
          (push (cons (if full
                          (fakir--file-fqn fakir-file)
                        (fakir-file-filename fakir-file))
                      (fakir--file-attribs fakir-file))
                files-and-attributes)))

    (if nosort
        files-and-attributes
      (sort files-and-attributes
            #'(lambda (s1 s2)
                (string-lessp (car s1) (car s2)))))))

(defun fakir--directory-files (directory &optional full match nosort)
  "Return a list of names of faked files in DIRECTORY.

There are three optional arguments:
If FULL is non-nil, return absolute file names.  Otherwise return names
 that are relative to the specified directory.
If MATCH is non-nil, mention only file names that match the regexp MATCH.
If NOSORT is non-nil, the list is not sorted--its order is unpredictable.
 Otherwise, the list returned is sorted with `string-lessp'.
 NOSORT is useful if you plan to sort the result yourself."
  (mapcar 'car (fakir--directory-files-and-attributes directory full match nosort)))

(defmacro fakir-fake-file (faked-file &rest body)
  "Fake FAKED-FILE and evaluate BODY.

FAKED-FILE must be a `fakir-file' object or a list of
`fakir-file' objects."
  (declare (indent 1)
           (debug (sexp &rest form)))
  (let ((ffv (make-symbol "ff")))
    `(let* ((,ffv ,faked-file)
            (fakir-file-namespace
             (if (fakir-file-p ,ffv)
                 (fakir--namespace ,ffv)
                 (apply 'fakir--namespace ,ffv))))
       (noflet
           ((expand-file-name (file-name &optional dir)
              (let ((expanded
                     (fakir--expand-file-name file-name dir)))
                (fakir--file-cond expanded
                  expanded
                  (funcall this-fn file-name dir))))
            (file-attributes (file-name)
              (fakir--file-cond file-name
                (fakir--file-attribs this-fakir-file)
                (funcall this-fn file-name)))
            (file-exists-p (file-name)
              (fakir--file-cond file-name
                t
                (funcall this-fn file-name)))
            (file-directory-p (file-name)
              (fakir--file-cond file-name
                (fakir-file-directory-p this-fakir-file)
                (funcall this-fn file-name)))
            (file-regular-p (file-name)
              (fakir--file-cond file-name
                (not (fakir-file-directory-p this-fakir-file))
                (funcall this-fn file-name)))
            (write-region (start end file-name &optional append visit lockname mustbenew)
              (fakir--file-cond file-name
                (fakir--write-region
                 this-fakir-file ; the faked file - should match file-name
                 start end file-name append visit mustbenew)
                (funcall this-fn start end file-name append visit mustbenew)))
            (rename-file (from to)
              (fakir--file-cond from
                (fakir--file-rename this-fakir-file to)
                (funcall this-fn from to)))
            (insert-file-contents
                (file-name &optional visit beg end replace)
              (fakir--file-cond file-name
                (insert (fakir-file-content this-fakir-file))
                (funcall this-fn file-name)))
            (insert-file-contents-literally
                (file-name &optional visit beg end replace)
              (fakir--file-cond file-name
                (insert (fakir-file-content this-fakir-file))
                (funcall this-fn file-name)))
            (find-file (file-name)
              (fakir--file-cond file-name
                (fakir--find-file this-fakir-file)
                (funcall this-fn file-name)))
            (find-file-noselect (file-name)
              (fakir--file-cond file-name
                (fakir--find-file this-fakir-file)
                (funcall this-fn file-name)))
            (directory-files (directory &optional full match nosort)
              (fakir--file-cond directory
                (fakir--directory-files directory full match nosort)
                (funcall this-fn directory full match nosort)))
            (directory-files-and-attributes (directory &optional full match nosort id-format)
              (fakir--file-cond directory
                (fakir--directory-files-and-attributes directory full match nosort id-format)
                (funcall this-fn directory full match nosort))))
         ,@body))))

(defmacro fakir-mock-file (faked-file &rest body)
  (declare (debug (sexp &rest form))
           (indent 1))
  `(fakir-fake-file ,faked-file ,@body))

(provide 'fakir)

;;; fakir.el ends here
