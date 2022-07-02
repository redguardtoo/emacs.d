;;; workgroups2.el --- save&load multiple named workspaces (or "workgroups") -*- coding: utf-8; lexical-binding: t -*-
;;
;; Copyright (C) 2020-2021 Chen Bin
;; Copyright (C) 2013-2014 Sergey Pashinin
;; Copyright (C) 2010-2011 tlh
;;
;; Author: Sergey Pashinin <sergey at pashinin dot com>
;; Keywords: session management window-configuration persistence
;; Homepage: https://github.com/pashinin/workgroups2
;; Version: 1.2.1
;; Package-Requires: ((emacs "25.1"))
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or (at
;; your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
;; USA
;;
;;; Commentary:
;;
;; This program can save&load multiple named workspaces (or "workgroups").
;;
;; If you find a bug - please post it here:
;; https://github.com/pashinin/workgroups2/issues
;;
;; Quick start,
;;
;; - `wg-create-workgroup' to save window&buffer layout as a work group
;; - `wg-open-workgroup' to open an existing work group
;; - `wg-kill-workgroup' to delete an existing work group
;;
;; Optionally, you can use minor-mode `workgroups-mode' by put below
;; line into .emacs ,
;;
;; (workgroups-mode 1)
;;
;; Most commands start with prefix `wg-prefix-key'.
;; You can change it before activating workgroups.
;; Change prefix key (before activating WG)
;;
;; (setq wg-prefix-key "C-c z")
;;
;; By default prefix is: "C-c z"
;;
;; <prefix> C-c    - create new workgroup
;; <prefix> C-v    - open existing workgroup
;; <prefix> C-k    - delete existing workgroup
;;
;; Change workgroups session file,
;;
;;   (setq wg-session-file "~/.emacs.d/.emacs_workgroups")
;;
;; Support any special buffer (say `ivy-occur-grep-mode'),
;;
;;   (with-eval-after-load 'workgroups2
;;     ;; provide major mode, package to require, and functions
;;     (wg-support 'ivy-occur-grep-mode 'ivy
;;                 `((serialize . ,(lambda (_buffer)
;;                                   (list (base64-encode-string (buffer-string) t))))
;;                   (deserialize . ,(lambda (buffer _vars)
;;                                     (switch-to-buffer (wg-buf-name buffer))
;;                                     (insert (base64-decode-string (nth 0 _vars)))
;;                                     ;; easier than `ivy-occur-grep-mode' to set up
;;                                     (grep-mode)
;;                                     ;; need return current buffer at the end of function
;;                                     (current-buffer))))))
;;
;;; Code:
;;

(require 'pp)
(require 'workgroups2-sdk)

(defconst wg-version "1.2.1" "Current version of Workgroups.")

(defgroup workgroups nil
  "Workgroups for Emacs -- Emacs session manager"
  :group 'convenience)

(defcustom wg-session-file "~/.emacs_workgroups"
  "Default filename to be used to save workgroups."
  :type 'file
  :group 'workgroups)

(defcustom wg-prefix-key "C-c z"
  "Workgroups' prefix key.
Setting this variable requires that `workgroups-mode' be turned
off and then on again to take effect."
  :type 'string
  :group 'workgroups)

(defcustom workgroups-mode nil
  "Non-nil if Workgroups mode is enabled."
  :set 'custom-set-minor-mode
  :initialize 'custom-initialize-default
  :group 'workgroups
  :type 'boolean)

(defcustom wg-first-wg-name "First workgroup"
  "Title of the first workgroup created."
  :type 'string
  :group 'workgroups)

(defcustom wg-control-frames t
  "Save/restore frames."
  :group 'workgroups
  :type 'boolean)

(defcustom wg-after-switch-to-workgroup-hook nil
  "Hook run by `wg-switch-to-workgroup-internal'."
  :type 'hook
  :group 'workgroups)

;; TODO: possibly add `buffer-file-coding-system', `text-scale-mode-amount'
(defcustom wg-buffer-local-variables-alist
  `((major-mode nil wg-deserialize-buffer-major-mode)
    (mark-ring wg-serialize-buffer-mark-ring wg-deserialize-buffer-mark-ring)
    (left-fringe-width nil nil)
    (right-fringe-width nil nil)
    (fringes-outside-margins nil nil)
    (left-margin-width nil nil)
    (right-margin-width nil nil)
    (vertical-scroll-bar nil nil))
  "Alist mapping buffer-local variable symbols to serdes functions.

The 1st of each entry should be a buffer-local variable symbol.

The 2nd of the entry should be either nil or a function of no
arguments.  If nil, the variable's value is used as-is, and
should have a readable printed representation.  If a function,
calling it yields a serialization of the value of the variable.

The 3rd of the entry should be either nil or a function of
one argument.  If nil, the serialized value from above is
assigned to the variable as-is.  It a function, calling it
on the serialized value from above should do whatever is
necessary to properly restore the original value of the variable.
For example, in the case of `major-mode' it should funcall the
value (a `major-mode' function symbol) rather than just assigning
it to `major-mode'."
  :type 'alist
  :group 'workgroups)

(defvar wg-buffer-uid nil
  "Symbol for the current buffer's wg-buf's uid.
Every Workgroups buffer object (wg-buf) has a uid.  When
Workgroups creates or encounters an Emacs buffer object
corresponding to a wg-buf, it tags it with the wg-buf's uid to
unambiguously pair the two.")
(make-variable-buffer-local 'wg-buffer-uid)

(defvar wg-current-workgroup nil "Bound to the current workgroup.")

(defvar wg-window-min-width 2
  "Bound to `window-min-width' when restoring wtrees.")

(defvar wg-window-min-height 1
  "Bound to `window-min-height' when restoring wtrees.")

(defvar wg-window-tree-selected-window nil
  "Used during wconfig restoration to hold the selected window.")

(defcustom wg-default-buffer "*scratch*"
  "Show this in case everything else fails.
When a buffer can't be restored, when creating a blank wg."
  :type 'string
  :group 'workgroups)

(defcustom wg-major-mode-excludes '(dired-mode
                                    minibuffer-inactive-mode
                                    minibuffer-mode)
  "Buffers/frames with the major modes in this list are excluded."
  :type '(repeat sexp)
  :group 'workgroups)

;; {{ crazy stuff to delete soon
(defconst wg-buffer-list-original (symbol-function 'buffer-list))
(defalias 'wg-buffer-list-emacs wg-buffer-list-original)
(defalias 'wg-switch-to-workgroup #'wg-open-workgroup)

(defun buffer-list (&optional frame)
  "Redefinition of `buffer-list'.  Pass FRAME to it.
Remove file and buffers that are not associated with workgroup."
  (let ((res (wg-buffer-list-emacs frame))
        (wg-buf-uids (wg-workgroup-associated-buf-uids)))
    (cl-remove-if (lambda (it)
                    (and (or (buffer-file-name it)
                             (memq (buffer-local-value 'major-mode it)
                                   wg-major-mode-excludes))
                         (not (member (wg-buffer-uid-or-add it) wg-buf-uids))) )
                  res)))

(defconst wg-buffer-list-function (symbol-function 'buffer-list))
(fset 'buffer-list wg-buffer-list-original)
;; }}

(defmacro wg-defstruct (name-form &rest slot-defs)
  "`defstruct' wrapper that namespace-prefixes all generated functions."
  (declare (indent 1))
  (let* ((prefix "wg")
         (name (symbol-name name-form)) ; string type
         (prefixed-name (concat prefix "-" name))
         (symbol-prefixed-name (intern prefixed-name)))
    (cl-labels ((rebind (opstr)
                        (let ((oldfnsym (intern (concat opstr "-" prefixed-name)))
                              (newfnsym (intern (concat prefix "-" opstr "-" name))))
                          `((fset ',newfnsym (symbol-function ',oldfnsym))
                            (fmakunbound ',oldfnsym)))))
      ;; `eval-and-compile' gets rid of byte-comp warnings ("function `foo' not
      ;; known to be defined").  We can accomplish this with `declare-function'
      ;; too, but it annoyingly requires inclusion of the function's arglist,
      ;; which gets ugly.
      `(eval-and-compile
         (cl-defstruct ,symbol-prefixed-name ,@slot-defs)
         ,@(rebind "make")
         ,@(rebind "copy")
         ',symbol-prefixed-name))))

;; {{
(wg-defstruct session
  (uid (wg-generate-uid))
  (name)
  (modified)
  (parameters)
  (file-name)
  (version wg-version)
  (workgroup-list)
  (buf-list))

(wg-defstruct workgroup
  (uid (wg-generate-uid))
  (name)
  (modified)
  (parameters)
  (base-wconfig)
  (selected-frame-wconfig)
  (saved-wconfigs)
  (strong-buf-uids)
  (weak-buf-uids))

(wg-defstruct workgroup-state
  (undo-pointer)
  (undo-list))

(wg-defstruct wconfig
  (uid (wg-generate-uid))
  (name)
  (parameters)
  (left)
  (top)
  (width)
  (height)
  (vertical-scroll-bars)
  (scroll-bar-width)
  (wtree))

(wg-defstruct wtree
  (uid)
  (dir)
  (edges)
  (wlist))

(wg-defstruct win
  (uid)
  (parameters)
  (edges)
  (point)
  (start)
  (hscroll)
  (dedicated)
  (selected)
  (minibuffer-scroll)
  (buf-uid))

(wg-defstruct buf
  (uid (wg-generate-uid))
  (name)
  (file-name)
  (point)
  (mark)
  (local-vars)
  (special-data)
  ;; This may be used later:
  (gc))
;; }}

(defmacro wg-with-slots (obj slot-bindings &rest body)
  "Bind OBJ's slot values to symbols in BINDS, then eval BODY.
The car of each element of SLOT-BINDINGS is the bound symbol, and
the cadr as the accessor function."
  (declare (indent 2))
  (wg-with-gensyms (objsym)
    `(let* ((,objsym ,obj)
            ,@(wg-docar (slot slot-bindings)
                `(,(car slot) (,(cadr slot) ,objsym))))
       ,@body)))

(defmacro wg-set-parameter (place parameter value)
  "Set PARAMETER to VALUE at PLACE.
This needs to be a macro to allow specification of a setf'able place."
  (wg-with-gensyms (p v)
    `(let ((,p ,parameter) (,v ,value))
       (wg-pickelable-or-error ,p)
       (wg-pickelable-or-error ,v)
       (setf ,place (wg-aput ,place ,p ,v))
       ,v)))

(defun wg-time-to-b36 ()
  "Convert `current-time' into a b36 string."
  (apply 'concat (wg-docar (time (current-time))
                   (wg-int-to-b36 time))))

(defun wg-generate-uid ()
  "Return a new uid."
  (concat (wg-time-to-b36) "-" (wg-int-to-b36 string-chars-consed)))

(defvar wg-current-session nil "Current session object.")
(defvar wg-snapshot-session nil "Snapshot of session object.")

(defun wg-get-current-session (&optional noerror)
  "Return current session or error unless NOERROR."
  wg-current-session)

;; locate-dominating-file
(defun wg-get-first-existing-dir (&optional dir)
  "Test if DIR exists and return it.
If not - try to go to the parent dir and do the same."
  (let* ((d (or dir default-directory)))
    (if (file-directory-p d) d
      (let* ((cur d) (parent (file-name-directory (directory-file-name cur))))
        (while (and (> (length cur) (length parent))
                    (not (file-directory-p parent)))
          (message "Test %s" parent)
          (setq cur parent)
          (setq parent (file-name-directory (directory-file-name cur))))
        parent))))


(defconst wg-pickel-identifier '~pickel!~
  "Symbol identifying a stream as a pickel.")

(defvar wg-pickel-pickelable-types
  '(integer
    float
    symbol
    string
    cons
    vector
    hash-table
    buffer
    marker
    wg-wconfig
    ;;window-configuration
    ;;frame
    ;;window
    ;;process
    )
  "Types pickel can serialize.")

(defvar wg-pickel-object-serializers
  '((integer    . identity)
    (float      . identity)
    (string     . identity)
    (symbol     . wg-pickel-symbol-serializer)
    (cons       . wg-pickel-cons-serializer)
    (vector     . wg-pickel-vector-serializer)
    (hash-table . wg-pickel-hash-table-serializer)
    (buffer     . wg-pickel-buffer-serializer)
    (marker     . wg-pickel-marker-serializer))
  "Alist mapping types to object serialization functions.")

(defvar wg-pickel-object-deserializers
  '((s . wg-pickel-deserialize-symbol)
    (c . wg-pickel-deserialize-cons)
    (v . wg-pickel-deserialize-vector)
    (h . wg-pickel-deserialize-hash-table)
    (b . wg-pickel-deserialize-buffer)
    (m . wg-pickel-deserialize-marker)
    (d . wg-pickel-deserialize-default)
    ;;(f . wg-pickel-deserialize-frame)
    )
  "Alist mapping type keys to object deserializing functions.")

(defvar wg-pickel-link-serializers
  '((cons       . wg-pickel-cons-link-serializer)
    (vector     . wg-pickel-vector-link-serializer)
    (hash-table . wg-pickel-hash-table-link-serializer))
  "Alist mapping types to link serialization functions.")

(defvar wg-pickel-link-deserializers
  `((c . wg-pickel-cons-link-deserializer)
    (v . wg-pickel-vector-link-deserializer)
    (h . wg-pickel-hash-table-link-deserializer))
  "Alist mapping type keys to link deserializing functions.")

(put 'wg-pickel-unpickelable-type-error
     'error-conditions
     '(error wg-pickel-errors wg-pickel-unpickelable-type-error))

(put 'wg-pickel-unpickelable-type-error
     'error-message
     "Attempt to pickel unpickelable type")

(defun wg-pickelable-or-error (obj)
  "Error when OBJ isn't pickelable."
  (unless (memq (type-of obj) wg-pickel-pickelable-types)
    (signal 'wg-pickel-unpickelable-type-error
            (format "Can't pickel objects of type: %S" (type-of obj))))
  (cl-typecase obj
    (cons
     (wg-pickelable-or-error (car obj))
     (wg-pickelable-or-error (cdr obj)))
    (vector
     (cl-map nil 'wg-pickelable-or-error obj))
    (hash-table
     (wg-dohash (key value obj)
       (wg-pickelable-or-error key)
       (wg-pickelable-or-error value)))))

(defun wg-pickel-p (obj)
  "Return t when OBJ is a pickel, nil otherwise."
  (and (consp obj) (eq (car obj) wg-pickel-identifier)))

;; accessor functions
(defun wg-pickel-default-serializer (object)
  "Return OBJECT's data."
  (list 'd (prin1-to-string object)))

(defun wg-pickel-object-serializer (obj)
  "Return the object serializer for the `type-of' OBJ."
  (or (wg-aget wg-pickel-object-serializers (type-of obj))
      #'wg-pickel-default-serializer))

(defun wg-pickel-link-serializer (obj)
  "Return the link serializer for the `type-of' OBJ."
  (wg-aget wg-pickel-link-serializers (type-of obj)))

(defun wg-pickel-object-deserializer (key)
  "Return the object deserializer for type key KEY, or error."
  (or (wg-aget wg-pickel-object-deserializers key)
      (error "Invalid object deserializer key: %S" key)))

(defun wg-pickel-link-deserializer (key)
  "Return the link deserializer for type key KEY, or error."
  (or (wg-aget wg-pickel-link-deserializers key)
      (error "Invalid link deserializer key: %S" key)))

;;; bindings
(defun wg-pickel-make-bindings-table (obj)
  "Return a table binding unique sub-objects of OBJ to ids."
  (let ((binds (make-hash-table :test 'eq))
        (id -1))
    (cl-labels
        ((inner (obj)
                (unless (gethash obj binds)
                  (puthash obj (cl-incf id) binds)
                  (cl-case (type-of obj)
                    (cons
                     (inner (car obj))
                     (inner (cdr obj)))
                    (vector
                     (dotimes (idx (length obj))
                       (inner (aref obj idx))))
                    (hash-table
                     (wg-dohash (key val obj)
                       (inner key)
                       (inner val)))))))
      (inner obj)
      binds)))

;;; Objects
(defun wg-pickel-symbol-serializer (symbol)
  "Return SYMBOL's serialization."
  (cond ((eq symbol t) t)
        ((eq symbol nil) nil)
        ((intern-soft symbol) symbol)
        (t (list 's (symbol-name symbol)))))

(defun wg-pickel-deserialize-symbol (name)
  "Return a new symbol from NAME."
  (make-symbol name))


;; buffer
(defun wg-pickel-buffer-serializer (buffer)
  "Return BUFFER's UID in workgroups buffer list."
  (list 'b (wg-add-buffer-to-buf-list buffer)))

(defun wg-pickel-deserialize-buffer (uid)
  "Return a restored buffer from it's UID."
  (wg-restore-buffer (wg-find-buf-by-uid uid)))


;; marker
(defun wg-pickel-marker-serializer (marker)
  "Return MARKER's data."
  (list 'm (list (marker-position marker)
                 (wg-add-buffer-to-buf-list (marker-buffer marker)))))

(defun wg-pickel-deserialize-marker (data)
  "Return marker from it's DATA."
  (let ((m (make-marker)))
    (set-marker m (car data) (wg-pickel-deserialize-buffer (car (cdr data))))))

(defun wg-pickel-deserialize-default (object)
  "Return data from OBJECT."
  (read object))

;; cons - http://www.gnu.org/software/emacs/manual/html_node/eintr/cons.html
(defun wg-pickel-cons-serializer (_cons)
  "Return CONS's serialization."
  (list 'c))
(defun wg-pickel-deserialize-cons ()
  "Return a new cons cell initialized to nil."
  (cons nil nil))
(defun wg-pickel-cons-link-serializer (cons binds)
  "Return the serialization of CONS's links in BINDS."
  (list 'c
        (gethash cons binds)
        (gethash (car cons) binds)
        (gethash (cdr cons) binds)))

(defun wg-pickel-cons-link-deserializer (cons-id car-id cdr-id binds)
  "Relink a cons cell with its car and cdr in BINDS."
  (let ((cons (gethash cons-id binds)))
    (setcar cons (gethash car-id binds))
    (setcdr cons (gethash cdr-id binds))))

(defun wg-pickel-vector-serializer (vector)
  "Return VECTOR's serialization."
  (list 'v (length vector)))
(defun wg-pickel-deserialize-vector (length)
  "Return a new vector of length LENGTH."
  (make-vector length nil))

(defun wg-pickel-vector-link-serializer (vector binds)
  "Return the serialization of VECTOR's links in BINDS."
  (let (result)
    (dotimes (i (length vector))
      (setq result
            (nconc (list 'v
                         (gethash vector binds)
                         i
                         (gethash (aref vector i) binds))
                   result)))))

(defun wg-pickel-vector-link-deserializer (vector-id index value-id binds)
  "Relink a vector with its elements in BINDS."
  (aset (gethash vector-id binds) index (gethash value-id binds)))

;; hash table - http://www.gnu.org/software/emacs/manual/html_node/elisp/Hash-Tables.html
(defun wg-pickel-hash-table-serializer (table)
  "Return HASH-TABLE's serialization."
  (list 'h
        (hash-table-test table)
        (hash-table-size table)
        (hash-table-rehash-size table)
        (hash-table-rehash-threshold table)
        (hash-table-weakness table)))

(defun wg-pickel-deserialize-hash-table (test size rsize rthresh weakness)
  "Return a new hash-table with the specified properties."
  (make-hash-table :test test :size size :rehash-size rsize
                   :rehash-threshold rthresh :weakness weakness))

(defun wg-pickel-hash-table-link-serializer (table binds)
  "Return the serialization of TABLE's links in BINDS."
  (let (result)
    (wg-dohash (key value table result)
      (setq result
            (nconc (list 'h
                         (gethash key binds)
                         (gethash value binds)
                         (gethash table binds))
                   result)))))

(defun wg-pickel-hash-table-link-deserializer (key-id value-id table-id binds)
  "Relink a hash-table with its keys and values in BINDS."
  (puthash (gethash key-id binds)
           (gethash value-id binds)
           (gethash table-id binds)))

(defun wg-pickel-serialize-objects (binds)
  "Return a list of serializations of the objects in BINDS."
  (let (result)
    (wg-dohash (obj id binds result)
      (setq result
            (nconc (list id (funcall (wg-pickel-object-serializer obj) obj))
                   result)))))

(defun wg-pickel-deserialize-objects (serial-objects)
  "Return a hash-table of objects to deserialize from SERIAL-OBJECTS."
  (let ((binds (make-hash-table)))
    (wg-destructuring-dolist ((id obj . rest) serial-objects binds)
      (puthash id
               (if (atom obj) obj
                 (wg-dbind (key . data) obj
                   (apply (wg-pickel-object-deserializer key) data)))
               binds))))

(defun wg-pickel-serialize-links (binds)
  "Return a list of serializations of the links between objects in BINDS."
  (let (result fn)
    (wg-dohash (obj _id binds result)
               (when (setq fn (wg-pickel-link-serializer obj) )
                 (setq result (nconc (funcall fn obj binds) result))))))

(defun wg-pickel-deserialize-links (serial-links binds)
  "Return BINDS after re-linking all its objects according to SERIAL-LINKS."
  (wg-destructuring-dolist ((key arg1 arg2 arg3 . rest) serial-links binds)
    (funcall (wg-pickel-link-deserializer key) arg1 arg2 arg3 binds)))

(defun wg-pickel (obj)
  "Return the serialization of OBJ."
  (wg-pickelable-or-error obj)
  (let ((binds (wg-pickel-make-bindings-table obj))
        rlt)
    (setq rlt (list wg-pickel-identifier
                    (wg-pickel-serialize-objects binds)
                    (wg-pickel-serialize-links binds)
                    (gethash obj binds)))
    (when wg-debug
      (message "wg-pickel called => %s" rlt))
    rlt))

(defun wg-unpickel (pickel)
  "Deserialize PICKEL."
  (unless (wg-pickel-p pickel)
    (error "Attempt to unpickel a non-pickel"))
  (wg-dbind (_id serial-objects serial-links result) pickel
    (gethash
     result
     (wg-pickel-deserialize-links
      serial-links
      (wg-pickel-deserialize-objects serial-objects)))))

(defadvice select-frame (before wg-update-current-workgroup-working-wconfig)
  "Update `selected-frame's current workgroup's working-wconfig.
Before selecting a new frame."
  (wg-update-current-workgroup-working-wconfig))

(defvar wg-deactivation-list nil
  "A stack of workgroups that are currently being switched away from.
Used to avoid associating the old workgroup's buffers with the
new workgroup during a switch.")

(defvar workgroups-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd (format "%s %s" wg-prefix-key "C-c")) 'wg-create-workgroup)
    (define-key map (kbd (format "%s %s" wg-prefix-key "C-v")) 'wg-open-workgroup)
    (define-key map (kbd (format "%s %s" wg-prefix-key "C-k")) 'wg-kill-workgroup)
    map)
    "Mode map for `workgroups-mode'.")

(defun wg-add-workgroups-mode-minor-mode-entries ()
  "Add Workgroups' minor-mode entries.
Adds entries to `minor-mode-list', `minor-mode-alist' and
`minor-mode-map-alist'."
  (cl-pushnew 'workgroups-mode minor-mode-list)
  (setq minor-mode-map-alist
        (cons (cons 'workgroups-mode workgroups-mode-map)
              (delete (assoc 'workgroups-mode minor-mode-map-alist)
                      minor-mode-map-alist))))

(defmacro wg-with-edges (w spec &rest body)
  "Bind W's edge list to SPEC and eval BODY."
  (declare (indent 2))
  `(wg-dbind ,spec (wg-w-edges ,w) ,@body))

(defmacro wg-with-bounds (wtree dir spec &rest body)
  "Bind SPEC to W's bounds in DIR, and eval BODY.
\"bounds\" are a direction-independent way of dealing with edge lists."
  (declare (indent 3))
  (wg-with-gensyms (_dir-sym l1 t1 r1 b1)
    (wg-dbind (ls1 hs1 lb1 hb1) spec
      `(wg-with-edges ,wtree (,l1 ,t1 ,r1 ,b1)
         (cond (,dir (let ((,ls1 ,l1) (,hs1 ,r1) (,lb1 ,t1) (,hb1 ,b1))
                       ,@body))
               (t    (let ((,ls1 ,t1) (,hs1 ,b1) (,lb1 ,l1) (,hb1 ,r1))
                       ,@body)))))))

(defun wg-set-bounds (w dir ls hs lb hb)
  "Set W's edges in DIR with bounds LS HS LB and HB."
  (wg-set-edges w (if dir (list ls lb hs hb) (list lb ls hb hs))))

(defun wg-w-size (width &optional height)
  "Return the WIDTH or HEIGHT of W, calculated from its edge list."
  (wg-with-edges width (l1 t1 r1 b1)
    (if height (- b1 t1) (- r1 l1))))

(defun wg-win-parameter (win parameter &optional default)
  "Return WIN's value for PARAMETER.
If PARAMETER is not found, return DEFAULT which defaults to nil.
SESSION nil defaults to the current session."
  (wg-aget (wg-win-parameters win) parameter default))

(defun wg-restore-window (win)
  "Restore WIN in `selected-window'."
  (let ((selwin (selected-window))
        (buf (wg-find-buf-by-uid (wg-win-buf-uid win))))
    (if (not buf) (wg-restore-default-buffer)
      (when (wg-restore-buffer buf t)
        ;; Restore various positions in WINDOW from their values in WIN
        (let ((window (or selwin (selected-window))))
          (wg-with-slots win
              ((win-point wg-win-point)
               (win-start wg-win-start)
               (win-hscroll wg-win-hscroll))
            (set-window-start window win-start t)
            (set-window-hscroll window win-hscroll)
            (set-window-point
             window
             (cond
              ((eq win-point :max) (point-max))
              (t win-point)))
            (when (>= win-start (point-max)) (recenter))))

        ;; restore dedicated window
        (set-window-dedicated-p selwin (wg-win-dedicated win))))
    (ignore-errors
      (set-window-prev-buffers
       selwin (wg-unpickel (wg-win-parameter win 'prev-buffers)))
      (set-window-next-buffers
       selwin (wg-unpickel (wg-win-parameter win 'next-buffers))))
    (dolist (param '(window-side window-slot))
      (let ((value (wg-win-parameter win param)))
        (when value
          (set-window-parameter selwin param value))))))


(defun wg-window-point (window)
  "Return `point' or :max.  WINDOW is an window object."
  (let ((p (window-point window)))
    (if (= p (point-max)) :max p)))

(defun wg-set-win-parameter (win parameter value)
  "Set WIN's value of PARAMETER to VALUE.
SESSION nil means use the current session.
Return value."
  (wg-set-parameter (wg-win-parameters win) parameter value)
  value)
;; (wg-win-parameters (wg-window-to-win (selected-window)))

(defun wg-window-to-win (&optional window)
  "Return the serialization (a wg-win) of Emacs window WINDOW."
  (let ((window (or window (selected-window)))
        (selected (eq window (selected-window)))
        win)
    (with-selected-window window
      (setq win
            (wg-make-win
             :edges              (window-edges window)
             :point              (wg-window-point window)
             :start              (window-start window)
             :hscroll            (window-hscroll window)
             :selected           selected
             :minibuffer-scroll  (eq window minibuffer-scroll-window)
             :dedicated          (window-dedicated-p window)
             :buf-uid            (wg-buffer-uid-or-add (window-buffer window))))
      ;; To solve: https://github.com/pashinin/workgroups2/issues/51
      ;; shouldn't ignore here
      (ignore-errors
        (wg-set-win-parameter
         win 'next-buffers (wg-pickel (remove nil (cl-subseq (window-next-buffers window) 0 4))))
        (wg-set-win-parameter
         win 'prev-buffers (wg-pickel (remove nil (cl-subseq (window-prev-buffers window) 0 4)))))
      (dolist (param '(window-side window-slot))
        (let ((value (window-parameter window param)))
          (when value
            (wg-set-win-parameter win param value)))))
    win))

(defun wg-w-edges (w)
  "Return W's edge list."
  (cl-etypecase w
    (wg-win (wg-win-edges w))
    (wg-wtree (wg-wtree-edges w))))

(defun wg-copy-w (w)
  "Return a copy of W.  W should be a wg-win or a wg-wtree."
  (cl-etypecase w
    (wg-win (wg-copy-win w))
    (wg-wtree (wg-copy-wtree w))))

(defun wg-set-edges (w edges)
  "Set W's EDGES list, and return W."
  (cl-etypecase w
    (wg-win (setf (wg-win-edges w) edges))
    (wg-wtree (setf (wg-wtree-edges w) edges)))
  w)

(defun wg-normalize-wtree (wtree)
  "Clean up and return a new wtree from WTREE.
Recalculate the edge lists of all sub-wins, and remove sub-wins
outside of WTREE's bounds.  If there's only one element in the
new wlist, return it instead of a new wtree."
  (if (wg-win-p wtree) wtree
    (wg-with-slots wtree ((dir wg-wtree-dir)
                          (wlist wg-wtree-wlist))
      (wg-with-bounds wtree dir (ls1 hs1 lb1 hb1)
        (let* ((min-size (if dir wg-window-min-height wg-window-min-width))
               (max (- hb1 1 min-size))
               (lastw (car (last wlist))))
          (cl-labels
              ((mapwl
                (wl)
                (wg-dbind (sw . rest) wl
                  (cons (wg-normalize-wtree
                         (wg-set-bounds
                          sw dir ls1 hs1 lb1
                          (setq lb1 (if (eq sw lastw) hb1
                                      (let ((hb2 (+ lb1 (wg-w-size sw dir))))
                                        (if (>= hb2 max) hb1 hb2))))))
                        (when (< lb1 max) (mapwl rest))))))
            (let ((new (mapwl wlist)))
              (if (not (cdr new)) (car new)
                (setf (wg-wtree-wlist wtree) new)
                wtree))))))))

(defun wg-scale-wtree (wtree wscale hscale)
  "Return a copy of WTREE with its dimensions scaled by WSCALE and HSCALE.
All WTREE's sub-wins are scaled as well."
  (let ((scaled (wg-with-edges wtree (left top right bottom)
                               (wg-set-edges (wg-copy-w wtree)
                                             (list left
                                                   top
                                                   (+ left (truncate (* (- right  left) wscale)))
                                                   (+ top  (truncate (* (- bottom top) hscale))))))))
    (if (wg-win-p wtree) scaled
      (wg-asetf (wg-wtree-wlist scaled)
                (wg-docar (sw it) (wg-scale-wtree sw wscale hscale)))
      scaled)))

(defun wg-wtree-buf-uids (wtree)
  "Return a new list of the buf uids of all wins in WTREE."
  (if (not wtree)
      (error "WTREE is nil in `wg-wtree-buf-uids'!"))
  (wg-flatten-wtree wtree 'wg-win-buf-uid))

(defun wg-wtree-unique-buf-uids (wtree)
  "Return a list of the unique buf uids of all wins in WTREE."
  (cl-remove-duplicates (wg-wtree-buf-uids wtree) :test 'string=))

(defun wg-reset-window-tree ()
  "Delete all but one window in `selected-frame'.
Then reset various parameters of that window in preparation for restoring a wtree."
  (delete-other-windows)
  (set-window-dedicated-p nil nil))

(defun wg-restore-window-tree-helper (w)
  "Recursion helper for `wg-restore-window-tree' W."
  (if (wg-wtree-p w)
      (cl-loop with dir = (wg-wtree-dir w)
               for (win . rest) on (wg-wtree-wlist w)
               do (when rest (split-window nil (wg-w-size win dir) (not dir)))
               do (wg-restore-window-tree-helper win))
    (wg-restore-window w)
    (when (wg-win-selected w)
      (setq wg-window-tree-selected-window (selected-window)))
    (when (wg-win-minibuffer-scroll w)
      (setq minibuffer-scroll-window (selected-window)))
    (other-window 1)))

(defun wg-restore-window-tree (wtree)
  "Restore WTREE in `selected-frame'."
  (let ((window-min-width wg-window-min-width)
        (window-min-height wg-window-min-height)
        (wg-window-tree-selected-window nil))
    (wg-reset-window-tree)
    (wg-restore-window-tree-helper wtree)
    (and wg-window-tree-selected-window
         (select-window wg-window-tree-selected-window))))

(defun wg-window-tree-to-wtree (&optional window-tree)
  "Return the serialization (a wg-wtree) of Emacs window tree WINDOW-TREE."
  (wg-barf-on-active-minibuffer)
  (unless window-tree
    (setq window-tree (window-tree)))
  (cl-labels
      ((inner (w) (if (windowp w) (wg-window-to-win w)
                    (wg-dbind (dir edges . wins) w
                      (wg-make-wtree
                       :dir    dir
                       :edges  edges
                       :wlist  (mapcar #'inner wins))))))
    (let ((w (car window-tree)))
      (when (and (windowp w) (window-minibuffer-p w))
        (error "Workgroups can't operate on minibuffer-only frames"))
      (inner w))))

(defun wg-flatten-wtree (wtree &optional key)
  "Return a new list by flattening WTREE.
KEY non returns returns a list of WTREE's wins.
KEY non-nil returns a list of the results of calling KEY on each win."
  (cl-labels
      ((inner (w) (if (wg-win-p w) (list (if key (funcall key w) w))
                    (cl-mapcan #'inner (wg-wtree-wlist w)))))
    (inner wtree)))

(defun wg-frame-to-wconfig (&optional frame)
  "Return the serialization (a wg-wconfig) of Emacs frame FRAME.
FRAME nil defaults to `selected-frame'."
  (let* ((frame (or frame (selected-frame)))
         (fullscrn (frame-parameter frame 'fullscreen)))
    (wg-make-wconfig
     :left                  (frame-parameter frame 'left)
     :top                   (frame-parameter frame 'top)
     :width                 (frame-parameter frame 'width)
     :height                (frame-parameter frame 'height)
     :parameters            `((fullscreen . ,fullscrn))
     :vertical-scroll-bars  (frame-parameter frame 'vertical-scroll-bars)
     :scroll-bar-width      (frame-parameter frame 'scroll-bar-width)
     :wtree                 (wg-window-tree-to-wtree (window-tree frame))
     )))

(defun wg-current-wconfig ()
  "Return the current wconfig.
If `wg-current-wconfig' is non-nil, return it.  Otherwise return
`wg-frame-to-wconfig'."
  (or (frame-parameter nil 'wg-current-wconfig)
      (wg-frame-to-wconfig)))

(defun wg-wconfig-buf-uids (wconfig)
  "Return WCONFIG's wtree's `wg-wtree-buf-uids'."
  (if (not (wg-wconfig-wtree wconfig))
      (error "WTREE is nil in `wg-wconfig-buf-uids'!"))
  (wg-wtree-unique-buf-uids (wg-wconfig-wtree wconfig)))

(defun wg-wconfig-restore-frame-position (wconfig &optional frame)
  "Use WCONFIG to restore FRAME's position.
If frame is nil then `selected-frame'."
  (let* ((left (wg-wconfig-left wconfig))
         (top (wg-wconfig-top wconfig)))
    ;; Check that arguments are integers
    ;; Problem: https://github.com/pashinin/workgroups2/issues/15
    (when wg-debug
      (message "wg-wconfig-restore-frame-position called => %s %s %s" wconfig left top))
    (when (and (integerp left)
               (integerp top))
      (set-frame-position frame left top))))

(defun wg-wconfig-restore-scroll-bars (wconfig)
  "Restore `selected-frame's scroll-bar settings from WCONFIG."
  (set-frame-parameter
   nil 'vertical-scroll-bars (wg-wconfig-vertical-scroll-bars wconfig))
  (set-frame-parameter
   nil 'scroll-bar-width (wg-wconfig-scroll-bar-width wconfig)))

(defun wg-scale-wconfigs-wtree (wconfig new-width new-height)
  "Scale WCONFIG's wtree with NEW-WIDTH and NEW-HEIGHT.
Return a copy WCONFIG's wtree scaled with `wg-scale-wtree' by the
ratio or NEW-WIDTH to WCONFIG's width, and NEW-HEIGHT to
WCONFIG's height."
  (when wg-debug
    (message "wg-scale-wconfigs-wtree called => %s %s %s %s"
             new-width new-height
             (wg-wconfig-width wconfig) (wg-wconfig-height wconfig)))
  (wg-normalize-wtree
   (wg-scale-wtree
    (wg-wconfig-wtree wconfig)
    (/ (float new-width)  (wg-wconfig-width wconfig))
    (/ (float new-height) (wg-wconfig-height wconfig)))))

(defun wg-scale-wconfig-to-frame (wconfig)
  "Scale WCONFIG buffers to fit current frame size.
Return a scaled copy of WCONFIG."
  (interactive)
  (wg-scale-wconfigs-wtree wconfig
                           (frame-parameter nil 'width)
                           (frame-parameter nil 'height)))

(defun wg-restore-frames ()
  "Try to recreate opened frames, take info from session's 'frame-list parameter."
  (interactive)
  (delete-other-frames)
  (when (wg-get-current-session)
    (let ((fl (wg-session-parameter 'frame-list nil (wg-get-current-session)))
          (frame (selected-frame)))
      (when wg-debug
        (message "wg-restore-frames called => %s" fl))
      (mapc (lambda (wconfig)
              (with-selected-frame (make-frame)
                (wg-restore-wconfig wconfig)))
            fl)
      (select-frame-set-input-focus frame))))

;; FIXME: throw a specific error if the restoration was unsuccessful
(defun wg-restore-wconfig (wconfig &optional frame)
  "Restore a workgroup configuration WCONFIG in a FRAME.
Runs each time you're switching workgroups."
  (unless frame (setq frame (selected-frame)))
  (let ((params (wg-wconfig-parameters wconfig)))
    (wg-barf-on-active-minibuffer)

    (when wg-debug
      (message "wg-restore-wconfig called => %s" params))

    ;; restore scroll bars
    (wg-wconfig-restore-scroll-bars wconfig)

    (when (null (wg-get-current-workgroup t))
      (when wg-debug
        (message "set frame fullscreen parameters"))
      (set-frame-parameter frame 'fullscreen
                           (if (assoc 'fullscreen params)
                               (cdr (assoc 'fullscreen params))
                             nil)))

    ;; Restore frame position
    (when (and (not (frame-parameter nil 'fullscreen))
               (null (wg-get-current-workgroup t)))
      (when wg-debug
        (message "restore frame position"))
      (wg-wconfig-restore-frame-position wconfig frame))

    ;; Restore buffers
    (wg-restore-window-tree (wg-scale-wconfig-to-frame wconfig))))

(require 'workgroups2-support)

;;; buffer-local variable serdes

(defun wg-serialize-buffer-mark-ring ()
  "Return a new list of the positions of the mark in `mark-ring'."
  (mapcar 'marker-position mark-ring))

(defun wg-deserialize-buffer-mark-ring (positions)
  "Set `mark-ring' to a new list of markers created from POSITIONS."
  (setq mark-ring
        (mapcar (lambda (pos) (set-marker (make-marker) pos))
                positions)))

(defun wg-deserialize-buffer-major-mode (major-mode-symbol)
  "Conditionally restore MAJOR-MODE-SYMBOL in `current-buffer'."
  (and (fboundp major-mode-symbol)
       (not (eq major-mode-symbol major-mode))
       (funcall major-mode-symbol)))

(defun wg-deserialize-buffer-local-variables (buf)
  "Restore BUF's buffer local variables in `current-buffer'."
  (cl-loop for ((var . val) . rest) on (wg-buf-local-vars buf)
           do
           (let ((it (assq var wg-buffer-local-variables-alist)))
             (when (assq var wg-buffer-local-variables-alist)
               (wg-dbind (var _ser des) it
                         (if des (funcall des val)
                           (set var val)))))))

(defmacro wg-workgroup-list ()
  "List of work groups."
  `(when (wg-get-current-session)
     (wg-session-workgroup-list (wg-get-current-session))))

(defmacro wg-buf-list ()
  "Return buf list."
  `(wg-session-buf-list (wg-get-current-session)))

(defun wg-restore-default-buffer (&optional switch)
  "Return `wg-default-buffer' and maybe SWITCH to it."
  (if switch
      (switch-to-buffer wg-default-buffer t)
    (get-buffer-create wg-default-buffer)))

(defun wg-restore-existing-buffer (buf &optional switch)
  "Return existing buffer from BUF and maybe SWITCH to it."
  (let* ((b (wg-find-buf-in-buffer-list buf (wg-buffer-list-emacs))))
    (when b
      (if switch (switch-to-buffer b t))
      (with-current-buffer b
        (wg-set-buffer-uid-or-error (wg-buf-uid buf))
        b))))

(defun wg-restore-file-buffer (buf &optional switch)
  "Restore BUF by finding its file and maybe SWITCH to it.
Return the created buffer.
If BUF's file doesn't exist, call `wg-restore-default-buffer'."
  (let ((file-name (wg-buf-file-name buf))
        buffer)
    (when (and file-name
               (or wg-restore-remote-buffers
                   (not (file-remote-p file-name))))
      (cond
       ((file-exists-p file-name)
        (condition-case err
            (progn
              (setq buffer (find-file-noselect file-name nil nil nil))
              (with-current-buffer buffer
                (rename-buffer (wg-buf-name buf) t)
                (wg-set-buffer-uid-or-error (wg-buf-uid buf))

                ;; restore mark
                (set-mark (wg-buf-mark buf))
                (deactivate-mark)

                (wg-deserialize-buffer-local-variables buf))
              (if switch (switch-to-buffer buffer)))
          (error
           (wg-file-buffer-error file-name (error-message-string err)))))

       ;; try directory
       ((file-directory-p (file-name-directory file-name))
        (dired (file-name-directory file-name)))

       (t
        (message "Attempt to restore nonexistent file: %S" file-name))))
    buffer))

(defun wg-restore-special-buffer (buf &optional switch)
  "Restore a buffer BUF and maybe SWITCH to it."
  (when wg-debug
    (message "wg-restore-special-buffer => buf-name=%s buf=%s switch=%s"
             (wg-buf-name buf) buf switch))
  (let* ((special-data (wg-buf-special-data buf))
         buffer)

    (when (and special-data
               (setq buffer (save-window-excursion
                              (condition-case err
                                  (let ((fn (car special-data))
                                        created-buffer)
                                    (cond
                                     ((null fn)
                                      (when wg-debug
                                        (message "fn is null. special-data=%s" special-data)))
                                     ((null (setq created-buffer (funcall fn buf)))
                                      (when wg-debug
                                        (message "(funcall fn buf) is null. special-data=%s" special-data))))
                                    created-buffer)
                                (error (message "Error deserializing %S: %S" (wg-buf-name buf) err)
                                       nil)))))
      (when switch (switch-to-buffer buffer t))
      (with-current-buffer buffer
        (wg-set-buffer-uid-or-error (wg-buf-uid buf)))
      buffer)))

(defun wg-restore-buffer (buf &optional switch)
  "Restore BUF, return it and maybe SWITCH to it."
  (let (rlt)
    (when buf
      (when wg-debug
        (message "wg-restore-buffer called => %s" buf))
      (fset 'buffer-list wg-buffer-list-original)
      (cond
       ((setq rlt (wg-restore-existing-buffer buf switch))
        (when wg-debug
          (message "wg-restore-existing-buffer succeeded.")))

       ((setq rlt (wg-restore-special-buffer buf switch))
        (when wg-debug
          (message "wg-restore-special-buffer succeeded.")))

       ((setq rlt (wg-restore-file-buffer buf switch))
        (when wg-debug
          (message "wg-restore-file-buffer succeeded.")))
       (t
        (wg-restore-default-buffer switch)
        (when wg-debug
          (message "wg-restore-default-buffer called.")))))
    rlt))

(defun wg-buffer-uid (buffer-or-name)
  "Return BUFFER-OR-NAME's buffer-local value of `wg-buffer-uid'."
  (buffer-local-value 'wg-buffer-uid (get-buffer buffer-or-name)))

(defun wg-bufobj-uid (bufobj)
  "Return BUFOBJ's uid."
  (cl-etypecase bufobj
    (buffer (wg-buffer-uid bufobj))
    (wg-buf (wg-buf-uid bufobj))
    (string (wg-bufobj-uid (get-buffer bufobj)))))

(defun wg-bufobj-name (bufobj)
  "Return BUFOBJ's buffer name."
  (cl-etypecase bufobj
    (buffer (buffer-name bufobj))
    (wg-buf (wg-buf-name bufobj))
    (string (buffer-name (get-buffer bufobj)))))

(defun wg-bufobj-file-name (bufobj)
  "Return BUFOBJ's filename."
  (cl-etypecase bufobj
    (buffer (buffer-file-name bufobj))
    (wg-buf (wg-buf-file-name bufobj))
    (string (wg-bufobj-file-name (get-buffer bufobj)))))

;; `wg-equal-bufobjs' and `wg-find-bufobj' may need to be made a lot smarter
(defun wg-equal-bufobjs (bufobj1 bufobj2)
  "Return t if BUFOBJ1 is \"equal\" to BUFOBJ2."
  (let ((fname1 (wg-bufobj-file-name bufobj1))
        (fname2 (wg-bufobj-file-name bufobj2)))
    (cond ((and fname1 fname2) (string= fname1 fname2))
          ((or fname1 fname2) nil)
          ((string= (wg-bufobj-name bufobj1) (wg-bufobj-name bufobj2)) t))))

(defun wg-find-bufobj (bufobj bufobj-list)
  "Find BUFOBJ in BUFOBJ-LIST, testing with `wg-equal-bufobjs'."
  (cl-find bufobj bufobj-list :test 'wg-equal-bufobjs))

(defun wg-find-bufobj-by-uid (uid bufobj-list)
  "Find the bufobj in BUFOBJ-LIST with uid UID."
  (cl-find uid bufobj-list :test 'string= :key 'wg-bufobj-uid))

(defun wg-find-buffer-in-buf-list (buffer-or-name buf-list)
  "Find BUFFER-OR-NAME in BUF-LIST."
  (if (wg-buffer-uid buffer-or-name)
      (wg-find-bufobj-by-uid (wg-buffer-uid buffer-or-name) buf-list)
    (wg-find-bufobj buffer-or-name buf-list)))

(defun wg-find-buf-in-buffer-list (buf buffer-list)
  "Find BUF in BUFFER-LIST."
  (or (wg-find-bufobj-by-uid (wg-buf-uid buf) buffer-list)
      (wg-find-bufobj buf buffer-list)))

(defun wg-find-buf-by-uid (uid)
  "Find a buf in `wg-buf-list' by UID."
  (when uid
    (wg-find-bufobj-by-uid uid (wg-buf-list))))

(defun wg-set-buffer-uid-or-error (uid)
  "Change UID value of a BUFFER's local var `wg-buffer-uid'."
  (if wg-buffer-uid (setq wg-buffer-uid uid)))

(defun wg-buffer-special-data (buffer)
  "Return BUFFER's auxiliary serialization, or nil."
  (when wg-debug
    (message "wg-buffer-special-data is called => %s" buffer))
  (let* ((rlt (cl-some (lambda (fn)
                         (let ((special-data (funcall fn buffer)))
                           (when wg-debug
                             (message "fn=%s special-data=%s" fn special-data))
                           special-data))
                       wg-special-buffer-serdes-functions)))
    (when wg-debug
      (message "wg-buffer-special-data was called => %s" rlt))
    rlt))

(defun wg-serialize-buffer-local-variables ()
  "Return an alist of buffer-local variable symbols and their values.
See `wg-buffer-local-variables-alist' for details."
  (wg-docar (entry wg-buffer-local-variables-alist)
    (wg-dbind (var ser _des) entry
      (when (local-variable-p var)
        (cons var (if ser (funcall ser) (symbol-value var)))))))

(defun wg-buffer-to-buf (buffer)
  "Return the serialization (a wg-buf) of Emacs buffer BUFFER."
  (with-current-buffer buffer
    (wg-make-buf
     :name           (buffer-name)
     :file-name      (buffer-file-name)
     :point          (point)
     :mark           (mark t)
     :local-vars     (wg-serialize-buffer-local-variables)
     :special-data   (wg-buffer-special-data buffer))))

(defun wg-add-buffer-to-buf-list (buffer)
  "Make a buf from BUFFER, and add it to `wg-buf-list' if necessary.
If there isn't already a buf corresponding to BUFFER in
`wg-buf-list', make one and add it.  Return BUFFER's uid
in either case."
  (when buffer
    (with-current-buffer buffer
      (let* ((found (wg-find-buffer-in-buf-list buffer (wg-buf-list))))
        (setq wg-buffer-uid
              (if found (wg-buf-uid found)
                (let ((buf (wg-buffer-to-buf buffer)))
                  (push buf (wg-buf-list))
                  (wg-buf-uid buf))))))))

(defun wg-buffer-uid-or-add (buffer)
  "Return BUFFER's uid.
If there isn't already a buf corresponding to BUFFER in
`wg-buf-list', make one and add it."
  (or (wg-buffer-uid buffer) (wg-add-buffer-to-buf-list buffer)))

(defun wg-bufobj-uid-or-add (bufobj)
  "If BUFOBJ is a wg-buf, return its uid.
If BUFOBJ is a buffer or a buffer name, see `wg-buffer-uid-or-add'."
  (cl-etypecase bufobj
    (wg-buf (wg-buf-uid bufobj)) ;; possibly also add to `wg-buf-list'
    (buffer (wg-buffer-uid-or-add bufobj))
    (string (wg-bufobj-uid-or-add (get-buffer bufobj)))))

(defun wg-update-buffer-in-buf-list (&optional buffer)
  "Update BUFFER's corresponding buf in `wg-buf-list'.
BUFFER nil defaults to `current-buffer'."
  (let* ((buffer (or buffer (current-buffer)))
         (uid (wg-buffer-uid buffer))
         (old-buf (wg-find-buf-by-uid uid))
         (new-buf (wg-buffer-to-buf buffer)))
    (when (and uid old-buf new-buf)
      (setf (wg-buf-uid new-buf) (wg-buf-uid old-buf))
      (wg-asetf (wg-buf-list) (cons new-buf (remove old-buf it))))))

(defcustom wg-no-confirm-on-destructive-operation nil
  "Do not request confirmation before various destructive operations."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-minibuffer-message-timeout 0.75
  "Bound to `minibuffer-message-timeout' when messaging while the
minibuffer is active."
  :type 'float
  :group 'workgroups)

(defun wg-read-object (prompt test warning &optional initial-contents keymap
                              read hist default-value inherit-input-method)
  "PROMPT for an object that satisfies TEST.  WARNING if necessary.
INITIAL-CONTENTS KEYMAP READ HIST DEFAULT-VALUE
INHERIT-INPUT-METHOD are `read-from-minibuffer's args."
  (cl-labels ((read () (read-from-minibuffer
                        prompt initial-contents keymap read hist
                        default-value inherit-input-method)))
    (let ((obj (read)))
      (when (and (equal obj "") default-value) (setq obj default-value))
      (while (not (funcall test obj))
        (message warning)
        (sit-for wg-minibuffer-message-timeout)
        (setq obj (read)))
      obj)))

(defun wg-read-new-workgroup-name (&optional prompt)
  "Read a non-empty name string from the minibuffer.
Print PROMPT"
  (let ((default (wg-new-default-workgroup-name)))
    (wg-read-object
     (or prompt (format "Name (default: %S): " default))
     (lambda (new) (and (stringp new)
                        (not (equal new ""))))
     "Please enter a non-empty name"
     nil nil nil nil default)))

(defun wg-minibuffer-inactive-p ()
  "Return t when `minibuffer-depth' is zero, nil otherwise."
  (zerop (minibuffer-depth)))

(defun wg-barf-on-active-minibuffer ()
  "Throw an error when the minibuffer is active."
  (when (not (wg-minibuffer-inactive-p))
    (error "Exit minibuffer to use workgroups functions!")))

(defun wg-flag-workgroup-modified (&optional workgroup)
  "Set WORKGROUP's and the current session's modified flags."
  (unless workgroup
    (setq workgroup (wg-get-workgroup nil t)))
  (when workgroup
    (setf (wg-workgroup-modified workgroup) t)))

(defun wg-get-current-workgroup (&optional noerror frame)
  "Return current workgroup in frame.
Error unless NOERROR, in FRAME if specified."
  (or wg-current-workgroup
      (if (frame-parameter frame 'wg-current-workgroup-uid)
          (wg-find-workgroup-by :uid (frame-parameter frame 'wg-current-workgroup-uid) noerror)
        (unless noerror (error "No current workgroup in this frame")))))

(defun wg-set-current-workgroup (workgroup &optional frame)
  "Set the current workgroup to WORKGROUP in FRAME.
WORKGROUP should be a workgroup or nil."
  (set-frame-parameter frame 'wg-current-workgroup-uid
                       (when workgroup (wg-workgroup-uid workgroup))))

(defun wg-current-workgroup-p (workgroup &optional frame)
  "Return t when WORKGROUP is the current workgroup of FRAME, nil otherwise."
  (eq workgroup (wg-get-current-workgroup t frame)))

(defun wg-get-workgroup (obj &optional noerror)
  "Return a workgroup from OBJ.
If OBJ is a workgroup, return it.
If OBJ is a string, return the workgroup named OBJ, or error unless NOERROR.
If OBJ is nil, return the current workgroup, or error unless NOERROR."
  (cond ((wg-workgroup-p obj) obj)
        ((stringp obj) (wg-find-workgroup-by :name obj noerror))
        ((null obj) (wg-get-current-workgroup noerror))
        (t (error "Can't get workgroup from type:: %S" (type-of obj)))))

(defun wg-workgroup-saved-wconfigs-buf-uids (workgroup)
  "Return a new list of all unique buf uids in WORKGROUP's base wconfig."
  (cl-reduce 'wg-string-list-union
             (wg-workgroup-saved-wconfigs workgroup)
             :key 'wg-wconfig-buf-uids))

(defun wg-workgroup-all-buf-uids (workgroup)
  "Return a new list of all unique buf uids in WORKGROUP."
  (cl-reduce 'wg-string-list-union
             (list (wg-wconfig-buf-uids (wg-workgroup-base-wconfig workgroup))
                   (wg-workgroup-saved-wconfigs-buf-uids workgroup))))

(defun wg-restore-workgroup (workgroup)
  "Restore WORKGROUP in `selected-frame'."
  (wg-update-current-workgroup-working-wconfig)
  (wg-restore-wconfig (wg-workgroup-working-wconfig workgroup)))

(defun wg-workgroup-list-or-error (&optional noerror)
  "Return workgroup list. Or scream unless NOERROR."
  (if (wg-get-current-session noerror)
      (or (wg-session-workgroup-list (wg-get-current-session noerror))
          (unless noerror (error "No workgroups are defined")))
    (unless noerror (error "Current session is nil.  No workgroups are defined"))))

(defun wg-find-workgroup-by (slotkey value &optional noerror)
  "Return the workgroup on which by SLOTKEY and VALUE."
  (let ((accessor (cl-ecase slotkey
                    (:name 'wg-workgroup-name)
                    (:uid  'wg-workgroup-uid))))
    (or (cl-find value (wg-workgroup-list-or-error noerror) :test 'equal :key accessor)
        (unless noerror
          (error "There are no workgroups with a %S of %S"
                 accessor value)))))

(defun wg-get-session-from-file ()
  "Get session from session file."
  (let ((session (read (wg-read-text wg-session-file))))
    (unless (wg-session-p session)
      (error "%S is not a Workgroups session file" wg-session-file))
    (when session
      (setf (wg-session-file-name session) wg-session-file))
    session))

(defun wg-workgroup-names ()
  "Get all workgroup names."
  (when (and wg-session-file
             (file-exists-p wg-session-file))
    (mapcar (lambda (group)
              ;; re-shape group for `completing-read'
              (cons (wg-workgroup-name group) group))
            (wg-session-workgroup-list
             (wg-get-session-from-file)))))

(defun wg-new-default-workgroup-name ()
  "Return a new, unique, default workgroup name."
  (let ((names (wg-workgroup-names)) (index -1) result)
    (while (not result)
      (let ((new-name (format "wg%s" (cl-incf index))))
        (unless (member new-name names)
          (setq result new-name))))
    result))

(defun wg-query-and-save-if-modified ()
  "Query for save when current session or any of its workgroups are modified."
  (let ((wg-modified-p (and (wg-get-current-session)
                            (or (cl-some 'wg-workgroup-modified (wg-workgroup-list))))))
    (or (not wg-modified-p)
        (when (y-or-n-p "Save modified workgroups? ")
          (wg-save-session)))))

(defun wg-add-workgroup (workgroup)
  "Add WORKGROUP to `wg-workgroup-list' at the end.
If a workgroup with the same name exists, overwrite it."
  (let ((group (wg-find-workgroup-by :name (wg-workgroup-name workgroup) t))
        index)
    (when group
      (setq index (cl-position group (wg-workgroup-list-or-error)))
      (wg-delete-workgroup group))

    (wg-asetf (wg-workgroup-list)
              (wg-insert-before workgroup it (or index (length it))))
    workgroup))

(defun wg-make-and-add-workgroup (name)
  "Create a workgroup named NAME with current `window-tree'.
Add it to `wg-workgroup-list'."
  (when (wg-find-workgroup-by :name name t)
    (unless (or wg-no-confirm-on-destructive-operation
                (y-or-n-p (format "%S exists.  Overwrite? " name)))
      (error "Canceled")))

  (let* ((workgroup (wg-make-workgroup
                     :name name
                     :base-wconfig (wg-current-wconfig)))
         (uid (wg-workgroup-uid workgroup)))

    (when (wg-find-workgroup-by :uid uid t)
      (error "A workgroup with uid %S already exists" uid))

    (wg-add-workgroup workgroup)))

(defun wg-get-workgroup-create (workgroup)
  "Return the workgroup specified by WORKGROUP, creating a new one if needed.
If `wg-get-workgroup' on WORKGROUP returns a workgroup, return it.
Otherwise, if WORKGROUP is a string, create a new workgroup with
that name and return it.  Otherwise error."
  (or (wg-get-workgroup workgroup t)
      (if (stringp workgroup)
          (wg-make-and-add-workgroup workgroup)
        (wg-get-workgroup workgroup))))  ; Call this again for its error message

(defun wg-switch-to-workgroup-internal (workgroup-name)
  "Switch to workgroup with WORKGROUP-NAME."
  (fset 'buffer-list wg-buffer-list-original)
  (let ((workgroup (wg-get-workgroup-create workgroup-name))
        (current (wg-get-current-workgroup t)))
    (unless (and (eq workgroup current))
      (when current (push current wg-deactivation-list))
      (unwind-protect
          (progn
            ;; Switch
            (wg-restore-workgroup workgroup)
            (wg-set-current-workgroup workgroup)
            (run-hooks 'wg-after-switch-to-workgroup-hook))
        (when current (pop wg-deactivation-list))))))

(defun wg-get-session-file ()
  "Return the path of file to save the session."
  (or (and (wg-get-current-session)
           (wg-session-file-name (wg-get-current-session)))
      wg-session-file))

(defun wg-create-workgroup (name)
  "Create and add a workgroup named NAME."
  (interactive (list (wg-read-new-workgroup-name)))

  ;; create session file if it doesn't exist
  (unless (file-exists-p (wg-get-session-file))
    (wg-reset-internal (wg-make-session))
    (wg-save-session))

  (unless (wg-get-current-session)
    ;; code extracted from `wg-open-session'.
    ;; open session but do NOT load any workgroup.
    (wg-reset-internal (wg-unpickel-session-parameters (wg-get-session-from-file))))

  (wg-switch-to-workgroup-internal (wg-make-and-add-workgroup name))

  ;; save the session file in real time
  (wg-save-session name)

  ;; I prefer simpler UI
  (message "Workgroup \"%s\" was created and saved." name)
  (wg-reset-internal nil))

(defun wg-workgroup-state-table (&optional frame)
  "Return FRAME's workgroup table, creating it first if necessary."
  (or (frame-parameter frame 'wg-workgroup-state-table)
      (let ((wtree (make-hash-table :test 'equal)))
        (set-frame-parameter frame 'wg-workgroup-state-table wtree)
        wtree)))

(defun wg-get-workgroup-state (workgroup &optional frame)
  "Return WORKGROUP's state table in a FRAME."
  (let ((uid (wg-workgroup-uid workgroup))
        (state-table (wg-workgroup-state-table frame)))
    (or (gethash uid state-table)
        (let ((wgs (wg-make-workgroup-state
                    :undo-pointer 0
                    :undo-list
                    (list (or (wg-workgroup-selected-frame-wconfig workgroup)
                              (wg-workgroup-base-wconfig workgroup))))))
          (puthash uid wgs state-table)
          wgs))))

(defmacro wg-with-undo (workgroup spec &rest body)
  "Bind WORKGROUP's undo state to SPEC and eval BODY."
  (declare (indent 2))
  (wg-dbind (state undo-pointer undo-list) spec
    `(let* ((,state (wg-get-workgroup-state ,workgroup))
            (,undo-pointer (wg-workgroup-state-undo-pointer ,state))
            (,undo-list (wg-workgroup-state-undo-list ,state)))
       ,@body)))

(defun wg-set-workgroup-working-wconfig (workgroup wconfig)
  "Set the working-wconfig of WORKGROUP to WCONFIG."
  (wg-flag-workgroup-modified workgroup)
  (setf (wg-workgroup-selected-frame-wconfig workgroup) wconfig)
  (wg-with-undo workgroup (state undo-pointer undo-list)
    (setcar (nthcdr undo-pointer undo-list) wconfig)))

(defun wg-workgroup-working-wconfig (workgroup &optional no-update)
  "Return WORKGROUP's working-wconfig.
If WORKGROUP is the current workgroup in `selected-frame', and
NO-UPDATE is nil, set its working wconfig in `selected-frame' to
`wg-current-wconfig' and return the updated wconfig.  Otherwise
return WORKGROUP's current undo state."
  (if (and (not no-update) (wg-current-workgroup-p workgroup))
      (wg-set-workgroup-working-wconfig workgroup (wg-current-wconfig))
    (wg-with-undo workgroup (state undo-pointer undo-list)
      (nth undo-pointer undo-list))))

(defun wg-update-current-workgroup-working-wconfig ()
  "Update `selected-frame's current workgroup's working-wconfig with `wg-current-wconfig'."
  (and (wg-get-current-workgroup t)
       (wg-set-workgroup-working-wconfig (wg-get-current-workgroup t) (wg-current-wconfig))))

(defun wg-workgroup-gc-buf-uids (workgroup)
  "Remove buf uids from WORKGROUP that have no referent in `wg-buf-list'."
  (wg-asetf (wg-workgroup-strong-buf-uids workgroup)
            (cl-remove-if-not 'wg-find-buf-by-uid it)
            (wg-workgroup-weak-buf-uids workgroup)
            (cl-remove-if-not 'wg-find-buf-by-uid it)))

(defun wg-pickel-workgroup-parameters (workgroup)
  "Return a copy of WORKGROUP after pickeling its parameters.
If WORKGROUP's parameters are non-nil, otherwise return
WORKGROUP."
  (if (not (wg-workgroup-parameters workgroup)) workgroup
    (let ((copy (wg-copy-workgroup workgroup)))
      (wg-asetf (wg-workgroup-parameters copy) (wg-pickel it))
      copy)))

(defun wg-unpickel-workgroup-parameters (workgroup)
  "If WORKGROUP's parameters are non-nil, return a copy of
WORKGROUP after unpickeling its parameters.  Otherwise return
WORKGROUP."
  (if (not (wg-workgroup-parameters workgroup)) workgroup
    (let ((copy (wg-copy-workgroup workgroup)))
      (wg-asetf (wg-workgroup-parameters copy) (wg-unpickel it))
      copy)))

(defun wg-delete-workgroup (workgroup)
  "Remove WORKGROUP from `wg-workgroup-list'.
Delete references to it by `wg-workgroup-state-table', `wg-current-workgroup'."
  (dolist (frame (frame-list))
    (remhash (wg-workgroup-uid workgroup) (wg-workgroup-state-table frame))
    (when (wg-current-workgroup-p workgroup frame)
      (wg-set-current-workgroup nil frame)))
  (setf (wg-workgroup-list) (remove workgroup (wg-workgroup-list-or-error)))
  workgroup)

(defun wg-read-text (path)
  "Read text with PATH, using `utf-8' coding."
  (decode-coding-string
   (with-temp-buffer
     (set-buffer-multibyte nil)
     (setq buffer-file-coding-system 'binary)
     (insert-file-contents-literally path)
     (buffer-substring-no-properties (point-min) (point-max)))
   'utf-8))

(defun wg-open-session ()
  "Load a session visiting `wg-session-file', creating one if none already exists."
  (cond
   ((file-exists-p wg-session-file)
    (wg-reset-internal (wg-unpickel-session-parameters (wg-get-session-from-file)))

    (if wg-control-frames (wg-restore-frames))

    (when (wg-workgroup-list)
      (wg-switch-to-workgroup-internal (car (wg-workgroup-list))))
    (wg-mark-everything-unmodified))

   (t
    (wg-query-and-save-if-modified)
    (wg-reset-internal (wg-make-session :file-name wg-session-file))
    (message "(New Workgroups session file)"))))

(defmacro wg-insert-and-indent (string)
  "Insert and indent STRING."
  `(let ((print-level nil)
         (print-length nil)
         (lisp-indent-function 'lisp-indent-function))
     (insert (format "%S" ,string))
     ;; indent
     (goto-char (point-min))
     (backward-prefix-chars)
     (pp-buffer)))

(defun wg-write-sexp-to-file (sexp file)
  "Write a printable (and human-readable) representation of SEXP to FILE."
  (with-temp-buffer
    (wg-insert-and-indent sexp)
    (write-file file)))

;; FIXME: Duplicate buf names probably shouldn't be allowed.  An unrelated error
;; causes two *scratch* buffers to be present, triggering the "uids don't match"
;; error.  Write something to remove buffers with duplicate names.
(defun wg-perform-session-maintenance ()
  "Perform various maintenance operations on the current Workgroups session."
  (wg-update-current-workgroup-working-wconfig)

  ;; Update every workgroup's base wconfig with `wg-workgroup-update-base-wconfig'
  (dolist (workgroup (wg-workgroup-list))
    (let ((selected (wg-workgroup-selected-frame-wconfig workgroup)))
      (when selected
        (setf (wg-workgroup-base-wconfig workgroup) selected
              (wg-workgroup-selected-frame-wconfig workgroup) nil))))

  ;; Garbage collection

  ;; Commenting this will cause a constantly growing session file:
  ;; (tried to comment this block to solve https://github.com/pashinin/workgroups2/issues/48)
  (let ((all-buf-uids (wg-all-buf-uids)))
    (wg-asetf (wg-buf-list)
              (cl-remove-if-not (lambda (uid) (member uid all-buf-uids)) it
                                :key 'wg-buf-uid)))

  (mapc 'wg-workgroup-gc-buf-uids (wg-workgroup-list))  ; Remove buf uids that have no referent in `wg-buf-list'
  (mapc 'wg-update-buffer-in-buf-list (wg-buffer-list-emacs)))

(defun wg-save-session (&optional workgroup-name)
  "Save the current Workgroups session if it's been modified.
When WORKGROUP-NAME is not nil, only save the work group with this name."
  (let* ((filename (wg-get-session-file)))
    (unless (file-writable-p filename)
      (error "File %s can't be written to" filename))
    (wg-perform-session-maintenance)
    (setf (wg-session-file-name (wg-get-current-session)) filename)

    ;; Save opened frames as a session parameter "frame-list".
    ;; Exclude `selected-frame' and daemon one (if any).
    ;; http://stackoverflow.com/questions/21151992/why-emacs-as-daemon-gives-1-more-frame-than-is-opened
    (if wg-control-frames
        (let ((fl (frame-list)))
          (mapc (lambda (frame)
                  (if (string-equal "initial_terminal" (terminal-name frame))
                      (delete frame fl)))
                fl)
          (setq fl (delete (selected-frame) fl))
          (wg-set-session-parameter 'frame-list (mapcar 'wg-frame-to-wconfig fl))))

    (let ((copy (wg-copy-session (wg-get-current-session))))
      (when (wg-session-parameters copy)
        (wg-asetf (wg-session-parameters copy) (wg-pickel it)))
      (wg-asetf (wg-session-workgroup-list copy)
                (cl-mapcar 'wg-pickel-workgroup-parameters it))
      (wg-write-sexp-to-file copy filename))

    (wg-mark-everything-unmodified)))

(defun wg-reset-internal (session)
  "Reset Workgroups, setting current session object to SESSION.
Resets all frame parameters, buffer-local vars, current session
object, etc.  SESSION nil defaults to a new, blank session."

  (dolist (frame (frame-list))
    (set-frame-parameter frame 'wg-workgroup-state-table nil)
    (set-frame-parameter frame 'wg-current-workgroup-uid nil))

  (dolist (buffer (wg-buffer-list-emacs))
    (with-current-buffer buffer (setq wg-buffer-uid nil)))

  (setq wg-current-session session))

(defun wg-all-buf-uids ()
  "Return the union of all buf-uids."
  (cl-union (cl-reduce 'wg-string-list-union
                       (wg-session-workgroup-list (wg-get-current-session))
                       :key 'wg-workgroup-all-buf-uids)
            (delq nil (mapcar 'wg-buffer-uid (wg-buffer-list-emacs)))
            :test 'string=))

(defun wg-mark-everything-unmodified ()
  "Mark the session and all workgroups as unmodified."
  (dolist (workgroup (wg-workgroup-list))
    (setf (wg-workgroup-modified workgroup) nil)))

(defun wg-session-parameter (parameter &optional default session)
  "Return session's value for PARAMETER.
If PARAMETER is not found, return DEFAULT which defaults to nil.
SESSION nil defaults to the current session."
  (wg-aget (wg-session-parameters (or session (wg-get-current-session)))
           parameter default))

(defun wg-set-session-parameter (parameter value)
  "Set PARAMETER to VALUE in SESSION.
SESSION nil means use the current session.  Return value."
  (when wg-debug
    (message "wg-set-session-parameter => %s %s" parameter values))
  (when (wg-get-current-session)
    (wg-set-parameter (wg-session-parameters (wg-get-current-session)) parameter value)
    value))

(defun wg-unpickel-session-parameters (session)
  "Return a copy of SESSION after unpickeling its parameters.
And the parameters of all its workgroups."
  (let ((copy (wg-copy-session session)))
    (when (wg-session-parameters copy)
      (wg-asetf (wg-session-parameters copy) (wg-unpickel it)))
    (wg-asetf (wg-session-workgroup-list copy)
              (cl-mapcar 'wg-unpickel-workgroup-parameters it))
    copy))

(defun wg-workgroup-associated-buf-uids ()
  "Return a new list containing all of 's associated buf uids."
  (let ((group (wg-get-current-workgroup t)))
    (when group
      (append (wg-workgroup-strong-buf-uids group)
              (wg-workgroup-weak-buf-uids group)))))

;;;###autoload
(defun workgroups-mode (&optional arg)
  "Turn `workgroups-mode' on and off.
ARG is nil - toggle
ARG >= 1   - turn on
ARG == 0   - turn off
ARG is anything else, turn on `workgroups-mode'."
  (interactive (list current-prefix-arg))
  (setq workgroups-mode
        (cond ((not arg) (not workgroups-mode))
              ((integerp arg) (if (> arg 0) t nil))
              (t)))
  (when workgroups-mode
    (if (boundp 'desktop-restore-frames)
        (setq desktop-restore-frames nil))
    (wg-add-workgroups-mode-minor-mode-entries))
  workgroups-mode)

;;;###autoload
(defun wg-open-workgroup (&optional group-name)
  "Open specific workgroup by GROUP-NAME."
  (interactive)
  (let ((group-names (wg-workgroup-names)))
    (cond
     (group-names
      (unless group-name
        (setq group-name
              (completing-read "Select work group: " group-names)))
      (when group-name
        (wg-open-session)
        (wg-switch-to-workgroup-internal group-name)
        (wg-reset-internal nil)))
     (t
      (message "No workgroup is created yet.")))))

;;;###autoload
(defun wg-kill-workgroup ()
  "Delete existing workgroup."
  (interactive)
  (let ((group-names (wg-workgroup-names))
        group-name
        group)
    (cond
     ((and group-names
           (setq group-name
                 (completing-read "Select work group: " group-names))
           (y-or-n-p (format "Will the work group \"%s\" be deleted?"
                             group-name)))
      (wg-open-session)
      (when (setq group (wg-find-workgroup-by :name group-name t))
        (wg-delete-workgroup group)
        (message "Work group %s was deleted." group-name)
        (wg-save-session)))

     (t
      (message "No workgroup is created yet.")))))

(provide 'workgroups2)
;;; workgroups2.el ends here
