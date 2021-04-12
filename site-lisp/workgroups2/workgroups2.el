;;; workgroups2.el --- New workspaces for Emacs -*- coding: utf-8; lexical-binding: t -*-
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
;; Workgroups2 is an Emacs session manager.  It is based on the
;; experimental branch of the original "workgroups" extension.
;;
;; If you find a bug - please post it here:
;; https://github.com/pashinin/workgroups2/issues
;;
;; Quick start,
;;
;; - `wg-create-workgroup' to save current windows layout
;; - `wg-open-workgroup' to open saved windows layout
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
;; (setq wg-prefix-key (kbd "C-c z"))
;;
;; By default prefix is: "C-c z"
;;
;; <prefix> <key>
;;
;; <prefix> C-c    - create new workgroup
;; <prefix> C-v    - open existing workgroup
;;
;; Change workgroups session file,
;; (setq wg-session-file "~/.emacs.d/.emacs_workgroups"
;;
;;; Code:

(require 'cl-lib)

(defconst wg-version "1.2.1" "Current version of Workgroups.")

(defgroup workgroups nil
  "Workgroups for Emacs -- Emacs session manager"
  :group 'convenience)

(defcustom wg-session-file "~/.emacs_workgroups"
  "Default filename to be used to save workgroups."
  :type 'file
  :group 'workgroups)

(defcustom wg-prefix-key (kbd "C-c z")
  "Workgroups' prefix key.
Setting this variable requires that `workgroups-mode' be turned
off and then on again to take effect."
  :type 'string
  :group 'workgroups)

(defvar workgroups-mode-map nil "Workgroups Mode's keymap.")

(defvar wg-incorrectly-restored-bufs nil
  "FIXME: docstring this.")
;; TODO: check it on switching WG

(defvar wg-record-incorrectly-restored-bufs nil
  "FIXME: docstring this.")

(defcustom wg-session-load-on-start (not (daemonp))
  "Load a session file on Workgroups start.
Don't do it with Emacs --daemon option."
  :type 'boolean
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

(defcustom workgroups-mode-hook nil
  "Hook run when `workgroups-mode' is turned on."
  :type 'hook
  :group 'workgroups)

(defcustom wg-after-switch-to-workgroup-hook nil
  "Hook run by `wg-switch-to-workgroup'."
  :type 'hook
  :group 'workgroups)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; FIXME:
;;
;; Only set `wg-workgroup-base-wconfig' on `wg-save-session-as' or
;; `delete-frame' and only with the most recently changed working-wconfig.
;; Then, since it's not overwritten on every call to
;; `wg-workgroup-working-wconfig', its restoration can be retried after manually
;; recreating buffers that couldn't be restored.  So it takes over the
;; 'incorrect restoration' portion of the base wconfig's duty.  All that leaves
;; to base wconfigs is that they're a saved wconfig the user felt was important.
;; So why not allow more of of them?  A workgroup could stash an unlimited
;; number of wconfigs.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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

The `car' of each entry should be a buffer-local variable symbol.

The `cadr' of the entry should be either nil or a function of no
arguments.  If nil, the variable's value is used as-is, and
should have a readable printed representation.  If a function,
`funcall'ing it should yield a serialization of the value of the
variable.

The `caddr' of the entry should be either nil or a function of
one argument.  If nil, the serialized value from above is
assigned to the variable as-is.  It a function, `funcall'ing it
on the serialized value from above should do whatever is
necessary to properly restore the original value of the variable.
For example, in the case of `major-mode' it should funcall the
value (a major-mode function symbol) rather than just assigning
it to `major-mode'."
  :type 'alist
  :group 'workgroups)

(defcustom wg-restore-remote-buffers t
  "Restore buffers that get \"t\" with `file-remote-p'."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-frame-position t
  "Non-nil means restore frame position on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-scroll-bars t
  "Non-nil means restore scroll-bar settings on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-fringes t
  "Non-nil means restore fringe settings on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-margins t
  "Non-nil means restore margin settings on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-point t
  "Non-nil means restore `point' on workgroup restore.
This is included mainly so point restoration can be suspended
during `wg-morph' -- you probably want this non-nil."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-point-max t
  "Controls point restoration when point is at `point-max'.
If `point' is at `point-max' when a wconfig is created, put
`point' back at `point-max' when the wconfig is restored, even if
`point-max' has increased in the meantime.  This is useful in,
say, irc buffers where `point-max' is constantly increasing."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-mark t
  "Non-nil means restore mark data on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defcustom wg-restore-window-dedicated-p t
  "Non-nil means restore `window-dedicated-p' on workgroup restore."
  :type 'boolean
  :group 'workgroups)

(defvar wg-buffer-uid nil
  "Symbol for the current buffer's wg-buf's uid.
Every Workgroups buffer object (wg-buf) has a uid.  When
Workgroups creates or encounters an Emacs buffer object
corresponding to a wg-buf, it tags it with the wg-buf's uid to
unambiguously pair the two.")
(make-variable-buffer-local 'wg-buffer-uid)

(defvar wg-already-updated-working-wconfig nil
  "Flag set by `wg-update-working-wconfig-hook'.")

(defvar wg-undoify-window-configuration-change t
  "Should windows undo info be updated or not.
When you change window configuration.")

(defvar wg-current-workgroup nil "Bound to the current workgroup.")

(defvar wg-window-min-width 2
  "Bound to `window-min-width' when restoring wtrees.")

(defvar wg-window-min-height 1
  "Bound to `window-min-height' when restoring wtrees.")

(defvar wg-window-min-pad 2
  "Added to `wg-window-min-foo' to produce the actual minimum window size.")

(defvar wg-actual-min-width (+ wg-window-min-width wg-window-min-pad)
  "Actual minimum window width when creating windows.")

(defvar wg-actual-min-height (+ wg-window-min-height wg-window-min-pad)
  "Actual minimum window height when creating windows.")

(defvar wg-min-edges `(0 0 ,wg-actual-min-width ,wg-actual-min-height)
  "Smallest allowable edge list of windows created by Workgroups.")

(defvar wg-null-edges '(0 0 0 0) "Null edge list.")

(defvar wg-window-tree-selected-window nil
  "Used during wconfig restoration to hold the selected window.")

(defvar wg-buffer-workgroup nil
  "A workgroup in which this buffer most recently appeared.
Buffer-local.")
(make-variable-buffer-local 'wg-buffer-workgroup)

(defcustom wg-default-buffer "*scratch*"
  "Show this in case everything else fails.
When a buffer can't be restored, when creating a blank wg."
  :type 'string
  :group 'workgroups)

;; {{ crazy stuff to delete soon
(defconst wg-buffer-list-original (symbol-function 'buffer-list))
(defalias 'wg-buffer-list-emacs wg-buffer-list-original)

(defun buffer-list (&optional frame)
  "Redefinition of `buffer-list'.
Pass FRAME to it.
Remove file and dired buffers that are not associated with workgroup."
  (let ((res (wg-buffer-list-emacs frame))
        (wg-buf-uids (wg-workgroup-associated-buf-uids)))
    (cl-remove-if (lambda (it)
                    (and (or (buffer-file-name it)
                             (eq (buffer-local-value 'major-mode it) 'dired-mode))
                         ;;(not (member b wg-buffers))
                         (not (member (wg-buffer-uid-or-add it) wg-buf-uids))) )
                  res)))

(defconst wg-buffer-list-function (symbol-function 'buffer-list))
(fset 'buffer-list wg-buffer-list-original)
;; }}

(eval-and-compile
  ;; `wg-docar' has been used in macro.
  (defmacro wg-docar (spec &rest body)
    "do-style wrapper for `mapcar'.

\(fn (VAR LIST) BODY...)"
    (declare (indent 1))
    `(mapcar (lambda (,(car spec)) ,@body) ,(cadr spec))))

(defmacro wg-with-gensyms (syms &rest body)
  "Bind all symbols in SYMS to `gensym's, and eval BODY."
  (declare (indent 1))
  `(let (,@(mapcar (lambda (sym) `(,sym (cl-gensym))) syms)) ,@body))

(defmacro wg-dbind (args expr &rest body)
  "Bind the variables in ARGS to the result of EXPR and execute BODY.
Abbreviation of `destructuring-bind'."
  (declare (indent 2))
  `(cl-destructuring-bind ,args ,expr ,@body))

(defmacro wg-when-boundp (symbols &rest body)
  "When all SYMBOLS are bound, `eval' BODY."
  (declare (indent 1))
  `(when (and ,@(mapcar (lambda (sym) `(boundp ',sym)) symbols))
     ,@body))

(defmacro wg-dohash (spec &rest body)
  "do-style wrapper for `maphash'.

\(fn (KEY VALUE TABLE [RESULT]) BODY...)"
  (declare (indent 1))
  (wg-dbind (key val table &optional result) spec
    `(progn (maphash (lambda (,key ,val) ,@body) ,table) ,result)))

(eval-and-compile
  ;; wg-partition has been used in macro.
  (defun wg-partition (items)
    "Take ITEMS, return a list of N length sublists, offset by STEP.
Iterative to prevent stack overflow."
    (let* (acc first-2-items)
      (while items
        (setq first-2-items (if (> (length items) 1) (list (nth 0 items) (nth 1 items))
                              (list (nth 1 items))))
        (push first-2-items acc)
        (setq items (nthcdr 2 items)))
      (nreverse acc))))

(defmacro wg-asetf (&rest places-and-values)
  "Anaphoric `setf'."
  `(progn ,@(mapcar (lambda (pv)
                      `(let ((it ,(car pv)))
                         ;; Fix compile warn
                         (ignore it)
                         (setf ,@pv)))
                    (wg-partition places-and-values))))

(defmacro wg-destructuring-dolist (spec &rest body)
  "Loop over a list.
Evaluate BODY, destructuring LIST into SPEC, then evaluate RESULT
to get a return value, defaulting to nil.  The only hitch is that
spec must end in dotted style, collecting the rest of the list
into a var, like so: (a (b c) . rest)

\(fn (SPEC LIST [RESULT]) BODY...)"
  (declare (indent 1))
  (wg-dbind (loopspec list &optional result) spec
    (let ((rest (cdr (last loopspec))))
      (wg-with-gensyms (list-sym)
        `(let ((,list-sym ,list))
           (while ,list-sym
             (wg-dbind ,loopspec ,list-sym
               ,@body
               (setq ,list-sym ,rest)))
           ,result)))))

;;; numbers
(defun wg-within (num lo hi &optional hi-inclusive)
  "Return t when NUM is within bounds LO and HI.
HI-INCLUSIVE non-nil means the HI bound is inclusive."
  (and (>= num lo) (if hi-inclusive (<= num hi) (< num hi))))

(defun wg-int-to-b36-one-digit (i)
  "Return a character in 0..9 or A..Z from I, and integer 0<=I<32.
Cribbed from `org-id-int-to-b36-one-digit'."
  (cond ((not (wg-within i 0 36))
         (error "%s out of range" i))
        ((< i 10) (+ ?0 i))
        ((< i 36) (+ ?A i -10))))

(defun wg-b36-to-int-one-digit (i)
  "Turn a character 0..9, A..Z, a..z into a number 0..61.
The input I may be a character, or a single-letter string.
Cribbed from `org-id-b36-to-int-one-digit'."
  (and (stringp i) (setq i (string-to-char i)))
  (cond ((and (>= i ?0) (<= i ?9)) (- i ?0))
        ((and (>= i ?A) (<= i ?Z)) (+ (- i ?A) 10))
        (t (error "Invalid b36 character"))))

(defun wg-int-to-b36 (i &optional length)
  "Return a base 36 string from I."
  (let ((base 36) b36)
    (cl-labels ((add-digit () (push (wg-int-to-b36-one-digit (mod i base)) b36)
                           (setq i (/ i base))))
      (add-digit)
      (while (> i 0) (add-digit))
      (setq b36 (cl-map 'string 'identity b36))
      (if (not length) b36
        (concat (make-string (max 0 (- length (length b36))) ?0) b36)))))

(defun wg-b36-to-int (str)
  "Convert STR, a base-36 string, into the corresponding integer.
Cribbed from `org-id-b36-to-int'."
  (let ((result 0))
    (mapc (lambda (i)
            (setq result (+ (* result 36)
                            (wg-b36-to-int-one-digit i))))
          str)
    result))

(defmacro wg-removef-p (item seq-place &rest keys)
  "If ITEM is a `member
*' of SEQ-PLACE, remove it from SEQ-PLACE and return t.
Otherwise return nil.  KEYS can be any keywords accepted by `remove*'."
  `(> (length ,seq-place)
      (length (setf ,seq-place (cl-remove ,item ,seq-place ,@keys)))))

(defmacro wg-pushnew-p (item seq-place &rest keys)
  "If ITEM is not a `member' of SEQ-PLACE, push it to SEQ-PLACE and return t.
Otherwise return nil.  KEYS can be any keyword args accepted by `pushnew'."
  `(< (length ,seq-place)
      (length (cl-pushnew ,item ,seq-place ,@keys))))

(defun wg-insert-before (elt list index)
  "Insert ELT into LIST before INDEX."
  (cond
   ((zerop index)
    (cons elt list))
   (t
    (push elt (cdr (nthcdr (1- index) list)))
    list)))

(defun wg-string-list-union (&optional list1 list2)
  "Return the `union' of LIST1 and LIST2, using `string=' as the test.
This only exists to get rid of duplicate lambdas in a few reductions."
  (cl-union list1 list2 :test 'string=))

(defun wg-aget (alist key &optional default)
  "Return the value of KEY in ALIST. Uses `assq'.
If PARAM is not found, return DEFAULT which defaults to nil."
  (or (cdr (assq key alist)) default))

(defun wg-aput (alist key value)
  "Return a new alist from ALIST with KEY's value set to VALUE."
  (let* ((found nil)
         (new (wg-docar (kvp alist)
                (if (not (eq key (car kvp))) kvp
                  (setq found (cons key value))))))
    (if found new (cons (cons key value) new))))

(defmacro wg-defstruct (name-form &rest slot-defs)
  "`defstruct' wrapper that namespace-prefixes all generated functions.
Note: this doesn't yet work with :conc-name, and possibly other
options."
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

(defun wg-add-or-remove-hooks (remove &rest pairs)
  "Add FUNCTION to or remove it from HOOK, depending on REMOVE."
  (dolist (pair (wg-partition pairs))
    (funcall (if remove 'remove-hook 'add-hook)
             (car pair) (cadr pair))))

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
                   (wg-int-to-b36 time 4))))

(defun wg-b36-to-time (b36)
  "Parse the time in B36 string from UID."
  (cl-loop for i from 0 to 8 by 4
           collect (wg-b36-to-int (cl-subseq b36 i (+ i 4)))))
(defalias 'wg-uid-to-time 'wg-b36-to-time)

(defun wg-generate-uid ()
  "Return a new uid."
  (concat (wg-time-to-b36) "-" (wg-int-to-b36 string-chars-consed)))

(defun wg-get-value (arg)
  "Get a value of ARG if it exists."
  (if (boundp `,arg) arg))

(defmacro wg-support (mode pkg params)
  "Macro to create (de)serialization functions for a buffer.
You need to save/restore a specific MODE which is loaded from a
package PKG.  In PARAMS you give local variables to save and a
deserialization function."
  (declare (indent 2))
  `(let ((mode-str (symbol-name ,mode))
         (args ,params))

     ;; Fix compile warn.
     (ignore args)

     (eval `(defun ,(intern (format "wg-deserialize-%s-buffer" mode-str)) (buffer)
              "DeSerialization function created with `wg-support'.
Gets saved variables and runs code to restore a BUFFER."
              (when (require ',,pkg nil 'noerror)
                (wg-dbind (this-function variables) (wg-buf-special-data buffer)
                  (let ((default-directory (car variables))
                        (df (cdr (assoc 'deserialize ',,params)))
                        (user-vars (cadr variables)))
                    (if df
                        (funcall df buffer user-vars)
                      (get-buffer-create wg-default-buffer))
                    ))))
           t)

     (eval `(defun ,(intern (format "wg-serialize-%s-buffer" mode-str)) (buffer)
              "Serialization function created with `wg-support'.
Saves some variables to restore a BUFFER later."
              (when (get-buffer buffer)
                (with-current-buffer buffer
                  (when (eq major-mode ',,mode)
                    (let ((sf (cdr (assoc 'serialize ',,params)))
                          (save (cdr (assoc 'save ',,params))))
                      (list ',(intern (format "wg-deserialize-%s-buffer" mode-str))
                            (list default-directory
                                  (if sf
                                      (funcall sf buffer)
                                    (if save (mapcar 'wg-get-value save)))
                                  )))))))
           t)
     ;; Maybe change a docstring for functions
     ;;(put (intern (format "wg-serialize-%s-buffer" (symbol-name mode)))
     ;;     'function-documentation
     ;;     (format "A function created by `wg-support'."))

     ;; Add function to `wg-special-buffer-serdes-functions' variable
     (eval `(add-to-list 'wg-special-buffer-serdes-functions
                         ',(intern (format "wg-serialize-%s-buffer" mode-str)) t)
           t)
     ))

(defvar wg-current-session nil "Current session object.")
(defun wg-current-session (&optional noerror)
  "Return `wg-current-session' or error unless NOERROR."
  (or wg-current-session
      (if workgroups-mode
          (unless noerror (error "No session is defined"))
        (unless noerror
          (error "Activate workgroups with (workgroups-mode 1)")))))

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
    (marker     . wg-pickel-marker-serializer)
    ;;(window-configuration   . wg-pickel-window-configuration-serializer)
    )
  "Alist mapping types to object serialization functions.")
(defvar wg-pickel-object-deserializers
  '((s . wg-pickel-deserialize-uninterned-symbol)
    (c . wg-pickel-deserialize-cons)
    (v . wg-pickel-deserialize-vector)
    (h . wg-pickel-deserialize-hash-table)
    (b . wg-pickel-deserialize-buffer)
    (m . wg-pickel-deserialize-marker)
    (d . wg-pickel-deserialize-default)
    ;;(f . wg-pickel-deserialize-frame)
    )
  "Alist mapping type keys to object deserialization functions.")

(defvar wg-pickel-link-serializers
  '((cons       . wg-pickel-cons-link-serializer)
    (vector     . wg-pickel-vector-link-serializer)
    (hash-table . wg-pickel-hash-table-link-serializer))
  "Alist mapping types to link serialization functions.")
(defvar wg-pickel-link-deserializers
  `((c . wg-pickel-cons-link-deserializer)
    (v . wg-pickel-vector-link-deserializer)
    (h . wg-pickel-hash-table-link-deserializer))
  "Alist mapping type keys to link deserialization functions.")



;;; errors and predicates

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
  "Return a table binding unique subobjects of OBJ to ids."
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

(defun wg-pickel-deserialize-uninterned-symbol (name)
  "Return a new uninterned symbol from NAME."
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



;; vector - http://www.gnu.org/software/emacs/manual/html_node/elisp/Vector-Functions.html
;; (wg-unpickel (wg-pickel (make-vector 9 'Z)))
;;
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


;; TODO
(defun wg-pickel-window-configuration-serializer (_wc)
  "Return Window configuration WC's serialization."
  (list 'wc 1))

(defun wg-pickel-serialize-objects (binds)
  "Return a list of serializations of the objects in BINDS."
  (let (result)
    (wg-dohash (obj id binds result)
      (setq result
            (nconc (list id (funcall (wg-pickel-object-serializer obj) obj))
                   result)))))

(defun wg-pickel-deserialize-objects (serial-objects)
  "Return a hash-table of objects deserialized from SERIAL-OBJECTS."
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
  "Return BINDS after relinking all its objects according to SERIAL-LINKS."
  (wg-destructuring-dolist ((key arg1 arg2 arg3 . rest) serial-links binds)
    (funcall (wg-pickel-link-deserializer key) arg1 arg2 arg3 binds)))

(defun wg-pickel (obj)
  "Return the serialization of OBJ."
  (wg-pickelable-or-error obj)
  (let ((binds (wg-pickel-make-bindings-table obj)))
    (list wg-pickel-identifier
          (wg-pickel-serialize-objects binds)
          (wg-pickel-serialize-links binds)
          (gethash obj binds))))

(defun wg-pickel-to-string (obj)
  "Serialize OBJ to a string and return the string."
  (format "%S" (wg-pickel obj)))

(defun wg-unpickel (pickel)
  "Return the deserialization of PICKEL."
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

(defun wg-add-workgroups-mode-minor-mode-entries ()
  "Add Workgroups' minor-mode entries.
Adds entries to `minor-mode-list', `minor-mode-alist' and
`minor-mode-map-alist'."
  (cl-pushnew 'workgroups-mode minor-mode-list)
  (setq minor-mode-map-alist
        (cons (cons 'workgroups-mode (wg-make-workgroups-mode-map))
              (delete (assoc 'workgroups-mode minor-mode-map-alist)
                      minor-mode-map-alist))))

(defun wg-fill-keymap (keymap &rest binds)
  "Return KEYMAP after defining in it all keybindings in BINDS."
  (while binds
    (define-key keymap (car binds) (cadr binds))
    (setq binds (cddr binds)))
  keymap)

(defvar wg-prefixed-map
  (wg-fill-keymap
   (make-sparse-keymap)
   (kbd "C-c")        'wg-create-workgroup
   (kbd "C-v")        'wg-open-workgroup)
  "The keymap that sits on `wg-prefix-key'.")

(defun wg-make-workgroups-mode-map ()
  "Return Workgroups' minor-mode-map.
This map includes `wg-prefixed-map' on `wg-prefix-key'"
  (let ((map (make-sparse-keymap)))
    (define-key map wg-prefix-key
      wg-prefixed-map)
    (setq workgroups-mode-map map)))

(defun wg-min-size (dir)
  "Return the minimum window size in split direction DIR."
  (if dir wg-window-min-height wg-window-min-width))

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

(defun wg-w-size (w &optional height)
  "Return the width or height of W, calculated from its edge list."
  (wg-with-edges w (l1 t1 r1 b1)
    (if height (- b1 t1) (- r1 l1))))

(defun wg-adjust-w-size (w width-fn height-fn &optional new-left new-top)
  "Adjust W's width and height with WIDTH-FN and HEIGHT-FN."
  (wg-with-edges w (left top right bottom)
    (let ((left (or new-left left)) (top (or new-top top)))
      (wg-set-edges (wg-copy-w w)
                    (list left
                          top
                          (+ left (funcall width-fn  (- right  left)))
                          (+ top  (funcall height-fn (- bottom top))))))))

(defun wg-scale-w-size (w width-scale height-scale)
  "Scale W's size by WIDTH-SCALE and HEIGHT-SCALE."
  (cl-labels
      ((wscale (width)  (truncate (* width  width-scale)))
       (hscale (height) (truncate (* height height-scale))))
    (wg-adjust-w-size w #'wscale #'hscale)))

(defun wg-win-parameter (win parameter &optional default)
  "Return WIN's value for PARAMETER.
If PARAMETER is not found, return DEFAULT which defaults to nil.
SESSION nil defaults to the current session."
  (wg-aget (wg-win-parameters win) parameter default))

(defun wg-restore-window (win)
  "Restore WIN in `selected-window'."
  (let ((selwin (selected-window))
        (buf (wg-find-buf-by-uid (wg-win-buf-uid win))))
    (if (not buf)
        (wg-restore-default-buffer)
      (when (wg-restore-buffer buf t)

        ;; Restore various positions in WINDOW from their values in WIN
        ;; (wg-restore-window-positions win selwin)
        (let ((window (or selwin (selected-window))))
          (wg-with-slots win
              ((win-point wg-win-point)
               (win-start wg-win-start)
               (win-hscroll wg-win-hscroll))
            (set-window-start window win-start t)
            (set-window-hscroll window win-hscroll)
            (set-window-point
             window
             (cond ((not wg-restore-point) win-start)
                   ((eq win-point :max) (point-max))
                   (t win-point)))
            (when (>= win-start (point-max)) (recenter))))

        (when wg-restore-window-dedicated-p
          (set-window-dedicated-p selwin (wg-win-dedicated win)))))
    (ignore-errors
      (set-window-prev-buffers
       selwin (wg-unpickel (wg-win-parameter win 'prev-buffers)))
      (set-window-next-buffers
       selwin (wg-unpickel (wg-win-parameter win 'next-buffers))))
    (dolist (param '(window-side window-slot))
      (let ((value (wg-win-parameter win param)))
        (when value
          (set-window-parameter selwin param value))))))


(defun wg-window-point (ewin)
  "Return `point' or :max.  See `wg-restore-point-max'.
EWIN should be an Emacs window object."
  (let ((p (window-point ewin)))
    (if (and wg-restore-point-max (= p (point-max))) :max p)))

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
Recalculate the edge lists of all subwins, and remove subwins
outside of WTREE's bounds.  If there's only one element in the
new wlist, return it instead of a new wtree."
  (if (wg-win-p wtree) wtree
    (wg-with-slots wtree ((dir wg-wtree-dir)
                          (wlist wg-wtree-wlist))
      (wg-with-bounds wtree dir (ls1 hs1 lb1 hb1)
        (let* ((min-size (wg-min-size dir))
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
All WTREE's subwins are scaled as well."
  (let ((scaled (wg-scale-w-size wtree wscale hscale)))
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
  "Delete all but one window in `selected-frame', and reset
various parameters of that window in preparation for restoring
a wtree."
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

(defmacro wg-with-current-wconfig (frame wconfig &rest body)
  "Eval BODY with WCONFIG current in FRAME.
FRAME nil defaults to `selected-frame'."
  (declare (indent 2))
  (wg-with-gensyms (frame-sym old-value)
    `(let* ((,frame-sym (or ,frame (selected-frame)))
            (,old-value (frame-parameter ,frame-sym 'wg-current-wconfig)))
       (unwind-protect
           (progn
             (set-frame-parameter ,frame-sym 'wg-current-wconfig ,wconfig)
             ,@body)
         (when (frame-live-p ,frame-sym)
           (set-frame-parameter ,frame-sym 'wg-current-wconfig ,old-value))))))

(defun wg-make-blank-wconfig (&optional buffer)
  "Return a new blank wconfig.
BUFFER or `wg-default-buffer' is visible in the only window."
  (save-window-excursion
    (delete-other-windows)
    (switch-to-buffer (or buffer wg-default-buffer))
    (wg-frame-to-wconfig)))

;;; base wconfig updating

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
  (when wg-current-session
    (let ((fl (wg-session-parameter 'frame-list nil wg-current-session))
          (frame (selected-frame)))
      (mapc (lambda (wconfig)
              (with-selected-frame (make-frame)
                (wg-restore-wconfig wconfig)
                ))
            fl)
      (select-frame-set-input-focus frame))))

;; FIXME: throw a specific error if the restoration was unsuccessful
(defun wg-restore-wconfig (wconfig &optional frame)
  "Restore a workgroup configuration WCONFIG in a FRAME.
Runs each time you're switching workgroups."
  (unless frame (setq frame (selected-frame)))
  (let ((wg-record-incorrectly-restored-bufs t)
        (wg-incorrectly-restored-bufs nil)
        (params (wg-wconfig-parameters wconfig)))
    (wg-barf-on-active-minibuffer)
    (when wg-restore-scroll-bars
      (wg-wconfig-restore-scroll-bars wconfig))

    (when (null (wg-current-workgroup t))
      (set-frame-parameter frame 'fullscreen (if (assoc 'fullscreen params)
                                                 (cdr (assoc 'fullscreen params))
                                               nil)))

    ;; Restore frame position
    (when (and wg-restore-frame-position
               (not (frame-parameter nil 'fullscreen))
               (null (wg-current-workgroup t)))
      (wg-wconfig-restore-frame-position wconfig frame))

    ;; Restore buffers
    (wg-restore-window-tree (wg-scale-wconfig-to-frame wconfig))

    (when wg-incorrectly-restored-bufs
      (message "Unable to restore these buffers: %S\
If you want, restore them manually and try again."
               (mapcar 'wg-buf-name wg-incorrectly-restored-bufs)))))

;; specialbufs
(defcustom wg-special-buffer-serdes-functions
  '(wg-serialize-comint-buffer
    )
  "Functions providing serialization/deserialization for complex buffers.

Use `wg-support' macro and this variable will be filled
automatically.

An entry should be either a function symbol or a lambda, and should
accept a single Emacs buffer object as an argument.

When a buffer is to be serialized, it is passed to each of these
functions in turn until one returns non-nil, or the list ends.  A
return value of nil indicates that the function can't handle
buffers of that type.  A non-nil return value indicates that it
can.  The first non-nil return value becomes the buffer's special
serialization data.  The return value should be a cons, with a
deserialization function (a function symbol or a lambda) as the car,
and any other serialization data as the cdr.

When it comes time to deserialize the buffer, the deserialization
function (the car of the cons mentioned above) is passed the
wg-buf object, from which it should restore the buffer.  The
special serialization data itself can be accessed
with (cdr (wg-buf-special-data <wg-buf>)).  The deserialization
function must return the restored Emacs buffer object.

See the definitions of the functions in this list for examples of
how to write your own."
  :type 'alist
  :group 'workgroups)

;; Dired
(wg-support 'dired-mode 'dired
  `((deserialize . ,(lambda (_buffer _vars)
                      (when (or wg-restore-remote-buffers
                                (not (file-remote-p default-directory)))
                        (let ((d (wg-get-first-existing-dir)))
                          (if (file-directory-p d) (dired d))))))))

;; `Info-mode'     C-h i
(wg-support 'Info-mode 'info
  `((save . (Info-current-file Info-current-node))
    (deserialize . ,(lambda (buffer vars)
                      ;;(with-current-buffer
                      ;;    (get-buffer-create (wg-buf-name buffer))
                      (if vars
                          (if (fboundp 'Info-find-node)
                              (apply #'Info-find-node var))
                        (info)
                        (get-buffer (wg-buf-name buffer)))))))

;; `help-mode'
;; Bug: https://github.com/pashinin/workgroups2/issues/29
;; bug in wg-get-value
(wg-support 'help-mode 'help-mode
  `((save . (help-xref-stack-item help-xref-stack help-xref-forward-stack))
    (deserialize . ,(lambda (_buffer vars)
                      (wg-dbind (item stack forward-stack) vars
                        (condition-case err
                            (apply (car item) (cdr item))
                          (error (message "%s" err)))
                        (when (get-buffer "*Help*")
                          (set-buffer (get-buffer "*Help*"))
                          (wg-when-boundp (help-xref-stack help-xref-forward-stack)
                                          (setq help-xref-stack stack
                                                help-xref-forward-stack forward-stack))))))))

;; ielm
(wg-support 'inferior-emacs-lisp-mode 'ielm
  `((deserialize . ,(lambda (_buffer _vars)
                      (ielm) (get-buffer "*ielm*")))))

;; Magit status
(wg-support 'magit-status-mode 'magit
  `((deserialize . ,(lambda (_buffer _vars)
                      (if (file-directory-p default-directory)
                          (magit-status-setup-buffer default-directory)
                        (let ((d (wg-get-first-existing-dir)))
                          (if (file-directory-p d) (dired d))))))))

;; Shell
(wg-support 'shell-mode 'shell
  `((deserialize . ,(lambda (buffer _vars)
                      (shell (wg-buf-name buffer))))))

;; org-agenda buffer
(defun wg-get-org-agenda-view-commands ()
  "Return commands to restore the state of Agenda buffer.
Can be restored using \"(eval commands)\"."
  (interactive)
  (when (boundp 'org-agenda-buffer-name)
    (if (get-buffer org-agenda-buffer-name)
        (with-current-buffer org-agenda-buffer-name
          (let* ((p (or (and (looking-at "\\'") (1- (point))) (point)))
                 (series-redo-cmd (get-text-property p 'org-series-redo-cmd)))
            (if series-redo-cmd
                (get-text-property p 'org-series-redo-cmd)
              (get-text-property p 'org-redo-cmd)))))))

(defun wg-run-agenda-cmd (f)
  "Run commands F in Agenda buffer.
You can get these commands using `wg-get-org-agenda-view-commands'."
  (when (and (boundp 'org-agenda-buffer-name)
             (fboundp 'org-current-line)
             (fboundp 'org-goto-line))
    (if (get-buffer org-agenda-buffer-name)
        (save-window-excursion
          (with-current-buffer org-agenda-buffer-name
            (let* ((line (org-current-line)))
              (if f (eval f t))
              (org-goto-line line)))))))

(wg-support 'org-agenda-mode 'org-agenda
  '((serialize . (lambda (buffer)
                   (wg-get-org-agenda-view-commands)))
    (deserialize . (lambda (buffer vars)
                     (org-agenda-list)
                     (let* ((buf (get-buffer org-agenda-buffer-name)))
                       (when
                        (with-current-buffer buf
                          (wg-run-agenda-cmd vars))
                        buf))))))

;; eshell
(wg-support 'eshell-mode 'esh-mode
  '((deserialize . (lambda (buffer vars)
                     (prog1 (eshell t)
                       (rename-buffer (wg-buf-name buffer) t))))))

;; term-mode
;;
;; This should work for `ansi-term's, too, as there doesn't seem to
;; be any difference between the two except how the name of the
;; buffer is generated.
;;
(wg-support 'term-mode 'term
  `((serialize . ,(lambda (buffer)
                    (if (get-buffer-process buffer)
                        (car (last (process-command (get-buffer-process buffer))))
                      "/bin/bash")))
    (deserialize . ,(lambda (buffer vars)
                      (cl-labels ((term-window-width () 80)
                                  (window-height () 24))
                        (prog1 (term vars)
                          (rename-buffer (wg-buf-name buffer) t)))))))

;; `inferior-python-mode'
(wg-support 'inferior-python-mode 'python
            `((save . (python-shell-interpreter python-shell-interpreter-args))
              (deserialize . ,(lambda (_buffer vars)
                                (wg-dbind (pythoncmd pythonargs) vars
                                          (run-python (concat pythoncmd " " pythonargs))
                                          (let ((buf (get-buffer (process-buffer
                                                                  (python-shell-get-process)))))
                                            (when buf
                                              (with-current-buffer buf (goto-char (point-max)))
                                              buf)))))))


;; Sage shell ;;
(wg-support 'inferior-sage-mode 'sage-mode
            `((deserialize . ,(lambda (_buffer _vars)
                                (save-window-excursion
                                  (if (boundp' sage-command)
                                      (run-sage t sage-command t)))
                                (when (and (boundp 'sage-buffer) sage-buffer)
                                  (set-buffer sage-buffer)
                                  (switch-to-buffer sage-buffer)
                                  (goto-char (point-max)))))))

;; `inferior-ess-mode'     M-x R
(defvar ess-history-file)
(defvar ess-ask-about-transfile)
(defvar ess-ask-for-ess-directory)

(wg-support 'inferior-ess-mode 'ess-inf
  `((save . (inferior-ess-program))
    (deserialize . ,(lambda (buffer vars)
                      (wg-dbind (_cmd) vars
                        (let ((ess-ask-about-transfile nil)
                              (ess-ask-for-ess-directory nil)
                              (ess-history-file nil))
                          (R)
                          (get-buffer (wg-buf-name buffer))))))))

;; `inferior-octave-mode'
(wg-support 'inferior-octave-mode 'octave
  `((deserialize . ,(lambda (buffer _vars)
                      (prog1 (run-octave)
                        (rename-buffer (wg-buf-name buffer) t))))))

;; `prolog-inferior-mode'
(wg-support 'prolog-inferior-mode 'prolog
  `((deserialize . ,(lambda (_buffer _vars)
                      (save-window-excursion
                        (run-prolog nil))
                      (switch-to-buffer "*prolog*")
                      (goto-char (point-max))))))

;; `ensime-inf-mode'
(wg-support 'ensime-inf-mode 'ensime
  `((deserialize . ,(lambda (_buffer _vars)
                      (save-window-excursion
                        (ensime-inf-switch))
                      (when (boundp 'ensime-inf-buffer-name)
                        (switch-to-buffer ensime-inf-buffer-name)
                        (goto-char (point-max)))))))

;; compilation-mode
;;
;; I think it's not a good idea to compile a program just to switch
;; workgroups. So just restoring a buffer name.
(wg-support 'compilation-mode 'compile
  `((serialize . ,(lambda (_buffer)
                    (if (boundp' compilation-arguments) compilation-arguments)))
    (deserialize . ,(lambda (buffer vars)
                      (save-window-excursion
                        (get-buffer-create (wg-buf-name buffer)))
                      (with-current-buffer (wg-buf-name buffer)
                        (when (boundp' compilation-arguments)
                          (make-local-variable 'compilation-arguments)
                          (setq compilation-arguments vars)))
                      (switch-to-buffer (wg-buf-name buffer))
                      (goto-char (point-max))))))

;; grep-mode
;; see grep.el - `compilation-start' - it is just a compilation buffer
;; local variables:
;; `compilation-arguments' == (cmd mode nil nil)
(wg-support 'grep-mode 'grep
  `((serialize . ,(lambda (_buffer)
                    (if (boundp' compilation-arguments) compilation-arguments)))
    (deserialize . ,(lambda (_buffer vars)
                      (compilation-start (car vars) (nth 1 vars))
                      (switch-to-buffer "*grep*")))))

(defun wg-deserialize-slime-buffer (buf)
  "Deserialize `slime' buffer BUF."
  (when (require 'slime nil 'noerror)
    (wg-dbind (_this-function args) (wg-buf-special-data buf)
      (let ((default-directory (car args))
            (arguments (nth 1 args)))
        (when (and (fboundp 'slime-start*)
                   (fboundp 'slime-process))
          (save-window-excursion
            (slime-start* arguments))
          (switch-to-buffer (process-buffer (slime-process)))
          (current-buffer))))))

;; `comint-mode'  (general mode for all shells)
;;
;; It may have different shells. So we need to determine which shell is
;; now in `comint-mode' and how to restore it.
;;
;; Just executing `comint-exec' may be not enough because we can miss
;; some hooks or any other stuff that is executed when you run a
;; specific shell.
(defun wg-serialize-comint-buffer (buffer)
  "Serialize comint BUFFER."
  (with-current-buffer buffer
    (if (fboundp 'comint-mode)
        (when (eq major-mode 'comint-mode)
          ;; `slime-inferior-lisp-args' var is used when in `slime'
          (when (and (boundp 'slime-inferior-lisp-args)
                     slime-inferior-lisp-args)
            (list 'wg-deserialize-slime-buffer
                  (list default-directory slime-inferior-lisp-args)
                  ))))))

;; inf-mongo
;; https://github.com/tobiassvn/inf-mongo
;; `mongo-command' - command used to start inferior mongo
(wg-support 'inf-mongo-mode 'inf-mongo
  `((serialize . ,(lambda (_buffer)
                    (if (boundp 'inf-mongo-command) inf-mongo-command)))
    (deserialize . ,(lambda (_buffer vars)
                      (save-window-excursion
                        (when (fboundp 'inf-mongo)
                          (inf-mongo vars)))
                      (when (get-buffer "*mongo*")
                        (switch-to-buffer "*mongo*")
                        (goto-char (point-max)))))))

(defun wg-temporarily-rename-buffer-if-exists (buffer)
  "Rename BUFFER if it exists."
  (when (get-buffer buffer)
    (with-current-buffer buffer
      (rename-buffer "*wg--temp-buffer*" t))))

;; SML shell
;; Functions to serialize deserialize inferior sml buffer
;; `inf-sml-program' is the program run as inferior sml, is the
;; `inf-sml-args' are the extra parameters passed, `inf-sml-host'
;; is the host on which sml was running when serialized
(wg-support 'inferior-sml-mode 'sml-mode
  `((serialize . ,(lambda (_buffer)
                    (list (if (boundp 'sml-program-name) sml-program-name)
                          (if (boundp 'sml-default-arg) sml-default-arg)
                          (if (boundp 'sml-host-name) sml-host-name))))
    (deserialize . ,(lambda (buffer vars)
                      (wg-dbind (program args host) vars
                        (save-window-excursion
                          ;; If a inf-sml buffer already exists rename it temporarily
                          ;; otherwise `run-sml' will simply switch to the existing
                          ;; buffer, however we want to create a separate buffer with
                          ;; the serialized name
                          (let* ((inf-sml-buffer-name (concat "*"
                                                              (file-name-nondirectory program)
                                                              "*"))
                                 (existing-sml-buf (wg-temporarily-rename-buffer-if-exists
                                                    inf-sml-buffer-name)))
                            (with-current-buffer (run-sml program args host)
                              ;; Rename the buffer
                              (rename-buffer (wg-buf-name buffer) t)

                              ;; Now we can re-rename the previously renamed buffer
                              (when existing-sml-buf
                                (with-current-buffer existing-sml-buf
                                  (rename-buffer inf-sml-buffer-name t))))))
                        (switch-to-buffer (wg-buf-name buffer))
                        (goto-char (point-max)))))))

;; Geiser repls
;; http://www.nongnu.org/geiser/
(wg-support 'geiser-repl-mode 'geiser
  `((save . (geiser-impl--implementation))
    (deserialize . ,(lambda (buffer vars)
                      (when (fboundp 'run-geiser)
                        (wg-dbind (impl) vars
                          (run-geiser impl)
                          (goto-char (point-max))))
                      (switch-to-buffer (wg-buf-name buffer))))))

;; w3m-mode
(wg-support 'w3m-mode 'w3m
  `((save . (w3m-current-url))
    (deserialize . ,(lambda (_buffer vars)
                      (wg-dbind (url) vars
                        (w3m-goto-url url))))))

;; notmuch
(wg-support 'notmuch-hello-mode 'notmuch
  `((deserialize . ,(lambda (buffer vars)
                      (ignore vars)
                      (notmuch)
                      (get-buffer (wg-buf-name buffer))))))

;; dired-sidebar
(defvar dired-sidebar-display-alist)
(wg-support 'dired-sidebar-mode 'dired-sidebar
  `((serialize . ,(lambda (_buffer) dired-sidebar-display-alist))
    (deserialize
     . ,(lambda (_buffer saved-display-alist)
          (when (and (or wg-restore-remote-buffers
                         (not (file-remote-p default-directory)))
                     ;; Restore buffer only if `dired-sidebar-show-sidebar'
                     ;; will place it in the same side window as before.
                     (equal dired-sidebar-display-alist saved-display-alist))
            (let ((dir (wg-get-first-existing-dir)))
              (when (file-directory-p dir)
                (let ((buffer (dired-sidebar-get-or-create-buffer dir)))
                  ;; Set up the buffer by calling `dired-sidebar-show-sidebar'
                  ;; for side effects only, discarding the created window. We
                  ;; don't want to add extra new windows during the session
                  ;; restoration process.
                  (save-window-excursion (dired-sidebar-show-sidebar buffer))
                  ;; HACK: Replace the just-restored window after session is
                  ;; restored. This ensures that we perform any additional
                  ;; window setup that was not done by deserialization. The
                  ;; point is to avoid depending too closely on the
                  ;; implementation details of dired-sidebar. Rather than
                  ;; serialize every detail, we let `dired-sidebar-show-sidebar'
                  ;; do the work.
                  (let ((frame (selected-frame)))
                    (run-at-time 0 nil
                                 (lambda ()
                                   (with-selected-frame frame
                                     (dired-sidebar-hide-sidebar)
                                     (dired-sidebar-show-sidebar buffer)))))
                  buffer))))))))

;;; buffer-local variable serdes

(defun wg-serialize-buffer-mark-ring ()
  "Return a new list of the positions of the marks in `mark-ring'."
  (mapcar 'marker-position mark-ring))

(defun wg-deserialize-buffer-mark-ring (positions)
  "Set `mark-ring' to a new list of markers created from POSITIONS."
  (setq mark-ring
        (mapcar (lambda (pos) (set-marker (make-marker) pos))
                positions)))

(defun wg-deserialize-buffer-major-mode (major-mode-symbol)
  "Conditionally retore MAJOR-MODE-SYMBOL in `current-buffer'."
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
  "Setf'able `wg-current-session' modified slot accessor."
  `(wg-session-workgroup-list (wg-current-session)))

(defmacro wg-buf-list ()
  "Setf'able `wg-current-session' buf-list slot accessor."
  `(wg-session-buf-list (wg-current-session)))

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
If BUF's file doesn't exist, call `wg-restore-default-buffer'"
  (let ((file-name (wg-buf-file-name buf)))
    (when (and file-name
               (or wg-restore-remote-buffers
                   (not (file-remote-p file-name))))
      (cond ((file-exists-p file-name)
             ;; jit ignore errors
             ;;(ignore-errors
             (condition-case err
                 (let ((b (find-file-noselect file-name nil nil nil)))
                   (with-current-buffer b
                     (rename-buffer (wg-buf-name buf) t)
                     (wg-set-buffer-uid-or-error (wg-buf-uid buf))
                     (when wg-restore-mark
                       (set-mark (wg-buf-mark buf))
                       (deactivate-mark))
                     (wg-deserialize-buffer-local-variables buf)
                     )
                   (if switch (switch-to-buffer b))
                   b)
               (error
                (message "Error while restoring a file %s:\n  %s" file-name (error-message-string err))
                nil)))
            (t
             ;; try directory
             (if (file-directory-p (file-name-directory file-name))
                 (dired (file-name-directory file-name))
               (progn
                 (message "Attempt to restore nonexistent file: %S" file-name)
                 nil))
             )))))

(defun wg-restore-special-buffer (buf &optional switch)
  "Restore a buffer BUF with DESERIALIZER-FN and maybe SWITCH to it."
  (let* ((special-data (wg-buf-special-data buf))
         (buffer (save-window-excursion
                   (condition-case err
                       (let ((fn (car special-data)))
                         (and fn (funcall (car special-data) buf)))
                     (error (message "Error deserializing %S: %S" (wg-buf-name buf) err)
                            nil)))))
    (when (and special-data buffer)
      (if switch (switch-to-buffer buffer t))
      (with-current-buffer buffer
        (wg-set-buffer-uid-or-error (wg-buf-uid buf)))
      buffer)))

(defun wg-restore-buffer (buf &optional switch)
  "Restore BUF, return it and maybe SWITCH to it."
  (when buf
    (fset 'buffer-list wg-buffer-list-original)
    (or (wg-restore-existing-buffer buf switch)
        (wg-restore-special-buffer buf switch)  ;; non existent dired problem
        (wg-restore-file-buffer buf switch)
        (progn (wg-restore-default-buffer switch) nil))))

;;; buffer object utils

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
  (cl-some (lambda (fn) (funcall fn buffer)) wg-special-buffer-serdes-functions))

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
     :mark           (mark)
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

(defun wg-reset-buffer (buffer)
  "Return BUFFER.
Currently only sets BUFFER's `wg-buffer-uid' to nil."
  (with-current-buffer buffer (setq wg-buffer-uid nil)))

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

(defun wg-flag-session-modified ()
  "Set SESSION's modified flag."
  (when wg-current-session
    (setf (wg-session-modified wg-current-session) t)))

(defun wg-flag-workgroup-modified (&optional workgroup)
  "Set WORKGROUP's and the current session's modified flags."
  (unless workgroup
    (setq workgroup (wg-get-workgroup nil t)))
  (when workgroup
    (setf (wg-workgroup-modified workgroup) t)
    (wg-flag-session-modified)))

(defun wg-current-workgroup (&optional noerror frame)
  "Return current workgroup in frame.
Error unless NOERROR, in FRAME if specified."
  (or wg-current-workgroup
      (if (frame-parameter frame 'wg-current-workgroup-uid)
          (wg-find-workgroup-by :uid (frame-parameter frame 'wg-current-workgroup-uid) noerror)
        (unless noerror (error "No current workgroup in this frame")))))

(defun wg-previous-workgroup (&optional noerror frame)
  "Return the previous workgroup in FRAME, or error unless NOERROR."
  (let ((param (frame-parameter frame 'wg-previous-workgroup-uid)))
    (if param
        (wg-find-workgroup-by :uid param noerror)
      (unless noerror (error "No previous workgroup in this frame")))))

(defun wg-set-current-workgroup (workgroup &optional frame)
  "Set the current workgroup to WORKGROUP in FRAME.
WORKGROUP should be a workgroup or nil."
  (set-frame-parameter frame 'wg-current-workgroup-uid
                       (when workgroup (wg-workgroup-uid workgroup))))

(defun wg-set-previous-workgroup (workgroup &optional frame)
  "Set the previous workgroup to WORKGROUP in FRAME.
WORKGROUP should be a workgroup or nil."
  (set-frame-parameter frame 'wg-previous-workgroup-uid
                       (when workgroup (wg-workgroup-uid workgroup))))

(defun wg-current-workgroup-p (workgroup &optional frame)
  "Return t when WORKGROUP is the current workgroup of FRAME, nil otherwise."
  (eq workgroup (wg-current-workgroup t frame)))

(defun wg-previous-workgroup-p (workgroup frame)
  "Return t when WORKGROUP is the previous workgroup of FRAME, nil otherwise."
  (eq workgroup (wg-previous-workgroup t frame)))

(defun wg-get-workgroup (obj &optional noerror)
  "Return a workgroup from OBJ.
If OBJ is a workgroup, return it.
If OBJ is a string, return the workgroup named OBJ, or error unless NOERROR.
If OBJ is nil, return the current workgroup, or error unless NOERROR."
  (cond ((wg-workgroup-p obj) obj)
        ((stringp obj) (wg-find-workgroup-by :name obj noerror))
        ((null obj) (wg-current-workgroup noerror))
        (t (error "Can't get workgroup from type:: %S" (type-of obj)))))


;;; workgroup parameters
;;
;; Quick test:
;; (wg-workgroup-parameters (wg-current-workgroup))
;; (wg-set-workgroup-parameter (wg-current-workgroup) 'test1 t)
;; (wg-workgroup-parameter (wg-current-workgroup) 'test1)
(defun wg-workgroup-parameter (workgroup parameter &optional default)
  "Return WORKGROUP's value for PARAMETER.
If PARAMETER is not found, return DEFAULT which defaults to nil.
WORKGROUP should be accepted by `wg-get-workgroup'."
  (wg-aget (wg-workgroup-parameters (wg-get-workgroup workgroup))
           parameter default))

(defun wg-set-workgroup-parameter (parameter value &optional workgroup)
  "Set PARAMETER to VALUE in a WORKGROUP.
WORKGROUP should be a value accepted by `wg-get-workgroup'.
Return VALUE."
  (let* ((workgroup (wg-get-workgroup (or workgroup (wg-current-workgroup t)) t)))
    (when workgroup
      (wg-set-parameter (wg-workgroup-parameters workgroup) parameter value)
      (wg-flag-workgroup-modified workgroup)
      value)))

(defun wg-workgroup-local-value (variable &optional workgroup)
  "Return the value of VARIABLE in WORKGROUP.
WORKGROUP nil defaults to the current workgroup.  If there is no
current workgroup, or if VARIABLE does not have a workgroup-local
binding in WORKGROUP, resolve VARIABLE with `wg-session-local-value'."
  (let ((workgroup (wg-get-workgroup workgroup t)))
    (if (not workgroup) (wg-session-local-value variable)
      (let* ((undefined (cl-gensym))
             (value (wg-workgroup-parameter workgroup variable undefined)))
        (if (not (eq value undefined)) value
          (wg-session-local-value variable))))))

(defun wg-workgroup-saved-wconfig-names (workgroup)
  "Return a new list of the names of all WORKGROUP's saved wconfigs."
  (mapcar 'wg-wconfig-name (wg-workgroup-saved-wconfigs workgroup)))

(defun wg-workgroup-get-saved-wconfig (wconfig-or-name &optional workgroup)
  "Return the wconfig by WCONFIG-OR-NAME from WORKGROUP's saved wconfigs.
WCONFIG-OR-NAME must be either a string or a wconfig.  If
WCONFIG-OR-NAME is a string and there is no saved wconfig with
that name, return nil.  If WCONFIG-OR-NAME is a wconfig, and it
is a member of WORKGROUP's saved wconfigs, return is as given.
Otherwise return nil."
  (let ((wconfigs (wg-workgroup-saved-wconfigs (or workgroup (wg-current-workgroup)))))
    (cl-etypecase wconfig-or-name
      (wg-wconfig (car (memq wconfig-or-name wconfigs)))
      (string (cl-find wconfig-or-name wconfigs
                       :key 'wg-wconfig-name
                       :test 'string=)))))

(defun wg-workgroup-save-wconfig (wconfig &optional workgroup)
  "Add WCONFIG to WORKGROUP's saved wconfigs.
WCONFIG must have a name.  If there's already a wconfig with the
same name in WORKGROUP's saved wconfigs, replace it."
  (let ((name (wg-wconfig-name wconfig)))
    (unless name (error "Attempt to save a nameless wconfig"))
    (setf (wg-workgroup-modified workgroup) t)
    (wg-asetf (wg-workgroup-saved-wconfigs workgroup)
              (cons wconfig (cl-remove name it
                                       :key 'wg-wconfig-name
                                       :test 'string=)))))

(defun wg-workgroup-kill-saved-wconfig (workgroup wconfig-or-name)
  "Delete WCONFIG-OR-NAME from WORKGROUP's saved wconfigs.
WCONFIG-OR-NAME is resolved with `wg-workgroup-get-saved-wconfig'."
  (let* ((wconfig (wg-workgroup-get-saved-wconfig wconfig-or-name workgroup)))
    (when wconfig
      (wg-asetf (wg-workgroup-saved-wconfigs workgroup) (remq wconfig it)
                (wg-workgroup-modified workgroup) t))))

(defun wg-workgroup-base-wconfig-buf-uids (workgroup)
  "Return a new list of all unique buf uids in WORKGROUP's working wconfig."
  (wg-wconfig-buf-uids (wg-workgroup-base-wconfig workgroup)))

(defun wg-workgroup-saved-wconfigs-buf-uids (workgroup)
  "Return a new list of all unique buf uids in WORKGROUP's base wconfig."
  (cl-reduce 'wg-string-list-union
             (wg-workgroup-saved-wconfigs workgroup)
             :key 'wg-wconfig-buf-uids))

(defun wg-workgroup-all-buf-uids (workgroup)
  "Return a new list of all unique buf uids in WORKGROUP."
  (cl-reduce 'wg-string-list-union
             (list (wg-workgroup-base-wconfig-buf-uids workgroup)
                   (wg-workgroup-saved-wconfigs-buf-uids workgroup))))

(defun wg-restore-workgroup (workgroup)
  "Restore WORKGROUP in `selected-frame'."
  (wg-unflag-undoify-window-configuration-change)
  (wg-update-current-workgroup-working-wconfig)
  (wg-restore-wconfig (wg-workgroup-working-wconfig workgroup)))

(defun wg-workgroup-list-or-error (&optional noerror)
  "Return the value of `wg-current-session's :workgroup-list slot.
Or scream unless NOERROR."
  (if (wg-current-session noerror)
      (or (wg-session-workgroup-list (wg-current-session noerror))
          (unless noerror (error "No workgroups are defined")))
    (unless noerror (error "Current session is nil.  No workgroups are defined"))))

(defun wg-find-workgroup-by (slotkey value &optional noerror)
  "Return the workgroup on which ACCESSOR returns VALUE or error."
  (let ((accessor (cl-ecase slotkey
                    (:name 'wg-workgroup-name)
                    (:uid  'wg-workgroup-uid))))
    (or (cl-find value (wg-workgroup-list-or-error noerror) :test 'equal :key accessor)
        (unless noerror
          (error "There are no workgroups with a %S of %S"
                 accessor value)))))

(defun wg-workgroup-names (&optional noerror)
  "Return a list of workgroup names or scream unless NOERROR."
  (mapcar 'wg-workgroup-name (wg-workgroup-list-or-error noerror)))

(defun wg-read-workgroup-name (&optional require-match)
  "Read a workgroup name from `wg-workgroup-names'.
REQUIRE-MATCH to match."
  (completing-read "Workgroup: "
                   (wg-workgroup-names)
                   nil
                   require-match
                   nil
                   nil
                   (and (wg-current-workgroup t)
                        (wg-workgroup-name (wg-current-workgroup t)))))

(defun wg-new-default-workgroup-name ()
  "Return a new, unique, default workgroup name."
  (let ((names (wg-workgroup-names t)) (index -1) result)
    (while (not result)
      (let ((new-name (format "wg%s" (cl-incf index))))
        (unless (member new-name names)
          (setq result new-name))))
    result))

(defun wg-read-saved-wconfig-name (workgroup &optional prompt require-match)
  "Read the name of a saved wconfig, completing on the names of
WORKGROUP's saved wconfigs."
  (completing-read (or prompt "Saved wconfig name: ")
                   (wg-workgroup-saved-wconfig-names workgroup)
                   nil require-match))

(defun wg-read-saved-wconfig (workgroup)
  "Read the name of and return one of WORKGROUP's saved wconfigs."
  (wg-workgroup-get-saved-wconfig
   (wg-read-saved-wconfig-name workgroup nil t)
   workgroup))

(defun wg-query-and-save-if-modified ()
  "Query for save when `wg-modified-p'."
  (or (not (wg-modified-p))
      (when (y-or-n-p "Save modified workgroups? ")
        (wg-save-session))))

(defun wg-create-workgroup (name &optional blank)
  "Create and add a workgroup named NAME.
Optional argument BLANK non-nil (set interactively with a prefix
arg) means use a blank, one window window-config.  Otherwise use
the current window-configuration."
  (interactive (list (wg-read-new-workgroup-name) current-prefix-arg))

  (unless (file-exists-p (wg-get-session-file))
    (wg-reset-internal (wg-make-session))
    (wg-save-session))

  (unless wg-current-session
    ;; code extracted from `wg-open-session'.
    ;; open session but do NOT load any workgroup.
    (let* ((session (read (wg-read-text wg-session-file))))
      (setf (wg-session-file-name session) wg-session-file)
      (wg-reset-internal (wg-unpickel-session-parameters session))))

  (wg-switch-to-workgroup (wg-make-and-add-workgroup name blank))

  ;; save the session file in real time
  (wg-save-session)

  ;; I prefer simpler UI
  (message "Workgroup \"%s\" was created and saved." name))

(defun wg-switch-to-workgroup (workgroup)
  "Switch to WORKGROUP."
  (interactive (list (wg-read-workgroup-name)))
  (fset 'buffer-list wg-buffer-list-original)
  (let ((workgroup (wg-get-workgroup-create workgroup))
        (current (wg-current-workgroup t)))
    (unless (and (eq workgroup current))
      (when current (push current wg-deactivation-list))
      (unwind-protect
          (progn
            ;; Switch
            (wg-restore-workgroup workgroup)
            (wg-set-previous-workgroup current)
            (wg-set-current-workgroup workgroup)

            ;; After switch
            ;; Save "last-workgroup" to the session params
            (and (wg-current-workgroup t)
                 (wg-set-session-parameter 'last-workgroup (wg-workgroup-name (wg-current-workgroup t))))
            (and (wg-previous-workgroup t)
                 (wg-set-session-parameter 'prev-workgroup (wg-workgroup-name (wg-previous-workgroup t))))

            (run-hooks 'wg-after-switch-to-workgroup-hook))
        (when current (pop wg-deactivation-list))))))


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

(defun wg-unflag-undoify-window-configuration-change ()
  "Set `wg-undoify-window-configuration-change' to nil, exempting
from undoification any window-configuration changes caused by the
current command."
  (setq wg-undoify-window-configuration-change nil))

(defun wg-set-workgroup-working-wconfig (workgroup wconfig)
  "Set the working-wconfig of WORKGROUP to WCONFIG."
  (wg-flag-workgroup-modified workgroup)
  (setf (wg-workgroup-selected-frame-wconfig workgroup) wconfig)
  (wg-with-undo workgroup (state undo-pointer undo-list)
    (setcar (nthcdr undo-pointer undo-list) wconfig)))

(defun wg-workgroup-working-wconfig (workgroup &optional noupdate)
  "Return WORKGROUP's working-wconfig.
If WORKGROUP is the current workgroup in `selected-frame', and
NOUPDATE is nil, set its working wconfig in `selected-frame' to
`wg-current-wconfig' and return the updated wconfig.  Otherwise
return WORKGROUP's current undo state."
  (if (and (not noupdate) (wg-current-workgroup-p workgroup))
      (wg-set-workgroup-working-wconfig workgroup (wg-current-wconfig))
    (wg-with-undo workgroup (state undo-pointer undo-list)
      (nth undo-pointer undo-list))))

(defun wg-update-current-workgroup-working-wconfig ()
  "Update `selected-frame's current workgroup's working-wconfig with `wg-current-wconfig'."
  (and (wg-current-workgroup t)
       (wg-set-workgroup-working-wconfig (wg-current-workgroup t) (wg-current-wconfig))))

(defun wg-update-working-wconfig-hook ()
  "Used in before advice on all functions that trigger `window-configuration-change-hook'.
To save up to date undo info before the change."
  (when (and (not wg-already-updated-working-wconfig)
             (wg-minibuffer-inactive-p))
    (wg-update-current-workgroup-working-wconfig)
    (setq wg-already-updated-working-wconfig t)))

(defun wg-workgroup-gc-buf-uids (workgroup)
  "Remove buf uids from WORKGROUP that have no referent in `wg-buf-list'."
  (wg-asetf (wg-workgroup-strong-buf-uids workgroup)
            (cl-remove-if-not 'wg-find-buf-by-uid it)
            (wg-workgroup-weak-buf-uids workgroup)
            (cl-remove-if-not 'wg-find-buf-by-uid it)))

(defun wg-create-first-wg ()
  "Create a first workgroup if needed."
  (when (and workgroups-mode
             wg-session-load-on-start
             (= (length (wg-workgroup-list)) 0))
    (wg-create-workgroup wg-first-wg-name)
    (wg-mark-everything-unmodified)))

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
WORKGROUP after unpickeling its parameters. Otherwise return
WORKGROUP."
  (if (not (wg-workgroup-parameters workgroup)) workgroup
    (let ((copy (wg-copy-workgroup workgroup)))
      (wg-asetf (wg-workgroup-parameters copy) (wg-unpickel it))
      copy)))

(defun wg-delete-workgroup (workgroup)
  "Remove WORKGROUP from `wg-workgroup-list'.
Also delete all references to it by `wg-workgroup-state-table',
`wg-current-workgroup' and `wg-previous-workgroup'."
  (dolist (frame (frame-list))
    (remhash (wg-workgroup-uid workgroup) (wg-workgroup-state-table frame))
    (when (wg-current-workgroup-p workgroup frame)
      (wg-set-current-workgroup nil frame))
    (when (wg-previous-workgroup-p workgroup frame)
      (wg-set-previous-workgroup nil frame)))
  (setf (wg-workgroup-list) (remove workgroup (wg-workgroup-list-or-error)))
  (wg-flag-session-modified)
  workgroup)

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
    (wg-flag-session-modified)
    workgroup))

(defun wg-check-and-add-workgroup (workgroup)
  "Add WORKGROUP to `wg-workgroup-list'.
Ask to overwrite if a workgroup with the same name exists."
  (let ((name (wg-workgroup-name workgroup))
        (uid (wg-workgroup-uid workgroup)))
    (when (wg-find-workgroup-by :uid uid t)
      (error "A workgroup with uid %S already exists" uid))
    (when (wg-find-workgroup-by :name name t)
      (unless (or wg-no-confirm-on-destructive-operation
                  (y-or-n-p (format "%S exists.  Overwrite? " name)))
        (error "Cancelled"))))
  (wg-add-workgroup workgroup))

(defun wg-make-and-add-workgroup (name &optional blank)
  "Create a workgroup named NAME with current `window-tree'.
If BLANK - then just scratch buffer.
Add it with `wg-check-and-add-workgroup'."
  (wg-check-and-add-workgroup
   (wg-make-workgroup
    :name name
    :base-wconfig (if blank (wg-make-blank-wconfig)
                    (wg-current-wconfig)))))

(defun wg-get-workgroup-create (workgroup)
  "Return the workgroup specified by WORKGROUP, creating a new one if needed.
If `wg-get-workgroup' on WORKGROUP returns a workgroup, return it.
Otherwise, if WORKGROUP is a string, create a new workgroup with
that name and return it.  Otherwise error."
  (or (wg-get-workgroup workgroup t)
      (if (stringp workgroup)
          (wg-make-and-add-workgroup workgroup)
        (wg-get-workgroup workgroup))))  ; Call this again for its error message

(defun wg-read-text (path)
  "Read text with PATH, using `utf-8' coding."
  (decode-coding-string
   (with-temp-buffer
     (set-buffer-multibyte nil)
     (setq buffer-file-coding-system 'binary)
     (insert-file-contents-literally path)
     (buffer-substring-no-properties (point-min) (point-max)))
   'utf-8))

(defun wg-open-session (filename)
  "Load a session visiting FILENAME, creating one if none already exists."
  (interactive "FFind session file: ")
  (cond ((file-exists-p filename)
         ;; TODO: handle errors when reading object
         (let ((session (read (wg-read-text filename))))
           (unless (wg-session-p session)
             (error "%S is not a Workgroups session file" filename))
           (setf (wg-session-file-name session) filename)
           (wg-reset-internal (wg-unpickel-session-parameters session)))

         (if wg-control-frames (wg-restore-frames))

         (when (wg-workgroup-list)
           (if (member (wg-session-parameter 'last-workgroup) (wg-workgroup-names))
               (wg-switch-to-workgroup (wg-session-parameter 'last-workgroup))
             (wg-switch-to-workgroup (car (wg-workgroup-list))))
           (let ((prev (wg-session-parameter 'prev-workgroup)))
             (when prev
               (when (and (member prev (wg-workgroup-names))
                          (wg-get-workgroup prev t))
                 (wg-set-previous-workgroup (wg-get-workgroup prev t))))))
         (wg-mark-everything-unmodified))
        (t
         (wg-query-and-save-if-modified)
         (wg-reset-internal (wg-make-session :file-name filename))
         (message "(New Workgroups session file)"))))

(defun wg-write-sexp-to-file (sexp file)
  "Write the printable representation of SEXP to FILE."
  (with-temp-buffer
    (let ((print-level nil)  (print-length nil))
      (insert (format "%S" sexp)))
    (write-file file)))

;; FIXME: Duplicate buf names probably shouldn't be allowed.  An unrelated error
;; causes two *scratch* buffers to be present, triggering the "uids don't match"
;; error.  Write something to remove bufs with duplicate names.
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

(defun wg-save-session-as (filename)
  "Write the current session into file FILENAME.
This makes the session visit that file, and marks it as not modified."
  (unless (file-writable-p filename)
    (error "File %s can't be written to" filename))
  (wg-perform-session-maintenance)
  (setf (wg-session-file-name (wg-current-session)) filename)
  (setf (wg-session-version (wg-current-session)) wg-version)

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
  (wg-write-sexp-to-file (wg-pickel-all-session-parameters) filename)
  (wg-mark-everything-unmodified))

(defun wg-get-session-file ()
  "Return the filename in which to save the session."
  (or (and wg-current-session
           (wg-session-file-name wg-current-session))
      wg-session-file))

(defun wg-save-session ()
  "Save the current Workgroups session if it's been modified.
When FORCE - save session regardless of whether it's been modified."
  (interactive)
  (wg-save-session-as (wg-get-session-file)))

(defun wg-reset-internal (session)
  "Reset Workgroups, setting `wg-current-session' to SESSION.
Resets all frame parameters, buffer-local vars, current session
object, etc.  SESSION nil defaults to a new, blank session."
  (mapc 'wg-reset-frame (frame-list))
  (mapc 'wg-reset-buffer (wg-buffer-list-emacs))
  (setq wg-current-session session))

(defun wg-all-buf-uids ()
  "Return the union of all buf-uids."
  (cl-union (cl-reduce 'wg-string-list-union
                       (wg-session-workgroup-list (wg-current-session))
                       :key 'wg-workgroup-all-buf-uids)
            (delq nil (mapcar 'wg-buffer-uid (wg-buffer-list-emacs)))
            :test 'string=))

(defun wg-modified-p ()
  "Return t when the current session or any of its workgroups are modified."
  (and wg-current-session
       (or (wg-session-modified wg-current-session)
           (cl-some 'wg-workgroup-modified (wg-workgroup-list)))))

(defun wg-mark-everything-unmodified ()
  "Mark the session and all workgroups as unmodified."
  (let (wg-undoify-window-configuration-change)    ; to skip WG's `post-command-hook' that marks "modified" again
    (when wg-current-session
      (setf (wg-session-modified wg-current-session) nil))
    (dolist (workgroup (wg-workgroup-list))
      (setf (wg-workgroup-modified workgroup) nil))))

(defun wg-session-parameter (parameter &optional default session)
  "Return session's value for PARAMETER.
If PARAMETER is not found, return DEFAULT which defaults to nil.
SESSION nil defaults to the current session."
  (wg-aget (wg-session-parameters (or session (wg-current-session)))
           parameter default))

(defun wg-set-session-parameter (parameter value)
  "Set PARAMETER to VALUE in SESSION.
SESSION nil means use the current session.  Return value."
  (when wg-current-session
    (wg-set-parameter (wg-session-parameters wg-current-session) parameter value)
    (wg-flag-session-modified)
    value))

(defun wg-session-local-value (variable &optional session)
  "Return the value of VARIABLE in SESSION.
SESSION nil defaults to the current session.  If VARIABLE does
not have a session-local binding in SESSION, the value is
resolved by Emacs."
  (let* ((undefined (cl-gensym))
         (value (wg-session-parameter variable undefined session)))
    (if (not (eq value undefined)) value
      (symbol-value variable))))

(defun wg-reset-frame (frame)
  "Reset Workgroups' `frame-parameters' in FRAME to nil."
  (set-frame-parameter frame 'wg-workgroup-state-table nil)
  (set-frame-parameter frame 'wg-current-workgroup-uid nil)
  (set-frame-parameter frame 'wg-previous-workgroup-uid nil))

(defun wg-pickel-all-session-parameters (&optional session)
  "Return a copy of SESSION after pickeling its parameters.
And the parameters of all its workgroups."
  (let ((copy (wg-copy-session (or session (wg-current-session)))))
    (when (wg-session-parameters copy)
      (wg-asetf (wg-session-parameters copy) (wg-pickel it)))
    (wg-asetf (wg-session-workgroup-list copy)
              (cl-mapcar 'wg-pickel-workgroup-parameters it))
    copy))

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
  (let ((group (wg-current-workgroup t)))
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
  (cond
   (workgroups-mode
    (if (boundp 'desktop-restore-frames)
        (setq desktop-restore-frames nil))
    (wg-reset-internal (wg-make-session))                              ; creates a new `wg-current-session'
    (wg-add-workgroups-mode-minor-mode-entries)

    ;; Load session
    (when (and wg-session-load-on-start
               (file-exists-p wg-session-file))
      (condition-case err
          (wg-open-session wg-session-file)
        (error (message "Error finding `wg-session-file': %s" err))))
    (run-hooks 'workgroups-mode-hook))
   (t
    (wg-save-session)))
  (wg-create-first-wg)
  workgroups-mode)

(defun wg-all-group-names ()
  "Get all group names."
  (mapcar (lambda (group)
            ;; re-shape group for `completing-read'
            (cons (wg-workgroup-name group) group))
          (wg-session-workgroup-list
           (read (wg-read-text wg-session-file)))))

;;;###autoload
(defun wg-open-workgroup ()
  "Open specific workgroup."
  (interactive)
  (let* ((group-names (wg-all-group-names))
         selected-group)
    (when (and group-names
               (setq selected-group
                     (completing-read "Select work group: " group-names)))
      (wg-open-session wg-session-file)
      (wg-switch-to-workgroup selected-group))))

(provide 'workgroups2)
;;; workgroups2.el ends here
