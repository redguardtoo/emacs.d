;;; c-eldoc.el --- helpful description of the arguments to C functions

;; Copyright (C) 2004 Paul Pogonyshev
;; Copyright (C) 2004, 2005 Matt Strange
;; Copyright (C) 2010 Nathaniel Flath
;; Copyright (C) 2010 mooz <stillpedant@gmail.com>

;; This file is NOT a part of GNU Emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of the
;; License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
;; USA

;;; Commentary:

;; To enable: put the following in your .emacs file:
;;
;; (add-hook 'c-mode-hook 'c-turn-on-eldoc-mode)

;; Nathaniel has submitted a caching patch to make this workable on large projects "like the emacs
;; codebase"
;; v0.5 01/02/2010

;; Provides helpful description of the arguments to C functions.
;; Uses child process grep and preprocessor commands for speed.
;; v0.4 01/16/2005

;; Your improvements are appreciated: I am no longer maintaining this code
;; m_strange at mail dot utexas dot edu.  Instead, direct all requests to
;; flat0103@gmail.com

;;; Code:

(require 'eldoc)
(require 'deferred)
(require 'cc-defs)
(eval-when-compile (require 'cl))

;; ============================================================
;; Cache
;; ============================================================

;;if cache.el isn't loaded, define the cache functions
(unless (fboundp 'cache-make-cache)
  (defun* cache-make-cache (init-fun test-fun cleanup-fun
                                     &optional &key
                                     (test #'eql)
                                     (size 65)
                                     (rehash-size 1.5)
                                     (rehash-threshold 0.8)
                                     (weakness nil))
    "Creates a cached hash table.  This is a hash table where
elements expire at some condition, as specified by init-fun and
test-fun.  The three arguments do as follows:

init-fun is a function that is called when a new item is inserted
into the cache.

test-fun is a function that is called when an item in the cache
is looked up.  It takes one argument, and will be passed the
result of init-fun that was generated when the item was inserted
into the cache.

cleanup-fun is called when an item is removed from the hash
table.  It takes one argument, the value of the key-value pair
being deleted.

Note that values are only deleted from the cache when accessed.

This will return a list of 4 elements: a has table and the 3
arguments.  All hash-table functions will work on the car of this
list, although if accessed directly the lookups will return a pair
 (value, (init-fun)).

The keyword arguments are the same as for make-hash-table and are applied
to the created hash table."
  (list (make-hash-table :test test
                         :size size
                         :rehash-size rehash-size
                         :rehash-threshold rehash-threshold
                         :weakness weakness) init-fun test-fun cleanup-fun))

  (defun cache-gethash (key cache)
    "Retrieve the value corresponding to key from cache."
    (let ((keyval (gethash key (car cache) )))
      (if keyval
          (let ((val (car keyval))
                (info (cdr keyval)))
            (if (funcall (caddr cache) info)
                (progn
                  (remhash key (car cache))
                  (funcall (cadddr cache) val)
                  nil)
              val)))))

  (defun cache-puthash (key val cache)
    "Puts the key-val pair into cache."
    (puthash key
             (cons val (funcall (cadr cache)))
             (car cache))))

;; original function
(defun c-eldoc-cache-force-expire (key cache)
  "Force expire the key in the cache."
  (let ((keyval (gethash key (car cache))))
    (if keyval
        (let ((val (car keyval))
              (info (cdr keyval)))
          (remhash key (car cache))
          (funcall (cadddr cache) val)))))

;; ============================================================
;; Variables
;; ============================================================

;; make sure that the opening parenthesis in C will work
(eldoc-add-command 'c-electric-paren)

(defface c-eldoc-current-argument-face
  '((t (:foreground "tomato" :bold t)))
  "Style of the corresponding argument in the document")

;; if you've got a non-GNU preprocessor with funny options, set these
;; variables to fix it
(defvar c-eldoc-cpp-macro-arguments "-dD -w -P")
(defvar c-eldoc-cpp-normal-arguments "-w -P")
(defvar c-eldoc-cpp-command "/lib/cpp ")
(defvar c-eldoc-includes
  "`pkg-config gtk+-2.0 --cflags` -I./ -I../ "
  "List of commonly used packages/include directories - For
  example, SDL or OpenGL.  This shouldn't slow down cpp, even if
  you've got a lot of them.")

(defvar c-eldoc-reserved-words
  (list "if" "else" "switch" "while" "for" "sizeof")
  "List of commands that eldoc will not check.")

(defvar c-eldoc-buffer-regenerate-time
  120
  "Time to keep a preprocessed buffer around.")

(defun c-eldoc-time-diff (t1 t2)
  "Return the difference between the two times, in seconds.
T1 and T2 are time values (as returned by `current-time' for example)."
  ;; Pacify byte-compiler with `symbol-function'.
  (time-to-seconds (subtract-time t1 t2)))

(defun c-eldoc-time-difference (old-time)
  "Returns whether or not old-time is less than c-eldoc-buffer-regenerate-time seconds ago."
  (> (c-eldoc-time-diff (current-time) old-time) c-eldoc-buffer-regenerate-time))

(defun c-eldoc-cleanup (preprocessed-buffer)
  (kill-buffer preprocessed-buffer))

(defvar c-eldoc-buffers
  (cache-make-cache #'current-time #'c-eldoc-time-difference #'c-eldoc-cleanup)
  "Cache of buffer->preprocessed file used to speed up finding arguments")

(defun c-turn-on-eldoc-mode ()
  "Enable c-eldoc-mode"
  (interactive)
  (set (make-local-variable 'eldoc-documentation-function)
       'c-eldoc-print-current-symbol-info)
  (turn-on-eldoc-mode))

(defsubst c-eldoc-create-preprocessor-command (filename &optional option)
  "Create preprocessor command for certain filename"
  (mapconcat 'identity
             `(,c-eldoc-cpp-command
               ,option
               ,c-eldoc-includes
               ,filename) " "))

(defsubst c-eldoc-format-arguments-string (arguments index)
  "Formats the argument list of a function."
  (let ((paren-pos (string-match "(" arguments))
        (pos 0))
    (when paren-pos
      (setq arguments (replace-regexp-in-string "\\\\?[[:space:]\\\n]"
                                                " "
                                                (substring arguments paren-pos))
            arguments (replace-regexp-in-string "\\s-+" " " arguments)
            arguments (replace-regexp-in-string " *, *" ", " arguments)
            arguments (replace-regexp-in-string "( +" "(" arguments)
            arguments (replace-regexp-in-string " +)" ")" arguments))
      ;; find the correct argument to highlight, taking `...'
      ;; arguments into account
      (while (and (> index 1)
                  pos
                  (not (string= (substring arguments (+ pos 2) (+ pos 6))
                                "...)")))
        (setq pos (string-match "," arguments (1+ pos))
              index (1- index)))
      ;; embolden the current argument
      (when (and pos
                 (setq pos (string-match "[^ ,()]" arguments pos)))

        (put-text-property pos (string-match "[,)]" arguments pos)
                           'face 'c-eldoc-current-argument-face
                           arguments))
      arguments)))

;; ============================================================
;; Deferred
;; ============================================================

(defvar c-eldoc-pp-is-running-table
  (make-hash-table :test 'equal))

(defvar c-eldoc-current-function-cons nil)

(defsubst c-eldoc-deferred:command (command &rest args)
  (deferred:process
    shell-file-name
    shell-command-switch
    (mapconcat 'identity (cons command args) " ")))

(defsubst c-eldoc-deferred:tag-buffer (buffer)
  "Call the preprocessor on the current file"
  (let* ((command-for-macro (c-eldoc-create-preprocessor-command
                             c-eldoc-cpp-macro-arguments
                             buffer-file-name))
         (command-for-function (c-eldoc-create-preprocessor-command
                                c-eldoc-cpp-normal-arguments
                                buffer-file-name))
         (output-buffer (generate-new-buffer
                         (concat "*" buffer-file-name "-preprocessed*"))))
    (bury-buffer output-buffer)
    ;; create deferred and return it
    (deferred:$
      (c-eldoc-deferred:command command-for-macro)
      ;; chain
      (deferred:nextc it
        `(lambda (result)
           (with-current-buffer ,output-buffer (insert result))))
      ;; chain
      (c-eldoc-deferred:command command-for-function)
      ;; chain
      (deferred:nextc it
        `(lambda (result)
           (with-current-buffer ,output-buffer (insert result))
           ;; cache
           (cache-puthash ,buffer ,output-buffer c-eldoc-buffers)
           ;; done
           (remhash ,buffer c-eldoc-pp-is-running-table)
           ;; return
           ,output-buffer)))
    ))

;; ============================================================
;; C
;; ============================================================

(defun c-eldoc-get-info (buffer current-function)
  (let ((current-function-regexp (concat "\\<" current-function "[ \t\n]*("))
        (current-macro-regexp (concat "#define[ \t\n]+[*]*" current-function "[ \t\n]*("))
        (arguments)
        (type-face 'font-lock-type-face)
        (function-name-point))
    (with-current-buffer buffer
      (goto-char (point-min))
      ;; protected regexp search
      (when (condition-case nil
                (progn
                  (if (not (re-search-forward current-macro-regexp (point-max) t))
                      (re-search-forward current-function-regexp))
                  t)
              (error (prog1 nil (message "Function doesn't exist..."))))
        ;; move outside arguments list
        (search-backward "(")
        (c-skip-ws-backward)
        (setq function-name-point (point))
        (forward-sexp)
        (setq arguments (buffer-substring-no-properties function-name-point
                                                        (point)))
        (goto-char function-name-point)
        (backward-char (length current-function))
        (c-skip-ws-backward)
        (setq function-name-point (point))
        (search-backward-regexp "[{}=,:;/#]" (point-min) t)
        ;; check for macros
        (if (= (char-after) ?#)
            (let ((is-define (looking-at "#[[:space:]]*define"))
                  (preprocessor-point (point)))
              (while (prog2 (end-of-line)
                         (= (char-before) ?\\)
                       (forward-char)))
              (when (and is-define (> (point) function-name-point))
                (goto-char preprocessor-point)
                (setq type-face 'font-lock-preprocessor-face)))
          (forward-char)
          (when (looking-back "//")
            (end-of-line)))
        ;; colorize
        (c-skip-ws-forward)
        ;; return type, function name, arguments and type-face
        (values (replace-regexp-in-string "^[[:space:]\n]+"
                                          ""
                                          (buffer-substring-no-properties (point) function-name-point))
                current-function
                arguments
                type-face)))))

(defsubst c-eldoc-create-message (buffer current-function-cons)
  (let* ((current-function (car current-function-cons))
         (info (c-eldoc-get-info buffer current-function)))
    (when info
      (multiple-value-bind (ret fun args type-face)
          info
        ;; ok
        (concat
         (propertize ret 'face 'font-lock-type-face) " "
         (propertize fun 'face 'font-lock-function-name-face) " "
         (c-eldoc-format-arguments-string args (cdr current-function-cons)))))))

(defsubst c-eldoc-function-and-argument (&optional limit)
  "Finds the current function and position in argument list."
  (let* ((literal-limits (c-literal-limits))
         (literal-type (c-literal-type literal-limits)))
    (save-excursion
      ;; if this is a string, move out to function domain
      (when (eq literal-type 'string)
        (goto-char (car literal-limits))
        (setq literal-type nil))
      (if literal-type
          nil
        (c-save-buffer-state ((argument-index 1))
          (while (or (eq (c-forward-token-2 -1 t limit) 0)
                     (when (eq (char-before) ?\[)
                       (backward-char)
                       t))
            (when (eq (char-after) ?,)
              (setq argument-index (1+ argument-index))))
          (c-backward-syntactic-ws)
          (when (eq (char-before) ?\()
            (backward-char)
            (c-forward-token-2 -1)
            (when (looking-at "[a-zA-Z_][a-zA-Z_0-9]*")
              (cons (buffer-substring-no-properties
                     (match-beginning 0) (match-end 0))
                    argument-index))))))))

(defun c-eldoc-print-current-symbol-info ()
  "Returns documentation string for the current symbol."
  (let* ((current-function-cons (c-eldoc-function-and-argument (- (point) 1000)))
         (current-function (car current-function-cons))
         (cur-buffer (current-buffer)))
    ;; save cons globally
    (make-local-variable 'c-eldoc-current-function-cons)
    (setq c-eldoc-current-function-cons current-function-cons)
    (when (and current-function
               (not (member current-function c-eldoc-reserved-words)))
      (let ((tag-buffer (cache-gethash cur-buffer c-eldoc-buffers)))
        (if tag-buffer
            (eldoc-message (c-eldoc-create-message tag-buffer c-eldoc-current-function-cons))
          ;; else
          (unless (gethash cur-buffer c-eldoc-pp-is-running-table)
            ;; mark as preprocessor is running on `buffer'
            (puthash cur-buffer t c-eldoc-pp-is-running-table)
            (eldoc-message "Getting the documentation ...")
            (deferred:nextc (c-eldoc-deferred:tag-buffer cur-buffer)
              (lambda (buffer)
                ;; delayed. create and display last functions document.
                (when c-eldoc-current-function-cons
                  (eldoc-message (c-eldoc-create-message buffer c-eldoc-current-function-cons)))))
            nil)
          )))))

(defun c-eldoc-force-cache-update ()
  "Returns documentation string for the current symbol."
  (interactive)
  (let ((cur-buffer (current-buffer)))
    (c-eldoc-cache-force-expire cur-buffer c-eldoc-buffers)
    (c-eldoc-print-current-symbol-info)))

(provide 'c-eldoc)
;;; c-eldoc.el ends here
