;;; ivy.el --- Incremental Vertical completYon -*- lexical-binding: t -*-

;; Copyright (C) 2015  Free Software Foundation, Inc.

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/swiper
;; Version: 0.2.3
;; Package-Requires: ((emacs "24.1"))
;; Keywords: matching

;; This file is part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This package provides `ivy-read' as an alternative to
;; `completing-read' and similar functions.
;;
;; There's no intricate code to determine the best candidate.
;; Instead, the user can navigate to it with `ivy-next-line' and
;; `ivy-previous-line'.
;;
;; The matching is done by splitting the input text by spaces and
;; re-building it into a regex.
;; So "for example" is transformed into "\\(for\\).*\\(example\\)".

;;; Code:
(require 'cl-lib)

;;* Customization
(defgroup ivy nil
  "Incremental vertical completion."
  :group 'convenience)

(defface ivy-current-match
  '((t (:inherit highlight)))
  "Face used by Ivy for highlighting first match.")

(defface ivy-confirm-face
  '((t :foreground "ForestGreen" :inherit minibuffer-prompt))
  "Face used by Ivy to issue a confirmation prompt.")

(defface ivy-match-required-face
  '((t :foreground "red" :inherit minibuffer-prompt))
  "Face used by Ivy to issue a match required prompt.")

(defface ivy-subdir
  '((t (:inherit 'dired-directory)))
  "Face used by Ivy for highlighting subdirs in the alternatives.")

(defface ivy-remote
  '((t (:foreground "#110099")))
  "Face used by Ivy for highlighting remotes in the alternatives.")

(defcustom ivy-height 10
  "Number of lines for the minibuffer window."
  :type 'integer)

(defcustom ivy-count-format "%-4d "
  "The style of showing the current candidate count for `ivy-read'.
Set this to nil if you don't want the count."
  :type 'string)

(defcustom ivy-wrap nil
  "Whether to wrap around after the first and last candidate."
  :type 'boolean)

(defcustom ivy-on-del-error-function 'minibuffer-keyboard-quit
  "The handler for when `ivy-backward-delete-char' throws.
This is usually meant as a quick exit out of the minibuffer."
  :type 'function)

(defcustom ivy-extra-directories '("../" "./")
  "Add this to the front of the list when completing file names.
Only \"./\" and \"../\" apply here. They appear in reverse order."
  :type 'list)

;;* Keymap
(require 'delsel)
(defvar ivy-minibuffer-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-m") 'ivy-done)
    (define-key map (kbd "C-j") 'ivy-alt-done)
    (define-key map (kbd "TAB") 'ivy-partial-or-done)
    (define-key map (kbd "C-n") 'ivy-next-line)
    (define-key map (kbd "C-p") 'ivy-previous-line)
    (define-key map (kbd "<down>") 'ivy-next-line)
    (define-key map (kbd "<up>") 'ivy-previous-line)
    (define-key map (kbd "C-s") 'ivy-next-line-or-history)
    (define-key map (kbd "C-r") 'ivy-previous-line-or-history)
    (define-key map (kbd "SPC") 'self-insert-command)
    (define-key map (kbd "DEL") 'ivy-backward-delete-char)
    (define-key map (kbd "M-<") 'ivy-beginning-of-buffer)
    (define-key map (kbd "M->") 'ivy-end-of-buffer)
    (define-key map (kbd "<left>") 'ivy-beginning-of-buffer)
    (define-key map (kbd "<right>") 'ivy-end-of-buffer)
    (define-key map (kbd "M-n") 'ivy-next-history-element)
    (define-key map (kbd "M-p") 'ivy-previous-history-element)
    (define-key map (kbd "C-g") 'minibuffer-keyboard-quit)
    (define-key map (kbd "C-v") 'ivy-scroll-up-command)
    (define-key map (kbd "M-v") 'ivy-scroll-down-command)
    (define-key map (kbd "C-M-n") 'ivy-next-line-and-call)
    (define-key map (kbd "C-M-p") 'ivy-previous-line-and-call)
    (define-key map (kbd "M-q") 'ivy-toggle-regexp-quote)
    map)
  "Keymap used in the minibuffer.")

;;* Globals
(cl-defstruct ivy-state
  prompt collection
  predicate require-match initial-input
  history preselect keymap update-fn sort
  ;; The window in which `ivy-read' was called
  window
  action
  unwind)

(defvar ivy-last nil
  "The last parameters passed to `ivy-read'.")

(defsubst ivy-set-action (action)
  (setf (ivy-state-action ivy-last) action))

(defvar ivy-history nil
  "History list of candidates entered in the minibuffer.

Maximum length of the history list is determined by the value
of `history-length', which see.")

(defvar ivy--directory nil
  "Current directory when completing file names.")

(defvar ivy--length 0
  "Store the amount of viable candidates.")

(defvar ivy-text ""
  "Store the user's string as it is typed in.")

(defvar ivy--current ""
  "Current candidate.")

(defvar ivy--index 0
  "Store the index of the current candidate.")

(defvar ivy-exit nil
  "Store 'done if the completion was successfully selected.
Otherwise, store nil.")

(defvar ivy--all-candidates nil
  "Store the candidates passed to `ivy-read'.")

(defvar ivy--default nil
  "Default initial input.")

(defvar ivy--update-fn nil
  "Current function to call when current candidate(s) update.")

(defvar ivy--prompt nil
  "Store the format-style prompt.
When non-nil, it should contain one %d.")

(defvar ivy--prompt-extra ""
  "Temporary modifications to the prompt.")

(defvar ivy--old-re nil
  "Store the old regexp.")

(defvar ivy--old-cands nil
  "Store the candidates matched by `ivy--old-re'.")

(defvar ivy--regex-function 'ivy--regex
  "Current function for building a regex.")

(defvar ivy--collection nil
  "Store the current collection function.")

(defvar Info-current-file)

;;* Commands
(defun ivy-done ()
  "Exit the minibuffer with the selected candidate."
  (interactive)
  (delete-minibuffer-contents)
  (when (cond (ivy--directory
               (if (zerop ivy--length)
                   (if (or (not (eq confirm-nonexistent-file-or-buffer t))
                           (equal " (confirm)" ivy--prompt-extra))
                       (progn
                         (insert
                          (expand-file-name ivy-text ivy--directory))
                         (setq ivy-exit 'done))
                     (setq ivy--prompt-extra " (confirm)")
                     (insert ivy-text)
                     (ivy--exhibit)
                     nil)
                 (insert
                  (expand-file-name
                   ivy--current ivy--directory))
                 (setq ivy-exit 'done)))
              ((zerop ivy--length)
               (if (memq (ivy-state-require-match ivy-last)
                         '(nil confirm confirm-after-completion))
                   (progn
                     (insert ivy-text)
                     (setq ivy-exit 'done))
                 (setq ivy--prompt-extra " (match required)")
                 (insert ivy-text)
                 (ivy--exhibit)
                 nil))
              (t
               (insert ivy--current)
               (setq ivy-exit 'done)))
    (exit-minibuffer)))

(defun ivy-build-tramp-name (x)
  "Reconstruct X into a path.
Is is a cons cell, related to `tramp-get-completion-function'."
  (let ((user (car x))
        (domain (cadr x)))
    (if user
        (concat user "@" domain)
      domain)))

(defun ivy-alt-done (&optional arg)
  "Exit the minibuffer with the selected candidate.
When ARG is t, exit with current text, ignoring the candidates."
  (interactive "P")
  (if arg
      (ivy-immediate-done)
    (let (dir)
      (cond ((and ivy--directory
                  (or
                   (and
                    (not (string= ivy--current "./"))
                    (cl-plusp ivy--length)
                    (file-directory-p
                     (setq dir (expand-file-name
                                ivy--current ivy--directory))))))
             (ivy--cd dir)
             (ivy--exhibit))
            ((string-match "^/\\([^/]+?\\):\\(?:\\(.*\\)@\\)?" ivy-text)
             (let ((method (match-string 1 ivy-text))
                   (user (match-string 2 ivy-text))
                   res)
               (dolist (x (tramp-get-completion-function method))
                 (setq res (append res (funcall (car x) (cadr x)))))
               (setq res (delq nil res))
               (when user
                 (dolist (x res)
                   (setcar x user)))
               (setq res (cl-delete-duplicates res :test 'equal))
               (let ((host (ivy-read "Find File: "
                                     (mapcar #'ivy-build-tramp-name res))))
                 (when host
                   (setq ivy--directory "/")
                   (ivy--cd (concat "/" method ":" host ":"))))))
            (t
             (ivy-done))))))

(defun ivy-partial-or-done ()
  "Complete the minibuffer text as much as possible.
When called twice in a row, exit the minibuffer with the current
candidate."
  (interactive)
  (if (eq this-command last-command)
      (progn
        (delete-minibuffer-contents)
        (insert ivy--current)
        (setq ivy-exit 'done)
        (exit-minibuffer))
    (let* ((parts (split-string ivy-text " " t))
           (postfix (car (last parts)))
           (new (try-completion postfix
                                (mapcar (lambda (str) (substring str (string-match postfix str)))
                                        ivy--old-cands))))
      (delete-region (minibuffer-prompt-end) (point-max))
      (setcar (last parts) new)
      (insert (mapconcat #'identity parts " ") " "))))

(defun ivy-immediate-done ()
  "Exit the minibuffer with the current input."
  (interactive)
  (delete-minibuffer-contents)
  (insert ivy-text)
  (setq ivy-exit 'done)
  (exit-minibuffer))

(defun ivy-resume ()
  "Resume the last completion session."
  (interactive)
  (ivy-read
   (ivy-state-prompt ivy-last)
   (ivy-state-collection ivy-last)
   :predicate (ivy-state-predicate ivy-last)
   :require-match (ivy-state-require-match ivy-last)
   :initial-input ivy-text
   :history (ivy-state-history ivy-last)
   :preselect (regexp-quote ivy--current)
   :keymap (ivy-state-keymap ivy-last)
   :update-fn (ivy-state-update-fn ivy-last)
   :sort (ivy-state-sort ivy-last)
   :action (ivy-state-action ivy-last)
   :unwind (ivy-state-unwind ivy-last)))

(defun ivy-beginning-of-buffer ()
  "Select the first completion candidate."
  (interactive)
  (setq ivy--index 0))

(defun ivy-end-of-buffer ()
  "Select the last completion candidate."
  (interactive)
  (setq ivy--index (1- ivy--length)))

(defun ivy-scroll-up-command ()
  "Scroll the candidates upward by the minibuffer height."
  (interactive)
  (setq ivy--index (min (+ ivy--index ivy-height)
                        (1- ivy--length))))

(defun ivy-scroll-down-command ()
  "Scroll the candidates downward by the minibuffer height."
  (interactive)
  (setq ivy--index (max (- ivy--index ivy-height)
                        0)))

(defun ivy-next-line (&optional arg)
  "Move cursor vertically down ARG candidates."
  (interactive "p")
  (setq arg (or arg 1))
  (cl-incf ivy--index arg)
  (when (>= ivy--index (1- ivy--length))
    (if ivy-wrap
        (ivy-beginning-of-buffer)
      (setq ivy--index (1- ivy--length)))))

(defun ivy-next-line-or-history (&optional arg)
  "Move cursor vertically down ARG candidates.
If the input is empty, select the previous history element instead."
  (interactive "p")
  (when (string= ivy-text "")
    (ivy-previous-history-element 1))
  (ivy-next-line arg))

(defun ivy-previous-line (&optional arg)
  "Move cursor vertically up ARG candidates."
  (interactive "p")
  (setq arg (or arg 1))
  (cl-decf ivy--index arg)
  (when (< ivy--index 0)
    (if ivy-wrap
        (ivy-end-of-buffer)
      (setq ivy--index 0))))

(defun ivy-previous-line-or-history (arg)
  "Move cursor vertically up ARG candidates.
If the input is empty, select the previous history element instead."
  (interactive "p")
  (when (string= ivy-text "")
    (ivy-previous-history-element 1))
  (ivy-previous-line arg))

(defun ivy-next-line-and-call (&optional arg)
  "Move cursor vertically down ARG candidates."
  (interactive "p")
  (ivy-next-line arg)
  (ivy--exhibit)
  (with-selected-window (ivy-state-window ivy-last)
    (funcall (ivy-state-action ivy-last))))

(defun ivy-previous-line-and-call (&optional arg)
  "Move cursor vertically down ARG candidates."
  (interactive "p")
  (ivy-previous-line arg)
  (ivy--exhibit)
  (with-selected-window (ivy-state-window ivy-last)
    (funcall (ivy-state-action ivy-last))))

(defun ivy-previous-history-element (arg)
  "Forward to `previous-history-element' with ARG."
  (interactive "p")
  (previous-history-element arg)
  (move-end-of-line 1)
  (ivy--maybe-scroll-history))

(defun ivy-next-history-element (arg)
  "Forward to `next-history-element' with ARG."
  (interactive "p")
  (next-history-element arg)
  (move-end-of-line 1)
  (ivy--maybe-scroll-history))

(defun ivy--maybe-scroll-history ()
  "If the selected history element has an index, scroll there."
  (let ((idx (ignore-errors
               (get-text-property
                (minibuffer-prompt-end)
                'ivy-index))))
    (when idx
      (ivy--exhibit)
      (setq ivy--index idx))))

(defun ivy--cd (dir)
  "When completing file names, move to directory DIR."
  (if (null ivy--directory)
      (error "Unexpected")
    (setq ivy--old-cands nil)
    (setq ivy--old-re nil)
    (setq ivy--index 0)
    (setq ivy--all-candidates
          (ivy--sorted-files (setq ivy--directory dir)))
    (setq ivy-text "")
    (delete-minibuffer-contents)))

(defun ivy-backward-delete-char ()
  "Forward to `backward-delete-char'.
On error (read-only), call `ivy-on-del-error-function'."
  (interactive)
  (if (and ivy--directory (= (minibuffer-prompt-end) (point)))
      (progn
        (ivy--cd (file-name-directory
                  (directory-file-name
                   (expand-file-name
                    ivy--directory))))
        (ivy--exhibit))
    (condition-case nil
        (backward-delete-char 1)
      (error
       (when ivy-on-del-error-function
         (funcall ivy-on-del-error-function))))))

(defvar ivy--regexp-quote 'regexp-quote
  "Store the regexp quoting state.")

(defun ivy-toggle-regexp-quote ()
  "Toggle the regexp quoting."
  (interactive)
  (setq ivy--old-re nil)
  (cl-rotatef ivy--regex-function ivy--regexp-quote))

(defun ivy-sort-file-function-default (x y)
  "Compare two files X and Y.
Prioritize directories."
  (if (get-text-property 0 'dirp x)
      (if (get-text-property 0 'dirp y)
          (string< x y)
        t)
    (if (get-text-property 0 'dirp y)
        nil
      (string< x y))))

(defvar ivy-sort-functions-alist
  '((read-file-name-internal . ivy-sort-file-function-default)
    (internal-complete-buffer . nil)
    (counsel-git-grep-function . nil)
    (t . string-lessp))
  "An alist of sorting functions for each collection function.
For each entry, nil means no sorting.
The entry associated to t is used for all fall-through cases.")

(defvar ivy-re-builders-alist
  '((t . ivy--regex-plus))
  "An alist of regex building functions for each collection function.
Each function should take a string and return a valid regex or a
regex sequence (see below).

The entry associated to t is used for all fall-through cases.
Possible choices: `ivy--regex', `regexp-quote', `ivy--regex-plus'.

In case a function returns a list, it should look like this:
'((\"matching-regexp\" . t) (\"non-matching-regexp\") ...).

The matches will be filtered in a sequence, you can mix the
regexps that should match and that should not match as you
like.")

(defcustom ivy-sort-max-size 30000
  "Sorting won't be done for collections larger than this."
  :type 'integer)

(defun ivy--sorted-files (dir)
  "Return the list of files in DIR.
Directories come first."
  (let* ((default-directory dir)
         (seq (all-completions "" 'read-file-name-internal))
         sort-fn)
    (if (equal dir "/")
        seq
      (setq seq (delete "./" (delete "../" seq)))
      (when (eq (setq sort-fn (cdr (assoc 'read-file-name-internal
                                          ivy-sort-functions-alist)))
                'ivy-sort-file-function-default)
        (setq seq (mapcar (lambda (x)
                            (propertize x 'dirp (string-match-p "/$" x)))
                          seq)))
      (when sort-fn
        (setq seq (cl-sort seq sort-fn)))
      (dolist (dir ivy-extra-directories)
        (push dir seq))
      seq)))

;;** Entry Point
(cl-defun ivy-read (prompt collection
                    &key predicate require-match initial-input
                      history preselect keymap update-fn sort
                      action unwind)
  "Read a string in the minibuffer, with completion.

PROMPT is a string to prompt with; normally it ends in a colon
and a space.  When PROMPT contains %d, it will be updated with
the current number of matching candidates.
See also `ivy-count-format'.

COLLECTION is a list of strings.

If INITIAL-INPUT is non-nil, insert it in the minibuffer initially.

KEYMAP is composed together with `ivy-minibuffer-map'.

If PRESELECT is non-nil select the corresponding candidate out of
the ones that match INITIAL-INPUT.

UPDATE-FN is called each time the current candidate(s) is changed.

When SORT is t, refer to `ivy-sort-functions-alist' for sorting.

ACTION is a lambda to call after a result was selected.

UNWIND is a lambda to call before exiting."
  (setq ivy-last
        (make-ivy-state
         :prompt prompt
         :collection collection
         :predicate predicate
         :require-match require-match
         :initial-input initial-input
         :history history
         :preselect preselect
         :keymap keymap
         :update-fn update-fn
         :sort sort
         :action action
         :window (selected-window)
         :unwind unwind))
  (setq ivy--directory nil)
  (setq ivy--regex-function
        (or (and (functionp collection)
                 (cdr (assoc collection ivy-re-builders-alist)))
            (cdr (assoc t ivy-re-builders-alist))
            'ivy--regex))
  (setq ivy--subexps 0)
  (setq ivy--regexp-quote 'regexp-quote)
  (setq ivy--collection (and (functionp collection)
                             collection))
  (setq ivy--old-text "")
  (setq ivy-text "")
  (let (coll sort-fn)
    (cond ((eq collection 'Info-read-node-name-1)
           (if (equal Info-current-file "dir")
               (setq coll
                     (mapcar (lambda (x) (format "(%s)" x))
                             (cl-delete-duplicates
                              (all-completions "(" collection predicate)
                              :test 'equal)))
             (setq coll (all-completions "" collection predicate))))
          ((eq collection 'read-file-name-internal)
           (setq ivy--directory default-directory)
           (setq coll
                 (ivy--sorted-files default-directory))
           (when initial-input
             (unless (or require-match
                         (equal initial-input default-directory))
               (setq coll (cons initial-input coll)))
             (setq initial-input nil)))
          ((eq collection 'internal-complete-buffer)
           (setq coll
                 (mapcar (lambda (x)
                           (if (with-current-buffer x
                                 (file-remote-p
                                  (abbreviate-file-name default-directory)))
                               (propertize x 'face 'ivy-remote)
                             x))
                         (all-completions "" collection predicate))))
          ((or (functionp collection)
               (vectorp collection)
               (listp (car collection)))
           (setq coll (all-completions "" collection predicate)))
          ((hash-table-p collection)
           (error "Hash table as a collection unsupported"))
          (t
           (setq coll collection)))
    (when sort
      (if (and (functionp collection)
               (setq sort-fn (assoc collection ivy-sort-functions-alist)))
          (when (and (setq sort-fn (cdr sort-fn))
                     (not (eq collection 'read-file-name-internal)))
            (setq coll (cl-sort coll sort-fn)))
        (unless (eq history 'org-refile-history)
          (if (and (setq sort-fn (cdr (assoc t ivy-sort-functions-alist)))
                   (<= (length coll) ivy-sort-max-size))
              (setq coll (cl-sort (copy-sequence coll) sort-fn))))))
    (when preselect
      (unless (or require-match
                  (cl-find-if `(lambda (x)
                                 (string-match ,(format "^%s" preselect) x))
                              coll))
        (setq coll (cons preselect coll))))
    (setq ivy--index (or
                      (and preselect
                           (ivy--preselect-index
                            coll initial-input preselect))
                      0))
    (setq ivy--old-re nil)
    (setq ivy--old-cands nil)
    (setq ivy--all-candidates coll)
    (setq ivy--update-fn update-fn)
    (setq ivy-exit nil)
    (setq ivy--default (or (thing-at-point 'symbol) ""))
    (setq ivy--prompt
          (cond ((string-match "%.*d" prompt)
                 prompt)
                ((string-match "%.*d" ivy-count-format)
                 (concat ivy-count-format prompt))
                (ivy--directory
                 prompt)
                (t
                 nil)))
    (prog1
        (unwind-protect
             (minibuffer-with-setup-hook
                 #'ivy--minibuffer-setup
               (let* ((hist (or history 'ivy-history))
                      (res (read-from-minibuffer
                            prompt
                            initial-input
                            (make-composed-keymap keymap ivy-minibuffer-map)
                            nil
                            hist)))
                 (when (eq ivy-exit 'done)
                   (set hist (cons (propertize ivy-text 'ivy-index ivy--index)
                                   (delete ivy-text
                                           (cdr (symbol-value hist)))))
                   res)))
          (remove-hook 'post-command-hook #'ivy--exhibit)
          (when (setq unwind (ivy-state-unwind ivy-last))
            (funcall unwind)))
      (when (setq action (ivy-state-action ivy-last))
        (funcall action)))))

(defun ivy-completing-read (prompt collection
                            &optional predicate require-match initial-input
                              history def _inherit-input-method)
  "Read a string in the minibuffer, with completion.

This is an interface that conforms to `completing-read', so that
it can be used for `completing-read-function'.

PROMPT is a string to prompt with; normally it ends in a colon and a space.
COLLECTION can be a list of strings, an alist, an obarray or a hash table.
PREDICATE limits completion to a subset of COLLECTION.
REQUIRE-MATCH is considered boolean. See `completing-read'.
INITIAL-INPUT is a string that can be inserted into the minibuffer initially.
_HISTORY is ignored for now.
DEF is the default value.
_INHERIT-INPUT-METHOD is ignored for now.

The history, defaults and input-method arguments are ignored for now."
  (ivy-read prompt collection
            :predicate predicate
            :require-match require-match
            :initial-input initial-input
            :preselect (if (listp def) (car def) def)
            :history history
            :keymap nil
            :sort t))

;;;###autoload
(define-minor-mode ivy-mode
    "Toggle Ivy mode on or off.
With ARG, turn Ivy mode on if arg is positive, off otherwise.
Turning on Ivy mode will set `completing-read-function' to
`ivy-completing-read'.

\\{ivy-minibuffer-map}"
  :group 'ivy
  :global t
  :lighter " ivy"
  (if ivy-mode
      (setq completing-read-function 'ivy-completing-read)
    (setq completing-read-function 'completing-read-default)))

(defun ivy--preselect-index (candidates initial-input preselect)
  "Return the index in CANDIDATES filtered by INITIAL-INPUT for PRESELECT."
  (when initial-input
    (setq initial-input (ivy--regex-plus initial-input))
    (setq candidates
          (cl-remove-if-not
           (lambda (x)
             (string-match initial-input x))
           candidates)))
  (or (cl-position preselect candidates :test 'equal)
      (cl-position-if
       (lambda (x)
         (string-match preselect x))
       candidates)))

;;* Implementation
;;** Regex
(defvar ivy--subexps 0
  "Number of groups in the current `ivy--regex'.")

(defvar ivy--regex-hash
  (make-hash-table :test 'equal)
  "Store pre-computed regex.")

(defun ivy--split (str)
  "Split STR into a list by single spaces.
The remaining spaces stick to their left.
This allows to \"quote\" N spaces by inputting N+1 spaces."
  (let ((len (length str))
        (start 0)
        res s)
    (while (and (string-match " +" str start)
                (< start len))
      (setq s (substring str start (1- (match-end 0))))
      (unless (= (length s) 0)
        (push s res))
      (setq start (match-end 0)))
    (setq s (substring str start))
    (unless (= (length s) 0)
      (push s res))
    (nreverse res)))

(defun ivy--regex (str &optional greedy)
  "Re-build regex from STR in case it has a space.
When GREEDY is non-nil, join words in a greedy way."
  (let ((hashed (unless greedy
                  (gethash str ivy--regex-hash))))
    (if hashed
        (prog1 (cdr hashed)
          (setq ivy--subexps (car hashed)))
      (cdr (puthash str
                    (let ((subs (ivy--split str)))
                      (if (= (length subs) 1)
                          (cons
                           (setq ivy--subexps 0)
                           (car subs))
                        (cons
                         (setq ivy--subexps (length subs))
                         (mapconcat
                          (lambda (x)
                            (if (string-match "^\\\\(.*\\\\)$" x)
                                x
                              (format "\\(%s\\)" x)))
                          subs
                          (if greedy
                              ".*"
                            ".*?")))))
                    ivy--regex-hash)))))

(defun ivy--regex-ignore-order (str)
  "Re-build regex from STR by splitting it on spaces.
Ignore the order of each group."
  (let* ((subs (split-string str " +" t))
         (len (length subs)))
    (cl-case len
      (1
       (setq ivy--subexps 0)
       (car subs))
      (t
       (setq ivy--subexps len)
       (let ((all (mapconcat #'identity subs "\\|")))
         (mapconcat
          (lambda (x)
            (if (string-match "^\\\\(.*\\\\)$" x)
                x
              (format "\\(%s\\)" x)))
          (make-list len all)
          ".*?"))))))

(defun ivy--regex-plus (str)
  "Build a regex sequence from STR.
Spaces are wild, everything before \"!\" should match.
Everything after \"!\" should not match."
  (let ((parts (split-string str "!" t)))
    (cl-case (length parts)
      (0
       "")
      (1
       (ivy--regex (car parts)))
      (2
       (let ((res
              (mapcar #'list
                      (split-string (cadr parts) " " t))))
         (cons (cons (ivy--regex (car parts)) t)
               res)))
      (t (error "Unexpected: use only one !")))))

;;** Rest
(defun ivy--minibuffer-setup ()
  "Setup ivy completion in the minibuffer."
  (set (make-local-variable 'completion-show-inline-help) nil)
  (set (make-local-variable 'minibuffer-default-add-function)
       (lambda ()
         (list ivy--default)))
  (setq-local max-mini-window-height ivy-height)
  (add-hook 'post-command-hook #'ivy--exhibit nil t)
  ;; show completions with empty input
  (ivy--exhibit))

(defun ivy--input ()
  "Return the current minibuffer input."
  ;; assume one-line minibuffer input
  (buffer-substring-no-properties
   (minibuffer-prompt-end)
   (line-end-position)))

(defun ivy--cleanup ()
  "Delete the displayed completion candidates."
  (save-excursion
    (goto-char (minibuffer-prompt-end))
    (delete-region (line-end-position) (point-max))))

(defvar ivy--dynamic-function nil
  "When this is non-nil, call it for each input change to get new candidates.")

(defvar ivy--full-length nil
  "When `ivy--dynamic-function' is non-nil, this can be the total amount of candidates.")

(defvar ivy--old-text ""
  "Store old `ivy-text' for dynamic completion.")

(defun ivy--insert-prompt ()
  "Update the prompt according to `ivy--prompt'."
  (when ivy--prompt
    (unless (memq this-command '(ivy-done ivy-alt-done ivy-partial-or-done
                                 counsel-find-symbol))
      (setq ivy--prompt-extra ""))
    (let (head tail)
      (if (string-match "\\(.*\\): $" ivy--prompt)
          (progn
            (setq head (match-string 1 ivy--prompt))
            (setq tail ": "))
        (setq head (substring ivy--prompt 0 -1))
        (setq tail " "))
      (let ((inhibit-read-only t)
            (std-props '(front-sticky t rear-nonsticky t field t read-only t))
            (n-str
             (format
              (concat head
                      ivy--prompt-extra
                      tail
                      (if ivy--directory
                          (abbreviate-file-name ivy--directory)
                        ""))
              (or (and ivy--dynamic-function
                       ivy--full-length)
                  ivy--length))))
        (save-excursion
          (goto-char (point-min))
          (delete-region (point-min) (minibuffer-prompt-end))
          (set-text-properties 0 (length n-str)
                               `(face minibuffer-prompt ,@std-props)
                               n-str)
          (ivy--set-match-props n-str "confirm"
                                `(face ivy-confirm-face ,@std-props))
          (ivy--set-match-props n-str "match required"
                                `(face ivy-match-required-face ,@std-props))
          (insert n-str))
        ;; get out of the prompt area
        (constrain-to-field nil (point-max))))))

(defun ivy--set-match-props (str match props)
  "Set STR text proprties that match MATCH to PROPS."
  (when (string-match match str)
    (set-text-properties
     (match-beginning 0)
     (match-end 0)
     props
     str)))

(defvar inhibit-message)

(defun ivy--exhibit ()
  "Insert Ivy completions display.
Should be run via minibuffer `post-command-hook'."
  (setq ivy-text (ivy--input))
  (if ivy--dynamic-function
      ;; while-no-input would cause annoying
      ;; "Waiting for process to die...done" message interruptions
      (let ((inhibit-message t))
        (while-no-input
          (unless (equal ivy--old-text ivy-text)
            (let ((store ivy--dynamic-function)
                  (ivy--dynamic-function nil))
              (setq ivy--all-candidates (funcall store ivy-text))))
          (ivy--insert-minibuffer (ivy--format ivy--all-candidates))))
    (cond (ivy--directory
           (if (string-match "/$" ivy-text)
               (if (member ivy-text ivy--all-candidates)
                   (ivy--cd (expand-file-name ivy-text ivy--directory))
                 (when (string-match "//$" ivy-text)
                   (ivy--cd "/")))
             (if (string-match "~$" ivy-text)
                 (ivy--cd (expand-file-name "~/")))))
          ((eq ivy--collection 'internal-complete-buffer)
           (when (or (and (string-match "^ " ivy-text)
                          (not (string-match "^ " ivy--old-text)))
                     (and (string-match "^ " ivy--old-text)
                          (not (string-match "^ " ivy-text))))
             (setq ivy--all-candidates
                   (all-completions
                    (if (and (> (length ivy-text) 0)
                             (eq (aref ivy-text 0)
                                 ?\ ))
                        " "
                      "")
                    'internal-complete-buffer))
             (setq ivy--old-re nil))))
    (ivy--insert-minibuffer
     (ivy--format
      (ivy--filter ivy-text ivy--all-candidates))))
  (setq ivy--old-text ivy-text))

(defun ivy--insert-minibuffer (text)
  "Insert TEXT into minibuffer with appropriate cleanup."
  (ivy--cleanup)
  (let ((buffer-undo-list t)
        deactivate-mark)
    (when ivy--update-fn
      (funcall ivy--update-fn))
    (ivy--insert-prompt)
    ;; Do nothing if while-no-input was aborted.
    (when (stringp text)
      (save-excursion
        (forward-line 1)
        (insert text)))))

(defun ivy--add-face (str face)
  "Propertize STR with FACE.
`font-lock-append-text-property' is used, since it's better than
`propertize' or `add-face-text-property' in this case."
  (require 'colir)
  (condition-case nil
      (colir-blend-face-background 0 (length str) face str)
    (error
     (ignore-errors
       (font-lock-append-text-property 0 (length str) 'face face str))))
  str)

(defun ivy--filter (name candidates)
  "Return all items that match NAME in CANDIDATES.
CANDIDATES are assumed to be static."
  (let* ((re (funcall ivy--regex-function name))
         (cands (cond ((and (equal re ivy--old-re)
                            ivy--old-cands)
                       ivy--old-cands)
                      ((and ivy--old-re
                            (stringp re)
                            (stringp ivy--old-re)
                            (not (string-match "\\\\" ivy--old-re))
                            (not (equal ivy--old-re ""))
                            (memq (cl-search
                                   (if (string-match "\\\\)$" ivy--old-re)
                                       (substring ivy--old-re 0 -2)
                                     ivy--old-re)
                                   re) '(0 2)))
                       (ignore-errors
                         (cl-remove-if-not
                          (lambda (x) (string-match re x))
                          ivy--old-cands)))
                      (t
                       (let ((re-list (if (stringp re) (list (cons re t)) re))
                             (res candidates))
                         (dolist (re re-list)
                           (setq res
                                 (ignore-errors
                                   (funcall
                                    (if (cdr re)
                                        #'cl-remove-if-not
                                      #'cl-remove-if)
                                    `(lambda (x) (string-match ,(car re) x))
                                    res))))
                         res))))
         (tail (nthcdr ivy--index ivy--old-cands))
         idx)
    (when (and tail ivy--old-cands)
      (unless (and (not (equal re ivy--old-re))
                   (or (setq ivy--index
                             (or
                              (cl-position re cands
                                           :test 'equal)
                              (and ivy--directory
                                   (cl-position
                                    (concat re "/") cands
                                    :test 'equal))))))
        (while (and tail (null idx))
          ;; Compare with eq to handle equal duplicates in cands
          (setq idx (cl-position (pop tail) cands)))
        (setq ivy--index (or idx 0))))
    (when (and (string= name "") (not (equal ivy--old-re "")))
      (setq ivy--index
            (or (cl-position (ivy-state-preselect ivy-last)
                             cands :test 'equal)
                ivy--index)))
    (setq ivy--old-re re)
    (setq ivy--old-cands cands)))

(defun ivy--format (cands)
  "Return a string for CANDS suitable for display in the minibuffer.
CANDS is a list of strings."
  (setq ivy--length (length cands))
  (when (>= ivy--index ivy--length)
    (setq ivy--index (max (1- ivy--length) 0)))
  (if (null cands)
      (setq ivy--current "")
    (let* ((half-height (/ ivy-height 2))
           (start (max 0 (- ivy--index half-height)))
           (end (min (+ start (1- ivy-height)) ivy--length))
           (cands (cl-subseq cands start end))
           (index (min ivy--index half-height (1- (length cands)))))
      (when ivy--directory
        (setq cands (mapcar (lambda (x)
                              (if (string-match-p "/$" x)
                                  (propertize x 'face 'ivy-subdir)
                                x))
                            cands)))
      (setq ivy--current (copy-sequence (nth index cands)))
      (setf (nth index cands)
            (ivy--add-face ivy--current 'ivy-current-match))
      (let* ((ww (window-width))
             (res (concat "\n" (mapconcat
                                (lambda (s)
                                  (if (> (length s) ww)
                                      (concat (substring s 0 (- ww 3)) "...")
                                    s))
                                cands "\n"))))
        (put-text-property 0 (length res) 'read-only nil res)
        res))))

(provide 'ivy)

;;; ivy.el ends here
