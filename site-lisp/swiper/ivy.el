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
;;* Customization
(defgroup ivy nil
  "Incremental vertical completion."
  :group 'convenience)

(defface ivy-current-match
  '((t (:inherit highlight)))
  "Face used by Ivy for highlighting first match.")

(defface ivy-subdir
  '((t (:weight bold)))
  "Face used by Ivy for highlighting subdirs in the alternatives.")

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

;;* User Visible
;;** Keymap
(require 'delsel)
(defvar ivy-minibuffer-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-m") 'ivy-done)
    (define-key map (kbd "C-j") 'ivy-alt-done)
    (define-key map (kbd "C-n") 'ivy-next-line)
    (define-key map (kbd "C-p") 'ivy-previous-line)
    (define-key map (kbd "C-s") 'ivy-next-line-or-history)
    (define-key map (kbd "C-r") 'ivy-previous-line-or-history)
    (define-key map (kbd "SPC") 'self-insert-command)
    (define-key map (kbd "DEL") 'ivy-backward-delete-char)
    (define-key map (kbd "M-<") 'ivy-beginning-of-buffer)
    (define-key map (kbd "M->") 'ivy-end-of-buffer)
    (define-key map (kbd "M-n") 'ivy-next-history-element)
    (define-key map (kbd "M-p") 'ivy-previous-history-element)
    (define-key map (kbd "C-g") 'minibuffer-keyboard-quit)
    (define-key map (kbd "C-v") 'ivy-scroll-up-command)
    (define-key map (kbd "M-v") 'ivy-scroll-down-command)
    map)
  "Keymap used in the minibuffer.")

(defvar ivy-history nil
  "History list of candidates entered in the minibuffer.

Maximum length of the history list is determined by the value
of `history-length', which see.")

(defvar ivy-require-match t
  "Store require-match. See `completing-read'.")

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

(defvar ivy--action nil
  "Store a function to call at the end of `ivy--read'.")

(defvar ivy--all-candidates nil
  "Store the candidates passed to `ivy-read'.")

(defvar ivy--default nil
  "Default initial input.")

(defvar ivy--update-fn nil
  "Current function to call when current candidate(s) update.")

(defvar ivy--prompt nil
  "Store the format-style prompt.
When non-nil, it should contain one %d.")

(defvar ivy--old-re nil
  "Store the old regexp.")

(defvar ivy--old-cands nil
  "Store the candidates matched by `ivy--old-re'.")

;;** Commands
(defun ivy-done ()
  "Exit the minibuffer with the selected candidate."
  (interactive)
  (delete-minibuffer-contents)
  (cond (ivy--directory
         (insert
          (cond ((string= ivy-text "")
                 (if (equal ivy--current "./")
                     ivy--directory
                   ivy--current))
                ((zerop ivy--length)
                 (expand-file-name ivy-text ivy--directory))
                (t
                 (expand-file-name ivy--current ivy--directory))))
         (setq ivy-exit 'done))
        ((zerop ivy--length)
         (when (memq ivy-require-match
                     '(nil confirm confirm-after-completion))
           (insert ivy-text)
           (setq ivy-exit 'done)))
        (t
         (insert ivy--current)
         (setq ivy-exit 'done)))
  (exit-minibuffer))

(defun ivy-alt-done ()
  "Exit the minibuffer with the selected candidate."
  (interactive)
  (let (dir)
    (cond ((and ivy--directory
                (= 0 ivy--index)
                (= 0 (length ivy-text)))
           (ivy-done))

          ((and ivy--directory
                (plusp ivy--length)
                (file-directory-p
                 (setq dir (expand-file-name
                            ivy--current ivy--directory))))
           (ivy--cd dir)
           (ivy--exhibit))

          (t
           (ivy-done)))))

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

(defun ivy-previous-history-element (arg)
  "Forward to `previous-history-element' with ARG."
  (interactive "p")
  (previous-history-element arg)
  (move-end-of-line 1))

(defun ivy-next-history-element (arg)
  "Forward to `next-history-element' with ARG."
  (interactive "p")
  (next-history-element arg)
  (move-end-of-line 1))

(defun ivy--cd (dir)
  "When completing file names, move to directory DIR."
  (if (null ivy--directory)
      (error "Unexpected")
    (setq ivy--old-cands nil)
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
                  (directory-file-name ivy--directory)))
        (ivy--exhibit))
    (condition-case nil
        (backward-delete-char 1)
      (error
       (when ivy-on-del-error-function
         (funcall ivy-on-del-error-function))))))

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

(defvar ivy-sort-file-function 'ivy-sort-file-function-default
  "The function that compares file names.
It should take two string arguments and return nil and non-nil.")

(defun ivy--sorted-files (dir)
  "Return the list of files in DIR.
Directories come first."
  (let* ((default-directory dir)
         (seq (all-completions "" 'read-file-name-internal)))
    (if (equal dir "/")
        seq
      (setq seq (delete "./" (delete "../" seq)))
      (when (eq ivy-sort-file-function 'ivy-sort-file-function-default)
        (setq seq (mapcar (lambda (x)
                            (propertize x 'dirp (string-match-p "/$" x)))
                          (delete "./" (delete "../" seq)))))
      (setq seq (cl-sort seq ivy-sort-file-function))
      (dolist (dir ivy-extra-directories)
        (push dir seq))
      seq)))

;;** Entry Point
(defun ivy-read (prompt collection
                 &optional predicate initial-input keymap preselect update-fn)
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

UPDATE-FN is called each time the current candidate(s) is changed."
  (setq ivy--directory nil)
  (cond ((eq collection 'Info-read-node-name-1)
         (if (equal Info-current-file "dir")
             (setq collection
                   (mapcar (lambda (x) (format "(%s)" x))
                           (cl-delete-duplicates
                            (all-completions "(" collection predicate)
                            :test 'equal)))
           (setq collection (all-completions "" collection predicate))))
        ((eq collection 'read-file-name-internal)
         (setq ivy--directory default-directory)
         (setq initial-input nil)
         (setq collection
               (ivy--sorted-files default-directory)))
        ((or (functionp collection)
             (vectorp collection))
         (setq collection (all-completions "" collection predicate)))
        ((hash-table-p collection)
         (error "Hash table as a collection unsupported"))
        ((listp (car collection))
         (setq collection (all-completions "" collection predicate))))
  (when preselect
    (unless (or ivy-require-match
                (all-completions preselect collection))
      (setq collection (cons preselect collection))))
  (cl-case (length collection)
    (0 nil)
    (1 (car collection))
    (t
     (setq ivy--index (or
                       (and preselect
                            (ivy--preselect-index
                             collection initial-input preselect))
                       0))
     (setq ivy--old-re nil)
     (setq ivy--old-cands nil)
     (setq ivy-text "")
     (setq ivy--all-candidates collection)
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
     (setq ivy--action nil)
     (prog1
         (unwind-protect
              (minibuffer-with-setup-hook
                  #'ivy--minibuffer-setup
                (let ((res (read-from-minibuffer
                            prompt
                            initial-input
                            (make-composed-keymap keymap ivy-minibuffer-map)
                            nil
                            'ivy-history)))
                  (when (eq ivy-exit 'done)
                    (pop ivy-history)
                    (setq ivy-history
                          (cons ivy-text (delete ivy-text ivy-history)))
                    res)))
           (remove-hook 'post-command-hook #'ivy--exhibit))
       (when ivy--action
         (funcall ivy--action))))))

(defun ivy-completing-read (prompt collection
                            &optional predicate require-match initial-input
                              _history def _inherit-input-method)
  "Read a string in the minibuffer, with completion.

This is an interface that conforms to `completing-read', so that
it can be used for `completing-read-function'.

PROMPT is a string to prompt with; normally it ends in a colon and a space.
COLLECTION can be a list of strings, an alist, an obarray or a hash table.
PREDICATE limits completion to a subset of COLLECTION.

REQUIRE-MATCH is stored into `ivy-require-match'. See `completing-read'.
INITIAL-INPUT is a string that can be inserted into the minibuffer initially.
_HISTORY is ignored for now.
DEF is the default value.
_INHERIT-INPUT-METHOD is ignored for now.

The history, defaults and input-method arguments are ignored for now."
  (when (listp def)
    (setq def (car def)))
  (setq ivy-require-match require-match)
  (ivy-read prompt collection predicate initial-input nil def))

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

(defun ivy--regex (str)
  "Re-build regex from STR in case it has a space."
  (let ((hashed (gethash str ivy--regex-hash)))
    (if hashed
        (prog1 (cdr hashed)
          (setq ivy--subexps (car hashed)))
      (cdr (puthash str
                    (let ((subs (split-string str " +" t)))
                      (if (= (length subs) 1)
                          (cons
                           (setq ivy--subexps 0)
                           (car subs))
                        (cons
                         (setq ivy--subexps (length subs))
                         (mapconcat
                          (lambda (x) (format "\\(%s\\)" x))
                          subs
                          ".*"))))
                    ivy--regex-hash)))))

;;** Rest
(defun ivy--minibuffer-setup ()
  "Setup ivy completion in the minibuffer."
  (set (make-local-variable 'completion-show-inline-help) nil)
  (set (make-local-variable 'minibuffer-default-add-function)
       (lambda ()
         (list ivy--default)))
  (use-local-map (make-composed-keymap ivy-minibuffer-map
                                       (current-local-map)))
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

(defun ivy--insert-prompt ()
  "Update the prompt according to `ivy--prompt'."
  (when ivy--prompt
    (let ((inhibit-read-only t)
          (n-str
           (format
            (if ivy--directory
                (concat ivy--prompt (abbreviate-file-name ivy--directory))
              ivy--prompt) ivy--length)))
      (save-excursion
        (goto-char (point-min))
        (delete-region (point-min) (minibuffer-prompt-end))
        (set-text-properties
         0 (length n-str)
         '(front-sticky t rear-nonsticky t field t read-only t face minibuffer-prompt)
         n-str)
        (insert n-str))
      ;; get out of the prompt area
      (constrain-to-field nil (point-max)))))

(defun ivy--exhibit ()
  "Insert Ivy completions display.
Should be run via minibuffer `post-command-hook'."
  (setq ivy-text (ivy--input))
  (ivy--cleanup)
  (when ivy--directory
    (if (string-match "/$" ivy-text)
        (if (member ivy-text ivy--all-candidates)
            (ivy--cd (expand-file-name ivy-text ivy--directory))
          (ivy--cd "/"))
      (if (string-match "~$" ivy-text)
          (ivy--cd (expand-file-name "~/")))))
  (let ((text (ivy-completions
               ivy-text
               ivy--all-candidates))
        (buffer-undo-list t)
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
  (font-lock-append-text-property 0 (length str) 'face face str)
  str)

(defun ivy-completions (name candidates)
  "Return as text the current completions.
NAME is a string of words separated by spaces that is used to
build a regex.
CANDIDATES is a list of strings."
  (let* ((re (ivy--regex name))
         (cands (cond ((and (equal re ivy--old-re)
                            ivy--old-cands)
                       ivy--old-cands)
                      ((and ivy--old-re
                            (not (equal ivy--old-re ""))
                            (eq 0 (cl-search ivy--old-re re)))
                       (ignore-errors
                         (cl-remove-if-not
                          (lambda (x) (string-match re x))
                          ivy--old-cands)))
                      (t
                       (ignore-errors
                         (cl-remove-if-not
                          (lambda (x) (string-match re x))
                          candidates)))))
         (tail (nthcdr ivy--index ivy--old-cands))
         (ww (window-width))
         idx)
    (when (and tail ivy--old-cands)
      (unless (and (not (equal re ivy--old-re))
                   (setq ivy--index (cl-position re cands :test 'equal)))
        (while (and tail (null idx))
          ;; Compare with eq to handle equal duplicates in cands
          (setq idx (cl-position (pop tail) cands)))
        (setq ivy--index (or idx 0))))
    (setq ivy--old-re re)
    (setq ivy--length (length cands))
    (setq ivy--old-cands cands)
    (when (>= ivy--index ivy--length)
      (setq ivy--index (max (1- ivy--length) 0)))
    (if (null cands)
        ""
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
        (let ((res (concat "\n" (mapconcat
                                 (lambda (s)
                                   (if (> (length s) ww)
                                       (concat (substring s 0 (- ww 3)) "...")
                                     s))
                                 cands "\n"))))
          (put-text-property 0 (length res) 'read-only nil res)
          res)))))

(provide 'ivy)

;;; ivy.el ends here
