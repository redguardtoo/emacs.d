;;; avy.el --- set-based completion -*- lexical-binding: t -*-

;; Copyright (C) 2015  Free Software Foundation, Inc.

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/avy
;; Package-Version: 0.3.0
;; Version: 0.3.0
;; Package-Requires: ((emacs "24.1") (cl-lib "0.5"))
;; Keywords: point, location

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
;; This package provides a generic completion method based on building
;; a balanced decision tree with each candidate being a leaf.  To
;; traverse the tree from the root to a desired leaf, typically a
;; sequence of `read-char' can be used.
;;
;; In order for `read-char' to make sense, the tree needs to be
;; visualized appropriately, with a character at each branch node.  So
;; this completion method works only for things that you can see on
;; your screen, all at once:
;;
;; * character positions
;; * word or subword start positions
;; * line beginning positions
;; * link positions
;; * window positions
;;
;; If you're familiar with the popular `ace-jump-mode' package, this
;; package does all that and more, without the implementation
;; headache.

;;; Code:
(require 'cl-lib)

;;* Customization
(defgroup avy nil
  "Jump to things tree-style."
  :group 'convenience
  :prefix "avy-")

(defcustom avy-keys '(?a ?s ?d ?f ?g ?h ?j ?k ?l)
  "Default keys for jumping."
  :type '(repeat :tag "Keys" character))

(defcustom avy-keys-alist nil
  "Alist of avy-jump commands to `avy-keys' overriding the default `avy-keys'."
  :type '(alist
          :key-type (choice :tag "Command"
                     (const avy-goto-char)
                     (const avy-goto-char-2)
                     (const avy-isearch)
                     (const avy-goto-line)
                     (const avy-goto-subword-0)
                     (const avy-goto-subword-1)
                     (const avy-goto-word-0)
                     (const avy-goto-word-1)
                     (const avy-copy-line)
                     (const avy-copy-region)
                     (const avy-move-line))
          :value-type (repeat :tag "Keys" character)))

(defcustom avy-style 'at-full
  "The default method of displaying the overlays.
Use `avy-styles-alist' to customize this per-command."
  :type '(choice
          (const :tag "Pre" pre)
          (const :tag "At" at)
          (const :tag "At Full" at-full)
          (const :tag "Post" post)
          (const :tag "De Bruijn" de-bruijn)))

(defcustom avy-styles-alist nil
  "Alist of avy-jump commands to the style for each command.
If the commands isn't on the list, `avy-style' is used."
  :type '(alist
          :key-type (choice :tag "Command"
                     (const avy-goto-char)
                     (const avy-goto-char-2)
                     (const avy-isearch)
                     (const avy-goto-line)
                     (const avy-goto-subword-0)
                     (const avy-goto-subword-1)
                     (const avy-goto-word-0)
                     (const avy-goto-word-1)
                     (const avy-copy-line)
                     (const avy-copy-region)
                     (const avy-move-line))
          :value-type (choice
                       (const :tag "Pre" pre)
                       (const :tag "At" at)
                       (const :tag "At Full" at-full)
                       (const :tag "Post" post))))

(defcustom avy-background nil
  "When non-nil, a gray background will be added during the selection."
  :type 'boolean)

(defcustom avy-all-windows t
  "Determine the list of windows to consider in search of candidates."
  :type
  '(choice
    (const :tag "All Frames" all-frames)
    (const :tag "This Frame" t)
    (const :tag "This Window" nil)))

(defcustom avy-case-fold-search t
  "Non-nil if searches should ignore case."
  :type 'boolean)

(defcustom avy-word-punc-regexp "[!-/:-@[-`{-~]"
  "Regexp of punctuation chars that count as word starts for `avy-goto-word-1.
When nil, punctuation chars will not be matched.

\"[!-/:-@[-`{-~]\" will match all printable punctuation chars."
  :type 'regexp)

(defcustom avy-ignored-modes '(image-mode doc-view-mode pdf-view-mode)
  "List of modes to ignore when searching for candidates.
Typically, these modes don't use the text representation.")

(defvar avy-translate-char-function #'identity
  "Function to translate user input key into another key.
For example, to make SPC do the same as ?a, use
\(lambda (c) (if (= c 32) ?a c)).")

(defface avy-lead-face-0
  '((t (:foreground "white" :background "#4f57f9")))
  "Face used for first non-terminating leading chars.")

(defface avy-lead-face-1
    '((t (:foreground "white" :background "gray")))
  "Face used for matched leading chars.")

(defface avy-lead-face-2
    '((t (:foreground "white" :background "#f86bf3")))
  "Face used for leading chars.")

(defface avy-lead-face
  '((t (:foreground "white" :background "#e52b50")))
  "Face used for the leading chars.")

(defface avy-background-face
  '((t (:foreground "gray40")))
  "Face for whole window background during selection.")

(defconst avy-lead-faces '(avy-lead-face
                           avy-lead-face-0
                           avy-lead-face-2
                           avy-lead-face
                           avy-lead-face-0
                           avy-lead-face-2)
  "Face sequence for `avy--overlay-at-full'.")

;;* Internals
;;** Tree
(defmacro avy-multipop (lst n)
  "Remove LST's first N elements and return them."
  `(if (<= (length ,lst) ,n)
       (prog1 ,lst
         (setq ,lst nil))
     (prog1 ,lst
       (setcdr
        (nthcdr (1- ,n) (prog1 ,lst (setq ,lst (nthcdr ,n ,lst))))
        nil))))

(defun avy--de-bruijn (keys n)
  "De Bruijn sequence for alphabet KEYS and subsequences of length N."
  (let* ((k (length keys))
         (a (make-list (* n k) 0))
         sequence)
    (cl-labels ((db (T p)
                  (if (> T n)
                      (if (eq (% n p) 0)
                          (setq sequence
                                (append sequence
                                        (cl-subseq a 1 (1+ p)))))
                    (setf (nth T a) (nth (- T p) a))
                    (db (1+ T) p)
                    (cl-loop for j from (1+ (nth (- T p) a)) to (1- k) do
                             (setf (nth T a) j)
                             (db (1+ T) T)))))
      (db 1 1)
      (mapcar (lambda (n)
                (nth n keys))
              sequence))))

(defun avy--path-alist-1 (lst seq-len keys)
  "Build a De Bruin sequence from LST.
SEQ-LEN is how many elements of KEYS it takes to identify a match."
  (let ((db-seq (avy--de-bruijn keys seq-len))
        prev-pos prev-seq prev-win path-alist)
    ;; The De Bruijn seq is cyclic, so append the seq-len - 1 first chars to
    ;; the end.
    (setq db-seq (nconc db-seq (cl-subseq db-seq 0 (1- seq-len))))
    (cl-labels ((subseq-and-pop ()
                  (when (nth (1- seq-len) db-seq)
                    (prog1 (cl-subseq db-seq 0 seq-len)
                      (pop db-seq)))))
      (while lst
        (let* ((cur (car lst))
               (pos (cond
                      ;; ace-window has matches of the form (pos . wnd)
                      ((integerp (car cur)) (car cur))
                      ;; avy-jump have form ((start . end) . wnd)
                      ((consp (car cur)) (caar cur))
                      (t (error "Unexpected match representation: %s" cur))))
               (win (cdr cur))
               (path (if prev-pos
                         (let ((diff (if (eq win prev-win)
                                         (- pos prev-pos)
                                       0)))
                           (when (and (> diff 0) (< diff seq-len))
                             (while (and (nth (1- seq-len) db-seq)
                                         (not
                                          (eq 0 (cl-search
                                                 (cl-subseq prev-seq diff)
                                                 (cl-subseq db-seq 0 seq-len)))))
                               (pop db-seq)))
                           (subseq-and-pop))
                       (subseq-and-pop))))
          (if (not path)
              (setq lst nil
                    path-alist nil)
            (push (cons path (car lst)) path-alist)
            (setq prev-pos pos
                  prev-seq path
                  prev-win win
                  lst (cdr lst))))))
    (nreverse path-alist)))

(defun avy-tree (lst keys)
  "Coerce LST into a balanced tree.
The degree of the tree is the length of KEYS.
KEYS are placed appropriately on internal nodes."
  (let ((len (length keys)))
    (cl-labels
        ((rd (ls)
           (let ((ln (length ls)))
             (if (< ln len)
                 (cl-pairlis keys
                             (mapcar (lambda (x) (cons 'leaf x)) ls))
               (let ((ks (copy-sequence keys))
                     res)
                 (dolist (s (avy-subdiv ln len))
                   (push (cons (pop ks)
                               (if (eq s 1)
                                   (cons 'leaf (pop ls))
                                 (rd (avy-multipop ls s))))
                         res))
                 (nreverse res))))))
      (rd lst))))

(defun avy-subdiv (n b)
  "Distribute N in B terms in a balanced way."
  (let* ((p (1- (floor (+ (log n b) 1e-6))))
         (x1 (expt b p))
         (x2 (* b x1))
         (delta (- n x2))
         (n2 (/ delta (- x2 x1)))
         (n1 (- b n2 1)))
    (append
     (make-list n1 x1)
     (list
      (- n (* n1 x1) (* n2 x2)))
     (make-list n2 x2))))

(defun avy-traverse (tree walker &optional recur-key)
  "Traverse TREE generated by `avy-tree'.
WALKER is a function that takes KEYS and LEAF.

RECUR-KEY is used in recursion.

LEAF is a member of LST argument of `avy-tree'.

KEYS is the path from the root of `avy-tree' to LEAF."
  (dolist (br tree)
    (let ((key (cons (car br) recur-key)))
      (if (eq (cadr br) 'leaf)
          (funcall walker key (cddr br))
        (avy-traverse (cdr br) walker key)))))

(defun avy-handler-default (char)
  "The default hander for a bad CHAR."
  (signal 'user-error (list "No such candidate" char))
  (throw 'done nil))

(defvar avy-handler-function 'avy-handler-default
  "A function to call for a bad `read-char' in `avy-read'.")

(defvar avy-current-path ""
  "Store the current incomplete path during `avy-read'.")

(defun avy-read (tree display-fn cleanup-fn)
  "Select a leaf from TREE using consecutive `read-char'.

DISPLAY-FN should take CHAR and LEAF and signify that LEAFs
associated with CHAR will be selected if CHAR is pressed.  This is
commonly done by adding a CHAR overlay at LEAF position.

CLEANUP-FN should take no arguments and remove the effects of
multiple DISPLAY-FN invokations."
  (catch 'done
    (setq avy-current-path "")
    (while tree
      (let ((avy--leafs nil))
        (avy-traverse tree
                      (lambda (path leaf)
                        (push (cons path leaf) avy--leafs)))
        (dolist (x avy--leafs)
          (funcall display-fn (car x) (cdr x))))
      (let ((char (funcall avy-translate-char-function (read-char)))
            branch)
        (funcall cleanup-fn)
        (if (setq branch (assoc char tree))
            (if (eq (car (setq tree (cdr branch))) 'leaf)
                (throw 'done (cdr tree))
              (setq avy-current-path
                    (concat avy-current-path (string char))))
          (funcall avy-handler-function char))))))

(defun avy-read-de-bruijn (lst keys)
  "Select from LST dispatching on KEYS."
  ;; In theory, the De Bruijn sequence B(k,n) has k^n subsequences of length n
  ;; (the path length) usable as paths, thus that's the lower bound.  Due to
  ;; partially overlapping matches, not all subsequences may be usable, so it's
  ;; possible that the path-len must be incremented, e.g., if we're matching
  ;; for x and a buffer contains xaxbxcx only every second subsequence is
  ;; usable for the four matches.
  (let* ((path-len (ceiling (log (length lst) (length keys))))
         (alist (avy--path-alist-1 lst path-len keys)))
    (while (not alist)
      (cl-incf path-len)
      (setq alist (avy--path-alist-1 lst path-len keys)))
    (let* ((len (length (caar alist)))
           (i 0))
      (setq avy-current-path "")
      (while (< i len)
        (dolist (x (reverse alist))
          (avy--overlay-at-full (reverse (car x)) (cdr x)))
        (let ((char (funcall avy-translate-char-function (read-char))))
          (avy--remove-leading-chars)
          (setq alist
                (delq nil
                      (mapcar (lambda (x)
                                (when (eq (caar x) char)
                                  (cons (cdr (car x)) (cdr x))))
                              alist)))
          (setq avy-current-path
                (concat avy-current-path (string char)))
          (cl-incf i)
          (unless alist
            (funcall avy-handler-function char))))
      (cdar alist))))

;;** Rest
(defun avy-window-list ()
  "Return a list of windows depending on `avy-all-windows'."
  (cond ((eq avy-all-windows 'all-frames)
         (cl-mapcan #'window-list (frame-list)))

        ((eq avy-all-windows t)
         (window-list))

        ((null avy-all-windows)
         (list (selected-window)))

        (t
         (error "Unrecognized option: %S" avy-all-windows))))

(defmacro avy-dowindows (flip &rest body)
  "Depending on FLIP and `avy-all-windows' run BODY in each or selected window."
  (declare (indent 1)
           (debug (form body)))
  `(let ((avy-all-windows (if ,flip
                              (not avy-all-windows)
                            avy-all-windows)))
     (dolist (wnd (avy-window-list))
       (with-selected-window wnd
         (unless (memq major-mode avy-ignored-modes)
           ,@body)))))

(defmacro avy--with-avy-keys (command &rest body)
  "Set `avy-keys' according to COMMAND and execute BODY."
  (declare (indent 1)
           (debug (form body)))
  `(let ((avy-keys (or (cdr (assq ',command avy-keys-alist))
                       avy-keys))
         (avy-style (or (cdr (assq ',command avy-styles-alist))
                        avy-style)))
     ,@body))

(defun avy--goto (x)
  "Goto X.
X is (POS . WND)
POS is either a position or (BEG . END)."
  (cond ((null x)
         (message "zero candidates"))

        ;; ignore exit from `avy-handler-function'
        ((eq x 'exit))

        (t
         (let* ((window (cdr x))
                (frame (window-frame window)))
           (unless (equal frame (selected-frame))
             (select-frame-set-input-focus frame))
           (select-window window))
         (let ((pt (car x)))
           (when (consp pt)
             (setq pt (car pt)))
           (unless (= pt (point)) (push-mark))
           (goto-char pt)))))

(defun avy--process (candidates overlay-fn)
  "Select one of CANDIDATES using `avy-read'.
Use OVERLAY-FN to visualize the decision overlay."
  (unwind-protect
       (cl-case (length candidates)
         (0
          nil)
         (1
          (car candidates))
         (t
          (avy--make-backgrounds
           (avy-window-list))
          (if (eq avy-style 'de-bruijn)
              (avy-read-de-bruijn
               candidates avy-keys)
            (avy-read (avy-tree candidates avy-keys)
                      overlay-fn
                      #'avy--remove-leading-chars))))
    (avy--done)))

(defvar avy--overlays-back nil
  "Hold overlays for when `avy-background' is t.")

(defun avy--make-backgrounds (wnd-list)
  "Create a dim background overlay for each window on WND-LIST."
  (when avy-background
    (setq avy--overlays-back
          (mapcar (lambda (w)
                    (let ((ol (make-overlay
                               (window-start w)
                               (window-end w)
                               (window-buffer w))))
                      (overlay-put ol 'face 'avy-background-face)
                      (overlay-put ol 'window w)
                      ol))
                  wnd-list))))

(defun avy--done ()
  "Clean up overlays."
  (mapc #'delete-overlay avy--overlays-back)
  (setq avy--overlays-back nil)
  (avy--remove-leading-chars))

(defun avy--regex-candidates (regex &optional beg end pred group)
  "Return all elements that match REGEX.
Each element of the list is ((BEG . END) . WND)
When PRED is non-nil, it's a filter for matching point positions.
When GROUP is non-nil, (BEG . END) should delimit that regex group."
  (setq group (or group 0))
  (let ((case-fold-search avy-case-fold-search)
        candidates)
    (avy-dowindows nil
      (let ((we (or end (window-end (selected-window) t))))
        (save-excursion
          (goto-char (or beg (window-start)))
          (while (re-search-forward regex we t)
            (unless (get-char-property (point) 'invisible)
              (when (or (null pred)
                        (funcall pred))
                (push (cons (cons (match-beginning group)
                                  (match-end group))
                            wnd) candidates)))))))
    (nreverse candidates)))

(defvar avy--overlay-offset 0
  "The offset to apply in `avy--overlay'.")

(defvar avy--overlays-lead nil
  "Hold overlays for leading chars.")

(defun avy--remove-leading-chars ()
  "Remove leading char overlays."
  (mapc #'delete-overlay avy--overlays-lead)
  (setq avy--overlays-lead nil))

(defun avy--overlay (str pt wnd)
  "Create an overlay with STR at PT in WND."
  (when (<= (1+ pt) (with-selected-window wnd (point-max)))
    (let* ((pt (+ pt avy--overlay-offset))
           (ol (make-overlay pt (1+ pt) (window-buffer wnd)))
           (old-str (with-selected-window wnd
                      (buffer-substring pt (1+ pt)))))
      (when avy-background
        (setq old-str (propertize
                       old-str 'face 'avy-background-face)))
      (overlay-put ol 'window wnd)
      (overlay-put ol 'display (concat str old-str))
      (push ol avy--overlays-lead))))

(defcustom avy-highlight-first nil
  "When non-nil highlight the first decision char with `avy-lead-face-0'.
Do this even when the char is terminating."
  :type 'boolean)

(defun avy--overlay-pre (path leaf)
  "Create an overlay with PATH at LEAF.
PATH is a list of keys from tree root to LEAF.
LEAF is normally ((BEG . END) . WND)."
  (let ((str (propertize (apply #'string (reverse path))
                         'face 'avy-lead-face)))
    (when (or avy-highlight-first (> (length str) 1))
      (set-text-properties 0 1 '(face avy-lead-face-0) str))
    (setq str (concat
               (propertize avy-current-path
                           'face 'avy-lead-face-1)
               str))
    (avy--overlay
     str
     (cond ((numberp leaf)
            leaf)
           ((consp (car leaf))
            (caar leaf))
           (t
            (car leaf)))
     (if (consp leaf)
         (cdr leaf)
       (selected-window)))))

(defun avy--overlay-at (path leaf)
  "Create an overlay with PATH at LEAF.
PATH is a list of keys from tree root to LEAF.
LEAF is normally ((BEG . END) . WND)."
  (let ((str (propertize
              (string (car (last path)))
              'face 'avy-lead-face))
        (pt (+ (if (consp (car leaf))
                   (caar leaf)
                 (car leaf))
               avy--overlay-offset))
        (wnd (cdr leaf)))
    (let ((ol (make-overlay pt (1+ pt)
                            (window-buffer wnd)))
          (old-str (with-selected-window wnd
                     (buffer-substring pt (1+ pt)))))
      (when avy-background
        (setq old-str (propertize
                       old-str 'face 'avy-background-face)))
      (overlay-put ol 'window wnd)
      (overlay-put ol 'display (if (string= old-str "\n")
                                   (concat str "\n")
                                 str))
      (push ol avy--overlays-lead))))

(defun avy--overlay-at-full (path leaf)
  "Create an overlay with PATH at LEAF.
PATH is a list of keys from tree root to LEAF.
LEAF is normally ((BEG . END) . WND)."
  (let* ((str (propertize
               (apply #'string (reverse path))
               'face 'avy-lead-face))
         (len (length path))
         (beg (if (consp (car leaf))
                  (caar leaf)
                (car leaf)))
         (wnd (cdr leaf))
         oov)
    (dotimes (i len)
      (set-text-properties (- len i 1) (- len i)
                           `(face ,(nth i avy-lead-faces))
                           str))
    (when (eq avy-style 'de-bruijn)
      (setq str (concat
                 (propertize avy-current-path
                             'face 'avy-lead-face-1)
                 str))
      (setq len (length str)))
    (with-selected-window wnd
      (save-excursion
        (goto-char beg)
        (when (setq oov
                    (delq nil
                          (mapcar
                           (lambda (o)
                             (and (eq (overlay-get o 'category) 'avy)
                                  (eq (overlay-get o 'window) wnd)
                                  (overlay-start o)))
                           (overlays-in (point) (min (+ (point) len)
                                                     (line-end-position))))))
          (setq len (- (apply #'min oov) beg))
          (setq str (substring str 0 len)))
        (let ((other-ov (cl-find-if
                         (lambda (o)
                           (and (eq (overlay-get o 'category) 'avy)
                                (eq (overlay-start o) beg)
                                (not (eq (overlay-get o 'window) wnd))))
                         (overlays-in (point) (min (+ (point) len)
                                                   (line-end-position))))))
          (when (and other-ov
                     (> (overlay-end other-ov)
                        (+ beg len)))
            (setq str (concat str (buffer-substring
                                   (+ beg len)
                                   (overlay-end other-ov))))
            (setq len (- (overlay-end other-ov)
                         beg))))
        (let* ((end (if (= beg (line-end-position))
                        (1+ beg)
                      (min (+ beg
                              (if (eq (char-after) ?\t)
                                  1
                                len))
                           (line-end-position))))
               (ol (make-overlay
                    beg end
                    (current-buffer)))
               (old-str (buffer-substring beg (1+ beg))))
          (when avy-background
            (setq old-str (propertize
                           old-str 'face 'avy-background-face)))
          (overlay-put ol 'window wnd)
          (overlay-put ol 'category 'avy)
          (overlay-put ol 'display
                       (cond ((string= old-str "\n")
                              (concat str "\n"))
                             ((string= old-str "\t")
                              (concat str (make-string (- tab-width len) ?\ )))
                             (t
                              str)))
          (push ol avy--overlays-lead))))))

(defun avy--overlay-post (path leaf)
  "Create an overlay with PATH at LEAF.
PATH is a list of keys from tree root to LEAF.
LEAF is normally ((BEG . END) . WND)."
  (let ((str (propertize (apply #'string (reverse path))
                         'face 'avy-lead-face)))
    (when (or avy-highlight-first (> (length str) 1))
      (set-text-properties 0 1 '(face avy-lead-face-0) str))
    (setq str (concat
               (propertize avy-current-path
                           'face 'avy-lead-face-1)
               str))
    (avy--overlay
     str
     (cond ((numberp leaf)
            leaf)
           ((consp (car leaf))
            (cdar leaf))
           (t
            (car leaf)))
     (if (consp leaf)
         (cdr leaf)
       (selected-window)))))

(defun avy--style-fn (style)
  "Transform STYLE symbol to a style function."
  (cl-case style
    (pre #'avy--overlay-pre)
    (at #'avy--overlay-at)
    (at-full 'avy--overlay-at-full)
    (post #'avy--overlay-post)
    (de-bruijn #'avy--overlay-at-full)
    (t (error "Unexpected style %S" style))))

(defun avy--generic-jump (regex window-flip style)
  "Jump to REGEX.
When WINDOW-FLIP is non-nil, do the opposite of `avy-all-windows'.
STYLE determines the leading char overlay style."
  (let ((avy-all-windows
         (if window-flip
             (not avy-all-windows)
           avy-all-windows)))
    (avy--goto
     (avy--process
      (avy--regex-candidates regex)
      (avy--style-fn style)))))

;;* Commands
;;;###autoload
(defun avy-goto-char (char &optional arg)
  "Jump to the currently visible CHAR.
The window scope is determined by `avy-all-windows' (ARG negates it)."
  (interactive (list (read-char "char: ")
                     current-prefix-arg))
  (avy--with-avy-keys avy-goto-char
    (avy--generic-jump
     (if (= 13 char)
         "\n"
       (regexp-quote (string char)))
     arg
     avy-style)))

;;;###autoload
(defun avy-goto-char-in-line (char)
  "Jump to the currently visible CHAR in the current line."
  (interactive (list (read-char "char: ")))
  (let ((avy-all-windows nil))
    (avy--with-avy-keys avy-goto-char
      (avy--goto
       (avy--process
        (save-restriction
          (narrow-to-region (line-beginning-position)
                            (line-end-position))
          (avy--regex-candidates (regexp-quote (string char))))
        (avy--style-fn avy-style))))))

;;;###autoload
(defun avy-goto-char-2 (char1 char2 &optional arg)
  "Jump to the currently visible CHAR1 followed by CHAR2.
The window scope is determined by `avy-all-windows' (ARG negates it)."
  (interactive (list (read-char "char 1: ")
                     (read-char "char 2: ")
                     current-prefix-arg))
  (avy--with-avy-keys avy-goto-char-2
    (avy--generic-jump
     (regexp-quote (string char1 char2))
     arg
     avy-style)))

;;;###autoload
(defun avy-isearch ()
  "Jump to one of the current isearch candidates."
  (interactive)
  (avy--with-avy-keys avy-isearch
    (let* ((candidates
            (avy--regex-candidates isearch-string))
           (avy-background nil)
           (candidate
            (avy--process candidates (avy--style-fn avy-style))))
      (isearch-done)
      (avy--goto candidate))))

;;;###autoload
(defun avy-goto-word-0 (arg)
  "Jump to a word start.
The window scope is determined by `avy-all-windows' (ARG negates it)."
  (interactive "P")
  (avy--with-avy-keys avy-goto-word-0
    (avy--generic-jump "\\b\\sw" arg avy-style)))

;;;###autoload
(defun avy-goto-word-1 (char &optional arg)
  "Jump to the currently visible CHAR at a word start.
The window scope is determined by `avy-all-windows' (ARG negates it)."
  (interactive (list (read-char "char: ")
                     current-prefix-arg))
  (avy--with-avy-keys avy-goto-word-1
    (let* ((str (string char))
           (regex (cond ((string= str ".")
                         "\\.")
                        ((and avy-word-punc-regexp
                              (string-match avy-word-punc-regexp str))
                         (regexp-quote str))
                        (t
                         (concat
                          "\\b"
                          str)))))
      (avy--generic-jump regex arg avy-style))))

(declare-function subword-backward "subword")

;;;###autoload
(defun avy-goto-subword-0 (&optional arg predicate)
  "Jump to a word or subword start.

The window scope is determined by `avy-all-windows' (ARG negates it).

When PREDICATE is non-nil it's a function of zero parameters that
should return true."
  (interactive "P")
  (require 'subword)
  (avy--with-avy-keys avy-goto-subword-0
    (let ((case-fold-search nil)
          candidates)
      (avy-dowindows arg
        (let ((ws (window-start))
              window-cands)
          (save-excursion
            (goto-char (window-end (selected-window) t))
            (subword-backward)
            (while (> (point) ws)
              (when (or (null predicate)
                        (and predicate (funcall predicate)))
                (push (cons (point) (selected-window)) window-cands))
              (subword-backward)))
          (setq candidates (nconc candidates window-cands))))
      (avy--goto
       (avy--process candidates (avy--style-fn avy-style))))))

;;;###autoload
(defun avy-goto-subword-1 (char arg)
  "Jump to the currently visible CHAR at a subword start.
The window scope is determined by `avy-all-windows' (ARG negates it).
The case of CHAR is ignored."
  (interactive (list (read-char "char: ")
                     current-prefix-arg))
  (avy--with-avy-keys avy-goto-subword-1
    (let ((char (downcase char)))
      (avy-goto-subword-0
       arg (lambda () (eq (downcase (char-after)) char))))))

(defun avy-goto-word-or-subword-1 ()
  "Forward to `avy-goto-subword-1' or `avy-goto-word-1'.
Which one depends on variable `subword-mode'."
  (interactive)
  (if (bound-and-true-p subword-mode)
      (call-interactively #'avy-goto-subword-1)
    (call-interactively #'avy-goto-word-1)))

(defun avy--line (&optional arg)
  "Select a line.
The window scope is determined by `avy-all-windows' (ARG negates it)."
  (let ((avy-background nil)
        candidates)
    (avy-dowindows arg
      (let ((ws (window-start)))
        (save-excursion
          (save-restriction
            (narrow-to-region ws (window-end (selected-window) t))
            (goto-char (point-min))
            (while (< (point) (point-max))
              (unless (get-char-property
                       (max (1- (point)) ws) 'invisible)
                (push (cons
                       (if (eq avy-style 'post)
                           (line-end-position)
                         (line-beginning-position))
                       (selected-window)) candidates))
              (forward-line 1))))))
    (avy--process (nreverse candidates) (avy--style-fn avy-style))))

;;;###autoload
(defun avy-goto-line (&optional arg)
  "Jump to a line start in current buffer.
The window scope is determined by `avy-all-windows' (ARG negates it)."
  (interactive "P")
  (avy--with-avy-keys avy-goto-line
    (let ((avy-handler-function
           (lambda (char)
             (if (or (< char ?0)
                     (> char ?9))
                 (avy-handler-default char)
               (let ((line (read-from-minibuffer
                            "Goto line: " (string char))))
                 (when line
                   (goto-char (point-min))
                   (forward-line (1- (string-to-number line)))
                   (throw 'done 'exit)))))))
      (avy--goto (avy--line arg)))))

;;;###autoload
(defun avy-copy-line (arg)
  "Copy a selected line above the current line.
ARG lines can be used."
  (interactive "p")
  (avy--with-avy-keys avy-copy-line
    (let ((start (car (avy--line))))
      (move-beginning-of-line nil)
      (save-excursion
        (insert
         (buffer-substring-no-properties
          start
          (save-excursion
            (goto-char start)
            (move-end-of-line arg)
            (point)))
         "\n")))))

;;;###autoload
(defun avy-move-line (arg)
  "Move a selected line above the current line.
ARG lines can be used."
  (interactive "p")
  (avy--with-avy-keys avy-move-line
    (let ((start (car (avy--line))))
      (move-beginning-of-line nil)
      (save-excursion
        (save-excursion
          (goto-char start)
          (kill-whole-line arg))
        (insert
         (current-kill 0))))))

;;;###autoload
(defun avy-copy-region ()
  "Select two lines and copy the text between them here."
  (interactive)
  (avy--with-avy-keys avy-copy-region
    (let ((beg (car (avy--line)))
          (end (car (avy--line)))
          (pad (if (bolp) "" "\n")))
      (move-beginning-of-line nil)
      (save-excursion
        (insert
         (buffer-substring-no-properties
          beg
          (save-excursion
            (goto-char end)
            (line-end-position)))
         pad)))))

;;;###autoload
(defun avy-setup-default ()
  "Setup the default shortcuts."
  (eval-after-load "isearch"
    '(define-key isearch-mode-map (kbd "C-'") 'avy-isearch)))

(defcustom avy-timeout-seconds 0.5
  "How many seconds to wait for the second char.")

;;;###autoload
(defun avy-goto-char-timer (&optional arg)
  "Read one or two consecutive chars and jump to the first one.
The window scope is determined by `avy-all-windows' (ARG negates it)."
  (interactive "P")
  (let ((c1 (read-char "char 1: "))
        (c2 (read-char "char 2: " nil avy-timeout-seconds)))
    (avy--generic-jump
     (regexp-quote
      (if c2
          (string c1 c2)
        (string c1)))
     arg
     avy-style)))

(define-obsolete-variable-alias
    'avy-goto-char-style 'avy-style "0.1.0"
    "Use `avy-style' and `avy-styles-alist' instead.")
(define-obsolete-variable-alias
    'avy-goto-word-style 'avy-style "0.1.0"
    "Use `avy-style' and `avy-styles-alist' instead.")
(define-obsolete-variable-alias 'avi-keys 'avy-keys "0.1.0")
(define-obsolete-variable-alias 'avi-background 'avy-background "0.1.0")
(define-obsolete-variable-alias 'avi-word-punc-regexp 'avy-word-punc-regexp "0.1.0")
(define-obsolete-face-alias 'avi-lead-face 'avy-lead-face "0.1.0")
(define-obsolete-function-alias 'avi--goto 'avy--goto "0.1.0")
(define-obsolete-function-alias 'avi--process 'avy--process "0.1.0")
(define-obsolete-variable-alias 'avi-all-windows 'avy-all-windows "0.1.0")
(define-obsolete-function-alias 'avi--overlay-pre 'avy--overlay-pre "0.1.0")
(define-obsolete-function-alias 'avi--overlay-at 'avy--overlay-at "0.1.0")
(define-obsolete-function-alias 'avi--overlay-post 'avy--overlay-post "0.1.0")
(define-obsolete-function-alias 'avi-goto-char 'avy-goto-char "0.1.0")
(define-obsolete-function-alias 'avi-goto-char-2 'avy-goto-char-2 "0.1.0")
(define-obsolete-function-alias 'avi-isearch 'avy-isearch "0.1.0")
(define-obsolete-function-alias 'avi-goto-word-0 'avy-goto-word-0 "0.1.0")
(define-obsolete-function-alias 'avi-goto-subword-0 'avy-goto-subword-0 "0.1.0")
(define-obsolete-function-alias 'avi-goto-word-1 'avy-goto-word-1 "0.1.0")
(define-obsolete-function-alias 'avi-goto-line 'avy-goto-line "0.1.0")
(define-obsolete-function-alias 'avi-copy-line 'avy-copy-line "0.1.0")
(define-obsolete-function-alias 'avi-move-line 'avy-move-line "0.1.0")
(define-obsolete-function-alias 'avi-copy-region 'avy-copy-region "0.1.0")
(define-obsolete-function-alias 'avi--regex-candidates 'avy--regex-candidates "0.1.0")

(provide 'avy)

;;; avy.el ends here
