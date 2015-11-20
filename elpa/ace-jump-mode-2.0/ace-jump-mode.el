;;; ace-jump-mode.el --- a quick cursor location minor mode for emacs -*- coding: utf-8-unix -*-

;; Copyright (C) 2012 Free Software Foundation, Inc.

;; Author   : winterTTr <winterTTr@gmail.com>
;; URL      : https://github.com/winterTTr/ace-jump-mode/
;; Package-Version: 2.0
;; Version  : 2.0.RC
;; Keywords : motion, location, cursor

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; INTRODUCTION
;;

;; What's this?
;;
;; It is a minor mode for Emacs. It can help you to move your cursor
;; to ANY position in emacs by using only 3 times key press. 

;; Where does ace jump mode come from ?
;;
;; I firstly see such kind of moving style is in a vim plugin called
;; EasyMotion. It really attract me a lot. So I decide to write
;; one for Emacs and MAKE IT BETTER.
;;
;; So I want to thank to :
;;         Bartlomiej P.   for his PreciseJump
;;         Kim Silkebækken for his EasyMotion


;; What's ace-jump-mode ?
;;
;; ace-jump-mode is an fast/direct cursor location minor mode. It will
;; create the N-Branch search tree internal and marks all the possible
;; position with predefined keys in within the whole emacs view.
;; Allowing you to move to the character/word/line almost directly.
;;

;;; Usage
;;
;; Add the following code to your init file, of course you can select
;; the key that you prefer to.
;; ----------------------------------------------------------
;; ;;
;; ;; ace jump mode major function
;; ;; 
;; (add-to-list 'load-path "/full/path/where/ace-jump-mode.el/in/")
;; (autoload
;;   'ace-jump-mode
;;   "ace-jump-mode"
;;   "Emacs quick move minor mode"
;;   t)
;; ;; you can select the key you prefer to
;; (define-key global-map (kbd "C-c SPC") 'ace-jump-mode)
;;
;; ;; 
;; ;; enable a more powerful jump back function from ace jump mode
;; ;;
;; (autoload
;;   'ace-jump-mode-pop-mark
;;   "ace-jump-mode"
;;   "Ace jump back:-)"
;;   t)
;; (eval-after-load "ace-jump-mode"
;;   '(ace-jump-mode-enable-mark-sync))
;; (define-key global-map (kbd "C-x SPC") 'ace-jump-mode-pop-mark)
;; 
;; ;;If you use viper mode :
;; (define-key viper-vi-global-user-map (kbd "SPC") 'ace-jump-mode)
;; ;;If you use evil
;; (define-key evil-normal-state-map (kbd "SPC") 'ace-jump-mode)
;; ----------------------------------------------------------

;;; For more information
;; Intro Doc: https://github.com/winterTTr/ace-jump-mode/wiki
;; FAQ      : https://github.com/winterTTr/ace-jump-mode/wiki/AceJump-FAQ

;;; Code:

(require 'cl)

;;;; ============================================
;;;; Utilities for ace-jump-mode
;;;; ============================================

;; ---------------------
;; aj-position
;; ---------------------

;; make a position in a visual area
(defstruct aj-position offset visual-area)

(defmacro aj-position-buffer (aj-pos)
  "Get the buffer object from `aj-position'."
  `(aj-visual-area-buffer (aj-position-visual-area ,aj-pos)))

(defmacro aj-position-window (aj-pos)
  "Get the window object from `aj-position'."
  `(aj-visual-area-window (aj-position-visual-area ,aj-pos)))

(defmacro aj-position-frame (aj-pos)
  "Get the frame object from `aj-position'."
  `(aj-visual-area-frame (aj-position-visual-area ,aj-pos)))

(defmacro aj-position-recover-buffer (aj-pos)
  "Get the recover-buffer object from `aj-position'."
  `(aj-visual-area-recover-buffer (aj-position-visual-area ,aj-pos)))


;; ---------------------
;; aj-visual-area
;; ---------------------

;; a record for all the possible visual area
;; a visual area is a window that showing some buffer in some frame.
(defstruct aj-visual-area buffer window frame recover-buffer)


;; ---------------------
;; a FIFO queue implementation
;; ---------------------
(defstruct aj-queue head tail)

(defun aj-queue-push (item q)
  "enqueue"
  (let ( (head (aj-queue-head q) )
         (tail (aj-queue-tail q) )
         (c (list item) ) )
    (cond
     ((null (aj-queue-head q))
      (setf (aj-queue-head q) c)
      (setf (aj-queue-tail q) c))
     (t
      (setf (cdr (aj-queue-tail q)) c)
      (setf (aj-queue-tail q) c)))))

(defun aj-queue-pop (q)
  "dequeue"
  (if (null (aj-queue-head q))
      (error "[AceJump] Interal Error: Empty queue"))

  (let ((ret (aj-queue-head q)))
    (if (eq ret (aj-queue-tail q))
        ;; only one item left
        (progn
          (setf (aj-queue-head q) nil)
          (setf (aj-queue-tail q) nil))
      ;; multi item left, move forward the head
      (setf (aj-queue-head q) (cdr ret)))
    (car ret)))



;;; main code start here

;; register as a minor mode
(or (assq 'ace-jump-mode minor-mode-alist)
    (nconc minor-mode-alist
           (list '(ace-jump-mode ace-jump-mode))))

;; custoize variable
(defvar ace-jump-word-mode-use-query-char t
  "If we need to ask for the query char before enter `ace-jump-word-mode'")

(defvar ace-jump-mode-case-fold case-fold-search
  "If non-nil, the ace-jump mode will ignore case.

The default value is set to the same as `case-fold-search'.")

(defvar ace-jump-mode-mark-ring nil
  "The list that is used to store the history for jump back.")

(defvar ace-jump-mode-mark-ring-max 100
  "The max length of `ace-jump-mode-mark-ring'")


(defvar ace-jump-mode-gray-background t
  "By default, when there is more than one candidate, the ace
jump mode will gray the background and then mark the possible
candidate position. Set this to nil means do not gray
background.")

(defvar ace-jump-mode-scope 'global
  "Define what is the scope that ace-jump-mode works.

Now, there are four kinds of values for this:
1. 'global  : ace jump can work across any window and frame, this is also the default.
2. 'frame   : ace jump will work for the all windows in current frame.
3. 'visible : ace jump will work for all windows in visible frames.
3. 'window  : ace jump will only work on current window only.
              This is the same behavior for 1.0 version.")

(defvar ace-jump-mode-detect-punc t
  "When this is non-nil, the ace jump word mode will detect the
char that is not alpha or number. Then, if the query char is a
printable punctuaction, we will use char mode to start the ace
jump mode. If it is nil, an error will come up when
non-alpha-number is given under word mode.")


(defvar ace-jump-mode-submode-list
  '(ace-jump-word-mode
    ace-jump-char-mode
    ace-jump-line-mode)
  "*The mode list when start ace jump mode.
The sequence is the calling sequence when give prefix argument.

Such as:
  If you use the default sequence, which is
      '(ace-jump-word-mode
        ace-jump-char-mode
        ace-jump-line-mode)
and using key to start up ace jump mode, such as 'C-c SPC',
then the usage to start each mode is as below:

   C-c SPC           ==> ace-jump-word-mode
   C-u C-c SPC       ==> ace-jump-char-mode
   C-u C-u C-c SPC   ==> ace-jump-line-mode

Currently, the valid submode is:
   `ace-jump-word-mode'
   `ace-jump-char-mode'
   `ace-jump-line-mode'

")

(defvar ace-jump-mode-move-keys
  (nconc (loop for i from ?a to ?z collect i)
         (loop for i from ?A to ?Z collect i))
  "*The keys that used to move when enter AceJump mode.
Each key should only an printable character, whose name will
fill each possible location.

If you want your own moving keys, you can custom that as follow,
for example, you only want to use lower case character:
\(setq ace-jump-mode-move-keys (loop for i from ?a to ?z collect i)) ")


;;; some internal variable for ace jump
(defvar ace-jump-mode nil
  "AceJump minor mode.")
(defvar ace-jump-background-overlay-list nil
  "Background overlay which will grey all the display.")
(defvar ace-jump-search-tree nil
  "N-branch Search tree. Every leaf node holds the overlay that
is used to highlight the target positions.")
(defvar ace-jump-query-char nil
  "Save the query char used between internal mode.")
(defvar ace-jump-current-mode nil
  "Save the current mode.
See `ace-jump-mode-submode-list' for possible value.")

(defvar ace-jump-sync-emacs-mark-ring nil
  "When this variable is not-nil, everytime `ace-jump-mode-pop-mark' is called,
ace jump will try to remove the same mark from buffer local mark
ring and global-mark-ring, which help you to sync the mark
information between emacs and ace jump.

Note, never try to set this variable manually, this is for ace
jump internal use.  If you want to change it, use
`ace-jump-mode-enable-mark-sync' or
`ace-jump-mode-disable-mark-sync'.")

(defvar ace-jump-search-filter nil
  "This should be nil or a point-dependant predicate
that `ace-jump-search-candidate' will use as an additional filter.")

(defgroup ace-jump nil
  "ace jump group"
  :group 'convenience)

;;; define the face
(defface ace-jump-face-background
  '((t (:foreground "gray40")))
  "Face for background of AceJump motion"
  :group 'ace-jump)


(defface ace-jump-face-foreground
  '((((class color)) (:foreground "red"))
    (((background dark)) (:foreground "gray100"))
    (((background light)) (:foreground "gray0"))
    (t (:foreground "gray100")))
  "Face for foreground of AceJump motion"
  :group 'ace-jump)


(defvar ace-jump-mode-before-jump-hook nil
  "Function(s) to call just before moving the cursor to a selected match")

(defvar ace-jump-mode-end-hook nil
  "Function(s) to call when ace-jump-mode is going to end up")

(defvar ace-jump-allow-invisible nil
  "Control if ace-jump should select the invisible char as candidate.
Normally, the ace jump mark cannot be seen if the target character is invisible.
So default to be nil, which will not include those invisible character as candidate.")


(defun ace-jump-char-category ( query-char )
  "Detect the type of the char.
For the ascii table, refer to http://www.asciitable.com/

There is four possible return value:
1. 'digit: the number character
2. 'alpha: A-Z and a-z
3. 'punc : all the printable punctuaiton
4. 'other: all the others"
  (cond
   ;; digit
   ((and (>= query-char #x30) (<= query-char #x39))
    'digit)
   ((or
     ;; capital letter
     (and (>= query-char #x41) (<= query-char #x5A))
     ;; lowercase letter
     (and (>= query-char #x61) (<= query-char #x7A)))
    'alpha)
   ((or
     ;; tab
     (equal query-char #x9)
     ;; punc before digit
     (and (>= query-char #x20) (<= query-char #x2F))
     ;; punc after digit before capital letter
     (and (>= query-char #x3A) (<= query-char #x40))
     ;; punc after capital letter before lowercase letter
     (and (>= query-char #x5B) (<= query-char #x60))
     ;; punc after lowercase letter
     (and (>= query-char #x7B) (<= query-char #x7E)))
    'punc)
   (t
    'other)))


(defun ace-jump-search-candidate (re-query-string visual-area-list)
  "Search the RE-QUERY-STRING in current view, and return the candidate position list.
RE-QUERY-STRING should be an valid regex used for `search-forward-regexp'.

You can control whether use the case sensitive or not by `ace-jump-mode-case-fold'.

Every possible `match-beginning' will be collected.
The returned value is a list of `aj-position' record."
  (loop for va in visual-area-list
        append (let* ((current-window (aj-visual-area-window va))
                      (start-point (window-start current-window))
                      (end-point   (window-end   current-window t)))
                 (with-selected-window current-window
                   (save-excursion
                     (goto-char start-point)
                     (let ((case-fold-search ace-jump-mode-case-fold))
                       (loop while (re-search-forward re-query-string nil t)
                             until (or
                                    (> (point) end-point)
                                    (eobp))
                             if (and (or ace-jump-allow-invisible (not (invisible-p (match-beginning 0))))
                                  (or (null ace-jump-search-filter)
                                      (ignore-errors
                                        (funcall ace-jump-search-filter))))
                             collect (make-aj-position :offset (match-beginning 0)
                                                       :visual-area va)
                             ;; when we use "^" to search line mode,
                             ;; re-search-backward will not move one
                             ;; char after search success, as line
                             ;; begin is not a valid visible char.
                             ;; We need to help it to move forward.
                             do (if (string-equal re-query-string "^")
                                    (goto-char (1+ (match-beginning 0)))))))))))

(defun ace-jump-tree-breadth-first-construct (total-leaf-node max-child-node)
  "Constrct the search tree, each item in the tree is a cons cell.
The (car tree-node) is the type, which should be only 'branch or 'leaf.
The (cdr tree-node) is data stored in a leaf when type is 'leaf,
while a child node list when type is 'branch"
  (let ((left-leaf-node (- total-leaf-node 1))
        (q (make-aj-queue))
        (node nil)
        (root (cons 'leaf nil)) )
    ;; we push the node into queue and make candidate-sum -1, so
    ;; create the start condition for the while loop
    (aj-queue-push root q)
    (while (> left-leaf-node 0)
      (setq node (aj-queue-pop q))
      ;; when a node is picked up from stack, it will be changed to a
      ;; branch node, we lose a leaft node
      (setf (car node) 'branch)
      ;; so we need to add the sum of leaf nodes that we wish to create
      (setq left-leaf-node (1+ left-leaf-node))
      (if (<= left-leaf-node max-child-node)
          ;; current child can fill the left leaf
          (progn
            (setf (cdr node)
                  (loop for i from 1 to left-leaf-node
                        collect (cons 'leaf nil)))
            ;; so this should be the last action for while
            (setq left-leaf-node 0))
        ;; the child can not cover the left leaf
        (progn
          ;; fill as much as possible. Push them to queue, so it have
          ;; the oppotunity to become 'branch node if necessary
          (setf (cdr node)
                (loop for i from 1 to max-child-node
                      collect (let ((n (cons 'leaf nil)))
                                (aj-queue-push n q)
                                n)))
          (setq left-leaf-node (- left-leaf-node max-child-node)))))
    ;; return the root node
    root))

(defun ace-jump-tree-preorder-traverse (tree &optional leaf-func branch-func)
  "we move over tree via preorder, and call BRANCH-FUNC on each branch
node and call LEAF-FUNC on each leaf node"
  ;; use stack to do preorder traverse
  (let ((s (list tree)))
    (while (not (null s))
      ;; pick up one from stack
      (let ((node (car s)))
        ;; update stack
        (setq s (cdr s))
        (cond
         ((eq (car node) 'branch)
          ;; a branch node
          (when branch-func
            (funcall branch-func node))
          ;; push all child node into stack
          (setq s (append (cdr node) s)))
         ((eq (car node) 'leaf)
          (when leaf-func
            (funcall leaf-func node)))
         (t
          (message "[AceJump] Internal Error: invalid tree node type")))))))


(defun ace-jump-populate-overlay-to-search-tree (tree candidate-list)
  "Populate the overlay to search tree, every leaf will give one overlay"
  
  (lexical-let* (;; create the locally dynamic variable for the following function
                 (position-list candidate-list)
                 
                 ;; make the function to create overlay for each leaf node,
                 ;; here we only create each overlay for each candidate
                 ;; position, , but leave the 'display property to be empty,
                 ;; which will be fill in "update-overlay" function
                 (func-create-overlay (lambda (node)
                                        (let* ((p (car position-list))
                                               (o (aj-position-offset p))
                                               (w (aj-position-window p))
                                               (b (aj-position-buffer p))
                                               ;; create one char overlay
                                               (ol (make-overlay o (1+ o) b)))
                                          ;; update leaf node to remember the ol
                                          (setf (cdr node) ol)
                                          (overlay-put ol 'face 'ace-jump-face-foreground)
                                          ;; this is important, because sometimes the different
                                          ;; window may dispaly the same buffer, in that case, 
                                          ;; overlay for different window (but the same buffer)
                                          ;; will show at the same time on both window
                                          ;; So we make it only on the specific window
                                          (overlay-put ol 'window w)
                                          ;; associate the aj-position data with overlay
                                          ;; so that we can use it to do the final jump
                                          (overlay-put ol 'aj-data p)
                                          ;; next candidate node
                                          (setq position-list (cdr position-list))))))
    (ace-jump-tree-preorder-traverse tree func-create-overlay)
    tree))


(defun ace-jump-delete-overlay-in-search-tree (tree)
  "Delete all the overlay in search tree leaf node"
  (let ((func-delete-overlay (lambda (node)
                               (delete-overlay (cdr node))
                               (setf (cdr node) nil))))
    (ace-jump-tree-preorder-traverse tree func-delete-overlay)))

(defun ace-jump-buffer-substring (pos)
  "Get the char under the POS, which is aj-position structure."
  (let* ((w (aj-position-window pos))
         (offset (aj-position-offset pos)))
    (with-selected-window w
      (buffer-substring offset (1+ offset)))))

(defun ace-jump-update-overlay-in-search-tree (tree keys)
  "Update overlay 'display property using each name in keys"
  (lexical-let* (;; create dynamic variable for following function
                 (key ?\0)
                 ;; populdate each leaf node to be the specific key,
                 ;; this only update 'display' property of overlay,
                 ;; so that user can see the key from screen and select
                 (func-update-overlay
                  (lambda (node)
                    (let ((ol (cdr node)))
                      (overlay-put
                       ol
                       'display
                       (concat (make-string 1 key)
                               (let* ((pos (overlay-get ol 'aj-data))
                                      (subs (ace-jump-buffer-substring pos)))
                                 (cond
                                  ;; when tab, we use more space to prevent screen
                                  ;; from messing up
                                  ((string-equal subs "\t")
                                   (make-string (1- tab-width) ? ))
                                  ;; when enter, we need to add one more enter
                                  ;; to make the screen not change
                                  ((string-equal subs "\n")
                                   "\n")
                                  (t
                                   ;; there are wide-width characters
                                   ;; so, we need paddings
                                   (make-string (max 0 (1- (string-width subs))) ? ))))))))))
    (loop for k in keys
          for n in (cdr tree)
          do (progn
               ;; update "key" variable so that the function can use
               ;; the correct context
               (setq key k)
               (if (eq (car n) 'branch)
                   (ace-jump-tree-preorder-traverse n
                                                    func-update-overlay)
                 (funcall func-update-overlay n))))))



(defun ace-jump-list-visual-area()
  "Based on `ace-jump-mode-scope', search the possible buffers that is showing now."
  (cond
   ((eq ace-jump-mode-scope 'global)
    (loop for f in (frame-list)
          append (loop for w in (window-list f)
                       collect (make-aj-visual-area :buffer (window-buffer w)
                                                    :window w
                                                    :frame f))))
   ((eq ace-jump-mode-scope 'visible)
    (loop for f in (frame-list)
          if (eq t (frame-visible-p f))
          append (loop for w in (window-list f)
                       collect (make-aj-visual-area :buffer (window-buffer w)
                                                    :window w
                                                    :frame f))))
   ((eq ace-jump-mode-scope 'frame)
    (loop for w in (window-list (selected-frame))
          collect (make-aj-visual-area :buffer (window-buffer w)
                                       :window w
                                       :frame (selected-frame))))
   ((eq ace-jump-mode-scope 'window)
    (list 
     (make-aj-visual-area :buffer (current-buffer)
                          :window (selected-window)
                          :frame  (selected-frame))))
   (t
    (error "[AceJump] Invalid ace-jump-mode-scope, please check your configuration"))))



(defun ace-jump-do( re-query-string )
  "The main function to start the AceJump mode.
QUERY-STRING should be a valid regexp string, which finally pass to `search-forward-regexp'.

You can constrol whether use the case sensitive via `ace-jump-mode-case-fold'.
"
  ;; we check the move key to make it valid, cause it can be customized by user
  (if (or (null ace-jump-mode-move-keys)
          (< (length ace-jump-mode-move-keys) 2)
          (not (every #'characterp ace-jump-mode-move-keys)))
      (error "[AceJump] Invalid move keys: check ace-jump-mode-move-keys"))
  ;; search candidate position
  (let* ((visual-area-list (ace-jump-list-visual-area))
         (candidate-list (ace-jump-search-candidate re-query-string visual-area-list)))
    (cond
     ;; cannot find any one
     ((null candidate-list)
      (setq ace-jump-current-mode nil)
      (error "[AceJump] No one found"))
     ;; we only find one, so move to it directly
     ((eq (cdr candidate-list) nil)
      (ace-jump-push-mark)
      (run-hooks 'ace-jump-mode-before-jump-hook)
      (ace-jump-jump-to (car candidate-list))
      (message "[AceJump] One candidate, move to it directly")
      (run-hooks 'ace-jump-mode-end-hook))
     ;; more than one, we need to enter AceJump mode
     (t
      ;; create background for each visual area
      (if ace-jump-mode-gray-background
          (setq ace-jump-background-overlay-list
                (loop for va in visual-area-list
                      collect (let* ((w (aj-visual-area-window va))
                                     (b (aj-visual-area-buffer va))
                                     (ol (make-overlay (window-start w)
                                                       (window-end w)
                                                       b)))
                                (overlay-put ol 'face 'ace-jump-face-background)
                                ol))))

      ;; construct search tree and populate overlay into tree
      (setq ace-jump-search-tree
            (ace-jump-tree-breadth-first-construct (length candidate-list)
                                                   (length ace-jump-mode-move-keys)))
      (ace-jump-populate-overlay-to-search-tree ace-jump-search-tree
                                                candidate-list)
      (ace-jump-update-overlay-in-search-tree ace-jump-search-tree
                                              ace-jump-mode-move-keys)

      ;; do minor mode configuration
      (cond
       ((eq ace-jump-current-mode 'ace-jump-char-mode)
        (setq ace-jump-mode " AceJump - Char"))
       ((eq ace-jump-current-mode 'ace-jump-word-mode)
        (setq ace-jump-mode " AceJump - Word"))
       ((eq ace-jump-current-mode 'ace-jump-line-mode)
        (setq ace-jump-mode " AceJump - Line"))
       (t
        (setq ace-jump-mode " AceJump")))
      (force-mode-line-update)


      ;; override the local key map
      (setq overriding-local-map
            (let ( (map (make-keymap)) )
              (dolist (key-code ace-jump-mode-move-keys)
                (define-key map (make-string 1 key-code) 'ace-jump-move))
              (define-key map (kbd "C-c C-c") 'ace-jump-quick-exchange)
              (define-key map [t] 'ace-jump-done)
              map))

      (add-hook 'mouse-leave-buffer-hook 'ace-jump-done)
      (add-hook 'kbd-macro-termination-hook 'ace-jump-done)))))


(defun ace-jump-jump-to (position)
  "Jump to the POSITION, which is a `aj-position' structure storing the position information"
  (let ((offset (aj-position-offset position))
        (frame (aj-position-frame position))
        (window (aj-position-window position))
        (buffer (aj-position-buffer position)))
        ;; focus to the frame
        (if (and (frame-live-p frame)
                 (not (eq frame (selected-frame))))
            (select-frame-set-input-focus (window-frame window)))
        
        ;; select the correct window
        (if (and (window-live-p window)
                 (not (eq window (selected-window))))
            (select-window window))
        
        ;; swith to buffer
        (if (and (buffer-live-p buffer)
                 (not (eq buffer (window-buffer window))))
            (switch-to-buffer buffer))

        ;; move to correct position
        (if (and (buffer-live-p buffer)
                 (eq (current-buffer) buffer))
            (goto-char offset))))

(defun ace-jump-push-mark ()
  "Push the current position information onto the `ace-jump-mode-mark-ring'."
  ;; add mark to the emacs basic push mark
  (push-mark (point) t)
  ;; we also push the mark on the `ace-jump-mode-mark-ring', which has
  ;; more information for better jump back
  (let ((pos (make-aj-position :offset (point)
                               :visual-area (make-aj-visual-area :buffer (current-buffer)
                                                                 :window (selected-window)
                                                                 :frame  (selected-frame)))))
    (setq ace-jump-mode-mark-ring (cons pos ace-jump-mode-mark-ring)))
  ;; when exeed the max count, discard the last one
  (if (> (length ace-jump-mode-mark-ring) ace-jump-mode-mark-ring-max)
      (setcdr (nthcdr (1- ace-jump-mode-mark-ring-max) ace-jump-mode-mark-ring) nil)))


;;;###autoload
(defun ace-jump-mode-pop-mark ()
  "Pop up a postion from `ace-jump-mode-mark-ring', and jump back to that position"
  (interactive)
  ;; we jump over the killed buffer position
  (while (and ace-jump-mode-mark-ring
              (not (buffer-live-p (aj-position-buffer
                                   (car ace-jump-mode-mark-ring)))))
    (setq ace-jump-mode-mark-ring (cdr ace-jump-mode-mark-ring)))
    
  (if (null ace-jump-mode-mark-ring)
      ;; no valid history exist
      (error "[AceJump] No more history"))

  (if ace-jump-sync-emacs-mark-ring
      (let ((p (car ace-jump-mode-mark-ring)))
        ;; if we are jump back in the current buffer, that means we
        ;; only need to sync the buffer local mark-ring
        (if (eq (current-buffer) (aj-position-buffer p))
            (if (equal (aj-position-offset p) (marker-position (mark-marker)))
                ;; if the current marker is the same as where we need
                ;; to jump back, we do the same as pop-mark actually,
                ;; copy implementation from pop-mark, cannot use it
                ;; directly, as there is advice on it
                (when mark-ring
                  (setq mark-ring (nconc mark-ring (list (copy-marker (mark-marker)))))
                  (set-marker (mark-marker) (+ 0 (car mark-ring)) (current-buffer))
                  (move-marker (car mark-ring) nil)
                  (setq mark-ring (cdr mark-ring))
                  (deactivate-mark))
              
              ;;  But if there is other marker put before the wanted destination, the following scenario
              ;;                                                           
              ;;             +---+---+---+---+                                   +---+---+---+---+
              ;;   Mark Ring | 2 | 3 | 4 | 5 |                                   | 2 | 4 | 5 | 3 |
              ;;             +---+---+---+---+                                   +---+---+---+---+
              ;;             +---+                                               +---+
              ;;   Marker    | 1 |                                               | 1 | <-- Maker (not changed)
              ;;             +---+                                               +---+
              ;;             +---+                                               +---+
              ;;   Cursor    | X |                     Pop up AJ mark 3          | 3 | <-- Cursor position
              ;;             +---+                                               +---+
              ;;             +---+---+---+                                       +---+---+---+ 
              ;;   AJ Ring   | 3 | 4 | 5 |                                       | 4 | 5 | 3 |
              ;;             +---+---+---+                                       +---+---+---+
              ;;   
              ;; So what we need to do, is put the found mark in mark-ring to the end
              (lexical-let ((po (aj-position-offset p)))
                (setq mark-ring
                      (ace-jump-move-first-to-end-if mark-ring
                                                     (lambda (x)
                                                       (equal (marker-position x) po))))))
              

          ;; when we jump back to another buffer, do as the
          ;; pop-global-mark does. But we move the marker with the
          ;; same target buffer to the end, not always the first one
          (lexical-let ((pb (aj-position-buffer p)))
            (setq global-mark-ring
                  (ace-jump-move-first-to-end-if global-mark-ring
                                                 (lambda (x)
                                                   (eq (marker-buffer x) pb))))))))
          
  
  ;; move the first element to the end of the ring
  (ace-jump-jump-to (car ace-jump-mode-mark-ring))
  (setq ace-jump-mode-mark-ring (nconc (cdr ace-jump-mode-mark-ring)
                                       (list (car ace-jump-mode-mark-ring)))))

(defun ace-jump-quick-exchange ()
  "The function that we can use to quick exhange the current mode between
word-mode and char-mode"
  (interactive)
  (cond
   ((eq ace-jump-current-mode 'ace-jump-char-mode)
    (if ace-jump-query-char
        ;; ace-jump-done will clean the query char, so we need to save it
        (let ((query-char ace-jump-query-char))
          (ace-jump-done)
          (ace-jump-word-mode query-char))))
   ((eq ace-jump-current-mode 'ace-jump-word-mode)
    (if ace-jump-query-char
        ;; ace-jump-done will clean the query char, so we need to save it
        (let ((query-char ace-jump-query-char))
          (ace-jump-done)
          ;; restore the flag
          (ace-jump-char-mode query-char))))
   ((eq ace-jump-current-mode 'ace-jump-line-mode)
    nil)
   (t
    nil)))




;;;###autoload
(defun ace-jump-char-mode (query-char)
  "AceJump char mode"
  (interactive (list (read-char "Query Char:")))

  ;; We should prevent recursion call this function.  This can happen
  ;; when you trigger the key for ace jump again when already in ace
  ;; jump mode.  So we stop the previous one first.
  (if ace-jump-current-mode (ace-jump-done))
  
  (if (eq (ace-jump-char-category query-char) 'other)
    (error "[AceJump] Non-printable character"))

  ;; others : digit , alpha, punc
  (setq ace-jump-query-char query-char)
  (setq ace-jump-current-mode 'ace-jump-char-mode)
  (ace-jump-do (regexp-quote (make-string 1 query-char))))


;;;###autoload
(defun ace-jump-word-mode (head-char)
  "AceJump word mode.
You can set `ace-jump-word-mode-use-query-char' to nil to prevent
asking for a head char, that will mark all the word in current
buffer."
  (interactive (list (if ace-jump-word-mode-use-query-char
                         (read-char "Head Char:")
                       nil)))

  ;; We should prevent recursion call this function.  This can happen
  ;; when you trigger the key for ace jump again when already in ace
  ;; jump mode.  So we stop the previous one first.
  (if ace-jump-current-mode (ace-jump-done))

  (cond
   ((null head-char)
    ;; \<  - start of word
    ;; \sw - word constituent
    (ace-jump-do "\\<\\sw"))
   ((memq (ace-jump-char-category head-char)
          '(digit alpha))
    (setq ace-jump-query-char head-char)
    (setq ace-jump-current-mode 'ace-jump-word-mode)
    (ace-jump-do (concat "\\<" (make-string 1 head-char))))
   ((eq (ace-jump-char-category head-char)
        'punc)
    ;; we do not query punctuation under word mode
    (if (null ace-jump-mode-detect-punc)
        (error "[AceJump] Not a valid word constituent"))
    ;; we will use char mode to continue search
    (setq ace-jump-query-char head-char)
    (setq ace-jump-current-mode 'ace-jump-char-mode)
    (ace-jump-do (regexp-quote (make-string 1 head-char))))
   (t
    (error "[AceJump] Non-printable character"))))


;;;###autoload
(defun ace-jump-line-mode ()
  "AceJump line mode.
Marked each no empty line and move there"
  (interactive)

  ;; We should prevent recursion call this function.  This can happen
  ;; when you trigger the key for ace jump again when already in ace
  ;; jump mode.  So we stop the previous one first.
  (if ace-jump-current-mode (ace-jump-done))
  
  (setq ace-jump-current-mode 'ace-jump-line-mode)
  (ace-jump-do "^"))

;;;###autoload
(defun ace-jump-mode(&optional prefix)
  "AceJump mode is a minor mode for you to quick jump to a
position in the curret view.
   There is three submode now:
     `ace-jump-char-mode'
     `ace-jump-word-mode'
     `ace-jump-line-mode'

You can specify the sequence about which mode should enter
by customize `ace-jump-mode-submode-list'.

If you do not want to query char for word mode, you can change
`ace-jump-word-mode-use-query-char' to nil.

If you don't like the default move keys, you can change it by
setting `ace-jump-mode-move-keys'.

You can constrol whether use the case sensitive via
`ace-jump-mode-case-fold'.
"
  (interactive "p")
  (let ((index (/ prefix 4))
        (submode-list-length (length ace-jump-mode-submode-list)))
    (if (< index 0)
        (error "[AceJump] Invalid prefix command"))
    (if (>= index submode-list-length)
        (setq index (1- submode-list-length)))
    (call-interactively (nth index ace-jump-mode-submode-list))))

(defun ace-jump-move ()
  "move cursor based on user input"
  (interactive)
  (let* ((index (let ((ret (position (aref (this-command-keys) 0)
                                     ace-jump-mode-move-keys)))
                  (if ret ret (length ace-jump-mode-move-keys))))
         (node (nth index (cdr ace-jump-search-tree))))
    (cond
     ;; we do not find key in search tree. This can happen, for
     ;; example, when there is only three selections in screen
     ;; (totally five move-keys), but user press the forth move key
     ((null node)
      (message "No such position candidate.")
      (ace-jump-done))
     ;; this is a branch node, which means there need further
     ;; selection
     ((eq (car node) 'branch)
      (let ((old-tree ace-jump-search-tree))
        ;; we use sub tree in next move, create a new root node
        ;; whose child is the sub tree nodes
        (setq ace-jump-search-tree (cons 'branch (cdr node)))
        (ace-jump-update-overlay-in-search-tree ace-jump-search-tree
                                                ace-jump-mode-move-keys)

        ;; this is important, we need remove the subtree first before
        ;; do delete, we set the child nodes to nil
        (setf (cdr node) nil)
        (ace-jump-delete-overlay-in-search-tree old-tree)))
     ;; if the node is leaf node, this is the final one
     ((eq (car node) 'leaf)
      ;; need to save aj data, as `ace-jump-done' will clean it
      (let ((aj-data (overlay-get (cdr node) 'aj-data)))
        (ace-jump-done)
        (ace-jump-push-mark)
        (run-hooks 'ace-jump-mode-before-jump-hook)
        (ace-jump-jump-to aj-data))
      (run-hooks 'ace-jump-mode-end-hook))
     (t
      (ace-jump-done)
      (error "[AceJump] Internal error: tree node type is invalid")))))



(defun ace-jump-done()
  "stop AceJump motion"
  (interactive)
  ;; clear the status flag
  (setq ace-jump-query-char nil)
  (setq ace-jump-current-mode nil)

  ;; clean the status line
  (setq ace-jump-mode nil)
  (force-mode-line-update)

  ;; delete background overlay
  (loop for ol in ace-jump-background-overlay-list
        do (delete-overlay ol))
  (setq ace-jump-background-overlay-list nil)


  ;; delete overlays in search tree
  (ace-jump-delete-overlay-in-search-tree ace-jump-search-tree)
  (setq ace-jump-search-tree nil)

  (setq overriding-local-map nil)

  (remove-hook 'mouse-leave-buffer-hook 'ace-jump-done)
  (remove-hook 'kbd-macro-termination-hook 'ace-jump-done))

(defun ace-jump-kill-buffer(buffer)
  "Utility function to kill buffer for ace jump mode.
We also need to handle the buffer which has clients on it"
  (if (and (boundp 'server-buffer-clients)
           server-buffer-clients)
      (server-buffer-done buffer t))
  (kill-buffer buffer))

;;;; ============================================
;;;; advice to sync emacs mark ring
;;;; ============================================

(defun ace-jump-move-to-end-if ( l pred )
  "Move all the element in a list to the end of list if it make
the PRED to return non-nil.

PRED is a function object which can pass to funcall and accept
one argument, which will be every element in the list.
Such as : (lambda (x) (equal x 1)) "
  (let (true-list false-list)
    (loop for e in l
          do (if (funcall pred e)
                 (setq true-list (cons e true-list))
               (setq false-list (cons e false-list))))
    (nconc (nreverse false-list)
           (and true-list (nreverse true-list)))))

(defun ace-jump-move-first-to-end-if (l pred)
  "Only move the first found one to the end of list"
  (lexical-let ((pred pred)
                found)
    (ace-jump-move-to-end-if l
                             (lambda (x)
                               (if found
                                   nil
                                 (setq found (funcall pred x)))))))

  

(defadvice pop-mark (before ace-jump-pop-mark-advice)
  "When `pop-mark' is called to jump back, this advice will sync the mark ring.
Move the same position to the end of `ace-jump-mode-mark-ring'."
  (lexical-let ((mp (mark t))
                (cb (current-buffer)))
    (if mp
        (setq ace-jump-mode-mark-ring
              (ace-jump-move-first-to-end-if ace-jump-mode-mark-ring
                                             (lambda (x)
                                               (and (equal (aj-position-offset x) mp)
                                                    (eq (aj-position-buffer x) cb))))))))
            

(defadvice pop-global-mark (before ace-jump-pop-global-mark-advice)
  "When `pop-global-mark' is called to jump back, this advice will sync the mark ring.
Move the aj-position with the same buffer to the end of `ace-jump-mode-mark-ring'."
  (interactive)
  ;; find the one that will be jump to
  (let ((index global-mark-ring))
    ;; refer to the implementation of `pop-global-mark'
    (while (and index (not (marker-buffer (car index))))
      (setq index (cdr index)))
    (if index
        ;; find the mark
        (lexical-let ((mb (marker-buffer (car index))))
          (setq ace-jump-mode-mark-ring
                (ace-jump-move-to-end-if ace-jump-mode-mark-ring
                                         (lambda (x)
                                           (eq (aj-position-buffer x) mb))))))))
                                              

(defun ace-jump-mode-enable-mark-sync ()
  "Enable the sync funciton between ace jump mode mark ring and emacs mark ring.

1. This function will enable the advice which activate on
`pop-mark' and `pop-global-mark'. These advice will remove the
same marker from `ace-jump-mode-mark-ring' when user use
`pop-mark' or `global-pop-mark' to jump back. 

2. Set variable `ace-jump-sync-emacs-mark-ring' to t, which will
sync mark information with emacs mark ring. "
  (ad-enable-advice 'pop-mark 'before 'ace-jump-pop-mark-advice)
  (ad-activate 'pop-mark)
  (ad-enable-advice 'pop-global-mark 'before 'ace-jump-pop-global-mark-advice)
  (ad-activate 'pop-global-mark)
  (setq ace-jump-sync-emacs-mark-ring t))

(defun ace-jump-mode-disable-mark-sync ()
  "Disable the sync funciton between ace jump mode mark ring and emacs mark ring.

1. This function will diable the advice which activate on
`pop-mark' and `pop-global-mark'. These advice will remove the
same marker from `ace-jump-mode-mark-ring' when user use
`pop-mark' or `global-pop-mark' to jump back. 

2. Set variable `ace-jump-sync-emacs-mark-ring' to nil, which
will stop synchronizing mark information with emacs mark ring. "
  (ad-disable-advice 'pop-mark 'before 'ace-jump-pop-mark-advice)
  (ad-activate 'pop-mark)
  (ad-disable-advice 'pop-global-mark 'before 'ace-jump-pop-global-mark-advice)
  (ad-activate 'pop-global-mark)
  (setq ace-jump-sync-emacs-mark-ring nil))


(provide 'ace-jump-mode)

;;; ace-jump-mode.el ends here

;; Local Variables: 
;; byte-compile-warnings: (not cl-functions) 
;; End: 
