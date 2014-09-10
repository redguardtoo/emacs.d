;;; evil-surround.el --- emulate surround.vim from Vim

;; Copyright (C) 2010, 2011 Tim Harper
;;
;; Author: Tim Harper <timcharper at gmail dot com>
;;      Vegard Øye <vegard_oye at hotmail dot com>
;; Maintainer: Please send bug reports to the mailing list (below).
;; Created: July 23 2011
;; Version: 0.1
;; Keywords: emulation, vi, evil
;; Mailing list: <implementations-list at lists.ourproject.org>
;;      Subscribe: http://tinyurl.com/implementations-list
;;      Newsgroup: nntp://news.gmane.org/gmane.emacs.vim-emulation
;;      Archives: http://dir.gmane.org/gmane.emacs.vim-emulation
;;
;; This file is not part of GNU Emacs.

;;; Commentary:

;; This package emulates surround.vim by Tim Pope.
;; The functionality is wrapped into a minor mode. To enable
;; it globally, add the following lines to ~/.emacs:
;;
;;     (require 'evil-surround)
;;     (global-evil-surround-mode 1)
;;
;; Alternatively, you can enable evil-surround-mode along a major mode
;; by adding `turn-on-evil-surround-mode' to the mode hook.
;;
;; This package uses Evil as its vi layer. It is available from:
;;
;;     http://gitorious.org/evil

;;; Code:

(require 'evil)

(defgroup surround nil
  "surround.vim for Emacs"
  :prefix "surround-"
  :group 'evil)

(defcustom evil-surround-pairs-alist
  '((?\( . ("( " . " )"))
    (?\[ . ("[ " . " ]"))
    (?\{ . ("{ " . " }"))

    (?\) . ("(" . ")"))
    (?\] . ("[" . "]"))
    (?\} . ("{" . "}"))

    (?# . ("#{" . "}"))
    (?b . ("(" . ")"))
    (?B . ("{" . "}"))
    (?> . ("<" . ">"))
    (?t . evil-surround-read-tag)
    (?< . evil-surround-read-tag)
    (?f . evil-surround-function))
  "Association list of surround items.
Each item is of the form (TRIGGER . (LEFT . RIGHT)), all strings.
Alternatively, a function can be put in place of (LEFT . RIGHT).
This only affects inserting pairs, not deleting or changing them."
  :group 'surround
  :type '(repeat (cons (regexp :tag "Key")
                       (symbol :tag "Surround pair"))))
(make-variable-buffer-local 'evil-surround-pairs-alist)

(defcustom evil-surround-operator-alist
  '((evil-change . change)
    (evil-delete . delete))
  "Association list of operators to their fundamental operation.
Each item is of the form (OPERATOR . OPERATION)."
  :group 'surround
  :type '(repeat (cons (symbol :tag "Operator")
                       (symbol :tag "Operation"))))

(defvar evil-surround-read-tag-map
  (let ((map (copy-keymap minibuffer-local-map)))
    (define-key map ">" 'exit-minibuffer)
    map)
  "Keymap used by `evil-surround-read-tag'.")

(defun evil-surround-function ()
  "Read a functionname from the minibuffer and wrap selection in function call"
  (let ((fname (read-from-minibuffer "" "" )))
    (cons (format "%s(" (or fname ""))
          ")")))

(defun evil-surround-read-tag ()
  "Read a XML tag from the minibuffer."
  (let* ((input (read-from-minibuffer "<" "" evil-surround-read-tag-map))
         (match (string-match "\\([0-9a-z-]+\\)\\(.*?\\)[>]*$" input))
         (tag  (match-string 1 input))
         (rest (match-string 2 input)))
    (cons (format "<%s%s>" (or tag "") (or rest ""))
          (format "</%s>" (or tag "")))))

(defun evil-surround-pair (char)
  "Return the evil-surround pair of char.
This is a cons cell (LEFT . RIGHT), both strings."
  (let ((pair (assoc-default char evil-surround-pairs-alist)))
    (cond
     ((functionp pair)
      (funcall pair))

     ((consp pair)
      pair)

     (t
      (cons (format "%c" char) (format "%c" char))))))

(defun evil-surround-outer-overlay (char)
  "Return outer overlay for the delimited range represented by CHAR.
This overlay includes the delimiters.
See also `evil-surround-inner-overlay'."
  (let ((outer (lookup-key evil-outer-text-objects-map (string char))))
    (when (functionp outer)
      (setq outer (funcall outer))
      (when (evil-range-p outer)
        (evil-surround-trim-whitespace-from-range outer "[[:space:]]")
        (setq outer (make-overlay (evil-range-beginning outer)
                                  (evil-range-end outer)
                                  nil nil t))))))

(defun evil-surround-trim-whitespace-from-range (range &optional regexp)
  "Given an evil-range, trim whitespace around range by shrinking the range such that it neither begins nor ends with whitespace. Does not modify the buffer."
  (let ((regexp (or regexp "[ \f\t\n\r\v]")))
    (save-excursion
      (save-match-data
        (goto-char (evil-range-beginning range))
        (while (looking-at regexp) (forward-char))
        (evil-set-range-beginning range (point))
        (goto-char (evil-range-end range))
        (while (looking-back regexp) (backward-char))
        (evil-set-range-end range (point))))))

(defun evil-surround-inner-overlay (char)
  "Return inner overlay for the delimited range represented by CHAR.
This overlay excludes the delimiters.
See also `evil-surround-outer-overlay'."
  (let ((inner (lookup-key evil-inner-text-objects-map (string char))))
    (when (functionp inner)
      (setq inner (funcall inner))
      (when (evil-range-p inner)
        (when (eq (char-syntax char) ?\()
          (evil-surround-trim-whitespace-from-range inner "[[:space:]]"))
        (setq inner (make-overlay (evil-range-beginning inner)
                                  (evil-range-end inner)
                                  nil nil t))))))

(evil-define-motion evil-surround-line (count)
  "Move COUNT - 1 lines down but return exclusive character motion."
  :type exclusive
  (let ((beg (line-beginning-position)))
    (evil-line count)
    (end-of-line)
    (let ((range (evil-range beg (point) 'exclusive)))
      (evil-expand-range range)
      range)))

;;;###autoload
(defun evil-surround-delete (char &optional outer inner)
  "Delete the surrounding delimiters represented by CHAR.
Alternatively, the text to delete can be represented with
the overlays OUTER and INNER, where OUTER includes the delimiters
and INNER excludes them. The intersection (i.e., difference)
between these overlays is what is deleted."
  (interactive "c")
  (cond
   ((and outer inner)
    (delete-region (overlay-start outer) (overlay-start inner))
    (delete-region (overlay-end inner) (overlay-end outer))
    (goto-char (overlay-start outer)))
   (t
    ;; no overlays specified: create them on the basis of CHAR
    ;; and delete after use
    (let* ((outer (evil-surround-outer-overlay char))
           (inner (evil-surround-inner-overlay char)))
      (unwind-protect
          (when (and outer inner)
            (evil-surround-delete char outer inner))
        (when outer (delete-overlay outer))
        (when inner (delete-overlay inner)))))))

;;;###autoload
(defun evil-surround-change (char &optional outer inner)
  "Change the surrounding delimiters represented by CHAR.
Alternatively, the text to delete can be represented with the
overlays OUTER and INNER, which are passed to `evil-surround-delete'."
  (interactive "c")
  (cond
   ((and outer inner)
    (evil-surround-delete char outer inner)
    (evil-surround-region (overlay-start outer)
                     (overlay-end outer)
                     nil (read-char)))
   (t
    (let* ((outer (evil-surround-outer-overlay char))
           (inner (evil-surround-inner-overlay char)))
      (unwind-protect
          (when (and outer inner)
            (evil-surround-change char outer inner))
        (when outer (delete-overlay outer))
        (when inner (delete-overlay inner)))))))

;; Dispatcher function in Operator-Pending state.
;; "cs" calls `evil-surround-change', "ds" calls `evil-surround-delete',
;; and "ys" calls `evil-surround-region'.
(evil-define-command evil-surround-edit (operation)
  "Edit the surrounding delimiters represented by CHAR.
If OPERATION is `change', call `evil-surround-change'.
if OPERATION is `surround', call `evil-surround-region'.
Otherwise call `evil-surround-delete'."
  (interactive
   (progn
     ;; abort the calling operator
     (setq evil-inhibit-operator t)
     (list (assoc-default evil-this-operator
                          evil-surround-operator-alist))))
  (cond
   ((eq operation 'change)
    (call-interactively 'evil-surround-change))
   ((eq operation 'delete)
    (call-interactively 'evil-surround-delete))
   (t
    (define-key evil-operator-shortcut-map "s" 'evil-surround-line)
    (call-interactively 'evil-surround-region))))

(evil-define-operator evil-surround-region (beg end type char &optional force-new-line)
  "Surround BEG and END with CHAR.

When force-new-line is true, and region type is not line, the
following: (vertical bars indicate region start/end points)

   do |:thing|

Becomes this:

   do {
     :thing
   }"

  (interactive "<R>c")
  (let* ((overlay (make-overlay beg end nil nil t))
         (pair (evil-surround-pair char))
         (open (car pair))
         (close (cdr pair)))
    (unwind-protect
        (progn
          (goto-char (overlay-start overlay))

          (cond ((eq type 'line)
                 (insert open)
                 (indent-according-to-mode)
                 (newline-and-indent)
                 (goto-char (overlay-end overlay))
                 (insert close)
                 (indent-according-to-mode)
                 (newline))

                (force-new-line
                 (insert open)
                 (indent-according-to-mode)
                 (newline-and-indent)
                 (goto-char (overlay-end overlay))
                 (newline-and-indent)
                 (insert close))

                (t
                 (insert open)
                 (goto-char (overlay-end overlay))
                 (insert close)))
          (goto-char (overlay-start overlay)))
      (delete-overlay overlay))))

(evil-define-operator evil-Surround-region (beg end type char)
  "Call surround-region, toggling force-new-line"
  (interactive "<R>c")
  (evil-surround-region beg end type char t))

;;;###autoload
(define-minor-mode evil-surround-mode
  "Buffer-local minor mode to emulate surround.vim."
  :keymap (make-sparse-keymap)
  (evil-normalize-keymaps))

;;;###autoload
(defun turn-on-evil-surround-mode ()
  "Enable evil-surround-mode in the current buffer."
  (evil-surround-mode 1))

;;;###autoload
(defun turn-off-evil-surround-mode ()
  "Disable evil-surround-mode in the current buffer."
  (evil-surround-mode -1))

;;;###autoload
(define-globalized-minor-mode global-evil-surround-mode
  evil-surround-mode turn-on-evil-surround-mode
  "Global minor mode to emulate surround.vim.")

(evil-define-key 'operator evil-surround-mode-map "s" 'evil-surround-edit)
(evil-define-key 'visual evil-surround-mode-map "s" 'evil-surround-region)
(evil-define-key 'visual evil-surround-mode-map "S" 'evil-Surround-region)

(provide 'evil-surround)

;;; evil-surround.el ends here
