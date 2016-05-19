;;; evil-matchit.el --- Vim matchit ported to Evil

;; Copyright (C) 2014,2015 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/evil-matchit
;; Version: 2.1.2
;; Keywords: matchit vim evil
;; Package-Requires: ((evil "1.0.7"))
;;
;; This file is not part of GNU Emacs.

;;; License:

;; This file is part of evil-matchit
;;
;; evil-matchit is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; evil-matchit is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This program emulates matchit.vim by Benji Fisher.
;; It allows you use % to match items.
;; See https://github.com/redguardtoo/evil-matchit/ for help
;;
;; This program requires EVIL (http://gitorious.org/evil)
;;

;;; Code:

(require 'evil)

(defvar evilmi-plugins '(emacs-lisp-mode
                         ((evilmi-simple-get-tag evilmi-simple-jump)))
  "The table to define which algorithm to use and when to jump items")

(defvar evilmi-may-jump-by-percentage t
  "Simulate evil-jump-item behaviour. For example, press 50% to jump to 50 percentage in buffer.
If this flag is nil, then 50 means jump 50 times.")


(defvar evilmi-ignore-comments t "Ignore comments when mathing")

(defvar evilmi-forward-chars (string-to-list "[{("))
(defvar evilmi-backward-chars (string-to-list "]})"))
(defvar evilmi-quote-chars (string-to-list "'\"/"))
(defvar evilmi-debug nil)

(defun evilmi--char-is-simple (ch)
  (let (rlt)
    (setq rlt
          (or (memq ch evilmi-forward-chars)
              (memq ch evilmi-backward-chars)
              ;; sorry we could not jump between ends of string in python-mode
              (memq ch evilmi-quote-chars)))

    (when (and (memq major-mode '(python-mode))
               ;; in evil-visual-state, (point) could equal to (line-end-position)
               (>= (point) (1- (line-end-position))))
      ;; handle follow python code,
      ;;
      ;; if true:
      ;;     a = "hello world"
      ;;
      ;; If current cursor is at end of line , rlt should be nil!
      ;; or else, matching algorithm can't work in above python sample
      (setq rlt nil))
    rlt))

(defun evilmi--get-char-at-position (pos)
  (let (ch)
    ;; evil load
    (setq ch (char-after pos))
    (if evilmi-debug (message "evilmi--get-char-at-position called. Return: %s" (string ch)))
    ch))

(defun evilmi--get-char-under-cursor ()
  "Return: (character position)"
  (let (ch p)
    (setq ch (following-char))
    (setq p (point))
    (if evilmi-debug (message "evilmi--get-char-under-cursor called. Return: (%d %s)" ch p))
    (list ch p)))

(defun evilmi--is-jump-forward ()
  "Return: (forward-direction font-face-under-cursor character-under-cursor)
If font-face-under-cursor is NOT nil, the quoted string is being processed"
  (let (tmp
        p
        ff
        ch
        rlt)
    (setq tmp (evilmi--get-char-under-cursor))
    (setq ch (car tmp))
    (setq p (cadr tmp))
    (cond
     ((memq ch evilmi-forward-chars)
      (setq rlt t))
     ((memq ch evilmi-backward-chars)
      (setq rlt nil))
     ((memq ch evilmi-quote-chars)
      (setq ff (get-text-property p 'face))
      (setq rlt (eq ff (get-text-property (+ 1 p) 'face))))
     (t (setq rlt t)))

    (if evilmi-debug (message "evilmi--is-jump-forward called. Return: (%s %s %s)"
                              rlt ff (string ch)))

    (list rlt ff ch)))

(defun evilmi--scan-sexps (is-forward)
  (let (rlt
        start-pos
        (arg (if is-forward 1 -1)))
    ;; normal state and other state
    (setq start-pos (if is-forward (point) (+ 1 (point))))
    (setq rlt (scan-sexps start-pos arg))
    (if evilmi-debug (message "evilmi--scan-sexps called. Return: %s" rlt))
    rlt))

(defun evilmi--adjust-quote-jumpto (is-forward pos)
  (let (rlt)
    (setq rlt (if is-forward pos (+ 1 pos)))
    (if evilmi-debug (message "evilmi--adjust-quote-jumpto called. Return: %s" rlt))
    rlt))

(defun evilmi--above-the-other-quote-char (ch pos ff delta)
  (and (= ch (evilmi--get-char-at-position (- pos delta)))
       (not (eq ff (get-text-property pos 'face)))))

(defun evilmi--find-the-other-quote-char (ff is-forward ch)
"The end character under cursor has different font-face from ff"
  (let (rlt
        pos
        (got nil)
        (delta (if is-forward 1 -1))
        (end (if is-forward (point-max) (point-min))))
    (setq pos (+ delta (point)))
    (while (not got)
      (if (or (= pos end)
              (evilmi--above-the-other-quote-char ch pos ff delta))
          (progn
            (setq rlt (evilmi--adjust-quote-jumpto is-forward pos))
            (setq got t))
        (setq pos (+ delta pos))))
    (if evilmi-debug (message "evilmi--find-the-other-quote-char called Return: %s" rlt))
    rlt))

(defun evilmi--adjust-jumpto (is-forward rlt)
  ;; normal-state hack!
  (unless (eq evil-state 'visual)
    (if is-forward (setq rlt (- rlt 1))))
  (if evilmi-debug (message "evilmi--adjust-jumpto called. Return: %s" rlt))
  rlt)

;; @see http://emacs.stackexchange.com/questions/13222/a-elisp-function-to-jump-between-matched-pair
(defun evilmi--find-position-to-jump (ff is-forward ch)
  "Non-nil ff means jumping between quotes"
  (let (rlt)
    (if ff (setq rlt (evilmi--find-the-other-quote-char ff is-forward ch))
      (setq rlt (evilmi--scan-sexps is-forward)))
    (setq rlt (evilmi--adjust-jumpto is-forward rlt))
    (if evilmi-debug (message "evilmi--find-position-to-jump called. Return: %s" rlt))
    rlt))

(defun evilmi--tweak-selected-region-finally (ff jump-forward)
  ;; visual-state hack!
  (if (and jump-forward (eq evil-state 'visual) (not ff))
      ;; if ff is non-nil, I control the jump flow from character level,
      ;; so hack to workaround scan-sexps is NOT necessary
        (evil-backward-char)))

(defun evilmi--simple-jump ()
  "Alternative for evil-jump-item"
  ;; parse-sexp-ignore-comments is used
  (interactive)
  (let ((old-flag parse-sexp-ignore-comments)
        tmp
        ch
        jumpto
        ff
        jump-forward)
    (setq tmp (evilmi--is-jump-forward))
    (setq jump-forward (car tmp))
    ;; if ff is not nil, it's jump between quotes
    ;; so we should not use (scan-sexps)
    (setq ff (nth 1 tmp))
    (setq ch (nth 2 tmp))

    (unless evilmi-ignore-comments
      (setq parse-sexp-ignore-comments nil))

    ;; need pass the char
    (setq jumpto (evilmi--find-position-to-jump ff jump-forward ch))
    (goto-char jumpto)
    (evilmi--tweak-selected-region-finally ff jump-forward)

    (unless evilmi-ignore-comments
      (setq parse-sexp-ignore-comments old-flag))
    ))

(defun evilmi--operate-on-item (NUM &optional FUNC)
  (let ((plugin (plist-get evilmi-plugins major-mode))
        rlt
        jumped
        where-to-jump-in-theory)

    (if (not NUM) (setq NUM 1))

    (if plugin
        (mapc
         (lambda (elem)
           (setq rlt (funcall (nth 0 elem)))
           (when (and rlt (not jumped))
             ;; before jump, we may need some operation
             (if FUNC (funcall FUNC rlt))
             ;; jump now
             (setq where-to-jump-in-theory (funcall (nth 1 elem) rlt NUM))
             ;; jump only once if the jump is successful
             (setq jumped t)
             ))
         plugin))

    (when (not jumped)
      (if FUNC (funcall FUNC (list (point))))
      (evilmi--simple-jump)
      (setq where-to-jump-in-theory (point)))

    (if evilmi-debug (message "evilmi--operate-on-item called. Return: %s" where-to-jump-in-theory))
    where-to-jump-in-theory))

(defun evilmi--push-mark (rlt)
    (push-mark (nth 0 rlt) t t))

(defun evilmi-init-plugins ()
  (interactive)

  ;; simple matching for languages containing "{(["
  (autoload 'evilmi-simple-get-tag "evil-matchit-simple" nil)
  (autoload 'evilmi-simple-jump "evil-matchit-simple" nil)
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-simple-get-tag evilmi-simple-jump))))
        '(java-mode perl-mode cperl-mode go-mode))

  ;; Javascript
  (autoload 'evilmi-javascript-get-tag "evil-matchit-javascript" nil)
  (autoload 'evilmi-javascript-jump "evil-matchit-javascript" nil)
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-simple-get-tag evilmi-simple-jump)
                                           (evilmi-javascript-get-tag evilmi-javascript-jump))))
        '(js-mode json-mode js2-mode js3-mode javascript-mode))

  ;; Html
  (autoload 'evilmi-template-get-tag "evil-matchit-template" nil)
  (autoload 'evilmi-template-jump "evil-matchit-template" nil)
  (autoload 'evilmi-html-get-tag "evil-matchit-html" nil)
  (autoload 'evilmi-html-jump "evil-matchit-html" nil)
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-template-get-tag evilmi-template-jump)
                                           (evilmi-simple-get-tag evilmi-simple-jump)
                                           (evilmi-html-get-tag evilmi-html-jump)))
          )
        '(web-mode html-mode nxml-mode nxhtml-mode sgml-mode message-mode))

  ;; Emacs Org-mode
  (autoload 'evilmi-org-get-tag "evil-matchit-org" nil)
  (autoload 'evilmi-org-jump "evil-matchit-org" nil t)
  (plist-put evilmi-plugins 'org-mode '((evilmi-org-get-tag evilmi-org-jump)))

  ;; Latex
  (autoload 'evilmi-latex-get-tag "evil-matchit-latex" nil)
  (autoload 'evilmi-latex-jump "evil-matchit-latex" nil t)
  (plist-put evilmi-plugins 'latex-mode '((evilmi-latex-get-tag evilmi-latex-jump)))

  ;; Python
  (autoload 'evilmi-python-get-tag "evil-matchit-python" nil)
  (autoload 'evilmi-python-jump "evil-matchit-python" nil)
  (plist-put evilmi-plugins 'python-mode '((evilmi-simple-get-tag evilmi-simple-jump)
                                           (evilmi-python-get-tag evilmi-python-jump)))

  ;; SQL
  (autoload 'evilmi-sql-get-tag "evil-matchit-sql" nil)
  (autoload 'evilmi-sql-jump "evil-matchit-sql" nil)
  (plist-put evilmi-plugins 'sql-mode '((evilmi-simple-get-tag evilmi-simple-jump)
                                           (evilmi-sql-get-tag evilmi-sql-jump)))

  ;; C/C++
  (autoload 'evilmi-c-get-tag "evil-matchit-c" nil)
  (autoload 'evilmi-c-jump "evil-matchit-c" nil)
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-c-get-tag evilmi-c-jump)
                                           (evilmi-simple-get-tag evilmi-simple-jump)))
          )
        '(c-mode c++-mode))

  ;; Fortran
  (autoload 'evilmi-fortran-get-tag "evil-matchit-fortran" nil)
  (autoload 'evilmi-fortran-jump "evil-matchit-fortran" nil)
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-fortran-get-tag evilmi-fortran-jump))))
        '(f90-mode fortran-mode))

  ;; CMake (http://www.cmake.org)
  (autoload 'evilmi-cmake-get-tag "evil-matchit-cmake" nil)
  (autoload 'evilmi-cmake-jump "evil-matchit-cmake" nil)
  (plist-put evilmi-plugins 'cmake-mode '((evilmi-cmake-get-tag evilmi-cmake-jump)))

  ;; sh-mode
  (autoload 'evilmi-sh-get-tag "evil-matchit-sh" nil)
  (autoload 'evilmi-sh-jump "evil-matchit-sh" nil)
  (plist-put evilmi-plugins 'sh-mode '((evilmi-sh-get-tag evilmi-sh-jump)))

  ;; Lua or any fine script languages
  (autoload 'evilmi-script-get-tag "evil-matchit-script" nil)
  (autoload 'evilmi-script-jump "evil-matchit-script" nil)
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-simple-get-tag evilmi-simple-jump)
                                           (evilmi-script-get-tag evilmi-script-jump))))
        '(lua-mode vimrc-mode))

  ;; Ruby
  (autoload 'evilmi-ruby-get-tag "evil-matchit-ruby" nil)
  (autoload 'evilmi-ruby-jump "evil-matchit-ruby" nil)
  ;; @see https://github.com/syl20bnr/spacemacs/issues/2093
  ;; spacemacs use enh-ruby-mode
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-simple-get-tag evilmi-simple-jump)
                                           (evilmi-ruby-get-tag evilmi-ruby-jump))))
        '(ruby-mode enh-ruby-mode))
  )

(defun evilmi--region-to-select-or-delete (NUM &optional is-inner)
  (let (where-to-jump-in-theory b e)
    (save-excursion
      (setq where-to-jump-in-theory (evilmi--operate-on-item NUM 'evilmi--push-mark))
      (if where-to-jump-in-theory (goto-char where-to-jump-in-theory))
      (setq b (region-beginning))
      (setq e (region-end))
      (goto-char b)

      ;; for inner text object, forward a line at the beginning
      (cond
       (is-inner
        (forward-line 1)
        (setq b (line-beginning-position)))
       (t
        (if (string-match "[ \t]*" (buffer-substring-no-properties (line-beginning-position) b))
            (setq b (line-beginning-position))
          ;; 1+ because the line feed
          )))

      ;; for inner text object, backward a line at the end
      ;; but in python-mode, last line is also code line
      (when (and is-inner (not (eq major-mode 'python-mode)))
        (goto-char e)
        (forward-line -1)
        (setq e (line-end-position)))
      )
    (if evilmi-debug (message "evilmi--region-to-select-or-delete called. Return: %s" (list b e)))
    (list b e)))

(evil-define-text-object evilmi-inner-text-object (&optional NUM begin end type)
  "Inner text object describing the region selected when you press % from evil-matchit"
  :type line
  (let (selected-region)
    (setq selected-region (evilmi--region-to-select-or-delete NUM t))
    (evil-range (car selected-region) (cadr selected-region) 'line)))

(evil-define-text-object evilmi-outer-text-object (&optional NUM begin end type)
  "Outer text object describing the region selected when you press % from evil-matchit"
  :type line
  (let (selected-region)
    (setq selected-region (evilmi--region-to-select-or-delete NUM))
    (evil-range (car selected-region) (cadr selected-region) 'line)))

(define-key evil-inner-text-objects-map "%" 'evilmi-inner-text-object)
(define-key evil-outer-text-objects-map "%" 'evilmi-outer-text-object)

;;;###autoload
(defun evilmi-select-items (&optional NUM)
  "Select items/tags and the region between them"
  (interactive "p")
  (let (selected-region)
    (setq selected-region (evilmi--region-to-select-or-delete NUM))
    (when selected-region
      (evilmi--push-mark selected-region)
      (goto-char (cadr selected-region)))
    ))

;;;###autoload
(defun evilmi-delete-items (&optional NUM)
  "Delete items/tags and the region between them"
  (interactive "p")
  (let (selected-region)
    (setq selected-region (evilmi--region-to-select-or-delete NUM))
    ;; 1+ because the line feed
    (kill-region (car selected-region) (1+ (cadr selected-region)))
    ))

;;;###autoload
(defun evilmi-jump-to-percentage (NUM)
  "Re-implementation of evil's similar functionality"
  (interactive "P")
  (let (dst)
    (when (and NUM (> NUM 0))
      (setq dst (let ((size (- (point-max) (point-min))))
                  (+ (point-min)
                     (if (> size 80000)
                         (* NUM (/ size 100))
                       (/ (* NUM size) 100)))))
      (cond
       ((< dst (point-min))
        (setq dst (point-min)))
       ((> dst (point-max))
        (setq dst (point-max))))
      (goto-char dst)
      (back-to-indentation))))

;;;###autoload
(defun evilmi-jump-items (&optional NUM)
  "Jump between item/tag(s)"
  (interactive "P")
  (cond
   ((and evilmi-may-jump-by-percentage NUM)
    (evilmi-jump-to-percentage NUM))
   (t (evilmi--operate-on-item NUM))
   ))

;;;###autoload
(defun evilmi-version() (interactive) (message "2.1.2"))

;;;###autoload
(define-minor-mode evil-matchit-mode
  "Buffer-local minor mode to emulate matchit.vim"
  :keymap (make-sparse-keymap)
  ;; get correct value of `(point)` in visual-line mode
  ;; @see https://bitbucket.org/lyro/evil/issues/540/get-the-char-under-cusor-in-visual-line
  (evil-set-command-property 'evilmi-jump-items :keep-visual t)
  (if (fboundp 'evilmi-customize-keybinding)
      ;; use user's own key bindings
      (evilmi-customize-keybinding)
    ;; else use default key bindgs
    (evil-define-key 'normal evil-matchit-mode-map "%" 'evilmi-jump-items)
    (evil-define-key 'visual evil-matchit-mode-map "%" 'evilmi-jump-items))

  (evil-normalize-keymaps)
  (evilmi-init-plugins))

;;;###autoload
(defun turn-on-evil-matchit-mode ()
  "Enable evil-matchit-mode in the current buffer."
  (evil-matchit-mode 1))

;;;###autoload
(defun turn-off-evil-matchit-mode ()
  "Disable evil-matchit-mode in the current buffer."
  (evil-matchit-mode -1))

;;;###autoload
(define-globalized-minor-mode global-evil-matchit-mode
  evil-matchit-mode turn-on-evil-matchit-mode
  "Global minor mode to emulate matchit.vim")

(provide 'evil-matchit)

;;; evil-matchit.el ends here
