;;; evil-matchit.el --- Vim matchit ported to Evil

;; Copyright (C) 2014 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/evil-matchit
;; Version: 1.4.2
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
;;
;; This program requires EVIL (http://gitorious.org/evil)
;;

;;; Code:

(require 'evil)

(defvar evilmi-plugins '(emacs-lisp-mode
                         ((evilmi-simple-get-tag evilmi-simple-jump)))
  "The table to define which algorithm to use and when to to jump items")

(defvar evilmi-may-jump-by-percentage t
  "Simulate evil-jump-item behaviour. For example, press 50% to jump to 50 percentage in buffer.
If this flag is nil, then 50 means jump 50 times.")

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
         plugin
         ))

    (when (not jumped)
      (if FUNC (funcall FUNC (list (point))))
      (evil-jump-item)
      (setq where-to-jump-in-theory (point))
      )
    where-to-jump-in-theory
    ))

(defun evilmi--push-mark (rlt)
    (push-mark (nth 0 rlt) t t)
  )

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
          (plist-put evilmi-plugins mode '((evilmi-javascript-get-tag evilmi-javascript-jump))))
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

  ;; C/C++
  (autoload 'evilmi-c-get-tag "evil-matchit-c" nil)
  (autoload 'evilmi-c-jump "evil-matchit-c" nil)
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-c-get-tag evilmi-c-jump)
                                           (evilmi-simple-get-tag evilmi-simple-jump)))
          )
        '(c-mode c++-mode))

  ;; CMake (http://www.cmake.org)
  (autoload 'evilmi-cmake-get-tag "evil-matchit-cmake" nil)
  (autoload 'evilmi-cmake-jump "evil-matchit-cmake" nil)
  (plist-put evilmi-plugins 'cmake-mode '((evilmi-cmake-get-tag evilmi-cmake-jump)))

  ;; sh-mode
  (autoload 'evilmi-sh-get-tag "evil-matchit-sh" nil)
  (autoload 'evilmi-sh-jump "evil-matchit-sh" nil)
  (plist-put evilmi-plugins 'sh-mode '((evilmi-sh-get-tag evilmi-sh-jump)))

  ;; Lua/Ruby ... any normal script languages
  (autoload 'evilmi-script-get-tag "evil-matchit-script" nil)
  (autoload 'evilmi-script-jump "evil-matchit-script" nil)
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-simple-get-tag evilmi-simple-jump)
                                           (evilmi-script-get-tag evilmi-script-jump))))
        '(lua-mode vimrc-mode))

  (autoload 'evilmi-ruby-get-tag "evil-matchit-ruby" nil)
  (autoload 'evilmi-ruby-jump "evil-matchit-ruby" nil)
  (mapc (lambda (mode)
          (plist-put evilmi-plugins mode '((evilmi-simple-get-tag evilmi-simple-jump)
                                           (evilmi-ruby-get-tag evilmi-ruby-jump))))
        '(ruby-mode))
  )

(defun evilmi--region-to-select-or-delete (NUM)
  (let (where-to-jump-in-theory b e)
    (save-excursion
      (setq where-to-jump-in-theory (evilmi--operate-on-item NUM 'evilmi--push-mark))
      (if where-to-jump-in-theory (goto-char where-to-jump-in-theory))
      (setq b (region-beginning))
      (setq e (region-end))
      (goto-char b)
      (when (string-match "[ \t]*" (buffer-substring-no-properties (line-beginning-position) b))
        (setq b (line-beginning-position))
        ;; 1+ because the line feed
        ))
    (list b e)))

(evil-define-text-object evilmi-text-object (&optional NUM begin end type)
  "text object describing the region selected when you press % from evil-matchit"
  :type line
  (let (selected-region)
    (setq selected-region (evilmi--region-to-select-or-delete NUM))
    (evil-range (car selected-region) (cadr selected-region) 'line)))

(define-key evil-inner-text-objects-map "%" 'evilmi-text-object)
(define-key evil-outer-text-objects-map "%" 'evilmi-text-object)

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
  "jump between item/tag(s)"
  (interactive "P")
  (cond
   ((and evilmi-may-jump-by-percentage NUM)
    (evilmi-jump-to-percentage NUM))
   (t (evilmi--operate-on-item NUM))
   ))

;;;###autoload
(defun evilmi-version() (interactive) (message "1.4.2"))

;;;###autoload
(define-minor-mode evil-matchit-mode
  "Buffer-local minor mode to emulate matchit.vim"
  :keymap (make-sparse-keymap)
  (if (fboundp 'evilmi-customize-keybinding)
      (evilmi-customize-keybinding)
    (evil-define-key 'normal evil-matchit-mode-map
      "%" 'evilmi-jump-items)
    )
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
