;;; counsel.el --- Various completion functions using Ivy -*- lexical-binding: t -*-

;; Copyright (C) 2015  Free Software Foundation, Inc.

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/swiper
;; Version: 0.1.0
;; Package-Requires: ((emacs "24.1") (swiper "0.3.0"))
;; Keywords: completion, matching

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
;; Just call one of the interactive functions in this file to complete
;; the corresponding thing using `ivy'.
;;
;; Currently available: Elisp symbols, Clojure symbols, Git files.

;;; Code:

(require 'ivy)

(defun counsel-el ()
  "Elisp completion at point."
  (interactive)
  (counsel--generic
   (lambda (str) (all-completions str obarray))))

(defvar counsel-describe-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-.") 'counsel-find-symbol)
    map))

(defun counsel-find-symbol ()
  "Jump to the definition of the current symbol."
  (interactive)
  (setq ivy--action 'counsel--find-symbol)
  (setq ivy-exit 'done)
  (exit-minibuffer))

(defun counsel--find-symbol ()
  (let ((sym (read ivy--current)))
    (cond ((boundp sym)
           (find-variable sym))
          ((fboundp sym)
           (find-function sym))
          ((or (featurep sym)
               (locate-library
                (prin1-to-string sym)))
           (find-library (prin1-to-string sym)))
          (t
           (error "Couldn't fild definition of %s"
                  sym)))))

(defun counsel-describe-variable (variable &optional buffer frame)
  "Forward to (`describe-variable' VARIABLE BUFFER FRAME)."
  (interactive
   (let ((v (variable-at-point))
         (enable-recursive-minibuffers t)
         (preselect (thing-at-point 'symbol))
         val)
     (setq val (ivy-read
                (if (symbolp v)
                    (format
                     "Describe variable (default %s): " v)
                  "Describe variable: ")
                (let (cands)
                  (mapatoms
                   (lambda (vv)
                     (when (or (get vv 'variable-documentation)
                               (and (boundp vv) (not (keywordp vv))))
                       (push (symbol-name vv) cands))))
                  cands)
                nil nil counsel-describe-map preselect))
     (list (if (equal val "")
               v
             (intern val)))))
  (describe-variable variable buffer frame))

(defun counsel-describe-function (function)
  "Forward to (`describe-function' FUNCTION) with ivy completion."
  (interactive
   (let ((fn (function-called-at-point))
         (enable-recursive-minibuffers t)
         (preselect (thing-at-point 'symbol))
         val)
     (setq val (ivy-read (if fn
                             (format "Describe function (default %s): " fn)
                           "Describe function: ")
                         (let (cands)
                           (mapatoms
                            (lambda (x)
                              (when (fboundp x)
                                (push (symbol-name x) cands))))
                           cands)
                         nil nil counsel-describe-map preselect))
     (list (if (equal val "")
               fn (intern val)))))
  (describe-function function))

(defvar info-lookup-mode)
(declare-function info-lookup->completions "info-look")
(declare-function info-lookup->mode-value "info-look")
(declare-function info-lookup-select-mode "info-look")
(declare-function info-lookup-change-mode "info-look")
(declare-function info-lookup "info-look")

(defun counsel-info-lookup-symbol (symbol &optional mode)
  "Forward to (`info-describe-symbol' SYMBOL MODE) with ivy completion."
  (interactive
   (progn
     (require 'info-look)
     (let* ((topic 'symbol)
            (mode (cond (current-prefix-arg
                         (info-lookup-change-mode topic))
                        ((info-lookup->mode-value
                          topic (info-lookup-select-mode))
                         info-lookup-mode)
                        ((info-lookup-change-mode topic))))
            (completions (info-lookup->completions topic mode))
            (enable-recursive-minibuffers t)
            (value (ivy-read
                    "Describe symbol: "
                    (mapcar #'car completions))))
       (list value info-lookup-mode))))
  (info-lookup 'symbol symbol mode))

(defun counsel-unicode-char ()
  "Insert a Unicode character at point."
  (interactive)
  (let* ((minibuffer-allow-text-properties t)
         (char (ivy-read "Unicode name: "
                         (mapcar (lambda (x)
                                   (propertize
                                    (format "% -60s%c" (car x) (cdr x))
                                    'result (cdr x)))
                                 (ucs-names)))))
    (insert-char (get-text-property 0 'result char))))

(declare-function cider-sync-request:complete "ext:cider-client")
(defun counsel-clj ()
  "Clojure completion at point."
  (interactive)
  (counsel--generic
   (lambda (str)
     (mapcar
      #'cl-caddr
      (cider-sync-request:complete str ":same")))))

(defun counsel-git ()
  "Find file in the current Git repository."
  (interactive)
  (let* ((default-directory (locate-dominating-file
                             default-directory ".git"))
         (cands (split-string
                 (shell-command-to-string
                  "git ls-files --full-name --")
                 "\n"
                 t))
         (file (ivy-read "Find file: " cands)))
    (when file
      (find-file file))))

(defun counsel-git-grep-function (string &optional _pred &rest _unused)
  "Grep in the current git repository for STRING."
  (split-string
   (shell-command-to-string
    (format "git --no-pager grep --full-name -n --no-color -i -e \"%s\"" string))
   "\n"
   t))

(defun counsel-git-grep ()
  "Grep for a string in the current git repository."
  (interactive)
  (let ((default-directory (locate-dominating-file
                             default-directory ".git"))
        (val (ivy-read "pattern: " 'counsel-git-grep-function))
        lst)
    (when val
      (setq lst (split-string val ":"))
      (find-file (car lst))
      (goto-char (point-min))
      (forward-line (1- (string-to-number (cadr lst)))))))

(defun counsel--generic (completion-fn)
  "Complete thing at point with COMPLETION-FN."
  (let* ((bnd (bounds-of-thing-at-point 'symbol))
         (str (if bnd
                  (buffer-substring-no-properties
                   (car bnd) (cdr bnd))
                ""))
         (candidates (funcall completion-fn str))
         (ivy-height 7)
         (res (ivy-read (format "pattern (%s): " str)
                        candidates)))
    (when (stringp res)
      (when bnd
        (delete-region (car bnd) (cdr bnd)))
      (insert res))))

(provide 'counsel)

;;; counsel.el ends here
