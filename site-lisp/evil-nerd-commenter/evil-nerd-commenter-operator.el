;;; evil-nerd-commenter-operator.el --- Provides an evil operator for evil-nerd-commenter

;; Copyright (C) 2013-2017, Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>

;; This file is not part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; Provides operators for evil-mode.

;;; Code:

(require 'evil nil 'noerror)
(require 'evil-nerd-commenter-sdk)

(defvar evilnc-c-style-comment-modes
  '(awk-mode
    c++-mode
    c-mode
    css-mode
    dart-mode
    ess-mode
    go-mode
    java-mode
    javascript-mode
    js-mode
    js2-mode
    perl-mode
    php-mode
    swift-mode
    web-mode))

(evil-define-operator evilnc-comment-operator (beg end type)
  "Comments text from BEG to END with TYPE."
  (interactive "<R>")
  (cond
   ((eq type 'block)
    (let* ((newpos (evilnc--extend-to-whole-comment beg end) ))
      (evil-apply-on-block #'evilnc--comment-or-uncomment-region
                           (nth 0 newpos)
                           (nth 1 newpos)
                           nil)))
   ((and (eq type 'line)
         (= end (point-max))
         (or (= beg end)
             (/= (char-before end) ?\n))
         (/= beg (point-min))
         (=  (char-before beg) ?\n))
    (evilnc--comment-or-uncomment-region (1- beg) end))

   ((eq type 'line)
    (evilnc--comment-or-uncomment-region beg (1- end)))

   (t
    (let* ((newpos (evilnc--extend-to-whole-comment beg end) ))
      (evilnc--comment-or-uncomment-region (nth 0 newpos) (nth 1 newpos)))))

  ;; place cursor on beginning of line
  (if (and (called-interactively-p 'any)
           (eq type 'line))
    (evil-first-non-blank)))

(evil-define-operator evilnc-copy-and-comment-operator (beg end)
  "Inserts an out commented copy of the text from BEG to END."
  :move-point (not evilnc-original-above-comment-when-copy-and-comment)
  (interactive "<r>")
    (evil-yank-lines beg end nil 'lines)
    (cond
     (evilnc-original-above-comment-when-copy-and-comment
      (let* ((p (point)))
        (comment-region beg end)
        (goto-char beg)
        (evil-paste-before 1)
        (goto-char p)))
     (t
      (goto-char end)
      (evil-paste-before 1)
      ;; actual comment operatio should happen at last
      ;; or else beg end will be screwed up
      (comment-region beg end))))

(defun evilnc-is-one-line-comment (b e)
  "one line comment, just select the comment."
  (save-excursion
    (goto-char b)
    (and (<= (line-beginning-position) b)
         (<= e (line-end-position)))))

(defun evilnc-get-comment-bounds ()
  (let* ((b (point))
         (e (point))
         rlt)
    ;; extend begin
    (while (evilnc-is-comment (- b 1))
      (setq b (- b 1)))

    ;; extend end
    (while (evilnc-is-comment (+ e 1))
      (setq e (+ e 1)))

    ;; we could select extra spaces at the end of comment
    ;; so we need go back
    (let* ((str (save-excursion
                  (goto-char e)
                  (buffer-substring-no-properties (line-beginning-position) e)))
           (empty-line-p (string-match "^[ \t]*$" str)))
      (if empty-line-p
          ;; empty line plus line feed
          (setq e (- e (length str) 1))))
    (cond
     ((>= b e)
      (setq rlt nil))
     ((evilnc-is-one-line-comment b e)
      ;; contract begin
      (while (not (evilnc-is-pure-comment b))
        (setq b (+ b 1)))

      ;; contract end
      (while (not (evilnc-is-pure-comment e))
        (setq e (- e 1)))

      (if (< b e) (setq rlt (cons b (+ e 1)))))
     (t
      ;; multi-line comment
      (setq rlt (cons b e))))
    rlt))

(defun evilnc-ajusted-comment-end (b e)
  (let* ((next-end-char (evilnc-get-char (- e 2)))
         (end-char (evilnc-get-char (- e 1))))
    ;; avoid selecting CR/LF at the end of comment
    (while (and (< b e)
                (memq (evilnc-get-char (- e 1)) '(10 13)))
      (setq e (- e 1)))

    ;; avoid selecting comment limiter
    (cond
     ((and (memq major-mode evilnc-c-style-comment-modes)
           (= end-char 47) ; "/" => 47
           (= next-end-char 42)) ; "*" => 42
      ;; avoid selecting the ending comment limiter "*/"
      (setq e (- e 2))
      (while (and (> e b)
                  (= (evilnc-get-char (- e 1)) 42))
        (setq e (- e 1))))
     (t
      ;; other languages we can safely use font face
      (while (and (> e b)
                  (evilnc-is-comment-delimiter (- e 1)))
        (setq e (- e 1)))))
    e))

(evil-define-text-object evilnc-inner-comment (&optional count begin end type)
  "An inner comment text object."
  (let* ((bounds (evilnc-get-comment-bounds)))
    (cond
     (bounds
      (let* ((b (save-excursion
                  (goto-char (car bounds))
                  (forward-word 1)
                  (forward-word -1)
                  (point)))
             (e (save-excursion
                  (goto-char (cdr bounds))
                  (goto-char (evilnc-ajusted-comment-end b (line-end-position)))
                  (point))))
        (when (evilnc-is-one-line-comment b e)
          (while (and (< b e)
                      (or (evilnc-is-comment-delimiter e)
                          (and (evilnc-is-pure-comment e)
                               (evilnc-is-whitespace e))))
            (setq e (- e 1)))
          (setq e (+ e 1)))

        (if (< b e) (evil-range b e 'block :expanded t))))
     (t
      (error "Not inside a comment.")))))

(evil-define-text-object evilnc-outer-commenter (&optional count begin end type)
  "An outer comment text object."
  (let* ((bounds (evilnc-get-comment-bounds)))
    (cond
     (bounds
      (let* ((b (car bounds))
             (e (cdr bounds)))
        (evil-range b e 'exclusive :expanded t)))
     (t
      (error "Not inside a comment.")))))

(provide 'evil-nerd-commenter-operator)
;;; evil-nerd-commenter-operator.el ends here

;; Local Variables:
;; byte-compile-warnings: (not free-vars unresolved)
;; End:
