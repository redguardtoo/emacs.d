;;; haskell-indentation.el -- indentation module for Haskell Mode

;; Copyright (C) 2009  Kristof Bastiaensen

;; Author: Kristof Bastiaensen <kristof.bastiaensen@vleeuwen.org>

;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Installation:
;;
;; To turn indentation on for all Haskell buffers under Haskell mode
;; <http://www.haskell.org/haskell-mode/> add this to .emacs:
;;
;;    (add-hook haskell-mode-hook 'turn-on-haskell-indentation)
;;
;; Otherwise, call `haskell-indentation-mode'.

;;; Code:

(require 'syntax)
(require 'cl-lib)

(defvar delete-active-region)

;; Dynamically scoped variables.
(defvar following-token)
(defvar current-token)
(defvar left-indent)
(defvar starter-indent)
(defvar current-indent)
(defvar layout-indent)
(defvar parse-line-number)
(defvar possible-indentations)
(defvar indentation-point)
(defvar haskell-literate)

(defgroup haskell-indentation nil
  "Haskell indentation."
  :link '(custom-manual "(haskell-mode)Indentation")
  :group 'haskell
  :prefix "haskell-indentation-")

(defcustom haskell-indentation-cycle-warn t
  "Warn before moving to the leftmost indentation, if you tab at the rightmost one."
  :type 'boolean
  :group 'haskell-indentation)

(defcustom haskell-indentation-delete-backward-indentation t
  "Delete backward removes indentation."
  :type 'boolean
  :group 'haskell-indentation)

(defcustom haskell-indentation-delete-backward-jump-line nil
  "Delete backward jumps to the previous line when removing last indentation."
  :type 'boolean
  :group 'haskell-indentation)

(defcustom haskell-indentation-delete-indentation t
  "Delete removes indentation."
  :type 'boolean
  :group 'haskell-indentation)

(defcustom haskell-indentation-indent-leftmost 'both
  "Indent to the left margin after certain keywords (for example after let .. in, case .. of).  If set to t it will only indent to the left.  If nil only relative to the containing expression.  If set to the keyword 'both then both positions are allowed."
  :type 'symbol
  :group 'haskell-indentation)

(defcustom haskell-indentation-layout-offset 2
  "Extra indentation to add before expressions in a haskell layout list."
  :type 'integer
  :group 'haskell-indentation)

(defcustom haskell-indentation-starter-offset 1
  "Extra indentation after an opening keyword (e.g. let)."
  :type 'integer
  :group 'haskell-indentation)

(defcustom haskell-indentation-left-offset 2
  "Extra indentation after an indentation to the left (e.g. after do)."
  :type 'integer
  :group 'haskell-indentation)

(defcustom  haskell-indentation-ifte-offset 2
  "Extra indentation after the keywords `if' `then' or `else'."
  :type 'integer
  :group 'haskell-indentation)

(defcustom haskell-indentation-where-pre-offset 2
  "Extra indentation before the keyword `where'."
  :type 'integer
  :group 'haskell-indentation)

(defcustom haskell-indentation-where-post-offset 2
  "Extra indentation after the keyword `where'."
  :type 'integer
  :group 'haskell-indentation)

(defcustom haskell-indentation-birdtrack-extra-space t
  "Append a space after every birdtrack in literate mode."
  :type 'boolean
  :group 'haskell-indentation)


;; Avoid a global bogus definition (which the original run-time
;; `defun' made), and support Emacs 21 without the syntax.el add-on.
(eval-when-compile
  (unless (fboundp 'syntax-ppss)
    (defsubst syntax-ppss (&rest pos)
      (parse-partial-sexp (point-min) (or pos (point))))))

(defconst haskell-indentation-mode-map
  (let ((keymap (make-sparse-keymap)))
    (define-key keymap (kbd "RET") 'haskell-newline-and-indent)
    (define-key keymap (kbd "DEL") 'haskell-indentation-delete-backward-char)
    (define-key keymap (kbd "<deletechar>") 'haskell-indentation-delete-char)
    keymap))

;; Used internally
(defvar haskell-indent-last-position)

;;;###autoload
(define-minor-mode haskell-indentation-mode
  "Haskell indentation mode that deals with the layout rule.
It rebinds RET, DEL and BACKSPACE, so that indentations can be
set and deleted as if they were real tabs.  It supports
autofill-mode."
  :lighter " Ind"
  :keymap haskell-indentation-mode-map
  (kill-local-variable 'indent-line-function)
  (kill-local-variable 'normal-auto-fill-function)
  (when haskell-indentation-mode
    (setq max-lisp-eval-depth (max max-lisp-eval-depth 600)) ;; set a higher limit for recursion
    (set (make-local-variable 'indent-line-function)
         'haskell-indentation-indent-line)
    (set (make-local-variable 'normal-auto-fill-function)
         'haskell-indentation-auto-fill-function)
    (set (make-local-variable 'haskell-indent-last-position)
         nil)))

;;;###autoload
(defun turn-on-haskell-indentation ()
  "Turn on the haskell-indentation minor mode."
  (interactive)
  (haskell-indentation-mode t))

(put 'parse-error
     'error-conditions
     '(error parse-error))
(put 'parse-error 'error-message "Parse error")

(defun parse-error (&rest args)
  (signal 'parse-error (apply 'format args)))

(defmacro on-parse-error (except &rest body)
  `(condition-case parse-error-string
       (progn ,@body)
     (parse-error
      ,except
      (message "%s" (cdr parse-error-string)))))

(defun haskell-current-column ()
  "Compute current column according to haskell syntax rules,
  correctly ignoring composition."
  (save-excursion
    (let ((start (point))
          (cc 0))
      (beginning-of-line)
      (while (< (point) start)
        (if (= (char-after) ?\t)
            (setq cc (* 8 (+ 1 (/ cc 8))))
          (cl-incf cc))
        (forward-char))
      cc)))

(defun kill-indented-line (&optional arg)
  "`kill-line' for indented text.
Preserves indentation and removes extra whitespace"
  (interactive "P")
  (let ((col (haskell-current-column))
        (old-point (point)))
    (cond ((or (and (numberp arg) (< arg 0))
               (and (not (looking-at "[ \t]*$"))
                    (or (not (numberp arg)) (zerop arg))))
                                        ;use default behavior when calling with a negative argument
                                        ;or killing (once) from the middle of a line
           (kill-line arg))
          ((and (skip-chars-backward " \t") ;always true
                (bolp)
                (save-excursion
                  (forward-line arg)
                  (not (looking-at "[ \t]*$"))))
                                        ; killing from an empty line:
                                        ; preserve indentation of the next line
           (kill-region (point)
                        (save-excursion
                          (forward-line arg)
                          (point)))
           (skip-chars-forward " \t")
           (if (> (haskell-current-column) col)
               (move-to-column col)))
          (t                            ; killing from not empty line:
                                        ; kill all indentation
           (goto-char old-point)
           (kill-region (point)
                        (save-excursion
                          (forward-line arg)
                          (skip-chars-forward " \t")
                          (point)))))))

(defun haskell-indentation-auto-fill-function ()
  (when (> (haskell-current-column) fill-column)
    (while (> (haskell-current-column) fill-column)
      (skip-syntax-backward "-")
      (skip-syntax-backward "^-"))
    (let ((auto-fill-function nil)
          (indent (car (last (haskell-indentation-find-indentations)))))
      (newline)
      (when (eq haskell-literate 'bird)
        (insert ">"))
      (indent-to indent)
      (end-of-line))))

(defun haskell-indentation-reindent (col)
  (beginning-of-line)
  (delete-region (point)
                 (progn
                   (when (and (eq haskell-literate 'bird)
                              (eq (char-after) ?>))
                     (forward-char))
                   (skip-syntax-forward "-")
                   (point)))
  (when (eq haskell-literate 'bird)
    (insert ">"))
  (indent-to col))

(defun haskell-indentation-current-indentation ()
  (if (eq haskell-literate 'bird)
      (save-excursion
        (beginning-of-line)
        (forward-char)
        (skip-syntax-forward "-")
        (current-column))
    (current-indentation)))

(defun haskell-indentation-outside-bird-line ()
  (and (eq haskell-literate 'bird)
       (or (< (current-column) 2)
           (save-excursion
             (beginning-of-line)
             (not (eq (char-after) ?>))))))

(defun haskell-newline-and-indent ()
  (interactive)
  (if (haskell-indentation-outside-bird-line)
      (progn
        (delete-horizontal-space)
        (newline))
    (on-parse-error
     (newline)
     (let* ((cc (haskell-current-column))
            (ci (haskell-indentation-current-indentation))
            (indentations (haskell-indentation-find-indentations)))
       (skip-syntax-forward "-")
       (if (prog1 (and (eolp)
                       (not (= (haskell-current-column) ci)))
             (delete-horizontal-space)
             (if (not (eq haskell-literate 'bird))
                 (newline)
               (when haskell-indentation-birdtrack-extra-space
                 (indent-to 2))
               (newline)
               (insert "> ")))
           (haskell-indentation-reindent
            (max (haskell-indentation-butlast indentations)
                 (haskell-indentation-matching-indentation
                  ci indentations)))
         (haskell-indentation-reindent (haskell-indentation-matching-indentation
                                        cc indentations)))))))

(defun haskell-indentation-one-indentation (col indentations)
  (let* ((last-pair (last indentations)))
    (cond ((null indentations)
           col)
          ((null (cdr indentations))
           (car indentations))
          ((<= col (car last-pair))
           col)
          (t (car last-pair)))))

(defun haskell-indentation-butlast (indentations)
  (when (consp (cdr indentations))
    (while (cddr indentations)
      (setq indentations (cdr indentations))))
  (car indentations))

(defun haskell-indentation-next-indentation (col indentations)
  "Find the lefmost indentation which is greater than COL."
  (catch 'return
    (while indentations
      (if (or (< col (car indentations))
              (null (cdr indentations)))
          (throw 'return (car indentations))
        (setq indentations (cdr indentations))))
    col))

(defun haskell-indentation-previous-indentation (col indentations)
  "Find the rightmost indentation which is less than COL."
  (and indentations
       (> col (car indentations))
       (catch 'return
         (while indentations
           (if (or (null (cdr indentations))
                   (<= col (cadr indentations)))
               (throw 'return (car indentations))
             (setq indentations (cdr indentations))))
         col)))

(defun haskell-indentation-matching-indentation (col indentations)
  "Find the leftmost indentation which is greater than or equal to COL."
  (catch 'return
    (while indentations
      (if (or (<= col (car indentations))
              (null (cdr indentations)))
          (throw 'return (car indentations))
        (setq indentations (cdr indentations))))
    col))

(defun haskell-indentation-indent-line ()
  (when (save-excursion
          (beginning-of-line)
          (not (nth 8 (syntax-ppss))))
    (let ((ci (haskell-indentation-current-indentation))
          (start-column (haskell-current-column)))
      (cond ((> (haskell-current-column) ci)
             (save-excursion
               (move-to-column ci)
               (haskell-indentation-reindent
                (haskell-indentation-one-indentation
                 ci (haskell-indentation-find-indentations)))))

            ((= (haskell-current-column) ci)
             (haskell-indentation-reindent
              (haskell-indentation-next-indentation
               ci (haskell-indentation-find-indentations))))

            (t (move-to-column ci)
               (haskell-indentation-reindent
                (haskell-indentation-matching-indentation
                 ci (haskell-indentation-find-indentations)))))
      (cond ((not (= (haskell-current-column) start-column))
             (setq haskell-indent-last-position nil))
            ((not haskell-indentation-cycle-warn)
             (haskell-indentation-reindent
              (haskell-indentation-next-indentation
               -1
               (haskell-indentation-find-indentations))))
            ((not (equal (point) haskell-indent-last-position))
             (message "Press TAB again to go to the leftmost indentation")
             (setq haskell-indent-last-position (point)))
            (t
             (haskell-indentation-reindent
              (haskell-indentation-next-indentation
               -1
               (haskell-indentation-find-indentations))))))))

(defun haskell-indentation-delete-backward-char (n)
  (interactive "p")
  (on-parse-error
   (delete-char (- n))
   (cond
    ((haskell-indentation-outside-bird-line)
     (delete-char (- n)))
    ((and (use-region-p)
          delete-active-region
          (not (= (point) (mark))))
     (delete-region (mark) (point)))
    ((or (= (haskell-current-column) 0)
         (> (haskell-current-column) (haskell-indentation-current-indentation))
         (nth 8 (syntax-ppss)))
     (delete-char (- n)))
    (haskell-indentation-delete-backward-indentation
     (let* ((ci (haskell-indentation-current-indentation))
            (pi (haskell-indentation-previous-indentation
                 ci (haskell-indentation-find-indentations))))
       (save-excursion
         (cond (pi
                (move-to-column pi)
                (delete-region (point)
                               (progn (move-to-column ci)
                                      (point))))
               (t
                (if (not haskell-indentation-delete-backward-jump-line)
                    (delete-char (- 1))
                  (beginning-of-line)
                  (delete-region (max (point-min) (- (point) 1))
                                 (progn (move-to-column ci)
                                        (point)))))))))
    (t (delete-char (- n))))))

(defun haskell-indentation-delete-char (n)
  (interactive "p")
  (if (haskell-indentation-outside-bird-line)
      (delete-char n)
    (on-parse-error (delete-char n)
                    (cond
                     ((and delete-selection-mode
                           mark-active
                           (not (= (point) (mark))))
                      (delete-region (mark) (point)))
                     ((and (eq haskell-literate 'bird)
                           (looking-at "\n> "))
                      (delete-char (+ n 2)))
                     ((or (eolp)
                          (>= (haskell-current-column) (haskell-indentation-current-indentation))
                          (nth 8 (syntax-ppss)))
                      (delete-char n))
                     (haskell-indentation-delete-indentation
                      (let* ((ci (haskell-indentation-current-indentation))
                             (pi (haskell-indentation-previous-indentation
                                  ci (haskell-indentation-find-indentations))))
                        (save-excursion
                          (if (and pi (> pi (haskell-current-column)))
                              (move-to-column pi))
                          (delete-region (point)
                                         (progn (move-to-column ci)
                                                (point))))))
                     (t (delete-char (- n)))))))

(defun haskell-indentation-goto-least-indentation ()
  (beginning-of-line)
  (if (eq haskell-literate 'bird)
      (catch 'return
        (while t
          (when (not (eq (char-after) ?>))
            (forward-line)
            (forward-char 2)
            (throw 'return nil))
          (let ((ps (nth 8 (syntax-ppss))))
            (when ps ;; inside comment or string
              (goto-char ps)
              (beginning-of-line)))
          (when (and (>= 2 (haskell-indentation-current-indentation))
                     (not (looking-at ">\\s-*$")))
            (forward-char 2)
            (throw 'return nil))
          (when (bobp)
            (forward-char 2)
            (throw 'return nil))
          (forward-line -1)))
    ;; not bird style
    (catch 'return
      (while (not (bobp))
        (forward-comment (- (buffer-size)))
        (beginning-of-line)
        (let ((ps (nth 8 (syntax-ppss))))
          (when ps ;; inside comment or string
            (goto-char ps)))
        (when (= 0 (haskell-indentation-current-indentation))
          (throw 'return nil))))
    (beginning-of-line)
    (when (bobp)
      (forward-comment (buffer-size)))))

(defun haskell-indentation-parse-to-indentations ()
  (save-excursion
    (skip-syntax-forward "-")
    (let ((indentation-point (point))
          (layout-indent 0)
          (parse-line-number 0)
          (current-indent haskell-indentation-layout-offset)
          (starter-indent haskell-indentation-layout-offset)
          (left-indent haskell-indentation-layout-offset)
          (case-fold-search nil)
          current-token
          following-token
          possible-indentations)
      (haskell-indentation-goto-least-indentation)
      (if (<= indentation-point (point))
          (haskell-indentation-first-indentation)
        (setq current-token (haskell-indentation-peek-token))
        (catch 'parse-end
          (haskell-indentation-toplevel)
          (unless (eq current-token 'end-tokens)
            (parse-error "Illegal token: %s" current-token)))
        possible-indentations))))

(defun haskell-indentation-first-indentation ()
  (if (eq haskell-literate 'bird) '(2) '(0)))

(defun haskell-indentation-find-indentations ()
  (let ((ppss (syntax-ppss)))
    (cond
     ((nth 3 ppss)
      (haskell-indentation-first-indentation))
     ((nth 4 ppss)
      (if (save-excursion
            (and (skip-syntax-forward "-")
                 (eolp)
                 (not (> (forward-line 1) 0))
                 (not (nth 4 (syntax-ppss)))))
          (haskell-indentation-parse-to-indentations)
        (haskell-indentation-first-indentation)))
     (t
      (haskell-indentation-parse-to-indentations)))))

(defconst haskell-indentation-unicode-tokens
  '(("→" . "->")     ;; #x2192 RIGHTWARDS ARROW
    ("∷" . "::")     ;; #x2237 PROPORTION
    ("←" . "<-")     ;; #x2190 LEFTWARDS ARROW
    ("⇒" . "=>")     ;; #x21D2 RIGHTWARDS DOUBLE ARROW
    ("∀" . "forall") ;; #x2200 FOR ALL
    ("↢" . "-<")     ;; #x2919 LEFTWARDS ARROW-TAIL
    ("↣" . ">-")     ;; #x291A RIGHTWARDS ARROW-TAIL
    ("⤛" . "-<<")    ;; #x291B LEFTWARDS DOUBLE ARROW-TAIL
    ("⤜" . ">>-")    ;; #x291C RIGHTWARDS DOUBLE ARROW-TAIL
    ("★" . "*"))     ;; #x2605 BLACK STAR
  "Translation dictionary from UnicodeSyntax tokens to their ASCII representation.")

(defconst haskell-indentation-toplevel-list
  '(("module" . haskell-indentation-module)
    ("data" . (lambda () (haskell-indentation-statement-right #'haskell-indentation-data)))
    ("type" . (lambda () (haskell-indentation-statement-right #'haskell-indentation-data)))
    ("newtype" . (lambda () (haskell-indentation-statement-right #'haskell-indentation-data)))
    ("class" . haskell-indentation-class-declaration)
    ("instance" . haskell-indentation-class-declaration)))

(defconst haskell-indentation-type-list
  '(("::"    . (lambda () (haskell-indentation-with-starter
                           (lambda () (haskell-indentation-separated #'haskell-indentation-type "->" nil)) nil)))
    ("("     . (lambda () (haskell-indentation-list #'haskell-indentation-type
                                                    ")" "," nil)))
    ("["     . (lambda () (haskell-indentation-list #'haskell-indentation-type
                                                    "]" "," nil)))
    ("{"     . (lambda () (haskell-indentation-list #'haskell-indentation-type
                                                    "}" "," nil)))))

(defconst haskell-indentation-expression-list
  '(("data" . haskell-indentation-data)
    ("type" . haskell-indentation-data)
    ("newtype" . haskell-indentation-data)
    ("if"    . haskell-indentation-if)
    ("let"   . (lambda () (haskell-indentation-phrase
                           '(haskell-indentation-declaration-layout
                             "in" haskell-indentation-expression))))
    ("do"    . (lambda () (haskell-indentation-with-starter
                           #'haskell-indentation-expression-layout nil)))
    ("mdo"   . (lambda () (haskell-indentation-with-starter
                           #'haskell-indentation-expression-layout nil)))
    ("rec"   . (lambda () (haskell-indentation-with-starter
                           #'haskell-indentation-expression-layout nil)))
    ("case"  . (lambda () (haskell-indentation-phrase
                           '(haskell-indentation-expression
                             "of" haskell-indentation-case-layout))))
    ("\\"    . (lambda () (haskell-indentation-with-starter
                           #'haskell-indentation-lambda-maybe-lambdacase nil)))
    ("proc"  . (lambda () (haskell-indentation-phrase
                           '(haskell-indentation-expression
                             "->" haskell-indentation-expression))))
    ("where" . (lambda () (haskell-indentation-with-starter
                           #'haskell-indentation-declaration-layout nil t)))
    ("::"    . (lambda () (haskell-indentation-with-starter
                           (lambda () (haskell-indentation-separated #'haskell-indentation-type "->" nil)) nil)))
    ("="     . (lambda () (haskell-indentation-statement-right #'haskell-indentation-expression)))
    ("<-"    . (lambda () (haskell-indentation-statement-right #'haskell-indentation-expression)))
    ("("     . (lambda () (haskell-indentation-list #'haskell-indentation-expression
                                                    ")" '(list "," "->") nil)))
    ("["     . (lambda () (haskell-indentation-list #'haskell-indentation-expression
                                                    "]" "," "|")))
    ("{"     . (lambda () (haskell-indentation-list #'haskell-indentation-expression
                                                    "}" "," nil)))))

(defun haskell-indentation-expression-layout ()
  (haskell-indentation-layout #'haskell-indentation-expression))

(defun haskell-indentation-declaration-layout ()
  (haskell-indentation-layout #'haskell-indentation-declaration))

(defun haskell-indentation-case-layout ()
  (haskell-indentation-layout #'haskell-indentation-case))

;; After a lambda (backslash) there are two possible cases:
;;   - the new lambdacase expression, that can be recognized by the
;;     next token being "case",
;;   - or simply an anonymous function definition in the form of
;;     "expression -> expression".
(defun haskell-indentation-lambda-maybe-lambdacase ()
  (if (string= current-token "case")
      (haskell-indentation-with-starter
       #'haskell-indentation-case-layout nil)
    (haskell-indentation-phrase-rest
     '(haskell-indentation-expression "->" haskell-indentation-expression))))

(defun haskell-indentation-fundep ()
  (haskell-indentation-with-starter
   (lambda () (haskell-indentation-separated
               #'haskell-indentation-fundep1 "," nil))
   nil))

(defun haskell-indentation-fundep1 ()
  (let ((current-indent (haskell-current-column)))
    (while (member current-token '(value "->"))
      (haskell-indentation-read-next-token))
    (when (and (eq current-token 'end-tokens)
               (member following-token '(value "->")))
      (haskell-indentation-add-indentation current-indent))))

(defun haskell-indentation-toplevel ()
  (haskell-indentation-layout
   (lambda ()
     (let ((parser (assoc current-token haskell-indentation-toplevel-list)))
       (if parser
           (funcall (cdr parser))
         (haskell-indentation-declaration))))))

(defun haskell-indentation-type ()
  (let ((current-indent (haskell-current-column)))
    (catch 'return
      (while t
        (cond
         ((member current-token '(value operator "->"))
          (haskell-indentation-read-next-token))

         ((eq current-token 'end-tokens)
          (when (member following-token
                        '(value operator no-following-token
                                "->" "(" "[" "{" "::"))
            (haskell-indentation-add-indentation current-indent))
          (throw 'return nil))

         (t (let ((parser (assoc current-token haskell-indentation-type-list)))
              (if (not parser)
                  (throw 'return nil)
                (funcall (cdr parser))))))))))

(defun haskell-indentation-data ()
  (haskell-indentation-with-starter
   (lambda ()
     (when (string= current-token "instance")
       (haskell-indentation-read-next-token))
     (haskell-indentation-type)
     (cond ((string= current-token "=")
            (haskell-indentation-with-starter
             (lambda () (haskell-indentation-separated #'haskell-indentation-type "|" "deriving"))
             nil))
           ((string= current-token "where")
            (haskell-indentation-with-starter
             #'haskell-indentation-expression-layout nil))))
   nil))

(defun haskell-indentation-class-declaration ()
  (haskell-indentation-with-starter
   (lambda ()
     (haskell-indentation-type)
     (when (string= current-token "|")
       (haskell-indentation-fundep))
     (when (string= current-token "where")
       (haskell-indentation-with-starter
        #'haskell-indentation-declaration-layout nil)))
   nil))

(defun haskell-indentation-module ()
  (haskell-indentation-with-starter
   (lambda ()
     (let ((current-indent (haskell-current-column)))
       (haskell-indentation-read-next-token)
       (when (string= current-token "(")
         (haskell-indentation-list
          #'haskell-indentation-module-export
          ")" "," nil))
       (when (eq current-token 'end-tokens)
         (haskell-indentation-add-indentation current-indent)
         (throw 'parse-end nil))
       (when (string= current-token "where")
         (haskell-indentation-read-next-token)
         (when (eq current-token 'end-tokens)
           (haskell-indentation-add-layout-indent)
           (throw 'parse-end nil))
         (haskell-indentation-layout #'haskell-indentation-toplevel))))
   nil))

(defun haskell-indentation-module-export ()
  (cond ((string= current-token "module")
         (let ((current-indent (haskell-current-column)))
           (haskell-indentation-read-next-token)
           (cond ((eq current-token 'end-tokens)
                  (haskell-indentation-add-indentation current-indent))
                 ((eq current-token 'value)
                  (haskell-indentation-read-next-token)))))
        (t (haskell-indentation-type))))

(defun haskell-indentation-list (parser end sep stmt-sep)
  (haskell-indentation-with-starter
   `(lambda () (haskell-indentation-separated #',parser
                                              ,sep
                                              ,stmt-sep))
   end))

(defun haskell-indentation-with-starter (parser end &optional where-expr?)
  (let ((starter-column (haskell-current-column))
        (current-indent current-indent)
        (left-indent (if (= (haskell-current-column) (haskell-indentation-current-indentation))
                         (haskell-current-column) left-indent)))
    (haskell-indentation-read-next-token)
    (when (eq current-token 'end-tokens)
      (if (equal following-token end)
          (haskell-indentation-add-indentation starter-column)
        (if where-expr?
            (haskell-indentation-add-where-post-indent left-indent)
          (haskell-indentation-add-indentation
           (+ left-indent haskell-indentation-left-offset))))
      (throw 'parse-end nil))
    (let* ((current-indent (haskell-current-column))
           (starter-indent (min starter-column current-indent))
           (left-indent (if end (+ current-indent haskell-indentation-starter-offset)
                          left-indent)))
      (funcall parser)
      (cond ((eq current-token 'end-tokens)
             (when (equal following-token end)
               (haskell-indentation-add-indentation starter-indent))
             (when end (throw 'parse-end nil))) ;; add no indentations
            ((equal current-token end)
             (haskell-indentation-read-next-token)) ;; continue
            (end (parse-error "Illegal token: %s" current-token))))))

(defun haskell-indentation-case-alternative ()
  (setq left-indent (current-column))
  (haskell-indentation-separated #'haskell-indentation-expression "," nil)
  (cond ((eq current-token 'end-tokens)
         (haskell-indentation-add-indentation current-indent))
        ((string= current-token "->")
         (haskell-indentation-statement-right #'haskell-indentation-expression))
        ;; otherwise fallthrough
        ))

(defun haskell-indentation-case ()
  (haskell-indentation-expression)
  (cond ((eq current-token 'end-tokens)
         (haskell-indentation-add-indentation current-indent))
        ((string= current-token "|")
	 (haskell-indentation-with-starter
	  (lambda ()
	    (haskell-indentation-separated #'haskell-indentation-case-alternative "|" nil))
	  nil))
        ((string= current-token "->")
         (haskell-indentation-statement-right #'haskell-indentation-expression))
        ;; otherwise fallthrough
        ))

(defun haskell-indentation-statement-right (parser)
  (haskell-indentation-read-next-token)
  (when (eq current-token 'end-tokens)
    (haskell-indentation-add-indentation
     (+ left-indent haskell-indentation-left-offset))
    (throw 'parse-end nil))
  (let ((current-indent (haskell-current-column)))
    (funcall parser)))

(defun haskell-indentation-simple-declaration ()
  (haskell-indentation-expression)
  (cond ((string= current-token "=")
         (haskell-indentation-statement-right #'haskell-indentation-expression))
        ((string= current-token "::")
         (haskell-indentation-statement-right #'haskell-indentation-type))
        ((and (eq current-token 'end-tokens)
              (string= following-token "="))
         (haskell-indentation-add-indentation current-indent)
         (throw 'parse-end nil))))

(defun haskell-indentation-guard ()
  (setq left-indent (current-column))
  (haskell-indentation-separated
   #'haskell-indentation-expression "," nil))

(defun haskell-indentation-declaration ()
  (haskell-indentation-separated #'haskell-indentation-expression "," nil)
  (cond ((string= current-token "|")
         (haskell-indentation-with-starter
          (lambda () (haskell-indentation-separated
		      #'haskell-indentation-guard "|" nil))
          nil))
        ((eq current-token 'end-tokens)
         (when (member following-token '("|" "=" "::" ","))
           (haskell-indentation-add-indentation current-indent)
           (throw 'parse-end nil)))))

(defun haskell-indentation-layout (parser)
  (if (string= current-token "{")
      (haskell-indentation-list parser "}" ";" nil)
    (haskell-indentation-implicit-layout-list parser)))

(defun haskell-indentation-expression-token (token)
  (member token '("if" "let" "do" "case" "\\" "(" "[" "::"
                  value operator no-following-token)))

(defun haskell-indentation-expression ()
  (let ((current-indent (haskell-current-column)))
    (catch 'return
      (while t
        (cond
         ((memq current-token '(value operator))
          (haskell-indentation-read-next-token))

         ((eq current-token 'end-tokens)
          (cond ((string= following-token "where")
                 (haskell-indentation-add-where-pre-indent))
                ((haskell-indentation-expression-token following-token)
                 (haskell-indentation-add-indentation
                  current-indent)))
          (throw 'return nil))

         (t (let ((parser (assoc current-token haskell-indentation-expression-list)))
              (when (null parser)
                (throw 'return nil))
              (funcall (cdr parser))
              (when (and (eq current-token 'end-tokens)
                         (string= (car parser) "let")
                         (= haskell-indentation-layout-offset current-indent)
                         (haskell-indentation-expression-token following-token))
                ;; inside a layout, after a let construct
                (haskell-indentation-add-layout-indent)
                (throw 'parse-end nil))
              (unless (member (car parser) '("(" "[" "{" "do" "case"))
                (throw 'return nil)))))))))

(defun haskell-indentation-test-indentations ()
  (interactive)
  (let ((indentations (save-excursion (haskell-indentation-find-indentations)))
        (str "")
        (pos 0))
    (while indentations
      (when (>= (car indentations) pos)
        (setq str (concat str (make-string (- (car indentations) pos) ?\ )
                          "|"))
        (setq pos (+ 1 (car indentations))))
      (setq indentations (cdr indentations)))
    (end-of-line)
    (newline)
    (insert str)))

(defun haskell-indentation-separated (parser separator stmt-separator)
  (catch 'return
    (while t
      (funcall parser)
      (cond ((if (listp separator) (member current-token separator) (equal current-token separator))
             (haskell-indentation-at-separator))

            ((equal current-token stmt-separator)
             (setq starter-indent (haskell-current-column))
             (haskell-indentation-at-separator))

            ((eq current-token 'end-tokens)
             (cond ((or (equal following-token separator)
                        (equal following-token stmt-separator))
                    (haskell-indentation-add-indentation starter-indent)
                    (throw 'parse-end nil)))
             (throw 'return nil))

            (t (throw 'return nil))))))

(defun haskell-indentation-at-separator ()
  (let ((separator-column
         (and (= (haskell-current-column) (haskell-indentation-current-indentation))
              (haskell-current-column))))
    (haskell-indentation-read-next-token)
    (cond ((eq current-token 'end-tokens)
           (haskell-indentation-add-indentation current-indent)
           (throw 'return nil))
          (separator-column ;; on the beginning of the line
           (setq current-indent (haskell-current-column))
           (setq starter-indent separator-column)))))

(defun haskell-indentation-implicit-layout-list (parser)
  (let* ((layout-indent (haskell-current-column))
         (current-indent (haskell-current-column))
         (left-indent (haskell-current-column)))
    (catch 'return
      (while t
        (let ((left-indent left-indent))
          (funcall parser))
        (cond ((member current-token '(layout-next ";"))
               (haskell-indentation-read-next-token))
              ((eq current-token 'end-tokens)
               (when (or (haskell-indentation-expression-token following-token)
                         (string= following-token ";"))
                 (haskell-indentation-add-layout-indent))
               (throw 'return nil))
              (t (throw 'return nil))))))
  ;; put haskell-indentation-read-next-token outside the current-indent definition
  ;; so it will not return 'layout-end again
  (when (eq current-token 'layout-end)
    (haskell-indentation-read-next-token))) ;; leave layout at 'layout-end or illegal token

(defun haskell-indentation-if ()
  (haskell-indentation-with-starter
   (lambda ()
     (if (string= current-token "|")
	 (haskell-indentation-with-starter
	  (lambda ()
	    (haskell-indentation-separated
	     #'haskell-indentation-case-alternative "|" nil))
	  nil)
       (haskell-indentation-phrase-rest
	'(haskell-indentation-expression
	  "then" haskell-indentation-expression
	  "else" haskell-indentation-expression))))
   nil))

(defun haskell-indentation-phrase (phrase)
  (haskell-indentation-with-starter
   `(lambda () (haskell-indentation-phrase-rest ',phrase))
   nil))

(defun haskell-indentation-phrase-rest (phrase)
  (let ((starter-line parse-line-number))
    (let ((current-indent (haskell-current-column)))
      (funcall (car phrase)))
    (cond
     ((eq current-token 'end-tokens)
      (cond ((null (cdr phrase))) ;; fallthrough
            ((equal following-token (cadr phrase))
             (haskell-indentation-add-indentation starter-indent)
             (throw 'parse-end nil))
            ((string= (cadr phrase) "in")
             (when (= left-indent layout-indent)
               (haskell-indentation-add-layout-indent)
               (throw 'parse-end nil)))
            (t (throw 'parse-end nil))))

     ((null (cdr phrase)))

     ((equal (cadr phrase) current-token)
      (let* ((on-new-line (= (haskell-current-column) (haskell-indentation-current-indentation)))
             (lines-between (- parse-line-number starter-line))
             (left-indent (if (<= lines-between 0)
                              left-indent
                            starter-indent)))
        (haskell-indentation-read-next-token)
	(when (eq current-token 'end-tokens)
          (cond ((member (cadr phrase) '("then" "else"))
		 (haskell-indentation-add-indentation
		  (+ starter-indent haskell-indentation-ifte-offset)))

		((member (cadr phrase) '("in" "->"))
		 ;; expression ending in another expression
		 (when (or (not haskell-indentation-indent-leftmost)
			   (eq haskell-indentation-indent-leftmost 'both))
		   (haskell-indentation-add-indentation
		    (+ starter-indent haskell-indentation-starter-offset)))
		 (when haskell-indentation-indent-leftmost
		   (haskell-indentation-add-indentation
		    (if on-new-line
			(+ left-indent haskell-indentation-starter-offset)
		      left-indent))))

		 (t
		  (when (or (not haskell-indentation-indent-leftmost)
			    (eq haskell-indentation-indent-leftmost 'both))
		    (haskell-indentation-add-indentation
		     (+ starter-indent haskell-indentation-starter-offset)))
		  (when haskell-indentation-indent-leftmost
		   (haskell-indentation-add-indentation
		    (if on-new-line
			(+ left-indent haskell-indentation-starter-offset)
		      left-indent)))))
          (throw 'parse-end nil))
        (haskell-indentation-phrase-rest (cddr phrase))))

     ((string= (cadr phrase) "in")) ;; fallthrough
     (t (parse-error "Expecting %s" (cadr phrase))))))

(defun haskell-indentation-add-indentation (indent)
  (haskell-indentation-push-indentation
   (if (<= indent layout-indent)
       (+ layout-indent haskell-indentation-layout-offset)
     indent)))

(defun haskell-indentation-add-layout-indent ()
  (haskell-indentation-push-indentation layout-indent))

(defun haskell-indentation-add-where-pre-indent ()
  (haskell-indentation-push-indentation
   (+ layout-indent haskell-indentation-where-pre-offset))
  (if (= layout-indent haskell-indentation-layout-offset)
      (haskell-indentation-push-indentation
       haskell-indentation-where-pre-offset)))

(defun haskell-indentation-add-where-post-indent (indent)
  (haskell-indentation-push-indentation
   (+ indent haskell-indentation-where-post-offset)))

(defun haskell-indentation-push-indentation (indent)
  (when (or (null possible-indentations)
            (< indent (car possible-indentations)))
    (setq possible-indentations
          (cons indent possible-indentations))))

(defun haskell-indentation-token-test ()
  (let ((current-token nil)
        (following-token nil)
        (layout-indent 0)
        (parse-line-number 0)
        (indentation-point (mark)))
    (haskell-indentation-read-next-token)))

(defun haskell-indentation-read-next-token ()
  (cond ((eq current-token 'end-tokens)
         'end-tokens)
        ((eq current-token 'layout-end)
         (cond ((> layout-indent (haskell-current-column))
                'layout-end)
               ((= layout-indent (haskell-current-column))
                (setq current-token 'layout-next))
               ((< layout-indent (haskell-current-column))
                (setq current-token (haskell-indentation-peek-token)))))
        ((eq current-token 'layout-next)
         (setq current-token (haskell-indentation-peek-token)))
        ((> layout-indent (haskell-current-column))
         (setq current-token 'layout-end))
        (t
         (haskell-indentation-skip-token)
         (if (>= (point) indentation-point)
             (progn
               (setq following-token
                     (if (= (point) indentation-point)
                         (haskell-indentation-peek-token)
                       'no-following-token))
               (setq current-token 'end-tokens))
           (when (= (haskell-current-column) (haskell-indentation-current-indentation))
             ;; on a new line
             (setq current-indent (haskell-current-column))
             (setq left-indent (haskell-current-column))
             (setq parse-line-number (+ parse-line-number 1)))
           (cond ((> layout-indent (haskell-current-column))
                  (setq current-token 'layout-end))
                 ((= layout-indent (haskell-current-column))
                  (setq current-token 'layout-next))
                 (t (setq current-token (haskell-indentation-peek-token))))))))

(defun haskell-indentation-peek-token ()
  "Return token starting at point."
  (cond ((looking-at "\\(if\\|then\\|else\\|let\\|in\\|mdo\\|rec\\|do\\|proc\\|case\\|of\\|where\\|module\\|deriving\\|data\\|type\\|newtype\\|class\\|instance\\)\\([^[:alnum:]'_]\\|$\\)")
         (match-string-no-properties 1))
        ((looking-at "[][(){}[,;]")
         (match-string-no-properties 0))
        ((looking-at "\\(\\\\\\|->\\|→\\|<-\\|←\\|::\\|∷\\|=\\||\\)\\([^-:!#$%&*+./<=>?@\\\\^|~]\\|$\\)")
         (match-string-no-properties 1))
        ((looking-at "\\(→\\|←\\|∷\\)\\([^-:!#$%&*+./<=>?@\\\\^|~]\\|$\\)")
         (let ((tok (match-string-no-properties 1)))
           (or (cdr (assoc tok haskell-indentation-unicode-tokens)) tok)))
        ((looking-at"[-:!#$%&*+./<=>?@\\\\^|~`]" )
         'operator)
        (t 'value)))

(defun haskell-indentation-skip-token ()
  "Skip to the next token."
  (let ((case-fold-search nil))

    (if (or (looking-at "'\\([^\\']\\|\\\\.\\)*'")
            (looking-at "\"\\([^\\\"]\\|\\\\.\\)*\"")
            (looking-at         ; Hierarchical names always start with uppercase
             "[[:upper:]]\\(\\sw\\|'\\)*\\(\\.\\(\\sw\\|'\\)+\\)*")
            (looking-at "\\sw\\(\\sw\\|'\\)*") ; Only unqualified vars can start with lowercase
            (looking-at "[0-9][0-9oOxXeE+-]*")
            (looking-at "[-:!#$%&*+./<=>?@\\\\^|~]+")
            (looking-at "[](){}[,;]")
            (looking-at "`[[:alnum:]']*`"))
        (goto-char (match-end 0))
      ;; otherwise skip until space found
      (skip-syntax-forward "^-"))
    (forward-comment (buffer-size))
    (while (and (eq haskell-literate 'bird)
                (bolp)
                (eq (char-after) ?>))
      (forward-char)
      (forward-comment (buffer-size)))))

(provide 'haskell-indentation)

;; Local Variables:
;; tab-width: 8
;; End:

;;; haskell-indentation.el ends here
