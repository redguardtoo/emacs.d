;;; wucuo.el --- Spell check code containing camel case words

;; Copyright (C) 2018 Chen Bin
;;
;; Version: 0.0.6
;; Keywords: convenience
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: http://github.com/redguardtoo/wucuo
;; Package-Requires: ((emacs "24.4"))

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:
;;
;; 1. Setup
;; Please install either aspell or hunspell and its corresponding dictionaries.
;;
;; 2. Usage
;; Run `wucuo-start' to setup and start `flyspell-mode'.
;; It spell check camel case words in code.
;;
;; To enable wucuo for all languages, insert below code into ".emacs",
;;
;;   (defun prog-mode-hook-setup ()
;;     (wucuo-start t))
;;   (add-hook 'prog-mode-hook 'prog-mode-hook-setup)
;;
;; Please note `flyspell-prog-mode' should not be enabled when using "wucuo".
;; `flyspell-prog-mode' could be replaced by "wucuo".
;;
;; Or add one line setup if you prefer running `flyspell-buffer' manually:
;;   (setq flyspell-generic-check-word-predicate #'wucuo-generic-check-word-predicate)
;;
;; Or setup for only one major mode when major mode has its own flyspell setup:
;;   (wucuo-setup-major-mode "js2-mode")

;;; Code:
(require 'flyspell)

(defgroup wucuo nil
  "Code spell checker."
  :group 'flyspell)

(defcustom wucuo-debug nil
  "Output debug information when it's not nil."
  :type 'boolean
  :group 'wucuo)

(defcustom wucuo-auto-turn-on-flyspell t
  "Turn on `flyspell-mode' automatically after running `wucuo-start'."
  :type 'boolean
  :group 'wucuo)

(defcustom wucuo-check-nil-font-face nil
  "If nil, ignore text without font face."
  :type 'sexp
  :group 'wucuo)

(defcustom wucuo-aspell-language-to-use "en"
  "Language to use passed to aspell option '--lang'."
  :type 'string
  :group 'wucuo)

(defcustom wucuo-hunspell-dictionary-base-name "en_US"
  "Dictionary base name pass to hunspell option '-d'."
  :type 'string
  :group 'wucuo)

(defcustom wucuo-font-faces-to-check
  '(font-lock-string-face
    font-lock-doc-face
    font-lock-comment-face
    font-lock-builtin-face
    font-lock-function-name-face
    font-lock-variable-name-face
    font-lock-type-face

    ;; javascript
    js2-function-call
    js2-function-param
    js2-object-property
    js2-object-property-access

    ;; css
    font-lock-builtin-face
    css-selector
    css-property

    ;; ReactJS
    rjsx-text
    rjsx-tag
    rjsx-attr)
  "Only check word whose font face is among this list."
  :type '(repeat sexp)
  :group 'wucuo)

(defcustom wucuo-personal-font-faces-to-check
  nil
  "Similar to `wucuo-font-faces-to-check'.
Define personal font faces to check."
  :type '(repeat sexp)
  :group 'wucuo)

(defcustom wucuo-major-modes-to-setup-by-force
  '(typescript-mode)
  "Major modes whose own predicate should be replaced by this program.
Running `wucuo-start' with first parameter being t will set up modes listed here."
  :type '(repeat sexp)
  :group 'wucuo)

(defcustom wucuo-extra-predicate '(lambda (word) t)
  "A callback to check WORD.  Return t if WORD is typo."
  :type 'function
  :group 'wucuo)

;;;###autoload
(defun wucuo-current-font-face (&optional quiet)
  "Get font face under cursor.
If QUIET is t, font face is not output."
  (interactive)
  (let* ((rlt (format "%S" (get-text-property (point) 'face))))
    (kill-new rlt)
    (unless quiet (message rlt))))

;;;###autoload
(defun wucuo-split-camel-case (word)
  "Split camel case WORD into a list of strings.
Ported from 'https://github.com/fatih/camelcase/blob/master/camelcase.go'."
  (let* ((case-fold-search nil)
         (len (length word))
         ;; 32 sub-words is enough
         (runes [nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil])
         (runes-length 0)
         (i 0)
         ch
         (last-class 0)
         (class 0)
         rlt)

    ;; split into fields based on class of character
    (while (< i len)
      (setq ch (elt word i))
      (cond
       ;; lower case
       ((and (>= ch ?a) (<= ch ?z))
        (setq class 1))
       ;; upper case
       ((and (>= ch ?A) (<= ch ?Z))
        (setq class 2))
       ((and (>= ch ?0) (<= ch ?9))
        (setq class 3))
       (t
        (setq class 4)))

      (cond
       ((= class last-class)
        (aset runes
              (1- runes-length)
              (concat (aref runes (1- runes-length)) (char-to-string ch))))
       (t
        (aset runes runes-length (char-to-string ch))
        (setq runes-length (1+ runes-length))))
      (setq last-class class)
      ;; end of while
      (setq i (1+ i)))

    ;; handle upper case -> lower case sequences, e.g.
    ;;     "PDFL", "oader" -> "PDF", "Loader"
    (setq i 0)
    (while (< i (1- runes-length))
      (let* ((ch-first (aref (aref runes i) 0))
             (ch-second (aref (aref runes (1+ i)) 0)))
        (when (and (and (>= ch-first ?A) (<= ch-first ?Z))
                   (and (>= ch-second ?a) (<= ch-second ?z)))
          (aset runes (1+ i) (concat (substring (aref runes i) -1) (aref runes (1+ i))))
          (aset runes i (substring (aref runes i) 0 -1))))
      (setq i (1+ i)))

    ;; construct final result
    (setq i 0)
    (while (< i runes-length)
      (when (> (length (aref runes i)) 0)
        (setq rlt (add-to-list 'rlt (aref runes i) t)))
      (setq i (1+ i)))
    rlt))

(defun wucuo-spell-checker-to-string (line)
  "Feed LINE into spell checker and return output as string."
  (let* ((cmd (cond
               ;; aspell: `echo "helle world" | aspell pipe --lang en`
               ((string-match-p "aspell$" ispell-program-name)
                (format "%s pipe --lang %s" ispell-program-name wucuo-aspell-language-to-use))
               ;; hunspell: `echo "helle world" | hunspell -a -d en_US`
               (t
                (format "%s -a -d %s" ispell-program-name wucuo-hunspell-dictionary-base-name))))
         rlt)
    (with-temp-buffer
      (call-process-region line ; feed line into process
                           nil ; ignored
                           shell-file-name
                           nil ; don't delete
                           t
                           nil
                           shell-command-switch
                           cmd)
      (setq rlt (buffer-substring-no-properties (point-min) (point-max))))
    (when wucuo-debug (message "wucuo-spell-checker-to-string => cmd=%s rlt=%s" cmd rlt))
    rlt))

;;;###autoload
(defun wucuo-check-camel-case-word-predicate (word)
  "Use aspell to check WORD.  If it's typo return t."
  (if (string-match-p "^&" (wucuo-spell-checker-to-string word)) t))

(defun wucuo-handle-sub-word (sub-word)
  "If return empty string, SUB-WORD is not checked by spell checker."
  (cond
   ;; don't check 1/2 character word
   ((< (length sub-word) 3)
    "")
   ;; don't  check word containing special character
   ((not (string-match-p "^[a-zA-Z]*$" sub-word))
    "")
   (t
    sub-word)))

;;;###autoload
(defun wucuo-generic-check-word-predicate ()
  "Function providing per-mode customization over which words are flyspelled.
Returns t to continue checking, nil otherwise.
Flyspell mode sets this variable to whatever is the `flyspell-mode-predicate'
property of the major mode name."
  ;; Emacs 24 uses `font-lock-fontify-buffer'.
  (if (fboundp 'font-lock-ensure) (font-lock-ensure)
    (font-lock-fontify-buffer))

  (let* ((case-fold-search nil)
         (pos (- (point) 1))
         (current-font-face (and (> pos 0) (get-text-property pos 'face)))
         (font-matched (or (memq current-font-face wucuo-font-faces-to-check)
                           (memq current-font-face wucuo-personal-font-faces-to-check)
                           (and wucuo-check-nil-font-face (eq current-font-face nil))))
         subwords
         word
         (rlt t))

    (when wucuo-debug (message "font-matched=%s, current-font-face=%s" font-matched current-font-face))
    (cond
     ((<= pos 0)
      nil)
     ;; only check word with certain fonts
     ((not font-matched)
      (setq rlt nil))

     ;; ignore two character word, some major mode word equals to sub-word
     ((< (length (setq word (thing-at-point 'symbol))) 2)
      (setq rlt nil))

     ;; handle camel case word
     ((and (setq subwords (wucuo-split-camel-case word)) (> (length subwords) 1))
      (let* ((s (mapconcat #'wucuo-handle-sub-word subwords " ")))
        (setq rlt (wucuo-check-camel-case-word-predicate s))))

     ;; `wucuo-extra-predicate' actually do nothing by default
     (t
      (setq rlt (funcall wucuo-extra-predicate word))))

    (when wucuo-debug (message "wucuo-generic-check-word-predicate => word=%s rlt=%s wucuo-extra-predicate=%s subwords=%s" word rlt wucuo-extra-predicate subwords))
    rlt))

;;;###autoload
(defun wucuo-create-aspell-personal-dictionary ()
  "Create aspell personal dictionary."
  (interactive)
  (with-temp-buffer
    (let* ((file (file-truename (format "~/.aspell.%s.pws" wucuo-aspell-language-to-use))))
      (insert (format "personal_ws-1.1 %s 2\nabcd\ndefg\n" wucuo-aspell-language-to-use))
      (write-file file)
      (message "%s created." file))))

;;;###autoload
(defun wucuo-create-hunspell-personal-dictionary ()
  "Create hunspell personal dictionary."
  (interactive)
  (with-temp-buffer
    (let* ((file (file-truename (format "~/.hunspell_%s" wucuo-hunspell-dictionary-base-name))))
      (insert "abcd\ndefg\n")
      (write-file file)
      (message "%s created." file))))

;;;###autoload
(defun wucuo-version ()
  "Output version."
  (message "0.0.6"))

;;;###autoload
(defun wucuo-setup-major-mode (mode)
  "Set up MODE's flyspell predicate."
  (if (stringp mode) (setq mode (symobol mode)))
  (eval-after-load mode
    (progn
      (put mode
           'flyspell-mode-predicate
           'wucuo-generic-check-word-predicate))))

;;;###autoload
(defun wucuo-start (&optional force)
  "Turn on wucuo to spell check code.
If FORCE is t, the major mode's own predicate setup."
  (interactive)
  (when force
    (dolist (mode wucuo-major-modes-to-setup-by-force)
      (wucuo-setup-major-mode mode)))

  ;; setup flyspell if the major mode does not have per its own flyspell setup.
  ;; to be honest, no other major mode can do better than this program
  (setq flyspell-generic-check-word-predicate
        #'wucuo-generic-check-word-predicate)

  (when wucuo-auto-turn-on-flyspell
    (flyspell-mode 1)))

(provide 'wucuo)
;;; wucuo.el ends here
