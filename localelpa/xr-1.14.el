;;; xr.el --- Convert string regexp to rx notation   -*- lexical-binding: t -*-

;; Copyright (C) 2019 Free Software Foundation, Inc.

;; Author: Mattias Engdegård <mattiase@acm.org>
;; Version: 1.14
;; URL: https://github.com/mattiase/xr
;; Keywords: lisp, maint, regexps

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is an inverse companion to the rx package for translating
;; regexps in string form to the rx notation.  Its chief uses are:
;;
;; - Migrating existing code to rx form, for better readability and
;;   maintainability
;; - Understanding complex regexp strings and finding errors in them
;;   
;; Please refer to `rx' for more information about the notation.
;;
;; In addition to Emacs regexps, this package can also parse and
;; find mistakes in skip set strings, which are arguments to
;; `skip-chars-forward' and `skip-chars-backward'.
;;
;; The exported functions are:
;;
;;  Regexps:
;;  `xr'               - returns the converted rx expression
;;  `xr-pp'            - converts to rx and pretty-prints
;;  `xr-lint'          - finds mistakes in a regexp string
;;
;;  Skip sets:
;;  `xr-skip-set'      - return the converted rx expression
;;  `xr-skip-set-pp'   - converts to rx and pretty-prints
;;  `xr-skip-set-lint' - finds mistakes in a skip set string
;;
;;  General:
;;  `xr-pp-rx-to-str'  - pretty-prints an rx expression to a string
;;
;; Example (regexp found in compile.el):
;;
;;   (xr-pp "\\`\\(?:[^^]\\|\\^\\(?: \\*\\|\\[\\)\\)")
;; =>
;;   (seq bos
;;        (or (not (any "^"))
;;            (seq "^"
;;                 (or " *" "["))))
;;
;; The rx notation admits many synonyms. The user is encouraged to
;; edit the result for maximum readability, consistency and personal
;; preference when replacing existing regexps in elisp code.
;;
;; Related work:
;;
;; The `lex' package, a lexical analyser generator, provides the
;; `lex-parse-re' function which translates regexps to rx, but does
;; not attempt to handle all the edge cases of Elisp's regexp syntax
;; or pretty-print the result.
;;
;; The `pcre2el' package, a regexp syntax converter and interactive
;; regexp explainer, could also be used for translating regexps to rx.
;; `xr' is narrower in scope but more accurate for the purpose of
;; parsing Emacs regexps and printing the results in rx form.
;;
;; Neither of these packages parse skip-set strings or provide
;; mistake-finding functions.

;;; News:

;; Version 1.14:
;; - Warn about repetition of grouped repetition
;; Version 1.13:
;; - More robust pretty-printing, especially for characters
;; - Generate (category CHAR) for unknown categories
;; Version 1.12:
;; - Warn about branch subsumption, like [AB]\|A
;; Version 1.11:
;; - Warn about repetition of empty-matching expressions
;; - Detect `-' not first or last in char alternatives or skip-sets
;; - Stronger ad-hoc [...] check in skip-sets
;; Version 1.10:
;; - Warn about [[:class:]] in skip-sets
;; - Warn about two-character ranges like [*-+] in regexps
;; Version 1.9:
;; - Don't complain about [z-a] and [^z-a] specifically
;; - Improved skip set checks
;; Version 1.8:
;; - Improved skip set checks
;; Version 1.7:
;; - Parse skip-sets, adding `xr-skip-set', `xr-skip-set-pp' and
;;   `xr-skip-set-lint'
;; - Ad-hoc check for misplaced `]' in regexps
;; Version 1.6:
;; - Detect duplicated branches like A\|A
;; Version 1.5:
;; - Add dialect option to `xr' and `xr-pp'
;; - Negative empty sets, [^z-a], now become `anything'
;; Version 1.4:
;; - Detect overlap in character alternatives
;; Version 1.3:
;; - Improved xr-lint warnings
;; Version 1.2:
;; - `xr-lint' added

;;; Code:

(require 'rx)
(require 'cl-lib)

(defun xr--report (warnings position message)
  "Add the report MESSAGE at POSITION to WARNINGS."
  (when warnings
    (push (cons (1- position) message) (car warnings))))

(defun xr--parse-char-alt (negated warnings)
  (let ((start-pos (point))
        (intervals nil)
        (classes nil))
    (cond
     ;; Initial ]-x range
     ((looking-at (rx "]-" (not (any "]"))))
      (let ((end (aref (match-string 0) 2)))
        (if (>= end ?\])
            (push (vector ?\] end (point)) intervals)
          (xr--report warnings (point)
                      (format "Reversed range `%s' matches nothing"
                              (xr--escape-string (match-string 0) nil))))
        (when (eq end ?^)
          (xr--report warnings (point)
                      (format "Two-character range `%s'"
                              (xr--escape-string (match-string 0) nil)))))
      (goto-char (match-end 0)))
     ;; Initial ]
     ((looking-at "]")
      (push (vector ?\] ?\] (point)) intervals)
      (forward-char 1)))

    (while (not (looking-at "]"))
      (cond
       ;; character class
       ((looking-at (rx "[:" (group (*? anything)) ":]"))
        (let ((sym (intern (match-string 1))))
          (unless (memq sym
                        '(ascii alnum alpha blank cntrl digit graph
                          lower multibyte nonascii print punct space
                          unibyte upper word xdigit))
            (error "No character class `%s'" (match-string 0)))
          (if (memq sym classes)
              (xr--report warnings (point)
                          (format "Duplicated character class `[:%s:]'" sym))
            (push sym classes))
          (goto-char (match-end 0))))
       ;; character range
       ((looking-at (rx (group (not (any "]"))) "-" (group (not (any "]")))))
        (let ((start (string-to-char (match-string 1)))
              (end   (string-to-char (match-string 2))))
          (cond
           ((<= start end)
            (push (vector start end (point)) intervals))
           ;; It's unlikely that anyone writes z-a by mistake; don't complain.
           ((and (eq start ?z) (eq end ?a)))
           (t
            (xr--report warnings (point)
                        (format "Reversed range `%s' matches nothing"
                                (xr--escape-string (match-string 0) nil)))))
          ;; Suppress warnings about ranges between adjacent digits,
          ;; like [0-1], as they are common and harmless.
          (when (and (= end (1+ start)) (not (<= ?0 start end ?9)))
            (xr--report warnings (point)
                        (format "Two-character range `%s'"
                                (xr--escape-string (match-string 0) nil))))
          (goto-char (match-end 0))))
       ((looking-at (rx eos))
        (error "Unterminated character alternative"))
       ;; plain character (including ^ or -)
       (t
        (let ((ch (following-char)))
          (when (and (eq ch ?\[)
                     ;; Ad-hoc pattern attempting to catch mistakes
                     ;; on the form [...[...]...]
                     ;; where we are    ^here
                     (looking-at (rx "["
                                     (zero-or-more (not (any "[]")))
                                     "]"
                                     (zero-or-more (not (any "[]")))
                                     (not (any "[\\"))
                                     "]"))
                     ;; Only if the alternative didn't start with ]
                     (not (and intervals
                               (eq (aref (car (last intervals)) 0) ?\]))))
            (xr--report warnings (point)
                        "Suspect `[' in char alternative"))
          (when (and (looking-at (rx "-" (not (any "]"))))
                     (> (point) start-pos))
            (xr--report
             warnings (point)
             "Literal `-' not first or last in character alternative"))
          (push (vector ch ch (point)) intervals))
        (forward-char 1))))

    (forward-char 1)                    ; eat the ]

    ;; Detect duplicates and overlapping intervals.
    (let* ((sorted
            (sort (nreverse intervals)
                  (lambda (a b) (< (aref a 0) (aref b 0)))))
           (s sorted))
      (while (cdr s)
        (let ((this (car s))
              (next (cadr s)))
          (when (>= (aref this 1) (aref next 0))
            (let ((message
                   (cond
                    ;; Duplicate character: drop it and warn.
                    ((and (eq (aref this 0) (aref this 1))
                          (eq (aref next 0) (aref next 1)))
                     (setcdr s (cddr s))
                     (format "Duplicated `%c' inside character alternative"
                             (aref this 0)))
                    ;; Duplicate range: drop it and warn.
                    ((and (eq (aref this 0) (aref next 0))
                          (eq (aref this 1) (aref next 1)))
                     (setcdr s (cddr s))
                     (format "Duplicated `%c-%c' inside character alternative"
                             (aref this 0) (aref this 1)))
                    ;; Character in range: drop it and warn.
                    ((eq (aref this 0) (aref this 1))
                     (setcar s next)
                     (setcdr s (cddr s))
                     (format "Character `%c' included in range `%c-%c'"
                             (aref this 0) (aref next 0) (aref next 1)))
                    ;; Same but other way around.
                    ((eq (aref next 0) (aref next 1))
                     (setcdr s (cddr s))
                     (format "Character `%c' included in range `%c-%c'"
                             (aref next 0) (aref this 0) (aref this 1)))
                    ;; Overlapping ranges: merge and warn.
                    (t
                     (let ((this-end (aref this 1)))
                       (aset this 1 (max (aref this 1) (aref next 1)))
                       (setcdr s (cddr s))
                       (format "Ranges `%c-%c' and `%c-%c' overlap"
                               (aref this 0) this-end
                               (aref next 0) (aref next 1)))))))
              (xr--report warnings (max (aref this 2) (aref next 2))
                          (xr--escape-string message nil)))))
        (setq s (cdr s)))
            
      ;; Gather ranges and single characters separately.
      ;; We make no attempts at merging adjacent intervals/characters,
      ;; nor at splitting short intervals such as "a-b"; if the user
      ;; wrote it that way, there was probably a reason for it.
      (let ((ranges nil)
            (chars nil))
        (dolist (interv sorted)
          (if (eq (aref interv 0) (aref interv 1))
              (push (aref interv 0) chars)
            (push (string (aref interv 0) ?- (aref interv 1))
                  ranges)))
        
        ;; Note that we return (any) for non-negated empty sets,
        ;; such as [z-a]. (any) is not accepted by rx but at least we
        ;; are not hiding potential bugs from the user.
        (cond
         ;; Negated empty set, like [^z-a]: anything.
         ((and negated
               (null chars)
               (null ranges)
               (null classes))
          'anything)
         ;; Non-negated single-char set, like [$]: make a string.
         ((and (= (length chars) 1)
               (not negated)
               (null ranges)
               (null classes))
          (string (car chars)))
         ;; Single named class, like [[:space:]]: use the symbol.
         ((and (= (length classes) 1)
               (null chars)
               (null ranges))
          (if negated
              (list 'not (car classes))
            (car classes)))
         ;; Anything else: produce (any ...)
         (t
          ;; Put dash last of all single characters.
          (when (memq ?- chars)
            (setq chars (cons ?- (delq ?- chars))))
          (let* ((set (cons 'any
                            (append
                             (and ranges
                                  (list (apply #'concat (nreverse ranges))))
                             (and chars
                                  (list (apply #'string (nreverse chars))))
                             (nreverse classes)))))
            (if negated
                (list 'not set)
              set))))))))

(defun xr--rev-join-seq (sequence)
  "Reverse a sequence, flatten any (seq ...) inside, and concatenate
adjacent strings."
  (let ((result nil))
    (while sequence
      (let ((elem (car sequence))
            (rest (cdr sequence)))
        (cond ((and (consp elem) (eq (car elem) 'seq))
               (setq sequence (append (reverse (cdr elem)) rest)))
              ((and (stringp elem) (stringp (car result)))
               (setq result (cons (concat elem (car result)) (cdr result)))
               (setq sequence rest))
              (t
               (setq result (cons elem result))
               (setq sequence rest)))))
    result))

(defun xr--char-category (negated category-code)
  (let* ((sym (assq category-code
                    '((?\s . space-for-indent)
                      (?. . base)
                      (?0 . consonant)
                      (?1 . base-vowel)                        
                      (?2 . upper-diacritical-mark)            
                      (?3 . lower-diacritical-mark)            
                      (?4 . tone-mark)                 
                      (?5 . symbol)                            
                      (?6 . digit)                             
                      (?7 . vowel-modifying-diacritical-mark)  
                      (?8 . vowel-sign)                        
                      (?9 . semivowel-lower)                   
                      (?< . not-at-end-of-line)                
                      (?> . not-at-beginning-of-line)          
                      (?A . alpha-numeric-two-byte)            
                      (?C . chinese-two-byte)                  
                      (?G . greek-two-byte)                    
                      (?H . japanese-hiragana-two-byte)        
                      (?I . indian-two-byte)                   
                      (?K . japanese-katakana-two-byte)        
                      (?L . strong-left-to-right)
                      (?N . korean-hangul-two-byte)            
                      (?R . strong-right-to-left)
                      (?Y . cyrillic-two-byte)         
                      (?^ . combining-diacritic)               
                      (?a . ascii)                             
                      (?b . arabic)                            
                      (?c . chinese)                           
                      (?e . ethiopic)                          
                      (?g . greek)                             
                      (?h . korean)                            
                      (?i . indian)                            
                      (?j . japanese)                          
                      (?k . japanese-katakana)         
                      (?l . latin)                             
                      (?o . lao)                               
                      (?q . tibetan)                           
                      (?r . japanese-roman)                    
                      (?t . thai)                              
                      (?v . vietnamese)                        
                      (?w . hebrew)                            
                      (?y . cyrillic)                          
                      (?| . can-break))))
         (item (list 'category (if sym (cdr sym) category-code))))
    (if negated (list 'not item) item)))

(defun xr--char-syntax (negated syntax-code)
  (let ((sym (assq syntax-code
                   '((?-  . whitespace)
                     (?\s . whitespace)
                     (?.  . punctuation)
                     (?w  . word)
                     (?W  . word)       ; undocumented
                     (?_  . symbol)
                     (?\( . open-parenthesis)
                     (?\) . close-parenthesis)
                     (?'  . expression-prefix)
                     (?\" . string-quote)
                     (?$  . paired-delimiter)
                     (?\\ . escape)
                     (?/  . character-quote)
                     (?<  . comment-start)
                     (?>  . comment-end)
                     (?|  . string-delimiter)
                     (?!  . comment-delimiter)))))
    (when (not sym)
      (error "Unknown syntax code `%s'"
             (xr--escape-string (char-to-string syntax-code) nil)))
    (let ((item (list 'syntax (cdr sym))))
      (if negated (list 'not item) item))))

(defun xr--postfix (operator operand)
  ;; We use verbose names for the common *, + and ? operators for readability,
  ;; even though these names are affected by the rx-greedy-flag.
  ;; For the (less common) non-greedy operators we might want to
  ;; consider using minimal-match/maximal-match instead, but
  ;; this would complicate the implementation.
  (let* ((sym (cdr (assoc operator '(("*"  . zero-or-more)
                                     ("+"  . one-or-more)
                                     ("?"  . opt)
                                     ("*?" . *?)
                                     ("+?" . +?)
                                     ("??" . ??)))))
         ;; Simplify when the operand is (seq ...)
         (body (if (and (listp operand) (eq (car operand) 'seq))
                   (cdr operand)
                 (list operand))))
    (cons sym body)))

(defun xr--repeat (lower upper operand)
  "Apply a repetition of {LOWER,UPPER} to OPERAND.
UPPER may be nil, meaning infinity."
  (when (and upper (> lower upper))
    (error "Invalid repetition interval"))
  ;; rx does not accept (= 0 ...) or (>= 0 ...), so we use 
  ;; (repeat 0 0 ...) and (zero-or-more ...), respectively.
  ;; Note that we cannot just delete the operand if LOWER=UPPER=0,
  ;; since doing so may upset the group numbering.
  (let* ((operator (cond ((null upper)
                          (if (zerop lower)
                              '(zero-or-more)
                            (list '>= lower)))
                         ((and (= lower upper) (> lower 0))
                          (list '= lower))
                         (t
                          (list 'repeat lower upper))))
         ;; Simplify when the operand is (seq ...).
         (body (if (and (listp operand) (eq (car operand) 'seq))
                   (cdr operand)
                 (list operand))))
    (append operator body)))
  
(defconst xr--zero-width-assertions
  '(bol eol bos eos bow eow word-boundary not-word-boundary
    symbol-start symbol-end point))

(defun xr--matches-empty-p (rx)
  "Whether RX can match the empty string regardless of context."
  (pcase rx
    (`(,(or 'seq 'one-or-more 'group) . ,body)
     (cl-every #'xr--matches-empty-p body))
    (`(or . ,body)
     (cl-some #'xr--matches-empty-p body))
    (`(group-n ,_ . ,body)
     (cl-every #'xr--matches-empty-p body))
    (`(,(or 'opt 'zero-or-more) . ,_)
     t)
    (`(repeat ,from ,_ . ,body)
     (or (= from 0)
         (cl-every #'xr--matches-empty-p body)))
    (`(,(or '= '>=) ,_ . ,body)
     (cl-every #'xr--matches-empty-p body))
    ("" t)))

(defun xr--parse-seq (warnings)
  (let ((sequence nil))                 ; reversed
    (while (not (looking-at (rx (or "\\|" "\\)" eos))))
      (cond
       ;; ^ - only special at beginning of sequence
       ((looking-at (rx "^"))
        (forward-char 1)
        (if (null sequence)
            (push 'bol sequence)
          (xr--report warnings (match-beginning 0) "Unescaped literal `^'")
          (push "^" sequence)))

       ;; $ - only special at end of sequence
       ((looking-at (rx "$"))
        (forward-char 1)
        (if (looking-at (rx (or "\\|" "\\)" eos)))
            (push 'eol sequence)
          (xr--report warnings (match-beginning 0) "Unescaped literal `$'")
          (push "$" sequence)))

       ;; * ? + (and non-greedy variants)
       ;; - not special at beginning of sequence or after ^
       ((looking-at (rx (group (any "*?+")) (opt "?")))
        (if (and sequence
                 (not (and (eq (car sequence) 'bol) (eq (preceding-char) ?^))))
            (let ((operator (match-string 0))
                  (operand (car sequence)))
              (when warnings
                (cond
                 ;; (* (* X)), for any repetitions *
                 ((and (consp operand)
                       (memq (car operand)
                             '(opt zero-or-more one-or-more +? *? ??)))
                  (xr--report warnings (match-beginning 0)
                              "Repetition of repetition"))
                 ;; (* (group (* X))), for any repetitions *
                 ((and (consp operand)
                       (eq (car operand) 'group)
                       (null (cddr operand))
                       (let ((inner (cadr operand)))
                         (and (consp inner)
                              (memq (car inner)
                                    '(opt zero-or-more one-or-more +? *? ??))
                              ;; Except (? (group (+ X))), since that may
                              ;; be legitimate.
                              (not (and (equal operator "?")
                                        (memq (car inner)
                                              '(one-or-more +?)))))))
                  (xr--report warnings (match-beginning 0)
                              "Repetition of repetition"))
                 ((memq operand xr--zero-width-assertions)
                  (xr--report warnings (match-beginning 0)
                              "Repetition of zero-width assertion"))
                 ((and (xr--matches-empty-p operand)
                       ;; Rejecting repetition of the empty string
                       ;; suppresses some false positives.
                       (not (equal operand "")))
                  (xr--report
                   warnings (match-beginning 0)
                   "Repetition of expression matching an empty string"))))
              (goto-char (match-end 0))
              (setq sequence (cons (xr--postfix operator operand)
                                   (cdr sequence))))
          (let ((literal (match-string 1)))
            (goto-char (match-end 1))
            (xr--report warnings (match-beginning 0)
                        (format "Unescaped literal `%s'" literal))
            (push literal sequence))))

       ;; \{..\} - not special at beginning of sequence or after ^
       ((and (looking-at (rx "\\{"))
             sequence
             (not (and (eq (car sequence) 'bol) (eq (preceding-char) ?^))))
        (forward-char 2)
        (let ((operand (car sequence)))
          (when warnings
            (cond
             ;; (** N M (* X)), for any repetition *
             ((and (consp operand)
                   (memq (car operand)
                         '(opt zero-or-more one-or-more +? *? ??)))
              (xr--report warnings (match-beginning 0)
                          "Repetition of repetition"))
             ;; (** N M (group (* X))), for any repetition *
             ((and (consp operand)
                   (eq (car operand) 'group)
                   (null (cddr operand))
                   (let ((inner (cadr operand)))
                     (and (consp inner)
                          (memq (car inner)
                                '(opt zero-or-more one-or-more +? *? ??)))))
              (xr--report warnings (match-beginning 0)
                          "Repetition of repetition"))
             ((memq operand xr--zero-width-assertions)
              (xr--report warnings (match-beginning 0)
                          "Repetition of zero-width assertion"))
             ((and (xr--matches-empty-p operand)
                   ;; Rejecting repetition of the empty string
                   ;; suppresses some false positives.
                   (not (equal operand "")))
              (xr--report
               warnings (match-beginning 0)
               "Repetition of expression matching an empty string"))))
          (if (looking-at (rx (opt (group (one-or-more digit)))
                              (opt (group ",")
                                   (opt (group (one-or-more digit))))
                              "\\}"))
              (let ((lower (if (match-string 1)
                               (string-to-number (match-string 1))
                             0))
                    (comma (match-string 2))
                    (upper (and (match-string 3)
                                (string-to-number (match-string 3)))))
                (unless (or (match-beginning 1) (match-string 3))
                  (xr--report warnings (- (match-beginning 0) 2)
                              (if comma
                                  "Uncounted repetition"
                                "Implicit zero repetition")))
                (goto-char (match-end 0))
                (setq sequence (cons (xr--repeat lower
                                                 (if comma upper lower)
                                                 operand)
                                     (cdr sequence))))
            (error "Invalid \\{\\} syntax"))))

       ;; nonspecial character
       ((looking-at (rx (not (any "\\.["))))
        (forward-char 1)
        (push (match-string 0) sequence))

       ;; character alternative
       ((looking-at (rx "[" (opt (group "^"))))
        (goto-char (match-end 0))
        (let ((negated (match-string 1)))
          (push (xr--parse-char-alt negated warnings) sequence)))

       ;; group
       ((looking-at (rx "\\(" (opt (group "?")
                                   (opt (opt (group (any "1-9")
                                                    (zero-or-more digit)))
                                        (group ":")))))
        (let ((question (match-string 1))
              (number (match-string 2))
              (colon (match-string 3)))
          (when (and question (not colon))
            (error "Invalid \\(? syntax"))
          (goto-char (match-end 0))
          (let* ((group (xr--parse-alt warnings))
                 ;; simplify - group has an implicit seq
                 (operand (if (and (listp group) (eq (car group) 'seq))
                              (cdr group)
                            (list group))))
            (when (not (looking-at (rx "\\)")))
              (error "Missing \\)"))
            (forward-char 2)
            (let ((item (cond (number   ; numbered group
                               (append (list 'group-n (string-to-number number))
                                       operand))
                              (question ; shy group
                               group)
                              (t        ; plain group
                               (cons 'group operand)))))
              (push item sequence)))))

       ;; back-reference
       ((looking-at (rx "\\" (group (any "1-9"))))
        (forward-char 2)
        (push (list 'backref (string-to-number (match-string 1)))
              sequence))

       ;; various simple substitutions
       ((looking-at (rx (or "." "\\w" "\\W" "\\`" "\\'" "\\="
                            "\\b" "\\B" "\\<" "\\>")))
        (goto-char (match-end 0))
        (let ((sym (cdr (assoc
                         (match-string 0)
                         '(("." . nonl)
                           ("\\w" . wordchar) ("\\W" . not-wordchar)
                           ("\\`" . bos) ("\\'" . eos)
                           ("\\=" . point)
                           ("\\b" . word-boundary) ("\\B" . not-word-boundary)
                           ("\\<" . bow) ("\\>" . eow))))))
          (push sym sequence)))

       ;; symbol-start, symbol-end
       ((looking-at (rx "\\_" (opt (group (any "<>")))))
        (let ((arg (match-string 1)))
          (unless arg
            (error "Invalid \\_ sequence"))
          (forward-char 3)
          (push (if (string-equal arg "<") 'symbol-start 'symbol-end)
                sequence)))

       ;; character syntax
       ((looking-at (rx "\\" (group (any "sS")) (opt (group anything))))
        (let ((negated (string-equal (match-string 1) "S"))
              (syntax-code (match-string 2)))
          (unless syntax-code
            (error "Incomplete \\%s sequence" (match-string 1)))
          (goto-char (match-end 0))
          (push (xr--char-syntax negated (string-to-char syntax-code))
                sequence)))

       ;; character categories
       ((looking-at (rx "\\" (group (any "cC")) (opt (group anything))))
        (let ((negated (string-equal (match-string 1) "C"))
              (category-code (match-string 2)))
          (unless category-code
            (error "Incomplete \\%s sequence" (match-string 1)))
          (goto-char (match-end 0))
          (push (xr--char-category negated (string-to-char category-code))
                sequence)))

       ;; Escaped character. Only \*+?.^$[ really need escaping, but we accept
       ;; any not otherwise handled character after the backslash since
       ;; such sequences are found in the wild.
       ((looking-at (rx "\\" (group (or (any "\\*+?.^$[]")
                                        (group anything)))))
        (forward-char 2)
        (push (match-string 1) sequence)
        (when (match-beginning 2)
          ;; Note that we do not warn about \\], since the symmetry with \\[
          ;; makes it unlikely to be a serious error.
          (xr--report warnings (match-beginning 0)
                      (format "Escaped non-special character `%s'"
                              (xr--escape-string (match-string 2) nil)))))

       (t (error "Backslash at end of regexp"))))

    (let ((item-seq (xr--rev-join-seq sequence)))
      (cond ((null item-seq)
             "")
            ((null (cdr item-seq))
             (car item-seq))
            (t 
             (cons 'seq item-seq))))))

(defun xr--range-string-to-items (str)
  "Convert a string of ranges to a list of pairs of their endpoints."
  (let ((len (length str))
        (ranges nil)
        (i 0))
    (while (< i len)
      (push (cons (aref str i) (aref str (+ i 2)))
            ranges)
      (setq i (+ i 3)))
    ranges))

(defun xr--any-arg-to-items (arg)
  "Convert an `any' argument to a list of characters, ranges (as pairs),
and classes (symbols)."
  ;; We know (since we built it) that x is either a symbol or
  ;; a string, and that the string does not mix ranges and chars.
  (cond ((symbolp arg) (list arg))
        ((and (>= (length arg) 3)
              (eq (aref arg 1) ?-))
         (xr--range-string-to-items arg))
        (t (string-to-list arg))))

(defun xr--any-item-superset-p (a b)
  "Whether A is a superset of B, both being `any' items: a character,
a range (pair of chars), or a class (symbol)."
  (cond
   ((symbolp a)
    (cond ((symbolp b) (eq a b))
          ((eq b ?\n)
           (memq a '(alnum alpha blank digit graph
                     lower multibyte nonascii print punct space
                     upper word xdigit)))))
   ((consp a)
    (or (and (characterp b)
             (<= (car a) b (cdr a)))
        (and (consp b)
             (<= (car a) (car b) (cdr b) (cdr a)))))
   (t
    (and (characterp b) (eq a b)))))

(defun xr--any-item-may-intersect-p (a b)
  "Whether A intersects B, both being `any' items: a character,
a range (pair of chars), or a class (symbol). If in doubt, return t."
  (cond
   ((symbolp a)
    (cond ((eq b ?\n)
           (not (memq a '(alnum alpha blank digit graph
                          lower multibyte nonascii print punct space
                          upper word xdigit))))
          (t t)))
   ((consp a)
    (or (and (characterp b)
             (<= (car a) b (cdr a)))
        (and (consp b)
             (<= (car a) (cdr b))
             (<= (car b) (cdr a)))
        (symbolp b)))
   ;; Now a must be a character.
   ((characterp b) (eq a b))
   (t (xr--any-item-may-intersect-p b a))))

(defun xr--char-superset-of-char-set-p (a-sets negated b-sets)
  "Whether A-SETS, possibly NEGATED, is a superset of B-SETS.
A-SETS and B-SETS are arguments to `any'."
  (let ((a-items (mapcan #'xr--any-arg-to-items a-sets))
        (b-items (mapcan #'xr--any-arg-to-items b-sets)))
    (cl-every (lambda (b-item)
                (if negated
                    (not (cl-some
                          (lambda (a-item)
                            (xr--any-item-may-intersect-p b-item a-item))
                          a-items))
                  (cl-some (lambda (a-item)
                             (xr--any-item-superset-p a-item b-item))
                           a-items)))
              b-items)))

(defun xr--char-superset-of-rx-p (sets negated rx)
  "Whether SETS, possibly NEGATED, is a superset of RX."
  (pcase rx
    (`(any . ,b-sets)
     (xr--char-superset-of-char-set-p sets negated b-sets))
    (`(not (any . ,b-sets))
     (and negated
          (xr--char-superset-of-char-set-p b-sets nil sets)))
    ((or 'ascii 'alnum 'alpha 'blank 'cntrl 'digit 'graph
         'lower 'multibyte 'nonascii 'print 'punct 'space
         'unibyte 'upper 'word 'xdigit)
     (xr--char-superset-of-char-set-p sets negated `(any ,rx)))
    ((pred stringp)
     (and (= (length rx) 1)
          (xr--char-superset-of-char-set-p sets negated (list rx))))))

(defun xr--single-non-newline-char-p (rx)
  "Whether RX only matches single characters none of which is newline."
  (pcase rx
    ((or 'nonl 'wordchar) t)
    (`(category ,_) t)
    (`(syntax ,s) (not (eq s ?>)))      ; comment-end often matches newline
    (_ (xr--char-superset-of-rx-p '("\n") t rx))))

(defun xr--syntax-superset-of-rx-p (syntax negated rx)
  "Whether SYNTAX, possibly NEGATED, is a superset of RX."
  ;; Syntax tables vary, but we make a (quite conservative) guess.
  (let* ((always-set
           ;; Characters we think always will be in the syntax set.
           '((whitespace " \t")
             (word "A-Za-z0-9")
             (open-parenthesis "([")
             (close-parenthesis "])")))
         (never-set
           ;; Characters we think never will be in the syntax set.
           '((whitespace "!-~")
             (punctuation "A-Za-z0-9")
             (open-parenthesis "\x00- A-Za-z0-9")
             (close-parenthesis "\x00- A-Za-z0-9")))
         (set (assq syntax (if negated never-set always-set))))
    (and set
         (xr--char-superset-of-rx-p (cdr set) nil rx))))

(defun xr--string-to-chars (str)
  (mapcar #'char-to-string (string-to-list str)))

(defun xr--expand-strings (rx)
  "If RX is a string or a seq of strings, convert them to seqs of
single-character strings."
  (cond ((consp rx)
         (if (eq (car rx) 'seq)
             (cons 'seq (mapcan (lambda (x)
                                  (if (and (stringp x)
                                           (> (length x) 1))
                                      (xr--string-to-chars x)
                                    (list x)))
                                (cdr rx)))
           rx))
        ((and (stringp rx)
              (> (length rx) 1))
         (cons 'seq (xr--string-to-chars rx)))
        (t rx)))

(defun xr--superset-seq-p (a b)
  "Whether A matches all that B matches, both lists of expressions."
  (while (and a b (xr--superset-p (car a) (car b)))
    (setq a (cdr a))
    (setq b (cdr b)))
  (and (not b)
       (or (not a)
           (xr--matches-empty-p (cons 'seq a)))))

(defun xr--make-seq (body)
  (if (> (length body) 1)
      (cons 'seq body)
    (car body)))

(defun xr--superset-p (a b)
  "Whether A matches all that B matches."
  (setq a (xr--expand-strings a))
  (setq b (xr--expand-strings b))

  (pcase b
    (`(or . ,b-body)
     (cl-every (lambda (b-expr) (xr--superset-p a b-expr)) b-body))
    (_
     (pcase a
       (`(any . ,sets)
        (xr--char-superset-of-rx-p sets nil b))
       (`(not (any . ,sets))
        (xr--char-superset-of-rx-p sets t b))
       ('nonl (xr--single-non-newline-char-p b))

       (`(seq . ,a-body)
        (pcase b
          (`(seq . ,b-body)
           (xr--superset-seq-p a-body b-body))
          (_
           (xr--superset-seq-p a-body (list b)))))
       (`(or . ,a-body)
        (cl-some (lambda (a-expr) (xr--superset-p a-expr b)) a-body))

       (`(zero-or-more . ,a-body)
        (pcase b
          (`(,(or 'opt 'zero-or-more 'one-or-more) . ,b-body)
           (xr--superset-p (xr--make-seq a-body) (xr--make-seq b-body)))
          (_ (xr--superset-p (xr--make-seq a-body) b))))
       (`(one-or-more . ,a-body)
        (pcase b
          (`(one-or-more . ,b-body)
           (xr--superset-p (xr--make-seq a-body) (xr--make-seq b-body)))
          (_ (xr--superset-p (xr--make-seq a-body) b))))
       (`(opt . ,a-body)
        (pcase b
          (`(opt . ,b-body)
           (xr--superset-p (xr--make-seq a-body) (xr--make-seq b-body)))
          (_ (xr--superset-p (xr--make-seq a-body) b))))
       (`(repeat ,lo ,_ . ,a-body)
        (if (<= lo 1)
            (xr--superset-p (xr--make-seq a-body) b)
          (equal a b)))
       
       ;; We do not expand through groups on the subset (b) side to
       ;; avoid false positives; "\\(a\\)\\|." should be without warning.
       (`(group . ,body)
        (xr--superset-p (xr--make-seq body) b))
       (`(group-n ,_ . ,body)
        (xr--superset-p (xr--make-seq body) b))

       (`(syntax ,syn)
        (or (equal a b) (xr--syntax-superset-of-rx-p syn nil b)))
       (`(not (syntax ,syn))
        (or (equal a b) (xr--syntax-superset-of-rx-p syn t b)))

       ((or `(category ,_) `(not (category ,_)))
        (or (equal a b)
            (and (stringp b)
                 (string-match-p (rx-to-string a) b))))

       (_ (equal a b))))))

(defun xr--parse-alt (warnings)
  (let ((alternatives nil))             ; reversed
    (push (xr--parse-seq warnings) alternatives)
    (while (not (looking-at (rx (or "\\)" eos))))
      (forward-char 2)                  ; skip \|
      (let ((pos (point))
            (seq (xr--parse-seq warnings)))
        (when warnings
          (cond
           ((member seq alternatives)
            (xr--report warnings pos "Duplicated alternative branch"))
           ((cl-some (lambda (branch) (xr--superset-p seq branch))
                     alternatives)
            (xr--report warnings pos
                        "Branch matches superset of a previous branch"))
           ((cl-some (lambda (branch) (xr--superset-p branch seq))
                     alternatives)
            (xr--report warnings pos
                        "Branch matches subset of a previous branch"))))
        (push seq alternatives)))
    (if (cdr alternatives)
        ;; Simplify (or nonl "\n") to anything
        (if (or (equal alternatives '(nonl "\n"))
                (equal alternatives '("\n" nonl)))
            'anything
          (cons 'or (reverse alternatives)))
      (car alternatives))))

(defun xr--parse (re-string warnings)
  (with-temp-buffer
    (set-buffer-multibyte t)
    (insert re-string)
    (goto-char (point-min))
    (let* ((case-fold-search nil)
           (rx (xr--parse-alt warnings)))
      (when (looking-at (rx "\\)"))
        (error "Unbalanced \\)"))
      rx)))

;; Grammar for skip-set strings:
;;
;; skip-set ::= `^'? item* dangling?
;; item     ::= range | single
;; range    ::= single `-' endpoint
;; single   ::= {any char but `\'}
;;            | `\' {any char}
;; endpoint ::= single | `\'
;; dangling ::= `\'
;;
;; Ambiguities in the above are resolved greedily left-to-right.

(defun xr--parse-skip-set-buffer (warnings)

  ;; An ad-hoc check, but one that catches lots of mistakes.
  (when (and (looking-at (rx "[" (one-or-more anything) "]"
                             (opt (any "+" "*" "?")
                                  (opt "?"))
                             eos))
             (not (looking-at (rx "[:" (one-or-more anything) ":]" eos))))
    (xr--report warnings (point) "Suspect skip set framed in `[...]'"))

  (let ((negated (looking-at (rx "^")))
        (start-pos (point))
        (ranges nil)
        (classes nil))
    (when negated
      (forward-char 1)
      (setq start-pos (point)))
    (while (not (eobp))
      (cond
       ((looking-at (rx "[:" (group (*? anything)) ":]"))
        (let ((sym (intern (match-string 1))))
          (unless (memq sym
                        '(ascii alnum alpha blank cntrl digit graph
                                lower multibyte nonascii print punct space
                                unibyte upper word xdigit))
            (error "No character class `%s'" (match-string 0)))
          ;; Another useful ad-hoc check.
          (when (and (eq (char-before) ?\[)
                     (eq (char-after (match-end 0)) ?\]))
            (xr--report warnings (1- (point))
                        "Suspect character class framed in `[...]'"))
          (when (memq sym classes)
            (xr--report warnings (point)
                        (format "Duplicated character class `%s'"
                                (match-string 0))))
          (push sym classes)))

       ((looking-at (rx (or (seq "\\" (group anything))
                            (group (not (any "\\"))))
                        (opt "-"
                             (or (seq "\\" (group anything))
                                 (group anything)))))
        (let ((start (string-to-char (or (match-string 1)
                                         (match-string 2))))
              (end (or (and (match-beginning 3)
                            (string-to-char (match-string 3)))
                       (and (match-beginning 4)
                            (string-to-char (match-string 4))))))
          (when (and (match-beginning 1)
                     (not (memq start '(?^ ?- ?\\))))
            (xr--report warnings (point)
                        (xr--escape-string
                         (format "Unnecessarily escaped `%c'" start) nil)))
          (when (and (match-beginning 3)
                     (not (memq end '(?^ ?- ?\\))))
            (xr--report warnings (1- (match-beginning 3))
                        (xr--escape-string
                         (format "Unnecessarily escaped `%c'" end) nil)))
          (when (and (eq start ?-)
                     (not end)
                     (match-beginning 2)
                     (< start-pos (point) (1- (point-max))))
            (xr--report warnings (point)
                        "Literal `-' not first or last"))
          (if (and end (> start end))
              (xr--report warnings (point)
                          (xr--escape-string
                           (format "Reversed range `%c-%c'" start end) nil))
            (cond
             ((eq start end)
              (xr--report warnings (point)
                          (xr--escape-string
                           (format "Single-element range `%c-%c'" start end)
                           nil)))
             ((eq (1+ start) end)
              (xr--report warnings (point)
                          (xr--escape-string
                           (format "Two-element range `%c-%c'" start end)
                           nil))))
            (let ((tail ranges))
              (while tail
                (let ((range (car tail)))
                  (if (and (<= (car range) (or end start))
                           (<= start (cdr range)))
                      (let ((msg
                             (cond
                              ((and end (< start end)
                                    (< (car range) (cdr range)))
                               (format "Ranges `%c-%c' and `%c-%c' overlap"
                                       (car range) (cdr range) start end))
                              ((and end (< start end))
                               (format "Range `%c-%c' includes character `%c'"
                                       start end (car range)))
                              ((< (car range) (cdr range))
                               (format
                                "Character `%c' included in range `%c-%c'"
                                start (car range) (cdr range)))
                              (t
                               (format "Duplicated character `%c'"
                                       start)))))
                        (xr--report warnings (point)
                                    (xr--escape-string msg nil))
                        ;; Expand previous interval to include this range.
                        (setcar range (min (car range) start))
                        (setcdr range (max (cdr range) (or end start)))
                        (setq start nil)
                        (setq tail nil))
                    (setq tail (cdr tail))))))
            (when start
              (push (cons start (or end start)) ranges)))))

       ((looking-at (rx "\\" eos))
        (xr--report warnings (point)
                    "Stray `\\' at end of string")))

      (goto-char (match-end 0)))

    (when (and (null ranges) (null classes))
      (xr--report warnings (point-min)
                  (if negated
                      "Negated empty set matches anything"
                    "Empty set matches nothing")))

    (cond
     ;; Single non-negated character, like "-": make a string.
     ((and (not negated)
           (null classes)
           (= (length ranges) 1)
           (eq (caar ranges) (cdar ranges)))
      (regexp-quote (char-to-string (caar ranges))))
     ;; Negated empty set, like "^": anything.
     ((and negated
           (null classes)
           (null ranges))
      'anything)
     ;; Single named class, like "[:nonascii:]": use the symbol.
     ((and (= (length classes) 1)
           (null ranges))
      (if negated
          (list 'not (car classes))
        (car classes)))
     ;; Anything else: produce (any ...)
     (t
      (let ((intervals nil)
            (chars nil))
        (dolist (range ranges)
          (if (eq (car range) (cdr range))
              (push (car range) chars)
            (push (string (car range) ?- (cdr range)) intervals)))
        ;; Put a single `-' last.
        (when (memq ?- chars)
          (setq chars (append (delq ?- chars) (list ?-))))
        (let ((set (cons 'any
                         (append
                          (and intervals
                               (list (apply #'concat intervals)))
                          (and chars
                               (list (apply #'string chars)))
                          (nreverse classes)))))
          (if negated
              (list 'not set)
            set)))))))

(defun xr--parse-skip-set (skip-string warnings)
  (with-temp-buffer
    (set-buffer-multibyte t)
    (insert skip-string)
    (goto-char (point-min))
    (xr--parse-skip-set-buffer warnings)))

(defun xr--substitute-keywords (head-alist body-alist rx)
  "Substitute keywords in RX using HEAD-ALIST and BODY-ALIST in the
head and body positions, respectively."
  (cond
   ((symbolp rx)
    (or (cdr (assq rx body-alist)) rx))
   ((consp rx)
    (cons (or (cdr (assq (car rx) head-alist))
              (car rx))
          (mapcar (lambda (elem) (xr--substitute-keywords
                                  head-alist body-alist elem))
                  (cdr rx))))
   (t rx)))

(defconst xr--keywords
  '((medium . nil)
    (brief . (((zero-or-more . 0+)
               (one-or-more  . 1+))
              . nil))
    (terse . (((seq          . :)
               (or           . |)
               (any          . in)
               (zero-or-more . *)
               (one-or-more  . +)
               (opt          . ? )
               (repeat       . **))
              . nil))
    (verbose . (((opt . zero-or-one))
                .
                ((nonl . not-newline)
                 (bol  . line-start)
                 (eol  . line-end)
                 (bos  . string-start)
                 (eos  . string-end)
                 (bow  . word-start)
                 (eow  . word-end)))))
  "Alist mapping keyword dialect to (HEAD-ALIST . BODY-ALIST),
or to nil if no translation should take place.
The alists are mapping from the default choice.")

(defun xr--in-dialect (rx dialect)
  (let ((keywords (assq (or dialect 'medium) xr--keywords)))
    (unless keywords
      (error "Unknown dialect `%S'" dialect))
    (if (cdr keywords)
        (xr--substitute-keywords (cadr keywords) (cddr keywords) rx)
      rx)))
  
;;;###autoload
(defun xr (re-string &optional dialect)
  "Convert a regexp string to rx notation; the inverse of `rx'.
Passing the returned value to `rx' (or `rx-to-string') yields a regexp string
equivalent to RE-STRING.  DIALECT controls the choice of keywords,
and is one of:
`verbose'       -- verbose keywords
`brief'         -- short keywords
`terse'         -- very short keywords
`medium' or nil -- a compromise (the default)"
  (xr--in-dialect (xr--parse re-string nil) dialect))

;;;###autoload
(defun xr-skip-set (skip-set-string &optional dialect)
  "Convert a skip set string argument to rx notation.
SKIP-SET-STRING is interpreted according to the syntax of
`skip-chars-forward' and `skip-chars-backward' and converted to
a character class on `rx' form.
If desired, `rx' can then be used to convert the result to an
ordinary regexp.
See `xr' for a description of the DIALECT argument."
  (xr--in-dialect (xr--parse-skip-set skip-set-string nil) dialect))

;;;###autoload
(defun xr-lint (re-string)
  "Detect dubious practices and possible mistakes in RE-STRING.
This includes uses of tolerated but discouraged constructs.
Outright regexp syntax violations are signalled as errors.
Return a list of (OFFSET . COMMENT) where COMMENT applies at OFFSET
in RE-STRING."
  (let ((warnings (list nil)))
    (xr--parse re-string warnings)
    (sort (car warnings) #'car-less-than-car)))

;;;###autoload
(defun xr-skip-set-lint (skip-set-string)
  "Detect dubious practices and possible mistakes in SKIP-SET-STRING.
This includes uses of tolerated but discouraged constructs.
Outright syntax violations are signalled as errors.
The argument is interpreted according to the syntax of
`skip-chars-forward' and `skip-chars-backward'.
Return a list of (OFFSET . COMMENT) where COMMENT applies at OFFSET
in SKIP-SET-STRING."
  (let ((warnings (list nil)))
    (xr--parse-skip-set skip-set-string warnings)
    (sort (car warnings) #'car-less-than-car)))

(defun xr--escape-string (string escape-printable)
  "Escape non-printing characters in a string for maximum readability.
If ESCAPE-PRINTABLE, also escape \\ and \", otherwise don't."
  (replace-regexp-in-string
   "[\x00-\x1f\"\\\x7f\x80-\xff][[:xdigit:]]?"
   (lambda (s)
     (let* ((c (logand (string-to-char s) #xff))
            (xdigit (substring s 1))
            (transl (assq c
                          '((?\b . "\\b")
                            (?\t . "\\t")
                            (?\n . "\\n")
                            (?\v . "\\v")
                            (?\f . "\\f")
                            (?\r . "\\r")
                            (?\e . "\\e")))))
       ;; We prefer hex escapes (\xHH) because that is what most users
       ;; want today, but use octal (\OOO) if the following character
       ;; is a legitimate hex digit.
       (concat
        (cond (transl (cdr transl))
              ((memq c '(?\\ ?\"))
               (if escape-printable (string ?\\ c) (string c)))
              ((zerop (length xdigit)) (format "\\x%02x" c))
              (t (format (format "\\%03o" c))))
        xdigit)))
   string 'fixedcase 'literal))

(defun xr--take (n list)
  "The N first elements of LIST."
  (butlast list (- (length list) n)))

(defun xr--rx-list-to-string (rx plain-prefix)
  "Print the list `rx' to a string, unformatted.
The first PLAIN-PREFIX elements are formatted using `prin1-to-string';
the rest with `xr--rx-to-string'."
  (concat "("
          (mapconcat #'identity
                     (append
                      (mapcar #'prin1-to-string (xr--take plain-prefix rx))
                      (mapcar #'xr--rx-to-string (nthcdr plain-prefix rx)))
                     " ")
          ")"))

(defun xr--rx-to-string (rx)
  "Print an rx expression to a string, unformatted."
  (cond
   ((eq rx '*?) "*?")                   ; Avoid unnecessary \ in symbol.
   ((eq rx '+?) "+?")
   ((eq rx '\??) "\\??")
   ((stringp rx) (concat "\"" (xr--escape-string rx t) "\""))
   ((characterp rx)
    (let ((esc (assq rx '((?\( . ?\()
                          (?\) . ?\))
                          (?\[ . ?\[)
                          (?\] . ?\])
                          (?\\ . ?\\)
                          (?\; . ?\;)
                          (?\" . ?\")
                          (?\s . ?s)
                          (?\n . ?n)
                          (?\r . ?r)
                          (?\t . ?t)
                          (?\e . ?e)
                          (?\b . ?b)
                          (?\f . ?f)
                          (?\v . ?v)))))
      (cond (esc (format "?\\%c" (cdr esc)))
            ;; Only base characters are displayed as ?char; this excludes
            ;; controls, combining, surrogates, noncharacters etc.
            ((aref (char-category-set rx) ?.) (format "?%c" rx))
            (t (format "#x%02x" rx)))))
   ((atom rx) (prin1-to-string rx))
   ((nlistp (cdr rx))
    (format "(%s . %s)"
            (xr--rx-to-string (car rx))
            (xr--rx-to-string (cdr rx))))
   ((or (eq (car rx) '**)
        (and (eq (car rx) 'repeat) (> (length rx) 3)))
    ;; First 2 args are integers.
    (xr--rx-list-to-string rx 3))
   ((memq (car rx) '(= >= repeat group-n backref))
    ;; First arg is integer.
    (xr--rx-list-to-string rx 2))
   (t
    ;; Render the space character as ? when first in a list.
    ;; Elsewhere, it's a character or integer.
    (let ((first (if (eq (car rx) ?\s)
                     "?"
                   (xr--rx-to-string (car rx))))
          (rest (mapcar #'xr--rx-to-string (cdr rx))))
      (concat "(" (mapconcat #'identity (cons first rest) " ") ")")))))

(defun xr-pp-rx-to-str (rx)
  "Pretty-print the regexp RX (in rx notation) to a string.
It does a slightly better job than standard `pp' for rx purposes."
  (with-temp-buffer
    (insert (xr--rx-to-string rx) "\n")
    (pp-buffer)

    ;; Remove the line break after short operator names for
    ;; readability and compactness.
    (goto-char (point-min))
    (while (re-search-forward
            (rx "(" (** 1 4 (any "a-z0-9" "+?:|*=>"))
                (group "\n" (zero-or-more blank)))
            nil t)
      (replace-match " " t t nil 1))
    
    ;; Reindent the buffer in case line breaks have been removed.
    (goto-char (point-min))
    (indent-sexp)

    (buffer-string)))

;;;###autoload
(defun xr-pp (re-string &optional dialect)
  "Convert to `rx' notation and output the pretty-printed result.
This function uses `xr' to translate RE-STRING into DIALECT.
It is intended for use from an interactive elisp session.
See `xr' for a description of the DIALECT argument."
  (insert (xr-pp-rx-to-str (xr re-string dialect))))

;;;###autoload
(defun xr-skip-set-pp (skip-set-string &optional dialect)
  "Convert a skip set string to `rx' notation and pretty-print.
This function uses `xr-skip-set' to translate SKIP-SET-STRING
into DIALECT.
It is intended for use from an interactive elisp session.
See `xr' for a description of the DIALECT argument."
  (insert (xr-pp-rx-to-str (xr-skip-set skip-set-string dialect))))

(provide 'xr)

;;; xr.el ends here
