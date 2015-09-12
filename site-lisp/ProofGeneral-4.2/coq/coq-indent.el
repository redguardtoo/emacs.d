;;; coq-indent.el --- indentation for Coq
;;
;; Copyright (C) 2004-2006 LFCS Edinburgh.
;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <courtieu@lri.fr>
;;
;; Commentary:
;; 
;; Indentation for Coq.
;; This is experimental, the code is rather ugly for the moment.
;;

;;; Code:

(require 'coq-syntax)

(eval-when-compile
  (defvar coq-script-indent nil))

(defconst coq-any-command-regexp
  (proof-regexp-alt-list coq-keywords))

(defconst coq-indent-inner-regexp
  (proof-regexp-alt
   "[[]()]" "[^{]|[^}]"
   ;; forall with must not be enclosed by \\< and
   ;;\\> . "~" forall but interacts with 'not'
   (proof-ids-to-regexp
    '("as" "Cases" "match" "else" "Fix" "forall" "fun" "if" "into" "let" "then"
      "using" "after"))))
; "ALL" "True" "False" "EX" "end" "in" "of" "with"

(defconst coq-comment-start-regexp "(\\*")
(defconst coq-comment-end-regexp "\\*)")
(defconst coq-comment-start-or-end-regexp
  (concat coq-comment-start-regexp "\\|" coq-comment-end-regexp))
(defconst coq-indent-open-regexp
  (proof-regexp-alt ;(proof-regexp-alt-list coq-keywords-goal) goal-command-p instead
   (proof-ids-to-regexp '("Cases" "match" "BeginSubproof"))
   "\\s(" "{|"))

(defconst coq-indent-close-regexp
  (proof-regexp-alt "\\s)" "|}" "}"
                    (proof-ids-to-regexp '("end" "EndSubProof"))
                    (proof-ids-to-regexp coq-keywords-save)))


(defconst coq-indent-closepar-regexp "\\s)")
(defconst coq-indent-closematch-regexp (proof-ids-to-regexp '("end")))
(defconst coq-indent-openpar-regexp "\\s(")
(defconst coq-indent-openmatch-regexp (proof-ids-to-regexp '("match" "Cases")))
(defconst coq-tacticals-tactics-regex
  (proof-regexp-alt (proof-regexp-alt-list (append coq-tacticals coq-tactics))))
(defconst coq-indent-any-regexp
  (proof-regexp-alt coq-indent-close-regexp coq-indent-open-regexp
                    coq-indent-inner-regexp coq-any-command-regexp
                    coq-tacticals-tactics-regex))
(defconst coq-indent-kw
  (proof-regexp-alt-list (cons coq-any-command-regexp
                               (cons coq-indent-inner-regexp
                                     (append coq-tacticals coq-tactics)))))

; pattern matching detection, will be tested only at beginning of a
; line (only white sapces before "|") must not match "|" followed by
; another symbol the following char must not be a symbol (tokens of coq
; are the biggest symbol cocateantions)

(defconst coq-indent-pattern-regexp "\\(|\\(?:(\\|\\s-\\|\\w\\|\n\\)\\|with\\)")

;;;; End of regexps

(defun coq-indent-goal-command-p (str)
  "Syntactical detection of a coq goal opening.
Only used in indentation code and in
v8.0 compatibility mode.  Module, Definition and Function need a special parsing to
detect if they start something or not."
  (let* ((match (coq-count-match "\\_<match\\_>" str))
         (with (coq-count-match "\\_<with\\_>" str))
         (letwith (+ (coq-count-match "\\_<let\\_>" str) (- with match)))
         (affect (coq-count-match ":=" str)))

    (and (proof-string-match coq-goal-command-regexp str)
         (not
          (and (proof-string-match "\\`\\(Definition\\|Instance\\|Lemma\\|Module\\)\\>" str)
               (not (= letwith affect))))
         (not (proof-string-match "\\`Declare\\s-+Module\\(\\w\\|\\s-\\|<\\)*:" str))
         (not
          (and (proof-string-match "\\`\\(Function\\|GenFixpoint\\)\\>" str)
               (not (proof-string-match "{\\s-*\\(wf\\|measure\\)" str)))))))


;; matches regular command end (. and ... followed by a space or buffer end)
(defconst coq-period-end-command
  "\\(?2:[^.]\\|\\=\\|\\.\\.\\)\\(?1:\\.\\)\\(?3:\\s-\\|\\'\\)")

;; matches curly bracket but not {| and |} WARNING this matches more
;; than the script parenthesizing '{' and '}' as curly bracket may
;; match this when used in regular expressions
(defconst coq-curlybracket-end-command
  "\\(?1:{\\)\\(?3:[^|]\\)\\|\\(?2:[^|]\\|\\=\\)\\(?1:}\\)")

;; matches bullets. WARNING this matches more than real bullets as - +
;; and * may match this when used in regular expressions
(defconst coq-bullet-end-command
  "\\(?2:\\s-\\|\\=\\)\\(?:\\(?1:-\\)\\|\\(?1:+\\)\\|\\(?1:\\*\\)\\)")

;; ". " and "... " are command endings, ".. " is not, same as in
;; proof-script-command-end-regexp in coq.el

;; HACK: bullets must be preceded by a space but since we usually
;; search for this expression from the first non white char of the
;; command, the space will not be seen by re-search-forward, so we
;; allow + - and * to be detected
;;


(defconst coq-end-command-regexp
  (concat coq-period-end-command "\\|"
          coq-curlybracket-end-command  "\\|"
          coq-bullet-end-command)
;  "\\(?2:[^.]\\|\\.\\.\\)\\(?1:\\.\\)\\(?3:\\s-\\|\\'\\)"
  "Regexp matching end of a command. There are 3 substrings:
* number 1 is the real coq ending string,
* number 2 is the left context matched that is not part of the ending string
* number 3 is the right context matched that is not part of the ending string

WARNING: this regexp accepts curly brackets (if not preceded by
'|') and bullets (+ - *) (if preceded by a space or at cursor).
This is of course not correct and some more check is needed to
distinguish between the different uses of this characters. ")


(defun coq-search-comment-delimiter-forward ()
  "Search forward for a comment start (return 1) or end (return -1).
Return nil if not found."
  (when (re-search-forward coq-comment-start-or-end-regexp nil 'dummy)
    (save-excursion
      (goto-char (match-beginning 0))
      (if (looking-at coq-comment-start-regexp) 1 -1))))


(defun coq-search-comment-delimiter-backward ()
  "Search backward for a comment start (return 1) or end (return -1).
Return nil if not found."
  (when (re-search-backward coq-comment-start-or-end-regexp nil 'dummy)
      (if (looking-at coq-comment-start-regexp) 1 -1)))


(defun coq-skip-until-one-comment-backward ()
  "Skips comments and normal text until finding an unclosed comment start.
Return nil if not found.  Point is moved to the the unclosed comment start
if found, to (point-max) otherwise. return true if found, nil otherwise."
  (if (= (point) (point-min)) nil
    (ignore-errors (backward-char 1))       ; if point is between '(' and '*'
    (if (looking-at coq-comment-start-regexp) t
      (forward-char 1)
      (let ((nbopen 1) (kind nil))
        (while (and (> nbopen 0) (setq kind (coq-search-comment-delimiter-backward)))
          (if (< kind 0)
              (setq nbopen (+ 1 nbopen))
            (setq nbopen (- nbopen 1))))
        (= nbopen 0)))))

(defun coq-skip-until-one-comment-forward ()
  "Skips comments and normal text until finding an unopened comment end."
  (ignore-errors (backward-char 1))            ; if point is between '*' and ')'
  (if (looking-at coq-comment-end-regexp) (progn (forward-char 2) t)
    (forward-char 1)
    (let ((nbopen 1) (kind nil))
      (while (and (> nbopen 0) (setq kind (coq-search-comment-delimiter-forward)))
        (if (> kind 0) (setq nbopen (+ 1 nbopen))
          (setq nbopen (- nbopen 1))))
      (= nbopen 0))))

(defun coq-looking-at-comment ()
  "Return non-nil if point is inside a comment."
  (or (proof-inside-comment (point))
      (proof-inside-comment (+ 1 (point)))))

(defun coq-find-comment-start ()
  "Go to the current comment start.
If inside nested comments, go to the start of the
outer most comment. Return the position of the comment start. If not inside a
comment, return nil and does not move the point."
  (when (coq-looking-at-comment)
    (let ((prevpos (point)) (init (point)))
      (while (coq-skip-until-one-comment-backward)
        (setq prevpos (point)))
      (goto-char prevpos)
      (if (= prevpos init) nil prevpos))))

(defun coq-find-comment-end ()
  "Go to the current comment end.
If inside nested comments, go to the end of the
outer most comment. Return the position of the end of comment end. If not inside a
comment, return nil and does not move the point."
  (let ((prevpos (point)) (init (point)))
    (while (coq-skip-until-one-comment-forward)
      (setq prevpos (point)))
    (goto-char prevpos)
    (if (= prevpos init) nil prevpos)))

; generic function is wrong when the point in between ( and *
(defun coq-looking-at-syntactic-context ()
  "See `proof-looking-at-syntactic-context'.
Use this one for coq instead of the generic one."
  (if (coq-looking-at-comment) 'comment
    (proof-looking-at-syntactic-context)))

(defconst coq-end-command-or-comment-regexp
  (concat coq-comment-end-regexp "\\|" coq-end-command-regexp))

(defconst coq-end-command-or-comment-start-regexp
  (concat coq-comment-start-regexp "\\|" coq-end-command-regexp))

(defun coq-find-not-in-comment-backward (reg &optional lim submatch)
  "Moves to the first not commented occurrence of REG found looking up.
The point is
put exactly before the occurrence if SUBMATCH is nil, otherwise the point is put
before SUBMATCHnth matched sub-expression (see `match-string').  If no occurrence is
found, go as far as possible and return nil."
  (coq-find-comment-start) ; first go out of comment if inside some
  (let ((found nil) (continue t)
        (regexp (concat coq-comment-end-regexp "\\|" reg)))
    (while (and (not found) continue)
      (setq continue (re-search-backward regexp lim 'dummy))
      (when continue
        (if (coq-looking-at-comment)
            (progn (coq-skip-until-one-comment-backward))
          (progn (when submatch (goto-char (match-beginning submatch)))
                 (setq found t)))))
    (when found (point))))


(defun coq-find-not-in-comment-forward (reg &optional lim submatch)
  "Moves to the first not commented occurrence of REG found looking down.
The point is put exactly before the occurrence if SUBMATCH is nil,
otherwise the point is put before SUBMATCHnth matched sub-expression
\(see `match-string').  If no occurrence is found, go as far as possible
and return nil."
  ;; da: PATCH here for http://proofgeneral.inf.ed.ac.uk/trac/ticket/173
  ;; (nasty example).  But I don't understand this code!
  ;; Sometimes we're called outside of a comment here.
  (if (coq-looking-at-comment)
      (coq-find-comment-end))
  (let ((found nil) (continue t)
        (regexp (concat coq-comment-start-regexp "\\|" reg)))
    (while (and (not found) continue)
      (setq continue (re-search-forward regexp lim 'dummy))
      (when continue
        (goto-char (match-beginning 0))
        (if (looking-at coq-comment-start-regexp)
            (progn (forward-char 2) (coq-skip-until-one-comment-forward))
          (progn (when (and submatch (match-beginning submatch))
                   (goto-char (match-beginning submatch)))
                 (setq found t))
          )))
    (when found (point))))


(defun coq-is-on-ending-context ()
  (cond
   ((looking-at "}") -1)
   ((save-excursion
      (ignore-errors
        (forward-char -1) ; always nil, don't use "and"
        (looking-at "{\\|\\."))) 1)
   (t 0)))

(defun coq-empty-command-p ()
  "Test if between point and previous command is empty.
Comments are ignored, of course."
  (let ((end (point))
        (start (coq-find-not-in-comment-backward "[^[:space:]]")))
    ;; we must find a "." to be sure, because {O} {P} is allowed in definitions
    ;; with implicits --> this function is recursive
    (if (looking-at "{\\|}\\|-\\|\\+\\|\\*") (coq-empty-command-p)
      (looking-at "\\.\\|\\`"))))


; slight modification of proof-script-generic-parse-cmdend (one of the
; candidate for proof-script-parse-function), to allow "{" and "}" to be
; command terminator when the command is empty. TO PLUG: swith the comment
; below and rename coq-script-parse-function2 into coq-script-parse-function
(defun coq-script-parse-cmdend-forward (&optional limit)
  "Move to the first end of command found looking forward from point.
Point is put exactly after the ending token (but before matching
substring if present). If no end command is found, go as far as
possible and return nil. End of command appearing in comments are
ignored. This function makes use of the substring 1 of the
command end regexp."
  (if (looking-at proof-script-comment-start-regexp)
      ;; Handle comments
      (if (proof-script-generic-parse-find-comment-end) 'comment)
    ;; Handle non-comments: assumed to be commands
    (if (< (coq-is-on-ending-context) 0)
        (ignore-errors (forward-char (coq-is-on-ending-context))))
    (let (foundend next-pos)
      ;; Find end of command
      (while (and (setq foundend
                        (and
                         (re-search-forward proof-script-command-end-regexp limit t)
                         (match-end 1)))
                  (setq next-pos (+ 1 (match-beginning 0)))
                  (or
                      (if (or (string-equal (match-string 1) "}")
                              (string-equal (match-string 1) "{")
                              (string-equal (match-string 1) "-")
                              (string-equal (match-string 1) "+")
                              (string-equal (match-string 1) "*"))
                          (save-excursion
                            (goto-char (match-beginning 1))
                            (not (coq-empty-command-p)))
                        nil)
                      (and
                       (goto-char foundend)
                       (proof-buffer-syntactic-context))))
        ;; go back as far as possible before the start of the current
        ;; matching string, this way we will match consecutive endings
        ;; like ine "}."
        (ignore-errors (goto-char next-pos))
;        (ignore-errors (forward-char -1))
        )
      (if (and foundend
               (goto-char foundend) ; move to command end
               (not (proof-buffer-syntactic-context)))
          ;; Found command end outside string/comment
          'cmd
        ;; Didn't find command end
        nil))))


; slight modification of proof-script-generic-parse-cmdend (one of the
; candidate for proof-script-parse-function), to allow "{" and "}" to be
; command terminator when the command is empty. TO PLUG: swith the comment
; below and rename coq-script-parse-function2 into coq-script-parse-function
(defun coq-script-parse-cmdend-backward (&optional limit)
  "Move to the first end of command (not commented) found looking up.
Point is put exactly before the last ending token (before the last
\".\" if \"...\"). If no end command is found, go as far as possible
and return nil."
  (if (looking-at proof-script-comment-start-regexp)
      ;; Handle comments
      (if (proof-script-generic-parse-find-comment-end) 'comment) ; start?
    ;; Handle non-comments: assumed to be commands
    ;; first shift if we are in the middle of a ending pattern
    (if (> (coq-is-on-ending-context) 0)
        (ignore-errors(forward-char (coq-is-on-ending-context))))
    (let (foundbeg next-pos)
      ;; Find end of command
      (while (and (setq foundbeg
                        (and
                         (re-search-backward proof-script-command-end-regexp limit 'dummy)
                         (match-beginning 1)))
                  (setq next-pos (- (match-end 0) 1))
                  (or (if (or (string-equal (match-string 1) "}")
                              (string-equal (match-string 1) "{")
                              (string-equal (match-string 1) "-")
                              (string-equal (match-string 1) "+")
                              (string-equal (match-string 1) "*"))
                          (save-excursion
                            (goto-char (match-beginning 1))
                            (not (coq-empty-command-p)))
                        nil)
                      (and
                       (goto-char foundbeg)
                       (proof-buffer-syntactic-context))))
        (ignore-errors (goto-char next-pos)))
      (if (and foundbeg
               (goto-char foundbeg) ; move to command end
               (not (proof-buffer-syntactic-context)))
          ;; Found command end outside string/comment
          'cmd
        ;; Didn't find command end
        nil))))


(defun coq-find-current-start ()
  "Move to the start of command at point.
The point is put exactly after the end of previous command, or at the (point-min if
there is no previous command)."
  (coq-script-parse-cmdend-backward)
  (if (proof-looking-at "\\.\\s-\\|{\\|}") (forward-char 1)) ; else = no match found
  (point))


(defun coq-find-real-start ()
  "Move to the start of command at point.
The point is put exactly before first non comment letter of the command."
  (coq-find-current-start)
  (coq-find-not-in-comment-forward "\\S-"))

(defun same-line (pt pt2)
 (or (= (line-number-at-pos pt) (line-number-at-pos pt2))))

(defun coq-command-at-point (&optional nojumplines)
  "Return the string of the command at point, nil if none.
Can jump line if NOJUMPLINES = nil."
  (let ((initpos (point)))
    (save-excursion
      (let* ((st (coq-find-real-start)) ; va chercher trop loin? OUI
             (linejumped (not (same-line initpos (point))))
             ;(xxx (goto-char (- (point) 1)))
             (nd (or (if (coq-script-parse-cmdend-forward) (point) nil)
                     (- (point-max) 1)))) ; idem?
        (if (and st (or (not nojumplines) (not linejumped)))
            (buffer-substring st nd)
          nil)))))


(defun coq-commands-at-line (&optional nojumplines)
  "Return the string of each command at current line."
  (save-excursion
    ;; we must capture a "." or a "{" at start of the line. So we go at the end of
    ;; previous line to have a left context to match
    (let ((initpoint (point))
          (forward-char (coq-is-on-ending-context))
          (command-found (coq-command-at-point nojumplines))
          res 
          )
      (if command-found (coq-find-real-start))
      (while (and command-found 
                  ;; need this second test even with nojumplines:
                  (same-line (point) initpoint)) 
        (setq res (cons command-found res))
        (if (and (coq-script-parse-cmdend-forward)
                 ;(ignore-errors (forward-char 1) t);to fit in the "and"
                 (coq-find-real-start))
            (setq command-found (coq-command-at-point nojumplines))
          (setq command-found nil)
          ))
      res)))


(defun coq-indent-only-spaces-on-line ()
  "Non-nil if there only spaces (or nothing) on the current line after point.
Moves point to first non space char if present, to the end of line otherwise."
  (skip-chars-forward " \t" (save-excursion (end-of-line) (point)))
  (eolp))

(defun coq-indent-find-reg (lim reg)
  "Non-nil if REG occurs between point and LIM, not in a comment or string.
Point is moved at the end of the match if found, at LIM otherwise."
  (let ((oldpt (point)) (limit lim) (found nil))
    (if (= limit (point)) nil
      ;;swap limit and point if necessary
;      (message "coq-indent-find-reg...")
      (when (< limit (point)) (let ((x limit)) (setq limit (point)) (goto-char x)))
      (prog1
          (coq-find-not-in-comment-forward reg limit)
        (goto-char (match-end 0))))))



(defun coq-find-no-syntactic-on-line ()
  "Return non-nil if there is a not commented non white character on the line.
Moves point to this char or to the end of the line if not found (and return nil in
this case)."
  (let ((eol (save-excursion (end-of-line) (point))))
    (back-to-indentation)
    (while (and (coq-looking-at-syntactic-context)
                (re-search-forward coq-comment-end-regexp eol 'dummy))
      (skip-chars-forward " \t"))
    (not (eolp))))



(defun coq-back-to-indentation-prevline ()
  "Move point back to previous pertinent line for indentation.
Move point to the first non white space character.  Returns 0 if
top of buffer was reached, 3 if inside a comment or string, 4 if
inside the {} of a record, 1 if the line found is not in the same
command as the point before the function was called, 2
otherwise (point and previous line are in the same command, and
not inside the {} of a record)."

  (if (coq-looking-at-syntactic-context) 3
    (let ((oldpt (point))
          (topnotreached (= (forward-line -1) 0))) ;;; nil if going one line backward
                                                   ;;; is not possible
      (while (and topnotreached
                  (not (coq-find-no-syntactic-on-line))
                  )
        (setq topnotreached (= (forward-line -1) 0))
        (end-of-line)
        (if (proof-looking-at-syntactic-context)
            (re-search-backward coq-comment-start-regexp nil 'dummy)
          ))
      (back-to-indentation)
      (if (not topnotreached) 0 ;; returns nil if top of buffer was reached
        ;; if we are at end of a command (dot) find this command
        ; if there is a "." alone on the line
        (let ((pos (point)))
          ;(ignore-errors (forward-char -1))
          (if (coq-script-parse-cmdend-forward oldpt)
              (progn (forward-char -1)
                     ;; one more if "." found, no more if "{" or "}"
                     (when (proof-looking-at "\\.") (forward-char -1))
                     (coq-find-real-start)
                     (back-to-indentation)
                     1)
            (goto-char pos)
            (if (save-excursion
                  (and
                       (not (= (point) (point-min)))
                       (or (forward-char -1) t)
                       (coq-find-real-start)
                       (proof-looking-at-safe "Record\\|Class\\|Instance"); {struct} should not match this
                       (coq-indent-find-reg oldpt "{[^|]")))
                4
              2)))))))


(defun coq-find-unclosed (&optional optlvl limit openreg closereg)
  "Finds the first unclosed open item (backward), counter starts to optlvl (default 1) and stops when reaching limit (default point-min)."

  (let* ((lvl (or optlvl 1))
         (open-re  (if openreg
                       (proof-regexp-alt openreg proof-indent-open-regexp)
                     proof-indent-open-regexp))
         (close-re (if closereg
                       (proof-regexp-alt closereg proof-indent-close-regexp)
                     proof-indent-close-regexp))
         (both-re (proof-regexp-alt "\\`" close-re open-re))
         (nextpt (save-excursion
                   (proof-re-search-backward both-re))))
    (while
        (and (not (= lvl 0))
             (>= nextpt (or limit (point-min)))
             (not (= nextpt (point-min))))
      (goto-char nextpt)
      (cond
       ((proof-looking-at-syntactic-context) ())
       ;; ((proof-looking-at-safe proof-indent-close-regexp)
       ;;  (coq-find-unclosed 1 limit)) ;; recursive call
       ((proof-looking-at-safe close-re) (setq lvl (+ lvl 1)))
       ((proof-looking-at-safe open-re) (setq lvl (- lvl 1))))
      (setq nextpt (save-excursion (proof-re-search-backward both-re))))
    (if (= lvl 0) t
      (goto-char (or limit (point-min)))
      nil)))


(defun coq-find-at-same-level-zero (limit openreg)
  "Move to open or openreg (first found) at same parenthesis level as point.
Returns point if found."
  (let* (found
         min-reached
         (open-re (if openreg
                      (proof-regexp-alt openreg proof-indent-open-regexp)
                    proof-indent-open-regexp))
         (close-re proof-indent-close-regexp)
         (both-re (proof-regexp-alt "\\`" close-re open-re))
         (nextpt (save-excursion
                   (proof-re-search-backward both-re))))

    (while ; min-reached is set to t only after we have tested if found.
        (and (not found) (not min-reached)
             (>= nextpt (or limit (point-min))))
      (goto-char nextpt)
      (cond
       ((proof-looking-at-syntactic-context) ())
       ((proof-looking-at-safe openreg) (setq found t))
       ((proof-looking-at-safe proof-indent-open-regexp) (setq found t));assert false?
       ;;       ((proof-looking-at-safe closereg) (coq-find-unclosed 1 limit))
       ((proof-looking-at-safe proof-indent-close-regexp)
        (coq-find-unclosed 1 limit)))
      (if (= nextpt (point-min)) (setq min-reached t))
      (setq nextpt (save-excursion (proof-re-search-backward both-re))))
    (if found (point) nil)))


(defun coq-find-unopened (&optional optlvl limit)
  "Finds the last unopened close item (looking forward from point), counter starts to OPTLVL (default 1) and stops when reaching limit (default point-max). This function only works inside an expression."

  (let ((lvl (or optlvl 1)) after nextpt endpt)
    (save-excursion
      (proof-re-search-forward
       (proof-regexp-alt "\\'"
                         proof-indent-close-regexp
                         proof-indent-open-regexp))
      (setq after (point))
      (goto-char (match-beginning 0))
      (setq nextpt (point)))
    (while
        (and (not (= lvl 0))
             (<= nextpt (or limit (point-max)))
             (not (= nextpt (point-max))))
      (goto-char nextpt)
      (setq endpt (point))
      (cond
       ((proof-looking-at-syntactic-context) ())

       ((proof-looking-at-safe proof-indent-close-regexp)
        (setq lvl (- lvl 1)))

       ((proof-looking-at-safe proof-indent-open-regexp)
        (setq lvl (+ lvl 1))))

      (goto-char after)
      (save-excursion
		  (proof-re-search-forward
			(proof-regexp-alt "\\'"
                                          proof-indent-close-regexp
                                          proof-indent-open-regexp))
		  (setq after (point))
		  (goto-char (match-beginning 0))
		  (setq nextpt (point))))
    (if (= lvl 0)
        (goto-char endpt)
      (goto-char (or limit (point-max)))
      nil)))



(defun coq-find-last-unopened (&optional optlvl limit)
  "Backward moves to and returns the point of the last close item that is not opened after limit."
  (let ((last nil))
	 (while (coq-find-unopened optlvl limit)
		(setq last (point))
		(forward-char 1)); shift one to the right,
                       ; that way the current match won'tbe matched again
	 (if last (goto-char last))
	 last))


(defun coq-end-offset (&optional limit)
  "Find the first unclosed open indent item, and returns its column. Stop when reaching limit (defaults tp point-min)."
  (save-excursion
    (let ((found nil)
          (anyreg (proof-regexp-alt "\\`" proof-indent-any-regexp)))
      (while
          (and (not found)
               (> (point) (or limit (point-min))))
        (proof-re-search-backward anyreg)
        (cond
         ((proof-looking-at-syntactic-context) ())

         ((proof-looking-at-safe proof-indent-close-regexp)
          (coq-find-unclosed))

         ((proof-looking-at-safe proof-indent-open-regexp)
          (setq found t))

         (t ())))

      (if found (current-column)
        -1000)                          ; no unclosed found
      )))


(defun coq-add-iter (l f)
  (if (eq l nil) 0 (+ (if (funcall f (car l)) 1 0) (coq-add-iter (cdr l) f))))

(defun coq-goal-count (l) (coq-add-iter l 'coq-indent-goal-command-p))

(defun coq-save-count (l)
  (coq-add-iter l (lambda (x) 
                    (or (coq-save-command-p nil x)
                        (eq (proof-string-match "\\<\\(?:EndSubproof\\)\\>\\|}" x) 0)))))

(defun coq-proof-count (l)
  (coq-add-iter l (lambda (x)
                    (eq (proof-string-match "\\<\\(?:Proof\\|BeginSubproof\\)\\>\\|{" x) 0))))

;; returns the difference between goal (and assimilate Proof and BeginSubproof) and
;; save commands in a commands list. This is to 
(defun coq-goal-save-diff-maybe-proof (l)
  (let ((proofs (coq-proof-count l))
        (saves (coq-save-count l))
        (goals (coq-goal-count l)))
;    (if (= goals 0) (- (if (<= proofs 0) 0 1) (coq-save-count l))
;      (- goals (coq-save-count l)))
    (- (+ proofs goals) saves)
    ))


(defun coq-indent-command-offset (kind prevcol prevpoint)
  "Returns the indentation offset of the current line.
This function indents a *command* line (the first line of a command).
Use `coq-indent-expr-offset' to indent a line belonging to an expression."
  (let ((diff-goal-save-current
         (coq-goal-save-diff-maybe-proof (coq-commands-at-line t)))
        (diff-goal-save-prev 
         (save-excursion
           (goto-char prevpoint)
           (coq-goal-save-diff-maybe-proof (coq-commands-at-line t))))
        (prev-closing-beginning ; t if the closing is at start of the (prev) line
         (save-excursion
           (goto-char prevpoint)
           (back-to-indentation)
           ;(forward-char -1)
           (looking-at coq-indent-close-regexp)))
        (current-closing-beginning  ; t if the closing is at start of the (current) line
         (save-excursion 
           (back-to-indentation)
           (looking-at coq-indent-close-regexp))))
    ;(message "currentkind,prevcol,prevpoint = %d , %d ,%d " kind prevcol prevpoint)
    (cond
     ((proof-looking-at-safe "\\<Proof\\>") 0);; no indentation at "Proof ..."

     (t (* proof-indent 
           (let ((res
                  (let ((a diff-goal-save-prev) (b diff-goal-save-current)
                        (a2 prev-closing-beginning) (b2 current-closing-beginning))
                    ;(message "a,b,a2,b2 = %d,%d,%S,%S" a b a2 b2)
                    (cond
                     ((and (>= a 0) (>= b 0)) a)
                     ((and (>= a 0) (< b 0) b2) (+ a -1)) ; a + b 
                     ((and (>= a 0) (< b 0) (not b2)) a)
                     ((and (< a 0) (< b 0) a2 b2) a) ; a +1 -1
                     ((and (< a 0) (< b 0) a2 (not b2)) (+ a 1))
                     ((and (< a 0) (< b 0) (not a2) b2) (+ a -1))
                     ((and (< a 0) (< b 0) (not a2) (not b2)) a)
                     ((and (< a 0) (>= b 0) a2) (+ a 1))
                     ((and (< a 0) (>= b 0) (not a2)) a)
                     (t (error "Muh?"))))))
             ;(message "RES = %S" res)
             ;(message "********************")
             res))
        )
    ;;  ;; we are at an end command -> one ident left unless previous line is a goal
    ;;  ;; (if goal and save are consecutive, then no indentation at all)
    ;;  ((and (< diff-goal-save-current 0) (<= diff-goal-save-prev 0)) (- proof-indent))
    ;; ;; previous command is a goal command -> one indent right unless the current one
    ;; ;; is an end (consecutive goal and save).
    ;; ((and (>= diff-goal-save-current 0) (> diff-goal-save-prev 0)) proof-indent)
    ;; ;; otherwise -> same indent as previous command
    ;; (t 0)
     )))



;; This function is very complex, indentation of a line (inside an
;; expression) is determined by the beginning of this line (current
;; point) and the indentation items found at previous pertinent (not
;; comment, not string, not empty) line. Sometimes we even need the
;; previous line of previous line.

;; prevcol is the indentation column of the previous line, prevpoint
;; is the indentation point of previous line, record tells if we are
;; inside the accolades of a record.

(defun coq-indent-expr-offset (kind prevcol prevpoint record)
  "Returns the indentation column of the current line.
This function indents a *expression* line (a line inside of a command).  Use
`coq-indent-command-offset' to indent a line belonging to a command.  The fourth
argument must be t if inside the {}s of a record, nil otherwise."
  ;(message "COQ-INDENT-EXPR-OFFSET")
  (let ((pt (point)) real-start)
    (save-excursion
      (setq real-start (coq-find-real-start)))

    (cond

     ;; at a ) -> same indent as the *line* of corresponding (
     ((proof-looking-at-safe coq-indent-closepar-regexp)
      (save-excursion (coq-find-unclosed 1 real-start)
                      (back-to-indentation)
                      (current-column)))

     ;; at an end -> same indent as the corresponding match or Case
     ((proof-looking-at-safe coq-indent-closematch-regexp)
      (save-excursion (coq-find-unclosed 1 real-start)
                      (current-column)))

     ;; if we find a "|" we indent from the first unclosed
     ;; or from the command start (if we are in an Inductive type)
     ((proof-looking-at-safe coq-indent-pattern-regexp)
      (save-excursion
        (coq-find-unclosed 1 real-start)
        (cond
         ((proof-looking-at-safe "\\s(")
          (+ (current-indentation) proof-indent))
         ((proof-looking-at-safe (proof-regexp-alt-list coq-keywords-defn))
          (current-column))
         (t (+ (current-column) proof-indent)))))

     ;; if we find a "then" we indent from the first unclosed if
     ;; or from the command start (should not happen)
     ((proof-looking-at-safe "\\<then\\>")
      (save-excursion
        (coq-find-unclosed 1 real-start "\\<if\\>" "\\<then\\>")
        (back-to-indentation)
        (+ (current-column) proof-indent)))

     ;; if we find a "else" we indent from the first unclosed if
     ;; or from the command start (should not happen)
     ((proof-looking-at-safe "\\<else\\>")
      (save-excursion
        (coq-find-unclosed 1 real-start "\\<then\\>" "\\<else\\>")
        (coq-find-unclosed 1 real-start "\\<if\\>" "\\<then\\>")
        (back-to-indentation)
        (+ (current-column) proof-indent)))

     ;; there is an unclosed open in the previous line
     ;; -> same column if match
     ;; -> same indent than prev line + indent if (
     ((coq-find-unclosed 1 prevpoint
                         coq-indent-openmatch-regexp
                         coq-indent-closematch-regexp)
      (let ((base (if (proof-looking-at-safe coq-indent-openmatch-regexp)
                      (current-column)
                    prevcol)))
        (+ base proof-indent)))


;; there is an unclosed '(' in the previous line -> prev line indent + indent
;;	  ((and (goto-char pt) nil)) ; just for side effect: jump to initial point
;;	  ((coq-find-unclosed 1 prevpoint
;;            coq-indent-openpar-regexp
;;            coq-indent-closepar-regexp)
;;		(+ prevcol proof-indent))

     ((and (goto-char prevpoint) nil)) ; just for side effect: jump to previous line

     ;; find the last unopened ) -> indentation of line + indent
     ((coq-find-last-unopened 1 pt) ; side effect, nil if no unopenned found
      (save-excursion
        (coq-find-unclosed 1 real-start)
        (back-to-indentation)
        (current-column)))

     ;; just for side effect: jumps to end of previous line
     ((and (goto-char prevpoint)
           (or (and (end-of-line) nil)
               (and (coq-find-not-in-comment-backward "[^[:space:]]") t)) nil))

     ;; TODO fix with new use of { for tactics enclosing
     ;; should be ok if record is ok.
     ((and  (proof-looking-at-safe ";") ;prev line has ";" at the end
            record)                     ; and we are inside {}s of a record
      (save-excursion
        (coq-find-unclosed 1 real-start)
        (back-to-indentation)
        (+ (current-column) proof-indent)))

     ;; just for side effect: jumps to end of previous line
     ((and (goto-char prevpoint)  (not (= (coq-back-to-indentation-prevline) 0))
           (or (and (end-of-line) nil)
               (and (forward-char -1) t)) nil))

     ((and (proof-looking-at-safe ";") ;prev prev line has ";" at the end
           record)                     ; and we are inside {}s of a record
      (save-excursion (+ prevcol proof-indent)))

     ((and (goto-char pt) nil)) ;; just for side effect: go back to initial point

     ;; There is a indent keyword (fun, forall etc)
     ;; and we are not in {}s of a record just after a ";"
     ((coq-find-at-same-level-zero prevpoint coq-indent-kw)
      ;(message "COQ-INDENT-KW")
      (+ prevcol proof-indent))

     ((and (goto-char prevpoint) nil)) ;; just for side effect: go back to previous line
     ;; "|" at previous line
     ((proof-looking-at-safe coq-indent-pattern-regexp)
      (+ prevcol proof-indent))

     (t prevcol))))


(defun coq-indent-comment-offset ()
  (save-excursion
    (back-to-indentation)
    (let ((oldpt (point))
          ;; atstart is true if the line to indent starts with a comment start
          (atstart (proof-looking-at coq-comment-start-regexp)))
      ;; go back looking for a non empty line
      (if (/= (forward-line -1) 0) 0 ; we are at beginning of buffer
        ;; only-space on a non empty line moves the point to first non space char
        (while (and (coq-indent-only-spaces-on-line) (= (forward-line -1) 0)) ())
        ;; now we found the previous non empty line
        (let ((eol (save-excursion (end-of-line) (point))))
        (cond
         ;; The previous line contains is the comment start
         ((and (not atstart) (string-match coq-comment-start-regexp
                                           (buffer-substring (point) eol)))
          (re-search-forward coq-comment-start-regexp) ;first '(*' in the line?
          (+ 1 (current-column)))

         ;; the previous is in the same comment start or a comment started at that line
         ((and (not atstart) (proof-looking-at-syntactic-context))
          (skip-chars-forward " \t")
          (current-column))

            ;;we were at the first line of a comment and the current line is the
            ;;previous one
         (t (goto-char oldpt)
            (coq-script-parse-cmdend-backward)
            (coq-find-real-start)
            (current-column))))))))


(defun coq-indent-offset (&optional notcomments)
  (let (kind prevcol prevpoint)
    (save-excursion
      (setq kind (coq-back-to-indentation-prevline) ;go to previous *command* (assert)
            prevcol (current-column)
            prevpoint (point)))
       ;(message "coq-indent-offset... kind = %s ; prevcol = %s; prevpoint = %s" kind prevcol prevpoint)
	 (cond
	  ((= kind 0) 0  ; top of the buffer reached
           )
	  ((= kind 1) ; we are at the command level
           (+ prevcol (coq-indent-command-offset kind prevcol prevpoint)))
	  ((= kind 2) ; we are at the expression level
           (coq-indent-expr-offset kind prevcol prevpoint nil))
	  ((= kind 4) ; we are at the expression level inside {}s of a record
           (coq-indent-expr-offset kind prevcol prevpoint t))
	  ((= kind 3)
           (if notcomments nil (coq-indent-comment-offset))))))

(defun coq-indent-calculate (&optional notcomments)
  (coq-indent-offset notcomments))

(defun coq-indent-line ()
  "Indent current line of proof script, if indentation enabled."
  (interactive)
  (unless (not coq-script-indent)
    (save-excursion
      (let ((ind (save-excursion (back-to-indentation) (coq-indent-calculate))))
        (indent-line-to (max 0 ind))))
    (if (< (current-column) (current-indentation))
        (back-to-indentation))))

(defun coq-indent-line-not-comments ()
  "Same as  `coq-indent-line' but comments are not indented."
  (interactive)
  (unless (not coq-script-indent)
    (save-excursion
      (let ((ind (save-excursion (back-to-indentation) (coq-indent-calculate t))))
        (when ind (indent-line-to (max 0 ind)))))
    (if (< (current-column) (current-indentation))
        (back-to-indentation))))

(defun coq-indent-region (start end)
  (let ((deb (min start end)) (fin (max start end)))
    (goto-char end)
    (setq fin (point-marker)) ;; to go back there even if shifted
    (goto-char deb)
    (while (< (point) fin)
      (or (and (bolp) (eolp))
          (coq-indent-line-not-comments))
      (forward-line 1))
    (goto-char fin)))


;;   Local Variables: ***
;;   indent-tabs-mode:nil ***
;;   End: ***


(provide 'coq-indent)

;;; coq-indent.el ends here
