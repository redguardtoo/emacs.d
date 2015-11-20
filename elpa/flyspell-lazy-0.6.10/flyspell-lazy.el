;;; flyspell-lazy.el --- Improve flyspell responsiveness using idle timers
;;
;; Copyright (c) 2012-14 Roland Walker
;;
;; Author: Roland Walker <walker@pobox.com>
;; Homepage: http://github.com/rolandwalker/flyspell-lazy
;; URL: http://raw.githubusercontent.com/rolandwalker/flyspell-lazy/master/flyspell-lazy.el
;; Package-Version: 0.6.10
;; Version: 0.6.10
;; Last-Updated: 22 Dec 2014
;; EmacsWiki: FlyspellLazy
;; Keywords: spelling
;;
;; Simplified BSD License
;;
;;; Commentary:
;;
;; Quickstart
;;
;;     (require 'flyspell-lazy)
;;
;;     (flyspell-lazy-mode 1)
;;
;;     (flyspell-mode 1)      ; or (flyspell-prog-mode)
;;
;; Explanation
;;
;; Emacs' built-in `flyspell-mode' has performance issues on some
;; platforms.  Specifically, keyboard responsiveness may be
;; significantly degraded on OS X.  See this bug:
;;
;;     http://debbugs.gnu.org/cgi/bugreport.cgi?bug=2056
;;
;; This package reduces the amount of work done by flyspell.  Instead
;; of checking *instantly* as you type, spelling will be checked when
;; Emacs has been idle for a short time.  (Vanilla `flyspell-mode'
;; does not use idle timers but a subtle combination of hooks and
;; `sit-for'.)
;;
;; This package also forces `flyspell-mode' off completely for certain
;; buffers.
;;
;; To use this library, add the following to your ~/.emacs
;;
;;     (require 'flyspell-lazy)
;;     (flyspell-lazy-mode 1)
;;
;; Then use `flyspell-mode' as you normally would.  This package does
;; not load flyspell for you.
;;
;; `flyspell-lazy-mode' will invoke spellcheck less frequently than
;; vanilla `flyspell-mode', though this can be changed somewhat via
;; `customize'.
;;
;; See Also
;;
;;     M-x customize-group RET flyspell-lazy RET
;;     M-x customize-group RET flyspell RET
;;     M-x customize-group RET ispell RET
;;
;; Notes
;;
;;     If you are using "aspell" instead of "ispell" on the backend,
;;     the following setting may improve performance:
;;
;;         (add-to-list 'ispell-extra-args "--sug-mode=ultra")
;;
;;     If you see the cursor flicker over the region during spellcheck,
;;     make sure that `flyspell-large-region' is set to 1 (this library
;;     tries to do that for you), and try adding the following to your
;;     ~/.emacs
;;
;;         (defadvice flyspell-small-region (around flyspell-small-region-no-sit-for activate)
;;           (flyspell-lazy--with-mocked-function 'sit-for t
;;             ad-do-it))
;;
;; Compatibility and Requirements
;;
;;     GNU Emacs version 24.4-devel     : yes, at the time of writing
;;     GNU Emacs version 24.3           : yes
;;     GNU Emacs version 23.3           : yes
;;     GNU Emacs version 22.2           : yes, with some limitations
;;     GNU Emacs version 21.x and lower : unknown
;;
;;     No external dependencies
;;
;; Bugs
;;
;;     The longer the delay before checking, the more inaccurate the
;;     coordinates in `flyspell-changes'.  These are static integers;
;;     they don't move with updates in the buffer.  To mitigate this
;;     effect, a second idle timer checks all visible text (at a much
;;     longer interval).
;;
;;     Flyspell-lazy-matches-last-text is not reliable - in debug mode
;;     it can be seen that it sometimes toggles between two states at
;;     every press of spacebar.  This may be related to generating the
;;     additional span around the point.
;;
;;     Flyspell-lazy-refine-changes is sometimes mistakenly scrubbing
;;     all pending spans.  Check the case where one char is deleted
;;     inside a word.
;;
;; TODO
;;
;;     Let flyspell-issue-message-flag and flyspell-issue-welcome-flag
;;     to nil wherever needed to improve performance.
;;
;;     Consider using while-no-input macro.
;;
;;     Figure out if flyspell-lazy affects suggestions -- must an
;;     update be forced on the word before running suggestions?
;;
;;     Force re-check of text after removing comments renders the
;;     text code again under flyspell-prog-mode.
;;
;;     Optionally add aspell extra args noted in doc.
;;
;;     Make flyspell-lazy-single-ispell actually work.  Currently, see
;;     a new "starting ispell" message for every buffer opened, in
;;     spite of flyspell-lazy-single-ispell setting.  This comes from
;;     flyspell-mode calling flyspell-mode-on.
;;
;;     What would be the ramifications of using a single ispell
;;     process?  Only loss of per-buffer dictionaries?
;;
;;     Enforce using a single ispell process on regions larger than
;;     flyspell-large-region.
;;
;;     Strip symbols from text - see flyspell-lazy-strip-symbols.
;;
;;     Heuristic to detect regular expressions and avoid checking
;;     them as strings.
;;
;;     Use buffer-undo-list instead of flyspell-changes, then can
;;     also remove flyspell's after-change hook.
;;
;;     Use the hints set in prog-mode to avoid checks in the per-word
;;     and refine stages.
;;
;;     Hints for commented-out code to avoid checking.
;;
;;; License
;;
;;    Simplified BSD License
;;
;;    Redistribution and use in source and binary forms, with or
;;    without modification, are permitted provided that the following
;;    conditions are met:
;;
;;       1. Redistributions of source code must retain the above
;;          copyright notice, this list of conditions and the following
;;          disclaimer.
;;
;;       2. Redistributions in binary form must reproduce the above
;;          copyright notice, this list of conditions and the following
;;          disclaimer in the documentation and/or other materials
;;          provided with the distribution.
;;
;;    This software is provided by Roland Walker "AS IS" and any express
;;    or implied warranties, including, but not limited to, the implied
;;    warranties of merchantability and fitness for a particular
;;    purpose are disclaimed.  In no event shall Roland Walker or
;;    contributors be liable for any direct, indirect, incidental,
;;    special, exemplary, or consequential damages (including, but not
;;    limited to, procurement of substitute goods or services; loss of
;;    use, data, or profits; or business interruption) however caused
;;    and on any theory of liability, whether in contract, strict
;;    liability, or tort (including negligence or otherwise) arising in
;;    any way out of the use of this software, even if advised of the
;;    possibility of such damage.
;;
;;    The views and conclusions contained in the software and
;;    documentation are those of the authors and should not be
;;    interpreted as representing official policies, either expressed
;;    or implied, of Roland Walker.
;;
;;; Code:
;;

;;; requirements

(eval-and-compile
  ;; for callf, callf2, setf
  (require 'cl))

;;; declarations

(declare-function flyspell-auto-correct-previous-hook "flyspell.el")
(declare-function flyspell-minibuffer-p               "flyspell.el")
(declare-function flyspell-overlay-p                  "flyspell.el")
(declare-function flyspell-post-command-hook          "flyspell.el")
(declare-function flyspell-pre-command-hook           "flyspell.el")
(declare-function flyspell-word                       "flyspell.el")
(declare-function ispell-set-spellchecker-params      "ispell.el"  )

(eval-when-compile
  (defvar flyspell-changes)
  (defvar flyspell-large-region)
  (defvar ispell-process))

;;; customizable variables

;;;###autoload
(defgroup flyspell-lazy nil
  "Improve flyspell responsiveness using idle timers."
  :version "0.6.10"
  :link '(emacs-commentary-link :tag "Commentary" "flyspell-lazy")
  :link '(url-link :tag "GitHub" "http://github.com/rolandwalker/flyspell-lazy")
  :link '(url-link :tag "EmacsWiki" "http://emacswiki.org/emacs/FlyspellLazy")
  :prefix "flyspell-lazy-"
  :group 'flyspell
  :group 'wp)

(defcustom flyspell-lazy-idle-seconds 3
  "How many seconds of idle time before running flyspell on recent changes."
  :type 'number
  :group 'flyspell-lazy)

(defcustom flyspell-lazy-window-idle-seconds 30
  "How many seconds of idle time before running flyspell on the entire visible window."
  :type 'number
  :group 'flyspell-lazy)

(defcustom flyspell-lazy-changes-threshold 300
  "Hurry the idle timer when this many individual edits are pending."
  :type 'number
  :group 'flyspell-lazy)

(defcustom flyspell-lazy-size-threshold 500
  "Hurry the idle timer when a single edit is larger than this number of characters."
  :type 'number
  :group 'flyspell-lazy)

(defcustom flyspell-lazy-use-flyspell-word nil
  "Use the `flyspell-word' function when leaving a marked word.  May be slower.

The default behavior is to hurry the idle timer when leaving a marked word."
  :type 'boolean
  :group 'flyspell-lazy)

(defcustom flyspell-lazy-extra-lazy nil
  "Never do per-word checks.  Only use idle timers.

The default behavior is to perform a single-word check if a word is completed
which is also currently marked as an error.  Setting this option might be
faster than the default."
  :type 'boolean
  :group 'flyspell-lazy)

(defcustom flyspell-lazy-minimum-word-length 3
  "Ignore new edits until a word is present which exceeds this length."
  :type 'integer
  :group 'flyspell-lazy)

(defcustom flyspell-lazy-disallow-buffers '("\\`[ *]")
  "Turn off flyspell in buffers matching these regular expressions.

The default list contains a single item matching the names of
special buffers such as \"*scratch*\".

Spellchecking is also disabled in the minibuffer."
  :type '(repeat regexp)
  :group 'flyspell-lazy)

(defcustom flyspell-lazy-less-feedback nil
  "Give less echo-area feedback."
  :type 'boolean
  :group 'flyspell-lazy)

;; so far this does not work
(defvar flyspell-lazy-single-ispell nil)
;; (defcustom flyspell-lazy-single-ispell nil
;;   "Use only a single ispell process for all buffers.
;;
;; This only affects checks on regions smaller than `flyspell-large-region'.
;;
;; Experimental. Side effects may include: sharing a single
;; dictionary for all buffers, lack of support for local words."
;;   :type 'boolean
;;   :group 'flyspell-lazy)

;;; variables

(defvar flyspell-lazy-mode         nil "Mode variable for `flyspell-lazy-mode'.")
(defvar flyspell-lazy-local        nil "Whether flyspell-lazy is active in the current buffer.")
(defvar flyspell-lazy-buffer-list  nil "List of buffers in which to run flyspell-lazy idle timer.")
(defvar flyspell-lazy-timer        nil "Idle timer used by flyspell-lazy.")
(defvar flyspell-lazy-window-timer nil "Idle timer used by flyspell-lazy for checking the visible window.")
(defvar flyspell-lazy-hurry-flag   nil "Non-nil means hurrying is currently active.")
(defvar flyspell-lazy-debug        nil "Run in debug mode.")
(defvar flyspell-lazy-last-text    ""  "Last text checked by flyspell-lazy.")
(make-variable-buffer-local 'flyspell-lazy-hurry-flag)
(make-variable-buffer-local 'flyspell-lazy-local)

;;; macros

(defmacro flyspell-lazy--with-mocked-function (func ret-val &rest body)
  "Execute BODY, mocking FUNC (a symbol) to unconditionally return RET-VAL.

This is portable to versions of Emacs without dynamic `flet`."
  (declare (debug t) (indent 2))
  (let ((o (gensym "--function--")))
    `(let ((,o (ignore-errors (symbol-function ,func))))
       (fset ,func #'(lambda (&rest _ignored) ,ret-val))
       (unwind-protect
           (progn ,@body)
         (when ,o
           (fset ,func ,o))))))

(eval-and-compile
  (if (and
       (boundp 'flyspell-lazy-debug)
       flyspell-lazy-debug)
      (defmacro flyspell-lazy-debug-progn (&rest body)
        (declare (indent 0))
        `(progn ,@body))
    (defmacro flyspell-lazy-debug-progn (&rest body)
      (declare (indent 0)) t)))

(defmacro flyspell-lazy-called-interactively-p (&optional kind)
  "A backward-compatible version of `called-interactively-p'.

Optional KIND is as documented at `called-interactively-p'
in GNU Emacs 24.1 or higher."
  (cond
    ((not (fboundp 'called-interactively-p))
     '(interactive-p))
    ((condition-case nil
         (progn (called-interactively-p 'any) t)
       (error nil))
     `(called-interactively-p ,kind))
    (t
     '(called-interactively-p))))

;;; compatibility functions

(unless (fboundp 'string-match-p)
  ;; added in 23.x
  (defun string-match-p (regexp string &optional start)
    "Same as `string-match' except this function does not change the match data."
    (let ((inhibit-changing-match-data t))
      (string-match regexp string start))))

;;; utility functions

(defun flyspell-lazy-safe-bounds (start end)
  "Return START and END, ordered and limited by `point-min', `point-max'."
  (let ((bounds (sort (list start end) '<)))
    (list (max (car bounds) (point-min))
          (min (cadr bounds) (point-max)))))

(defun flyspell-lazy-safe-buffer-substring (start end)
  "Safer version of `buffer-substring-no-properties'.

START and END are as documented for `buffer-substring-no-properties'."
  (apply 'buffer-substring-no-properties
         (flyspell-lazy-safe-bounds start end)))

;; defsubsts

;; Yes, this looks like defsubst abuse, just trying
;; everything possible to make flyspell go faster.

;; These may be called from inside the spellcheck functions

(defsubst flyspell-lazy-checkable-buffer-p (&optional buffer)
  "Whether BUFFER is checkable."
  (callf or buffer (current-buffer))
  (when (memq buffer flyspell-lazy-buffer-list)
    buffer))

(defsubst flyspell-lazy-sort-and-merge-spans (nearby)
  "Operate on `flyspell-changes' directly, sorting and merging spans.

Depends on variables bound in `flyspell-lazy-refine-changes'."
  (let ((merged-changes nil))
    (dolist (chg (sort flyspell-changes #'(lambda (a b)
                                            (< (car a) (car b)))))
      (cond
        ;; accept the first span without change
        ((null merged-changes)
         (setq merged-changes (list chg)))
        ;; merge overlapping spans
        ((and (>= (car chg) (car (car (last merged-changes))))
              (<= (car chg) (cdr (car (last merged-changes)))))
         (setf (cdr (car (last merged-changes))) (cdr chg)))
        ;; merge nearby spans
        ((<= (abs (- (cdr (car (last merged-changes))) (car chg))) nearby)
         (setf (cdr (car (last merged-changes))) (cdr chg)))
        (t
         ;; keep this span unaltered
         (callf append merged-changes (list chg)))))
    (setq flyspell-changes merged-changes)))

;; This is the main bit of logic that allows flyspell-lazy
;; to invoke the check much less often.
(defsubst flyspell-lazy-refine-changes (&optional add-point)
  "Refine the list of edits found in `flyspell-changes'.

`flyspell-changes' contains a list of edits in the form of
cons cells, each representing the span of character positions
over which a modification occurred.

This function merges and tweaks the spans before they are
fed to `flyspell-region'.  The number of spans should be
reduced by an order of magnitude during busy edits.

When ADD-POINT is set, add a span around the current point."

  (when flyspell-changes

    (save-match-data
      (let* ((tinysize 5)
             (normalsize 40)
             (halfsize (round (* .5 normalsize)))
             (nearby 40))

        ;; optionally add a span including the point
        (when add-point
          (push (cons
                 (save-excursion (search-backward-regexp "[[:alpha:]]" (- (point) nearby) t))
                 (save-excursion (search-forward-regexp  "[[:alpha:]]" (+ (point) nearby) t)))
                flyspell-changes))

        ;; strip bogons
        (callf2 remove '(nil) flyspell-changes)

        ;; replace nils and single entries with integers
        (dolist (chg flyspell-changes)
          (unless (cdr chg)
            (setf (cdr chg) (+ (car chg) tinysize))))
        (dolist (chg flyspell-changes)
          (unless (car chg)
            (setf (car chg) (- (cdr chg) tinysize))))

        ;; always order min-to-max within cells
        (dolist (chg flyspell-changes)
          (when (> (car chg) (cdr chg))
            (let ((a (car chg))
                  (d (cdr chg)))
              (setf (cdr chg) a)
              (setf (car chg) d))))

        ;; sort and merge contiguous spans
        ;; we do this more than once.  here the purpose is to
        ;; reduce the number of spans for speed.
        (flyspell-lazy-sort-and-merge-spans nearby)

        ;; rectify spans that exceed buffer boundaries
        (dolist (chg flyspell-changes)
          (when (< (car chg) (point-min))
            (setf (car chg) (point-min)))
          (when (> (cdr chg) (point-max))
            (setf (cdr chg) (point-max))))

        ;; remove text-free spans
        (dolist (chg flyspell-changes)
          (unless (string-match-p "[[:alpha:]]" (buffer-substring-no-properties (car chg) (cdr chg)))
            (setf (car chg) nil)
            (setf (cdr chg) nil)))
        (callf2 remove '(nil) flyspell-changes)

        ;; extend span boundaries to whitespace breaks
        (dolist (chg flyspell-changes)
          (let ((newbound (save-excursion
                            (save-match-data
                              (goto-char (car chg))
                              (search-backward-regexp "[ \n\t\r\f]" (- (car chg) normalsize) t)))))
            (when newbound
              (setf (car chg) newbound)))
          (let ((newbound (save-excursion
                            (save-match-data
                              (goto-char (cdr chg))
                              (search-forward-regexp "[ \n\t\r\f]" (+ (cdr chg) normalsize) t)))))
            (when newbound
              (setf (cdr chg) newbound))))

        ;; remove spans without substantial words
        (let ((pattern (concat "[[:alpha:]]\\{" (format "%s" flyspell-lazy-minimum-word-length) ",\\}")))
          (dolist (chg flyspell-changes)
            (unless (string-match-p pattern (buffer-substring-no-properties (car chg) (cdr chg)))
              (setf (car chg) nil)
              (setf (cdr chg) nil)))
          (callf2 remove '(nil) flyspell-changes))

        ;; sort and merge contiguous spans, second pass
        (flyspell-lazy-sort-and-merge-spans nearby)

        ;; rectify spans that exceed buffer boundaries
        (dolist (chg flyspell-changes)
          (when (< (car chg) (point-min))
            (setf (car chg) (point-min)))
          (when (> (cdr chg) (point-max))
            (setf (cdr chg) (point-max))))

        ;; remove remaining tiny spans
        (dolist (chg flyspell-changes)
          (when (<= (abs (- (cdr chg) (car chg))) tinysize)
            (setf (car chg) nil)
            (setf (cdr chg) nil)))
        (callf2 remove '(nil) flyspell-changes)))))

(defsubst flyspell-lazy-strip-text (text)
  "Strip TEXT to prepare for comparison."
  (setq text (replace-regexp-in-string "[[:punct:]]+"                                        " " text))
  (setq text (replace-regexp-in-string "^[ \n\t\r\f]+"                                        "" text))
  (setq text (replace-regexp-in-string "^\\([^ \n\t\r\f]\\{1,3\\}\\([ \n\t\r\f]+\\|$\\)\\)+"  "" text))
  (setq text (replace-regexp-in-string "[ \n\t\r\f]+$"                                        "" text))
  (setq text (replace-regexp-in-string "\\(\\([ \n\t\r\f]+\\|^\\)[^ \n\t\r\f]\\{1,3\\}\\)+$"  "" text))
  text)

(defsubst flyspell-lazy-matches-last-text ()
  "True if `flyspell-changes' has one element, matching the last-checked text.

Whitespace, punctuation and short words are neglected.

This is used to avoid unneeded spell checks."
  (save-match-data
    (when (= 1 (length flyspell-changes))
      (let ((new-text (flyspell-lazy-strip-text
                       (flyspell-lazy-safe-buffer-substring
                        (car (car flyspell-changes))
                        (cdr (car flyspell-changes))))))
        (unless (get 'flyspell-lazy-last-text 'stripped)
          (callf flyspell-lazy-strip-text flyspell-lazy-last-text)
          (put 'flyspell-lazy-last-text 'stripped t))
        (flyspell-lazy-debug-progn
          (message "comparing %s / %s" flyspell-lazy-last-text new-text))
        (and (> (length flyspell-lazy-last-text) 0)
             (> (length new-text) 0)
             (equal flyspell-lazy-last-text new-text))))))

(defsubst flyspell-lazy-hurry (seconds)
  "Hurry `flyspell-lazy-timer' by SECONDS.

If SECONDS is nil or 0, turn off hurrying, reverting to
`flyspell-lazy-idle-seconds'.

If SECONDS is t, hurry by 1 second."
  (when (timerp flyspell-lazy-timer)
    (cond
      ((or (null seconds)
           (and (numberp seconds) (<= seconds 0)))
       (setq flyspell-lazy-hurry-flag nil)
       (timer-set-idle-time flyspell-lazy-timer flyspell-lazy-idle-seconds t))
      ((not (numberp seconds))
       (setq flyspell-lazy-hurry-flag t)
       (timer-set-idle-time flyspell-lazy-timer 1 t))
      (t
       (setq flyspell-lazy-hurry-flag t)
       (timer-set-idle-time flyspell-lazy-timer seconds t)))))

(defsubst flyspell-lazy-has-overlay (pos)
  "If POS has a flyspell overlay, return the overlay."
  (catch 'saw
    (dolist (ov (overlays-at pos))
      (when (flyspell-overlay-p ov)
        (throw 'saw ov)))
    nil))

;; These may be called from inside hooks on interactive commands

(defsubst flyspell-lazy-user-just-completed-word ()
  "Whether the user just completed a word."
  (and (= 1 (length (this-command-keys-vector)))
       ;; This is not a complete list of word-terminators, and it does not have to be.
       ;; For other cases, the regular idle timer will catch up with the typist.
       (memq (aref (this-command-keys-vector) 0) '(?\n ?\r ?\f ?\t ?\s ?, ?: ?! ?. ?? ?\" ?\( ?\) ?/))
       (not (minibufferp (current-buffer)))
       (not (ignore-errors (looking-back "[ \n\t\r\f,:!.?\"()/]\\{2\\}\\=")))))

(defsubst flyspell-lazy-prev-or-current-word-contains-error ()
  "Whether the previous or current word contains an error.

This function only looks backward, so it does not detect an
error marked in the current word if that overlay starts
after the point."
  (or (flyspell-lazy-has-overlay (point))
      (flyspell-lazy-has-overlay (1- (point)))
      (and (> (previous-overlay-change (point))
              (save-excursion
                (if (memq (char-before) '(?\n ?\r ?\f ?\t ?\s ?, ?: ?! ?. ?? ?\" ?\( ?\) ?/))
                    (or (search-backward-regexp "[^ \n\t\r\f,:!.?\"()/]" (- (point) 50) t) (point))
                  (point))))
           (flyspell-lazy-has-overlay (1- (previous-overlay-change (point)))))))

;; buffer functions

(defun flyspell-lazy-uncheck-buffer (&optional buffer)
  "Remove BUFFER from the list of checkable buffers."
  (callf or buffer (current-buffer))
  (callf2 remove buffer flyspell-lazy-buffer-list))

(defun flyspell-lazy-disallowed-buffer-p (&optional buffer)
  "Whether BUFFER is to be disallowed from checking."
  (callf or buffer (current-buffer))
  (or (flyspell-minibuffer-p buffer)
      (catch 'match
        (dolist (pat flyspell-lazy-disallow-buffers)
          (when (string-match-p pat (buffer-name buffer))
            (throw 'match (buffer-name buffer)))))))

;; hooks

(defun flyspell-lazy-after-change-function (start stop len)
  "Determine when to hurry the flyspell idle-timer.

Optionally, `flyspell-word' may be used to check the most
recent word.  See `flyspell-lazy-use-flyspell-word'.

START, STOP, and LEN are as passed to a hook on
`after-change-functions'."
  (save-match-data
    ;; hurry spellcheck timer based on number or size of recent edits
    (when (and (not flyspell-lazy-hurry-flag)
               (or (> (length flyspell-changes) flyspell-lazy-changes-threshold)
                   (> (abs (- stop start)) flyspell-lazy-size-threshold)))
      (flyspell-lazy-hurry .5))
    ;; hurry spellcheck timer if the user might have just corrected a word marked with error
    (when (and (not flyspell-lazy-extra-lazy)
               (or flyspell-lazy-use-flyspell-word (not flyspell-lazy-hurry-flag))
               (flyspell-lazy-user-just-completed-word)
               (flyspell-lazy-prev-or-current-word-contains-error))
      (flyspell-lazy-debug-progn
        (message "last completed word needs checking"))
      (if flyspell-lazy-use-flyspell-word
          (flyspell-word)
        (flyspell-lazy-hurry .3)))))

;; todo disable flyspell-lazy for just the current buffer,
;; keeping flyspell-mode as-is, without inflooping in hooks.
;; Is this function sufficient now?
(defun flyspell-lazy-unload (&optional global)
  "Remove timers and hooks used by `flyspell-lazy'.

If GLOBAL is set, removes global hook from `flyspell-mode-hook',
with the result that `flyspell-lazy' will no longer
be activated in every flyspell buffer."
  (when flyspell-mode
    (flyspell-mode-off))
  (when global
    (flyspell-lazy-debug-progn
      (message "unloading flyspell-lazy globally"))
    (setq flyspell-lazy-buffer-list nil)
    (remove-hook 'flyspell-mode-hook 'flyspell-lazy-load)
    (when (timerp flyspell-lazy-timer)
      (cancel-timer flyspell-lazy-timer))
    (when (timerp flyspell-lazy-window-timer)
      (cancel-timer flyspell-lazy-window-timer))
    (setq flyspell-lazy-timer nil)
    (setq flyspell-lazy-window-timer nil))
  (flyspell-lazy-debug-progn
    (message "unloading flyspell-lazy for buffer"))
  (setq flyspell-lazy-hurry-flag nil)
  (setq flyspell-lazy-local nil)
  (flyspell-lazy-uncheck-buffer)
  (remove-hook 'after-change-functions 'flyspell-lazy-after-change-function t))

(defun flyspell-lazy-load ()
  "Setup for `flyspell-lazy'.  Designed to be used inside `flyspell-mode-hook'."

  (if (or (flyspell-lazy-disallowed-buffer-p (current-buffer))
          (not flyspell-mode))

      ;; unload for only this buffer - working?
      (flyspell-lazy-unload)

    ;; else do setup
    (flyspell-lazy-debug-progn
      (message "setting up flyspell-lazy for buffer"))

    (setq flyspell-lazy-local t)
    (add-to-list 'flyspell-lazy-buffer-list (current-buffer))

    (set (make-local-variable 'flyspell-large-region) 1)

    (when (and flyspell-lazy-single-ispell
               (not ispell-process))
      (ispell-set-spellchecker-params))

    (unless (> flyspell-lazy-idle-seconds 0)
      (setq flyspell-lazy-idle-seconds 1))

    (unless (numberp flyspell-lazy-minimum-word-length)
      (setq flyspell-lazy-minimum-word-length 1))
    (callf round flyspell-lazy-minimum-word-length)
    (unless (> flyspell-lazy-minimum-word-length 0)
      (setq flyspell-lazy-minimum-word-length 1))

    ;; Remove hooks that bog down responsiveness.  These are the main
    ;; things that bog down Cocoa Emacs.
    (remove-hook 'post-command-hook      (function flyspell-post-command-hook) t)
    (remove-hook 'pre-command-hook       (function flyspell-pre-command-hook) t)
    (remove-hook 'pre-command-hook       (function flyspell-auto-correct-previous-hook) t)

    ;; todo Still using the data gathered by this hook, though it seems like
    ;;      a more clever idea would be to remove it as well and then piggyback
    ;;      spellchecking on the data in buffer-undo-list.
    ;; (remove-hook 'after-change-functions 'fly-spell-after-change-function t)

    ;; Add the hooks and timers used by flyspell-lazy, which are hopefully
    ;; more efficient than the above.
    (unless (and flyspell-lazy-timer
                 (memq flyspell-lazy-timer timer-idle-list))
      (setq flyspell-lazy-timer (run-with-idle-timer flyspell-lazy-idle-seconds t 'flyspell-lazy-check-pending)))

    (unless (and flyspell-lazy-window-timer
                 (memq flyspell-lazy-window-timer timer-idle-list))
      (setq flyspell-lazy-window-timer (run-with-idle-timer flyspell-lazy-window-idle-seconds t 'flyspell-lazy-check-visible)))

    (add-hook 'kill-buffer-hook #'(lambda ()
                                    (with-demoted-errors (flyspell-lazy-uncheck-buffer))))
    (add-hook 'after-change-functions 'flyspell-lazy-after-change-function nil t)))

;; spellchecker functions

(defun flyspell-lazy-check-pending ()
  "Check spelling on edits recorded in `flyspell-changes'.

This is the primary driver for `flyspell-lazy'."
  (flyspell-lazy-debug-progn
    (message "firing do-check"))
  (with-local-quit
    (let ((buf (current-buffer)))
      (when (flyspell-lazy-checkable-buffer-p buf)
        (with-current-buffer buf   ; trying to defensively code against timer firing in wrong buffer
          (flyspell-lazy-debug-progn
            (message "checking in buffer: %s" buf))
          (if (not flyspell-changes)
              (when flyspell-lazy-hurry-flag
                (flyspell-lazy-hurry nil))
            (when (not (input-pending-p))
              (when flyspell-lazy-hurry-flag
                (flyspell-lazy-hurry nil))
              (flyspell-lazy-debug-progn
                (message "raw changes: %s" flyspell-changes)
                (message "number of raw changes: %s" (length flyspell-changes)))
              (flyspell-lazy-refine-changes 'add-point)
              (flyspell-lazy-debug-progn
                (message "refined changes: %s" flyspell-changes)
                (message "number of refined changes: %s" (length flyspell-changes))
                (message "testing against last-text: %s" flyspell-lazy-last-text))
              (unless (flyspell-lazy-matches-last-text)
                (flyspell-lazy-debug-progn
                  (message "no match to cleaned last-text: %s" flyspell-lazy-last-text))
                (while (and (not (input-pending-p))
                            (consp flyspell-changes)
                            (eq buf (current-buffer)))                ; should not be needed, trying to work around bug
                  (save-excursion
                    (let ((start (max (point-min) (car (car flyspell-changes))))
                          (end   (min (point-max) (cdr (car flyspell-changes))))
                          (flyspell-issue-message-flag nil))          ; improves performance
                      (flyspell-lazy-debug-progn
                        (message "checking region: %s to %s" start end)
                        (move-overlay compilation-highlight-overlay start end)
                        (redisplay)
                        (sleep-for .5)
                        (compilation-goto-locus-delete-o))
                      (setq flyspell-lazy-last-text
                            (flyspell-lazy-safe-buffer-substring start end))
                      (put 'flyspell-lazy-last-text 'stripped nil)
                      (with-timeout (1 (message "Spellcheck interrupted"))
                        (if flyspell-lazy-single-ispell
                            (flyspell-lazy--with-mocked-function 'ispell-set-spellchecker-params t
                              (flyspell-lazy--with-mocked-function 'flyspell-accept-buffer-local-defs t
                                (apply 'flyspell-region (flyspell-lazy-safe-bounds start end))))
                          (apply 'flyspell-region (flyspell-lazy-safe-bounds start end))))))
                  (pop flyspell-changes))
                (flyspell-lazy-debug-progn
                  (message "leftover changes: %s" flyspell-changes)
                  (message "number of leftover changes: %s" (length flyspell-changes)))))))))))

(defun flyspell-lazy-check-visible ()
  "Check spelling on the visible window."
  (flyspell-lazy-debug-progn
    (message "firing do-window-check"))
  (with-local-quit
    (let ((buf (current-buffer)))
      (when (and (flyspell-lazy-checkable-buffer-p buf)
                 (not (input-pending-p)))
        (with-current-buffer buf
          (flyspell-lazy-debug-progn
            (message "checking in buffer: %s" buf))
          (when flyspell-lazy-hurry-flag
            (flyspell-lazy-hurry nil))
          (save-excursion
            (let ((start (window-start))
                  (end   (window-end))
                  (flyspell-issue-message-flag nil))      ; improves performance
              (flyspell-lazy-debug-progn
                (move-overlay compilation-highlight-overlay start end)
                (redisplay)
                (sleep-for .5)
                (compilation-goto-locus-delete-o))
              ;; compensate for inaccuracy of window-end
              (setq end (min (+ end (window-width)) (point-max)))
              ;; move to word boundaries
              (setq start (save-excursion
                            (save-match-data
                              (goto-char start)
                              (search-backward-regexp "[ \n\t\r\f]" (- (point) 50) t)
                              (point))))
              (setq end (save-excursion
                          (save-match-data
                            (goto-char end)
                            (search-forward-regexp "[ \n\t\r\f]" (+ (point) 50) t)
                            (point))))
              (with-timeout (1 (message "Spellcheck interrupted"))
                (if flyspell-lazy-single-ispell
                            (flyspell-lazy--with-mocked-function 'ispell-set-spellchecker-params t
                              (flyspell-lazy--with-mocked-function 'flyspell-accept-buffer-local-defs t
                                (flyspell-region start end)))
                  (flyspell-region start end))))))))))

;; todo not in use - this is difficult to fit into the flyspell model
;;      for small regions, may have to advise flyspell-get-word, which returns a list, the word being the first element
;;      for large regions, may have to advise ispell-call-process-region - maybe creating a temp buffer with the stripped region
;; (defun flyspell-lazy-strip-symbols (text)
;;   ;; shell/perl-style variables with sigils
;;   (setq (text (replace-regexp-in-string "[$@%]\\w+\\(\\[[^ \n\t\r\f]+?\\]\\|{[^ \n\t\r\f]+?}\\)" " " text)))
;;   ;; lisp-style variables with dashes
;;   (setq (text (replace-regexp-in-string "\\(?:[^a-zA-Z0-9-]\\|^\\)\\w+\\(?:-+\\w+\\)\\{2,\\}\\(?:[^a-zA-Z0-9-]\\|\\'\\)" " " text)))
;;   (let ((case-fold-search nil))
;;     ;; CamelCase
;;     (setq text (replace-regexp-in-string "\\<\\(?:[A-Z][a-z0-9]+\\)\\(?:[A-Z][a-z0-9]+\\|[A-Z]\\{3,\\}\\)+\\>" " " text))
;;     ;; ACRONYMS
;;     (setq text (replace-regexp-in-string "\\<[A-Z]\\{3,\\}" " " text))))

;;; minor mode definition

;;;###autoload
(define-minor-mode flyspell-lazy-mode
  "Turn on flyspell-lazy-mode.

Turning on flyspell-lazy-mode will set up hooks which
change how `flyspell-mode' works, in every buffer for which
flyspell is enabled.

When called interactively with no prefix argument this command
toggles the mode.  With a prefix argument, it enables the mode
if the argument is positive and otherwise disables the mode.

When called from Lisp, this command enables the mode if the
argument is omitted or nil, and toggles the mode if the argument
is 'toggle."
  :group 'flyspell-lazy
  :global t
  (cond
   (flyspell-lazy-mode
    (add-hook 'flyspell-mode-hook 'flyspell-lazy-load t)
    (when (and (flyspell-lazy-called-interactively-p 'interactive)
               (not flyspell-lazy-less-feedback))
      (message "flyspell-lazy mode enabled")))
   (t
    (flyspell-lazy-unload 'global)
    (when (and (flyspell-lazy-called-interactively-p 'interactive)
               (not flyspell-lazy-less-feedback))
      (message "flyspell-lazy mode disabled")))))

;;; interactive commands

;;;###autoload
(defun flyspell-lazy-check-buffer (&optional force)
  "Check spelling on the whole buffer, respecting flyspell-lazy settings.

With optional FORCE, force spell-check even on a buffer which
would usually be skipped."
  (interactive)
  (with-local-quit
    (if (or (not (and flyspell-lazy-local flyspell-lazy-mode))
            (and (not force)
                 (not (flyspell-lazy-checkable-buffer-p (current-buffer)))))
        (message "Skipping spellcheck on buffer %s." (current-buffer))
      ;; else
      (with-timeout (5 (message "Spellcheck interrupted"))
        (when font-lock-mode
          (let ((font-lock-fontify-buffer-function 'font-lock-default-fontify-buffer))
            (font-lock-fontify-buffer)))
        (if flyspell-lazy-single-ispell
            (flyspell-lazy--with-mocked-function 'ispell-set-spellchecker-params t
              (flyspell-lazy--with-mocked-function 'flyspell-accept-buffer-local-defs t
                (flyspell-buffer)))
          ;; else
          (flyspell-buffer))))))

(provide 'flyspell-lazy)

;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions redefine)
;; End:
;;
;; LocalWords: FlyspellLazy aspell setq args prog flyspell's flet
;; LocalWords: callf setf flylz nils defsubsts defsubst checkable
;; LocalWords: inflooping punct devel
;;

;;; flyspell-lazy.el ends here
