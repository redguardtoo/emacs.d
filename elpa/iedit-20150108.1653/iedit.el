;;; iedit.el --- Edit multiple regions in the same way simultaneously.

;; Copyright (C) 2010, 2011, 2012 Victor Ren

;; Time-stamp: <2013-10-07 11:26:05 Victor Ren>
;; Author: Victor Ren <victorhge@gmail.com>
;; Keywords: occurrence region simultaneous refactoring
;; Version: 0.97
;; X-URL: http://www.emacswiki.org/emacs/Iedit
;; Compatibility: GNU Emacs: 22.x, 23.x, 24.x

;; This file is not part of GNU Emacs, but it is distributed under
;; the same terms as GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This package is an Emacs minor mode and allows you to edit one occurrence of
;; some text in a buffer (possibly narrowed) or region, and simultaneously have
;; other occurrences edited in the same way.
;;
;; Normal scenario of iedit-mode is like:
;;
;; - Highlight certain contents - by press C-; (The default binding)
;;   All occurrences of a symbol, string in the buffer or a region may be
;;   highlighted corresponding to current mark, point and prefix argument.
;;   Refer to the document of `iedit-mode' for details.
;;
;; - Edit one of the occurrences
;;   The change is applied to other occurrences simultaneously.
;;
;; - Finish - by pressing C-; again
;;
;; You can also use Iedit mode as a quick way to temporarily show only the
;; buffer lines that match the current text being edited.  This gives you the
;; effect of a temporary `keep-lines' or `occur'.  To get this effect, hit C-'
;; when in Iedit mode - it toggles hiding non-matching lines.
;;
;; Renaming refactoring is convenient in Iedit mode
;;
;; - The symbol under point is selected as occurrence by default and only
;;   complete symbols are matched
;; - With digit prefix argument 0, only symbols in current function are matched
;; - Restricting symbols in current region can be done by pressing C-; again
;; - Last renaming refactoring is remembered and can be applied to other buffers
;;   later
;;
;; There are also some other facilities you may never think about.  Refer to the
;; document of function `iedit-mode' (C-h f iedit-mode RET) for more details.

;; The code was developed and fully tested on Gnu Emacs 24.0.93, partially
;; tested on Gnu Emacs 22. If you have any compatible problem, please let me
;; know.

;;; todo:
;; - Add more easy access keys for whole occurrence

;;; Contributors
;; Adam Lindberg <eproxus@gmail.com> added a case sensitivity option that can be toggled.

;; Tassilo Horn <tassilo@member.fsf.org> added an option to match only complete
;; words, not inside words

;; Le Wang <l26wang@gmail.com> proposed to match only complete symbols,  not
;; inside symbols, contributed rectangle support

;;; Code:

(eval-when-compile (require 'cl))
(require 'iedit-lib)

(defcustom iedit-current-symbol-default t
  "If no-nil, use current symbol by default for the occurrence."
  :type 'boolean
  :group 'iedit)

(defcustom iedit-only-at-symbol-boundaries t
  "If no-nil, matches have to start and end at symbol boundaries.
For example, when invoking command `iedit-mode' on the \"in\" in the
  sentence \"The king in the castle...\", the \"king\" is not
  edited."
  :type 'boolean
  :group 'iedit)

(defcustom iedit-toggle-key-default (kbd "C-;")
  "If no-nil, the key is inserted into global-map, isearch-mode-map, esc-map and help-map."
  :type 'vector
  :group 'iedit)

(defvar iedit-mode-hook nil
  "Function(s) to call after starting up an iedit.")

(defvar iedit-mode-end-hook nil
  "Function(s) to call after terminating an iedit.")

(defvar iedit-mode nil) ;; Name of the minor mode

(defvar iedit-only-complete-symbol-local nil
  "This is buffer local variable which indicates the occurrence
only matches complete symbol.")

(defvar iedit-only-complete-symbol-global nil
  "This is global variable which indicates the last global occurrence
only matches complete symbol.")

(defvar iedit-last-occurrence-local nil
  "This is buffer local variable which is the occurrence when
Iedit mode is turned off last time.")

(defvar iedit-last-occurrence-global nil
  "This is global variable which is the occurrence when
Iedit mode is turned off last time.")

(defvar iedit-last-initial-string-global nil
  "This is a global variable which is the last initial occurrence string.")

(defvar iedit-initial-string-local nil
  "This is buffer local variable which is the initial string to start Iedit mode.")
(defvar iedit-initial-region nil
  "This is buffer local variable which is the initial region
where Iedit mode is started from.")

(defvar iedit-num-lines-to-expand-up 0
  "This is a global variable indicating how many lines up from
point should be included in the replacement region.")

(defvar iedit-num-lines-to-expand-down 0
  "This is a global variable indicating how many lines down from
point should be included in the replacement region.")

(defvar iedit-current-symbol '(lambda () (current-word t))
  "This is a function which returns a string as occurrence candidate.
This local buffer varialbe can be configured in some modes.
An example of how to use this variable: todo")

(make-variable-buffer-local 'iedit-mode)
(make-variable-buffer-local 'iedit-only-complete-symbol-local)
(make-variable-buffer-local 'iedit-last-occurrence-local)
(make-variable-buffer-local 'iedit-initial-string-local)
(make-variable-buffer-local 'iedit-initial-region)
(make-variable-buffer-local 'iedit-current-symbol)

(or (assq 'iedit-mode minor-mode-alist)
    (nconc minor-mode-alist
           (list '(iedit-mode iedit-mode))))

;;; Define iedit help map.
(eval-when-compile (require 'help-macro))

(defvar iedit-help-map
  (let ((map (make-sparse-keymap)))
    (define-key map (char-to-string help-char) 'iedit-help-for-help)
    (define-key map [help] 'iedit-help-for-help)
    (define-key map [f1] 'iedit-help-for-help)
    (define-key map "?" 'iedit-help-for-help)
    (define-key map "b" 'iedit-describe-bindings)
    (define-key map "k" 'iedit-describe-key)
    (define-key map "m" 'iedit-describe-mode)
    (define-key map "q" 'help-quit)
    map)
  "Keymap for characters following the Help key for Iedit mode.")

(make-help-screen
 iedit-help-for-help-internal
 (purecopy "Type a help option: [bkm] or ?")
 "You have typed %THIS-KEY%, the help character.  Type a Help option:
\(Type \\<help-map>\\[help-quit] to exit the Help command.)

b           Display all Iedit key bindings.
k KEYS      Display full documentation of Iedit key sequence.
m           Display documentation of Iedit mode.

You can't type here other help keys available in the global help map,
but outside of this help window when you type them in Iedit mode,
they exit Iedit mode before displaying global help."
 iedit-help-map)

(defun iedit-help-for-help ()
  "Display Iedit help menu."
  (interactive)
  (let (same-window-buffer-names same-window-regexps)
    (iedit-help-for-help-internal)))

(defun iedit-describe-bindings ()
  "Show a list of all keys defined in Iedit mode, and their definitions.
This is like `describe-bindings', but displays only Iedit keys."
  (interactive)
  (let (same-window-buffer-names
        same-window-regexps
        (keymap (substitute-command-keys "\\{iedit-mode-keymap}\\{iedit-mode-occurrence-keymap}")))
    (with-help-window "*Help*"
      (with-current-buffer standard-output
        (princ "Iedit Mode Bindings: ")
        (princ keymap)))))

(defun iedit-describe-key ()
  "Display documentation of the function invoked by Iedit mode key."
  (interactive)
  (let (same-window-buffer-names same-window-regexps)
    (call-interactively 'describe-key)))

(defun iedit-describe-mode ()
  "Display documentation of Iedit mode."
  (interactive)
  (let (same-window-buffer-names same-window-regexps)
    (describe-function 'iedit-mode)))

;;; Default key bindings:
(when iedit-toggle-key-default
  (define-key global-map iedit-toggle-key-default 'iedit-mode)
  (define-key isearch-mode-map iedit-toggle-key-default 'iedit-mode-from-isearch)
  (define-key esc-map iedit-toggle-key-default 'iedit-execute-last-modification)
  (define-key help-map iedit-toggle-key-default 'iedit-mode-toggle-on-function))

;; Avoid to restore Iedit mode when restoring desktop
(add-to-list 'desktop-minor-mode-handlers
             '(iedit-mode . nil))

;;; Define iedit help map.
(eval-when-compile (require 'help-macro))

(defvar iedit-mode-occurrence-keymap
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map iedit-occurrence-keymap-default)
    (define-key map (kbd "M-H") 'iedit-restrict-function)
    (define-key map (kbd "M-I") 'iedit-restrict-current-line)
    (define-key map (kbd "M-{") 'iedit-expand-up-a-line)
    (define-key map (kbd "M-}") 'iedit-expand-down-a-line)
    (define-key map (kbd "M-G") 'iedit-apply-global-modification)
    (define-key map (kbd "M-C") 'iedit-toggle-case-sensitive)
    map)
  "Keymap used within overlays in Iedit mode.")

(defvar iedit-mode-keymap
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map iedit-lib-keymap)
    (define-key map (char-to-string help-char) iedit-help-map)
    (define-key map [help] iedit-help-map)
    (define-key map [f1] iedit-help-map)
    (define-key map (kbd "M-;") 'iedit-toggle-selection)
    map)
  "Keymap used while Iedit mode is enabled.")

;;; Define Iedit mode map
(or (assq 'iedit-mode minor-mode-map-alist)
    (setq minor-mode-map-alist
          (cons (cons 'iedit-mode iedit-mode-keymap) minor-mode-map-alist)))

;; Avoid to restore Iedit mode when restoring desktop
(add-to-list 'desktop-minor-mode-handlers
             '(iedit-mode . nil))

;;;###autoload
(defun iedit-mode (&optional arg)
  "Toggle Iedit mode.
This command behaves differently, depending on the mark, point,
prefix argument and variable `iedit-transient-mark-sensitive'.

If Iedit mode is off, turn Iedit mode on.

When Iedit mode is turned on, all the occurrences of the current
region in the buffer (possibly narrowed) or a region are
highlighted.  If one occurrence is modified, the change are
propagated to all other occurrences simultaneously.

If region is not active, the current symbol (returns from
`iedit-current-symbol') is used as the occurrence by default.
The occurrences of the current symbol, but not include
occurrences that are part of other symbols, are highlighted.  If
you still want to match all the occurrences, even though they are
parts of other symbols, you may have to mark the symbol first.

In the above two situations, with digit prefix argument 0, only
occurrences in current function are matched.  This is good for
renaming refactoring in programming.

You can also switch to Iedit mode from isearch mode directly. The
current search string is used as occurrence.  All occurrences of
the current search string are highlighted.

With an universal prefix argument, the occurrence when Iedit mode
is turned off last time in current buffer is used as occurrence.
This is intended to recover last Iedit mode which is turned off.
If region active, Iedit mode is limited within the current
region.

With repeated universal prefix argument, the occurrence when
Iedit mode is turned off last time (might be in other buffer) is
used as occurrence.  If region active, Iedit mode is limited
within the current region.

If Iedit mode is on and region is active, Iedit mode is
restricted in the region, e.g. the occurrences outside of the
region is excluded.

If Iedit mode is on and region is active, with an universal
prefix argument, Iedit mode is restricted outside of the region,
e.g. the occurrences in the region is excluded.

Turn off Iedit mode in other situations.

Commands:
\\{iedit-mode-keymap}
Keymap used within overlays:
\\{iedit-mode-occurrence-keymap}"
  (interactive "P")
  (if iedit-mode
      (progn
        (iedit-mode-on-action arg)
        (setq iedit-only-complete-symbol-global iedit-only-complete-symbol-local))
    (iedit-barf-if-lib-active)
    (let (occurrence
          complete-symbol
          (beg (if (eq major-mode 'occur-edit-mode) ; skip the first occurrence
                   (next-single-char-property-change 1 'read-only)
                 (point-min)))
          (end (point-max)))
      (cond ((and arg
                  (= 4 (prefix-numeric-value arg))
                  iedit-last-occurrence-local)
             (setq occurrence iedit-last-occurrence-local)
             (setq complete-symbol iedit-only-complete-symbol-local))
            ((and arg
                  (= 16 (prefix-numeric-value arg))
                  iedit-last-initial-string-global)
             (setq occurrence iedit-last-initial-string-global)
             (setq complete-symbol iedit-only-complete-symbol-global))
            ((iedit-region-active)
             (setq occurrence  (buffer-substring-no-properties
                                (mark) (point))))
            ((and iedit-current-symbol-default
                  (setq occurrence (funcall iedit-current-symbol)))
             (when iedit-only-at-symbol-boundaries
               (setq complete-symbol t)))
            (t (error "No candidate of the occurrence, cannot enable Iedit mode")))
      (when arg
        (if (= 0 (prefix-numeric-value arg))
            (save-excursion
              (mark-defun)
              (setq beg (region-beginning))
              (setq end (region-end)))
          (when (iedit-region-active)
            (setq beg (region-beginning))
            (setq end (region-end)))))
      (setq iedit-only-complete-symbol-local complete-symbol)
      (setq mark-active nil)
      (run-hooks 'deactivate-mark-hook)
      (setq iedit-initial-string-local occurrence)
      (iedit-start (iedit-regexp-quote occurrence) beg end))))

(defun iedit-mode-from-isearch (regexp)
  "Start Iedit mode using last search string as the regexp."
  (interactive
   (let ((regexp (cond
                  ((functionp isearch-word)
                   (funcall isearch-word isearch-string))
                  (isearch-word (word-search-regexp isearch-string))
                  (isearch-regexp isearch-string)
                  (t (regexp-quote isearch-string)))))
     (list regexp)))
  (or isearch-success
      (error "No match" ))
  (if (or isearch-regexp isearch-word)
      nil
    (setq iedit-initial-string-local isearch-string))
  (let ((iedit-case-sensitive (not isearch-case-fold-search)))
    (isearch-exit)
    (setq mark-active nil)
    (run-hooks 'deactivate-mark-hook)
    (when iedit-mode
      (iedit-cleanup))
    (iedit-start regexp (point-min) (point-max))
    ;; TODO: reconsider how to avoid the loop in iedit-same-length
    (cond ((not iedit-occurrences-overlays)
           (message "No matches found")
           (iedit-done))
          ((not (iedit-same-length))
           (message "Matches are not the same length.")
           (iedit-done)))))

(defun iedit-start (occurrence-regexp beg end)
  "Start Iedit mode for the `occurrence-regexp' in the current buffer."

  ;; enforce skip modification once, errors may happen to cause this to be
  ;; unset.
  (setq iedit-skip-modification-once t)
  (setq iedit-unmatched-lines-invisible iedit-unmatched-lines-invisible-default)
  (setq iedit-initial-region (list beg end))
  (message "%d matches for \"%s\""
           (iedit-start2 occurrence-regexp beg end)
           (iedit-printable occurrence-regexp))
  (run-hooks 'iedit-mode-hook)
  (add-hook 'kbd-macro-termination-hook 'iedit-done nil t)
  (add-hook 'change-major-mode-hook 'iedit-done nil t)
  (add-hook 'iedit-aborting-hook 'iedit-done nil t))

(defun iedit-regexp-quote (exp)
  "Return a regexp string."
  (if iedit-only-complete-symbol-local
      (concat "\\_<" (regexp-quote exp) "\\_>")
    (regexp-quote exp)))

(defun iedit-start2 (occurrence-regexp beg end)
  "Refresh Iedit mode."
  (setq iedit-occurrence-keymap iedit-mode-occurrence-keymap)
  (let ((counter(iedit-make-occurrences-overlays occurrence-regexp beg end)))
    (setq iedit-mode
          (propertize
           (concat " Iedit:" (number-to-string counter))
           'face
           'font-lock-warning-face))
    (force-mode-line-update)
    counter))

(defun iedit-done ()
  "Exit Iedit mode.
Save the current occurrence string locally and globally.  Save
the initial string globally."
  (when iedit-buffering
      (iedit-stop-buffering))
  (setq iedit-last-occurrence-local (iedit-current-occurrence-string))
  (setq iedit-last-occurrence-global iedit-last-occurrence-local)
  (setq iedit-last-initial-string-global iedit-initial-string-local)
  (if iedit-last-occurrence-local
      (kill-new iedit-last-occurrence-local)) ; Make occurrence the latest kill in the kill ring.
  (setq iedit-num-lines-to-expand-up 0)
  (setq iedit-num-lines-to-expand-down 0)

  (iedit-cleanup)

  (setq iedit-initial-string-local nil)
  (setq iedit-mode nil)
  (force-mode-line-update)
  (remove-hook 'kbd-macro-termination-hook 'iedit-done t)
  (remove-hook 'change-major-mode-hook 'iedit-done t)
  (remove-hook 'iedit-aborting-hook 'iedit-done t)
  (run-hooks 'iedit-mode-end-hook))

(defun iedit-mode-on-action (&optional arg)
  "Turn off Iedit mode or restrict it in a region if region is active."
  (if (iedit-region-active)
      ;; Restrict iedit-mode
      (let ((beg (region-beginning))
            (end (region-end)))
        (if (null (iedit-find-overlay beg end 'iedit-occurrence-overlay-name arg))
            (iedit-done)
          (iedit-restrict-region beg end arg)))
    (iedit-done)))


;;;###autoload
(defun iedit-mode-toggle-on-function ()
  "Toggle Iedit mode on current function."
  (interactive)
  (iedit-mode 0))

(defun iedit-execute-last-modification (&optional arg)
  "Apply last modification in Iedit mode to the current buffer or an active region."
  (interactive "*P")
  (or (and iedit-last-initial-string-global
           (not (string= iedit-last-initial-string-global iedit-last-occurrence-global)))
      (error "No modification available"))
  (let ((occurrence-exp (regexp-quote iedit-last-initial-string-global))
        (replacement  iedit-last-occurrence-global)
        (case-fold-search (not iedit-case-sensitive))
        beg end)
    (when case-fold-search
      (setq occurrence-exp (downcase occurrence-exp))
      (setq replacement (downcase replacement)))
    (if iedit-only-complete-symbol-global
        (setq occurrence-exp (concat "\\_<"  occurrence-exp "\\_>")))
    (when (iedit-region-active)
      (setq beg (region-beginning))
      (setq end (region-end)))
    (perform-replace occurrence-exp replacement t t nil nil nil beg end)))

(defun iedit-apply-global-modification ()
  "Apply last global modification."
  (interactive "*")
  (if (and iedit-last-initial-string-global
           (string= iedit-initial-string-local iedit-last-initial-string-global)
           (not (string= iedit-last-initial-string-global iedit-last-occurrence-global)))
      (iedit-replace-occurrences iedit-last-occurrence-global)
    (message "No global modification available.")))

(defun iedit-toggle-selection ()
  "Select or deselect the occurrence under point."
  (interactive)
  (iedit-barf-if-buffering)
  (let ((ov (iedit-find-current-occurrence-overlay)))
    (if ov
        (iedit-restrict-region (overlay-start ov) (overlay-end ov) t)
      (let ((current-occurrence-string (iedit-current-occurrence-string)))
        (when (not (null current-occurrence-string))
          (save-excursion
            (goto-char (if (> (point) (length current-occurrence-string))
                           ( - (point) (length current-occurrence-string))
                         (point-min)))
            (iedit-add-next-occurrence-overlay
             (iedit-regexp-quote current-occurrence-string)))
          (setq iedit-mode (propertize
                            (concat " Iedit:" (number-to-string
                                               (length iedit-occurrences-overlays)))
                            'face 'font-lock-warning-face))
          (force-mode-line-update))))))

(defun iedit-restrict-function(&optional arg)
  "Restricting Iedit mode in current function."
  (interactive "P")
  (save-excursion
    (mark-defun)
    (iedit-restrict-region (region-beginning) (region-end) arg))
  (message "Restricted in current function, %d matches."
           (length iedit-occurrences-overlays)))

(defun iedit-restrict-current-line ()
  "Restrict Iedit mode to current line."
  (interactive)
  (iedit-restrict-region (iedit-char-at-bol) (iedit-char-at-eol))
  (message "Restricted to current line, %d match%s."
           (length iedit-occurrences-overlays)
           (if (= 1 (length iedit-occurrences-overlays)) "" "es")))

(defun iedit-expand-by-a-line (where amount)
  "After restricting iedit to the current line with
`iedit-restrict-current-line', this function expands the top or
bottom of the search region upwards or downwards by `amount'
lines. The region being acted upon is controlled with
`where' ('top to act on the top, anything else for the
bottom). With a prefix, collapses the top or bottom of the search
region by `amount' lines."
  (interactive "P")
  ;; Since iedit-done resets iedit-num-lines-to-expand-{down,up}, we
  ;; have to hang on to them in tmp variables
  (let ((tmp-up iedit-num-lines-to-expand-up)
        (tmp-down iedit-num-lines-to-expand-down)
        ;; we want to call iedit-mode with a universal prefix arg
        (current-prefix-arg '(4)))
    (iedit-done)
    (call-interactively 'iedit-mode)
    (setq iedit-num-lines-to-expand-up tmp-up)
    (setq iedit-num-lines-to-expand-down tmp-down)
    (if (eq where 'top)
        (setq iedit-num-lines-to-expand-up (max 0
                                                (+ amount iedit-num-lines-to-expand-up)))
      (setq iedit-num-lines-to-expand-down (max 0
                                                (+ amount iedit-num-lines-to-expand-down))))
    (iedit-restrict-region (iedit-char-at-bol (- iedit-num-lines-to-expand-up))
                           (iedit-char-at-eol iedit-num-lines-to-expand-down))
    (message "Now looking -%d/+%d lines around current line, %d match%s."
             iedit-num-lines-to-expand-up
             iedit-num-lines-to-expand-down
             (length iedit-occurrences-overlays)
             (if (= 1 (length iedit-occurrences-overlays)) "" "es"))))

(defun iedit-expand-up-a-line (&optional arg)
  "After restricting iedit to the current line with
`iedit-restrict-current-line', this function expands the search
region upwards by one line. With a prefix, bring the top of the
region back down one line."
  (interactive "P")
  (iedit-expand-by-a-line 'top
                          (if arg -1 1)))

(defun iedit-expand-down-a-line (&optional arg)
  "After restricting iedit to the current line with
`iedit-restrict-current-line', this function expands the search
region downwards by one line. With a prefix, bring the bottom of
the region back up one line."
  (interactive "P")
  (iedit-expand-by-a-line 'bottom
                          (if arg -1 1)))

(defun iedit-restrict-region (beg end &optional inclusive)
  "Restricting Iedit mode in a region."
  (when iedit-buffering
    (iedit-stop-buffering))
  (setq iedit-last-occurrence-local (iedit-current-occurrence-string))
  (setq mark-active nil)
  (run-hooks 'deactivate-mark-hook)
  (iedit-show-all)
  (iedit-cleanup-occurrences-overlays beg end inclusive)
  (if iedit-unmatched-lines-invisible
      (iedit-hide-unmatched-lines iedit-occurrence-context-lines))
  (setq iedit-mode (propertize
                    (concat " Iedit:" (number-to-string
                                       (length iedit-occurrences-overlays)))
                    'face 'font-lock-warning-face))
  (force-mode-line-update))

(defun iedit-toggle-case-sensitive ()
  "Toggle case-sensitive matching occurrences. "
  (interactive)
  (setq iedit-case-sensitive (not iedit-case-sensitive))
  (if iedit-buffering
      (iedit-stop-buffering))
  (setq iedit-last-occurrence-local (iedit-current-occurrence-string))
  (when iedit-last-occurrence-local
    (remove-overlays nil nil iedit-occurrence-overlay-name t)
    (iedit-show-all)
    (let* ((occurrence-regexp (iedit-regexp-quote iedit-last-occurrence-local))
           (begin (car iedit-initial-region))
           (end (cadr iedit-initial-region))
           (counter (iedit-start2 occurrence-regexp begin end)))
      (message "iedit %s. %d matches for \"%s\""
               (if iedit-case-sensitive
                   "is case sensitive"
                 "ignores case")
               counter
               (iedit-printable occurrence-regexp)))))

(provide 'iedit)

;;; iedit.el ends here

;;  LocalWords:  iedit el MERCHANTABILITY kbd isearch todo ert Lindberg Tassilo
;;  LocalWords:  eval defgroup defcustom boolean defvar assq alist nconc
;;  LocalWords:  substring cadr keymap defconst purecopy bkm defun princ prev
;;  LocalWords:  iso lefttab backtab upcase downcase concat setq autoload arg
;;  LocalWords:  refactoring propertize cond goto nreverse progn rotatef eq elp
;;  LocalWords:  dolist pos unmatch args ov sReplace iedit's cdr quote'ed
