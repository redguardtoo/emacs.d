;;; avy-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (avy-goto-char-timer avy-setup-default avy-copy-region
;;;;;;  avy-move-line avy-copy-line avy-goto-line avy-goto-subword-1
;;;;;;  avy-goto-subword-0 avy-goto-word-1 avy-goto-word-0 avy-isearch
;;;;;;  avy-goto-char-2 avy-goto-char-in-line avy-goto-char) "avy"
;;;;;;  "avy.el" (22027 35941 729460 66000))
;;; Generated autoloads from avy.el

(autoload 'avy-goto-char "avy" "\
Jump to the currently visible CHAR.
The window scope is determined by `avy-all-windows' (ARG negates it).

\(fn CHAR &optional ARG)" t nil)

(autoload 'avy-goto-char-in-line "avy" "\
Jump to the currently visible CHAR in the current line.

\(fn CHAR)" t nil)

(autoload 'avy-goto-char-2 "avy" "\
Jump to the currently visible CHAR1 followed by CHAR2.
The window scope is determined by `avy-all-windows' (ARG negates it).

\(fn CHAR1 CHAR2 &optional ARG)" t nil)

(autoload 'avy-isearch "avy" "\
Jump to one of the current isearch candidates.

\(fn)" t nil)

(autoload 'avy-goto-word-0 "avy" "\
Jump to a word start.
The window scope is determined by `avy-all-windows' (ARG negates it).

\(fn ARG)" t nil)

(autoload 'avy-goto-word-1 "avy" "\
Jump to the currently visible CHAR at a word start.
The window scope is determined by `avy-all-windows' (ARG negates it).

\(fn CHAR &optional ARG)" t nil)

(autoload 'avy-goto-subword-0 "avy" "\
Jump to a word or subword start.

The window scope is determined by `avy-all-windows' (ARG negates it).

When PREDICATE is non-nil it's a function of zero parameters that
should return true.

\(fn &optional ARG PREDICATE)" t nil)

(autoload 'avy-goto-subword-1 "avy" "\
Jump to the currently visible CHAR at a subword start.
The window scope is determined by `avy-all-windows' (ARG negates it).
The case of CHAR is ignored.

\(fn CHAR ARG)" t nil)

(autoload 'avy-goto-line "avy" "\
Jump to a line start in current buffer.
The window scope is determined by `avy-all-windows' (ARG negates it).

\(fn &optional ARG)" t nil)

(autoload 'avy-copy-line "avy" "\
Copy a selected line above the current line.
ARG lines can be used.

\(fn ARG)" t nil)

(autoload 'avy-move-line "avy" "\
Move a selected line above the current line.
ARG lines can be used.

\(fn ARG)" t nil)

(autoload 'avy-copy-region "avy" "\
Select two lines and copy the text between them here.

\(fn)" t nil)

(autoload 'avy-setup-default "avy" "\
Setup the default shortcuts.

\(fn)" nil nil)

(autoload 'avy-goto-char-timer "avy" "\
Read one or two consecutive chars and jump to the first one.
The window scope is determined by `avy-all-windows' (ARG negates it).

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("avy-pkg.el") (22027 35941 914973 331000))

;;;***

(provide 'avy-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; avy-autoloads.el ends here
