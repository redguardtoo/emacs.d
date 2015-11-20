;;; iedit-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (iedit-mode-toggle-on-function iedit-mode) "iedit"
;;;;;;  "iedit.el" (21767 9068 981877 933000))
;;; Generated autoloads from iedit.el

(autoload 'iedit-mode "iedit" "\
Toggle Iedit mode.
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
\\{iedit-mode-occurrence-keymap}

\(fn &optional ARG)" t nil)

(autoload 'iedit-mode-toggle-on-function "iedit" "\
Toggle Iedit mode on current function.

\(fn)" t nil)

;;;***

;;;### (autoloads (iedit-rectangle-mode) "iedit-rect" "iedit-rect.el"
;;;;;;  (21767 9069 17877 933000))
;;; Generated autoloads from iedit-rect.el

(autoload 'iedit-rectangle-mode "iedit-rect" "\
Toggle Iedit-rect mode.

When Iedit-rect mode is on, a rectangle is started with visible
rectangle highlighting.  Rectangle editing support is based on
Iedit mechanism.

Commands:
\\{iedit-rect-keymap}

\(fn &optional BEG END)" t nil)

;;;***

;;;### (autoloads nil nil ("iedit-lib.el" "iedit-pkg.el") (21767
;;;;;;  9069 114301 396000))

;;;***

(provide 'iedit-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; iedit-autoloads.el ends here
