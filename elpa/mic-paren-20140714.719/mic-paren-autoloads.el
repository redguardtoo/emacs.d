;;; mic-paren-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (paren-backward-sexp paren-forward-sexp paren-toggle-open-paren-context
;;;;;;  paren-toggle-matching-quoted-paren paren-toggle-matching-paired-delimiter
;;;;;;  paren-deactivate paren-activate) "mic-paren" "mic-paren.el"
;;;;;;  (21767 9004 357878 660000))
;;; Generated autoloads from mic-paren.el

(autoload 'paren-activate "mic-paren" "\
Activate mic-paren parenthesis highlighting.
Note: This also deactivates the paren.el
and stig-paren.el packages if they are active!

The following options are available via the customize-feature:
  `paren-priority'
  `paren-overlay-priority'
  `paren-sexp-mode'
  `paren-highlight-at-point'
  `paren-highlight-offscreen'
  `paren-display-message'
  `paren-message-linefeed-display'
  `paren-message-no-match'
  `paren-message-show-linenumber'
  `paren-message-truncate-lines'
  `paren-ding-unmatched'
  `paren-delay'
  `paren-dont-touch-blink'
  `paren-match-face'
  `paren-mismatch-face'
  `paren-no-match-face'
  `paren-bind-modified-sexp-functions'

The following options are settable via toggling functions (look at the
documentation of these options for the names of these functions):
  `paren-match-quoted-paren'
  `paren-match-paired-delimiter'
  `paren-open-paren-context-backward'

\(fn)" t nil)

(autoload 'paren-deactivate "mic-paren" "\
Deactivate mic-paren parenthesis highlighting.

\(fn)" t nil)

(autoload 'paren-toggle-matching-paired-delimiter "mic-paren" "\
Toggle matching paired delimiter.
Force on with positive ARG.  Use this in mode hooks to activate or
deactivate paired delimiter matching.  If optional second argument
NO-MESSAGE is non-nil then don't display a message about the
current activation state of the paired-delimiter-matching feature.

\(fn ARG &optional NO-MESSAGE)" t nil)

(autoload 'paren-toggle-matching-quoted-paren "mic-paren" "\
Toggle matching quoted parens.
Force on with positive ARG.  Use this in mode hooks to activate or
deactivate quoted paren matching.  If optional second argument
NO-MESSAGE is non-nil then don't display a message about the
current activation state of the quoted-paren-matching feature.

\(fn ARG &optional NO-MESSAGE)" t nil)

(autoload 'paren-toggle-open-paren-context "mic-paren" "\
Toggle whether or not to determine context of the matching open-paren.
Force backward context with positive ARG.  Use this in mode-hooks.
See `paren-open-paren-context-backward'.

\(fn ARG)" t nil)

(autoload 'paren-forward-sexp "mic-paren" "\
Act like `forward-sexp' but also handle quoted parens.
See `paren-match-quoted-paren'.

\(fn &optional ARG)" t nil)

(autoload 'paren-backward-sexp "mic-paren" "\
Act like `backward-sexp' but also match quoted parens.
See `paren-match-quoted-paren'.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("mic-paren-pkg.el") (21767 9004 433088
;;;;;;  555000))

;;;***

(provide 'mic-paren-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; mic-paren-autoloads.el ends here
