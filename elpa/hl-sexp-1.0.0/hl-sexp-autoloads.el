;;; hl-sexp-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (global-hl-sexp-mode hl-sexp-mode) "hl-sexp" "hl-sexp.el"
;;;;;;  (21767 9019 413878 490000))
;;; Generated autoloads from hl-sexp.el

(autoload 'hl-sexp-mode "hl-sexp" "\
Minor mode to highlight the sexp about point in the current window.
With ARG, turn Hl-Sexp mode on if ARG is positive, off otherwise.
Uses functions `hl-sexp-unhighlight' and `hl-sexp-highlight' on
`pre-command-hook' and `post-command-hook'.

\(fn &optional ARG)" t nil)

(defvar global-hl-sexp-mode nil "\
Non-nil if Global-Hl-Sexp mode is enabled.
See the command `global-hl-sexp-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `global-hl-sexp-mode'.")

(custom-autoload 'global-hl-sexp-mode "hl-sexp" nil)

(autoload 'global-hl-sexp-mode "hl-sexp" "\
Toggle Hl-Sexp mode in all buffers.
With prefix ARG, enable Global-Hl-Sexp mode if ARG is positive;
otherwise, disable it.  If called from Lisp, enable the mode if
ARG is omitted or nil.

Hl-Sexp mode is enabled in all buffers where
`hl-sexp-mode' would do it.
See `hl-sexp-mode' for more information on Hl-Sexp mode.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("hl-sexp-pkg.el") (21767 9019 487455 818000))

;;;***

(provide 'hl-sexp-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; hl-sexp-autoloads.el ends here
