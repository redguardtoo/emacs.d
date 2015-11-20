;;; pointback-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (global-pointback-mode pointback-mode) "pointback"
;;;;;;  "pointback.el" (21767 9023 369878 446000))
;;; Generated autoloads from pointback.el

(autoload 'pointback-mode "pointback" "\
Restore previous window point when switching back to a buffer.

\(fn &optional ARG)" t nil)

(defvar global-pointback-mode nil "\
Non-nil if Global-Pointback mode is enabled.
See the command `global-pointback-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `global-pointback-mode'.")

(custom-autoload 'global-pointback-mode "pointback" nil)

(autoload 'global-pointback-mode "pointback" "\
Toggle Pointback mode in all buffers.
With prefix ARG, enable Global-Pointback mode if ARG is positive;
otherwise, disable it.  If called from Lisp, enable the mode if
ARG is omitted or nil.

Pointback mode is enabled in all buffers where
`pointback-on' would do it.
See `pointback-mode' for more information on Pointback mode.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("pointback-pkg.el") (21767 9023 429135
;;;;;;  469000))

;;;***

(provide 'pointback-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; pointback-autoloads.el ends here
