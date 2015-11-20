;;; writeroom-mode-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (global-writeroom-mode writeroom-mode) "writeroom-mode"
;;;;;;  "writeroom-mode.el" (21767 8973 965879 1000))
;;; Generated autoloads from writeroom-mode.el

(autoload 'writeroom-mode "writeroom-mode" "\
Minor mode for distraction-free writing.

\(fn &optional ARG)" t nil)

(defvar global-writeroom-mode nil "\
Non-nil if Global-Writeroom mode is enabled.
See the command `global-writeroom-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `global-writeroom-mode'.")

(custom-autoload 'global-writeroom-mode "writeroom-mode" nil)

(autoload 'global-writeroom-mode "writeroom-mode" "\
Toggle Writeroom mode in all buffers.
With prefix ARG, enable Global-Writeroom mode if ARG is positive;
otherwise, disable it.  If called from Lisp, enable the mode if
ARG is omitted or nil.

Writeroom mode is enabled in all buffers where
`turn-on-writeroom-mode' would do it.
See `writeroom-mode' for more information on Writeroom mode.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("writeroom-mode-pkg.el") (21767 8974 106594
;;;;;;  954000))

;;;***

(provide 'writeroom-mode-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; writeroom-mode-autoloads.el ends here
