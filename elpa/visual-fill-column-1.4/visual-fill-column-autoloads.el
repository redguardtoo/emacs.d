;;; visual-fill-column-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (global-visual-fill-column-mode visual-fill-column-mode)
;;;;;;  "visual-fill-column" "visual-fill-column.el" (21767 8972
;;;;;;  693879 15000))
;;; Generated autoloads from visual-fill-column.el

(autoload 'visual-fill-column-mode "visual-fill-column" "\
Wrap lines according to `fill-column' in `visual-line-mode'.

\(fn &optional ARG)" t nil)

(defvar global-visual-fill-column-mode nil "\
Non-nil if Global-Visual-Fill-Column mode is enabled.
See the command `global-visual-fill-column-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `global-visual-fill-column-mode'.")

(custom-autoload 'global-visual-fill-column-mode "visual-fill-column" nil)

(autoload 'global-visual-fill-column-mode "visual-fill-column" "\
Toggle Visual-Fill-Column mode in all buffers.
With prefix ARG, enable Global-Visual-Fill-Column mode if ARG is positive;
otherwise, disable it.  If called from Lisp, enable the mode if
ARG is omitted or nil.

Visual-Fill-Column mode is enabled in all buffers where
`turn-on-visual-fill-column-mode' would do it.
See `visual-fill-column-mode' for more information on Visual-Fill-Column mode.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("visual-fill-column-pkg.el") (21767 8972
;;;;;;  767442 180000))

;;;***

(provide 'visual-fill-column-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; visual-fill-column-autoloads.el ends here
