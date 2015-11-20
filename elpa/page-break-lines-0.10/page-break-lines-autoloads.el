;;; page-break-lines-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (global-page-break-lines-mode page-break-lines-mode-maybe
;;;;;;  turn-off-page-break-lines-mode turn-on-page-break-lines-mode
;;;;;;  page-break-lines-mode) "page-break-lines" "page-break-lines.el"
;;;;;;  (21767 9022 741878 453000))
;;; Generated autoloads from page-break-lines.el

(autoload 'page-break-lines-mode "page-break-lines" "\
Toggle Page Break Lines mode.

In Page Break mode, page breaks (^L characters) are displayed as a
horizontal line of `page-break-string-char' characters.

\(fn &optional ARG)" t nil)

(autoload 'turn-on-page-break-lines-mode "page-break-lines" "\
Enable `page-break-lines-mode' in this buffer.

\(fn)" nil nil)

(autoload 'turn-off-page-break-lines-mode "page-break-lines" "\
Disable `page-break-lines-mode' in this buffer.

\(fn)" nil nil)

(autoload 'page-break-lines-mode-maybe "page-break-lines" "\
Enable `page-break-lines-mode' in the current buffer if desired.
When `major-mode' is listed in `page-break-lines-modes', then
`page-break-lines-mode' will be enabled.

\(fn)" nil nil)

(defvar global-page-break-lines-mode nil "\
Non-nil if Global-Page-Break-Lines mode is enabled.
See the command `global-page-break-lines-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `global-page-break-lines-mode'.")

(custom-autoload 'global-page-break-lines-mode "page-break-lines" nil)

(autoload 'global-page-break-lines-mode "page-break-lines" "\
Toggle Page-Break-Lines mode in all buffers.
With prefix ARG, enable Global-Page-Break-Lines mode if ARG is positive;
otherwise, disable it.  If called from Lisp, enable the mode if
ARG is omitted or nil.

Page-Break-Lines mode is enabled in all buffers where
`page-break-lines-mode-maybe' would do it.
See `page-break-lines-mode' for more information on Page-Break-Lines mode.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("page-break-lines-pkg.el") (21767 9022
;;;;;;  814381 514000))

;;;***

(provide 'page-break-lines-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; page-break-lines-autoloads.el ends here
