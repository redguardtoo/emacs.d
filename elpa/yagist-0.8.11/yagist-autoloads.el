;;; yagist-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (yagist-global-minor-mode yagist-minor-mode yagist-list
;;;;;;  yagist-region-or-buffer-private yagist-region-or-buffer yagist-buffer-private
;;;;;;  yagist-buffer yagist-region-private yagist-region) "yagist"
;;;;;;  "yagist.el" (21767 8951 781879 250000))
;;; Generated autoloads from yagist.el

(autoload 'yagist-region "yagist" "\
Post the current region as a new paste at gist.github.com
Copies the URL into the kill ring.

With a prefix argument, makes a private paste.

\(fn BEGIN END &optional PRIVATE NAME)" t nil)

(autoload 'yagist-region-private "yagist" "\
Post the current region as a new private paste at gist.github.com
Copies the URL into the kill ring.

\(fn BEGIN END)" t nil)

(autoload 'yagist-buffer "yagist" "\
Post the current buffer as a new paste at gist.github.com.
Copies the URL into the kill ring.

With a prefix argument, makes a private paste.

\(fn &optional PRIVATE)" t nil)

(autoload 'yagist-buffer-private "yagist" "\
Post the current buffer as a new private paste at gist.github.com.
Copies the URL into the kill ring.

\(fn)" t nil)

(autoload 'yagist-region-or-buffer "yagist" "\
Post either the current region, or if mark is not set, the
current buffer as a new paste at gist.github.com Copies the URL
into the kill ring.

With a prefix argument, makes a private paste.

\(fn &optional PRIVATE)" t nil)

(autoload 'yagist-region-or-buffer-private "yagist" "\
Post either the current region, or if mark is not set, the
current buffer as a new private paste at gist.github.com Copies
the URL into the kill ring.

\(fn)" t nil)

(autoload 'yagist-list "yagist" "\
Displays a list of all of the current user's gists in a new buffer.

\(fn)" t nil)

(autoload 'yagist-minor-mode "yagist" "\


\(fn &optional ARG)" t nil)

(defvar yagist-global-minor-mode nil "\
Non-nil if Yagist-Global minor mode is enabled.
See the command `yagist-global-minor-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `yagist-global-minor-mode'.")

(custom-autoload 'yagist-global-minor-mode "yagist" nil)

(autoload 'yagist-global-minor-mode "yagist" "\
Toggle Yagist minor mode in all buffers.
With prefix ARG, enable Yagist-Global minor mode if ARG is positive;
otherwise, disable it.  If called from Lisp, enable the mode if
ARG is omitted or nil.

Yagist minor mode is enabled in all buffers where
`yagist-minor-mode-maybe' would do it.
See `yagist-minor-mode' for more information on Yagist minor mode.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("yagist-pkg.el") (21767 8951 863881 605000))

;;;***

(provide 'yagist-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; yagist-autoloads.el ends here
