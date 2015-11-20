;;; flyspell-lazy-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (flyspell-lazy-check-buffer flyspell-lazy-mode
;;;;;;  flyspell-lazy) "flyspell-lazy" "flyspell-lazy.el" (21767
;;;;;;  9062 669878 4000))
;;; Generated autoloads from flyspell-lazy.el

(let ((loads (get 'flyspell-lazy 'custom-loads))) (if (member '"flyspell-lazy" loads) nil (put 'flyspell-lazy 'custom-loads (cons '"flyspell-lazy" loads))))

(defvar flyspell-lazy-mode nil "\
Non-nil if Flyspell-Lazy mode is enabled.
See the command `flyspell-lazy-mode' for a description of this minor mode.
Setting this variable directly does not take effect;
either customize it (see the info node `Easy Customization')
or call the function `flyspell-lazy-mode'.")

(custom-autoload 'flyspell-lazy-mode "flyspell-lazy" nil)

(autoload 'flyspell-lazy-mode "flyspell-lazy" "\
Turn on flyspell-lazy-mode.

Turning on flyspell-lazy-mode will set up hooks which
change how `flyspell-mode' works, in every buffer for which
flyspell is enabled.

When called interactively with no prefix argument this command
toggles the mode.  With a prefix argument, it enables the mode
if the argument is positive and otherwise disables the mode.

When called from Lisp, this command enables the mode if the
argument is omitted or nil, and toggles the mode if the argument
is 'toggle.

\(fn &optional ARG)" t nil)

(autoload 'flyspell-lazy-check-buffer "flyspell-lazy" "\
Check spelling on the whole buffer, respecting flyspell-lazy settings.

With optional FORCE, force spell-check even on a buffer which
would usually be skipped.

\(fn &optional FORCE)" t nil)

;;;***

;;;### (autoloads nil nil ("flyspell-lazy-pkg.el") (21767 9062 741676
;;;;;;  895000))

;;;***

(provide 'flyspell-lazy-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; flyspell-lazy-autoloads.el ends here
