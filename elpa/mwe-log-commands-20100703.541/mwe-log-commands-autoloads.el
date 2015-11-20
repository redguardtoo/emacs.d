;;; mwe-log-commands-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (mwe:open-command-log-buffer mwe:log-keyboard-commands)
;;;;;;  "mwe-log-commands" "mwe-log-commands.el" (21767 9022 65878
;;;;;;  461000))
;;; Generated autoloads from mwe-log-commands.el

(autoload 'mwe:log-keyboard-commands "mwe-log-commands" "\
Enables keyboard command logging for the current buffer.
If optional ARG is nil, logging is turned off.

\(fn &optional ARG)" t nil)

(autoload 'mwe:open-command-log-buffer "mwe-log-commands" "\
Opens (and creates, if non-existant) a buffer used for logging keyboard commands.
If ARG is Non-nil, the existing command log buffer is cleared.

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("mwe-log-commands-pkg.el") (21767 9022
;;;;;;  137344 396000))

;;;***

(provide 'mwe-log-commands-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; mwe-log-commands-autoloads.el ends here
