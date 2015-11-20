;;; flymake-jslint-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (flymake-jslint-load flymake-jslint-command flymake-jslint-detect-trailing-comma)
;;;;;;  "flymake-jslint" "flymake-jslint.el" (21767 9015 929878 530000))
;;; Generated autoloads from flymake-jslint.el

(defvar flymake-jslint-detect-trailing-comma t "\
Whether or not to report warnings about trailing commas.")

(custom-autoload 'flymake-jslint-detect-trailing-comma "flymake-jslint" t)

(defvar flymake-jslint-command "jsl" "\
Whether or not to report warnings about trailing commas.")

(custom-autoload 'flymake-jslint-command "flymake-jslint" t)

(autoload 'flymake-jslint-load "flymake-jslint" "\
Configure flymake mode to check the current buffer's javascript syntax.

This function is designed to be called in `js-mode-hook' or
equivalent; it does not alter flymake's global configuration, so
function `flymake-mode' alone will not suffice.

\(fn)" t nil)

;;;***

;;;### (autoloads nil nil ("flymake-jslint-pkg.el") (21767 9016 7210
;;;;;;  343000))

;;;***

(provide 'flymake-jslint-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; flymake-jslint-autoloads.el ends here
