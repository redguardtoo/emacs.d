;;; robe-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (ac-robe-setup ac-robe-available) "ac-robe" "ac-robe.el"
;;;;;;  (21767 8957 437879 187000))
;;; Generated autoloads from ac-robe.el

(autoload 'ac-robe-available "ac-robe" "\
Return t if `robe-mode' completions are available, otherwise nil.

\(fn)" nil nil)

(autoload 'ac-robe-setup "ac-robe" "\


\(fn)" nil nil)

(defconst ac-source-robe '((available . ac-robe-available) (candidates . ac-robe-candidates) (document . ac-robe-doc) (symbol . "r")) "\
`auto-complete' completion source for Ruby using `robe-mode'.")

;;;***

;;;### (autoloads (company-robe) "company-robe" "company-robe.el"
;;;;;;  (21767 8957 469879 187000))
;;; Generated autoloads from company-robe.el

(autoload 'company-robe "company-robe" "\
A `company-mode' completion back-end for `robe-mode'.

\(fn COMMAND &optional ARG)" t nil)

;;;***

;;;### (autoloads (robe-mode) "robe" "robe.el" (21767 8957 133879
;;;;;;  190000))
;;; Generated autoloads from robe.el

(autoload 'robe-mode "robe" "\
Improved navigation for Ruby.

The following commands are available:

\\{robe-mode-map}

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads nil nil ("robe-pkg.el") (21767 8957 509527 779000))

;;;***

(provide 'robe-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; robe-autoloads.el ends here
