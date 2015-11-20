;;; multi-term-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (multi-term-dedicated-select multi-term-dedicated-toggle
;;;;;;  multi-term-dedicated-open multi-term-prev multi-term-next
;;;;;;  multi-term) "multi-term" "multi-term.el" (21767 9115 13877
;;;;;;  416000))
;;; Generated autoloads from multi-term.el

(autoload 'multi-term "multi-term" "\
Create new term buffer.
Will prompt you shell name when you type `C-u' before this command.

\(fn)" t nil)

(autoload 'multi-term-next "multi-term" "\
Go to the next term buffer.
If OFFSET is `non-nil', will goto next term buffer with OFFSET.

\(fn &optional OFFSET)" t nil)

(autoload 'multi-term-prev "multi-term" "\
Go to the previous term buffer.
If OFFSET is `non-nil', will goto previous term buffer with OFFSET.

\(fn &optional OFFSET)" t nil)

(autoload 'multi-term-dedicated-open "multi-term" "\
Open dedicated `multi-term' window.
Will prompt you shell name when you type `C-u' before this command.

\(fn)" t nil)

(autoload 'multi-term-dedicated-toggle "multi-term" "\
Toggle dedicated `multi-term' window.

\(fn)" t nil)

(autoload 'multi-term-dedicated-select "multi-term" "\
Select the `multi-term' dedicated window.

\(fn)" t nil)

;;;***

;;;### (autoloads nil nil ("multi-term-pkg.el") (21767 9115 106620
;;;;;;  3000))

;;;***

(provide 'multi-term-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; multi-term-autoloads.el ends here
