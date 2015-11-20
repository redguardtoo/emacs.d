;;; neotree-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (neotree-dir neotree-hide neotree-show neotree-toggle
;;;;;;  neotree-find) "neotree" "neotree.el" (22027 35954 213459
;;;;;;  925000))
;;; Generated autoloads from neotree.el

(autoload 'neotree-find "neotree" "\
Quick select node which specified PATH in NeoTree.
If path is nil and no buffer file name, then use DEFAULT-PATH,

\(fn &optional PATH DEFAULT-PATH)" t nil)

(autoload 'neotree-toggle "neotree" "\
Toggle show the NeoTree window.

\(fn)" t nil)

(autoload 'neotree-show "neotree" "\
Show the NeoTree widnow.

\(fn)" t nil)

(autoload 'neotree-hide "neotree" "\
Close the NeoTree window.

\(fn)" t nil)

(autoload 'neotree-dir "neotree" "\
Show the NeoTree window, and change root to PATH.

\(fn PATH)" t nil)

(defalias 'neotree 'neotree-show "\
Show the NeoTree window.")

;;;***

;;;### (autoloads nil nil ("neotree-pkg.el") (22027 35954 336933
;;;;;;  874000))

;;;***

(provide 'neotree-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; neotree-autoloads.el ends here
