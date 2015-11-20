;;; ruby-compilation-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (ruby-compilation-this-test ruby-compilation-cap
;;;;;;  pcomplete/cap ruby-compilation-rake ruby-compilation-rake-refresh-tasks
;;;;;;  pcomplete/rake ruby-compilation-this-buffer ruby-compilation-run)
;;;;;;  "ruby-compilation" "ruby-compilation.el" (21767 9028 505878
;;;;;;  388000))
;;; Generated autoloads from ruby-compilation.el

(eval-after-load 'ruby-mode '(progn (define-key ruby-mode-map (kbd "C-x t") 'ruby-compilation-this-buffer) (define-key ruby-mode-map (kbd "C-x T") 'ruby-compilation-this-test)))

(autoload 'ruby-compilation-run "ruby-compilation" "\
Run CMD using `ruby-compilation-executable' in a ruby compilation buffer.
Argument RUBY-OPTIONS can be used to specify additional
command line args for ruby.  If supplied, NAME will be used in
place of the script name to construct the name of the compilation
buffer.

\(fn CMD &optional RUBY-OPTIONS NAME)" t nil)

(autoload 'ruby-compilation-this-buffer "ruby-compilation" "\
Run the current buffer through Ruby compilation.

\(fn)" t nil)

(autoload 'pcomplete/rake "ruby-compilation" "\
Start pcompletion using the list of available rake tasks.

\(fn)" nil nil)

(autoload 'ruby-compilation-rake-refresh-tasks "ruby-compilation" "\
Reset the list of available rake tasks for the current Rakefile environment.

\(fn)" t nil)

(autoload 'ruby-compilation-rake "ruby-compilation" "\
Run a rake process dumping output to a ruby compilation buffer.
If EDIT is t, prompt the user to edit the command line.  If TASK
is not supplied, the user will be prompted.  ENV-VARS is an
optional list of (name . value) pairs which will be passed to rake.

The list of rake tasks will be remembered between invocations (on
a per-Rakefile basis) in the variable
`ruby-compilation-rake-tasks-cache'.  If the Rakefile is updated,
the available tasks will automatically be refreshed.  Use function
`ruby-compilation-rake-refresh-tasks' to force an update of the
available tasks, e.g. if tasks defined outside the Rakefile change.

\(fn &optional EDIT TASK ENV-VARS)" t nil)

(autoload 'pcomplete/cap "ruby-compilation" "\
Start pcompletion using the list of available capistrano tasks.

\(fn)" nil nil)

(autoload 'ruby-compilation-cap "ruby-compilation" "\
Run a capistrano process dumping output to a ruby compilation buffer.
If EDIT is t, prompt the user to edit the command line.  If TASK
is not supplied, the user will be prompted.  ENV-VARS is an
optional list of (name . value) pairs which will be passed to
capistrano.

\(fn &optional EDIT TASK ENV-VARS)" t nil)

(autoload 'ruby-compilation-this-test "ruby-compilation" "\
Run the test at point through Ruby compilation.

\(fn)" t nil)

;;;***

;;;### (autoloads nil nil ("ruby-compilation-pkg.el") (21767 9028
;;;;;;  581637 170000))

;;;***

(provide 'ruby-compilation-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; ruby-compilation-autoloads.el ends here
