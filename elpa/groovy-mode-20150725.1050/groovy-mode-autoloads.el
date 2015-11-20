;;; groovy-mode-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (groovy-electric-mode) "groovy-electric" "groovy-electric.el"
;;;;;;  (22027 35946 645460 10000))
;;; Generated autoloads from groovy-electric.el

(autoload 'groovy-electric-mode "groovy-electric" "\
Toggle Groovy Electric minor mode.
With no argument, this command toggles the mode.  Non-null prefix
argument turns on the mode.  Null prefix argument turns off the
mode.

When Groovy Electric mode is enabled, simple, double and back
quotes as well as braces are paired auto-magically. Expansion
does not occur inside comments and strings. Note that you must
have Font Lock enabled. ${ } is expanded when in a GString

\(fn &optional ARG)" t nil)

;;;***

;;;### (autoloads (groovy-mode groovy-mode-hook) "groovy-mode" "groovy-mode.el"
;;;;;;  (22027 35946 481460 12000))
;;; Generated autoloads from groovy-mode.el
 (add-to-list 'auto-mode-alist '("\\.g\\(?:ant\\|roovy\\|radle\\)\\'" . groovy-mode))

(defvar groovy-mode-hook nil "\
*Hook called by `groovy-mode'.")

(custom-autoload 'groovy-mode-hook "groovy-mode" t)

(autoload 'groovy-mode "groovy-mode" "\
Major mode for editing Groovy code.

The hook `c-mode-common-hook' is run with no args at mode
initialization, then `groovy-mode-hook'.

Key bindings:
\\{groovy-mode-map}

\(fn)" t nil)

;;;***

;;;### (autoloads (run-groovy inferior-groovy-mode inf-groovy-keys)
;;;;;;  "inf-groovy" "inf-groovy.el" (22027 35946 545460 12000))
;;; Generated autoloads from inf-groovy.el

(autoload 'inf-groovy-keys "inf-groovy" "\
Set local key defs for inf-groovy in groovy-mode

\(fn)" nil nil)

(autoload 'inferior-groovy-mode "inf-groovy" "\
Major mode for interacting with an inferior groovy (groovysh) process.

The following commands are available:
\\{inferior-groovy-mode-map}

A groovy process can be fired up with M-x run-groovy.

Customisation: Entry to this mode runs the hooks on comint-mode-hook and
inferior-groovy-mode-hook (in that order).

You can send text to the inferior groovy process from other buffers containing
Groovy source.
    switch-to-groovy switches the current buffer to the groovy process buffer.
    groovy-send-definition sends the current definition to the groovy process.
    groovy-send-region sends the current region to the groovy process.

    groovy-send-definition-and-go, groovy-send-region-and-go,
        switch to the groovy process buffer after sending their text.
For information on running multiple processes in multiple buffers, see
documentation for variable groovy-buffer.

Commands:
Return after the end of the process' output sends the text from the
    end of process to point.
Return before the end of the process' output copies the sexp ending at point
    to the end of the process' output, and sends it.
Delete converts tabs to spaces as it moves back.
Tab indents for groovy; with argument, shifts rest
    of expression rigidly with the current line.
C-M-q does Tab on each line starting within following expression.
Paragraphs are separated only by blank lines.  # start comments.
If you accidentally suspend your process, use \\[comint-continue-subjob]
to continue it.

\(fn)" t nil)

(autoload 'run-groovy "inf-groovy" "\
Run an inferior Groovy process, input and output via buffer *groovy*.
If there is a process already running in `*groovy*', switch to that buffer.
With argument, allows you to edit the command line (default is value
of `groovy-program-name').  Runs the hooks `inferior-groovy-mode-hook'
\(after the `comint-mode-hook' is run).
\(Type \\[describe-mode] in the process buffer for a list of commands.)

\(fn CMD)" t nil)

(eval-after-load 'groovy-mode (lambda nil (add-hook 'groovy-mode-hook 'inf-groovy-keys)))

;;;***

;;;### (autoloads nil nil ("groovy-mode-pkg.el") (22027 35946 804498
;;;;;;  336000))

;;;***

(provide 'groovy-mode-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; groovy-mode-autoloads.el ends here
