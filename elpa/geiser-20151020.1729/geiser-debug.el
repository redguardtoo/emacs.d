;;; geiser-debug.el -- displaying debug information and evaluation results

;; Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014, 2015 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Mon Feb 23, 2009 22:34



(require 'geiser-edit)
(require 'geiser-autodoc)
(require 'geiser-impl)
(require 'geiser-eval)
(require 'geiser-menu)
(require 'geiser-popup)
(require 'geiser-base)
(require 'geiser-image)


;;; Customization:

(defgroup geiser-debug nil
  "Debugging and error display options."
  :group 'geiser)

(geiser-custom--defcustom geiser-debug-always-display-sexp-after-p nil
  "Whether to always display the sexp whose evaluation caused an
error after the error message in the debug pop-up. If nil,
expressions shorter than `geiser-debug-long-sexp-lines` lines are
show before the error message."
  :group 'geiser-debug
  :type 'boolean)

(geiser-custom--defcustom geiser-debug-long-sexp-lines 6
  "Length of an expression in order to be relegated to the bottom
of the debug pop-up (after the error message). If
`geiser-debug-always-display-sexp-after-p` is t, this variable
has no effect."
  :group 'geiser-debug
  :type 'int)

(geiser-custom--defcustom geiser-debug-jump-to-debug-p t
  "When set to t (the default), jump to the debug pop-up buffer
  in case of evaluation errors.

See also `geiser-debug-show-debug-p`. "
  :group 'geiser-debug
  :type 'boolean)

(geiser-custom--defcustom geiser-debug-show-debug-p t
  "When set to t (the default), show the debug pop-up buffer in
  case of evaluation errors.

This option takes effect even if `geiser-debug-jump-to-debug-p`
is set."
  :group 'geiser-debug
  :type 'boolean)

(geiser-custom--defcustom geiser-debug-auto-display-images-p t
  "Whether to automatically invoke the external viewer to display
images when they're evaluated.

See also `geiser-repl-auto-display-images-p'."
  :group 'geiser-debug
  :type 'boolean)


;;; Debug buffer mode:

(defvar geiser-debug-mode-map
  (let ((map (make-sparse-keymap)))
    (suppress-keymap map)
    (set-keymap-parent map button-buffer-map)
    map))

(defun geiser-debug-mode ()
  "A major mode for displaying Scheme compilation and evaluation results.
\\{geiser-debug-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (buffer-disable-undo)
  (use-local-map geiser-debug-mode-map)
  (set-syntax-table scheme-mode-syntax-table)
  (setq mode-name "Geiser DBG")
  (setq major-mode 'geiser-debug-mode)
  (setq next-error-function 'geiser-edit--open-next)
  (setq buffer-read-only t))

(defun geiser-debug--button-p (nextp)
  (let ((m (funcall (if nextp 'next-button 'previous-button) (point))))
    (and m (funcall (if nextp '< '>) (point) (marker-position m)))))

(geiser-menu--defmenu debug geiser-debug-mode-map
  ("Next error" "n" forward-button :enable (geiser-debug--button-p t))
  ("Previous error" "p" backward-button :enable (geiser-debug--button-p t))
  --
  ("Quit" nil View-quit))


;;; Buffer for displaying evaluation results:

(geiser-popup--define debug "*Geiser dbg*" geiser-debug-mode)


;;; Displaying retorts

(geiser-impl--define-caller geiser-debug--display-error
    display-error (module key message)
    "This method takes 3 parameters (a module name, the error key,
and the accompanying error message) and should display
(in the current buffer) a formatted version of the error. If the
error was successfully displayed, the call should evaluate to a
non-null value.")

(geiser-impl--define-caller geiser-debug--enter-debugger
    enter-debugger ()
  "This method is called upon entering the debugger, in the REPL
buffer.")

(defun geiser-debug--display-after (what)
  (or geiser-debug-always-display-sexp-after-p
      (>= (with-temp-buffer
            (insert what)
            (count-lines (point-min) (point-max)))
          geiser-debug-long-sexp-lines)))

(defun geiser-debug--insert-res (res)
  (let ((begin (point)))
    (insert res)
    (let ((end (point)))
      (goto-char begin)
      (let ((no (geiser-image--replace-images
                 t geiser-debug-auto-display-images-p)))
        (goto-char end)
        (newline 2)
        (and no (> no 0))))))

(defun geiser-debug--display-retort (what ret &optional res auto-p)
  (let* ((err (geiser-eval--retort-error ret))
         (key (geiser-eval--error-key err))
         (output (geiser-eval--retort-output ret))
         (impl geiser-impl--implementation)
         (module (geiser-eval--get-module))
         (dbg nil)
         (img nil)
         (dir default-directory)
         (buffer (current-buffer))
         (debug (eq key 'geiser-debugger))
         (after (geiser-debug--display-after what)))
    (when debug
      (switch-to-geiser nil nil buffer)
      (geiser-debug--enter-debugger impl))
    (geiser-debug--with-buffer
      (erase-buffer)
      (when dir (setq default-directory dir))
      (unless after
        (geiser-debug--display-error impl module nil what)
        (newline 2))
      (setq img (when (and res (not err)) (geiser-debug--insert-res res)))
      (setq dbg (geiser-debug--display-error impl module key output))
      (when after
        (goto-char (point-max))
        (insert "\nExpression evaluated was:\n\n")
        (geiser-debug--display-error impl module nil what))
      (goto-char (point-min)))
    (when (or img dbg)
      (geiser-debug--pop-to-buffer)
      (when (and dbg (not geiser-debug-jump-to-debug-p))
        (next-error)
        (when (not geiser-debug-show-debug-p)
          (pop-to-buffer (geiser-debug--buffer)
                         'display-buffer-reuse-window t)
          (View-quit))
        (message "Evaluation error: %s" dbg)))))

(defsubst geiser-debug--wrap-region (str)
  (format "(begin %s)" str))

(defun geiser-debug--unwrap (str)
  (if (string-match "(begin[ \t\n\v\r]+\\(.+\\)*)" str)
      (match-string 1 str)
    str))

(defun geiser-debug--send-region (compile start end and-go wrap &optional nomsg)
  (let* ((str (buffer-substring-no-properties start end))
         (wrapped (if wrap (geiser-debug--wrap-region str) str))
         (code `(,(if compile :comp :eval) (:scm ,wrapped)))
         (ret (geiser-eval--send/wait code))
         (res (geiser-eval--retort-result-str ret nil))
         (err (geiser-eval--retort-error ret)))
    (when and-go (funcall and-go))
    (when (not err)
      (save-excursion
        (goto-char (/ (+ end start) 2))
        (geiser-autodoc--clean-cache))
      (unless nomsg (message "%s" res)))
    (geiser-debug--display-retort (geiser-syntax--scheme-str str) ret res)
    ret))

(defun geiser-debug--expand-region (start end all wrap)
  (let* ((str (buffer-substring-no-properties start end))
         (wrapped (if wrap (geiser-debug--wrap-region str) str))
         (code `(:eval (:ge macroexpand (quote (:scm ,wrapped))
                            ,(if all :t :f))))
         (ret (geiser-eval--send/wait code))
         (err (geiser-eval--retort-error ret))
         (result (geiser-eval--retort-result ret)))
    (if err
        (geiser-debug--display-retort str ret)
      (geiser-debug--with-buffer
        (erase-buffer)
        (insert (format "%s" (if wrap (geiser-debug--unwrap result) result)))
        (goto-char (point-min)))
      (geiser-debug--pop-to-buffer))))


(provide 'geiser-debug)
