;;; rewind.el -- Resume the last completing-read session -*- lexical-binding: t; -*-

;; Copyright (C) 2026
;; Author: Chen Bin
;; Version: 0.1
;; Keywords: convenience, minibuffer
;; Package-Requires: ((emacs "29.1"))

;;; Commentary:
;; A completion-front-end-independent approximation of `ivy-resume' for
;; commands which use the built-in `completing-read'.
;;
;; The package records the arguments passed to `completing-read', the input
;; visible when the minibuffer exits, and the command/buffer context.  Calling
;; `rewind-resume' re-runs that command and replays the saved
;; `completing-read' call with the saved arguments and last input.  The selected
;; value is returned to the command normally, so the command's code following
;; `completing-read' runs as usual.
;;

;;; Code:

(defgroup rewind nil
  "Resume the last `completing-read' session."
  :group 'minibuffer
  :prefix "rewind-")

(defcustom rewind-excluded-commands
  '(rewind-resume
    execute-extended-command)
  "Commands to excluded from this package."
  :group 'rewind
  :type '(repeat sexp))

(defvar rewind-debug nil "Debug flag.")

(defvar rewind-last-session nil
  "Plist describing the most recently recorded `completing-read' call.")

(defvar rewind-replay-session nil
  "Dynamically bound session being replayed, or nil.")

(defvar rewind-replaying-p nil
  "Non-nil after the saved completion call is replaying.")

(defun rewind-capture-input (session)
  "Capture the minibuffer input for SESSION on exit."
  (setq session (plist-put session :input (minibuffer-contents-no-properties)))
  (when (eq session rewind-last-session)
    (setq rewind-last-session session)))

(defun rewind-capture-before-command (session)
  "Capture minibuffer input before each command and save it into SESSION."
  (when (and (minibufferp)
             (eq session rewind-last-session))
    (setq rewind-last-session
          (plist-put rewind-last-session :input
                     (minibuffer-contents-no-properties))
          rewind-last-session
          (plist-put rewind-last-session :input-captured t))))

(defun rewind-capture-input (session)
  "Capture minibuffer input on exit and save it into SESSION."
  (unless (plist-get session :input-captured)
    ;; fallback, in case `rewind-capture-before-command' failed to capture input
    (setq session
          (plist-put session :input
                     (minibuffer-contents-no-properties)))
    (when (eq session rewind-last-session)
      (setq rewind-last-session session))))

(defun rewind-setup-minibuffer (session)
  "Try record minibuffer's content into SESSION."
  (add-hook 'pre-command-hook
            (apply-partially #'rewind-capture-before-command session)
            nil t)
  (add-hook 'minibuffer-exit-hook
            (apply-partially #'rewind-capture-input session)
            nil t))

(defun rewind-read (orig args session)
  "Call ORIG with ARGS while capturing the minibuffer input in SESSION."
  (minibuffer-with-setup-hook
      (apply-partially #'rewind-setup-minibuffer session)
    (apply orig args)))

(defun rewind-around-completing-read (orig &rest args)
  "Record `completing-read' and replay one when resuming.
ORIG is the original function and ARGS are its arguments."
  (let* ((command this-command)
         session
         saved-args
         input)
    (when rewind-debug
      (message "rewind-around-completing-read called. command=%s" command))
    (cond
     ((and rewind-replay-session
           (not rewind-replaying-p))
      ;; Reuse the exact saved collection and options, changing only the
      ;; initial input to the text the user had typed when leaving the session.
      (setq session rewind-replay-session)
      (setq saved-args (copy-sequence (plist-get session :args)))
      (setq input (or (plist-get session :input) ""))
      (setq rewind-replaying-p t)
      ;; `completing-read' arguments are PROMPT, COLLECTION, PREDICATE,
      ;; REQUIRE-MATCH, INITIAL-INPUT, HISTORY, DEF, INHERIT-INPUT-METHOD.
      ;; Therefore INITIAL-INPUT is list element 4 (zero-based).
      (when rewind-debug
        (message "Patch the session with input=%s" input))
      (while (< (length saved-args) 5)
        (setq saved-args (append saved-args (list nil))))
      (setf (nth 4 saved-args) input)
      (rewind-read orig saved-args session))

     ((or rewind-replay-session
          (not (commandp command))
          (memq command rewind-excluded-commands))
      (when rewind-debug
        (message "nothing happened."))
      (apply orig args))

     (t
      (when rewind-debug
        (message "Save the initial session"))
      ;; Record ordinary calls made by an interactive command.  Ignore calls
      ;; outside a command context and calls made by this package itself.
      (rewind-read orig
                   args
                   (setq rewind-last-session
                         (list :command command
                               :args (copy-sequence args)
                               :directory default-directory
                               :prefix current-prefix-arg
                               :input (or (nth 4 args) ""))))))))

;;;###autoload
(defun rewind-resume ()
  "Resume the last recorded `completing-read' session.
Re-run the original command and restore the saved completion arguments and
last minibuffer input."
  (interactive)
  (let* ((session rewind-last-session)
         (command (plist-get session :command))
         (directory (plist-get session :directory)))
    (unless session
      (user-error "No saved completing-read session"))
    (unless (commandp command)
      (user-error "Saved command is not interactive: %S" command))
    (let ((rewind-replay-session session)
          (rewind-replaying-p nil)
          (current-prefix-arg (plist-get session :prefix))
          (default-directory directory))
        (call-interactively command)
      (unless rewind-replaying-p
        (message
         "The command did not call completing-read during replay; session not resumed")))))

;;;###autoload
(define-minor-mode rewind-mode
  "Globally record `completing-read' sessions for `rewind'."
  :global t
  :group 'rewind
  (if rewind-mode
      (advice-add 'completing-read :around #'rewind-around-completing-read)
    (advice-remove 'completing-read #'rewind-around-completing-read)))

(provide 'rewind)
;;; rewind.el ends here
