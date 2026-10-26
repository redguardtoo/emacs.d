;;; cmd-rewind.el -- Resume the last completing-read session -*- lexical-binding: t; -*-

;; Copyright (C) 2026
;; Author: Chen Bin
;; Version: 0.2
;; Keywords: convenience, minibuffer
;; Package-Requires: ((emacs "29.1"))

;;; Commentary:
;; A completion-front-end-independent approximation of `ivy-resume' for
;; named interactive commands which use the built-in `completing-read'.
;;
;; The package records the arguments passed to `completing-read', the input
;; visible when the minibuffer exits, and the command/buffer context.
;; Calling `cmd-rewind-resume' re-runs that command and replays the saved
;; `completing-read' call with the saved arguments and last input.
;;
;; Anonymous interactive functions are not recorded or replayed.
;;
;; Note for command developers:
;; When `cmd-rewind-replay-session' is non-nil, `cmd-rewind' will replay the
;; saved `completing-read' call using its original arguments.
;; If the command performs expensive work solely to prepare the collection,
;; you may skip that work during replay, provided the saved collection remains
;; valid.
;;
;; `cmd-rewind-replay-session' is like,
;;   (list :command command
;;         :completing-read-args arguments
;;         :directory directory
;;         :prefix command-prefix
;;         :completing-read-input user-input)
;;
;; So get collection of original `completing-read' is,
;;   (setq collection (nth 1 (plist-get cmd-rewind-replay-session :completing-read-args)))
;;
;; An advanced example for command developer (Please add the line ";; -*- lexical-binding: t; -*-"
;; into the beginning of code file),
;;
;;   (defun my-completion-table (candidates)
;;     "Create a completion table CANDIDATES."
;;     (lambda (string pred action)
;;        (cond
;;         ((eq action 'metadata)
;;          `(metadata (category . my-command)))
;;         ((eq action 'original-candidates)
;;          candidates)
;;         (t
;;          (complete-with-action action candidates string pred)))))
;;
;;   (defun my-computing ()
;;     "Do some computing here."
;;     '(("Apple" . "My apple") ("Peach" . "My peach")))
;;
;;   (defun my-command ()
;;     "My command."
;;     (interactive)
;;     (let* ((replay-session (and (boundp 'cmd-rewind-replay-session)
;;                                 cmd-rewind-replay-session))
;;            (candidates (cond
;;                         (replay-session
;;                          ;; `my-command' is started by `cmd-rewind-resume'
;;                          ;; Avoid execution of `my-computing' here, use cached data
;;                          ;; Note COLLECTION is second parameters of `completing-read'
;;                          ;; See `my-completion-table' for details
;;                          (funcall (nth 1 (plist-get replay-session :completing-read-args)) nil nil 'original-candidates))
;;                         (t
;;                          (my-computing))))
;;            (selected (completing-read "Select fruit: " (my-completion-table candidates))))
;;       (message "Selected fruit: %s" (cdr (assoc selected candidates)))))
;;
;;; Code:

(require 'cl-lib)

(defgroup cmd-rewind nil
  "Resume the last `completing-read' session."
  :group 'minibuffer
  :prefix "cmd-rewind-")

(defcustom cmd-rewind-excluded-commands
  '("^cmd-rewind-resume$"
    "^.*-buffer$"
    "^describe-.*$"
    "^apropos.*$"
    "^bookmark-.*$"
    "recentf"
    "^execute-extended-command$"
    "^helpful-.*$"
    "imenu"
    "^find-function$"
    "^find-variable$")
  "Regular expressions matching excluded command names."
  :group 'cmd-rewind
  :type '(repeat string))

(defvar cmd-rewind-debug nil
  "Non-nil enables debug messages.")

(defvar cmd-rewind-last-session nil
  "Plist describing the most recently recorded `completing-read' call.")

(defvar cmd-rewind-replay-session nil
  "Dynamically bound session being replayed, or nil.")

(defvar cmd-rewind-completing-read-replaying-p nil
  "Non-nil while the saved `completing-read' call is being replayed.")

(defvar cmd-rewind-replay-completed-p nil
  "Non-nil if a `completing-read' call was replayed during resume.")

(defun cmd-rewind-current-session-p (session)
  "Return non-nil if SESSION is the current recorded session."
  (eq session cmd-rewind-last-session))

(defun cmd-rewind-capture-input-before-command (session)
  "Capture minibuffer input before each command and save it into SESSION."
  (when (and (minibufferp)
             (not cmd-rewind-completing-read-replaying-p)
             (cmd-rewind-current-session-p session))
    (setq cmd-rewind-last-session
          (plist-put cmd-rewind-last-session
                     :completing-read-input
                     (minibuffer-contents-no-properties)))
    (setq cmd-rewind-last-session
          (plist-put cmd-rewind-last-session
                     :completing-read-input-captured
                     t))))

(defun cmd-rewind-capture-input-before-exit-minibuffer (session)
  "Capture minibuffer input on exit and save it into SESSION."
  (when (and (not cmd-rewind-completing-read-replaying-p)
             (not (plist-get session :completing-read-input-captured))
             (cmd-rewind-current-session-p session))
    ;; Fallback in case `cmd-rewind-capture-input-before-command' failed.
    (setq session
          (plist-put session
                     :completing-read-input
                     (minibuffer-contents-no-properties)))
    (setq cmd-rewind-last-session session)))

(defun cmd-rewind-setup-minibuffer (session)
  "Set up hooks to capture minibuffer input for SESSION."
  (add-hook 'pre-command-hook
            (apply-partially
             #'cmd-rewind-capture-input-before-command session)
            nil t)
  (add-hook 'minibuffer-exit-hook
            (apply-partially
             #'cmd-rewind-capture-input-before-exit-minibuffer session)
            nil t))

(defun cmd-rewind-read (orig args session)
  "Call ORIG with ARGS while capturing minibuffer input in SESSION."
  (if cmd-rewind-completing-read-replaying-p
      (apply orig args)
    (minibuffer-with-setup-hook
        (apply-partially #'cmd-rewind-setup-minibuffer session)
      (apply orig args))))

(defun cmd-rewind-excluded-command-p (command)
  "Return non-nil if named COMMAND matches an excluded command pattern."
  (and (symbolp command)
       (let ((name (symbol-name command)))
         (cl-some (lambda (pattern)
                    (string-match-p pattern name))
                  cmd-rewind-excluded-commands))))

(defun cmd-rewind-around-completing-read (orig &rest args)
  "Record `completing-read' or replay a saved session.
ORIG is the original function and ARGS are its arguments."

  ;; `this-command' changes to `exit-minibuffer' when `read-string' is called
  ;; so we use `current-minibuffer-command' instead
  (let* ((command current-minibuffer-command)
         session
         saved-completing-read-args
         completing-read-initial-input)
    (when cmd-rewind-debug
      (message "cmd-rewind-around-completing-read: command=%S" command))
    (cond
     ;; Anonymous&Non-interactive commands and never participate in recording or replay
     ((or (not (symbolp command))
          (not (commandp command)))
      (when cmd-rewind-debug
        (message "Ignoring command: %S" command))
      (apply orig args))

     ;; Replay a named command, but `completing-read' not called, yet.
     ((and cmd-rewind-replay-session
           (not cmd-rewind-completing-read-replaying-p))
      (setq session cmd-rewind-replay-session)
      (setq saved-completing-read-args
            (copy-sequence
             (plist-get session :completing-read-args)))
      (setq completing-read-initial-input
            (or (plist-get session :completing-read-input) ""))

      ;; INITIAL-INPUT is argument 5 (zero-based index 4).
      (while (< (length saved-completing-read-args) 5)
        (setq saved-completing-read-args
              (append saved-completing-read-args (list nil))))
      (setf (nth 4 saved-completing-read-args)
            completing-read-initial-input)

      (when cmd-rewind-debug
        (message "Replaying saved arguments: %S"
                 saved-completing-read-args))

      ;; Track success separately; dynamically bind the replaying flag so
      ;; it is restored even if the completion call exits with an error.
      (setq cmd-rewind-replay-completed-p t)
      (let ((cmd-rewind-completing-read-replaying-p t))
        (cmd-rewind-read orig saved-completing-read-args session)))

     ;; Do not record nested calls during replay, or commands explicitly excluded by configuration.
     ((or (and cmd-rewind-replay-session
               cmd-rewind-completing-read-replaying-p) ; inside `completing-read'
          ;; Please note `cmd-rewind-resume' is excluded too.
          ;; Its logic is different from other excluded commands, see the code from beginning of
          ;; this function!
          ;; So `cmd-rewind-excluded-command-p' called is near the end of conditional statement
          (cmd-rewind-excluded-command-p command))
      (when cmd-rewind-debug
        (message "Not recording command: %S" command))
      (apply orig args))

     ;; Record a new session.
     (t
      (when cmd-rewind-debug
        (message "Recording session for command: %S" command))
      (cmd-rewind-read
       orig
       args
       (setq cmd-rewind-last-session
             (list :command command
                   :completing-read-args (copy-sequence args)
                   :directory default-directory
                   :prefix current-prefix-arg
                   :completing-read-input (or (nth 4 args) ""))))))))

;;;###autoload
(defun cmd-rewind-resume ()
  "Resume the last recorded `completing-read' session."
  (interactive)
  (let* ((session cmd-rewind-last-session)
         (command (plist-get session :command))
         (default-directory (plist-get session :directory)))
    (unless session
      (user-error "No saved completing-read session"))
    (unless (and (symbolp command) (commandp command))
      (user-error "Saved command is not a named interactive command: %S"
                  command))
    (let ((cmd-rewind-replay-session session)
          (cmd-rewind-completing-read-replaying-p nil)
          (cmd-rewind-replay-completed-p nil)
          (current-prefix-arg (plist-get session :prefix)))
      (call-interactively command)
      (unless cmd-rewind-replay-completed-p
        (message
         "The command did not call completing-read during replay; session not resumed")))))

;;;###autoload
(define-minor-mode cmd-rewind-mode
  "Globally record `completing-read' sessions for `cmd-rewind'."
  :global t
  :group 'cmd-rewind
  (if cmd-rewind-mode
      (advice-add 'completing-read :around
                  #'cmd-rewind-around-completing-read)
    (advice-remove 'completing-read
                   #'cmd-rewind-around-completing-read)))

(provide 'cmd-rewind)
;;; cmd-rewind.el ends here