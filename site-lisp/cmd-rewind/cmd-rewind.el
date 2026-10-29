;;; cmd-rewind.el --- Resume the last completing-read session     -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Chen Bin

;; Author: Chen Bin <chb_sh@hotmail.com>
;; Package-Version: 1.0.1
;; Package-Requires: ((emacs "29.1"))
;; Keywords: convenience, tools
;; URL: http://github.com/redguardtoo/cmd-rewind

;; SPDX-License-Identifier: GPL-3.0-or-later

;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;; This file is NOT part of GNU Emacs.

;;; Commentary:

;; A completion-front-end-independent approximation of `ivy-resume' for
;; named interactive commands which use the built-in `completing-read'.
;;
;; The package records the arguments passed to `completing-read', the input
;; visible when the minibuffer exits, and the command/buffer context.
;; Calling `cmd-rewind-resume' re-runs that command and replays the saved
;; `completing-read' call with the saved arguments and last input.
;; Calling `cmd-rewind-clear' to clear the last recorded session.
;;
;; Each command must call `completing-read' only once.  Add commands that call it
;; multiple times to `cmd-rewind-excluded-commands'.
;;
;; Sessions can also be saved to and loaded from files:
;;   - `cmd-rewind-save-session' saves the current session to a file.
;;   - `cmd-rewind-load-session' loads a previously saved session from a file.
;;
;; Session files are stored in `cmd-rewind-session-directory', which defaults
;; to a "~/.emacs.d/cmd-rewind-sessions/".
;; The save and load commands allow sessions to be reused across Emacs
;; restarts, provided the saved arguments and completion data remain usable.
;;
;; Anonymous interactive functions are not recorded or replayed.
;;
;; If you use Ivy/Counsel/Swiper, use `ivy-resume' instead.
;; If you use Vertico (e.g., together with Consult), use `vertico-repeat'.
;; `cmd-rewind' targets the built-in `completing-read' with no
;; completion front-end (or front-ends that do not provide their own
;; resume command).
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

;;; Code:
(require 'cl-lib)
(require 'subr-x)

(defgroup cmd-rewind nil
  "Resume the last `completing-read' session."
  :group 'minibuffer
  :prefix "cmd-rewind-")

(defcustom cmd-rewind-session-directory
  (expand-file-name "cmd-rewind-sessions/" user-emacs-directory)
  "Directory where cmd-rewind sessions are stored."
  :type 'directory
  :group 'cmd-rewind)

(defcustom cmd-rewind-excluded-commands
  '("^cmd-rewind-resume$"
    "^cmd-rewind-save-session$"
    "^cmd-rewind-load-session$"
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

(defvar cmd-rewind-command-start-directory nil
  "Directory before the current interactive command started.")

(defun cmd-rewind-current-session-p (session)
  "Return non-nil if SESSION is the current recorded session."
  (eq session cmd-rewind-last-session))

(defun cmd-rewind-capture-command-start ()
  "Capture the command and directory before a command start."
  (unless (minibufferp)
    (setq cmd-rewind-command-start-directory default-directory)))

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
         completing-read-initial-input
         rlt)
    (when cmd-rewind-debug
      (message "cmd-rewind-around-completing-read: command=%S" command))
    (cond
     ;; Anonymous&Non-interactive commands and never participate in recording or replay
     ((or (not (symbolp command))
          (not (commandp command)))
      (when cmd-rewind-debug
        (message "Ignoring command: %S" command))
      (setq rlt (apply orig args)))

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
      (let ((cmd-rewind-completing-read-replaying-p t))
        (setq rlt (cmd-rewind-read orig saved-completing-read-args session))))

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
      (setq rlt (apply orig args)))

     ;; Record a new session.
     (t
      (when cmd-rewind-debug
        (message "Recording session for command: %S" command))
      (setq rlt
            (cmd-rewind-read
             orig
             args
             (setq cmd-rewind-last-session
                   (list :command command
                         :completing-read-args (copy-sequence args)
                         :directory (or cmd-rewind-command-start-directory default-directory)
                         :prefix current-prefix-arg
                         :completing-read-input (or (nth 4 args) "")
                         :completing-read-input-captured nil))))))
    rlt))


;;;###autoload
(defun cmd-rewind-clear ()
  "Clear the last recorded `completing-read' session."
  (interactive)
  (setq cmd-rewind-last-session nil))

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
          (current-prefix-arg (plist-get session :prefix)))
      (condition-case err
          (call-interactively command)
        (error
         (message "cmd-rewind-resume failed: %s" (error-message-string err))
         (signal (car err) (cdr err)))))))

;;;###autoload
(define-minor-mode cmd-rewind-mode
  "Globally record `completing-read' sessions for `cmd-rewind'."
  :global t
  :group 'cmd-rewind
  (cond
   (cmd-rewind-mode
    (advice-add 'completing-read :around #'cmd-rewind-around-completing-read)
    (add-hook 'pre-command-hook #'cmd-rewind-capture-command-start))
   (t
    (advice-remove 'completing-read #'cmd-rewind-around-completing-read)
    (remove-hook 'pre-command-hook #'cmd-rewind-capture-command-start))))

(defun cmd-rewind-sanitize-session-name (name)
  "Convert NAME into a safe filename component."
  (let ((name (replace-regexp-in-string
               "[^[:alnum:]_-]+" "-" name)))
    (setq name (replace-regexp-in-string "\\`[-_]+" "" name))
    (setq name (replace-regexp-in-string "[-_]+\\'" "" name))
    (if (string-empty-p name)
        "session"
      name)))


(defun cmd-rewind-default-session-name (session)
  "Generate a default filename stem from SESSION."
  (cmd-rewind-sanitize-session-name
   (format "%s-%s"
           (let ((command (plist-get session :command)))
             (if (symbolp command)
                 (symbol-name command)
               "session"))
           (or (plist-get session :completing-read-input) ""))))

(defun cmd-rewind-read-session-file (file)
  "Read a session plist from FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (goto-char (point-min))
    (let* ((read-eval nil)
           (read-circle t)
           (session (read (current-buffer))))
      ;; The file must contain exactly one Lisp object.
      (skip-chars-forward " \t\r\n")
      (unless (eobp)
        (error "Unexpected trailing content in %s" file))
      session)))


(defun cmd-rewind-serialize-session (session)
  "Serialize SESSION and verify that it can be read back."
  (let* ((print-length nil)
         (print-level nil)
         (print-circle t)
         (serialized (prin1-to-string session)))
    (with-temp-buffer
      (insert serialized)
      (goto-char (point-min))
      (let* ((read-eval nil)
             (read-circle t)
             (copy (read (current-buffer))))
        (skip-chars-forward " \t\r\n")
        (unless (eobp)
          (error "Unexpected trailing content after serialization"))
        (unless (equal copy session)
          (error "Session did not survive serialization unchanged"))))
    serialized))


;;;###autoload
(defun cmd-rewind-save-session ()
  "Save `cmd-rewind-last-session' to a named file."
  (interactive)

  (unless cmd-rewind-last-session
    (user-error "No recorded cmd-rewind session"))

  (let* ((session cmd-rewind-last-session)
         (default-name (cmd-rewind-default-session-name session))
         (input-name (read-string
                      (format "Save session as (default %s): " default-name)
                      nil nil default-name))
         (name (cmd-rewind-sanitize-session-name
                (if (string-empty-p input-name) default-name input-name)))
         (directory (expand-file-name cmd-rewind-session-directory))
         (file (expand-file-name (concat name ".sexp") directory))
         (serialized (condition-case err
                         (cmd-rewind-serialize-session session)
                       (error
                        (user-error "Cannot serialize session: %s"
                                    (error-message-string err))))))

    ;; make sure directory exsits
    (make-directory directory t)

    (when (file-exists-p file)
      (unless (yes-or-no-p (format "File %s exists.  Overwrite? " file))
        (user-error "Save cancelled")))

    (unless (file-writable-p directory)
      (user-error "Directory is not writable: %s" directory))

    (when (and (file-exists-p file)
               (not (file-writable-p file)))
      (user-error "File is not writable: %s" file))

    (with-temp-file file
      (insert ";; cmd-rewind session plist\n")
      (insert serialized "\n"))

    (message "cmd-rewind session saved: %s" file)))


;;;###autoload
(defun cmd-rewind-load-session (&optional file)
  "Load a saved session plist into `cmd-rewind-last-session'.

Interactively, prompt for a session file.
Optional FILE specifies the file to load."
  (interactive)
  (let* ((directory
          (file-name-as-directory
           (expand-file-name cmd-rewind-session-directory)))
         (session-file
          (or file
              (read-file-name
               "Load cmd-rewind session: "
               directory
               nil
               t
               nil
               (lambda (candidate)
                 (or (file-directory-p candidate)
                     (string-suffix-p ".sexp" candidate))))))
         (session-file (expand-file-name session-file)))

    (unless (file-regular-p session-file)
      (user-error "Not a regular session file: %s" session-file))

    (let ((session
           (condition-case err
               (cmd-rewind-read-session-file session-file)
             (error
              (user-error "Cannot load session: %s"
                          (error-message-string err))))))
      ;; Change the current session only after successful validation.
      (setq cmd-rewind-last-session session)
      (message "cmd-rewind session loaded: %s"
               (file-name-nondirectory session-file))
      session)))

(provide 'cmd-rewind)
;;; cmd-rewind.el ends here