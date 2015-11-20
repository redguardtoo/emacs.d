;;; haskell-load.el --- Compiling and loading modules in the GHCi process

;; Copyright (c) 2014 Chris Done. All rights reserved.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:

(require 'cl-lib)
(require 'haskell-process)
(require 'haskell-interactive-mode)
(require 'haskell-modules)
(require 'haskell-commands)
(require 'haskell-session)

(defun haskell-process-look-config-changes (session)
  "Checks whether a cabal configuration file has
changed. Restarts the process if that is the case."
  (let ((current-checksum (haskell-session-get session 'cabal-checksum))
        (new-checksum (haskell-cabal-compute-checksum
                       (haskell-session-get session 'cabal-dir))))
    (when (not (string= current-checksum new-checksum))
      (haskell-interactive-mode-echo session (format "Cabal file changed: %s" new-checksum))
      (haskell-session-set-cabal-checksum session
                                          (haskell-session-get session 'cabal-dir))
      (unless (and haskell-process-prompt-restart-on-cabal-change
                   (not (y-or-n-p "Cabal file changed; restart GHCi process? ")))
        (haskell-process-start (haskell-interactive-session))))))

(defun haskell-process-live-build (process buffer echo-in-repl)
  "Show live updates for loading files."
  (cond ((haskell-process-consume
          process
          (concat "\\[[ ]*\\([0-9]+\\) of \\([0-9]+\\)\\]"
                  " Compiling \\([^ ]+\\)[ ]+"
                  "( \\([^ ]+\\), \\([^ ]+\\) )[^\r\n]*[\r\n]+"))
         (haskell-process-echo-load-message process buffer echo-in-repl nil)
         t)
        ((haskell-process-consume
          process
          (concat "\\[[ ]*\\([0-9]+\\) of \\([0-9]+\\)\\]"
                  " Compiling \\[TH\\] \\([^ ]+\\)[ ]+"
                  "( \\([^ ]+\\), \\([^ ]+\\) )[^\r\n]*[\r\n]+"))
         (haskell-process-echo-load-message process buffer echo-in-repl t)
         t)
        ((haskell-process-consume process "Loading package \\([^ ]+\\) ... linking ... done.\n")
         (haskell-mode-message-line
          (format "Loading: %s"
                  (match-string 1 buffer)))
         t)
        ((haskell-process-consume
          process
          "^Preprocessing executables for \\(.+?\\)\\.\\.\\.")
         (let ((msg (format "Preprocessing: %s" (match-string 1 buffer))))
           (haskell-interactive-mode-echo
            (haskell-process-session process)
            msg)
           (haskell-mode-message-line msg)))
        ((haskell-process-consume process "Linking \\(.+?\\) \\.\\.\\.")
         (let ((msg (format "Linking: %s" (match-string 1 buffer))))
           (haskell-interactive-mode-echo (haskell-process-session process) msg)
           (haskell-mode-message-line msg)))
        ((haskell-process-consume process "\nBuilding \\(.+?\\)\\.\\.\\.")
         (let ((msg (format "Building: %s" (match-string 1 buffer))))
           (haskell-interactive-mode-echo
            (haskell-process-session process)
            msg)
           (haskell-mode-message-line msg)))))

(defun haskell-process-load-complete (session process buffer reload module-buffer &optional cont)
  "Handle the complete loading response. BUFFER is the string of
text being sent over the process pipe. MODULE-BUFFER is the
actual Emacs buffer of the module being loaded."
  (when (get-buffer (format "*%s:splices*" (haskell-session-name session)))
    (with-current-buffer (haskell-interactive-mode-splices-buffer session)
      (erase-buffer)))
  (cond ((haskell-process-consume process "Ok, modules loaded: \\(.+\\)\\.$")
         (let* ((modules (haskell-process-extract-modules buffer))
                (cursor (haskell-process-response-cursor process)))
           (haskell-process-set-response-cursor process 0)
           (let ((warning-count 0))
             (while (haskell-process-errors-warnings session process buffer)
               (setq warning-count (1+ warning-count)))
             (haskell-process-set-response-cursor process cursor)
             (if (and (not reload)
                      haskell-process-reload-with-fbytecode)
                 (haskell-process-reload-with-fbytecode process module-buffer)
               (haskell-process-import-modules process (car modules)))
             (haskell-mode-message-line
              (if reload "Reloaded OK." "OK."))
             (when cont
               (condition-case e
                   (funcall cont t)
                 (error (message "%S" e))
                 (quit nil))))))
        ((haskell-process-consume process "Failed, modules loaded: \\(.+\\)\\.$")
         (let* ((modules (haskell-process-extract-modules buffer))
                (cursor (haskell-process-response-cursor process)))
           (haskell-process-set-response-cursor process 0)
           (while (haskell-process-errors-warnings session process buffer))
           (haskell-process-set-response-cursor process cursor)
           (if (and (not reload) haskell-process-reload-with-fbytecode)
               (haskell-process-reload-with-fbytecode process module-buffer)
             (haskell-process-import-modules process (car modules)))
           (haskell-interactive-mode-compile-error session "Compilation failed.")
           (when cont
             (condition-case e
                 (funcall cont nil)
               (error (message "%S" e))
               (quit nil)))))))

(defun haskell-process-suggest-imports (session file modules ident)
  "Given a list of MODULES, suggest adding them to the import section."
  (cl-assert session)
  (cl-assert file)
  (cl-assert ident)
  (let* ((process (haskell-session-process session))
         (suggested-already (haskell-process-suggested-imports process))
         (module (cond ((> (length modules) 1)
                        (when (y-or-n-p (format "Identifier `%s' not in scope, choose module to import?"
                                                ident))
                          (haskell-complete-module-read "Module: " modules)))
                       ((= (length modules) 1)
                        (let ((module (car modules)))
                          (unless (member module suggested-already)
                            (haskell-process-set-suggested-imports process (cons module suggested-already))
                            (when (y-or-n-p (format "Identifier `%s' not in scope, import `%s'?"
                                                    ident
                                                    module))
                              module)))))))
    (when module
      (haskell-process-find-file session file)
      (haskell-add-import module))))

(defun haskell-process-trigger-suggestions (session msg file line)
  "Trigger prompting to add any extension suggestions."
  (cond ((let ((case-fold-search nil))
           (or (and (string-match " -X\\([A-Z][A-Za-z]+\\)" msg)
                    (not (string-match "\\([A-Z][A-Za-z]+\\) is deprecated" msg)))
               (string-match "Use \\([A-Z][A-Za-z]+\\) to permit this" msg)
               (string-match "Use \\([A-Z][A-Za-z]+\\) to allow" msg)
               (string-match "use \\([A-Z][A-Za-z]+\\)" msg)
               (string-match "You need \\([A-Z][A-Za-z]+\\)" msg)))
         (when haskell-process-suggest-language-pragmas
           (haskell-process-suggest-pragma session "LANGUAGE" (match-string 1 msg) file)))
        ((string-match " The \\(qualified \\)?import of[ ][‘`‛]\\([^ ]+\\)['’] is redundant" msg)
         (when haskell-process-suggest-remove-import-lines
           (haskell-process-suggest-remove-import session
                                                  file
                                                  (match-string 2 msg)
                                                  line)))
        ((string-match "Warning: orphan instance: " msg)
         (when haskell-process-suggest-no-warn-orphans
           (haskell-process-suggest-pragma session "OPTIONS" "-fno-warn-orphans" file)))
        ((or (string-match "against inferred type [‘`‛]\\[Char\\]['’]" msg)
             (string-match "with actual type [‘`‛]\\[Char\\]['’]" msg))
         (when haskell-process-suggest-overloaded-strings
           (haskell-process-suggest-pragma session "LANGUAGE" "OverloadedStrings" file)))
        ((string-match "^Not in scope: .*[‘`‛]\\(.+\\)['’]$" msg)
         (let* ((match1 (match-string 1 msg))
                (ident (if (string-match "^[A-Za-z0-9_'.]+\\.\\(.+\\)$" match1)
                           ;; Skip qualification.
                           (match-string 1 match1)
                         match1)))
           (when haskell-process-suggest-hoogle-imports
             (let ((modules (haskell-process-hoogle-ident ident)))
               (haskell-process-suggest-imports session file modules ident)))
           (when haskell-process-suggest-haskell-docs-imports
             (let ((modules (haskell-process-haskell-docs-ident ident)))
               (haskell-process-suggest-imports session file modules ident)))
           (when haskell-process-suggest-hayoo-imports
             (let ((modules (haskell-process-hayoo-ident ident)))
               (haskell-process-suggest-imports session file modules ident)))))
        ((string-match "^[ ]+It is a member of the hidden package [‘`‛]\\(.+\\)['’].$" msg)
         (when haskell-process-suggest-add-package
           (haskell-process-suggest-add-package session msg)))))

(defun haskell-process-do-cabal (command)
  "Run a Cabal command."
  (let ((process (haskell-interactive-process)))
    (haskell-process-queue-command
     process
     (make-haskell-command
      :state (list (haskell-interactive-session) process command 0)

      :go
      (lambda (state)
        (haskell-process-send-string
         (cadr state)
         (format haskell-process-do-cabal-format-string
                 (haskell-session-cabal-dir (car state))
                 (format "%s %s"
                         (cl-ecase (haskell-process-type)
                           ('ghci haskell-process-path-cabal)
                           ('cabal-repl haskell-process-path-cabal)
                           ('cabal-ghci haskell-process-path-cabal)
                           ('cabal-dev haskell-process-path-cabal-dev))
                         (cl-caddr state)))))

      :live
      (lambda (state buffer)
        (let ((cmd (replace-regexp-in-string "^\\([a-z]+\\).*"
                                             "\\1"
                                             (cl-caddr state))))
          (cond ((or (string= cmd "build")
                     (string= cmd "install"))
                 (haskell-process-live-build (cadr state) buffer t))
                (t
                 (haskell-process-cabal-live state buffer)))))

      :complete
      (lambda (state response)
        (let* ((process (cadr state))
               (session (haskell-process-session process))
               (message-count 0)
               (cursor (haskell-process-response-cursor process)))
          (haskell-process-set-response-cursor process 0)
          (while (haskell-process-errors-warnings session process response)
            (setq message-count (1+ message-count)))
          (haskell-process-set-response-cursor process cursor)
          (let ((msg (format "Complete: cabal %s (%s compiler messages)"
                             (cl-caddr state)
                             message-count)))
            (haskell-interactive-mode-echo session msg)
            (when (= message-count 0)
              (haskell-interactive-mode-echo
               session
               "No compiler messages, dumping complete output:")
              (haskell-interactive-mode-echo session response))
            (haskell-mode-message-line msg)
            (when (and haskell-notify-p
                       (fboundp 'notifications-notify))
              (notifications-notify
               :title (format "*%s*" (haskell-session-name (car state)))
               :body msg
               :app-name (cl-ecase (haskell-process-type)
                           ('ghci haskell-process-path-cabal)
                           ('cabal-repl haskell-process-path-cabal)
                           ('cabal-ghci haskell-process-path-cabal)
                           ('cabal-dev haskell-process-path-cabal-dev))
               :app-icon haskell-process-logo)))))))))

(defun haskell-process-echo-load-message (process buffer echo-in-repl th)
  "Echo a load message."
  (let ((session (haskell-process-session process))
        (module-name (match-string 3 buffer))
        (file-name (match-string 4 buffer)))
    (haskell-interactive-show-load-message
     session
     'compiling
     module-name
     (haskell-session-strip-dir session file-name)
     echo-in-repl
     th)))

(defun haskell-process-extract-modules (buffer)
  "Extract the modules from the process buffer."
  (let* ((modules-string (match-string 1 buffer))
         (modules (split-string modules-string ", ")))
    (cons modules modules-string)))

(defun haskell-process-errors-warnings (session process buffer &optional return-only)
  "Trigger handling type errors or warnings. Either prints the
messages in the interactive buffer or if CONT is specified,
passes the error onto that."
  (cond
   ((haskell-process-consume
     process
     "\\(Module imports form a cycle:[ \n]+module [^ ]+ ([^)]+)[[:unibyte:][:nonascii:]]+?\\)\nFailed")
    (let ((err (match-string 1 buffer)))
      (if (string-match "module [`'‘‛]\\([^ ]+\\)['’`] (\\([^)]+\\))" err)
          (let* ((default-directory (haskell-session-current-dir session))
                 (module (match-string 1 err))
                 (file (match-string 2 err))
                 (relative-file-name (file-relative-name file)))
            (unless return-only
              (haskell-interactive-show-load-message
               session
               'import-cycle
               module
               relative-file-name
               nil
               nil)
              (haskell-interactive-mode-compile-error
               session
               (format "%s:1:0: %s"
                       relative-file-name
                       err)))
            (list :file file :line 1 :col 0 :msg err :type 'error))
        t)))
   ((haskell-process-consume
     process
     (concat "[\r\n]\\([A-Z]?:?[^ \r\n:][^:\n\r]+\\):\\([0-9()-:]+\\):"
             "[ \n\r]+\\([[:unibyte:][:nonascii:]]+?\\)\n[^ ]"))
    (haskell-process-set-response-cursor process
                                         (- (haskell-process-response-cursor process) 1))
    (let* ((buffer (haskell-process-response process))
           (file (match-string 1 buffer))
           (location (match-string 2 buffer))
           (error-msg (match-string 3 buffer))
           (warning (string-match "^Warning:" error-msg))
           (splice (string-match "^Splicing " error-msg))
           (final-msg (format "%s:%s: %s"
                              (haskell-session-strip-dir session file)
                              location
                              error-msg)))
      (if return-only
          (let* ((location (haskell-process-parse-error (concat file ":" location ": x")))
                 (file (plist-get location :file))
                 (line (plist-get location :line))
                 (col1 (plist-get location :col)))
            (list :file file :line line :col col1 :msg error-msg :type (if warning 'warning 'error)))
        (progn (funcall (cond (warning
                               'haskell-interactive-mode-compile-warning)
                              (splice
                               'haskell-interactive-mode-compile-splice)
                              (t 'haskell-interactive-mode-compile-error))
                        session final-msg)
               (unless warning
                 (haskell-mode-message-line final-msg))
               (haskell-process-trigger-suggestions
                session
                error-msg
                file
                (plist-get (haskell-process-parse-error final-msg) :line))
               t))))))

(defun haskell-interactive-show-load-message (session type module-name file-name echo th)
  "Show the '(Compiling|Loading) X' message."
  (let ((msg (concat
              (cl-ecase type
                ('compiling
                 (if haskell-interactive-mode-include-file-name
                     (format "Compiling: %s (%s)" module-name file-name)
                   (format "Compiling: %s" module-name)))
                ('loading (format "Loading: %s" module-name))
                ('import-cycle (format "Module has an import cycle: %s" module-name)))
              (if th " [TH]" ""))))
    (haskell-mode-message-line msg)
    (when haskell-interactive-mode-delete-superseded-errors
      (haskell-interactive-mode-delete-compile-messages session file-name))
    (when echo
      (haskell-interactive-mode-echo session msg))))

;;;###autoload
(defun haskell-process-reload-devel-main ()
  "Reload the module `DevelMain' and then run
`DevelMain.update'. This is for doing live update of the code of
servers or GUI applications. Put your development version of the
program in `DevelMain', and define `update' to auto-start the
program on a new thread, and use the `foreign-store' package to
access the running context across :load/:reloads in GHCi."
  (interactive)
  (with-current-buffer (or (get-buffer "DevelMain.hs")
                           (if (y-or-n-p "You need to open a buffer named DevelMain.hs. Find now?")
                               (ido-find-file)
                             (error "No DevelMain.hs buffer.")))
    (let ((session (haskell-interactive-session)))
      (let ((process (haskell-interactive-process)))
        (haskell-process-queue-command
         process
         (make-haskell-command
          :state (list :session session
                       :process process
                       :buffer (current-buffer))
          :go (lambda (state)
                (haskell-process-send-string (plist-get state ':process)
                                             ":l DevelMain"))
          :live (lambda (state buffer)
                  (haskell-process-live-build (plist-get state ':process)
                                              buffer
                                              nil))
          :complete (lambda (state response)
                      (haskell-process-load-complete
                       (plist-get state ':session)
                       (plist-get state ':process)
                       response
                       nil
                       (plist-get state ':buffer)
                       (lambda (ok)
                         (when ok
                           (haskell-process-queue-without-filters
                            (haskell-interactive-process)
                            "DevelMain.update")
                           (message "DevelMain updated.")))))))))))

(provide 'haskell-load)
