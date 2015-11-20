;;; haskell-commands.el --- Commands that can be run on the process

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
(require 'etags)
(require 'haskell-compat)
(require 'haskell-process)
(require 'haskell-font-lock)
(require 'haskell-interactive-mode)
(require 'haskell-session)
(require 'highlight-uses-mode)

;;;###autoload
(defun haskell-process-restart ()
  "Restart the inferior Haskell process."
  (interactive)
  (haskell-process-reset (haskell-interactive-process))
  (haskell-process-set (haskell-interactive-process) 'command-queue nil)
  (haskell-process-start (haskell-interactive-session)))

(defun haskell-process-start (session)
  "Start the inferior Haskell process."
  (let ((existing-process (get-process (haskell-session-name (haskell-interactive-session)))))
    (when (processp existing-process)
      (haskell-interactive-mode-echo session "Restarting process ...")
      (haskell-process-set (haskell-session-process session) 'is-restarting t)
      (delete-process existing-process)))
  (let ((process (or (haskell-session-process session)
                     (haskell-process-make (haskell-session-name session))))
        (old-queue (haskell-process-get (haskell-session-process session)
                                        'command-queue)))
    (haskell-session-set-process session process)
    (haskell-process-set-session process session)
    (haskell-process-set-cmd process nil)
    (haskell-process-set (haskell-session-process session) 'is-restarting nil)
    (let ((default-directory (haskell-session-cabal-dir session))
          (log-and-command (haskell-process-compute-process-log-and-command session (haskell-process-type))))
      (haskell-session-pwd session)
      (haskell-process-set-process
       process
       (progn
         (haskell-process-log (propertize (format "%S" log-and-command)))
         (apply #'start-process (cdr log-and-command)))))
    (progn (set-process-sentinel (haskell-process-process process) 'haskell-process-sentinel)
           (set-process-filter (haskell-process-process process) 'haskell-process-filter))
    (haskell-process-send-startup process)
    (unless (eq 'cabal-repl (haskell-process-type)) ;; "cabal repl" sets the proper CWD
      (haskell-process-change-dir session
                                  process
                                  (haskell-session-current-dir session)))
    (haskell-process-set process 'command-queue
                         (append (haskell-process-get (haskell-session-process session)
                                                      'command-queue)
                                 old-queue))
    process))

(defun haskell-process-send-startup (process)
  "Send the necessary start messages."
  (haskell-process-queue-command
   process
   (make-haskell-command
    :state process

    :go (lambda (process)
          (haskell-process-send-string process ":set prompt \"\\4\"")
          (haskell-process-send-string process "Prelude.putStrLn \"\"")
          (haskell-process-send-string process ":set -v1"))

    :live (lambda (process buffer)
            (when (haskell-process-consume
                   process
                   "^\*\*\* WARNING: \\(.+\\) is writable by someone else, IGNORING!$")
              (let ((path (match-string 1 buffer)))
                (haskell-session-modify
                 (haskell-process-session process)
                 'ignored-files
                 (lambda (files)
                   (cl-remove-duplicates (cons path files) :test 'string=)))
                (haskell-interactive-mode-compile-warning
                 (haskell-process-session process)
                 (format "GHCi is ignoring: %s (run M-x haskell-process-unignore)"
                         path)))))

    :complete (lambda (process _)
                (haskell-interactive-mode-echo
                 (haskell-process-session process)
                 (concat (nth (random (length haskell-process-greetings))
                              haskell-process-greetings)
                         (when haskell-process-show-debug-tips
                           "
If I break, you can:
  1. Restart:           M-x haskell-process-restart
  2. Configure logging: C-h v haskell-process-log (useful for debugging)
  3. General config:    M-x customize-mode
  4. Hide these tips:   C-h v haskell-process-show-debug-tips")))))))

(defun haskell-commands-process ()
  "Get the Haskell session, throws an error if not available."
  (or (haskell-session-process (haskell-session-maybe))
      (error "No Haskell session/process associated with this
      buffer. Maybe run M-x haskell-session-change?")))

;;;###autoload
(defun haskell-process-clear ()
  "Clear the current process."
  (interactive)
  (haskell-process-reset (haskell-commands-process))
  (haskell-process-set (haskell-commands-process) 'command-queue nil))

;;;###autoload
(defun haskell-process-interrupt ()
  "Interrupt the process (SIGINT)."
  (interactive)
  (interrupt-process (haskell-process-process (haskell-commands-process))))

(defun haskell-process-reload-with-fbytecode (process module-buffer)
  "Reload FILE-NAME with -fbyte-code set, and then restore -fobject-code."
  (haskell-process-queue-without-filters process ":set -fbyte-code")
  (haskell-process-touch-buffer process module-buffer)
  (haskell-process-queue-without-filters process ":reload")
  (haskell-process-queue-without-filters process ":set -fobject-code"))

;;;###autoload
(defun haskell-process-touch-buffer (process buffer)
  "Updates mtime on the file for BUFFER by queing a touch on
PROCESS."
  (interactive)
  (haskell-process-queue-command
   process
   (make-haskell-command
    :state (cons process buffer)
    :go (lambda (state)
          (haskell-process-send-string
           (car state)
           (format ":!%s %s"
                   "touch"
                   (shell-quote-argument (buffer-file-name
                                          (cdr state))))))
    :complete (lambda (state _)
                (with-current-buffer (cdr state)
                  (clear-visited-file-modtime))))))

(defvar url-http-response-status)
(defvar url-http-end-of-headers)

(defun haskell-process-hayoo-ident (ident)
  "Hayoo for IDENT, returns a list of modules asyncronously through CALLBACK."
  ;; We need a real/simulated closure, because otherwise these
  ;; variables will be unbound when the url-retrieve callback is
  ;; called.
  ;; TODO: Remove when this code is converted to lexical bindings by
  ;; default (Emacs 24.1+)
  (let ((url (format haskell-process-hayoo-query-url (url-hexify-string ident))))
    (with-current-buffer (url-retrieve-synchronously url)
      (if (= 200 url-http-response-status)
          (progn
            (goto-char url-http-end-of-headers)
            (let* ((res (json-read))
                   (results (assoc-default 'result res)))
              ;; TODO: gather packages as well, and when we choose a
              ;; given import, check that we have the package in the
              ;; cabal file as well.
              (cl-mapcan (lambda (r)
                           ;; append converts from vector -> list
                           (append (assoc-default 'resultModules r) nil))
                         results)))
        (warn "HTTP error %s fetching %s" url-http-response-status url)))))

(defun haskell-process-hoogle-ident (ident)
  "Hoogle for IDENT, returns a list of modules."
  (with-temp-buffer
    (let ((hoogle-error (call-process "hoogle" nil t nil "search" "--exact" ident)))
      (goto-char (point-min))
      (unless (or (/= 0 hoogle-error)
                  (looking-at "^No results found")
                  (looking-at "^package "))
        (while (re-search-forward "^\\([^ ]+\\).*$" nil t)
          (replace-match "\\1" nil nil))
        (cl-remove-if (lambda (a) (string= "" a))
                      (split-string (buffer-string)
                                    "\n"))))))

(defun haskell-process-haskell-docs-ident (ident)
  "Search with haskell-docs for IDENT, returns a list of modules."
  (cl-remove-if-not (lambda (a) (string-match "^[A-Z][A-Za-b0-9_'.]+$" a))
                    (split-string (shell-command-to-string (concat "haskell-docs --modules " ident))
                                  "\n")))

(defun haskell-process-import-modules (process modules)
  "Import `modules' with :m +, and send any import statements
from `module-buffer'."
  (when haskell-process-auto-import-loaded-modules
    (haskell-process-queue-command
     process
     (make-haskell-command
      :state (cons process modules)
      :go (lambda (state)
            (haskell-process-send-string
             (car state)
             (format ":m + %s" (mapconcat 'identity (cdr state) " "))))))))

;;;###autoload
(defun haskell-describe (ident)
  "Describe the given identifier."
  (interactive (list (read-from-minibuffer "Describe identifier: "
                                           (haskell-ident-at-point))))
  (let ((results (read (shell-command-to-string
                        (concat "haskell-docs --sexp "
                                ident)))))
    (help-setup-xref (list #'haskell-describe ident)
		     (called-interactively-p 'interactive))
    (save-excursion
      (with-help-window (help-buffer)
        (with-current-buffer (help-buffer)
          (if results
              (cl-loop for result in results
                       do (insert (propertize ident 'font-lock-face
                                              '((:inherit font-lock-type-face
                                                          :underline t)))
                                  " is defined in "
                                  (let ((module (cadr (assoc 'module result))))
                                    (if module
                                        (concat module " ")
                                      ""))
                                  (cadr (assoc 'package result))
                                  "\n\n")
                       do (let ((type (cadr (assoc 'type result))))
                            (when type
                              (insert (haskell-fontify-as-mode type 'haskell-mode)
                                      "\n")))
                       do (let ((args (cadr (assoc 'type results))))
                            (cl-loop for arg in args
                                     do (insert arg "\n"))
                            (insert "\n"))
                       do (insert (cadr (assoc 'documentation result)))
                       do (insert "\n\n"))
            (insert "No results for " ident)))))))

;;;###autoload
(defun haskell-rgrep (&optional prompt)
  "Grep the effective project for the symbol at point. Very
useful for codebase navigation. Prompts for an arbitrary regexp
given a prefix arg."
  (interactive "P")
  (let ((sym (if prompt
                 (read-from-minibuffer "Look for: ")
               (haskell-ident-at-point))))
    (rgrep sym
           "*.hs" ;; TODO: common Haskell extensions.
           (haskell-session-current-dir (haskell-interactive-session)))))

;;;###autoload
(defun haskell-process-do-info (&optional prompt-value)
  "Print info on the identifier at point.
If PROMPT-VALUE is non-nil, request identifier via mini-buffer."
  (interactive "P")
  (haskell-process-do-simple-echo
   (let ((ident (replace-regexp-in-string
                 "^!\\([A-Z_a-z]\\)"
                 "\\1"
                 (if prompt-value
                     (read-from-minibuffer "Info: " (haskell-ident-at-point))
                   (haskell-ident-at-point))))
         (modname (unless prompt-value
                    (haskell-utils-parse-import-statement-at-point))))
     (if modname
         (format ":browse! %s" modname)
       (format (if (string-match "^[a-zA-Z_]" ident)
                   ":info %s"
                 ":info (%s)")
               (or ident
                   (haskell-ident-at-point)))))
   'haskell-mode))

;;;###autoload
(defun haskell-process-do-type (&optional insert-value)
  "Print the type of the given expression."
  (interactive "P")
  (if insert-value
      (haskell-process-insert-type)
    (haskell-process-do-simple-echo
     (let ((ident (haskell-ident-at-point)))
       ;; TODO: Generalize all these `string-match' of ident calls into
       ;; one function.
       (format (if (string-match "^[_[:lower:][:upper:]]" ident)
                   ":type %s"
                 ":type (%s)")
               ident))
     'haskell-mode)))

;;;###autoload
(defun haskell-mode-jump-to-def-or-tag (&optional next-p)
  "Jump to the definition (by consulting GHCi), or (fallback)
jump to the tag.

Remember: If GHCi is busy doing something, this will delay, but
it will always be accurate, in contrast to tags, which always
work but are not always accurate.
If the definition or tag is found, the location from which you jumped
will be pushed onto `xref--marker-ring', so you can return to that
position with `xref-pop-marker-stack'."
  (interactive "P")
  (let ((initial-loc (point-marker))
        (loc (haskell-mode-find-def (haskell-ident-at-point))))
    (if loc
        (haskell-mode-handle-generic-loc loc)
      (call-interactively 'haskell-mode-tag-find))
    (unless (equal initial-loc (point-marker))
      (save-excursion
        (goto-char initial-loc)
        (set-mark-command nil)
        ;; Store position for return with `xref-pop-marker-stack'
        (xref-push-marker-stack)))))

;;;###autoload
(defun haskell-mode-goto-loc ()
  "Go to the location of the thing at point. Requires the :loc-at
command from GHCi."
  (interactive)
  (let ((loc (haskell-mode-loc-at)))
    (when loc
      (haskell-mode-goto-span loc))))

(defun haskell-mode-goto-span (span)
  "Jump to the span, whatever file and line and column it needs
to to get there."
  (xref-push-marker-stack)
  (find-file (expand-file-name (plist-get span :path)
                               (haskell-session-cabal-dir (haskell-interactive-session))))
  (goto-char (point-min))
  (forward-line (1- (plist-get span :start-line)))
  (forward-char (plist-get span :start-col)))

(defun haskell-process-insert-type ()
  "Get the identifer at the point and insert its type, if
possible, using GHCi's :type."
  (let ((process (haskell-interactive-process))
        (query (let ((ident (haskell-ident-at-point)))
                 (format (if (string-match "^[_[:lower:][:upper:]]" ident)
                             ":type %s"
                           ":type (%s)")
                         ident))))
    (haskell-process-queue-command
     process
     (make-haskell-command
      :state (list process query (current-buffer))
      :go (lambda (state)
            (haskell-process-send-string (nth 0 state)
                                         (nth 1 state)))
      :complete (lambda (state response)
                  (cond
                   ;; TODO: Generalize this into a function.
                   ((or (string-match "^Top level" response)
                        (string-match "^<interactive>" response))
                    (message response))
                   (t
                    (with-current-buffer (nth 2 state)
                      (goto-char (line-beginning-position))
                      (insert (format "%s\n" (replace-regexp-in-string "\n$" "" response)))))))))))

(defun haskell-mode-find-def (ident)
  "Find definition location of identifier. Uses the GHCi process
to find the location.

Returns:

    (library <package> <module>)
    (file <path> <line> <col>)
    (module <name>)
"
  (let ((reply (haskell-process-queue-sync-request
                (haskell-interactive-process)
                (format (if (string-match "^[a-zA-Z_]" ident)
                            ":info %s"
                          ":info (%s)")
                        ident))))
    (let ((match (string-match "-- Defined \\(at\\|in\\) \\(.+\\)$" reply)))
      (when match
        (let ((defined (match-string 2 reply)))
          (let ((match (string-match "\\(.+?\\):\\([0-9]+\\):\\([0-9]+\\)$" defined)))
            (cond
             (match
              (list 'file
                    (expand-file-name (match-string 1 defined)
                                      (haskell-session-current-dir (haskell-interactive-session)))
                    (string-to-number (match-string 2 defined))
                    (string-to-number (match-string 3 defined))))
             (t
              (let ((match (string-match "`\\(.+?\\):\\(.+?\\)'$" defined)))
                (if match
                    (list 'library
                          (match-string 1 defined)
                          (match-string 2 defined))
                  (let ((match (string-match "`\\(.+?\\)'$" defined)))
                    (if match
                        (list 'module
                              (match-string 1 defined))))))))))))))

;;;###autoload
(defun haskell-mode-jump-to-def (ident)
  "Jump to definition of identifier at point."
  (interactive (list (haskell-ident-at-point)))
  (let ((loc (haskell-mode-find-def ident)))
    (when loc
      (haskell-mode-handle-generic-loc loc))))

(defun haskell-mode-handle-generic-loc (loc)
  "Either jump to or display a generic location. Either a file or
a library."
  (cl-case (car loc)
    (file (haskell-mode-jump-to-loc (cdr loc)))
    (library (message "Defined in `%s' (%s)."
                      (elt loc 2)
                      (elt loc 1)))
    (module (message "Defined in `%s'."
                     (elt loc 1)))))

(defun haskell-mode-loc-at ()
  "Get the location at point. Requires the :loc-at command from
GHCi."
  (let ((pos (or (when (region-active-p)
                   (cons (region-beginning)
                         (region-end)))
                 (haskell-spanable-pos-at-point)
                 (cons (point)
                       (point)))))
    (when pos
      (let ((reply (haskell-process-queue-sync-request
                    (haskell-interactive-process)
                    (save-excursion
                      (format ":loc-at %s %d %d %d %d %s"
                              (buffer-file-name)
                              (progn (goto-char (car pos))
                                     (line-number-at-pos))
                              (1+ (current-column)) ;; GHC uses 1-based columns.
                              (progn (goto-char (cdr pos))
                                     (line-number-at-pos))
                              (1+ (current-column)) ;; GHC uses 1-based columns.
                              (buffer-substring-no-properties (car pos)
                                                              (cdr pos)))))))
        (if reply
            (if (string-match "\\(.*?\\):(\\([0-9]+\\),\\([0-9]+\\))-(\\([0-9]+\\),\\([0-9]+\\))"
                              reply)
                (list :path (match-string 1 reply)
                      :start-line (string-to-number (match-string 2 reply))
                      ;; ;; GHC uses 1-based columns.
                      :start-col (1- (string-to-number (match-string 3 reply)))
                      :end-line (string-to-number (match-string 4 reply))
                      ;; GHC uses 1-based columns.
                      :end-col (1- (string-to-number (match-string 5 reply))))
              (error (propertize reply 'face 'compilation-error)))
          (error (propertize "No reply. Is :loc-at supported?"
                             'face 'compilation-error)))))))

(defun haskell-mode-type-at ()
  "Get the type of the thing at point. Requires the :type-at
command from GHCi."
  (let ((pos (or (when (region-active-p)
                   (cons (region-beginning)
                         (region-end)))
                 (haskell-spanable-pos-at-point)
                 (cons (point)
                       (point)))))
    (when pos
      (replace-regexp-in-string
       "\n$"
       ""
       (save-excursion
         (haskell-process-queue-sync-request
          (haskell-interactive-process)
          (replace-regexp-in-string
           "\n"
           " "
           (format ":type-at %s %d %d %d %d %s"
                   (buffer-file-name)
                   (progn (goto-char (car pos))
                          (line-number-at-pos))
                   (1+ (current-column))
                   (progn (goto-char (cdr pos))
                          (line-number-at-pos))
                   (1+ (current-column))
                   (buffer-substring-no-properties (car pos)
                                                   (cdr pos))))))))))

;;;###autoload
(defun haskell-process-cd (&optional not-interactive)
  "Change directory."
  (interactive)
  (let* ((session (haskell-interactive-session))
         (dir (haskell-session-pwd session t)))
    (haskell-process-log
     (propertize (format "Changing directory to %s ...\n" dir)
                 'face font-lock-comment-face))
    (haskell-process-change-dir session
                                (haskell-interactive-process)
                                dir)))

(defun haskell-session-pwd (session &optional change)
  "Prompt for the current directory."
  (or (unless change
        (haskell-session-get session 'current-dir))
      (progn (haskell-session-set-current-dir
              session
              (haskell-utils-read-directory-name
               (if change "Change directory: " "Set current directory: ")
               (or (haskell-session-get session 'current-dir)
                   (haskell-session-get session 'cabal-dir)
                   (if (buffer-file-name)
                       (file-name-directory (buffer-file-name))
                     "~/"))))
             (haskell-session-get session 'current-dir))))

(defun haskell-process-change-dir (session process dir)
  "Change the directory of the current process."
  (haskell-process-queue-command
   process
   (make-haskell-command
    :state (list session process dir)
    :go
    (lambda (state)
      (haskell-process-send-string
       (cadr state) (format ":cd %s" (cl-caddr state))))

    :complete
    (lambda (state _)
      (haskell-session-set-current-dir (car state) (cl-caddr state))
      (haskell-interactive-mode-echo (car state)
                                     (format "Changed directory: %s"
                                             (cl-caddr state)))))))

;;;###autoload
(defun haskell-process-cabal-macros ()
  "Send the cabal macros string."
  (interactive)
  (haskell-process-queue-without-filters (haskell-interactive-process)
                                         ":set -optP-include -optPdist/build/autogen/cabal_macros.h"))

(defun haskell-process-do-try-info (sym)
  "Get info of `sym' and echo in the minibuffer."
  (let ((process (haskell-interactive-process)))
    (haskell-process-queue-command
     process
     (make-haskell-command
      :state (cons process sym)
      :go (lambda (state)
            (haskell-process-send-string
             (car state)
             (if (string-match "^[A-Za-z_]" (cdr state))
                 (format ":info %s" (cdr state))
               (format ":info (%s)" (cdr state)))))
      :complete (lambda (state response)
                  (unless (or (string-match "^Top level" response)
                              (string-match "^<interactive>" response))
                    (haskell-mode-message-line response)))))))

(defun haskell-process-do-try-type (sym)
  "Get type of `sym' and echo in the minibuffer."
  (let ((process (haskell-interactive-process)))
    (haskell-process-queue-command
     process
     (make-haskell-command
      :state (cons process sym)
      :go (lambda (state)
            (haskell-process-send-string
             (car state)
             (if (string-match "^[A-Za-z_]" (cdr state))
                 (format ":type %s" (cdr state))
               (format ":type (%s)" (cdr state)))))
      :complete (lambda (state response)
                  (unless (or (string-match "^Top level" response)
                              (string-match "^<interactive>" response))
                    (haskell-mode-message-line response)))))))

;;;###autoload
(defun haskell-mode-show-type-at (&optional insert-value)
  "Show the type of the thing at point."
  (interactive "P")
  (let ((ty (haskell-mode-type-at))
        (orig (point)))
    (if insert-value
        (let ((ident-pos (haskell-ident-pos-at-point)))
          (cond
           ((region-active-p)
            (delete-region (region-beginning)
                           (region-end))
            (insert "(" ty ")")
            (goto-char (1+ orig)))
           ((= (line-beginning-position) (car ident-pos))
            (goto-char (line-beginning-position))
            (insert (haskell-fontify-as-mode ty 'haskell-mode)
                    "\n"))
           (t
            (save-excursion
              (let ((col (save-excursion (goto-char (car ident-pos))
                                         (current-column))))
                (save-excursion (insert "\n")
                                (indent-to col))
                (insert (haskell-fontify-as-mode ty 'haskell-mode)))))))
      (message "%s" (haskell-fontify-as-mode ty 'haskell-mode)))))

;;;###autoload
(defun haskell-process-generate-tags (&optional and-then-find-this-tag)
  "Regenerate the TAGS table."
  (interactive)
  (let ((process (haskell-interactive-process)))
    (haskell-process-queue-command
     process
     (make-haskell-command
      :state (cons process and-then-find-this-tag)
      :go (lambda (state)
            (if (eq system-type 'windows-nt)
                (haskell-process-send-string
                 (car state)
                 (format ":!powershell -Command \"& { cd %s ; hasktags -e -x (ls -fi *.hs *.lhs *.hsc -exclude \\\"#*#\\\" -name -r) ; exit }\""
                         (haskell-session-cabal-dir
                          (haskell-process-session (car state)))))
              (haskell-process-send-string
               (car state)
               (format ":!cd %s && %s | %s"
                       (haskell-session-cabal-dir
                        (haskell-process-session (car state)))
                       "find . -name '*.hs' -print0 -or -name '*.lhs' -print0 -or -name '*.hsc' -print0"
                       "xargs -0 hasktags -e -x"))))
      :complete (lambda (state response)
                  (when (cdr state)
                    (let ((tags-file-name
                           (haskell-session-tags-filename
                            (haskell-process-session (car state)))))
                      (find-tag (cdr state))))
                  (haskell-mode-message-line "Tags generated."))))))

(defun haskell-process-add-cabal-autogen ()
  "Add <cabal-project-dir>/dist/build/autogen/ to the ghci search
path. This allows modules such as 'Path_...', generated by cabal,
to be loaded by ghci."
  (unless (eq 'cabal-repl (haskell-process-type)) ;; redundant with "cabal repl"
    (let*
        ((session       (haskell-interactive-session))
         (cabal-dir     (haskell-session-cabal-dir session))
         (ghci-gen-dir  (format "%sdist/build/autogen/" cabal-dir)))
      (haskell-process-queue-without-filters
       (haskell-interactive-process)
       (format ":set -i%s" ghci-gen-dir)))))

;;;###autoload
(defun haskell-process-unignore ()
  "Unignore any files that were specified as being ignored by the
  inferior GHCi process."
  (interactive)
  (let ((session (haskell-interactive-session))
        (changed nil))
    (if (null (haskell-session-get session
                                   'ignored-files))
        (message "Nothing to unignore!")
      (cl-loop for file in (haskell-session-get session
                                                'ignored-files)
               do (cl-case (read-event
                            (propertize (format "Set permissions? %s (y, n, v: stop and view file)"
                                                file)
                                        'face 'minibuffer-prompt))
                    (?y
                     (haskell-process-unignore-file session file)
                     (setq changed t))
                    (?v
                     (find-file file)
                     (cl-return))))
      (when (and changed
                 (y-or-n-p "Restart GHCi process now? "))
        (haskell-process-restart)))))

;;;###autoload
(defun haskell-session-change-target (target)
  "Set the build target for cabal repl"
  (interactive "sNew build target:")
  (let* ((session haskell-session)
         (old-target (haskell-session-get session 'target)))
    (when session
      (haskell-session-set-target session target)
      (when (and (not (string= old-target target))
                 (y-or-n-p "Target changed, restart haskell process?"))
        (haskell-process-start session)))))

;;;###autoload
(defun haskell-mode-stylish-buffer ()
  "Apply stylish-haskell to the current buffer."
  (interactive)
  (let ((column (current-column))
        (line (line-number-at-pos)))
    (haskell-mode-buffer-apply-command "stylish-haskell")
    (goto-char (point-min))
    (forward-line (1- line))
    (goto-char (+ column (point)))))

(defun haskell-mode-buffer-apply-command (cmd)
  "Execute shell command CMD with current buffer as input and
replace the whole buffer with the output. If CMD fails the buffer
remains unchanged."
  (set-buffer-modified-p t)
  (let* ((chomp (lambda (str)
                  (while (string-match "\\`\n+\\|^\\s-+\\|\\s-+$\\|\n+\\'" str)
                    (setq str (replace-match "" t t str)))
                  str))
         (errout (lambda (fmt &rest args)
                   (let* ((warning-fill-prefix "    "))
                     (display-warning cmd (apply 'format fmt args) :warning))))
         (filename (buffer-file-name (current-buffer)))
         (cmd-prefix (replace-regexp-in-string " .*" "" cmd))
         (tmp-file (make-temp-file cmd-prefix))
         (err-file (make-temp-file cmd-prefix))
         (default-directory (if (and (boundp 'haskell-session)
                                     haskell-session)
                                (haskell-session-cabal-dir haskell-session)
                              default-directory))
         (errcode (with-temp-file tmp-file
                    (call-process cmd filename
                                  (list (current-buffer) err-file) nil)))
         (stderr-output
          (with-temp-buffer
            (insert-file-contents err-file)
            (funcall chomp (buffer-substring-no-properties (point-min) (point-max)))))
         (stdout-output
          (with-temp-buffer
            (insert-file-contents tmp-file)
            (buffer-substring-no-properties (point-min) (point-max)))))
    (if (string= "" stderr-output)
        (if (string= "" stdout-output)
            (funcall errout
                     "Error: %s produced no output, leaving buffer alone" cmd)
          (save-restriction
            (widen)
            ;; command successful, insert file with replacement to preserve
            ;; markers.
            (insert-file-contents tmp-file nil nil nil t)))
      ;; non-null stderr, command must have failed
      (funcall errout "%s failed: %s" cmd stderr-output))
    (delete-file tmp-file)
    (delete-file err-file)))

;;;###autoload
(defun haskell-mode-find-uses ()
  "Find uses of the identifier at point, highlight them all."
  (interactive)
  (let ((spans (haskell-mode-uses-at)))
    (unless (null spans)
      (highlight-uses-mode 1)
      (cl-loop for span in spans
               do (haskell-mode-make-use-highlight span)))))

(defun haskell-mode-make-use-highlight (span)
  "Make a highlight overlay at the given span."
  (save-window-excursion
    (save-excursion
      (haskell-mode-goto-span span)
      (save-excursion
        (highlight-uses-mode-highlight
         (progn
           (goto-char (point-min))
           (forward-line (1- (plist-get span :start-line)))
           (forward-char (plist-get span :start-col))
           (point))
         (progn
           (goto-char (point-min))
           (forward-line (1- (plist-get span :end-line)))
           (forward-char (plist-get span :end-col))
           (point)))))))

(defun haskell-mode-uses-at ()
  "Get the locations of uses for the ident at point. Requires
the :uses command from GHCi."
  (let ((pos (or (when (region-active-p)
                   (cons (region-beginning)
                         (region-end)))
                 (haskell-ident-pos-at-point)
                 (cons (point)
                       (point)))))
    (when pos
      (let ((reply (haskell-process-queue-sync-request
                    (haskell-interactive-process)
                    (save-excursion
                      (format ":uses %s %d %d %d %d %s"
                              (buffer-file-name)
                              (progn (goto-char (car pos))
                                     (line-number-at-pos))
                              (1+ (current-column)) ;; GHC uses 1-based columns.
                              (progn (goto-char (cdr pos))
                                     (line-number-at-pos))
                              (1+ (current-column)) ;; GHC uses 1-based columns.
                              (buffer-substring-no-properties (car pos)
                                                              (cdr pos)))))))
        (if reply
            (let ((lines (split-string reply "\n" t)))
              (cl-remove-if
               #'null
               (mapcar (lambda (line)
                         (if (string-match "\\(.*?\\):(\\([0-9]+\\),\\([0-9]+\\))-(\\([0-9]+\\),\\([0-9]+\\))"
                                           line)
                             (list :path (match-string 1 line)
                                   :start-line (string-to-number (match-string 2 line))
                                   ;; ;; GHC uses 1-based columns.
                                   :start-col (1- (string-to-number (match-string 3 line)))
                                   :end-line (string-to-number (match-string 4 line))
                                   ;; GHC uses 1-based columns.
                                   :end-col (1- (string-to-number (match-string 5 line))))
                           (error (propertize line 'face 'compilation-error))))
                       lines)))
          (error (propertize "No reply. Is :uses supported?"
                             'face 'compilation-error)))))))

(provide 'haskell-commands)
