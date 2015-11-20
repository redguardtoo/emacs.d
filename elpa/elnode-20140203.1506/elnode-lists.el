;;; elnode-lists.el - management tools for elnode

(require 'elnode)
(require 'tabulated-list)
(require 'noflet)

;;; Deferred queue list

;;;###autoload
(defun elnode-deferred-queue (arg)
  "Message the length of the deferred queue."
  (interactive "P")
  (if (not arg)
      (message
       "elnode deferred queue: %d %s"
       (length elnode--deferred)
       elnode--defer-timer)
    (setq elnode--deferred (list))
    (message "elnode deferred queue reset!")))

(defun elnode--list-deferreds ()
  "List the deferred servers."
  ;; TODO have the defer stuff put a better reference to the actual
  ;; handler onto the process?
  ;;
  ;; we could have the mapper add the mapped function to the process as well?
  ;;
  ;; into a list of mapped functions on this process?
  (loop for (proc . deferred-closure) in elnode--deferred
     collect
       (list
        proc
        (let ((pl (process-plist proc)))
          (vector (apply 'format "%s:%S" (process-contact proc))
                  (apply
                   'format "%s.%s.%s.%s.:%s"
                   (mapcar 'identity (process-contact proc :local)))
                  (symbol-name (plist-get pl :elnode-http-handler))
                  (plist-get pl :elnode-http-resource))))))

(define-derived-mode
    elnode-deferred-list-mode tabulated-list-mode "Elnode defered queue list"
    "Major mode for listing the currently deferred Elnode handlers."
    (setq tabulated-list-entries 'elnode--list-deferreds)
    (setq tabulated-list-format
          [("Address" 15 nil)
           ("Local server" 15 nil)
           ("Handler function" 20 nil)
           ("Resource" 30 nil)])
    (tabulated-list-init-header))

;;;###autoload
(defun elnode-deferred-list (&optional prefix)
  "List the currently deferred Elnode handlers."
  (interactive "P")
  (with-current-buffer (get-buffer-create "*elnode deferreds*")
    (elnode-deferred-list-mode)
    (tabulated-list-print)
    (if prefix
        (switch-to-buffer-other-window (current-buffer))
        (switch-to-buffer (current-buffer)))))

;;;###autoload
(defalias 'list-elnode-deferreds 'elnode-deferred-list)

;;; Server list

(defun elnode--list-servers ()
  "List the current Elnode servers for `elnode-list-mode'."
  (noflet ((closurep (v)
           (and (functionp v) (listp v) (eq (car v) 'closure))))
    (loop for (port . socket-proc) in elnode-server-socket
       collect
         (list
          port
          (let* ((fn (process-get socket-proc :elnode-http-handler))
                 (doc (when (functionp fn)
                        (documentation fn))))
            (vector
             (format "%s" port)
             (cond
               ((closurep fn) (format "%S" fn))
               ((byte-code-function-p fn) (format "byte-code"))
               ((and (listp fn)(eq (car fn) 'lambda)) (format "lambda"))
               (t (symbol-name fn)))
             (or (if (and doc (string-match "^\\([^\n]+\\)" doc))
                     (match-string 1 doc)
                     "no documentation."))))))))

(defun elnode-lists-server-find-handler ()
  "Find the handler mentioned in the handler list."
  (interactive)
  (let ((line
         (buffer-substring-no-properties
          (line-beginning-position)
          (line-end-position))))
    (when (string-match "^[0-9]+ +\\([^ ]+\\) .*" line)
      (let ((handler-name (intern (match-string 1 line))))
        (with-current-buffer
            (find-file
             (or (symbol-file handler-name)
                 (error "no such file")))
          (find-function handler-name))))))

(defun elnode-lists-kill-server ()
  (interactive)
  (goto-char (line-beginning-position))
  (re-search-forward "^\\([0-9]+\\)" (line-end-position) t)
  (let ((port (string-to-number (match-string 1))))
    (elnode-stop port)
    (let ((buffer-read-only nil))
      (erase-buffer)
      (tabulated-list-print))))

(define-derived-mode
    elnode-list-mode tabulated-list-mode "Elnode server list"
    "Major mode for listing Elnode servers currently running."
    (setq tabulated-list-entries 'elnode--list-servers)
    (define-key elnode-list-mode-map (kbd "\r")
      'elnode-lists-server-find-handler)
    (define-key elnode-list-mode-map (kbd "k")
      'elnode-lists-kill-server)
    (setq tabulated-list-format
          [("Port" 10 nil)
           ("Handler function" 40 nil)
           ("Documentation" 80 nil)])
    (tabulated-list-init-header))

;;;###autoload
(defun elnode-server-list (&optional prefix)
  "List the currently running Elnode servers."
  (interactive "P")
  (with-current-buffer (get-buffer-create "*elnode servers*")
    (elnode-list-mode)
    (tabulated-list-print)
    (if prefix
        (switch-to-buffer-other-window (current-buffer))
        (switch-to-buffer (current-buffer)))))

;;;###autoload
(defalias 'list-elnode-servers 'elnode-server-list)

(provide 'elnode-list)

;;; enlode-list.el ends here
