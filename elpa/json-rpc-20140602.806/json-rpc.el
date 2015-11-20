;;; json-rpc.el --- JSON-RPC library -*- lexical-binding: t; -*-

;; This is free and unencumbered software released into the public domain.

;; Author: Christopher Wellons <wellons@nullprogram.com>
;; URL: https://github.com/skeeto/elisp-json-rpc
;; Package-Version: 20140602.806
;; Version: 0.0.1
;; Package-Requires: ((emacs "24.1") (cl-lib "0.5"))

;;; Commentary:

;; The two important functions are `json-rpc-connect' and `json-rpc'.
;; The first one returns a connection object and the second one makes
;; synchronous requests on the connection, returning the result or
;; signaling an error.

;; Here's an example using the bitcoind JSON-RPC API:

;; (setf rpc (json-rpc-connect "localhost" 8332 "bitcoinrpc" "mypassword"))
;; (json-rpc rpc "getblockcount")  ; => 285031
;; (json-rpc rpc "setgenerate" t 3)

;; TODO:
;;  * asynchronous requests
;;  * response timeout
;;  * detect auth rejection

;;; Code:

(require 'cl-lib)
(require 'json)

(cl-defstruct (json-rpc (:constructor json-rpc--create))
  "A connection to a remote JSON-RPC server."
  process host port auth id-counter)

;; Set up error condition.
(setf (get 'json-rpc-error 'error-conditions) '(json-rpc-error error)
      (get 'json-rpc-error 'error-message) "JSON-RPC error condition")

(defun json-rpc-connect (host port &optional username password)
  "Create a JSON-RPC HTTP connection to HOST:PORT."
  (let ((auth (when (and username password)
                (base64-encode-string (format "%s:%s" username password))))
        (port-num (if (stringp port) (read port) port)))
    (json-rpc-ensure
     (json-rpc--create :host host :port port-num :auth auth :id-counter 0))))

(defun json-rpc-close (connection)
  "Close TCP connection in CONNECTION."
  (let ((process (json-rpc-process connection)))
    (when (and process (process-live-p process))
      (process-send-eof process))))

(defun json-rpc-ensure (connection)
  "Re-establish connection to CONNECTION if needed, returning CONNECTION."
  (let ((old-process (json-rpc-process connection)))
    (if (and old-process (process-live-p old-process))
        connection
      (let* ((buffer (generate-new-buffer " *json-rpc*"))
             (host (json-rpc-host connection))
             (process (make-network-process :name (format "json-rpc-%s" host)
                                            :buffer buffer
                                            :host host
                                            :service (json-rpc-port connection)
                                            :family 'ipv4
                                            :coding '(utf-8 . utf-8))))
        (setf (process-sentinel process)
              (lambda (proc _)
                (run-at-time 0 nil #'kill-buffer (process-buffer proc))))
        (prog1 connection
          (setf (json-rpc-process connection) process))))))

(defun json-rpc-live-p (connection)
  "Return non-nil if CONNECTION is still connected."
  (process-live-p (json-rpc-process connection)))

(defun json-rpc (connection method &rest params)
  "Send request of METHOD to CONNECTION, returning result or signalling error."
  (let* ((id (cl-incf (json-rpc-id-counter connection)))
         (vparams (vconcat params))
         (request `(:jsonrpc "2.0" :method ,method :params ,vparams :id ,id))
         (auth (json-rpc-auth connection))
         (process (json-rpc-process (json-rpc-ensure connection)))
         (encoded (json-encode request)))
    (with-current-buffer (process-buffer (json-rpc-process connection))
      (erase-buffer))
    (with-temp-buffer
      (insert "POST / HTTP/1.1\r\n")
      (when auth (insert "Authorization: Basic " auth "\r\n"))
      (insert (format "Content-Length: %d\r\n\r\n" (string-bytes encoded))
              encoded)
      (process-send-region process (point-min) (point-max)))
    (json-rpc-wait connection)))

(defun json-rpc--move-to-content ()
  "Move the point to after the headers."
  (setf (point) (point-min))
  (search-forward-regexp "\r?\n\r?\n" nil t))

(defun json-rpc--content-finished-p ()
  "Return non-nil if all of the content has arrived."
  (setf (point) (point-min))
  (when (search-forward "Content-Length: " nil t)
    (let ((length (read (current-buffer))))
      (and (json-rpc--move-to-content)
           (<= length (- (position-bytes (point-max))
                         (position-bytes (point))))))))

(defun json-rpc-wait (connection)
  "Wait for the response from CONNECTION and return it, or signal the error."
  (with-current-buffer (process-buffer (json-rpc-process connection))
    (cl-block nil
      (while t
        (when (or (json-rpc--content-finished-p)
                  (not (json-rpc-live-p connection)))
          (json-rpc--move-to-content)
          (let* ((json-object-type 'plist)
                 (json-key-type 'keyword)
                 (result (json-read)))
            (if (plist-get result :error)
                (signal 'json-rpc-error (plist-get result :error))
              (cl-return (plist-get result :result)))))
        (accept-process-output)))))

(defmacro json-rpc-with-connection (var-and-spec &rest body)
  "Open a temporary RPC connection, evaluate BODY, and close the connection.
The connection will close even if evaluation results in an error.

    (json-rpc-with-connection (btc \"localhost\" 8332 \"bitcoinrpc\" \"pw\")
      (message \"bitcoind status: %d blocks, %f BTC\"
               (json-rpc btc \"getblockcount\")
               (json-rpc btc \"getbalance\")))"
  (declare (indent 1))
  (cl-destructuring-bind (var . spec) var-and-spec
    `(let ((,var (json-rpc-connect ,@spec)))
       (unwind-protect
           (progn ,@body)
         (json-rpc-close ,var)))))

(provide 'json-rpc)

;;; json-rpc.el ends here
