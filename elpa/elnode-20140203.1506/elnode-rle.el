;;; elnode-rle.el --- Remote Lisp Executiion with Elnode  -*- lexical-binding: t -*-

;; Copyright (C) 2012  Nic Ferrier

;; Author: Nic Ferrier
;; Keywords: lisp, hypermedia, processes

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This is an elnode handler and tools for doing asynchrous
;; programming.
;;
;; The idea is that you can setup associated child processes and pass
;; them work to do and receive their output over HTTP.

;;; Code:

(require 'elnode)
(require 'web)
(require 'loadhist)
(require 'server)

(defun elnode-rle--handler (httpcon)
  "Remote Lisp Evaluator handler.

This can be spawned in a client to allow any lisp code to be
passed over the client-server link."
  (let* ((lisp-to-run (elnode-http-param httpcon "lisp"))
         (lisp
          (if lisp-to-run
              (car (read-from-string lisp-to-run))))
         (bindings-to-use (elnode-http-param httpcon "bindings"))
         (bindings
          (if bindings-to-use
              (car (read-from-string bindings-to-use))))
         (to-eval (list 'let bindings lisp)))
    (elnode-http-start httpcon 200 '("Content-type" . "text/plain"))
    (let ((nomessage t))
      (with-stdout-to-elnode httpcon
          (eval to-eval)))))

(ert-deftest elnode-rle--handler ()
  "Test the Remote Lisp Evaluator handler."
  :expected-result :failed
  (flet ((lisp-encode (param lisp)
           (cons param (format "%S" lisp)))
         (do-test (lisp bindings)
           (fakir-mock-process
               :httpcon
               ((:elnode-http-params (list lisp bindings)))
             (elnode-rle--handler :httpcon)
             (with-current-buffer (process-buffer :httpcon)
               (goto-char (point-min))
               ;; Find the header end.
               (re-search-forward "\r\n\r\n" nil 't)
               (buffer-substring (point) (point-max))))))
      (should
       (equal
        ;; Match the content transfer encoded
        "c\r\nhello world!\r\n0\r\n\r\n"
        (let*
            ((lisp (lisp-encode
                    "lisp" '(let ((a "hello world!")) (princ a))))
             (bindings (lisp-encode
                        "bindings" '((a 10)(b 20)))))
          (do-test lisp bindings))))
      (should
       (equal
        "2\r\n30\r\n0\r\n\r\n"
        (let*
            ((lisp (lisp-encode
                    "lisp" '(let ((a (+ b 10))) (princ a))))
             (bindings (lisp-encode
                        "bindings" '((a 10)(b 20)))))
          (do-test lisp bindings))))))

(defvar elnode-rle--servers (make-hash-table :test 'equal)
  "The hash of RLE servers available.")

(defun elnode-rle--load-path-ize (lisp)
  "Wrap LISP in the current load-path."
  (concat
   ;; There is a very strange thing with sending lisp to
   ;; (read) over a piped stream... (read) can't cope with
   ;; multiple lines; so we encode newline here.
   ;;(replace-regexp-in-string
   ;; "\n"
   ;; "\\\\n"
   (format "(progn (setq load-path (quote %S)) %s)"
           (append (list default-directory) load-path)
           lisp)))

(defun elnode-rle--handler-lisp (to-require)
  "Return a file with Lisp to start Elnode with TO-REQUIRE.

Used to construct the lisp to send.  You're unlikely to need to
override this at all, the function is just here to make the
implementation easier to debug.

TO-REQUIRE is a list of things to require, currently only 1 is
allowed."
  (let ((temp-file
         (make-temp-file
          (format "elnode-rle-%s" (symbol-name to-require)))))
    (with-temp-file temp-file
      (insert
       (elnode-rle--load-path-ize
        (format "(progn
 (setq elnode-do-init nil)
 (setq elnode--do-error-logging nil)
 (require (quote %s))
 (require (quote elnode-rle))
 (toggle-debug-on-error)
 (setq elnode-rle-port (elnode-find-free-service))
 (elnode-start 'elnode-rle--handler :port elnode-rle-port)
 (print (format \"\\nelnode-port=%%d\\n\" port)))"
                to-require))))
    temp-file))

(defun elnode-rle--httpcon-mapper (client-header
                                   client-data
                                   elnode-httpcon
                                   &optional end-callback)
  "Elnode specific client connection to HTTP connection mapper.

Maps client async data responses to an elnode server response."
  (unless (process-get elnode-httpcon :elnode-rle-header-sent)
    (elnode-http-start
     elnode-httpcon
     (gethash 'status-code client-header))
    (process-put elnode-httpcon :elnode-rle-header-sent t))
  (if (eq client-data :done)
      (elnode-http-return elnode-httpcon) ; return if we're done
      ;; Else just send the data
      (elnode-http-send-string elnode-httpcon client-data)))

(defun elnode-rle--client-data-mapper (con header data stream end-callback)
  "Recevies data from the RLE server and sends it to the STREAM.

END-CALLBACK is to be called when the client sees EOF."
  (cond
    ((processp stream) ; this should really elnode-http-p
     (elnode-rle--httpcon-mapper header data stream end-callback))
    ((bufferp stream)
     (if (not (eq data :done))
         (with-current-buffer stream
           (save-excursion
             (goto-char (point-max))
             (insert data)))
         ;; Process is done.
         (and (functionp end-callback)
              (funcall end-callback header))))))

(defun elnode-rle--call-mapper (data-to-send stream port
                                &optional end-callback)
  "Make a client call to PORT mapping response to STREAM.

When it finishes, call END-CALLBACK, if present, with the header."
  (web-http-post
   (lambda (con header data)
     (elnode-rle--client-data-mapper
      con
      header
      data
      stream
      end-callback))
   "/"
   :host "localhost"
   :port port
   :data data-to-send
   :mime-type "application/x-elnode"
   :mode 'stream))

(defun elnode-rle--make-server (to-require)
  "Make an RLE server, a child Emacs running the RLE handler.

Return a proc that represents the child process.  The child
process has a property `:exec' which is a function that calls the
RLE handler in the child's Elnode server (waiting for the server
to start first and provide the relevant port) by calling
`elnode-rle-call-mapper' with the stream from the `:exec' call
and the child's remote HTTP port.

The `:exec' proc will signal `elnode-rle-child-port' if the child
server does not start properly."  ; yes. I know it's bloody complicated.
  (let* ((proc-buffer
          (get-buffer-create
           (format "* %s *" "thingy")))
         (emacsrun
          "/usr/bin/emacs -Q --daemon=elnode-debugit")
         (proc
          (start-process-shell-command
           "elnode-rle-server"
           proc-buffer
           emacsrun))
         (file-of-lisp
          (elnode-rle--handler-lisp
           to-require)))
    ;; Start elnode in it
    (server-eval-at "elnode-debugit" `(load-file ,file-of-lisp))
    (process-put proc :daemonhandle "elnode-debugit")
    (process-put
     proc
     :port
     (server-eval-at
      (process-get proc :daemonhandle)
      'elnode-rle-port))
    ;; Collect the port from the remote Emacs
    ;; - FIXME this should also collect the secure token
    (set-process-filter
     proc
     (lambda (proc data)
       ;; Optional delay for test reasons
       (with-current-buffer (process-buffer proc)
         (save-excursion
           (goto-char (point-max))
           (insert data)))))
    ;; Make a handler to call the server
    (process-put
     proc :exec
     (lambda (data stream &optional end-callback)
       (let ((ephemeral-port (process-get proc :port)))
         (elnode-rle--call-mapper data stream ephemeral-port end-callback))))
    proc))

(defun elnode-rle--sender (stream to-require bindings body
                           &optional end-callback)
  "Make a call using a client to the RLE server elsewhere.

The RLE server is reused over TO-REQUIRE, if it's not already
existing, it is created."
  (let ((server (gethash to-require elnode-rle--servers)))
    ;; Make the server if we don't have it
    (unless server
      (setq server
            (puthash to-require
                     (elnode-rle--make-server (car to-require))
                     elnode-rle--servers)))
    ;; Now make the call to the server
    (let ((data (make-hash-table :test 'equal)))
      (puthash "bindings" (format "%S" bindings) data)
      (puthash "lisp" (format "%S" body) data)
      (let ((client-connection
             (funcall
              (process-get server :exec)
              data
              stream
              end-callback)))
        ;; If we're streaming to elnode then we need to mark the connection
        (when (processp stream)
          (process-put
           stream
           :elnode-child-process
           client-connection))))))

(defvar elnode-rle--async-do-end-callback nil
  "Used by `elnode-async-do' as the source of an end-callback.

This is just used by tests for end signalling.")

(defmacro elnode-async-do (stream
                           requires requirements
                           with-environment bindings
                           do &rest body)
  "Execute the BODY in a remote Emacs.

The STREAM is used to handle any output.

The REQUIREMENTS is a list of provide symbol names that will be
used to establish the right environment in the remote.

The BINDINGS are also sent to the remote.

TODO

security for the remote using the stored key."
  (assert (eq with-environment 'with-environment))
  (assert (eq requires 'requires))
  (assert (eq do 'do))
  (let ((bodyv (make-symbol "body"))
        (bindsv (make-symbol "binds"))
        (streamv (make-symbol "streamv"))
        (requirev (make-symbol "providing")))
    `(let* ((,streamv ,stream)
            (,bodyv (quote (progn ,@body)))
            (,bindsv (list
                      ,@(loop for p in bindings
                           collect
                             (if (and p (listp p))
                                 (list 'list `(quote ,(car p)) (cadr p))
                                 (list 'cons `,p nil)))))
            (,requirev (quote ,requirements)))
       (elnode-rle--sender
        ,streamv ,requirev ,bindsv ,bodyv
        elnode-rle--async-do-end-callback))))

(defmacro with-elnode-rle-wait (&rest body)
  "Simplify the wait for RLE; for testers."
  `(unwind-protect
        (let (ended)
          (progn
            ,@body)
          (while (not ended) (sit-for 1)))
     ;; FIXME - can we get to the name of this?
     (server-eval-at "elnode-debugit" '(kill-emacs))))

(ert-deftest elnode-rle--make-server ()
  "Test making an RLE server.

Do it all 3 ways: directly with the `elnode-rle-make-server',
with the `elnode-rle--sender' function and finally with the user
facing macro `elnode-async-do'.

The output from the RLE call is collected in a buffer
and tested."
  :expected-result :failed
  (flet ((make-hash (bindings)
           (let ((h (make-hash-table :test 'equal)))
             (loop for b in bindings
                  do (puthash (car b) (cadr b) h))
             h)))
    ;; Do it RAW
    (should
     (equal
      "hello"
      (with-temp-buffer
        (let* ((child-proc (elnode-rle--make-server 'elnode))
               (daemon-handler (process-get child-proc :daemonhandle))
               (collect-buf (current-buffer)))
          (with-elnode-rle-wait
              (funcall
               (process-get child-proc :exec)
               (make-hash '(("bindings" "((a \"hello\"))")
                            ("lisp" "(princ \"hello\")")))
               (current-buffer)
               (lambda (hdr) ; the end proc
                 (setq ended t))))
          (buffer-substring (point-min) (point-max))))))
    ;; Do it via the sender func
    (should
     (equal
      "40"
      (with-temp-buffer
        (with-elnode-rle-wait
            (let ((elnode-rle--servers (make-hash-table :test 'equal)))
              (elnode-rle--sender
               (current-buffer)
               '(elnode)
               '((a 10) (b 20))
               '(let ((c 30))(princ (+ c a)))
               (lambda (header)
                 (message "elnode-rle: all done!")(setq ended t)))))
        (buffer-substring (point-min) (point-max)))))
    ;; Do it with the macro
    (should
     (equal
      "hello"
      (with-temp-buffer
        (with-elnode-rle-wait
            (let ((elnode-rle--servers (make-hash-table :test 'equal))
                  (elnode-rle--async-do-end-callback
                   (lambda (header)
                     (message "elnode-rle: in the dyn bound callback!")
                     (setq ended t))))
              (elnode-async-do
               (current-buffer)
               requires (elnode enode-rle)
               with-environment ((a 10)(b 20))
               do (princ "hello"))))
        (buffer-substring (point-min) (point-max)))))))

(provide 'elnode-rle)

;; elnode-rle ends here
