;;; web.el --- useful HTTP client -*- lexical-binding: t -*-

;; Copyright (C) 2012  Nic Ferrier

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;; Maintainer: Nic Ferrier <nferrier@ferrier.me.uk>
;; Created: 3 Aug 2012
;; Version: 0.5.2
;; Package-Version: 20141231.1201
;; Url: http://github.com/nicferrier/emacs-web
;; Keywords: lisp, http, hypermedia
;; Package-requires: ((dash "2.9.0")(s "1.5.0"))

;; This file is NOT part of GNU Emacs.

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
;; This is an HTTP client using lexical scope.  This makes coding with
;; callbacks easier than with `url'.  This package also provides a
;; streaming mode where the callback is continually called whenever
;; data arrives. This is particularly useful for chunked encoding
;; scenarios.

;; Examples:

;; GET-ing an HTTP page
;;
;; (web-http-get
;;  (lambda (con header data)
;;    (message "the page returned is: %s" data))
;;  :url "http://emacswiki.org/wiki/NicFerrier")

;; POST-ing to an HTTP app
;;
;; (web-http-post
;;  (lambda (con header data)
;;    (message "the data is: %S" data))
;;  :url "http://example.org/postplace/"
;;  :data '(("parameter1" . "data")
;;          ("parameter2" . "more data")))

;;; Code:

;; Style-note: This codes uses the Emacs style of:
;;
;;    web/private-function
;;
;; for private functions.

(eval-when-compile
  (require 'cl))
(require 'cl-lib)
(require 'url-parse)
(require 'json)
(require 'browse-url)
(require 'dash)
(require 'time-stamp)
(require 'rx)
(require 's)

(defconst web/request-mimetype
  'application/x-www-form-urlencoded
  "The default MIME type used for requests.")

(defconst web-multipart-mimetype
  'multipart/form-data
  "The MIME type used for multipart requests.")

(defun web-header-parse (data)
  "Parse an HTTP response header.

Each header line is stored in the hash with a symbol form of the
header name.

The status line is expected to be the first line of the data.
The status is stored in the header as well with the following
keys:

  status-version
  status-code
  status-string

which are stored as symbols the same as the normal header keys."
  (let* ((header-hash (make-hash-table :test 'equal))
         (header-lines (split-string data "\r\n"))
         (status-line (car header-lines)))
    (when (string-match
           "HTTP/\\([0-9.]+\\) \\([0-9]\\{3\\}\\)\\( \\(.*\\)\\)*"
           status-line)
      (puthash 'status-version (match-string 1 status-line) header-hash)
      (puthash 'status-code (match-string 2 status-line) header-hash)
      (puthash 'status-string
               (or (match-string 4 status-line) "")
               header-hash))
    (cl-loop for line in (cdr header-lines)
       if (string-match
           "^\\([A-Za-z0-9.-]+\\):[ ]*\\(.*\\)"
           line)
       do
         (let ((name (intern (downcase (match-string 1 line))))
               (value (match-string 2 line)))
           (puthash name value header-hash)))
    header-hash))

(defun web/chunked-decode-stream (con data consumer)
  "Decode the chunked encoding stream on the process CON.

DATA is a lump of data from the stream, as passed from a filter
function for example.

CONSUMER is a function that will be called with the resulting
data like:

  CON CHUNK

the CON is the same as the CON in this call.  The `chunk' is the
chunk that has been read.  Only complete chunks are sent to the
CONSUMER.

When the chunked stream ends the CONSUMER is called with CHUNK
being `:done'.  This can be used to do clean up.  It is NOT
expected that the callback will have to clean up the CON, that
should be done by the caller.

CON is used to store state with the process property
`:chunked-encoding-buffer' being used as a buffer."
  ;; Make data the whole chunk
  (setq data (let ((saved (process-get con :chunked-encoding-buffer)))
               (if saved (concat saved data) data)))
  (if (not (string-match "^\\([0-9A-Fa-f]+\\)\r\n" data))
      (process-put con :chunked-encoding-buffer data)
      ;; We have identified a chunk
      (let* ((chunk-num (match-string 1 data))
             (chunk-size (string-to-number chunk-num 16))
             (toread-pos (+ 2 (length chunk-num))) ; +2 == \r\n after chunk sz
             (chunk-end (+ toread-pos chunk-size)))
        (if (< (length data) (+ 2 chunk-end)) ; +2 == \r\n at end of chunk
            (process-put con :chunked-encoding-buffer data)
            (let ((toread (substring data toread-pos chunk-end))
                  (trailing (substring data chunk-end (+ chunk-end 2)))
                  (left (substring data (+ chunk-end 2))))
              (if trailing
                  (assert (equal trailing "\r\n") t))
              (cond
                ((equal 0 chunk-size)
                 ;; Finished
                 (funcall consumer con :done)
                 :done)
                ((> chunk-size (length toread))
                 (process-put con :chunked-encoding-buffer data))
                (t
                 ;; Eat the data
                 (funcall consumer con toread)
                 ;; Clear the buffer
                 (process-put con :chunked-encoding-buffer "")
                 ;; Go round again if we need to
                 (if left
                     (web/chunked-decode-stream
                      con left consumer)))))))))

(defun web/cleanup-process (proc)
  "Kill the buffer and clean the process."
  (let ((buf (process-buffer proc)))
    (delete-process proc)
    (kill-buffer buf)))


(defconst web-cookie-jar-file
  (expand-file-name "web-cookies" user-emacs-directory)
  "The location of the cookie jar file.

Override this with dynamic scope if you need to use a specific
file.")

(defun web/cookie-split (cookie-header)
  (when (string-match "\\([^=]+\\)=\\(.*\\)" cookie-header)
    (let* ((name (match-string 1 cookie-header))
           (cookie-str (match-string 2 cookie-header))
           (parts (s-split ";" cookie-str))
           (value (car parts))
           (args (--keep (s-split "=" (s-trim it) t) (cdr parts))))
      (list name value args))))

(defun web/cookie-handler (con hdr)
  "Maintains a cookie jar.

Cookies are written to file \"web-cookie-jar-file\" in a JSON
format but prefixed by the url that caused the cookie to be set."
  (save-match-data
    (let ((cookie-hdr (gethash 'set-cookie hdr)))
      (when (string-match "\\([^=]+\\)=\\(.*\\)" cookie-hdr)
        (let* ((name (match-string 1 cookie-hdr))
               (cookie-str (match-string 2 cookie-hdr))
               (parts (s-split ";" cookie-str))
               (value (car parts))
               (args (--keep (s-split "=" (s-trim it) t) (cdr parts))))
          (condition-case err
              (when web-cookie-jar-file
                (with-current-buffer (find-file-noselect web-cookie-jar-file)
                  (goto-char (point-min))
                  (let ((url (process-get con :web-url))
                        (json (json-encode `(,name ,value ,args))))
                    (save-match-data
                      (if (re-search-forward
                           (rx-to-string `(and bol ,url " " (group-n 1 (* anything))))
                           nil t)
                          (replace-match json nil t nil 1)
                          (goto-char (point-max))
                          (insert url " " json "\n"))))
                  (write-file (buffer-file-name))))
            (error (message
                    "web/cookie-handler: '%s' writing cookies to '%s'"
                    err web-cookie-jar-file))))))))

(defun web/chunked-filter (callback con mode header data)
  "Filter for the client when we're doing chunking."
  (cond
    ((eq mode 'stream)
     (funcall callback con header data)
     (when (eq data :done)
       (web/cleanup-process con)))
    ((and (eq mode 'batch)
          (eq data :done))
     (funcall callback con header (process-get con :web-buffer))
     (web/cleanup-process con))
    (t
     (process-put
      con :web-buffer
      (concat (or (process-get con :web-buffer) "")
              data)))))

(defun web/content-length-filter (callback con mode header data)
  "Does the content-length filtering."
  (let ((content-len (string-to-number (gethash 'content-length header))))
    (if (eq mode 'batch)
        (let ((so-far (concat (process-get con :web-buffer) data)))
          (if (> content-len (length so-far))
              (process-put con :web-buffer so-far)
              ;; We have all the data, callback and then kill the process
              (unwind-protect
                   (funcall callback con header so-far)
                (web/cleanup-process con))))
        ;; Else we're in stream mode so deliver the bits
        (let ((collected (+ (or (process-get con :web-len) 0)
                            (length data))))
          (if (> content-len collected)
              (progn
                (process-put con :web-len collected)
                (funcall callback con header data))
              ;; Else we're done
              (funcall callback con header data)
              (funcall callback con header :done)
              (web/cleanup-process con))))))

(defun web/http-post-filter (con data callback mode)
  "Filter function for HTTP POST.

Not actually a filter function because it also receives the
CALLBACK and the MODE from the actual filter function, a lexical
closure inside `web-http-post'.

CALLBACK is a user supplied function handling the return from the
HTTP server.

MODE comes from the `web-http-post' call.  This function
handles the MODE by either streaming the data to the CALLBACK or
by collecting it and then batching it to the CALLBACK."
  (with-current-buffer (process-buffer con)
    (let ((header (process-get con :http-header)))
      (if (not header)
          (save-excursion
            (goto-char (point-max))
            (insert data)
            ;; Find the header if we don't have it
            (if (and (not header)
                     (progn
                       (goto-char (point-min))
                       (re-search-forward "\r\n\r\n" nil t)))
                (let ((hdr (web-header-parse
                            (buffer-substring (point-min) (point-max))))
                      ;; From the point of the end of header to the end
                      ;; is the data we need... this may be nothing.
                      (part-data (if (> (point-max) (point))
                                     (buffer-substring (point) (point-max))
                                     nil)))
                  (process-put con :http-header-pos (point))
                  (process-put con :http-header hdr)
                  ;; If we have more data call ourselves to process it
                  (when part-data
                    (web/http-post-filter con part-data callback mode)))))
          ;; Else we have the header, read the body and call callback
          ;; FIXME - we could do cookie handling here... and auto redirect 
          (cond
            ((equal "chunked" (gethash 'transfer-encoding header))
             (web/chunked-decode-stream
              con data
              ;; FIXME we still need the callback to know if this is completion
              (lambda (con data)
                (web/chunked-filter callback con mode header data))))
            ;; We have a content-length header so just buffer that much data
            ((gethash 'content-length header)
             (web/content-length-filter callback con mode header data)))))))

(defun web/key-value-encode (key value)
  "Encode a KEY and VALUE for url encoding."
  (cond
    ((or
      (numberp value)
      (stringp value))
     (format
      "%s=%s"
      (url-hexify-string (format "%s" key))
      (url-hexify-string (format "%s" value))))
    (t
     (format "%s" (url-hexify-string (format "%s" key))))))

(defun web-to-query-string (object)
  "Convert OBJECT (a hash-table or alist) to an HTTP query string.

If OBJECT is of type `hash-table' then the keys and values of the
hash are iterated into the string depending on their types.

Keys with `number' and `string' values are encoded as
\"key=value\" in the resulting query.

Keys with a boolean value (or any other value not already
described) are encoded just as \"key\".

Keys may be symbols or strings."
  (mapconcat
   (lambda (pair)
     (web/key-value-encode (car pair) (cdr pair)))
   (cond
     ((hash-table-p object)
      (let (result)
        (maphash
         (lambda (key value)
           (setq result (append (list (cons key value)) result)))
         object)
        (reverse result)))
     ((listp object)
      object))
   "&"))


;; What a multipart body looks like
;; Content-type: multipart/form-data, boundary=AaB03x
;;
;; --AaB03x
;; content-disposition: form-data; name="field1"
;;
;; Joe Blow
;; --AaB03x
;; content-disposition: form-data; name="pics"; filename="file1.txt"
;; Content-Type: text/plain
;;
;;  ... contents of file1.txt ...
;; --AaB03x--

(defun web/to-multipart-boundary ()
  "Make a boundary marker."
  (sha1 (format "%s%s" (random) (time-stamp-string))))

(defun web/is-file (kv)
  (let ((b (cdr kv)))
    (and (bufferp b) (buffer-file-name b) b)))

(defun web-to-multipart (data)
  "Convert DATA, an ALIST or Hashtable, into a Multipart body.

Returns a string of the multipart body propertized with
`:boundary' with a value of the boundary string."
  (let* ((boundary (web/to-multipart-boundary))
         (parts (mapconcat  ; first the params ...
                 (lambda (kv)
                   (let ((name (car kv))
                         (value (cdr kv)))
                     (format "--%s\r
Content-Disposition: form-data; name=\"%s\"\r\n\r\n%s"
                             boundary name value)))
                 (-filter (lambda (kv) (not (web/is-file kv))) data) "\r\n"))
         (files (mapconcat  ; then the files ...
                 (lambda (kv)
                   (let* ((name (car kv))
                          (buffer (cdr kv))
                          (filename (buffer-file-name buffer))
                          (mime-enc (or
                                     (mm-default-file-encoding filename)
                                     "text/plain")))
                     (format "--%s\r
Content-Transfer-Encoding: BASE64\r
Content-Disposition: form-data; name=\"%s\"; filename=\"%s\"\r
Content-Type: %s\r\n\r\n%s"
                             boundary name (file-name-nondirectory filename) mime-enc
                             ;; FIXME - We should base64 the content when appropriate
                             (base64-encode-string
                              (apply
                               'encode-coding-string
                               (with-current-buffer buffer
                                 (list (buffer-string) buffer-file-coding-system)))))))
                 (-filter 'web/is-file data) "\r\n")))
    (propertize
     (format "%s%s--%s--\r\n" 
             (if (and parts (not (equal parts ""))) (concat parts "\r\n") "")
             (if (and files (not (equal files ""))) (concat files "\r\n") "")
             boundary)
     :boundary boundary)))

(defvar web-log-info nil
  "Whether to log info messages, specifically from the sentinel.")

(defun web/http-post-sentinel (con evt)
  "Sentinel for the HTTP POST."
  ;; FIXME I'm sure this needs to be different - but how? it needs to
  ;; communicate to the filter function?
  (cond
    ((equal evt "closed\n")
     (when web-log-info
       (message "web/http-post-sentinel http client post closed")))
    ((equal evt "deleted\n")
     (delete-process con)
     (when web-log-info
       (message "web/http-post-sentinel http client post deleted")))
    ((equal evt "connection broken by peer\n")
     (when web-log-info
       (message "web/http-post-sentinel http client broken")))
    (t
     (when web-log-info
       (message "web/http-post-sentinel unexpected evt: %s" evt)))))

(defun web/http-post-sentinel-with-logging (con evt logging)
  "Map a logging variable into the sentinel."
  (let ((web-log-info logging))
    (web/http-post-sentinel con evt)))

(defun web/header-list (headers)
  "Convert HEADERS (hash-table or alist) into a header list."
  (cl-labels
      ((hdr (key val)
         (format "%s: %s\r\n" key val)))
    (cond
      ((hash-table-p headers)
       (let (res)
         (maphash
          (lambda (key val)
            (setq res (append (list (hdr key val)) res)))
          headers)
         res))
      ((listp headers)
       (mapcar
        (lambda (pair) (hdr (car pair)(cdr pair)))
        headers)))))

(defun web/header-string (method headers mime-type to-send)
  "Return a string of all the HEADERS formatted for a request.

Content-Type and Content-Length are both computed automatically.

METHOD specifies the usual HTTP method and therefore whether
there might be a Content-Type on the request body.

MIME-TYPE specifies the MIME-TYPE of any TO-SEND.

TO-SEND is any request body that needs to be sent.  TO-SEND may
be propertized with a multipart boundary marker which needs to be
set on the Content-Type header."
  (let ((http-hdrs (web/header-list headers))
        (boundary (and to-send
                       (plist-get (text-properties-at 0 to-send) :boundary))))
    (when (member method '("POST" "PUT"))
      (when (> (length to-send) 1)
        (push (format
               "Content-type: %s%s\r\n" mime-type
               (if boundary (format "; boundary=%s" boundary) ""))
         http-hdrs)))
    (when (and to-send (> (length to-send) 0))
      (push
       (format "Content-length: %d\r\n" (length to-send))
       http-hdrs))
    (cl-loop for hdr in http-hdrs if hdr concat hdr)))

(defun web/log (log)
  (when log
    (with-current-buffer (get-buffer-create "*web-log*")
      (save-excursion
        (goto-char (point-max))
        (insert "web-http ")
        (insert (format "%s" log))
        (insert "\n")))))

;;;###autoload
(cl-defun web-http-call (method
                         callback
                         &key
                         url
                         (host "localhost")
                         (port 80)
                         secure
                         (path "/")
                         extra-headers
                         data
                         (mime-type web/request-mimetype)
                         (mode 'batch)
                         logging)
  "Make an HTTP method to the URL or the HOST, PORT, PATH and send DATA.

If URL is specified then it takes precedence over SECURE, HOST,
PORT and PATH.  URL may be HTTP or HTTPS.

Important note: any query in URL is currently IGNORED!

SECURE is `nil' by default but if `t' then SSL is used.

PORT is 80 by default.  Even if SECURE it `t'.  If you manually
specify SECURE you should manually specify PORT to be 443.  Using
URL negates the need for that, an SSL URL will work correctly.

The URL connected to (whether specified by URL or by the HOST and
PORT) is recorded on the resulting connection as the process
property `:web-url'.

EXTRA-HEADERS is an alist or a hash-table of extra headers to
send to the server.

The full set of headers sent to the server is recorded on the
connection with the process property `:web-headers'.

DATA is of MIME-TYPE.  We try to interpret DATA and MIME-TYPE
usefully:

If MIME-TYPE is `application/form-www-url-encoded' then
`web-to-query-string' is used to to format the DATA into a POST
body.

If MIME-TYPE is `multipart/form-data' then `web-to-multipart' is
called to get a POST body.

Any data sent to the server is recorded on the connection with
the process property `:web-sent'.

When the request comes back the CALLBACK is called.  CALLBACK is
always passed 3 arguments: the HTTP connection which is a process
object, the HTTP header which is a `hash-table' and `data', which
is normally a string.  `data' depends somewhat on the context.
See below.

MODE defines what it means for the request to cause the CALLBACK
to be fired.  When MODE is `stream' then the CALLBACK is called
for every chunk of data received after the header has arrived.
This allows streaming data to somewhere else; hence `stream'
mode.  In this mode CALLBACK's `data' argument is a single chunk
of the stream or `:done' when the stream ends.

The default MODE is `batch' which collects all the data from the
response before calling CALLBACK with all the data as a string."
  (when logging (web/log url))
  (let* ((mode (or mode 'batch))
         (parsed-url (url-generic-parse-url
                      (if url url
                          (format "%s://%s:%d%s"
                                  (if secure "https" "http")
                                  host port path))))
         (host (progn
                 (assert
                  (or (equal (url-type parsed-url) "http")
                      (equal (url-type parsed-url) "https"))
                  t "The url scheme must be http")
                 (url-host parsed-url)))
         (port (url-port parsed-url))
         (path (let ((pth (url-filename parsed-url)))
                 (if (equal pth "") "/" pth)))
         (dest (format "%s:%s%s" host port path))
         (buf (generate-new-buffer dest))
         (con (open-network-stream
               (format "web-http-post-%s" dest)
               buf host port
               :type (cond
                      ((equal (url-type parsed-url) "http") 'plain)
                      ((equal (url-type parsed-url) "https") 'tls)))))
    ;; We must use this coding system or the web dies
    (set-process-coding-system con 'raw-text-unix 'raw-text-unix)
    (set-process-sentinel con (lambda (con evt)
                                (web/http-post-sentinel-with-logging
                                 con evt logging)))
    (set-process-filter
     con
     (lambda (con data)
       (let ((mode mode)
             (cb callback))
         (web/http-post-filter con data cb mode))))
    ;; Send the request
    (let*
        ((sym-mt (if (symbolp mime-type) mime-type (intern mime-type)))
         (to-send (case sym-mt
                    ('multipart/form-data
                     (web-to-multipart data))
                    ('application/x-www-form-urlencoded
                     (web-to-query-string data))
                    ;; By default just have the data
                    (t data)))
         (headers (or (web/header-string
                       method extra-headers mime-type to-send)
                      ""))
         (submission
          (format
           "%s %s HTTP/1.1\r\nHost: %s\r\n%s\r\n%s"
           method path host
           headers
           (if to-send to-send ""))))
      ;; Set some data on the connection process so users will be able to find data
      (process-put con :web-url (format "http://%s" dest))
      (process-put con :web-headers headers)
      (process-put con :web-sent to-send)
      (when logging (web/log submission))
      (process-send-string con submission))
    con))

;;;###autoload
(cl-defun web-http-get (callback
                      &key
                      url
                      (host "localhost")
                      (port 80)
                      (path "/")
                      extra-headers
                      (mode 'batch)
                      (logging t))
  "Make a GET calling CALLBACK with the result.

For information on URL or PATH, HOST, PORT and also EXTRA-HEADERS
and MODE see `web-http-call'.

The callback probably won't work unless you set `lexical-binding'
to `t'."
  (web-http-call
   "GET"
   callback
   :url url
   :host host
   :port port
   :path path
   :extra-headers extra-headers
   :mode mode
   :logging logging))

;;;###autoload
(cl-defun web-http-post (callback
                       &key
                       url
                       (host "localhost")
                       (port 80)
                       (path "/")
                       extra-headers
                       data
                       (mime-type web/request-mimetype)
                       (mode 'batch)
                       (logging t))
  "Make a POST and call CALLBACK with the result.

For information on URL or PATH, HOST, PORT and also MODE see
`web-http-call'.

The callback probably won't work unless you set `lexical-binding'
to `t'."
  (web-http-call
   "POST"
   callback
   :url url
   :host host
   :port port
   :path path
   :extra-headers extra-headers
   :data data
   :mime-type mime-type
   :logging logging
   :mode mode))

(defvar web-json-expected-mimetypes-list
  '("application/json"
    "application/x-javascript"
    "text/javascript"
    "text/x-javascript"
    "text/x-json")
  "List of mimetypes that we use to accept JSON.")

(defun web-json-default-expectation-failure (data http-con headers)
  "Default expectation callback for JSON expectation errors."
  (error "web-json failed to read %S as json with %s and %s"
         data http-con headers))

(cl-defun web/json-parse (json-candidate-data
                          &key
                          (json-array-type json-array-type)
                          (json-object-type json-object-type)
                          (json-key-type json-key-type))
  "Parse DATA as JSON and return the result."
  (json-read-from-string json-candidate-data))

;;;###autoload
(cl-defun web-json-post (callback
                         &key
                         url data headers
                         (mime-type web/request-mimetype)
                         (logging t)
                         (json-array-type json-array-type)
                         (json-object-type json-object-type)
                         (json-key-type json-key-type)
                         (expectation-failure-callback
                          'web-json-default-expectation-failure))
  "POST DATA to URL expecting a JSON response sent to CALLBACK.

See `web-json-expected-mimetypes-list' for the list of Mime Types
we accept JSON for.  This may be let bound.  If the expectation
is not met then EXPECTATION-FAILURE-CALLBACK is called being
passed the CALLBACK parameters.  By default
EXPECTATION-FAILURE-CALLBACK is
`web-json-default-expectation-failure'.

The CALLBACK is called as:

  CALLBACK RESPONSE-DATA HTTPCON RESPONSE-HEADER

so the function may be defined like this:

  (lambda (data &rest stuff) ...)

HEADERS may be specified, these are treated as extra-headers to
be sent with the request.

The DATA is sent as `application/x-www-form-urlencoded' by
default, MIME-TYPE can change that.

JSON-ARRAY-TYPE, JSON-OBJECT-TYPE and JSON-KEY-TYPE, if present,
are used to let bind the `json-read' variables of the same name
affecting the resulting lisp structure."
  (let ((closed-json-array-type json-array-type)
        (closed-json-object-type json-object-type)
        (closed-json-key-type json-key-type))
    (web-http-post
     (lambda (httpcon header http-data)
       ;; Add a member test for the MIMETYPE expectation
       (let ((lisp-data
              (condition-case err
                  (web/json-parse
                   http-data
                   :json-array-type closed-json-array-type
                   :json-object-type closed-json-object-type
                   :json-key-type closed-json-key-type)
                (error
                 (when logging
                   (message "web-json-post expectation failure %S" err))
                 (funcall expectation-failure-callback
                          http-data httpcon header)))))
         (funcall callback lisp-data httpcon header)))
      :url url
      :data data
      :mime-type mime-type
      :extra-headers headers
      :logging logging)))

(defvar web-get-history-list nil
  "History for `web-get' interactive forms.")

;;;###autoload
(defun web-get (url &optional buffer)
  "Get the specified URL into the BUFFER."
  (interactive
   (list
    (let ((def-url (browse-url-url-at-point)))
      (read-from-minibuffer "URL: " def-url nil nil 'web-get-history-list))
    (when current-prefix-arg
        (read-buffer "Buffer: " '("*web-get*")))))
  (let ((handler
         (lambda (httpc header data)
           (with-current-buffer
               (if (bufferp buffer)
                   buffer
                   (if (stringp buffer)
                       (generate-new-buffer buffer)
                       (generate-new-buffer "*web-get*")))
             (goto-char (point-max))
             (insert data)
             (switch-to-buffer (current-buffer))))))
    (web-http-get handler :url url)))

(defun web-header (header name &optional convert)
  "Look up NAME in HEADER."
  (let ((val (if (hash-table-p header)
                 (let ((v (gethash (intern name) header)))
                   (when v (cons name v)))
                 ;; Else presume it's an alist
                 (assoc name header))))
    (when val
      (case convert
        (:num (string-to-number (cdr val)))
        (t val)))))


(provide 'web)

;;; web.el ends here
