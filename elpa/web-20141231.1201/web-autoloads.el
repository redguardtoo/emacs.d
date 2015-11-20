;;; web-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (web-get web-json-post web-http-post web-http-get
;;;;;;  web-http-call) "web" "web.el" (21767 9140 325877 131000))
;;; Generated autoloads from web.el

(autoload 'web-http-call "web" "\
Make an HTTP method to the URL or the HOST, PORT, PATH and send DATA.

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
response before calling CALLBACK with all the data as a string.

\(fn METHOD CALLBACK &key URL (host \"localhost\") (port 80) SECURE (path \"/\") EXTRA-HEADERS DATA (mime-type web/request-mimetype) (mode (quote batch)) LOGGING)" nil nil)

(autoload 'web-http-get "web" "\
Make a GET calling CALLBACK with the result.

For information on URL or PATH, HOST, PORT and also EXTRA-HEADERS
and MODE see `web-http-call'.

The callback probably won't work unless you set `lexical-binding'
to `t'.

\(fn CALLBACK &key URL (host \"localhost\") (port 80) (path \"/\") EXTRA-HEADERS (mode (quote batch)) (logging t))" nil nil)

(autoload 'web-http-post "web" "\
Make a POST and call CALLBACK with the result.

For information on URL or PATH, HOST, PORT and also MODE see
`web-http-call'.

The callback probably won't work unless you set `lexical-binding'
to `t'.

\(fn CALLBACK &key URL (host \"localhost\") (port 80) (path \"/\") EXTRA-HEADERS DATA (mime-type web/request-mimetype) (mode (quote batch)) (logging t))" nil nil)

(autoload 'web-json-post "web" "\
POST DATA to URL expecting a JSON response sent to CALLBACK.

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
affecting the resulting lisp structure.

\(fn CALLBACK &key URL DATA HEADERS (mime-type web/request-mimetype) (logging t) (json-array-type json-array-type) (json-object-type json-object-type) (json-key-type json-key-type) (expectation-failure-callback (quote web-json-default-expectation-failure)))" nil nil)

(autoload 'web-get "web" "\
Get the specified URL into the BUFFER.

\(fn URL &optional BUFFER)" t nil)

;;;***

;;;### (autoloads nil nil ("web-pkg.el") (21767 9140 384702 138000))

;;;***

(provide 'web-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; web-autoloads.el ends here
