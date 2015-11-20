;;; elnode-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (elnode-do-init elnode-init elnode-webserver elnode-make-webserver
;;;;;;  elnode--webserver-handler-proc elnode-hostpath-default-table
;;;;;;  elnode-start elnode-app) "elnode" "elnode.el" (21767 9141
;;;;;;  897877 114000))
;;; Generated autoloads from elnode.el

(defconst elnode-config-directory (expand-file-name (concat user-emacs-directory "elnode/")) "\
The config directory for elnode to store peripheral files.

This is used as a base for other constant directory or file
names (the elnode auth database is a file in this directory, the
elnode webserver has a docroot directory in this directory).

It is based on the `user-emacs-directory' which always seems to
be set, even when emacs is started with -Q.")

(autoload 'elnode-app "elnode" "\
A macro that sets up the boring boilerplate for Elnode apps.

This sets up lexical binding, captures the module's parent
directory in DIR-VAR, requires `cl' and any other features you
list.  Use it like this:

 (elnode-app my-app-dir esxml mongo-elnode)

Once used you can access the variable `my-app-dir' as the dirname
of your module (which is useful for serving files and such).

\(fn DIR-VAR &rest FEATURES)" nil t)

(put 'elnode-app 'lisp-indent-function '1)

(autoload 'elnode-start "elnode" "\
Start a server using REQUEST-HANDLER.

REQUEST-HANDLER will handle requests on PORT on HOST (which is
'localhost' by default).

REQUEST-HANDLER is a function which is called with the request.
The function is called with one argument, which is the
http-connection.

You can use functions such as `elnode-http-start' and
`elnode-http-send-body' to send the http response.

Example:

  (defun nic-server (httpcon)
    (elnode-http-start httpcon 200 '(\"Content-Type\" . \"text/html\"))
    (elnode-http-return httpcon \"<html><b>BIG!</b></html>\"))
  (elnode-start 'nic-server)

Now visit http://127.0.0.1:8000

If PORT is non-nil, then run server on PORT, otherwise default to
8000.

If HOST is non-nil, then run the server on the specified local IP
address, otherwise use localhost.  A few names are predefined:

  \"localhost\" is 127.0.0.1
  \"*\" is 0.0.0.0

Additionally, you may specifiy an IP address, e.g \"1.2.3.4\"

Note that although HOST may be specified, elnode does not
disambiguate on running servers by HOST.  So you cannot start two
elnode servers on the same port on different hosts.

DEFER-MODE may be used to control how deferred handlers are
managed for this server.

SERVICE-MAPPINGS is an alist of service resource symbols mapped
to integer port numbers.  This can be supplied to elnode-start to
allow it to map service resources defined by handlers to
different TCP ports and therefore different Emacs instances.

The list of SERVICE-MAPPINGS is also used to start ancilliary
port servers.  Ancilliary port servers should be automatically
stopped when the main server is stopped.

\(fn REQUEST-HANDLER &key PORT (host \"localhost\") (defer-mode :managed) SERVICE-MAPPINGS)" t nil)

(defvar elnode-hostpath-default-table '(("[^/]+//wiki/\\(.*\\)" . elnode-wikiserver) ("[^/]+//\\(.*\\)" . elnode-webserver)) "\
Defines mappings for `elnode-hostpath-default-handler'.

This is the default mapping table for Elnode, out of the box. If
you customize this then elnode will serve these hostpath mappings
by just loading Elnode.

By default the table maps everything to
`elnode-webserver'. Unless you're happy with the default you
should probably get rid of the everything path because it will
interfere with any other mappings you add.")

(custom-autoload 'elnode-hostpath-default-table "elnode" t)

(defconst elnode-config-directory (expand-file-name (concat user-emacs-directory "elnode/")) "\
The config directory for elnode to store peripheral files.

This is used as a base for other constant directory or file
names (the elnode auth database is a file in this directory, the
elnode webserver has a docroot directory in this directory).

It is based on the `user-emacs-directory' which always seems to
be set, even when emacs is started with -Q.")

(autoload 'elnode--webserver-handler-proc "elnode" "\
Actual webserver implementation.

Do webserving to HTTPCON from the DOCROOT using the MIME-TYPES
for meta information.

This is not a real handler (because it takes more than the
HTTPCON) but it is called directly by the real webserver
handlers.

\(fn HTTPCON DOCROOT MIME-TYPES)" nil nil)

(autoload 'elnode-make-webserver "elnode" "\
Make a webserver interactively, for DOCROOT on PORT.

An easy way for a user to make a webserver for a particular
directory.

\(fn DOCROOT PORT &optional HOST)" t nil)

(autoload 'elnode-webserver "elnode" "\
A simple webserver that serves documents out of `elnode-webserver-docroot'.

This is just an example of an elnode webserver, but it may be all
that is needed most of the time.

See `elnode-webserver-handler-maker' for more possibilities for
making webserver functions.

HTTPCON is the HTTP connection to the user agent.

\(fn HTTPCON)" nil nil)

(autoload 'elnode-init "elnode" "\
Bootstraps the elnode environment when the Lisp is loaded.

It's useful to have elnode start automatically... on Lisp
load.  If the variable `elnode-init-port' is set then this
function will launch a server on it.

The server is started with `elnode-hostpath-default-handler' as
the handler and listening on `elnode-init-host'

\(fn)" t nil)

(defvar elnode-do-init nil "\
Should elnode start a server on load?

The server that is started is controlled by more elnode
customizations.

`elnode-hostpath-default-table' defines the mappings from
hostpath regexs to handler functions. By default elnode ships
with this customization setup to serve the document root defined
in `elnode-webserver-docroot', which by default is ~/public_html.")

(custom-autoload 'elnode-do-init "elnode" t)

(eval-after-load 'elnode '(if (and (boundp 'elnode-do-init) elnode-do-init (or (not (boundp 'elnode--inited)) (not elnode--inited))) (progn (elnode-init) (setq elnode--inited nil))))

;;;***

;;;### (autoloads (elnode-server-list elnode-deferred-list elnode-deferred-queue)
;;;;;;  "elnode-lists" "elnode-lists.el" (21767 9141 829877 114000))
;;; Generated autoloads from elnode-lists.el

(autoload 'elnode-deferred-queue "elnode-lists" "\
Message the length of the deferred queue.

\(fn ARG)" t nil)

(autoload 'elnode-deferred-list "elnode-lists" "\
List the currently deferred Elnode handlers.

\(fn &optional PREFIX)" t nil)

(defalias 'list-elnode-deferreds 'elnode-deferred-list)

(autoload 'elnode-server-list "elnode-lists" "\
List the currently running Elnode servers.

\(fn &optional PREFIX)" t nil)

(defalias 'list-elnode-servers 'elnode-server-list)

;;;***

;;;### (autoloads ((quote elnode-log-mode)) "elnode-log-mode" "elnode-log-mode.el"
;;;;;;  (21767 9142 77877 112000))
;;; Generated autoloads from elnode-log-mode.el

(autoload 'elnode-log-mode "elnode-log-mode" "\
Elnode log viewing mode.

For viewing access log files from Elnode.

\(fn)" t nil)

;;;***

;;;### (autoloads (elnode-make-proxy-server elnode-make-proxy) "elnode-proxy"
;;;;;;  "elnode-proxy.el" (21767 9141 717877 116000))
;;; Generated autoloads from elnode-proxy.el

(autoload 'elnode-make-proxy "elnode-proxy" "\
Make a proxy handler sending requests to URL.

See `elnode-proxy-do' for how URL is handled.

An HTTP user-agent with a specified HTTP proxy sends the full
request as the path, eg:

  GET http://somehost:port/path?query HTTP/1.1

So `elnode-make-proxy' can make (something like) a full proxy
server with:

  (elnode-make-proxy \"${path}${query}\")

There may be many things that a full proxy does that this does
not do however.

Reverse proxying is a simpler and perhaps more useful.

\(fn URL)" nil nil)

(autoload 'elnode-make-proxy-server "elnode-proxy" "\
Make a proxy server on the specified PORT.

Optionally have requests go to URL.  If URL is not specified it
is \"${path}${query}\".

Interactively use C-u to specify the URL.

\(fn PORT &optional URL)" t nil)

;;;***

;;;### (autoloads (elnode-wikiserver elnode-wikiserver-test elnode-wikiserver-wikiroot)
;;;;;;  "elnode-wiki" "elnode-wiki.el" (21767 9141 941877 113000))
;;; Generated autoloads from elnode-wiki.el

(defconst elnode-wikiserver-wikiroot-default (expand-file-name (concat elnode-config-directory "wiki/")) "\
The default location of the wiki root.

This is used to detect whether elnode needs to create this
directory or not.")

(defvar elnode-wikiserver-wikiroot elnode-wikiserver-wikiroot-default "\
The root for the Elnode wiki files.

This is where elnode-wikiserver serves wiki files from.")

(custom-autoload 'elnode-wikiserver-wikiroot "elnode-wiki" t)

(autoload 'elnode-wikiserver-test "elnode-wiki" "\
Test whether we should serve Wiki or not.

\(fn)" nil nil)

(autoload 'elnode-wikiserver "elnode-wiki" "\
Serve Wiki pages from `elnode-wikiserver-wikiroot'.

HTTPCON is the request.

The Wiki server is only available if the `creole' package is
provided. Otherwise it will just error.

\(fn HTTPCON)" nil nil)

;;;***

;;;### (autoloads nil nil ("elnode-pkg.el" "elnode-rle.el" "elnode-testsupport.el")
;;;;;;  (21767 9142 148528 335000))

;;;***

(provide 'elnode-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; elnode-autoloads.el ends here
