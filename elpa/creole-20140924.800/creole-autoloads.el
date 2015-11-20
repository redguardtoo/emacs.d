;;; creole-autoloads.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads (creole-wiki) "creole" "creole.el" (21767 9139
;;;;;;  233877 144000))
;;; Generated autoloads from creole.el

(autoload 'creole-wiki "creole" "\
Export WikiCreole SOURCE into HTML.

Returns the buffer where the HTML was exported. This could be a
user supplied buffer (see DESTINATION) or a buffer created based
on the filename of the source (or just automatically created).

SOURCE can be a buffer or plain text or something we might
recognize as a file.  A file-name is detected by a leading
'~' (meaning expand from the user root) or '/' (meaning rooted)
or './' (meaning expand from the root of the source creole file).

If SOURCE is a filename it is loaded with `creole/get-file'.


Keyword arguments are supported to change the way the HTML is
produced.

DESTINATION can be a buffer or a buffer name to write the HTML
into or it can be 't' to indicate the default output stream.  In
the latter case an automatic buffer is still created and the HTML
is sent to the default output stream when the export is done.

The DESTINATION buffer is always returned.

STRUCTURE-TRANSFORM-FN is a structure transformation function or
list of functions, see `creole-html' for details.

HTMLFONTIFY - use 'htmlfontify' to fontify any code blocks; this
is true by default.

Code blocks are marked up like pre-formatted areas but must begin
with a line stating the Emacs mode to fontify the text as; for
example:

 {{{
 ##! emacs-lisp
 (let ((x 1)) x)
 }}}

would cause Emacs Lisp to be fontified.

HTMLFONTIFY-STYLE - add an HTML-STYLE block for 'htmlfontify'
code blocks. If this is nil an HTML-STYLE block is NOT added.

BODY-HEADER - a string or a file-name with HTML code to be
inserted in the BODY of the HTML document before the Creole
markup export.  A file-name is detected in the same way as for
SOURCE.

BODY-FOOTER - a string or a file-name with HTML code to be
inserted in the BODY of the HTML document after the Creole markup
export.  A file-name is detected in the same way as for SOURCE.

The BODY-HEADER and the BODY-FOOTER are treated as moustache
templates and expanded before being inserted.  See
'creole-moustache' for a description.  Variables passed to
'creole-moustache' with the template are:

  text - the creole source text of the page

or any variable in VARIABLES, which is an alist of
symbols -> values.

DOCROOT - base any files to be served.  Any file-name reference
for CSS or JavaScript, if residing under this docroot, will be
linked to the document rather than embedded.

DOCROOT-ALIAS - is the docroot path to use in any links as an
alias for the docroot.

CSS - a list of cascading style sheets, each entry can either be
a file-name (a file-name is detected in the same way as
for SOURCE) or a string with W3C-CSS statements in it.

If a DOCROOT is specified then any cascading style sheets
file-name is LINKed into the resulting document, if not then the
statements are embedded directly.

JAVASCRIPT - a list of JavaScript, as for CSS, each entry can
be either a string of the JavaScript to be directly embedded or a
file-name reference (as in SOURCE).  As for :CSS if
a :DOCROOT is specified then the scripts will be loaded as links
but otherwise will be embedded.

META - a list of strings specifying resulting HTML-META elements.
For example:

 :meta '(\"name='description'
          content='Free Web tutorials on HTML, CSS, XML'\")

:OTHER-LINK - a list of string specifying resulting HTML-LINK
elements, for example:

 :other-link '(\"rel='alternate' href='/my-feed.rss'\")

:DOCTYPE may be nil, in which case nothing is added or it may be
a string in which case it is inserted directly before the <html>
element, or it may be one of the symbols 'xhtml or 'html5 in
which case the right doctype is added.

All, any or none of these keys may be specified.

\(fn SOURCE &key DESTINATION STRUCTURE-TRANSFORM-FN (htmlfontify t) (htmlfontify-style t) BODY-HEADER BODY-FOOTER VARIABLES DOCROOT DOCROOT-ALIAS CSS JAVASCRIPT META OTHER-LINK DOCTYPE)" t nil)

;;;***

;;;### (autoloads nil nil ("creole-pkg.el") (21767 9139 357686 298000))

;;;***

(provide 'creole-autoloads)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; creole-autoloads.el ends here
