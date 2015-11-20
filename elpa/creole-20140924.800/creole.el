;;; creole.el --- A parser for the Creole Wiki language

;;; Copyright (C) 2011, 2012 by Nic Ferrier

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;; Maintainer: Nic Ferrier <nferrier@ferrier.me.uk>
;; Created: 27th October 2011
;; Version: 1.0.6
;; Package-Version: 20140924.800
;; Package-requires: ((noflet "0.0.3")(kv "0.0.17"))
;; Keywords: lisp, creole, wiki

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

;; This is a WikiCreole wiki parser. WikiCreole is something like the
;; Wiki language used by OddMuse, which is the EmacsWiki wiki
;; language.

;; This parser now includes extra support to help deal with OddMuse
;; files.

;; This code was originally written to mark the death of John McCarthy
;; - http://news.ycombinator.com/item?id=3151988

;; WikiCreole is an emerging standard documented at:
;; http://www.wikicreole.org/wiki/Creole1.0

;;; Code:

(require 'htmlfontify)
(require 'org-table)
(require 'calc)
(require 'rx)
(require 'noflet)
(require 'cl)
(require 'kv)

(defmacro when1 (expr &rest body)
  "Evaluate BODY when EXPR but return EXPR."
  (declare (debug (form &rest form))
           (indent 1))
  (let ((expr-val (make-symbol "expr-val")))
    `(let ((,expr-val ,expr))
       (when ,expr-val
         ,@body)
       ,expr-val)))

(defgroup creole nil
  "A WikiCreole parser and associated tools."
  :group 'hypertext)

(defvar creole-oddmuse-on nil
  "Whether creole should include OddMuse compatability.

OddMuse is the Wiki language used by the EmacsWiki.  It is very
nearly WikiCreole but not quite.  Hence this flag which turns on
various small tweaks in behaviour.")

(defvar creole-link-resolver-fn nil
  "The function which will resolve links.

Resolving a link is necessary for links without context such as:

  [thing]

or a link formed by CamelCaps.

By default there is no link resolver and these links are not
resolved.")

(defun creole/link-resolve (name)
  "A simple creole link resolver.

Resolve the link by looking in the current directory for a
.creole file that matches the name.

A note for Wiki implementors: This is not a good implementation
for a web app since it exposes the extensions and does not
prepend a URL.  If you use a resolver to prepend the url then you
may as well resolve the extension in the webapp."
  (let ((candidates
         (directory-files
          default-directory
          nil (concat name ".creole"))))
    (if (and (listp candidates)
             (car-safe candidates))
        (car candidates)
        name)))

(defun creole/link-replacer (m)
  "Replace regexp replacer for `creole-link'."
  (apply
   'format
   "<a href='%s'>%s</a>"
   (cond
     ;; We have both a url and a link
     ((match-string 4 m)
      (let ((link (match-string 1 m))
            (text (match-string 5 m)))
        (list
         (if (and (not (string-match-p (rx (or "ftp" "http" "mailto") ":") link))
                  (functionp creole-link-resolver-fn))
             (funcall creole-link-resolver-fn link) link) text)))
     ;; We only have a url
     ((match-string 1 m)
      (let ((link (match-string 1 m)))
        (list
         (if (and (not (string-match-p (rx (or "ftp" "http" "mailto") ":") link))
                  (functionp creole-link-resolver-fn))
             (funcall creole-link-resolver-fn link) link)
         link))))))

(defun creole-link-parse (text)
  "Parse TEXT for creole links.

If `creole-oddmuse-on' is t then OddMuse links (that do not start
with '!') will be parsed as well. OddMuse links are single
bracket links, like:

 [ThisIsOddMuse]

If `creole-link-resolver-fn' is non-nil and a function then all
single element links are passed through it.  This variable also
turns on CamelCase linking."
  (if (and creole-oddmuse-on (string-match-p (rx bol "!") text))
      (replace-regexp-in-string (rx bol "!") "" text t)
      ;; Else it's not an escaped link
      (let* ((resolvable-link
              (if (functionp creole-link-resolver-fn)
                  (let* ((case-fold-search nil)) ; do CamelCaps links
                    (replace-regexp-in-string
                     (rx
                      (or buffer-start bol bos)
                      (group
                       (? (not (any "[")))
                       (group
                        (>= 2 (and (any upper)
                                   (one-or-more (any lower)))))))
                     (lambda (m)
                       (let ((link (match-string 1 m)))
                         (format
                          "<a href='%s'>%s</a>"
                          (funcall creole-link-resolver-fn link)
                          link)))
                     text t))
                  ;; Else just use the text
                  text))
             (real-creole
              (replace-regexp-in-string
               (rx "[["
                   (group
                    (* (group (or "ftp" "http" "mailto") ":"))
                    (+ (not (any "]|"))))
                   (*
                  (group
                   "|" (group (group (+ (not (any "]")))))))
                   "]]")
               'creole/link-replacer
               resolvable-link))
             (oddmuse
              (when creole-oddmuse-on
                (replace-regexp-in-string
                 (rx "["
                     (group
                      (* (group (and (+ (in alpha))) ":"))
                      (+ (not (any "]| "))))
                     (* (group
                         (any "| ")
                         (group (group (+ (not (any ?\])))))))
                     "]")
                 'creole/link-replacer
                 real-creole)))
             (bracket-resolved (if oddmuse oddmuse real-creole)))
        bracket-resolved)))

(defvar creole-image-class nil
  "A default class to be applied to wiki linked images.")

(defun creole/image->html (m)
  "Convert image urls to HTML."
  (let (title)
    (apply
     'format
     (append
      '("<img %ssrc=\"%s\" alt=\"%s\" %s%s></img>")
      (list
       ;; Whether we have a class to apply or not
       (if creole-image-class (format "class=\"%s\" " creole-image-class) "")
       ;; URL of the image
       (if (functionp creole-link-resolver-fn)
           (funcall creole-link-resolver-fn (match-string 1 m))
           ;; Else
           (match-string 1 m))
       ;; if we don't have an alternate, use the URL
       (if (match-string 4 m)
           (setq title (match-string 5 m))
           (match-string 1 m))
       ;; title
       (if title (format "title=\"%s\" " title) "")
       ;; Match only the size part for now
       (if (match-string 2 m)
           (let ((options (match-string 3 m)))
             (save-match-data
               ;; 'size=' is optional and is the only parameter right now
               (string-match
                (rx (group (+ digit))
                    (? (group (and ?x (group (+ digit))))))
                options)
               (when (match-string 1 options)
                 (concat
                  (format
                   "width=\"%s\" " (match-string 1 options))
                  (when (match-string 2 options)
                    (format "height=\"%s\" " (match-string 3 options)))))))
           ""))))))

(defun creole-include-handler (match-data scheme path)
  "Embed handler to handle \"include:file\" embeds.

Add this to `creole-embed-hanndlers' (for example, for scheme
\"include\") to support creole includes, for example:

  = A document =
  {{include:somecreolefile}}

allows \"somecreolefile\" to be HTML rendered and embedded in the
output of the main document.

If `creole-link-resolver' is defined then link resolution is
performed on PATH before loading.

`creole-html' is used to render the HTML for the included file."
  (let* ((file-path (if (functionp creole-link-resolver-fn)
                        (funcall creole-link-resolver-fn path)
                        ;; Else just the path
                        path)))
    (with-temp-buffer
      (insert-file-contents-literally file-path)
      (let ((creole-buffer (current-buffer)))
        (with-temp-buffer
          (creole-html creole-buffer (current-buffer) :erase-existing t)
          (buffer-string))))))

(defvar creole-youtube-handler-width 420
  "The width that will be used for youtube videos.

Note that not all widths are possible.")

(defvar creole-youtube-handler-height 315
  "The height that will be used for youtube videos.

Note that not all heights are possible.")

(defun creole-youtube-handler (m scheme path)
  "Handle \"youtube\" scheme, turning it into an HTML embed.

This creole:

  {{youtube:WcUwCsAhWMk|a nice video on emacs-lisp}}

will produce this HTML:

 <span class=\"youtube\">
   <iframe src=\"//www.youtube.com/embed/WcUwCsAhWMk\"
         width=\"420\" height=\"315\"
         frameborder=\"0\" allowfullscreen></iframe>
   <em>a nice video on emacs-lisp</em>
 </span>

The link resolver is not consulted to resolve the link."
  ;; Just the youtube iframe thing
  (format "<span class=\"youtube\"><iframe src=\"//www.youtube.com/embed/%s\"
width=\"%s\" height=\"%s\"
frameborder=\"0\" allowfullscreen></iframe>
%s
</span>" path creole-youtube-handler-width creole-youtube-handler-height
(if (match-string 4 m)
    (format "<em>%s</em>" (match-string 5 m))
    "")))

(defvar creole-summary-resolver nil
  "Optional resolver function for article links from summaries.

If set to a function of one argument, this is used by
`creole-summary-handler' to resolve the path to the summary
article into an article path.")

(defun creole-summary-handler (m scheme path)
  "Embed handler to handle \"summary:file\" embeds.

Using this will let you pull in the first para of an article."
  ;; This is not a very good summary handler
  ;;
  ;; what is SHOULD do is to take the elements up to and including the
  ;; first para and then throw everything else away.
  (let* ((file-path (if (functionp creole-link-resolver-fn)
                        (funcall creole-link-resolver-fn path)
                        ;; Else just the path
                        path)))
    (with-temp-buffer
      (insert-file-contents-literally file-path)
      (let* ((creole-buffer (current-buffer))
             ;; We could cache the creole-structure?
             (struct
              (creole-structure (creole-tokenize creole-buffer)))
             ;; cdar expects a para...need to change that
             (summary (cdar struct))
             (decorated (format "%s [[%s|... read more]]"
                                summary
                                path)))
        (with-temp-buffer
          (insert
           (let ((creole-link-resolver-fn
                  (lambda (path)
                    (if (functionp creole-summary-resolver)
                        (funcall creole-summary-resolver path)
                        path))))
             (creole-block-parse decorated)))
          (buffer-string))))))


(defvar creole-embed-handlers nil
  "An a-list of scheme . handler-function pairs for handling embeds.

The image syntax can be used to handle generic embedding, turning
a URL into some generic output code.  Each url scheme that can be
used to do that must be registered here.

For example: youtube:TR7DPvEi7Jg could be returned as the embed
HTML for that specific youtube video.

Handlers should expect three arguments: the match data (as passed
to `creole-image-resolve') and then the scheme and the path (the
non-scheme part of the url).")

(defun creole-image-resolve (m)
  "Resolve M, a match object, into HTML.

M comes from `creole-image-parse' and has the following groups:

 1 the url part
 2 the query part with the leading \"?\"
 3 the query part without the \"?\"
 4 the description part with the leading \"|\"
 5 the description part without the leading \"|\"

The resolution uses `creole-embed-handlers' to attach handling
logic to urls via url schemes.

If no handler is found the embed is presumed to be an image and
passed to `creole/image->html'."
  (let ((md (match-data)))
    ;; Match the url part for a scheme
    (noflet ((matches (regex to-match)
               (save-match-data
                 (when (string-match regex to-match)
                   (loop for i from 0 to (- (/ (length (match-data)) 2) 1)
                      collect (match-string i to-match))))))
      (let ((url (match-string 1 m)))
        (destructuring-bind (&optional url scheme path)
            (matches
             (rx (group (+ (any "A-Za-z"))) ":"
                 (group (+ anything)))
             url)
          ;; I do this because save-match-data doesn't seem to work.
          (set-match-data md)
          ;; Find whether we have a specific handler for scheme and then
          ;; pass it path
          (let ((handler-fn (kva scheme creole-embed-handlers)))
            (if (functionp handler-fn)
                (save-match-data
                  (funcall handler-fn m scheme path))
                ;; Else just call the image handler
                (creole/image->html m))))))))

(defun creole-image-parse (text)
  "Parse TEXT for creole images.

Images should have this format:

{{image.jpg?size=50x100|description}}

where the size and description is optional, and the second
dimension in size can be omitted.

The 'size=' is optional, and I keep there because this way you
could add more parameters to the image if you needed them. By
now, a size is supposed, and the values are assumed to be either
a Width, or a WidthxHeight specification.

If defined then `creole-link-resolver-fn' is used for links."
  (replace-regexp-in-string
   (rx "{{"
       (group (+ (not (any "?|}"))))
       (* (group "?" (group (+ (not (any "?|}"))))))
       (? (group "|" (group (+ (not (any "}"))))))
       "}}")
   'creole-image-resolve
   text))

(defun creole-block-parse (text)
  "Parses TEXT as a creole block.

A creole block is a paragraph or list item that can include
links, italic, bold, line break or inline preformatted markup.

Returns a copy of TEXT with the WikiCreole replaced with
appropriate HTML."
  (let ((transformed
         (replace-regexp-in-string
          (rx "**"
              (group (*? anything))
              "**")
          "<strong>\\1</strong>"
          (replace-regexp-in-string
           (rx (group (not (any ":")))
               "//"
               (group (*? anything) (not (any ":")))
               "//")
           "\\1<em>\\2</em>"
           (replace-regexp-in-string
            (rx bol
                "//"
                (group (*? anything) (not (any ":")))
                "//")
            "<em>\\1</em>"
            (replace-regexp-in-string
             (rx "{{{"
                 (group (*? anything))
                 "}}}")
             "<code>\\1</code>"
             (replace-regexp-in-string
              (rx ?\\)
              "<br/>"
              text)))))))
    (if creole-oddmuse-on
        (creole-image-parse
         (creole-link-parse
          (replace-regexp-in-string
           (rx "'''"
               (group (*? not-newline))
               "'''")
           "<em>\\1</em>"
           (replace-regexp-in-string
            (rx "##"
                (group (*? not-newline))
                "##")
            "<code>\\1</code>"
            transformed))))
        ;; Else
        (creole-image-parse (creole-link-parse transformed)))))

(defvar creole-recalculate-org-tables t
  "Indicates that Org tables should be recalculated inplace.

Table calculation is performed calling
`org-table-recalculate'. The default value is to recalculate the
tables. However, this leaves the original buffer modified. If you
don't want the original buffer modified, or you don't have
formulas in your tables (so recalculation is not necessary), you
can change this value to nil.")

(defun creole/org-table-row-parser (row-text)
  "Split an org-table row into a list of cells."
  (noflet ((last-pos (text) ;; find the last |
             (string-match "|[ \n]*$" text)))
    (let* ((pairs (list (cons "//" "//")
                        (cons "{{" "}}")
                        (cons "[[" "]]")))
           (cellstart 1)
           (pt cellstart)
           lst)
      (catch :escape
        (while t
          (if (< pt (last-pos row-text))
              (let* ((cell (substring row-text pt))
                     (delim-pos (string-match
                                 (rx (group
                                      (or "//" "{{" "[[" "|")))
                                 cell))
                     (delim (match-string 1 cell)))
                (if (equal delim "|")
                    (progn
                      (push
                       (substring row-text cellstart
                                  (+ pt delim-pos))
                       lst)
                      (setq pt (setq cellstart (+ pt delim-pos 1))))
                    ;; else it's got some formatting so skip it whatever it is
                    (let* ((start (+ delim-pos (length delim)))
                           (delim-end (kva delim pairs))
                           (end (string-match
                                 (rx-to-string `(and ,delim-end) t)
                                 (substring cell start))))
                      ;; and add it to l to find end point
                      ;; and then search again
                      (setq pt (+ pt (+ start end (length delim-end)))))))
              ;; Else
              (unless (equal cellstart pt)
                (push (substring row-text cellstart pt) lst))
              (throw :escape (reverse lst))))))))

(defun creole/org-table-to-lisp (&optional txt)
  "Convert the table at point to a Lisp structure.

Replaces `org-table-to-lisp' with something that handles cells
for creole better since a cell with a link in it would fail
otherwise because creole uses the | as a link separator."
  (unless txt
    (unless (org-at-table-p)
      (user-error "No table at point")))
  (let* ((txt (or txt
		  (buffer-substring-no-properties
                   (org-table-begin)
                   (org-table-end))))
	 (lines (org-split-string txt "[ \t]*\n[ \t]*")))
    (mapcar
     (lambda (x)
       (if (string-match org-table-hline-regexp x)
	   'hline
           (creole/org-table-row-parser x)))
     lines)))

(defun creole-tokenize (docbuf)
  "Parse DOCBUF which is full of creole wiki text.

See http://www.wikicreole.org/wiki/Creole1.0 for more information
on WikiCreole.

Returns a list of parsed elements."
  (with-current-buffer docbuf
    (save-excursion
      (goto-char (point-min))
      (let ((res '()))
        (while (not (eobp))
          (cond
           (;; Heading
            (looking-at (rx bol (group (+ "=")) (in blank)))
             (let ((level (length (match-string 1))))
               ;; Actually, the end = is optional... not sure if, when
               ;; there is an end = it has to be the same number as the
               ;; first one
               (if (not
                    (re-search-forward
                     (rx bol
                         (group (+ "="))
                         (+ blank)
                         (group (* any))
                         (+ blank)
                         (group (+ "="))
                         eol)
                     nil 't))
                   (error "Creole: badly formatted heading"))
               (when (equal (length (match-string 3))
                            level)
                 (setq res (append res
                                   (list
                                    (cons
                                     (intern (format "heading%s" level))
                                     ;; The string that is the heading
                                     ;; - any internal rules we should
                                     ;; deal with here
                                     (match-string 2)))))
                 (forward-line))))
            (;; OddMuse portraits
             (and creole-oddmuse-on (looking-at
                                     (rx bol "portrait:" (group (* any)))))
             (setq res (append res (list (cons 'portrait (match-string 1)))))
             (forward-line))
            (;; Table
             (looking-at "^|")
             ;; Recalculate tables?
             (when creole-recalculate-org-tables
               ;; Requires that we're back in the table
               (org-table-recalculate t))
             (let* ((tbl (creole/org-table-to-lisp))
                    (pt (org-table-end)))
               (setq res (append
                          res
                          (list
                           (cons 'table tbl))))
               (goto-char pt)
               ;; Skip forward over any org-tbl comments
               (unless (re-search-forward "^[^#]" nil t)
                 (goto-char (point-max)))
               (beginning-of-line)))
            (;; Unordered list item
             (looking-at
              (rx bol
                  (group (+ "*"))
                  (in blank)
                  (group (* any))))
             (let ((level (length (match-string 1))))
               (setq res (append res
                                 (list
                                  (cons
                                   (intern (format "ul%s" level))
                                   ;; The string that is the heading
                                   ;; - any internal rules we should
                                   ;; deal with here
                                   (match-string 2)))))
               (forward-line)))
            (;; Ordered list item
             (looking-at (rx bol
                             (group (+ "#"))
                             (in blank)
                             (group (* any))))
             (let ((level (length (match-string 1))))
               (setq res (append res
                                 (list
                                  (cons
                                   (intern (format "ol%s" level))
                                   ;; The string that is the heading
                                   ;; - any internal rules we should
                                   ;; deal with here
                                   (match-string 2)))))
               (forward-line)))
            (;; Horizontal rule
             (looking-at (rx bol
                             (* (in blank))
                             "----"
                             (* (in blank))
                             eol))
             (setq res (append res (list (cons 'hr ""))))
             (forward-line))
            (;; Pre-formatted block
             (looking-at (rx bol "\n{{{" eol))
             (if (not
                  (re-search-forward
                   (rx bol
                       "\n{{{\n"
                       (group (*? anything))
                       "\n}}}" (* space)
                       eol)
                   nil t))
                 (error "Creole: bad preformatted block"))
             (setq res (append res
                               (list
                                (cons 'preformatted (match-string 1)))))
             (forward-line))
            ;; Oddmuse allows space defined pre-blocks
            ((and creole-oddmuse-on (looking-at "^\n +[^-]"))
             (let* ((start (point))
                    (end (progn (next-line)
                                (re-search-forward "^$" nil t)))
                    (str (buffer-substring start end)))
               (setq res (append res (list (cons 'preformatted str))))
               (goto-char end)))
            (;; Lisp-plugin
             (or (looking-at (rx bol "\n" "<<(" eol))
                 (and (looking-at "^<<(")
                      (when1 (save-excursion
                               (previous-line)
                               (looking-at (rx bol "\n" "<<(")))
                        (previous-line))))
             (if (not
                  (re-search-forward
                   (rx bol
                       "\n"
                       "<<("
                       "\n"
                       (group (*? anything))
                       "\n"
                       ")>>"
                       (* space)
                       eol)
                   nil t))
                 (error "Creole: bad Lisp plugin block"))
             (let* ((plugin-lisp (match-string 1))
                    (value (eval (car (read-from-string plugin-lisp))))
                    (plugin-fragment (with-temp-buffer
                                       (insert value)
                                       (creole-tokenize (current-buffer)))))
               (setq res (append res plugin-fragment)))
             (forward-line))
            (;; HTML-plugin
             (or (looking-at "^\n<<html\n")
                 (and
                  (looking-at "<<html\n")
                  (when1
                      (save-excursion
                        (previous-line)
                        (looking-at "\n<<html\n"))
                    (previous-line))))
             (if (not
                  (re-search-forward
                   (rx bol
                       "\n"
                       "<<html"
                       "\n"
                       (group-n 1 (*? anything))
                       "\n"
                       "html>>"
                       eol) nil t))
                 (error "Creole: bad HTML plugin block"))
             (setq res (append res
                               (list
                                (cons 'plugin-html (match-string 1)))))
             (forward-line))
            (;; Paragraph line
             (and (looking-at (rx bol (not (any "=*"))))
                  (not (looking-at (rx bol "<<html")))
                  (not (looking-at (rx bol eol))))
             (let* ((start (point))
                    (end
                     (save-match-data
                       (let* ((matched-end
                               ;; Find the end - the end is actually BEFORE this
                               (re-search-forward
                                (rx (or (group bol eol)
                                        (group bol (in "=*"))
                                        (group eol "\nhtml>>\n")))
                                nil 't))
                              (matched (if matched-end (match-string 0))))
                         (cond
                           ((equal matched "") (- matched-end 1))
                           ((equal matched "*") (- matched-end 2))
                           ((equal matched "=") (- matched-end 2))
                           ((equal matched "\n<<html") (- matched-end 8))
                           (t
                            (point-max)))))))
               (setq res
                     (append
                      res
                      (list
                       (cons 'para (buffer-substring start end)))))
               (goto-char end)))
            ('t
             (forward-line))))
        res))))

(defun creole/test-doc (buffer)
  "Insert a test document of creole text into BUFFER."
  (with-current-buffer buffer
    (insert "= Heading! =\n")
    (insert "\n")
    (insert "== Heading2! ==\n")
    (insert "# an ordered list item\n## a 2nd ordered list item\n")
    (insert "== Heading3 is a multi word heading ==\n")
    (insert "\n{{{\n== this is preformatted ==\n{{\nIt looks great\n}}\n}}}\n")
    (insert "* list item\n** 2nd list item\n*** 3rd list item\n")
    (insert "** another 2nd list item\n*** another 3rd list item\n")
    (insert " ----\n")
    (insert "This is a paragraph
that runs over several lines
* and a list item stops it
")
    (insert "This is a paragraph {{{with code}}} and [[links]]
and **bold** and //italics//.")))

(defun creole/list-item (list-symbol)
  "Return the type and the level of the LIST-SYMBOL.

For example:

 (creole/list-item 'ol1)
  => (ordered . 1)

 (creole/list-item 'ul10)
  => (unordered . 10)"
  (save-match-data
    (let ((s (symbol-name list-symbol)))
      (when (string-match (rx (group (in "uo") "l")
                              (group (+ digit)))
                          s)
        (cons
         (intern (match-string 1 s))
         (string-to-number (match-string 2 s)))))))

(defun creole-structure (lst)
  "Make a parsed structure from a list.

This is a parser, of sorts, in that it turns a list of tokens
into more of a tree structure.  In WikiCreole though, the only
thing that really needs a tree representation is ordered and
unordered lists, so all this function does is add structure to a
stream of list tokens.  All other tokens are passed through
directly.

This is not marked private because it does form part of what
might be called the parsing API of this creole library."
  (let* ((docptr lst)
         (state '()) ; used as a stack
         (result '()))
    (while docptr
      (let* ((token (car docptr))
             (lst-item (creole/list-item (car token))))
        (case (if lst-item 'listitem (car token))
          (listitem
           (let* ((last (if (car state) (cdar state)))
                  (last-level (if (car state) (caar state)))
                  (new (list (car lst-item) (cdr token))))
             (cond
              ;; Current level is higher than the last, embed a new list
              ((and last
                    (> (cdr lst-item) last-level))
               (setcdr last (append (cdr last) (list new)))
               ;; Update the stack
               (push (cons (cdr lst-item) new) state))
              ;; Current level is same as the last, extend the last list
              ((and last
                    (= (cdr lst-item) last-level))
               (setq new (list (cdr token)))
               (setcdr last (append (cdr last) new))
               ;; Reset the top of the stack
               (pop state)
               (push (cons (cdr lst-item) new) state))
              ;; Current level is same as the last, extend the last list
              ((and last
                    (< (cdr lst-item) last-level))
               (loop for i from 1 to (- last-level (cdr lst-item))
                     do (pop state))
               (let* ((last (if (car state) (cdar state)))
                      (last-level (if (car state) (caar state))))
                 (setq new (list (cdr token)))
                 (setcdr last (append (cdr last) new))))
              ;; The default action when we're dealing with lists
              (t
               (setq result (append result (list new)))
               ;; Update the stack
               (push (cons (cdr lst-item) new) state)))))
          ;; Not a list item - just push it onto the result, always
          ;; empty the list state
          (t
           (setq state '())
           (setq result (append result (list token))))))
      (setq docptr (cdr docptr)))
    result))

;; Exporting functions

(defun creole/html-list (type lst)
  "Export the specified LST in HTML.

The exported HTML is written into the current buffer.

This is NOT intended to be used by anything but
`creole-export-html'."
  (let ((first t))
    (insert "<" (symbol-name type) ">\n")
    (loop for item in lst
          do
          (cond
           ((listp item)
            (creole/html-list (car item) (cdr item))
            (setq first nil))
           (t
            (when (not first)
              (insert "</li>\n"))
            (setq first nil)
            (insert "<li>")
            (insert (creole-block-parse item)))))
    (insert "</li>\n")
    (insert "</" (symbol-name type) ">\n")))

(defun creole/html-table (table-list)
  "Convert the org-table structure TABLE-LIST to HTML.

We use `orgtbl-to-generic' to do this."
  (let ((value
         (orgtbl-to-generic
          table-list
          (list
           :tstart "<table>"
           :tend "</table>\n"
           :hlstart "<thead><tr>\n"
           :hlend "</tr></thead>"
           :hllstart "<thead><tr>\n"
           :hllend "</tr></thead>"
           :lstart "<tr>\n"
           :lend "</tr>"
           :hline nil
           :hfmt (lambda (field)
                  ;; Where we do block formatting
                  (format
                   "<th>%s</th>\n"
                   (creole-block-parse field)))
           :fmt (lambda (field)
                  ;; Where we do block formatting
                  (format
                   "<td>%s</td>\n"
                   (creole-block-parse field)))
           ))))
    value))

(defun creole-htmlize/mode-func (text)
  "Work out the mode function for TEXT.

A list is returned.  The first element is whether the first line
of the text should be stripped or not (if forcing marker text is
used that should be the case).  The `cdr' of the cons is the
Emacs mode function to use to color the text.  This either uses
some heuristics or a specific instruction at the start of the
text:

 ##! C
 int main(char** argv, int argc)
 {
   return 0;
 }

Shows how to indicate some C.

The heuristics are very simple right now.  They will probably
change to something heavily based on existing mode choosing
logic."
  (save-match-data
    (cond
      ((string-match
        (rx bol "##! " (group (* any)) "\n")
        text)
       (list
        t
        (intern
         (concat
          (or (match-string 1 text)
              (downcase mode-name))
          "-mode"))))
      ((string-match-p (rx bol (or (group ";;" (* ";") " " (* any)) "(")) text)
       ;; It's lisp
       (list nil (if (string-match-p (rx bol (* any) " -*- " (* any)) text)
                     'emacs-lisp-mode
                   'lisp-mode)))
      ((string-match-p (rx bol "#!/bin/" (+ lower) "sh" eol) text)
       (list nil 'shell-script-mode))
      ((string-match-p (rx bol "-module(") text)
       (list nil 'erlang-mode))
      (t (list nil text)))))

(defun creole-htmlize-string (text)
  "Make TEXT syntax coloured HTML using Emacs font-lock.

The syntax coloring to use is decided by `creole-htmlize/mode-func'.

A string containing the HTML syntax coloured with
`font-lock-fontify-buffer' and `htmlfontify' is returned.

If called interactively the current region is used as the string
and the result buffer is left open and switched to.

A property `:css-list' attached to the returned string contains
the list of CSS declarations generated by `htmlfontify'.  The
list can be turned into CSS by `creole-css-list-to-style-decl'.

Unfortunately, when run in batch mode Emacs doesn't attach colors
to faces and so we don't get coloured styles.  It should be
possible to use the `cadr' of the style to add colors."
  (interactive
   (list
    (if (mark)
        (buffer-substring
         (region-beginning)
         (region-end))
      (buffer-substring
       (point-min)
       (point-max)))))
  (destructuring-bind (strip-line mode-func) (creole-htmlize/mode-func text)
    (save-match-data
      (if (not (functionp mode-func))
          (concat "<pre>\n" text "\n</pre>")
          (with-temp-buffer
            ;; Get font-lock?
            (insert text "\n")
            (when strip-line
              ;; Kill the mode variable line
              (goto-char (point-min))
              (kill-line))
            ;; Now switch that mode into the new mode
            (funcall mode-func)
            (whitespace-mode -1)
            (font-lock-fontify-buffer)
            ;; Do some dynamic binding magic to alter htmlfontify
            ;; behaviour - no header, no footer and the styles list is
            ;; captured rather than written out.
            (let (css-list)
              (noflet ((hfy-sprintf-stylesheet
                        (css file)
                        (setq css-list css)
                        ""))
                (let ((hfy-display-class '((type x-toolkit)))
                      (hfy-page-footer (lambda (&optional file-name) "" "")))
                  (let (result
                        (htmlbuf
                         (noflet
                             ((message (format-str &rest args) t)) ; htmlfontify has annoying messages in it.
                             (htmlfontify-buffer))))
                    (with-current-buffer htmlbuf
                      ;; FIXME we should add another property
                      ;; detailing which mode we're dealing with-
                      ;;
                      ;; We MAY want to disambiguate styles, like
                      ;; "keyword" into "pre.emacs-lisp span.keyword"
                      (put-text-property
                       (point-min) (point-max)
                       :css-list css-list)
                      (setq
                       result
                       (buffer-substring
                        (point-min)
                        (point-max))))
                    (if (called-interactively-p 'interactive)
                        (switch-to-buffer htmlbuf)
                        (with-current-buffer htmlbuf
                          (set-buffer-modified-p nil))
                        (kill-buffer htmlbuf))
                    result)))))))))

(defun creole-content-list (structure)
  "Add a table of contents list to the STRUCTURE.

The list is only added if the STRUCTURE has at least 2 headings."
  (let* ((heads '(heading1 heading2 heading3 heading4))
         (headings
          (loop for el in structure
             if (memq (car el) heads)
             collect el))
         (heading-texts
          (loop for el in headings
             collect (list
                      (car el)
                      (format
                       "<a href='#%s'>%s</a>"
                       (creole/heading-text->id (cdr el))
                       (cdr el))))))
    (if (< (length headings) 2)
        structure
        ;; Else add the index before the 2nd index
        (let* ((toc `(ul ,@(loop for (head . data)
                              in (cdr heading-texts)
                              collect (car data)))))
          (loop for el in structure
             if (equal el (elt headings 0))
             append `((heading2 . "Table of content") ,toc)
             collect el)))))

(defvar creole-structured '()
  "A buffer local containing the parsed creole for the buffer.")

(defun creole/structure-pipeline (pipeline structure)
  "Calls each function in PIPELINE transforming STRUCTURE."
  (assert (listp pipeline) "creole/structure-pipeline needs a list")
  (loop
     with result = structure
     for stage in pipeline
       do (setq result (funcall stage result))
       finally return result))

(defun creole/heading-text->id (heading-text)
  "Make HEADING-TEXT into an HTML ID."
  (replace-regexp-in-string " " "-" heading-text))

(defvar creole-do-anchor-headings t
  "Whether to give each heading it's own anchor.

This behaviour is also controlled by `creole-oddmuse-on'.")

(defun creole/heading->html (heading-cons)
  "Convert a heading to HTML.

If `creole-oddmuse-on' or `creole-do-anchor-headings' is `t' then
an anchor is added automatically."
  (let* ((h-str (symbol-name (car heading-cons)))
         (level (save-match-data
                  (string-match
                   (rx "heading" (group (+ digit)))
                   h-str)
                  (match-string 1 h-str)))
         (h-text (if (listp (cdr heading-cons))
                     (cadr heading-cons)
                     (cdr heading-cons))))
    (format
     "%s<h%s>%s</h%s>\n"
     (if (or creole-oddmuse-on
             creole-do-anchor-headings)
         (format
          "<a id='%s'></a>\n"
          (creole/heading-text->id h-text)) "") ; else
     level h-text level)))

(defun* creole-html (docbuf
                     &optional html-buffer
                     &key result-mode
                     (erase-existing t)
                     (do-font-lock t)
                     switch-to
                     structure-transform-fn)
  "Export DOCBUF as HTML to HTML-BUFFER.

If HTML-BUFFER does not exist then a buffer is created based on
the name of DOCBUF. If DOCBUF doesn't have a name then the
destination buffer is called:

 *creolehtml.html

If RESULT-MODE is specified then the HTML-BUFFER is placed in
that mode.

If ERASE-EXISTING is not nil then any existing content in the
HTML-BUFFER is erased before rendering.  By default this is true.

If DO-FONT-LOCK is not nil then any pre-formatted areas tested
for fontification with `creole-htmlize/mode-func'.  It is `t' by
default.

If SWITCH-TO is not nil then the HTML-BUFFER is switched to when
the export is done.

When called interactively RESULT-MODE is set to 'html-mode',
ERASE-EXISTING is set to true and SWITCH-TO is set to true.

STRUCTURE-TRANSFORM-FN may be a function or a list of functions
to transform the parsed structure of the creole source.  A
transformation function must result in a legal creole
structure.  If a list is used the result of the first function in
the list is passed to the next until the list is exhausted.

The buffer local variable `creole-structured' is set on the
HTML-BUFFER with the parsed creole in it.  See `creole-structure'
for the details of that data structure.

Returns the HTML-BUFFER."
  (interactive
   (list
    (read-buffer "Creole buffer: " (current-buffer))
    nil
    :result-mode 'html-mode
    :switch-to 't))
  (let ((result-buffer ; make up the result buffer
         (or html-buffer
             (get-buffer-create
              (replace-regexp-in-string
               (rx (group (* "*"))
                   (group (* any))
                   (group (* "*")))
               "*creolehtml\\2.html"
               (buffer-name
                (if (bufferp docbuf)
                    docbuf
                  (get-buffer docbuf))))))))
    (make-local-variable 'creole-structured)
    (let ((creole
           (creole/structure-pipeline
            (if (functionp structure-transform-fn)
                (list structure-transform-fn)
                structure-transform-fn)
            (creole-structure
             (creole-tokenize docbuf)))))  ; Get the parsed creole doc
      (with-current-buffer result-buffer
        (if erase-existing (erase-buffer)) ; Erase if we were asked to
        (loop for element in creole
              do
              (let ((syntax (car element)))
                (case syntax
                  ;; The list elements can follow on from each other
                  ;; and require special handling
                  ((ul ol)
                   ;; FIXME lists don't do block level replacement yet!
                   (creole/html-list syntax (cdr element)))
                  ;; Headings
                  ((heading1 heading2 heading3 heading4 heading5)
                   (insert (creole/heading->html element)))
                  (portrait ; this is oddmuse/emacswiki stuff
                   (insert (format
                            "<img class='portrait' src='%s'><img>"
                            (cdr element))))
                  ;; Tables
                  (table
                   (insert (creole/html-table (cdr element))))
                  ;; We support htmfontify for PRE blocks
                  (preformatted
                   (let ((styled (and do-font-lock
                                      (creole-htmlize-string (cdr element)))))
                     (if (not styled)
                         (insert
                          (format
                           "<pre>\n%s\n</pre>\n"
                           (cdr element)))
                       (insert styled))))
                  ;; Just embed any HTML
                  (plugin-html
                   (insert (cdr element)))
                  (hr
                   (insert "<hr/>\n"))
                  (para
                   (insert (format
                            "<p>%s</p>\n"
                            (creole-block-parse (cdr element))))))))
        (if result-mode (call-interactively result-mode))
        (setq creole-structured creole))
      (if switch-to (switch-to-buffer result-buffer))
      result-buffer)))


(defun creole/file-under-root-p (file-name root)
  "Is FILE-NAME under the directory ROOT?

Return nil if there is no match or the part of the file-name
which was not under the docroot."
  (and root
       (file-directory-p root)
       (let* ((true-name
               (file-truename
                (expand-file-name file-name)))
              (root-dir
               (directory-file-name
                (expand-file-name root))))
         (let ((docroot-match-index
                (compare-strings
                 root-dir 0 (length root-dir)
                 true-name 0 (length true-name))))
           ;; If the compare-value is less than 0 we matched
           ;; and we have extra characters in the
           ;; true-name...  we *should* have extra
           ;; characters because otherwise we'd be referring
           ;; to the docroot.
           (when (< docroot-match-index 0)
             (substring
              true-name
              ;; -2 here because of index 0 *and* needing the
              ;; -leading slash
              (- (abs docroot-match-index) 1)
              (length true-name)))))))

(defun creole/get-file (filename)
  "An exception based FILENAME lookup.

Either loads the FILENAME in a buffer (but does not select it) or
errors 'file-error.

The FILENAME is expanded and `file-truename'd first."
  (let ((file-path
         (ignore-errors
           (file-truename (expand-file-name filename)))))
    (if (not (file-exists-p file-path))
        (signal 'file-error (format "No such file %s" file-path))
      (find-file-noselect file-path))))

(defun creole/expand-item-value (item &optional docroot)
  "Expand ITEM to be a value.

If ITEM begins with a file-name identifying character then try
and resolve the ITEM as a file-name, optionally under the
DOCROOT.

Return a cons cell with the `car' identifying the type, one of:

 :link     to indicate a linkable file-name
 :string   to indicate the raw data

and the `cdr' being the expanded string."
  (save-match-data
    (if (string-match
         (rx bol (or "./" "/" "~") (* any))
         item)
        ;; file-name templating has been requested
        ;; Check if we have a docroot that works
        (let* ((path-info (creole/file-under-root-p item docroot)))
          (if path-info
              ;; The file is linkable so return the template with the
              ;; docroot-ed true-name
              (cons :link path-info)
            ;; No workable docroot so return either the text of the
            ;; file (if it exists) or just the filename
            (condition-case err
                (with-current-buffer (creole/get-file item)
                  (cons :string
                        (buffer-substring
                         (point-min)
                         (point-max))))
              ;; FIXME - I'd like this to be file-error - why doesn't
              ;; that work???
              (error (cons :link item)))))
      ;; The item was not a file-name so just return it
      (cons :string item))))

(defun creole/wrap-buffer-text (start end &optional buffer)
  "Simply wrap the text of BUFFER (or the current buffer).

START is placed at the start of the BUFFER and END is placed at
the end of the BUFFER."
  (let ((buf (or buffer (current-buffer))))
    (with-current-buffer buf
      (save-excursion
        (goto-char (point-min))
        (insert start)
        (goto-char (point-max))
        (insert end)))))

(defun creole/insert-template (key
                                position
                                docroot
                                link-template
                                embed-template
                                &optional docroot-alias)
  "Insert either the LINK-TEMPLATE or the EMBED-TEMPLATE.

KEY specifies a value that is expanded with
`creole/expand-item-value', possibly with DOCROOT.

Whether we're a :link or a :string will cause either the
LINK-TEMPLATE or the EMBED-TEMPLATE to be inserted at the marker
POSITION.

If DOCROOT-ALIAS is specified and the :link template is used then
the filename is concatenated with that."
  (save-excursion
    (when key
      (goto-char position)
      (let ((value (creole/expand-item-value key docroot)))
        (case (car value)
          (:link
           (insert
            (format
             link-template
             (if docroot-alias
                 (concat docroot-alias (cdr value))
                 (cdr value)))))
          (:string
           (insert
            (format embed-template (cdr value)))))))))

(defcustom creole-css-color-type "#000000"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-default "#000000"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-whitespace-empty "#b22222"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-regexp-grouping-construct "#000000"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-builtin "#483d8b"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-function-name "#0000ff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-doc "#8b2252"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-string "#8b2252"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-variable-name "#a0522d"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-constant "#008b8b"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-keyword "#a020f0"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-comment "#b22222"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-whitespace-space "#d3d3d3"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-color-comment-delimiter "#b22222"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-default "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-whitespace-empty "#ffff00"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-regexp-grouping-construct "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-regexp-grouping-backslash "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-builtin "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-function-name "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-doc "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-string "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-variable-name "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-constant "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-keyword "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-comment "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-whitespace-space "#ffffe0"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defcustom creole-css-background-comment-delimiter "#ffffff"
  "A custom color to be used for CSS style rendering."
  :group 'creole
  :type '(string))

(defun creole-css-list-to-style-decl (css-list)
  "Make the CSS-LIST into an HTML STYLE decl.

A CSS-LIST should look something like this:

 ((default \"default\" . \"{ ... CSS declarations ... }\")
  (font-lock-string-face \"string\" . \"{ ... CSS declarations ... }\")
  (font-lock-type-face \"type\" . \"{ ... CSS declarations ... }\")
  (font-lock-function-name-face \"function-name\" . \"{ ... CSS declarations ... }\")
  (font-lock-keyword-face \"keyword\" . \"{ ... CSS declarations ... }\")
  (font-lock-comment-face \"comment\" . \"{ ... CSS declarations ... }\")
  (whitespace-space \"whitespace-space\" . \"{ ... CSS declarations ... }\")
  (font-lock-comment-delimiter-face \"comment-delimiter\" . \"{ ... CSS declarations ... }\"))

Each element of the list contains the descriptive part of a CSS
class declaration.

This is from `hfy-sprintf-stylesheet' which is part of
`htmlfontify'."
  (mapconcat
   (lambda (style)
     (format
      "span.%s   %s\nspan.%s a %s\n%s\n"
      (cadr style) (cddr style)
      (cadr style) (hfy-link-style (cddr style))
      ;; Add in our own colors - just add nothing
      ;; if we don't have customization for it
      (condition-case err
          (let ((css-value
                 (symbol-value
                  (intern
                   (concat
                    "creole-css-color-"
                    (cadr style))))))
            (if css-value
                (format
                 "span.%s { color: %s; }\n"
                 (cadr style)
                 css-value)))
        (void-variable ""))))
   css-list
   "\n"))

(defun creole-moustache (template variables)
  "Moustache replace in TEMPLATE with VARIABLES.

Eg:

  (creole-moustache
    \"<textarea>{{text}}</textarea>\"
    '((text . \"this is my text\")))

  =>  \"<textarea>this is my text</textarea>\""
  (replace-regexp-in-string
   (rx "{{"
       (group (+ (in alphanumeric "_-")))
       "}}")
   (lambda (m)
     (let* ((expansion (match-string 1 m))
            (var (intern expansion))
            (pair (assoc var variables)))
       (if pair
           (cdr pair)
         (concat "{{" expansion "}}"))))
   template
   nil
   t))

(defun creole-list-text-properties (buffer property predicate)
  "List all the values for PROPERTY in BUFFER.

PREDICATE is used to merge the properties."
  (with-current-buffer buffer
    (save-excursion
      (goto-char (point-min))
      (let* ((lst (list))
             (p (next-single-property-change
                 (point-min)
                 :css-list
                 (current-buffer)
                 (point-max))))
        (while (not (equal p (point-max)))
          (let ((prop (get-text-property p property)))
            (when prop
              (setq lst
                    (merge
                     'list
                     lst prop
                     predicate))))
            (goto-char (+ 1 p))
            (setq p (next-single-property-change
                     (point)
                     property
                     (current-buffer)
                     (point-max))))
          lst))))

;;;###autoload
(defun* creole-wiki (source
                     &key
                     destination
                     structure-transform-fn
                     (htmlfontify t)
                     (htmlfontify-style t)
                     body-header
                     body-footer
                     variables
                     docroot
                     docroot-alias
                     css
                     javascript
                     meta
                     other-link
                     doctype)
  "Export WikiCreole SOURCE into HTML.

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
"
  (interactive "fCreole file: ")
  (let* (file-opened ;; a flag to indicate whether we opened a file or not
         (source-buffer
          ;; Detect what sort of source we have
          (cond
           ((bufferp source)
            source)
           ((string-match (rx bol (or "/" "~") (* any)) source)
            (creole/get-file source))
           (t
            (with-current-buffer (generate-new-buffer "* creole-source *")
              (insert source)
              (current-buffer)))))
         (html-buffer
          (cond
           ((bufferp destination)
            destination)
           ((stringp destination)
            (get-buffer-create destination))
           (t
            (get-buffer-create "*creole-html*")))))

    ;; Export the creole to the result buffer
    (creole-html source-buffer html-buffer
                 :do-font-lock htmlfontify
                 :structure-transform-fn structure-transform-fn)

    ;; Now a bunch of other transformations on the result buffer
    (with-current-buffer html-buffer
      (let* ((creole-text
              (with-current-buffer source-buffer
                (buffer-substring (point-min)(point-max))))
             ;; We should let users specify more variables in the
             ;; call to creole-wiki?
             (vars (append `((text . ,creole-text)) variables)))

        ;; Insert the BODY header and footer
        (when body-header
          (let ((hdr (creole/expand-item-value body-header)))
            (when (eq (car hdr) :string)
              (goto-char (point-min))
              (insert
               (creole-moustache
                (cdr hdr)
                vars)))))

        (when body-footer
          (let ((ftr (creole/expand-item-value body-footer)))
            (when (eq (car ftr) :string)
               (goto-char (point-max))
               (insert
                (creole-moustache
                 (cdr ftr)
                 vars)))))

        ;; Now wrap everything we have so far with the BODY tag
        (creole/wrap-buffer-text "<body>\n" "</body>\n")

        ;; Now stuff that should go in a header
        (when (or css javascript meta other-link
                  (and htmlfontify
                       htmlfontify-style
                       (next-single-property-change
                        (point-min)
                        :css-list
                        (current-buffer)
                        (point-max))))
          (let (head-marker)
            (goto-char (point-min))
            (insert "<head>\n")
            (let ((creole-doc-title (assoc 'heading1 creole-structured)))
              (when creole-doc-title
                (insert (format "<title>%s</title>\n" (cdr creole-doc-title)))))
            (setq head-marker (point-marker))
            (insert "</head>\n")
            ;; First the CSS
            (loop for ss in css
               do (creole/insert-template
                   ss
                   head-marker
                   docroot
                   "<link rel='stylesheet' href='%s' type='text/css'/>\n"
                   "<style>\n%s\n</style>\n"
                   docroot-alias))
            ;; Now the JS
            (loop for js in javascript
               do (creole/insert-template
                   js
                   head-marker
                   docroot
                   "<script src='%s' language='Javascript'></script>\n"
                   "<script>
//<!--
%s
//-->
</script>
"
                   docroot-alias))
            ;; Now meta
            (creole/insert-template
             meta
             head-marker
             docroot
             "<meta %s/>\n"
             "<meta %s/>\n")
            (creole/insert-template
             other-link
             head-marker
             docroot
             "<link %s/>\n"
             "<link %s/>\n")

            ;; Find any styles that are embedded
            (if (and htmlfontify htmlfontify-style)
                (let ((css (remove-duplicates
                            (creole-list-text-properties
                             (current-buffer)
                             :css-list
                             (lambda (a b) (string< (cadr a) (cadr b))))
                            :test (lambda (a b) (string= (cadr a) (cadr b))))))
                    (save-excursion
                      (goto-char head-marker)
                      (insert
                       "<style>\n"
                       (creole-css-list-to-style-decl css)
                       "\n</style>\n"))))))

        ;; Wrap the whole thing in the DOCTYPE and the HTML tag
        (creole/wrap-buffer-text
         (cond
           ((eq doctype 'html5) "<!DOCTYPE html>\n<html>")
           ((eq doctype 'xhtml) "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">\n")
           ((stringp doctype) (concat doctype "<html>\n"))
           ((eq doctype nil) "<html>\n"))
         "</html>\n")))

    ;; Should we output the whole thing to the default output stream?
    (when (eq destination t)
      (with-current-buffer html-buffer
        (princ (buffer-substring (point-min)(point-max)))))

    (when (called-interactively-p 'any)
      (switch-to-buffer html-buffer))

    (when file-opened
      (kill-buffer source-buffer))

    ;; Return the destination buffer
    html-buffer))


;; Useful functions

(defun creole-directory-list (directory-name &optional make-links)
  "WikiCreole format a table of files in DIRECTORY-NAME.

MAKE-LINKS causes the files to be WikiCreole links."
  (loop for filename in (directory-files directory-name)
        if (not (or (equal filename ".")
                    (equal filename "..")))
        concat
        (let* ((fq (expand-file-name filename directory-name))
               (fa (file-attributes fq))
               (timestr
                (apply 'format
                       "%04d-%02d-%02d %02d:%02d"
                       (let ((dt (decode-time (elt fa 5))))
                         (list (elt dt 5)
                               (elt dt 4)
                               (elt dt 3)
                               (elt dt 2)
                               (elt dt 1))))))
          (format
           "|%s|%s|%s|\n"
           (if make-links
               (format "[[%s]]" filename)
             filename)
           timestr
           (elt fa 7)))))

(provide 'creole)

;;; creole.el ends here
