
;;; csharp-mode.el --- C# mode derived mode

;; Author     : Dylan R. E. Moonfire (original)
;; Maintainer : Jostein Kjønigsen <jostein@gmail.com>
;; Created    : Feburary 2005
;; Modified   : November 2014
;; Version    : 0.8.9
;; Keywords   : c# languages oop mode
;; Package-Version: 20150315.345
;; X-URL      : https://github.com/josteink/csharp-mode
;; Last-saved : <2014-Nov-29 13:56:00>

;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;;
;;    This is a major mode for editing C# code. It performs automatic
;;    indentation of C# syntax; font locking; and integration with
;;    imenu.el.
;;
;;    csharp-mode requires CC Mode 5.30 or later.  It works with
;;    cc-mode 5.31.3, which is current at this time.
;;
;; Features:
;;
;;   - font-lock and indent of C# syntax including:
;;       all c# keywords and major syntax
;;       attributes that decorate methods, classes, fields, properties
;;       enum types
;;       #if/#endif  #region/#endregion
;;       instance initializers
;;       anonymous functions and methods
;;       verbatim literal strings (those that begin with @)
;;       generics
;;
;;   - automagic code-doc generation when you type three slashes.
;;
;;   - compatible with electric-pair-mode for intelligent insertion
;;     of matched braces, quotes, etc.
;;
;;   - imenu integration - generates an index of namespaces, classes,
;;     interfaces, methods, and properties for easy navigation within
;;     the buffer.
;;


;; Installation instructions
;; --------------------------------
;;
;; Put csharp-mode.el somewhere in your load path, optionally byte-compile
;; it, and add the following to your .emacs file:
;;
;;   (autoload 'csharp-mode "csharp-mode" "Major mode for editing C# code." t)
;;   (setq auto-mode-alist
;;      (append '(("\\.cs$" . csharp-mode)) auto-mode-alist))
;;
;;
;; Optionally, define and register a mode-hook function. To do so, use
;; something like this in your .emacs file:
;;
;;   (defun my-csharp-mode-fn ()
;;      "function that runs when csharp-mode is initialized for a buffer."
;;      (turn-on-auto-revert-mode)
;;      (setq indent-tabs-mode nil)
;;      ...insert more code here...
;;      ...including any custom key bindings you might want ...
;;   )
;;   (add-hook  'csharp-mode-hook 'my-csharp-mode-fn t)
;;
;;
;;  General
;;  ----------------------------
;;
;;  Mostly C# mode will "just work."  Use `describe-mode' to see the
;;  default keybindings and the highlights of the mode.
;;
;;
;;  imenu integration
;;  -----------------------------
;;
;;  This should just work. For those who don't know what imenu is, it
;;  allows navigation to different points within the file from an
;;  "Index" menu, in the window's menubar.  csharp-mode computes the
;;  menu containing the namespaces, classes, methods, and so on, in the
;;  buffer.  This happens at the time the file is loaded; for large
;;  files it takes a bit of time to complete the scan.  If you don't
;;  want this capability, set `csharp-want-imenu' to nil.
;;
;;


;;; Known Bugs:
;;
;;   The imenu scan is text-based and naive. For example, if you
;;   intersperse comments between the name of a class/method/namespace,
;;   and the curly brace, the scan will not recognize the thing being
;;   declared. This is fixable - would need to extract the buffer
;;   substring then remove comments before doing the regexp checks - but
;;   it would make the scan much slower.  Also, the scan doesn't deal
;;   with preproc symbol definitions and #if/#else. Those things are
;;   invisible to the scanner csharp-mode uses to build the imenu menu.
;;
;;   Leading identifiers are no longer being fontified, for some reason.
;;   See matchers-before. (Not sure this is still a problem - 19 may
;;   2011 DPC)
;;
;;   Method names with a preceding attribute are not fontified.
;;
;;   The symbol followng #if is not fontified.  It should be treated like
;;   define and get font-lock-variable-name-face .
;;
;;   This code doesn't seem to work when you compile it, then
;;   load/require in the emacs file. You will get an error (error
;;   "`c-lang-defconst' must be used in a file") which happens because
;;   cc-mode doesn't think it is in a buffer while loading directly
;;   from the init. However, if you call it based on a file extension,
;;   it works properly. Interestingly enough, this doesn't happen if
;;   you don't byte-compile cc-mode.
;;
;;
;;
;;  Todo:
;;
;;   imenu should scan for and find delegates and events, in addition
;;   to the classes, structs, properties and methods it does currently.
;;
;;   Get csharp-mode.el accepted as part of the emacs standard distribution.
;;   Must contact monnier at iro.umontreal.ca to make this happen.
;;
;;   Add refactoring capabilities?
;;     - extract as method - extract a block of code into a method
;;     - extract as Func<> - extract a block of code into an Action<T>
;;
;;   More code-gen power:
;;     - interface implementation - I think would require csharp-shell
;;
;;
;;  Acknowledgements:
;;
;;    Thanks to Alan Mackenzie and Stefan Monnier for answering questions
;;    and making suggestions. And to Trey Jackson for sharing his
;;    knowledge of emacs lisp.
;;
;;

;;; Versions:
;;
;;    0.1.0 - Initial release.
;;    0.2.0 - Fixed the identification on the "enum" keyword.
;;          - Fixed the font-lock on the "base" keyword
;;    0.3.0 - Added a regex to fontify attributes. It isn't the
;;            the best method, but it handles single-like attributes
;;            well.
;;          - Got "super" not to fontify as a keyword.
;;          - Got extending classes and interfaces to fontify as something.
;;    0.4.0 - Removed the attribute matching because it broke more than
;;            it fixed.
;;          - Corrected a bug with namespace not being properly identified
;;            and treating the class level as an inner object, which screwed
;;            up formatting.
;;          - Added "partial" to the keywords.
;;    0.5.0 - Found bugs with compiled cc-mode and loading from init files.
;;          - Updated the eval-when-compile to code to let the mode be
;;            compiled.
;;    0.6.0 - Added the c-filter-ops patch for 5.31.1 which made that
;;            function in cc-langs.el unavailable.
;;          - Added a csharp-lineup-region for indention #region and
;;            #endregion block differently.
;;    0.7.0 - Added autoload so update-directory-autoloads works
;;            (Thank you, Nikolaj Schumacher)
;;          - Fontified the entire #region and #endregion lines.
;;          - Initial work to get get, set, add, remove font-locked.
;;    0.7.1 - Added option to indent #if/endif with code
;;          - Fixed c-opt-cpp-prefix defn (it must not include the BOL
;;            char (^).
;;          - proper fontification and indent of classes that inherit
;;            (previously the colon was confusing the parser)
;;          - reclassified namespace as a block beginner
;;          - removed $ as a legal symbol char - not legal in C#.
;;          - added struct to c-class-decl-kwds so indent is correct
;;            within a struct.
;;    0.7.2 - Added automatic codedoc insertion.
;;    0.7.3 - Instance initializers (new Type { ... } ) and
;;            (new Type() { ...} ) are now indented properly.
;;          - proper fontification and indent of enums as brace-list-*,
;;            including special treatment for enums that explicitly
;;            inherit from an int type. Previously the colon was
;;            confusing the parser.
;;          - proper fontification of verbatim literal strings,
;;            including those that end in slash. This edge case was not
;;            handled at all before; it is now handled correctly.
;;          - code cleanup and organization; removed the formfeed.
;;          - intelligent curly-brace insertion with
;;            `csharp-insert-open-brace'
;;    0.7.4 - added a C# style
;;          - using is now a keyword and gets fontified correctly
;;          - fixed a bug that had crept into the codedoc insertion.
;;    0.7.5 - now fontify namespaces in the using statements. This is
;;            done in the csharp value for c-basic-matchers-before .
;;          - also fontify the name following namespace decl.
;;            This is done in the csharp value for c-basic-matchers-after .
;;          - turn on recognition of generic types. They are now
;;            fontified correctly.
;;          - <> are now treated as syntactic parens and can be jumped
;;            over with c-forward-sexp.
;;          - Constructors are now fontified.
;;          - Field/Prop names inside object initializers are now fontified.
;;
;;    0.7.7 - relocate running c-run-mode-hooks to the end of
;;            csharp-mode, to allow user to modify key bindings in a
;;            hook if he doesn't like the defaults.
;;
;;    0.7.8 - redefine csharp-log to insert timestamp.
;;          - Fix byte-compile errors on emacs 23.2 ?  Why was
;;            c-filter-ops duplicated here?  What was the purpose of its
;;            presence here, I am not clear.
;;
;;    0.8.0 - include flymake magic into this module.
;;          - include yasnippet integration
;;
;;    0.8.2 2011 April DPC
;;          - small tweaks; now set a one-time bool for flymake installation
;;          - some doc updates on flymake
;;
;;    0.8.3 2011 May 17  DPC
;;          - better help on csharp-mode
;;          - csharp-move-* functions for manual navigation.
;;          - imenu integration for menu-driven navigation - navigate to
;;            named methods, classes, etc.
;;          - adjusted the flymake regexp to handle output from fxcopcmd,
;;            and extended the help to provide examples how to use this.
;;
;;    0.8.4 DPC 2011 May 18
;;          - fix a basic bug in the `csharp-yasnippet-fixup' fn.
;;
;;    0.8.5 DPC 2011 May 21
;;          - imenu: correctly parse Properties that are part of an
;;            explicitly specified interface. Probably need to do this
;;            for methods, too.
;;          - fontify the optional alias before namespace in a using (import).
;;          - Tweak open-curly magic insertion for object initializers.
;;          - better fontification of variables and references
;;          - "sealed" is now fontified as a keyword
;;          - imenu: correctly index ctors that call this or base.
;;          - imenu: correctly index Extension methods (this System.Enum e)
;;          - imenu: correctly scan  method params tagged with out, ref, params
;;          - imenu scan: now handle curlies within strings.
;;          - imenu: split menus now have better labels, are sorted correctly.
;;
;;    0.8.6 DPC 2011 May ??
;;          - extern keyword
;;
;;    0.8.7 2014 November 29
;;          - Fix broken cl-dependency in emacs24.4 and defadvice for tooltips.
;;
;;    0.8.8 2014 December 3
;;          - Fix broken byte-compile.
;;          - Add extra C# keywords.
;;          - Call prog-mode hooks.
;;
;;    0.8.9 2015 March 15
;;          - (Re)add compilation-mode support for msbuild and xbuild.
;;

(require 'cc-mode)

;; cc-defs in emacs 24.4 depends on cl-macroexpand-all, but does not load 'cl itself.
(require 'cl)

;; ==================================================================
;; c# upfront stuff
;; ==================================================================

;; This is a copy of the function in cc-mode which is used to handle the
;; eval-when-compile which is needed during other times.
;;
;; NB: I think this is needed to satisfy requirements when this module
;; calls `c-lang-defconst'. (DPC)

;; (defun c-filter-ops (ops opgroup-filter op-filter &optional xlate)
;;   ;; See cc-langs.el, a direct copy.
;;   (unless (listp (car-safe ops))
;;     (setq ops (list ops)))
;;   (cond ((eq opgroup-filter t)
;;          (setq opgroup-filter (lambda (opgroup) t)))
;;         ((not (functionp opgroup-filter))
;;          (setq opgroup-filter `(lambda (opgroup)
;;                                  (memq opgroup ',opgroup-filter)))))
;;   (cond ((eq op-filter t)
;;          (setq op-filter (lambda (op) t)))
;;         ((stringp op-filter)
;;          (setq op-filter `(lambda (op)
;;                             (string-match ,op-filter op)))))
;;   (unless xlate
;;     (setq xlate 'identity))
;;   (c-with-syntax-table (c-lang-const c-mode-syntax-table)
;;     (delete-duplicates
;;      (mapcan (lambda (opgroup)
;;                (when (if (symbolp (car opgroup))
;;                          (when (funcall opgroup-filter (car opgroup))
;;                            (setq opgroup (cdr opgroup))
;;                            t)
;;                        t)
;;                  (mapcan (lambda (op)
;;                            (when (funcall op-filter op)
;;                              (let ((res (funcall xlate op)))
;;                                (if (listp res) res (list res)))))
;;                          opgroup)))
;;              ops)
;;      :test 'equal)))




;; These are only required at compile time to get the sources for the
;; language constants.  (The load of cc-fonts and the font-lock
;; related constants could additionally be put inside an
;; (eval-after-load "font-lock" ...) but then some trickery is
;; necessary to get them compiled.)

(eval-when-compile
  (let ((load-path
         (if (and (boundp 'byte-compile-dest-file)
                  (stringp byte-compile-dest-file))
             (cons (file-name-directory byte-compile-dest-file) load-path)
           load-path)))
    (load "cc-mode" nil t)
    (load "cc-fonts" nil t)
    (load "cc-langs" nil t)))

(eval-and-compile
  ;; ==================================================================
  ;; constants used in this module
  ;; ==================================================================

  (defconst csharp-enum-decl-re
    (concat
     "\\<enum[ \t\n\r\f\v]+"
     "\\([[:alpha:]_][[:alnum:]_]*\\)"
     "[ \t\n\r\f\v]*"
     "\\(:[ \t\n\r\f\v]*"
     "\\("
     (c-make-keywords-re nil
			 (list "sbyte" "byte" "short" "ushort" "int" "uint" "long" "ulong"))
     "\\)"
     "\\)?")
    "Regex that captures an enum declaration in C#"
    )

  ;; ==================================================================

  ;; Make our mode known to the language constant system.  Use Java
  ;; mode as the fallback for the constants we don't change here.
  ;; This needs to be done also at compile time since the language
  ;; constants are evaluated then.
  (c-add-language 'csharp-mode 'java-mode))

;; ==================================================================
;; end of c# upfront stuff
;; ==================================================================











;; ==================================================================
;; csharp-mode utility and feature defuns
;; ==================================================================

(defun csharp--at-vsemi-p (&optional pos)
  "Determines if there is a virtual semicolon at POS or point.
It returns t if at a position where a virtual-semicolon is.
Otherwise nil.

This is the C# version of the function. It gets set into
the variable `c-at-vsemi-p-fn'.

A vsemi is a cc-mode concept implying the end of a statement,
where no actual end-of-statement signifier character ( semicolon,
close-brace) appears.  The concept is used to allow proper
indenting of blocks of code: Where a vsemi appears, the following
line will not indent further.

A vsemi appears in 2 cases in C#:

 - after an attribute that decorates a class, method, field, or
   property.

 - in an object initializer, before the open-curly?

An example of the former is  [WebMethod] or [XmlElement].

Providing this function allows the indenting in csharp-mode
to work properly with code that includes attributes.

"
  (save-excursion
    (let ((pos-or-point (progn (if pos (goto-char pos)) (point))))

      (cond

       ;; before open curly in object initializer. new Foo* { }
       ((and (looking-back
              (concat "\\<new[ \t\n\f\v\r]+"
              "\\(?:[A-Za-z_][[:alnum:]]*\\.\\)*"
              "[A-Za-z_][[:alnum:]]*[\ t\n\f\v\r]*"))
             (looking-at "[ \t\n\f\v\r]*{"))
        t)

       ;; put a vsemi after an attribute, as with
       ;;   [XmlElement]
       ;; Except when the attribute is used within a line of code, as
       ;; specifying something for a parameter.
       ((c-safe (backward-sexp) t)
        (cond
           ((re-search-forward
             (concat
              "\\(\\["
              "[ \t\n\r\f\v]*"
              "\\("
              "\\(?:[A-Za-z_][[:alnum:]]*\\.\\)*"
              "[A-Za-z_][[:alnum:]]*"
              "\\)"
              "[^]]*\\]\\)"
              )
             (1+ pos-or-point) t)

             (c-safe (backward-sexp))
             (c-backward-syntactic-ws)
             (cond

              ((eq (char-before) 93) ;; close sq brace (a previous attribute)
               (csharp--at-vsemi-p (point))) ;; recurse

              ((or
                (eq (char-before) 59) ;; semicolon
                (eq (char-before) 123) ;; open curly
                (eq (char-before) 125)) ;; close curly
               t)

              ;; attr is used within a line of code
              (t nil)))

           (t nil)))

        (t nil))
      )))




(defun csharp-lineup-region (langelem)
  "Indent all #region and #endregion blocks inline with code while
retaining normal column-zero indention for #if and the other
processing blocks.

To use this indenting just put the following in your emacs file:
   (c-set-offset 'cpp-macro 'csharp-lineup-region)

An alternative is to use `csharp-lineup-if-and-region'.
"

  (save-excursion
    (back-to-indentation)
    (if (re-search-forward "#\\(end\\)?region" (c-point 'eol) [0]) 0  [0])))





(defun csharp-lineup-if-and-region (langelem)

"Indent all #region/endregion blocks and #if/endif blocks inline
with code while retaining normal column-zero indention for any
other processing blocks.

To use this indenting just put the following in your emacs file:
  (c-set-offset 'cpp-macro 'csharp-lineup-if-and-region)

Another option is to use `csharp-lineup-region'.

"
  (save-excursion
    (back-to-indentation)
    (if (re-search-forward "#\\(\\(end\\)?\\(if\\|region\\)\\|else\\)" (c-point 'eol) [0]) 0  [0])))




  (defun csharp-in-literal (&optional lim detect-cpp)
    "Return the type of literal point is in, if any.
Basically this works like `c-in-literal' except it doesn't
use or fill the cache (`c-in-literal-cache').

The return value is a symbol: `c' if in a C-style comment, `c++'
if in a C++ style comment, `string' if in a string literal,
`pound' if DETECT-CPP is non-nil and in a preprocessor line, or
nil if somewhere else.  Optional LIM is used as the backward
limit of the search.  If omitted, or nil, `c-beginning-of-syntax'
is used.

Note that this function might do hidden buffer changes.  See the
comment at the start of cc-engine.el for more info."

    (let ((rtn
           (save-excursion
             (let* ((pos (point))
                    (lim (or lim (progn
                                   (c-beginning-of-syntax)
                                   (point))))
                    (state (parse-partial-sexp lim pos)))
               (csharp-log 4 "parse lim(%d) state: %s" lim (prin1-to-string state))
               (cond
                ((elt state 3)
                 (csharp-log 4 "in literal string (%d)" pos)
                 'string)
                ((elt state 4)
                 (csharp-log 4 "in literal comment (%d)" pos)
                 (if (elt state 7) 'c++ 'c))
                ((and detect-cpp (c-beginning-of-macro lim)) 'pound)
                (t nil))))))
      rtn))


(defun csharp-is-square-parentasis-block-p ()
  "Attempts to safely assess if the current point is at the opening of
a square parentasis block [ ... ]."
  (let* ((start (point)) ;; variables used to hold our position, so that we know that
	 (end))          ;; our code isn't stuck trying to look for a non-existant sexp.
    (and (eq (char-after) 91) ;; open square
	 (while (and (eq (char-after) 91)
		     (not (eq start end)))
	   (c-safe (c-forward-sexp 1))
	   (setq end (point)))
	 (eq (char-before) 93))) ;; close square
  )



;; ==================================================================
;; end of csharp-mode utility and feature defuns
;; ==================================================================



;; ==================================================================
;; c# values for "language constants" defined in cc-langs.el
;; ==================================================================

(c-lang-defconst c-at-vsemi-p-fn
  csharp 'csharp--at-vsemi-p)


;; This c-opt-after-id-concat-key is a regexp that matches
;; dot.  In other words: "\\(\\.\\)"
;; Not sure why this needs to be so complicated.
;; This const is now internal (obsolete); need to move to
;; c-after-id-concat-ops.  I don't yet understand the meaning
;; of that variable, so for now. . .  .

;; (c-lang-defconst c-opt-after-id-concat-key
;;   csharp (if (c-lang-const c-opt-identifier-concat-key)
;;              (c-lang-const c-symbol-start)))

(c-lang-defconst c-opt-after-id-concat-key
  csharp "[[:alpha:]_]" )




;; The matchers elements can be of many forms.  It gets pretty
;; complicated.  Do a describe-variable on font-lock-keywords to get a
;; description.  (Why on font-lock-keywords? I don't know, but that's
;; where you get the help.)
;;
;; Aside from the provided documentation, the other option of course, is
;; to look in the source code as an example for what to do.  The source
;; in cc-fonts uses a defun c-make-font-lock-search-function to produce
;; most of the matchers.  Called this way:
;;
;;   (c-make-font-lock-search-function  regexp '(A B c))
;;
;; The REGEXP is used in re-search-forward, and if there's a match, then
;; A is called within a save-match-data. If B and C are non-nil, they
;; are called as pre and post blocks, respecitvely.
;;
;; Anyway the c-make-font-lock-search-function works for a single regex,
;; but more complicated scenarios such as those intended to match and
;; fontify object initializers, call for a hand-crafted lambda.
;;
;; The object initializer is special because matching on it must
;; allow nesting.
;;
;; In c#, the object initializer block is used directly after a
;; constructor, like this:
;;
;;     new MyType
;;     {
;;        Prop1 = "foo"
;;     }
;;
;; csharp-mode needs to fontify the properties in the
;; initializer block in font-lock-variable-name-face. The key thing is
;; to set the text property on the open curly, using type c-type and
;; value c-decl-id-start. This apparently allows `parse-partial-sexp' to
;; do the right thing, later.
;;
;; This simple case is easy to handle in a regex, using the basic
;; `c-make-font-lock-search-function' form.  But the general syntax for a
;; constructor + object initializer in C# is more complex:
;;
;;     new MyType(..arglist..) {
;;        Prop1 = "foo"
;;     }
;;
;; A simple regex match won't satisfy here, because the ..arglist.. can
;; be anything, including calls to other constructors, potentially with
;; object initializer blocks. This may nest arbitrarily deeply, and the
;; regex in emacs doesn't support balanced matching.  Therefore there's
;; no way to match on the "outside" pair of parens, to find the relevant
;; open curly.  What's necessary is to do the match on "new MyType" then
;; skip over the sexp defined by the parens, then set the text property on
;; the appropriate open-curly.
;;
;; To make that happen, it's good to have insight into what the matcher
;; really does.  The output of `c-make-font-lock-search-function' before
;; byte-compiling, is:
;;
;; (lambda (limit)
;;   (let ((parse-sexp-lookup-properties
;;          (cc-eval-when-compile
;;            (boundp 'parse-sexp-lookup-properties))))
;;     (while (re-search-forward REGEX limit t)
;;       (unless
;;           (progn
;;             (goto-char (match-beginning 0))
;;             (c-skip-comments-and-strings limit))
;;         (goto-char (match-end 0))
;;         (progn
;;           B
;;           (save-match-data A)
;;           C ))))
;;   nil)
;;
;; csharp-mode uses this hand-crafted form of a matcher to handle the
;; general case for constructor + object initializer, within
;; `c-basic-matchers-after' .
;;




;; (defun c-make-font-lock-search-function (regexp &rest highlights)
;;     ;; This function makes a byte compiled function that works much like
;;     ;; a matcher element in `font-lock-keywords'.  It cuts out a little
;;     ;; bit of the overhead compared to a real matcher.  The main reason
;;     ;; is however to pass the real search limit to the anchored
;;     ;; matcher(s), since most (if not all) font-lock implementations
;;     ;; arbitrarily limits anchored matchers to the same line, and also
;;     ;; to insulate against various other irritating differences between
;;     ;; the different (X)Emacs font-lock packages.
;;     ;;
;;     ;; REGEXP is the matcher, which must be a regexp.  Only matches
;;     ;; where the beginning is outside any comment or string literal are
;;     ;; significant.
;;     ;;
;;     ;; HIGHLIGHTS is a list of highlight specs, just like in
;;     ;; `font-lock-keywords', with these limitations: The face is always
;;     ;; overridden (no big disadvantage, since hits in comments etc are
;;     ;; filtered anyway), there is no "laxmatch", and an anchored matcher
;;     ;; is always a form which must do all the fontification directly.
;;     ;; `limit' is a variable bound to the real limit in the context of
;;     ;; the anchored matcher forms.
;;     ;;
;;     ;; This function does not do any hidden buffer changes, but the
;;     ;; generated functions will.  (They are however used in places
;;     ;; covered by the font-lock context.)
;;
;;     ;; Note: Replace `byte-compile' with `eval' to debug the generated
;;     ;; lambda easier.
;;     (byte-compile
;;      `(lambda (limit)
;;         (let (;; The font-lock package in Emacs is known to clobber
;;               ;; `parse-sexp-lookup-properties' (when it exists).
;;               (parse-sexp-lookup-properties
;;                (cc-eval-when-compile
;;                  (boundp 'parse-sexp-lookup-properties))))
;;           (while (re-search-forward ,regexp limit t)
;;             (unless (progn
;;                       (goto-char (match-beginning 0))
;;                       (c-skip-comments-and-strings limit))
;;               (goto-char (match-end 0))
;;               ,@(mapcar
;;                  (lambda (highlight)
;;                    (if (integerp (car highlight))
;;                        (progn
;;                          (unless (eq (nth 2 highlight) t)
;;                            (error
;;                             "The override flag must currently be t in %s"
;;                             highlight))
;;                          (when (nth 3 highlight)
;;                            (error
;;                             "The laxmatch flag may currently not be set in %s"
;;                             highlight))
;;                          `(save-match-data
;;                             (c-put-font-lock-face
;;                              (match-beginning ,(car highlight))
;;                              (match-end ,(car highlight))
;;                              ,(elt highlight 1))))
;;                      (when (nth 3 highlight)
;;                        (error "Match highlights currently not supported in %s"
;;                               highlight))
;;                      `(progn
;;                         ,(nth 1 highlight)
;;                         (save-match-data ,(car highlight))
;;                         ,(nth 2 highlight))))
;;                  highlights))))
;;         nil))
;;     )


(c-lang-defconst c-basic-matchers-before
  csharp `(
           ;;;; Font-lock the attributes by searching for the
           ;;;; appropriate regex and marking it as TODO.
           ;;,`(,(concat "\\(" csharp-attribute-regex "\\)")
           ;;   0 font-lock-function-name-face)

           ;; Put a warning face on the opener of unclosed strings that
           ;; can't span lines.  Later font
           ;; lock packages have a `font-lock-syntactic-face-function' for
           ;; this, but it doesn't give the control we want since any
           ;; fontification done inside the function will be
           ;; unconditionally overridden.
           ,(c-make-font-lock-search-function
             ;; Match a char before the string starter to make
             ;; `c-skip-comments-and-strings' work correctly.
             (concat ".\\(" c-string-limit-regexp "\\)")
             '((c-font-lock-invalid-string)))


           ;; Fontify keyword constants.
           ,@(when (c-lang-const c-constant-kwds)
               (let ((re (c-make-keywords-re nil
                           (c-lang-const c-constant-kwds))))
                 `((eval . (list ,(concat "\\<\\(" re "\\)\\>")
                                 1 c-constant-face-name)))))


           ;; Fontify the namespaces that follow using statements.
           ;; This regex handles the optional alias, as well.
           ,`(,(concat
                "\\<\\(using\\)[ \t\n\f\v\r]+"
                "\\(?:"
                "\\([A-Za-z_][[:alnum:]]*\\)"
                "[ \t\n\f\v\r]*="
                "[ \t\n\f\v\r]*"
                "\\)?"
                "\\(\\(?:[A-Za-z_][[:alnum:]]*\\.\\)*[A-Za-z_][[:alnum:]]*\\)"
                "[ \t\n\f\v\r]*;")
              (2 font-lock-constant-face t t)
              (3 font-lock-constant-face))


           ;; Fontify all keywords except the primitive types.
           ,`(,(concat "\\<" (c-lang-const c-regular-keywords-regexp))
              1 font-lock-keyword-face)


           ;; Fontify leading identifiers as a reference? in fully
           ;; qualified names like "Foo.Bar".
           ,@(when (c-lang-const c-opt-identifier-concat-key)
               `((,(byte-compile
                    `(lambda (limit)
                       (csharp-log 3 "bmb reference? p(%d) L(%d)" (point) limit)
                       (while (re-search-forward
                               ,(concat "\\(\\<" ;; 1
                                        "\\("  ;; 2
                                        ;;"[A-Z]";; uppercase - assume upper = classname
                                        "[A-Za-z_]"  ;; any old
                                        "[A-Za-z0-9_]*" ;; old: (c-lang-const c-symbol-key)
                                        "\\)"
                                        "[ \t\n\r\f\v]*"
                                        "\\."   ;;(c-lang-const c-opt-identifier-concat-key)
                                        "[ \t\n\r\f\v]*"
                                        "\\)" ;; 1 ends
                                        "\\("
                                        "[[:alpha:]_][A-Za-z0-9_]*" ;; start of another symbolname
                                        "\\)"  ;; 3 ends
                                        )
                               limit t)
                         (csharp-log 3 "bmb ref? B(%d)" (match-beginning 0))
                         (unless (progn
                                   (goto-char (match-beginning 0))
                                   (c-skip-comments-and-strings limit))
                           (let* ((prefix  (match-string 2))
                                  (me1 (match-end 1))
                                  (first-char (string-to-char prefix))
                                  (is-upper (and (>= first-char 65)
                                                 (<= first-char 90))))
                             (csharp-log 3 "  - class/intf ref (%s)" prefix)
                             ;; only put face if not there already
                             (or (get-text-property (match-beginning 2) 'face)
                                 (c-put-font-lock-face (match-beginning 2)
                                                       (match-end 2)
                                                       (if is-upper
                                                           font-lock-type-face ;; it's a type!
                                                         font-lock-variable-name-face)))

                             (goto-char (match-end 3))
                             (c-forward-syntactic-ws limit)

                             ;; now, maybe fontify the thing afterwards, too
                             (let ((c (char-after)))
                               (csharp-log 3 "  - now lkg at c(%c)" c)

                               (cond

                                ((= c 40) ;; open paren
                                 (or (get-text-property (match-beginning 3) 'face)
                                     (c-put-font-lock-face (match-beginning 3)
                                                           (match-end 3)
                                                           font-lock-function-name-face))
                                 (goto-char (match-end 3)))

                                ;;  these all look like variables or properties
                                ((or (= c 59)  ;; semicolon
                                     (= c 91)  ;; open sq brack
                                     (= c 41)  ;; close paren
                                     (= c 44)  ;; ,
                                     (= c 33)  ;; !
                                     (= c 124) ;; |
                                     (= c 61)  ;; =
                                     (= c 43)  ;; +
                                     (= c 45)  ;; -
                                     (= c 42)  ;; *
                                     (= c 47)) ;; /
                                 (or (get-text-property (match-beginning 3) 'face)
                                     (c-put-font-lock-face (match-beginning 3)
                                                           (match-end 3)
                                                           font-lock-variable-name-face))
                                 (goto-char (match-end 3)))

                                (t
                                 (goto-char (match-end 1)))))))))))))

           ))



(c-lang-defconst c-basic-matchers-after
  csharp `(

           ;; option 1:
           ;;            ,@(when condition
           ;;                `((,(byte-compile
           ;;                     `(lambda (limit) ...
           ;;
           ;; option 2:
           ;;            ,`((lambda (limit) ...
           ;;
           ;; I don't know how to avoid the (when condition ...) in the
           ;; byte-compiled version.
           ;;
           ;; X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+X+

           ;; Case 1: invocation of constructor + maybe an object
           ;; initializer.  Some possible examples that satisfy:
           ;;
           ;;   new Foo ();
           ;;
           ;;   new Foo () { };
           ;;
           ;;   new Foo {  };
           ;;
           ;;   new Foo { Prop1= 7 };
           ;;
           ;;   new Foo {
           ;;     Prop1= 7
           ;;   };
           ;;
           ;;   new Foo {
           ;;     Prop1= 7,
           ;;     Prop2= "Fred"
           ;;   };
           ;;
           ;;   new Foo {
           ;;      Prop1= new Bar()
           ;;   };
           ;;
           ;;   new Foo {
           ;;      Prop1= new Bar { PropA = 5.6F }
           ;;   };
           ;;
           ,@(when t
               `((,(byte-compile
                    `(lambda (limit)
                        (let ((parse-sexp-lookup-properties
                               (cc-eval-when-compile
                                 (boundp 'parse-sexp-lookup-properties))))

                          (while (re-search-forward
                                  ,(concat "\\<new"
                                           "[ \t\n\r\f\v]+"
                                           "\\(\\(?:"
                                           (c-lang-const c-symbol-key)
                                           "\\.\\)*"
                                           (c-lang-const c-symbol-key)
                                           "\\)"
                                           )
                                  limit t)
                            (unless
                                (progn
                                  (goto-char (match-beginning 0))
                                  (c-skip-comments-and-strings limit))

                              (csharp-log 3 "ctor invoke? at %d" (match-beginning 1))

                              (save-match-data
                                ;; next thing could be: [] () <> or {} or nothing (semicolon, comma).

                                ;; fontify the typename
                                (c-put-font-lock-face (match-beginning 1)
                                                      (match-end 1)
                                                      'font-lock-type-face)

                                (goto-char (match-end 0))
                                (c-forward-syntactic-ws limit)
                                (if (eq (char-after) ?<) ;; ctor for generic type
                                    (progn
                                      (csharp-log 3 " - this is a generic type")
                                      ;; skip over <> safely
                                      (c-safe (c-forward-sexp 1) t)
                                      (c-forward-syntactic-ws)))

                                ;; now, could be [] or (..) or {..} or semicolon.

                                (csharp-log 3 " - looking for sexp")

                                (if (or
                                     (eq (char-after) ?{) ;; open curly
                                     (csharp-is-square-parentasis-block-p)
                                     (and (eq (char-after) 40) ;; open paren
                                          (c-safe (c-forward-sexp 1) t)))

                                    (progn
                                      ;; at this point we've jumped over any intervening s-exp,
                                      ;; like sq brackets or parens.
                                      (c-forward-syntactic-ws)
                                      (csharp-log 3 " - after fwd-syn-ws point(%d)" (point))
                                      (csharp-log 3 " - next char:  %c" (char-after))
                                      (if (eq (char-after) ?{)
                                          (let ((start (point))
                                                (end (if (c-safe (c-forward-sexp 1) t)
                                                         (point) 0)))
                                            (csharp-log 3 " -  open curly gets c-decl-id-start %d" start)
                                            (c-put-char-property start
                                                                 'c-type
                                                                 'c-decl-id-start)
                                            (goto-char start)
                                            (if (> end start)
                                                (progn
                                                  (forward-char 1) ;; step over open curly
                                                  (c-forward-syntactic-ws)
                                                  (while (> end (point))
                                                    ;; now, try to fontify/assign variables to any properties inside the curlies
                                                    (csharp-log 3 " - inside open curly  point(%d)" (point))
                                                    (csharp-log 3 " -   next char:  %c" (char-after))
                                                    ;; fontify each property assignment
                                                    (if (re-search-forward
                                                         (concat "\\(" (c-lang-const c-symbol-key) "\\)\\s*=")
                                                         end t)
                                                        (progn
                                                          (csharp-log 3 " -   found variable  %d-%d"
                                                                      (match-beginning 1)
                                                                      (match-end 1))
                                                          (c-put-font-lock-face (match-beginning 1)
                                                                                (match-end 1)
                                                                                'font-lock-variable-name-face)
                                                          (goto-char (match-end 0))
                                                          (c-forward-syntactic-ws)
                                                          ;; advance to the next assignment, if possible
                                                          (if (eq (char-after) ?@)
                                                              (forward-char 1))

                                                          (if (c-safe (c-forward-sexp 1) t)
                                                              (progn
                                                                (forward-char 1)
                                                                (c-forward-syntactic-ws))))

                                                      ;; else
                                                      (csharp-log 3 " -   no more assgnmts found")
                                                      (goto-char end)))))
                                            )))))

                              (goto-char (match-end 0))
                              )))
                        nil))
                    )))


           ;; Case 2: declaration of enum with or without an explicit
           ;; base type.
           ;;
           ;; Examples:
           ;;
           ;;  public enum Foo { ... }
           ;;
           ;;  public enum Foo : uint { ... }
           ;;
           ,@(when t
               `((,(byte-compile
                    `(lambda (limit)
                       (let ((parse-sexp-lookup-properties
                              (cc-eval-when-compile
                                (boundp 'parse-sexp-lookup-properties))))
                         (while (re-search-forward
                                 ,(concat csharp-enum-decl-re
                                          "[ \t\n\r\f\v]*"
                                          "{")
                                 limit t)

                           (csharp-log 3 "enum? at %d" (match-beginning 0))

                           (unless
                               (progn
                                 (goto-char (match-beginning 0))
                                 (c-skip-comments-and-strings limit))
                             (progn
                               (save-match-data
                                 (goto-char (match-end 0))
                                 (c-put-char-property (1- (point))
                                                      'c-type
                                                      'c-decl-id-start)
                                 (c-forward-syntactic-ws))
                               (save-match-data
                                 (c-font-lock-declarators limit t nil))
                               (goto-char (match-end 0))
                               )
                             )))
                       nil))
                  )))


           ;; Case 3: declaration of constructor
           ;;
           ;; Example:
           ;;
           ;; private Foo(...) {...}
           ;;
           ,@(when t
               `((,(byte-compile
                    `(lambda (limit)
                       (let ((parse-sexp-lookup-properties
                              (cc-eval-when-compile
                                (boundp 'parse-sexp-lookup-properties)))
                             (found-it nil))
                         (while (re-search-forward
                                 ,(concat
                                   "^[ \t\n\r\f\v]*"
                                   "\\(\\<\\(public\\|private\\|protected\\)\\)?[ \t\n\r\f\v]+"
                                   "\\(@?[[:alpha:]_][[:alnum:]_]*\\)" ;; name of constructor
                                   "[ \t\n\r\f\v]*"
                                   "\\("
                                   "("
                                   "\\)")
                                 limit t)

                           (unless
                               (progn
                                 (goto-char (match-beginning 0))
                                 (c-skip-comments-and-strings limit))

                             (goto-char (match-end 0))

                             (csharp-log 3 "ctor decl? L(%d) B(%d) E(%d)"
                                         limit (match-beginning 0) (point))

                             (backward-char 1) ;; just left of the open paren
                             (save-match-data
                               ;; Jump over the parens, safely.
                               ;; If it's an unbalanced paren, no problem,
                               ;; do nothing.
                               (if (c-safe (c-forward-sexp 1) t)
                                   (progn
                                     (c-forward-syntactic-ws)
                                     (cond

                                      ;; invokes base or this constructor.
                                      ((re-search-forward
                                        ,(concat
                                          "\\(:[ \t\n\r\f\v]*\\(base\\|this\\)\\)"
                                          "[ \t\n\r\f\v]*"
                                          "("
                                          )
                                        limit t)
                                       (csharp-log 3 " - ctor with dependency?")

                                       (goto-char (match-end 0))
                                       (backward-char 1) ;; just left of the open paren
                                       (csharp-log 3 " - before paren at %d" (point))

                                       (if (c-safe (c-forward-sexp 1) t)
                                           (progn
                                             (c-forward-syntactic-ws)
                                             (csharp-log 3 " - skipped over paren pair %d" (point))
                                             (if (eq (char-after) ?{)
                                                 (setq found-it t)))))

                                      ;; open curly. no depedency on other ctor.
                                      ((eq (char-after) ?{)
                                       (csharp-log 3 " - no dependency, curly at %d" (point))
                                       (setq found-it t)))

                                     )))

                             (if found-it
                                 ;; fontify the constructor symbol
                                 (c-put-font-lock-face (match-beginning 3)
                                                       (match-end 3)
                                                       'font-lock-function-name-face))
                             (goto-char (match-end 0)))))
                       nil)))))


           ;; Case 4: using clause. Without this, using (..) gets fontified as a fn.
           ,@(when t
               `((,(byte-compile
                    `(lambda (limit)
                       (let ((parse-sexp-lookup-properties
                              (cc-eval-when-compile
                                (boundp 'parse-sexp-lookup-properties))))
                         (while (re-search-forward
                                 ,(concat "\\<\\(using\\)"
                                          "[ \t\n\r\f\v]*"
                                          "(")
                                 limit t)

                           (csharp-log 3 "using clause p(%d)" (match-beginning 0))

                           (unless
                               (progn
                                 (goto-char (match-beginning 0))
                                 (c-skip-comments-and-strings limit))

                             (save-match-data
                               (c-put-font-lock-face (match-beginning 1)
                                                     (match-end 1)
                                                     'font-lock-keyword-face)
                               (goto-char (match-end 0))))))
                       nil))
                  )))

           ;; Case 5: attributes
           ,`((lambda (limit)
                (let ((parse-sexp-lookup-properties
                       (cc-eval-when-compile
                         (boundp 'parse-sexp-lookup-properties))))

                  (while (re-search-forward
                          ,(concat "[ \t\n\r\f\v]+"
                                   "\\(\\["
                                   "[ \t\n\r\f\v]*"
                                   "\\(?:\\(?:return\\|assembly\\)[ \t]*:[ \t]*\\)?"
                                   "\\("
                                   "\\(?:[A-Za-z_][[:alnum:]]*\\.\\)*"
                                   "[A-Za-z_][[:alnum:]]*"
                                   "\\)"
                                   "[^]]*\\]\\)"
                                   )
                          limit t)

                    (csharp-log 3 "attribute? - %d limit(%d)" (match-beginning 1)
                                limit)

                    (unless
                        (progn
                          (goto-char (match-beginning 1))
                          (c-skip-comments-and-strings limit))

                      (let ((b2 (match-beginning 2))
                            (e2 (match-end 2))
                            (is-attr nil))
                        (csharp-log 3 " - type match: %d - %d"
                                    b2 e2)
                        (save-match-data
                          (c-backward-syntactic-ws)
                          (setq is-attr (or
                                         (eq (char-before) 59) ;; semicolon
                                         (eq (char-before) 93) ;; close square brace
                                         (eq (char-before) 123) ;; open curly
                                         (eq (char-before) 125) ;; close curly
                                         (save-excursion
                                           (c-beginning-of-statement-1)
                                           (looking-at
                                            "#\\(pragma\\|endregion\\|region\\|if\\|else\\|endif\\)"))
                                         )))

                        (if is-attr
                            (progn
                              (if (<= 3 csharp-log-level)
                                  (csharp-log 3 " - attribute: '%s'"
                                              (buffer-substring-no-properties b2 e2)))
                              (c-put-font-lock-face b2 e2 'font-lock-type-face)))))
                    (goto-char (match-end 0))
                    ))
                nil))

           ;; Fontify labels after goto etc.
           ,@(when (c-lang-const c-before-label-kwds)
               `( ;; (Got three different interpretation levels here,
                 ;; which makes it a bit complicated: 1) The backquote
                 ;; stuff is expanded when compiled or loaded, 2) the
                 ;; eval form is evaluated at font-lock setup (to
                 ;; substitute c-label-face-name correctly), and 3) the
                 ;; resulting structure is interpreted during
                 ;; fontification.)
                 (eval
                  . ,(let* ((c-before-label-re
                             (c-make-keywords-re nil
                               (c-lang-const c-before-label-kwds))))
                       `(list
                         ,(concat "\\<\\(" c-before-label-re "\\)\\>"
                                  "\\s *"
                                  "\\(" ; identifier-offset
                                  (c-lang-const c-symbol-key)
                                  "\\)")
                         (list ,(+ (regexp-opt-depth c-before-label-re) 2)
                               c-label-face-name nil t))))))



           ;; Fontify the clauses after various keywords.
           ,@(when (or (c-lang-const c-type-list-kwds)
                       (c-lang-const c-ref-list-kwds)
                       (c-lang-const c-colon-type-list-kwds)
                       (c-lang-const c-paren-type-kwds))
               `((,(c-make-font-lock-search-function
                    (concat "\\<\\("
                            (c-make-keywords-re nil
                              (append (c-lang-const c-type-list-kwds)
                                      (c-lang-const c-ref-list-kwds)
                                      (c-lang-const c-colon-type-list-kwds)
                                      (c-lang-const c-paren-type-kwds)))
                            "\\)\\>")
                    '((c-fontify-types-and-refs ((c-promote-possible-types t))
                        (c-forward-keyword-clause 1)
                        (if (> (point) limit) (goto-char limit))))))))


           ;; Fontify the name that follows each namespace declaration
           ;; this needs to be done in the matchers-after because
           ;; otherwise the namespace names get the font-lock-type-face,
           ;; due to the energetic efforts of c-forward-type.
           ,`("\\<\\(namespace\\)[ \t\n\r\f\v]+\\(\\(?:[A-Za-z_][[:alnum:]]*\\.\\)*[A-Za-z_][[:alnum:]]*\\)"
              2 font-lock-constant-face t)


           ))



;; C# does generics.  Setting this to t tells the parser to put
;; parenthesis syntax on angle braces that surround a comma-separated
;; list.
(c-lang-defconst c-recognize-<>-arglists
  csharp t)


(c-lang-defconst c-identifier-key
  csharp (concat "\\([[:alpha:]_][[:alnum:]_]*\\)" ; 1
                 "\\("
                 "[ \t\n\r\f\v]*"
                 "\\(\\.\\)"             ;;(c-lang-const c-opt-identifier-concat-key)
                 "[ \t\n\r\f\v]*"
                 "\\(\\([[:alpha:]_][[:alnum:]_]*\\)\\)"
                 "\\)*"))

;; C# has a few rules that are slightly different than Java for
;; operators. This also removed the Java's "super" and replaces it
;; with the C#'s "base".
(c-lang-defconst c-operators
  csharp `((prefix "base")))


;; C# uses CPP-like prefixes to mark #define, #region/endregion,
;; #if/else/endif, and #pragma.  This regexp matches the prefix, not
;; including the beginning-of-line (BOL), and not including the term
;; after the prefix (define, pragma, region, etc).  This regexp says
;; whitespace, followed by the prefix, followed by maybe more
;; whitespace.

(c-lang-defconst c-opt-cpp-prefix
  csharp "\\s *#\\s *")


;; there are no message directives in C#
(c-lang-defconst c-cpp-message-directives
  csharp nil)

(c-lang-defconst c-cpp-expr-directives
  csharp '("if"))

(c-lang-defconst c-opt-cpp-macro-define
  csharp "define")

;; $ is not a legal char in an identifier in C#.  So we need to
;; create a csharp-specific definition of this constant.
(c-lang-defconst c-symbol-chars
  csharp (concat c-alnum "_"))

;; c-identifier-syntax-modifications by default defines $ as a word
;; syntax, which is not legal in C#.  So, define our own lang-specific
;; value.
(c-lang-defconst c-identifier-syntax-modifications
  csharp '((?_ . "w")))



(c-lang-defconst c-colon-type-list-kwds
  csharp '("class"))

(c-lang-defconst c-block-prefix-disallowed-chars

  ;; Allow ':' for inherit list starters.
  csharp (set-difference (c-lang-const c-block-prefix-disallowed-chars)
                         '(?: ?,)))


(c-lang-defconst c-assignment-operators
  csharp '("=" "*=" "/=" "%=" "+=" "-=" ">>=" "<<=" "&=" "^=" "|="))

(c-lang-defconst c-primitive-type-kwds
  ;; ECMA-344, S8
  csharp '("object" "string" "sbyte" "short" "int" "long" "byte"
           "ushort" "uint" "ulong" "float" "double" "bool" "char"
           "decimal" "void"))

;; The keywords that define that the following is a type, such as a
;; class definition.
(c-lang-defconst c-type-prefix-kwds
  ;; ECMA-344, S?
  csharp '("class" "interface" "struct"))  ;; no enum here.
                                           ;; we want enum to be a brace list.


;; Type modifier keywords. They appear anywhere in types, but modify
;; instead of create one.
(c-lang-defconst c-type-modifier-kwds
  ;; EMCA-344, S?
  csharp '("readonly" "const"))


;; Tue, 20 Apr 2010  16:02
;; need to verify that this works for lambdas...
(c-lang-defconst c-special-brace-lists
  csharp '((?{ . ?}) ))



;; dinoch
;; Thu, 22 Apr 2010  18:54
;;
;; No idea why this isn't getting set properly in the first place.
;; In cc-langs.el, it is set to the union of a bunch of things, none
;; of which include "new", or "enum".
;;
;; But somehow both of those show up in the resulting derived regexp.
;; This breaks indentation of instance initializers, such as
;;
;;         var x = new Foo { ... };
;;
;; Based on my inspection, the existing c-lang-defconst should work!
;; I don't know how to fix this c-lang-defconst, so I am re-setting this
;; variable here, to provide the regex explicitly.
;;
(c-lang-defconst c-decl-block-key
  csharp '"\\(namespace\\)\\([^[:alnum:]_]\\|$\\)\\|\\(class\\|interface\\|struct\\)\\([^[:alnum:]_]\\|$\\)" )


;; Thu, 22 Apr 2010  14:29
;; I want this to handle    var x = new Foo[] { ... };
;; not sure if necessary.
(c-lang-defconst c-inexpr-brace-list-kwds
  csharp '("new"))


;; ;;(c-lang-defconst c-inexpr-class-kwds
;; ;; csharp '("new"))



(c-lang-defconst c-class-decl-kwds
  ;; EMCA-344, S?
  ;; don't include enum here, because we want it to be fontified as a brace
  ;; list, with commas delimiting the values. see c-brace-list-decl-kwds
  ;; below.
  csharp '("class" "interface" "struct" ))  ;; no "enum"!!


;; The various modifiers used for class and method descriptions.
(c-lang-defconst c-modifier-kwds
  csharp '("public" "partial" "private" "const" "abstract" "sealed"
           "protected" "ref" "out" "static" "virtual"
           "override" "params" "internal"))


;; Thu, 22 Apr 2010  23:02
;; Based on inspection of the cc-mode code, the c-protection-kwds
;; c-lang-const is used only for objective-c.  So the value is
;; irrelevant for csharp.
(c-lang-defconst c-protection-kwds
  csharp nil
  ;; csharp '("private" "protected" "public" "internal")
)


;; Define the keywords that can have something following after them.
(c-lang-defconst c-type-list-kwds
  csharp '("struct" "class" "interface" "is" "as"
           "delegate" "event" "set" "get" "add" "remove"))


;; This allows the classes after the : in the class declartion to be
;; fontified.
(c-lang-defconst c-typeless-decl-kwds
  csharp '(":"))

;; Sets up the enum to handle the list properly, and also the new
;; keyword to handle object initializers.  This requires a modified
;; c-basic-matchers-after (see above) in order to correctly fontify C#
;; 3.0 object initializers.
(c-lang-defconst c-brace-list-decl-kwds
  csharp '("enum" "new"))


;; Statement keywords followed directly by a substatement.
;; catch is not one of them, because catch has a paren (typically).
(c-lang-defconst c-block-stmt-1-kwds
  csharp '("do" "try" "finally" "unsafe"))


;; Statement keywords followed by a paren sexp and then by a substatement.
(c-lang-defconst c-block-stmt-2-kwds
  csharp '("for" "if" "switch" "while" "catch" "foreach" "using"
           "checked" "unchecked" "lock"))


;; Statements that break out of braces
(c-lang-defconst c-simple-stmt-kwds
  csharp '("return" "continue" "break" "throw" "goto" ))

;; Statements that allow a label
;; TODO?
(c-lang-defconst c-before-label-kwds
  csharp nil)

;; Constant keywords
(c-lang-defconst c-constant-kwds
  csharp '("true" "false" "null"))

;; Keywords that start "primary expressions."
(c-lang-defconst c-primary-expr-kwds
  csharp '("this" "base"))

;; Treat namespace as an outer block so class indenting
;; works properly.
(c-lang-defconst c-other-block-decl-kwds
  csharp '("namespace"))

(c-lang-defconst c-other-kwds
  csharp '("sizeof" "typeof" "is" "as" "yield" "extern"
           "where" "select" "in" "from" "let" "orderby" "ascending" "descending"
	   "await" "async" "var"))

(c-lang-defconst c-overloadable-operators
  ;; EMCA-344, S14.2.1
  csharp '("+" "-" "*" "/" "%" "&" "|" "^"
           "<<" ">>" "==" "!=" ">" "<" ">=" "<="))


;; This c-cpp-matchers stuff is used for fontification.
;; see cc-font.el
;;

;; There's no preprocessor in C#, but there are still compiler
;; directives to fontify: "#pragma", #region/endregion, #define, #undef,
;; #if/else/endif.  (The definitions for the extra keywords above are
;; enough to incorporate them into the fontification regexps for types
;; and keywords, so no additional font-lock patterns are required for
;; keywords.)

(c-lang-defconst c-cpp-matchers
  csharp (cons
      ;; Use the eval form for `font-lock-keywords' to be able to use
      ;; the `c-preprocessor-face-name' variable that maps to a
      ;; suitable face depending on the (X)Emacs version.
      '(eval . (list "^\\s *\\(#pragma\\|undef\\|define\\)\\>\\(.*\\)"
                     (list 1 c-preprocessor-face-name)
                     '(2 font-lock-string-face)))
      ;; There are some other things in `c-cpp-matchers' besides the
      ;; preprocessor support, so include it.
      (c-lang-const c-cpp-matchers)))



;; Custom variables
;;;###autoload
(defcustom csharp-mode-hook nil
    "*Hook called by `csharp-mode'."
    :type 'hook
    :group 'csharp)

  ;; The following fn allows this:
  ;;    (csharp-log 3 "scan result...'%s'" state)

(defcustom csharp-log-level 0
    "The current log level for CSharp-mode-specific operations.
This is used in particular by the verbatim-literal
string scanning.

Most other csharp functions are not instrumented.
0 = NONE, 1 = Info, 2 = VERBOSE, 3 = DEBUG, 4 = SHUTUP ALREADY. "
    :type 'integer
    :group 'csharp)


;;;###autoload
(defcustom csharp-want-imenu t
  "*Whether to generate a buffer index via imenu for C# buffers."
  :type 'boolean :group 'csharp)


(defconst csharp-font-lock-keywords-1 (c-lang-const c-matchers-1 csharp)
  "Minimal highlighting for C# mode.")

(defconst csharp-font-lock-keywords-2 (c-lang-const c-matchers-2 csharp)
  "Fast normal highlighting for C# mode.")

(defconst csharp-font-lock-keywords-3 (c-lang-const c-matchers-3 csharp)
  "Accurate normal highlighting for C# mode.")

(defvar csharp-font-lock-keywords csharp-font-lock-keywords-3
  "Default expressions to highlight in C# mode.")


(defvar csharp-mode-syntax-table nil
  "Syntax table used in csharp-mode buffers.")
(or csharp-mode-syntax-table
    (setq csharp-mode-syntax-table
          (funcall (c-lang-const c-make-mode-syntax-table csharp))))

(defvar csharp-mode-abbrev-table nil
  "Abbreviation table used in csharp-mode buffers.")
(c-define-abbrev-table 'csharp-mode-abbrev-table
  ;; Keywords that if they occur first on a line might alter the
  ;; syntactic context, and which therefore should trig reindentation
  ;; when they are completed.
  '(("else" "else" c-electric-continued-statement 0)
    ("while" "while" c-electric-continued-statement 0)
    ("catch" "catch" c-electric-continued-statement 0)
    ("finally" "finally" c-electric-continued-statement 0)))

(defvar csharp-mode-map (let ((map (c-make-inherited-keymap)))
                      ;; Add bindings which are only useful for C#
                      map)
  "Keymap used in csharp-mode buffers.")


;; TODO
;; Defines our constant for finding attributes.
;;(defconst csharp-attribute-regex "\\[\\([XmlType]+\\)(")
;;(defconst csharp-attribute-regex "\\[\\(.\\)")
;; This doesn't work because the string regex happens before this point
;; and getting the font-locking to work before and after is fairly difficult
;;(defconst csharp-attribute-regex
;;  (concat
;;   "\\[[a-zA-Z][ \ta-zA-Z0-9.]+"
;;   "\\((.*\\)?"
;;))


;; ==================================================================
;; end of c# values for "language constants" defined in cc-langs.el
;; ==================================================================


;; ========================================================================
;; moving

;; alist of regexps for various structures in a csharp source file.
(eval-and-compile
  (defconst csharp--regexp-alist
    (list

     `(func-start
       ,(concat
         "^[ \t\n\r\f\v]*"                            ;; leading whitespace
         "\\("
         "public\\(?: static\\)?\\|"                  ;; 1. access modifier
         "private\\(?: static\\)?\\|"
         "protected\\(?: internal\\)?\\(?: static\\)?\\|"
         "static\\|"
         "\\)"
         "[ \t\n\r\f\v]+"
         "\\(?:override[ \t\n\r\f\v]+\\)?"            ;; optional
         "\\([[:alpha:]_][^\t\(\n]+\\)"               ;; 2. return type - possibly generic
         "[ \t\n\r\f\v]+"
         "\\([[:alpha:]_][[:alnum:]_]*\\)"            ;; 3. name of func
         "[ \t\n\r\f\v]*"
         "\\(\([^\)]*\)\\)"                           ;; 4. params w/parens
         "[ \t\n\r\f\v]*"
         ))

     `(ctor-start
       ,(concat
         "^[ \t\n\r\f\v]*"                            ;; leading whitespace
         "\\("
         "public\\|"                                  ;; 1. access modifier
         "private\\|"
         "protected\\(?: internal\\)?\\|"
         "static\\|"
         "\\)"
         "[ \t\n\r\f\v]+"
         "\\([[:alpha:]_][[:alnum:]_]*\\)"            ;; 2. name of ctor
         "[ \t\n\r\f\v]*"
         "\\(\([^\)]*\)\\)"                           ;; 3. parameter list (with parens)
         "\\("                                        ;; 4. ctor dependency
         "[ \t\n]*:[ \t\n]*"                          ;; colon
         "\\(?:this\\|base\\)"                        ;; this or base
         "[ \t\n\r\f\v]*"
         "\\(?:\([^\)]*\)\\)"                         ;; parameter list (with parens)
         "\\)?"                                       ;; possibly
         "[ \t\n\r\f\v]*"
         ))


     `(using-stmt
       ,(concat
         ;;"^[ \t\n\r\f\v]*"
         "\\(\\<using\\)"
         "[ \t\n\r\f\v]+"
         "\\(?:"
         "\\([[:alpha:]_][[:alnum:]_]*\\)"            ;; alias
         "[ \t\n\r\f\v]*"
         "="
         "[ \t\n\r\f\v]*"
         "\\)?"
         "\\("
         "\\(?:[A-Za-z_][[:alnum:]]*\\.\\)*"
         "[A-Za-z_][[:alnum:]]*"
         "\\)"                                        ;; imported namespace
         "[ \t\n\r\f\v]*"
         ";"
         ))

     `(class-start
       ,(concat
         "^[ \t]*"                                    ;; leading whitespace
         "\\("
         "public\\(?: \\(?:static\\|sealed\\)\\)?[ \t]+\\|"  ;; access modifiers
         "internal\\(?: \\(?:static\\|sealed\\)\\)?[ \t]+\\|"
         "static\\(?: internal\\)?[ \t]+\\|"
         "sealed\\(?: internal\\)?[ \t]+\\|"
         "static[ \t]+\\|"
         "sealed[ \t]+\\|"
         "\\)"
         "\\(\\(?:partial[ \t]+\\)?class\\|struct\\)" ;; class/struct keyword
         "[ \t]+"
         "\\([[:alpha:]_][[:alnum:]]*\\)"             ;; type name
         "\\("
         "[ \t\n]*:[ \t\n]*"                          ;; colon
         "\\([[:alpha:]_][^\t\(\n]+\\)"               ;; base / intf - poss generic
         "\\("
         "[ \t\n]*,[ \t\n]*"
         "\\([[:alpha:]_][^\t\(\n]+\\)"               ;; addl interface - poss generic
         "\\)*"
         "\\)?"                                       ;; possibly
         "[ \t\n\r\f\v]*"
         ))

     `(genclass-start
       ,(concat
         "^[ \t]*"                                    ;; leading whitespace
         "\\("
         "public\\(?: \\(?:static\\|sealed\\)\\)?[ \t]+\\|"  ;; access modifiers
         "internal\\(?: \\(?:static\\|sealed\\)\\)?[ \t]+\\|"
         "static\\(?: internal\\)?[ \t]+\\|"
         "sealed\\(?: internal\\)?[ \t]+\\|"
         "static[ \t]+\\|"
         "sealed[ \t]+\\|"
         "\\)"
         "\\(\\(?:partial[ \t]+\\)?class\\|struct\\)" ;; class/struct keyword
         "[ \t]+"
         "\\([[:alpha:]_][[:alnum:]_<>, ]*\\)"        ;; type name (generic)
         "\\("
         "[ \t\n]*:[ \t\n]*"                          ;; colon
         "\\([[:alpha:]_][^\t\(\n]+\\)"               ;; base / intf - poss generic
         "\\("
         "[ \t\n]*,[ \t\n]*"
         "\\([[:alpha:]_][^\t\(\n]+\\)"               ;; addl interface - poss generic
         "\\)*"
         "\\)?"                                       ;; possibly
         "[ \t\n\r\f\v]*"
         ))

     `(enum-start
       ,(concat
         "^[ \t\f\v]*"                                ;; leading whitespace
         "\\("
         "public[ \t]+enum\\|"                        ;; enum keyword
         "enum"
         "\\)"
         "[ \t\n\r\f\v]+"
         "\\([[:alpha:]_][[:alnum:]_]*\\)"            ;; name of enum
         "[ \t\n\r\f\v]*"
         "\\(:[ \t\n\r\f\v]*"
         "\\("
         "sbyte\\|byte\\|short\\|ushort\\|int\\|uint\\|long\\|ulong"
         "\\)"
         "[ \t\n\r\f\v]*"
         "\\)?"                                       ;; possibly
         "[ \t\n\r\f\v]*"
         ))


     `(intf-start
       ,(concat
         "^[ \t\f\v]*"                                ;; leading whitespace
         "\\(?:"
         "public\\|internal\\|"                       ;; access modifier
         "\\)"
         "[ \t\n\r\f\v]+"
         "\\(interface\\)"
         "[ \t\n\r\f\v]+"
         "\\([[:alpha:]_][[:alnum:]_]*\\)"            ;; name of interface
         "[ \t\n\r\f\v]*"
         ))

     `(prop-start
       ,(concat
         "^[ \t\f\v]*"                                ;; leading whitespace
         "\\("
         "public\\|"                                  ;; 1: access modifier
         "private\\|"
         "protected internal\\|"
         "internal protected\\|"
         "internal\\|"
         "\\)"
         "[ \t\n\r\f\v]+"
         "\\([[:alpha:]_][^\t\(\n]+\\)"               ;; 2: return type - possibly generic
         "[ \t\n\r\f\v]+"
         "\\("
         "\\(?:[A-Za-z_][[:alnum:]_]*\\.\\)*"          ;; possible prefix interface
         "[[:alpha:]_][[:alnum:]_]*"                  ;; 3: name of prop
         "\\)"
         "[ \t\n\r\f\v]*"
         ))

     `(indexer-start
       ,(concat
         "^[ \t\f\v]*"                                ;; leading whitespace
         "\\("
         "public\\|"                                  ;; 1: access modifier
         "private\\|"
         "protected internal\\|"
         "internal protected\\|"
         "internal\\|"
         "\\)"
         "[ \t\n\r\f\v]+"
         "\\([[:alpha:]_][^\t\(\n]+\\)"               ;; 2: return type - possibly generic
         "[ \t\n\r\f\v]+"
         "\\(this\\)"                                 ;; 3: 'this' keyword
         "[ \t\n\r\f\v]*"
         "\\["                                        ;; open square bracket
         "[ \t\n\r\f\v]*"
         "\\([^\]]+\\)"                               ;; 4: index type
         "[ \t\n\r\f\v]+"
         "[[:alpha:]_][[:alnum:]_]*"                  ;; index name - a simple identifier
         "\\]"                                        ;; closing sq bracket
         "[ \t\n\r\f\v]*"
         ))

     `(namespace-start
       ,(concat
         "^[ \t\f\v]*"                                ;; leading whitespace
         "\\(namespace\\)"
         "[ \t\n\r\f\v]+"
         "\\("
         "\\(?:[A-Za-z_][[:alnum:]_]*\\.\\)*"          ;; name of namespace
         "[A-Za-z_][[:alnum:]]*"
         "\\)"
         "[ \t\n\r\f\v]*"
         ))

     )))


(defun csharp--regexp (symbol)
  "Retrieves a regexp from the `csharp--regexp-alist' corresponding
to the given symbol.
"
  (let ((elt (assoc symbol csharp--regexp-alist)))
    (if elt (cadr elt) nil)))


(defun csharp-move-back-to-beginning-of-block ()
  "Moves to the previous open curly.
"
  (interactive)
  (re-search-backward "{" (point-min) t))


(defun csharp--move-back-to-beginning-of-something (must-match &optional must-not-match)
  "Moves back to the open-curly that defines the beginning of *something*,
defined by the given MUST-MATCH, a regexp which must match immediately
preceding the curly.  If MUST-NOT-MATCH is non-nil, it is treated
as a regexp that must not match immediately preceding the curly.

This is a helper fn for `csharp-move-back-to-beginning-of-defun' and
`csharp-move-back-to-beginning-of-class'

"
  (interactive)
  (let (done
        (found (point))
        (need-to-backup (not (looking-at "{"))))
    (while (not done)
      (if need-to-backup
          (setq found (csharp-move-back-to-beginning-of-block)))
      (if found
          (setq done (and (looking-back must-match)
                          (or (not must-not-match)
                              (not (looking-back must-not-match))))
                need-to-backup t)
        (setq done t)))
    found))



(defun csharp-move-back-to-beginning-of-defun ()
  "Moves back to the open-curly that defines the beginning of the
enclosing method.  If point is outside a method, then move back to the
beginning of the prior method.

See also, `csharp-move-fwd-to-end-of-defun'.
"
  (interactive)
  (cond

   ((bobp) nil)

   (t
    (let (found)
      (save-excursion
        ;; handle the case where we're at the top of a fn now.
        ;; if the user is asking to move back, then obviously
        ;; he wants to move back to a *prior* defun.
        (if (and (looking-at "{")
                 (looking-back (csharp--regexp 'func-start))
                 (not (looking-back (csharp--regexp 'namespace-start))))
            (forward-char -1))

        ;; now do the real work
        (setq found (csharp--move-back-to-beginning-of-something
                     (csharp--regexp 'func-start)
                     (csharp--regexp 'namespace-start))))
      (if found
          (goto-char found))))))


(defun csharp--on-defun-close-curly-p ()
  "return t when point is on the close-curly of a method."
  (and (looking-at "}")
       (save-excursion
         (and
          (progn (forward-char) (forward-sexp -1) t)
          (not (looking-back (csharp--regexp 'class-start)))
          (not (looking-back (csharp--regexp 'namespace-start)))
          (looking-back (csharp--regexp 'func-start))))))

(defun csharp--on-ctor-close-curly-p ()
  "return t when point is on the close-curly of a constructor."
  (and (looking-at "}")
       (save-excursion
         (and
          (progn (forward-char) (forward-sexp -1) t)
          (looking-back (csharp--regexp 'ctor-start))))))

(defun csharp--on-class-close-curly-p ()
  "return t when point is on the close-curly of a class or struct."
  (and (looking-at "}")
       (save-excursion
         (and
          (progn (forward-char) (forward-sexp -1) t)
          (not (looking-back (csharp--regexp 'namespace-start)))
          (looking-back (csharp--regexp 'class-start))))))

(defun csharp--on-intf-close-curly-p ()
  "return t when point is on the close-curly of an interface."
  (and (looking-at "}")
       (save-excursion
         (and
          (progn (forward-char) (forward-sexp -1) t)
          (looking-back (csharp--regexp 'intf-start))))))

(defun csharp--on-enum-close-curly-p ()
  "return t when point is on the close-curly of an enum."
  (and (looking-at "}")
       (save-excursion
         (and
          (progn (forward-char) (forward-sexp -1) t)
          (looking-back (csharp--regexp 'enum-start))))))

(defun csharp--on-namespace-close-curly-p ()
  "return t when point is on the close-curly of a namespace."
  (and (looking-at "}")
       (save-excursion
         (and
          (progn (forward-char) (forward-sexp -1) t)
          (looking-back (csharp--regexp 'namespace-start))))))

(defun csharp--on-defun-open-curly-p ()
  "return t when point is on the open-curly of a method."
  (and (looking-at "{")
       (not (looking-back (csharp--regexp 'class-start)))
       (not (looking-back (csharp--regexp 'namespace-start)))
       (looking-back (csharp--regexp 'func-start))))

(defun csharp--on-class-open-curly-p ()
  "return t when point is on the open-curly of a class."
  (and (looking-at "{")
       (not (looking-back (csharp--regexp 'namespace-start)))
       (looking-back (csharp--regexp 'class-start))))

(defun csharp--on-genclass-open-curly-p ()
  "return t when point is on the open-curly of a generic class."
  (and (looking-at "{")
       (looking-back (csharp--regexp 'genclass-start))))

(defun csharp--on-namespace-open-curly-p ()
  "return t when point is on the open-curly of a namespace."
  (and (looking-at "{")
       (looking-back (csharp--regexp 'namespace-start))))

(defun csharp--on-ctor-open-curly-p ()
  "return t when point is on the open-curly of a ctor."
  (and (looking-at "{")
       (looking-back (csharp--regexp 'ctor-start))))

(defun csharp--on-intf-open-curly-p ()
  "return t when point is on the open-curly of a interface."
  (and (looking-at "{")
       (looking-back (csharp--regexp 'intf-start))))

(defun csharp--on-prop-open-curly-p ()
  "return t when point is on the open-curly of a property."
  (and (looking-at "{")
       (not (looking-back (csharp--regexp 'class-start)))
       (looking-back (csharp--regexp 'prop-start))))

(defun csharp--on-indexer-open-curly-p ()
  "return t when point is on the open-curly of a C# indexer."
  (and (looking-at "{")
       (looking-back (csharp--regexp 'indexer-start))))

(defun csharp--on-enum-open-curly-p ()
  "return t when point is on the open-curly of a interface."
  (and (looking-at "{")
       (looking-back (csharp--regexp 'enum-start))))



(defun csharp-move-fwd-to-end-of-defun ()
  "Moves forward to the close-curly that defines the end of the enclosing
method. If point is outside a method, moves forward to the close-curly that
defines the end of the next method.

See also, `csharp-move-back-to-beginning-of-defun'.
"
  (interactive)

  (let ((really-move
         (lambda ()
           (let ((start (point))
                 dest-char)
             (save-excursion
               (csharp-move-back-to-beginning-of-defun)
               (forward-sexp)
               (if (>= (point) start)
                   (setq dest-char (point))))
             (if dest-char
                 (goto-char dest-char))))))

    (cond

     ;; case 1: end of buffer.  do nothing.
     ((eobp) nil)

     ;; case 2: we're at the top of a class
     ((csharp--on-class-open-curly-p)
      (let (found-it)
        (save-excursion
          (forward-char 1) ;; get off the curly
          (setq found-it
                (and ;; look for next open curly
                 (re-search-forward "{" (point-max) t)
                 (funcall really-move))))
        (if found-it
            (goto-char found-it))))


     ;; case 3: we're at the top of a fn now.
     ((csharp--on-defun-open-curly-p)
      (forward-sexp))


     ;; case 4: we're at the bottom of a fn now (possibly
     ;; after just calling csharp-move-fwd-to-end-of-defun.
     ((and (looking-back "}")
           (save-excursion
             (forward-sexp -1)
             (csharp--on-defun-open-curly-p)))

      (let (found-it)
        (save-excursion
          (setq found-it
                (and (re-search-forward "{" (point-max) t)
                     (funcall really-move))))
        (if found-it
            (goto-char found-it))))


     ;; case 5: we're at none of those places.
     (t
      (funcall really-move)))))




(defun csharp-move-back-to-beginning-of-class ()
  "Moves back to the open-curly that defines the beginning of the
enclosing class.  If point is outside a class, then move back to the
beginning of the prior class.

See also, `csharp-move-fwd-to-end-of-defun'.
"
  (interactive)

  (cond
   ((bobp) nil)

   (t
    (let (found)
      (save-excursion
        ;; handle the case where we're at the top of a class now.
        ;; if the user is asking to move back, then obviously
        ;; he wants to move back to a *prior* defun.
        (if (and (looking-at "{")
                 (looking-back (csharp--regexp 'class-start))
                 (not (looking-back (csharp--regexp 'namespace-start))))
            (forward-char -1))

        ;; now do the real work
        (setq found (csharp--move-back-to-beginning-of-something
                     (csharp--regexp 'class-start)
                     (csharp--regexp 'namespace-start))))
      (if found
          (goto-char found))))))




(defun csharp-move-fwd-to-end-of-class ()
  "Moves forward to the close-curly that defines the end of the
enclosing class.

See also, `csharp-move-back-to-beginning-of-class'.
"
  (interactive)
  (let ((start (point))
        dest-char)
    (save-excursion
      (csharp-move-back-to-beginning-of-class)
      (forward-sexp)
      (if (>= (point) start)
          (setq dest-char (point))))

    (if dest-char
        (goto-char dest-char))))



(defun csharp-move-back-to-beginning-of-namespace ()
  "Moves back to the open-curly that defines the beginning of the
enclosing namespace.  If point is outside a namespace, then move back
to the beginning of the prior namespace.

"
  (interactive)
  (cond

   ((bobp) nil)

   (t
    (let (found)
      (save-excursion
        ;; handle the case where we're at the top of a namespace now.
        ;; if the user is asking to move back, then obviously
        ;; he wants to move back to a *prior* defun.
        (if (and (looking-at "{")
                 (looking-back (csharp--regexp 'namespace-start)))
            (forward-char -1))

        ;; now do the real work
        (setq found (csharp--move-back-to-beginning-of-something
                     (csharp--regexp 'namespace-start))))
      (if found
          (goto-char found))))))

;; moving
;; ========================================================================




;; ==================================================================
;;; imenu stuff

;; define some advice for menu construction.

;; The way imenu constructs menus from the index alist, in
;; `imenu--split-menu', is ... ah ... perplexing.  If the csharp
;; create-index fn returns an ordered menu, and the imenu "sort" fn has
;; been set to nil, imenu still sorts the menu, according to the rule
;; that all submenus must appear at the top of any menu. Why?  I don't
;; know. This advice disables that weirdness in C# buffers.

(defadvice imenu--split-menu (around
                              csharp--imenu-split-menu-patch
                              activate compile)
  ;; This advice will run in all buffers.  Let's may sure we
  ;; actually execute the important bits only when a C# buffer is active.
  (if (and (string-match "\\.[Cc][Ss]$"  (file-relative-name buffer-file-name))
           (boundp 'csharp-want-imenu)
           csharp-want-imenu)
      (let ((menulist (copy-sequence menulist))
            keep-at-top)
        (if (memq imenu--rescan-item menulist)
            (setq keep-at-top (list imenu--rescan-item)
                  menulist (delq imenu--rescan-item menulist)))
        ;; This is the part from the original imenu code
        ;; that puts submenus at the top.  huh? why?
        ;; --------------------------------------------
        ;; (setq tail menulist)
        ;; (dolist (item tail)
        ;;   (when (imenu--subalist-p item)
        ;;     (push item keep-at-top)
        ;;     (setq menulist (delq item menulist))))
        (if imenu-sort-function
            (setq menulist (sort menulist imenu-sort-function)))
        (if (> (length menulist) imenu-max-items)
            (setq menulist
                  (mapcar
                   (lambda (menu)
                     (cons (format "From: %s" (caar menu)) menu))
                   (imenu--split menulist imenu-max-items))))
        (setq ad-return-value
              (cons title
                    (nconc (nreverse keep-at-top) menulist))))
    ;; else
    ad-do-it))


;;
;; I used this to examine the performance of the imenu scanning.
;; It's not necessary during normal operation.
;;
;; (defun csharp-imenu-begin-profile ()
;;   "turn on profiling"
;;   (interactive)
;;   (let ((fns '(csharp--on-class-open-curly-p
;;              csharp--on-namespace-open-curly-p
;;              csharp--on-ctor-open-curly-p
;;              csharp--on-enum-open-curly-p
;;              csharp--on-intf-open-curly-p
;;              csharp--on-prop-open-curly-p
;;              csharp--on-indexer-open-curly-p
;;              csharp--on-defun-open-curly-p
;;              csharp--imenu-create-index-helper
;;              looking-back
;;              looking-at)))
;;     (if (fboundp 'elp-reset-all)
;;         (elp-reset-all))
;;     (mapc 'elp-instrument-function fns)))



(defun csharp--imenu-remove-param-names-from-paramlist (s)
  "The input string S is a parameter list, of the form seen in a
C# method.  TYPE1 NAME1 [, TYPE2 NAME2 ...]

This fn returns a string of the form TYPE1 [, TYPE2...]

Upon entry, it's assumed that the parens included in S.

"
  (if (string= s "()")
      s
    (save-match-data
      (let* (new
             (state 0)  ;; 0 => ws, 1=>slurping param...
             c
             cs
             nesting
             need-type
             ix2
             (s2 (substring s 1 -1))
             (len (length s2))
             (i (1- len)))

        (while (> i 0)
          (setq c (aref s2 i) ;; current character
                cs (char-to-string c)) ;; s.t. as a string

          (cond

           ;; backing over whitespace "after" the param
           ((= state 0)
            (cond
             ;; more ws
             ((string-match "[ \t\f\v\n\r]" cs)
              t)
             ;; a legal char for an identifier
             ((string-match "[A-Za-z_0-9]" cs)
              (setq state 1))
             (t
              (error "unexpected char (A)"))))


           ;; slurping param name
           ((= state 1)
            (cond
             ;; ws signifies the end of the param
             ((string-match "[ \t\f\v\n\r]" cs)
              (setq state 2))
             ;; a legal char for an identifier
             ((string-match "[A-Za-z_0-9]" cs)
              t)
             (t
              (error "unexpected char (B)"))))


           ;; ws between typespec and param name
           ((= state 2)
            (cond
             ((string-match "[ \t\f\v\n\r]" cs)
              t)
             ;; non-ws indicates the type spec is beginning
             (t
              (incf i)
              (setq state 3
                    need-type nil
                    nesting 0
                    ix2 i))))


           ;; slurping type
           ((= state 3)
            (cond
             ((= ?> c) (incf nesting))
             ((= ?< c)
              (decf nesting)
              (setq need-type t))

             ;; ws or comma maybe signifies the end of the typespec
             ((string-match "[ \t\f\v\n\r,]" cs)
              (if (and (= nesting 0) (not need-type))
                  (progn
                    (setq new (cons (substring s2 (1+ i) ix2) new))
                    (setq state
                          (if (= c ?,) 0 4)))))

             ((string-match "[A-Za-z_0-9]" cs)
              (setq need-type nil))))


           ;; awaiting comma or b-o-s
           ((= state 4)
            (cond

             ((= ?, c)
              (if  (= nesting 0)
                  (setq state 0)))

             ((string-match "[ \t\f\v\n\r]" cs)
              t)

             ((= 93 c) (incf nesting)) ;; sq brack
             ((= 91 c)  ;; open sq brack
              (decf nesting))

             ;; handle this (extension methods), out, ref, params
             ((and (>= i 5)
                   (string= (substring s2 (- i 5) (1+ i)) "params"))
              (setf (car new) (concat "params " (car new)))
              (setq i (- i 5)))

             ((and (>= i 3)
                   (string= (substring s2 (- i 3) (1+ i)) "this"))
              (setf (car new) (concat "this " (car new)))
              (setq i (- i 3)))

             ((and (>= i 2)
                   (string= (substring s2 (- i 2) (1+ i)) "ref"))
              (setf (car new) (concat "ref " (car new)))
              (setq i (- i 2)))

             ((and (>= i 2)
                   (string= (substring s2 (- i 2) (1+ i)) "out"))
              (setf (car new) (concat "out " (car new)))
              (setq i (- i 2)))

             (t
              (error "unexpected char (C)"))))
           )

          (decf i))

        (if (and (= state 3) (= nesting 0))
            (setq new (cons (substring s2 i ix2) new)))

        (concat "("
                (if new
                    (mapconcat 'identity new ", ")
                  "")
                ")")))))


(defun csharp--imenu-item-basic-comparer (a b)
  "Compares the car of each element, assumed to be a string."
  (string-lessp (car a) (car b)))


(defun csharp--imenu-get-method-name-from-sig (sig)
  "Extract a method name with its parameter list from a method
signature, SIG. This is used to aid in sorting methods by name,
and secondarily by parameter list.

For this input:

    private Dict<String, int>  DoSomething(int, string)

...the output is:

   DoSomething(int, string)

"
  (let* (c
         result
         (state 0)
         (len (length sig))
         (i (1- len)))
    (while (> i 0)
      (setq c (aref sig i))

      (cond
       ((and (= state 0) (= c 40))
        (setq state 1))

       ((and (= state 1) (or (= c 9) (= c 32)))
        (setq result (substring sig (1+ i))
              i 0)))
      (decf i))
    result))



(defun csharp--imenu-item-method-name-comparer (a b)
  "Compares the method names in the respective cars of each element.

The car of each element is assumed to be a string with multiple
tokens in it, representing a method signature, including access
modifier, return type, and parameter list (surrounded by parens).
If the method takes no params, then it's just an empty pair of
parens.

This fn extracts the method name and param list from that
signature and compares *that*.

"
  (let ((methoda (csharp--imenu-get-method-name-from-sig (car a)))
        (methodb (csharp--imenu-get-method-name-from-sig (car b))))
    ;;(csharp-log -1 "compare '%s' <> '%s'" methoda methodb)
    (string-lessp methoda methodb)))



(defun csharp--imenu-create-index-helper (&optional parent-ns indent-level
                                                    consider-usings consider-namespaces)
  "Helper fn for `csharp-imenu-create-index'.

Scans a possibly narrowed section of a c# buffer.  It finds
namespaces, classes, structs, enums, interfaces, and methods
within classes and structs.

The way it works: it looks for an open-curly.  If the open-curly
is a namespace or a class, it narrows to whatever is inside the
curlies, then recurses.

Otherwise (the open-curly is neither of those things), this fn
tries to recognize the open-curly as the beginning of an enum,
method, or interface.

If it succeeds, then a menu item is created for the thing. Then
it jumps to the matching close-curly, and continues. Stop when no
more open-curlies are found.

"

  ;; A C# module consists of zero of more explicitly denoted (and
  ;; possibly nested) namespaces. In the absence of an
  ;; explicitly-denoted namespace, the global namespace is implicitly
  ;; applied.  Within each namespace there can be zero or more
  ;; "container" things - like class, struct, or interface; each with
  ;; zero or more indexable items - like methods, constructors.
  ;; and so on.

  ;; This fn parses the module and indexes those items, creating a
  ;; hierarchically organized list to describe them.  Each container
  ;; (ns/class/struct/etc) is represented on a separate submenu.

  ;; It works like this:
  ;; (start at the top of the module)
  ;;
  ;; 1. look for a using clause
  ;;    yes - insert an item in the menu; move past all using clauses.
  ;;
  ;; 2. go to next open curly
  ;;
  ;; 2. beginning of a container? (a class or namespace)
  ;;
  ;;    yes - narrow, and recurse
  ;;
  ;;    no - create a menu item for the thing, whatever it is.  add to
  ;;         the submenu. Go to the end of the thing (to the matching
  ;;         close curly) then goto step 1.
  ;;

  (let (container-name
        (pos-last-curly -1)
        this-flavor
        this-item
        this-menu
        found-usings
        done)

    (while (not done)

      ;; move to the next thing
      (c-forward-syntactic-ws)
      (cond
       ((and consider-usings
             (re-search-forward (csharp--regexp 'using-stmt) (point-max) t))
        (goto-char (match-beginning 1))
        (setq found-usings t
              done nil))

       ((re-search-forward "{" (point-max) t)
        (if (= pos-last-curly (point))
            (progn
              ;;(csharp-log -1 "imenu: No advance? quitting (%d)" (point))
              (setq done t)) ;; haven't advanced- likely a loop

          (setq pos-last-curly (point))
          (let ((literal (csharp-in-literal)))
            ;; skip over comments?
            (cond

             ((memq literal '(c c++))
              (while (memq literal '(c c++))
                (end-of-line)
                (forward-char 1)
                (setq literal (csharp-in-literal)))
              (if (re-search-forward "{" (point-max) t)
                  (forward-char -1)
                ;;(csharp-log -1 "imenu: No more curlies (A) (%d)" (point))
                (setq done t)))

             ((eq literal 'string)
              (if  (re-search-forward "\"" (point-max) t)
                  (forward-char 1)
                ;;(csharp-log -1 "imenu: Never-ending string? posn(%d)" (point))
                (setq done t)))

             (t
              (forward-char -1)))))) ;; backup onto the curly

       (t
        ;;(csharp-log -1 "imenu: No more curlies (B) posn(%d)" (point))
        (setq done t)))


      (if (not done)
          (cond

           ;; case 1: open curly for an array initializer
           ((looking-back "\\[\\][ \t\n\r]*")
            (forward-sexp 1))

           ;; case 2: just jumped over a string
           ((looking-back "\"")
            (forward-char 1))

           ;; case 3: at the head of a block of using statements
           (found-usings
            (setq found-usings nil
                  consider-usings nil) ;; only one batch
            (let ((first-using (match-beginning 1))
                  (count 0)
                  marquis
                  ;; don't search beyond next open curly
                  (limit (1-
                          (save-excursion
                            (re-search-forward "{" (point-max) t)))))

              ;; count the using statements
              (while (re-search-forward (csharp--regexp 'using-stmt) limit t)
                (incf count))

              (setq marquis (if (eq count 1) "using (1)"
                              (format "usings (%d)" count)))
              (push (cons marquis first-using) this-menu)))


           ;; case 4: an interface or enum inside the container
           ;; (must come before class / namespace )
           ((or (csharp--on-intf-open-curly-p)
                (csharp--on-enum-open-curly-p))
              (setq consider-namespaces nil
                    consider-usings nil
                    this-menu
                    (append this-menu
                            (list
                             (cons (concat
                                    (match-string-no-properties 1) ;; thing flavor
                                    " "
                                    (match-string-no-properties 2)) ;; intf name
                                   (match-beginning 1)))))
              (forward-sexp 1))


           ;; case 5: at the start of a container (class, namespace)
           ((or (and consider-namespaces (csharp--on-namespace-open-curly-p))
                (csharp--on-class-open-curly-p)
                (csharp--on-genclass-open-curly-p))

            ;; produce a fully-qualified name for this thing
            (if (string= (match-string-no-properties 1) "namespace")
                (setq this-flavor (match-string-no-properties 1)
                      this-item (match-string-no-properties 2))
              (setq this-flavor (match-string-no-properties 2)
                    this-item (match-string-no-properties 3)
                    consider-usings nil
                    consider-namespaces nil))

            (setq container-name (if parent-ns
                                     (concat parent-ns "." this-item)
                                   this-item))

            ;; create a submenu
            (let (submenu
                  (top (match-beginning 1))
                  (open-curly (point))
                  (close-curly (save-excursion
                                 (forward-sexp 1)
                                 (point))))
              (setq submenu
                    (list
                     (concat this-flavor " " container-name)
                     (cons "(top)" top)))

              ;; find all contained items
              (save-restriction
                (narrow-to-region (1+ open-curly) (1- close-curly))

                (let* ((yok (string= this-flavor "namespace"))
                       (child-menu
                        (csharp--imenu-create-index-helper container-name
                                                           (concat indent-level "  ")
                                                           yok yok)))
                  (if child-menu
                      (setq submenu
                            (append submenu
                                    (sort child-menu
                                          'csharp--imenu-item-basic-comparer))))))
              (setq submenu
                    (append submenu
                            (list (cons "(bottom)" close-curly))))

              (setq this-menu
                    (append this-menu (list submenu)))

              (goto-char close-curly)))


           ;; case 6: a property
           ((csharp--on-prop-open-curly-p)
            (setq consider-namespaces nil
                  consider-usings nil
                  this-menu
                  (append this-menu
                          (list
                           (cons (concat
                                  "prop "
                                  (match-string-no-properties 3)) ;; prop name
                                 (match-beginning 1)))))
            (forward-sexp 1))


           ;; case 7: an indexer
           ((csharp--on-indexer-open-curly-p)
            (setq consider-namespaces nil
                    consider-usings nil
                    this-menu
                    (append this-menu
                            (list
                             (cons (concat
                                    "indexer "
                                    (match-string-no-properties 4)) ;; index type
                                   (match-beginning 1)))))
            (forward-sexp 1))


           ;; case 8: a constructor inside the container
           ((csharp--on-ctor-open-curly-p)
            (setq consider-namespaces nil
                  consider-usings nil
                  this-menu
                  (append this-menu
                          (list
                           (cons (concat
                                  "ctor "
                                  (match-string-no-properties 2) ;; ctor name
                                  (csharp--imenu-remove-param-names-from-paramlist
                                   (match-string-no-properties 3))) ;; ctor params
                                 (match-beginning 1)))))
            (forward-sexp 1))


           ;; case 9: a method inside the container
           ((csharp--on-defun-open-curly-p)
            (setq consider-namespaces nil
                  consider-usings nil
                  this-menu
                  (append this-menu
                          (list
                           (cons (concat
                                  "method "
                                  (match-string-no-properties 2) ;; return type
                                  " "
                                  (match-string-no-properties 3) ;; func name
                                  (csharp--imenu-remove-param-names-from-paramlist
                                   (match-string-no-properties 4))) ;; fn params
                                 (match-beginning 1)))))
            (forward-sexp 1))


           ;; case 10: unknown open curly - just jump over it.
           ((looking-at "{")
            (forward-sexp 1))

           ;; case 11: none of the above. shouldn't happen?
           (t
            (forward-char 1)))))

    this-menu))


;; =======================================================
;; DPC Thu, 19 May 2011  11:25
;; There are two challenges with the imenu support: generating the
;; index, and generating a reasonable display for the index.  The index
;; generation is pretty straightforward: use regexi to locate
;; interesting stuff in the buffer.
;;
;; The menu generation is a little trickier.  Long lists of methods
;; mixed with properties and interfaces (etc) will be displayed in the
;; menu but will look Very Bad. Better to organize the menu into
;; submenus, organized primarily by category.  Also the menus should be
;; sorted, for ease of human scanning.  The next section of logic is
;; designed to do the stuff for the menu generation.


(defcustom csharp-imenu-max-similar-items-before-extraction 6
  "The maximum number of things of a particular
category (constructor, property, method, etc) that will be
separely displayed on an imenu without factoring them into a
separate submenu.

For example, if a module has 3 consructors, 5 methods, and 7
properties, and the value of this variable is 4, then upon
refactoring, the constructors will remain in the toplevel imenu
and the methods and properties will each get their own
category-specific submenu.

See also `csharp-imenu-min-size-for-sub-submenu'.

For more information on how csharp-mode uses imenu,
see `csharp-want-imenu', and `csharp-mode'.
"
  :type 'integer
  :group 'csharp)


(defcustom csharp-imenu-min-size-for-sub-submenu 18
  "The minimum number of imenu items  of a particular
category (constructor, property, method, etc) that will be
broken out into sub-submenus.

For example, if a module has 28 properties, then the properties will
be placed in a submenu, and then that submenu with be further divided
into smaller submenus.

See also `csharp-imenu-max-similar-items-before-extraction'

For more information on how csharp-mode uses imenu,
see `csharp-want-imenu', and `csharp-mode'.
"
  :type 'integer
  :group 'csharp)


(defun csharp--first-word (s)
  "gets the first word from the given string.
It had better be a string!"
  (car (split-string s nil t)))


(defun csharp--make-plural (s)
  "make a word plural. For use within the generated imenu."
  (cond
   ((string= s "prop") "properties")
   ((string= s "class") "classes")
   ((string= s "ctor") "constructors")
   (t (concat s "s"))))


(defun csharp--imenu-counts (list)
  "Returns an alist, each item is a cons cell where the car is a
unique first substring of an element of LIST, and the cdr is the
number of occurrences of that substring in elements in the
list.

For a complicated imenu generated for a large C# module, the result of
this fn will be something like this:

    ((\"(top)\"        . 1)
     (\"properties\"   . 38)
     (\"methods\"      . 12)
     (\"constructors\" . 7)
     (\"(bottom)\"     . 1))

"
  (flet ((helper (list new)
                 (if (null list) new
                   (let* ((elt (car list))
                          (topic (csharp--make-plural (csharp--first-word (car elt))))
                          (xelt (assoc topic new)))
                     (helper (cdr list)
                             (if xelt
                                 (progn (incf (cdr xelt)) new)
                               (cons (cons topic 1) new)))))))
    (nreverse (helper list nil))))



(defun csharp--imenu-get-submenu-size (n)
  "Gets the preferred size of submenus given N, the size of the
flat, unparceled menu.

Suppose there are 50 properties in a given C# module. This fn maps
from that number, to the maximum size of the submenus into which the
large set of properties should be broken.

Currently the submenu size for 50 is 12.  To change this, change
the lookup table.

The reason it's a lookup table and not a simple arithmetic
function: I think it would look silly to have 2 submenus each
with 24 items.  Sixteen or 18 items on a submenu seems fine when
you're working through 120 items total. But if you have only 28
items, better to have 3 submenus with 10 and 9 items each.  So
it's not a linear function. That's what this lookup tries to do.

"
  (let ((size-pairs '((100 . 22)
                      (80 . 20)
                      (60 . 18)
                      (40 . 15)
                      (30 . 14)
                      (24 . 11)
                      (0  . 9)))
        elt
        (r 0))

    (while (and size-pairs (eq r 0))
      (setq elt (car size-pairs))
      (if (> n (car elt))
          (setq r (cdr elt)))
      (setq size-pairs (cdr size-pairs)))
    r))



(defun csharp--imenu-remove-category-names (menu-list)
  "Input is a list, each element is (LABEL . LOCATION). This fn
returns a modified list, with the first word - the category name
- removed from each label.

"
  (mapcar (lambda (elt)
            (let ((tokens (split-string (car elt) "[ \t]" t)))
              (cons (mapconcat 'identity (cdr tokens) " ")
                    (cdr elt))))
          menu-list))

(defun string-indexof (s c)
  "Returns the index of the first occurrence of character C in string S.
Returns nil if not found.

See also, `string-lastindexof'

"
  (let ((len (length s))
        (i 0) ix c2)
    (while (and (< i len) (not ix))
      (setq c2 (aref s i))
      (if (= c c2)
          (setq ix i))
      (incf i))
    ix))

(defun string-lastindexof (s c)
  "Returns the index of the last occurrence of character C in string S.
Returns nil if not found.

See also, `string-indexof'

"
  (let ((i (1- (length s)))
        ix c2)
    (while (and (>= i 0) (not ix))
      (setq c2 (aref s i))
      (if (= c c2)
          (setq ix i))
      (decf i))
    ix))


(defun csharp--imenu-submenu-label (sig flavor)
  "generate a submenu label from the given signature, SIG.
The sig is a method signature, property type-and-name,
constructor, and so on, indicated by FLAVOR.

This fn returns a simple name that can be used in the label for a
break out submenu.

"
  (if (string= flavor "method")
      (let ((method-name (csharp--imenu-get-method-name-from-sig sig)))
        (substring method-name 0 (string-indexof method-name 40)))
    (substring sig (1+ (string-lastindexof sig 32)))))




(defun csharp--imenu-break-one-menu-into-submenus (menu-list)
  "Parcels a flat list MENU-LIST up into smaller sublists. It tries
to balance the number of sublists and the size of each sublist.

The max size of any sublist will be about 20 (arbitrary) and the
min size will be 7 or so. See `csharp--imenu-get-submenu-size'
for how this is done.

It does this destructively, using `nbutlast'.

Returns a new list, containing sublists.
"

  (let ((len (length menu-list))
        (counts (csharp--imenu-counts menu-list)))

    (cond
     ;; a small number, and all the same flavor
     ((and (< len csharp-imenu-min-size-for-sub-submenu) (= (length counts) 1))
      (csharp--imenu-remove-category-names
       (sort menu-list
             (if (string= (caar counts) "methods")
                 'csharp--imenu-item-method-name-comparer
               'csharp--imenu-item-basic-comparer))))

     ;; is the length already pretty short?
     ((< len csharp-imenu-min-size-for-sub-submenu)
      menu-list)

     ((/= (length counts) 1)
      menu-list)

     (t
      (let* ((lst    (sort menu-list
                           (if (string= (caar counts) "methods")
                               'csharp--imenu-item-method-name-comparer
                             'csharp--imenu-item-basic-comparer)))
             new
             (sz     (csharp--imenu-get-submenu-size len)) ;; goal max size of sublist
             (n      (ceiling (/ (* 1.0 len) sz))) ;; total number of sublists
             (adj-sz (ceiling (/ (* 1.0 len) n)))  ;; maybe a little less than sz
             (nsmall (mod (- adj-sz (mod len adj-sz)) adj-sz)) ;; num of (n-1) lists
             (i      0)
             (base-name (csharp--first-word (caar lst)))
             label
             chunksz
             this-chunk)

        (while lst
          (setq chunksz (if (> nsmall i) (1- adj-sz) adj-sz)
                this-chunk (csharp--imenu-remove-category-names
                            (nthcdr (- len chunksz) lst))
                lst (nbutlast lst chunksz)
                ;;label (format "%s %d" plural-name (- n i))
                label (concat "from " (csharp--imenu-submenu-label (caar this-chunk) base-name))
                new (cons (cons label this-chunk) new)
                len (- len chunksz))
          (incf i))
        new)))))



(defun csharp--imenu-break-into-submenus (menu-list)
  "For an imenu menu-list with category-based submenus,
possibly break a submenu into smaller sublists, based on size.

"
  (mapcar (lambda (elt)
            (if (imenu--subalist-p elt)
                (cons (car elt)
                      (csharp--imenu-break-one-menu-into-submenus (cdr elt)))
              elt))
          menu-list))





(defun csharp--imenu-reorg-alist-intelligently (menu-alist)
  "Accepts an imenu alist. Returns an alist, reorganized.
Things get sorted, factored out into category submenus,
and split into multiple submenus, where conditions warrant.

For example, suppose this imenu alist is generated from a scan:

    ((\"usings (4)\" . 1538)
     (\"namespace Ionic.Zip\"
      (\"(top)\" . 1651)
      (\"partial class Ionic.Zip.ZipFile\"
       (\"(top)\" . 5473)
       (\"prop FullScan\" . 8036)
           ...
       (\"prop Comment\" . 21118)
       (\"prop Verbose\" . 32278)
       (\"method override String ToString\" . 96577)
       (\"method internal void NotifyEntryChanged\" . 97608)
          ....
       (\"method internal void Reset\" . 98231)
       (\"ctor ZipFile\" . 103598)
           ...
       (\"ctor ZipFile\" . 109723)
       (\"ctor ZipFile\" . 116487)
       (\"indexer int\" . 121232)
       (\"indexer String\" . 124933)
       (\"(bottom)\" . 149777))
      (\"public enum Zip64Option\" . 153839)
      (\"enum AddOrUpdateAction\" . 154815)
      (\"(bottom)\" . 154893)))


This is displayed as a toplevel menu with 2 items; the namespace
menu has 5 items (top, bottom, the 2 enums, and the class).  The
class menu has 93 items. It needs to be reorganized to be more usable.

After transformation of the alist through this fn, the result is:

    ((\"usings (4)\" . 1538)
     (\"namespace Ionic.Zip\"
      (\"(top)\" . 1651)
      (\"partial class Ionic.Zip.ZipFile\"
       (\"(top)\" . 5473)
       (\"properties\"
        (\"WriteStream\" . 146489)
        (\"Count\" . 133827)
            ....
        (\"BufferSize\" . 12837)
        (\"FullScan\" . 8036))
       (\"methods\"
        (\"virtual void Dispose\" . 144389)
        (\"void RemoveEntry\" . 141027)
           ....
        (\"method override String ToString\" . 96577)
        (\"method bool ContainsEntry\" . 32517))
       (\"constructors\"
        (\"ZipFile\" . 116487)
           ....
        (\"ZipFile\" . 105698)
        (\"ZipFile\" . 103598))
       (\"indexer int\" . 121232)
       (\"indexer String\" . 124933)
       (\"(bottom)\" . 149777))
      (\"public enum Zip64Option\" . 153839)
      (\"enum AddOrUpdateAction\" . 154815)
      (\"(bottom)\" . 154893)))

All menus are the same except the class menu, which has been
organized into subtopics, each of which gets its own cascaded
submenu.  If the submenu itself holds more than
`csharp-imenu-max-similar-items-before-extraction' items that are
all the same flavor (properties, methods, etc), thos get split
out into multiple submenus.

"
  (let ((counts (csharp--imenu-counts menu-alist)))
    (flet ((helper
            (list new)
            (if (null list)
                new
              (let* ((elt (car list))
                     (topic (csharp--make-plural (csharp--first-word (car elt))))
                     (xelt (assoc topic new)))
                (helper
                 (cdr list)
                 (if xelt
                     (progn
                       (rplacd xelt (cons elt (cdr xelt)))
                       new)
                   (cons

                    (cond
                     ((> (cdr (assoc topic counts))
                         csharp-imenu-max-similar-items-before-extraction)
                      (cons topic (list elt)))

                     ((imenu--subalist-p elt)
                      (cons (car elt)
                            (csharp--imenu-reorg-alist-intelligently (cdr elt))))
                     (t
                      elt))

                    new)))))))

      (csharp--imenu-break-into-submenus
       (nreverse (helper menu-alist nil))))))




(defun csharp-imenu-create-index ()
  "This function is called by imenu to create an index for the
current C# buffer, conforming to the format specified in
`imenu--index-alist' .

See `imenu-create-index-function' for background information.

To produce the index, which lists the classes, functions,
methods, and properties for the current buffer, this function
scans the entire buffer.

This can take a long time for a large buffer. The scan uses
regular expressions that attempt to match on the general-case C#
syntax, for classes and functions, generic types, base-classes,
implemented interfaces, and so on. This can be time-consuming.
For a large source file, say 160k, it can take 10 seconds or more.
The UI hangs during the scan.

imenu calls this fn when it feels like it, I suppose when it
thinks the buffer has been updated. The user can also kick it off
explicitly by selecting *Rescan* from the imenu menu.

After generating the hierarchical list of props, methods,
interfaces, classes, and namespaces, csharp-mode re-organizes the
list as appropriate:

 - it extracts sets of like items into submenus. All properties
   will be placed on a submenu. See
   `csharp-imenu-max-similar-items-before-extraction' for a way
   to tune this.

 - it converts those submenus into sub-submenus, if there are more than
   `csharp-imenu-min-size-for-sub-submenu' items.

 - it sorts each set of items on the outermost menus lexicographically.

The result of these transformations is what is provided to imenu
to generate the visible menus.  Just FYI - the reorganization of
the scan results is much much faster than the actual generation
of the scan results. If you're looking to save time, the re-org
logic is not where the cost is.

imenu itself likes to sort the menus. See `imenu--split-menu' and
also `csharp--imenu-split-menu-patch', which is advice that
attempts to disable the weird re-jiggering that imenu performs.

"
  ;; I think widen/narrow causes the buffer to be marked as
  ;; modified. This is a bit surprising, but I have no other
  ;; explanation for the source of the problem.
  ;; So I use `c-save-buffer-state' so that the buffer is not
  ;; marked modified when the scan completes.

  (c-save-buffer-state ()
      (save-excursion
        (save-restriction
          (widen)
          (goto-char (point-min))

          (let ((index-alist
                 (csharp--imenu-create-index-helper nil "" t t)))

            (csharp--imenu-reorg-alist-intelligently index-alist)

            ;;index-alist

            ;; What follows is No longer used.
            ;; =======================================================

            ;; If the index menu contains exactly one element, and it is
            ;; a namespace menu, then remove it.  This simplifies the
            ;; menu, and results in no loss of information: all types
            ;; get fully-qualified names anyway. This will probably
            ;; cover the majority of cases; often a C# source module
            ;; defines either one class, or a set of related classes
            ;; inside a single namespace.

            ;; To remove that namespace, we need to prune & graft the tree.
            ;; Remove the ns hierarchy level, but also remove the 1st and
            ;; last elements in the sub-menu, which represent the top and
            ;; bottom of the namespace.

            ;; (if (and
            ;;      (= 1 (length index-alist))
            ;;      (consp (car index-alist))
            ;;      (let ((tokens (split-string
            ;;                     (car (car index-alist))
            ;;                     "[ \t]" t)))
            ;;        (and (<= 1 (length tokens))
            ;;             (string= (downcase
            ;;                       (nth 0 tokens)) "namespace"))))
            ;;
            ;;     (let (elt
            ;;           (newlist (cdar index-alist)))
            ;;       (setf (car (car newlist))  (car (car index-alist)))
            ;;       newlist)
            ;;
            ;;   index-alist)

            )))))


;; ==================================================================




;; ==================================================================
;; C# code-doc insertion magic
;; ==================================================================
;;
;; In Visual Studio, if you type three slashes, it immediately expands into
;; an inline code-documentation fragment.  The following method does the
;; same thing.
;;
;; This is the kind of thing that could be handled by YASnippet or
;; another similarly flexible snippet framework. But I don't want to
;; introduce a dependency on yasnippet to csharp-mode. So the capability
;; must live within csharp-mode itself.

(defun csharp-maybe-insert-codedoc (arg)

  "Insert an xml code documentation template as appropriate, when
typing slashes.  This fn gets bound to / (the slash key), in
csharp-mode.  If the slash being inserted is not the third
consecutive slash, the slash is inserted as normal.  If it is the
third consecutive slash, then a xml code documentation template
may be inserted in some cases. For example,

  a <summary> template is inserted if the prior line is empty,
        or contains only an open curly brace;
  a <remarks> template is inserted if the prior word
        closes the <summary> element;
  a <returns> template is inserted if the prior word
        closes the <remarks> element;
  an <example> template is inserted if the prior word closes
        the <returns> element;
  a <para> template is inserted if the prior word closes
        a <para> element.

In all other cases the slash is inserted as normal.

If you want the default cc-mode behavior, which implies no automatic
insertion of xml code documentation templates, then use this in
your `csharp-mode-hook' function:

     (local-set-key (kbd \"/\") 'c-electric-slash)

 "
  (interactive "*p")
  ;;(message "csharp-maybe-insert-codedoc")
  (let (
        (cur-point (point))
        (char last-command-event)
        (cb0 (char-before (- (point) 0)))
        (cb1 (char-before (- (point) 1)))
        is-first-non-whitespace
        did-auto-insert
        )

    ;; check if two prior chars were slash, in other words,
    ;; check if this is the third slash in a row.
    (if (and (= char ?/) cb0 (= ?/ cb0) cb1 (= ?/ cb1))

        (progn
          ;;(message "yes - this is the third consecutive slash")
          (setq is-first-non-whitespace
                (save-excursion
                  (back-to-indentation)
                  (= cur-point (+ (point) 2))))

          (if is-first-non-whitespace
              ;; This is a 3-slash sequence.  It is the first non-whitespace text
              ;; on the line. Now we need to examine the surrounding context
              ;; in order to determine which xml cod doc template to insert.
              (let (word-back char0 char1
                              word-fore char-0 char-1
                              text-to-insert         ;; text to insert in lieu of slash
                              fn-to-call     ;; func to call after inserting text
                              (preceding-line-is-empty (or
                                                        (= (line-number-at-pos) 1)
                                                        (save-excursion
                                                          (forward-line -1)
                                                          (beginning-of-line)
                                                          (looking-at "[ \t]*$\\|[ \t]*{[ \t]*$"))))
                              (flavor 0) ;; used only for diagnostic purposes
                              )

                ;;(message "starting a 3-slash comment")
                ;; get the prior word, and the 2 chars preceding it.
                (backward-word)

                (setq word-back (thing-at-point 'word)
                      char0 (char-before (- (point) 0))
                      char1 (char-before (- (point) 1)))

                ;; restore prior position
                (goto-char cur-point)

                ;; get the following word, and the 2 chars preceding it.
                (forward-word)
                (backward-word)
                (setq word-fore (thing-at-point 'word)
                      char-0 (char-before (- (point) 0))
                      char-1 (char-before (- (point) 1)))

                ;; restore prior position again
                (goto-char cur-point)

                (cond
                 ;; The preceding line is empty, or all whitespace, or
                 ;; contains only an open-curly.  In this case, insert a
                 ;; summary element pair.
                 (preceding-line-is-empty
                  (setq text-to-insert  "/ <summary>\n///   \n/// </summary>"
                        flavor 1) )

                 ;; The preceding word closed a summary element.  In this case,
                 ;; if the forward word does not open a remarks element, then
                 ;; insert a remarks element.
                 ((and (string-equal word-back "summary") (eq char0 ?/)  (eq char1 ?<))
                  (if (not (and (string-equal word-fore "remarks") (eq char-0 ?<)))
                      (setq text-to-insert "/ <remarks>\n///   <para>\n///     \n///   </para>\n/// </remarks>"
                            flavor 2)))

                 ;; The preceding word closed the remarks section.  In this case,
                 ;; insert an example element.
                 ((and (string-equal word-back "remarks")  (eq char0 ?/)  (eq char1 ?<))
                  (setq text-to-insert "/ <example>\n///   \n/// </example>"
                        flavor 3))

                 ;; The preceding word closed the example section.  In this
                 ;; case, insert an returns element.  This isn't always
                 ;; correct, because sometimes the xml code doc is attached to
                 ;; a class or a property, neither of which has a return
                 ;; value. A more intelligent implementation would inspect the
                 ;; syntax state and only inject a returns element if
                 ;; appropriate.
                 ((and (string-equal word-back "example")  (eq char0 ?/)  (eq char1 ?<))
                  (setq text-to-insert "/ <returns></returns>"
                        fn-to-call (lambda ()
                                     (backward-word)
                                     (backward-char)
                                     (backward-char)
                                     (c-indent-line-or-region)
                                     )
                        flavor 4))

                 ;; The preceding word opened the remarks section, or it
                 ;; closed a para section. In this case, insert a para
                 ;; element, using appropriate indentation with respect to the
                 ;; prior tag.
                 ((or
                   (and (string-equal word-back "remarks")  (eq char0 ?<)  (or (eq char1 32) (eq char1 9)))
                   (and (string-equal word-back "para")     (eq char0 ?/)  (eq char1 ?<)))

                  (let (prior-point spacer)
                    (save-excursion
                      (backward-word)
                      (backward-char)
                      (backward-char)
                      (setq prior-point (point))
                      (skip-chars-backward "\t ")
                      (setq spacer (buffer-substring (point) prior-point))
                      ;;(message (format "pt(%d) prior(%d) spacer(%s)" (point) prior-point spacer))
                      )

                    (if (string-equal word-back "remarks")
                        (setq spacer (concat spacer "   ")))

                    (setq text-to-insert (format "/%s<para>\n///%s  \n///%s</para>"
                                                 spacer spacer spacer)
                          flavor 6)))

                 ;; The preceding word opened a para element.  In this case, if
                 ;; the forward word does not close the para element, then
                 ;; close the para element.
                 ;; --
                 ;; This is a nice idea but flawed.  Suppose I have a para element with some
                 ;; text in it. If I position the cursor at the first line, then type 3 slashes,
                 ;; I get a close-element, and that would be inappropriate.  Not sure I can
                 ;; easily solve that problem, so the best thing might be to simply punt, and
                 ;; require people to close their own elements.
                 ;;
                 ;;              ( (and (string-equal word-back "para")  (eq char0 60)  (or (eq char1 32) (eq char1 9)))
                 ;;                (if (not (and (string-equal word-fore "para") (eq char-0 47) (eq char-1 60) ))
                 ;;                    (setq text-to-insert "/   \n/// </para>\n///"
                 ;;                          fn-to-call (lambda ()
                 ;;                                       (previous-line)
                 ;;                                       (end-of-line)
                 ;;                                       )
                 ;;                          flavor 7) )
                 ;;                )

                 ;; the default case - do nothing
                 (t nil))

                (if text-to-insert
                    (progn
                      ;;(message (format "inserting special text (f(%d))" flavor))

                      ;; set the flag, that we actually inserted text
                      (setq did-auto-insert t)

                      ;; save point of beginning of insertion
                      (setq cur-point (point))

                      ;; actually insert the text
                      (insert text-to-insert)

                      ;; indent the inserted string, and re-position point, either through
                      ;; the case-specific fn, or via the default progn.
                      (if fn-to-call
                          (funcall fn-to-call)

                        (let ((newline-count 0) (pos 0) ix)

                          ;; count the number of newlines in the inserted string
                          (while (string-match "\n" text-to-insert pos)
                            (setq pos (match-end 0)
                                  newline-count (+ newline-count 1) )
                            )

                          ;; indent what we just inserted
                          (c-indent-region cur-point (point) t)

                          ;; move up n/2 lines. This assumes that the
                          ;; inserted text is ~symmetric about the halfway point.
                          ;; The assumption holds if the xml code doc uses a
                          ;; begin-elt and end-elt on a new line all by themselves,
                          ;; and a blank line in between them where the point should be.
                          ;; A more intelligent implementation would use a specific
                          ;; marker string, like @@DOT, to note the desired point.
                          (forward-line (- 0 (/ newline-count 2)))
                          (end-of-line)))))))))

    (if (not did-auto-insert)
        (self-insert-command (prefix-numeric-value arg)))))

;; ==================================================================
;; end of c# code-doc insertion magic
;; ==================================================================




;; ==================================================================
;; c# fontification extensions
;; ==================================================================
;; Commentary:
;;
;; The purpose of the following code is to fix font-lock for C#,
;; specifically for the verbatim-literal strings. C# is a cc-mode
;; language and strings are handled mostly like other c-based
;; languages. The one exception is the verbatim-literal string, which
;; uses the syntax @"...".
;;
;; `parse-partial-sexp' treats those strings as just regular strings,
;; with the @ a non-string character.  This is fine, except when the
;; verblit string ends in a slash, in which case, font-lock breaks from
;; that point onward in the buffer.
;;
;; This is an attempt to fix that.
;;
;; The idea is to scan the buffer in full for verblit strings, and apply the
;; appropriate syntax-table text properties for verblit strings. Also setting
;; `parse-sexp-lookup-properties' to t tells `parse-partial-sexp'
;; to use the syntax-table text properties set up by the scan as it does
;; its parse.
;;
;; Also need to re-scan after any changes in the buffer, but on a more
;; limited region.
;;


;; ;; I don't remember what this is supposed to do,
;; ;; or how I figured out the value.
;; ;;
;; (defconst csharp-font-lock-syntactic-keywords
;;   '(("\\(@\\)\\(\"\\)[^\"]*\\(\"\\)\\(\"\\)[^\"]*\\(\"\\)[^\"]"
;;      (1 '(6)) (2 '(7)) (3 '(1)) (4 '(1)) (5 '(7))
;;                  ))
;;   "Highlighting of verbatim literal strings. See also the variable
;;   `font-lock-keywords'.")



(defun csharp-time ()
  "returns the time of day as a string.  Used in the `csharp-log' function."
  (substring (current-time-string) 11 19)) ;24-hr time


(defun csharp-log (level text &rest args)
  "Log a message at level LEVEL.
If LEVEL is higher than `csharp-log-level', the message is
ignored.  Otherwise, it is printed using `message'.
TEXT is a format control string, and the remaining arguments ARGS
are the string substitutions (see `format')."
  (if (<= level csharp-log-level)
      (let* ((msg (apply 'format text args)))
        (message "C# %s %s" (csharp-time) msg))))



(defun csharp-max-beginning-of-stmt ()
  "Return the greater of `c-beginning-of-statement-1' and
`c-beginning-of-statement' .  I don't understand why both of
these methods are necessary or why they differ. But they do."

  (let (dash
        nodash
        (curpos (point)))

    ;; I think this may need a save-excursion...
    ;; Calling c-beginning-of-statement-1 resets the point!

    (setq dash (progn (c-beginning-of-statement-1) (point)))
    (csharp-log 3 "max-bostmt dash(%d)" dash)
    (goto-char curpos)

    (setq nodash (progn (c-beginning-of-statement 1) (point)))
    (csharp-log 3 "max-bostmt nodash(%d)" nodash)
    (goto-char curpos)

    (max dash nodash)))





(defun csharp-set-vliteral-syntax-table-properties (beg end)
  "Scan the buffer text between BEG and END, a verbatim literal
string, setting and clearing syntax-table text properties where
necessary.

We need to modify the default syntax-table text property in these cases:
  (backslash)    - is not an escape inside a verbatim literal string.
  (double-quote) - can be a literal quote, when doubled.

BEG is the @ delimiter. END is the 'old' position of the ending quote.

see http://www.sunsite.ualberta.ca/Documentation/Gnu/emacs-lisp-ref-21-2.7/html_node/elisp_592.html
for the list of syntax table numeric codes.

"

  (csharp-log 3 "set-vlit-syntax-table:  beg(%d) end(%d)" beg end)

  (if (and (> beg 0) (> end 0))

      (let ((curpos beg)
            (state 0))

        (c-clear-char-properties beg end 'syntax-table)

        (while (<= curpos end)

          (cond
           ((= state 0)
            (if (= (char-after curpos) ?@)
                (progn
                  (c-put-char-property curpos 'syntax-table '(6)) ; (6) = expression prefix, (3) = symbol
                  ;;(message (format "set-s-t: prefix pos(%d) chr(%c)" beg (char-after beg)))
                  )
              )
            (setq state (+ 1 state)))

           ((= state 1)
            (if (= (char-after curpos) ?\")
                (progn
                  (c-put-char-property curpos 'syntax-table '(7)) ; (7) = string quote
                  ;;(message (format "set-s-t: open quote pos(%d) chr(%c)"
                  ;; curpos (char-after curpos)))
                  ))
            (setq state (+ 1 state)))

           ((= state 2)
            (cond
             ;; handle backslash inside the string
             ((= (char-after curpos) ?\\)
              (c-put-char-property curpos 'syntax-table '(2)) ; (1) = punctuation, (2) = word
              ;;(message (format "set-s-t: backslash word pos(%d) chr(%c)" curpos (char-after curpos)))
              )

             ;; doubled double-quote
             ((and
               (= (char-after curpos) ?\")
               (= (char-after (+ 1 curpos)) ?\"))
              (c-put-char-property curpos 'syntax-table '(2)) ; (1) = punctuation, (2) = word
              (c-put-char-property (+ 1 curpos) 'syntax-table '(2)) ; (1) = punctuation
              ;;(message (format "set-s-t: double doublequote pos(%d) chr(%c)" curpos (char-after curpos)))
              (setq curpos (+ curpos 1))
              )

             ;; a single double-quote, which should be a string terminator
             ((= (char-after curpos) ?\")
              (c-put-char-property curpos 'syntax-table '(7)) ; (7) = string quote
              ;;(message (format "set-s-t: close quote pos(%d) chr(%c)" curpos (char-after curpos)))
              ;;go no further
              (setq state (+ 1 state)))

             ;; everything else
             (t
              ;;(message (format "set-s-t: none pos(%d) chr(%c)" curpos (char-after curpos)))
              nil))))
          ;; next char
          (setq curpos (+ curpos 1))))))



(defun csharp-end-of-verbatim-literal-string (&optional lim)
  "Moves to and returns the position of the end quote of the verbatim literal
string.  When calling, point should be on the @ of the verblit string.
If it is not, then no movement is performed and `point' is returned.

This function ignores text properties. In fact it is the
underlying scanner used to set the text properties in a C# buffer.
"

  (csharp-log 3 "end-of-vlit-string: point(%d) c(%c)" (point) (char-after))

  (let (curpos
        (max (or lim (point-max))))

    (if (not (looking-at "@\""))
        (point)
      (forward-char 2) ;; pass up the @ sign and first quote
      (setq curpos (point))

      ;; Within a verbatim literal string, a doubled double-quote
      ;; escapes the double-quote."
      (while (and                                  ;; process characters...
              (or                                  ;; while...
               (not (eq (char-after curpos) ?\"))  ;; it's not a quote
               (eq (char-after (+ curpos 1)) ?\")) ;; or, its a double (double) quote
              (< curpos max))                      ;; and we're not done yet

        (cond
         ((and (eq (char-after curpos) ?\")        ;; it's a double-quote.
               (eq (char-after (+ curpos 1)) ?\"))
          (setq curpos (+ 2 curpos)))              ;; Skip 2
         (t                                        ;; anything else
          (setq curpos (+ 1 curpos)))))            ;; skip fwd 1
      curpos)))




(defun csharp-scan-for-verbatim-literals-and-set-props (&optional beg end)
  "Scans the buffer, between BEG and END, for verbatim literal
strings, and sets override text properties on each string to
allow proper syntax highlighting, indenting, and cursor movement.

BEG and END define the limits of the scan.  When nil, they
default to `point-min' and `point-max' respectively.

Setting text properties generally causes the buffer to be marked
as modified, but this fn suppresses that via the
`c-buffer-save-state' macro, for any changes in text properties
that it makes.  This fn also ignores the read-only setting on a
buffer, using the same macro.

This fn is called when a csharp-mode buffer is loaded, with BEG
and END set to nil, to do a full scan.  It is also called on
every buffer change, with the BEG and END set to the values for
the change.

The return value is nil if the buffer was not a csharp-mode
buffer. Otherwise it is the last cursor position examined by the
scan.
"

  (if (not (c-major-mode-is 'csharp-mode)) ;; don't scan if not csharp mode
      nil
    (save-excursion
      (c-save-buffer-state
          ((curpos (or beg (point-min)))
           (lastpos (or end (point-max)))
           (state 0) (start 0) (cycle 0)
           literal eos limits)

        (csharp-log 3 "verblit scan")
        (goto-char curpos)

        (while (and (< curpos lastpos) (< cycle 10000))
          (cond

           ;; Case 1: current char is a @ sign
           ;; --------------------------------------------
           ;; Check to see if it demarks the beginning of a verblit
           ;; string.
           ((= ?@ (char-after curpos))

            ;; are we in a comment?   a string?  Maybe the @ is a prefix
            ;; to allow the use of a reserved word as a symbol. Let's find out.

            ;; not sure why I need both of the following.
            (syntax-ppss-flush-cache 1)
            (parse-partial-sexp 1 curpos)
            (goto-char curpos)
            (setq literal (csharp-in-literal))
            (cond

             ;; Case 1.A: it's a @ within a string.
             ;; --------------------------------------------
             ;; This should never happen, because this scanner hops over strings.
             ;; But it might happen if the scan starts at an odd place.
             ((eq literal 'string) nil)

             ;; Case 1.B: The @ is within a comment.  Hop over it.
             ((and (memq literal '(c c++))
                   ;; This is a kludge for XEmacs where we use
                   ;; `buffer-syntactic-context', which doesn't correctly
                   ;; recognize "\*/" to end a block comment.
                   ;; `parse-partial-sexp' which is used by
                   ;; `c-literal-limits' will however do that in most
                   ;; versions, which results in that we get nil from
                   ;; `c-literal-limits' even when `c-in-literal' claims
                   ;; we're inside a comment.
                   ;;(setq limits (c-literal-limits start)))
                   (setq limits (c-literal-limits)))

              ;; advance to the end of the comment
              (if limits
                  (progn
                    (csharp-log 4 "scan: jump end comment A (%d)" (cdr limits))
                    (setq curpos (cdr limits)))))


             ;; Case 1.B: curpos is at least 2 chars before the last
             ;; position to examine, and, the following char is a
             ;; double-quote (ASCII 34).
             ;; --------------------------------------------
             ;; This looks like the beginning of a verbatim string
             ;; literal.
             ((and (< (+ 2 curpos) lastpos)
                   (= ?\" (char-after (+ 1 curpos))))

              (setq eos (csharp-end-of-verbatim-literal-string))
              ;; set override syntax properties on the verblit string
              (csharp-set-vliteral-syntax-table-properties curpos eos)

              (csharp-log 4 "scan: jump end verblit string (%d)" eos)
              (setq curpos eos))))


           ;; Case 2: current char is a double-quote.
           ;; --------------------------------------------
           ;; If this is a string, we hop over it, on the assumption that
           ;; this scanner need not bother with regular literal strings, which
           ;; get the proper syntax with the generic approach.
           ;; If in a comment, hop over the comment.
           ((= ?\" (char-after curpos))
            (goto-char curpos)
            (setq literal (c-in-literal))
            (cond

             ;; Case 2.A: a quote within a string
             ;; --------------------------------------------
             ;; This shouldn't happen, because we hop over strings.
             ;; But it might.
             ((eq literal 'string) nil)

             ;; Case 2.B: a quote within a comment
             ;; --------------------------------------------
             ((and (memq literal '(c c++))
                   ;; This is a kludge for XEmacs where we use
                   ;; `buffer-syntactic-context', which doesn't correctly
                   ;; recognize "\*/" to end a block comment.
                   ;; `parse-partial-sexp' which is used by
                   ;; `c-literal-limits' will however do that in most
                   ;; versions, which results in that we get nil from
                   ;; `c-literal-limits' even when `c-in-literal' claims
                   ;; we're inside a comment.
                   ;;(setq limits (c-literal-limits start)))
                   (setq limits (c-literal-limits)))

              ;; advance to the end of the comment
              (if limits
                  (progn
                    (setq curpos (cdr limits))
                    (csharp-log 3 "scan: jump end comment B (%s)" curpos))))


             ;; Case 2.C: Not in a comment, and not in a string.
             ;; --------------------------------------------
             ;; This is the beginning of a literal (but not verbatim) string.
             (t
              (forward-char 1) ;; pass up the quote
              (if (consp (setq limits (c-literal-limits)))
                  (progn
                    (csharp-log 4 "scan: jump end literal (%d)" (cdr limits))
                    (setq curpos (cdr limits))))))))

          (setq cycle (+ 1 cycle))
          (setq curpos (+ 1 curpos))
          (c-safe (goto-char curpos)))))))



(defun csharp--before-font-lock (beg end old-len)
  "Adjust`syntax-table' properties on the region affected by the change
in a csharp-mode buffer.

This function is the C# value for `c-before-font-lock-function'.
It intended to be called only by the cc-mode runtime.

It prepares the buffer for font locking, hence must get called
before `font-lock-after-change-function'.

It does hidden buffer changes.

BEG, END and OLD-LEN have the same meaning here as for any
after-change function.

Point is undefined both before and after this function call.
The return value is meaningless, and is ignored by cc-mode.
"
  (csharp-log 2 "before font lock %d %d %d %d" beg end old-len (point))
  (let ((start-scan (progn
                      ;; is this right?  I think
                      (c-beginning-of-statement 1)
                      (point))))
    (csharp-scan-for-verbatim-literals-and-set-props start-scan end)))



(c-lang-defconst c-before-font-lock-function
  csharp 'csharp--before-font-lock)

;; ==================================================================
;; end of c# fontification extensions
;; ==================================================================





;; ==================================================================
;; C#-specific optimizations of cc-mode funcs
;; ==================================================================

;; There's never a need to move over an Obj-C directive in csharp-mode.
(defadvice c-forward-objc-directive (around
                                     csharp-mode-advice-2
                                     compile activate)
  (if (c-major-mode-is 'csharp-mode)
      nil
    ad-do-it)
  )

;; ==================================================================
;; end of C#-specific optimizations of cc-mode funcs
;; ==================================================================








;; ==================================================================
;; c# - monkey-patching of basic parsing logic
;; ==================================================================
;;
;; The following 2 defuns redefine functions from cc-mode, to add
;; special cases for C#.  These primarily deal with indentation of
;; instance initializers, which are somewhat unique to C#.  I couldn't
;; figure out how to get cc-mode to do what C# needs, without modifying
;; these defuns.
;;

(defun c-looking-at-inexpr-block (lim containing-sexp &optional check-at-end)
  ;; Return non-nil if we're looking at the beginning of a block
  ;; inside an expression.  The value returned is actually a cons of
  ;; either 'inlambda, 'inexpr-statement or 'inexpr-class and the
  ;; position of the beginning of the construct.
  ;;
  ;; LIM limits the backward search.  CONTAINING-SEXP is the start
  ;; position of the closest containing list.  If it's nil, the
  ;; containing paren isn't used to decide whether we're inside an
  ;; expression or not.  If both LIM and CONTAINING-SEXP are used, LIM
  ;; needs to be farther back.
  ;;
  ;; If CHECK-AT-END is non-nil then extra checks at the end of the
  ;; brace block might be done.  It should only be used when the
  ;; construct can be assumed to be complete, i.e. when the original
  ;; starting position was further down than that.
  ;;
  ;; This function might do hidden buffer changes.

  (save-excursion
    (let ((res 'maybe) passed-paren
          (closest-lim (or containing-sexp lim (point-min)))
          ;; Look at the character after point only as a last resort
          ;; when we can't disambiguate.
          (block-follows (and (eq (char-after) ?{) (point))))

      (while (and (eq res 'maybe)
                  (progn (c-backward-syntactic-ws)
                         (> (point) closest-lim))
                  (not (bobp))
                  (progn (backward-char)
                         (looking-at "[\]\).]\\|\w\\|\\s_"))
                  (c-safe (forward-char)
                          (goto-char (scan-sexps (point) -1))))

        (setq res
              (if (looking-at c-keywords-regexp)
                  (let ((kw-sym (c-keyword-sym (match-string 1))))
                    (cond
                     ((and block-follows
                           (c-keyword-member kw-sym 'c-inexpr-class-kwds))
                      (and (not (eq passed-paren ?\[))

                           ;; dinoch Thu, 22 Apr 2010  18:20
                           ;; ============================================
                           ;; looking at new MyType() { ... }
                           ;; means this is a brace list, so, return nil,
                           ;; implying NOT looking-at-inexpr-block
                           (not
                            (and (c-major-mode-is 'csharp-mode)
                                 (looking-at "new[ \t\n\f\v\r]+\\([[:alnum:]_]+\\)\\b")))

                           (or (not (looking-at c-class-key))
                               ;; If the class instantiation is at the start of
                               ;; a statement, we don't consider it an
                               ;; in-expression class.
                               (let ((prev (point)))
                                 (while (and
                                         (= (c-backward-token-2 1 nil closest-lim) 0)
                                         (eq (char-syntax (char-after)) ?w))
                                   (setq prev (point)))
                                 (goto-char prev)
                                 (not (c-at-statement-start-p)))
                               ;; Also, in Pike we treat it as an
                               ;; in-expression class if it's used in an
                               ;; object clone expression.
                               (save-excursion
                                 (and check-at-end
                                      (c-major-mode-is 'pike-mode)
                                      (progn (goto-char block-follows)
                                             (zerop (c-forward-token-2 1 t)))
                                      (eq (char-after) ?\())))
                           (cons 'inexpr-class (point))))
                     ((c-keyword-member kw-sym 'c-inexpr-block-kwds)
                      (when (not passed-paren)
                        (cons 'inexpr-statement (point))))
                     ((c-keyword-member kw-sym 'c-lambda-kwds)
                      (when (or (not passed-paren)
                                (eq passed-paren ?\())
                        (cons 'inlambda (point))))
                     ((c-keyword-member kw-sym 'c-block-stmt-kwds)
                      nil)
                     (t
                      'maybe)))

                (if (looking-at "\\s(")
                    (if passed-paren
                        (if (and (eq passed-paren ?\[)
                                 (eq (char-after) ?\[))
                            ;; Accept several square bracket sexps for
                            ;; Java array initializations.
                            'maybe)
                      (setq passed-paren (char-after))
                      'maybe)
                  'maybe))))

      (if (eq res 'maybe)
          (when (and c-recognize-paren-inexpr-blocks
                     block-follows
                     containing-sexp
                     (eq (char-after containing-sexp) ?\())
            (goto-char containing-sexp)
            (if (or (save-excursion
                      (c-backward-syntactic-ws lim)
                      (and (> (point) (or lim (point-min)))
                           (c-on-identifier)))
                    (and c-special-brace-lists
                         (c-looking-at-special-brace-list)))
                nil
              (cons 'inexpr-statement (point))))

        res))))





(defun c-inside-bracelist-p (containing-sexp paren-state)
  ;; return the buffer position of the beginning of the brace list
  ;; statement if we're inside a brace list, otherwise return nil.
  ;; CONTAINING-SEXP is the buffer pos of the innermost containing
  ;; paren.  PAREN-STATE is the remainder of the state of enclosing
  ;; braces
  ;;
  ;; N.B.: This algorithm can potentially get confused by cpp macros
  ;; placed in inconvenient locations.  It's a trade-off we make for
  ;; speed.
  ;;
  ;; This function might do hidden buffer changes.
  (or
   ;; This will pick up brace list declarations.
   (c-safe
     (save-excursion
       (goto-char containing-sexp)
       (c-safe (c-forward-sexp -1))
       (let (bracepos)
         (if (and (or (looking-at c-brace-list-key)

                      (progn
                        (c-safe (c-forward-sexp -1))
                        (looking-at c-brace-list-key))

                      ;; dinoch Thu, 22 Apr 2010  18:20
                      ;; ============================================
                      ;; looking enum Foo : int
                      ;; means this is a brace list, so, return nil,
                      ;; implying NOT looking-at-inexpr-block

                      (and (c-major-mode-is 'csharp-mode)
                           (progn
                             (c-safe (c-forward-sexp -1))
                             (looking-at csharp-enum-decl-re))))

                  (setq bracepos (c-down-list-forward (point)))
                  (not (c-crosses-statement-barrier-p (point)
                                                      (- bracepos 2))))
             (point)))))

   ;; this will pick up array/aggregate init lists, even if they are nested.
   (save-excursion
     (let ((class-key
            ;; Pike can have class definitions anywhere, so we must
            ;; check for the class key here.
            (and (c-major-mode-is 'pike-mode)
                 c-decl-block-key))
           bufpos braceassignp lim next-containing)
       (while (and (not bufpos)
                   containing-sexp)
         (when paren-state
           (if (consp (car paren-state))
               (setq lim (cdr (car paren-state))
                     paren-state (cdr paren-state))
             (setq lim (car paren-state)))
           (when paren-state
             (setq next-containing (car paren-state)
                   paren-state (cdr paren-state))))
         (goto-char containing-sexp)
         (if (c-looking-at-inexpr-block next-containing next-containing)
             ;; We're in an in-expression block of some kind.  Do not
             ;; check nesting.  We deliberately set the limit to the
             ;; containing sexp, so that c-looking-at-inexpr-block
             ;; doesn't check for an identifier before it.
             (setq containing-sexp nil)
           ;; see if the open brace is preceded by = or [...] in
           ;; this statement, but watch out for operator=
           (setq braceassignp 'dontknow)
           (c-backward-token-2 1 t lim)
           ;; Checks to do only on the first sexp before the brace.
           (when (and c-opt-inexpr-brace-list-key
                      (eq (char-after) ?\[))
             ;; In Java, an initialization brace list may follow
             ;; directly after "new Foo[]", so check for a "new"
             ;; earlier.
             (while (eq braceassignp 'dontknow)
               (setq braceassignp
                     (cond ((/= (c-backward-token-2 1 t lim) 0) nil)
                           ((looking-at c-opt-inexpr-brace-list-key) t)
                           ((looking-at "\\sw\\|\\s_\\|[.[]")
                            ;; Carry on looking if this is an
                            ;; identifier (may contain "." in Java)
                            ;; or another "[]" sexp.
                            'dontknow)
                           (t nil)))))
           ;; Checks to do on all sexps before the brace, up to the
           ;; beginning of the statement.
           (while (eq braceassignp 'dontknow)
             (cond ((eq (char-after) ?\;)
                    (setq braceassignp nil))
                   ((and class-key
                         (looking-at class-key))
                    (setq braceassignp nil))
                   ((eq (char-after) ?=)
                    ;; We've seen a =, but must check earlier tokens so
                    ;; that it isn't something that should be ignored.
                    (setq braceassignp 'maybe)
                    (while (and (eq braceassignp 'maybe)
                                (zerop (c-backward-token-2 1 t lim)))
                      (setq braceassignp
                            (cond
                             ;; Check for operator =
                             ((and c-opt-op-identifier-prefix
                                   (looking-at c-opt-op-identifier-prefix))
                              nil)
                             ;; Check for `<opchar>= in Pike.
                             ((and (c-major-mode-is 'pike-mode)
                                   (or (eq (char-after) ?`)
                                       ;; Special case for Pikes
                                       ;; `[]=, since '[' is not in
                                       ;; the punctuation class.
                                       (and (eq (char-after) ?\[)
                                            (eq (char-before) ?`))))
                              nil)
                             ((looking-at "\\s.") 'maybe)
                             ;; make sure we're not in a C++ template
                             ;; argument assignment
                             ((and
                               (c-major-mode-is 'c++-mode)
                               (save-excursion
                                 (let ((here (point))
                                       (pos< (progn
                                               (skip-chars-backward "^<>")
                                               (point))))
                                   (and (eq (char-before) ?<)
                                        (not (c-crosses-statement-barrier-p
                                              pos< here))
                                        (not (c-in-literal))
                                        ))))
                              nil)
                             (t t))))))
             (if (and (eq braceassignp 'dontknow)
                      (/= (c-backward-token-2 1 t lim) 0))
                 (setq braceassignp nil)))
           (if (not braceassignp)
               (if (eq (char-after) ?\;)
                   ;; Brace lists can't contain a semicolon, so we're done.
                   (setq containing-sexp nil)
                 ;; Go up one level.
                 (setq containing-sexp next-containing
                       lim nil
                       next-containing nil))
             ;; we've hit the beginning of the aggregate list
             (c-beginning-of-statement-1
              (c-most-enclosing-brace paren-state))
             (setq bufpos (point))))
         )
       bufpos))
   ))

;; ==================================================================
;; end of monkey-patching of basic parsing logic
;; ==================================================================




;;(easy-menu-define csharp-menu csharp-mode-map "C# Mode Commands"
;;                ;; Can use `csharp' as the language for `c-mode-menu'
;;                ;; since its definition covers any language.  In
;;                ;; this case the language is used to adapt to the
;;                ;; nonexistence of a cpp pass and thus removing some
;;                ;; irrelevant menu alternatives.
;;                (cons "C#" (c-lang-const c-mode-menu csharp)))

;;; Compilation regexps
;; When invoked by MSBuild, csc’s errors look like this:
;; subfolder\file.cs(6,18): error CS1006: Name of constructor must
;; match name of class [c:\Users\user\project.csproj]

(defun csharp--compilation-error-file-resolve ()
  ;; http://stackoverflow.com/a/18049590/429091
  (cons (match-string 1) (file-name-directory (match-string 4))))

(defconst csharp-compilation-re-msbuild-error
  (concat
   "^[[:blank:]]*"
   "\\([^(\r\n)]+\\)(\\([0-9]+\\)\\(?:,\\([0-9]+\\)\\)?): "
   "error [[:alnum:]]+: [^[\r\n]+\\[\\([^]\r\n]+\\)\\]$")
  "Regexp to match compilation error from msbuild.")

(defconst csharp-compilation-re-msbuild-warning
  (concat
   "^[[:blank:]]*"
   "\\([^(\r\n)]+\\)(\\([0-9]+\\)\\(?:,\\([0-9]+\\)\\)?): "
   "warning [[:alnum:]]+: [^[\r\n]+\\[\\([^]\r\n]+\\)\\]$")
  "Regexp to match compilation warning from msbuild.")

(defconst csharp-compilation-re-xbuild-error
  (concat
   "^[[:blank:]]*"
   "\\([^(\r\n)]+\\)(\\([0-9]+\\)\\(?:,\\([0-9]+\\)\\)?): "
   "error [[:alnum:]]+: .+$")
  "Regexp to match compilation error from xbuild.")

(defconst csharp-compilation-re-xbuild-warning
  (concat
   "^[[:blank:]]*"
   "\\([^(\r\n)]+\\)(\\([0-9]+\\)\\(?:,\\([0-9]+\\)\\)?): "
   "warning [[:alnum:]]+: .+$")
  "Regexp to match compilation warning from xbuild.")

(eval-after-load 'compile
  (lambda ()
    (dolist
        (regexp
         `((xbuild-error
            ,csharp-compilation-re-xbuild-error
            1 2 3 2)
           (xbuild-warning
            ,csharp-compilation-re-xbuild-warning
            1 2 3 1)
           (msbuild-error
            ,csharp-compilation-re-msbuild-error
            csharp--compilation-error-file-resolve
            2
            3
            2
            nil
            (1 compilation-error-face)
            (4 compilation-error-face))
           (msbuild-warning
            ,csharp-compilation-re-msbuild-warning
            csharp--compilation-error-file-resolve
            2
            3
            1
            nil
            (1 compilation-warning-face)
            (4 compilation-warning-face))))
      (add-to-list 'compilation-error-regexp-alist-alist regexp)
      (add-to-list 'compilation-error-regexp-alist (car regexp)))))

;;; Autoload mode trigger
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.cs$" . csharp-mode))


(c-add-style "C#"
             '("Java"
               (c-basic-offset . 4)
               (c-comment-only-line-offset . (0 . 0))
               (c-offsets-alist . (
                                   (access-label          . -)
                                   (arglist-close         . c-lineup-arglist)
                                   (arglist-cont          . 0)
                                   (arglist-cont-nonempty . c-lineup-arglist)
                                   (arglist-intro         . c-lineup-arglist-intro-after-paren)
                                   (block-close           . 0)
                                   (block-open            . 0)
                                   (brace-entry-open      . 0)
                                   (brace-list-close      . 0)
                                   (brace-list-entry      . 0)
                                   (brace-list-intro      . +)
                                   (brace-list-open       . +)
                                   (c                     . c-lineup-C-comments)
                                   (case-label            . +)
                                   (catch-clause          . 0)
                                   (class-close           . 0)
                                   (class-open            . 0)
                                   (comment-intro         . c-lineup-comment)
                                   (cpp-macro             . 0)
                                   (cpp-macro-cont        . c-lineup-dont-change)
                                   (defun-block-intro     . +)
                                   (defun-close           . 0)
                                   (defun-open            . 0)
                                   (do-while-closure      . 0)
                                   (else-clause           . 0)
                                   (extern-lang-close     . 0)
                                   (extern-lang-open      . 0)
                                   (friend                . 0)
                                   (func-decl-cont        . +)
                                   (inclass               . +)
                                   (inexpr-class          . +)
                                   (inexpr-statement      . 0)
                                   (inextern-lang         . +)
                                   (inher-cont            . c-lineup-multi-inher)
                                   (inher-intro           . +)
                                   (inlambda              . c-lineup-inexpr-block)
                                   (inline-close          . 0)
                                   (inline-open           . 0)
                                   (innamespace           . +)
                                   (knr-argdecl           . 0)
                                   (knr-argdecl-intro     . 5)
                                   (label                 . 0)
                                   (lambda-intro-cont     . +)
                                   (member-init-cont      . c-lineup-multi-inher)
                                   (member-init-intro     . +)
                                   (namespace-close       . 0)
                                   (namespace-open        . 0)
                                   (statement             . 0)
                                   (statement-block-intro . +)
                                   (statement-case-intro  . +)
                                   (statement-case-open   . +)
                                   (statement-cont        . +)
                                   (stream-op             . c-lineup-streamop)
                                   (string                . c-lineup-dont-change)
                                   (substatement          . +)
                                   (substatement-open     . 0)
                                   (template-args-cont c-lineup-template-args +)
                                   (topmost-intro         . 0)
                                   (topmost-intro-cont    . +)
                                   ))
               ))


;;; The entry point into the mode
;;;###autoload
  (defun csharp-mode ()
  "Major mode for editing C# code. This mode is derived from CC Mode to
support C#.

Normally, you'd want to autoload this mode by setting `auto-mode-alist' with
an entry for csharp, in your .emacs file:

   (autoload 'csharp-mode \"csharp-mode\" \"Major mode for editing C# code.\" t)
   (setq auto-mode-alist
      (append '((\"\\.cs$\" . csharp-mode)) auto-mode-alist))

The mode provides fontification and indent for C# syntax, as well
as some other handy features.

At mode startup, there are two interesting hooks that run:
`c-mode-common-hook' is run with no args, then `csharp-mode-hook' is run after
that, also with no args.

To run your own logic after csharp-mode starts, do this:

  (defun my-csharp-mode-fn ()
    \"my function that runs when csharp-mode is initialized for a buffer.\"
    (turn-on-font-lock)
    (turn-on-auto-revert-mode) ;; helpful when also using Visual Studio
    (setq indent-tabs-mode nil) ;; tabs are evil
    ....your own code here...
  )
  (add-hook  'csharp-mode-hook 'my-csharp-mode-fn t)


The function above is just a suggestion.


IMenu Integraiton
===============================

Check the menubar for menu entries for Imenu; It is labelled
\"Index\".

The Imenu index gets computed when the file is .cs first opened and loaded.
This may take a moment or two.  If you don't like this delay and don't
use imenu, you can turn this off with the variable `csharp-want-imenu'.



Key bindings:
\\{csharp-mode-map}"
    (interactive)
    (kill-all-local-variables)
    (make-local-variable 'beginning-of-defun-function)
    (make-local-variable 'end-of-defun-function)
    (c-initialize-cc-mode t)
    (set-syntax-table csharp-mode-syntax-table)

    ;; define underscore as part of a word in the Csharp syntax table
    (modify-syntax-entry ?_ "w" csharp-mode-syntax-table)

    ;; define @ as an expression prefix in Csharp syntax table
    (modify-syntax-entry ?@ "'" csharp-mode-syntax-table)

    (setq major-mode 'csharp-mode
          mode-name "C#"
          local-abbrev-table csharp-mode-abbrev-table
          abbrev-mode t)
    (use-local-map csharp-mode-map)

    ;; `c-init-language-vars' is a macro that is expanded at compile
    ;; time to a large `setq' with all the language variables and their
    ;; customized values for our language.
    (c-init-language-vars csharp-mode)

    ;; Set style to c# style unless a file local variable or default
    ;; style is found, in which case it should be set after
    ;; calling `c-common-init' below.
    (unless (or c-file-style
                (stringp c-default-style)
                (assq 'csharp-mode c-default-style))
      (c-set-style "c#" t))
    
    ;; `c-common-init' initializes most of the components of a CC Mode
    ;; buffer, including setup of the mode menu, font-lock, etc.
    ;; There's also a lower level routine `c-basic-common-init' that
    ;; only makes the necessary initialization to get the syntactic
    ;; analysis and similar things working.
    (c-common-init 'csharp-mode)

    (local-set-key (kbd "/") 'csharp-maybe-insert-codedoc)

    ;; Need the following for parse-partial-sexp to work properly with
    ;; verbatim literal strings Setting this var to non-nil tells
    ;; `parse-partial-sexp' to pay attention to the syntax text
    ;; properties on the text in the buffer.  If csharp-mode attaches
    ;; text syntax to @"..." then, `parse-partial-sexp' will treat those
    ;; strings accordingly.
    (set (make-local-variable 'parse-sexp-lookup-properties) t)

    ;; scan the entire buffer for verblit strings
    ;; This will happen on font; it's necessary only
    ;; if font-lock is disabled. But it won't hurt.
    (csharp-scan-for-verbatim-literals-and-set-props nil nil)

    ;; Allow fill-paragraph to work on xml code doc
    ;; This setting gets overwritten quietly by c-run-mode-hooks,
    ;; so I put it afterwards to make it stick.
    (make-local-variable 'paragraph-separate)

    ;;(message "C#: set paragraph-separate")

    ;; Speedbar handling
    (if (fboundp 'speedbar-add-supported-extension)
        (speedbar-add-supported-extension '(".cs"))) ;; idempotent

    (c-update-modeline)
    ;; run prog-mode-hooks if available
    (if (boundp 'prog-mode-hook)
	(c-run-mode-hooks 'prog-mode-hook 'c-mode-common-hook 'csharp-mode-hook)
      (c-run-mode-hooks 'c-mode-common-hook 'csharp-mode-hook))

    ;; maybe do imenu scan after hook returns
    (if csharp-want-imenu
      (progn
        ;; There are two ways to do imenu indexing. One is to provide a
        ;; function, via `imenu-create-index-function'.  The other is to
        ;; provide imenu with a list of regexps via
        ;; `imenu-generic-expression'; imenu will do a "generic scan" for you.
        ;; csharp-mode uses the former method.
        ;;
        (setq imenu-create-index-function 'csharp-imenu-create-index)
        (imenu-add-menubar-index)))

    ;; The paragraph-separate variable was getting stomped by
    ;; other hooks, so it must reside here.
    (setq paragraph-separate
          "[ \t]*\\(//+\\|\\**\\)\\([ \t]+\\|[ \t]+<.+?>\\)$\\|^\f")

    (setq beginning-of-defun-function 'csharp-move-back-to-beginning-of-defun)
    ;; end-of-defun-function   can remain forward-sexp !!

    (set (make-local-variable 'comment-auto-fill-only-comments) t)
    )

(provide 'csharp-mode)

;;; csharp-mode.el ends here
