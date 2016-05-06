;;; web-mode.el --- major mode for editing web templates
;;; -*- coding: utf-8 -*-

;; Copyright 2011-2016 François-Xavier Bois

;; Version: 14.0.0
;; Author: François-Xavier Bois <fxbois AT Google Mail Service>
;; Maintainer: François-Xavier Bois
;; URL: http://web-mode.org
;; Repository: http://github.com/fxbois/web-mode
;; Created: July 2011
;; Keywords: languages
;; License: GNU General Public License >= 2
;; Distribution: This file is not part of Emacs

;;==============================================================================
;;WEB-MODE is sponsored by ** Kernix ** Best Digital Factory & Data Lab in Paris
;;==============================================================================

;;; Code:

;;---- CONSTS ------------------------------------------------------------------

(defconst web-mode-version "14.0.0"
  "Web Mode version.")

;;---- GROUPS ------------------------------------------------------------------

(defgroup web-mode nil
  "Major mode for editing web templates"
  :group 'languages
  :prefix "web-"
  :link '(url-link :tag "Site" "http://web-mode.org")
  :link '(url-link :tag "Repository" "https://github.com/fxbois/web-mode"))

(defgroup web-mode-faces nil
  "Faces for syntax highlighting."
  :group 'web-mode
  :group 'faces)

;;---- CUSTOMS -----------------------------------------------------------------

(defcustom web-mode-script-padding 1
  "Script element left padding."
  :type 'integer
  :group 'web-mode)

(defcustom web-mode-style-padding 1
  "Style element left padding."
  :type 'integer
  :group 'web-mode)

(defcustom web-mode-block-padding 0
  "Multi-line block (php, ruby, java, python, asp, etc.) left padding."
  :type 'integer
  :group 'web-mode)

(defcustom web-mode-attr-indent-offset nil
  "Html attribute indentation level."
  :type 'integer
  :safe #'integerp
  :group 'web-mode)

(defcustom web-mode-attr-value-indent-offset nil
  "Html attribute value indentation level."
  :type 'integer
  :safe #'integerp
  :group 'web-mode)

(defcustom web-mode-markup-indent-offset
  (if (and (boundp 'standard-indent) standard-indent) standard-indent 2)
  "Html indentation level."
  :type 'integer
  :safe #'integerp
  :group 'web-mode)

(defcustom web-mode-css-indent-offset
  (if (and (boundp 'standard-indent) standard-indent) standard-indent 2)
  "CSS indentation level."
  :type 'integer
  :safe #'integerp
  :group 'web-mode)

(defcustom web-mode-code-indent-offset
  (if (and (boundp 'standard-indent) standard-indent) standard-indent 2)
  "Code (javascript, php, etc.) indentation level."
  :type 'integer
  :safe #'integerp
  :group 'web-mode)

(defcustom web-mode-sql-indent-offset 4
  "Sql (inside strings) indentation level."
  :type 'integer
  :safe #'integerp
  :group 'web-mode)

(defcustom web-mode-enable-css-colorization (display-graphic-p)
  "In a CSS part, set background according to the color: #xxx, rgb(x,x,x)."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-auto-indentation (display-graphic-p)
  "Auto-indentation."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-auto-closing (display-graphic-p)
  "Auto-closing."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-auto-pairing (display-graphic-p)
  "Auto-pairing."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-auto-opening (display-graphic-p)
  "Html element auto-opening."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-auto-quoting (display-graphic-p)
  "Add double quotes after the character = in a tag."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-auto-expanding nil
  "e.g. s/ expands to <span>|</span>."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-control-block-indentation t
  "Control blocks increase indentation."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-current-element-highlight nil
  "Disable element highlight."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-current-column-highlight nil
  "Show column for current element."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-whitespace-fontification nil
  "Enable whitespaces."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-html-entities-fontification nil
  "Enable html entities fontification."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-block-face nil
  "Enable block face (useful for setting a background for example).
See web-mode-block-face."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-part-face nil
  "Enable part face (useful for setting background of <style> or <script>
 elements for example). See web-mode-part-face."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-inlays nil
  "Enable inlays (e.g. LaTeX) highlighting."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-sexp-functions t
  "Enable specific sexp functions."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-comment-interpolation t
  "Enable highlight of keywords like FIXME, TODO, etc. in comments."
  :type 'list
  :group 'web-mode)

(defcustom web-mode-enable-string-interpolation t
  "Enable string interpolation fontification (php and erb)."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-sql-detection nil
  "Enable fontification and indentation of sql queries in strings."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-heredoc-fontification t
  "Enable heredoc fontification. The identifier should contain JS, JAVASCRIPT, CSS or HTML."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-element-content-fontification nil
  "Enable element content fontification. The content of an element can have a face associated."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-element-tag-fontification nil
  "Enable tag name fontification."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-enable-engine-detection nil
  "Detect such directive -*- engine: ENGINE -*- at the top of the file."
  :type 'boolean
  :group 'web-mode)

(defcustom web-mode-comment-style 1
  "Comment style : 1 = default, 2 = force server comments outside a block."
  :group 'web-mode
  :type '(choice (const :tag "default" 1)
                 (const :tag "force engine comments" 2)))

(defcustom web-mode-indent-style 2
  "Indentation style."
  :group 'web-mode
  :type '(choice (const :tag "default (all lines are indented)" 2)
                 (const :tag "text at the beginning of line is not indented" 1)))

(defcustom web-mode-auto-close-style 1
  "Auto-close style."
  :group 'web-mode
  :type '(choice (const :tag "Auto-close on </" 1)
                 (const :tag "Auto-close on > and </" 2)))

(defcustom web-mode-extra-expanders '()
  "A list of additional expanders."
  :type 'list
  :group 'web-mode)

(defcustom web-mode-extra-auto-pairs '()
  "A list of additional snippets."
  :type 'list
  :group 'web-mode)

(defcustom web-mode-extra-snippets '()
  "A list of additional snippets."
  :type 'list
  :group 'web-mode)

(defcustom web-mode-extra-builtins '()
  "A list of additional builtins."
  :type 'list
  :group 'web-mode)

(defcustom web-mode-extra-constants '()
  "A list of additional constants."
  :type 'list
  :group 'web-mode)

(defcustom web-mode-extra-keywords '()
  "A list of additional keywords."
  :type 'list
  :group 'web-mode)

(defcustom web-mode-extra-types '()
  "A list of additional types."
  :type 'list
  :group 'web-mode)

(defcustom web-mode-tests-directory (concat default-directory "tests/")
  "Directory containing all the unit tests."
  :type 'list
  :group 'web-mode)

(defcustom web-mode-jsx-depth-faces nil
;;  '(web-mode-jsx-depth-1-face
;;    web-mode-jsx-depth-2-face
;;    web-mode-jsx-depth-3-face
;;    web-mode-jsx-depth-4-face)
  "Each jsx depth has is own face."
  :type 'list
  :group 'web-mode)

;;---- FACES -------------------------------------------------------------------

(defface web-mode-error-face
  '((t :background "red"))
  "Face for warning."
  :group 'web-mode-faces)

(defface web-mode-warning-face
  '((t :inherit font-lock-warning-face))
  "Face for warning."
  :group 'web-mode-faces)

(defface web-mode-preprocessor-face
  '((t :inherit font-lock-preprocessor-face))
  "Face for preprocessor."
  :group 'web-mode-faces)

(defface web-mode-block-delimiter-face
  '((t :inherit font-lock-preprocessor-face))
  "Face for block delimiters."
  :group 'web-mode-faces)

(defface web-mode-block-control-face
  '((t :inherit font-lock-preprocessor-face))
  "Face for preprocessor."
  :group 'web-mode-faces)

(defface web-mode-builtin-face
  '((t :inherit font-lock-builtin-face))
  "Face for builtins."
  :group 'web-mode-faces)

(defface web-mode-symbol-face
  '((t :foreground "gold"))
  "Face for symbols."
  :group 'web-mode-faces)

(defface web-mode-doctype-face
  '((t :foreground "Grey"))
  "Face for html doctype."
  :group 'web-mode-faces)

(defface web-mode-html-tag-face
  '((((class color) (min-colors 88) (background dark))  :foreground "Snow4")
    (((class color) (min-colors 88) (background light)) :foreground "Snow4")
    (((class color) (min-colors 16) (background dark))  :foreground "Snow4")
    (((class color) (min-colors 16) (background light)) :foreground "Grey15")
    (((class color) (min-colors 8))                     :foreground "Snow4")
    (((type tty) (class mono))                          :inverse-video t)
    (t                                                  :foreground "Snow4"))
  "Face for html tags."
  :group 'web-mode-faces)

(defface web-mode-html-tag-custom-face
  '((t :inherit web-mode-html-tag-face))
  "Face for html custom tags (e.g. <polymer-element>)."
  :group 'web-mode-faces)

(defface web-mode-html-tag-namespaced-face
  '((t :inherit web-mode-block-control-face))
  "Face for html namespaced tags (e.g. <c:forEach>)."
  :group 'web-mode-faces)

(defface web-mode-html-tag-bracket-face
  '((((class color) (min-colors 88) (background dark))  :foreground "Snow3")
    (((class color) (min-colors 88) (background light)) :foreground "Grey14")
    (((class color) (min-colors 16) (background dark))  :foreground "Snow3")
    (((class color) (min-colors 16) (background light)) :foreground "Grey14")
    (((class color) (min-colors 8))                     :foreground "Snow3")
    (((type tty) (class mono))                          :inverse-video t)
    (t                                                  :foreground "Snow3"))
  "Face for html tags angle brackets (<, > and />)."
  :group 'web-mode-faces)

(defface web-mode-html-attr-name-face
  '((((class color) (min-colors 88) (background dark))  :foreground "Snow3")
    (((class color) (min-colors 88) (background light)) :foreground "Snow4")
    (((class color) (min-colors 16) (background dark))  :foreground "Snow3")
    (((class color) (min-colors 16) (background light)) :foreground "Grey13")
    (((class color) (min-colors 8))                     :foreground "Snow3")
    (((type tty) (class mono))                          :inverse-video t)
    (t                                                  :foreground "Snow4"))
  "Face for html attribute names."
  :group 'web-mode-faces)

(defface web-mode-html-attr-custom-face
  '((t :inherit web-mode-html-attr-name-face))
  "Face for custom attribute names (e.g. data-*)."
  :group 'web-mode-faces)

(defface web-mode-html-attr-engine-face
  '((t :inherit web-mode-block-delimiter-face))
  "Face for custom engine attribute names (e.g. ng-*)."
  :group 'web-mode-faces)

(defface web-mode-html-attr-equal-face
  '((t :inherit web-mode-html-attr-name-face))
  "Face for the = character between name and value."
  :group 'web-mode-faces)

(defface web-mode-html-attr-value-face
  '((t :inherit font-lock-string-face))
  "Face for html attribute values."
  :group 'web-mode-faces)

(defface web-mode-block-attr-name-face
  '((t :foreground "#8fbc8f"))
  "Face for block attribute names."
  :group 'web-mode-faces)

(defface web-mode-block-attr-value-face
  '((t :foreground "#5f9ea0"))
  "Face for block attribute values."
  :group 'web-mode-faces)

(defface web-mode-variable-name-face
  '((t :inherit font-lock-variable-name-face))
  "Face for variable names."
  :group 'web-mode-faces)

(defface web-mode-css-selector-face
  '((t :inherit font-lock-keyword-face))
  "Face for CSS rules."
  :group 'web-mode-faces)

(defface web-mode-css-pseudo-class-face
  '((t :inherit font-lock-builtin-face))
  "Face for CSS pseudo-classes."
  :group 'web-mode-faces)

(defface web-mode-css-at-rule-face
  '((t :inherit font-lock-constant-face))
  "Face for CSS at-rules."
  :group 'web-mode-faces)

(defface web-mode-css-property-name-face
  '((t :inherit font-lock-variable-name-face))
  "Face for CSS props."
  :group 'web-mode-faces)

(defface web-mode-css-color-face
  '((t :inherit font-lock-builtin-face))
  "Face for CSS colors (#xxx)."
  :group 'web-mode-faces)

(defface web-mode-css-priority-face
  '((t :inherit font-lock-builtin-face))
  "Face for CSS priority (!important)."
  :group 'web-mode-faces)

(defface web-mode-css-function-face
  '((t :inherit font-lock-builtin-face))
  "Face for CSS functions."
  :group 'web-mode-faces)

(defface web-mode-css-variable-face
  '((t :inherit web-mode-variable-name-face :slant italic))
  "Face for CSS vars."
  :group 'web-mode-faces)

(defface web-mode-function-name-face
  '((t :inherit font-lock-function-name-face))
  "Face for function names."
  :group 'web-mode-faces)

(defface web-mode-filter-face
  '((t :inherit font-lock-function-name-face))
  "Face for function names."
  :group 'web-mode-faces)

(defface web-mode-function-call-face
  '((t :inherit font-lock-function-name-face))
  "Face for function calls."
  :group 'web-mode-faces)

(defface web-mode-string-face
  '((t :inherit font-lock-string-face))
  "Face for strings."
  :group 'web-mode-faces)

(defface web-mode-block-string-face
  '((t :inherit web-mode-string-face))
  "Face for block strings."
  :group 'web-mode-faces)

(defface web-mode-part-string-face
  '((t :inherit web-mode-string-face))
  "Face for part strings."
  :group 'web-mode-faces)

(defface web-mode-javascript-string-face
  '((t :inherit web-mode-string-face))
  "Face for javascript strings."
  :group 'web-mode-faces)

(defface web-mode-css-string-face
  '((t :inherit web-mode-string-face))
  "Face for css strings."
  :group 'web-mode-faces)

(defface web-mode-json-key-face
  '((t :foreground "plum"))
  "Face for json key strings."
  :group 'web-mode-faces)

(defface web-mode-json-context-face
  '((t :foreground "orchid3"))
  "Face for json context strings."
  :group 'web-mode-faces)

(defface web-mode-json-string-face
  '((t :inherit web-mode-string-face))
  "Face for json strings."
  :group 'web-mode-faces)

(defface web-mode-comment-face
  '((t :inherit font-lock-comment-face))
  "Face for comments."
  :group 'web-mode-faces)

(defface web-mode-block-comment-face
  '((t :inherit web-mode-comment-face))
  "Face for server comments."
  :group 'web-mode-faces)

(defface web-mode-part-comment-face
  '((t :inherit web-mode-comment-face))
  "Face for part comments."
  :group 'web-mode-faces)

(defface web-mode-json-comment-face
  '((t :inherit web-mode-comment-face))
  "Face for json comments."
  :group 'web-mode-faces)

(defface web-mode-javascript-comment-face
  '((t :inherit web-mode-comment-face))
  "Face for javascript comments."
  :group 'web-mode-faces)

(defface web-mode-css-comment-face
  '((t :inherit web-mode-comment-face))
  "Face for css comments."
  :group 'web-mode-faces)

(defface web-mode-constant-face
  '((t :inherit font-lock-constant-face))
  "Face for language constants."
  :group 'web-mode-faces)

(defface web-mode-type-face
  '((t :inherit font-lock-type-face))
  "Face for language types."
  :group 'web-mode-faces)

(defface web-mode-keyword-face
  '((t :inherit font-lock-keyword-face))
  "Face for language keywords."
  :group 'web-mode-faces)

(defface web-mode-param-name-face
  '((t :foreground "Snow3"))
  "Face for server attribute names."
  :group 'web-mode-faces)

(defface web-mode-whitespace-face
  '((t :background "DarkOrchid4"))
  "Face for whitespaces."
  :group 'web-mode-faces)

(defface web-mode-inlay-face
  '((((class color) (min-colors 88) (background dark))  :background "Black")
    (((class color) (min-colors 88) (background light)) :background "LightYellow1")
    (((class color) (min-colors 16) (background dark))  :background "Brey18")
    (((class color) (min-colors 16) (background light)) :background "LightYellow1")
    (((class color) (min-colors 8))                     :background "Black")
    (((type tty) (class mono))                          :inverse-video t)
    (t                                                  :background "Grey"))
  "Face for inlays. Must be used in conjunction with web-mode-enable-inlays."
  :group 'web-mode-faces)

(defface web-mode-block-face
  '((((class color) (min-colors 88) (background dark))  :background "Black")
    (((class color) (min-colors 88) (background light)) :background "LightYellow1")
    (((class color) (min-colors 16) (background dark))  :background "Grey18")
    (((class color) (min-colors 16) (background light)) :background "LightYellow1")
    (((class color) (min-colors 8))                     :background "Black")
    (((type tty) (class mono))                          :inverse-video t)
    (t                                                  :background "Grey"))
  "Face for blocks (useful for setting a background for example).
Must be used in conjunction with web-mode-enable-block-face."
  :group 'web-mode-faces)

(defface web-mode-part-face
  '((t :inherit web-mode-block-face))
  "Face for parts."
  :group 'web-mode-faces)

(defface web-mode-script-face
  '((t :inherit web-mode-part-face))
  "Face for javascript inside a script element."
  :group 'web-mode-faces)

(defface web-mode-style-face
  '((t :inherit web-mode-part-face))
  "Face for css inside a style element."
  :group 'web-mode-faces)

(defface web-mode-folded-face
  '((t :underline t))
  "Overlay face for folded."
  :group 'web-mode-faces)

(defface web-mode-bold-face
  '((t :weight bold))
  "bold face."
  :group 'web-mode-faces)

(defface web-mode-italic-face
  '((t :slant italic))
  "bold face."
  :group 'web-mode-faces)

(defface web-mode-underline-face
  '((t :underline t))
  "bold face."
  :group 'web-mode-faces)

(defface web-mode-current-element-highlight-face
  '((t :background "#000000"))
  "Overlay face for element highlight."
  :group 'web-mode-faces)

(defface web-mode-current-column-highlight-face
  '((t :background "#3e3c36"))
  "Overlay face for current column."
  :group 'web-mode-faces)

(defface web-mode-comment-keyword-face
  '((t :weight bold :box t))
  "Comment keywords."
  :group 'web-mode-faces)

(defface web-mode-sql-keyword-face
  '((t :weight bold :slant italic))
  "Sql keywords."
  :group 'web-mode-faces)

(defface web-mode-html-entity-face
  '((t :slant italic))
  "Face html entities (e.g. &#8211;, &eacute;)."
  :group 'web-mode-faces)

(defface web-mode-jsx-depth-1-face
  '((t :background "#333333"))
  "jsx depth 1"
  :group 'web-mode-faces)

(defface web-mode-jsx-depth-2-face
  '((t :background "#222222"))
  "jsx"
  :group 'web-mode-faces)

(defface web-mode-jsx-depth-3-face
  '((t :background "#111111"))
  "jsx"
  :group 'web-mode-faces)

(defface web-mode-jsx-depth-4-face
  '((t :background "#000000"))
  "jsx"
  :group 'web-mode-faces)

;;---- VARS --------------------------------------------------------------------

(defvar font-lock-beg)
(defvar font-lock-end)

(defvar web-mode-auto-pairs nil)
(defvar web-mode-block-regexp nil)
(defvar web-mode-change-beg nil)
(defvar web-mode-change-end nil)
(defvar web-mode-chunk-length 64)
(defvar web-mode-column-overlays nil)
(defvar web-mode-comments-invisible nil)
(defvar web-mode-content-type "")
(defvar web-mode-engine nil)
(defvar web-mode-engine-attr-regexp nil)
(defvar web-mode-engine-font-lock-keywords nil)
(defvar web-mode-engine-token-regexp nil)
(defvar web-mode-expand-initial-pos nil)
(defvar web-mode-expand-initial-scroll nil)
(defvar web-mode-expand-previous-state "")
(defvar web-mode-font-lock-keywords '(web-mode-font-lock-highlight))
(defvar web-mode-inhibit-fontification nil)
(defvar web-mode-inlay-regexp nil)
(defvar web-mode-is-scratch nil)
(defvar web-mode-jshint-errors 0)
(defvar web-mode-minor-engine nil)
(defvar web-mode-obarray nil)
(defvar web-mode-overlay-tag-start nil)
(defvar web-mode-overlay-tag-end nil)
(defvar web-mode-snippets nil)
(defvar web-mode-time (current-time))

(defvar web-mode-indentless-elements
  '("code" "pre" "textarea"))

(defvar web-mode-indentless-attributes
  '("onclick" "onmouseover" "onmouseout" "onsubmit"))

(defvar web-mode-void-elements
  '("area" "base" "br" "col" "command" "embed" "hr" "img" "input" "keygen"
    "link" "meta" "param" "source" "track" "wbr"))

(defvar web-mode-part-content-types '("css" "javascript" "json" "jsx"))

(defvar web-mode-javascript-languages '("javascript" "jsx" "ejs"))

;; NOTE: without 'syntax-table forward-word fails (#377)
(defvar web-mode-scan-properties
  (list 'tag-beg 'tag-end 'tag-name 'tag-type
        'tag-attr 'tag-attr-beg 'tag-attr-end
        'part-side 'part-token
        'jsx-beg 'jsx-end 'jsx-depth
        'block-side 'block-token 'block-controls 'block-beg 'block-end
        'syntax-table)
  "Text properties used for code regions/tokens and html nodes.")

(defvar web-mode-start-tag-regexp "<\\([[:alpha:]][[:alnum:]:-]*\\)"
  "Regular expression for HTML/XML start tag.")

(defvar web-mode-whitespaces-regexp
  "^[ \t]\\{2,\\}$\\| \t\\|\t \\|[ \t]+$\\|^[ \n\t]+\\'\\|^[ \t]?[\n]\\{2,\\}"
  "Regular expression for whitespaces.")

(defvar web-mode-imenu-regexp-list
  '(("<\\(h[1-9]\\)\\([^>]*\\)>\\([^<]*\\)" 1 3 ">")
    ("^[ \t]*<\\([@a-z]+\\)[^>]*>? *$" 1 "id=\"\\([a-zA-Z0-9_]+\\)\"" "#" ">"))
  "Regexps to match imenu items (see http://web-mode.org/doc/imenu.txt)")

(defvar web-mode-indentation-params
  '(("lineup-args"       . t)
    ("lineup-calls"      . t)
    ("lineup-concats"    . t)
    ("lineup-quotes"     . t)
    ("lineup-ternary"    . t)
    ("case-extra-offset" . t)
    ))

(defvar web-mode-engines
  '(("angular"          . ("angularjs" "angular.js"))
    ("asp"              . ())
    ("aspx"             . ())
    ("blade"            . ("laravel"))
    ("cl-emb"           . ())
    ("clip"             . ())
    ("closure"          . ("soy"))
    ("ctemplate"        . ("mustache" "handlebars" "hapax" "ngtemplate" "ember"
                           "kite" "meteor" "blaze" "ractive"))
    ("django"           . ("dtl" "twig" "swig" "jinja" "erlydtl" "liquid"
                           "clabango" "selmer" "nunjucks"))
    ("dust"             . ("dustjs"))
    ("ejs"              . ())
    ("elixir"           . ("phoenix"))
    ("erb"              . ("eruby" "erubis"))
    ("freemarker"       . ())
    ("go"               . ("gtl"))
    ("jsp"              . ("grails"))
    ("mako"             . ())
    ("marko"            . ())
    ("mason"            . ("poet"))
    ("lsp"              . ("lisp"))
    ("mojolicious"      . ())
    ("php"              . ())
    ("python"           . ())
    ("razor"            . ("play" "play2"))
    ("riot"             . ())
    ("template-toolkit" . ())
    ("smarty"           . ())
    ("thymeleaf"        . ())
    ("underscore"       . ("underscore.js"))
    ("velocity"         . ("vtl" "cheetah" "ssp"))
    ("web2py"           . ()))
  "Engine name aliases")

(defvar web-mode-content-types
  '(("css"        . "\\.\\(s?css\\|css\\.erb\\)\\'")
    ("javascript" . "\\.\\([jt]s\\|[jt]s\\.erb\\)\\'")
    ("json"       . "\\.\\(api\\|json\\|jsonld\\)\\'")
    ("jsx"        . "\\.[jt]sx\\'")
    ("xml"        . "\\.xml\\'")
    ("html"       . "."))
  "content types")

(defvar web-mode-engine-attr-regexps
  '(("angular"   . "ng-")
    ("thymeleaf" . "th:"))
  "Engine custom attributes")

(defvar web-mode-last-enabled-feature nil)

(defvar web-mode-features
  '(("css-colorization"          . web-mode-enable-css-colorization)
    ("element-highlight"         . web-mode-enable-current-element-highlight)
    ("column-highlight"          . web-mode-enable-current-column-highlight)
    ("whitespace-fontification"  . web-mode-enable-whitespace-fontification)
    ("element-tag-fontification" . web-mode-enable-element-tag-fontification)
    ("block-face"                . web-mode-enable-block-face)
    ("part-face"                 . web-mode-enable-part-face)))

(defvar web-mode-comment-prefixing t)

(defvar web-mode-comment-formats
  '(("java"       . "/*")
    ("javascript" . "/*")
    ("php"        . "/*")
    ))

(defvar web-mode-engine-file-regexps
  '(("asp"              . "\\.asp\\'")
    ("aspx"             . "\\.as[cp]x\\'")
    ("blade"            . "\\.blade\\.php\\'")
    ("cl-emb"           . "\\.clemb\\'")
    ("clip"             . "\\.ctml\\'")
    ("closure"          . "\\.soy\\'")
    ("ctemplate"        . "\\.\\(chtml\\|mustache\\)\\'")
    ("django"           . "\\.\\(djhtml\\|tmpl\\|dtl\\|liquid\\|j2\\)\\'")
    ("dust"             . "\\.dust\\'")
    ("elixir"           . "\\.eex\\'")
    ("ejs"              . "\\.ejs\\'")
    ("erb"              . "\\.\\(erb\\|rhtml\\|erb\\.html\\)\\'")
    ("freemarker"       . "\\.ftl\\'")
    ("go"               . "\\.go\\(html\\|tmpl\\)\\'")
    ("handlebars"       . "\\.\\(hb\\.html\\|hbs\\)\\'")
    ("jinja"            . "\\.jinja\\'")
    ("jsp"              . "\\.[gj]sp\\'")
    ("lsp"              . "\\.lsp\\'")
    ("mako"             . "\\.mako?\\'")
    ("marko"            . "\\.marko\\'")
    ("mason"            . "\\.mas\\'")
    ("mojolicious"      . "\\.epl?\\'")
    ("php"              . "\\.\\(p[hs]p\\|ctp\\|inc\\)\\'")
    ("python"           . "\\.pml\\'")
    ("razor"            . "\\.\\(cs\\|vb\\)html\\'")
    ("riot"           .  "\\.tag\\'")
    ("smarty"           . "\\.tpl\\'")
    ("template-toolkit" . "\\.tt.?\\'")
    ("thymeleaf"        . "\\.thtml\\'")
    ("velocity"         . "\\.v\\(sl\\|tl\\|m\\)\\'")

    ("django"           . "[st]wig")
    ("razor"            . "scala")

    )
  "Engine file extensions.")

(defvar web-mode-smart-quotes
  '("«" . "»")
  "Preferred smart quotes")

(defvar web-mode-xml-chars
  '((?\& . "&amp;")
    (?\< . "&lt;")
    (?\> . "&gt;"))
  "XML chars")

(defvar web-mode-html-entities
  '(("AElig" . 198) ("Aacute" . 193) ("Acirc" . 194) ("Agrave" . 192)
    ("Alpha" . 913) ("Aring" . 197) ("Atilde" . 195) ("Auml" . 196)
    ("Beta" . 914)
    ("Ccedil" . 199) ("Chi" . 935)
    ("Dagger" . 8225) ("Delta" . 916)
    ("ETH" . 208) ("Eacute" . 201) ("Ecirc" . 202) ("Egrave" . 200)
    ("Epsilon" . 917) ("Eta" . 919) ("Euml" . 203)
    ("Gamma" . 915)
    ("Iacute" . 205) ("Icirc" . 206) ("Igrave" . 204) ("Iota" . 921)
    ("Iuml" . 207)
    ("Kappa" . 922)
    ("Lambda" . 923)
    ("Mu" . 924)
    ("Ntilde" . 209) ("Nu" . 925)
    ("OElig" . 338) ("Oacute" . 211) ("Ocirc" . 212) ("Ograve" . 210)
    ("Omega" . 937) ("Omicron" . 927) ("Oslash" . 216) ("Otilde" . 213)
    ("Ouml" . 214)
    ("Phi" . 934) ("Pi" . 928) ("Prime" . 8243) ("Psi" . 936)
    ("Rho" . 929)
    ("Scaron" . 352) ("Sigma" . 931)
    ("THORN" . 222) ("Tau" . 932) ("Theta" . 920)
    ("UArr" . 8657) ("Uacute" . 218) ("Uacute" . 250) ("Ucirc" . 219)
    ("Ugrave" . 217)  ("Upsih" . 978)
    ("Upsilon" . 933) ("Uuml" . 220) ("Uuml" . 252)
    ("Xi" . 926)
    ("Yacute" . 221) ("Yuml" . 376)
    ("Zeta" . 918)
    ("aacute" . 225) ("acirc" . 226) ("acute" . 180) ("aelig" . 230)
    ("agrave" . 224) ("alefsym" . 8501) ("alpha" . 945) ("amp" . 38)
    ("ang" . 8736) ("apos" . 39) ("aring" . 229) ("asymp" . 8776)
    ("atilde" . 227) ("auml" . 228)
    ("bdquo" . 8222) ("beta" . 946) ("brvbar" . 166) ("bull" . 8226)
    ("cap" . 8745) ("ccedil" . 231) ("cedil" . 184) ("cent" . 162)
    ("chi" . 967) ("circ" . 710) ("clubs" . 9827) ("cong" . 8773)
    ("copy" . 169) ("crarr"  . 8629) ("cup" . 8746) ("curren" . 164)
    ("dArr" . 8659) ("dagger" . 8224) ("darr" . 8595) ("deg" . 176)
    ("delta" . 948) ("diams" . 9830) ("divide" . 247)
    ("eacute" . 233) ("ecirc"  . 234) ("egrave" . 232) ("empty" . 8709)
    ("emsp" . 8195) ("ensp" . 8194) ("epsilon" . 949) ("equiv" . 8801)
    ("eta" . 951) ("eth" . 240) ("euml" . 235) ("euro" . 8364) ("exist" . 8707)
    ("fnof" . 402) ("forall" . 8704) ("frac12" . 189) ("frac14" . 188)
    ("frac34" . 190) ("frasl" . 8260)
    ("gamma" . 947) ("ge" . 8805) ("gt" . 62)
    ("hArr" . 8660) ("harr" . 8596) ("hearts" . 9829) ("hellip" . 8230)
    ("iacute" . 237) ("icirc" . 238) ("iexcl" . 161) ("igrave" . 236)
    ("image" . 8465) ("infin" . 8734) ("int" . 8747) ("iota" . 953)
    ("iquest" . 191) ("isin" . 8712) ("iuml" . 239)
    ("kappa" . 954)
    ("lArr" . 8656) ("lambda" . 955) ("lang" . 9001) ("laquo" . 171)
    ("larr" . 8592) ("lceil" . 8968) ("ldquo" . 8220) ("le" . 8804)
    ("lfloor" . 8970) ("lowast" . 8727) ("loz" . 9674) ("lrm" . 8206)
    ("lsaquo" . 8249) ("lsquo" . 8249) ("lt" . 60)
    ("macr" . 175) ("mdash" . 8212) ("micro" . 181) ("middot" . 183)
    ("minus" . 8722) ("mu" . 956)
    ("nabla" . 8711) ("nbsp" . 160) ("ndash" . 8211) ("ne" . 8800)
    ("ni" . 8715) ("not" . 172) ("notin" . 8713) ("nsub" . 8836)
    ("ntilde" . 241) ("nu" . 957) ("oacute" . 243) ("ocirc" . 244)
    ("oelig" . 339) ("ograve" . 242) ("oline" . 8254) ("omega" . 969)
    ("omicron" . 959) ("oplus" . 8853) ("or" . 8744) ("ordf" . 170)
    ("ordm" . 186) ("oslash" . 248) ("otilde" . 245) ("otimes" . 8855)
    ("ouml" . 246)
    ("para" . 182) ("part" . 8706) ("permil" . 8240) ("perp" . 8869)
    ("phi" . 966) ("pi" . 960) ("piv" . 982) ("plusmn" . 177) ("pound" . 163)
    ("prime" . 8242) ("prod" . 8719) ("prop" . 8733) ("psi" . 968)
    ("quot" . 34)
    ("rArr" . 8658) ("radic" . 8730) ("rang" . 9002) ("raquo" . 187)
    ("rarr" . 8594) ("rceil" . 8969) ("rdquo" . 8221) ("real" . 8476)
    ("reg" . 174) ("rfloor" . 8971) ("rho" . 961) ("rlm" . 8207)
    ("rsaquo" . 8250) ("rsquo" . 8250) ("sbquo" . 8218)
    ("scaron" . 353) ("sdot" . 8901) ("sect" . 167) ("shy" . 173)
    ("sigma" . 963) ("sigmaf" . 962) ("sim" . 8764) ("spades" . 9824)
    ("sub" . 8834) ("sube" . 8838) ("sum" . 8721) ("sup" . 8835)
    ("sup1" . 185) ("sup2" . 178) ("sup3" . 179) ("supe" . 8839)
    ("szlig" . 223)
    ("tau" . 964) ("there4" . 8756) ("theta" . 952) ("thetasym" . 977)
    ("thinsp" . 8201) ("thorn" . 254) ("tilde" . 732) ("times" . 215)
    ("trade" . 8482)
    ("uarr" . 8593) ("ucirc" . 251) ("ugrave" . 249) ("uml" . 168)
    ("upsilon" . 965)
    ("weierp" . 8472)
    ("xi" . 958)
    ("yacute" . 253) ("yen" . 165) ("yuml" . 255)
    ("zeta" . 950) ("zwj" . 8205) ("zwnj" . 8204)))

;; http://webdesign.about.com/od/localization/l/blhtmlcodes-ascii.htm
(defvar web-mode-display-table
  (let ((table (make-display-table)))
    (aset table 9  (vector ?\xBB ?\t))
    (aset table 10 (vector ?\xB6 ?\n))
    (aset table 32 (vector ?\xB7))
    table)
  "Display table used when switching to the whitespace visualization.")

(defvar web-mode-expanders
  '(("a/" . "<a href=\"|\"></a>")
    ("b/" . "<table><tbody><tr><td>|</td><td></td></tr></tbody></table>")
    ("c/" . "<div class=\"|\"></div>")
    ("d/" . "<div>|</div>")
    ("e/" . "<em>|</em>")
    ("f/" . "<form>|</form>")
    ("g/" . "<strong>|</strong>")
    ("h/" . "<h1>|</h1>")
    ("i/" . "<img src=\"|\" />")
    ("j/" . "<script>|</script>")
    ("l/" . "<li>|</li>")
    ("m/" . "<main>|</main>")
    ("n/" . "<input type=\"|\" />")
    ("p/" . "<p>|</p>")
    ("q/" . "<quote>|</quote>")
    ("s/" . "<span>|</span>")
    ("t/" . "<td>|</td>")
    ("u/" . "<ul><li>|</li><li></li></ul>")
    ("x/" . "<textarea>|</textarea>")
    ("2/" . "<h2>|</h2>")
    ("3/" . "<h3>|</h3>")
    ("?/" . "<?php | ?>")))

(defvar web-mode-engines-auto-pairs
  '(("angular"          . (("{{ " . " }}")))
    ("asp"              . (("<% " . " %>")))
    ("aspx"             . (("<% " . " %>")
                           ("<%=" . "%>")
                           ("<%#" . "%>")
                           ("<%$" . "%>")
                           ("<%@" . "%>")
                           ("<%:" . "%>")
                           ("<%-" . "- | --%>")))
    ("blade"            . (("{{{" . " | }}}")
                           ("{{ " . " }}")
                           ("{!!" . " | !!}")
                           ("@{{" . " | }}")
                           ("{{-" . "- | --}}")))
    ("cl-emb"           . (("<% " . " %>")
                           ("<%=" . " | %>")
                           ("<%#" . " | %>")))
    ("ctemplate"        . (("{{ " . "| }}")
                           ("{{{" . " | }}}")
                           ("{~{" . " | }}")
                           ("{{~" . "{ | }}}")
                           ("{{!" . "-- | --}}")
                           ("{{/" . "}}")
                           ("{{#" . "}}")))
    ("django"           . (("{{ " . " }}")
                           ("{% " . " %}")
                           ("{%-" . " | %}")
                           ("{# " . " #}")))
    ("elixir"           . (("<% " . " %>")
                           ("<%=" . " | %>")
                           ("<%%" . " | %>")
                           ("<%#" . " | %>")))
    ("ejs"              . (("<% " . " %>")
                           ("<%=" . "%>")
                           ("<%#" . "%>")
                           ("<%-" . "%>")))
    ("erb"              . (("<% " . " %>")
                           ("<%=" . "%>")
                           ("<%#" . "%>")
                           ("<%-" . "%>")))
    ("freemarker"       . (("<% " . " %>")
                           ("<#-" . "- | -->")
                           ("${ " . " }")
                           ("[% " . " %]")
                           ("[# " . " #]")
                           ("[#-" . "- | --]")))
    ("jsp"              . (("<% " . " %>")
                           ("<%-" . "- | --%>")
                           ("<%=" . "%>")
                           ("<%!" . "%>")
                           ("<%@" . "%>")
                           ("${ " . " }")))
    ("lsp"              . (("<% " . " %>")
                           ("<%%" . " | %>")
                           ("<%#" . " | %>")))
    ("mako"             . (("<% " . " %>")
                           ("<%!" . " | %>")
                           ("${ " . " }")))
    ("marko"            . (("${ " . " }")))
    ("mason"            . (("<% " . " %>")
                           ("<& " . " &>")))
    ("mojolicious"      . (("<% " . " %>")
                           ("<%=" . " | %>")
                           ("<%%" . " | %>")
                           ("<%#" . " | %>")))
    ("php"              . (("<?p" . "hp | ?>")
                           ("<? " . " ?>")
                           ("<?=" . "?>")))
    ("template-toolkit" . (("[% " . " %]")
                           ("[%-" . " | %]")
                           ("[%#" . " | %]")))
    ("riot"             . (("={ " . " }")))
    ("underscore"       . (("<% " . " %>")))
    ("web2py"           . (("{{ " . " }}")
                           ("{{=" . "}}")))
    (nil                . (("<!-" . "- | -->")))
    ))

(defvar web-mode-engines-snippets
  '(("ejs" . (("for"     . "<% for (|) { %>\n\n<% } %>")
              ("if"      . "<% if (|) { %>\n\n<% } %>")))
    ("erb" . (("each"    . "<% |.each do  %>\n\n<% end %>")
              ("if"      . "<% if | %>\n\n<% end %>")
              ("when"    . "<% when | %>\n\n<% end %>")
              ("unless"  . "<% unless | %>\n\n<% end %>")))
    ("php" . (("if"      . "<?php if (|): ?>\n\n<?php endif; ?>")
              ("while"   . "<?php while (|): ?>\n\n<?php endwhile; ?>")
              ("for"     . "<?php for (| ; ; ): ?>\n\n<?php endfor; ?>")
              ("foreach" . "<?php foreach (| as ): ?>\n\n<?php endforeach; ?>")
              ("each"    . "<?php foreach (| as ): ?>\n\n<?php endforeach; ?>")
              ("switch"  . "<?php switch (|): ?>\n<?php case 1: ?>\n\n<?php break ;?>\n<?php case 2: ?>\n\n<?php break ;?>\n<?php endswitch;?>")))
    ("django" . (("block"      . "{% block | %}\n\n{% endblock %}")
                 ("comment"    . "{% comment | %}\n\n{% endcomment %}")
                 ("cycle"      . "{% cycle | as  %}\n\n{% endcycle  %}")
                 ("filter"     . "{% filter | %}\n\n{% endfilter %}")
                 ("for"        . "{% for | in  %}\n\n{% endfor %}")
                 ("if"         . "{% if | %}\n\n{% endif %}")
                 ("ifequal"    . "{% ifequal | %}\n\n{% endifequal %}")
                 ("ifnotequal" . "{% ifnotequal | %}\n\n{% endifnotequal %}")
                 ("safe"       . "{% safe | %}\n\n{% endsafe %}")))
    ("template-toolkit" . (("if"      . "[% IF | %]\n\n[% END %]")))
    (nil . (("html5" . "<!doctype html>\n<html>\n<head>\n<title></title>\n<meta charset=\"utf-8\" />\n</head>\n<body>\n|\n</body>\n</html>")
            ("table" . "<table><tbody>\n<tr>\n<td>|</td>\n<td></td>\n</tr>\n</tbody></table>")
            ("ul"    . "<ul>\n<li>|</li>\n<li></li>\n</ul>")))
    ))

(defvar web-mode-engine-token-regexps
  (list
   '("asp"         . "//\\|/\\*\\|\"\\|'")
   '("ejs"         . "//\\|/\\*\\|\"\\|'")
   '("erb"         . "\"\\|'\\|#\\|<<[-]?['\"]?\\([[:alnum:]_]+\\)['\"]?")
   '("lsp"         . "\"\\|#|\\|;")
   '("mako"        . "\"\\|'\\|#")
   '("mason"       . "\"\\|'\\|#")
   '("mojolicious" . "\"\\|'")
   '("php"         . "//\\|/\\*\\|#\\|\"\\|'\\|<<<['\"]?\\([[:alnum:]]+\\)['\"]?")
   '("python"      . "\"\\|'\\|#")
   '("web2py"      . "\"\\|'"))
  "Engine regexps used to identify tokens (strings / comments) in blocks.")

(defvar web-mode-engine-open-delimiter-regexps
  (list
   '("angular"          . "{{")
   '("asp"              . "<%\\|</?[[:alpha:]]+:[[:alpha:]]+\\|</?[[:alpha:]]+Template")
   '("aspx"             . "<%.")
   '("blade"            . "{{.\\|{!!\\|@{{\\|@[[:alpha:]]")
   '("cl-emb"           . "<%")
   '("closure"          . "{.\\|/\\*\\| //")
   '("clip"             . "</?c:[[:alpha:]-]+")
   '("ctemplate"        . "[$]?{[{~].")
   '("django"           . "{[#{%]")
   '("dust"             . "{.")
   '("elixir"           . "<%.")
   '("ejs"              . "<%")
   '("erb"              . "<%\\|^%.")
   '("freemarker"       . "<%\\|${\\|</?[[:alpha:]]+:[[:alpha:]]\\|</?[@#]\\|\\[/?[@#].")
   '("go"               . "{{.")
   '("jsp"              . "<%\\|${")
   '("lsp"              . "<%")
   '("mako"             . "</?%\\|${\\|^[ \t]*%.\\|^[ \t]*##")
   '("marko"            . "${")
   '("mason"            . "</?[&%]\\|^%.")
   '("mojolicious"      . "<%\\|^[ \t]*%.")
   '("php"              . "<\\?")
   '("python"           . "<\\?")
   '("razor"            . "@.\\|^[ \t]*}")
   '("riot"             . "{.")
   '("smarty"           . "{[[:alpha:]#$/*\"]")
   '("template-toolkit" . "\\[%.\\|%%#")
   '("underscore"       . "<%")
   '("velocity"         . "#[[:alpha:]#*]\\|$[[:alpha:]!{]")
   '("web2py"           . "{{"))
  "Engine regexps used to identify blocks.")

(defvar web-mode-normalization-rules
  '(("tag-case"          . "lower-case")
    ("attr-case"         . "lower-case")
    ("special-chars"     . "unicode") ;"unicode" "entities"
    ("css-indentation"   . t)
    ("smart-apostrophes" . t)
    ("smart-quotes"      . t)
    ("whitespaces"       . t)
    ("indentation"       . t))
  "Normalization rules")

(defvar web-mode-element-tag-faces
  (list
   '("h1"     . web-mode-underline-face)
   '("h2"     . web-mode-underline-face)
   '("h3"     . web-mode-underline-face)
   '("h4"     . web-mode-underline-face)
   '("title"  . web-mode-underline-face)
   '("em"     . web-mode-italic-face)
   '("strong" . web-mode-bold-face)
   ))

(defvar web-mode-element-content-faces
  (list
   '("h1"     . web-mode-underline-face)
   '("h2"     . web-mode-underline-face)
   '("h3"     . web-mode-underline-face)
   '("h4"     . web-mode-underline-face)
   '("title"  . web-mode-underline-face)
   '("em"     . web-mode-italic-face)
   '("strong" . web-mode-bold-face)
   ))

(defvar web-mode-comment-keywords
  (regexp-opt
   (append
    (cdr (assoc "comment" web-mode-extra-keywords))
    '("FIXME" "TODO" "BUG" "KLUDGE" "WORKAROUND" "OPTIMIZE" "HACK" "REFACTOR" "REVIEW"))))

(defvar web-mode-file-extensions
  (list
   '("\.png$" 0 nil)
   '("\.jpe?g$" 0 nil)
   '("\.gif$" 0 nil)
   '("\.svg$" 1 nil)
   '("\.js$" 2 t)
   '("\.css$" 3 t))
  "List of regexps matching filetypes in `web-mode-file-link'. Second value of each list should be the index of list containing matching tags in `web-mode-file-elements', and the third one should be t if the link is supposed to be in head or nil.")

(defvar web-mode-links
  '(("<img src=\"|\" />" . "\\.\\(png\\|jpe?g\\|gif\\)$")
    ("<object data=\"|\" type=\"image/svg+xml\"></object>" . "\\.svg$")
    ("<script type=\"text/javascript\" src=\"|\"></script>" . "\\.js$")
    ("<link rel=\"stylesheet\" type=\"text/css\" href=\"|\" />" . "\\.css$"))
  "List of tags to be used by `web-mode-file-link'.")

(defvar web-mode-file-elements
  (list
   '("<img src=\"" "\" />")
   '("<object data=\"" "\" type=\"image/svg+xml\"></object>")
   '("<script type=\"text/javascript\" src=\"" "\"></script>")
   '("<link rel=\"stylesheet\" type=\"text/css\" href=\"" "\" />"))
  "List of tags to be used by `web-mode-file-link'.")

(defvar web-mode-sql-queries
  (regexp-opt
   '("SELECT" "INSERT" "UPDATE" "DELETE" "select" "insert" "update" "delete")))

(defvar web-mode-sql-keywords
  (regexp-opt
   (append
    (cdr (assoc "sql" web-mode-extra-keywords))
    '("SELECT" "INSERT" "UPDATE" "DELETE"
      "FROM" "WHERE" "GROUP BY" "LIMIT" "HAVING" "JOIN" "LEFT" "INNER"
      "FULL" "OUTER" "VALUES" "ORDER BY" "SEPARATOR" "ASC" "DESC"
      "AND" "OR" "ON"))))

(defvar web-mode-python-constants
  (regexp-opt
   (append
    (cdr (assoc "python" web-mode-extra-constants))
    '("True" "False" "None" "__debug__" "NotImplemented" "Ellipsis"))))

(defvar web-mode-erlang-constants
  (regexp-opt
   (append
    (cdr (assoc "erlang" web-mode-extra-constants))
    '("true" "false"))))

(defvar web-mode-erlang-keywords
  (regexp-opt
   (append
    (cdr (assoc "erlang" web-mode-extra-keywords))
    '("else" "if" "do" "end"))))

(defvar web-mode-cl-emb-constants
  (regexp-opt
   '("nil" "t" "raw" "escape")))

(defvar web-mode-cl-emb-keywords
  (regexp-opt
   '("if" "else" "endif" "unless" "endunless" "var" "repeat"
     "endrepeat" "loop" "endloop" "include" "call" "with"
     "endwith" "set" "genloop" "endgenloop" "insert")))

(defvar web-mode-lsp-constants
  (regexp-opt
   '("nil" "t")))

(defvar web-mode-lsp-keywords
  (regexp-opt
   '("dolist" "let" "while" "cond" "when" "progn" "if"
     "dotimes" "unless" "lambda"
     "loop" "for" "and" "or" "in" "do" "defun")))

(defvar web-mode-php-constants
  (regexp-opt
   (append
    (cdr (assoc "php" web-mode-extra-constants))
    '("TRUE" "FALSE" "NULL" "true" "false" "null"
      "STR_PAD_LEFT" "STR_PAD_RIGHT"
      "ENT_COMPAT" "ENT_QUOTES" "ENT_NOQUOTES" "ENT_IGNORE"
      "ENT_SUBSTITUTE" "ENT_DISALLOWED" "ENT_HTML401" "ENT_XML1"
      "ENT_XHTML" "ENT_HTML5" "JSON_PRETTY_PRINT"
      "LIBXML_NOBLANKS"))))

(defvar web-mode-php-keywords
  (regexp-opt
   (append
    (cdr (assoc "php" web-mode-extra-keywords))
    '("and" "array" "as" "break"
      "callable" "case" "catch"  "catch all" "class" "const" "continue"
      "default" "die" "do" "echo" "else" "elseif" "empty"
      "endfor" "endforeach" "endif" "endswitch" "endwhile" "exit" "extends"
      "finally" "for" "foreach" "function" "global" "goto"
      "if" "include" "include_once" "instanceof" "interface" "isset"
      "list" "next" "new" "or" "private" "protected" "public"
      "require" "require_once" "return" "static" "switch" "try" "throw"
      "unset" "use" "var" "when" "while" "xor" "yield"))))

(defvar web-mode-php-types
  (eval-when-compile
    (regexp-opt
     '("array" "bool" "boolean" "char" "const" "double" "float"
       "int" "integer" "long" "mixed" "object" "real" "string"))))

(defvar web-mode-css-at-rules
  (eval-when-compile
    (regexp-opt
     '("charset" "import" "media" "page" "font-face"
       "namespace" "supports" "document"
       "keyframes" "-moz-keyframes" "-webkit-keyframes"
       "mixin"))))

(defvar web-mode-css-pseudo-classes
  (eval-when-compile
    (regexp-opt
     '("active" "after" "before" "checked" "disabled" "empty" "enabled"
       "first" "first-child" "first-letter" "first-line" "first-of-type" "focus"
       "hover" "lang" "last-child" "last-of-type" "left" "link"
       "not" "nth-child" "nth-last-child" "nth-last-of-type" "nth-of-type"
       "only-child" "only-of-type"
       "right" "root" "selection" "target" "visited"))))

(defvar web-mode-python-keywords
  (regexp-opt
   (append
    (cdr (assoc "python" web-mode-extra-keywords))
    '("and" "as" "assert" "break" "class" "continue" "def" "del"
      "elif" "else" "except" "finally" "for" "from" "global"
      "if" "import" "in" "is" "lambda" "nonlocal" "not" "or" "pass"
      "raise" "return" "try" "while" "with" "yield"))))

(defvar web-mode-jsp-keywords
  (regexp-opt
   (append
    (cdr (assoc "jsp" web-mode-extra-keywords))
    '("case" "catch" "do" "else" "end" "false" "for" "function"
      "if" "in" "include"
      "new" "package" "page" "private" "protected" "public"
      "return" "tag" "taglib" "throw" "throws" "true" "try" "void" "while"))))

(defvar web-mode-erb-keywords
  (regexp-opt
   (append
    (cdr (assoc "erb" web-mode-extra-keywords))
    '("alias" "and" "begin" "break" "case" "class" "def" "defined?" "do"
      "elsif" "else" "end" "ensure" "fail" "for" "if" "in"
      "module" "next" "not" "or" "redo" "rescue" "retry" "return"
      "then" "super" "unless" "undef" "until" "when" "while" "yield"
      "__ENCODING__" "__FILE__" "__LINE__"))))

(defvar web-mode-mason-keywords
  (regexp-opt
   (append
    (cdr (assoc "mason" web-mode-extra-keywords))
    '("and" "base" "close" "die" "each" "else" "elsif" "eval" "exists"
      "foreach" "grep" "if" "length" "local" "my" "next" "open" "or"
      "package" "pop" "ref" "return" "stat" "sub" "tie"
      "undef" "unless" "use" "while"))))

(defvar web-mode-erb-builtins
  (regexp-opt
   (append
    (cdr (assoc "erb" web-mode-extra-builtins))

    '("__callee__" "__dir__" "__method__"
      "abort" "at_exit" "autoload" "autoload?"
      "binding" "block_given?" "caller" "catch"
      "eval" "exec" "exit" "exit!" "fail" "fork" "format"
      "lambda" "load" "loop" "open"
      "p" "print" "printf" "proc" "putc" "puts"
      "raise" "rand" "readline" "readlines" "require" "require_relative"
      "sleep" "spawn" "sprintf" "srand" "syscall" "system"
      "throw" "trap" "warn"
      "alias_method" "attr" "attr_accessor" "attr_reader" "attr_writer"
      "define_method" "extend" "include" "module_function"
      "prepend" "private" "protected" "public"
      "refine" "using"

      "error_message_on" "error_messages_for" "form" "input"
      "auto_discovery_link_tag" "image_tag" "javascript_include_tag"
      "stylesheet_link_tag" "image_path" "path_to_image"" "
      "javascript_path" "path_to_javascript" "register_javascript_expansion"
      "register_javascript_include_default" "register_stylesheet_expansion"
      "stylesheet_path" "path_to_stylesheet" "atom_feed" "entry" "updated"
      "benchmark" "cache" "capture" "content_for" "distance_of_time_in_words"
      "distance_of_time_in_words_to_now" "time_ago_in_words" "date_select"
      "datetime_select" "time_select" "select_date" "select_datetime"
      "select_day" "select_hour" "select_minute" "select_month" "select_second"
      "select_time" "select_year" "debug"
      "check_box" "fields_for" "file_field" "form_for" "hidden_field"
      "label" "password_field" "radio_button" "text_area" "text_field"
      "check_box_tag" "field_set_tag" "file_field_tag" "form_tag"
      "hidden_field_tag" "image_submit_tag" "label_tag" "password_field_tag"
      "radio_button_tag" "select_tag" "submit_tag" "text_area_tag"
      "text_field_tag"
      "collection_select" "country_options_for_select" "country_select"
      "option_groups_from_collection_for_select" "options_for_select"
      "options_from_collection_for_select" "select"
      "time_zone_options_for_select"
      "time_zone_select" "button_to_function" "define_javascript_functions"
      "escape_javascript" "javascript_tag" "link_to_function"" "
      "number_to_currency" "number_to_human_size" "number_to_percentage"
      "number_to_phone" "number_with_delimiter" "number_with_precision"
      "evaluate_remote_response" "form_remote_for" "form_remote_tag"
      "link_to_remote" "observe_field" "observe_field"
      "periodically_call_remote"
      "remote_form_for" "remote_function" "submit_to_remote" "update_page"
      "update_page_tag" "dom_class" "dom_id" "partial_path" "sanitize"
      "sanitize_css" "strip_links" "strip_tags"
      "cdata_section" "content_tag" "escape_once" "tag"
      "auto_link" "concat" "cycle" "excerpt" "highlight" "markdown" "pluralize"
      "reset_cycle" "simple_format" "textilize" "textilize_without_paragraph"
      "truncate" "word_wrap" "button_to" "current_page?" "link_to" "link_to_if"
      "link_to_unless" "link_to_unless_current" "mail_to" "url_for"
      "action_name" "atom_feed" "audio_path" "audio_tag"
      "content_tag_for" "controller" "controller_name" "action_name"
      "controller_path" "convert_to_model" "cookies" "csrf_meta_tag"
      "csrf_meta_tags" "headers"
      "current_cycle" "div_for" "email_field" "email_field_tag"
      "favicon_link_tag" "flash" "l" "button_tag"
      "grouped_collection_select" "grouped_options_for_select"
      "image_alt" "j" "javascript_cdata_section"
      "localize" "logger" "number_field"
      "number_field_tag" "number_to_human" "params" "path_to_audio"
      "path_to_video" "phone_field" "phone_field_tag" "provide"
      "range_field" "range_field_tag" "raw" "render" "request"
      "request_forgery_protection_token" "response" "safe_concat"
      "safe_join" "search_field" "search_field_tag"
      "session" "t" "telephone_field" "telephone_field_tag"
      "time_tag" "translate" "url_field" "url_field_tag"
      "url_options" "video_path" "video_tag" "simple_form_for"

      ))))

(defvar web-mode-asp-constants
  (regexp-opt
   (append
    (cdr (assoc "asp" web-mode-extra-constants))
    '("adAsyncExecute" "adAsyncFetch" "adAsyncFetchNonBlocking" "adCmdFile"
      "adCmdStoredProc" "adCmdTable" "adCmdTableDirect" "adCmdText" "adCmdUnknown"
      "adCmdUnspecified" "adExecuteNoRecords" "adExecuteRecord" "adExecuteStream"
      "adLockBatchOptimistic" "adLockOptimistic" "adLockPessimistic"
      "adLockReadOnly" "adLockUnspecified" "adOpenDynamic" "adOpenForwardOnly"
      "adOpenKeyset" "adOpenStatic" "adOpenUnspecified" "adOptionUnspecified"
      "Empty" "Nothing" "Null" "True" "False"
      "vbBack" "vbCr" "vbCrLf" "vbFormFeed" "vbLf" "vbNewLine" "vbNullChar"
      "vbNullString" "vbObjectError" "vbScript" "vbTab" "vbVerticalTab"))))

(defvar web-mode-asp-keywords
  (regexp-opt
   (append
    (cdr (assoc "asp" web-mode-extra-keywords))
    '("Abs" "And" "Array" "Asc" "Atn"
      "CBool" "CByte" "CCur" "CDate" "CDbl" "CInt" "CLng" "CSng" "CStr"
      "Call" "Case" "Chr" "Class" "Const" "Cos" "CreateObject"
      "Date" "DateAdd" "DateDiff" "DatePart" "DateSerial" "DateValue"
      "Day" "Dim" "Do"
      "Each" "Else" "ElseIf" "End" "Erase" "Err" "Eval" "Exit" "Exp"
      "Explicit"
      "Filter" "Fix" "For" "FormatCurrency" "FormatDateTime"
      "FormatNumber" "FormatPercent" "Function"
      "GetLocale" "GetObject" "GetRef" "Hex" "Hour"
      "If" "In" "InStr" "InStrRev" "InputBox" "Int" "IsArray" "IsDate"
      "IsEmpty" "IsNull" "IsNumeric" "IsObject" "Join"
      "LBound" "LCase" "LTrim" "Language" "Left" "Len" "Let"
      "LoadPicture" "Log" "Loop"
      "Mid" "Minute" "Month" "MonthName" "MsgBox"
      "New" "Next" "Not" "Now"
      "Oct" "On" "Option" "Or" "Preserve" "Private" "Public"
      "RGB" "RTrim" "Redim" "Rem" "Replace" "Right" "Rnd" "Round"
      "ScriptEngine" "ScriptEngineBuildVersion"
      "ScriptEngineMajorVersion" "ScriptEngineMinorVersion"
      "Second" "Select" "Set" "SetLocale" "Sgn" "Sin" "Space" "Split"
      "Sqr" "StrComp" "StrReverse" "String" "Sub"
      "Tan" "Then" "Time" "TimeSerial" "TimeValue" "Timer" "To" "Trim"
      "TypeName"
      "UBound" "UCase" "Until" "VarType"
      "Weekday" "WeekdayName" "Wend" "With" "While" "Year"))))

(defvar web-mode-asp-types
  (regexp-opt
   (append
    (cdr (assoc "asp" web-mode-extra-types))
    '("Application" "ASPError" "Request" "Response" "Server" "Session"))))

(defvar web-mode-aspx-keywords
  (regexp-opt
   (append
    (cdr (assoc "aspx" web-mode-extra-keywords))
    '("case" "catch" "do" "else" "end" "for" "foreach" "function"
      "if" "in" "include" "new" "package" "page" "return"
      "tag" "throw" "throws" "try" "while"))))

(defvar web-mode-smarty-keywords
  (regexp-opt '("as")))

(defvar web-mode-velocity-keywords
  (eval-when-compile
    (regexp-opt '("in" "true" "false"))))

(defvar web-mode-freemarker-keywords
  (eval-when-compile
    (regexp-opt '("as" "list"))))

(defvar web-mode-go-keywords
  (eval-when-compile
    (regexp-opt
     '("define" "else" "end" "if" "pipeline" "range" "template" "with"))))

(defvar web-mode-go-functions
  (eval-when-compile
    (regexp-opt
     '("and" "call" "html" "index" "js" "len" "not" "or"
       "print" "printf" "println" "urlquery"))))

(defvar web-mode-closure-keywords
  (eval-when-compile
    (regexp-opt '("in" "and" "not" "or"))))

(defvar web-mode-django-control-blocks
  '(

    "assets" "autoescape"
    "block" "blocktrans"
    "cache" "call" "capture" "comment"
    "draw"
    "embed"
    "filter" "for" "foreach" "form"
    "if" "ifchanged" "ifequal" "ifnotequal"
    "macro"
    "random" "raw"
    "safe" "sandbox" "spaceless"
    "tablerow"
    "unless"
    "verbatim"
    "with"

    "endassets" "endautoescape"
    "endblock" "endblocktrans"
    "endcache" "endcall" "endcapture" "endcomment"
    "draw"
    "endembed"
    "endfilter" "endfor" "endforeach" "endform"
    "endif" "endifchanged" "endifequal" "endifnotequal"
    "endmacro"
    "endrandom" "endraw"
    "endsafe" "endsandbox"  "endspaceless"
    "endtablerow"
    "endunless"
    "endverbatim"
    "endwith"

    ;; "set" "endset" ;#504

    "csrf_token" "cycle" "debug"
    "elif" "else" "elseif" "elsif" "empty" "extends"
    "firstof" "include" "load" "lorem" "now" "regroup" "ssi"
    "trans" "templatetag" "url" "widthratio"

    ))

(defvar web-mode-django-control-blocks-regexp
  (regexp-opt web-mode-django-control-blocks t))

(defvar web-mode-django-keywords
  (eval-when-compile
    (regexp-opt
     '("and" "as" "assign"
       "break"
       "cache" "call" "case" "context" "continue"
       "do"
       "flush" "from"
       "ignore" "import" "in" "is"
       "layout" "load"
       "missing"
       "none" "not"
       "or"
       "pluralize"
       "random"
       "set" ;#504
       "unless" "use"
       "var"
       ))))

(defvar web-mode-django-types
  (eval-when-compile
    (regexp-opt '("null" "false" "true"))))

(defvar web-mode-directives
  (eval-when-compile
    (regexp-opt
     '("include" "page" "taglib"
       "Assembly" "Control" "Implements" "Import"
       "Master" "OutputCache" "Page" "Reference" "Register"))))

(defvar web-mode-template-toolkit-keywords
  (regexp-opt
   '("block" "call" "case" "catch" "clear" "default" "do"
     "else" "elsif" "end" "filter" "final" "for"
     "foreach" "get" "if" "in" "include" "insert" "is" "last"
     "macro" "meta" "or" "perl" "process" "rawperl" "return"
     "set" "stop" "switch" "tags" "throw" "try"
     "unless" "use" "while" "wrapper")))

(defvar web-mode-perl-keywords
  (regexp-opt
   '("__DATA__" "__END__" "__FILE__" "__LINE__" "__PACKAGE__"
     "and" "cmp" "continue" "CORE" "do" "else" "elsif" "eq" "exp"
     "for" "foreach" "ge" "gt" "if" "le" "lock" "lt" "m" "ne" "no"
     "or" "package" "q" "qq" "qr" "qw" "qx" "s" "sub"
     "tr" "unless" "until" "while" "xor" "y"
     "my" "use" "print" "say")))

(defvar web-mode-javascript-keywords
  (regexp-opt
   (append
    (cdr (assoc "javascript" web-mode-extra-keywords))
    '("break" "case" "catch" "class" "const" "continue"
      "debugger" "default" "delete" "do" "else" "enum" "eval"
      "export" "extends" "finally" "for" "from" "function" "get" "if"
      "implements" "import" "in" "instanceof" "interface" "let"
      "new" "of" "package" "private" "protected" "public"
      "return" "set" "static" "super" "switch"
      "throw" "try" "typeof" "var" "void" "while" "with" "yield"))))

(defvar web-mode-javascript-constants
  (regexp-opt
   '("false" "null" "undefined" "Infinity" "NaN" "true" "arguments" "this")))

(defvar web-mode-razor-keywords
  (regexp-opt
   (append
    (cdr (assoc "razor" web-mode-extra-keywords))
    '("false" "true" "foreach" "if" "else" "in" "var" "for" "display"
      "match" "case" "to"
      "Html"))))

(defvar web-mode-selector-font-lock-keywords
  (list
   '("$[[:alnum:]-]+" 0 'web-mode-css-variable-face)
   (cons (concat "@\\(" web-mode-css-at-rules "\\)\\_>")
         '(0 'web-mode-css-at-rule-face))
   '("\\_<\\(all\|braille\\|embossed\\|handheld\\|print\\|projection\\|screen\\|speech\\|tty\\|tv\\|and\\|or\\)\\_>"
     1 'web-mode-keyword-face)
   '("[^,]+" 0 'web-mode-css-selector-face)
   (cons (concat ":\\(" web-mode-css-pseudo-classes "\\)\\(([^)]*)\\)?")
         '(0 'web-mode-css-pseudo-class-face t t))
   ))

(defvar web-mode-declaration-font-lock-keywords
  (list
   '("--[[:alnum:]-]+" 0 'web-mode-css-variable-face)
   '("$[[:alnum:]-]+" 0 'web-mode-css-variable-face)
   (cons (concat "@\\(" web-mode-css-at-rules "\\)\\_>") '(1 'web-mode-css-at-rule-face))
   '("\\([[:alpha:]-]+\\)[ ]?:" 0 'web-mode-css-property-name-face)
   '("\\([[:alpha:]-]+\\)[ ]?(" 1 'web-mode-css-function-face)
   '("#[[:alnum:]]\\{1,6\\}" 0 'web-mode-css-color-face t t)
   '("![ ]?important" 0 'web-mode-css-priority-face t t)
   '("\\([^,]+\\)[ ]+{" 1 'web-mode-css-selector-face)
   '("'[^']*'\\|\"[^\"]*\"" 0 'web-mode-string-face t t)
   ))

(defvar web-mode-html-font-lock-keywords
  (list
   '("</?[[:alnum:]]+[ >]\\|>" 0 'web-mode-html-tag-face t)
   '(" \\([[:alnum:]-]+=\\)\\(\"[^\"]+\"\\)"
     (1 'web-mode-html-attr-name-face)
     (2 'web-mode-html-attr-value-face))
   ))

(defvar web-mode-javascript-font-lock-keywords
  (list
   '("@\\([[:alnum:]_]+\\)\\_>" 0 'web-mode-keyword-face)
   ;;(cons (concat "\\_<\\(" web-mode-javascript-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   (cons (concat "\\([ \t}{(]\\|^\\)\\(" web-mode-javascript-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   (cons (concat "\\_<\\(" web-mode-javascript-constants "\\)\\_>") '(0 'web-mode-constant-face))
   '("\\_<\\(new\\|instanceof\\|class\\|extends\\) \\([[:alnum:]_.]+\\)\\_>" 2 'web-mode-type-face)
   '("\\_<\\([[:alnum:]_]+\\):[ ]*function[ ]*(" 1 'web-mode-function-name-face)
   '("\\_<\\(function\\|get\\|set\\)[ ]+\\([[:alnum:]_]+\\)"
     (1 'web-mode-keyword-face)
     (2 'web-mode-function-name-face))
   '("([ ]*\\([[:alnum:]_]+\\)[ ]*=>" 1 'web-mode-function-name-face)
   '("[ ]*\\([[:alnum:]_]+\\)[ ]*=[ ]*([^)]*)[ ]*=>[ ]*{" 1 'web-mode-function-name-face)
   '("\\_<\\(var\\|let\\|const\\)[ ]+\\([[:alnum:]_]+\\)" 2 'web-mode-variable-name-face)
   '("\\([[:alnum:]_]+\\)[ ]*=> [{(]" 1 'web-mode-variable-name-face)
   '("\\(function\\|[,=]\\|^\\)[ ]*("
     ("\\([[:alnum:]_]+\\)\\([ ]*=[^,)]*\\)?[,)]" nil nil (1 'web-mode-variable-name-face)))
   '("\\([[:alnum:]_]+\\):" 1 'web-mode-variable-name-face)
   '("\\_<\\([[:alnum:]_-]+\\)[ ]?(" 1 'web-mode-function-call-face)
   ))

(defvar web-mode-html-tag-font-lock-keywords
  (list
   '("\\(</?\\)\\([[:alnum:]]+\\)"
     (1 'web-mode-html-tag-bracket-face)
     (2 'web-mode-html-tag-face))
   '("\"[^\"]*\"" 0 'web-mode-html-attr-value-face)
   '("\\([[:alnum:]]+\\)" 1 'web-mode-html-attr-name-face)
   '("/?>" 0 'web-mode-html-tag-bracket-face)
  ))

(defvar web-mode-dust-font-lock-keywords
  (list
   '("{[#:/?@><+^]\\([[:alpha:]_.]+\\)" 1 'web-mode-block-control-face)
   '(":\\([[:alpha:]]+\\)" 1 'web-mode-keyword-face)
   '("\\_<\\([[:alnum:]_]+=\\)\\(\"[^\"]*\"\\|[[:alnum:]_]*\\)"
     (1 'web-mode-block-attr-name-face)
     (2 'web-mode-block-attr-value-face))
   '("\\\([[:alnum:]_.]+\\)" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-template-toolkit-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-template-toolkit-keywords "\\)\\_>") '(1 'web-mode-keyword-face))
   '("\\\([[:alpha:]][[:alnum:]_]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("\\\([[:alpha:]][[:alnum:]_]+\\)" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-smarty-font-lock-keywords
  (list
   (cons (concat "[ ]\\(" web-mode-smarty-keywords "\\)[ ]") '(1 'web-mode-keyword-face))
   '("{/?\\([[:alpha:]_]+\\)" 1 'web-mode-block-control-face)
   '("\\([}{]\\)" 0 'web-mode-block-delimiter-face)
   '("\\_<\\([$]\\)\\([[:alnum:]_]+\\)" (1 nil) (2 'web-mode-variable-name-face))
   '("\\_<\\(\\sw+\\)[ ]?(" 1 'web-mode-function-call-face)
   '(" \\(\\sw+[ ]?=\\)" 1 'web-mode-param-name-face)
   '(" \\(\\sw+\\)[ }]" 1 'web-mode-param-name-face)
   '("|\\([[:alnum:]_]+\\)" 1 'web-mode-function-call-face)
   '("\\(->\\)\\(\\sw+\\)" (1 nil) (2 'web-mode-variable-name-face))
   '("[.]\\([[:alnum:]_-]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("[.]\\([[:alnum:]_]+\\)" 1 'web-mode-variable-name-face)
   '("#\\([[:alnum:]_]+\\)#" 1 'web-mode-variable-name-face)
   ))

(defvar web-mode-velocity-font-lock-keywords
  (list
   '("#{?\\([[:alpha:]_]+\\)\\_>" (1 'web-mode-block-control-face))
   (cons (concat "\\_<\\(" web-mode-velocity-keywords "\\)\\_>") '(1 'web-mode-keyword-face t t))
   '("#macro([ ]*\\([[:alpha:]]+\\)[ ]+" 1 'web-mode-function-name-face)
   '("[.]\\([[:alnum:]_-]+\\)" 1 'web-mode-variable-name-face)
   '("\\_<\\($[!]?[{]?\\)\\([[:alnum:]_-]+\\)[}]?" (1 nil) (2 'web-mode-variable-name-face))
   ))

(defvar web-mode-mako-tag-font-lock-keywords
  (list
   '("</?%\\([[:alpha:]:]+\\)" 1 'web-mode-block-control-face)
   '("\\_<\\([[:alpha:]]+=\\)\\(\"[^\"]*\"\\)"
     (1 'web-mode-block-attr-name-face t t)
     (2 'web-mode-block-attr-value-face t t))
   ))

(defvar web-mode-mako-block-font-lock-keywords
  (list
   '("\\_<\\(\\sw+\\)[ ]?(" 1 'web-mode-function-call-face)
   (cons (concat "\\_<\\(" web-mode-python-constants "\\)\\_>") '(1 'web-mode-constant-face))
   (cons (concat "\\_<\\(" web-mode-python-keywords "\\)\\_>") '(1 'web-mode-keyword-face))
   (cons (concat "\\_<\\(endfor\\|endif\\|endwhile\\)\\_>") '(1 'web-mode-keyword-face))
   ))

(defvar web-mode-web2py-font-lock-keywords
  (list
   '("\\_<\\(\\sw+\\)[ ]?(" 1 'web-mode-function-call-face)
   (cons (concat "\\_<\\(" web-mode-python-constants "\\)\\_>") '(1 'web-mode-constant-face))
   (cons (concat "\\_<\\(" web-mode-python-keywords "\\)\\_>") '(1 'web-mode-keyword-face))
   (cons (concat "\\_<\\(block\\|extend\\|super\\|end\\|include\\)\\_>") '(1 'web-mode-keyword-face))
   ))

(defvar web-mode-django-expr-font-lock-keywords
  (list
   '("|[ ]?\\([[:alpha:]_]+\\)\\_>" 1 'web-mode-filter-face)
   (cons (concat "\\_<\\(" web-mode-django-types "\\)\\_>") '(1 'web-mode-type-face))
   '("\\_<\\([[:alpha:]_]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("[[:alnum:]_]+" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-django-code-font-lock-keywords
  (list
   (cons (concat "{%[ ]*\\(" web-mode-django-control-blocks-regexp "\\)[ %]") '(1 'web-mode-block-control-face))
   '("{%[ ]*\\(end[[:alpha:]]+\\)\\_>" 1 'web-mode-block-control-face) ;#504
   (cons (concat "\\_<\\(" web-mode-django-keywords "\\)\\_>") '(1 'web-mode-keyword-face))
   (cons (concat "\\_<\\(" web-mode-django-types "\\)\\_>") '(1 'web-mode-type-face))
   '("|[ ]?\\([[:alpha:]_]+\\)\\_>" 1 'web-mode-function-call-face)
   '("\\_<\\([[:alpha:]_]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("[[:alnum:]_.]+" 0 'web-mode-variable-name-face)
   '("[[:alnum:]_]+\\([.][[:alnum:]_]+\\)+" 0 'web-mode-variable-name-face t t)
   ))

(defvar web-mode-ctemplate-font-lock-keywords
  (list
   '("{[~]?{[#/>]?[ ]*\\([[:alnum:]_-]+\\)" 1 'web-mode-block-control-face)
   '("[ \t]+\\([[:alnum:]_-]+\\)=\\([[:alnum:]_.]+\\|\"[^\"]+\"\\|'[^']+'\\|\([^)]+\)\\)"
     (1 'web-mode-block-attr-name-face)
     (2 'web-mode-block-attr-value-face))
   '("\"[^\"]+\"" 0 'web-mode-block-string-face)
   ))

(defvar web-mode-razor-font-lock-keywords
  (list
   '("@\\([[:alnum:]_.]+\\)[ ]*[({]" 1 'web-mode-block-control-face)
   (cons (concat "\\_<\\(" web-mode-razor-keywords "\\)\\_>") '(1 'web-mode-keyword-face))
   '("\\_<\\(String\\)\\_>" 1 'web-mode-type-face)
   '("\\([[:alnum:]]+:\\)" 1 'web-mode-symbol-face)
   '("\\(@[[:alnum:]_.]+\\)" 1 'web-mode-variable-name-face)
   ))

(defvar web-mode-riot-font-lock-keywords
  (list
   '("\\(parent\\|opts\\|tags\\|this\\)\\.\\([[:alnum:]_.]+\\)"
     (1 'web-mode-constant-face)
     (2 'web-mode-variable-name-face))
   '("\\([[:alnum:]_.]+\\)" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-closure-font-lock-keywords
  (list
   '("{/?\\([[:alpha:]]+\\)" 1 'web-mode-block-control-face)
   '("{param[ ]+\\([[:alnum:]]+\\)" 1 'web-mode-symbol-face)
   '("\\_<\\(true\\|false\\|null\\)\\_>" 1 'web-mode-type-face)
   (cons (concat "\\_<\\(" web-mode-closure-keywords "\\)\\_>") '(1 'web-mode-keyword-face))
   '("{\\(alias\\|call\\|delcall\\|delpackage\\|deltemplate\\|namespace\\|template\\)[ ]+\\([[:alnum:].]+\\)" 2 'web-mode-constant-face)
   '("\\(allowemptydefault\\|data\\|desc\\|meaning\\|autoescape\\|private\\|variant\\)=" 0 'web-mode-block-attr-name-face)
   '("|\\([[:alpha:]]+\\)" 1 'web-mode-function-call-face)
   '("\\_<\\([[:alnum:]]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("$\\([[:alnum:]._]+\\)" 1 'web-mode-variable-name-face)
   ))

(defvar web-mode-go-font-lock-keywords
  (list
   '("{{[ ]*\\([[:alpha:]]+\\)" 1 'web-mode-block-control-face)
   (cons (concat "\\_<\\(" web-mode-go-keywords "\\)\\_>") '(1 'web-mode-keyword-face))
   (cons (concat "\\_<\\(" web-mode-go-functions "\\)\\_>") '(1 'web-mode-function-call-face))
   '("[$.]\\([[:alnum:]_]+\\)" 1 'web-mode-variable-name-face t t)
   ))

(defvar web-mode-expression-font-lock-keywords
  (list
   '("[[:alpha:]_]" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-angular-font-lock-keywords
  (list
   '("[[:alpha:]_]" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-underscore-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-javascript-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   '("\\_<\\(_\.[[:alpha:]]+\\)(" 1 'web-mode-function-call-face)
   '("\\_<new \\([[:alnum:]_.]+\\)\\_>" 1 'web-mode-type-face)
   '("\\_<\\([[:alnum:]_]+\\):[ ]*function[ ]*(" 1 'web-mode-function-name-face)
   '("\\_<\\(var\\)\\_>[ ]+\\([[:alnum:]_]+\\)"
     (1 'web-mode-keyword-face)
     (2 'web-mode-variable-name-face))
   ))

(defvar web-mode-engine-tag-font-lock-keywords
  (list
   '("</?\\([[:alpha:]]+\\(?:Template\\|[:.][[:alpha:]-]+\\)\\)" 1 'web-mode-block-control-face)
   '("\\_<\\([[:alpha:]-]+=\\)\\(\"[^\"]*\"\\)"
     (1 'web-mode-block-attr-name-face t t)
     (2 'web-mode-block-attr-value-face t t))
   '("\\_<\\([[:alpha:]-]+=\\)\\('[^']*\'\\)"
     (1 'web-mode-block-attr-name-face t t)
     (2 'web-mode-block-attr-value-face t t))
   ))

(defvar web-mode-jsp-font-lock-keywords
  (list
   '("\\(throws\\|new\\|extends\\)[ ]+\\([[:alnum:].]+\\)" 2 'web-mode-type-face)
   (cons (concat "\\_<\\(" web-mode-jsp-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   '("\\_<\\([[:alnum:]._]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("@\\(\\sw*\\)" 1 'web-mode-variable-name-face)
   '("\\_<\\([[:alnum:].]+\\)[ ]+[{[:alpha:]]+" 1 'web-mode-type-face)
   ))

(defvar web-mode-asp-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-asp-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   (cons (concat "\\_<\\(" web-mode-asp-types "\\)\\_>") '(0 'web-mode-type-face))
   (cons (concat "\\_<\\(" web-mode-asp-constants "\\)\\_>") '(0 'web-mode-constant-face))
   '("\\(Class\\|new\\) \\([[:alnum:]_]+\\)" 2 'web-mode-type-face)
   '("Const \\([[:alnum:]_]+\\)" 1 'web-mode-constant-face)
   '("\\_<dim\\_>"
     (0 'web-mode-keyword-face)
     ("[[:alnum:]_]+" nil nil (0 'web-mode-variable-name-face)))
   '("\\_<\\(public\\|private\\|sub\\|function\\)\\_> \\([[:alnum:]_]+\\)[ ]*(" 2 'web-mode-function-name-face)
   '("\\_<\\(public\\|private\\|dim\\)\\_> \\([[:alnum:]_]+\\)" 2 'web-mode-variable-name-face)
   ))

(defvar web-mode-aspx-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-aspx-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   '("\\_<\\([[:alnum:].]+\\)[ ]+[[:alpha:]]+" 1 'web-mode-type-face)
   ))

(defvar web-mode-uel-font-lock-keywords
  (list
   '("[$#{]{\\|}" 0 'web-mode-preprocessor-face)
   '("\\([[:alpha:]_]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("|[ ]*\\(trim\\|x\\|u\\)" 1 'web-mode-function-call-face)
   '("[[:alpha:]_]" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-php-var-interpolation-font-lock-keywords
  (list
   '("[[:alpha:]_]" 0 'web-mode-variable-name-face)
   '("\".+\"\\|'.*'" 0 'web-mode-string-face)
   ))

(defvar web-mode-marko-font-lock-keywords
  (list
   '("[[:alnum:]_]+" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-freemarker-square-font-lock-keywords
  (list
   '("\\[/?[#@]\\([[:alpha:]_.]*\\)" 1 'web-mode-block-control-face)
   '("#\\(macro\\|function\\) \\([[:alpha:]]+\\)" 2 'web-mode-function-name-face)
   (cons (concat "\\_<\\(" web-mode-freemarker-keywords "\\)\\_>") '(1 'web-mode-keyword-face))
   '("\\_<\\([[:alnum:]._]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("[[:alpha:]]\\([[:alnum:]_]+\\)?" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-freemarker-font-lock-keywords
  (list
   '("</?[#@]\\([[:alpha:]_.]*\\)" 1 'web-mode-block-control-face)
   '("#\\(macro\\|function\\) \\([[:alpha:]]+\\)" 2 'web-mode-function-name-face)
   (cons (concat "\\_<\\(" web-mode-freemarker-keywords "\\)\\_>") '(1 'web-mode-keyword-face))
   '("\\_<\\([[:alnum:]._]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("[[:alpha:]]\\([[:alnum:]_]+\\)?" 0 'web-mode-variable-name-face)
   ))

(defvar web-mode-directive-font-lock-keywords
  (list
   '("<%@[ ]*\\([[:alpha:]]+\\)[ ]+" 1 'web-mode-block-control-face)
   '("\\_<\\([[:alpha:]]+=\\)\\(\"[^\"]*\"\\)"
     (1 'web-mode-block-attr-name-face t t)
     (2 'web-mode-block-attr-value-face t t))
   ))

(defvar web-mode-erb-font-lock-keywords
  (list
   '("[^:]\\(:[[:alnum:]_]+\\)" 1 'web-mode-symbol-face)
   '("\\([[:alnum:]_]+:\\)[ ]+" 1 'web-mode-symbol-face)
   (cons (concat "\\_<\\(" web-mode-erb-builtins "\\)\\_>") '(0 'web-mode-builtin-face))
   (cons (concat "\\_<\\(" web-mode-erb-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   '("\\_<\\(self\\|true\\|false\\|nil\\)\\_>" 0 'web-mode-variable-name-face)
   '("[@$]@?\\([[:alnum:]_]+\\)" 0 'web-mode-variable-name-face)
   '("class[ ]+\\([[:alnum:]_]+\\)" 1 'web-mode-type-face)
   '("def[ ]+\\([[:alnum:]_]+\\)" 1 'web-mode-function-name-face)
   '("\\(?:\\_<\\|::\\)\\([A-Z]+[[:alnum:]_]+\\)" 1 (unless (eq (char-after) ?\() 'web-mode-type-face))
   '("/[^/]+/" 0 'web-mode-string-face)
   ))

(defvar web-mode-ejs-font-lock-keywords
  web-mode-javascript-font-lock-keywords)

(defvar web-mode-python-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-python-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   ))

(defvar web-mode-erlang-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-erlang-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   (cons (concat "\\_<\\(" web-mode-erlang-constants "\\)\\_>") '(0 'web-mode-constant-face))
   '("@\\([[:alnum:]_]+\\)" 0 'web-mode-variable-name-face)
   '("[ ]\\(:[[:alnum:]-_]+\\)" 1 'web-mode-symbol-face)
   ))

(defvar web-mode-mason-code-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-mason-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   '("sub[ ]+\\([[:alnum:]_]+\\)" 1 'web-mode-function-name-face)
   '("\\_<\\([[:alnum:]_]+\\)[ ]?::" 1 'web-mode-type-face)
   '("\\([@]\\)\\([[:alnum:]#_]*\\)" (1 nil) (2 'web-mode-variable-name-face))
   '("\\_<\\([$%]\\)\\([[:alnum:]@#_]*\\)" (1 nil) (2 'web-mode-variable-name-face))
   '("{\\([[:alnum:]_]+\\)}" 1 'web-mode-variable-name-face)
   '("\\_<\\(\\sw+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("[[:alnum:]_][ ]?::[ ]?\\([[:alnum:]_]+\\)" 1 'web-mode-variable-name-face)
   '("->[ ]?\\([[:alnum:]_]+\\)" 1 'web-mode-variable-name-face)
   '("\\(?:method\\|def\\) \\([[:alnum:]._]+\\)" 1 'web-mode-function-name-face)
   '("|[ ]*\\([[:alnum:],]+\\)[ ]*%>" 1 'web-mode-filter-face)
   ))

(defvar web-mode-mason-block-font-lock-keywords
  (list
   '("<[/]?%\\([[:alpha:]]+\\)" 1 'web-mode-block-control-face)
   '("[[:alpha:]]" 0 'web-mode-block-attr-value-face)
   ))

(defvar web-mode-mojolicious-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-perl-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   '("\\_<\\(begin\\|end\\)\\_>" 1 'web-mode-constant-face)
   '("\\_<\\([$]\\)\\([[:alnum:]_]*\\)" (1 nil) (2 'web-mode-variable-name-face))
   ))

(defvar web-mode-lsp-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-lsp-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   (cons (concat "\\_<\\(" web-mode-lsp-constants "\\)\\_>") '(1 'web-mode-constant-face))
   '("[ ]\\(:[[:alnum:]-_]+\\)" 1 'web-mode-symbol-face)
   '("(defun \\([[:alnum:]-:]+\\)" 1 'web-mode-function-name-face)
   '("(defvar \\([[:alnum:]-:]+\\)" 1 'web-mode-variable-name-face)
   ))

(defvar web-mode-cl-emb-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-cl-emb-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   (cons (concat "\\_<\\(" web-mode-cl-emb-constants "\\)\\_>") '(0 'web-mode-constant-face))
   '("\\(@\\)" 1 'web-mode-function-call-face)
   (list (concat "\\(@" web-mode-cl-emb-keywords "\\)[ ]+\\([[:alnum:]_]+\\)")
         '(1 'web-mode-keyword-face)
         '(2 'web-mode-variable-name-face))
   ))

(defvar web-mode-php-font-lock-keywords
  (list
   (cons (concat "\\_<\\(" web-mode-php-keywords "\\)\\_>") '(0 'web-mode-keyword-face))
   (cons (concat "(\\_<\\(" web-mode-php-types "\\)\\_>") '(1 'web-mode-type-face))
   (cons (concat "\\_<\\(" web-mode-php-constants "\\)\\_>") '(0 'web-mode-constant-face))
   '("function[ ]+\\([[:alnum:]_]+\\)" 1 'web-mode-function-name-face)
   '("\\_<\\([[:alnum:]_]+\\)[ ]?(" 1 'web-mode-function-call-face)
   '("[[:alnum:]_][ ]?::[ ]?\\([[:alnum:]_]+\\)" 1 'web-mode-constant-face)
   '("->[ ]?\\([[:alnum:]_]+\\)" 1 'web-mode-variable-name-face)
   '("\\_<\\([[:alnum:]_]+\\)[ ]?::" 1 'web-mode-type-face)
   '("\\_<\\(instanceof\\|class\\|extends\\|new\\)[ ]+\\([[:alnum:]_]+\\)" 2 'web-mode-type-face)
   '("\\_<\\([$]\\)\\([[:alnum:]_]*\\)" (1 nil) (2 'web-mode-variable-name-face))
   ))

(defvar web-mode-latex-font-lock-keywords
  (list
   '("[[:alnum:]_]+" 0 'web-mode-function-name-face t t)
   ))

(defvar web-mode-blade-font-lock-keywords
  (append
   (list
    '("@\\([[:alpha:]_]+\\)" (1 'web-mode-block-control-face)))
   web-mode-php-font-lock-keywords))

(defvar web-mode-engines-font-lock-keywords
  '(("angular"          . web-mode-angular-font-lock-keywords)
    ("blade"            . web-mode-blade-font-lock-keywords)
    ("cl-emb"           . web-mode-cl-emb-font-lock-keywords)
    ("closure"          . web-mode-closure-font-lock-keywords)
    ("ctemplate"        . web-mode-ctemplate-font-lock-keywords)
    ("dust"             . web-mode-dust-font-lock-keywords)
    ("elixir"           . web-mode-erlang-font-lock-keywords)
    ("ejs"              . web-mode-ejs-font-lock-keywords)
    ("erb"              . web-mode-erb-font-lock-keywords)
    ("go"               . web-mode-go-font-lock-keywords)
    ("lsp"              . web-mode-lsp-font-lock-keywords)
    ("marko"            . web-mode-marko-font-lock-keywords)
    ("mojolicious"      . web-mode-mojolicious-font-lock-keywords)
    ("php"              . web-mode-php-font-lock-keywords)
    ("python"           . web-mode-python-font-lock-keywords)
    ("razor"            . web-mode-razor-font-lock-keywords)
    ("riot"             . web-mode-riot-font-lock-keywords)
    ("smarty"           . web-mode-smarty-font-lock-keywords)
    ("template-toolkit" . web-mode-template-toolkit-font-lock-keywords)
    ("underscore"       . web-mode-underscore-font-lock-keywords)
    ("web2py"           . web-mode-web2py-font-lock-keywords)
    ("velocity"         . web-mode-velocity-font-lock-keywords))
  "Engines font-lock keywords")

(defvar web-mode-before-auto-complete-hooks nil
  "List of functions to run before triggering the auto-complete library.

Auto-complete sources will sometimes need some tweaking to work
nicely with web-mode. This hook gives users the chance to adjust
the environment as needed for ac-sources, right before they're used.")

(defvar web-mode-ignore-ac-start-advice nil
  "If not nil 'defadvice' for 'ac-start' will be ignored.

Can be set inside a hook in 'web-mode-before-auto-complete-hooks' to
non nil to ignore the defadvice which sets ac-sources according to current
language. This is needed if the corresponding auto-completion triggers
another auto-completion with different ac-sources (e.g. ac-php)")

(defvar web-mode-ac-sources-alist nil
  "alist mapping language names to ac-sources for that language.")

(defvar web-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?- "_" table)
    (modify-syntax-entry ?_ "_" table) ;#563
    (modify-syntax-entry ?< "." table)
    (modify-syntax-entry ?> "." table)
    (modify-syntax-entry ?& "." table)
    (modify-syntax-entry ?/ "." table)
    (modify-syntax-entry ?= "." table)
    (modify-syntax-entry ?% "." table)
    table)
  "Syntax table used to reveal whitespaces.")

(defvar web-mode-map
  (let ((map (make-sparse-keymap)))

    (define-key map [menu-bar wm]             (cons "Web-Mode" (make-sparse-keymap)))
    (define-key map [menu-bar wm dom]         (cons "Dom" (make-sparse-keymap)))
    (define-key map [menu-bar wm blk]         (cons "Block" (make-sparse-keymap)))
    (define-key map [menu-bar wm attr]        (cons "Html Attr" (make-sparse-keymap)))
    (define-key map [menu-bar wm tag]         (cons "Html Tag" (make-sparse-keymap)))
    (define-key map [menu-bar wm elt]         (cons "Html Element" (make-sparse-keymap)))

    (define-key map [menu-bar wm sep-1]       '(menu-item "--"))

    (define-key map [menu-bar wm dom dom-xpa] '(menu-item "XPath" web-mode-dom-xpath))
    (define-key map [menu-bar wm dom dom-tra] '(menu-item "Traverse" web-mode-dom-traverse))
    (define-key map [menu-bar wm dom dom-err] '(menu-item "Show error(s)" web-mode-dom-errors-show))
    (define-key map [menu-bar wm dom dom-ent] '(menu-item "Replace html entities" web-mode-dom-entities-replace))
    (define-key map [menu-bar wm dom dom-quo] '(menu-item "Replace dumb quotes" web-mode-dom-quotes-replace))
    (define-key map [menu-bar wm dom dom-apo] '(menu-item "Replace apostrophes" web-mode-dom-apostrophes-replace))
    (define-key map [menu-bar wm dom dom-nor] '(menu-item "Normalise" web-mode-dom-normalize))

    (define-key map [menu-bar wm blk blk-sel] '(menu-item "Select" web-mode-block-select))
    (define-key map [menu-bar wm blk blk-pre] '(menu-item "Previous" web-mode-block-previous))
    (define-key map [menu-bar wm blk blk-nex] '(menu-item "Next" web-mode-block-next))
    (define-key map [menu-bar wm blk blk-kil] '(menu-item "Kill" web-mode-block-kill))
    (define-key map [menu-bar wm blk blk-end] '(menu-item "End" web-mode-block-end))
    (define-key map [menu-bar wm blk blk-clo] '(menu-item "Close" web-mode-block-close))
    (define-key map [menu-bar wm blk blk-beg] '(menu-item "Beginning" web-mode-block-beginning))

    (define-key map [menu-bar wm attr attr-ins] '(menu-item "Insert" web-mode-attribute-insert))
    (define-key map [menu-bar wm attr attr-end] '(menu-item "End" web-mode-attribute-end))
    (define-key map [menu-bar wm attr attr-beg] '(menu-item "Beginning" web-mode-attribute-beginning))
    (define-key map [menu-bar wm attr attr-sel] '(menu-item "Select" web-mode-attribute-select))
    (define-key map [menu-bar wm attr attr-kil] '(menu-item "Kill" web-mode-attribute-kill))
    (define-key map [menu-bar wm attr attr-nex] '(menu-item "Next" web-mode-attribute-next))
    (define-key map [menu-bar wm attr attr-pre] '(menu-item "Previous" web-mode-attribute-previous))
    (define-key map [menu-bar wm attr attr-tra] '(menu-item "Transpose" web-mode-attribute-transpose))

    (define-key map [menu-bar wm tag tag-beg] '(menu-item "Sort Attributes" web-mode-tag-attributes-sort))
    (define-key map [menu-bar wm tag tag-sel] '(menu-item "Select" web-mode-tag-select))
    (define-key map [menu-bar wm tag tag-pre] '(menu-item "Previous" web-mode-tag-previous))
    (define-key map [menu-bar wm tag tag-nex] '(menu-item "Next" web-mode-tag-next))
    (define-key map [menu-bar wm tag tag-end] '(menu-item "End" web-mode-tag-end))
    (define-key map [menu-bar wm tag tag-beg] '(menu-item "Beginning" web-mode-tag-beginning))

    (define-key map [menu-bar wm elt elt-wra] '(menu-item "Wrap" web-mode-element-wrap))
    (define-key map [menu-bar wm elt elt-van] '(menu-item "Vanish" web-mode-element-vanish))
    (define-key map [menu-bar wm elt elt-exc] '(menu-item "Transpose" web-mode-element-transpose))
    (define-key map [menu-bar wm elt elt-sel] '(menu-item "Select" web-mode-element-select))
    (define-key map [menu-bar wm elt elt-ren] '(menu-item "Rename" web-mode-element-rename))
    (define-key map [menu-bar wm elt elt-pre] '(menu-item "Previous" web-mode-element-previous))
    (define-key map [menu-bar wm elt elt-par] '(menu-item "Parent" web-mode-element-parent))
    (define-key map [menu-bar wm elt elt-nex] '(menu-item "Next" web-mode-element-next))
    (define-key map [menu-bar wm elt elt-mut] '(menu-item "Mute blanks" web-mode-element-mute-blanks))
    (define-key map [menu-bar wm elt elt-del] '(menu-item "Kill" web-mode-element-kill))
    (define-key map [menu-bar wm elt elt-end] '(menu-item "End" web-mode-element-end))
    (define-key map [menu-bar wm elt elt-inn] '(menu-item "Content (select)" web-mode-element-content-select))
    (define-key map [menu-bar wm elt elt-clo] '(menu-item "Close" web-mode-element-close))
    (define-key map [menu-bar wm elt elt-ins] '(menu-item "Insert" web-mode-element-insert))
    (define-key map [menu-bar wm elt elt-dup] '(menu-item "Clone" web-mode-element-clone))
    (define-key map [menu-bar wm elt elt-cfo] '(menu-item "Children fold" web-mode-element-children-fold-or-unfold))
    (define-key map [menu-bar wm elt elt-chi] '(menu-item "Child" web-mode-element-child))
    (define-key map [menu-bar wm elt elt-beg] '(menu-item "Beginning" web-mode-element-beginning))

    (define-key map [menu-bar wm fol]         '(menu-item "Fold/Unfold" web-mode-fold-or-unfold))
    (define-key map [menu-bar wm hig]         '(menu-item "Highlight buffer" web-mode-buffer-highlight))
    (define-key map [menu-bar wm ind]         '(menu-item "Indent buffer" web-mode-buffer-indent))
    (define-key map [menu-bar wm nav]         '(menu-item "Tag/Block navigation" web-mode-navigate))
    (define-key map [menu-bar wm exp]         '(menu-item "Mark and Expand" web-mode-mark-and-expand))
    (define-key map [menu-bar wm spa]         '(menu-item "Toggle whitespaces" web-mode-whitespaces-show))
    (define-key map [menu-bar wm sni]         '(menu-item "Insert snippet" web-mode-snippet-insert))

    ;;--------------------------------------------------------------------------
    ;; "C-c <LETTER>" are reserved for users

    (define-key map (kbd "C-c C-a b") 'web-mode-attribute-beginning)
    (define-key map (kbd "C-c C-a e") 'web-mode-attribute-end)
    (define-key map (kbd "C-c C-a i") 'web-mode-attribute-insert)
    (define-key map (kbd "C-c C-a n") 'web-mode-attribute-next)
    (define-key map (kbd "C-c C-a s") 'web-mode-attribute-select)
    (define-key map (kbd "C-c C-a k") 'web-mode-attribute-kill)
    (define-key map (kbd "C-c C-a p") 'web-mode-attribute-previous)
    (define-key map (kbd "C-c C-a t") 'web-mode-attribute-transpose)

    (define-key map (kbd "C-c C-b b") 'web-mode-block-beginning)
    (define-key map (kbd "C-c C-b c") 'web-mode-block-close)
    (define-key map (kbd "C-c C-b e") 'web-mode-block-end)
    (define-key map (kbd "C-c C-b k") 'web-mode-block-kill)
    (define-key map (kbd "C-c C-b n") 'web-mode-block-next)
    (define-key map (kbd "C-c C-b p") 'web-mode-block-previous)
    (define-key map (kbd "C-c C-b s") 'web-mode-block-select)

    (define-key map (kbd "C-c C-d a") 'web-mode-dom-apostrophes-replace)
    (define-key map (kbd "C-c C-d d") 'web-mode-dom-errors-show)
    (define-key map (kbd "C-c C-d e") 'web-mode-dom-entities-replace)
    (define-key map (kbd "C-c C-d n") 'web-mode-dom-normalize)
    (define-key map (kbd "C-c C-d q") 'web-mode-dom-quotes-replace)
    (define-key map (kbd "C-c C-d t") 'web-mode-dom-traverse)
    (define-key map (kbd "C-c C-d x") 'web-mode-dom-xpath)

    (define-key map (kbd "C-c C-e /") 'web-mode-element-close)
    (define-key map (kbd "C-c C-e a") 'web-mode-element-content-select)
    (define-key map (kbd "C-c C-e b") 'web-mode-element-beginning)
    (define-key map (kbd "C-c C-e c") 'web-mode-element-clone)
    (define-key map (kbd "C-c C-e d") 'web-mode-element-child)
    (define-key map (kbd "C-c C-e e") 'web-mode-element-end)
    (define-key map (kbd "C-c C-e f") 'web-mode-element-children-fold-or-unfold)
    (define-key map (kbd "C-c C-e i") 'web-mode-element-insert)
    (define-key map (kbd "C-c C-e k") 'web-mode-element-kill)
    (define-key map (kbd "C-c C-e m") 'web-mode-element-mute-blanks)
    (define-key map (kbd "C-c C-e n") 'web-mode-element-next)
    (define-key map (kbd "C-c C-e p") 'web-mode-element-previous)
    (define-key map (kbd "C-c C-e r") 'web-mode-element-rename)
    (define-key map (kbd "C-c C-e s") 'web-mode-element-select)
    (define-key map (kbd "C-c C-e t") 'web-mode-element-transpose)
    (define-key map (kbd "C-c C-e u") 'web-mode-element-parent)
    (define-key map (kbd "C-c C-e v") 'web-mode-element-vanish)
    (define-key map (kbd "C-c C-e w") 'web-mode-element-wrap)

    (define-key map (kbd "C-c C-t a") 'web-mode-tag-attributes-sort)
    (define-key map (kbd "C-c C-t b") 'web-mode-tag-beginning)
    (define-key map (kbd "C-c C-t e") 'web-mode-tag-end)
    (define-key map (kbd "C-c C-t m") 'web-mode-tag-match)
    (define-key map (kbd "C-c C-t n") 'web-mode-tag-next)
    (define-key map (kbd "C-c C-t p") 'web-mode-tag-previous)
    (define-key map (kbd "C-c C-t s") 'web-mode-tag-select)

    ;;--------------------------------------------------------------------------

    (define-key map (kbd "M-;")       'web-mode-comment-or-uncomment)

    ;;C-c C-a : attribute
    ;;C-c C-b : block
    ;;C-c C-d : dom
    ;;C-c C-e : element
    (define-key map (kbd "C-c C-f")   'web-mode-fold-or-unfold)
    (define-key map (kbd "C-c C-h")   'web-mode-buffer-highlight)
    (define-key map (kbd "C-c C-i")   'web-mode-buffer-indent)
    (define-key map (kbd "C-c C-j")   'web-mode-jshint)
    (define-key map (kbd "C-c C-l")   'web-mode-file-link)
    (define-key map (kbd "C-c C-m")   'web-mode-mark-and-expand)
    (define-key map (kbd "C-c C-n")   'web-mode-navigate)
    (define-key map (kbd "C-c C-r")   'web-mode-reload)
    (define-key map (kbd "C-c C-s")   'web-mode-snippet-insert)
    ;;C-c C-t : tag
    (define-key map (kbd "C-c C-w")   'web-mode-whitespaces-show)

    map)
  "Keymap for `web-mode'.")

;;---- COMPATIBILITY -----------------------------------------------------------

(eval-and-compile

  ;; compatibility with emacs 22
  (defun web-mode-string-match-p (regexp string &optional start)
    "Same as `string-match' except it does not change the match data."
    (let ((inhibit-changing-match-data t))
      (string-match regexp string start)))

  (unless (fboundp 'string-match-p)
    (fset 'string-match-p (symbol-function 'web-mode-string-match-p)))

  ;; compatibility with emacs < 23.3
  (if (fboundp 'with-silent-modifications)
      (defalias 'web-mode-with-silent-modifications 'with-silent-modifications)
    (defmacro web-mode-with-silent-modifications (&rest body)
      `(let ((old-modified-p (buffer-modified-p))
             (inhibit-modification-hooks t)
             (buffer-undo-list t))
         (unwind-protect
             ,@body
           (set-buffer-modified-p old-modified-p)))))

  ;; compatibility with emacs < 24
  (defalias 'web-mode-prog-mode
    (if (fboundp 'prog-mode) 'prog-mode 'fundamental-mode))

  ;; compatibility with emacs < 24.3
  (defun web-mode-buffer-narrowed-p ()
    (if (fboundp 'buffer-narrowed-p)
        (buffer-narrowed-p)
      (/= (- (point-max) (point-min)) (buffer-size))))

  ;; compatibility with emacs < 24.3
  (unless (fboundp 'setq-local)
    (defmacro setq-local (var val)
    `(set (make-local-variable ',var) ,val)))

  ) ;eval-and-compile

;;---- MAJOR MODE --------------------------------------------------------------

;;;###autoload
(define-derived-mode web-mode web-mode-prog-mode "Web"
  "Major mode for editing web templates."

  (make-local-variable 'web-mode-attr-indent-offset)
  (make-local-variable 'web-mode-attr-value-indent-offset)
  (make-local-variable 'web-mode-auto-pairs)
  (make-local-variable 'web-mode-block-regexp)
  (make-local-variable 'web-mode-change-beg)
  (make-local-variable 'web-mode-change-end)
  (make-local-variable 'web-mode-code-indent-offset)
  (make-local-variable 'web-mode-column-overlays)
  (make-local-variable 'web-mode-comment-formats)
  (make-local-variable 'web-mode-comment-style)
  (make-local-variable 'web-mode-content-type)
  (make-local-variable 'web-mode-css-indent-offset)
  (make-local-variable 'web-mode-display-table)
  (make-local-variable 'web-mode-django-control-blocks)
  (make-local-variable 'web-mode-django-control-blocks-regexp)
  (make-local-variable 'web-mode-enable-block-face)
  (make-local-variable 'web-mode-enable-inlays)
  (make-local-variable 'web-mode-enable-part-face)
  (make-local-variable 'web-mode-enable-sexp-functions)
  (make-local-variable 'web-mode-engine)
  (make-local-variable 'web-mode-engine-attr-regexp)
  (make-local-variable 'web-mode-engine-file-regexps)
  (make-local-variable 'web-mode-engine-open-delimiter-regexps)
  (make-local-variable 'web-mode-engine-token-regexp)
  (make-local-variable 'web-mode-expand-initial-pos)
  (make-local-variable 'web-mode-expand-initial-scroll)
  (make-local-variable 'web-mode-expand-previous-state)
  (make-local-variable 'web-mode-indent-style)
  (make-local-variable 'web-mode-indentless-attributes)
  (make-local-variable 'web-mode-indentless-elements)
  (make-local-variable 'web-mode-inhibit-fontification)
  (make-local-variable 'web-mode-is-scratch)
  (make-local-variable 'web-mode-jshint-errors)
  (make-local-variable 'web-mode-last-enabled-feature)
  (make-local-variable 'web-mode-markup-indent-offset)
  (make-local-variable 'web-mode-minor-engine)
  (make-local-variable 'web-mode-overlay-tag-end)
  (make-local-variable 'web-mode-overlay-tag-start)
  (make-local-variable 'web-mode-sql-indent-offset)
  (make-local-variable 'web-mode-time)

  (make-local-variable 'comment-end)
  (make-local-variable 'comment-region-function)
  (make-local-variable 'comment-start)
  (make-local-variable 'fill-paragraph-function)
  (make-local-variable 'font-lock-beg)
  (make-local-variable 'font-lock-defaults)
  (make-local-variable 'font-lock-extend-region-functions)
  (make-local-variable 'font-lock-end)
  (make-local-variable 'font-lock-support-mode)
  (make-local-variable 'font-lock-unfontify-region-function)
  (make-local-variable 'imenu-case-fold-search)
  (make-local-variable 'imenu-create-index-function)
  (make-local-variable 'imenu-generic-expression)
  (make-local-variable 'indent-line-function)
  (make-local-variable 'parse-sexp-lookup-properties)
  (make-local-variable 'uncomment-region-function)
  (make-local-variable 'yank-excluded-properties)

  (setq comment-end "-->"
        comment-region-function 'web-mode-comment-or-uncomment-region
        comment-start "<!--"
        fill-paragraph-function 'web-mode-fill-paragraph
        font-lock-defaults '(web-mode-font-lock-keywords t)
        font-lock-extend-region-functions '(web-mode-extend-region)
        font-lock-support-mode nil
        font-lock-unfontify-region-function 'web-mode-unfontify-region
        imenu-case-fold-search t
        imenu-create-index-function 'web-mode-imenu-index
        indent-line-function 'web-mode-indent-line
        parse-sexp-lookup-properties t
        yank-excluded-properties t
        uncomment-region-function 'web-mode-comment-or-uncomment-region)

  (substitute-key-definition 'indent-new-comment-line
                             'web-mode-comment-indent-new-line
                             web-mode-map global-map)

  (add-hook 'after-change-functions 'web-mode-on-after-change nil t)
  (add-hook 'after-save-hook        'web-mode-on-after-save t t)
  (add-hook 'change-major-mode-hook 'web-mode-on-exit nil t)
  (add-hook 'post-command-hook      'web-mode-on-post-command nil t)

  (cond
   ((boundp 'yas-after-exit-snippet-hook)
    (add-hook 'yas-after-exit-snippet-hook
              'web-mode-yasnippet-exit-hook
              t t))
   ((boundp 'yas/after-exit-snippet-hook)
    (add-hook 'yas/after-exit-snippet-hook
              'web-mode-yasnippet-exit-hook
              t t))
   )

  (when web-mode-enable-whitespace-fontification
    (web-mode-whitespaces-on))

  (when web-mode-enable-sexp-functions
    (setq-local forward-sexp-function 'web-mode-forward-sexp))

  (web-mode-guess-engine-and-content-type)
  (setq web-mode-change-beg (point-min)
        web-mode-change-end (point-max))
  (when (> (point-max) 256000)
    (web-mode-buffer-highlight))

  (when (and (boundp 'hs-special-modes-alist)
             (not (assoc major-mode hs-special-modes-alist)))
    (add-to-list 'hs-special-modes-alist '(web-mode "{" "}" "/[*/]" web-mode-forward-sexp nil))
    ) ;when

  )

;;---- DEFUNS ------------------------------------------------------------------

(defun web-mode-scan-region (beg end &optional content-type)
  "Identify nodes/parts/blocks and syntactic symbols (strings/comments)."
  ;;(message "scan-region: beg(%d) end(%d) content-type(%S)" beg end content-type)
  (web-mode-with-silent-modifications
   (save-excursion
     (save-restriction
       (save-match-data
         (let ((inhibit-point-motion-hooks t)
               (inhibit-quit t))
           (remove-list-of-text-properties beg end web-mode-scan-properties)
           (cond
            ((and content-type (string= content-type "php"))
;;             (web-mode-block-scan beg end)
             )
            ((and content-type (member content-type web-mode-part-content-types))
             (put-text-property beg end 'part-side
                                (cond
                                 ((string= content-type "javascript") 'javascript)
                                 ((string= content-type "json") 'json)
                                 ((string= content-type "jsx") 'jsx)
                                 ((string= content-type "css") 'css)
                                 ))
             (web-mode-scan-blocks beg end)
             (web-mode-part-scan beg end content-type))
            ((member web-mode-content-type web-mode-part-content-types)
             (web-mode-scan-blocks beg end)
             (web-mode-part-scan beg end))
            ((string= web-mode-engine "riot")
             (web-mode-scan-elements beg end)
             (web-mode-scan-blocks beg end)
             (web-mode-process-parts beg end 'web-mode-part-scan))
            (t
             (web-mode-scan-blocks beg end)
             (web-mode-scan-elements beg end)
             (web-mode-process-parts beg end 'web-mode-part-scan))
            ) ;cond
           (cons beg end)
           ))))))

(defun web-mode-scan-blocks (reg-beg reg-end)
  "Identifies blocks (with block-side, block-beg, block-end text properties)."
  (save-excursion

    (let ((i 0) open close closing-string start sub1 sub2 pos tagopen tmp delim-open delim-close part-beg part-end tagclose)

      (goto-char reg-beg)

      ;;(message "%S: %Sx%S" (point) reg-beg reg-end)
      ;;(message "regexp=%S" web-mode-block-regexp)
      (while (and (< i 2000)
                  (> reg-end (point))
                  web-mode-block-regexp
                  (re-search-forward web-mode-block-regexp reg-end t)
                  (not (eobp)))

        (setq i (1+ i)
              closing-string nil
              close nil
              tagopen (match-string 0)
              open (match-beginning 0)
              delim-open nil
              delim-close nil
              pos nil)

        (let ((l (length tagopen)))
          (when (member (string-to-char tagopen) '(?\s ?\t))
            (setq tagopen (replace-regexp-in-string "\\`[ \t]*" "" tagopen))
            (setq open (+ open (- l (length tagopen))))
            (setq l (length tagopen))
            )
          (setq sub1 (substring tagopen 0 1)
                sub2 (substring tagopen 0 (if (>= l 2) 2 1)))
          )
        ;;(message " found block #(%S) at pos=(%S), part-type=(%S)" i open (get-text-property open 'part-side))
        (cond

         ((string= web-mode-engine "php")
          (unless (member (char-after) '(?x ?X))
            (setq closing-string '("<\\?". "\\?>")))
          (cond
           ((looking-at-p "<?php")
            (setq delim-open "<?php"))
           ((eq (char-after) ?\=)
            (setq delim-open "<?="))
           (t
            (setq delim-open "<?"))
           ) ;cond
          (setq delim-close "?>")
          ) ;php

         ((string= web-mode-engine "erb")
          (cond
           ((string= sub2 "<%")
            (setq closing-string '("<%". "%>")
                  delim-open "<%[=-]?"
                  delim-close "[-]?%>")
            )
           (t
            (setq closing-string "EOL"
                  delim-open "%"))
           )
          ) ;erb

         ((string= web-mode-engine "django")
          (cond
           ((string= sub2 "{{")
            (setq closing-string '("{{" . "}}")
                  delim-open "{{"
                  delim-close "}}"))
           ((string= sub2 "{%")
            (setq closing-string "%}"
                  delim-open "{%[+-]?"
                  delim-close "[-]?%}"))
           (t
            (setq closing-string "#}"))
           )
          ) ;django

         ((string= web-mode-engine "ejs")
          (setq closing-string "%>"
                delim-open "<%[=-]?"
                delim-close "[-]?%>")
          ) ;ejs

         ((string= web-mode-engine "lsp")
          (setq closing-string "%>"
                delim-open "<%[%#]?"
                delim-close "%>")
          ) ;lsp

         ((string= web-mode-engine "mako")
          (cond
           ((and (string= tagopen "<%")
                 (member (char-after) '(?\s ?\n ?\!)))
            (setq closing-string "%>"
                  delim-open "<%[!]?"
                  delim-close "%>"))
           ((member sub2 '("<%" "</"))
            (setq closing-string ">"
                  delim-open "</?%"
                  delim-close "/?>"))
           ((string= sub2 "${")
            (setq closing-string "}"
                  delim-open "${"
                  delim-close "}"))
           (t
            (setq closing-string "EOL"
                  delim-open "%"))
           )
          ) ;mako

         ((string= web-mode-engine "cl-emb")
          (cond
           ((string= tagopen "<%#")
            (setq closing-string "#%>"))
           ((string= sub2 "<%")
            (setq closing-string "%>"
                  delim-open "<%[=%]?"
                  delim-close "%>"))
           )
          ) ;cl-emb

         ((string= web-mode-engine "elixir")
          (cond
           ((string= tagopen "<%#")
            (setq closing-string "%>"))
           ((string= sub2 "<%")
            (setq closing-string "%>"
                  delim-open "<%[=%]?"
                  delim-close "%>"))
           )
          ) ;elixir

         ((string= web-mode-engine "mojolicious")
          (cond
           ((string= tagopen "<%#")
            (setq closing-string "%>"))
           ((string= sub2 "<%")
            (setq closing-string "%>"
                  delim-open "<%\\(==\\|[=%]\\)?"
                  delim-close "%>"))
           ((string= sub2 "%#")
            (setq closing-string "EOL"))
           (t
            (setq closing-string "EOL"
                  delim-open "%\\(==\\|[=%]\\)?"))
           )
          ) ;mojolicious

         ((string= web-mode-engine "ctemplate")
          (cond
           ((member tagopen '("{{{" "{{~"))
            (setq closing-string "}~?}}"
                  delim-open "{{~?{"
                  delim-close "}~?}}")
            )
           ((string= tagopen "{~{")
            (setq closing-string "}~?}"
                  delim-open "{~{"
                  delim-close "}~?}")
            )
           ((string= tagopen "{{!")
            (setq closing-string (if (looking-at-p "--") "--}}" "}}"))
            )
           ((string= sub2 "{{")
            (setq closing-string "}~?}"
                  delim-open "{{[>#/%^&]?"
                  delim-close "}~?}"))
           (t
            (setq closing-string "}}"
                  delim-open "${{"
                  delim-close "}}"))
           )
          ) ;ctemplate

         ((string= web-mode-engine "aspx")
          (setq closing-string "%>"
                delim-open "<%[:=#@$]?"
                delim-close "%>")
          ) ;aspx

         ((string= web-mode-engine "asp")
          (cond
           ((string= sub2 "<%")
            (setq closing-string "%>"
                  delim-open "<%[:=#@$]?"
                  delim-close "%>"))
           (t
            (setq closing-string ">"
                  delim-open "</?"
                  delim-close "/?>"))
           )
          ) ;asp

         ((string= web-mode-engine "jsp")
          (cond
           ((looking-at-p "--")
            (setq closing-string "--%>"))
           ((string= sub2 "<%")
            (setq closing-string "%>"
                  delim-open "<%\\([!=@]\\|#=\\)?"
                  delim-close "[-]?%>"))
           ((string= sub2 "${")
            (setq closing-string "}"
                  delim-open "${"
                  delim-close "}"))
           )
          ) ;jsp

         ((string= web-mode-engine "clip")
          (setq closing-string ">"
                delim-open "</?"
                delim-close "/?>")
          ) ;clip

         ((string= web-mode-engine "blade")
          (cond
           ((string= tagopen "{{-")
            (setq closing-string "--}}"))
           ((string= tagopen "{!!")
            (setq closing-string "!!}"
                  delim-open "{!!"
                  delim-close "!!}"))
           ((string= tagopen "@{{")
            (setq closing-string nil))
           ((string= tagopen "{{{")
            (setq closing-string "}}}"
                  delim-open "{{{"
                  delim-close "}}}"))
           ((string= sub2 "{{")
            (setq closing-string "}}"
                  delim-open "{{"
                  delim-close "}}"))
           ((looking-at-p "[[:alnum:]]+\\.[[:alpha:]]+")
            )
           ((string= sub2 "@y")
            (setq closing-string ")"
                  delim-open "@"))
           ((string= sub1 "@")
            (setq closing-string "EOL"
                  delim-open "@"))
           )
          ) ;blade

         ((string= web-mode-engine "smarty")
          (cond
           ((string= tagopen "{*")
            (setq closing-string "*}")
            )
           ((string= tagopen "{#")
            (setq closing-string "#}"
                  delim-open "{#"
                  delim-close "#}")
            )
           (t
            (setq closing-string (cons "{" "}")
                  delim-open "{/?"
                  delim-close "}")
            ) ;t
           ) ;cond
          ) ;smarty

         ((string= web-mode-engine "web2py")
          (setq closing-string "}}"
                delim-open "{{[=]?"
                delim-close "}}")
          ) ;web2py

         ((string= web-mode-engine "dust")
          (cond
           ((string= sub2 "{!")
            (setq closing-string "!}"))
           (t
            (setq closing-string '("{". "}") ;;closing-string "}"
                  delim-open "{[#/:?@><+^]?"
                  delim-close "/?}")
            )
           )
          ) ;dust

         ((string= web-mode-engine "closure")
          (cond
           ((string= sub2 "//")
            (setq closing-string "EOL")
            )
           ((string= sub2 "/*")
            (setq closing-string "*/")
            )
           (t
            (setq closing-string "}"
                  delim-open "{/?"
                  delim-close "/?}")
            )
           )
          ) ;closure

         ((string= web-mode-engine "go")
          (setq closing-string "}}"
                delim-open "{{"
                delim-close "}}")
          ) ;go

         ((string= web-mode-engine "angular")
          (setq closing-string "}}"
                delim-open "{{"
                delim-close "}}")
          ) ;angular

         ((string= web-mode-engine "mason")
          (cond
           ((and (member sub2 '("<%" "</"))
                 (looking-at "[[:alpha:]]+"))
            (if (member (match-string-no-properties 0) '("after" "around" "augment" "before" "def" "filter" "method" "override"))
                (setq closing-string ">"
                      delim-open "<[/]?%"
                      delim-close ">")
              (setq closing-string (concat "</%" (match-string-no-properties 0) ">")
                    delim-open "<[^>]+>"
                    delim-close "<[^>]+>")
              ) ;if
            )
           ((and (string= sub2 "<%")
                 (eq (char-after) ?\s))
            (setq closing-string "%>"
                  delim-open "<%"
                  delim-close "%>"))
           ((string= tagopen "</&")
            (setq closing-string ">"
                  delim-open "</&"
                  delim-close ">")
            )
           ((string= sub2 "<&")
            (setq closing-string "&>"
                  delim-open "<&[|]?"
                  delim-close "&>"))
           (t
            (setq closing-string "EOL"
                  delim-open "%"))
           )
          ) ;mason

         ((string= web-mode-engine "underscore")
          (setq closing-string "%>"
                delim-open "<%"
                delim-close "%>")
          ) ;underscore

         ((string= web-mode-engine "template-toolkit")
          (cond
           ((string= tagopen "%%#")
            (setq closing-string "EOL"))
           ((string= tagopen "[%#")
            (setq closing-string "%]"))
           (t
            (setq closing-string "%]"
                  delim-open "\\[%[-+]?"
                  delim-close "[-=+]?%\\]"))
           )
          ) ;template-toolkit

         ((string= web-mode-engine "freemarker")
          (cond
           ((and (string= sub2 "<#") (eq (char-after) ?\-))
            (setq closing-string "-->"))
           ((string= sub1 "<")
            (setq closing-string ">"
                  delim-open "</?[#@]"
                  delim-close "/?>"))
           ((string= sub1 "[")
            (setq closing-string "]"
                  delim-open "\\[/?[#@]"
                  delim-close "/?\\]"))
           (t
            (setq closing-string "}"
                  delim-open "${"
                  delim-close "}"))
           )
          ) ;freemarker

         ((string= web-mode-engine "velocity")
          (cond
           ((string= sub2 "##")
            (setq closing-string "EOL"))
           ((string= sub2 "#*")
            (setq closing-string "*#"))
           (t
            (setq closing-string "EOV"
                  delim-open "#"))
           )
          ) ;velocity

         ((string= web-mode-engine "razor")
          (cond
           ((string= sub2 "@@")
            (forward-char 2)
            (setq closing-string nil))
           ((string= sub2 "@*")
            (setq closing-string "*@"))
           ((string= sub1 "@")
            (setq closing-string "EOR"
                  delim-open "@"))
           ((and (string= sub1 "}")
                 (looking-at-p "[ ]*\n"))
            (setq closing-string "EOC")
            )
           ((string= sub1 "}")
            ;;(message "%s: %s" (point) sub1)
            (save-excursion
              (let (paren-pos)
                (setq paren-pos (web-mode-part-opening-paren-position (1- (point))))
                (if (and paren-pos (get-text-property paren-pos 'block-side))
                    (setq closing-string "EOR")
                  (setq closing-string nil)
                  ) ;if
                ) ;let
              ) ;let
            ) ;case }
           ) ;cond
          ) ;razor

         ((and (string= web-mode-engine "riot")
               (not (get-text-property open 'part-side)))
          (setq closing-string "}"
                delim-open "{"
                delim-close "}")
          ) ;riot

         ((string= web-mode-engine "marko")
          (setq closing-string "}"
                delim-open "${"
                delim-close "}")
          ) ;marko

         ) ;cond

        (when closing-string

          (cond

           ((listp closing-string)
            (cond
             ((web-mode-rsf-balanced (car closing-string) (cdr closing-string) reg-end t)
              (setq close (match-end 0)
                    pos (point))
              )
             ((and (string= web-mode-engine "php")
                   (string= "<?" sub2))

              (if (or (text-property-not-all (1+ open) (point-max) 'tag-beg nil)
                      (text-property-not-all (1+ open) (point-max) 'block-beg nil)
                      (looking-at-p "[ \t\n]*<"))
                  (setq close nil
                        delim-close nil
                        pos (point))
                (setq close (point-max)
                      delim-close nil
                      pos (point-max))
                ) ;if
              ) ;case
             ) ;cond
            ) ;case listp

           ((and (string= web-mode-engine "smarty")
                 (string= closing-string "}"))
            (goto-char open)
            (setq tmp (web-mode-closing-delimiter-position
                       "}"
                       (point)
                       (line-end-position)))
            (if tmp
                (setq tmp (1+ tmp))
              (setq tmp (line-end-position)))
            (goto-char tmp)
            (setq close (point)
                  pos (point))
            )

           ((and (member web-mode-engine '("closure"))
                 (string= closing-string "}"))
            (goto-char open)
            (setq tmp (web-mode-closing-paren-position (point) (line-end-position)))
            (if tmp
                (setq tmp (1+ tmp))
              (setq tmp (line-end-position)))
            (goto-char tmp)
            (setq close (point)
                  pos (point))
            )

           ((string= closing-string "EOL")
            (end-of-line)
            (setq close (point)
                  pos (point)))

           ((string= closing-string "EOC")
            (setq close (point)
                  pos (point)))

           ((string= closing-string "EOR")
            (web-mode-razor-skip open)
            (setq close (if (> (point) reg-end) reg-end (point))
                  pos (if (> (point) reg-end) reg-end (point)))
            (goto-char pos))

           ((string= closing-string "EOV")
            (web-mode-velocity-skip open)
            (setq close (point)
                  pos (point)))

           ((and (member web-mode-engine '("ctemplate"))
                 (re-search-forward closing-string reg-end t))
            (setq close (match-end 0)
                  pos (point)))

           ((search-forward closing-string reg-end t)
            (setq close (match-end 0)
                  pos (point)))
           ) ;cond

          (when (and close (>= reg-end pos))
            ;;(message "pos(%S) : open(%S) close(%S)" pos open close)
            (put-text-property open (1+ open) 'block-beg 0)
            (put-text-property open (1+ open) 'block-controls 0)
            (put-text-property open close 'block-side t)
            (put-text-property (1- close) close 'block-end t)
            (when delim-open
              (web-mode-block-delimiters-set open close delim-open delim-close))
            (web-mode-block-scan open close)
            (cond
             ((and (string= web-mode-engine "erb")
                   (looking-at-p "<%= javascript_tag do %>"))
              (setq tagopen "<%= javascript_tag do %>"))
             ((and (string= web-mode-engine "mako")
                   (looking-at-p "<%block filter=\"collect_js\">"))
              (setq tagopen "<%block filter=\"collect_js\">"))
             ((and (string= web-mode-engine "mako")
                   (looking-at-p "<%block filter=\"collect_css\">"))
              (setq tagopen "<%block filter=\"collect_css\">"))
             )
            ;;(message "%S %s" (point) tagopen)
            (when (and (member tagopen '("<r:script" "<r:style"
                                         "<c:js" "<c:css"
                                         "<%= javascript_tag do %>"
                                         "<%block filter=\"collect_js\">"
                                         "<%block filter=\"collect_css\">"))
                       (setq part-beg close)
                       (setq tagclose
                             (cond
                              ((string= tagopen "<r:script") "</r:script")
                              ((string= tagopen "<r:style") "</r:style")
                              ((string= tagopen "<c:js") "</c:js")
                              ((string= tagopen "<c:css") "</c:css")
                              ((string= tagopen "<%= javascript_tag do %>") "<% end %>")
                              ((member tagopen '("<%block filter=\"collect_js\">"
                                                 "<%block filter=\"collect_css\">")) "</%block")
                              ))
                       (web-mode-sf tagclose)
                       (setq part-end (match-beginning 0))
                       (> part-end part-beg))
              (put-text-property part-beg part-end
                                 'part-side
                                 (cond
                                  ((member tagopen '("<r:style" "<c:css" "<%block filter=\"collect_css\">")) 'css)
                                  (t 'javascript)))
              (setq pos part-beg
                    part-beg nil
                    part-end nil)
              ) ;when
            ) ;when close

          (if pos (goto-char pos))

          ) ;when closing-string

        ) ;while

      (cond
       ((>= i 2000)
        (message "scan-blocks ** warning (%S) **" i))
       ((string= web-mode-engine "razor")
        (web-mode-process-blocks reg-beg reg-end 'web-mode-block-scan))
       ((string= web-mode-engine "django")
        (web-mode-scan-engine-comments reg-beg reg-end
                                       "{% comment %}" "{% endcomment %}"))
       ((string= web-mode-engine "mako")
        (web-mode-scan-engine-comments reg-beg reg-end
                                       "<%doc>" "</%doc>"))
       ((string= web-mode-engine "mason")
        (web-mode-scan-engine-comments reg-beg reg-end
                                       "<%doc>" "</%doc>"))
       ) ;cond

      )))

(defun web-mode-block-delimiters-set (reg-beg reg-end delim-open delim-close)
  "Set text-property 'block-token to 'delimiter-(beg|end) on block delimiters (e.g. <?php ?>)"
  ;;(message "reg-beg(%S) reg-end(%S) delim-open(%S) delim-close(%S)" reg-beg reg-end delim-open delim-close)
  (when (member web-mode-engine
                '("asp" "aspx" "cl-emb" "clip" "closure" "ctemplate" "django" "dust"
                  "elixir" "ejs" "erb" "freemarker" "jsp" "lsp" "mako" "mason" "mojolicious"
                  "smarty" "template-toolkit" "web2py"))
    (save-excursion
      (when delim-open
        (goto-char reg-beg)
        (looking-at delim-open)
        (setq delim-open (match-string-no-properties 0)))
      (when delim-close
        (goto-char reg-end)
        (looking-back delim-close reg-beg t)
        (setq delim-close (match-string-no-properties 0)))
      ))
  (when delim-open
    (put-text-property reg-beg (+ reg-beg (length delim-open))
                       'block-token 'delimiter-beg))
  (when delim-close
    (put-text-property (- reg-end (length delim-close)) reg-end
                       'block-token 'delimiter-end))
  )

(defun web-mode-process-blocks (reg-beg reg-end func)
  (let ((i 0) (continue t) (block-beg reg-beg) (block-end nil))
    (while continue
      (setq block-end nil)
      (unless (get-text-property block-beg 'block-beg)
        (setq block-beg (web-mode-block-next-position block-beg)))
      (when (and block-beg (< block-beg reg-end))
        (setq block-end (web-mode-block-end-position block-beg)))
      (cond
       ((> (setq i (1+ i)) 2000)
        (message "process-blocks ** warning (%S) **" (point))
        (setq continue nil))
       ((or (null block-end) (> block-end reg-end))
        (setq continue nil))
       (t
        (setq block-end (1+ block-end))
        (funcall func block-beg block-end)
        (setq block-beg block-end)
        ) ;t
       ) ;cond
      ) ;while
    ))

(defun web-mode-process-parts (reg-beg reg-end func)
  (let ((i 0) (continue t) (part-beg reg-beg) (part-end nil))
    (while continue
      (setq part-end nil)
      (unless (get-text-property part-beg 'part-side)
        (setq part-beg (web-mode-part-next-position part-beg)))
      (when (and part-beg (< part-beg reg-end))
        (setq part-end (web-mode-part-end-position part-beg)))
      (cond
       ((> (setq i (1+ i)) 100)
        (message "process-parts ** warning (%S) **" (point))
        (setq continue nil))
       ((or (null part-end) (> part-end reg-end))
        (setq continue nil))
       (t
        (setq part-end (1+ part-end))
        (funcall func part-beg part-end)
        (setq part-beg part-end)
        )
       ) ;cond
      ) ;while
    ))

(defun web-mode-block-scan (block-beg block-end)
  (let (sub1 sub2 sub3 regexp token-type)

    ;;(message "block-beg=%S block-end=%S" block-beg block-end)
    ;;(remove-text-properties block-beg block-end web-mode-scan-properties)

    (goto-char block-beg)

    (cond
     ((>= (point-max) (+ block-beg 3))
      (setq sub3 (buffer-substring-no-properties block-beg (+ block-beg 3))
            sub2 (buffer-substring-no-properties block-beg (+ block-beg 2))
            sub1 (buffer-substring-no-properties block-beg (+ block-beg 1)))
      )
     ((>= (point-max) (+ block-beg 2))
      (setq sub3 (buffer-substring-no-properties block-beg (+ block-beg 2))
            sub2 (buffer-substring-no-properties block-beg (+ block-beg 2))
            sub1 (buffer-substring-no-properties block-beg (+ block-beg 1)))
      )
     (t
      (setq sub1 (buffer-substring-no-properties block-beg (+ block-beg 1)))
      (setq sub2 sub1
            sub3 sub1)
      )
     )

    (cond

     ((member web-mode-engine '("php" "lsp" "python" "web2py" "mason"))
      (setq regexp web-mode-engine-token-regexp))

     ((string= web-mode-engine "mako")
      (cond
       ((string= sub2 "##")
        (setq token-type 'comment)
        )
       (t
        (setq regexp web-mode-engine-token-regexp))
       )
      ) ;mako

     ((string= web-mode-engine "django")
      (cond
       ((member sub2 '("{{" "{%"))
        (setq regexp "\"\\|'"))
       ((string= sub2 "{#")
        (setq token-type 'comment))
       )
      ) ;django

     ((string= web-mode-engine "ctemplate")
      (cond
       ((string= sub3 "{{!")
        (setq token-type 'comment))
       ((member sub2 '("{{"))
        )
       )
      ) ;ctemplate

     ((string= web-mode-engine "go")
      (cond
       ((string= sub3 "{{/")
        (setq token-type 'comment))
       ((string= sub2 "{{")
        (setq regexp "\"\\|'"))
       )
      ) ;go

     ((string= web-mode-engine "razor")
      (cond
       ((string= sub2 "@*")
        (setq token-type 'comment))
       (t
        (setq regexp "//\\|@\\*\\|\"\\|'"))
       )
      ) ;razor

     ((string= web-mode-engine "blade")
      (cond
       ((string= sub3 "{{-")
        (setq token-type 'comment))
       (t
        (setq regexp "\"\\|'"))
       )
      ) ;blade

     ((string= web-mode-engine "cl-emb")
      (cond
       ((string= sub3 "<%#")
        (setq token-type 'comment))
       (t
        (setq regexp "\"\\|'"))
       )
      ) ;cl-emb

     ((string= web-mode-engine "elixir")
      (cond
       ((string= sub3 "<%#")
        (setq token-type 'comment))
       (t
        (setq regexp "\"\\|'"))
       )
      ) ;elixir

     ((string= web-mode-engine "mojolicious")
      (cond
       ((or (string= sub2 "%#") (string= sub3 "<%#"))
        (setq token-type 'comment))
       (t
        (setq regexp "\"\\|'"))
       )
      ) ;mojolicious

     ((string= web-mode-engine "velocity")
      (cond
       ((member sub2 '("##" "#*"))
        (setq token-type 'comment))
       ((member sub1 '("$" "#"))
        (setq regexp "\"\\|'"))
       )
      ) ;velocity

     ((string= web-mode-engine "jsp")
      (cond
       ((string= sub3 "<%-")
        (setq token-type 'comment))
       ((string= sub3 "<%@")
        (setq regexp "/\\*"))
       ((member sub2 '("${" "#{"))
        (setq regexp "\"\\|'"))
       ((string= sub2 "<%")
        (setq regexp "//\\|/\\*\\|\"\\|'"))
       )
      ) ;jsp

     ((string= web-mode-engine "clip")
      (setq regexp nil)
      ) ;clip

     ((and (string= web-mode-engine "asp")
           (string= sub2 "<%"))
      (setq regexp "//\\|/\\*\\|\"\\|'")
      ) ;asp

     ((string= web-mode-engine "aspx")
      (cond
       ((string= sub3 "<%-")
        (setq token-type 'comment))
       ((string= sub3 "<%@")
        (setq regexp "/\\*"))
       ((string= sub3 "<%$")
        (setq regexp "\"\\|'"))
       (t
        (setq regexp "//\\|/\\*\\|\"\\|'"))
       )
      ) ;aspx

     ((string= web-mode-engine "freemarker")
      (cond
       ((member sub3 '("<#-" "[#-"))
        (setq token-type 'comment))
       ((member sub2 '("${" "#{"))
        (setq regexp "\"\\|'"))
       ((or (member sub2 '("<@" "[@" "<#" "[#"))
            (member sub3 '("</@" "[/@" "</#" "[/#")))
        (setq regexp "\"\\|'"))
       )
      ) ;freemarker

     ((member web-mode-engine '("ejs" "erb"))
      (cond
       ((string= sub3 "<%#")
        (setq token-type 'comment))
       (t
        (setq regexp web-mode-engine-token-regexp))
       )
      ) ;erb

     ((string= web-mode-engine "template-toolkit")
      (cond
       ((member sub3 '("[%#" "%%#"))
        (setq token-type 'comment))
       (t
        (setq regexp "#\\|\"\\|'"))
       )
      ) ;template-toolkit

     ((string= web-mode-engine "underscore")
      (setq regexp "/\\*\\|\"\\|'")
      ) ;underscore

     ((string= web-mode-engine "angular")
      ) ;angular

     ((string= web-mode-engine "smarty")
      (cond
       ((string= sub2 "{*")
        (setq token-type 'comment))
       (t
        (setq regexp "\"\\|'")))
      ) ;smarty

     ((string= web-mode-engine "dust")
      (cond
       ((string= sub2 "{!")
        (setq token-type 'comment))
       (t
        (setq regexp "\"\\|'"))
       )
      ) ;dust

     ((string= web-mode-engine "closure")
      (cond
       ((member sub2 '("/*" "//"))
        (setq token-type 'comment))
       (t
        (setq regexp "\"\\|'"))
       )
      ) ;closure

     ) ;cond

    (cond
     (token-type
      (put-text-property block-beg block-end 'block-token token-type))
     ((and regexp
           (> (- block-end block-beg) 6))
      (web-mode-block-tokenize
       (web-mode-block-code-beginning-position block-beg)
       (web-mode-block-code-end-position block-beg)
       regexp)
      )
     ) ;cond

    ))

(defun web-mode-block-tokenize (reg-beg reg-end &optional regexp)
  (unless regexp (setq regexp web-mode-engine-token-regexp))
  ;;(message "tokenize: reg-beg(%S) reg-end(%S) regexp(%S)" reg-beg reg-end regexp)
  ;;(message "tokenize: reg-beg(%S) reg-end(%S) command(%S)" reg-beg reg-end this-command)
  ;;(message "%S>%S : %S" reg-beg reg-end (buffer-substring-no-properties reg-beg reg-end))
  (save-excursion
    (let ((pos reg-beg) beg end char match continue (flags 0) token-type token-end)

      (remove-list-of-text-properties reg-beg reg-end '(block-token))

      ;; TODO : vérifier la cohérence
      (put-text-property reg-beg reg-end 'block-side t)

      (goto-char reg-beg)

      (when (> reg-beg reg-end)
        (message "block-tokenize ** reg-beg(%S) reg-end(%S) **" reg-beg reg-end))

      (while (and (< reg-beg reg-end) (re-search-forward regexp reg-end t))
        (setq beg (match-beginning 0)
              match (match-string 0)
              continue t
              token-type 'comment
              token-end (if (< reg-end (line-end-position)) reg-end (line-end-position))
              char (aref match 0))
        (cond

         ((and (string= web-mode-engine "asp")
               (eq char ?\'))
          (goto-char token-end))

         ((eq char ?\')
          (setq token-type 'string)
          (while (and continue (search-forward "'" reg-end t))
            (if (looking-back "\\\\+'" reg-beg t)
                (setq continue (= (mod (- (point) (match-beginning 0)) 2) 0))
              (setq continue nil))))

         ((eq char ?\")
          (setq token-type 'string)
          (while (and continue (search-forward "\"" reg-end t))
            (if (looking-back "\\\\+\"" reg-beg t)
                (setq continue (= (mod (- (point) (match-beginning 0)) 2) 0))
              (setq continue nil))))

         ((string= match "//")
          (goto-char token-end))

         ((eq char ?\;)
          (goto-char token-end))

         ((string= match "#|")
          (unless (search-forward "|#" reg-end t)
            (goto-char token-end)))

         ((eq char ?\#)
          (goto-char token-end))

         ((string= match "/*")
          (unless (search-forward "*/" reg-end t)
            (goto-char token-end))
          )

         ((string= match "@*")
          (unless (search-forward "*@" reg-end t)
            (goto-char token-end)))

         ((eq char ?\<)
          (setq token-type 'string)
          (re-search-forward (concat "^[ ]*" (match-string 1)) reg-end t))

         (t
          (message "block-tokenize ** token end (%S) **" beg)
          (setq token-type nil))

         ) ;cond

        ;;(when (eq token-type 'comment) (message "comment: %S %S" beg (point)))

        (put-text-property beg (point) 'block-token token-type)

        (when (eq token-type 'comment)
          (put-text-property beg (1+ beg) 'syntax-table (string-to-syntax "<"))
          (if (or (< (point) (line-end-position)) (= (point) (point-max)))
              (put-text-property (1- (point)) (point) 'syntax-table (string-to-syntax ">")) ;#445 #480
            (put-text-property (point) (1+ (point)) 'syntax-table (string-to-syntax ">")) ;#377
            )
          )

        ) ;while

      (web-mode-block-controls-unset pos)

      )))

(defun web-mode-set-php-controls (reg-beg reg-end)
  (goto-char reg-beg)
  (let (match controls
        (continue t)
        (regexp "endif\\|endforeach\\|endfor\\|endwhile\\|elseif\\|else\\|if\\|foreach\\|for\\|while"))
    (while continue
      (if (not (web-mode-block-rsf regexp reg-end))
          (setq continue nil)
        (setq match (match-string-no-properties 0))
;;        (message "%S %S" match (point))
        (cond
         ((and (member match '("else" "elseif"))
               (looking-at-p "[ ]*[:(]"))
          (setq controls (append controls (list (cons 'inside "if"))))
          )
         ((and (>= (length match) 3)
               (string= (substring match 0 3) "end"))
          (setq controls (append controls (list (cons 'close (substring match 3)))))
          )
         ((and (progn (skip-chars-forward "[ ]") t)
               (eq (char-after) ?\()
               (web-mode-closing-paren reg-end)
               ;;(progn (message "ixi%S" (point)))
               (looking-at-p ")[ ]*:"))
          (setq controls (append controls (list (cons 'open match))))
          )
         ) ;cond
        ) ;if
      ) ;while
    ;;(message "%S-%S %S" reg-beg reg-end controls)
    (when (and controls (> (length controls) 1))
      (setq controls (web-mode-block-controls-reduce controls)))
    controls))

(defun web-mode-block-controls-reduce (controls)
  (when (and (eq (car (car controls)) 'open)
             (member (cons 'close (cdr (car controls))) controls))
    (setq controls nil))
  controls)

(defun web-mode-block-controls-unset (pos)
  (cond
   ((null (get-text-property pos 'block-side))
    (message "block-controls-unset ** invalid value (%S) **" pos))
   ((or (get-text-property pos 'block-beg)
        (setq pos (web-mode-block-beginning-position pos)))
    (put-text-property pos (1+ pos) 'block-controls 0))
   (t
    (message "block-controls-unset ** failure (%S) **" (point)))
   ))

(defun web-mode-block-controls-get (pos)
  (web-mode-with-silent-modifications
   (let ((controls nil))
     (cond
      ((null (get-text-property pos 'block-side))
       (message "block-controls-get ** invalid value (%S) **" pos))
      ((or (get-text-property pos 'block-beg)
           (setq pos (web-mode-block-beginning-position pos)))
       (setq controls (get-text-property pos 'block-controls))
       (when (integerp controls)
         (web-mode-block-controls-set pos (web-mode-block-end-position pos))
         (setq controls (get-text-property pos 'block-controls))
         )
       )
      (t
       (message "block-controls-get ** failure (%S) **" (point)))
      ) ;cond
     controls)))

(defun web-mode-block-controls-set (reg-beg reg-end)
  (save-excursion
    (goto-char reg-beg)
    (let (controls pos type control)

      (cond

       ((null web-mode-engine)
        (message "block-controls-set ** unknown engine (%S) **" web-mode-engine)
        )

       ((string= web-mode-engine "php")
        (setq controls (web-mode-set-php-controls reg-beg reg-end))
        (when (web-mode-block-starts-with "}" reg-beg)
          (setq controls (append controls (list (cons 'close "{")))))
        (when (web-mode-block-ends-with (cons "{" "}") reg-beg)
          (setq controls (append controls (list (cons 'open "{")))))
        ) ;php

       ((string= web-mode-engine "ejs")
        (cond
         ((web-mode-block-ends-with "}[ ]*else[ ]*{" reg-beg)
          (setq controls (append controls (list (cons 'inside "{")))))
         ((web-mode-block-starts-with "}" reg-beg)
          (setq controls (append controls (list (cons 'close "{")))))
         ((web-mode-block-ends-with "{" reg-beg)
          (setq controls (append controls (list (cons 'open "{")))))
         )
        ) ;ejs

       ((string= web-mode-engine "erb")
        (cond
         ((web-mode-block-starts-with "else\\|elsif\\|when" reg-beg)
          (setq controls (append controls (list (cons 'inside "ctrl")))))
         ((web-mode-block-starts-with "end" reg-beg)
          (setq controls (append controls (list (cons 'close "ctrl")))))
         ((web-mode-block-ends-with " do\\( |.*|\\)?" reg-beg)
          (setq controls (append controls (list (cons 'open "ctrl")))))
         ((and (web-mode-block-starts-with "\\(for\\|if\\|unless\\|case\\)\\_>" reg-beg)
               (not (web-mode-block-ends-with "end" reg-end)))
          (setq controls (append controls (list (cons 'open "ctrl")))))
         )
        ) ;erb

       ((string= web-mode-engine "django")
        (when (eq (char-after (1+ reg-beg)) ?\%)
          (cond
           ((and (string= web-mode-minor-engine "jinja") ;#504
                 (web-mode-block-starts-with "else\\_>" reg-beg))
            (let ((continue t)
                  (pos reg-beg)
                  (ctrl nil))
              (while continue
                (cond
                 ((null (setq pos (web-mode-block-control-previous-position 'open pos)))
                  (setq continue nil))
                 ((member (setq ctrl (cdr (car (get-text-property pos 'block-controls)))) '("if" "ifequal" "ifnotequal" "for"))
                  (setq continue nil)
                  )
                 ) ;cond
                )
              (setq controls (append controls (list (cons 'inside (or ctrl "if")))))
              )
            )
           ((web-mode-block-starts-with "\\(else\\|els?if\\)" reg-beg)
            (let ((continue t)
                  (pos reg-beg)
                  (ctrl nil))
              (while continue
                (cond
                 ((null (setq pos (web-mode-block-control-previous-position 'open pos)))
                  (setq continue nil))
                 ((member (setq ctrl (cdr (car (get-text-property pos 'block-controls)))) '("if" "ifequal" "ifnotequal"))
                  (setq continue nil)
                  )
                 ) ;cond
                ) ;while
              (setq controls (append controls (list (cons 'inside (or ctrl "if")))))
              ) ;let
            ) ;case else
           ((web-mode-block-starts-with "\\(empty\\)" reg-beg)
            (setq controls (append controls (list (cons 'inside "for")))))
           ((web-mode-block-starts-with "end\\([[:alpha:]]+\\)" reg-beg)
            (setq controls (append controls (list (cons 'close (match-string-no-properties 1))))))
           ((web-mode-block-starts-with (concat web-mode-django-control-blocks-regexp "[ %]") reg-beg)
            (let (control)
              (setq control (match-string-no-properties 1))
              ;;(message "%S %S %S" control (concat "end" control) web-mode-django-control-blocks)
              (when (member (concat "end" control) web-mode-django-control-blocks)
                (setq controls (append controls (list (cons 'open control)))))
              ) ;let
            ) ;case
           ) ;cond
          ) ;when
        ) ;django

       ((string= web-mode-engine "smarty")
        (cond
         ((and (eq (char-after (1+ reg-beg)) ?\/)
               (web-mode-block-starts-with "\\([[:alpha:]]+\\)" reg-beg))
          (setq controls (append controls (list (cons 'close (match-string-no-properties 1))))))
         ((web-mode-block-starts-with "\\(else\\|elseif\\)" reg-beg)
          (setq controls (append controls (list (cons 'inside "if")))))
         ((web-mode-block-starts-with "\\(block\\|foreach\\|for\\|if\\|section\\|while\\)")
          (setq controls (append controls (list (cons 'open (match-string-no-properties 1))))))
         )
        ) ;smarty

       ((string= web-mode-engine "web2py")
        (cond
         ((web-mode-block-starts-with "def" reg-beg)
          (setq controls (append controls (list (cons 'open "def")))))
         ((web-mode-block-starts-with "return" reg-beg)
          (setq controls (append controls (list (cons 'close "def")))))
         ((web-mode-block-starts-with "block" reg-beg)
          (setq controls (append controls (list (cons 'open "block")))))
         ((web-mode-block-starts-with "end" reg-beg)
          (setq controls (append controls (list (cons 'close "block")))))
         ((web-mode-block-starts-with "pass" reg-beg)
          (setq controls (append controls (list (cons 'close "ctrl")))))
         ((web-mode-block-starts-with "\\(except\\|finally\\|els\\)" reg-beg)
          (setq controls (append controls (list (cons 'inside "ctrl")))))
         ((web-mode-block-starts-with "\\(if\\|for\\|try\\|while\\)")
          (setq controls (append controls (list (cons 'open "ctrl")))))
         )
        ) ;web2py

       ((string= web-mode-engine "dust")
        (cond
         ((eq (char-after (1- reg-end)) ?\/)
          )
         ((eq (char-after (1+ reg-beg)) ?\:)
          (setq pos (web-mode-block-control-previous-position 'open reg-beg))
          (when pos
            (setq controls (append controls
                                   (list
                                    (cons 'inside
                                          (cdr (car (web-mode-block-controls-get pos))))))))
          )
         ((looking-at "{/\\([[:alpha:].]+\\)")
          (setq controls (append controls (list (cons 'close (match-string-no-properties 1))))))
         ((looking-at "{[#?@><+^]\\([[:alpha:].]+\\)")
          (setq controls (append controls (list (cons 'open (match-string-no-properties 1))))))
         )
        ) ;dust

       ((member web-mode-engine '("mojolicious"))
        (cond
         ((web-mode-block-ends-with "begin" reg-beg)
          (setq controls (append controls (list (cons 'open "begin")))))
         ((web-mode-block-starts-with "end" reg-beg)
          (setq controls (append controls (list (cons 'close "begin")))))
         ((web-mode-block-starts-with "}[ ]*else[ ]*{" reg-beg)
          (setq controls (append controls (list (cons 'inside "{")))))
         ((web-mode-block-starts-with "}" reg-beg)
          (setq controls (append controls (list (cons 'close "{")))))
         ((web-mode-block-ends-with "{" reg-beg)
          (setq controls (append controls (list (cons 'open "{")))))
         )
        ) ;mojolicious

       ((member web-mode-engine '("aspx" "underscore"))
        (cond
         ((web-mode-block-starts-with "}" reg-beg)
          (setq controls (append controls (list (cons 'close "{")))))
         ((web-mode-block-ends-with "{" reg-beg)
          (setq controls (append controls (list (cons 'open "{")))))
         )
        ) ;aspx underscore

       ((member web-mode-engine '("jsp" "asp" "clip"))
        (cond
         ((eq (char-after (1- reg-end)) ?\/)
          )
         ((looking-at "</?\\([[:alpha:]]+\\(?:[:.][[:alpha:]]+\\)\\|[[:alpha:]]+Template\\)")
          (setq control (match-string-no-properties 1)
                type (if (eq (aref (match-string-no-properties 0) 1) ?\/) 'close 'open))
          (when (not (member control '("h:inputtext" "jsp:usebean" "jsp:forward" "struts:property")))
            (setq controls (append controls (list (cons type control)))))
          )
         (t
          (when (web-mode-block-starts-with "}" reg-beg)
            (setq controls (append controls (list (cons 'close "{")))))
          (when (web-mode-block-ends-with "{" reg-beg)
            (setq controls (append controls (list (cons 'open "{")))))
          )
         )
        ) ;jsp asp

       ((string= web-mode-engine "mako")
        (cond
         ((looking-at "</?%\\([[:alpha:]]+\\(?:[:][[:alpha:]]+\\)?\\)")
          (cond
           ((eq (char-after (- (web-mode-block-end-position reg-beg) 1)) ?\/)
            )
           (t
            (setq control (match-string-no-properties 1)
                  type (if (eq (aref (match-string-no-properties 0) 1) ?\/) 'close 'open))
            (setq controls (append controls (list (cons type control)))))
           )
          )
         ((web-mode-block-starts-with "\\(else\\|elif\\)" reg-beg)
          (setq controls (append controls (list (cons 'inside "if")))))
         ((web-mode-block-starts-with "end\\(if\\|for\\)" reg-beg)
          (setq controls (append controls (list (cons 'close (match-string-no-properties 1))))))
         ((and (web-mode-block-starts-with "if\\|for" reg-beg)
               (web-mode-block-ends-with ":" reg-beg))
          (setq controls (append controls (list (cons 'open (match-string-no-properties 0))))))
         )
        ) ;mako

       ((string= web-mode-engine "mason")
        (cond
         ((looking-at "</?%\\(after\\|around\\|augment\\|before\\|def\\|filter\\|method\\|override\\)")
          (setq control (match-string-no-properties 1)
                type (if (eq (aref (match-string-no-properties 0) 1) ?\/) 'close 'open))
          (setq controls (append controls (list (cons type control))))
          )
         ) ;mason
        )

       ((string= web-mode-engine "ctemplate")
        (cond
         ((looking-at-p "{{else") ;#721
          (let ((continue t)
                (pos reg-beg)
                (ctrl nil))
            (while continue
              (cond
               ((null (setq pos (web-mode-block-control-previous-position 'open pos)))
                (setq continue nil))
               ((member (setq ctrl (cdr (car (get-text-property pos 'block-controls)))) '("if" "each"))
                (setq continue nil)
                )
               ) ;cond
              ) ;while
            (setq controls (append controls (list (cons 'inside (or ctrl "if")))))
            )
          ;;(setq controls (append controls (list (cons 'inside "if"))))
          )

         ((looking-at "{{[#^/][ ]*\\([[:alpha:]-]+\\)")
          (setq control (match-string-no-properties 1)
                type (if (eq (aref (match-string-no-properties 0) 2) ?\/) 'close 'open))
          (setq controls (append controls (list (cons type control))))
          )
         )
        ) ;ctemplate

       ((string= web-mode-engine "blade")
        (cond
         ((not (eq (char-after) ?\@))
          )
         ((web-mode-block-starts-with
           "section\(\s*\\(['\"]\\).*\\1\s*,\s*\\(['\"]\\).*\\2\s*\)" reg-beg)
          )
         ((web-mode-block-starts-with
           "\\(?:end\\)?\\(foreach\\|forelse\\|for\\|if\\|section\\|unless\\|while\\)"
           reg-beg)
          (setq control (match-string-no-properties 1)
                type (if (eq (aref (match-string-no-properties 0) 0) ?e) 'close 'open))
          (setq controls (append controls (list (cons type control))))
          )
         ((web-mode-block-starts-with "stop\\|show\\|overwrite" reg-beg)
          (setq controls (append controls (list (cons 'close "section")))))
         ((web-mode-block-starts-with "else\\|elseif" reg-beg)
          (setq controls (append controls (list (cons 'inside "if")))))
         ((web-mode-block-starts-with "empty" reg-beg)
          (setq controls (append controls (list (cons 'inside "forelse")))))
         )
        ) ;blade

       ((string= web-mode-engine "closure")
        (cond
         ((eq (char-after (1- reg-end)) ?\/)
          )
         ((looking-at "alias\\|namespace")
          )
         ((web-mode-block-starts-with "ifempty" reg-beg)
          (setq controls (append controls (list (cons 'inside "foreach")))))
         ((web-mode-block-starts-with "else\\|elseif" reg-beg)
          (setq controls (append controls (list (cons 'inside "if")))))
         ((web-mode-block-starts-with "case\\|default" reg-beg)
          (setq controls (append controls (list (cons 'inside "switch")))))
         ((looking-at
           "{/?\\(call\\|deltemplate\\|for\\|foreach\\|if\\|let\\|literal\\|msg\\|param\\|switch\\|template\\)")
          (setq control (match-string-no-properties 1)
                type (if (eq (aref (match-string-no-properties 0) 1) ?\/) 'close 'open))
          (setq controls (append controls (list (cons type control))))
          )
         )
        ) ;closure

       ((string= web-mode-engine "go")
        (cond
         ((web-mode-block-starts-with "end\\_>" reg-beg)
          (setq controls (append controls (list (cons 'close "ctrl")))))
         ((web-mode-block-starts-with "else\\_>" reg-beg)
          (setq controls (append controls (list (cons 'inside "ctrl")))))
         ((web-mode-block-starts-with "\\(range\\|with\\|if\\)\\_>" reg-beg)
          (setq controls (append controls (list (cons 'open "ctrl")))))
         )
        ) ;go

       ((string= web-mode-engine "template-toolkit")
        (cond
         ((web-mode-block-starts-with "end" reg-beg)
          (setq controls (append controls (list (cons 'close "ctrl")))))
         ((web-mode-block-starts-with "els\\|catch\\|final" reg-beg)
          (setq controls (append controls (list (cons 'inside "ctrl")))))
         ((web-mode-block-starts-with "filter\\|foreach\\|if\\|last\\|next\\|perl\\|rawperl\\|try\\|unless\\|while" reg-beg)
          (setq controls (append controls (list (cons 'open "ctrl")))))
         )
        ) ;template-toolkit

       ((string= web-mode-engine "cl-emb")
        (cond
         ((web-mode-block-starts-with "@else" reg-beg)
          (setq controls (append controls (list (cons 'inside "if")))))
         ((web-mode-block-starts-with "@\\(?:end\\)?\\(if\\|unless\\|repeat\\|loop\\|with\\|genloop\\)" reg-beg)
          (setq control (match-string-no-properties 1)
                type (if (eq (aref (match-string-no-properties 0) 1) ?e) 'close 'open))
          (setq controls (append controls (list (cons type control)))))
         )
        ) ;cl-emb

       ((string= web-mode-engine "elixir")
        (cond
         ((web-mode-block-starts-with "end" reg-beg)
          (setq controls (append controls (list (cons 'close "ctrl")))))
         ((web-mode-block-starts-with "else" reg-beg)
          (setq controls (append controls (list (cons 'inside "ctrl")))))
         ((web-mode-block-ends-with " do" reg-beg)
          (setq controls (append controls (list (cons 'open "ctrl")))))
         )
        ) ;elixir

       ((string= web-mode-engine "velocity")
        (cond
         ((web-mode-block-starts-with "{?end" reg-beg)
          (setq controls (append controls (list (cons 'close "ctrl")))))
         ((web-mode-block-starts-with "{?els" reg-beg)
          (setq controls (append controls (list (cons 'inside "ctrl")))))
         ((web-mode-block-starts-with "{?\\(define\\|if\\|for\\|foreach\\|macro\\)" reg-beg)
          (setq controls (append controls (list (cons 'open "ctrl")))))
         )
        ) ;velocity

       ((string= web-mode-engine "freemarker")
        (cond
         ((looking-at "<#\\(import\\|assign\\|return\\|local\\)")
          )
         ((eq (char-after (1- reg-end)) ?\/)
          )
         ((looking-at "[<[]#\\(break\\|case\\|default\\)")
          (setq controls (append controls (list (cons 'inside "switch"))))
          )
         ((looking-at "[<[]#els")
          (setq controls (append controls (list (cons 'inside "if"))))
          )
         ((looking-at "</?\\([[:alpha:]]+\\(?:[:][[:alpha:]]+\\)?\\)")
          (setq control (match-string-no-properties 1)
                type (if (eq (aref (match-string-no-properties 0) 1) ?\/) 'close 'open))
          (setq controls (append controls (list (cons type control))))
          )
         ((looking-at "</?\\(@\\)")
          (setq control (match-string-no-properties 1)
                type (if (eq (aref (match-string-no-properties 0) 1) ?\/) 'close 'open))
          (setq controls (append controls (list (cons type control))))
          )
         ((looking-at "[<[]/?#\\([[:alpha:]]+\\(?:[:][[:alpha:]]+\\)?\\)")
          (setq control (match-string-no-properties 1)
                type (if (eq (aref (match-string-no-properties 0) 1) ?\/) 'close 'open))
          (setq controls (append controls (list (cons type control))))
          )
         (t
          (when (web-mode-block-starts-with "}" reg-beg)
            (setq controls (append controls (list (cons 'close "{")))))
          (when (web-mode-block-ends-with "{" reg-beg)
            (setq controls (append controls (list (cons 'open "{")))))
          )
         )
        ) ;freemarker

       ((string= web-mode-engine "razor")
        (when (web-mode-block-starts-with "}" reg-beg)
          (setq controls (append controls (list (cons 'close "{")))))
        (when (web-mode-block-ends-with "{" reg-beg)
          (setq controls (append controls (list (cons 'open "{")))))
        ) ;razor

       ((string= web-mode-engine "lsp")
        (when (web-mode-block-starts-with ")" reg-beg)
          (setq controls (append controls (list (cons 'close "(")))))
        (when (web-mode-block-is-opened-sexp reg-beg reg-end)
          (setq controls (append controls (list (cons 'open "(")))))
        ) ;lsp

       ) ;cond engine

      (put-text-property reg-beg (1+ reg-beg) 'block-controls controls)
      ;;      (message "(%S) controls=%S" reg-beg controls)

      )))

(defun web-mode-block-is-opened-sexp (reg-beg reg-end)
  (let ((n 0))
    (save-excursion
      (goto-char reg-beg)
      (while (web-mode-block-rsf "[()]" reg-end)
        (if (eq (char-before) ?\() (setq n (1+ n)) (setq n (1- n)))))
    (> n 0)))

(defvar web-mode-regexp1 "<\\(/?[[:alpha:]][[:alnum:]:-]*\\|!--\\|!\\[CDATA\\[\\|!doctype\\|!DOCTYPE\\|\?xml\\)")

(defvar web-mode-regexp2 "<\\(/?[[:alpha:]][[:alnum:]:-]*\\|!--\\|!\\[CDATA\\[\\)")

(defun web-mode-scan-elements (reg-beg reg-end)
  (save-excursion
    (let (part-beg part-end flags limit close-expr props tname tbeg tend element-content-type (regexp web-mode-regexp1) part-close-tag char)

      (goto-char reg-beg)

      (while (web-mode-dom-rsf regexp reg-end)

        (setq flags 0
              tname (downcase (match-string-no-properties 1))
              char (aref tname 0)
              tbeg (match-beginning 0)
              tend nil
              element-content-type nil
              limit reg-end
              part-beg nil
              part-end nil
              props nil
              close-expr nil
              part-close-tag nil)

        (cond
         ((not (member char '(?\! ?\?)))
          (cond
           ((string-match-p "-" tname)
            (setq flags (logior flags 2)))
           ((string-match-p ":" tname)
            (setq flags (logior flags 32)))
           )
          (cond
           ((eq char ?\/)
            (setq props (list 'tag-name (substring tname 1) 'tag-type 'end)
                  flags (logior flags 4)
                  limit (if (> reg-end (line-end-position)) (line-end-position) reg-end))
            )
           ((web-mode-element-is-void tname)
            (setq props (list 'tag-name tname 'tag-type 'void)))
           (t
            (setq props (list 'tag-name tname 'tag-type 'start)))
           ) ;cond
          )
         ((and (eq char ?\!) (eq (aref tname 1) ?\-))
          (setq close-expr "-->"
                props '(tag-type comment)))
         ((string= tname "?xml")
          (setq regexp web-mode-regexp2
                close-expr "?>"
                props '(tag-type declaration)))
         ((string= tname "![cdata[")
          (setq close-expr "]]>"
                props '(tag-type cdata)))
         ((string= tname "!doctype")
          (setq regexp web-mode-regexp2
                props '(tag-type doctype)))
         ) ;cond

        (cond
         ((and (null close-expr) (eq (char-after) ?\>))
          (setq flags (logior flags 16)
                tend (1+ (point))))
         ((null close-expr)
          (setq flags (logior flags (web-mode-attr-skip reg-end)))
          (when (> (logand flags 8) 0)
            (setq props (plist-put props 'tag-type 'void)))
          (setq tend (point)))
         ((web-mode-dom-sf close-expr limit t)
          (setq tend (point)))
         (t
          (setq tend (line-end-position)))
         )

        (cond
         ((string= tname "style")
          (setq element-content-type "css"
                part-close-tag "</style>"))
         ((string= tname "script")
          (let (script)
            (setq script (buffer-substring-no-properties tbeg tend)
                  part-close-tag "</script>")
            (cond
             ((string-match-p " type[ ]*=[ ]*[\"']text/\\(jsx\\|babel\\)" script)
              (setq element-content-type "jsx"))
             ((string-match-p " type[ ]*=[ ]*[\"']text/\\(x-handlebars\\|x-jquery-tmpl\\|html\\|ng-template\\|template\\|mustache\\)" script)
              (setq element-content-type "html"
                    part-close-tag nil))
             ((string-match-p " type[ ]*=[ ]*[\"']application/\\(ld\\+json\\|json\\)" script)
              (setq element-content-type "json"))
             (t
              (setq element-content-type "javascript"))
             ) ;cond
            ) ;let
          ) ;script
         )

        (add-text-properties tbeg tend props)
        (put-text-property tbeg (1+ tbeg) 'tag-beg flags)
        (put-text-property (1- tend) tend 'tag-end t)

        (when (and part-close-tag
                   (web-mode-dom-sf part-close-tag reg-end t)
                   (setq part-beg tend)
                   (setq part-end (match-beginning 0))
                   (> part-end part-beg))
          (put-text-property part-beg part-end 'part-side
                             (intern element-content-type web-mode-obarray))
          (setq tend part-end)
          ) ;when

        (goto-char tend)

        ) ;while

      )))

;; tag flags
;; (1)attrs (2)custom (4)slash-beg (8)slash-end (16)bracket-end
;; (32)namespaced

;; attr flags
;; (1)custom-attr (2)engine-attr (4)spread-attr[jsx] (8)code-value

;; attr states
;; (0)nil (1)space (2)name (3)space-before (4)equal (5)space-after
;; (6)value-uq (7)value-sq (8)value-dq (9)value-bq : jsx attr={}

(defun web-mode-attr-skip (limit)

  (let ((tag-flags 0) (attr-flags 0) (continue t) (attrs 0) (counter 0) (brace-depth 0)
        (pos-ori (point)) (state 0) (equal-offset 0) (go-back nil)
        (is-jsx (or (string= web-mode-content-type "jsx") (eq (get-text-property (point) 'part-type) 'jsx)))
        attr name-beg name-end val-beg char pos escaped spaced quoted)

    (while continue

      (setq pos (point)
            char (char-after)
            spaced (eq char ?\s))

      (when quoted (setq quoted (1+ quoted)))

      (cond

       ((>= pos limit)
        (setq continue nil)
        (setq go-back t)
        (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset)))
        )

       ((or (and (= state 8) (not (member char '(?\" ?\\))))
            (and (= state 7) (not (member char '(?\' ?\\))))
            (and (= state 9) (not (member char '(?} ?\\))))
            )
        (when (and (= state 9) (eq char ?\{))
          (setq brace-depth (1+ brace-depth)))
        )

       ((and (= state 9) (eq char ?\}) (> brace-depth 1))
        (setq brace-depth (1- brace-depth)))

       ((get-text-property pos 'block-side)
        (when (= state 2)
          (setq name-end pos))
        )

       ((and (= state 2) is-jsx (eq char ?\}) (eq attr-flags 4))
        (setq name-end pos)
        (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset)))
        (setq state 0
              attr-flags 0
              equal-offset 0
              name-beg nil
              name-end nil
              val-beg nil)
        )

       ((or (and (= state 8) (eq ?\" char) (not escaped))
            (and (= state 7) (eq ?\' char) (not escaped))
            (and (= state 9) (eq ?\} char) (= brace-depth 1))
            )

        ;;(message "%S %S" (point) attr-flags)
        (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset)))
        (setq state 0
              attr-flags 0
              equal-offset 0
              name-beg nil
              name-end nil
              val-beg nil)
        )

       ((and (member state '(4 5)) (member char '(?\' ?\" ?\{)))
        (setq val-beg pos)
        (setq quoted 1)
        (setq state (cond ((eq ?\' char) 7)
                          ((eq ?\" char) 8)
                          (t             9)))
        (when (= state 9)
          (setq brace-depth 1))
        )

       ((and (eq ?\= char) (member state '(2 3)))
        (setq equal-offset (- pos name-beg))
        (setq state 4)
        (setq attr (buffer-substring-no-properties name-beg (1+ name-end)))
        (when (and web-mode-indentless-attributes (member (downcase attr) web-mode-indentless-attributes))
          ;;(message "onclick")
          (setq attr-flags (logior attr-flags 8)))
        )

       ((and spaced (= state 0))
        (setq state 1)
        )

       ((and (eq char ?\<) (not (member state '(7 8 9))))
        (setq continue nil)
        (setq go-back t)
        (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset)))
        )

       ((and (eq char ?\>) (not (member state '(7 8 9))))
        (setq tag-flags (logior tag-flags 16))
        (when (eq (char-before) ?\/)
          (setq tag-flags (logior tag-flags 8))
          )
        (setq continue nil)
        (when name-beg
          (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset))))
        )

       ((and spaced (member state '(1 3 5)))
        )

       ((and spaced (= state 2))
        (setq state 3)
        )

       ((and (eq char ?\/) (member state '(4 5)))
        (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset)))
        (setq state 1
              attr-flags 0
              equal-offset 0
              name-beg nil
              name-end nil
              val-beg nil)
        )

       ((and (eq char ?\/) (member state '(0 1)))
        )

       ((and spaced (= state 4))
        (setq state 5)
        )

       ((and (= state 3)
             (or (and (>= char 97) (<= char 122)) ;a - z
                 (and (>= char 65) (<= char 90)) ;A - Z
                 (eq char ?\-)))
        (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset)))
        (setq state 2
              attr-flags 0
              equal-offset 0
              name-beg pos
              name-end pos
              val-beg nil)
        )

       ((and (eq char ?\n) (not (member state '(7 8 9))))
        (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset)))
        (setq state 1
              attr-flags 0
              equal-offset 0
              name-beg nil
              name-end nil
              val-beg nil)
        )

       ((and (= state 6) (member char '(?\s ?\n ?\/)))
        (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset)))
        (setq state 1
              attr-flags 0
              equal-offset 0
              name-beg nil
              name-end nil
              val-beg nil)
        )

       ((and quoted (= quoted 2) (member char '(?\s ?\n ?\>)))
        (when (eq char ?\>)
          (setq tag-flags (logior tag-flags 16))
          (setq continue nil))
        (setq state 6)
        (setq attrs (+ attrs (web-mode-attr-scan state char name-beg name-end val-beg attr-flags equal-offset)))
        (setq state 1
              attr-flags 0
              equal-offset 0
              name-beg nil
              name-end nil
              val-beg nil)
        )

       ((and (not spaced) (= state 1))
        (when (and is-jsx (eq char ?\{))
          (setq attr-flags 4))
        (setq state 2)
        (setq name-beg pos
              name-end pos)
        )

       ((member state '(4 5))
        (setq val-beg pos)
        (setq state 6)
        )

       ((= state 1)
        (setq state 2)
        )

       ((= state 2)
        (setq name-end pos)
        (when (and (= attr-flags 0) (member char '(?\- ?\:)))
          (let (attr)
            (setq attr (buffer-substring-no-properties name-beg (1+ name-end)))
            (cond
             ((member attr '("http-equiv"))
              (setq attr-flags (1- attr-flags))
              )
             ((and web-mode-engine-attr-regexp
                   (string-match-p web-mode-engine-attr-regexp attr))
              ;;(message "%S: %S" pos web-mode-engine-attr-regexp)
              (setq attr-flags (logior attr-flags 2))
              ;;(setq attr-flags (1- attr-flags))
              )
             ((and (eq char ?\-) (not (string= attr "http-")))
              (setq attr-flags (logior attr-flags 1)))
             ) ;cond
            ) ;let
          ) ;when attr-flags = 1
        ) ;state=2

       ) ;cond

      ;;(message "point(%S) end(%S) state(%S) c(%S) name-beg(%S) name-end(%S) val-beg(%S) attr-flags(%S) equal-offset(%S)" pos end state char name-beg name-end val-beg attr-flags equal-offset)

      (when (and quoted (>= quoted 2))
        (setq quoted nil))

      (setq escaped (eq ?\\ char))
      (when (null go-back)
        (forward-char))

      ) ;while

    (when (> attrs 0) (setq tag-flags (logior tag-flags 1)))

    tag-flags))

(defun web-mode-attr-scan (state char name-beg name-end val-beg flags equal-offset)
;;  (message "point(%S) state(%S) c(%c) name-beg(%S) name-end(%S) val-beg(%S) flags(%S) equal-offset(%S)"
;;           (point) state char name-beg name-end val-beg flags equal-offset)
  (if (null flags) (setq flags 0))
  (cond
   ((null name-beg)
;;    (message "name-beg is null (%S)" (point))
    0)
   ((or (and (= state 8) (not (eq ?\" char)))
        (and (= state 7) (not (eq ?\' char))))
    (put-text-property name-beg (1+ name-beg) 'tag-attr-beg flags)
    (put-text-property name-beg val-beg 'tag-attr t)
    (put-text-property (1- val-beg) val-beg 'tag-attr-end equal-offset)
    1)
   ((and (member state '(4 5)) (null val-beg))
    (put-text-property name-beg (1+ name-beg) 'tag-attr-beg flags)
    (put-text-property name-beg (+ name-beg equal-offset 1) 'tag-attr t)
    (put-text-property (+ name-beg equal-offset) (+ name-beg equal-offset 1) 'tag-attr-end equal-offset)
    1)
   (t
    (let (val-end)
      (if (null val-beg)
          (setq val-end name-end)
        (setq val-end (point))
        (when (or (null char) (member char '(?\s ?\n ?\> ?\/)))
          (setq val-end (1- val-end))
          )
        ) ;if
      (put-text-property name-beg (1+ name-beg) 'tag-attr-beg flags)
      (put-text-property name-beg (1+ val-end) 'tag-attr t)
      (put-text-property val-end (1+ val-end) 'tag-attr-end equal-offset)
      ) ;let
    1) ;t
   ) ;cond
  )

(defun web-mode-part-scan (reg-beg reg-end &optional content-type depth)
  (save-excursion
    (let (token-re ch-before ch-at ch-next token-type beg continue)
      ;;(message "%S %S" reg-beg reg-end)
      (cond
       (content-type
        )
       ((member web-mode-content-type web-mode-part-content-types)
        (setq content-type web-mode-content-type))
       (t
        (setq content-type (symbol-name (get-text-property reg-beg 'part-side))))
       ) ;cond

      (goto-char reg-beg)

      (cond
       ((member content-type '("javascript" "json"))
        (setq token-re "/\\|\"\\|'\\|`"))
       ((member content-type '("jsx"))
        (setq token-re "/\\|\"\\|'\\|`\\|</?[[:alpha:]]"))
       ((string= web-mode-content-type "css")
        (setq token-re "\"\\|'\\|/\\*\\|//"))
       ((string= content-type "css")
        (setq token-re "\"\\|'\\|/\\*"))
       (t
        (setq token-re "/\\*\\|\"\\|'"))
       )

      (while (and token-re (< (point) reg-end) (web-mode-dom-rsf token-re reg-end t))

        (setq beg (match-beginning 0)
              token-type nil
              continue t
              ch-at (char-after beg)
              ch-next (or (char-after (1+ beg)) ?\d)
              ch-before (or (char-before beg) ?\d))

        ;;(message "[%S>%S|%S] %S %c %c %c" reg-beg reg-end depth beg ch-before ch-at ch-next)

        (cond

         ((eq ?\' ch-at)
          (while (and continue (search-forward "'" reg-end t))
            (cond
             ((get-text-property (1- (point)) 'block-side)
              (setq continue t))
             ((looking-back "\\\\+'" reg-beg t)
              (setq continue (= (mod (- (point) (match-beginning 0)) 2) 0))
              )
             (t
              (setq continue nil))
             )
            ) ;while
          (setq token-type 'string))

         ((eq ?\` ch-at)
          (while (and continue (search-forward "`" reg-end t))
            (cond
             ((get-text-property (1- (point)) 'block-side)
              (setq continue t))
             ((looking-back "\\\\+`" reg-beg t)
              (setq continue (= (mod (- (point) (match-beginning 0)) 2) 0)))
             (t
              (setq continue nil))
             )
            ) ;while
          (setq token-type 'string))

         ((eq ?\" ch-at)
          (while (and continue (search-forward "\"" reg-end t))
            (cond
             ((get-text-property (1- (point)) 'block-side)
              (setq continue t))
             ((looking-back "\\\\+\"" reg-beg t)
              (setq continue (= (mod (- (point) (match-beginning 0)) 2) 0)))
             (t
              (setq continue nil))
             ) ;cond
            ) ;while
          (cond
           ((string= content-type "json")
            (if (looking-at-p "[ ]*:")
                (cond
                 ((eq ?\@ (char-after (1+ beg)))
                  (setq token-type 'context))
                 (t
                  (setq token-type 'key))
                 )
              (setq token-type 'string))
            ) ;json
           (t
            (setq token-type 'string))
           ) ;cond
          )

         ((eq ?\< ch-at)
          ;;(message "before [%S>%S|%S] pt=%S" reg-beg reg-end depth (point))
          (if (web-mode-jsx-skip reg-end)
              (web-mode-jsx-scan-element beg (point) depth)
            (forward-char))
          ;;(message "after [%S>%S|%S] pt=%S" reg-beg reg-end depth (point))
          )

         ((and (eq ?\/ ch-at) (member content-type '("javascript" "jsx")))
          (cond
           ((eq ?\\ ch-before)
            )
           ((eq ?\* ch-next)
            ;;(message "--> %S %S" (point) reg-end)
            (when (search-forward "*/" reg-end t)
              (setq token-type 'comment))
            )
           ((eq ?\/ ch-next)
            (setq token-type 'comment)
            (goto-char (if (< reg-end (line-end-position)) reg-end (line-end-position)))
            )
           ((and (looking-at-p ".*/")
                 (looking-back "[[(,=:!&|?{};][ ]*/"))
                 ;;(re-search-forward "/[gimyu]*" reg-end t))
            (let ((eol (line-end-position)))
              (while (and continue (search-forward "/" eol t))
                (cond
                 ((get-text-property (1- (point)) 'block-side)
                  (setq continue t))
                 ((looking-back "\\\\+/" reg-beg t)
                  (setq continue (= (mod (- (point) (match-beginning 0)) 2) 0)))
                 (t
                  (re-search-forward "[gimyu]*" eol t)
                  (setq token-type 'string)
                  (setq continue nil))
                 )
                ) ;while
              ) ;let
            )
           ) ;cond
          )

         ((eq ?\/ ch-next)
          (unless (eq ?\\ ch-before)
            (setq token-type 'comment)
            (goto-char (if (< reg-end (line-end-position)) reg-end (line-end-position)))
            )
          )

         ((eq ?\* ch-next)
          (cond
           ((search-forward "*/" reg-end t)
            (setq token-type 'comment))
           ((not (eobp))
            (forward-char))
           ) ;cond
          )

         ) ;cond

        (when (and beg (>= reg-end (point)) token-type)
          (put-text-property beg (point) 'part-token token-type)
          (cond
           ((eq token-type 'comment)
            (put-text-property beg (1+ beg) 'syntax-table (string-to-syntax "<"))
            (when (< (point) (point-max))
              (if (< (point) (line-end-position))
                  (put-text-property (1- (point)) (point) 'syntax-table (string-to-syntax ">")) ;#445
                (put-text-property (point) (1+ (point)) 'syntax-table (string-to-syntax ">")) ;#377
                )
              ) ;when
            ) ;comment
           ((eq token-type 'string)
            (put-text-property beg (1+ beg) 'syntax-table (string-to-syntax "|"))
            (when (< (point) (point-max))
              (if (< (point) (line-end-position))
                  (put-text-property (1- (point)) (point) 'syntax-table (string-to-syntax "|"))
                (put-text-property (point) (1+ (point)) 'syntax-table (string-to-syntax "|"))
                )
              ) ;when
            ) ;string
           ) ;cond
          ) ;when

        (when (> (point) reg-end)
          (message "reg-beg(%S) reg-end(%S) token-type(%S) point(%S)" reg-beg reg-end token-type (point)))

        ;;(message "#[%S>%S|%S] %S %c %c %c | (%S)" reg-beg reg-end depth beg ch-before ch-at ch-next (point))

        ) ;while

      )))

(defun web-mode-jsx-skip (reg-end)
  (let ((continue t) (pos nil) (i 0))
    (save-excursion
      (while continue
        (cond
         ((> (setq i (1+ i)) 100)
          (message "jsx-skip ** warning **")
          (setq continue nil))
         ((not (web-mode-dom-rsf ">\\([ \t\n]*[\];,)':}]\\)\\|{" reg-end))
          (setq continue nil)
          )
         ((eq (char-before) ?\{)
          (backward-char)
          (web-mode-closing-paren reg-end)
          (forward-char)
          )
         (t
          (setq continue nil)
          (setq pos (match-beginning 1))
          ) ;t
         ) ;cond
        ) ;while
      ) ;save-excursion
    (when pos (goto-char pos))
    ;;(message "jsx-skip: %S" pos)
    pos))

;; http://facebook.github.io/jsx/
;; https://github.com/facebook/jsx/blob/master/AST.md
(defun web-mode-jsx-scan-element (reg-beg reg-end depth)
  (unless depth (setq depth 1))
  (save-excursion
    (let (token-beg token-end regexp)
      (goto-char reg-beg)
      (put-text-property reg-beg (1+ reg-beg) 'jsx-beg depth)
      (put-text-property (1- reg-end) reg-end 'jsx-end depth)
      (put-text-property reg-beg reg-end 'jsx-depth depth)
      (goto-char reg-beg)
      (while (web-mode-part-sf "/*" reg-end t)
        (goto-char (match-beginning 0))
        (if (looking-back "{")
            (progn
              (backward-char)
              (setq regexp "*/}"))
          (setq regexp "*/"))
        (setq token-beg (point))
        (if (not (web-mode-part-sf regexp reg-end t))
            (goto-char reg-end)
          (setq token-end (point))
          (put-text-property token-beg token-end 'part-token 'comment)
          ) ;if
        ) ;while
      (web-mode-scan-elements reg-beg reg-end)
      (web-mode-jsx-scan-expression reg-beg reg-end (1+ depth))
      )))

(defun web-mode-jsx-scan-expression (reg-beg reg-end depth)
  (let ((continue t) beg end)
    (save-excursion
      (goto-char reg-beg)
      ;;(message "reg-beg=%S reg-end=%S" reg-beg reg-end)
      (while (and continue (search-forward "{" reg-end t))
        (backward-char)
        (setq beg (point)
              end (web-mode-closing-paren reg-end))
        (cond
         ((eq (get-text-property beg 'part-token) 'comment)
          (forward-char))
         ((not end)
          (setq continue nil))
         (t
          (setq end (1+ end))
          (put-text-property beg end 'jsx-depth depth)
          (put-text-property beg (1+ beg) 'jsx-beg depth)
          (put-text-property (1- end) end 'jsx-end depth)
          (web-mode-part-scan beg end "jsx" (1+ depth))
          ) ;t
         ) ;cond
        )
      )
    ))

(defun web-mode-jsx-is-html (&optional pos)
  (interactive)
  (unless pos (setq pos (point)))
  (let ((depth (get-text-property pos 'jsx-depth)))
    (cond
     ((or (null depth) (<= pos 2))
      (setq pos nil))
     ((and (= depth 1) (get-text-property pos 'jsx-beg))
      (setq pos nil))
     ((get-text-property pos 'jsx-beg)
      (setq pos (null (get-text-property pos 'tag-beg))))
     ((setq pos (web-mode-jsx-depth-beginning-position pos))
      (setq pos (not (null (get-text-property pos 'tag-beg)))))
     (t
      (setq pos nil))
     ) ;cond
    ;;(message "is-html: %S (depth=%S)" pos depth)
    pos))

(defun web-mode-jsx-depth-beginning-position (&optional pos target-depth)
  (interactive)
  (unless pos (setq pos (point)))
  (unless target-depth (setq target-depth (get-text-property pos 'jsx-depth)))
  (cond
   ((or (null target-depth) (bobp))
    (setq pos nil))
   ((and (get-text-property pos 'jsx-beg) (= target-depth (get-text-property pos 'jsx-depth)))
    )
   (t
    (let ((continue t) depth)
      (while continue
        (setq pos (previous-single-property-change pos 'jsx-depth))
        (cond
         ((or (null pos)
              (null (setq depth (get-text-property pos 'jsx-depth))))
          (setq continue nil
                pos nil))
         ((and (get-text-property pos 'jsx-beg) (= target-depth depth))
          (setq continue nil))
         ) ;cond
        ) ;while
      ) ;let
    ) ;t
   ) ;cond
  ;;(message "beg: %S" pos)
  pos)

(defun web-mode-jsx-element-next (reg-end)
  (let (continue beg end)
    (setq beg (point))
    (unless (get-text-property beg 'jsx-depth)
      (setq beg (next-single-property-change beg 'jsx-beg)))
    (setq continue (and beg (< beg reg-end))
          end beg)
    (while continue
      (setq end (next-single-property-change end 'jsx-end))
      (cond
       ((or (null end) (> end reg-end))
        (setq continue nil
              end nil))
       ((eq (get-text-property end 'jsx-depth) 1)
        (setq continue nil))
       (t
        (setq end (1+ end)))
       ) ;cond
      ) ;while
    ;;(message "beg=%S end=%S" beg end)
    (if (and beg end (< beg end)) (cons beg end) nil)))

(defun web-mode-jsx-expression-next (reg-end)
  (let (beg end depth continue pos)
    (setq beg (point))
    ;;(message "pt=%S" beg)
    (unless (and (get-text-property beg 'jsx-beg) (null (get-text-property beg 'tag-beg)))
      ;;(setq beg (next-single-property-change beg 'jsx-beg))
      (setq continue t
            pos (1+ beg))
      (while continue
        (setq pos (next-single-property-change pos 'jsx-beg))
        (cond
         ((null pos)
          (setq continue nil
                beg nil))
         ((> pos reg-end)
          (setq continue nil
                beg nil))
         ((null (get-text-property pos 'jsx-beg))
          )
         ((null (get-text-property pos 'tag-beg))
          (setq continue nil
                beg pos))
         ;;(t
         ;; (setq pos (1+ pos)))
         ) ;cond
        ) ;while
      ) ;unless
    ;;(message "beg=%S" beg)
    (when (and beg (< beg reg-end))
      (setq depth (get-text-property beg 'jsx-beg)
            continue (not (null depth))
            pos beg)
      ;;(message "beg=%S" beg)
      (while continue
        (setq pos (next-single-property-change pos 'jsx-end))
        ;;(message "pos=%S" pos)
        (cond
         ((null pos)
          (setq continue nil))
         ((> pos reg-end)
          (setq continue nil))
         ((eq depth (get-text-property pos 'jsx-end))
          (setq continue nil
                end pos))
         (t
          ;;(setq pos (1+ pos))
          )
         ) ;cond
        ) ;while
      ) ;when
    ;;(message "%S > %S" beg end)
    (if (and beg end) (cons beg end) nil)))

(defun web-mode-jsx-depth-next (reg-end)
  (let (beg end depth continue pos)
    (setq beg (point))
    ;;(message "pt=%S" beg)
    (unless (get-text-property beg 'jsx-beg)
      ;;(setq beg (next-single-property-change beg 'jsx-beg))
      ;;(setq pos (1+ beg))
      (setq pos (next-single-property-change (1+ beg) 'jsx-beg))
      (cond
       ((null pos)
        (setq beg nil))
       ((>= pos reg-end)
        (setq beg nil))
       (t
        (setq beg pos))
       ) ;cond
      ) ;unless
    ;;(message "beg=%S" beg)
    (when beg
      (setq depth (get-text-property beg 'jsx-beg)
            continue (not (null depth))
            pos beg)
      ;;(message "beg=%S" beg)
      (while continue
        (setq pos (next-single-property-change pos 'jsx-end))
        ;;(message "pos=%S" pos)
        (cond
         ((null pos)
          (setq continue nil))
         ((> pos reg-end)
          (setq continue nil))
         ((eq depth (get-text-property pos 'jsx-end))
          (setq continue nil
                end pos))
         (t
          ;;(setq pos (1+ pos))
          )
         ) ;cond
        ) ;while
      ) ;when
    ;;(message "%S > %S" beg end)
    (if (and beg end) (cons beg end) nil)))

(defun web-mode-jsx-beginning ()
  (interactive)
  (let (depth (continue t) (reg-beg (point-min)) (pos (point)))
    (setq depth (get-text-property pos 'jsx-depth))
    (cond
     ((not depth)
      )
     ((get-text-property (1- pos) 'jsx-beg)
      (goto-char (1- pos)))
     (t
      (while continue
        (setq pos (previous-single-property-change pos 'jsx-beg))
        ;;(message "pos=%S" pos)
        (cond
         ((null pos)
          (setq continue nil))
         ((<= pos reg-beg)
          (setq continue nil))
         ((eq depth (get-text-property pos 'jsx-beg))
          (setq continue nil))
         ) ;cond
        ) ;while
      (web-mode-go pos)
      ) ;t
     ) ;cond
    ))

(defun web-mode-jsx-end ()
  (interactive)
  (let (depth (continue t) (reg-end (point-max)) (pos (point)))
    (setq depth (get-text-property pos 'jsx-depth))
    (cond
     ((not depth)
      )
     ((get-text-property pos 'jsx-end)
      (goto-char (+ pos 1)))
     (t
      (while continue
        (setq pos (next-single-property-change pos 'jsx-end))
        ;;(message "pos=%S" pos)
        (cond
         ((null pos)
          (setq continue nil))
         ((> pos reg-end)
          (setq continue nil))
         ((eq depth (get-text-property pos 'jsx-end))
          (setq continue nil))
         ) ;cond
        ) ;while
      (web-mode-go pos 1)
      ) ;t
     ) ;cond
    ))

(defun web-mode-velocity-skip (pos)
  (goto-char pos)
  (let ((continue t) (i 0))
    (when (eq ?\# (char-after))
      (forward-char))
    (when (member (char-after) '(?\$ ?\@))
      (forward-char))
    (when (member (char-after) '(?\!))
      (forward-char))
    (if (member (char-after) '(?\{))
        (search-forward "}")
      (setq continue t)
      (while continue
        (skip-chars-forward "a-zA-Z0-9_-")
        (when (> (setq i (1+ i)) 500)
          (message "velocity-skip ** warning (%S) **" pos)
          (setq continue nil))
        (when (member (char-after) '(?\())
          (search-forward ")" nil t))
        (if (member (char-after) '(?\.))
            (forward-char)
          (setq continue nil))
        ) ;while
      ) ;if
    ))

(defun web-mode-razor-skip (pos)
  (goto-char pos)
  (let ((continue t) (i 0))
    (while continue
      (skip-chars-forward " =@a-zA-Z0-9_-")
      (cond
       ((> (setq i (1+ i)) 500)
        (message "razor-skip ** warning **")
        (setq continue nil))
       ((and (eq (char-after) ?\*)
             (eq (char-before) ?@))
        (when (not (search-forward "*@" nil t))
          (setq continue nil))
        )
       ((looking-at-p "@[({]")
        (forward-char)
        (when (setq pos (web-mode-closing-paren-position (point)))
          (goto-char pos))
        (forward-char)
        )
       ((and (not (eobp)) (eq ?\( (char-after)))
        (if (looking-at-p "[ \n]*[<@]")
            (setq continue nil)
          (when (setq pos (web-mode-closing-paren-position))
            (goto-char pos))
          (forward-char)
          ) ;if
        )
       ((and (not (eobp)) (eq ?\. (char-after)))
        (forward-char))
       ((looking-at-p "[ \n]*{")
        (search-forward "{")
        (if (looking-at-p "[ \n]*[<@]")
            (setq continue nil)
          (backward-char)
          (when (setq pos (web-mode-closing-paren-position))
            (goto-char pos))
          (forward-char)
          ) ;if
        )
       ((looking-at-p "}")
        (forward-char))
       (t
        (setq continue nil))
       ) ;cond
      ) ;while
    ))

;; css rule = selector(s) + declaration (properties)
(defun web-mode-css-rule-next (limit)
  (let (at-rule sel-beg sel-end dec-beg dec-end chunk)
    (skip-chars-forward "\n\t ")
    (setq sel-beg (point))
    (when (and (< (point) limit)
               (web-mode-part-rsf "[{;]" limit))
      (setq sel-end (1- (point)))
      (cond
       ((eq (char-before) ?\{)
        (setq dec-beg (point))
        (setq dec-end (web-mode-closing-paren-position (1- dec-beg) limit))
        (if dec-end
            (progn
              (goto-char dec-end)
              (forward-char))
          (setq dec-end limit)
          (goto-char limit))
        )
       (t
        )
       ) ;cond
      (setq chunk (buffer-substring-no-properties sel-beg sel-end))
      (when (string-match "@\\([[:alpha:]-]+\\)" chunk)
        (setq at-rule (match-string-no-properties 1 chunk)))
      ) ;when
    (if (not sel-end)
        (progn (goto-char limit) nil)
      (list :at-rule at-rule
            :sel-beg sel-beg
            :sel-end sel-end
            :dec-beg dec-beg
            :dec-end dec-end)
      ) ;if
    ))

(defun web-mode-css-rule-current (&optional pos part-beg part-end)
  "Current CSS rule boundaries."
  (unless pos (setq pos (point)))
  (unless part-beg (setq part-beg (web-mode-part-beginning-position pos)))
  (unless part-end (setq part-end (web-mode-part-end-position pos)))
  (save-excursion
    (let (beg end)
      (goto-char pos)
      (if (not (web-mode-part-sb "{" part-beg))
          (progn
            (setq beg part-beg)
            (if (web-mode-part-sf ";" part-end)
                (setq end (1+ (point)))
              (setq end part-end))
            ) ;progn
        (setq beg (point))
        (setq end (web-mode-closing-paren-position beg part-end))
        (if end
            (setq end (1+ end))
          (setq end (line-end-position)))
;;        (message "%S >>beg%S >>end%S" pos beg end)
        (if (> pos end)

            ;;selectors
            (progn
              (goto-char pos)
              (if (web-mode-part-rsb "[};]" part-beg)
                  (setq beg (1+ (point)))
                (setq beg part-beg)
                ) ;if
              (goto-char pos)
              (if (web-mode-part-rsf "[{;]" part-end)
                  (cond
                   ((eq (char-before) ?\;)
                    (setq end (point))
                    )
                   (t
                    (setq end (web-mode-closing-paren-position (1- (point)) part-end))
                    (if end
                        (setq end (1+ end))
                      (setq end part-end))
                    )
                   ) ;cond
                (setq end part-end)
                )
              ) ;progn selectors

          ;; declaration
          (goto-char beg)
          (if (web-mode-part-rsb "[}{;]" part-beg)
              (setq beg (1+ (point)))
            (setq beg part-beg)
            ) ;if
          ) ;if > pos end
        )
;;      (message "beg(%S) end(%S)" beg end)
      (when (eq (char-after beg) ?\n)
        (setq beg (1+ beg)))
      (cons beg end)
      )))

(defun web-mode-scan-engine-comments (reg-beg reg-end tag-start tag-end)
  "Scan engine comments (mako, django)."
  (save-excursion
    (let (beg end (continue t))
      (goto-char reg-beg)
      (while (and continue
                  (< (point) reg-end)
                  (re-search-forward tag-start reg-end t))
        (goto-char (match-beginning 0))
        (setq beg (point))
        (if (not (re-search-forward tag-end reg-end t))
            (setq continue nil)
          (setq end (point))
          (remove-list-of-text-properties beg end web-mode-scan-properties)
          (add-text-properties beg end '(block-side t block-token comment))
          (put-text-property beg (1+ beg) 'block-beg 0)
          (put-text-property (1- end) end 'block-end t)
          ) ;if
        ) ;while
      )))

(defun web-mode-propertize (&optional beg end)

  (unless beg (setq beg web-mode-change-beg))
  (unless end (setq end web-mode-change-end))

  ;;(message "%S %S" web-mode-content-type (get-text-property beg 'part-side))
  ;;(message "propertize: beg(%S) end(%S)" web-mode-change-beg web-mode-change-end)
  ;;(message "%S %S" (get-text-property beg 'part-side) (get-text-property end 'part-side))

  (when (and end (> end (point-max)))
    (setq end (point-max)))

  (setq web-mode-change-beg nil
        web-mode-change-end nil)
  (cond

   ((or (null beg) (null end))
    nil)

   ((and (member web-mode-engine '("php" "asp"))
         (get-text-property beg 'block-side)
         (get-text-property end 'block-side)
         (> beg (point-min))
         (not (eq (get-text-property (1- beg) 'block-token) 'delimiter-beg))
         (not (eq (get-text-property end 'block-token) 'delimiter-end)))
    ;;(message "invalidate block")
    (web-mode-invalidate-block-region beg end))

   ((and (or (member web-mode-content-type '("css" "jsx" "javascript"))
             (and (get-text-property beg 'part-side)
                  (get-text-property end 'part-side)
                  (> beg (point-min))
                  (get-text-property (1- beg) 'part-side))
             ))
    ;;(message "invalidate part (%S > %S)" beg end)
    (web-mode-invalidate-part-region beg end))

   (t
    ;;(message "invalidate default (%S > %S)" beg end)
    (web-mode-invalidate-region beg end))

   ) ;cond

  )

;; NOTE: il est important d'identifier des caractères en fin de ligne
;; web-mode-block-tokenize travaille en effet sur les fins de lignes pour
;; les commentaires de type //
(defun web-mode-invalidate-block-region (pos-beg pos-end)
  ;;  (message "pos-beg(%S) pos-end(%S)" pos-beg pos-end)
  (save-excursion
    (let (beg end code-beg code-end)
      ;;(message "invalidate-block-region: pos-beg(%S)=%S" pos-beg (get-text-property pos 'block-side))
      ;;(message "code-beg(%S) code-end(%S) pos-beg(%S) pos-end(%S)" code-beg code-end pos-beg pos-end)
      (cond
       ((not (and (setq code-beg (web-mode-block-code-beginning-position pos-beg))
                  (setq code-end (web-mode-block-code-end-position pos-beg))
                  (>= pos-beg code-beg)
                  (<= pos-end code-end)
                  (> code-end code-beg)))
        (web-mode-invalidate-region pos-beg pos-end))
       ((member web-mode-engine '("asp"))
        (goto-char pos-beg)
        (forward-line -1)
        (setq beg (line-beginning-position))
        (when (> code-beg beg)
          (setq beg code-beg))
        (goto-char pos-beg)
        (forward-line)
        (setq end (line-end-position))
        (when (< code-end end)
          (setq end code-end))
        ;; ?? pas de (web-mode-block-tokenize beg end) ?
        (cons beg end)
        ) ;asp
       (t
        (goto-char pos-beg)
        (when (string= web-mode-engine "php")
          (cond
           ((and (looking-back "\*")
                 (looking-at-p "/"))
            (search-backward "/*" code-beg))
           ) ;cond
          )
        (if (web-mode-block-rsb "[;{}(][ ]*\n" code-beg)
            (setq beg (match-end 0))
          (setq beg code-beg))
        (goto-char pos-end)
        (if (web-mode-block-rsf "[;{})][ ]*\n" code-end)
            (setq end (1- (match-end 0)))
          (setq end code-end))
        (web-mode-block-tokenize beg end)
        ;;(message "beg(%S) end(%S)" beg end)
        (cons beg end)
        )
       ) ;cond
      )))

(defun web-mode-invalidate-part-region (pos-beg pos-end)
  (save-excursion
    (let (beg end part-beg part-end language)
      (if (member web-mode-content-type '("css" "javascript" "json" "jsx"))
          (setq language web-mode-content-type)
        (setq language (symbol-name (get-text-property pos-beg 'part-side))))
      (setq part-beg (web-mode-part-beginning-position pos-beg)
            part-end (web-mode-part-end-position pos-beg))
      ;;(message "language(%S) pos-beg(%S) pos-end(%S) part-beg(%S) part-end(%S)"
      ;;         language pos-beg pos-end part-beg part-end)
      (goto-char pos-beg)
      (cond
       ((not (and part-beg part-end
                  (>= pos-beg part-beg)
                  (<= pos-end part-end)
                  (> part-end part-beg)))
        (web-mode-invalidate-region pos-beg pos-end))
       ((member language '("javascript" "json" "jsx"))
        (if (web-mode-javascript-rsb "[;{}(][ ]*\n" part-beg)
            (setq beg (match-end 0))
          (setq beg part-beg))
        (goto-char pos-end)
        (if (web-mode-javascript-rsf "[;{})][ ]*\n" part-end)
            (setq end (match-end 0))
          (setq end part-end))
        (web-mode-scan-region beg end language))
       ((string= language "css")
        (let (rule1 rule2)
          (setq rule1 (web-mode-css-rule-current pos-beg))
          (setq rule2 rule1)
          (when (> pos-end (cdr rule1))
            (setq rule2 (web-mode-css-rule-current pos-end)))
          (setq beg (car rule1)
                end (cdr rule2))
          )
        (web-mode-scan-region beg end language))
       (t
        (setq beg part-beg
              end part-end)
        (web-mode-scan-region beg end language))
       ) ;cond
      )))

(defun web-mode-invalidate-region (reg-beg reg-end)
  ;;(message "%S | reg-beg(%S) reg-end(%S)" (point) reg-beg reg-end)
  (setq reg-beg (web-mode-invalidate-region-beginning-position reg-beg)
        reg-end (web-mode-invalidate-region-end-position reg-end))
  ;;(message "invalidate-region: reg-beg(%S) reg-end(%S)" reg-beg reg-end)
  (web-mode-scan-region reg-beg reg-end))

(defun web-mode-invalidate-region-beginning-position (pos)
  (save-excursion
    (goto-char pos)
    (when (and (bolp) (not (bobp)))
      (backward-char))
    (beginning-of-line)
    ;;(message "pos=%S %S" (point) (text-properties-at (point)))
    (setq pos (point-min))
    (let ((continue (not (bobp))))
      (while continue
        (cond
         ((bobp)
          (setq continue nil))
         ;; NOTE: Going back to the previous start tag is necessary
         ;; when inserting a part endtag (e.g. </script>).
         ;; Indeed, parts must be identified asap.
         ((and (progn (back-to-indentation) t)
               (get-text-property (point) 'tag-beg)
               (eq (get-text-property (point) 'tag-type) 'start))
          (setq pos (point)
                continue nil))
         (t
          (forward-line -1))
         ) ;cond
        ) ;while
      ;;(message "pos=%S" pos)
      pos)))

(defun web-mode-invalidate-region-end-position (pos)
  (save-excursion
    (goto-char pos)
    ;;(message "pos=%S %S" pos (get-text-property pos 'block-token))
    (when (string= web-mode-engine "jsp")
      (cond
       ((and (looking-back "<%")
             (looking-at-p "--"))
        (search-forward "--%>"))
       ((and (looking-back "-- %")
             (looking-at-p ">"))
        (search-forward "--%>"))
       ) ;cond
      ) ;when

    (setq pos (point-max))
    (let ((continue (not (eobp))))
      (while continue
        (end-of-line)
        ;;(message "%S %S" (point) (get-text-property (point) 'block-token))
        (cond
         ((eobp)
          (setq continue nil))
         ;;()
         ((and (not (get-text-property (point) 'tag-type))
               (not (get-text-property (point) 'part-side))
               (not (get-text-property (point) 'block-side)))
          (setq pos (point)
                continue nil))
         (t
          (forward-line))
         ) ;cond
        ) ;while
      pos)))

(defun web-mode-buffer-scan ()
  "Scan entine buffer."
  (interactive)
  (web-mode-scan-region (point-min) (point-max)))

;;---- FONTIFICATION -----------------------------------------------------------

(defun web-mode-font-lock-highlight (limit)
  ;;(message "font-lock-highlight: point(%S) limit(%S) change-beg(%S) change-end(%S)" (point) limit web-mode-change-beg web-mode-change-end)
  (cond
   (web-mode-inhibit-fontification
    nil)
   (t
    (web-mode-highlight-region (point) limit)
    nil)
   ))

(defun web-mode-buffer-highlight ()
  (interactive)
  (if (fboundp 'font-lock-flush)
      (font-lock-flush)
    (font-lock-fontify-buffer)))

(defun web-mode-extend-region ()
  ;;(message "extend-region: flb(%S) fle(%S) wmcb(%S) wmce(%S)" font-lock-beg font-lock-end web-mode-change-beg web-mode-change-end)
  ;;  (setq font-lock-beg web-mode-change-beg
  ;;        font-lock-end web-mode-change-end)
  (cond
   (web-mode-inhibit-fontification
    nil)
   (t ;;(and web-mode-change-beg web-mode-change-end)
    (when (or (null web-mode-change-beg) (< font-lock-beg web-mode-change-beg))
      ;;(message "font-lock-beg(%S) < web-mode-change-beg(%S)" font-lock-beg web-mode-change-beg)
      (setq web-mode-change-beg font-lock-beg))
    (when (or (null web-mode-change-end) (> font-lock-end web-mode-change-end))
      ;;(message "font-lock-end(%S) > web-mode-change-end(%S)" font-lock-end web-mode-change-end)
      (setq web-mode-change-end font-lock-end))
    (let ((region (web-mode-propertize web-mode-change-beg web-mode-change-end)))
      (when region
        ;;(message "region: %S" region)
        (setq font-lock-beg (car region)
              font-lock-end (cdr region)
              ;;web-mode-change-beg (car region)
              ;;web-mode-change-end (cdr region)
              )
        ) ;when
      ) ;let
    nil) ;t
   ))

(defun web-mode-unfontify-region (beg end)
  ;;(message "unfontify: %S %S" beg end)
  )

(defun web-mode-highlight-region (&optional beg end) ;; content-type)
  ;;(message "highlight-region: beg(%S) end(%S)" beg end)
  (web-mode-with-silent-modifications
   (save-excursion
     (save-restriction
       (save-match-data
         (let ((buffer-undo-list t)
               ;;(inhibit-modification-hooks t)
               (inhibit-point-motion-hooks t)
               (inhibit-quit t))
           (remove-list-of-text-properties beg end '(font-lock-face face))
           (cond
            ((and (get-text-property beg 'block-side)
                  (not (get-text-property beg 'block-beg)))
             (web-mode-block-highlight beg end))
            ((or (member web-mode-content-type web-mode-part-content-types)
                 ;;(member content-type web-mode-part-content-types)
                 (get-text-property beg 'part-side))
             (web-mode-part-highlight beg end)
             (web-mode-process-blocks beg end 'web-mode-block-highlight))
            ((string= web-mode-engine "none")
             (web-mode-highlight-tags beg end)
             (web-mode-process-parts beg end 'web-mode-part-highlight))
            (t
             (web-mode-highlight-tags beg end)
             (web-mode-process-parts beg end 'web-mode-part-highlight)
             (web-mode-process-blocks beg end 'web-mode-block-highlight))
            ) ;cond
           (when web-mode-enable-element-content-fontification
             (web-mode-highlight-elements beg end))
           (when web-mode-enable-whitespace-fontification
             (web-mode-highlight-whitespaces beg end))
           ;;(message "%S %S" font-lock-keywords font-lock-keywords-alist)
           ))))))

(defun web-mode-highlight-tags (reg-beg reg-end &optional depth)
  (let ((continue t))
    (goto-char reg-beg)
    (when (and (not (get-text-property (point) 'tag-beg))
               (not (web-mode-tag-next)))
      (setq continue nil))
    (when (and continue (>= (point) reg-end))
      (setq continue nil))
    (while continue
      (cond
       (depth
        (when (eq depth (get-text-property (point) 'jsx-depth))
          (web-mode-tag-highlight))
        )
       (t
        (web-mode-tag-highlight))
       ) ;cond
      (when (or (not (web-mode-tag-next))
                (>= (point) reg-end))
        (setq continue nil))
      ) ;while
    (when web-mode-enable-inlays
      (when (null web-mode-inlay-regexp)
        (setq web-mode-inlay-regexp (regexp-opt '("\\[" "\\(" "\\begin{align}"))))
      (let (beg end expr)
        (goto-char reg-beg)
        (while (web-mode-dom-rsf web-mode-inlay-regexp reg-end)
          (setq beg (match-beginning 0)
                end nil
                expr (substring (match-string-no-properties 0) 0 2))
          (setq expr (cond
                      ((string= expr "\\[") "\\]")
                      ((string= expr "\\(") "\\)")
                      (t "\\end{align}")))
          (when (and (web-mode-dom-sf expr reg-end)
                     (setq end (match-end 0))
                     (not (text-property-any beg end 'tag-end t)))
            (font-lock-append-text-property beg end 'font-lock-face 'web-mode-inlay-face)
            ) ;when
          ) ;while
        ) ;let
      ) ;when
    (when web-mode-enable-html-entities-fontification
      (let (beg end)
        (goto-char reg-beg)
        (while (web-mode-dom-rsf "&\\([#]?[[:alnum:]]\\{2,8\\}\\);" reg-end)
          (setq beg (match-beginning 0)
                end (match-end 0))
          (when (not (text-property-any beg end 'tag-end t))
            (font-lock-append-text-property beg end 'font-lock-face 'web-mode-html-entity-face)
            ) ;when
          ) ;while
        ) ;let
      ) ;when
    ))

(defun web-mode-tag-highlight (&optional beg end)
  (unless beg (setq beg (point)))
  (unless end (setq end (1+ (web-mode-tag-end-position beg))))
  (let (name type face flags slash-beg slash-end bracket-end)
    (setq flags (get-text-property beg 'tag-beg)
          type (get-text-property beg 'tag-type)
          name (get-text-property beg 'tag-name))
    (cond
     ((eq type 'comment)
      (put-text-property beg end 'font-lock-face 'web-mode-comment-face)
      (when (and web-mode-enable-comment-interpolation (> (- end beg) 5))
        (web-mode-interpolate-comment beg end nil)))
     ((eq type 'cdata)
      (put-text-property beg end 'font-lock-face 'web-mode-doctype-face))
     ((eq type 'doctype)
      (put-text-property beg end 'font-lock-face 'web-mode-doctype-face))
     ((eq type 'declaration)
      (put-text-property beg end 'font-lock-face 'web-mode-doctype-face))
     (name
      (setq face (cond
                  ((and web-mode-enable-element-tag-fontification
                        (setq face (cdr (assoc name web-mode-element-tag-faces))))
                   face)
                  ((> (logand flags 32) 0) 'web-mode-html-tag-namespaced-face)
                  ((> (logand flags 2) 0)  'web-mode-html-tag-custom-face)
                  (t                       'web-mode-html-tag-face))
            slash-beg (> (logand flags 4) 0)
            slash-end (> (logand flags 8) 0)
            bracket-end (> (logand flags 16) 0))
      (put-text-property beg (+ beg (if slash-beg 2 1))
                         'font-lock-face 'web-mode-html-tag-bracket-face)
      (put-text-property (+ beg (if slash-beg 2 1)) (+ beg (if slash-beg 2 1) (length name))
                         'font-lock-face face)
      (when (or slash-end bracket-end)
        (put-text-property (- end (if slash-end 2 1)) end 'font-lock-face 'web-mode-html-tag-bracket-face)
        ) ;when
      (when (> (logand flags 1) 0)
        ;;(message "%S>%S" beg end)
        (web-mode-highlight-attrs beg end))
      ) ;case name
     ) ;cond
    ))

(defun web-mode-highlight-attrs (reg-beg reg-end)
  (let ((continue t) (pos reg-beg) beg end flags offset face)
    ;;(message "highlight-attrs %S>%S" reg-beg reg-end)
    (while continue
      (setq beg (web-mode-attribute-next-position pos reg-end))
      (cond
       ((or (null beg) (>= beg reg-end))
        (setq continue nil))
       (t
        (setq flags (or (get-text-property beg 'tag-attr-beg) 0))
        (setq face (cond
                    ((= (logand flags 1) 1) 'web-mode-html-attr-custom-face)
                    ((= (logand flags 2) 2) 'web-mode-html-attr-engine-face)
                    ((= (logand flags 4) 4) nil)
                    (t                      'web-mode-html-attr-name-face)))
        ;;(setq end (if (get-text-property beg 'tag-attr-end) beg (web-mode-attribute-end-position beg)))
        (setq end (web-mode-attribute-end-position beg))
        (cond
         ((or (null end) (>= end reg-end))
          (setq continue nil))
         (t
          (setq offset (get-text-property end 'tag-attr-end))
          (if (= offset 0)
              (put-text-property beg (1+ end) 'font-lock-face face)
            (put-text-property beg (+ beg offset) 'font-lock-face face)
            (put-text-property (+ beg offset) (+ beg offset 1)
                               'font-lock-face
                               'web-mode-html-attr-equal-face)
            (when (not (get-text-property (+ beg offset 1) 'jsx-beg))
              (put-text-property (+ beg offset 1) (1+ end)
                                 'font-lock-face
                                 'web-mode-html-attr-value-face)
              )
            ) ;if offset
          (setq pos (1+ end))
          ) ;t
         ) ;cond
        ) ;t
       );cond
      ) ;while
    ))

(defun web-mode-block-highlight (reg-beg reg-end)
  (let (sub1 sub2 sub3 continue char keywords token-type face beg end (buffer (current-buffer)))
    ;;(message "reg-beg=%S reg-end=%S" reg-beg reg-end)

    ;; NOTE: required for block inside tag attr
    (remove-list-of-text-properties reg-beg reg-end '(font-lock-face))

    (goto-char reg-beg)

    (when (null web-mode-engine-font-lock-keywords)
      (setq sub1 (buffer-substring-no-properties
                  reg-beg (+ reg-beg 1))
            sub2 (buffer-substring-no-properties
                  reg-beg (+ reg-beg 2))
            sub3 (buffer-substring-no-properties
                  reg-beg (+ reg-beg (if (>= (point-max) (+ reg-beg 3)) 3 2))))
      )

    (cond

     ((and (get-text-property reg-beg 'block-beg)
           (eq (get-text-property reg-beg 'block-token) 'comment))
      (put-text-property reg-beg reg-end 'font-lock-face 'web-mode-comment-face)
      ) ;comment block

     (web-mode-engine-font-lock-keywords
      (setq keywords web-mode-engine-font-lock-keywords)
      )

     ((string= web-mode-engine "django")
      (cond
       ((string= sub2 "{{")
        (setq keywords web-mode-django-expr-font-lock-keywords))
       ((string= sub2 "{%")
        (setq keywords web-mode-django-code-font-lock-keywords))
       )) ;django

     ((string= web-mode-engine "mako")
      (cond
       ((member sub3 '("<% " "<%\n" "<%!"))
        (setq keywords web-mode-mako-block-font-lock-keywords))
       ((eq (aref sub2 0) ?\%)
        (setq keywords web-mode-mako-block-font-lock-keywords))
       ((member sub2 '("<%" "</"))
        (setq keywords web-mode-mako-tag-font-lock-keywords))
       ((member sub2 '("${"))
        (setq keywords web-mode-uel-font-lock-keywords))
       )) ;mako

     ((string= web-mode-engine "mason")
      ;;(message "%S %S" sub2 sub3)
      (cond
       ((member sub3 '("<% " "<%\n" "<&|"))
        (setq keywords web-mode-mason-code-font-lock-keywords))
       ((eq (aref sub2 0) ?\%)
        (setq keywords web-mode-mason-code-font-lock-keywords))
       ((and (or (string= sub2 "<%") (string= sub3 "</%"))
             (not (member sub3 '("<%c" "<%i" "<%p"))))
        (setq keywords web-mode-mason-block-font-lock-keywords))
       (t
        (setq keywords web-mode-mason-code-font-lock-keywords))
       )) ;mason

     ((string= web-mode-engine "jsp")
      (cond
       ((string= sub3 "<%@")
        (setq keywords web-mode-directive-font-lock-keywords))
       ((member sub2 '("${" "#{"))
        (setq keywords web-mode-uel-font-lock-keywords))
       ((string= sub2 "<%")
        (setq keywords web-mode-jsp-font-lock-keywords))
       ;;(t
       ;; (setq keywords web-mode-engine-tag-font-lock-keywords))
       )) ;jsp

     ((string= web-mode-engine "asp")
      (cond
       ((or (string= sub2 "<%")
            (not (string= sub1 "<")))
        (setq keywords web-mode-asp-font-lock-keywords))
       (t
        (setq keywords web-mode-engine-tag-font-lock-keywords))
       )) ;asp

     ((string= web-mode-engine "clip")
      (setq keywords web-mode-engine-tag-font-lock-keywords)
      ) ;clip

     ((string= web-mode-engine "aspx")
      (cond
       ((string= sub3 "<%@")
        (setq keywords web-mode-directive-font-lock-keywords))
       ((string= sub3 "<%$")
        (setq keywords web-mode-expression-font-lock-keywords))
       (t
        (setq keywords web-mode-aspx-font-lock-keywords))
       )) ;aspx

     ((string= web-mode-engine "freemarker")
      (cond
       ((member sub2 '("${" "#{"))
        (setq keywords web-mode-uel-font-lock-keywords))
       ((or (member sub2 '("<@" "[@" "<#" "[#"))
            (member sub3 '("</@" "[/@" "</#" "[/#")))
        (setq keywords (if (eq ?\[ (aref sub2 0))
                           web-mode-freemarker-square-font-lock-keywords
                         web-mode-freemarker-font-lock-keywords)))
       (t
        (setq keywords web-mode-engine-tag-font-lock-keywords))
       )) ;freemarker

     ) ;cond

    (when keywords
      (web-mode-fontify-region reg-beg reg-end keywords)
      (setq continue t)
      (setq end reg-beg)
      (while continue
        (if (get-text-property end 'block-token)
            (setq beg end)
          (setq beg (next-single-property-change end 'block-token buffer reg-end)))
        (setq end nil)
        (when beg (setq char (char-after beg)))
        (if (and beg (< beg reg-end))
            (progn
              (setq token-type (get-text-property beg 'block-token))
              (setq face (cond
                          ((eq token-type 'string)  'web-mode-block-string-face)
                          ((eq token-type 'comment) 'web-mode-block-comment-face)
                          (t                        'web-mode-block-delimiter-face)))
              (setq end (next-single-property-change beg 'block-token buffer reg-end))
;;              (message "end=%S" end)
              (if (and end (<= end reg-end))
                  (progn
                    ;;(message "%S > %S face(%S)" beg end face)
                    (remove-list-of-text-properties beg end '(face))
                    (put-text-property beg end 'font-lock-face face)
                    )
                (setq continue nil
                      end nil)
                ) ;if end
              ) ;progn beg
          (setq continue nil
                end nil)
          ) ;if beg
        (when (and beg end)
          (save-match-data
            (when (and web-mode-enable-heredoc-fontification
                       (eq char ?\<)
                       (> (- end beg) 8)
                       ;;(progn (message "%S" (buffer-substring-no-properties beg end)) t)
                       (string-match-p "JS\\|JAVASCRIPT\\|HTM\\|CSS" (buffer-substring-no-properties beg end)))
              (setq keywords
                    (cond
                     ((string-match-p "H" (buffer-substring-no-properties beg (+ beg 8)))
                      web-mode-html-font-lock-keywords)
                     (t
                      web-mode-javascript-font-lock-keywords)
                     ))
              (web-mode-fontify-region beg end keywords)
            ))
;;          (message "%S %c %S beg=%S end=%S" web-mode-enable-string-interpolation char web-mode-engine beg end)
          (when (and web-mode-enable-string-interpolation
                     (member char '(?\" ?\<))
                     (member web-mode-engine '("php" "erb"))
                     (> (- end beg) 4))
            (web-mode-interpolate-block-string beg end)
            ) ;when
          (when (and web-mode-enable-comment-interpolation
                     (eq token-type 'comment)
                     (> (- end beg) 3))
            (web-mode-interpolate-comment beg end t)
            ) ;when
          (when (and web-mode-enable-sql-detection
                     (eq token-type 'string)
                     (> (- end beg) 6)
                     ;;(eq char ?\<)
                     ;;(web-mode-looking-at-p (concat "[ \n]*" web-mode-sql-queries) (1+ beg))
                     (web-mode-looking-at-p (concat "\\(.\\|<<<[[:alnum:]]+\\)[ \n]*" web-mode-sql-queries) beg)
                     )
            (web-mode-interpolate-sql-string beg end)
            ) ;when
          ) ;when beg end
        ) ;while continue
      ) ;when keywords

    ;;(when (and (member web-mode-engine '("jsp" "mako"))
    (when (and (member web-mode-engine '("mako"))
               (> (- reg-end reg-beg) 12)
               (eq ?\< (char-after reg-beg)))
      (web-mode-interpolate-block-tag reg-beg reg-end))

    (when web-mode-enable-block-face
;;      (message "block-face %S %S" reg-beg reg-end)
      (font-lock-append-text-property reg-beg reg-end 'face 'web-mode-block-face))

    ))

(defun web-mode-part-highlight (reg-beg reg-end &optional depth)
  (save-excursion
    (let (start continue token-type face pos beg end string-face comment-face content-type)
      ;;(message "part-highlight: reg-beg(%S) reg-end(%S)" reg-beg reg-end)
      (if (member web-mode-content-type web-mode-part-content-types)
          (setq content-type web-mode-content-type)
        (setq content-type (symbol-name (get-text-property reg-beg 'part-side))))
      (unless depth
        (when (string= content-type "jsx") (setq depth 0))
        )
      (cond
       ((member content-type '("javascript" "jsx"))
        (setq string-face 'web-mode-javascript-string-face
              comment-face 'web-mode-javascript-comment-face)
        (web-mode-fontify-region reg-beg reg-end web-mode-javascript-font-lock-keywords))
       ((string= content-type "json")
        (setq string-face 'web-mode-json-string-face
              comment-face 'web-mode-json-comment-face)
        (web-mode-fontify-region reg-beg reg-end web-mode-javascript-font-lock-keywords))
       ((string= content-type "css")
        (setq string-face 'web-mode-css-string-face
              comment-face 'web-mode-css-comment-face)
        (web-mode-css-rules-highlight reg-beg reg-end))
       (t
        (setq string-face 'web-mode-part-string-face
              comment-face 'web-mode-part-comment-face))
       )

      (goto-char reg-beg)

      ;;(when (string= content-type "jsx") (web-mode-highlight-tags reg-beg reg-end))
      ;;(setq continue (and pos (< pos reg-end)))
      (setq continue t
            pos reg-beg)
      (while continue
        (if (get-text-property pos 'part-token)
            (setq beg pos)
          (setq beg (next-single-property-change pos 'part-token)))
        (cond
         ((or (null beg) (>= beg reg-end))
          (setq continue nil
                end nil))
         ((and (eq depth 0) (get-text-property beg 'jsx-depth))
          (setq pos (or (next-single-property-change beg 'jsx-depth) (point-max))))
         (t
          (setq token-type (get-text-property beg 'part-token))
          (setq face (cond
                      ((eq token-type 'string)  string-face)
                      ((eq token-type 'comment) comment-face)
                      ((eq token-type 'context) 'web-mode-json-context-face)
                      ((eq token-type 'key)     'web-mode-json-key-face)
                      (t                        nil)))
          (setq end (or (next-single-property-change beg 'part-token) (point-max))
                pos end)
          (cond
           ((or (null end) (> end reg-end))
            (setq continue nil
                  end nil))
           (t
            (when face
              (remove-list-of-text-properties beg end '(face))
              (put-text-property beg end 'font-lock-face face))
            (cond
             ((< (- end beg) 6)
              )
             ((eq token-type 'string)
              (when (and web-mode-enable-string-interpolation
                         (member content-type '("javascript" "jsx")))
                (web-mode-interpolate-javascript-string beg end)))
             ((eq token-type 'comment)
              (when web-mode-enable-comment-interpolation
                (web-mode-interpolate-comment beg end t)))
             ) ;cond
            ) ;t
           ) ;cond
          ) ;t
         ) ;cond
        ) ;while

      (when (and (string= web-mode-content-type "html") web-mode-enable-part-face)
        (font-lock-append-text-property reg-beg reg-end 'face
                                        (if (string= content-type "javascript")
                                            'web-mode-script-face
                                          'web-mode-style-face))
        )

      (when (and (eq depth 0) (string= content-type "jsx"))
        (let (pair elt-beg elt-end exp-beg exp-end exp-depth)
          (goto-char reg-beg)
          (while (setq pair (web-mode-jsx-element-next reg-end))
            ;;(message "elt-pair=%S" pair)
            (setq elt-beg (car pair)
                  elt-end (cdr pair))
            (remove-list-of-text-properties elt-beg (1+ elt-end) '(face))
            (web-mode-highlight-tags elt-beg elt-end 1)
            (goto-char elt-beg)
            (while (setq pair (web-mode-jsx-expression-next elt-end))
              ;;(message "exp-pair=%S elt-end=%S" pair elt-end)
              (setq exp-beg (car pair)
                    exp-end (cdr pair))
              (when (eq (char-after exp-beg) ?\{)
                (setq exp-depth (get-text-property exp-beg 'jsx-depth))
                (remove-list-of-text-properties exp-beg exp-end '(font-lock-face))
                (put-text-property exp-beg (1+ exp-beg) 'font-lock-face 'web-mode-block-delimiter-face)
                (when (and (eq (get-text-property exp-beg 'tag-attr-beg) 4) (web-mode-looking-at-p "\.\.\." (1+ exp-beg)))
                  (put-text-property exp-beg (+ exp-beg 4) 'font-lock-face 'web-mode-block-delimiter-face))
                (put-text-property exp-end (1+ exp-end) 'font-lock-face 'web-mode-block-delimiter-face)
                (web-mode-highlight-tags (1+ exp-beg) exp-end (1+ exp-depth))
                (web-mode-part-highlight (1+ exp-beg) exp-end exp-depth)
                (web-mode-fontify-region (1+ exp-beg) exp-end web-mode-javascript-font-lock-keywords)
                )
              (goto-char (1+ exp-beg))
              ) ;while exp

            (when (and elt-beg web-mode-jsx-depth-faces)
              (let (depth-beg depth-end jsx-face)
                (goto-char elt-beg)
                (while (setq pair (web-mode-jsx-depth-next reg-end))
                  ;;(message "depth-pair=%S" pair)
                  (setq depth-beg (car pair)
                        depth-end (cdr pair)
                        depth (get-text-property depth-beg 'jsx-depth)
                        jsx-face (elt web-mode-jsx-depth-faces (1- depth)))
                  ;;(message "%S" jsx-face)
                  (font-lock-prepend-text-property depth-beg (1+ depth-end) 'face jsx-face)
                  (goto-char (+ depth-beg 2))
                  )
                ) ;let
              )

            (goto-char (1+ elt-end))
            ) ;while elt
          ) ;let
        ) ;when

      ) ;let
    ) ;save-excursion
  )

(defun web-mode-css-rules-highlight (part-beg part-end)
  (save-excursion
    (goto-char part-beg)
    (let (rule (continue t) (i 0) (at-rule nil))
      (while continue
        (setq rule (web-mode-css-rule-next part-end))
        ;;(message "rule=%S" rule)
        (cond
         ((> (setq i (1+ i)) 1000)
          (message "css-rules-highlight ** too much rules **")
          (setq continue nil))
         ((null rule)
          (setq continue nil))
         ((and (setq at-rule (plist-get rule :at-rule))
               (not (member at-rule '("charset" "font-face" "import")))
               (plist-get rule :dec-end))
          (web-mode-css-rule-highlight (plist-get rule :sel-beg)
                                       (plist-get rule :sel-end)
                                       nil nil)
          (web-mode-css-rules-highlight (plist-get rule :dec-beg)
                                        (plist-get rule :dec-end)))
         (t
          (web-mode-css-rule-highlight (plist-get rule :sel-beg)
                                       (plist-get rule :sel-end)
                                       (plist-get rule :dec-beg)
                                       (plist-get rule :dec-end)))
         ) ;cond
        ) ;while
      ) ;let
    ))

(defun web-mode-css-rule-highlight (sel-beg sel-end dec-beg dec-end)
  (save-excursion
;;    (message "sel-beg=%S sel-end=%S dec-beg=%S dec-end=%S" sel-beg sel-end dec-beg dec-end)
    (web-mode-fontify-region sel-beg sel-end
                             web-mode-selector-font-lock-keywords)
    (when (and dec-beg dec-end)
      (web-mode-fontify-region dec-beg dec-end
                               web-mode-declaration-font-lock-keywords)
      (goto-char dec-beg)
      (while (and web-mode-enable-css-colorization
                  (re-search-forward "#[0-9a-fA-F]\\{6\\}\\|#[0-9a-fA-F]\\{3\\}\\|rgba?([ ]*\\([[:digit:]]\\{1,3\\}\\)[ ]*,[ ]*\\([[:digit:]]\\{1,3\\}\\)[ ]*,[ ]*\\([[:digit:]]\\{1,3\\}\\)\\(.*?\\))" dec-end t)
                  (< (point) dec-end))
        (web-mode-colorize (match-beginning 0) (match-end 0))
        )
      )))

(defun web-mode-fontify-region (beg end keywords)
;;  (message "beg=%S end=%S" beg end);; (symbol-name keywords))
  (save-excursion
    (let ((font-lock-keywords keywords)
          (font-lock-multiline nil)
          (font-lock-keywords-case-fold-search
           (member web-mode-engine '("asp" "template-toolkit")))
          (font-lock-keywords-only t)
          (font-lock-extend-region-functions nil))
      ;;      (message "%S" keywords)
      (when (listp font-lock-keywords)
        (font-lock-fontify-region beg end)
        )
      )
    ))

(defun web-mode-colorize-foreground (color)
  (let* ((values (x-color-values color))
	 (r (car values))
	 (g (cadr values))
	 (b (car (cdr (cdr values)))))
    (if (> 128.0 (floor (+ (* .3 r) (* .59 g) (* .11 b)) 256))
	"white" "black")))

(defun web-mode-colorize (beg end)
  (let (str plist len)
    (setq str (buffer-substring-no-properties beg end))
    (setq len (length str))
    (cond
     ((string= (substring str 0 1) "#")
      (setq plist (list :background str
                        :foreground (web-mode-colorize-foreground str)))
      (put-text-property beg end 'face plist))
     ((string= (substring str 0 4) "rgb(")
      (setq str (format "#%02X%02X%02X"
                        (string-to-number (match-string-no-properties 1))
                        (string-to-number (match-string-no-properties 2))
                        (string-to-number (match-string-no-properties 3))))
      (setq plist (list :background str
                        :foreground (web-mode-colorize-foreground str)))
      (put-text-property beg end 'face plist))
     ) ;cond
    ))

(defun web-mode-interpolate-block-tag (beg end)
  (save-excursion
    (goto-char (+ 4 beg))
    (setq end (1- end))
    (while (re-search-forward "${.*?}" end t)
      (remove-list-of-text-properties (match-beginning 0) (match-end 0) '(face))
      (web-mode-fontify-region (match-beginning 0) (match-end 0)
                               web-mode-uel-font-lock-keywords))
    ))

(defun web-mode-interpolate-javascript-string (beg end)
  (save-excursion
    (goto-char (1+ beg))
    (setq end (1- end))
    (while (re-search-forward "${.*?}" end t)
      (put-text-property (match-beginning 0) (match-end 0)
                         'font-lock-face
                         'web-mode-variable-name-face)
      )
    ))

;; todo : parsing plus compliqué: {$obj->values[3]->name}
(defun web-mode-interpolate-block-string (beg end)
  (save-excursion
    (goto-char (1+ beg))
    (setq end (1- end))
    (cond
     ((string= web-mode-engine "php")
      (while (re-search-forward "$[[:alnum:]_]+\\(->[[:alnum:]_]+\\)*\\|{[ ]*$.+?}" end t)
;;        (message "%S > %S" (match-beginning 0) (match-end 0))
        (remove-list-of-text-properties (match-beginning 0) (match-end 0) '(font-lock-face))
        (web-mode-fontify-region (match-beginning 0) (match-end 0)
                                 web-mode-php-var-interpolation-font-lock-keywords)
        ))
     ((string= web-mode-engine "erb")
      (while (re-search-forward "#{.*?}" end t)
        (remove-list-of-text-properties (match-beginning 0) (match-end 0) '(font-lock-face))
        (put-text-property (match-beginning 0) (match-end 0)
                           'font-lock-face 'web-mode-variable-name-face)
        ))
     ) ;cond
    ))

(defun web-mode-interpolate-comment (beg end block-side)
  (save-excursion
    (let ((regexp (concat "\\_<\\(" web-mode-comment-keywords "\\)\\_>")))
      (goto-char beg)
      (while (re-search-forward regexp end t)
        (font-lock-prepend-text-property (match-beginning 1) (match-end 1)
                                         'font-lock-face
                                         'web-mode-comment-keyword-face)
        ) ;while
      )))

(defun web-mode-interpolate-sql-string (beg end)
  (save-excursion
    (let ((case-fold-search t)
          (regexp (concat "\\_<\\(" web-mode-sql-keywords "\\)\\_>")))
      (goto-char beg)
      (while (re-search-forward regexp end t)
        (font-lock-prepend-text-property (match-beginning 1) (match-end 1)
                                         'font-lock-face
                                         'web-mode-sql-keyword-face)
        ) ;while
      )))

(defun web-mode-fill-paragraph (&optional justify)
  (save-excursion
    (let ((pos (point)) fill-coll
          prop pair beg end delim-beg delim-end chunk fill-col)
      (cond
       ((or (eq (get-text-property pos 'part-token) 'comment)
            (eq (get-text-property pos 'block-token) 'comment))
        (setq prop
              (if (get-text-property pos 'part-token) 'part-token 'block-token))
        (setq pair (web-mode-property-boundaries prop pos))
        (when (and pair (> (- (cdr pair) (car pair)) 6))
          (setq fill-coll (if (< fill-column 10) 70 fill-column))
          (setq beg (car pair)
                end (cdr pair))
          (goto-char beg)
          (setq chunk (buffer-substring-no-properties beg (+ beg 2)))
          (cond
           ((string= chunk "//")
            (setq delim-beg "//"
                  delim-end "EOL"))
           ((string= chunk "/*")
            (setq delim-beg "/*"
                  delim-end "*/"))
           ((string= chunk "{#")
            (setq delim-beg "{#"
                  delim-end "#}"))
           ((string= chunk "<!")
            (setq delim-beg "<!--"
                  delim-end "-->"))
           )
          )
        ) ;comment - case

       ((web-mode-is-content)
        (setq pair (web-mode-content-boundaries pos))
        (setq beg (car pair)
              end (cdr pair))
        )

       ) ;cond
;;      (message "beg(%S) end(%S)" beg end)
      (when (and beg end)
        (fill-region beg end))
      t)))

(defun web-mode-property-boundaries (prop &optional pos)
  "property boundaries (cdr is 1+)"
  (unless pos (setq pos (point)))
  (let (beg end val)
    (setq val (get-text-property pos prop))
    (if (null val)
        val
      (if (or (bobp)
              (not (eq (get-text-property (1- pos) prop) val)))
          (setq beg pos)
        (setq beg (previous-single-property-change pos prop))
        (when (null beg) (setq beg (point-min))))
      (if (or (eobp)
              (not (eq (get-text-property (1+ pos) prop) val)))
          (setq end pos)
        (setq end (next-single-property-change pos prop))
        (when (null end) (setq end (point-min))))
      (cons beg end))))

(defun web-mode-content-boundaries (&optional pos)
  (unless pos (setq pos (point)))
  (let (beg end)
    (setq beg (or (previous-property-change pos (current-buffer))
                  (point-max)))
    (setq end (or (next-property-change pos (current-buffer))
                  (point-min)))
    (while (and (< beg end) (member (char-after beg) '(?\s ?\n)))
      (setq beg (1+ beg)))
    (while (and (> end beg) (member (char-after (1- end)) '(?\s ?\n)))
      (setq end (1- end)))
;;    (message "beg(%S) end(%S)" beg end)
    (cons beg end)
    ))

(defun web-mode-engine-syntax-check ()
  (interactive)
  (let ((proc nil)
        (errors nil)
        (file (concat temporary-file-directory "emacs-web-mode-tmp")))
    (write-region (point-min) (point-max) file)
    (cond
     ;;       ((null (buffer-file-name))
     ;;        )
     ((string= web-mode-engine "php")
      (setq proc (start-process "php-proc" nil "php" "-l" file))
      (set-process-filter proc
                          (lambda (proc output)
                            (cond
                             ((string-match-p "No syntax errors" output)
                              (message "No syntax errors")
                              )
                             (t
;;                              (setq output (replace-regexp-in-string temporary-file-directory "" output))
;;                              (message output)
                              (message "Syntax error")
                              (setq errors t))
                             ) ;cond
;;                            (delete-file file)
                            ) ;lambda
                          )
      ) ;php
     (t
      (message "no syntax checker found")
      ) ;t
     ) ;cond
    errors))

(defun web-mode-jshint ()
  "Run JSHint on all the JavaScript parts."
  (interactive)
  (let (proc lines)
    (when (buffer-file-name)
      (setq proc (start-process
                  "jshint-proc"
                  nil
                  (or (executable-find "jshint") "/usr/local/bin/jshint")
                  "--extract=auto"
                  (buffer-file-name)))
      (setq web-mode-jshint-errors 0)
      (set-process-filter proc
                          (lambda (proc output)
                            (let ((offset 0) overlay pos (old 0) msg)
                              (remove-overlays (point-min) (point-max) 'font-lock-face 'web-mode-error-face)
                              (while (string-match
                                      "line \\([[:digit:]]+\\), col \\([[:digit:]]+\\), \\(.+\\)\\.$"
                                      output offset)
                                (setq web-mode-jshint-errors (1+ web-mode-jshint-errors))
                                (setq offset (match-end 0))
                                (setq pos (web-mode-coord-position
                                           (match-string-no-properties 1 output)
                                           (match-string-no-properties 2 output)))
                                (when (get-text-property pos 'tag-beg)
                                  (setq pos (1- pos)))
                                (when (not (= pos old))
                                  (setq old pos)
                                  (setq overlay (make-overlay pos (1+ pos)))
                                  (overlay-put overlay 'font-lock-face 'web-mode-error-face)
                                  )
                                (setq msg (or (overlay-get overlay 'help-echo)
                                               (concat "line="
                                                       (match-string-no-properties 1 output)
                                                       " column="
                                                       (match-string-no-properties 2 output)
                                                       )))
                                (overlay-put overlay 'help-echo
                                             (concat msg " ## " (match-string-no-properties 3 output)))
                                ) ;while
                              ))
                          )
      ) ;when
    ))

(defun web-mode-dom-errors-show ()
  "Show unclosed tags."
  (interactive)
  (let (beg end tag pos l n tags i cont cell overlay overlays first
            (ori (point))
            (errors 0)
            (continue t)
        )
    (setq overlays (overlays-in (point-min) (point-max)))
    (when overlays
      (dolist (overlay overlays)
        (when (eq (overlay-get overlay 'face) 'web-mode-warning-face)
          (delete-overlay overlay)
          )
        )
      )
    (goto-char (point-min))
    (when (not (or (get-text-property (point) 'tag-beg)
                   (web-mode-tag-next)))
      (setq continue nil))
    (while continue
      (setq pos (point))
      (setq tag (get-text-property pos 'tag-name))
      (cond
       ((eq (get-text-property (point) 'tag-type) 'start)
        (setq tags (add-to-list 'tags (list tag pos)))
;;        (message "(%S) opening %S" pos tag)
        )
       ((eq (get-text-property (point) 'tag-type) 'end)
        (setq i 0
              l (length tags)
              cont t)
        (while (and (< i l) cont)
          (setq cell (nth i tags))
;;          (message "cell=%S" cell)
          (setq i (1+ i))
          (cond
           ((string= tag (nth 0 cell))
            (setq cont nil)
            )
           (t
            (setq errors (1+ errors))
            (setq beg (nth 1 cell))
            (setq end (web-mode-tag-end-position beg))
            (unless first
              (setq first beg))
            (setq overlay (make-overlay beg (1+ end)))
            (overlay-put overlay 'font-lock-face 'web-mode-warning-face)
;;            (message "invalid <%S> at %S" (nth 0 cell) (nth 1 cell))
            )
           ) ;cond
          ) ;while

        (dotimes (i i)
          (setq tags (cdr tags)))

        )
       ) ;cond
      (when (not (web-mode-tag-next))
        (setq continue nil))
      ) ;while
    (message "%S error(s) detected" errors)
    (if (< errors 1)
        (goto-char ori)
      (goto-char first)
      (recenter))
    ;;    (message "%S" tags)
    ))

(defun web-mode-highlight-elements (beg end)
  (save-excursion
    (goto-char beg)
    (let ((continue (or (get-text-property (point) 'tag-beg) (web-mode-tag-next)))
          (i 0) (ctx nil) (face nil))
      (while continue
        (cond
         ((> (setq i (1+ i)) 1000)
          (message "highlight-elements ** too much tags **")
          (setq continue nil))
         ((> (point) end)
          (setq continue nil))
         ((not (get-text-property (point) 'tag-beg))
          (setq continue nil))
         ((eq (get-text-property (point) 'tag-type) 'start)
          (when (and (setq ctx (web-mode-element-boundaries (point)))
                     (<= (car (cdr ctx)) end)
                     (setq face (cdr (assoc (get-text-property (point) 'tag-name) web-mode-element-content-faces))))
            (font-lock-prepend-text-property (1+ (cdr (car ctx))) (car (cdr ctx))
                                             'font-lock-face face))
          )
         ) ;cond
        (when (not (web-mode-tag-next))
          (setq continue nil))
        ) ;while
      )))

(defun web-mode-enable (feature)
  "Enable one feature."
  (interactive
   (list (completing-read
          "Feature: "
          (let (features)
            (dolist (elt web-mode-features)
              (setq features (append features (list (car elt)))))
            features))))
  (when (and (or (not feature) (< (length feature) 1)) web-mode-last-enabled-feature)
    (setq feature web-mode-last-enabled-feature))
  (when feature
    (setq web-mode-last-enabled-feature feature)
    (setq feature (cdr (assoc feature web-mode-features)))
    (cond
     ((eq feature 'web-mode-enable-current-column-highlight)
      (web-mode-column-show))
     ((eq feature 'web-mode-enable-current-element-highlight)
      (when (not web-mode-enable-current-element-highlight)
        (web-mode-toggle-current-element-highlight))
      )
     ((eq feature 'web-mode-enable-whitespace-fontification)
      (web-mode-whitespaces-on))
     (t
      (set feature t)
      (web-mode-buffer-highlight))
     )
    ) ;when
  )

(defun web-mode-disable (feature)
  "Disable one feature."
  (interactive
   (list (completing-read
          "Feature: "
          (let (features)
            (dolist (elt web-mode-features)
              (setq features (append features (list (car elt)))))
            features))))
  (when (and (or (not feature) (< (length feature) 1)) web-mode-last-enabled-feature)
    (setq feature web-mode-last-enabled-feature))
  (when feature
    (setq feature (cdr (assoc feature web-mode-features)))
    (cond
     ((eq feature 'web-mode-enable-current-column-highlight)
      (web-mode-column-hide))
     ((eq feature 'web-mode-enable-current-element-highlight)
      (when web-mode-enable-current-element-highlight
        (web-mode-toggle-current-element-highlight))
      )
     ((eq feature 'web-mode-enable-whitespace-fontification)
      (web-mode-whitespaces-off))
     (t
      (set feature nil)
      (web-mode-buffer-highlight))
     )
    ) ;when
  )

(defun web-mode-make-tag-overlays ()
  (unless web-mode-overlay-tag-start
    (setq web-mode-overlay-tag-start (make-overlay 1 1)
          web-mode-overlay-tag-end (make-overlay 1 1))
    (overlay-put web-mode-overlay-tag-start
                 'font-lock-face
                 'web-mode-current-element-highlight-face)
    (overlay-put web-mode-overlay-tag-end
                 'font-lock-face
                 'web-mode-current-element-highlight-face)))

(defun web-mode-delete-tag-overlays ()
  (when web-mode-overlay-tag-start
    (delete-overlay web-mode-overlay-tag-start)
    (delete-overlay web-mode-overlay-tag-end)))

(defun web-mode-column-overlay-factory (index)
  (let (overlay)
    (when (null web-mode-column-overlays)
      (dotimes (i 100)
        (setq overlay (make-overlay 1 1))
        (overlay-put overlay 'font-lock-face 'web-mode-current-column-highlight-face)
        (setq web-mode-column-overlays (append web-mode-column-overlays (list overlay)))
        )
      ) ;when
    (setq overlay (nth index web-mode-column-overlays))
    (when (null overlay)
      (setq overlay (make-overlay 1 1))
      (overlay-put overlay 'font-lock-face 'web-mode-current-column-highlight-face)
      (setq web-mode-column-overlays (append web-mode-column-overlays (list overlay)))
      ) ;when
    overlay))

(defun web-mode-column-hide ()
  (setq web-mode-enable-current-column-highlight nil)
  (remove-overlays (point-min) (point-max)
                   'font-lock-face
                   'web-mode-current-column-highlight-face))

(defun web-mode-column-show ()
  (let ((index 0) overlay diff column line-to line-from)
    (web-mode-column-hide)
    (setq web-mode-enable-current-column-highlight t)
    (save-excursion
      (back-to-indentation)
      (setq column (current-column)
            line-to (web-mode-line-number))
      (when (and (get-text-property (point) 'tag-beg)
                 (member (get-text-property (point) 'tag-type) '(start end))
                 (web-mode-tag-match)
                 (setq line-from (web-mode-line-number))
                 (not (= line-from line-to)))
        (when (> line-from line-to)
          (let (tmp)
            (setq tmp line-from)
            (setq line-from line-to)
            (setq line-to tmp))
          ) ;when
        ;;(message "column(%S) line-from(%S) line-to(%S)" column line-from line-to)
        (goto-char (point-min))
        (when (> line-from 1)
          (forward-line (1- line-from)))
        (while (<= line-from line-to)
          (setq overlay (web-mode-column-overlay-factory index))
          (setq diff (- (line-end-position) (point)))
          (cond
           ((or (and (= column 0) (= diff 0))
                (> column diff))
            (end-of-line)
            (move-overlay overlay (point) (point))
            (overlay-put overlay
                         'after-string
                         (concat
                          (if (> column diff) (make-string (- column diff) ?\s) "")
                          (propertize " "
                                      'font-lock-face
                                      'web-mode-current-column-highlight-face)
                          ) ;concat
                         )
            )
           (t
            (move-to-column column)
            (overlay-put overlay 'after-string nil)
            (move-overlay overlay (point) (1+ (point)))
            )
           ) ;cond
          (setq line-from (1+ line-from))
          (forward-line)
          (setq index (1+ index))
          ) ;while
        ) ;when
      ) ;save-excursion
    ) ;let
  )

(defun web-mode-highlight-current-element ()
  (let ((ctx (web-mode-element-boundaries)) len)
    (cond
     ((null ctx)
      (web-mode-delete-tag-overlays))
     (t
      (web-mode-make-tag-overlays)
      (setq len (length (get-text-property (caar ctx) 'tag-name)))
      (move-overlay web-mode-overlay-tag-start (+ (caar ctx) 1) (+ (caar ctx) 1 len))
      (move-overlay web-mode-overlay-tag-end (+ (cadr ctx) 2) (+ (cadr ctx) 2 len))
      ) ;t
     ) ;cond
    ))

(defun web-mode-highlight-whitespaces (beg end)
  (save-excursion
    (goto-char beg)
    (while (re-search-forward web-mode-whitespaces-regexp end t)
      (add-text-properties (match-beginning 0) (match-end 0)
                           '(face web-mode-whitespace-face))
      ) ;while
    ))

(defun web-mode-whitespaces-show ()
  "Toggle whitespaces."
  (interactive)
  (if web-mode-enable-whitespace-fontification
      (web-mode-whitespaces-off)
    (web-mode-whitespaces-on)))

(defun web-mode-whitespaces-on ()
  "Show whitespaces."
  (interactive)
  (when web-mode-display-table
    (setq buffer-display-table web-mode-display-table))
  (setq web-mode-enable-whitespace-fontification t))

(defun web-mode-whitespaces-off ()
  (setq buffer-display-table nil)
  (setq web-mode-enable-whitespace-fontification nil))

(defun web-mode-use-tabs ()
  "Tweaks vars to be compatible with TAB indentation."
  (let (offset)
    (setq web-mode-block-padding 0)
    (setq web-mode-script-padding 0)
    (setq web-mode-style-padding 0)
    (setq offset
          (cond
           ((and (boundp 'tab-width) tab-width) tab-width)
           ((and (boundp 'standard-indent) standard-indent) standard-indent)
           (t 4)))
    ;;    (message "offset(%S)" offset)
    (setq web-mode-attr-indent-offset offset)
    (setq web-mode-code-indent-offset offset)
    (setq web-mode-css-indent-offset offset)
    (setq web-mode-markup-indent-offset offset)
    (setq web-mode-sql-indent-offset offset)
    (add-to-list 'web-mode-indentation-params '("lineup-args" . nil))
    (add-to-list 'web-mode-indentation-params '("lineup-calls" . nil))
    (add-to-list 'web-mode-indentation-params '("lineup-concats" . nil))
    (add-to-list 'web-mode-indentation-params '("lineup-ternary" . nil))
    ))

(defun web-mode-buffer-indent ()
  "Indent all buffer."
  (interactive)
  (indent-region (point-min) (point-max))
  (delete-trailing-whitespace))

(defun web-mode-buffer-change-tag-case (&optional type)
  "Change html tag case."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (let ((continue t) f)
      (setq f (if (member type '("upper" "uppercase" "upper-case")) 'uppercase 'downcase))
      (when (and (not (get-text-property (point) 'tag-beg))
                 (not (web-mode-tag-next)))
        (setq continue nil))
      (while continue
        (skip-chars-forward "<!/")
        (if (looking-at "\\([[:alnum:]:-]+\\)")
            (replace-match (funcall f (match-string 0)) t))
;;        (message "tag: %S (%S)"
;;                 (get-text-property (point) 'tag-name)
;;                 (point))
        (unless (web-mode-tag-next)
          (setq continue nil))
        ) ;while
      )))

(defun web-mode-buffer-change-attr-case (&optional type)
  "Change case of html attribute names."
  (interactive)
  (unless type (setq type "downcase"))
  (save-excursion
    (goto-char (point-min))
    (let ((continue t)
          (fun (if (eq (aref (downcase type) 0) ?u) 'uppercase 'downcase)))
      (while continue
        (cond
         ((not (web-mode-attribute-next))
          (setq continue nil))
         ((looking-at "\\([[:alnum:]-]+\\)")
          (replace-match (funcall fun (match-string 0)) t)
          )
         ) ;cond
        ) ;while
      )))

;; todo : passer de règle en règle et mettre un \n à la fin
(defun web-mode-css-indent ()
  (save-excursion
    (goto-char (point-min))
    (let ((continue t) rule part-end)
      (while continue
        (cond
         ((not (web-mode-part-next))
          (setq continue nil))
         ((eq (get-text-property (point) 'part-side) 'css)
          (setq part-end (web-mode-part-end-position))
          (while (setq rule (web-mode-css-rule-next part-end))
            (when (not (looking-at-p "[[:space:]]*\\($\\|<\\)"))
              (newline)
              (indent-according-to-mode)
              (setq part-end (web-mode-part-end-position)))
            )
          )
         ) ;cond
        )
      )))

;; tag-case=lower|upper-case , attr-case=lower|upper-case
;; special-chars=unicode|html-entities
;; smart-apostrophes=bool , smart-quotes=bool , indentation=bool
(defun web-mode-dom-normalize ()
  "Normalize buffer"
  (interactive)
  (save-excursion
    (let ((rules web-mode-normalization-rules) elt)
      (when (setq elt (cdr (assoc "tag-case" rules)))
        (web-mode-buffer-change-tag-case elt))
      (when (setq elt (cdr (assoc "attr-case" rules)))
        (web-mode-buffer-change-attr-case elt))
      (when (setq elt (cdr (assoc "css-indentation" rules)))
        (web-mode-css-indent))
      (when (setq elt (cdr (assoc "smart-apostrophes" rules)))
        (web-mode-dom-apostrophes-replace))
      (when (setq elt (cdr (assoc "smart-quotes" rules)))
        (web-mode-dom-quotes-replace))
      (when (setq elt (cdr (assoc "special-chars" rules)))
        (if (string= elt "entities")
            (web-mode-dom-entities-encode)
          (web-mode-dom-entities-replace)))
      (when (setq elt (cdr (assoc "whitespaces" rules)))
        (goto-char (point-min))
        (while (not (eobp))
          (forward-line)
          (delete-blank-lines))
        (delete-trailing-whitespace)
        (untabify (point-min) (point-max)))
      (when (setq elt (cdr (assoc "indentation" rules)))
        (web-mode-buffer-indent))
      )))

;;---- INDENTATION -------------------------------------------------------------

(defun web-mode-point-context (pos)
  "POS should be at the beginning of the indentation."
  (save-excursion
    (let (curr-char curr-indentation curr-line
          language
          options
          reg-beg reg-col
          prev-char prev-indentation prev-line prev-pos
          token
          part-language
          depth)

      (setq reg-beg (point-min)
            reg-col 0
            token "live"
            options ""
            language ""
            prev-line ""
            prev-char 0
            prev-pos nil)

      (when (get-text-property pos 'part-side)
        (setq part-language (symbol-name (get-text-property pos 'part-side))))

      (cond

       ((and (bobp) (member web-mode-content-type '("html" "xml")))
        (setq language web-mode-content-type)
        )

       ((string= web-mode-content-type "css")
        (setq language "css"
              curr-indentation web-mode-css-indent-offset))

       ((member web-mode-content-type '("javascript" "json"))
        (setq language "javascript"
              curr-indentation web-mode-code-indent-offset))

       ((or (string= web-mode-content-type "jsx")
            (and part-language (string= part-language "jsx")))
        (setq language "jsx"
              curr-indentation web-mode-code-indent-offset)
        (cond
         ((web-mode-jsx-is-html pos)
          (setq curr-indentation web-mode-markup-indent-offset
                options "is-html"))
         ((and (setq depth (get-text-property pos 'jsx-depth)) (> depth 1))
          (when (get-text-property pos 'jsx-beg)
            (setq depth (1- depth)))
          (setq reg-beg (web-mode-jsx-depth-beginning-position pos depth))
          (setq reg-beg (1+ reg-beg))
          (save-excursion
            (goto-char reg-beg)
            (cond
             ((and (not (looking-at-p "[ ]*$"))
                   (looking-back "^[[:space:]]*{"))
              (setq reg-col (+ (current-indentation) 1
                               (cond
                                ((looking-at "[ ]+") (length (match-string-no-properties 0)))
                                (t 0))
                               ))
              )
             ((looking-at-p "[ ]*\\[[ ]*$") ;; #0659
              (setq reg-col (current-indentation))
             )
             (t
              ;;(message "%S %S : %S %S" (point) (current-indentation) web-mode-code-indent-offset)
              ;;(setq reg-col (+ (current-indentation) web-mode-code-indent-offset web-mode-jsx-expression-padding)))
              (setq reg-col (+ (current-indentation) web-mode-code-indent-offset)))
             )

            ;;(message "%S %S %S" (point) (current-indentation) reg-col)
            ) ;save-excursion
          )
         ((string= web-mode-content-type "jsx")
          (setq reg-beg (point-min)))
         (t
          (setq reg-beg (or (web-mode-part-beginning-position pos) (point-min)))
          (save-excursion
            (goto-char reg-beg)
            (search-backward "<" nil t)
            (setq reg-col (current-column))
            ) ;save-excursion
          )
         ) ;cond
        ;;(message "jsx reg-beg=%S" reg-beg)
        ) ;jsx

       ((string= web-mode-content-type "php")
        (setq language "php"
              curr-indentation web-mode-code-indent-offset))

       ((or (string= web-mode-content-type "xml"))
        (setq language "xml"
              curr-indentation web-mode-markup-indent-offset))

       ;; TODO: est ce util ?
       ((and (get-text-property pos 'tag-beg)
             (get-text-property pos 'tag-name)
             ;;(not (get-text-property pos 'part-side))
             )
        (setq language "html"
              curr-indentation web-mode-markup-indent-offset))

       ((and (get-text-property pos 'block-side)
             (not (get-text-property pos 'block-beg)))

        (setq reg-beg (or (web-mode-block-beginning-position pos) (point-min)))
        (goto-char reg-beg)
        (setq reg-col (current-column))
        (setq language web-mode-engine)
        (setq curr-indentation web-mode-code-indent-offset)

        (cond
         ((string= web-mode-engine "blade")
          (save-excursion
            (when (web-mode-rsf "{[{!]+[ ]*")
              (setq reg-col (current-column))))
          (setq reg-beg (+ reg-beg 2))
          )
         ((string= web-mode-engine "razor")
          (setq reg-beg (+ reg-beg 2))
          )
         ;; tests/demo.chtml
         ((string= web-mode-engine "ctemplate")
          (save-excursion
            (when (web-mode-rsf "{{#?")
              (setq reg-col (current-column))))
          )
         ((string= web-mode-engine "dust")
          (save-excursion
            (when (web-mode-rsf "{@")
              (setq reg-col (current-column))))
          )
         ((string= web-mode-engine "template-toolkit")
          (setq reg-beg (+ reg-beg 3)
                reg-col (+ reg-col 3))
          )
         ((and (string= web-mode-engine "jsp")
               ;;(web-mode-looking-at "<%@\\|<[[:alpha:]]" reg-beg))
               (web-mode-looking-at "<%@" reg-beg))
          (save-excursion
            (goto-char reg-beg)
            (looking-at "<%@[ ]*[[:alpha:]]+[ ]+\\|</?[[:alpha:]]+[:.][[:alpha:]]+[ ]+")
            (goto-char (match-end 0))
            (setq reg-col (current-column))
            )
          )
         ((and (string= web-mode-engine "freemarker")
               (web-mode-looking-at "<@\\|<%@\\|<[[:alpha:]]" reg-beg))
          (save-excursion
            (goto-char reg-beg)
            (looking-at "<@[[:alpha:].]+[ ]+\\|<%@[ ]*[[:alpha:]]+[ ]+\\|<[[:alpha:]]+:[[:alpha:]]+[ ]+")
            (goto-char (match-end 0))
            (setq reg-col (current-column))
            )
          )
         ) ;cond
        ) ;block-side

       ((and part-language (member part-language '("css" "javascript")))
        (setq reg-beg (or (web-mode-part-beginning-position pos) (point-min)))
        (goto-char reg-beg)
        (search-backward "<" nil t)
        (setq reg-col (current-column))
        (setq language part-language)
        (cond
         ((string= language "css")
          (setq curr-indentation web-mode-css-indent-offset))
         (t
          (setq language "javascript"
                curr-indentation web-mode-code-indent-offset))
         )
        ) ;part-side

       (t
        (setq language "html"
              curr-indentation web-mode-markup-indent-offset)
        )

       ) ;cond

      (cond
       ((or (and (> pos (point-min))
                 (eq (get-text-property pos 'part-token) 'comment)
                 (eq (get-text-property (1- pos) 'part-token) 'comment)
                 (progn
                   (setq reg-beg (previous-single-property-change pos 'part-token))
                   t))
            (and (> pos (point-min))
                 (eq (get-text-property pos 'block-token) 'comment)
                 (eq (get-text-property (1- pos) 'block-token) 'comment)
                 (progn
                   (setq reg-beg (previous-single-property-change pos 'block-token))
                   t))
            (and (> pos (point-min))
                 (eq (get-text-property pos 'tag-type) 'comment)
                 (not (get-text-property pos 'tag-beg))
                 (progn
                   (setq reg-beg (web-mode-tag-beginning-position pos))
                   t))
            )
        (setq token "comment"))
       ((or (and (> pos (point-min))
                 (member (get-text-property pos 'part-token)
                         '(string context key))
                 (member (get-text-property (1- pos) 'part-token)
                         '(string context key)))
            (and (eq (get-text-property pos 'block-token) 'string)
                 (eq (get-text-property (1- pos) 'block-token) 'string)))
        (setq token "string"))
       )

      (goto-char pos)
      (setq curr-line (web-mode-trim
                       (buffer-substring-no-properties
                        (line-beginning-position)
                        (line-end-position))))
      (setq curr-char (if (string= curr-line "") 0 (aref curr-line 0)))

      (when (or (member language '("php" "blade" "javascript" "jsx" "razor"))
                (and (member language '("html" "xml"))
                     (not (eq ?\< curr-char))))
        (let (prev)
          (cond
           ((member language '("html" "xml" "javascript" "jsx"))
            (when (setq prev (web-mode-part-previous-live-line reg-beg))
              (setq prev-line (nth 0 prev)
                    prev-indentation (nth 1 prev)
                    prev-pos (nth 2 prev))
              )
            )
           ((setq prev (web-mode-block-previous-live-line))
            (setq prev-line (car prev)
                  prev-indentation (cdr prev))
            (setq prev-line (web-mode-clean-block-line prev-line)))
           ) ;cond
          ) ;let
        (when (>= (length prev-line) 1)
          (setq prev-char (aref prev-line (1- (length prev-line))))
          (setq prev-line (substring-no-properties prev-line))
          )
        )

      (cond
       ((not (member web-mode-content-type '("html" "xml")))
        )
       ((member language '("javascript" "jsx"))
        (setq reg-col (+ reg-col web-mode-script-padding)))
       ((member language '("css"))
        (setq reg-col (+ reg-col web-mode-style-padding)))
       ((not (member language '("html" "xml" "razor")))
        (setq reg-col (+ reg-col web-mode-block-padding)))
       )

      (list :curr-char curr-char
            :curr-indentation curr-indentation
            :curr-line curr-line
            :language language
            :options options
            :prev-char prev-char
            :prev-indentation prev-indentation
            :prev-line prev-line
            :prev-pos prev-pos
            :reg-beg reg-beg
            :reg-col reg-col
            :token token)
      )))

(defun web-mode-indent-line ()

  (web-mode-propertize)

  (let ((offset nil)
        (char nil)
        (inhibit-modification-hooks t)
        (adjust t))

    (save-excursion
      (back-to-indentation)
      (setq char (char-after))
      (let* ((pos (point))
             (ctx (web-mode-point-context pos))
             (curr-char (plist-get ctx :curr-char))
             (curr-indentation (plist-get ctx :curr-indentation))
             (curr-line (plist-get ctx :curr-line))
             (language (plist-get ctx :language))
             (prev-char (plist-get ctx :prev-char))
             (prev-indentation (plist-get ctx :prev-indentation))
             (prev-line (plist-get ctx :prev-line))
             (prev-pos (plist-get ctx :prev-pos))
             (reg-beg (plist-get ctx :reg-beg))
             (reg-col (plist-get ctx :reg-col))
             (token (plist-get ctx :token))
             (options (plist-get ctx :options))
             (chars (list curr-char prev-char)))

        ;;(message "curr-char=[%c] prev-char=[%c]\n%S" curr-char prev-char ctx)

        (cond

         ((or (bobp) (= (line-number-at-pos pos) 1))
          (setq offset 0))

         ((string= token "string")
          (cond
           ((and web-mode-enable-sql-detection
                 (web-mode-block-token-starts-with (concat "[ \n]*" web-mode-sql-queries)))
            (save-excursion
              (let (col)
                (web-mode-block-string-beginning)
                (skip-chars-forward "[ \"'\n]")
                (setq col (current-column))
                (goto-char pos)
                (if (looking-at-p "\\(SELECT\\|INSERT\\|DELETE\\|UPDATE\\|FROM\\|LEFT\\|JOIN\\|WHERE\\|GROUP BY\\|LIMIT\\|HAVING\\|\)\\)")
                    (setq offset col)
                  (setq offset (+ col web-mode-sql-indent-offset)))
                )
              ) ;save-excursion
            )
           (t
            (setq offset nil))
           ) ;cond
          ) ;case string

         ((string= token "comment")
          (if (eq (get-text-property pos 'tag-type) 'comment)
              (web-mode-tag-beginning)
            (goto-char (car
                        (web-mode-property-boundaries
                         (if (eq (get-text-property pos 'part-token) 'comment)
                             'part-token
                           'block-token)
                         pos))))
          (setq offset (current-column))
          (cond
           ((string= web-mode-engine "freemarker")
            (setq offset (+ (current-indentation) 2)))
           ((member (buffer-substring-no-properties (point) (+ (point) 2)) '("/*" "{*" "@*"))
            (cond
             ((eq ?\* curr-char)
              (setq offset (+ offset 1)))
             (t
              (setq offset (+ offset 3)))
             ) ;cond
            )
           ((string= (buffer-substring-no-properties (point) (+ (point) 4)) "<!--")
            (cond
             ((string-match-p "^<!\\[endif" curr-line)
              )
             ((looking-at-p "<!--\\[if")
              (setq offset (+ offset web-mode-markup-indent-offset)))
             ((eq ?\- curr-char)
              (setq offset (+ offset 3)))
             (t
              (setq offset (+ offset 5)))
             ) ;cond
            )
           ((and (string= web-mode-engine "django") (looking-back "{% comment %}"))
            (setq offset (- offset 12)))
           ((and (string= web-mode-engine "mako") (looking-back "<%doc%>"))
            (setq offset (- offset 6)))
           ((and (string= web-mode-engine "mason") (looking-back "<%doc%>"))
            (setq offset (- offset 6)))
           ) ;cond
          ) ;case comment

         ((and (string= web-mode-engine "mason")
               (string-match-p "^%" curr-line))
          (setq offset 0))

         ((and (get-text-property pos 'block-beg)
               (or (web-mode-block-is-close pos)
                   (web-mode-block-is-inside pos)))
          (when (web-mode-block-match)
            (setq offset (current-indentation))))

         ((eq (get-text-property pos 'block-token) 'delimiter-end)
          (when (web-mode-block-beginning)
            (setq reg-col (current-indentation))
            (setq offset (current-column))))

         ((and (get-text-property pos 'tag-beg)
               (eq (get-text-property pos 'tag-type) 'end))
          (when (web-mode-tag-match)
            (setq offset (current-indentation))))

         ((and (member language '("jsx"))
               (eq curr-char ?\})
               (get-text-property pos 'jsx-end))
          (web-mode-go (1- reg-beg))
          (setq reg-col nil)
          (setq offset (current-column)))

         ((and (member language '("html" "xml" "javascript" "jsx"))
               (get-text-property pos 'tag-type)
               (not (get-text-property pos 'tag-beg))
               (or (not (string= language "jsx"))
                   (string= options "is-html")))
          ;;(message "html-attr")
          (cond
           ((and (get-text-property pos 'tag-attr)
                 (get-text-property (1- pos) 'tag-attr)
                 (web-mode-attribute-beginning))

            (cond
             ((eq (logand (get-text-property (point) 'tag-attr-beg) 8) 8)
              (setq offset nil))
             ((and web-mode-attr-value-indent-offset (web-mode-tag-beginning))
              (setq offset (+ (current-column) web-mode-attr-value-indent-offset)))
             (t
              (web-mode-dom-rsf "=[ ]*[\"']?" pos)
              (setq offset (current-column)))
             ) ;cond

            )
           ((not (web-mode-tag-beginning))
            )
           ((string-match-p "^/?>" curr-line)
            (setq offset (current-column)))
           (web-mode-attr-indent-offset
            (setq offset (+ (current-column) web-mode-attr-indent-offset)))
           ((looking-at-p (concat web-mode-start-tag-regexp "[ ]*\n"))
            (setq offset (+ (current-column) (or web-mode-attr-indent-offset 4))))
           ((web-mode-attribute-next)
            (setq offset (current-column)))
           ) ;cond
          )

         ((or (member language '("html" "xml"))
              (and (member language '("jsx"))
                   (string= options "is-html")))
          ;;(message "html")
          (cond
           ((get-text-property pos 'tag-beg)
            (setq offset (web-mode-markup-indentation pos))
            )
           ((and web-mode-indentless-elements
                 (not (string= language "jsx"))
                 (null (get-text-property pos 'block-side))
                 (null (get-text-property pos 'part-side))
                 (and (null (get-text-property pos 'tag-beg))
                      (save-excursion
                        (and (web-mode-element-parent)
                             (member (get-text-property (point) 'tag-name) web-mode-indentless-elements))))
                 )
            (setq offset nil))
           ((or (eq (length curr-line) 0)
                (= web-mode-indent-style 2)
                (get-text-property pos 'tag-beg)
                (get-text-property pos 'reg-beg))
            (setq offset (web-mode-markup-indentation pos))
            )
           )
          )

         ((string= language "ctemplate")
          (setq offset reg-col))

         ((member language '("mako" "web2py"))
          (setq offset (web-mode-python-indentation pos
                                                    curr-line
                                                    reg-col
                                                    curr-indentation
                                                    reg-beg)))

         ((string= language "asp")
          (setq offset (web-mode-asp-indentation pos
                                                 curr-line
                                                 reg-col
                                                 curr-indentation
                                                 reg-beg)))

         ((member language '("lsp" "cl-emb"))
          (setq offset (web-mode-lisp-indentation pos ctx)))

         ((member curr-char '(?\} ?\) ?]))
          (let (ori)
            (if (get-text-property pos 'block-side)
                (setq ori (web-mode-block-opening-paren-position pos reg-beg))
              (setq ori (web-mode-part-opening-paren-position pos reg-beg)))
            (cond
             ((null ori)
              (setq offset reg-col))
             ((and (goto-char ori)
                   (looking-back ")[ ]*") ;; peut-on se passer du looking-back ?
                   (re-search-backward ")[ ]*" nil t)
                   (web-mode-block-opening-paren reg-beg))
              (back-to-indentation)
              (setq offset (current-indentation))
              )
             (t
              (goto-char ori)
              (back-to-indentation)
              (setq offset (current-indentation))
              (when (get-text-property pos 'jsx-end)
                (setq adjust nil))
              ) ;t
             ) ;cond
            ) ;let
          )

         ((string= language "erb")
          (setq offset (web-mode-ruby-indentation pos
                                                  curr-line
                                                  reg-col
                                                  curr-indentation
                                                  reg-beg)))

         ((string= language "css")
          (setq offset (car (web-mode-css-indentation pos
                                                      reg-col
                                                      curr-indentation
                                                      language
                                                      reg-beg))))

         ((and (string= language "razor")
               (string-match-p "^\\." curr-line)
               (string-match-p "^\\." prev-line))
          (setq offset prev-indentation))

         ((and (string= language "razor")
               (string-match-p "^case " curr-line)
               (string-match-p "^case " prev-line))
          (search-backward "case ")
          (setq offset (current-column)))

         ;; TODO : prev-pos : se plasser sur ), remonter sur ( et
         ;; verifer que ca n'est pas if
         ((and (member language '("javascript" "jsx" "ejs" "php"))
               (or (and (eq prev-char ?\))
                        (string-match-p "^\\(for\\|if\\|while\\)[ ]*(" prev-line)
;;                        (progn (message "%S" (point)) t)
                        )
                   (and (member language '("javascript" "jsx"))
                        (web-mode-part-is-opener prev-pos reg-beg))
                   (string-match-p "^else$" prev-line))
               (not (string-match-p "^\\([{.]\\|->\\)" curr-line)))
          ;;(message "ici")
          (cond
           ((and (eq prev-char ?\))
                 (string-match-p "^\\(for\\|if\\|while\\)[ ]*(" prev-line))
            (setq offset (+ prev-indentation web-mode-code-indent-offset))
            )
           ((member language '("javascript" "jsx" "ejs"))
            (setq offset
                  (+ (car (web-mode-javascript-indentation pos
                                                           reg-col
                                                           curr-indentation
                                                           language
                                                           reg-beg))
                     web-mode-code-indent-offset))
            )
           (t
            (setq offset (+ prev-indentation web-mode-code-indent-offset))
            )
           )
          )

         ((and (member language '("javascript" "jsx" "ejs"))
               (member ?\. chars)
               (not (string-match-p "^\\.\\.\\." curr-line)))
          (let (pair)
            (setq pair (web-mode-javascript-calls-beginning-position pos reg-beg))
            (when pair
              (goto-char (car pair))
              ;;(message "%S %S" (point) pair)
              (cond
               ((cdr (assoc "lineup-calls" web-mode-indentation-params))
                ;;(search-forward ".")
                (if (cdr pair)
                    (progn
                      (goto-char (cdr pair))
                      (setq offset (current-column))
                      (looking-at "\\.\\([ \t\n]*\\)")
                      (setq offset (- offset (length (match-string-no-properties 1))))
                      (unless (eq curr-char ?\.) (setq offset (1+ offset)))
                      ) ;progn
                  ;; TODO: cela devrait etre fait dans web-mode-javascript-calls-beginning-position
                  (skip-chars-forward " \t\n")
                  (setq offset (+ (current-indentation) web-mode-code-indent-offset))
                  ) ;if
                )
               (t
                (setq offset (+ (current-indentation) web-mode-code-indent-offset))
                ) ;t
               ) ;cond
              ) ;when
            ) ;let
          )

         ((and (member language '("javascript" "jsx" "ejs"))
               (member ?\+ chars))
          ;;(message "js-concat")
          (cond
           ((not (web-mode-javascript-string-beginning pos reg-beg))
            )
           ((null (cdr (assoc "lineup-concats" web-mode-indentation-params)))
            (setq offset (+ (current-indentation) web-mode-code-indent-offset)))
           ((not (eq curr-char ?\+))
            (setq offset (current-column)))
           (t
            (setq offset (current-column))
            (goto-char pos)
            (looking-at "\\+[ \t\n]*")
            (setq offset (- offset (length (match-string-no-properties 0))))
            )
           )
          )

         ;; #579
         ((and (member language '("javascript" "jsx" "ejs" "php"))
               (string-match-p "=>$" prev-line))
          (setq offset (+ prev-indentation web-mode-code-indent-offset))
          ;;(message "ici%S" offset)
          )

         ;; #446, #638
         ((and (member language '("javascript" "jsx" "ejs" "php"))
               (or (string-match-p "[&|?:+-]$" prev-line)
                   (string-match-p "^[&|?:+-]" curr-line))
               (not (and (string= language "php")
                         (string-match-p "^->" curr-line)))
               (not (and (eq prev-char ?\:)
                         (string-match-p "^\\(case\\|default\\)" prev-line))))
          (cond
           ((not (funcall (if (member language '("javascript" "jsx" "ejs"))
                              'web-mode-javascript-statement-beginning
                            'web-mode-block-statement-beginning)
                          pos reg-beg))
            )
           ((null (cdr (assoc "lineup-ternary" web-mode-indentation-params)))
            (setq offset (+ (current-indentation) web-mode-code-indent-offset)))
           (t
            (setq offset (current-column))
            (when (member curr-char '(?\+ ?\- ?\& ?\| ?\? ?\:))
              (goto-char pos)
              (looking-at "\\(||\\|&&\\|[&|?:+-]\\)[ \t\n]*")
              (setq offset (- offset (length (match-string-no-properties 0)))))
            )
           ) ;cond
          )

         ((and (member language '("javascript" "jsx" "ejs"))
               (or (member ?\, chars)
                   (member prev-char '(?\( ?\[))))
          (cond
           ((not (web-mode-javascript-args-beginning pos reg-beg))
            (message "no js args beg")
            )
           ((or (not (cdr (assoc "lineup-args" web-mode-indentation-params)))
                (looking-at-p "\n"))
            (if (and reg-col (> reg-col (current-indentation)))
                (setq offset (+ reg-col web-mode-code-indent-offset))
              (setq offset (+ (current-indentation) web-mode-code-indent-offset)))
            )
           ((not (eq curr-char ?\,))
            (setq offset (current-column)))
           (t
            (setq offset (current-column))
            (goto-char pos)
            (looking-at ",[ \t\n]*")
            (setq offset (- offset (length (match-string-no-properties 0)))))
           ))

         ((and (member language '("php" "blade")) (string-match-p "^->" curr-line))
          (cond
           ((not (web-mode-block-calls-beginning pos reg-beg))
            )
           ((cdr (assoc "lineup-calls" web-mode-indentation-params))
            ;;(message "point=%S" (point))
            (if (looking-back "::[ ]*")
                (progn
                  (re-search-backward "::[ ]*")
                  (setq offset (current-column))
                  ;;(message "ici%S offset=%S" (point) offset)
                  )
              (search-forward "->")
              (setq offset (- (current-column) 2)))
            )
           (t
            (setq offset (+ (current-indentation) web-mode-code-indent-offset)))
           ))

         ((member ?\, chars)
          (cond
           ((not (web-mode-block-args-beginning pos reg-beg))
            )
           ((cdr (assoc "lineup-args" web-mode-indentation-params))
            (setq offset (current-column))
            (when (eq curr-char ?\,)
              (goto-char pos)
              (looking-at ",[ \t\n]*")
              (setq offset (- offset (length (match-string-no-properties 0)))))
            )
           (t
            (setq offset (+ (current-indentation) web-mode-code-indent-offset)))
           ))

         ((and (string= language "php") (member ?\. chars))
          (cond
           ((not (web-mode-block-string-beginning pos reg-beg))
            )
           ((null (cdr (assoc "lineup-concats" web-mode-indentation-params)))
            (setq offset (+ (current-indentation) web-mode-code-indent-offset)))
           ((not (eq curr-char ?\.))
            ;;(message "%S" (point))
            (setq offset (current-column)))
           (t
            (setq offset (current-column))
            (goto-char pos)
            (when (cdr (assoc "lineup-quotes" web-mode-indentation-params))
              (looking-at "\\.[ \t\n]*")
              (setq offset (- offset (length (match-string-no-properties 0)))))
            )))

         ((member language '("javascript" "jsx" "ejs" "underscore"))
          ;;(message "js-indent")
          (setq offset (car (web-mode-javascript-indentation pos
                                                             reg-col
                                                             curr-indentation
                                                             language
                                                             reg-beg))))

         (t
          ;;(message "ici")
          (setq offset (car (web-mode-bracket-indentation pos
                                                          reg-col
                                                          curr-indentation
                                                          language
                                                          reg-beg))))

         ) ;cond

        (when (and offset reg-col adjust (< offset reg-col)) (setq offset reg-col))

        ) ;let
      ) ;save-excursion

    (when offset
      (let ((diff (- (current-column) (current-indentation))))
        (when (not (= offset (current-indentation)))
          (setq web-mode-change-beg (line-beginning-position)
                web-mode-change-end (+ web-mode-change-beg offset)))
        (setq offset (max 0 offset))
        (indent-line-to offset)
        (if (> diff 0) (move-to-column (+ (current-column) diff)))
        (when (and (string= web-mode-engine "mason")
                   (= offset 0)
                   (eq char ?\%))
          (save-excursion
            (font-lock-fontify-region (line-beginning-position) (line-end-position)))
          ) ;when
        ) ;let
      ) ;when

    ))

(defun web-mode-markup-indentation (pos)
  (let ((offset 0) beg ret)
    (when (setq beg (web-mode-markup-indentation-origin pos))
      (when (and (get-text-property pos 'jsx-depth)
                 (not (get-text-property beg 'jsx-depth)))
        (setq beg (web-mode-jsx-depth-beginning-position pos)))
      (cond
       ((null (setq ret (web-mode-element-is-opened beg pos)))
        (setq offset (web-mode-indentation-at-pos beg)))
       ((eq ret t)
        (setq offset (+ (web-mode-indentation-at-pos beg) web-mode-markup-indent-offset)))
       (t
        (setq offset ret))
       ) ;cond
      ) ;when beg
    offset))

(defun web-mode-css-indentation (pos initial-column language-offset language &optional limit)
  (let ((open-ctx (web-mode-bracket-up pos language limit)) offset)
    (cond
     ((or (null open-ctx) (null (plist-get open-ctx :pos)))
      (setq offset initial-column))
     (t
      (setq offset (+ (plist-get open-ctx :indentation) language-offset)))
     ) ;cond
    (cons (if (< offset initial-column) initial-column offset) open-ctx)
    ))

(defun web-mode-javascript-indentation (pos initial-column language-offset language &optional limit)
  (let ((open-ctx (web-mode-bracket-up pos language limit)) indentation offset sub)
    ;;(message "pos(%S) initial-column(%S) language-offset(%S) language(%S) limit(%S)" pos initial-column language-offset language limit)
    ;;(message "javascript-indentation: %S\nchar=%c" open-ctx (plist-get open-ctx :char))
    (setq indentation (plist-get open-ctx :indentation))
    (when (and initial-column (> initial-column indentation))
      (setq indentation initial-column)
      )
    (cond
     ((or (null open-ctx) (null (plist-get open-ctx :pos)))
      (setq offset initial-column))
     ((and (member language '("javascript" "jsx" "ejs"))
           (eq (plist-get open-ctx :char) ?\{)
           (web-mode-looking-back "switch[ ]*(.*)[ ]*" (plist-get open-ctx :pos)))
      (setq sub (if (cdr (assoc "case-extra-offset" web-mode-indentation-params)) 0 1))
      (cond
       ((looking-at-p "case\\|default")
        (setq offset (+ indentation (* language-offset (- 1 sub)))))
       (t
        (setq offset (+ indentation (* language-offset (- 2 sub)))))
       ) ;cond switch
      )
     (t
      (setq offset (+ indentation language-offset)))
     ) ;cond
    (cons (if (< offset initial-column) initial-column offset) open-ctx)
    ))

(defun web-mode-bracket-indentation (pos initial-column language-offset language &optional limit)
  (save-excursion
    (let* ((ctx (web-mode-bracket-up pos language limit))
           (char (plist-get ctx :char))
           (pos (plist-get ctx :pos))
           (indentation (plist-get ctx :indentation)))
      ;;(message "pos(%S) initial-column(%S) language-offset(%S) language(%S) limit(%S)" pos initial-column language-offset language limit)
      ;;(message "bracket-up: %S, %c" ctx char)
      (cond
       ((null pos)
        (setq indentation initial-column))
       ((and (member language '("php"))
             (eq char ?\{)
             (web-mode-looking-back "switch[ ]*(.*)[ ]*" pos)
             (not (looking-at-p "case\\|default")))
        (setq indentation (+ indentation (* language-offset 2)))
        )
       ((and (member language '("php"))
             (eq char ?\{)
             (goto-char pos)
             (web-mode-looking-back "[)][ ]*" pos)
             (search-backward ")")
             (web-mode-block-opening-paren limit))
        (setq indentation (+ (current-indentation) language-offset))
        )
       (t
        (setq indentation (+ indentation language-offset))
        )
       )
      (cons (if (< indentation initial-column) initial-column indentation) ctx)
      )))

(defun web-mode-ruby-indentation (pos line initial-column language-offset limit)
  (unless limit (setq limit nil))
  (let (h offset prev-line prev-indentation open-ctx)
    (setq open-ctx (web-mode-bracket-up pos "ruby" limit))
    ;;(message "%S" open-ctx)
    (if (plist-get open-ctx :pos)

        (cond
         ((web-mode-looking-at-p ".[ \t\n]+" (plist-get open-ctx :pos))
          ;;(message "ici %S" (plist-get open-ctx :pos))
          (setq offset (+ (plist-get open-ctx :indentation) language-offset)))
         (t
          (setq offset (1+ (plist-get open-ctx :column))))
         )

      (setq h (web-mode-previous-line pos limit))
      (setq offset initial-column)
      (when h
        (setq prev-line (car h))
        ;;(message "%S" prev-line)
        (setq prev-indentation (cdr h))
        (cond
         ((string-match-p "^\\(end\\|else\\|elsif\\|when\\)" line)
          (setq offset (- prev-indentation language-offset))
          )
         ((string-match-p "\\(when\\|if\\|else\\|elsif\\|unless\\|for\\|while\\|def\\|class\\)" prev-line)
          (setq offset (+ prev-indentation language-offset))
          )
         (t
          (setq offset prev-indentation)
          )
         )
        ) ;when
      ) ;if
    offset))

(defun web-mode-python-indentation (pos line initial-column language-offset limit)
  (unless limit (setq limit nil))
  (let (h out prev-line prev-indentation ctx)
    (setq h (web-mode-previous-line pos limit))
    (setq out initial-column)
    (when h
      (setq prev-line (car h))
      (setq prev-indentation (cdr h))
      (cond
       ((string-match-p "^\\(pass\\|else\\|elif\\|when\\)" line)
        (setq out (- prev-indentation language-offset))
        )
       ((string-match-p "\\(if\\|else\\|elif\\|for\\|while\\)" prev-line)
        (setq out (+ prev-indentation language-offset))
        )
       (t
        (setq out prev-indentation)
        )
       ) ;cond
      ) ;when
    ;;out
    (if (< out initial-column) initial-column out)
    ))

(defun web-mode-lisp-indentation (pos point-ctx)
  (let (offset open-ctx)
    (setq open-ctx (web-mode-bracket-up pos "lsp" (plist-get point-ctx :reg-beg)))
    ;;(message "point-ctx=%S" point-ctx)
    ;;(message "open-ctx=%S" open-ctx)
    (cond
     ((null (plist-get open-ctx :pos))
      (setq offset (plist-get point-ctx :reg-col)))
     ((member (plist-get point-ctx :curr-char) '(?\( ?\)))
      (if (web-mode-looking-at-p "((" (plist-get open-ctx :pos))
          (setq offset (+ (plist-get open-ctx :column) 1))
        (setq offset (+ (plist-get open-ctx :column) web-mode-code-indent-offset)))
      )
     (t
      (goto-char (plist-get open-ctx :pos))
      (forward-char)
      (web-mode-rsf "[[:alnum:]-:]+ ")
      (setq offset (current-column))
      )
     ) ;cond
    offset))

(defun web-mode-asp-indentation (pos line initial-column language-offset limit)
  (unless limit (setq limit nil))
  (let (h out prev-line prev-indentation)
    (setq h (web-mode-previous-line pos limit))
    (setq out initial-column)
    (when h
      (setq prev-line (car h))
      (setq prev-indentation (cdr h))
      (cond
       ;; ----------------------------------------------------------------------
       ;; unindent
       ((string-match-p "\\_<\\(\\(end \\(if\\|function\\|class\\|sub\\|with\\)\\)\\|else\\|elseif\\|next\\|loop\\)\\_>" line)
        (setq out (- prev-indentation language-offset)))
       ;; ----------------------------------------------------------------------
       ;; select case statement
       ((string-match-p "\\_<\\(select case\\)\\_>" line)
        (setq out (- prev-indentation 0)))
       ((string-match-p "\\_<\\(end select\\)" line)
        (setq out (- prev-indentation (* 2 language-offset))))
       ((and (string-match-p "\\_<\\(case\\)\\_>" line) (not (string-match-p "\\_<\\(select case\\)\\_>" prev-line)))
        (setq out (- prev-indentation language-offset)))
       ;; ----------------------------------------------------------------------
       ;; do nothing
       ((string-match-p "\\_<\\(\\(end \\(if\\|function\\|class\\|sub\\|select\\|with\\)\\)\\|loop\\( until\\| while\\)?\\)\\_>" prev-line)
        (setq out (+ prev-indentation 0)))
       ;; indent
       ((string-match-p "\\_<\\(\\(select \\)?case\\|else\\|elseif\\|unless\\|for\\|class\\|with\\|do\\( until\\| while\\)?\\|while\\|\\(public \\|private \\)?\\(function\\|sub\\|class\\)\\)\\_>" prev-line)
        (setq out (+ prev-indentation language-offset)))
       ;; single line if statement
       ((string-match-p "\\_<if\\_>.*\\_<then\\_>[ \t]*[[:alpha:]]+" prev-line)
        (setq out (+ prev-indentation 0)))
       ;; normal if statement
       ((string-match-p "\\_<\\if\\_>" prev-line)
        (setq out (+ prev-indentation language-offset)))
       (t
        (setq out prev-indentation))
       )
      ) ;when
    out))

(defun web-mode-block-previous-live-line ()
  (save-excursion
    (let ((continue t) (line "") (pos (point)))
      (beginning-of-line)
      (while (and continue (not (bobp)) (forward-line -1))
        (when (not (web-mode-block-is-token-line))
          (setq line (web-mode-trim (buffer-substring (point) (line-end-position)))))
        (when (not (string= line ""))
          (setq continue nil))
        ) ;while
      (if (string= line "")
          (progn (goto-char pos) nil)
        (cons line (current-indentation)))
      )))

(defun web-mode-part-is-opener (pos reg-beg)
  (save-excursion
    (save-match-data
      (and pos
           (web-mode-go (web-mode-part-opening-paren-position pos))
           (>= (point) reg-beg)
           ;;(progn (message "%S %S" pos (point)))
           (looking-back "if[ ]*")))))

(defun web-mode-part-previous-live-line (reg-beg)
  (unless reg-beg (setq reg-beg (point-min)))
  ;;(message "reg-beg=%S" reg-beg)
  (save-excursion
    (let ((continue (> (point) reg-beg))
          (line "")
          bol-pos
          eol-pos
          pos)
      (beginning-of-line)
      (while (and continue (> (point) reg-beg) (forward-line -1))
        (setq bol-pos (point)
              eol-pos (line-end-position))
        (when (> reg-beg bol-pos)
          (setq bol-pos reg-beg))
        (when (not (web-mode-part-is-token-line bol-pos))
          (setq line (web-mode-trim (buffer-substring bol-pos eol-pos)))
          (when (not (string= line "")) (setq continue nil))
          ) ;when
        ) ;while
      (cond
       ((string= line "")
        nil)
       (t
        (setq continue t)
        (setq pos (1- eol-pos))
        (while (and (>= pos bol-pos) continue)
          (cond
           ((eq (char-after pos) ?\s)
            (setq pos (1- pos)))
           ((get-text-property pos 'part-token)
            (setq pos (1- pos)))
           (t
            (setq continue nil))
           ) ;cond
          ) ;while
        ;;(message "%S %S : %S" bol-pos eol-pos pos)
        (setq line (web-mode-clean-part-line line))
        (list line (current-indentation) pos))
       )
      )))

(defun web-mode-in-code-block (open close &optional prop)
  (save-excursion
    (let ((pos (point)) pos-open pos-close start end ret)
      (when prop
        (setq start pos
              end pos)
        (when (eq (get-text-property pos prop) (get-text-property (1- pos) prop))
          (setq start (or (previous-single-property-change pos prop) (point-min))))
        (when (eq (get-text-property pos prop) (get-text-property (1+ pos) prop))
          (setq end (next-single-property-change pos prop)))
        ;;        (message "start(%S) end(%S)" start end)
        )
      (setq ret (and (web-mode-sb open start t)
                     (setq pos-open (point))
                     (web-mode-sf close end t)
                     (setq pos-close (point))
                     (>= pos-close pos)))
      (if ret
          (cons pos-open pos-close)
        ret)
      )))

(defun web-mode-clean-part-line (input)
  (let ((out "")
        (beg 0)
        (keep t)
        (n (length input)))
    (dotimes (i n)
      (if (or (get-text-property i 'block-side input)
              (eq (get-text-property i 'part-token input) 'comment)
              (eq (get-text-property i 'tag-type input) 'comment))
          (when keep
            (setq out (concat out (substring input beg i))
                  beg 0
                  keep nil))
        (when (null keep)
          (setq beg i
                keep t))
        ) ;if
      ) ;dotimes
    (if (> beg 0) (setq out (concat out (substring input beg n))))
    (setq out (if (= (length out) 0) input out))
    (web-mode-trim out)
    ))

(defun web-mode-clean-block-line (input)
  (let ((out "")
        (beg 0)
        (keep t)
        (n (length input)))
    (dotimes (i n)
      (if (or (not (get-text-property i 'block-side input))
              (member (get-text-property i 'block-token input)
                      '(comment delimiter-beg delimiter-end)))
          (when keep
            (setq out (concat out (substring input beg i))
                  beg 0
                  keep nil))
        (when (null keep)
          (setq beg i
                keep t))
        ) ;if
      ) ;dotimes
    (if (> beg 0) (setq out (concat out (substring input beg n))))
    (setq out (if (= (length out) 0) input out))
    (web-mode-trim out)
    ;;    (message "%S [%s] > [%s]" beg input out)
    ))

(defun web-mode-language-at-pos (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((get-text-property pos 'block-side)
    web-mode-engine)
   ((get-text-property pos 'part-side)
    (symbol-name (get-text-property pos 'part-side)))
   (t
    web-mode-content-type)
   ) ;cond
  )

(defun web-mode-coord-position (line column)
  (save-excursion
    (when (stringp line) (setq line (string-to-number line)))
    (when (stringp column) (setq column (string-to-number column)))
    (goto-char (point-min))
    (forward-line (1- line))
    (move-to-column (1- column))
    (point)))

(defun web-mode-column-at-pos (&optional pos)
  (unless pos (setq pos (point)))
  (save-excursion
    (goto-char pos)
    (current-column)))

(defun web-mode-is-single-line-block (pos)
  (= (web-mode-line-number (web-mode-block-beginning-position pos))
     (web-mode-line-number (web-mode-block-end-position pos))))

(defun web-mode-line-number (&optional pos)
  (unless pos (setq pos (point)))
  (let (ret)
    (setq ret (+ (count-lines 1 pos)
                 (if (= (web-mode-column-at-pos pos) 0) 1 0)))))

(defun web-mode-block-is-control (pos)
  (save-excursion
    (let (control state controls pair)
      (goto-char pos)
      (setq controls (web-mode-block-controls-get pos))
      (setq pair (car controls))
      (cond
       ((eq (car pair) 'inside)
        )
       ((eq (car pair) 'open)
        (setq state t
              control (cdr pair)))
       ((eq (car pair) 'close)
        (setq state nil
              control (cdr pair)))
       ) ;cond
      ;;      (message "engine=%S control=%S state=%S" web-mode-engine control state)
      (if control (cons control state) nil)
      )))

(defun web-mode-block-is-opening-control (pos)
  (save-excursion
    (let (controls pair)
      (goto-char pos)
      (if (and (setq controls (web-mode-block-controls-get pos))
               (= (length controls) 1)
               (setq pair (car controls))
               (eq (car pair) 'open))
          (cdr pair)
        nil)
      )))

(defun web-mode-markup-indentation-origin (pos)
  (save-excursion
    (let* ((continue (not (bobp)))
           ;;         (pos (point))
           (part-side (not (null (get-text-property pos 'part-side)))) ;part-side at the origin
           (types '(start end void)))
      (while continue
        (forward-line -1)
        (if (bobp)
            (setq pos (point)
                  continue nil)
          (back-to-indentation)
          (setq pos (point))
          (setq continue (not (or (and (null part-side)
                                       (null (get-text-property pos 'part-side))
                                       (get-text-property pos 'tag-beg)
                                       (member (get-text-property pos 'tag-type) types)
                                       (null (get-text-property (1- pos) 'invisible)))
                                  (and part-side
                                       (get-text-property pos 'part-side)
                                       (get-text-property pos 'tag-beg)
                                       (member (get-text-property pos 'tag-type) types)
                                       (null (get-text-property (1- pos) 'invisible)))
                                  (and (get-text-property pos 'block-beg)
                                       (not (get-text-property pos 'tag-type))
                                       (web-mode-block-is-control pos)
                                       (not (looking-at-p "{% comment"))))))
          ) ;if
        ) ;while
      ;;(message "indent-origin=%S" pos)
      pos)))

;;TODO : prendre en compte part-token
;; state=t <=> start tag
(defun web-mode-element-is-opened (pos limit)
  (let (tag
        last-end-tag
        tag-pos block-pos
        state
        n
        ret
        (continue t)
        controls
        control
        (buffer (current-buffer))
        (h (make-hash-table :test 'equal))
        (h2 (make-hash-table :test 'equal)))

;;    (message "pos-ori=%S limit=%S" pos limit)

    (while continue
      (setq control nil
            controls nil
            last-end-tag nil
            tag nil)

      (cond
       ((get-text-property pos 'tag-beg)
        (when (member (get-text-property pos 'tag-type) '(start end))
          (setq tag (get-text-property pos 'tag-name)
                state (eq (get-text-property pos 'tag-type) 'start))
          (if (null state) (setq last-end-tag (cons tag pos)))
          (setq n (gethash tag h 0))
          (if (null state)
              (progn
                (when (> n 0) (puthash tag (1- n) h))
                (puthash tag (1- n) h2))
            (puthash tag (1+ n) h)
            (puthash tag (1+ n) h2))
          ) ;when
        (when (setq pos (web-mode-tag-end-position pos))
          (setq tag-pos nil)
          (when (and block-pos (> pos block-pos))
            (setq block-pos nil))
          ) ;when
        )
       ((and web-mode-enable-control-block-indentation
             (get-text-property pos 'block-beg))
        (when (setq controls (web-mode-block-controls-get pos))
          (dolist (control controls)
            (setq tag (cdr control))
            (setq n (gethash tag h 0))
            (cond
             ((eq (car control) 'inside)
              )
             ((eq (car control) 'open)
              (puthash tag (1+ n) h))
             ((> n 0)
              (puthash tag (1- n) h))
             ) ;cond
            ) ;dolist
          )
        (when (setq pos (web-mode-block-end-position pos))
          (setq block-pos nil)
          (when (and tag-pos (> pos tag-pos))
            (setq tag-pos nil))
          )
        )
       ) ;cond

;;      (message "tag=%S end-pos=%S" tag pos)

      (when (and pos (< pos limit))
        (when (or (null tag-pos) (>= pos tag-pos))
          (setq tag-pos (web-mode-tag-next-position pos limit))
;;          (message "from=%S tag-next-pos=%S" pos tag-pos)
          )
        (when (or (null block-pos) (>= pos block-pos))
          (setq block-pos (web-mode-block-next-position pos limit))
;;          (message "from=%S block-next-pos=%S" pos block-pos)
          )
        )

      (cond
       ((null pos)
        )
       ((and (null tag-pos)
             (null block-pos))
        (setq pos nil))
       ((and tag-pos block-pos)
        (if (< tag-pos block-pos)
            (progn
              (setq pos tag-pos)
              (setq tag-pos nil))
          (setq pos block-pos)
          (setq block-pos nil))
        )
       ((null tag-pos)
        (setq pos block-pos)
        (setq block-pos nil))
       (t
        (setq pos tag-pos)
        (setq tag-pos nil))
       )

      (when (or (null pos)
                (>= pos limit))
        (setq continue nil))
      ) ;while

;;    (message "hashtable=%S" h)
    (maphash (lambda (k v) (if (> v 0) (setq ret t))) h)

    (when (and (null ret)
               last-end-tag
               (> (hash-table-count h2) 1)
               (< (gethash (car last-end-tag) h2) 0))
;;      (message "last-end-tag=%S" last-end-tag)
      (save-excursion
        (goto-char (cdr last-end-tag))
        (web-mode-tag-match)
        (when (not (= (point) (cdr last-end-tag)))
          (setq n (point))
          (back-to-indentation)
          (if (= n (point)) (setq ret (current-indentation))))
        ))

    ret))

(defun web-mode-previous-line (pos limit)
  (save-excursion
    (let (beg end line (continue t))
      (goto-char pos)
      (while continue
        (forward-line -1)
        (setq end (line-end-position))
        (setq line (buffer-substring-no-properties (point) end))
        (when (or (not (string-match-p "^[ \t]*$" line))
                  (bobp)
                  (<= (point) limit))
          (setq continue nil))
        )
      (if (<= (point) limit)
          ;;todo : affiner (le + 3 n est pas générique cf. <?php <% <%- etc.)
          (setq beg (if (< (+ limit 3) end) (+ limit 3) end))
        (setq beg (line-beginning-position))
        ) ;if
      (setq line (buffer-substring-no-properties beg end))
      (cons line (current-indentation))
      )))

(defun web-mode-bracket-up (pos language &optional limit)
  (unless limit (setq limit nil))
  ;;(message "pos(%S) language(%S) limit(%S)" pos language limit)
  (save-excursion
    (goto-char pos)
    (let ((continue t)
          (regexp "[\]\[}{)(]")
          (char nil)
          (map nil)
          (key nil)
          (value 0)
          (searcher (if (get-text-property pos 'block-side) 'web-mode-block-rsb 'web-mode-part-rsb)))
      (while (and continue (funcall searcher regexp limit))
        (setq char (aref (match-string-no-properties 0) 0))
        (setq key (cond ((eq char ?\)) ?\()
                        ((eq char ?\}) ?\{)
                        ((eq char ?\]) ?\[)
                        (t             char)))
        (setq value (or (plist-get map key) 0))
        (setq value (if (member char '(?\( ?\{ ?\[)) (1+ value) (1- value)))
        (setq map (plist-put map key value))
        (setq continue (< value 1))
        ;;(message "pos=%S char=%c key=%c value=%S map=%S" (point) char key value map)
        ) ;while
      (list :pos (if (> value 0) (point) nil)
            :char char
            :column (current-column)
            :indentation (current-indentation))
      ) ;let
    ))

(defun web-mode-count-char-in-string (char string)
  (let ((n 0))
    (dotimes (i (length string))
      (if (eq (elt string i) char)
          (setq n (1+ n))))
    n))

(defun web-mode-mark-and-expand ()
  "Mark and expand."
  (interactive)
  (web-mode-mark (point)))

(defun web-mode-mark (pos)
  (let ((beg pos) (end pos) prop reg-beg boundaries)

    (if mark-active
        (setq reg-beg (region-beginning))
      (setq web-mode-expand-initial-pos (point)
            web-mode-expand-initial-scroll (window-start))
      )

    ;; (message "regs=%S %S %S %S" (region-beginning) (region-end) (point-min) (point-max))
    ;; (message "before=%S" web-mode-expand-previous-state)

    (cond

     ((and mark-active
           (= (region-beginning) (point-min))
           (or (= (region-end) (point-max))
               (= (1+ (region-end)) (point-max))))
      (deactivate-mark)
      (goto-char (or web-mode-expand-initial-pos (point-min)))
      (setq web-mode-expand-previous-state nil)
      (when web-mode-expand-initial-scroll
        (set-window-start (selected-window) web-mode-expand-initial-scroll))
      )

     ((string= web-mode-expand-previous-state "elt-content")
      (web-mode-element-parent)
      ;;(message "pos=%S" (point))
      (web-mode-element-select)
      (setq web-mode-expand-previous-state "html-parent"))

     ((and (member (get-text-property pos 'block-token) '(comment string))
           (not (member web-mode-expand-previous-state '("block-token" "block-body" "block-side"))))
      (when (eq (get-text-property pos 'block-token) (get-text-property (1- pos) 'block-token))
        (setq beg (or (previous-single-property-change pos 'block-token) (point-min))))
      (when (eq (get-text-property pos 'block-token) (get-text-property (1+ pos) 'block-token))
        (setq end (next-single-property-change pos 'block-token)))
      (set-mark beg)
      (goto-char end)
      (exchange-point-and-mark)
      (setq web-mode-expand-previous-state "block-token"))

     ((and (get-text-property pos 'block-side)
           (not (member web-mode-expand-previous-state '("block-body" "block-side")))
           (not (member web-mode-engine '(django go)))
           (setq boundaries (web-mode-in-code-block "{" "}" 'block-side)))
      (set-mark (car boundaries))
      (goto-char (cdr boundaries))
      (exchange-point-and-mark)
      (setq web-mode-expand-previous-state "block-body"))

     ((and (get-text-property pos 'block-side)
           (not (member web-mode-expand-previous-state '("block-side"))))
      (set-mark (web-mode-block-beginning-position pos))
      (goto-char (1+ (web-mode-block-end-position pos)))
      (exchange-point-and-mark)
      (setq web-mode-expand-previous-state "block-side"))

     ((and (get-text-property pos 'part-token)
           (not (string= web-mode-expand-previous-state "part-token")))
      (when (eq (get-text-property pos 'part-token) (get-text-property (1- pos) 'part-token))
        (setq beg (previous-single-property-change pos 'part-token)))
      (when (eq (get-text-property pos 'part-token) (get-text-property (1+ pos) 'part-token))
        (setq end (next-single-property-change pos 'part-token)))
      (set-mark beg)
      (goto-char end)
      (exchange-point-and-mark)
      (setq web-mode-expand-previous-state "part-token"))

     ((and (get-text-property pos 'part-side)
           (not (string= web-mode-expand-previous-state "client-part"))
           (setq boundaries (web-mode-in-code-block "{" "}" 'part-side)))
      (set-mark (car boundaries))
      (goto-char (cdr boundaries))
      (exchange-point-and-mark)
      (setq web-mode-expand-previous-state "client-part"))

     ((and (get-text-property pos 'part-side)
           (not (string= web-mode-expand-previous-state "part-side")))
      (when (eq (get-text-property pos 'part-side) (get-text-property (1- pos) 'part-side))
        (setq beg (previous-single-property-change pos 'part-side)))
      (when (eq (get-text-property pos 'part-side) (get-text-property (1+ pos) 'part-side))
        (setq end (next-single-property-change pos 'part-side)))
      (when (eq (char-after beg) ?\n)
        (setq beg (1+ beg)))
      (set-mark beg)
      (goto-char end)
      (when (looking-back "^[ \t]+")
        (beginning-of-line))
      (exchange-point-and-mark)
      (setq web-mode-expand-previous-state "part-side"))

     ((and (get-text-property pos 'tag-attr)
           (not (member web-mode-expand-previous-state '("html-attr" "html-tag"))))
      (web-mode-attribute-select pos)
      (setq web-mode-expand-previous-state "html-attr"))

     ((and (eq (get-text-property pos 'tag-type) 'comment)
           (not (member web-mode-expand-previous-state '("html-tag" "html-comment" "html-elt" "html-parent"))))
      (web-mode-tag-select)
      (setq web-mode-expand-previous-state "html-comment"))

     ((and (get-text-property pos 'tag-name)
           (not (member web-mode-expand-previous-state '("html-tag" "html-elt" "html-parent"))))
      (web-mode-tag-select)
      (setq web-mode-expand-previous-state "html-tag"))

     ((and (get-text-property pos 'tag-beg)
           (string= web-mode-expand-previous-state "html-tag"))
      (web-mode-element-select)
      (setq web-mode-expand-previous-state "html-elt"))

     (t
      (cond
       ((not (web-mode-element-parent))
        (push-mark (point))
        (push-mark (point-max) nil t)
        (goto-char (point-min))
        (setq web-mode-expand-previous-state "mark-whole"))
       ((not (= (web-mode-tag-end-position (point)) (1- beg)))
        (web-mode-element-content-select)
        (setq web-mode-expand-previous-state "elt-content"))
       (t
        (web-mode-element-select)
        (setq web-mode-expand-previous-state "html-parent"))
       )
      ) ;t

     ) ;cond

    ;;(message "w=%S" (window-end))
    ;;(message "after=%S" web-mode-expand-previous-state)

    ))

(defun web-mode-block-kill ()
  "Kill the current block."
  (interactive)
  (web-mode-block-select)
  (when mark-active
    (kill-region (region-beginning) (region-end))))

(defun web-mode-block-select ()
  "Select the current block."
  (interactive)
  (let (beg)
    (when (setq beg (web-mode-block-beginning-position (point)))
      (goto-char beg)
      (set-mark (point))
      (web-mode-block-end)
      (exchange-point-and-mark))
    beg))

(defun web-mode-tag-select ()
  "Select the current html tag."
  (interactive)
  (let (beg)
    (when (setq beg (web-mode-tag-beginning-position (point)))
      (goto-char beg)
      (set-mark (point))
      (web-mode-tag-end)
      (exchange-point-and-mark))
    beg))

(defun web-mode-element-content-select ()
  "Select the content of a html element."
  (interactive)
  (let (pos beg end)
    (web-mode-element-select)
    (when mark-active
      (setq pos (point))
      (deactivate-mark)
      (web-mode-tag-match)
      (setq end (point))
      (goto-char pos)
      (web-mode-tag-end)
      (set-mark (point))
      (goto-char end)
      (exchange-point-and-mark)
      )))

(defun web-mode-element-select ()
  "Select the current html element (including opening and closing tags)."
  (interactive)
  (let* ((pos (point))
         (type (get-text-property pos 'tag-type)))
    (if type
        (cond
         ((member type '(start void))
          (web-mode-tag-beginning)
          (set-mark (point))
          (web-mode-tag-match)
          (web-mode-tag-end)
          (exchange-point-and-mark))
         (t
          (web-mode-tag-match)
          (set-mark (point))
          (web-mode-tag-match)
          (web-mode-tag-end)
          (exchange-point-and-mark))
         ) ;cond
      (web-mode-element-parent)
      (unless (= (point) pos) (web-mode-element-select))
      ) ;if
    ))

(defun web-mode-element-is-collapsed (&optional pos)
  (unless pos (setq pos (point)))
  (let (boundaries)
    (and (setq boundaries (web-mode-element-boundaries pos))
         (or (= (car (car boundaries)) (car (cdr boundaries)))
             (= (cdr (car boundaries)) (1- (car (cdr boundaries)))))
         )))

(defun web-mode-element-transpose ()
  "Transpose two html elements."
  (interactive)
  (let (pos start1 end1 start2 end2)
    (save-excursion
      (setq pos (point))
      (cond
       ((get-text-property pos 'tag-type)
        (setq start1 (web-mode-element-beginning-position pos)
              end1 (1+ (web-mode-element-end-position pos)))
        )
       ((setq start1 (web-mode-element-parent-position pos))
        (setq end1 (1+ (web-mode-element-end-position pos)))
        )
       ) ;cond
      (when (and start1 end1 (> end1 0))
        (goto-char end1)
        (unless (get-text-property (point) 'tag-beg)
          (skip-chars-forward "\n\t "))
        (when (get-text-property (point) 'tag-beg)
          (setq start2 (web-mode-element-beginning-position (point))
                end2 (1+ (web-mode-element-end-position (point))))
          )
        )
      (transpose-regions start1 end1 start2 end2)
      ) ;save-excursion
    start2))

(defun web-mode-element-children-fold-or-unfold (&optional pos)
  "Fold/Unfold all the children of the current html element."
  (interactive)
  (unless pos (setq pos (point)))
  (save-excursion
    (dolist (child (reverse (web-mode-element-children pos)))
      (goto-char child)
      (web-mode-fold-or-unfold))
    ))

(defun web-mode-element-mute-blanks ()
  "Mute blanks."
  (interactive)
  (let (pos parent beg end children elt)
    (setq pos (point))
    (save-excursion
      (when (and (setq parent (web-mode-element-boundaries pos))
                 (web-mode-element-child-position (point)))
        (setq children (reverse (web-mode-element-children)))
        (goto-char (car (cdr parent)))
        (dolist (child children)
          (setq elt (web-mode-element-boundaries child))
          (when (> (point) (1+ (cddr elt)))
            (when (and (not (eq (get-text-property (point) 'part-token) 'comment))
                       (not (eq (get-text-property (1+ (cddr elt)) 'part-token) 'comment)))
              (web-mode-insert-text-at-pos "-->" (point))
              (web-mode-insert-text-at-pos "<!--" (1+ (cddr elt))))
            )
          (goto-char child)
          )
        (when (and (> (point) (1+ (cdr (car parent))))
                   (not (eq (get-text-property (point) 'part-token) 'comment))
                   (not (eq (get-text-property (1+ (cdr (car parent))) 'part-token) 'comment)))
          (web-mode-insert-text-at-pos "-->" (point))
          (web-mode-insert-text-at-pos "<!--" (1+ (cdr (car parent)))))
        ) ;when
      )))

(defun web-mode-element-children (&optional pos)
  (unless pos (setq pos (point)))
  (let ((continue t) (i 0) child children)
    (save-excursion
      (when (and (member (get-text-property pos 'tag-type) '(start end))
                 (setq child (web-mode-element-child-position pos)))
        (while continue
          (cond
           ((> (setq i (1+ i)) 100)
            (setq continue nil)
            (message "element-children ** warning **"))
           ((= i 1)
            (goto-char child))
           ((web-mode-element-sibling-next)
            )
           (t
            (setq continue nil))
           ) ;cond
          (when continue
            (setq children (append children (list (point)))))
          ) ;while
        ) ;when
      ) ;save-excursion
    children))

(defun web-mode-element-boundaries (&optional pos)
  "Return ((start-tag-beg . start-tag-end) . (end-tag-beg . end-tag-end))
First level car and cdr are the same with void elements.
Pos should be in a tag."
  (unless pos (setq pos (point)))
  (let (start-tag-beg start-tag-end end-tag-beg end-tag-end)
    (cond
     ((eq (get-text-property pos 'tag-type) 'start)
      (setq start-tag-beg (web-mode-tag-beginning-position pos)
            start-tag-end (web-mode-tag-end-position pos))
      (when (setq pos (web-mode-tag-match-position pos))
        (setq end-tag-beg pos
              end-tag-end (web-mode-tag-end-position pos)))
      )
     ((eq (get-text-property pos 'tag-type) 'end)
      (setq end-tag-beg (web-mode-tag-beginning-position pos)
            end-tag-end (web-mode-tag-end-position pos))
      (when (setq pos (web-mode-tag-match-position pos))
        (setq start-tag-beg pos
              start-tag-end (web-mode-tag-end-position pos)))
      )
     ((eq (get-text-property pos 'tag-type) 'void)
      (setq start-tag-beg (web-mode-tag-beginning-position pos)
            start-tag-end (web-mode-tag-end-position pos))
      (setq end-tag-beg start-tag-beg
            end-tag-end start-tag-end)
      )
     ) ;cond
    (if (and start-tag-beg start-tag-end end-tag-beg end-tag-end)
        (cons (cons start-tag-beg start-tag-end) (cons end-tag-beg end-tag-end))
      nil)
    ))

(defun web-mode-surround ()
  "Surround each line of the current REGION with a start/end tag."
  (interactive)
  (when mark-active
    (let (beg end line-beg line-end pos tag tag-start tag-end)
      (save-excursion
        (setq tag (read-from-minibuffer "Tag name? ")
              tag-start (concat "<" tag ">")
              tag-end (concat "</" tag ">")
              pos (point)
              beg (region-beginning)
              end (region-end)
              line-beg (web-mode-line-number beg)
              line-end (web-mode-line-number end))
        (goto-char end)
        (unless (bolp)
          (insert tag-end)
          (back-to-indentation)
          (when (> beg (point))
            (goto-char beg))
          (insert tag-start))
        (while (> line-end line-beg)
          (forward-line -1)
          (setq line-end (1- line-end))
          (unless (looking-at-p "[[:space:]]*$")
            (end-of-line)
            (insert tag-end)
            (back-to-indentation)
            (when (> beg (point))
              (goto-char beg))
            (insert tag-start))
          ) ;while
        (deactivate-mark)
        ))))

(defun web-mode-element-wrap (&optional tag-name)
  "Wrap current REGION with start and end tags.
Prompt user if TAG-NAME isn't provided."
  (interactive)
  (let (beg end pos tag sep)
    (save-excursion
      (setq tag (or tag-name (read-from-minibuffer "Tag name? ")))
      (setq pos (point))
      (cond
       (mark-active
        (setq beg (region-beginning)
              end (region-end)))
       ((get-text-property pos 'tag-type)
        (setq beg (web-mode-element-beginning-position pos)
              end (1+ (web-mode-element-end-position pos))))
       ((setq beg (web-mode-element-parent-position pos))
        (setq end (1+ (web-mode-element-end-position pos))))
       )
      ;;      (message "beg(%S) end(%S)" beg end)
      (when (and beg end (> end 0))
        (setq sep (if (get-text-property beg 'tag-beg) "\n" ""))
        (web-mode-insert-text-at-pos (concat sep "</" tag ">") end)
        (web-mode-insert-text-at-pos (concat "<" tag ">" sep) beg)
        (when (string= sep "\n") (indent-region beg (+ end (* (+ 3 (length tag)) 2))))
        )
      ) ;save-excursion
    (web-mode-go beg)))

(defun web-mode-element-vanish (&optional arg)
  "Vanish the current html element. The content of the element is kept."
  (interactive "p")
  (let (type (pos (point)) start-b start-e end-b end-e)
    (while (>= arg 1)
      (setq type (get-text-property pos 'tag-type))
      (when type
        (cond
         ((member type '(void))
          (web-mode-element-kill)
          (set-mark (point))
          (web-mode-tag-match)
          (web-mode-tag-end)
          (exchange-point-and-mark))
         ((member type '(start))
          (setq start-b (web-mode-tag-beginning-position)
                start-e (web-mode-tag-end-position))
          (when (web-mode-tag-match)
            (setq end-b (web-mode-tag-beginning-position)
                  end-e (web-mode-tag-end-position)))
          )
         (t
          (setq end-b (web-mode-tag-beginning-position)
                end-e (web-mode-tag-end-position))
          (when (web-mode-tag-match)
            (setq start-b (web-mode-tag-beginning-position)
                  start-e (web-mode-tag-end-position)))
          ) ;t
         ) ;cond
        (when (and start-b end-b)
          (goto-char end-b)
          (delete-region end-b (1+ end-e))
          (delete-blank-lines)
          (goto-char start-b)
          (delete-region start-b (1+ start-e))
          (delete-blank-lines)
          (web-mode-buffer-indent)
          )
        ;;        (message "start %S %S - end %S %S" start-b start-e end-b end-e))
        ) ;when
      (skip-chars-forward "[:space:]\n")
      (setq arg (1- arg))
      ) ;while
    ) ;let
  )

(defun web-mode-element-kill (&optional arg)
  "Kill the current html element."
  (interactive "p")
  (while (>= arg 1)
    (setq arg (1- arg))
    (web-mode-element-select)
    (when mark-active
      (kill-region (region-beginning) (region-end)))
    ) ;while
  )

(defun web-mode-element-clone (&optional arg)
  "Clone the current html element."
  (interactive "p")
  (let (col pos)
    (while (>= arg 1)
      (setq arg (1- arg)
            col 0)
      (web-mode-element-select)
      (when mark-active
        (save-excursion
          (goto-char (region-beginning))
          (setq col (current-column)))
        (kill-region (region-beginning) (region-end))
        (yank)
        (newline)
        (indent-line-to col)
        (setq pos (point))
        (yank)
        (goto-char pos))
      )
    ) ;let
  )

(defun web-mode-element-insert ()
  "Insert an html element."
  (interactive)
  (let (tag-name)
    (cond
     ((and (get-text-property (point) 'tag-type)
           (not (get-text-property (point) 'tag-beg)))
      (message "element-insert ** invalid context **"))
     ((not (and (setq tag-name (read-from-minibuffer "Tag name? "))
                (> (length tag-name) 0)))
      (message "element-insert ** failure **"))
     ((web-mode-element-is-void tag-name)
      (insert (concat "<" tag-name "/>"))
      )
     (mark-active
      (let ((beg (region-beginning)) (end (region-end)))
        (deactivate-mark)
        (goto-char end)
        (insert "</" tag-name ">")
        (goto-char beg)
        (insert "<" tag-name ">")
        )
      )
     (t
      (insert (concat "<" tag-name ">" "</" tag-name ">"))
      (web-mode-sb "</")
      )
     ) ;cond
    ))

(defun web-mode-element-rename ()
  "Rename the current html element."
  (interactive)
  (save-excursion
    (let (pos tag-name)
      (setq tag-name (read-from-minibuffer "New tag name? "))
      (when (and (> (length tag-name) 0)
                 (web-mode-element-beginning)
                 (looking-at "<\\([[:alnum:]]+\\(:?[-][[:alpha:]]+\\)?\\)"))
        (setq pos (point))
        (unless (web-mode-element-is-void)
            (save-match-data
              (web-mode-tag-match)
              (if (looking-at "</[ ]*\\([[:alnum:]]+\\(:?[-][[:alpha:]]+\\)?\\)")
                  (replace-match (concat "</" tag-name))
                )))
        (goto-char pos)
        (replace-match (concat "<" tag-name))
        ))))

(defun web-mode-current-trimmed-line ()
  (web-mode-trim (buffer-substring-no-properties
                  (line-beginning-position)
                  (line-end-position))))

(defun web-mode-trim (string)
  (replace-regexp-in-string "\\`[ \t\n]*" "" (replace-regexp-in-string "[ \t\n]*\\'" "" string)))

(defun web-mode-block-is-token-line ()
  (save-excursion
    (let ((continue t) (counter 0))
      (beginning-of-line)
      (back-to-indentation)
      (while (and continue (not (eolp)))
        (cond
         ((get-text-property (point) 'block-token)
          (setq counter (1+ counter)))
         ((not (eq ?\s (following-char)))
          (setq continue nil
                counter 0))
         ) ;cond
        (forward-char)
        ) ;while
      (> counter 0)
      )))

(defun web-mode-part-is-token-line (pos)
  (save-excursion
    (let ((continue t)
          (counter 0))
      (goto-char pos)
      (setq continue (not (eolp)))
      (while continue
        (forward-char)
        (cond
         ((eolp)
          (setq continue nil))
         ((or (get-text-property (point) 'block-side)
              (member (get-text-property (point) 'part-token) '(comment string)))
          (setq counter (1+ counter)))
         ((eq ?\s (following-char))
          )
         (t
          (setq continue nil
                counter 0))
         )
        ) ;while
      (> counter 0))))

(defun web-mode-is-content (&optional pos)
  (unless pos (setq pos (point)))
  (not (or (get-text-property pos 'part-side)
           (get-text-property pos 'tag-type)
           (get-text-property pos 'block-side)
           )))

(defun web-mode-is-comment-or-string (&optional pos)
  (unless pos (setq pos (point)))
  (not (null (or (eq (get-text-property pos 'tag-type) 'comment)
                 (member (get-text-property pos 'block-token) '(comment string))
                 (member (get-text-property pos 'part-token) '(comment string))))))

;; NOTE: we look at the firt one
(defun web-mode-block-is-open (&optional pos)
  (unless pos (setq pos (point))))

;; NOTE: we look at the last one
(defun web-mode-block-is-close (&optional pos)
  (unless pos (setq pos (point)))
  (and (get-text-property pos 'block-side)
       (eq (caar (web-mode-block-controls-get pos)) 'close)))

;; NOTE: we look at the first one
(defun web-mode-block-is-inside (&optional pos)
  (unless pos (setq pos (point)))
  (and (get-text-property pos 'block-side)
       (eq (caar (web-mode-block-controls-get pos)) 'inside)))

(defun web-mode-element-is-void (&optional tag)
  (cond
   ((and tag (member tag '("div" "li" "a" "p")))
    nil)
   ((and tag (string= web-mode-content-type "jsx"))
    (member (downcase tag) '("img" "br" "hr")))
   (tag
    (car (member (downcase tag) web-mode-void-elements)))
   (t
    (eq (get-text-property (point) 'tag-type) 'void))
   ))

(defun web-mode-toggle-current-element-highlight ()
  "Toggle highlighting of the current html element."
  (interactive)
  (if web-mode-enable-current-element-highlight
      (progn
        (web-mode-delete-tag-overlays)
        (setq web-mode-enable-current-element-highlight nil))
    (setq web-mode-enable-current-element-highlight t)
    ))

(defun web-mode-fold-or-unfold (&optional pos)
  "Toggle folding on an html element or a control block."
  (interactive)
  (web-mode-propertize)
  (web-mode-with-silent-modifications
   (save-excursion
     (if pos (goto-char pos))
     (let (beg-inside beg-outside end-inside end-outside overlay overlays regexp)
       (when (looking-back "^[\t ]*")
         (back-to-indentation))
       (setq overlays (overlays-at (point)))
       (dolist (elt overlays)
         (when (and (not overlay)
                    (eq (overlay-get elt 'font-lock-face) 'web-mode-folded-face))
           (setq overlay elt)))
       (cond
        ;; *** unfolding
        (overlay
         (setq beg-inside (overlay-start overlay)
               end-inside (overlay-end overlay))
         (remove-overlays beg-inside end-inside)
         (put-text-property beg-inside end-inside 'invisible nil)
         )
        ;; *** tag folding
        ((member (get-text-property (point) 'tag-type) '(start end))
         (when (not (web-mode-element-is-collapsed (point)))
           (web-mode-tag-beginning)
           (when (eq (get-text-property (point) 'tag-type) 'end)
             (web-mode-tag-match))
           (setq beg-outside (point))
           (web-mode-tag-end)
           (setq beg-inside (point))
           (goto-char beg-outside)
           (when (web-mode-tag-match)
             (setq end-inside (point))
             (web-mode-tag-end)
             (setq end-outside (point)))
           )
         )
        ;; *** block folding
        ((cdr (web-mode-block-is-control (point)))
         (setq beg-outside (web-mode-block-beginning-position (point)))
         (setq beg-inside (1+ (web-mode-block-end-position (point))))
         (when (web-mode-block-match)
           (setq end-inside (point))
           (setq end-outside (1+ (web-mode-block-end-position (point)))))
         )
        ) ;cond
       (when (and beg-inside beg-outside end-inside end-outside)
         (setq overlay (make-overlay beg-outside end-outside))
         (overlay-put overlay 'font-lock-face 'web-mode-folded-face)
         (put-text-property beg-inside end-inside 'invisible t))
       ))))

(defun web-mode-toggle-comments ()
  "Toggle comments visbility."
  (interactive)
  (save-excursion
    (if web-mode-comments-invisible
        (remove-overlays))
    (setq web-mode-comments-invisible (null web-mode-comments-invisible))
    (let ((continue t)
          (pos (point-min))
          (visibility web-mode-comments-invisible)
          overlay end)
      (while continue
        (setq pos (next-single-property-change pos 'font-lock-face))
        (if (null pos)
            (setq continue nil)
          (when (eq (get-text-property pos 'font-lock-face) 'web-mode-comment-face)
            (setq end (next-single-property-change pos 'font-lock-face))
            (put-text-property pos end 'invisible visibility)
            (when visibility
              (setq overlay (make-overlay pos end)))
            (goto-char pos)
            )
          )
        )
      ) ;let
    ))

(defun web-mode-comment-or-uncomment-region (beg end &optional arg)
  (interactive)
  (save-excursion
    (push-mark end)
    (goto-char beg)
    (setq mark-active t)
    (web-mode-comment-or-uncomment)
    (pop-mark)))

(defun web-mode-comment-or-uncomment ()
  "Comment or uncomment line(s), block or region at POS."
  (interactive)
  ;; TODO : if mark is at eol, mark--
  (if (and (not mark-active) (looking-at-p "[[:space:]]*$"))
      (web-mode-comment-insert)
    (when (and (use-region-p) (eq (point) (region-end)))
      (if (bolp) (backward-char))
      (exchange-point-and-mark))
    (skip-chars-forward "[:space:]" (line-end-position))
    (cond
     ((or (eq (get-text-property (point) 'tag-type) 'comment)
          (eq (get-text-property (point) 'block-token) 'comment)
          (eq (get-text-property (point) 'part-token) 'comment))
      (web-mode-uncomment (point)))
     (t
      (web-mode-comment (point)))
     )
    ) ;if
  )

(defun web-mode-comment-insert ()
  (cond
   ((get-text-property (point) 'block-side)
    (insert "/*  */")
    (search-backward " */"))
   ((get-text-property (point) 'part-side)
    (insert "/*  */")
    (search-backward " */"))
   (t
    (insert "<!--  -->")
    (search-backward " -->"))
   )
  )

(defun web-mode-comment-indent-new-line (&optional soft)
  (interactive)
  (let (ctx)
    (setq ctx (web-mode-comment-context))
    (if (null ctx) nil
      ;; (message "ctx=%S" ctx)
      (newline 1)
      (indent-line-to (plist-get ctx :col))
      (insert (concat (plist-get ctx :prefix) ""))
      ) ;if
    ))

(defun web-mode-comment-context (&optional pos)
  (cond
   (pos
    )
   ((and (eolp) (not (bobp)))
    (setq pos (1- (point))))
   (t
    (setq pos (point)))
   ) ;cond
  (let (beg col prefix type format)
    (cond
     ((eq (get-text-property pos 'block-token) 'comment)
      (setq type "block"))
     ((eq (get-text-property pos 'tag-type) 'comment)
      (setq type "tag"))
     ((eq (get-text-property pos 'part-token) 'comment)
      (setq type "part"))
     )
    (if (null type) nil
      (save-excursion
        (goto-char pos)
        (web-mode-comment-beginning)
        (setq beg (point)
              col (current-column))
        (cond
         ((looking-at-p "/\\*")
          (setq format "/*"
                prefix " * "))
         ((looking-at-p "//")
          (setq format "//"
                prefix "//"))
         ((looking-at-p "#")
          (setq format "#"
                prefix "#"))
         ((looking-at-p ";")
          (setq format ";"
                prefix ";"))
         ) ;cond
        (list :beg beg :col col :prefix prefix :type type :format format)))))

(defun web-mode-comment (pos)
  (let (ctx language col sel beg end tmp block-side single-line-block pos-after content)

    (setq pos-after pos)

    (setq block-side (get-text-property pos 'block-side))
    (setq single-line-block (web-mode-is-single-line-block pos))

    (cond

     ((and block-side (string= web-mode-engine "erb"))
      (web-mode-comment-erb-block pos)
      )

     ((and single-line-block block-side
           (intern-soft (concat "web-mode-comment-" web-mode-engine "-block")))
        (funcall (intern (concat "web-mode-comment-" web-mode-engine "-block")) pos)
        )

     (t
      (setq ctx (web-mode-point-context
                 (if mark-active (region-beginning) (line-beginning-position))))
      (setq language (plist-get ctx :language))
      (setq col (current-column))
      (cond
       (mark-active
        ;;(message "%S %S" (point) col)
        )
       ((and (member language '("html" "xml"))
             (get-text-property (progn (back-to-indentation) (point)) 'tag-beg))
        (web-mode-element-select))
       (t
        (end-of-line)
        (set-mark (line-beginning-position)))
       ) ;cond

      (setq beg (region-beginning)
            end (region-end))

      (when (> (point) (mark))
        (exchange-point-and-mark))

      (if (and (eq (char-before end) ?\n)
               (not (eq (char-after end) ?\n)))
          (setq end (1- end)))

      (setq sel (buffer-substring-no-properties beg end))

      (cond

       ((member language '("html" "xml"))
        (cond
           ((and (= web-mode-comment-style 2) (string= web-mode-engine "django"))
            (setq content (concat "{# " sel " #}")))
           ((and (= web-mode-comment-style 2) (member web-mode-engine '("ejs" "erb")))
            (setq content (concat "<%# " sel " %>")))
           ((and (= web-mode-comment-style 2) (string= web-mode-engine "aspx"))
            (setq content (concat "<%-- " sel " --%>")))
           ((and (= web-mode-comment-style 2) (string= web-mode-engine "smarty"))
            (setq content (concat "{* " sel " *}")))
           ((and (= web-mode-comment-style 2) (string= web-mode-engine "blade"))
            (setq content (concat "{{-- " sel " --}}")))
           ((and (= web-mode-comment-style 2) (string= web-mode-engine "ctemplate"))
            (setq content (concat "{{!-- " sel " --}}")))
           ((and (= web-mode-comment-style 2) (string= web-mode-engine "razor"))
            (setq content (concat "@* " sel " *@")))
           (t
            (setq content (concat "<!-- " sel " -->"))
            (when (< (length sel) 1)
              (search-backward " -->")
              (setq pos-after nil))
            ))
        ) ;case html

       ((member language '("php" "javascript" "java" "jsx"))
        (let (alt)
          (cond
           ((get-text-property pos 'jsx-depth)
            (setq content (concat "{/* " sel " */}")))
           ((and (setq alt (cdr (assoc language web-mode-comment-formats)))
                 (string= alt "//"))
            (setq content (replace-regexp-in-string (concat "\n[ ]\\{" (number-to-string col) "\\}") "\n// " sel))
            (setq content (concat "// " content))
            ;;(setq content (replace-regexp-in-string "^[ ]*" alt sel))
            )
           (web-mode-comment-prefixing
            (setq content (replace-regexp-in-string (concat "\n[ ]\\{" (number-to-string col) "\\}") "\n* " sel))
            (setq content (concat "/* " content "*/")))
           (t
            (setq content (concat "/* " sel " */")))
           ) ;cond
          ) ;let
        )

       ((member language '("erb"))
        (setq content (replace-regexp-in-string "^[ ]*" "#" sel)))

       ((member language '("asp"))
        (setq content (replace-regexp-in-string "^[ ]*" "''" sel)))

       (t
        (setq content (concat "/* " sel " */")))

       ) ;cond

      (when content
        (delete-region beg end)
        (deactivate-mark)
        (let (beg end)
          (setq beg (point-at-bol))
          (insert content)
          (setq end (point-at-eol))
          (indent-region beg end)
          )
        ) ;when

      ) ;t
     ) ;cond

    (when pos-after (goto-char pos-after))

    ))

(defun web-mode-comment-ejs-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-insert-text-at-pos "//" (+ beg 2))))

(defun web-mode-comment-erb-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-insert-text-at-pos "#" (+ beg 2))))

(defun web-mode-comment-django-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-insert-text-at-pos "#" end)
    (web-mode-insert-text-at-pos "#" (1+ beg))))

(defun web-mode-comment-dust-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-insert-text-at-pos "!" end)
    (web-mode-insert-text-at-pos "!" (1+ beg))))

(defun web-mode-comment-aspx-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-insert-text-at-pos "#" end)
    (web-mode-insert-text-at-pos "#" (1+ beg))))

(defun web-mode-comment-jsp-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-insert-text-at-pos "--" (+ beg 2))))

(defun web-mode-comment-go-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-insert-text-at-pos "/" (+ beg 2))))

(defun web-mode-comment-php-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-insert-text-at-pos "*/" (- end 1))
    (web-mode-insert-text-at-pos "/*" (+ beg (if (web-mode-looking-at "<\\?php" beg) 5 3)))))

(defun web-mode-comment-boundaries (&optional pos)
  (interactive)
  (unless pos (setq pos (point)))
  (let ((beg pos) (end pos) prop)
    (save-excursion
      (goto-char pos)
      (setq prop
            (cond
             ((eq (get-text-property pos 'block-token) 'comment) 'block-token)
             ((eq (get-text-property pos 'tag-type) 'comment) 'tag-type)
             ((eq (get-text-property pos 'part-token) 'comment) 'part-token)
             (t nil)
             ))
      (if (null prop)
          (setq beg nil
                end nil)
        (when (and (not (bobp))
                   (eq (get-text-property pos prop) (get-text-property (1- pos) prop)))
          (setq beg (or (previous-single-property-change pos prop) (point-min))))
        (when (and (not (eobp))
                   (eq (get-text-property pos prop) (get-text-property (1+ pos) prop)))
          (setq end (or (next-single-property-change pos prop) (point-max)))))
      (when (and beg (string= (buffer-substring-no-properties beg (+ beg 2)) "//"))
        (goto-char end)
        (while (and (looking-at-p "\n[ ]*//")
                    (not (eobp)))
          (search-forward "//")
          (backward-char 2)
          ;;(message "%S" (point))
          (setq end (next-single-property-change (point) prop))
          (goto-char end)
          ;;(message "%S" (point))
          ) ;while
        ) ;when
      (when end (setq end (1- end)))
      ) ;save-excursion
    ;;(message "beg=%S end=%S" beg end)
    (if (and beg end) (cons beg end) nil)
    ))

(defun web-mode-uncomment (pos)
  (let ((beg pos) (end pos) (sub2 "") comment boundaries)
    (save-excursion
      (cond
       ((and (get-text-property pos 'block-side)
             (intern-soft (concat "web-mode-uncomment-" web-mode-engine "-block")))
        (funcall (intern (concat "web-mode-uncomment-" web-mode-engine "-block")) pos))
       ((and (setq boundaries (web-mode-comment-boundaries pos))
             (setq beg (car boundaries))
             (setq end (1+ (cdr boundaries)))
             (> (- end beg) 4))
        ;;(message "beg(%S) end(%S)" beg end)
        (setq comment (buffer-substring-no-properties beg end))
        (setq sub2 (substring comment 0 2))
        (cond
         ((member sub2 '("<!" "<%"))
          (setq comment (replace-regexp-in-string "\\(^<[!%]--[ ]?\\|[ ]?--[%]?>$\\)" "" comment)))
         ((string= sub2 "{#")
          (setq comment (replace-regexp-in-string "\\(^{#[ ]?\\|[ ]?#}$\\)" "" comment)))
         ((string= sub2 "{/") ;jsx comments
          (setq comment (replace-regexp-in-string "\\(^{/\\*[ ]?\\|[ ]?\\*/}$\\)" "" comment)))
         ((string= sub2 "/*")
          (setq comment (replace-regexp-in-string "\\(^/\\*[ ]?\\|[ ]?\\*/$\\|^[ \t]*\\*\\)" "" comment)))
         ((string= sub2 "//")
          (setq comment (replace-regexp-in-string "\\(//\\)" "" comment)))
         ) ;cond
        (delete-region beg end)
        (web-mode-insert-and-indent comment)
        (goto-char beg)
        )
       ) ;cond
      (indent-according-to-mode)
      )))

(defun web-mode-uncomment-erb-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (if (string-match-p "<[%[:alpha:]]" (buffer-substring-no-properties (+ beg 2) (- end 2)))
        (progn
          (web-mode-remove-text-at-pos 2 (1- end))
          (web-mode-remove-text-at-pos 3 beg))
      (web-mode-remove-text-at-pos 1 (+ beg 2))
      ) ;if
    )
  )

(defun web-mode-uncomment-ejs-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-remove-text-at-pos 1 (+ beg 2))))

(defun web-mode-uncomment-django-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-remove-text-at-pos 2 (1- end))
    (web-mode-remove-text-at-pos 2 beg)))

(defun web-mode-uncomment-ctemplate-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-remove-text-at-pos 5 (- end 4))
    (web-mode-remove-text-at-pos 5 beg)))

(defun web-mode-uncomment-dust-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-remove-text-at-pos 1 (1- end))
    (web-mode-remove-text-at-pos 1 (1+ beg))))

(defun web-mode-uncomment-aspx-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-remove-text-at-pos 1 (1- end))
    (web-mode-remove-text-at-pos 1 (1+ beg))))

(defun web-mode-uncomment-jsp-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-remove-text-at-pos 2 (+ beg 2))))

(defun web-mode-uncomment-go-block (pos)
  (let (beg end)
    (setq beg (web-mode-block-beginning-position pos)
          end (web-mode-block-end-position pos))
    (web-mode-remove-text-at-pos 1 (+ beg 2))))

(defun web-mode-snippet-names ()
  (let (codes)
    (dolist (snippet web-mode-snippets)
      (add-to-list 'codes (car snippet) t))
    codes))

(defun web-mode-snippet-insert (code)
  "Insert a snippet."
  (interactive
   (list (completing-read "Snippet: " (web-mode-snippet-names))))
  (let (beg
        (continue t)
        (counter 0)
        end
        sel
        snippet
        (l (length web-mode-snippets))
        pos)
    (when mark-active
      (setq sel (web-mode-trim (buffer-substring-no-properties
                                (region-beginning) (region-end))))
      (delete-region (region-beginning) (region-end)))
    (while (and continue (< counter l))
      (setq snippet (nth counter web-mode-snippets))
      (when (string= (car snippet) code)
        (setq continue nil))
      (setq counter (1+ counter)))
    (when snippet
      (setq snippet (cdr snippet))
      (setq beg (point-at-bol))
      (insert snippet)
      (setq pos (point)
            end (point))
      (when (string-match-p "|" snippet)
        (search-backward "|")
        (delete-char 1)
        (setq pos (point)
              end (1- end)))
      (when sel
        (insert sel)
        (setq pos (point)
              end (+ end (length sel))))
      (goto-char end)
      (setq end (point-at-eol))
      (unless sel (goto-char pos))
      (indent-region beg end))
    ))

(defun web-mode-looking-at (regexp pos)
  (save-excursion
    (goto-char pos)
    (looking-at regexp)))

(defun web-mode-looking-at-p (regexp pos)
  (save-excursion
    (goto-char pos)
    (looking-at-p regexp)))

(defun web-mode-looking-back (regexp pos &optional limit greedy)
  (save-excursion
    (goto-char pos)
    (if limit
        (looking-back regexp limit greedy)
      (looking-back regexp))))

(defun web-mode-insert-text-at-pos (text pos)
  (let ((mem web-mode-enable-auto-pairing))
    (setq web-mode-enable-auto-pairing nil)
    (save-excursion
      (goto-char pos)
      (insert text)
      (setq web-mode-enable-auto-pairing mem)
      )))

(defun web-mode-remove-text-at-pos (n &optional pos)
  (unless pos (setq pos (point)))
  (delete-region pos (+ pos n)))

(defun web-mode-insert-and-indent (text)
  (let (beg end)
    (setq beg (point-at-bol))
    (insert text)
    (setq end (point-at-eol))
    (indent-region beg end)
    ))

(defun web-mode-indentation-at-pos (pos)
  (save-excursion
    (goto-char pos)
    (current-indentation)))

(defun web-mode-navigate (&optional pos)
  "Move point to the matching opening/closing tag/block."
  (interactive)
  (unless pos (setq pos (point)))
  (let (init)
    (goto-char pos)
    (setq init (point))
    (when (> (current-indentation) (current-column))
      (back-to-indentation))
    (setq pos (point))
    (cond
     ((and (get-text-property pos 'block-side)
           (web-mode-block-beginning)
           (web-mode-block-controls-get (point)))
      (web-mode-block-match))
     ((member (get-text-property pos 'tag-type) '(start end))
      (web-mode-tag-beginning)
      (web-mode-tag-match))
     (t
      (goto-char init))
     )
    ))

(defun web-mode-block-match (&optional pos)
  (unless pos (setq pos (point)))
  (let (pos-ori controls control (counter 1) type (continue t) pair)
    (setq pos-ori pos)
    (goto-char pos)
    (setq controls (web-mode-block-controls-get pos))
    ;;(message "controls=%S" controls)
    (cond
     (controls
      (setq pair (car controls))
      (setq control (cdr pair))
      (setq type (car pair))
      (when (eq type 'inside) (setq type 'close))
      (while continue
        (cond
         ((and (> pos-ori 1) (bobp))
          (setq continue nil))
         ((or (and (eq type 'open) (not (web-mode-block-next)))
              (and (eq type 'close) (not (web-mode-block-previous))))
          (setq continue nil)
          )
         ((null (setq controls (web-mode-block-controls-get (point))))
          )
         (t
          ;;TODO : est il nécessaire de faire un reverse sur controls si on doit matcher backward
          (dolist (pair controls)
            (cond
             ((not (string= (cdr pair) control))
              )
             ((eq (car pair) 'inside)
              )
             ((eq (car pair) type)
              (setq counter (1+ counter)))
             (t
              (setq counter (1- counter)))
             )
            ) ;dolist
          (when (= counter 0)
            (setq continue nil))
          ) ;t
         ) ;cond
        ) ;while
      (if (= counter 0) (point) nil)
      ) ;controls
     (t
      (goto-char pos-ori)
      nil
      ) ;controls = nul
     ) ;conf
    ))

(defun web-mode-tag-match (&optional pos)
  "Move point to the matching opening/closing tag."
  (interactive)
  (unless pos (setq pos (point)))
  (let (regexp)
    (setq regexp (concat "</?" (get-text-property pos 'tag-name)))
    (when (member (get-text-property pos 'tag-type) '(start end))
      (web-mode-tag-beginning)
      (setq pos (point)))
    (if (eq (get-text-property pos 'tag-type) 'end)
        (web-mode-tag-fetch-opening regexp pos)
      (web-mode-tag-fetch-closing regexp pos))
    t))

(defun web-mode-tag-fetch-opening (regexp pos)
  (let ((counter 1) (n 0) (type nil))
    (goto-char pos)
    (while (and (> counter 0) (re-search-backward regexp nil t))
      (when (and (get-text-property (point) 'tag-beg)
                 (member (get-text-property (point) 'tag-type) '(start end)))
        (setq n (1+ n))
        (cond
         ((eq (get-text-property (point) 'tag-type) 'end)
          (setq counter (1+ counter)))
         (t
          (setq counter (1- counter))
          )
         )
        )
      )
    (if (= n 0) (goto-char pos))
    ))

(defun web-mode-tag-fetch-closing (regexp pos)
  (let ((counter 1) (n 0))
    (goto-char pos)
    (web-mode-tag-end)
    (while (and (> counter 0) (re-search-forward regexp nil t))
      (when (get-text-property (match-beginning 0) 'tag-beg)
        (setq n (1+ n))
        (if (eq (get-text-property (point) 'tag-type) 'end)
            (setq counter (1- counter))
          (setq counter (1+ counter))))
      )
    (if (> n 0)
        (web-mode-tag-beginning)
      (goto-char pos))
    ))

(defun web-mode-element-tag-name (&optional pos)
  (unless pos (setq pos (point)))
  (save-excursion
    (goto-char pos)
    (if (and (web-mode-tag-beginning)
             (looking-at "</?\\([[:alpha:]][[:alnum:]:-]*\\)"))
        (match-string-no-properties 1)
      nil)))

(defun web-mode-element-close ()
  "Close html element."
  (interactive)
  (let (jump epp ins tag)

    (if (and (eq (char-before) ?\>)
             (web-mode-element-is-void (get-text-property (1- (point)) 'tag-name)))
        (unless (eq (char-before (1- (point))) ?\/)
          (backward-char)
          (insert "/")
          (forward-char))
      (setq epp (web-mode-element-parent-position)))

    ;;(message "epp=%S" epp)
    (when epp
      (setq tag (get-text-property epp 'tag-name))
      (setq tag (web-mode-element-tag-name epp))
      ;;(message "tag=%S %c" tag (char-before))
      (cond
       ((or (null tag) (web-mode-element-is-void tag))
        (setq epp nil))
       ((looking-back "</")
        (setq ins tag))
       ((looking-back "<")
        (setq ins (concat "/" tag)))
       (t
        ;;auto-close-style = 2
        ;;(message "%S %c" (point) (char-after))
        (when (and (looking-at-p "[[:alpha:]]") (> (length tag) 4))
          (dolist (elt '("div" "span" "strong" "pre" "li"))
            (when (and (string-match-p (concat "^" elt) tag) (not (string= tag elt)))
              (setq tag elt)
              (put-text-property epp (point) 'tag-name tag))
            )
          ) ;when
        (if (web-mode-element-is-void (get-text-property (point) 'tag-name))
            (setq ins nil
                  epp nil)
          (setq ins (concat "</" tag)))
        )
       ) ;cond
      (when ins
        (unless (looking-at-p "[ ]*>")
          (setq ins (concat ins ">")))
        (insert ins)
        (save-excursion
          (search-backward "<")
          (setq jump (and (eq (char-before) ?\>)
                          (string= (get-text-property (1- (point)) 'tag-name) tag)))
          (if jump (setq jump (point)))
          ) ;save-excursion
        (if jump (goto-char jump))
        ) ;when not ins
      ) ;when epp
    epp))

(defun web-mode-detect-content-type ()
  (cond
   ((and (string= web-mode-engine "none")
         (< (point) 16)
         (eq (char-after 1) ?\#)
         (string-match-p "php" (buffer-substring-no-properties
                                (line-beginning-position)
                                (line-end-position))))
    (web-mode-set-engine "php"))
   ((and (string= web-mode-content-type "javascript")
         (< (point) web-mode-chunk-length)
         (eq (char-after (point-min)) ?\/)
         (string-match-p "@jsx" (buffer-substring-no-properties
                                 (line-beginning-position)
                                 (line-end-position))))
    (web-mode-set-content-type "jsx"))
   ))

(defun web-mode-on-after-change (beg end len)
 ;;(message "after-change: pos=%d, beg=%d, end=%d, len=%d, ocmd=%S, cmd=%S" (point) beg end len this-original-command this-command)
 ;;(backtrace)
 ;;(message "this-command=%S" this-command)
  (when (eq this-original-command 'yank)
    (setq web-mode-inhibit-fontification t))
  (when (or (null web-mode-change-beg) (< beg web-mode-change-beg))
    (setq web-mode-change-beg beg))
  (when (or (null web-mode-change-end) (> end web-mode-change-end))
    (setq web-mode-change-end end))
  )

(defun web-mode-complete ()
  "Autocomple at point."
  (interactive)
  (let ((pos (point))
        (char (char-before))
        (chunk (buffer-substring-no-properties (- (point) 2) (point)))
        (auto-closed   nil)
        (auto-expanded nil)
        (auto-paired   nil)
        (auto-quoted   nil)
        expanders)

    ;;-- auto-closing
    (when (and web-mode-enable-auto-closing
               (>= pos 4)
               (or (string= "</" chunk)
                   ;;(progn (message "%c" char) nil)
                   (and (= web-mode-auto-close-style 2)
                        (or (string= web-mode-content-type "jsx")
                            (not (get-text-property pos 'part-side)))
                        (string-match-p "[[:alnum:]'\"]>" chunk)))
               (not (get-text-property (- pos 2) 'block-side))
               (web-mode-element-close))
      (setq auto-closed t))

    ;;-- auto-pairing
    (when (and web-mode-enable-auto-pairing
               (>= pos 4)
               (not auto-closed))
      (let ((i 0) expr after pos-end (l (length web-mode-auto-pairs)))
        (setq pos-end (if (> (+ pos 32) (line-end-position))
                          (line-end-position)
                        (+ pos 10)))
        (setq chunk (buffer-substring-no-properties (- pos 3) pos)
              after (buffer-substring-no-properties pos pos-end))
        (while (and (< i l) (not auto-paired))
          (setq expr (elt web-mode-auto-pairs i)
                i (1+ i))
          ;;(message "chunk=%S expr=%S after=%S" chunk expr after)
          (when (and (string= (car expr) chunk)
                     (not (string-match-p (regexp-quote (cdr expr)) after)))
            (setq auto-paired t)
            (insert (cdr expr))
            (if (string-match-p "|" (cdr expr))
                (progn
                  (search-backward "|")
                  (delete-char 1))
              (goto-char pos))
            ) ;when
          ) ;while
        ) ;let
      )

    ;;-- auto-expanding
    (when (and web-mode-enable-auto-expanding
               (not auto-closed)
               (not auto-paired)
               (eq char ?\/)
               (not (get-text-property (1- pos) 'tag-type))
               (not (get-text-property (1- pos) 'part-side))
               (not (get-text-property (1- pos) 'block-side))
               (looking-back "\\(^\\|[[:punct:][:space:]>]\\)./"))
      (setq expanders (append web-mode-expanders web-mode-extra-expanders))
      (let ((i 0) pair (l (length expanders)))
        (setq chunk (buffer-substring-no-properties (- pos 2) pos))
        ;;(message "%S" chunk)
        (while (and (< i l) (not auto-expanded))
          (setq pair (elt expanders i)
                i (1+ i))
          (when (string= (car pair) chunk)
            (setq auto-expanded t)
            (delete-char -2)
            (insert (cdr pair))
            (when (string-match-p "|" (cdr pair))
              (search-backward "|")
              (delete-char 1))
            ) ;when
          ) ;while
        ) ;let
      )

    ;;-- auto-quoting
    (when (and web-mode-enable-auto-quoting
               (>= pos 4)
               (not (get-text-property pos 'block-side))
               (not auto-closed)
               (not auto-paired)
               (not auto-expanded)
               (get-text-property (- pos 2) 'tag-attr)
               )
      (cond
       ((and (eq char ?\=)
             (not (looking-at-p "[ ]*[\"']")))
        (insert "\"\"")
        (backward-char)
        (setq auto-quoted t))
       ((and (eq char ?\")
             (looking-back "=[ ]*\"")
             (not (looking-at-p "[ ]*[\"]")))
        (insert-and-inherit "\"")
        (backward-char)
        (setq auto-quoted t))
       ((and (eq char ?\')
             (looking-back "=[ ]*'")
             (not (looking-at-p "[ ]*[']")))
        (insert-and-inherit "'")
        (backward-char)
        (setq auto-quoted t))
       ((and (eq char ?\")
             (eq (char-after) ?\"))
        (delete-char 1)
        (cond
         ((looking-back "=\"\"")
          (backward-char))
         ((eq (char-after) ?\s)
          (forward-char))
         (t
          (insert " "))
         ) ;cond
        )
       ) ;cond
      ) ;when

    ;;--
    (cond
     ((or auto-closed auto-paired auto-expanded auto-quoted)
      (when (and web-mode-change-end
                 (>= (line-end-position) web-mode-change-end))
        (setq web-mode-change-end (line-end-position)))
      (list :auto-closed auto-closed
            :auto-paired auto-paired
            :auto-expanded auto-expanded
            :auto-quoted auto-quoted))
     (t
      nil)
     )

    ))

(defun web-mode-on-post-command ()
  (let (ctx n char)

    ;;(message "this-command=%S (%S)" this-command web-mode-expand-previous-state)
    ;;(message "%S: %S %S" this-command web-mode-change-beg web-mode-change-end)

    (when (and web-mode-expand-previous-state
               (not (member this-command '(web-mode-mark-and-expand
                                           er/expand-region
                                           mc/mark-next-like-this))))
      (when (eq this-command 'keyboard-quit)
        (goto-char web-mode-expand-initial-pos))
      (deactivate-mark)
      (when web-mode-expand-initial-scroll
        (set-window-start (selected-window) web-mode-expand-initial-scroll)
        )
      (setq web-mode-expand-previous-state nil
            web-mode-expand-initial-pos nil
            web-mode-expand-initial-scroll nil))

    (when (member this-command '(yank))
      (let ((beg web-mode-change-beg) (end web-mode-change-end))
        (setq web-mode-inhibit-fontification nil)
        (when (and web-mode-change-beg web-mode-change-end)
          (save-excursion
            (font-lock-fontify-region web-mode-change-beg web-mode-change-end))
          (when web-mode-enable-auto-indentation
            (indent-region beg end))
          ) ;and
        )
      )

    (when (< (point) 16)
      (web-mode-detect-content-type))

    (when (and web-mode-enable-engine-detection
               (or (null web-mode-engine) (string= web-mode-engine "none"))
               (< (point) web-mode-chunk-length)
               (web-mode-detect-engine))
      (web-mode-on-engine-setted)
      (web-mode-buffer-highlight))

    (when (> (point) 1)
      (setq char (char-before)))

    (cond

     ((null char)
      )

     ((and (>= (point) 3)
           (member this-command '(self-insert-command))
           (not (member (get-text-property (point) 'part-token) '(comment string))))
      (setq ctx (web-mode-complete)))

     ((and web-mode-enable-auto-opening
           (member this-command '(newline electric-newline-and-maybe-indent))
           (or (and (not (eobp))
                    (eq (char-after) ?\<)
                    (eq (get-text-property (point) 'tag-type) 'end)
                    (looking-back ">\n[ \t]*")
                    (setq n (length (match-string-no-properties 0)))
                    (eq (get-text-property (- (point) n) 'tag-type) 'start)
                    (string= (get-text-property (- (point) n) 'tag-name)
                             (get-text-property (point) 'tag-name))
                    )
               (and (get-text-property (1- (point)) 'block-side)
                    (string= web-mode-engine "php")
                    (looking-back "<\\?php[ ]*\n")
                    (looking-at-p "[ ]*\\?>"))))
      (newline-and-indent)
      (forward-line -1)
      (indent-according-to-mode)
      )
     ) ;cond

    (when (and web-mode-enable-auto-indentation
               (member this-command '(self-insert-command))
               (or (and ctx
                        (or (plist-get ctx :auto-closed)
                            (plist-get ctx :auto-expanded)))
                   (and (> (point) (point-min))
                        (get-text-property (1- (point)) 'tag-end)
                        (get-text-property (line-beginning-position) 'tag-beg))))
      (indent-according-to-mode)
      (when (and web-mode-change-end (> web-mode-change-end (point-max)))
        (message "post-command: enlarge web-mode-change-end")
        (setq web-mode-change-end (point-max))
        )
      ) ;when auto-indent

    (when web-mode-enable-current-element-highlight
      (web-mode-highlight-current-element))

    (when (and web-mode-enable-current-column-highlight
               (not (web-mode-buffer-narrowed-p)))
      (web-mode-column-show))

    ;;(message "post-command (%S) (%S)" web-mode-change-end web-mode-change-end)

    ))

(defun web-mode-dom-apostrophes-replace ()
  "Replace char(') with char(’) in the html contents of the buffer."
  (interactive)
  (save-excursion
    (let ((min (point-min)) (max (point-max)))
      (when mark-active
        (setq min (region-beginning)
              max (region-end))
        (deactivate-mark))
      (goto-char min)
      (while (web-mode-content-rsf "\\([[:alpha:]]\\)'\\([[:alpha:]]\\)" max)
        (replace-match "\\1’\\2"))
      )))

(defun web-mode-dom-entities-encode ()
  (save-excursion
    (let (regexp ms elt (min (point-min)) (max (point-max)))
      (when mark-active
        (setq min (region-beginning)
              max (region-end))
        (deactivate-mark))
      (goto-char min)
      (setq regexp "[")
      (dolist (pair web-mode-html-entities)
        (setq regexp (concat regexp (char-to-string (cdr pair))))
        )
      (setq regexp (concat regexp "]"))
      (while (web-mode-content-rsf regexp max)
        (setq elt (match-string-no-properties 0))
        (setq elt (aref elt 0))
        (setq elt (car (rassoc elt web-mode-html-entities)))
        (replace-match (concat "&" elt ";"))
        ) ;while
      )))

(defun web-mode-dom-entities-replace ()
  "Replace html entities (e.g. &eacute; &#233; or &#x00E9; become é)"
  (interactive)
  (save-excursion
    (let (ms pair elt (min (point-min)) (max (point-max)))
      (when mark-active
        (setq min (region-beginning)
              max (region-end))
        (deactivate-mark))
      (goto-char min)
      (while (web-mode-content-rsf "&\\([#]?[[:alnum:]]\\{2,8\\}\\);" max)
        (setq elt nil)
        (setq ms (match-string-no-properties 1))
        (cond
         ((not (eq (aref ms 0) ?\#))
          (and (setq pair (assoc ms web-mode-html-entities))
               (setq elt (cdr pair))
               (setq elt (char-to-string elt))))
         ((eq (aref ms 1) ?x)
          (setq elt (substring ms 2))
          (setq elt (downcase elt))
          (setq elt (string-to-number elt 16))
          (setq elt (char-to-string elt)))
         (t
          (setq elt (substring ms 1))
          (setq elt (char-to-string (string-to-number elt))))
         ) ;cond
        (when elt (replace-match elt))
        ) ;while
      )))

(defun web-mode-dom-xml-replace ()
  "Replace &, > and < in html content."
  (interactive)
  (save-excursion
    (let (expr (min (point-min)) (max (point-max)))
      (when mark-active
        (setq min (region-beginning)
              max (region-end))
        (deactivate-mark))
      (goto-char min)
      (while (web-mode-content-rsf "[&<>]" max)
        (replace-match (cdr (assq (char-before) web-mode-xml-chars)) t t))
      )))

(defun web-mode-dom-quotes-replace ()
  "Replace dumb quotes."
  (interactive)
  (save-excursion
    (let (expr (min (point-min)) (max (point-max)))
      (when mark-active
        (setq min (region-beginning)
              max (region-end))
        (deactivate-mark))
      (goto-char min)
      (setq expr (concat (car web-mode-smart-quotes) "\\2" (cdr web-mode-smart-quotes)))
      (while (web-mode-content-rsf "\\(\"\\)\\(.\\{1,200\\}\\)\\(\"\\)" max)
        (replace-match expr)
        ) ;while
      )))

(defun web-mode-dom-xpath (&optional pos)
  "Display html path."
  (interactive)
  (unless pos (setq pos (point)))
  (save-excursion
    (goto-char pos)
    (let (path)
      (while (web-mode-element-parent)
        (setq path (cons (get-text-property (point) 'tag-name) path))
        )
      (message "/%s" (mapconcat 'identity path "/"))
      )))

(defun web-mode-block-ends-with (regexp &optional pos)
  (unless pos (setq pos (point)))
  (save-excursion
    (goto-char pos)
    (save-match-data
      (if (stringp regexp)
          (and (web-mode-block-end)
               (progn (backward-char) t)
               (web-mode-block-skip-blank-backward)
               (progn (forward-char) t)
               (looking-back regexp))
        (let ((pair regexp)
              (block-beg (web-mode-block-beginning-position pos))
              (block-end (web-mode-block-end-position pos)))
          (and (web-mode-block-end)
               (web-mode-block-sb (car pair) block-beg)
               (not (web-mode-sf (cdr pair) block-end)))
          ) ;let
        ) ;if
      )))

(defun web-mode-block-token-starts-with (regexp &optional pos)
  (unless pos (setq pos (point)))
  (save-excursion
    (and (goto-char pos)
         (web-mode-block-token-beginning)
         (skip-chars-forward "[\"']")
         (looking-at regexp))
    ))

(defun web-mode-block-starts-with (regexp &optional pos)
  (unless pos (setq pos (point)))
  (save-excursion
    (and (web-mode-block-beginning)
         (web-mode-block-skip-blank-forward)
         (looking-at regexp))
    ))

(defun web-mode-block-skip-blank-backward (&optional pos)
  (unless pos (setq pos (point)))
  (let ((continue t))
    (goto-char pos)
    (while continue
      (if (and (get-text-property (point) 'block-side)
               (not (bobp))
               (or (member (char-after) '(?\s ?\n))
                   (member (get-text-property (point) 'block-token)
                           '(delimiter-beg delimiter-end comment))))
          (backward-char)
        (setq continue nil))
      ) ;while
    (point)))

(defun web-mode-block-skip-blank-forward (&optional pos)
  (unless pos (setq pos (point)))
  (let ((continue t))
    (goto-char pos)
    (while continue
      (if (and (get-text-property (point) 'block-side)
               (or (member (char-after) '(?\s ?\n ?\t))
                   (member (get-text-property (point) 'block-token)
                           '(delimiter-beg delimiter-end comment))))
          (forward-char)
        (setq continue nil))
      ) ;while
;;    (message "pt=%S" (point))
    (point)))

(defun web-mode-tag-attributes-sort (&optional pos)
  "Sort the attributes inside the current html tag."
  (interactive)
  (unless pos (setq pos (point)))
  (save-excursion
    (let (attrs (continue t) min max tag-beg tag-end attr attr-name attr-beg attr-end indent indentation sorter ins)
      (if (not (member (get-text-property pos 'tag-type) '(start void)))
          nil
        (setq tag-beg (web-mode-tag-beginning-position pos)
              tag-end (web-mode-tag-end-position))
;;        (message "%S %S" tag-beg tag-end)
        (goto-char tag-beg)
        (while continue
          (if (or (not (web-mode-attribute-next))
                  (>= (point) tag-end))
              (setq continue nil)
            ;;(message "attr=%S" (point))
            (setq attr-beg (web-mode-attribute-beginning-position)
                  attr-end (1+ (web-mode-attribute-end-position)))
            (when (null min)
              (setq min attr-beg))
            (setq max attr-end)
            (goto-char attr-beg)
            (setq attr (buffer-substring-no-properties attr-beg attr-end))
            (if (string-match "^\\([[:alnum:]-]+\\)=" attr)
                (setq attr-name (match-string-no-properties 1 attr))
              (setq attr-name attr))
            (setq indent (looking-back "^[ \t]*"))
            (setq attrs (append attrs (list (list attr-beg attr-end attr-name attr indent))))
            ) ;if
          ) ;while
        ) ;if in tag
      (when attrs
        (setq sorter (function
                      (lambda (elt1 elt2)
                        (string< (nth 2 elt1) (nth 2 elt2))
                        )))
        (setq attrs (sort attrs sorter))
        (delete-region (1- min) max)
        (setq ins "")
        (dolist (elt attrs)
          (if (and (nth 4 elt) (> (length ins) 1))
              (setq ins (concat ins "\n"))
            (setq ins (concat ins " ")))
          (setq ins (concat ins (nth 3 elt)))
          )
        (goto-char (1- min))
        (insert ins)
        (web-mode-tag-beginning)
        (setq min (line-beginning-position))
        (web-mode-tag-end)
        (setq max (line-end-position))
        (indent-region min max)
        )
      ;;(message "attrs=%S" attrs)
      )))

(defun web-mode-attribute-insert ()
  "Insert an attribute inside current tag."
  (interactive)
  (let (attr attr-name attr-value)
    (cond
     ((not (eq (get-text-property (point) 'tag-type) 'start))
      (message "attribute-insert ** invalid context **"))
     ((not (and (setq attr-name (read-from-minibuffer "Attribute name? "))
                (> (length attr-name) 0)))
      (message "attribute-insert ** failure **"))
     (t
      (setq attr (concat " " attr-name))
      (when (setq attr-value (read-from-minibuffer "Attribute value? "))
        (setq attr (concat attr "=\"" attr-value "\"")))
      (web-mode-tag-end)
      (re-search-backward "/?>")
      (insert attr)
      )
     ) ;cond
    ))

(defun web-mode-attribute-transpose (&optional pos)
  "Transpose the current html attribute."
  (interactive)
  (unless pos (setq pos (point)))
  (let (ret attr-beg attr-end next-beg next-end tag-end)
    (when (and (get-text-property pos 'tag-attr)
               (setq next-beg (web-mode-attribute-next-position pos))
               (setq next-end (web-mode-attribute-end-position next-beg))
               (setq tag-end (web-mode-tag-end-position pos))
               (> tag-end next-end))
      (setq attr-beg (web-mode-attribute-beginning-position pos)
            attr-end (web-mode-attribute-end-position pos))
      ;;      (message "%S %S - %S %S" attr-beg attr-end next-beg next-end)
      (transpose-regions attr-beg (1+ attr-end) next-beg (1+ next-end))
      )))

(defun web-mode-attribute-select (&optional pos)
  "Select the current html attribute."
  (interactive)
  (unless pos (setq pos (point)))
  (if (null (get-text-property pos 'tag-attr))
      nil
    (goto-char pos)
    (web-mode-attribute-beginning)
    (set-mark (point))
    (web-mode-attribute-end)
    (point)
    ))

(defun web-mode-attribute-kill (&optional arg)
  "Kill the current html attribute."
  (interactive "p")
  (unless arg (setq arg 1))
  (while (>= arg 1)
    (setq arg (1- arg))
    (web-mode-attribute-select)
    (when mark-active
      (let ((beg (region-beginning)) (end (region-end)))
        (save-excursion
          (goto-char end)
          (when (looking-at "[ \n\t]*")
            (setq end (+ end (length (match-string-no-properties 0)))))
          ) ;save-excursion
        (kill-region beg end)
        ) ;let
      ) ;when
    ) ;while
  )

(defun web-mode-block-close (&optional pos)
  "Close the first unclosed control block."
  (interactive)
  (unless pos (setq pos (point)))
  (let ((continue t)
        (h (make-hash-table :test 'equal)) ctx ctrl n closing-block)
    (save-excursion
      (while (and continue (web-mode-block-previous))
        (when (setq ctx (web-mode-block-is-control (point)))
          (setq ctrl (car ctx))
          (setq n (gethash ctrl h 0))
          (if (cdr ctx)
              (puthash ctrl (1+ n) h)
            (puthash ctrl (1- n) h))
          (when (> (gethash ctrl h) 0)
            (setq continue nil))
          )
        ) ;while
      ) ;save-excursion
    (when (and (null continue)
               (setq closing-block (web-mode-closing-block ctrl)))
      (insert closing-block)
      (indent-according-to-mode)
      ;;      (indent-for-tab-command)
      )
    ))

(defun web-mode-closing-block (type)
  (cond
   ((string= web-mode-engine "php")       (concat "<?php end" type "; ?>"))
   ((string= web-mode-engine "django")    (concat "{% end" type " %}"))
   ((string= web-mode-engine "ctemplate") (concat "{{/" type "}}"))
   ((string= web-mode-engine "blade")
    (if (string= type "section") (concat "@show") (concat "@end" type)))
   ((string= web-mode-engine "dust")      (concat "{/" type "}"))
   ((string= web-mode-engine "mako")      (concat "% end" type))
   ((string= web-mode-engine "closure")   (concat "{/" type "}"))
   ((string= web-mode-engine "smarty")    (concat "{/" type "}"))
   ((string= web-mode-engine "underscore")        "<% } %>")
   ((string= web-mode-engine "lsp")               "<% ) %>")
   ((string= web-mode-engine "erb")               "<% } %>")
   ((string= web-mode-engine "erb")               "<% end %>")
   ((string= web-mode-engine "go")                "{{end}}")
   ((string= web-mode-engine "velocity")          "#end")
   ((string= web-mode-engine "velocity")          "#{end}")
   ((string= web-mode-engine "template-toolkit")  "[% end %]")
   ((member web-mode-engine '("asp" "jsp"))
    (if (string-match-p "[:.]" type) (concat "</" type ">") "<% } %>"))
   (t nil)
   ) ;cond
  )

;;---- POSITION ----------------------------------------------------------------

(defun web-mode-comment-beginning-position (&optional pos)
  (unless pos (setq pos (point)))
  (car (web-mode-comment-boundaries pos)))

(defun web-mode-comment-end-position (&optional pos)
  (unless pos (setq pos (point)))
  (cdr (web-mode-comment-boundaries pos)))

(defun web-mode-part-opening-paren-position (pos &optional limit)
  (save-restriction
    (unless limit (setq limit nil))
    (goto-char pos)
    (let* ((n -1)
           (paren (char-after))
           (pairs '((?\) . "[)(]")
                    (?\] . "[\]\[]")
                    (?\} . "[}{]")
                    (?\> . "[><]")))
           (regexp (cdr (assoc paren pairs)))
           (continue (not (null regexp)))
           (counter 0))
      (while (and continue (re-search-backward regexp limit t))
        (cond
         ((> (setq counter (1+ counter)) 500)
          (message "part-opening-paren-position ** warning **")
          (setq continue nil))
         ((or (web-mode-is-comment-or-string)
              (get-text-property (point) 'block-side))
          )
         ((eq (char-after) paren)
          (setq n (1- n)))
         (t
          (setq n (1+ n))
          (setq continue (not (= n 0))))
         )
        ) ;while
      (if (= n 0) (point) nil)
      )))

(defun web-mode-closing-paren-position (&optional pos limit)
  (save-excursion
    (unless pos (setq pos (point)))
    (unless limit (setq limit nil))
    (goto-char pos)
    (let* ((n 0)
           (block-side (and (get-text-property pos 'block-side)
                            (not (string= web-mode-engine "razor"))))
           (paren (char-after))
           (pairs '((?\( . "[)(]")
                    (?\[ . "[\]\[]")
                    (?\{ . "[}{]")
                    (?\< . "[><]")))
           (regexp (cdr (assoc paren pairs)))
           (continue (not (null regexp))))
      (while (and continue (re-search-forward regexp limit t))
        (cond
         ((or (web-mode-is-comment-or-string (1- (point)))
              (and block-side (not (get-text-property (point) 'block-side))))
          ;;(message "pt=%S" (point))
          )
         ((eq (char-before) paren)
          (setq n (1+ n)))
         (t
          (setq n (1- n))
          (setq continue (not (= n 0)))
          )
         ) ;cond
        ) ;while
      (if (= n 0) (1- (point)) nil)
      )))

(defun web-mode-closing-delimiter-position (delimiter &optional pos limit)
  (unless pos (setq pos (point)))
  (unless limit (setq limit nil))
  (save-excursion
    (goto-char pos)
    (setq pos nil)
    (let ((continue t))
      (while (and continue (re-search-forward delimiter limit t))
        (setq continue nil
              pos (1- (point)))
        ) ;while
      pos)))

(defun web-mode-tag-match-position (&optional pos)
  (unless pos (setq pos (point)))
  (save-excursion
    (web-mode-tag-match pos)
    (if (= pos (point)) nil (point))))

(defun web-mode-tag-beginning-position (&optional pos)
  (unless pos (setq pos (point)))
  (let (beg end depth)
    (setq depth (get-text-property pos 'jsx-depth))
    (when (and depth (get-text-property pos 'tag-attr-beg))
       (setq depth (get-text-property (1- pos) 'jsx-depth)))
    (cond
     ((null pos)
      (setq end nil))
     ((get-text-property pos 'tag-beg)
      (setq beg pos))
     ((and (> pos 1) (get-text-property (1- pos) 'tag-beg))
      (setq beg (1- pos)))
     ((get-text-property pos 'tag-type)
      (setq beg (previous-single-property-change pos 'tag-beg))
      (when beg (setq beg (1- beg)))
      (cond
       ((not (get-text-property beg 'tag-beg))
        (setq beg nil))
       ((and depth (not (eq depth (get-text-property beg 'jsx-depth))))
        (let ((continue (> beg (point-min))))
          (while continue
            (setq beg (previous-single-property-change beg 'tag-beg))
            (when beg (setq beg (1- beg)))
            (cond
             ((null beg)
              (setq continue nil))
             ((not (get-text-property beg 'tag-beg))
              (setq continue nil
                    beg nil))
             ((eq depth (get-text-property beg 'jsx-depth))
              (setq continue nil))
             ) ;cond
            ) ;while
          ) ;let
        )
       ) ;cond
      )
     (t
      (setq beg nil))
     ) ;cond
    beg))

(defun web-mode-tag-end-position (&optional pos)
  (unless pos (setq pos (point)))
  (let (end depth)
    (setq depth (get-text-property pos 'jsx-depth))
    (when (and depth (get-text-property pos 'tag-attr-beg))
      (setq depth (get-text-property (1- pos) 'jsx-depth)))
    (cond
     ((null pos)
      (setq end nil))
     ((get-text-property pos 'tag-end)
      (setq end pos))
     ((get-text-property pos 'tag-type)
      (setq end (next-single-property-change pos 'tag-end))
      (cond
       ((not (get-text-property end 'tag-end))
        (setq end nil))
       ((and depth (not (eq depth (get-text-property end 'jsx-depth))))
        (let ((continue (< end (point-max))))
          (while continue
            (setq end (1+ end))
            (setq end (next-single-property-change end 'tag-end))
            (cond
             ((null end)
              (setq continue nil))
             ((not (get-text-property end 'tag-end))
              (setq continue nil
                    end nil))
             ((eq depth (get-text-property end 'jsx-depth))
              (setq continue nil))
             ) ;cond
            ) ;while
          ) ;let
        )
       ) ;cond
      )
     (t
      (setq end nil))
     ) ;cond
    end))

;; TODO: prendre en compte jsx-depth
(defun web-mode-tag-next-position (&optional pos limit)
  (unless pos (setq pos (point)))
  (unless limit (setq limit (point-max)))
  (cond
   ((or (>= pos (point-max)) (>= pos limit)) nil)
   (t
    (when (get-text-property pos 'tag-beg) (setq pos (1+ pos)))
    (setq pos (next-single-property-change pos 'tag-beg))
    (if (and pos (<= pos limit)) pos nil))
   ))

;; TODO: prendre en compte jsx-depth
(defun web-mode-tag-previous-position (&optional pos limit)
  (unless pos (setq pos (point)))
  (unless limit (setq limit (point-min)))
  (cond
   ((or (<= pos (point-min)) (<= pos limit)) nil)
   (t
    (when (get-text-property pos 'tag-beg) (setq pos (1- pos)))
    (web-mode-go (previous-single-property-change pos 'tag-beg) -1))
   ))

;; TODO: prendre en compte jsx-depth
(defun web-mode-attribute-beginning-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((null (get-text-property pos 'tag-attr))
    nil)
   ((get-text-property pos 'tag-attr-beg)
    pos)
   (t
    (setq pos (previous-single-property-change pos 'tag-attr-beg))
    (setq pos (1- pos)))
   ))

;; TODO: retoucher en incluant un param limit et en s'inspirant de
;;       web-mode-attribute-next-position
(defun web-mode-attribute-end-position (&optional pos)
  (unless pos (setq pos (point)))
  (let (end depth)
    (setq depth (get-text-property pos 'jsx-depth))
    (cond
     ((null pos)
      (setq end nil))
     ((get-text-property pos 'tag-attr-end)
      (setq end pos))
     ((get-text-property pos 'tag-attr)
      (setq end (next-single-property-change pos 'tag-attr-end))
      (cond
       ((not (get-text-property end 'tag-attr-end))
        (setq end nil))
       ((and depth
             (eq depth (get-text-property end 'jsx-depth))
             (not (eq depth (get-text-property end 'jsx-end))))
        )
       ((and depth (eq (1+ depth) (get-text-property end 'jsx-depth)))
        )
       ((and depth (not (eq (1+ depth) (get-text-property end 'jsx-depth))))
        (let ((continue (< end (point-max))))
          (while continue
            (setq end (1+ end))
            (setq end (next-single-property-change end 'tag-attr-end))
            (cond
             ((null end)
              (setq continue nil))
             ((not (get-text-property end 'tag-attr-end))
              (setq continue nil
                    end nil))
             ((eq (1+ depth) (get-text-property end 'jsx-depth))
              (setq continue nil))
             ) ;cond
            ) ;while
          ) ;let
        )
       ) ;cond
      )
     (t
      (setq end nil))
     ) ;cond
    end))

(defun web-mode-attribute-next-position (&optional pos limit)
  (unless pos (setq pos (point)))
  (unless limit (setq limit (point-max)))
  (let (continue depth)
    (when (get-text-property pos 'tag-attr-beg)
      (setq pos (1+ pos)))
    (if (< pos limit)
        (setq continue t
              depth (get-text-property pos 'jsx-depth))
      (setq continue nil
            pos nil))
    (while continue
      (setq pos (next-single-property-change pos 'tag-attr-beg))
      (cond
       ((null pos)
        (setq continue nil))
       ((>= pos limit)
        (setq continue nil
              pos nil))
       ((null depth)
        (setq continue nil))
       ((eq depth (get-text-property pos 'jsx-depth))
        (setq continue nil))
       (t
        (setq pos (1+ pos)
              continue (< pos limit)))
       )
      ) ;while
    pos))

(defun web-mode-attribute-previous-position (&optional pos limit)
  (unless pos (setq pos (point)))
  (unless limit (setq limit (point-min)))
  (let (continue depth)
    (when (get-text-property pos 'tag-attr-beg)
      (setq pos (1- pos)))
    (if (> pos limit)
        (setq continue t
              depth (get-text-property pos 'jsx-depth))
      (setq continue nil
            pos nil))
    (while continue
      (setq pos (previous-single-property-change pos 'tag-attr-beg))
      (cond
       ((null pos)
        (setq continue nil))
       ((< pos limit)
        (setq continue nil
              pos nil))
       ((null depth)
        (setq continue nil))
       ((eq depth (get-text-property pos 'jsx-depth))
        (setq continue nil))
       (t
        (setq pos (1- pos)
              continue (> pos limit)))
       ) ;cond
      ) ;while
    pos))

;; TODO: prendre en compte jsx-depth
(defun web-mode-element-beginning-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((null (get-text-property pos 'tag-type))
    (setq pos (web-mode-element-parent-position)))
   ((eq (get-text-property pos 'tag-type) 'end)
    (setq pos (web-mode-tag-match-position pos))
    (setq pos (if (get-text-property pos 'tag-beg) pos nil)))
   ((member (get-text-property pos 'tag-type) '(start void))
    (setq pos (web-mode-tag-beginning-position pos)))
   (t
    (setq pos nil))
   ) ;cond
  pos)

;; TODO: prendre en compte jsx-depth
(defun web-mode-element-end-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((null (get-text-property pos 'tag-type))
    (setq pos (web-mode-element-parent-position pos))
    (when pos
      (setq pos (web-mode-tag-match-position pos))
      (when pos (setq pos (web-mode-tag-end-position pos)))
      )
    )
   ((member (get-text-property pos 'tag-type) '(end void))
    (setq pos (web-mode-tag-end-position pos))
    )
   ((member (get-text-property pos 'tag-type) '(start))
    (setq pos (web-mode-tag-match-position pos))
    (when pos (setq pos (web-mode-tag-end-position pos))))
   (t
    (setq pos nil))
   ) ;cond
  pos)

(defun web-mode-element-child-position (&optional pos)
  (save-excursion
    (let (child close)
      (unless pos (setq pos (point)))
      (goto-char pos)
      (cond
       ((eq (get-text-property pos 'tag-type) 'start)
        (web-mode-tag-match)
        (setq close (point))
        (goto-char pos)
        )
       ((eq (get-text-property pos 'tag-type) 'void)
        )
       ((eq (get-text-property pos 'tag-type) 'end)
        (web-mode-tag-beginning)
        (setq close (point))
        (web-mode-tag-match)
        )
       ((web-mode-element-parent-position pos)
        (setq pos (point))
        (web-mode-tag-match)
        (setq close (point))
        (goto-char pos)
        )
       ) ;cond
      (when (and close
                 (web-mode-element-next)
                 (< (point) close))
        (setq child (point))
        )
      child)))

(defun web-mode-element-parent-position (&optional pos)
  (let (n tag-type tag-name (continue t) (tags (make-hash-table :test 'equal)))
    (save-excursion
      (if pos (goto-char pos))
      (while (and continue (web-mode-tag-previous))
        (setq pos (point)
              tag-type (get-text-property pos 'tag-type)
              tag-name (get-text-property pos 'tag-name)
              n (gethash tag-name tags 0))
        (when (member tag-type '(end start))
          (if (eq tag-type 'end)
              (puthash tag-name (1- n) tags)
            (puthash tag-name (1+ n) tags)
            (when (= n 0) (setq continue nil))
            ) ;if
          ) ;when
        ) ;while
      ) ;save-excursion
    (if (null continue) pos nil)))

(defun web-mode-element-previous-position (&optional pos limit)
  (unless pos (setq pos (point)))
  (unless limit (setq limit (point-min)))
  (save-excursion
    (goto-char pos)
    (let ((continue (not (bobp)))
          (props '(start void comment)))
      (while continue
        (setq pos (web-mode-tag-previous))
        (cond
         ((or (null pos) (< (point) limit))
          (setq continue nil
                pos nil))
         ((member (get-text-property (point) 'tag-type) props)
          (setq continue nil))
         )
        ) ;while
      pos)))

(defun web-mode-element-next-position (&optional pos limit)
  (unless pos (setq pos (point)))
  (unless limit (setq limit (point-max)))
  (save-excursion
    (goto-char pos)
    (let ((continue (not (eobp)))
          (props '(start void comment)))
      (while continue
        (setq pos (web-mode-tag-next))
        (cond
         ((or (null pos) (> (point) limit))
          (setq continue nil
                pos nil))
         ((member (get-text-property (point) 'tag-type) props)
          (setq continue nil))
         )
        ) ;while
;;      (message "pos=%S" pos)
      pos)))

(defun web-mode-part-end-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((member web-mode-content-type web-mode-part-content-types)
    (setq pos (point-max)))
   ((not (get-text-property pos 'part-side))
    (setq pos nil))
   ((= pos (point-max))
    (setq pos nil))
   ((not (get-text-property (1+ pos) 'part-side))
    pos)
   (t
    (setq pos (next-single-property-change pos 'part-side)))
   ) ;cond
  pos)

(defun web-mode-part-beginning-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((member web-mode-content-type web-mode-part-content-types)
    (setq pos (point-min)))
   ((not (get-text-property pos 'part-side))
    (setq pos nil))
   ((= pos (point-min))
    (setq pos nil))
   ((not (get-text-property (1- pos) 'part-side))
    pos)
   (t
    (setq pos (previous-single-property-change pos 'part-side)))
   ) ;cond
  pos)

(defun web-mode-part-next-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((and (= pos (point-min)) (get-text-property pos 'part-side))
    )
   ((not (get-text-property pos 'part-side))
    (setq pos (next-single-property-change pos 'part-side)))
   ((and (setq pos (web-mode-part-end-position pos)) (>= pos (point-max)))
    (setq pos nil))
   ((and (setq pos (1+ pos)) (not (get-text-property pos 'part-side)))
    (setq pos (next-single-property-change pos 'part-side)))
   ) ;cond
  pos)

(defun web-mode-block-match-position (&optional pos)
  (unless pos (setq pos (point)))
  (save-excursion
    (web-mode-block-match pos)
    (if (= pos (point)) nil (point))))

(defun web-mode-block-control-previous-position (type &optional pos)
  (unless pos (setq pos (point)))
  (let ((continue t) controls)
    (while continue
      (setq pos (web-mode-block-previous-position pos))
      (cond
       ((null pos)
        (setq continue nil
              pos nil))
       ((and (setq controls (web-mode-block-controls-get pos))
             (eq (car (car controls)) type))
        (setq continue nil))
       ) ;cond
      ) ;while
    pos))

(defun web-mode-block-opening-paren-position (pos limit)
  (save-excursion
    (when (> limit pos)
      (message "block-opening-paren-position: limit(%S) > pos(%S)" limit pos))
    (goto-char pos)
    (let (c
          n
          pt
          (continue (> pos limit))
          (pairs '((?\) . ?\()
                   (?\] . ?\[)
                   (?\} . ?\{)))
          (h (make-hash-table :test 'equal))
          (regexp "[\]\[)(}{]"))
      (while (and continue (re-search-backward regexp limit t))
        (cond
         ((web-mode-is-comment-or-string)
          )
         (t
          (setq c (char-after))
          (cond
           ((member c '(?\( ?\{ ?\[))
            (setq n (gethash c h 0))
            (if (= n 0)
                (setq continue nil
                      pt (point))
              (puthash c (1+ n) h)
              ))
           (t
            (setq c (cdr (assoc c pairs)))
            (setq n (gethash c h 0))
            (puthash c (1- n) h))
           ) ;cond
          ) ;t
         ) ;cond
        ) ;while
      pt)))

(defun web-mode-block-code-beginning-position (&optional pos)
  (unless pos (setq pos (point)))
  (when (and (setq pos (web-mode-block-beginning-position pos))
             (eq (get-text-property pos 'block-token) 'delimiter-beg))
    (setq pos (next-single-property-change pos 'block-token)))
  pos)

(defun web-mode-block-beginning-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((or (and (get-text-property pos 'block-side) (= pos (point-min)))
        (get-text-property pos 'block-beg))
    )
   ((and (> pos (point-min)) (get-text-property (1- pos) 'block-beg))
    (setq pos (1- pos)))
   ((get-text-property pos 'block-side)
    (setq pos (previous-single-property-change pos 'block-beg))
    (setq pos (if (and pos (> pos (point-min))) (1- pos) (point-min))))
   (t
    (setq pos nil))
   ) ;cond
  pos)

(defun web-mode-block-string-beginning-position (pos &optional block-beg)
  (unless pos (setq pos (point)))
  (unless block-beg (setq block-beg (web-mode-block-beginning-position pos)))
  (let (char (ori pos) (continue (not (null pos))))
    (while continue
      (setq char (char-after pos))
      (cond
       ((< pos block-beg)
        (setq continue nil
              pos block-beg))
       ((and (member (get-text-property pos 'block-token) '(string comment))
             (eq (get-text-property pos 'block-token) (get-text-property (1- pos) 'block-token)))
        (setq pos (web-mode-block-token-beginning-position pos))
        )
       ((member char '(?\) ?\]))
        (setq pos (web-mode-block-opening-paren-position pos block-beg))
        (setq pos (1- pos))
        )
       ((and (> ori pos) (member char '(?\( ?\= ?\[ ?\? ?\: ?\; ?\, ?\`)))
        (setq continue nil)
        (web-mode-looking-at ".[ \t\n]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0))))
        )
       ((web-mode-looking-back "\\_<\\(return\\|echo\\|include\\|print\\)[ \n\t]*" pos)
        (setq continue nil))
       (t
        (setq pos (1- pos)))
       ) ;cond
      ) ;while
    ;;(message "pos=%S" pos)
    pos))

(defun web-mode-block-statement-beginning-position (pos &optional block-beg)
  (unless pos (setq pos (point)))
  (setq pos (1- pos))
  (unless block-beg (setq block-beg (web-mode-block-beginning-position pos)))
  (let (char (continue (not (null pos))))
    (while continue
      (setq char (char-after pos))
      (cond
       ((< pos block-beg)
        (setq continue nil
              pos block-beg))
       ((and (member (get-text-property pos 'block-token) '(string comment))
             (eq (get-text-property pos 'block-token) (get-text-property (1- pos) 'block-token)))
        (setq pos (web-mode-block-token-beginning-position pos)))
       ((member char '(?\) ?\] ?\}))
        (setq pos (web-mode-block-opening-paren-position pos block-beg))
        (setq pos (1- pos)))
       ((member char '(?\( ?\[ ?\{ ?\=))
        (setq continue nil)
        (web-mode-looking-at ".[ \t\n]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0)))))
       ((web-mode-looking-back "\\_<\\(return\\|echo\\|include\\|print\\)[ \n\t]*" pos)
        (setq continue nil))
       (t
        (setq pos (1- pos)))
       ) ;cond
      ) ;while
    pos))

(defun web-mode-block-args-beginning-position (pos &optional block-beg)
  (unless pos (setq pos (point)))
  (setq pos (1- pos)) ;#512
  (unless block-beg (setq block-beg (web-mode-block-beginning-position pos)))
  (let (char (continue (not (null pos))))
    (while continue
      (setq char (char-after pos))
      (cond
       ((< pos block-beg)
        (message "block-args-beginning-position ** failure **")
        (setq continue nil
              pos block-beg))
       ((and (member (get-text-property pos 'block-token) '(string comment))
             (eq (get-text-property pos 'block-token) (get-text-property (1- pos) 'block-token)))
        (setq pos (web-mode-block-token-beginning-position pos)))
       ((member char '(?\) ?\] ?\}))
        (setq pos (web-mode-block-opening-paren-position pos block-beg))
        (setq pos (1- pos)))
       ((member char '(?\( ?\[ ?\{))
        (setq continue nil)
        (web-mode-looking-at ".[ \t\n]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0)))))
       ((and (string= web-mode-engine "php")
             (web-mode-looking-back "\\_<\\(extends\\|implements\\)[ \n\t]*" pos))
        (setq continue nil))
       (t
        (setq pos (1- pos)))
       ) ;cond
      ) ;while
    pos))

(defun web-mode-block-calls-beginning-position (pos &optional block-beg)
  (unless pos (setq pos (point)))
  (unless block-beg (setq block-beg (web-mode-block-beginning-position pos)))
  (let (char (continue (not (null pos))))
    (while continue
      (setq char (char-after pos))
      (cond
       ((< pos block-beg)
        (message "block-calls-beginning-position ** failure **")
        (setq continue nil
              pos block-beg))
       ((and (member (get-text-property pos 'block-token) '(string comment))
             (eq (get-text-property pos 'block-token) (get-text-property (1- pos) 'block-token)))
        (setq pos (web-mode-block-token-beginning-position pos)))
       ((member char '(?\) ?\]))
        (setq pos (web-mode-block-opening-paren-position pos block-beg))
        (setq pos (1- pos)))
       ((member char '(?\( ?\[ ?\{ ?\} ?\= ?\? ?\: ?\; ?\,))
        (setq continue nil)
        (web-mode-looking-at ".[ \t\n]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0)))))
       ((web-mode-looking-back "\\(return\\|else\\)[ \n\t]*" pos)
        (setq ;;pos (point)
              continue nil))
       (t
        (setq pos (1- pos)))
       ) ;cond
      ) ;while
    pos))

(defun web-mode-javascript-string-beginning-position (pos &optional reg-beg)
  (unless pos (setq pos (point)))
  (let ((char nil)
        (blockside (get-text-property pos 'block-side))
        (i 0)
        (continue (not (null pos))))
    (unless reg-beg
      (if blockside
          (setq reg-beg (web-mode-block-beginning-position pos))
        (setq reg-beg (web-mode-part-beginning-position pos)))
      )
    (while continue
      (setq char (char-after pos))
      (cond
       ((> (setq i (1+ i)) 20000)
        (message "javascript-string-beginning-position ** warning (%S) **" pos)
        (setq continue nil
              pos nil))
       ((null pos)
        (message "javascript-string-beginning-position ** invalid pos **")
        (setq continue nil))
       ((< pos reg-beg)
        (message "javascript-string-beginning-position ** failure **")
        (setq continue nil
              pos reg-beg))
       ((and blockside
             (member (get-text-property pos 'block-token) '(string comment))
             (eq (get-text-property pos 'block-token) (get-text-property (1- pos) 'block-token)))
        (setq pos (web-mode-block-token-beginning-position pos)))
       ((and (not blockside)
             (member (get-text-property pos 'part-token) '(string comment))
             (eq (get-text-property pos 'part-token) (get-text-property (1- pos) 'part-token)))
        (setq pos (web-mode-part-token-beginning-position pos)))
       ((and (not blockside)
             (get-text-property pos 'block-side))
        (when (setq pos (web-mode-block-beginning-position pos))
          (setq pos (1- pos))))
       ((member char '(?\) ?\] ?\}))
        (setq pos (web-mode-part-opening-paren-position pos reg-beg))
        (setq pos (1- pos)))
       ((member char '(?\( ?\{ ?\[ ?\= ?\? ?\: ?\; ?\, ?\& ?\|))
        (setq continue nil)
        (web-mode-looking-at ".[ \t\n]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0)))))
       ((web-mode-looking-back "\\(return\\)[ \n\t]*" pos)
        (setq continue nil))
       (t
        (setq pos (1- pos)))
       ) ;cond
      ) ;while
    ;;(message "js-statement-beg:%S" pos)
    pos))

;; TODO: reg-beg : jsx-beg
;; TODO: skipper les expr dont la depth est superieure

;; NOTE: blockside is useful for ejs
(defun web-mode-javascript-statement-beginning-position (pos &optional reg-beg)
  (unless pos (setq pos (point)))
  (setq pos (1- pos))
  (let ((char nil)
        (blockside (get-text-property pos 'block-side))
        (i 0)
        (is-jsx (string= web-mode-content-type "jsx"))
        (depth-o nil) (depth-l nil)
        (continue (not (null pos))))
    (setq depth-o (get-text-property pos 'jsx-depth))
    (unless reg-beg
      (cond
       (blockside
        (setq reg-beg (web-mode-block-beginning-position pos)))
       (is-jsx
        (setq reg-beg (web-mode-jsx-depth-beginning-position pos)))
       (t
        (setq reg-beg (web-mode-part-beginning-position pos)))
       ) ;cond
      ) ;unless
    (while continue
      (setq char (char-after pos))
      (cond
       ((> (setq i (1+ i)) 20000)
        (message "javascript-statement-beginning-position ** warning (%S) **" pos)
        (setq continue nil
              pos nil))
       ((null pos)
        (message "javascript-statement-beginning-position ** invalid pos **")
        (setq continue nil))
       ((< pos reg-beg)
        (when (not is-jsx)
          (message "javascript-statement-beginning-position ** failure **"))
        (setq continue nil
              pos reg-beg))
       ((and is-jsx
             (progn (setq depth-l (get-text-property pos 'jsx-depth)))
             (not (eq depth-l depth-o)))
        ;;(message "%S > depth-o(%S) depth-l(%S)" pos depth-o depth-l)
        (setq pos (previous-single-property-change pos 'jsx-depth))
        (setq pos (1- pos))
        ;;(message "--> %S %S" pos (get-text-property pos 'jsx-depth))
        )
       ((and blockside
             (member (get-text-property pos 'block-token) '(string comment))
             (eq (get-text-property pos 'block-token) (get-text-property (1- pos) 'block-token)))
        (setq pos (web-mode-block-token-beginning-position pos)))
       ((and (not blockside)
             (member (get-text-property pos 'part-token) '(string comment))
             (eq (get-text-property pos 'part-token) (get-text-property (1- pos) 'part-token)))
        (setq pos (web-mode-part-token-beginning-position pos)))
       ((and (not blockside)
             (get-text-property pos 'block-side))
        (when (setq pos (web-mode-block-beginning-position pos))
          (setq pos (1- pos))))
       ((member char '(?\) ?\] ?\}))
        (setq pos (web-mode-part-opening-paren-position pos reg-beg))
        (setq pos (1- pos)))
       ((and (eq char ?\=)
             (web-mode-looking-back "[<>!=]+" pos reg-beg t))
        (setq pos (- pos 1 (length (match-string-no-properties 0))))
        ;;(setq pos (1- pos))
        ;;(message "%S pos=%S" (match-string-no-properties 0) pos)
        )
       ((member char '(?\( ?\{ ?\[ ?\=))
        (setq continue nil)
        (web-mode-looking-at ".[ \t\n]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0)))))
       ((web-mode-looking-back "\\_<\\(return\\)[ \n\t]*" pos)
        (setq continue nil)
        (web-mode-looking-at "[ \t\n]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0)))))
       (t
        (setq pos (1- pos)))
       ) ;cond
      ) ;while
    ;;(message "%S -------" pos)
    pos))

(defun web-mode-javascript-args-beginning-position (pos &optional reg-beg)
  (unless pos (setq pos (point)))
  (setq pos (1- pos))
  (let ((char nil)
        (blockside (get-text-property pos 'block-side))
        (i 0)
        (continue (not (null pos))))
    (unless reg-beg
      (if blockside
          (setq reg-beg (web-mode-block-beginning-position pos))
        (setq reg-beg (web-mode-part-beginning-position pos)))
      )
    (while continue
      (setq char (char-after pos))
      (cond
       ((> (setq i (1+ i)) 20000)
        (message "javascript-args-beginning-position ** warning (%S) **" pos)
        (setq continue nil
              pos nil))
       ((null pos)
        (message "javascript-args-beginning-position ** invalid pos **")
        (setq continue nil))
       ((< pos reg-beg)
        (message "javascript-args-beginning-position ** failure **")
        (setq continue nil
              pos reg-beg))
       ((and blockside
             (member (get-text-property pos 'block-token) '(string comment))
             (eq (get-text-property pos 'block-token) (get-text-property (1- pos) 'block-token)))
        (setq pos (web-mode-block-token-beginning-position pos)))
       ((and (not blockside)
             (member (get-text-property pos 'part-token) '(string comment))
             (eq (get-text-property pos 'part-token) (get-text-property (1- pos) 'part-token)))
        (setq pos (web-mode-part-token-beginning-position pos)))
       ((and (not blockside)
             (get-text-property pos 'block-side))
        (when (setq pos (web-mode-block-beginning-position pos))
          (setq pos (1- pos)))
        )
       ((member char '(?\) ?\] ?\}))
        (when (setq pos (web-mode-part-opening-paren-position pos reg-beg))
          (setq pos (1- pos))))
       ((member char '(?\( ?\[ ?\{))
;;        (web-mode-looking-at ".[ \t\n]*" pos)
        (web-mode-looking-at ".[ ]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0)))
              continue nil)
;;        (message "=>%S" pos)
        )
       ((web-mode-looking-back "\\_<\\(var\\|let\\|return\\|const\\)[ \n\t]+" pos)
;;        (web-mode-looking-at "[ \t\n]*" pos)
        (web-mode-looking-at "[ \t]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0)))
              continue nil))
       (t
        (setq pos (1- pos)))
       ) ;cond
      ) ;while
    ;;(message "=%S" pos)
    pos))

(defun web-mode-javascript-calls-beginning-position (pos &optional reg-beg)
  (unless pos (setq pos (point)))
  ;;(message "pos=%S" pos)
  (let ((char nil)
        (dot-pos nil)
        (blockside (get-text-property pos 'block-side))
        (i 0)
        (continue (not (null pos))))
    (unless reg-beg
      (if blockside
          (setq reg-beg (web-mode-block-beginning-position pos))
        (setq reg-beg (web-mode-part-beginning-position pos)))
      )
    (while continue
      (setq char (char-after pos))
      ;;(message "%S| %S=%c" reg-beg pos char)
      (cond
       ((> (setq i (1+ i)) 20000)
        (message "javascript-calls-beginning-position ** warning (%S) **" pos)
        (setq continue nil
              pos nil))
       ((null pos)
        (message "javascript-calls-beginning-position ** invalid pos **")
        (setq continue nil))
       ((< pos reg-beg)
        ;;(forward-char)
        ;;(skip-chars-forward " \t")
        ;;(message "pos(%S) reg-beg(%S)" pos reg-beg)
        ;;(message "javascript-calls-beginning-position ** failure **")
        (setq continue nil
              pos reg-beg))
       ((and blockside
             (member (get-text-property pos 'block-token) '(string comment))
             (eq (get-text-property pos 'block-token) (get-text-property (1- pos) 'block-token)))
        (setq pos (web-mode-block-token-beginning-position pos)))
       ((and (not blockside)
             (member (get-text-property pos 'part-token) '(string comment))
             (eq (get-text-property pos 'part-token) (get-text-property (1- pos) 'part-token)))
        (setq pos (web-mode-part-token-beginning-position pos)))
       ((and (not blockside)
             (get-text-property pos 'block-side))
        (when (setq pos (web-mode-block-beginning-position pos))
          (setq pos (1- pos))))
       ;;((member char '(?\) ?\] ?\}))
       ;;((member char '(?\s ?\t))
       ;; (skip-chars-backward " \t" reg-beg))
       ((and (member char '(?\.)) (> i 1))
        (setq dot-pos pos
              pos (1- pos)))
       ((member char '(?\) ?\]))
        (when (setq pos (web-mode-part-opening-paren-position pos reg-beg))
          (setq pos (1- pos)))
        ;;(message "pos=%S" pos)
        )
       ((member char '(?\( ?\{ ?\} ?\[ ?\= ?\? ?\: ?\; ?\, ?\& ?\|))
        (setq continue nil)
        (web-mode-looking-at ".[ \t\n]*" pos)
        (setq pos (+ pos (length (match-string-no-properties 0)))))
       ((web-mode-looking-back "\\_<\\(return\\|else\\)[ \n\t]*" pos)
        (setq continue nil))
       (t
        (setq pos (1- pos)))
       ) ;cond
      ) ;while
    ;;(message "pos=%S dot-pos=%S" pos dot-pos)
    (if (null pos) pos (cons pos dot-pos))
    ))

(defun web-mode-part-token-beginning-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((not (get-text-property pos 'part-token))
    nil)
   ((or (= pos (point-min))
        (and (> pos (point-min))
             (not (get-text-property (1- pos) 'part-token))))
    pos)
   (t
    (setq pos (previous-single-property-change pos 'part-token))
    (if (and pos (> pos (point-min))) pos (point-min)))
   ))

(defun web-mode-part-token-end-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((not (get-text-property pos 'part-token))
    nil)
   ((or (= pos (point-max))
        (not (get-text-property (1+ pos) 'part-token)))
    pos)
   (t
    (1- (next-single-property-change pos 'part-token)))
   ))

(defun web-mode-block-token-beginning-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((not (get-text-property pos 'block-token))
    nil)
   ((or (= pos (point-min))
        (and (> pos (point-min))
             (not (get-text-property (1- pos) 'block-token))))
    pos)
   (t
    (setq pos (previous-single-property-change pos 'block-token))
    (if (and pos (> pos (point-min))) pos (point-min)))
   ))

(defun web-mode-block-token-end-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((not (get-text-property pos 'block-token))
    nil)
   ((or (= pos (point-max))
        (not (get-text-property (1+ pos) 'block-token)))
    pos)
   (t
    (1- (next-single-property-change pos 'block-token)))
   ))

(defun web-mode-block-code-end-position (&optional pos)
  (unless pos (setq pos (point)))
  (setq pos (web-mode-block-end-position pos))
  (cond
   ((not pos)
    nil)
   ((and (eq (get-text-property pos 'block-token) 'delimiter-end)
         (eq (get-text-property (1- pos) 'block-token) 'delimiter-end))
    (previous-single-property-change pos 'block-token))
   ((= pos (1- (point-max))) ;; TODO: comparer plutot avec line-end-position
    (point-max))
   (t
    pos)
   ))

(defun web-mode-block-end-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((get-text-property pos 'block-end)
    pos)
   ((get-text-property pos 'block-side)
    (or (next-single-property-change pos 'block-end)
        (point-max)))
   (t
    nil)
   ))

(defun web-mode-block-previous-position (&optional pos)
  (unless pos (setq pos (point)))
  (cond
   ((= pos (point-min))
    (setq pos nil))
   ((get-text-property pos 'block-side)
    (setq pos (web-mode-block-beginning-position pos))
    (cond
     ((or (null pos) (= pos (point-min)))
      (setq pos nil)
      )
     ((and (setq pos (previous-single-property-change pos 'block-beg))
           (> pos (point-min)))
      (setq pos (1- pos))
      )
     )
    ) ;block-side
   ((get-text-property (1- pos) 'block-side)
    (setq pos (web-mode-block-beginning-position (1- pos)))
    )
   (t
    (setq pos (previous-single-property-change pos 'block-side))
    (cond
     ((and (null pos) (get-text-property (point-min) 'block-beg))
      (setq pos (point-min)))
     ((and pos (> pos (point-min)))
      (setq pos (web-mode-block-beginning-position (1- pos))))
     )
    )
   ) ;conf
  pos)

(defun web-mode-block-next-position (&optional pos limit)
  (unless pos (setq pos (point)))
  (unless limit (setq limit (point-max)))
  (cond
   ((and (get-text-property pos 'block-side)
         (setq pos (web-mode-block-end-position pos))
         (< pos (point-max))
         (setq pos (1+ pos)))
    (unless (get-text-property pos 'block-beg)
      (setq pos (next-single-property-change pos 'block-side)))
    )
   (t
    (setq pos (next-single-property-change pos 'block-side)))
   ) ;cond
  (if (and pos (<= pos limit)) pos nil))

;;---- EXCURSION ---------------------------------------------------------------

(defun web-mode-backward-sexp (n)
  (interactive "p")
  (if (< n 0) (web-mode-forward-sexp (- n))
    (let (pos)
      (dotimes (_ n)
        (skip-chars-backward "[:space:]")
        (setq pos (point))
        (cond
         ((bobp) nil)
         ((get-text-property (1- pos) 'block-end)
          (backward-char 1)
          (web-mode-block-beginning))
         ((get-text-property (1- pos) 'block-token)
          (backward-char 1)
          (web-mode-block-token-beginning))
         ((get-text-property (1- pos) 'part-token)
          (backward-char 1)
          (web-mode-part-token-beginning))
         ((get-text-property (1- pos) 'tag-end)
          (backward-char 1)
          (web-mode-element-beginning))
         ((get-text-property (1- pos) 'tag-attr)
          (backward-char 1)
          (web-mode-attribute-beginning))
         ((get-text-property (1- pos) 'tag-type)
          (backward-char 1)
          (web-mode-tag-beginning))
         ((get-text-property (1- pos) 'jsx-end)
          (backward-char 1)
          (web-mode-jsx-beginning))
         (t
          (let ((forward-sexp-function nil))
            (backward-sexp))
          ) ;case t
         ) ;cond
        ) ;dotimes
      ))) ;let if defun

(defun web-mode-forward-sexp (n)
  (interactive "p")
  (if (< n 0) (web-mode-backward-sexp (- n))
    (let (pos)
      (dotimes (_ n)
        (skip-chars-forward "[:space:]")
        (setq pos (point))
        (cond
         ((eobp) nil)
         ((get-text-property pos 'block-beg)
          (web-mode-block-end))
         ((get-text-property pos 'block-token)
          (web-mode-block-token-end))
         ((get-text-property pos 'part-token)
          (web-mode-part-token-end))
         ((get-text-property pos 'tag-beg)
          (web-mode-element-end))
         ((get-text-property pos 'tag-attr)
          (web-mode-attribute-end))
         ((get-text-property pos 'tag-type)
          (web-mode-tag-end))
         ((get-text-property pos 'jsx-beg)
          (web-mode-jsx-end))
         (t
          (let ((forward-sexp-function nil))
            (forward-sexp))
          ) ;case t
         ) ;cond
        ) ;dotimes
      ))) ;let if defun

(defun web-mode-comment-beginning ()
  "Fetch current comment beg."
  (interactive)
  (web-mode-go (web-mode-comment-beginning-position (point))))

(defun web-mode-comment-end ()
  "Fetch current comment end."
  (interactive)
  (web-mode-go (web-mode-comment-end-position (point)) 1))

(defun web-mode-tag-beginning ()
  "Fetch current html tag beg."
  (interactive)
  (web-mode-go (web-mode-tag-beginning-position (point))))

(defun web-mode-tag-end ()
  "Fetch current html tag end."
  (interactive)
  (web-mode-go (web-mode-tag-end-position (point)) 1))

(defun web-mode-tag-previous ()
  "Fetch previous tag."
  (interactive)
  (web-mode-go (web-mode-tag-previous-position (point))))

(defun web-mode-tag-next ()
  "Fetch next tag. Might be html comment or server tag (e.g. jsp)."
  (interactive)
  (web-mode-go (web-mode-tag-next-position (point))))

(defun web-mode-attribute-beginning ()
  "Fetch html attribute beginning."
  (interactive)
  (web-mode-go (web-mode-attribute-beginning-position (point))))

(defun web-mode-attribute-end ()
  "Fetch html attribute end."
  (interactive)
  (web-mode-go (web-mode-attribute-end-position (point)) 1))

(defun web-mode-attribute-next (&optional arg)
  "Fetch next attribute."
  (interactive "p")
  (unless arg (setq arg 1))
  (cond
   ((= arg 1) (web-mode-go (web-mode-attribute-next-position (point))))
   ((< arg 1) (web-mode-element-previous (* arg -1)))
   (t
    (while (>= arg 1)
      (setq arg (1- arg))
      (web-mode-go (web-mode-attribute-next-position (point)))
      )
    )
   )
  )

(defun web-mode-attribute-previous (&optional arg)
  "Fetch previous attribute."
  (interactive "p")
  (unless arg (setq arg 1))
  (unless arg (setq arg 1))
  (cond
   ((= arg 1) (web-mode-go (web-mode-attribute-previous-position (point))))
   ((< arg 1) (web-mode-element-next (* arg -1)))
   (t
    (while (>= arg 1)
      (setq arg (1- arg))
      (web-mode-go (web-mode-attribute-previous-position (point)))
      )
    )
   )
  )

(defun web-mode-element-previous (&optional arg)
  "Fetch previous element."
  (interactive "p")
  (unless arg (setq arg 1))
  (cond
   ((= arg 1) (web-mode-go (web-mode-element-previous-position (point))))
   ((< arg 1) (web-mode-element-next (* arg -1)))
   (t
    (while (>= arg 1)
      (setq arg (1- arg))
      (web-mode-go (web-mode-element-previous-position (point)))
      ) ;while
    ) ;t
   ) ;cond
  )

(defun web-mode-element-next (&optional arg)
  "Fetch next element."
  (interactive "p")
  (unless arg (setq arg 1))
  (cond
   ((= arg 1) (web-mode-go (web-mode-element-next-position (point))))
   ((< arg 1) (web-mode-element-previous (* arg -1)))
   (t
    (while (>= arg 1)
      (setq arg (1- arg))
      (web-mode-go (web-mode-element-next-position (point)))
      ) ;while
    ) ;t
   ) ;cond
  )

(defun web-mode-element-sibling-next ()
  "Fetch next sibling element."
  (interactive)
  (let ((pos (point)))
    (save-excursion
      (cond
       ((not (get-text-property pos 'tag-type))
        (if (and (web-mode-element-parent)
                 (web-mode-tag-match)
                 (web-mode-element-next))
            (setq pos (point))
          (setq pos nil))
        )
       ((eq (get-text-property pos 'tag-type) 'start)
        (if (and (web-mode-tag-match)
                 (web-mode-element-next))
            (setq pos (point))
          (setq pos nil))
        )
       ((web-mode-element-next)
        (setq pos (point)))
       (t
        (setq pos nil))
       ) ;cond
      ) ;save-excursion
    (web-mode-go pos)))

(defun web-mode-element-sibling-previous ()
  "Fetch previous sibling element."
  (interactive)
  (let ((pos (point)))
    (save-excursion
      (cond
       ((not (get-text-property pos 'tag-type))
        (if (and (web-mode-element-parent)
                 (web-mode-tag-previous)
                 (web-mode-element-beginning))
            (setq pos (point))
          (setq pos nil))
        )
       ((eq (get-text-property pos 'tag-type) 'start)
        (if (and (web-mode-tag-beginning)
                 (web-mode-tag-previous)
                 (web-mode-element-beginning))
            (setq pos (point))
          (setq pos nil))
        )
       ((and (web-mode-element-beginning)
             (web-mode-tag-previous)
             (web-mode-element-beginning))
        (setq pos (point)))
       (t
        (setq pos nil))
       ) ;cond
      ) ;save-excursion
    (web-mode-go pos)))

(defun web-mode-element-beginning ()
  "Move to beginning of element."
  (interactive)
  (web-mode-go (web-mode-element-beginning-position (point))))

(defun web-mode-element-end ()
  "Move to end of element."
  (interactive)
  (web-mode-go (web-mode-element-end-position (point)) 1))

(defun web-mode-element-parent ()
  "Fetch parent element."
  (interactive)
  (web-mode-go (web-mode-element-parent-position (point))))

(defun web-mode-element-child ()
  "Fetch child element."
  (interactive)
  (web-mode-go (web-mode-element-child-position (point))))

(defun web-mode-dom-traverse ()
  "Traverse html dom tree."
  (interactive)
  (cond
   ((web-mode-element-child)
    )
   ((web-mode-element-sibling-next)
    )
   ((and (web-mode-element-parent)
         (not (web-mode-element-sibling-next)))
    (goto-char (point-min)))
   (t
    (goto-char (point-min)))
   ) ;cond
  )

(defun web-mode-closing-paren (limit)
  (let ((pos (web-mode-closing-paren-position (point) limit)))
    (if (or (null pos) (> pos limit))
        nil
      (goto-char pos)
      pos)
    ))

(defun web-mode-part-next ()
  "Move point to the beginning of the next part."
  (interactive)
  (web-mode-go (web-mode-part-next-position (point))))

(defun web-mode-part-beginning ()
  "Move point to the beginning of the current part."
  (interactive)
  (web-mode-go (web-mode-part-beginning-position (point))))

(defun web-mode-part-end ()
  "Move point to the end of the current part."
  (interactive)
  (web-mode-go (web-mode-part-end-position (point)) 1))

(defun web-mode-block-previous ()
  "Move point to the beginning of the previous block."
  (interactive)
  (web-mode-go (web-mode-block-previous-position (point))))

(defun web-mode-block-next ()
  "Move point to the beginning of the next block."
  (interactive)
  (web-mode-go (web-mode-block-next-position (point))))

(defun web-mode-block-beginning ()
  "Move point to the beginning of the current block."
  (interactive)
  (web-mode-go (web-mode-block-beginning-position (point))))

(defun web-mode-block-end ()
  "Move point to the end of the current block."
  (interactive)
  (web-mode-go (web-mode-block-end-position (point)) 1))

(defun web-mode-block-token-beginning ()
  (web-mode-go (web-mode-block-token-beginning-position (point))))

(defun web-mode-block-token-end ()
  (web-mode-go (web-mode-block-token-end-position (point)) 1))

(defun web-mode-part-token-beginning ()
  (web-mode-go (web-mode-part-token-beginning-position (point))))

(defun web-mode-part-token-end ()
  (web-mode-go (web-mode-part-token-end-position (point)) 1))

(defun web-mode-block-opening-paren (limit)
  (web-mode-go (web-mode-block-opening-paren-position (point) limit)))

(defun web-mode-block-string-beginning (&optional pos block-beg)
  (unless pos (setq pos (point)))
  (unless block-beg (setq block-beg (web-mode-block-beginning-position pos)))
  (web-mode-go (web-mode-block-string-beginning-position pos block-beg)))

(defun web-mode-block-statement-beginning (&optional pos block-beg)
  (unless pos (setq pos (point)))
  (unless block-beg (setq block-beg (web-mode-block-beginning-position pos)))
  (web-mode-go (web-mode-block-statement-beginning-position pos block-beg)))

(defun web-mode-block-args-beginning (&optional pos block-beg)
  (unless pos (setq pos (point)))
  (unless block-beg (setq block-beg (web-mode-block-beginning-position pos)))
  (web-mode-go (web-mode-block-args-beginning-position pos block-beg)))

(defun web-mode-block-calls-beginning (&optional pos block-beg)
  (unless pos (setq pos (point)))
  (unless block-beg (setq block-beg (web-mode-block-beginning-position pos)))
  (web-mode-go (web-mode-block-calls-beginning-position pos block-beg)))

(defun web-mode-javascript-string-beginning (&optional pos reg-beg)
  (unless pos (setq pos (point)))
  (unless reg-beg
    (if (get-text-property pos 'block-side)
        (setq reg-beg (web-mode-block-beginning-position pos))
      (setq reg-beg (web-mode-part-beginning-position pos))))
  (web-mode-go (web-mode-javascript-string-beginning-position pos reg-beg)))

(defun web-mode-javascript-statement-beginning (&optional pos reg-beg)
  (unless pos (setq pos (point)))
  (unless reg-beg
    (if (get-text-property pos 'block-side)
        (setq reg-beg (web-mode-block-beginning-position pos))
      (setq reg-beg (web-mode-part-beginning-position pos))))
  (web-mode-go (web-mode-javascript-statement-beginning-position pos reg-beg)))

(defun web-mode-javascript-args-beginning (&optional pos reg-beg)
  (unless pos (setq pos (point)))
  (unless reg-beg
    (if (get-text-property pos 'block-side)
        (setq reg-beg (web-mode-block-beginning-position pos))
      (setq reg-beg (web-mode-part-beginning-position pos))))
  (web-mode-go (web-mode-javascript-args-beginning-position pos reg-beg)))

(defun web-mode-javascript-calls-beginning (&optional pos reg-beg)
  (unless pos (setq pos (point)))
  (unless reg-beg
    (if (get-text-property pos 'block-side)
        (setq reg-beg (web-mode-block-beginning-position pos))
      (setq reg-beg (web-mode-part-beginning-position pos))))
  (let (pair)
    (setq pair (web-mode-javascript-calls-beginning-position pos reg-beg))
    (when pair (web-mode-go (car pair)))
    ))

(defun web-mode-go (pos &optional offset)
  (unless offset (setq offset 0))
  (when pos
    (cond
     ((and (> offset 0) (<= (+ pos offset) (point-max)))
      (setq pos (+ pos offset)))
     ((and (< offset 0) (>= (+ pos offset) (point-min)))
      (setq pos (+ pos offset)))
     ) ;cond
    (goto-char pos))
  pos)

;;---- SEARCH ------------------------------------------------------------------

(defun web-mode-rsf-balanced (regexp-open regexp-close &optional limit noerror)
  (unless noerror (setq noerror t))
  (let ((continue t)
        (level 1)
        (pos (point))
        ret
        (regexp (concat regexp-open "\\|" regexp-close)))
    (while continue
      (setq ret (re-search-forward regexp limit noerror))
      (cond
       ((null ret)
        (setq continue nil)
        )
       (t
        (if (string-match-p regexp-open (match-string-no-properties 0))
            (setq level (1+ level))
          (setq level (1- level)))
        (when (< level 1)
          (setq continue nil)
          )
        ) ;t
       ) ;cond
      ) ;while
    (when (not (= level 0)) (goto-char pos))
    ret))

(defun web-mode-block-sb (expr &optional limit noerror)
  (unless limit (setq limit (web-mode-block-beginning-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (search-backward expr limit noerror))
      (when (or (null ret)
                (not (get-text-property (point) 'block-token)))
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-block-sf (expr &optional limit noerror)
  (unless limit (setq limit (web-mode-block-end-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (search-forward expr limit noerror))
      (when (or (null ret)
                (not (get-text-property (point) 'block-token)))
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-block-rsb (regexp &optional limit noerror)
  (unless limit (setq limit (web-mode-block-beginning-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (re-search-backward regexp limit noerror))
      (when (or (null ret)
                (not (get-text-property (point) 'block-token)))
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-block-rsf (regexp &optional limit noerror)
  (unless limit (setq limit (web-mode-block-end-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (re-search-forward regexp limit noerror))
      (when (or (null ret)
                (not (get-text-property (point) 'block-token)))
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-part-sb (expr &optional limit noerror)
  (unless limit (setq limit (web-mode-part-beginning-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (search-backward expr limit noerror))
      (when (or (null ret)
                (and (not (get-text-property (point) 'part-token))
                     (not (get-text-property (point) 'block-side)))
                )
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-part-sf (expr &optional limit noerror)
  (unless limit (setq limit (web-mode-part-end-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (search-forward expr limit noerror))
      (when (or (null ret)
                (and (not (get-text-property (point) 'part-token))
                     (not (get-text-property (point) 'block-side)))
                )
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-part-rsb (regexp &optional limit noerror)
  (unless limit (setq limit (web-mode-part-beginning-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (re-search-backward regexp limit noerror))
      (when (or (null ret)
                (and (not (get-text-property (point) 'part-token))
                     (not (get-text-property (point) 'block-side)))
                )
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-part-rsf (regexp &optional limit noerror)
  (unless limit (setq limit (web-mode-part-end-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (re-search-forward regexp limit t))
      (when (or (null ret)
                (and (not (get-text-property (point) 'part-token))
                     (not (get-text-property (point) 'block-side)))
                )
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-javascript-rsb (regexp &optional limit noerror)
  (unless limit (setq limit (web-mode-part-beginning-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (re-search-backward regexp limit noerror))
      (when (or (null ret)
                (and (not (get-text-property (point) 'part-token))
                     (not (get-text-property (point) 'block-side))
                     (not (get-text-property (point) 'jsx-depth)))
                )
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-javascript-rsf (regexp &optional limit noerror)
  (unless limit (setq limit (web-mode-part-end-position (point))))
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (re-search-forward regexp limit t))
      (when (or (null ret)
                (and (not (get-text-property (point) 'part-token))
                     (not (get-text-property (point) 'block-side))
                     (not (get-text-property (point) 'jsx-depth)))
                )
        (setq continue nil)
        ) ;when
      ) ;while
    ret))

(defun web-mode-dom-sf (expr &optional limit noerror)
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (search-forward expr limit noerror))
      (if (or (null ret)
              (not (get-text-property (- (point) (length expr)) 'block-side)))
          (setq continue nil))
      )
    ret))

(defun web-mode-dom-rsf (regexp &optional limit noerror)
  (unless noerror (setq noerror t))
  (let ((continue t) (ret nil))
    (while continue
      (setq ret (re-search-forward regexp limit noerror))
      ;;      (message "ret=%S point=%S limit=%S i=%S" ret (point) limit 0)
      (cond
       ((null ret)
        (setq continue nil))
       ((or (get-text-property (match-beginning 0) 'block-side)
            (get-text-property (match-beginning 0) 'part-token))
        )
       (t
        (setq continue nil))
       ) ;cond
      ) ;while
    ret))

(defun web-mode-rsb (regexp &optional limit noerror)
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (re-search-backward regexp limit noerror))
      (if (or (null ret)
              (not (web-mode-is-comment-or-string)))
          (setq continue nil)))
    ret))

(defun web-mode-rsf (regexp &optional limit noerror)
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (re-search-forward regexp limit noerror))
      (if (or (null ret)
              (not (web-mode-is-comment-or-string)))
          (setq continue nil))
      )
    ret))

(defun web-mode-sb (expr &optional limit noerror)
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (search-backward expr limit noerror))
      (if (or (null ret)
              (not (web-mode-is-comment-or-string)))
          (setq continue nil)))
    ret))

(defun web-mode-sf (expr &optional limit noerror)
  (unless noerror (setq noerror t))
  (let ((continue t) ret)
    (while continue
      (setq ret (search-forward expr limit noerror))
      (if (or (null ret)
              (not (web-mode-is-comment-or-string)))
          (setq continue nil)))
    ret))

(defun web-mode-content-rsf (regexp &optional limit noerror)
  (unless noerror (setq noerror t))
  (let ((continue t) ret beg end)
    (while continue
      (setq ret (re-search-forward regexp limit noerror)
            beg (if (null ret) (point) (match-beginning 0))
            end (if (null ret) (point) (1- (match-end 0))))
      (if (or (null ret)
              (and (web-mode-is-content beg)
                   (web-mode-is-content end)))
          (setq continue nil)))
    ret))

;;---- ADVICES -----------------------------------------------------------------

(defadvice ac-start (before web-mode-set-up-ac-sources activate)
  "Set `ac-sources' based on current language before running auto-complete."
  (when (equal major-mode 'web-mode)
    ;; set ignore each time to nil. User has to implement a hook to change it
    ;; for each completion
    (setq web-mode-ignore-ac-start-advice nil)
    (run-hooks 'web-mode-before-auto-complete-hooks)
    (unless web-mode-ignore-ac-start-advice
      (when web-mode-ac-sources-alist
        (let ((new-web-mode-ac-sources
               (assoc (web-mode-language-at-pos)
                      web-mode-ac-sources-alist)))
          (setq ac-sources (cdr new-web-mode-ac-sources)))))))

;;---- MINOR MODE ADDONS -------------------------------------------------------

(defun web-mode-yasnippet-exit-hook ()
  "Yasnippet exit hook"
  (when (and (boundp 'yas-snippet-beg) (boundp 'yas-snippet-end))
    (indent-region yas-snippet-beg yas-snippet-end)))

(defun web-mode-imenu-index ()
  (interactive)
  "Returns imenu items."
  (let (toc-index
        line)
    (save-excursion
      (goto-char (point-min))
      (while (not (eobp))
        (setq line (buffer-substring-no-properties
                    (line-beginning-position)
                    (line-end-position)))
        (let (found
              (i 0)
              item
              regexp
              type
              type-idx
              content
              content-idx
              content-regexp
              close-tag-regexp
              concat-str
              jumpto
              str)
          (while (and (not found ) (< i (length web-mode-imenu-regexp-list)))
            (setq item (nth i web-mode-imenu-regexp-list))
            (setq regexp (nth 0 item))
            (setq type-idx (nth 1 item))
            (setq content-idx (nth 2 item))
            (setq concat-str (nth 3 item))
            (when (not (numberp content-idx))
              (setq content-regexp (nth 2 item)
                    close-tag-regexp (nth 4 item)
                    content-idx nil))

            (when (string-match regexp line)

              (cond
               (content-idx
                (setq type (match-string type-idx line))
                (setq content (match-string content-idx line))
                (setq str (concat type concat-str content))
                (setq jumpto (line-beginning-position)))
               (t
                (let (limit)
                  (setq type (match-string type-idx line))
                  (goto-char (line-beginning-position))
                  (save-excursion
                    (setq limit (re-search-forward close-tag-regexp (point-max) t)))

                  (when limit
                    (when (re-search-forward content-regexp limit t)
                      (setq content (match-string 1))
                      (setq str (concat type concat-str content))
                      (setq jumpto (line-beginning-position))
                      )
                    )))
               )
              (when str (setq toc-index
                              (cons (cons str jumpto)
                                    toc-index)
                              )
                    (setq found t))
              )
            (setq i (1+ i))))
        (forward-line)
        (goto-char (line-end-position)) ;; make sure we are at eobp
        ))
    (nreverse toc-index)))

;;---- UNIT TESTING ------------------------------------------------------------

(defun web-mode-test ()
  "Executes web-mode unit tests. See `web-mode-tests-directory'."
  (interactive)
  (let (files ret regexp)
    (setq regexp "^[[:alnum:]][[:alnum:]._]+\\'")
    (setq files (directory-files web-mode-tests-directory t regexp))
    (dolist (file files)
      (cond
       ((eq (string-to-char (file-name-nondirectory file)) ?\_)
        (delete-file file))
       (t
        (setq ret (web-mode-test-process file)))
       ) ;cond
      ) ;dolist
    ))

(defun web-mode-test-process (file)
  (with-temp-buffer
    (let (out sig1 sig2 success err)
      (setq-default indent-tabs-mode nil)
      (if (string-match-p "sql" file)
          (setq web-mode-enable-sql-detection t)
        (setq web-mode-enable-sql-detection nil))
      (insert-file-contents file)
      (set-visited-file-name file)
      (web-mode)
      (setq sig1 (md5 (current-buffer)))
      (delete-horizontal-space)
      (while (not (eobp))
        (forward-line)
        (delete-horizontal-space)
        (end-of-line))
      (web-mode-buffer-indent)
      (setq sig2 (md5 (current-buffer)))
      (setq success (string= sig1 sig2))
      (setq out (concat (if success "ok" "ko") " : " (file-name-nondirectory file)))
      (message out)
      (setq err (concat (file-name-directory file) "_err." (file-name-nondirectory file)))
      (if success
          (when (file-readable-p err)
            (delete-file err))
        (write-file err)
        (message "[%s]" (buffer-string))
        ) ;if
      out)))

;;---- MISC --------------------------------------------------------------------

(defun web-mode-set-engine (engine)
  "Set the engine for the current buffer."
  (interactive
   (list (completing-read
          "Engine: "
          (let (engines)
            (dolist (elt web-mode-engines)
              (setq engines (append engines (list (car elt)))))
            engines))))
  (setq web-mode-content-type "html"
        web-mode-engine (web-mode-engine-canonical-name engine)
        web-mode-minor-engine engine)
  (web-mode-on-engine-setted)
  (web-mode-buffer-highlight))

(defun web-mode-set-content-type (content-type)
  "Set the content-type for the current buffer"
  (interactive (list (completing-read "Content-type: " web-mode-part-content-types)))
  (setq web-mode-content-type content-type)
  (when (called-interactively-p 'any)
    )
  (web-mode-buffer-highlight))

(defun web-mode-on-engine-setted ()
  (let (elt elts engines)

    (when (string= web-mode-engine "razor") (setq web-mode-enable-block-face t))
    (setq web-mode-engine-attr-regexp (cdr (assoc web-mode-engine web-mode-engine-attr-regexps)))
    (setq web-mode-engine-token-regexp (cdr (assoc web-mode-engine web-mode-engine-token-regexps)))

    ;;(message "%S %S" web-mode-engine-attr-regexp web-mode-engine)

    (when (null web-mode-minor-engine)
      (setq web-mode-minor-engine "none"))

    (setq elt (assoc web-mode-engine web-mode-engine-open-delimiter-regexps))
    (if elt
        (setq web-mode-block-regexp (cdr elt))
      (setq web-mode-engine "none"))

    (unless (boundp 'web-mode-extra-auto-pairs)
      (setq web-mode-extra-auto-pairs nil))

    (setq web-mode-auto-pairs
          (append
           (cdr (assoc web-mode-engine web-mode-engines-auto-pairs))
           (cdr (assoc nil web-mode-engines-auto-pairs))
           (cdr (assoc web-mode-engine web-mode-extra-auto-pairs))
           (cdr (assoc nil web-mode-extra-auto-pairs))))

    (unless (boundp 'web-mode-extra-snippets)
      (setq web-mode-extra-snippets nil))

    (setq elts
          (append
           (cdr (assoc web-mode-engine web-mode-extra-snippets))
           (cdr (assoc nil             web-mode-extra-snippets))
           (cdr (assoc web-mode-engine web-mode-engines-snippets))
           (cdr (assoc nil             web-mode-engines-snippets))))

    (dolist (elt elts)
      (unless (assoc (car elt) web-mode-snippets)
        (setq web-mode-snippets (append (list elt) web-mode-snippets)))
      )

    (setq web-mode-engine-font-lock-keywords
          (symbol-value (cdr (assoc web-mode-engine web-mode-engines-font-lock-keywords))))

    (when (and (string= web-mode-minor-engine "jinja")
               (not (member "endtrans" web-mode-django-control-blocks)))
      (add-to-list 'web-mode-django-control-blocks "endtrans")
      (setq web-mode-django-control-blocks-regexp
            (regexp-opt web-mode-django-control-blocks t))
      )

;;    (message "%S" (symbol-value (cdr (assoc web-mode-engine web-mode-engines-font-lock-keywords))))

    ))

(defun web-mode-detect-engine ()
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "-\\*- engine:[ ]*\\([[:alnum:]-]+\\)[ ]*-\\*-" web-mode-chunk-length t)
      (setq web-mode-minor-engine (match-string-no-properties 1))
      (setq web-mode-engine (web-mode-engine-canonical-name web-mode-minor-engine)))
    web-mode-minor-engine))

(defun web-mode-guess-engine-and-content-type ()
  (let (buff-name elt found)

    (setq buff-name (buffer-file-name))
    (unless buff-name (setq buff-name (buffer-name)))
    (setq web-mode-is-scratch (string= buff-name "*scratch*"))
    (setq web-mode-content-type nil)

    (when (boundp 'web-mode-content-types-alist)
      (setq found nil)
      (dolist (elt web-mode-content-types-alist)
        (when (and (not found) (string-match-p (cdr elt) buff-name))
          (setq web-mode-content-type (car elt)
                found t))
        ) ;dolist
      ) ;when

    (unless web-mode-content-type
      (setq found nil)
      (dolist (elt web-mode-content-types)
        (when (and (not found) (string-match-p (cdr elt) buff-name))
          (setq web-mode-content-type (car elt)
                found t))
        ) ;dolist
      ) ;unless

    (when (boundp 'web-mode-engines-alist)
      (setq found nil)
      (dolist (elt web-mode-engines-alist)
        (cond
         ((stringp (cdr elt))
          (when (string-match-p (cdr elt) buff-name)
            (setq web-mode-engine (car elt))))
         ((functionp (cdr elt))
          (when (funcall (cdr elt))
            (setq web-mode-engine (car elt))))
         ) ;cond
        ) ;dolist
      ) ;when

    (unless web-mode-engine
      (setq found nil)
      (dolist (elt web-mode-engine-file-regexps)
        ;;(message "%S %S" (cdr elt) buff-name)
        (when (and (not found) (string-match-p (cdr elt) buff-name))
          (setq web-mode-engine (car elt)
                found t))
        )
      )

    (when (and (or (null web-mode-engine) (string= web-mode-engine "none"))
               (string-match-p "php" (buffer-substring-no-properties
                                      (line-beginning-position)
                                      (line-end-position))))
      (setq web-mode-engine "php"))

    (when (and (string= web-mode-content-type "javascript")
               (string-match-p "@jsx"
                               (buffer-substring-no-properties
                                (point-min)
                                (if (< (point-max) web-mode-chunk-length)
                                    (point-max)
                                  web-mode-chunk-length)
                                )))
      (setq web-mode-content-type "jsx"))

    (when web-mode-engine
      (setq web-mode-minor-engine web-mode-engine
            web-mode-engine (web-mode-engine-canonical-name web-mode-engine))
      )

    (when (and (or (null web-mode-engine)
                   (string= web-mode-engine "none"))
               web-mode-enable-engine-detection)
      (web-mode-detect-engine))

    (web-mode-on-engine-setted)

    ))

(defun web-mode-engine-canonical-name (name)
  (let (engine)
    (cond
     ((null name)
      nil)
     ((assoc name web-mode-engines)
      name)
     (t
      (dolist (elt web-mode-engines)
        (when (and (null engine) (member name (cdr elt)))
          (setq engine (car elt)))
        ) ;dolist
      engine)
     )))

(defun web-mode-on-after-save ()
  (when web-mode-is-scratch
    (web-mode-guess-engine-and-content-type)
    (web-mode-buffer-highlight))
  nil)

(defun web-mode-on-exit ()
  (web-mode-with-silent-modifications
   (put-text-property (point-min) (point-max) 'invisible nil)
   (remove-overlays)
   (remove-hook 'change-major-mode-hook 'web-mode-on-exit t)
   ))

(defun web-mode-file-link ()
  "Insert a link to the file in html document. This function can be extended to support more filetypes by customizing `web-mode-file-extensions' and `web-mode-file-elements'."
  (interactive
   (let ((type nil)
         (file (file-relative-name (read-file-name "Link file: ")))
         (matched nil)
         (point-line (line-number-at-pos))
         (point-column (current-column)))
     (dolist (type web-mode-file-extensions)		;for every element in web-mode-type-list
       (when (string-match (nth 0 type) file)
         (setq matched t)
         ;; move to head if the link requires it
         (when (nth 2 type)
           (goto-char (point-min))
           (search-forward "</head>")
           (backward-char 7)
           (open-line 1))
         (insert (nth 0 (nth (nth 1 type) web-mode-file-elements)) file (nth 1 (nth (nth 1 type) web-mode-file-elements)))
         (indent-for-tab-command)
         ;; fix indentation and return point where it was
         (when (nth 2 type)
           (forward-line)
           (indent-for-tab-command)
           (forward-line (+ point-line 1))
           (move-to-column point-column))))
     (when (not matched)		;return an error if filetype is unknown
       (error "Unknown file type")))))

(defun web-mode-reload ()
  "Reload web-mode."
  (interactive)
  (web-mode-with-silent-modifications
    (put-text-property (point-min) (point-max) 'invisible nil)
    (remove-overlays)
    (setq font-lock-unfontify-region-function 'font-lock-default-unfontify-region)
    (load "web-mode.el")
    (setq web-mode-change-beg nil
          web-mode-change-end nil)
    (web-mode)
    ))

(defun web-mode-trace (msg)
  (let (sub)
    ;;      (when (null web-mode-time) (setq web-mode-time (current-time)))
    (setq sub (time-subtract (current-time) web-mode-time))
    (when nil
      (save-excursion
        (let ((n 0))
          (goto-char (point-min))
          (while (web-mode-tag-next)
            (setq n (1+ n))
            )
          (message "%S tags found" n)
          )))
    (message "%18s: time elapsed = %Ss %9Sµs" msg (nth 1 sub) (nth 2 sub))
    ))

(defun web-mode-reveal ()
  "Display text properties at point."
  (interactive)
  (let (symbols out)
    (setq out (format
               "[point=%S engine=%S minor=%S content-type=%S language-at-pos=%S]\n"
               (point)
               web-mode-engine
               web-mode-minor-engine
               web-mode-content-type
               (web-mode-language-at-pos (point))))
    (setq symbols (append web-mode-scan-properties '(font-lock-face face)))
    (dolist (symbol symbols)
      (when symbol
        (setq out (concat out (format "%s(%S) " (symbol-name symbol) (get-text-property (point) symbol)))))
      )
    (message "%s\n" out)
    ;;(message "syntax-class=%S" (syntax-class (syntax-after (point))))
    (message nil)))

(defun web-mode-debug ()
  "Display informations useful for debugging."
  (interactive)
  (let ((modes nil)
        (customs '(web-mode-enable-current-column-highlight web-mode-enable-current-element-highlight indent-tabs-mode))
        (ignore '(abbrev-mode auto-composition-mode auto-compression-mode auto-encryption-mode auto-insert-mode blink-cursor-mode column-number-mode delete-selection-mode display-time-mode electric-indent-mode file-name-shadow-mode font-lock-mode global-font-lock-mode global-hl-line-mode line-number-mode menu-bar-mode mouse-wheel-mode recentf-mode show-point-mode tool-bar-mode tooltip-mode transient-mark-mode)))
    (message "\n")
    (message "--- WEB-MODE DEBUG BEG ---")
    (message "versions: emacs(%S.%S) web-mode(%S)"
             emacs-major-version emacs-minor-version web-mode-version)
    (message "vars: engine(%S) minor(%S) content-type(%S) file(%S)"
             web-mode-engine
             web-mode-minor-engine
             web-mode-content-type
             (or (buffer-file-name) (buffer-name)))
    (message "system: window(%S) config(%S)" window-system system-configuration)
    (message "colors: fg(%S) bg(%S) "
             (cdr (assoc 'foreground-color default-frame-alist))
             (cdr (assoc 'background-color default-frame-alist)))
    (mapc (lambda (mode)
            (condition-case nil
                (if (and (symbolp mode) (symbol-value mode) (not (member mode ignore)))
                    (add-to-list 'modes mode))
              (error nil))
            ) ;lambda
          minor-mode-list)
    (message "minor modes: %S" modes)
    (message "vars:")
    (dolist (custom customs)
      (message (format "%s=%S " (symbol-name custom) (symbol-value custom))))
    (message "--- WEB-MODE DEBUG END ---")
    (switch-to-buffer "*Messages*")
    (goto-char (point-max))
    (recenter)
  ))

(provide 'web-mode)

;;; web-mode.el ends here

;; Local Variables:
;; coding: utf-8
;; indent-tabs-mode: nil
;; End:
