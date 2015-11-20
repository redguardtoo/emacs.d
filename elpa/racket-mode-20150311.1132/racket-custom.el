;;; racket-custom.el

;; Copyright (c) 2013-2015 by Greg Hendershott.
;; Portions Copyright (C) 1985-1986, 1999-2013 Free Software Foundation, Inc.

;; Author: Greg Hendershott
;; URL: https://github.com/greghendershott/racket-mode

;; License:
;; This is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version. This is distributed in the hope that it will be
;; useful, but without any warranty; without even the implied warranty
;; of merchantability or fitness for a particular purpose. See the GNU
;; General Public License for more details. See
;; http://www.gnu.org/licenses/ for details.

;;; All `defcustom's and `defface's go here.
;;; This makes it easier to provide a consistent UI.

;; NOTE: `:prefix` is disabled as of Emacs 24.3, so I'm using explicit
;; `:tag`s. But also note that options are sorted (by default; user
;; can turn that off) based on the identifier name not the `:tag`. As
;; a result, I'm defining `:tag`s AS IF `:prefix "racket-"` did work.
;; In other words defcustom of racket-foo-bar has a :tag "Foo Bar".

(defgroup racket nil
  "Editing and REPL for the Racket language."
  :group 'languages
  :link '(url-link :tag "README on GitHub" "https://github.com/greghendershott/racket-mode/blob/master/README.md"))

(defvar racket--winp (string-match "windows" (symbol-name system-type)))

(defcustom racket-racket-program (cond (racket--winp "Racket.exe")
                                       (t            "racket"))
  "Pathname of the racket executable."
  :tag "Racket Program"
  :type '(file :must-match t)
  :risky t
  :group 'racket)

(defcustom racket-raco-program (cond (racket--winp "Raco.exe")
                                     (t            "raco"))
  "Pathname of the raco executable."
  :tag "Raco Program"
  :type '(file :must-match t)
  :risky t
  :group 'racket)

(defcustom racket-memory-limit 2048
  "Terminate the Racket process if memory use exceeds this value in MB.
Changes to this value take effect upon the next `racket-run'.

Caveat: This uses Racket's `custodian-limit-memory`, which does
not enforce the limit exactly. Instead, the program will be
terminated upon the first garbage collection where memory exceeds
the limit (maybe by a significant amount)."
  :tag "Memory Limit"
  :type 'integer
  :safe #'integerp
  :group 'racket)

(defcustom racket-error-context 'medium
  "The level of context used for `racket-run' error stack traces.

Each level improves stack trace information, but causes your
program to run more slowly.

  - 'low corresponds to `compile-context-preservation-enabled`
    `#f`.

  - 'medium corresponds to `compile-context-preservation-enabled`
    `#t`, which disables some optimizations like inlining.

  - 'high corresponds to `compile-context-preservation-enabled`
    `#t` and to use of `errortrace`, which heavily instruments
    your code and therefore may be significantly slower.

Tip: Regardless of this setting, you can enable 'high errortrace
for a specific `racket-run' using a C-u prefix. This lets you
normally run with a faster setting, and temporarily re-run to get
a more-helpful error message."
  :tag "Error Context"
  :type '(radio (const :tag "Low" low)
                (const :tag "Medium (slower)" medium)
                (const :tag "High (much slower)" high))
  :risky t
  :group 'racket)

;;; REPL

(defgroup racket-repl nil
  "REPL Options"
  :tag "REPL"
  :group 'racket)

(defcustom racket-history-filter-regexp "\\`\\s *\\S ?\\S ?\\s *\\'"
  "Input matching this regexp are not saved on the history list.
Defaults to a regexp ignoring all inputs of 0, 1, or 2 letters."
  :tag "History Filter Regexp"
  :type 'regexp
  :safe #'stringp
  :group 'racket-repl)

(defcustom racket-images-inline t
  "Whether to display inline images in the REPL."
  :tag "Images Inline"
  :type 'boolean
  :safe #'booleanp
  :group 'racket-repl)

(defcustom racket-images-keep-last 100
  "How many images to keep in the image cache."
  :tag "Images Keep Last"
  :type 'integer
  :safe #'integerp
  :group 'racket-repl)

(defcustom racket-images-system-viewer "display"
  "Which system image viewer program to invoke upon M-x
 `racket-view-last-image'."
  :tag "Images System Viewer"
  :type 'string
  :risky t
  :group 'racket-repl)

(defcustom racket-pretty-print t
  "Use pretty-print instead of print in REPL."
  :tag "Pretty Print"
  :type 'boolean
  :safe #'booleanp
  :group 'racket-repl)

(defcustom racket-wait-for-prompt-timeout 30
  "When REPL starts Racket process, how long to wait for Racket prompt."
  :tag "Wait For Prompt Timeout"
  :type 'number
  :safe #'numberp
  :group 'racket-repl)


;;; Other

(defgroup racket-other nil
  "Other Options"
  :tag "Other"
  :group 'racket)

(defcustom racket-indent-curly-as-sequence t
  "Indent `{}` with items aligned with the head item?
This is indirectly disabled if `racket-indent-sequence-depth' is 0.
This is safe to set as a file-local variable."
  :tag "Indent Curly As Sequence"
  :type 'boolean
  :safe #'booleanp
  :group 'racket-other)

(defcustom racket-indent-sequence-depth 0
  "To what depth should `racket--align-sequence-to-head' search.
This affects the indentation of forms like `` '()` `() #() `` --
and `{}` if `racket-indent-curly-as-sequence' is t -- but not
`` #'() #`() ,() ,@() ``. A zero value disables, giving the
normal indent behavior of DrRacket or Emacs `lisp-mode' derived
modes like `scheme-mode'. Setting this to a high value can make
indentation noticeably slower. This is safe to set as a
file-local variable."
  :tag "Indent Sequence Depth"
  :type 'integerp
  :safe #'integerp
  :group 'racket-other)

(defcustom racket-pretty-lambda nil
  "Display lambda keywords using λ. This is deprecated.
Instead you can insert actual λ characters using
\\<racket-mode-map>\\[racket-insert-lambda]
`racket-insert-lambda'."
  :tag "Pretty Lambda"
  :type 'boolean
  :safe #'booleanp
  :group 'racket-other)

(defcustom racket-smart-open-bracket-enable nil
  "Use `racket-smart-open-bracket' when `[` is pressed?"
  :tag "Smart Open Bracket Enable"
  :type 'boolean
  :safe #'booleanp
  :group 'racket-other)

(defcustom racket-use-company-mode t
  "Enable company-mode for racket-mode edit buffers?"
  :tag "Use Company Mode"
  :type 'boolean
  :safe #'booleanp
  :group 'racket-other)


;;; Faces

(defgroup racket-faces nil
  "Faces"
  :tag "Faces"
  :group 'faces
  :group 'racket)

(defconst racket-check-syntax-def-face 'racket-check-syntax-def-face)
(defface racket-check-syntax-def-face
  '((t
     (:foreground "Black" :background "SeaGreen1" :weight bold)))
  "Face `racket-check-syntax' uses to highlight definitions."
  :tag "Check Syntax Def Face"
  :group 'racket-faces)

(defconst racket-check-syntax-use-face 'racket-check-syntax-use-face)
(defface racket-check-syntax-use-face
  '((t
     (:foreground "Black" :background "PaleGreen1" :slant italic)))
  "Face `racket-check-syntax' uses to highlight uses."
  :tag "Check Syntax Use Face"
  :group 'racket-faces)

(defconst racket-keyword-argument-face 'racket-keyword-argument-face)
(defface racket-keyword-argument-face
  '((((background dark))
     (:foreground "IndianRed"))
    (((background light))
     (:foreground "Red3")))
  "Face for `#:keyword` arguments."
  :tag "Keyword Argument Face"
  :group 'racket-faces)

(defconst racket-paren-face 'racket-paren-face)
(defface racket-paren-face
  (let ((fg (face-foreground 'default)))
    `((t (:foreground ,fg))))
  "Face for `() [] {}`."
  :tag "Paren Face"
  :group 'racket-faces)

(defconst racket-selfeval-face 'racket-selfeval-face)
(defface racket-selfeval-face
  '((t
     (:foreground "SeaGreen")))
  "Face for self-evaluating expressions like numbers, symbols, strings."
  :tag "Selfeval Face"
  :group 'racket-faces)

;; racket-custom.el ends here

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:

(provide 'racket-custom)
