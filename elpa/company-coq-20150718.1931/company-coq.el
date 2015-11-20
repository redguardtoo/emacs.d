;;; company-coq.el --- Company-mode backend for Proof General's coq-mode -*- lexical-binding: t -*-

;; Copyright (C) 2015  Clément Pit--Claudel
;; Author: Clément Pit--Claudel <clement.pitclaudel@live.com>
;; URL: https://github.com/cpitclaudel/company-coq

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
;; This package includes a company backend for Proof-General's Coq mode, and
;; many useful extensions to Proof-General.
;;
;; See https://github.com/cpitclaudel/company-coq/ for a full description,
;; including screenshots and documentation. After installing, you may want to
;; use M-x company-coq-tutorial to open the tutorial.
;;

;;; Code:
;;
;; Technical notes
;; ===============
;;
;; Sending  commands to  the prover  when it's  already busy  breaks everything.
;; 'proof-shell-handle-delayed-output-hook is  a good  place to  reload symbols,
;; except when an error occurs (in that case the hook runs before all output has
;; been processed.
;;
;; This problem is solved by refusing  to communicate with the prover, unless it
;; is reported as available. When it isn't, the interaction is either abandonned
;; (that's what happens  with documentation, and with completion  if the symbols
;; aren't available yet)) or delayed using  an idle timer (reload; in fact, this
;; one is always wrapped in an idle  timer). To prevent loops due to idle timers
;; firing in succession, reloads are only attempted once.
;;
;; The current implementation uses two hooks:
;;  * 'proof-shell-insert-hook
;;      In this one we check the input to see if it might introduce new symbols
;;      (e.g. [Require ...])
;;  * 'proof-shell-handle-delayed-output-hook
;;      In this one we parse the output to see if it suggests that new symbols
;;      have been introduced (e.g. [... defined])
;;
;; Since these  two hooks are  called into even for  commands issued by  our own
;; code, we only execute their body if  we are not currently already waiting for
;; an answer from the prover (company-coq-asking-question).

(require 'shr)          ;; HTML rendering
(require 'company)      ;; Autocompletion
(require 'company-math) ;; Math symbols
(require 'cl-lib)       ;; Compatibility
(require 'outline)      ;; Outlines
(require 'yasnippet)    ;; Templates
(require 'paren)        ;; Find matching block start
(require 'smie)         ;; Move around the source code
(require 'diff-mode)    ;; Browsing through large error messages
(require 'dash)         ;; -when-let and -if-let ;; FIXME: Require only on compilation

(require 'company-coq-abbrev) ;; Tactics from the manual
(require 'company-coq-tg)     ;; Parsing code for tactic notations

(unless (require 'proof-site nil t)
  (message "company-coq: Unable to load proof-site. Is ProofGeneral installed, and did you add it to your load-path?"))

(defgroup company-coq nil
  "Completion back-end for Coq"
  :group 'company)

(defcustom company-coq-debug nil
  "Debug mode for company-coq."
  :group 'company-coq)

(defcustom company-coq-custom-snippets '("Section ${1:SectionName}.\n$0\nEnd $1."
                                         "Chapter ${1:ChapterName}.\n$0\nEnd $1." ;; Commented out in RefMan-ext.v
                                         "Module ${1:ModuleName}.\n$0\nEnd $1."
                                         "Module Type ${1:ModuleTypeName}.\n$0\nEnd $1."
                                         "match ${ident} with"
                                         "match goal with\n$0\nend")
  "Custom YAS snippets") ;; FIXME add to tutorial

(defcustom company-coq-dynamic-autocompletion nil
  "Autocomplete theorem and tactic names by periodically querying coq about defined identifiers. This is an experimental feature. It requires a patched version of Coq to work properly; it will be very slow otherwise."
  :group 'company-coq)

(defvar company-coq--has-dynamic-completion nil
  "Equal to `company-coq-dynamic-autocompletion' if capability detection succeeds")

(defcustom company-coq-autocomplete-context t
  "Autocomplete hypotheses by parsing the latest Goals output. This is an experimental feature."
  :group 'company-coq)

(defcustom company-coq-autocomplete-modules t
  "Autocomplete module names by periodically querying coq about the current load path. This is an experimental feature."
  :group 'company-coq)

(defcustom company-coq-autocomplete-block-end t
  "Autocomplete the name of the last opened block. This is an experimental feature."
  :group 'company-coq)

(defcustom company-coq-autocomplete-search-results t
  "Autocomplete symbol names pulled from the results of the last search. This is an experimental feature."
  :group 'company-coq)

(defcustom company-coq-autocomplete-symbols t
  "Autocomplete symbols by searching in the buffer for lemmas and theorems. If `company-coq-dynamic-autocompletion' is non-nil, query the proof assistant in addition to searching."
  :group 'company-coq)

(defcustom company-coq-prettify-symbols t
  "Transparently replace keywords by the corresponding symbols (e.g. ∀ for forall). The contents of the buffer are not changed."
  :group 'company-coq)

(defcustom company-coq-explicit-placeholders t
  "Show holes using explicit placeholders"
  :group 'company-coq)

(defcustom company-coq-backends '(company-math-symbols-unicode company-coq-reserved-keywords company-coq-keywords)
  "List of backends to use for completion."
  :group 'company-coq)

(defcustom company-coq-disabled-patterns '("without loss")
  "List of patterns that are not imported from Proof General's list."
  :group 'company-coq)

(defvar company-coq-disabled-patterns-regexp (regexp-opt company-coq-disabled-patterns)
  "Regexp version of `company-coq-disabled-patterns'")

(defcustom company-coq-sorted-backends '(company-math-symbols-unicode
                                         company-coq-reserved-keywords
                                         company-coq-block-end
                                         company-coq-modules
                                         company-coq-context
                                         company-coq-keywords
                                         company-coq-defuns
                                         company-coq-search-results
                                         company-coq-tactics
                                         company-coq-symbols)
  "List of all backends, listed in the order in which you want
the results displayed. Note that the first backend that returns a
prefix superseeds all the others; they all must work with the
same prefix."
  :group 'company-coq)

(defvar company-coq-asking-question nil
  "Indicates whether a interaction has been initiated with the prover, to disable the input and output hooks.")

(defvar company-coq-symbols-reload-needed nil
  "Indicates whether a reload of all symbols might be needed. This variable is
  set from places where immediate reloading is impossible, for example in proof-shell-insert-hook")

(defvar company-coq-tactics-reload-needed nil
  "Indicates whether a reload of all tactics might be needed. This variable is
  set from places where immediate reloading is impossible, for example in proof-shell-insert-hook")

(defvar company-coq-modules-reload-needed nil
  "Indicates whether a reload of all modules might be needed. This variable is
  set from places where immediate reloading is impossible, for example in proof-shell-insert-hook")

(defvar company-coq-dynamic-symbols nil
  "Keeps track of defined symbols.")

(defvar company-coq-dynamic-tactics nil
  "Keeps track of defined tactics.")

(defvar company-coq-buffer-defuns nil
  "Keeps track of buffer symbols, based on regexp searches")

(defvar company-coq-current-context nil
  "Keeps track of the context while proofs are ongoing.")

(defvar company-coq-known-path-specs nil
  "Keeps track of paths specs in load path.")

(defvar  company-coq-known-keywords nil
  "List of defined Coq syntax forms")

(defvar company-coq-last-goals-output nil
  "If proof-shell-last-goals-output matches this, it is ignored. This prevents old goals from being reparsed.")

(defvar company-coq-last-search-results nil
  "This stores a list of symbol names, extracted form the response of a search command.")

(defvar company-coq-last-search-scan-size nil
  "If the response buffer has this size, search results are deemed up to date.")

(defvar company-coq-definition-overlay nil
  "Overlay used to show a definition for the symbol under point")

(defvar company-coq-needs-capability-detection t
  "Tracks whether capability detection has already happened.")

(defconst company-coq-capability-test-cmd "Test Search Output Name Only"
  "Command use to test for dynamic completion capabilities. Two patches are
required for proper completion: [Redirect]ion to a file, and [Search Output
Name Only].")

(defconst company-coq-id-regexp            "\\(?:[a-zA-Z0-9_][a-zA-Z0-9_']*\\)")
(defconst company-coq-prefix-regexp        "\\(?:[a-zA-Z0-9_][a-zA-Z0-9_.'!]*\\)?") ;; '!' included for patterns like [intros!]
(defconst company-coq-symbol-regexp        "\\(?:[a-zA-Z0-9_]\\(?:[a-zA-Z0-9_.']*[a-zA-Z0-9_.']\\)?\\)")

(defconst company-coq-all-symbols-slow-regexp (concat "^\\(" company-coq-symbol-regexp "\\):")
  "Regexp used to filter out lines without symbols in output of SearchPattern")

(defconst company-coq-goals-hyp-regexp (concat "\\`  \\(" company-coq-id-regexp "\\) : \\(.*\\)\\'")
  "Regexp used to find hypotheses in goals output")

(defconst company-coq-goal-separator-regexp "  \\(=============================*\\)")

(defconst company-coq-goal-separator-line-regexp (concat "\\`" company-coq-goal-separator-regexp " *\\'")
  "Regexp used to find hypotheses in goals output")

(defconst company-coq-goal-lines-regexp "\\`   "
  "Regexp used to find goal lines in goals output")

(defconst company-coq-path-regexp  (concat "\\`\\(\\S-*\\) +\\(\\S-*\\)\\'"))

(defun company-coq-make-headers-regexp (headers &optional body)
  (concat "^[[:blank:]]*\\_<\\(" (regexp-opt headers) "\\)\\_>"
          (when body (concat "\\s-*\\(" body "\\)"))))

(defconst company-coq-defuns-kwds `("Class" "CoFixpoint" "CoInductive" "Corollary"
                                    "Definition" "Example" "Fact" "Fixpoint"
                                    "Function" "Inductive" "Instance" "Lemma"
                                    "Let" "Ltac" "Program" "Program Fixpoint"
                                    "Record" "Theorem" "with"))

(defconst company-coq-defuns-regexp (company-coq-make-headers-regexp company-coq-defuns-kwds
                                                                     company-coq-id-regexp)
  "Regexp used to locate symbol definitions in the current buffer.
This is mostly useful of company-coq-dynamic-autocompletion is nil.")

(defconst company-coq-block-end-regexp (company-coq-make-headers-regexp '("End") company-coq-id-regexp)
  "Regexp used to find section endings")

(defcustom company-coq-search-blacklist '("_ind" "_rec" "_rect" "Raw" "Proofs") ;; "_refl" "_sym" "_trans"
  "List of strings to add to Coq's search blacklist when loading completion candidates")

(defconst company-coq-search-blacklist-str (mapconcat (lambda (str) (concat "\"" str "\""))
                                                      company-coq-search-blacklist " "))

(defconst company-coq-search-blacklist-add-cmd (concat "Add Search Blacklist "
                                                       company-coq-search-blacklist-str))

(defconst company-coq-search-blacklist-rem-cmd (concat "Remove Search Blacklist "
                                                       company-coq-search-blacklist-str))

(defconst company-coq-all-symbols-prelude (cons company-coq-search-blacklist-add-cmd
                                                '("Set Search Output Name Only"))
  "Command to run before listing all symbols, using a patched version of Coq")

(defconst company-coq-redirection-template "Redirect \"%s\" %s")

(defconst company-coq-all-symbols-cmd "SearchPattern _"
  "Command used to list all symbols.")

(defconst company-coq-all-ltacs-cmd "Print Ltac Signatures"
  "Command used to list all tactics.")

(defconst company-coq-all-notations-cmd "Print Grammar tactic"
  "Command used to list all tactic notations.")

(defvar company-coq-extra-symbols-cmd nil
  "Command used to list more symbols ([SearchPattern _] doesn't search inside modules in 8.4).")

(defconst company-coq-all-symbols-coda (cons company-coq-search-blacklist-rem-cmd
                                             '("Unset Search Output Name Only"))
  "Command to run after listing all symbols, using a patched version of Coq")

(defconst company-coq-doc-cmd "About %s"
  "Command used to retrieve the documentation of a symbol.")

(defconst company-coq-def-cmd "Print %s"
  "Command used to retrieve the definition of a symbol.")

(defconst company-coq-type-cmd "Check %s"
  "Command used to retrieve the type of a symbol.")

(defconst company-coq-tactic-def-cmd "Print Ltac %s"
  "Command used to retrieve the documentation of a symbol.")

(defconst company-coq-symbols-meta-cmd "Check %s."
  "Command used to retrieve a short description of a symbol.")

(defconst company-coq-modules-cmd "Print LoadPath."
  "Command used to retrieve module path specs (for module name completion).")

(defconst company-coq-locate-symbol-cmd "Locate %s."
  "Command used to retrieve the qualified name of a symbol (to locate the corresponding source file).")

(defconst company-coq-locate-tactic-cmd "Locate Ltac %s."
  "Command used to retrieve the qualified name of an Ltac. Needed
in 8.4, not in 8.5.")

(defconst company-coq-locate-output-format (concat "\\`" (regexp-opt (cons "Constant" company-coq-defuns-kwds)) "\\_> +"
                                                   "\\(" company-coq-symbol-regexp "\\)")
  "Output of `company-coq-locate-tactic-cmd' and `company-coq-locate-symbol-cmd'; it can contain details
about shorter names, and other matches")

(defconst company-coq-locate-lib-cmd "Locate Library %s."
  "Command used to retrieve the qualified name of a symbol (to locate the corresponding source file).")

(defconst company-coq-locate-lib-output-format "\\`\\(.*\\)\\s-*has\\s-*been\\s-*loaded\\s-*from\\s-*file\\s-*\\(.*\\.vi?o\\)"
  "Output of `company-coq-locate-lib-cmd'")

(defconst company-coq-compiled-regexp "\\.vi?o\\'"
  "Regexp matching the extension of compiled Coq files.")

(defconst company-coq-end-of-def-regexp "\\(is\\|are\\) \\(recursively \\)?\\(defined\\|assumed\\)"
  "Regexp used to detect signs that new definitions have been added to the context")

(defconst company-coq-error-regexp "\\`Error: "
  "Regexp used to detect errors (useful in particular to prevent reloading the modules list after a failed import.")

(defconst company-coq-error-regexps `(,company-coq-error-regexp
                                      " not a defined object.\\s-\\'"
                                      "\\`No object of basename"
                                      "\\`Toplevel input, characters"
                                      "\\`No Ltac definition is referred to by")
  "Regexp used to detect invalid output")

(defconst company-coq-import-regexp (regexp-opt '("From" "Require" "Import" "Export"))
  "Regexp used to detect signs that new definitions will be added to the context")

(defconst company-coq-tac-notation-regexp (regexp-opt '("Tactic Notation"))
  "Regexp used to detect signs that a tactic notation will be added to the context")

(defconst company-coq-load-regexp "\\(LoadPath\\)"
  "Regexp used to detect signs that new paths will be added to the load path")

(defconst company-coq-doc-tagline "Documentation for symbol %s"
  "Format string for the header of the documentation buffer")

(defconst company-coq-doc-def-sep "\n---\n\n"
  "Separation line between sections in the doc buffer.")

(defconst company-coq-dabbrev-to-yas-regexp "#\\|@{\\([^}]+\\)}"
  "Used to match replace holes in dabbrevs")

(defconst company-coq-yasnippet-choice-regexp "${\\([a-z]+\\(|[a-z]+\\)+\\)}"
  "Used to find choice patterns in dabbrevs")

(defconst company-coq-placeholder-regexp (concat company-coq-dabbrev-to-yas-regexp
                                                 "\\|\\${\\([^}]+\\)}\\|\\$[[:digit:]]")
  "Used to count placeholders in abbrevs")

(defconst company-coq-section-kwds '("Chapter" "Module" "Module Type" "Section")
  "Keywords used in outline mode and in company-coq-occur")

(defconst company-coq-named-outline-kwds `("Equations" "Notation" "Remark" "Tactic Notation"
                                           ,@company-coq-section-kwds ,@company-coq-defuns-kwds)
  "Keywords used in outline mode and in company-coq-occur")

(defconst company-coq-anonymous-outline-kwds '("Goal"))

(defconst company-coq-section-regexp (company-coq-make-headers-regexp company-coq-section-kwds
                                                                      company-coq-id-regexp)
  "Regexp used to locate the closest section opening")

;; TODO: Would be nice to fold [Require Import]s together instead of hiding them entirely
(defconst company-coq-outline-regexp
  (concat "\\(?:" (company-coq-make-headers-regexp company-coq-named-outline-kwds company-coq-id-regexp)
          "\\)\\|\\(?:" (company-coq-make-headers-regexp company-coq-anonymous-outline-kwds nil) "\\)")
  "Regexp used to locate headings")

(defun company-coq-outline-level ()
  "Function used to determine the current outline level"
  0)

(defconst company-coq-outline-heading-end-regexp "\\.[ \t\n]\\|\n"
  "Regexp used to locate the end of a heading")

(defcustom company-coq-prettify-symbols-alist '(("|-" . ?⊢) ("True" . ?⊤) ("False" . ?⊥)
                                                ("->" . ?→) ("-->" . ?⟶) ("<-" . ?←)
                                                ("<--" . ?⟵) ("<->" . ?↔) ("<-->" . ?⟷)
                                                ("=>" . ?⇒) ("==>" . ?⟹) ("<==" . ?⟸)
                                                ("++>" . ?⟿) ("<++" . ?⬳) ("fun" . ?λ)
                                                ("forall" . ?∀) ("exists" . ?∃) ("/\\" . ?∧)
                                                ("\\/" . ?∨) ("~" . ?¬) ("+-" . ?±)
                                                ("<=" . ?≤) (">=" . ?≥) ("<>" . ?≠)
                                                ("*" . ?×) ("++" . ?⧺) ("nat" . ?𝓝)
                                                ("Z" . ?ℤ) ("N" . ?ℕ) ("Q" . ?ℚ)
                                                ("Real" . ?ℝ) ("bool" . ?𝔹) ("Prop" . ?𝓟))
  "An alist of symbols to prettify.
Assigned to `prettify-symbols-alist' in emacs >= 24.4"
  :group 'company-coq
  :type 'alist)

(defcustom company-coq-local-symbols nil
  "An alist of file-specific symbols to prettify.
Combined with `company-coq-prettify-symbols-alist'. Most useful
as a file or dir-local variable."
  :group 'company-coq
  :type 'alist
  :safe 'listp)

(defconst company-coq-numeric-hypothesis-regexp "\\(?:^  \\|, \\)[A-Za-zΑ-Ωα-ω]\\([0-9]+\\)\\b"
  "Regexp used to detect hypotheses of the form Hyp25 and change them into Hyp_25")

(defconst company-coq-lemma-introduction-forms
  '("repeat match goal with H:_ |- _ => clear H end"
    "repeat match goal with H:_ |- _ => generalize dependent H; try (generalize dependent H; fail 1) end")
  "Forms run after 'generalize dependent ...' to produce a lemma
statement. The try (...) part ensures that section variables
don't cause an infinite loop (they are not cleared by [generalize
dependent]).")

(defconst company-coq-unification-error-header
  "\\(?:The command has indeed failed with message:\\|Error:\\)")

(defconst company-coq-unification-error-messages
  '("Refiner was given an argument \".*\" of type \"\\(?1:.*\\)\" instead of \"\\(?2:.*\\)\"."
    "Unable to unify \"\\(?1:.*\\)\" with \"\\(?2:.*\\)\"."
    "Impossible to unify \"\\(?1:.*\\)\" with \"\\(?2:.*\\)\"."
    "In environment.*The term \".*\" has type \"\\(?1:.*\\)\" while it is expected to have type \"\\(?2:.*\\)\"."))

(defconst company-coq-unification-error-message
  (replace-regexp-in-string
   (regexp-quote ".") (replace-quote "\\(?:.\\|[\n]\\)")
   (replace-regexp-in-string
    (regexp-quote " ") (replace-quote "\\s-*")
    (concat company-coq-unification-error-header " " "\\(?:"
            (mapconcat #'identity company-coq-unification-error-messages "\\|")
            "\\)\\s-*"))))

(defconst company-coq-deprecated-options '("Equality Scheme" "Record Elimination Schemes"
                                           "Tactic Evars Pattern Unification" "Undo")
  "Deprecated options, as reported by [Print Tables].")

(defconst company-coq-deprecated-options-re (concat "\\(?1:" (regexp-opt '("Set" "Unset" "Test")) " "
                                                    (regexp-opt company-coq-deprecated-options) "\\)")
  "Regexp to spot uses of deprecated options.")

(defconst company-coq-deprecated-vernacs-re (concat "\\(?1:" (regexp-opt '("Include Type"
                                                                           "Arguments Scope"
                                                                           "Implicit Arguments")) "\\)")
  "Regexp to spot uses of deprecated vernacs.")

(defconst company-coq-deprecated-man-re
  (mapconcat (lambda (x) (concat "\\(?:\\_<" x "\\)"))
             '("\\(?1:assert\\) (.* := .*)" "\\(?1:double induction\\)"
               "\\(?1:appcontext\\_>\\)[ a-zA-Z]*\\[" "\\(?1:cutrewrite\\) \\(?:<-\\|->\\)"
               "\\(?1:Backtrack [[:digit:]]+ [[:digit:]]+ [[:digit:]]+\\)" "\\(?1:SearchAbout\\_>\\)"
               "\\(?1:Save\\_>\\(?: \\(?:Lemma\\|Theorem\\|Remark\\|Fact\\|Corollary\\|Proposition\\)\\_>\\)?\\)"
               "\\(?1:absurd_hyp\\_>\\) [A-Za-z]")
             "\\|"))

(defconst company-coq-deprecated-re (concat "^[[:blank:]]*\\(?:"
                                            "\\(?:" company-coq-deprecated-options-re "\\)\\|"
                                            "\\(?:" company-coq-deprecated-vernacs-re "\\)\\|"
                                            "\\(?:" company-coq-deprecated-man-re "\\)"
                                            "\\)")
  "Deprecated forms.")

(defconst company-coq-script-full-path load-file-name
  "Full path of this script")

(defface company-coq-doc-header-face-source
  '((t :height 1.5))
  "Face used to highlight the target line in source view"
  :group 'company-coq)

(defface company-coq-doc-header-face-docs
  '((t :inherit highlight :height 1.2))
  "Face used to highlight the target line in the docs"
  :group 'company-coq)

(defface company-coq-doc-tt-face
  '((t :inherit font-lock-keyword-face :weight bold))
  "Face used to highlight keywords in the docs"
  :group 'company-coq)

(defface company-coq-doc-i-face
  '((t :inherit font-lock-variable-name-face :weight bold :slant italic))
  "Face used to highlight symbol names in the docs"
  :group 'company-coq)

(defface company-coq-subscript-face
  '((t :height 0.9))
  "Face used to change nubers to subscripts in hypothese names"
  :group 'company-coq)

(defconst company-coq-subscript-spec
  `((,company-coq-numeric-hypothesis-regexp 1 '(face 'company-coq-subscript-face display (raise -0.1)) append))
  "Create a face specification for subscripts, suitable for use with `font-lock-add-keywords'.")

(defconst company-coq-goal-separator-spec
  `((,(concat "^" company-coq-goal-separator-regexp) 1
     '(face nil display "════════════════════════════") append))
  "Create a face specification for a sequence of '=' signs, suitable for use with `font-lock-add-keywords'.")

(defconst company-coq-deprecated-spec
  `((,company-coq-deprecated-re 1
     '(face (:underline (:color "#FF0000" :style wave)) help-echo "This form is deprecated (8.5)") append))
  "Create a face specification for deprecated forms, suitable for use with `font-lock-add-keywords'.")

(defmacro company-coq-dbg (format &rest args)
  "Print a message if company-coq-debug is non-nil"
  `(when company-coq-debug
     (message (concat "company-coq: " ,format) ,@args)))

(defmacro company-coq-suppress-warnings (&rest body)
  (declare (indent 0))
  (if (and (= emacs-major-version 24) (< emacs-minor-version 4))
      `(with-no-warnings ,@body)
    `(progn ,@body)))

;; FIXME: This should happen at the PG level. Introduced to fix #8.
(defmacro company-coq-with-window-start (window &rest body)
  (declare (indent defun))
  `(if ,window
       (let ((wstart (window-start ,window))
             (output (progn ,@body)))
         (when (not (equal wstart (window-start ,window)))
           (set-window-start ,window wstart))
         output)
     (progn ,@body)))

(defun company-coq-ask-prover (question &optional preserve-window-start)
  (when question
    (if (and (company-coq-prover-available) (fboundp 'proof-shell-invisible-cmd-get-result))
        (progn
          (setq company-coq-asking-question t)
          (unwind-protect
              (company-coq-with-window-start (and preserve-window-start (company-coq-get-goals-window))
                (proof-shell-invisible-cmd-get-result question))
            (setq company-coq-asking-question nil)))
      (company-coq-dbg "Prover not available; [%s] discarded" question)
      nil)))

(defun company-coq-unless-error (str)
  "Returns STR, unless STR is a message saying that a symbol is undefined, or an error."
  (and str
       (cl-loop for regexp in company-coq-error-regexps
                never (string-match-p regexp str))
       str))

(defun company-coq-ask-prover-swallow-errors (question &optional preserve-window-start)
  (company-coq-unless-error (company-coq-ask-prover question preserve-window-start)))

(defun company-coq-split-lines (str &optional omit-nulls)
  (if str (split-string str "\n" omit-nulls)))

(defun company-coq-split-wrapped-lines (str &optional omit-nulls)
  (when str
    (let ((unwrapped (replace-regexp-in-string "\n +" " " str)))
      (company-coq-split-lines unwrapped omit-nulls))))

(defun company-coq-looking-back (regexp limit)
  "A greedier version of `looking-back`"
  (save-excursion
    (save-restriction
      (narrow-to-region limit (point))
      (goto-char limit)
      (re-search-forward (concat "\\(?:" regexp "\\)\\'") nil t))))

(defun company-coq-text-width (from to)
  (interactive "r")
  ;; TODO: Is this faster? (string-width (buffer-substring (point-at-bol) (point-at-eol)))
  (- (save-excursion (goto-char to)   (current-column))
     (save-excursion (goto-char from) (current-column))))

(defun company-coq-max-line-length ()
  (save-excursion
    (goto-char (point-min))
    (cl-loop maximize (company-coq-text-width (point-at-bol) (point-at-eol))
             until (eobp) do (forward-line 1))))

(defun company-coq-truncate-buffer (start n-lines &optional ellipsis)
  (cl-assert (and n-lines (> n-lines 0)))
  (save-excursion
    (goto-char start)
    (forward-line n-lines)
    (unless (eobp)
      (delete-region (point) (point-max))
      (forward-line -1)
      (goto-char (point-at-eol))
      (insert (or ellipsis "...")))))

(defun company-coq-prefix-all-lines (prefix)
  (save-excursion
    (goto-char (point-min))
    (while (not (eobp))
      (insert prefix)
      (forward-line 1))))

(defun company-coq-insert-spacer (pos)
  (save-excursion
    (goto-char pos)
    (let* ((from  (point))
           (to    (progn (insert "\n") (point)))
           (color (or (face-attribute 'highlight :background) "black")))
      (when (fboundp 'add-face-text-property)
        (company-coq-suppress-warnings (add-face-text-property from to `(:height 1 :background ,color)))))))

(defun company-coq-get-header (str)
  (save-match-data
    (let ((header-end (and (string-match "\n\\s-*\\(\n\\|\\'\\)" str) (match-beginning 0))))
      (substring-no-properties str 0 header-end))))

(defun company-coq-boundp-string-match (regexp symbol)
  (and (boundp symbol)
       (symbol-value symbol)
       (string-match regexp (symbol-value symbol))))

(defun company-coq-boundp-equal (var symbol)
  (and (boundp var) (equal (symbol-value var) symbol)))

(defun company-coq-value-or-nil (symbol)
  (and (boundp symbol) (symbol-value symbol)))

(defun company-coq-insert-indented (lines)
  "Insert LINES into the buffer on a new line (or on the current
line if empty). Calls `indent-region' on the inserted lines."
  (save-excursion
    (unless (and (equal (point-at-bol) (skip-chars-backward " \t"))
                 (equal (point-at-eol) (skip-chars-forward " \t")))
      (newline)))
  (let ((beg (point-at-bol)))
    (mapc #'insert lines)
    (indent-region beg (point))
    (indent-according-to-mode)))

(defmacro company-coq-with-current-buffer-maybe (bufname &rest body)
  (declare (indent defun))
  `(let ((buf (get-buffer ,bufname)))
     (when buf
       (with-current-buffer buf
         ,@body))))

(defun company-coq-insert-match-in-buffer (bufname subgroup &optional prefix postprocess)
  (let ((str (match-string-no-properties subgroup)))
    (with-current-buffer (get-buffer-create bufname)
      (let ((inhibit-read-only t))
        (erase-buffer)
        (when prefix (insert prefix))
        (insert str)
        (when postprocess (funcall postprocess)))
      (current-buffer))))

(defun company-coq-extend-path (path components)
  "Contruct a path by appending each element in COMPONENTS to PATH"
  (mapc (lambda (component)
          (setq path (expand-file-name component path))) components)
  path)

(defun company-coq-chomp (l1 l2)
  "Remove the longest common prefix of l1 and l2. Returns a cons of what remains"
  ;; (message "> [%s] [%s]" l1 l2)
  (while (and l1 l2 (string-prefix-p (car l1) (car l2)))
    (setq l1 (cdr l1))
    (setq l2 (cdr l2)))
  ;; (message "< [%s] [%s]" l1 l2)
  (cons l1 l2))

(defun company-coq-split-logical-path (path)
  "Split a logical path, such as a module path, into individual components"
  (unless (string-equal path "<>")
    (split-string path "\\.")))

(defun company-coq-prover-available ()
  (and (not company-coq-asking-question)
       (proof-shell-available-p)))

(defun company-coq-force-reload-with-prover (track-symbol store-symbol load-function)
  (company-coq-dbg "company-coq-force-reload-from-prover: %s %s %s"
                   (symbol-name track-symbol) (symbol-name store-symbol) (symbol-name load-function))
  (if (not (company-coq-prover-available))
      (company-coq-dbg "company-coq-force-reload-from-prover: Reloading aborted; proof process busy")
    (set track-symbol nil)
    (set store-symbol (funcall load-function))))

(defun company-coq-init-db (db initfun)
  (company-coq-dbg "company-coq-init-db: Loading %s (if nil; currently has %s elems)" db (length (symbol-value db)))
  (or (symbol-value db)
      (funcall initfun)))

(defun company-coq-format-redirection (cmd fname)
  (format company-coq-redirection-template fname cmd))

(defun company-coq-read-and-delete (fname)
  (ignore-errors
    (let ((contents (with-temp-buffer
                      (insert-file-contents fname nil nil nil t)
                      (buffer-string))))
      (delete-file fname)
      contents)))

(defun company-coq-ask-prover-redirect (cmd)
  (when cmd
    (let* ((prefix   (expand-file-name "coq" temporary-file-directory))
           (fname    (make-temp-name prefix))
           (question (company-coq-format-redirection cmd fname))
           (answer   (company-coq-ask-prover question)))
      (company-coq-dbg "Asking coq to redirect output of [%s] to [%s]" cmd prefix)
      (cons answer (company-coq-read-and-delete (concat fname ".out"))))))

(defun company-coq-get-symbols ()
  "Load symbols by issuing command `company-coq-all-symbols-cmd' and parsing the results. Do not call if proof process is busy."
  (with-temp-message "company-coq: Loading symbols..."
    (let* ((start-time     (current-time))
           (_              (mapc #'company-coq-ask-prover company-coq-all-symbols-prelude))
           (output         (cdr (company-coq-ask-prover-redirect company-coq-all-symbols-cmd)))
           (extras         (cdr (company-coq-ask-prover-redirect company-coq-extra-symbols-cmd)))
           (_              (mapc #'company-coq-ask-prover company-coq-all-symbols-coda))
           (half-time      (current-time))
           (lines          (nconc (company-coq-split-lines output t) (company-coq-split-lines extras t)))
           (names          (company-coq-union-sort #'string-equal #'string-lessp lines)))
      (message "Loaded %d symbols (%d lines) in %.03f+%.03f seconds"
               (length names) (length lines) (float-time (time-subtract half-time start-time)) (float-time (time-since half-time)))
      names)))

(defun company-coq-get-ltacs ()
  "Load ltacs by issuing command `company-coq-all-ltacs-cmd' and parsing the results. Do not call if proof process is busy."
  (let* ((start-time     (current-time))
         (output         (cdr (company-coq-ask-prover-redirect company-coq-all-ltacs-cmd)))
         (lines          (company-coq-split-wrapped-lines output t))
         (tactics        (mapcar #'company-coq-parse-dynamic-ltacs-db-entry lines)))
    (company-coq-dbg "Loaded %d tactics in %.03f seconds"
                     (length tactics) (float-time (time-since start-time)))
    tactics))

(defun company-coq-get-all-notations ()
  "Load all tactic notations by parsing the output of
`company-coq-all-notations-cmd'. Do not call if proof process is
busy."
  (let ((output (company-coq-ask-prover-swallow-errors company-coq-all-notations-cmd)))
    (and output (company-coq-tg--extract-notations output))))

(defun company-coq-get-notations ()
  "Load tactic notations, filtering out notations listed in
`company-coq-tg--useless'. Initialization of that variable
is done at init. If this fails, the first sucessful call to this
function will set the ignore list and return nil. Do not call if
proof process is busy."
  (let ((tactics (company-coq-get-all-notations)))
    (unless company-coq-tg--useless ;; Fallback if initialization failed
      (setq company-coq-tg--useless (company-coq--list-to-table tactics)))
    (mapcar #'company-coq-parse-dynamic-notations-db-entry
            (company-coq--filter-using-table tactics company-coq-tg--useless))))

(defun company-coq-get-tactics ()
  (append (company-coq-get-ltacs) (company-coq-get-notations)))

(defun company-coq-initialize-notations-filter ()
  (setq company-coq-tg--useless (company-coq--list-to-table (company-coq-get-all-notations))))

(defun company-coq-force-reload-symbols ()
  (when company-coq--has-dynamic-completion
    (company-coq-force-reload-with-prover
     'company-coq-symbols-reload-needed 'company-coq-dynamic-symbols #'company-coq-get-symbols)))

(defun company-coq-force-reload-tactics ()
  (when company-coq--has-dynamic-completion
    (company-coq-force-reload-with-prover
     'company-coq-tactics-reload-needed 'company-coq-dynamic-tactics #'company-coq-get-tactics)))

(defun company-coq-init-symbols ()
  (company-coq-dbg "company-coq-init-symbols: Loading symbols (if never loaded)")
  (company-coq-init-db 'company-coq-dynamic-symbols 'company-coq-force-reload-symbols))

(defun company-coq-init-tactics ()
  (company-coq-dbg "company-coq-init-tactics: Loading tactics (if never loaded)")
  (company-coq-init-db 'company-coq-dynamic-tactics 'company-coq-force-reload-tactics))

(defun company-coq-init-defuns ()
  (company-coq-dbg "company-coq-init-defuns: Loading symbols from buffer")
  (company-coq-reload-buffer-defuns))

(defun company-coq-find-all (re beg end)
  (when (< beg end) ;; point-at-bol may be before unproc-beg
    (let ((case-fold-search nil)
          (matches          nil))
      (save-excursion
        (goto-char beg)
        (while (search-forward-regexp re end t)
          (push (match-string-no-properties 2) matches)))
      matches)))

(defun company-coq-reload-buffer-defuns ()
  (interactive) ;; FIXME should timeout after some time, and should accumulate search results
  (let* ((unproc-beg (proof-unprocessed-begin)))
    (setq company-coq-buffer-defuns
          (if (and company-coq--has-dynamic-completion company-coq-dynamic-autocompletion)
              (company-coq-find-all company-coq-defuns-regexp unproc-beg (point-at-bol))
            (company-coq-find-all company-coq-defuns-regexp (point-min) (point-at-bol))))))

(defun company-coq-line-is-import-p ()
  (save-excursion ;; FIXME Multi line imports
    (let* ((limit         (point))
           (bol           (point-at-bol))
           (command-begin (or (search-backward ". " bol t) bol)))
      (goto-char command-begin)
      (re-search-forward company-coq-import-regexp limit t))))

(defun company-coq-line-is-block-end-p ()
  (company-coq-looking-back company-coq-block-end-regexp (point-at-bol)))

(defun company-coq-parse-path-specs (loadpath-output)
  "Parse output of `company-coq-modules-cmd'. Output is a list of
pairs of paths in the form (LOGICAL . PHYSICAL)"
  (when loadpath-output
    (save-match-data
      (cdr-safe (cl-loop for     line
                         in      (company-coq-split-wrapped-lines loadpath-output)
                         if      (string-match company-coq-path-regexp line)
                         collect (cons (match-string 1 line) (match-string 2 line)))))))

(defun company-coq-get-path-specs ()
  "Load modules by issuing command company-coq-modules-cmd and parsing the results. Do not call if proof process is busy."
  (interactive)
  (let* ((time       (current-time))
         (output     (company-coq-ask-prover-swallow-errors company-coq-modules-cmd))
         (path-specs (company-coq-parse-path-specs output)))
    (company-coq-dbg "Loaded %d modules paths (%.03f seconds)" (length path-specs) (float-time (time-since time)))
    path-specs))

(defun company-coq-force-reload-modules ()
  (interactive)
  (company-coq-force-reload-with-prover 'company-coq-modules-reload-needed
                                        'company-coq-known-path-specs
                                        #'company-coq-get-path-specs))

(defun company-coq-init-modules ()
  (interactive)
  (company-coq-dbg "company-coq-init-modules: Loading modules (if never loaded)")
  (company-coq-init-db 'company-coq-known-path-specs 'company-coq-force-reload-modules))

(defun company-coq-get-pg-keywords-db ()
  (apply #'append
         (mapcar #'company-coq-value-or-nil ;; Don't fail when PG is missing
                 '(coq-tactics-db coq-solve-tactics-db coq-solve-cheat-tactics-db coq-tacticals-db coq-commands-db))))

(defun company-coq-get-man-keywords-db ()
  company-coq-abbrevs)

(defun company-coq-normalize-abbrev (kwd)
  (downcase
   (replace-regexp-in-string
    "[ .]+\\'" ""
    (replace-regexp-in-string
     (concat " *\\(" company-coq-placeholder-regexp "\\) *") "#"
     kwd))))

(defun company-coq-parse-keywords-pg-entry (menuname _abbrev insert &optional _statech _kwreg insert-fun _hide)
  (when (or (and insert (not (string-match-p company-coq-disabled-patterns-regexp insert)))
            (and (not insert) insert-fun))
    (propertize (if insert-fun menuname insert)
                'source 'pg
                'insert insert
                'insert-fun insert-fun
                'stripped (company-coq-normalize-abbrev insert)))) ;; TODO: Remove inter-word spaces

(defun company-coq-parse-man-db-entry (abbrev-and-anchor)
  (let ((abbrev (car abbrev-and-anchor))
        (anchor (cdr abbrev-and-anchor)))
    (propertize abbrev
                'source 'man
                'anchor anchor
                'insert abbrev
                'stripped (company-coq-normalize-abbrev abbrev))))

(defun company-coq-parse-dynamic-ltacs-db-entry (line)
  "Prepare a proper completion entry from one line of output of
`company-coq-all-ltacs-cmd'."
  (let ((abbrev (replace-regexp-in-string " \\(\\S-+\\)" " @{\\1}" line)))
    (propertize abbrev
                'source 'ltac 'insert abbrev
                'stripped (company-coq-normalize-abbrev abbrev))))

;; TODO this should be in tg
(defun company-coq-parse-dynamic-notations-db-entry (tactic)
  "Annotate a tactic notation'."
  (propertize tactic
              'source 'tacn 'insert tactic
              'stripped (company-coq-normalize-abbrev tactic)))

(defun company-coq-parse-custom-db-entry (abbrev)
  (propertize abbrev
              'source 'custom
              'insert abbrev
              'stripped (company-coq-normalize-abbrev abbrev)))

(defun company-coq-abbrev-equal (a1 a2)
  (and (equal (company-coq-read-normalized-abbrev a1)
              (company-coq-read-normalized-abbrev a2))
       (not (equal (company-coq-read-abbrev-source a1)
                   (company-coq-read-abbrev-source a2)))))

(defun company-coq-read-normalized-abbrev (kwd)
  (get-text-property 0 'stripped kwd))

(defun company-coq-read-abbrev-source (kwd)
  (get-text-property 0 'source kwd))

(defun company-coq-union-nosort (test comp key &rest lists)
  (let ((merged  (cl-stable-sort (apply #'append lists) comp :key key))
        (prev    nil))
    (while merged
      (let ((top (pop merged)))
        (when (and prev (funcall test top prev))
          (put-text-property 0 (length top) 'dup t top))
        (setq prev top)))
    (cl-loop for abbrev in (apply #'append lists)
             if (not (get-text-property 0 'dup abbrev))
             collect abbrev)))

(defun company-coq-union-sort (test comp &rest lists)
  (let ((merged  (cl-stable-sort (apply #'append lists) comp))
        (deduped nil)
        (prev    nil))
    (while merged
      (let ((top (pop merged)))
        (unless (and prev (funcall test top prev))
          (push top deduped))
        (setq prev top)))
    deduped))

(defun company-coq-sorted-intersection (l1 l2)
  (let ((inter nil))
    (while (and l1 l2)
      (cond
       ((string< (car l1) (car l2)) (pop l1))
       ((string< (car l2) (car l1)) (pop l2))
       ((string= (car l1) (car l2))
        (push (car l1) inter)
        (pop l1) (pop l2))))
    inter))

(defun company-coq-number (ls)
  (let ((num 0))
    (mapc (lambda (x)
            (put-text-property 0 (length x) 'num num x)
            (setq num (+ 1 num)))
          ls)))

(defun company-coq-get-annotated-keywords ()
  (company-coq-dbg "company-coq-get-annotated-keywords: Called")
  (let ((pg-keywords     (remove nil (mapcar (lambda (db-entry)
                                               (apply 'company-coq-parse-keywords-pg-entry db-entry))
                                             (company-coq-get-pg-keywords-db))))
        (man-keywords    (company-coq-number
                          (mapcar #'company-coq-parse-man-db-entry (company-coq-get-man-keywords-db))))
        (custom-keywords (mapcar #'company-coq-parse-custom-db-entry company-coq-custom-snippets)))
    (company-coq-union-nosort
     #'company-coq-abbrev-equal #'string-lessp #'company-coq-read-normalized-abbrev
     custom-keywords man-keywords pg-keywords)))

(defun company-coq-force-reload-keywords ()
  (company-coq-dbg "company-coq-force-reload-keywords: Called")
  (setq company-coq-known-keywords (company-coq-get-annotated-keywords))
  (company-coq-dbg "company-coq-force-reload-keywords: Loaded %s symbols" (length company-coq-known-keywords)))

(defun company-coq-init-keywords ()
  (interactive)
  (company-coq-dbg "company-coq-init-keywords: Loading keywords (if never loaded)")
  (company-coq-init-db 'company-coq-known-keywords 'company-coq-force-reload-keywords))

(defun company-coq-is-lower (str)
  (let ((case-fold-search nil))
    (string-match-p "\\`[[:lower:]]" str)))

(defun company-coq-string-lessp-foldcase (str1 str2)
  (string-lessp (upcase str1) (upcase str2)))

(defmacro company-coq-bool-lessp-fallback (a1 a2 fallback-t &optional fallback-nil)
  (declare (indent defun))
  `(let ((a1 ,a1)
         (a2 ,a2))
     (or (and      a1  (not a2))
         (and      a1       a2  ,fallback-t)
         (and (not a1) (not a2) ,(or fallback-nil fallback-t)))))

(defmacro company-coq-attr-lessp (symbol str1 str2 extraction cmp fallback-t &optional fallback-nil)
  (declare (indent defun))
  `(let ((a1 (,extraction ,cmp (get-text-property 0 ,symbol ,str1)))
         (a2 (,extraction ,cmp (get-text-property 0 ,symbol ,str2))))
     (company-coq-bool-lessp-fallback a1 a2
       ,fallback-t ,fallback-nil)))

(defun company-coq-string-lessp-match-beginning (str1 str2)
  (company-coq-attr-lessp 'match-beginning str1 str2 eq 0
    (company-coq-string-lessp-foldcase str1 str2)))

(defun company-coq-string-lessp-keywords (str1 str2)
  ;; Rank 'custom first (before 'man)
  (company-coq-attr-lessp 'source str1 str2 eq 'custom
    ;; Rank lowercase (tactics) before uppercase (vernacs)
    (company-coq-bool-lessp-fallback (company-coq-is-lower str1) (company-coq-is-lower str2)
      ;; If both are lowercase (tactics)
      (company-coq-attr-lessp 'num str1 str2 or nil
        ;; If both have a number, preserve the original manual order
        (< a1 a2)
        ;; Otherwise rank alphabetically (eg two PG tactics)
        (company-coq-string-lessp-foldcase str1 str2))
      ;; If both are uppercase (vernacs)
      (if (and (company-coq-get-anchor str1)
               (equal (company-coq-get-anchor str1) (company-coq-get-anchor str2)))
          ;; If both have the same non-nil anchor, sort in original order
          (< (get-text-property 0 'num str1) (get-text-property 0 'num str2))
        ;; Otherwise sort alphabetically
        (company-coq-string-lessp-foldcase str1 str2)))))

(defun company-coq-propertize-match (match beginning end)
  (company-coq-dbg "company-coq-propertize-match: %s %s %s" match beginning end)
  (put-text-property 0 (length match) 'match-beginning beginning match)
  (put-text-property 0 (length match) 'match-end end match)
  match)

(defun company-coq-complete-prefix-substring (prefix completions &optional ignore-case)
  "List elements of COMPLETIONS containing with PREFIX"
  (let ((completion-ignore-case ignore-case)
        (case-fold-search       ignore-case)
        (prefix-re              (regexp-quote prefix)))
    (cl-loop for completion in completions
             if (string-match prefix-re completion)
             collect (company-coq-propertize-match completion (match-beginning 0) (match-end 0)))))

;; (defun company-coq-complete-prefix (prefix completions &optional ignore-case)
;;   "List elements of COMPLETIONS starting with PREFIX"
;;   (company-coq-dbg "company-coq-complete-prefix: Completing for prefix %s (%s symbols)" prefix (length completions))
;;   (let ((completion-ignore-case ignore-case)
;;         (prefix-len             (length prefix)))
;;     (mapcar
;;      (lambda (completion) (company-coq-propertize-match completion 0 prefix-len))
;;      (all-completions prefix completions))))

(defun company-coq-complete-sub-re (prefix candidates)
  (let* ((chars (string-to-list prefix)) ;; The regexp says: skip stuff before beginning a new word, or skip nothing
         (re    (concat "\\`\\W*" (mapconcat (lambda (c) (regexp-quote (char-to-string c))) chars "\\(\\|.+?\\_<\\)")))
         (case-fold-search nil))
    (save-match-data
      (cl-loop for     candidate
               in      candidates
               when    (string-match re candidate)
               collect (company-coq-propertize-match candidate 0 (match-end 0))))))

(defun company-coq-match-logical-paths (module-atoms path-atoms)
  "Produces a cons (QUALID-ATOMS SEARCH-ATOMS LEFT-PTH) from a
module path and a logical path. This function distinguishes three
cases:

1. The logical path is longer; in this case, the qualifier is the
   full logical path, and the search term is empty.

2. The module path is longer; in this case, the qualifier is the
   full logical path, plus what remains of the module path (minus
   the last item of the module path), and the search term is the
   last item of the module path.

3. The two paths don't match; in this case, there is no qualifier
   nor search term."
  (pcase (company-coq-chomp module-atoms path-atoms)
    (`(,mod .  nil) (let ((subdirectory-atoms (butlast mod)))
                      (unless (member "" subdirectory-atoms) ;; We don't support skipping over subdirectories
                        (cons (append path-atoms subdirectory-atoms) (cons mod nil)))))
    (`(nil  . ,pth) (cons path-atoms (cons nil pth)))
    (_              nil)))

(defun company-coq-complete-module-unqualified (search-path search-regexp)
  "Find module names matching SEARCH-REGEXP in SEARCH-PATH.
Results are file names only, and do not include the .v[i]o
extension." ;; TODO format directories properly
  (when (file-exists-p search-path)
    (cl-loop for file in (directory-files search-path nil nil t)
             if      (or (not search-regexp) (string-match-p search-regexp file))
             if      (string-match-p company-coq-compiled-regexp file)
             collect (replace-regexp-in-string company-coq-compiled-regexp "" file)
             else if (and (not (string-match-p "\\." file)) (file-directory-p (expand-file-name file search-path)))
             collect (concat file "."))))

(defun company-coq-take-summed-lengths (ls count)
  (cl-loop for i = 0 then (+ 1 i)
           for l = ls then (cdr l)
           while (< i count)
           sum (length (car-safe l))))

(defun company-coq-qualify-module-names (mod-names qualid-atoms fully-matched-count part-matched-len physical-path)
  "Qualify each name in MOD-NAMES using QUALID-ATOMS."
  (when mod-names
    (let* ((qualid     (mapconcat 'identity qualid-atoms "."))
           (prefix     (if qualid-atoms (concat qualid ".") ""))
           (m-pref-len (company-coq-take-summed-lengths qualid-atoms fully-matched-count))
           (match-end  (+ m-pref-len ;; fully matched prefix
                          part-matched-len ;; partially matched element (end of search term)
                          fully-matched-count))) ;; dots
      (mapcar (lambda (mod-name)
                (propertize (concat prefix mod-name)
                            'meta      (concat physical-path " -> " mod-name)
                            'location  (expand-file-name (concat mod-name ".v") physical-path)
                            'match-end match-end))
              mod-names))))

(defun company-coq-complete-module-qualified
    (qualid-atoms search-atoms physical-path fully-matched-count part-matched-len)
  "Find qualified module names in PHYSICAL-PATH that match SEARCH-ATOMS."
  ;; (message "> [%s] [%s] [%s]" (prin1-to-string qualid-atoms) (prin1-to-string search-atoms) physical-path)
  (let* ((kwd           (car-safe (last search-atoms)))
         (nil-kwd       (or (not kwd) (equal kwd "")))
         (ext-path      (company-coq-extend-path physical-path search-atoms))
         (search-path   (if nil-kwd (file-name-as-directory ext-path)
                          (file-name-directory ext-path)))
         (search-regexp (if nil-kwd nil (concat "\\`" (regexp-quote kwd))))
         (mod-names     (company-coq-complete-module-unqualified
                         search-path search-regexp)))
    ;; (message "Searching in [%s] with regexp [%s]: [%s]" search-path search-regexp mod-names)
    (company-coq-qualify-module-names mod-names qualid-atoms fully-matched-count part-matched-len search-path)))

(defun company-coq-complete-module-from-atoms (module-atoms path-atoms physical-path)
  "Wrapper around company-coq-complete-module-qualified."
  (pcase (company-coq-match-logical-paths module-atoms path-atoms)
    (`(,qualid . (,search . ,pth))
     (let* (;; Fully matched count is the full qualid if the search term
            ;; (module-atoms) was strictly longer than the path, and otherwise
            ;; one less than the number of elements in common
            (fully-matched-count (if (eq search nil)
                                     (- (length path-atoms) (length pth) 1)
                                   (length qualid)))
            ;; Part matched len is always the length of the last search term
            (part-matched-len    (length (car-safe (last module-atoms)))))
       (company-coq-complete-module-qualified qualid search physical-path fully-matched-count part-matched-len)))))

(defun company-coq-complete-module-from-path-spec (module-atoms path-spec)
  "Find modules matching MODULE-ATOMS in PATH-SPEC.
This essentially attempts to match MODULE-ATOMS to the logical
path in PATH-SPEC, and for each matching position computes a
search term and a qualifier."
  (cl-destructuring-bind (logical-path . physical-path) path-spec
    (let* ((path-atoms   (company-coq-split-logical-path logical-path))
           (completions  (list (company-coq-complete-module-from-atoms module-atoms nil physical-path))))
      (while path-atoms
        (push (company-coq-complete-module-from-atoms
               module-atoms path-atoms physical-path)
              completions)
        (setq path-atoms (cdr path-atoms)))
      (apply #'append completions))))

(defun company-coq-complete-modules (module)
  (when module
    (let ((module-atoms (company-coq-split-logical-path module))
          (completions nil))
      (mapc (lambda (path-spec)
              (push (company-coq-complete-module-from-path-spec
                     module-atoms path-spec)
                    completions))
            company-coq-known-path-specs)
      (apply #'company-coq-union-sort
             #'string-equal #'string-lessp completions))))

(defun company-coq-shell-output-is-end-of-def ()
  "Checks whether the output of the last command matches company-coq-end-of-def-regexp"
  (company-coq-boundp-string-match company-coq-end-of-def-regexp 'proof-shell-last-output))

(defun company-coq-shell-output-is-end-of-proof ()
  "Checks whether proof-general signaled a finished proof"
  (company-coq-value-or-nil 'proof-shell-proof-completed))

(defun company-coq-shell-output-is-error ()
  "Checks whether proof-general signaled an error"
  (company-coq-boundp-string-match company-coq-error-regexp 'proof-shell-last-output))

(defun company-coq-detect-capabilities ()
  (let* ((output     (car (company-coq-ask-prover-redirect company-coq-capability-test-cmd)))
         (capability (company-coq-unless-error output)))
    (when output
      (setq company-coq-needs-capability-detection nil)
      (setq company-coq--has-dynamic-completion (and capability company-coq-dynamic-autocompletion))
      (when company-coq-dynamic-autocompletion
        (message "Capability detection complete: dynamic completion is %savailable." (if capability "" "not "))
        (when (not capability)
          (warn (concat "`company-coq-dynamic-autocompletion' is non-nil, but "
                        "your version of coqtop does not seem to support symbols completion. "
                        "Falling back to same-buffer completion.")))))))

(defun company-coq-maybe-reload-each ()
  (company-coq-dbg "company-coq-maybe-reload-each: [%s] [%s] [%s]"
                   company-coq-needs-capability-detection
                   company-coq-symbols-reload-needed
                   company-coq-modules-reload-needed)
  (when (company-coq-prover-available)
    (when company-coq-needs-capability-detection (company-coq-detect-capabilities))
    (when company-coq-tactics-reload-needed (company-coq-force-reload-tactics))
    (when company-coq-symbols-reload-needed (company-coq-force-reload-symbols))
    (when company-coq-modules-reload-needed (company-coq-force-reload-modules))))

(defmacro company-coq-remember-hyp (hyp-cons context)
  `(cl-destructuring-bind (name . type-lines) ,hyp-cons
     (when (and name type-lines)
       ;; (message "New hyp: [%s . [%s]]" name type-lines)
       (let ((type (mapconcat #'company-coq-trim (nreverse type-lines) " ")))
         (push (propertize name 'meta type) ,context)))))

(defun company-coq-extract-context (goal-lines)
  ;; FIXME: This does not properly deal with "a, b: nat", which was introduced in 8.5
  ;; It doesn't matter too much though, because 8.5 lists hypotheses in search results.
  (cl-loop for     line
           in      goal-lines
           with    context  = nil
           with    current-hyp = `(nil . nil)
           while   (not (string-match-p company-coq-goal-separator-line-regexp line))
           if      (string-match company-coq-goals-hyp-regexp line)
           do      (company-coq-remember-hyp current-hyp context)
           and do  (setq current-hyp `(,(match-string 1 line) . ,(list (match-string 2 line))))
           else do (push line (cdr current-hyp))
           finally (company-coq-remember-hyp current-hyp context)
           finally return context))

(defun company-coq-extract-goal (goal-lines)
  (while (and goal-lines (not (string-match-p company-coq-goal-separator-line-regexp (car goal-lines))))
    (pop goal-lines))
  (cl-loop for     line
           in      (cdr-safe goal-lines)
           while   (string-match-p company-coq-goal-lines-regexp line)
           collect line))

(defun company-coq-run-and-parse-context (command)
  (-if-let* ((output (company-coq-ask-prover-swallow-errors command)))
      (let* ((lines   (company-coq-split-lines output))
             (context (company-coq-extract-context lines))
             (goal    (company-coq-extract-goal lines)))
        (cons context goal))
    (error (format "company-coq-parse-context: failed with message %s" output))))

(defun company-coq-maybe-reload-context (&optional end-of-proof)
  "Updates company-coq-current-context."
  (company-coq-dbg "company-coq-maybe-reload-context: Called")
  (let* ((output        (company-coq-value-or-nil 'proof-shell-last-goals-output))
         (is-new-output (not (string-equal output company-coq-last-goals-output))))
    (cond (end-of-proof  (company-coq-dbg "company-coq-maybe-reload-context: Clearing context")
                         (setq company-coq-current-context nil)
                         (setq output nil))
          (is-new-output (company-coq-dbg "company-coq-maybe-reload-context: Reloading context")
                         (setq company-coq-current-context (company-coq-extract-context
                                                            (company-coq-split-lines output)))))
    (setq company-coq-last-goals-output output)))

(defun company-coq-maybe-proof-output-reload-things ()
  "Updates `company-coq-tactics-reload-needed' and
`company-coq-symbols-reload-needed' if a proof just completed or
if output mentions new symbol, then calls
`company-coq-maybe-reload-each'. Also calls
`company-coq-maybe-reload-context'."
  (interactive)
  (company-coq-dbg "company-coq-maybe-proof-output-reload-things: Called")
  (unless company-coq-asking-question
    (let ((is-error         (company-coq-shell-output-is-error))
          (is-end-of-def    (company-coq-shell-output-is-end-of-def))
          (is-end-of-proof  (company-coq-shell-output-is-end-of-proof)))
      (when is-end-of-proof (company-coq-dbg "company-coq-maybe-proof-output-reload-things: At end of proof"))
      (when is-end-of-def   (company-coq-dbg "company-coq-maybe-proof-output-reload-things: At end of definition"))
      (setq company-coq-symbols-reload-needed (or company-coq-symbols-reload-needed is-end-of-def is-end-of-proof))
      (setq company-coq-tactics-reload-needed (or company-coq-tactics-reload-needed is-end-of-def))
      (company-coq-maybe-reload-context (or is-end-of-def is-end-of-proof))
      (if is-error (company-coq-dbg "Last output was an error; not reloading")
        ;; Delay call until after we have returned to the command loop
        (company-coq-dbg "This could be a good time to reload things?")
        (run-with-timer 0 nil #'company-coq-maybe-reload-each)))))

(defun company-coq-maybe-proof-input-reload-things ()
  "Reload symbols if input mentions new symbols"
  (interactive)
  (company-coq-dbg "company-coq-maybe-proof-input-reload-things: Called")
  (unless company-coq-asking-question
    (let* ((is-advancing  (company-coq-boundp-equal 'action 'proof-done-advancing))
           (is-retracting (company-coq-boundp-equal 'action 'proof-done-retracting))
           (is-tac-not    (and is-advancing (company-coq-boundp-string-match company-coq-tac-notation-regexp 'string)))
           (is-import     (and is-advancing (company-coq-boundp-string-match company-coq-import-regexp 'string)))
           (is-load       (and is-advancing (company-coq-boundp-string-match company-coq-load-regexp   'string))))
      (when is-retracting (company-coq-dbg "company-coq-maybe-proof-input-reload-things: Rewinding"))
      (when is-import     (company-coq-dbg "company-coq-maybe-proof-input-reload-things: New import"))
      (when is-load       (company-coq-dbg "company-coq-maybe-proof-input-reload-things: Touching load path"))
      (setq company-coq-symbols-reload-needed (or company-coq-symbols-reload-needed is-import)) ;; is-retracting
      (setq company-coq-tactics-reload-needed (or company-coq-tactics-reload-needed is-import is-tac-not))
      (setq company-coq-modules-reload-needed (or company-coq-modules-reload-needed is-import is-load))
      (when is-retracting (company-coq-maybe-reload-context t)))))

(defvar company-coq-goals-window nil)

(defun company-coq-state-change (&rest _args)
  (unless (window-live-p company-coq-goals-window)
    (setq company-coq-goals-window (company-coq-get-goals-window)))

  ;; Hide the docs and redisplay the goals buffer
  (-when-let* ((doc-buf   (get-buffer "*company-documentation*")))
    (bury-buffer doc-buf))
  (-when-let* ((goals-buf (company-coq-get-goals-buffer))
               (goals-win (company-coq-get-goals-window)))
    (set-window-buffer goals-win goals-buf)))

(defun company-coq-coq-mode-p ()
  (derived-mode-p 'coq-mode))

(defun company-coq-grab-prefix ()
  ;; Only one grab function; otherwise the first backend in the list of backend shadows the others
  ;; FIXME: Should not return nil at the beginning of a hole
  (unless (and (char-after) (memq (char-syntax (char-after)) '(?w ?_)))
    (save-excursion ;; TODO could be optimized
      (when (company-coq-looking-back company-coq-prefix-regexp (point-at-bol))
        (match-string-no-properties 0)))))

(defun company-coq-symbol-at-point-with-pos () ;; FIXME could use (coq-id-or-notation-at-point)
  (let* ((start  (and (company-coq-looking-back company-coq-prefix-regexp (point-at-bol))
                      (match-beginning 0)))
         (symbol (and start (save-excursion
                              (goto-char start)
                              (when (looking-at company-coq-symbol-regexp)
                                (match-string-no-properties 0))))))
    (and symbol (cons symbol start))))

(defun company-coq-symbol-at-point ()
  (car-safe (company-coq-symbol-at-point-with-pos)))

(defun company-coq-prefix-simple ()
  (interactive)
  (company-coq-dbg "company-coq-prefix-simple: Called")
  (when (company-coq-coq-mode-p)
    (company-coq-grab-prefix)))

(defun company-coq-trim (str)
  (replace-regexp-in-string "\\` *" "" (replace-regexp-in-string " *\\'" "" str)))

(defun company-coq-truncate-to-minibuf (str)
  (when str
    (let* ((minibuf-w  (window-body-width (minibuffer-window))))
      (if (> (length str) minibuf-w)
          (concat (substring str 0 (- minibuf-w 3)) "...")
        str))))

(defun company-coq-meta-symbol (name)
  (company-coq-dbg "company-coq-meta-symbol: Called for name %s" name)
  (-when-let* ((output (company-coq-ask-prover-swallow-errors
                        (format company-coq-symbols-meta-cmd name))))
    (company-coq-truncate-to-minibuf
     (replace-regexp-in-string "\\s-+" " " (company-coq-trim output)))))

(defun company-coq-meta-keyword (name)
  (company-coq-dbg "company-coq-meta-keyword: Called for name %s" name)
  (and (company-coq-get-anchor name) ;; substitute-command-keys doesn't work here
       "C-h: Quick docs. C-w: Full docs (scrollable)."))

(defun company-coq-meta-simple (name)
  (company-coq-dbg "company-coq-meta-simple: Called for name %s" name)
  (company-coq-truncate-to-minibuf
   (get-text-property 0 'meta name)))

(defun company-coq-get-goals-buffer ()
  (get-buffer "*goals*"))

(defun company-coq-get-goals-window ()
  (let ((pg-buffer (company-coq-get-goals-buffer)))
    (or (and pg-buffer (get-buffer-window pg-buffer))
        (and (window-live-p company-coq-goals-window) company-coq-goals-window))))

(defun company-coq-display-in-pg-window (buffer alist)
  ;; This always displays the buffer, unless no window is available.  This was
  ;; important, because if the window is not displayed upon calling
  ;; shr-insert-document, then shr would get the window width incorrectly, and
  ;; thus fail to wrap text properly. Setting the wrap limit to a large value
  ;; fixes this, except when it yields an out of memory exception (eg. for the
  ;; mutually co-inductive records error documentation)
  (company-coq-dbg "Called company-coq-display-in-pg-buffer with %s %s" buffer alist)
  (-if-let* ((pg-window (company-coq-get-goals-window)))
      (progn (set-window-dedicated-p pg-window nil)
             (set-window-buffer pg-window buffer)
             pg-window)
    (display-buffer buffer)))

(defmacro company-coq-with-clean-doc-buffer (&rest body)
  (declare (indent defun)
           (debug body))
  `(progn
     (company-coq-dbg "company-prepare-doc-buffer: Called") ;; TODO the buffer could have a different name
     (let ((doc-buffer (get-buffer-create "*company-documentation*")))
       (with-selected-window (company-coq-display-in-pg-window doc-buffer nil)
         (with-current-buffer doc-buffer
           (let ((inhibit-read-only t))
             (help-mode)
             (erase-buffer)
             (remove-overlays)
             (buffer-disable-undo)
             (visual-line-mode 1)
             (set (make-local-variable 'show-trailing-whitespace) nil)
             ,@body))))))

(defun company-coq-setup-temp-coq-buffer ()
  (coq-mode)
  (company-coq-initialize)
  (set-buffer-modified-p nil)
  (set (make-local-variable 'buffer-offer-save) nil))

(defun company-coq-search-then-scroll-up (target)
  "Finds a definition, then returns a nice point to scroll to,
before that definition. This could be two lines higher or, if that's
inside a comment, at the beginning of the comment."
  (save-excursion
    (or (and target
             (goto-char (point-min))
             (re-search-forward target nil t)
             (progn
               (company-coq-make-title-line 'company-coq-doc-header-face-source t)
               (forward-line -2)
               (or (and (functionp 'coq-looking-at-comment)
                        (company-coq-suppress-warnings (coq-looking-at-comment))
                        (functionp 'coq-get-comment-region)
                        (car (company-coq-suppress-warnings (coq-get-comment-region (point)))))
                   (point))))
        0)))

(defun company-coq-location-simple (name &optional target interactive)
  (company-coq-dbg "company-coq-location-simple: Called for name %s" name)
  (let* ((fname-or-buffer (get-text-property 0 'location name))
         (is-buffer       (and fname-or-buffer (bufferp fname-or-buffer)))
         (is-fname        (and fname-or-buffer (stringp fname-or-buffer) (file-exists-p fname-or-buffer))))
    (if (or is-buffer is-fname)
        (company-coq-with-clean-doc-buffer
          (cond (is-buffer (insert-buffer-substring fname-or-buffer))
                (is-fname  (insert-file-contents fname-or-buffer nil nil nil t)))
          (company-coq-setup-temp-coq-buffer)
          (cons (current-buffer)
                (set-window-start nil (goto-char (company-coq-search-then-scroll-up target)))))
      (when interactive
        (error "No location found for %s" name)))))

(defun company-coq-longest-matching-path-spec (qname)
  "Finds the longest matching logical name, and returns the
corresponding (logical name . real name) pair."
  (cl-loop for     (logical . real)
           in      company-coq-known-path-specs
           with    longest = nil
           when    (string-match-p (concat "\\`" (regexp-quote logical) "\\.") qname)
           do      (when (> (length logical) (length (car longest)))
                     (setq longest (cons logical real)))
           finally return longest))

(defun company-coq-fully-qualified-name-simple (name cmd)
  (-when-let* ((output (company-coq-ask-prover-swallow-errors (format cmd name))))
    (save-match-data
      (when (string-match company-coq-locate-output-format output)
        (match-string-no-properties 1 output)))))

(defun company-coq-fully-qualified-name (name cmds)
  "Finds the fully qualified name of NAME, successively issuing
commands in CMD until one of the returns proper output. When CMDS
is nil, both of `company-coq-locate-tactic-cmd' and
`company-coq-locate-symbols-cmd'"
  (cl-loop for cmd in cmds
           thereis (company-coq-fully-qualified-name-simple name cmd)))

(defun company-coq-library-path (lib-path mod-name fallback-spec)
  "Gets the path of a .v file likely to hold the definition
of (concat LIB-PATH MOD-NAME), or a buffer visiting that
file. FALLBACK-SPEC is a module path specification to be used if
[Locate Library] points to a non-existent file (for an example of
                                                    such a case, try [Locate Library Peano] in 8.4pl3)."
  (if (and (equal lib-path "") (equal mod-name "Top"))
      (current-buffer)
    (let* ((lib-name (concat lib-path mod-name))
           (output   (company-coq-ask-prover (format company-coq-locate-lib-cmd lib-name))))
      (or (and output (save-match-data
                        (when (string-match company-coq-locate-lib-output-format output)
                          (replace-regexp-in-string "\\.vi?o\\'" ".v" (match-string-no-properties 2 output)))))
          (and fallback-spec (expand-file-name (concat mod-name ".v") (cdr fallback-spec)))))))

(defun company-coq-location-source (name locate-cmds &optional interactive)
  "Shows the definition of NAME in its surrounding source
context. LOCATE-CMDS is a list of queries to use to guess the
fully qualified name of NAME."
  (company-coq-dbg "company-coq-location-source: Called for [%s]" name)
  (-if-let* ((qname (company-coq-fully-qualified-name name locate-cmds)))
      (let* ((spec       (company-coq-longest-matching-path-spec qname))
             (logical    (if spec (concat (car spec) ".") ""))
             (short-name (replace-regexp-in-string "\\`.*\\." "" qname))
             (mod-name   (replace-regexp-in-string "\\..*\\'" "" qname nil nil nil (length logical)))
             (fname      (company-coq-library-path logical mod-name spec))
             (target     (concat (company-coq-make-headers-regexp company-coq-named-outline-kwds)
                                 "\\s-*" (regexp-quote short-name) "\\_>")))
        (company-coq-location-simple (propertize name 'location fname) target interactive))
    (when interactive (error "No location found for %s" name))))

(defvar company-coq-location-history nil
  "Keeps track of manual location queries")

(defun company-coq-location-interact (dynamic-pool)
  (let ((completions (apply #'append
                            (and company-coq-autocomplete-symbols (company-coq-init-defuns))
                            (and company-coq--has-dynamic-completion dynamic-pool))))
    (list (completing-read "Name to find sources for? " completions
                           (lambda (choice) (not (eq (get-text-property 0 'source choice) 'tacn)))
                           nil nil 'company-coq-location-history (company-coq-symbol-at-point) t)
          t)))

(defun company-coq-location-symbol (name &optional interactive)
  (interactive (company-coq-location-interact (list company-coq-dynamic-symbols)))
  (company-coq-location-source name (list company-coq-locate-symbol-cmd) interactive))

(defun company-coq-location-tactic (name &optional interactive)
  (interactive (company-coq-location-interact (list company-coq-dynamic-tactics)))
  (setq name (replace-regexp-in-string " .*" "" name))
  (company-coq-location-source name (list company-coq-locate-tactic-cmd) interactive))

(defun company-coq-location-defun (name &optional interactive)
  (interactive (company-coq-location-interact (list company-coq-dynamic-symbols company-coq-dynamic-tactics)))
  (company-coq-location-source name (list company-coq-locate-symbol-cmd
                                          company-coq-locate-tactic-cmd)
                               interactive))

(defun company-coq-make-title-line (face &optional skip-space)
  (let* ((start   (save-excursion (goto-char (point-at-bol))
                                  (if skip-space (skip-chars-forward " \t"))
                                  (point)))
         (end     (1+ (point-at-eol))) ;; +1 to cover the full line
         (overlay (make-overlay start end)))
    (overlay-put overlay 'face face)))

(defun company-coq-get-anchor (kwd)
  (get-text-property 0 'anchor kwd))

(defun company-coq-count-holes (snippet)
  (let* ((count   0)
         (counter (lambda (_) (setq count (+ 1 count)) ""))
         (_       (replace-regexp-in-string company-coq-placeholder-regexp counter snippet)))
    count))

(defun company-coq-annotation-keywords (candidate)
  (let* ((snippet   (company-coq-get-snippet candidate))
         (num-holes (and snippet (company-coq-count-holes snippet)))
         (prefix    (if (company-coq-get-anchor candidate) "..." "")))
    (if (and (numberp num-holes) (> num-holes 0))
        (format "%s<kwd (%d)>" prefix num-holes)
      (format "%s<kwd>" prefix))))

(defun company-coq-annotation-context (_)
  "<h>")

(defun company-coq-annotation-tactic (arg)
  (concat "<" (or (symbol-name (get-text-property 0 'source arg)) "") ">"))

(defun company-coq-doc-buffer-collect-outputs (name templates &optional fallbacks)
  (or (cl-loop for template in templates
               for cmd = (format template name)
               for output = (company-coq-ask-prover-swallow-errors cmd)
               when output collect output)
      (and fallbacks (company-coq-doc-buffer-collect-outputs name fallbacks))))

(defun company-coq-doc-buffer-generic (name cmds)
  (company-coq-dbg "company-coq-doc-buffer-generic: Called for name %s" name)
  (-when-let* ((chapters (company-coq-doc-buffer-collect-outputs name cmds)))
    (let* ((fontized-name (propertize name 'font-lock-face 'company-coq-doc-i-face))
           (doc-tagline   (format company-coq-doc-tagline fontized-name))
           (doc-body      (mapconcat #'identity chapters company-coq-doc-def-sep))
           (doc-full      (concat doc-tagline "\n\n" doc-body)))
      (company-coq-with-clean-doc-buffer
        (insert doc-full)
        (when (fboundp 'coq-response-mode)
          (coq-response-mode))
        (goto-char (point-min))
        (company-coq-make-title-line 'company-coq-doc-header-face-docs)
        (current-buffer)))))

(defun company-coq-doc-buffer-symbol (name)
  (company-coq-doc-buffer-generic name (list company-coq-doc-cmd
                                             company-coq-def-cmd)))

(defun company-coq-doc-buffer-defun (name)
  (company-coq-doc-buffer-generic name (list company-coq-doc-cmd
                                             company-coq-def-cmd
                                             company-coq-tactic-def-cmd)))

(defun company-coq-doc-buffer-tactic (name)
  (setq name (replace-regexp-in-string " .*" "" name))
  (company-coq-doc-buffer-generic name (list company-coq-tactic-def-cmd)))

(defun company-coq-shr-fontize (dom font)
  (funcall (if (functionp 'shr-fontize-cont)
               'shr-fontize-cont
             'shr-fontize-dom)
           dom font))

(defun company-coq-shr-tag-tt (cont)
  (company-coq-shr-fontize cont 'company-coq-doc-tt-face))

(defun company-coq-shr-tag-i (cont)
  (company-coq-shr-fontize cont 'company-coq-doc-i-face))

(defun company-coq-doc-keywords-prettify-title (target-point truncate)
  ;; Company-mode returns to the beginning of the buffer, so centering
  ;; vertically doesn't work.  Instead, just truncate everything, leaving
  ;; just a bit of room for comments preceeding the tactic if any.
  (goto-char (or target-point (point-min)))
  (when target-point
    (company-coq-make-title-line 'company-coq-doc-header-face-docs)
    (when (= (char-after (point)) ?*)
      (delete-char 1)) ;; Remove the star (*) added by shr
    (if (not (eq truncate 'truncate))
        (recenter)
      (forward-line -2)
      (delete-region (point-min) (point)))))

(defun company-coq-is-old-emacs ()
  (< emacs-major-version 25))

(defun company-coq-doc-keywords-put-html (html-full-path truncate)
  (let ((doc (with-temp-buffer
               (insert-file-contents html-full-path)
               (libxml-parse-html-region (point-min) (point-max))))
        ;; Disable line filling for emacs >= 25
        ;; FIXME: This is undocumented behaviour (and new in 25.0)
        ;; Using most-positive-fixnum instead of 0 causes an OOM exception when
        ;; shr tries to render an <hr> or a <table>, so all <hr>s and <table>s
        ;; are removed from the source manual.
        (shr-width (if (company-coq-is-old-emacs) most-positive-fixnum 0))
        (after-change-functions nil)
        (shr-external-rendering-functions '((tt . company-coq-shr-tag-tt)
                                            (i  . company-coq-shr-tag-i))))
    (shr-insert-document doc) ;; This sets the 'shr-target-id property upon finding the shr-target-id anchor
    (company-coq-doc-keywords-prettify-title (next-single-property-change (point-min) 'shr-target-id) truncate)))

(defun company-coq-doc-buffer-keywords (name-or-anchor &optional truncate)
  (interactive)
  (company-coq-dbg "company-coq-doc-buffer-keywords: Called for %s" name-or-anchor)
  (when (fboundp 'libxml-parse-html-region)
    (let* ((anchor         (if (stringp name-or-anchor) (company-coq-get-anchor name-or-anchor) name-or-anchor))
           (shr-target-id  (and anchor (concat "qh" (int-to-string (cdr anchor)))))
           (doc-short-path (and anchor (concat (car anchor) ".html.gz")))
           (doc-full-path  (and doc-short-path
                                (concat (file-name-directory company-coq-script-full-path) "refman/" doc-short-path))))
      (when doc-full-path
        (company-coq-with-clean-doc-buffer
          (company-coq-doc-keywords-put-html doc-full-path truncate)
          (cons (current-buffer) (point)))))))

(defun company-coq-candidates-symbols (prefix)
  "List elements of company-coq-dynamic-symbols or company-coq-buffer-defuns containing PREFIX"
  (when (and company-coq--has-dynamic-completion (company-coq-init-symbols))
    (company-coq-complete-prefix-substring prefix company-coq-dynamic-symbols)))

(defun company-coq-candidates-tactics (prefix)
  "List elements of company-coq-dynamic-symbols or company-coq-buffer-defuns containing PREFIX"
  (when (and company-coq--has-dynamic-completion (company-coq-init-tactics))
    (company-coq-complete-sub-re prefix company-coq-dynamic-tactics)))

(defun company-coq-candidates-defuns (prefix)
  "List elements of `company-coq-buffer-defuns' containing PREFIX"
  (when (company-coq-init-defuns)
    (company-coq-complete-prefix-substring prefix company-coq-buffer-defuns)))

(defun company-coq-candidates-keywords (prefix)
  "List elements of company-coq-known-keywords starting with PREFIX"
  (company-coq-dbg "company-coq-candidates-keywords: Called")
  (when (company-coq-init-keywords)
    (company-coq-complete-sub-re prefix company-coq-known-keywords)))

(defun company-coq-candidates-context (prefix)
  "List elements of company-coq-current-context containing PREFIX"
  (company-coq-complete-prefix-substring prefix company-coq-current-context))

(defun company-coq-candidates-modules (prefix)
  (when (and (company-coq-line-is-import-p) (company-coq-init-modules))
    (company-coq-complete-modules prefix)))

(defun company-coq-candidates-block-end (prefix)
  "Find the closest section/chapter/... opening, if it matches the prefix at point"
  (when (and prefix (company-coq-line-is-block-end-p) (boundp 'show-paren-data-function) (functionp show-paren-data-function))
    (save-excursion
      ;; Find matching delimiter
      (when (re-search-backward company-coq-block-end-regexp)
        (goto-char (+ 1 (match-beginning 1)))
        (-when-let* ((delim-info (funcall show-paren-data-function)))
          (cl-destructuring-bind (_hb _he _tb there-end mismatch) delim-info
            (when (and (not mismatch) there-end)
              (goto-char there-end)
              (re-search-backward company-coq-section-regexp nil t)
              (let ((nearest-section-name (match-string-no-properties 2)))
                (when (and nearest-section-name
                           (equal prefix (substring nearest-section-name 0 (length prefix))))
                  (list nearest-section-name))))))))))

(defun company-coq-candidates-reserved (prefix)
  (interactive)
  (when (and (boundp 'coq-reserved) (member prefix coq-reserved))
    (list prefix)))

(defun company-coq-parse-search-results ()
  "Parse the last output of the prover, looking for symbol names,
and store them in `company-coq-last-search-results'. Prover
output size is cached in `company-coq-last-search-scan-size'."
  (let* ((response-buffer (get-buffer "*response*"))
         (response-size   (buffer-size response-buffer))
         (needs-update    (and response-buffer
                               (not (equal response-size
                                           company-coq-last-search-scan-size)))))
    (unless (and response-buffer (not needs-update))
      (setq company-coq-last-search-results nil))
    (when needs-update
      (setq company-coq-last-search-scan-size response-size)
      (with-current-buffer response-buffer
        (save-match-data
          (save-excursion
            (while (re-search-forward company-coq-all-symbols-slow-regexp nil t)
              (push (match-string-no-properties 1) company-coq-last-search-results))))))))

(defun company-coq-candidates-search-results (prefix)
  (company-coq-parse-search-results)
  (company-coq-complete-prefix-substring prefix company-coq-last-search-results))

(defun company-coq-match (completion)
  (get-text-property 0 'match-end completion))

(defun company-coq-dabbrev-to-yas-format-one (match)
  (let ((identifier (or (match-string 1 match)
                        (and company-coq-explicit-placeholders "_") "")))
    (concat  "${" identifier "}")))

(defun company-coq-yasnippet-choicify-one (match)
  (let ((choices (save-match-data (split-string (match-string 1 match) "|"))))
    (concat "${$$" (prin1-to-string `(company-coq-choose-value (list ,@choices))) "}")))

(defun company-coq-dabbrev-to-yas (abbrev)
  (replace-regexp-in-string company-coq-dabbrev-to-yas-regexp
                            #'company-coq-dabbrev-to-yas-format-one abbrev))

(defun company-coq-dabbrev-to-yas-with-choices (abbrev)
  (let ((snippet (company-coq-dabbrev-to-yas abbrev))
        (case-fold-search t))
    (replace-regexp-in-string company-coq-yasnippet-choice-regexp
                              #'company-coq-yasnippet-choicify-one snippet)))

;; (company-coq-dabbrev-to-yas-with-choices "Typeclasses eauto := @{dfs|bfs} @{depth}.")

(defconst company-coq-abbrevs-transforms-alist '((man  . company-coq-dabbrev-to-yas-with-choices)
                                                 (ltac . company-coq-dabbrev-to-yas)
                                                 (tacn . company-coq-dabbrev-to-yas)
                                                 (pg   . company-coq-dabbrev-to-yas)))

(defun company-coq-abbrev-to-yas (abbrev source)
  (company-coq-dbg "company-coq-abbrev-to-yas: Transforming %s" abbrev)
  (-if-let* ((transform (cdr-safe (assq source company-coq-abbrevs-transforms-alist))))
      (funcall transform abbrev)
    abbrev))

(defun company-coq-get-snippet (candidate)
  (let* ((abbrev  (get-text-property 0 'insert candidate))
         (source  (company-coq-read-abbrev-source candidate))
         (snippet (and abbrev (company-coq-abbrev-to-yas abbrev source))))
    snippet))

(defun company-coq-post-completion-keyword (kwd)
  (-when-let* ((found   (search-backward kwd))
               (start   (match-beginning 0))
               (end     (match-end 0))
               (snippet (company-coq-get-snippet kwd)))
    (let ((insert-fun (get-text-property 0 'insert-fun kwd)))
      (if insert-fun
          (progn
            (delete-region start end)
            (funcall insert-fun))
        (yas-expand-snippet snippet start end)))))

(defun company-coq-goto-occurence (&optional _event)
  (interactive)
  (let ((pos (occur-mode-find-occurrence)))
    (switch-to-buffer (marker-buffer pos))
    (goto-char pos)
    (kill-buffer "*Occur*")))

(defun company-coq-occur ()
  (interactive)
  (let ((same-window-buffer-names '("*Occur*")))
    (occur company-coq-outline-regexp)
    (company-coq-with-current-buffer-maybe "*Occur*"
      (let ((local-map (copy-keymap (current-local-map))))
        (substitute-key-definition #'occur-mode-goto-occurrence
                                   #'company-coq-goto-occurence local-map)
        (substitute-key-definition #'occur-mode-mouse-goto
                                   #'company-coq-goto-occurence local-map)
        (use-local-map local-map)))))

(defun company-coq-grep-symbol (regexp)
  "Find REGEXP in the current directory and subdirectories."
  (interactive
   (list (cond
          ((use-region-p)
           (buffer-substring-no-properties (region-beginning) (region-end)))
          (t
           (let ((symbol (company-coq-symbol-at-point)))
             (if (> (length symbol) 1) (regexp-quote symbol)
               (read-from-minibuffer "Regexp to look for: ")))))))
  (company-coq-dbg "company-coq-grep-symbol: Looking for [%s]" regexp)
  (grep-compute-defaults)
  (message "Using regexp [%s]" regexp)
  (rgrep regexp "*.v" default-directory)
  (with-current-buffer next-error-last-buffer
    (let ((inhibit-read-only t))
      (save-excursion ;; Prettify buffer title
        (goto-char (point-min))
        (when (re-search-forward "\\`[^\0]*?find.*" (point-max) t)
          (replace-match (replace-quote (format "Searching for [%s] in [%s]\n" regexp default-directory)))
          (goto-char (point-min))
          (company-coq-make-title-line 'company-coq-doc-header-face-docs))))))

(defun company-coq-diff-unification-error (&optional context)
  (interactive "P")
  (unless (numberp context) (setq context 10))
  (with-current-buffer "*response*"
    (save-match-data
      (save-excursion
        (goto-char (point-min))
        (if (re-search-forward company-coq-unification-error-message nil t)
            (let ((same-window-buffer-names '("*Diff*"))
                  (b1 "*company-coq-unification-A*")
                  (b2 "*company-coq-unification-B*"))
              (diff (company-coq-insert-match-in-buffer b1 1 " " #'newline)
                    (company-coq-insert-match-in-buffer b2 2 " " #'newline)
                    (list (concat "--unified=" (int-to-string context)) "--minimal" "--ignore-all-space")
                    'noasync)
              (company-coq-with-current-buffer-maybe "*Diff*"
                (diff-refine-hunk))
              (kill-buffer b1)
              (kill-buffer b2))
          (error "Buffer *response* does not match the format of a unification error message."))))))

;; TODO It would be nice to get syntax coloring in the grep buffer

;; TODO this could work better by using information from show-paren-data-function

(defun company-coq-cant-fold-unfold ()
  (save-excursion
    (condition-case nil
        (progn (outline-back-to-heading) nil)
      ('error t))))

(defun company-coq-call-compat (func fallback)
  "Compatibility layer for obsolete function in 24.3"
  (funcall (if (functionp func) func fallback)))

(defun company-coq-fold ()
  "Hide the body of the current proof or definition. When outside
a proof, or when repeated, hide the body of all proofs and
definitions."
  (interactive)
  (when outline-minor-mode
    (if (or (eq last-command #'company-coq-fold) (company-coq-cant-fold-unfold))
        (company-coq-call-compat 'outline-hide-body 'hide-body)
      (company-coq-call-compat 'outline-hide-subtree 'hide-subtree))))

;; Disable company-coq-fold
(unless (plist-member (symbol-plist 'company-coq-fold) 'disabled)
  (put #'company-coq-fold 'disabled t))

(defun company-coq-unfold ()
  (interactive)
  (when outline-minor-mode
    (if (or (eq last-command #'company-coq-unfold) (company-coq-cant-fold-unfold))
        (company-coq-call-compat #'outline-show-all 'show-all)
      (company-coq-call-compat #'outline-show-subtree 'show-subtree))))

;; TODO completion at end of full symbol

(defun company-coq-symbols (command &optional arg &rest ignored)
  "A company-mode backend for dynamically known Coq symbols."
  (interactive (list 'interactive))
  (company-coq-dbg "dynamic symbols backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-symbols))
    (`prefix (company-coq-prefix-simple))
    (`candidates (company-coq-candidates-symbols arg))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-symbol arg))
    (`no-cache t)
    (`match (company-coq-match arg))
    (`annotation "<symb>")
    (`location (company-coq-location-symbol arg))
    (`doc-buffer (company-coq-doc-buffer-symbol arg))
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defun company-coq-tactics (command &optional arg &rest ignored)
  "A company-mode backend for dynamically known Coq tactics."
  (interactive (list 'interactive))
  (company-coq-dbg "dynamic symbols backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-tactics))
    (`prefix (company-coq-prefix-simple))
    (`candidates (company-coq-candidates-tactics arg))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-keyword arg))
    (`no-cache t)
    (`match (company-coq-match arg))
    (`annotation (company-coq-annotation-tactic arg))
    (`location (company-coq-location-tactic arg))
    (`post-completion (company-coq-post-completion-keyword arg))
    (`doc-buffer (company-coq-doc-buffer-tactic arg))
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defun company-coq-defuns (command &optional arg &rest ignored)
  "A company-mode backend for statically known Coq symbols."
  (interactive (list 'interactive))
  (company-coq-dbg "static symbols backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-defuns))
    (`prefix (company-coq-prefix-simple))
    (`candidates (company-coq-candidates-defuns arg))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-symbol arg))
    (`no-cache t)
    (`match (company-coq-match arg))
    (`annotation "<lsymb>")
    (`location (company-coq-location-defun arg))
    (`doc-buffer (company-coq-doc-buffer-defun arg))
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defun company-coq-keywords (command &optional arg &rest ignored)
  "A company-mode backend for Coq keywords."
  (interactive (list 'interactive))
  (company-coq-dbg "keywords backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-keywords))
    (`prefix (company-coq-prefix-simple))
    (`candidates (company-coq-candidates-keywords arg))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-keyword arg))
    (`no-cache t)
    (`match (company-coq-match arg))
    (`annotation (company-coq-annotation-keywords arg))
    (`post-completion (company-coq-post-completion-keyword arg))
    (`doc-buffer (car (company-coq-doc-buffer-keywords arg 'truncate)))
    (`location (company-coq-doc-buffer-keywords arg nil)) ;; TODO
    (`comparison-fun #'company-coq-string-lessp-keywords)
    (`require-match 'never)))

(defun company-coq-context (command &optional arg &rest ignored)
  "A company-mode backend for identifiers grabbed from the current proof context."
  (interactive (list 'interactive))
  (company-coq-dbg "context backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-context))
    (`prefix (company-coq-prefix-simple))
    (`candidates (company-coq-candidates-context arg))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-simple arg))
    (`no-cache t)
    (`annotation (company-coq-annotation-context arg))
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defun company-coq-modules (command &optional arg &rest ignored)
  "A company-mode backend for Coq modules."
  (interactive (list 'interactive))
  (company-coq-dbg "modules backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-modules))
    (`prefix (company-coq-prefix-simple)) ;; FIXME Completion at beginning of hole
    (`candidates (company-coq-candidates-modules arg))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-simple arg))
    (`location (company-coq-location-simple arg))
    (`no-cache t)
    (`match (company-coq-match arg))
    (`require-match 'never)))

(defun company-coq-block-end (command &optional arg &rest ignored)
  "A company-mode backend for the end of Sections and Chapters."
  (interactive (list 'interactive))
  (company-coq-dbg "section end backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-block-end))
    (`prefix (company-coq-prefix-simple))
    (`candidates (company-coq-candidates-block-end arg))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`require-match 'never)))

(defun company-coq-reserved-keywords (command &optional arg &rest ignored)
  "A company-mode backend for language keywords, to prevent completion from kicking in instead of newline."
  (interactive (list 'interactive))
  (company-coq-dbg "reserved keywords backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-reserved-keywords))
    (`prefix (company-coq-prefix-simple))
    (`candidates (company-coq-candidates-reserved arg))
    (`post-completion (call-interactively #'newline))
    (`annotation "<reserved>")
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`require-match 'never)))

(defun company-coq-search-results (command &optional arg &rest ignored)
  "A company-mode backend for search results, offering candidates pulled from the response buffer."
  (interactive (list 'interactive))
  (company-coq-dbg "search results backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-search-results))
    (`prefix (company-coq-prefix-simple))
    (`candidates (company-coq-candidates-search-results arg))
    (`match (company-coq-match arg))
    (`annotation "<search>")
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`location (company-coq-location-defun arg))
    (`doc-buffer (company-coq-doc-buffer-defun arg))
    (`meta (company-coq-meta-symbol arg))
    (`no-cache t)
    (`comparison-fun #'company-coq-string-lessp-match-beginning)
    (`require-match 'never)))

(defvar company-coq-choices-list nil)
(defvar company-coq-saved-idle-delay nil)

(defun company-coq-choose-value (values)
  "Sets company up so that a completion list will popup with values VALUES.
This is a bit tricky, because it's not sufficient to just call
company-begin-backend; the reason is that company doesn't support
recursive calls to itself, and this function may be called as the
result of expanding a snippet, and thus as a descendant of a
company function. Instead of calling it directly, we set the idle
delay to 0, and we override this-command to allow completion to
proceed."
  (unless company-coq-saved-idle-delay
    (setq company-coq-saved-idle-delay company-idle-delay))
  ;; (yas-verify-value values)
  (if yas-moving-away-p
      (company-coq-forget-choices)
    (setq company-coq-choices-list values
          this-command 'self-insert-command
          company-idle-delay 0))
  nil) ;; yas-text would work as well

(defun company-coq-forget-choices ()
  (setq company-coq-choices-list nil
        company-idle-delay (or company-coq-saved-idle-delay company-idle-delay)
        company-coq-saved-idle-delay nil))

(defun company-coq-point-in-field ()
  (and
   (boundp 'yas--active-field-overlay)
   (overlay-start yas--active-field-overlay)
   (overlay-end   yas--active-field-overlay)
   (<= (overlay-start yas--active-field-overlay) (point))
   (>= (overlay-end   yas--active-field-overlay) (point))))

(defun company-coq-choices-prefix ()
  (when (and company-coq-choices-list
             (company-coq-point-in-field))
    (cons (company-grab-word) t)))

(defun company-coq-choices-post-completion ()
  (company-coq-forget-choices)
  (yas-next-field))

(defun company-coq-choices (command &optional arg &rest ignored)
  "A company-mode backend for holes allowing a pre-determined set of values."
  (interactive (list 'interactive))
  (company-coq-dbg "choices backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-choices))
    (`prefix (company-coq-choices-prefix))
    (`candidates (company-coq-complete-prefix-substring arg company-coq-choices-list t))
    (`post-completion (company-coq-choices-post-completion))))

(defun company-coq-make-backends-alist ()
  (mapcar (lambda (backend) (cons backend ()))
          (append '(nil) company-coq-sorted-backends)))

(defun company-coq-push-to-backend-alist (candidate backends-alist)
  (let* ((company-tag   (get-text-property 0 'company-backend candidate))
         (tag-container (or (assq company-tag backends-alist)
                            (assq nil         backends-alist))))
    (push candidate (cdr tag-container))))

(defun company-coq-sort-in-backends-order (candidates)
  (let ((backends-alist (company-coq-make-backends-alist)))
    (mapc (lambda (candidate) ;; Partition the candidates by backend
            (company-coq-push-to-backend-alist candidate backends-alist))
          candidates)
    (apply #'append
           (mapcar (lambda (pair) ;; Sort the results of each backends, and concat all
                     (let ((comparison-fun (and (car pair) (funcall (car pair) 'comparison-fun))))
                       (cl-stable-sort (cdr pair) (or comparison-fun #'company-coq-string-lessp-foldcase))))
                   backends-alist))))

(defvar company-coq-map
  (let ((cc-map (make-sparse-keymap)))
    (define-key cc-map (kbd "C-c C-/")          #'company-coq-fold)
    (define-key cc-map (kbd "C-c C-\\")         #'company-coq-unfold)
    (define-key cc-map (kbd "C-c C-,")          #'company-coq-occur)
    (define-key cc-map (kbd "C-c C-&")          #'company-coq-grep-symbol)
    (define-key cc-map (kbd "C-<return>")       #'company-manual-begin)
    (define-key cc-map (kbd "C-c C-a C-e")      #'company-coq-document-error)
    (define-key cc-map (kbd "C-c C-a C-x")      #'company-coq-lemma-from-goal)
    (define-key cc-map (kbd "C-c C-a RET")      #'company-coq-insert-match-construct)
    (define-key cc-map (kbd "<M-return>")       #'company-coq-insert-match-rule-simple)
    (define-key cc-map (kbd "<M-S-return>")     #'company-coq-insert-match-rule-complex)
    (define-key cc-map (kbd "SPC")              #'company-coq-maybe-exit-snippet)
    (define-key cc-map (kbd "RET")              #'company-coq-maybe-exit-snippet)
    (define-key cc-map (kbd "<C-down-mouse-1>") #'company-coq-show-definition-overlay-under-pointer)
    (define-key cc-map (kbd "<C-mouse-1>")      #'company-coq-clear-definition-overlay)
    (define-key cc-map (kbd "<menu>")           #'company-coq-show-definition-overlay)
    (define-key cc-map [remap proof-goto-point] #'company-coq-proof-goto-point)
    (define-key cc-map [remap narrow-to-defun]  #'company-coq-narrow-to-defun) ;; FIXME handle sections properly
    cc-map)
  "Keymap for company-coq keybindings")

(define-minor-mode company-coq--keybindings-minor-mode
  "Minor mode to provide company-coq keybindings."
  :lighter nil
  :keymap company-coq-map)

(defvar company-coq-electric-exit-characters '(?\; ?.)
  "Characters that exit the current snippet.")

(defun company-coq-after-exit-char ()
  (member (char-before (point)) company-coq-electric-exit-characters))

(defun company-coq-snippet-at-point ()
  (car-safe (yas--snippets-at-point)))

;; FIXME this should only happend in the last hole, and only if not in
;; nested parens, so as to prevent [assert true by (blah;] from
;; exiting.
(defun company-coq-maybe-exit-snippet (arg)
  (interactive "p")
  (let* ((after-exit-char (company-coq-after-exit-char))
         (snippet         (and after-exit-char (company-coq-snippet-at-point)))
         (company-coq--keybindings-minor-mode nil)
         (original-func   (key-binding (this-command-keys-vector))))
    (when snippet
      (yas-exit-snippet snippet))
    (if original-func (call-interactively original-func)
      (self-insert-command arg))))

;; Needed for delete-selection-mode to work properly
(put 'company-coq-maybe-exit-snippet 'delete-selection t)

(defun company-coq-proof-goto-point (&rest args)
  (interactive)
  (when (bound-and-true-p company-mode)
    (company-abort))
  (apply #'proof-goto-point args))

(defmacro company-coq-repeat-until-fixpoint-or-scan-error (body retform)
  `(save-excursion
     (condition-case nil
         (let ((prev-point nil))
           (while (not (equal prev-point (point)))
             (setq prev-point (point))
             ,body))
       (scan-error nil))
     ,retform))

(defun company-coq-beginning-of-proof ()
  (interactive)
  (company-coq-repeat-until-fixpoint-or-scan-error
   (smie-backward-sexp-command 1) (point-at-bol)))

(defun company-coq-end-of-proof ()
  (interactive)
  (company-coq-repeat-until-fixpoint-or-scan-error
   (smie-forward-sexp-command 1) (point-at-eol)))

(defun company-coq-narrow-to-defun ()
  (interactive)
  (narrow-to-region (company-coq-beginning-of-proof) (company-coq-end-of-proof)))

(defun company-coq-region-whitespace-p (beg end)
  (interactive "r")
  (save-excursion
    (goto-char beg)
    (skip-chars-forward " \t\r\n" end)
    (equal (point) end)))

(defun company-coq-insert-match-rule (snippet)
  (when (featurep 'yasnippet)
    (let ((empty-before (company-coq-region-whitespace-p (point-at-bol) (point)))
          (empty-after  (company-coq-region-whitespace-p (point) (point-at-eol))))
      (when (not empty-before) (newline))
      (when (not empty-after)  (just-one-space))
      (yas-expand-snippet snippet)
      (indent-according-to-mode))))

(defun company-coq-insert-match-rule-simple (&optional arg)
  (interactive "P")
  (if (consp arg)
      (company-coq-insert-match-rule "| ${constructor} : $0")
    (company-coq-insert-match-rule "| ${_} => $0")))

(defun company-coq-insert-match-rule-complex (&optional arg)
  (interactive "P")
  (if (consp arg)
      (company-coq-insert-match-rule "| ${constructor} : ${args} -> $0")
    (company-coq-insert-match-rule "| [ ${H: ${hyps}} |- ${_} ] => $0")))

(defun company-coq-lemma-from-goal-interact ()
  "Interactively ask for a lemma name, and hypothesis from the context."
  (let ((hyps       nil)
        (lemma-name "")
        (candidates (cons "" (car-safe (company-coq-run-and-parse-context "Show")))))
    (while (string-equal lemma-name "")
      (setq lemma-name (read-string "Lemma name? ")))
    (while candidates ;; TODO consider completing-read-multiple
      (let ((hyp (completing-read "Hypothesis to keep? " candidates nil t)))
        (if (string-equal hyp "")
            (setq candidates nil)
          (setq candidates (remove hyp candidates))
          (push hyp hyps))))
    (list lemma-name hyps)))

(defun company-coq-lemma-from-goal (lemma-name hyps)
  "Inserts a new lemma into the buffer, called LEMMA-NAME, with
hypotheses HYPS, and everything that they depend on."
  (interactive (company-coq-lemma-from-goal-interact))
  (proof-shell-ready-prover)
  (let* ((gen-cmds  (mapcar (lambda (hyp) (concat "generalize dependent " hyp)) hyps))
         (full-cmd  (mapconcat 'identity (nconc gen-cmds company-coq-lemma-introduction-forms) ";"))
         (ctx-goal  (company-coq-run-and-parse-context full-cmd))
         (_         (company-coq-ask-prover "Undo 1"))
         (lemma     (cdr ctx-goal)))
    (if lemma
        (company-coq-insert-indented
         `(,(concat "Lemma " lemma-name ":\n")
           ,@(mapconcat #'identity lemma "\n")
           ".\nProof.\n"))
      (error "Lemma extraction failed"))))

(defun company-coq-insert-match-construct-interact ()
  (list (read-from-minibuffer "Type of the matched expression (e.g. nat, bool, list, ...): ")))

(defun company-coq-insert-match-construct (type)
  "Insert a match expression.
Similar to `coq-insert-match', but using YAS."
  (interactive (company-coq-insert-match-construct-interact))
  (proof-shell-ready-prover)
  (let* ((question (concat "Show Match " type))
         (response (company-coq-ask-prover question)))
    (if (company-coq-unless-error response)
        (let* ((cleaned (replace-regexp-in-string "\\s-+\\'" "" response))
               (snippet (replace-regexp-in-string "=>$" "=> #" cleaned)))
          (yas-expand-snippet (company-coq-dabbrev-to-yas snippet)))
      (error response))))

(defun company-coq-normalize-error (msg)
  (let* ((truncated (replace-regexp-in-string "\\(?:.\\|[\n]\\)*Error:\\s-" "" msg))
         (cleaned   (replace-regexp-in-string "\"[^\"]+\"" "" truncated))
         (upped     (upcase cleaned))
         (split     (split-string upped "[^[:word:]0-9]+" t))
         (sorted    (sort split #'string<)))
    sorted))

(defun company-coq-find-errors-overlap (reference msg)
  (let* ((norm-ref (company-coq-normalize-error (car reference)))
         (inter    (company-coq-sorted-intersection msg norm-ref)))
    (cons (cons (/ (float (length inter)) (length norm-ref))
                (length norm-ref)) reference)))

(defun company-coq->> (x y)
  (or (> (car x) (car y))
      (and (= (car x) (car y))
           (> (cdr y) (cdr x)))))

(defun company-coq-find-closest-errors (msg)
  (let* ((normalized    (company-coq-normalize-error msg))
         (intersections (cl-loop for reference in company-coq-errors
                                 collect (company-coq-find-errors-overlap reference normalized))))
    (sort intersections (lambda (x y) (company-coq->> (car x) (car y)))))) ;; LATER get maximum instead?

(defconst company-coq-error-doc-min-score 0.5)

(defun company-coq-browse-error-messages ()
  (interactive)
  (let* ((db     (sort (copy-sequence company-coq-errors)
                       (lambda (x y) (company-coq-string-lessp-foldcase (car x) (car y)))))
         (msg    (completing-read "Error message: " db nil t))
         (anchor (cdr-safe (assoc msg company-coq-errors))))
    (when anchor (company-coq-doc-buffer-keywords anchor))))

(defun company-coq-guess-error-message-from-response ()
  (interactive)
  (let* ((err (company-coq-with-current-buffer-maybe "*response*" (buffer-string)))
         (hit (and err (car-safe (company-coq-find-closest-errors err)))))
    (when hit
      (company-coq-dbg "Top reference [%s] has score [%s]" (cadr hit) (car hit))
      (if (< (caar hit) company-coq-error-doc-min-score)
          (error "No documentation found for this error")
        (message "Found error reference [%s]" (cadr hit))
        (company-coq-doc-buffer-keywords (cddr hit))))))

(defun company-coq-document-error (&optional arg)
  (interactive "P")
  (if (consp arg)
      (company-coq-browse-error-messages)
    (company-coq-guess-error-message-from-response)))

(defun company-coq-search-in-coq-buffer (regexp)
  "Search for REGEXP in *coq* buffer. Useful for debugging
tactics in older versions of Coq: use [idtac \"!!!\" message] to
print [message] to output, and `company-coq-search-in-coq-buffer'
to locate lines starting with \"^!!!\"."
  (interactive "MRegexp search in *coq* buffer: ")
  (-if-let* ((coq-buffer (get-buffer-create "*coq*"))
             (same-window-buffer-names '("*Occur*")))
      (with-current-buffer coq-buffer
        (occur regexp))
    (error "*coq* buffer not found")))

(defun company-coq--prepare-for-definition-overlay (strs offset &optional max-lines)
  (let* ((line-width (window-body-width))
         (max-lines  (or max-lines 8))
         (strs       (mapcar #'company-coq-get-header strs)))
    (with-temp-buffer
      (cl-loop for str in strs ;;  for len in lengths   for ins-point = (point)
               do (insert str "\n"))
      (company-coq-truncate-buffer (point-min) max-lines "...")
      (let* ((block-width (company-coq-max-line-length))
             (real-offset (max 0 (min offset (- line-width block-width)))))
        (company-coq-prefix-all-lines (propertize " " 'display `(space . (:width ,real-offset)))))
      (coq-mode)
      (with-no-warnings
        (if (company-coq-is-old-emacs)
            (font-lock-fontify-buffer)
          (font-lock-ensure)))
      ;; Prevent text from inheriting properties of neighbouring characters
      (when (fboundp 'add-face-text-property)
        (company-coq-suppress-warnings (add-face-text-property (point-min) (point-max) 'default t)))
      (company-coq-insert-spacer (point-min))
      (company-coq-insert-spacer (point-max))
      (buffer-string))))

(defun company-coq--count-lines-under-point (&optional max-lines) ;; FIXME this could be much more efficient
  (setq max-lines (or max-lines (window-body-height)))
  (save-excursion
    (let ((line-move-visual 1))
      (cl-loop for x = 0 then (1+ x)
               while (and (< x max-lines) (pos-visible-in-window-p))
               do (vertical-motion 1)
               finally return x))))

(defun company-coq--show-definition-overlay-at-point ()
  (let* ((sb-pos  (company-coq-symbol-at-point-with-pos))
         (ins-pos (and sb-pos (save-excursion (and (forward-line 1)
                                                   (> (point-at-bol) (cdr sb-pos))
                                                   (point-at-bol)))))
         (docs    (and ins-pos (company-coq-doc-buffer-collect-outputs
                                (car sb-pos) (list company-coq-doc-cmd
                                                   company-coq-tactic-def-cmd
                                                   company-coq-def-cmd)
                                (list company-coq-type-cmd))))
         (max-h   (max 4 (min 16 (- (company-coq--count-lines-under-point) 3)))))
    (cond
     (docs (let* ((offset  (company-coq-text-width (point-at-bol) (cdr sb-pos)))
                  (ins-str (company-coq--prepare-for-definition-overlay docs offset max-h)))
             (setq company-coq-definition-overlay (make-overlay ins-pos ins-pos))
             (overlay-put company-coq-definition-overlay 'after-string ins-str)))
     (ins-pos (error "No information found for %s" (car sb-pos)))
     (sb-pos  (error "No newline at end of file"))
     (t       (error "No symbol here")))))

(defcustom company-coq-keyboard-repeat-delay 0.75
  "Duration before a key starts repeating. Increase if the inline definition showed by pressing <menu> flickers."
  :group 'company-coq)

(defcustom company-coq-keyboard-repeat-interval 0.2
  "Duration between two repeats of the same key. Increase if the inline definition showed by pressing <menu> flickers."
  :group 'company-coq)

(defun company-coq-show-definition-overlay ()
  "Displays info about the symbol at point, inline. The display
disappears shortly after the key that this function is bound to
is released."
  ;; Implementation note: The true part of the if case could be made to return
  ;; nil, and the timer made to run after company-coq-keyboard-repeat-interval,
  ;; but this causes the overlay to flicker when used when a list of suggestions
  ;; is also being displayed.
  (interactive)
  (if company-coq-definition-overlay
      ;; Already displayed. Keypress is going to fire again soon, just wait for
      ;; a tiny bit. This will be called again if it does, and otherwise the
      ;; company-coq-clear-definition-overlay timer will fire
      (sit-for company-coq-keyboard-repeat-interval)
    ;; First key press. Show the overlay
    (company-coq--show-definition-overlay-at-point)
    ;; ... then start a timer
    (run-with-idle-timer 0 nil #'company-coq-clear-definition-overlay)
    ;; ... but prevent it from firing while we wait for the next key repeat
    (sit-for company-coq-keyboard-repeat-delay)))

(defun company-coq-show-definition-overlay-under-pointer (event)
  (interactive "e")
  (let* ((window  (posn-window (event-start event)))
         (buffer  (and window (window-buffer window))))
    (if buffer
        (with-current-buffer buffer
          (when (eq major-mode 'coq-mode)
            (save-excursion
              (mouse-set-point event)
              (company-coq-clear-definition-overlay)
              (company-coq--show-definition-overlay-at-point))))
      (mouse-set-point event))))

(defun company-coq-clear-definition-overlay ()
  (interactive)
  (when company-coq-definition-overlay
    (delete-overlay company-coq-definition-overlay)
    (setq company-coq-definition-overlay nil)))

(defun company-coq-prover-init ()
  "This function runs every time a new instance of the prover
starts. It does basic capability detection, and records known
tactic notations, thus ensuring that they are ignored in
subsequent invocations."
  (setq company-coq-needs-capability-detection t)
  (when (proof-shell-available-p)
    (company-coq-dbg "Doing early capability detection and filter initialization")
    (company-coq-detect-capabilities)
    (company-coq-initialize-notations-filter)))

;;;###autoload
(defun company-coq-tutorial ()
  (interactive)
  "Opens the company-coq tutorial in a new buffer, or pop to it
if it is already open."
  (let* ((tutorial-name   "*company-coq-tutorial*")
         (tutorial-buffer (get-buffer tutorial-name))
         (tutorial-path   (expand-file-name "refman/tutorial.v" (file-name-directory company-coq-script-full-path))))
    (unless tutorial-buffer
      (with-current-buffer (setq tutorial-buffer (get-buffer-create tutorial-name))
        (insert-file-contents tutorial-path nil nil nil t)
        (company-coq-setup-temp-coq-buffer)))
    (pop-to-buffer-same-window tutorial-buffer)))

(defun company-coq-setup-keybindings ()
  (company-coq--keybindings-minor-mode))

(defun company-coq-setup-hooks () ;; NOTE: This could be made callable at the beginning of every completion.
  ;; PG hooks
  (add-hook 'proof-shell-init-hook #'company-coq-prover-init)
  (add-hook 'proof-state-change-hook #'company-coq-state-change)
  (add-hook 'proof-shell-insert-hook #'company-coq-maybe-proof-input-reload-things)
  (add-hook 'proof-shell-handle-delayed-output-hook #'company-coq-maybe-proof-output-reload-things)
  (add-hook 'proof-shell-handle-error-or-interrupt-hook #'company-coq-maybe-reload-context)
  (add-hook 'coq-goals-mode-hook #'company-coq-setup-goals-buffer)
  (add-hook 'coq-response-mode-hook #'company-coq-setup-response-buffer)
  ;; Yasnippet
  (add-hook 'yas-after-exit-snippet-hook #'company-coq-forget-choices)
  ;; Prettify
  (add-hook 'hack-local-variables-hook #'company-coq-update-local-symbols))

(defun company-coq-setup-optional-backends ()
  (when company-coq-autocomplete-context
    (add-to-list 'company-coq-backends #'company-coq-context t))

  (when company-coq-autocomplete-modules
    (add-to-list 'company-coq-backends #'company-coq-modules t))

  (when company-coq-autocomplete-symbols
    (add-to-list 'company-coq-backends #'company-coq-defuns t)
    (when company-coq-dynamic-autocompletion
      (add-to-list 'company-coq-backends #'company-coq-tactics t)
      (add-to-list 'company-coq-backends #'company-coq-symbols t)))

  (when company-coq-autocomplete-block-end
    (add-to-list 'company-coq-backends #'company-coq-block-end t))

  (when company-coq-autocomplete-search-results
    (add-to-list 'company-coq-backends #'company-coq-search-results t)))

(defun company-coq-setup-company ()
  (company-mode 1)
  (set (make-local-variable 'company-idle-delay) 0)
  (set (make-local-variable 'company-tooltip-align-annotations) t)
  (set (make-local-variable 'company-abort-manual-when-too-short) t)

  ;; Let company know about our backends
  (add-to-list (make-local-variable 'company-backends) company-coq-backends)
  (add-to-list (make-local-variable 'company-backends) #'company-coq-choices)
  (add-to-list (make-local-variable 'company-transformers) #'company-coq-sort-in-backends-order))

(defun company-coq-setup-outline ()
  (outline-minor-mode 1)
  (set (make-local-variable 'outline-level) #'company-coq-outline-level)
  (set (make-local-variable 'outline-regexp) company-coq-outline-regexp)
  (set (make-local-variable 'outline-heading-end-regexp) company-coq-outline-heading-end-regexp))

(defun company-coq-setup-prettify ()
  (when (and (display-graphic-p)
             (fboundp #'prettify-symbols-mode)
             company-coq-prettify-symbols)
    (company-coq-suppress-warnings
     (set (make-local-variable 'prettify-symbols-alist)
          (append prettify-symbols-alist company-coq-prettify-symbols-alist company-coq-local-symbols))
     (prettify-symbols-mode))))

(defun company-coq-update-local-symbols ()
  (when (assoc 'company-coq-local-symbols file-local-variables-alist)
    (company-coq-setup-prettify)))

(defun company-coq-get-comment-opener (comment-string-start)
  (ignore-errors
    (when comment-string-start
      (save-excursion
        (goto-char comment-string-start)
        (buffer-substring (point) (progn (skip-chars-forward "(*!+" (+ 5 (point))) (1+ (point))))))))

(defun company-coq-syntactic-face-function-aux (_depth _innermost-start _last-complete-start
                                                in-string comment-depth _after-quote _min-paren-depth
                                                _comment-style comment-string-start _continuation)
  (cond
   (in-string font-lock-string-face)
   ((or comment-depth (numberp comment-depth))
    (let* ((comment-opener (company-coq-get-comment-opener comment-string-start))
           (matches        (lambda (pattern) (string-match-p (concat "\\`" (regexp-quote pattern)) comment-opener))))
      (cond
        ((funcall matches "(*!")   '(:inherit font-lock-doc-face :height 1.2))
        ((funcall matches "(*+")   '(:inherit font-lock-doc-face :height 1.8))
        ((funcall matches "(*** ") '(:inherit font-lock-doc-face :height 2.5))
        ((funcall matches "(**")   font-lock-doc-face)
        (t        font-lock-comment-face))))))

(defun company-coq-syntactic-face-function (args)
  (apply #'company-coq-syntactic-face-function-aux args))

(defun company-coq-fill-nobreak-predicate ()
  (not (memq (get-text-property (point) 'face) '(font-lock-doc-face font-lock-comment-face))))

(defun company-coq-setup-fontlock ()
  (set (make-local-variable 'font-lock-syntactic-face-function) #'company-coq-syntactic-face-function)
  (font-lock-add-keywords nil '(("\\_<pose proof\\_>" 0 'proof-tactics-name-face prepend)) 'add)
  (font-lock-add-keywords nil '(("\\(?:\\W\\|\\`\\)\\(@\\)\\_<" 1 'font-lock-constant-face append)) 'add)
  (font-lock-add-keywords nil '(("\\(?:\\W\\|\\`\\)\\(\\?\\(?:\\s_\\|\\sw\\)+\\)\\_>" 1 'font-lock-variable-name-face append)) 'add)
  (add-to-list (make-local-variable 'font-lock-extra-managed-props) 'help-echo)
  (font-lock-add-keywords nil company-coq-deprecated-spec t))

(defun company-coq-setup-misc-pc-improvements ()
  (set (make-local-variable 'fill-nobreak-predicate) #'company-coq-fill-nobreak-predicate)
  (set (make-local-variable 'help-at-pt-display-when-idle) t)
  (help-at-pt-set-timer))

(defun company-coq-setup-minor-modes ()
  (yas-minor-mode 1)
  (show-paren-mode 1)
  (company-coq-setup-company)
  (company-coq-setup-outline)
  (company-coq-setup-prettify)
  (company-coq-setup-fontlock))

(defun company-coq-setup-goals-buffer ()
  (add-to-list (make-local-variable 'font-lock-extra-managed-props) 'display)
  (font-lock-add-keywords nil company-coq-goal-separator-spec t)  ;; Prettify the goals line ("=====")
  (font-lock-add-keywords nil company-coq-subscript-spec t)  ;; Transform H1 into H_1
  (company-coq-setup-prettify))

(defun company-coq-setup-response-buffer ()
  (company-coq-setup-prettify)
  (visual-line-mode 1))

;;;###autoload
(defun company-coq-initialize () ;; TODO this could be a minor mode
  (interactive)
  (when (not (company-coq-coq-mode-p))
    (error "company-coq only works with coq-mode."))

  ;; Setup backends and relevant minor modes
  (company-coq-setup-optional-backends)
  (company-coq-setup-minor-modes)

  ;; Some more improvements that don't fit in any of the minor modes
  (company-coq-setup-misc-pc-improvements)

  ;; Load keywords
  (company-coq-init-keywords)

  ;; Setup hooks
  (company-coq-setup-hooks)

  ;; Set up a few convenient key bindings
  (company-coq-setup-keybindings))

(defun company-coq-unload-function ()
  (cl-loop for feature in '(company-coq-abbrev company-coq-tg)
           when (featurep feature)
           do (unload-feature feature t))

  (remove-hook 'proof-shell-init-hook #'company-coq-prover-init)
  (remove-hook 'proof-shell-insert-hook #'company-coq-maybe-proof-input-reload-things)
  (remove-hook 'proof-shell-handle-delayed-output-hook #'company-coq-maybe-proof-output-reload-things)
  (remove-hook 'proof-shell-handle-error-or-interrupt-hook #'company-coq-maybe-reload-context)

  (remove-hook 'coq-goals-mode-hook #'company-coq-setup-goals-buffer)
  (remove-hook 'coq-response-mode-hook #'company-coq-setup-response-buffer)

  (remove-hook 'yas-after-exit-snippet-hook #'company-coq-forget-choices)
  (remove-hook 'hack-local-variables-hook #'company-coq-update-local-symbols)

  (setq font-lock-syntactic-face-function (default-value 'font-lock-syntactic-face-function))
  (help-at-pt-cancel-timer)

  (setq company-backends     (delete company-coq-backends company-backends))
  (setq company-backends     (delete #'company-coq-choices company-backends))
  (setq company-transformers (delete #'company-coq-sort-in-backends-order company-transformers))

  (cl-loop for buffer in (buffer-list)
           do (with-current-buffer buffer
                (when (company-coq-coq-mode-p)
                  (company-mode -1)
                  (yas-minor-mode -1)
                  (outline-minor-mode -1)
                  (when (fboundp 'prettify-symbols-mode)
                    (company-coq-suppress-warnings (prettify-symbols-mode -1)))
                  (company-coq--keybindings-minor-mode -1))))

  nil)

(defun toggle-company-coq-debug ()
  "Toggles company-coq-debug. When on, prints debug messages during operation."
  (interactive)
  (setq company-coq-debug (not company-coq-debug))
  (message "company-coq-debug: %s" company-coq-debug))

;; TODO add a binding to look up the word at point

(provide 'company-coq)
;;; company-coq.el ends here
