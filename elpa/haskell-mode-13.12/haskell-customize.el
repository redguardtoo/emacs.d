;;; haskell-customize.el --- Customization settings

;; Copyright (c) 2014 Chris Done. All rights reserved.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:

(require 'cl-lib)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization variables

(defgroup haskell nil
  "Major mode for editing Haskell programs."
  :link '(custom-manual "(haskell-mode)")
  :group 'languages
  :prefix "haskell-")

(defvar haskell-mode-pkg-base-dir (file-name-directory load-file-name)
  "Package base directory of installed `haskell-mode'.
Used for locating additional package data files.")

(defcustom haskell-completing-read-function 'ido-completing-read
  "Default function to use for completion."
  :group 'haskell
  :type '(choice
          (function-item :tag "ido" :value ido-completing-read)
          (function-item :tag "helm" :value helm--completing-read-default)
          (function-item :tag "completing-read" :value completing-read)
          (function :tag "Custom function")))

(defcustom haskell-process-type
  'auto
  "The inferior Haskell process type to use."
  :type '(choice (const auto) (const ghci) (const cabal-repl) (const cabal-dev) (const cabal-ghci))
  :group 'haskell-interactive)

(defcustom haskell-process-wrapper-function
  #'identity
  "Wrap or transform haskell process commands using this function.

Can be set to a custom function which takes a list of arguments
and returns a possibly-modified list.

The following example function arranges for all haskell process
commands to be started in the current nix-shell environment:

  (lambda (argv) (append (list \"nix-shell\" \"-I\" \".\" \"--command\" )
                    (list (mapconcat 'identity argv \" \"))))

See Info Node `(emacs)Directory Variables' for a way to set this option on
a per-project basis."
  :group 'haskell-interactive
  :type '(choice
          (function-item :tag "None" :value identity)
          (function :tag "Custom function")))

(defcustom haskell-ask-also-kill-buffers
  t
  "Ask whether to kill all associated buffers when a session
 process is killed."
  :type 'boolean
  :group 'haskell-interactive)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Configuration

(defvar haskell-process-end-hook nil
  "Hook for when the haskell process ends.")

(defgroup haskell-interactive nil
  "Settings for REPL interaction via `haskell-interactive-mode'"
  :link '(custom-manual "(haskell-mode)haskell-interactive-mode")
  :group 'haskell)

(defcustom haskell-process-path-ghci
  "ghci"
  "The path for starting ghci."
  :group 'haskell-interactive
  :type '(choice string (repeat string)))

(defcustom haskell-process-path-cabal
  "cabal"
  "Path to the `cabal' executable."
  :group 'haskell-interactive
  :type '(choice string (repeat string)))

(defcustom haskell-process-path-cabal-ghci
  "cabal-ghci"
  "The path for starting cabal-ghci."
  :group 'haskell-interactive
  :type '(choice string (repeat string)))

(defcustom haskell-process-path-cabal-dev
  "cabal-dev"
  "The path for starting cabal-dev."
  :group 'haskell-interactive
  :type '(choice string (repeat string)))

(defcustom haskell-process-args-ghci
  '("-ferror-spans")
  "Any arguments for starting ghci."
  :group 'haskell-interactive
  :type '(repeat (string :tag "Argument")))

(defcustom haskell-process-args-cabal-repl
  '("--ghc-option=-ferror-spans")
  "Additional arguments to for `cabal repl' invocation.
Note: The settings in `haskell-process-path-ghci' and
`haskell-process-args-ghci' are not automatically reused as `cabal repl'
currently invokes `ghc --interactive'. Use
`--with-ghc=<path-to-executable>' if you want to use a different
interactive GHC frontend; use `--ghc-option=<ghc-argument>' to
pass additional flags to `ghc'."
  :group 'haskell-interactive
  :type '(repeat (string :tag "Argument")))

(defcustom haskell-process-do-cabal-format-string
  ":!cd %s && %s"
  "The way to run cabal comands. It takes two arguments -- the directory and the command.
See `haskell-process-do-cabal' for more details."
  :group 'haskell-interactive
  :type 'string)

(defcustom haskell-process-log
  nil
  "Enable debug logging to \"*haskell-process-log*\" buffer."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-show-debug-tips
  t
  "Show debugging tips when starting the process."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-notify-p
  nil
  "Notify using notifications.el (if loaded)?"
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-suggest-no-warn-orphans
  t
  "Suggest adding -fno-warn-orphans pragma to file when getting orphan warnings."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-suggest-hoogle-imports
  nil
  "Suggest to add import statements using Hoogle as a backend."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-suggest-hayoo-imports
  nil
  "Suggest to add import statements using Hayoo as a backend."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-hayoo-query-url
  "http://hayoo.fh-wedel.de/json/?query=%s"
  "Query url for json hayoo results."
  :type 'string
  :group 'haskell-interactive)

(defcustom haskell-process-suggest-haskell-docs-imports
  nil
  "Suggest to add import statements using haskell-docs as a backend."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-suggest-add-package
  t
  "Suggest to add packages to your .cabal file when Cabal says it
is a member of the hidden package, blah blah."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-suggest-language-pragmas
  t
  "Suggest adding LANGUAGE pragmas recommended by GHC."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-suggest-remove-import-lines
  nil
  "Suggest removing import lines as warned by GHC."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-suggest-overloaded-strings
  t
  "Suggest adding OverloadedStrings pragma to file when getting type mismatches with [Char]."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-check-cabal-config-on-load
  t
  "Check changes cabal config on loading Haskell files and
restart the GHCi process if changed.."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-prompt-restart-on-cabal-change
  t
  "Ask whether to restart the GHCi process when the Cabal file
has changed?"
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-auto-import-loaded-modules
  nil
  "Auto import the modules reported by GHC to have been loaded?"
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-reload-with-fbytecode
  nil
  "When using -fobject-code, auto reload with -fbyte-code (and
then restore the -fobject-code) so that all module info and
imports become available?"
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-use-presentation-mode
  nil
  "Use presentation mode to show things like type info instead of
  printing to the message area."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-process-suggest-restart
  t
  "Suggest restarting the process when it has died"
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-interactive-mode-scroll-to-bottom
  nil
  "Scroll to bottom in the REPL always."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-interactive-popup-errors
  t
  "Popup errors in a separate buffer."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-interactive-mode-collapse
  nil
  "Collapse printed results."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-interactive-types-for-show-ambiguous
  t
  "Show types when there's no Show instance or there's an
ambiguous class constraint."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-interactive-mode-eval-pretty
  nil
  "Print eval results that can be parsed as Show instances prettily. Requires sexp-show (on Hackage)."
  :type 'boolean
  :group 'haskell-interactive)

(defvar haskell-interactive-prompt "λ> "
  "The prompt to use.")

(defcustom haskell-interactive-mode-eval-mode
  nil
  "Use the given mode's font-locking to render some text."
  :type '(choice function (const :tag "None" nil))
  :group 'haskell-interactive)

(defcustom haskell-interactive-mode-hide-multi-line-errors
  nil
  "Hide collapsible multi-line compile messages by default."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-interactive-mode-delete-superseded-errors
  t
  "Whether to delete compile messages superseded by recompile/reloads."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-interactive-mode-include-file-name
  t
  "Include the file name of the module being compiled when
printing compilation messages."
  :type 'boolean
  :group 'haskell-interactive)

(defcustom haskell-import-mapping
  '()
  "Support a mapping from module to import lines.

E.g. '((\"Data.Map\" . \"import qualified Data.Map as M
import Data.Map (Map)
\"))

This will import

import qualified Data.Map as M
import Data.Map (Map)

when Data.Map is the candidate.

"
  :type '(repeat (cons (string :tag "Module name")
                       (string :tag "Import lines")))
  :group 'haskell-interactive)

(defcustom haskell-language-extensions
  '()
  "Language extensions in use. Should be in format: -XFoo, -XNoFoo etc."
  :group 'shm
  :type '(repeat 'string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Accessor functions

(defun haskell-process-type ()
  "Return `haskell-process-type', or a guess if that variable is 'auto."
  (if (eq 'auto haskell-process-type)
      (if (locate-dominating-file
           default-directory
           (lambda (d)
             (or (file-directory-p (expand-file-name ".cabal-sandbox" d))
                 (cl-find-if (lambda (f) (string-match-p ".\\.cabal\\'" f)) (directory-files d)))))
          'cabal-repl
        'ghci)
    haskell-process-type))

;;;###autoload
(defun haskell-customize ()
  "Browse the haskell customize sub-tree.
This calls 'customize-browse' with haskell as argument and makes
sure all haskell customize definitions have been loaded."
  (interactive)
  ;; make sure all modules with (defcustom ...)s are loaded
  (mapc 'require
        '(haskell-checkers haskell-compile haskell-doc haskell-font-lock haskell-indentation haskell-indent haskell-interactive-mode haskell-menu haskell-process haskell-yas inf-haskell))
  (customize-browse 'haskell))

(provide 'haskell-customize)
