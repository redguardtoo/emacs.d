;;; js2-refactor.el --- The beginnings of a JavaScript refactoring library in emacs.

;; Copyright (C) 2012-2014 Magnar Sveen
;; Copyright (C) 2015 Magnar Sveen and Nicolas Petton

;; Author: Magnar Sveen <magnars@gmail.com>,
;;         Nicolas Petton <nicolas@petton.fr>
;; Keywords: conveniences

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

;; This is a collection of small refactoring functions to further the idea of a
;; JavaScript IDE in Emacs that started with js2-mode.

;; ## Installation

;; Start by installing the dependencies:

;;  * js2-mode https://github.com/mooz/js2-mode/
;;  * dash https://github.com/magnars/dash.el
;;  * multiple-cursors https://github.com/magnars/multiple-cursors.el

;; It is also recommended to get
;; [expand-region](https://github.com/magnars/expand-region.el) to more easily mark
;; vars, method calls and functions for refactorings.

;; Then add this to your emacs settings:

;;     (require 'js2-refactor)
;;     (add-hook 'js2-mode-hook #'js2-refactor-mode)
;;     (js2r-add-keybindings-with-prefix "C-c C-m")

;; Note: I am working on a smoother installation path through package.el,
;; but I haven't had the time to whip this project into that sort of
;; structure - yet.

;; ## Usage

;; All refactorings start with `C-c C-m` and then a two-letter mnemonic shortcut.

;;  * `ef` is `extract-function`: Extracts the marked expressions out into a new named function.
;;  * `em` is `extract-method`: Extracts the marked expressions out into a new named method in an object literal.
;;  * `ip` is `introduce-parameter`: Changes the marked expression to a parameter in a local function.
;;  * `lp` is `localize-parameter`: Changes a parameter to a local var in a local function.
;;  * `eo` is `expand-object`: Converts a one line object literal to multiline.
;;  * `co` is `contract-object`: Converts a multiline object literal to one line.
;;  * `eu` is `expand-function`: Converts a one line function to multiline (expecting semicolons as statement delimiters).
;;  * `cu` is `contract-function`: Converts a multiline function to one line (expecting semicolons as statement delimiters).
;;  * `ea` is `expand-array`: Converts a one line array to multiline.
;;  * `ca` is `contract-array`: Converts a multiline array to one line.
;;  * `wi` is `wrap-buffer-in-iife`: Wraps the entire buffer in an immediately invoked function expression
;;  * `ig` is `inject-global-in-iife`: Creates a shortcut for a marked global by injecting it in the wrapping immediately invoked function expression
;;  * `ag` is `add-to-globals-annotation`: Creates a `/*global */` annotation if it is missing, and adds the var at point to it.
;;  * `ev` is `extract-var`: Takes a marked expression and replaces it with a var.
;;  * `iv` is `inline-var`: Replaces all instances of a variable with its initial value.
;;  * `rv` is `rename-var`: Renames the variable on point and all occurrences in its lexical scope.
;;  * `vt` is `var-to-this`: Changes local `var a` to be `this.a` instead.
;;  * `ao` is `arguments-to-object`: Replaces arguments to a function call with an object literal of named arguments. Requires yasnippets.
;;  * `3i` is `ternary-to-if`: Converts ternary operator to if-statement.
;;  * `sv` is `split-var-declaration`: Splits a `var` with multiple vars declared, into several `var` statements.
;;  * `ss` is `split-string`: Splits a `string`.
;;  * `uw` is `unwrap`: Replaces the parent statement with the selected region.

;; There are also some minor conveniences bundled:

;;  * `C-S-down` and `C-S-up` moves the current line up or down. If the line is an
;;    element in an object or array literal, it makes sure that the commas are
;;    still correctly placed.
;;  * `k` `kill-line`: Like `kill-line` but respecting the AST.

;; ## Todo

;; A list of some wanted improvements for the current refactorings.

;;  * expand- and contract-array: should work recursively with nested object literals and nested arrays.
;;  * expand- and contract-function: should deal better with nested object literals, array declarations, and statements terminated only by EOLs (without semicolons).
;;  * wrap-buffer-in-iife: should skip comments and namespace initializations at buffer start.
;;  * extract-variable: could end with a query-replace of the expression in its scope.

;; ## Contributions

;; * [Matt Briggs](https://github.com/mbriggs) contributed `js2r-add-to-globals-annotation`
;; * [Alex Chamberlain](https://github.com/apchamberlain) contributed contracting and expanding arrays and functions.
;; * [Nicolas Petton](https://github.com/NicolasPetton) contributed `js2r-kill`
;; Thanks!

;; ## Contribute

;; This project is still in its infancy, and everything isn't quite sorted out
;; yet. If you're eager to contribute, please add an issue here on github and we
;; can discuss your changes a little before diving into the elisp. :-)

;; To fetch the test dependencies:

;;     $ cd /path/to/multiple-cursors
;;     $ git submodule init
;;     $ git submodule update

;; Run the tests with:

;;     $ ./util/ecukes/ecukes features

;;; Code:

(require 'js2-mode)
(require 'js2r-helpers)
(require 'js2r-formatting)
(require 'js2r-iife)
(require 'js2r-vars)
(require 'js2r-functions)
(require 'js2r-wrapping)
(require 'js2r-conditionals)
(require 'js2r-conveniences)
(require 'js2r-paredit)

(defvar js2-refactor-mode-map
  (make-sparse-keymap)
  "Keymap for js2-refactor.")

(define-minor-mode js2-refactor-mode
  "Minor mode providing JavaScript refactorings."
  :lighter " js2r"
  :keymap js2-refactor-mode-map
  (when js2-refactor-mode
    (yas-minor-mode-on)))

;;; Settings ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar js2r-use-strict nil
  "When non-nil, js2r inserts strict declarations in IIFEs.")

;;; Keybindings ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun js2r--add-keybindings (key-fn)
  "Add js2r refactoring keybindings to `js2-mode-map' using KEY-FN to create each keybinding."
  (define-key js2-refactor-mode-map (funcall key-fn "eo") 'js2r-expand-object)
  (define-key js2-refactor-mode-map (funcall key-fn "co") 'js2r-contract-object)
  (define-key js2-refactor-mode-map (funcall key-fn "eu") 'js2r-expand-function)
  (define-key js2-refactor-mode-map (funcall key-fn "cu") 'js2r-contract-function)
  (define-key js2-refactor-mode-map (funcall key-fn "ea") 'js2r-expand-array)
  (define-key js2-refactor-mode-map (funcall key-fn "ca") 'js2r-contract-array)
  (define-key js2-refactor-mode-map (funcall key-fn "wi") 'js2r-wrap-buffer-in-iife)
  (define-key js2-refactor-mode-map (funcall key-fn "ig") 'js2r-inject-global-in-iife)
  (define-key js2-refactor-mode-map (funcall key-fn "ev") 'js2r-extract-var)
  (define-key js2-refactor-mode-map (funcall key-fn "iv") 'js2r-inline-var)
  (define-key js2-refactor-mode-map (funcall key-fn "rv") 'js2r-rename-var)
  (define-key js2-refactor-mode-map (funcall key-fn "vt") 'js2r-var-to-this)
  (define-key js2-refactor-mode-map (funcall key-fn "ag") 'js2r-add-to-globals-annotation)
  (define-key js2-refactor-mode-map (funcall key-fn "sv") 'js2r-split-var-declaration)
  (define-key js2-refactor-mode-map (funcall key-fn "ss") 'js2r-split-string)
  (define-key js2-refactor-mode-map (funcall key-fn "ef") 'js2r-extract-function)
  (define-key js2-refactor-mode-map (funcall key-fn "em") 'js2r-extract-method)
  (define-key js2-refactor-mode-map (funcall key-fn "ip") 'js2r-introduce-parameter)
  (define-key js2-refactor-mode-map (funcall key-fn "lp") 'js2r-localize-parameter)
  (define-key js2-refactor-mode-map (funcall key-fn "tf") 'js2r-toggle-function-expression-and-declaration)
  (define-key js2-refactor-mode-map (funcall key-fn "ao") 'js2r-arguments-to-object)
  (define-key js2-refactor-mode-map (funcall key-fn "uw") 'js2r-unwrap)
  (define-key js2-refactor-mode-map (funcall key-fn "wl") 'js2r-wrap-in-for-loop)
  (define-key js2-refactor-mode-map (funcall key-fn "3i") 'js2r-ternary-to-if)
  (define-key js2-refactor-mode-map (funcall key-fn "lt") 'js2r-log-this)
  (define-key js2-refactor-mode-map (funcall key-fn "dt") 'js2r-debug-this)
  (define-key js2-refactor-mode-map (funcall key-fn "sl") 'js2r-forward-slurp)
  (define-key js2-refactor-mode-map (funcall key-fn "ba") 'js2r-forward-barf)
  (define-key js2-refactor-mode-map (funcall key-fn "k") 'js2r-kill)
  (define-key js2-refactor-mode-map (kbd "<C-S-down>") 'js2r-move-line-down)
  (define-key js2-refactor-mode-map (kbd "<C-S-up>") 'js2r-move-line-up))

;;;###autoload
(defun js2r-add-keybindings-with-prefix (prefix)
  "Add js2r keybindings using the prefix PREFIX."
  (js2r--add-keybindings (-partial 'js2r--key-pairs-with-prefix prefix)))

;;;###autoload
(defun js2r-add-keybindings-with-modifier (modifier)
  "Add js2r keybindings using the modifier MODIFIER."
  (js2r--add-keybindings (-partial 'js2r--key-pairs-with-modifier modifier)))

(provide 'js2-refactor)
;;; js2-refactor.el ends here
