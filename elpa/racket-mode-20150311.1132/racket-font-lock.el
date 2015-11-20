;;; racket-font-lock.el

;; Copyright (c) 2013-2015 by Greg Hendershott.

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

(require 'racket-custom)
(require 'racket-keywords-and-builtins)

(defconst racket-font-lock-keywords
  (eval-when-compile
    ;; Note: font-lock iterates by matcher, doing an re-search-forward
    ;; over the entire region. As a result, it's faster to consolidate
    ;; matchers that will yield the same result (unless they need to
    ;; be tried in a certain order).
    `(
      ;; paren
      (,(rx (any "[](){}")) . racket-paren-face)

      ;; #shebang
      (,(rx bol "#!" (+ nonl) eol) . font-lock-comment-face)

      ;; #lang
      (,(rx (group (group "#lang")
                   (1+ " ")
                   (group (1+ not-newline))))
       (2 font-lock-keyword-face nil t)
       (3 font-lock-variable-name-face nil t))

      ;; keyword argument
      (,(rx "#:" (1+ (or (syntax word) (syntax symbol))))
       . racket-keyword-argument-face)

      ;; Various things for racket-selfeval-face
      (,(rx (or
             ;; symbol
             (seq ?' ?| (+? any) ?|)
             (seq ?' (1+ (or (syntax word) (syntax symbol))))
             (seq "#\\" (1+ (or (syntax word) (syntax symbol))))))
       . racket-selfeval-face)

      ;; #rx #px. Needs `group'.
      (,(rx (group (or "#rx" "#px")) ?\")
       1 racket-selfeval-face)

      (,(regexp-opt racket-type-list 'symbols) . font-lock-type-face)
      (,(regexp-opt racket-builtins 'symbols) . font-lock-builtin-face)
      (,(regexp-opt racket-keywords 'symbols) . font-lock-keyword-face)

      ;; def* -- variables
      (,(rx "(def" (0+ (not (any " "))) (1+ " ")
            (group (1+ (not (any "( ")))))
       1 font-lock-variable-name-face)
      (,(rx "(define-values" (0+ " ") "(" (group (1+ (not (any "(")))) ")")
       1 font-lock-variable-name-face)

      ;; def* -- functions
      (,(rx "(def" (0+ (or (syntax word) (syntax symbol))) (1+ " ")
            (+ "(") (group (1+ (or (syntax word) (syntax symbol)))))
       1 font-lock-function-name-face)

      ;; module and module*
      (,(rx "("
            (group "module" (? "*"))
            (1+ " ")
            (group (1+ (or (syntax word) (syntax symbol))))
            (1+ " ")
            (group (1+ (or (syntax word) (syntax symbol)))))
       (1 font-lock-keyword-face nil t)
       (2 font-lock-function-name-face nil t)
       (3 font-lock-variable-name-face nil t))
      ;; module+
      (,(rx "("
            (group "module+")
            (1+ " ")
            (group (1+ (or (syntax word) (syntax symbol)))))
       (1 font-lock-keyword-face nil t)
       (2 font-lock-function-name-face nil t))

      ;; pretty lambda
      (,(rx (syntax open-parenthesis)
            (? (or "case-" "match-" "opt-"))
            (group "lambda")
            (or word-end symbol-end))
       1
       (if racket-pretty-lambda
           (progn (compose-region (match-beginning 1)
                                  (match-end       1)
                                  racket-lambda-char)
                  nil)
         font-lock-keyword-face)
       nil t)

      ;; Some self-eval constants
      (,(regexp-opt '("#t" "#f" "+inf.0" "-inf.0" "+nan.0") 'symbols)
       . racket-selfeval-face)

      ;; Numeric literals including Racket reader hash prefixes.
      (,(rx
         (seq symbol-start
              (or
               ;; #d #e #i or no hash prefix
               (seq (? "#" (any "dei"))
                    (or (seq (? (any "-+"))
                             (1+ digit)
                             (? (any "./") (1+ digit)))
                        (seq (1+ digit)
                             ?e
                             (? (any "-+"))
                             (1+ digit))))
               ;; #x
               (seq "#x"
                    (? (any "-+"))
                    (1+ hex-digit)
                    (? (any "./") (1+ hex-digit)))
               ;; #b
               (seq "#b"
                    (or (seq (? (any "-+"))
                             (1+ (any "01"))
                             (? (any "./") (1+ (any "01"))))
                        (seq (1+ (any "01"))
                             ?e
                             (? (any "-+"))
                             (1+ (any "01")))))
               ;; #o
               (seq "#o"
                    (or (seq (? (any "-+"))
                             (1+ (any "0-7"))
                             (? (any "./") (1+ (any "0-7"))))
                        (seq (1+ (any "0-7"))
                             ?e
                             (? (any "-+"))
                             (1+ (any "0-7"))))))
              symbol-end))
       . racket-selfeval-face)))
    "Font lock keywords for Racket mode")

(provide 'racket-font-lock)

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:

;; racket-font-lock.el ends here
