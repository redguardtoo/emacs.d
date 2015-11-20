;;; faceup.el --- Regression test system for font-lock

;; Copyright (C) 2013-2015 Anders Lindgren

;; Author: Anders Lindgren
;; Version: 0.0.3
;; Package-Version: 20150215.1348
;; Created: 2013-01-21
;; Keywords: faces languages
;; URL: https://github.com/Lindydancer/faceup

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Emacs is capable of highlighting buffers based on language-specific
;; `font-lock' rules. This package, `faceup', makes it possible to
;; perform regression test for packages that provide font-lock rules.
;;
;; The underlying idea is to convert text with highlights ("faces")
;; into a plain text representation using the Faceup markup language.
;; By comparing the current highlight with a highlight performed with
;; earlier versions of a package, it's possible to find problems that
;; otherwise would have been hard to spot.
;;
;; The `faceup' package is designed to be used in conjunction with
;; Ert, the standard Emacs regression test system.
;;
;; The Faceup markup language is a generic markup language, regression
;; testing is merely one way to use it.

;; Installation:
;;
;; This package is designed to be installed with the Emacs built-in
;; package manager.

;; Regression test examples:
;;
;; This section describes the two typical ways regression testing with
;; this package is performed.
;;
;;
;; Full source file highlighting:
;;
;; The most straight-forward way to perform regression testing is to
;; collect a number of representative source files. From each source
;; file, say `alpha.mylang', you can use `M-x faceup-write-file RET'
;; to generate a Faceup file named `alpha.mylang.faceup', this file
;; use the Faceup markup language to represent the text with
;; highlights and is used as a reference in future tests.
;;
;; An Ert test case can be defined as follows:
;;
;;    (require 'faceup)
;;
;;    (defvar mylang-font-lock-test-dir (faceup-this-file-directory))
;;
;;    (defun mylang-font-lock-test-apps (file)
;;      "Test that the mylang FILE is fontifies as the .faceup file describes."
;;      (faceup-test-font-lock-file 'mylang-mode
;;                                  (concat mylang-font-lock-test-dir file)))
;;    (faceup-defexplainer mylang-font-lock-test-apps)
;;
;;    (ert-deftest mylang-font-lock-file-test ()
;;      (should (mylang-font-lock-test-apps "apps/FirstApp/alpha.mylang"))
;;      ;; ... Add more test files here ...
;;      )
;;
;; To execute the tests simply run something like `M-x ert RET t RET'.
;;
;;
;; Source snippets:
;;
;; To test smaller snippets of code, you can use the
;; `faceup-test-font-lock-string'. It takes a major mode and a string
;; written using the Faceup markup language. The functions strips away
;; the Faceup markup, inserts the plain text into a temporary buffer,
;; highlights it, converts the result back into the Faceup markup
;; language, and finally compares the result with the original Faceup
;; string.
;;
;; For example:
;;
;;    (defun mylang-font-lock-test (faceup)
;;      (faceup-test-font-lock-string 'mylang-mode faceup))
;;    (faceup-defexplainer mylang-font-lock-test)
;;
;;    (ert-deftest mylang-font-lock-test-simple ()
;;      "Simple MyLang font-lock tests."
;;      (should (mylang-font-lock-test "«k:this» is a keyword"))
;;      (should (mylang-font-lock-test "«k:function» «f:myfunc» («v:var»)")))
;;

;; Executing the tests:
;;
;; Once the tests have been defined, you can use `M-x ert RET t RET'
;; to execute them. Hopefully, you will be given the "all clear".
;; However, if there is a problem, you will be presented with
;; something like:
;;
;;     F mylang-font-lock-file-test
;;         (ert-test-failed
;;          ((should
;;            (mylang-font-lock-test-apps "apps/FirstApp/alpha.mylang"))
;;           :form
;;           (mylang-font-lock-test-apps "apps/FirstApp/alpha.mylang")
;;           :value nil :explanation
;;           ((on-line 2
;;     		("but_«k:this»_is_not_a_keyword")
;;     		("but_this_is_not_a_keyword")))))
;;
;; You should read this that on line 2, the old font-lock rules
;; highlighted `this' inside `but_this_is_not_a_keyword' (which is
;; clearly wrong), whereas the new doesn't. Of course, if this is the
;; desired result (for example, the result of a recent change) you can
;; simply regenerate the .faceup file and store it as the reference
;; file for the future.

;; The Faceup markup language:
;;
;; The Faceup markup language is designed to be human-readable and
;; minimalistic.
;;
;; The two special characters `«' and `»' marks the start and end of a
;; range of a face.
;;
;;
;; Compact format for special faces:
;;
;; The compact format `«<LETTER>:text»' is used for a number of common
;; faces. For example, `«U:abc»' means that the text `abc' is
;; underlined.
;;
;; See `faceup-face-short-alist' for the known faces and the
;; corresponding letter.
;;
;;
;; Full format:
;;
;; The format `«:<NAME OF FACE>:text»' is used use to encode other
;; faces.
;;
;; For example `«:my-special-face:abc»' meanst that `abc' has the face
;; `my-special-face'.
;;
;;
;; Anonymous faces:
;;
;; An "anonymous face" is when the `face' property contains a property
;; list (plist) on the form `(:key value)'. This is represented using
;; a variant of the full format: `«:(:key value):text»'.
;;
;; For example, `«:(:background "red"):abc»' represent the text `abc'
;; with a red background.
;;
;;
;; Multiple properties:
;;
;; In case a text contains more than one face property, they are
;; represented using nested sections.
;;
;; For example:
;;
;; * `«B:abc«U:def»»' represent the text `abcdef' that is both *bold*
;;   and *underlined*.
;;
;; * `«W:abc«U:def»ghi»' represent the text `abcdefghi' where the
;;   entire text is in *warning* face and `def' is *underlined*.
;;
;; In case two faces partially overlap, the ranges will be split when
;; represented in Faceup. For example:
;;
;; * `«B:abc«U:def»»«U:ghi»' represent the text `abcdefghi' where
;;   `abcdef' is bold and `defghi' is underlined.
;;
;;
;; Escaping start and end markers:
;;
;; Any occurrence of the start or end markers in the original text
;; will be escaped using the start marker in the Faceup
;; representation. In other words, the sequences `««' and `«»'
;; represent a start and end marker, respectively.
;;
;;
;; Other properties:
;;
;; In addition to representing the `face' property (or, more
;; correctly, the value of `faceup-default-property') other properties
;; can be encoded. The variable `faceup-properties' contains a list of
;; properties to track. If a property behaves like the `face'
;; property, it is encoded as described above, with the addition of
;; the property name placed in parentheses, for example:
;; `«(my-face)U:abd»'.
;;
;; The variable `faceup-face-like-properties' contains a list of
;; properties considered face-like.
;;
;; Properties that are not considered face-like are always encoded
;; using the full format and the don't nest. For example:
;; `«(my-fibonacci-property):(1 1 2 3 5 8):abd»'.
;;
;; Examples of properties that could be tracked are:
;;
;; * `font-lock-face' -- an alias to `face' when `font-lock-mode' is
;;   enabled.
;;
;; * `syntax-table' -- used by a custom `syntax-propertize' to
;;   override the default syntax table.
;;
;; * `help-echo' -- provides tooltip text displayed when the mouse is
;;   held over a text.

;; Reference section:
;;
;; Faceup commands and functions:
;;
;; `M-x faceup-write-file RET' - generate a Faceup file based on the
;; current buffer.
;;
;; `M-x faceup-view-file RET' - view the current buffer converted to
;; Faceup.
;;
;; `faceup-markup-{string,buffer}' - convert text with properties to
;; the Faceup markup language.
;;
;; `faceup-render-view-buffer' - convert buffer with Faceup markup to
;; a buffer with real text properties and display it.
;;
;; `faceup-render-string' - return string with real text properties
;; from a string with Faceup markup.
;;
;; `faceup-render-to-{buffer,string}' - convert buffer with Faceup
;; markup to a buffer/string with real text properties.
;;
;; `faceup-clean-{buffer,string}' - remove Faceup markup from buffer
;; or string.
;;
;;
;; Regression test support:
;;
;; The following functions can be used as Ert test functions, or can
;; be used to implement new Ert test functions.
;;
;; `faceup-test-equal' - Test function, work like Ert:s `equal', but
;; more ergonomically when reporting multi-line string errors.
;; Concretely, it breaks down multi-line strings into lines and
;; reports which line number the error occurred on and the content of
;; that line.
;;
;; `faceup-test-font-lock-buffer' - Test that a buffer is highlighted
;; according to a reference Faceup text, for a specific major mode.
;;
;; `faceup-test-font-lock-string' - Test that a text with Faceup
;; markup is refontified to match the original Faceup markup.
;;
;; `faceup-test-font-lock-file' - Test that a file is highlighted
;; according to a reference .faceup file.
;;
;; `faceup-defexplainer' - Macro, define an explainer function and set
;; the `ert-explainer' property on the original function, for
;; functions based on the above test functions.
;;
;; `faceup-this-file-directory' - Macro, the directory of the current
;; file.

;; Real-world examples:
;;
;; The following are examples of real-world package that use faceup to
;; test their font-lock keywords.
;;
;; * [cmake-font-lock](https://github.com/Lindydancer/cmake-font-lock)
;;   an advanced set of font-lock keywords for the CMake language
;;
;; * [objc-font-lock](https://github.com/Lindydancer/objc-font-lock)
;;   highlight Objective-C function calls.
;;

;;; Code:

(eval-when-compile
  (require 'cl))


(defvar faceup-default-property 'face
  "The property that should be represented in Faceup without the (prop) part.")

(defvar faceup-properties '(face)
  "List of properties that should be converted to the Faceup format.

Only face-like property use the short format. All other use the
non-nesting full format. (See `faceup-face-like-properties'.)" )


(defvar faceup-face-like-properties '(face font-lock-face)
  "List of properties that behave like `face'.

The following properties are assumed about face-like properties:

* Elements are either symbols or property lists, or lists thereof.

* A plain element and a list containing the same element are
  treated as equal

* Property lists and sequences of property lists are considered
  equal. For example:

     ((:underline t :foreground \"red\"))

  and

     ((:underline t) (:foreground \"red\"))

Face-like properties are converted to faceup in a nesting fashion.

For example, the string AAAXXXAAA (where the property `prop' has
the value `(a)' on the A:s and `(a b)' on the X:s) is converted
as follows, when treated as a face-like property:

    «(prop):a:AAA«(prop):b:XXX»AAAA»

When treated as a non-face-like property:

    «(prop):(a):AAA»«(prop):(a b):XXX»«(prop):(a):AAA»")


(defvar faceup-markup-start-char 171)   ;; «
(defvar faceup-markup-end-char   187)   ;; »

(defvar faceup-face-short-alist
  '(;; Generic faces (uppercase letters)
    (bold                                . "B")
    (bold-italic                         . "Q")
    (default                             . "D")
    (error                               . "E")
    (highlight                           . "H")
    (italic                              . "I")
    (underline                           . "U")
    (warning                             . "W")
    ;; font-lock-specific faces (lowercase letters)
    (font-lock-builtin-face              . "b")
    (font-lock-comment-delimiter-face    . "m")
    (font-lock-comment-face              . "x")
    (font-lock-constant-face             . "c")
    (font-lock-doc-face                  . "d")
    (font-lock-function-name-face        . "f")
    (font-lock-keyword-face              . "k")
    (font-lock-negation-char-face        . "n")
    (font-lock-preprocessor-face         . "p")
    (font-lock-regexp-grouping-backslash . "h")
    (font-lock-regexp-grouping-construct . "o")
    (font-lock-string-face               . "s")
    (font-lock-type-face                 . "t")
    (font-lock-variable-name-face        . "v")
    (font-lock-warning-face              . "w"))
  "Alist from faces to one-character representation.")


;; Plain: «W....»
;; Nested: «W...«W...»»

;; Overlapping:   xxxxxxxxxx
;;                    yyyyyyyyyyyy
;;                «X..«Y..»»«Y...»


(defun faceup-markup-string (s)
  "Return the faceup version of the string S."
  (with-temp-buffer
    (insert s)
    (faceup-markup-buffer)))


;;;###autoload
(defun faceup-view-buffer ()
  "Display the faceup representation of the selected buffer."
  (interactive)
  (let ((buffer (get-buffer-create "*FaceUp*")))
    (with-current-buffer buffer
      (delete-region (point-min) (point-max)))
    (faceup-markup-to-buffer buffer)
    (display-buffer buffer)))


;;;###autoload
(defun faceup-write-file (&optional file-name)
  "Save the faceup representation of the current buffer to the file FILE-NAME.

Unless a name is given, the file will be named xxx.faceup, where
xxx is the file name associated with the buffer."
  (interactive
   (let ((suggested-name (and (buffer-file-name)
                              (concat (buffer-file-name)
                                      ".faceup"))))
     (list (read-file-name "Write faceup file: "
                           default-directory
                           suggested-name
                           nil
                           (file-name-nondirectory suggested-name)))))
  (unless file-name
    (setq file-name (concat (buffer-file-name) ".faceup")))
  (let ((buffer (current-buffer)))
    (with-temp-buffer
      (faceup-markup-to-buffer (current-buffer) buffer)
      ;; Note: Must set `require-final-newline' inside
      ;; `with-temp-buffer', otherwise the value will be overridden by
      ;; the buffers local value.
      ;;
      ;; Clear `window-size-change-functions' as a workaround for
      ;; Emacs bug#19576 (`write-file' saves the wrong buffer if a
      ;; function in the list change current buffer).
      (let ((require-final-newline nil)
            (window-size-change-functions '()))
        (write-file file-name t)))))


(defun faceup-markup-buffer ()
  "Return a string with the content of the buffer using faceup markup."
  (let ((buf (current-buffer)))
    (with-temp-buffer
      (faceup-markup-to-buffer (current-buffer) buf)
      (buffer-substring-no-properties (point-min) (point-max)))))


;; Idea:
;;
;; Typically, only one face is used. However, when two faces are used,
;; the one of top is typically shorter. Hence, the faceup variant
;; should treat the inner group of nested ranges the upper (i.e. the
;; one towards the front.) For example:
;;
;;     «f:aaaaaaa«U:xxxx»aaaaaa»

(defun faceup-copy-and-quote (start end to-buffer)
  "Quote and insert the text between START and END into TO-BUFFER"
  (let ((not-markup (concat "^"
                            (make-string 1 faceup-markup-start-char)
                            (make-string 1 faceup-markup-end-char))))
    (save-excursion
      (goto-char start)
      (while (< (point) end)
        (let ((old (point)))
          (skip-chars-forward not-markup end)
          (let ((s (buffer-substring-no-properties old (point))))
            (with-current-buffer to-buffer
              (insert s))))
        ;; Quote stray markup characters.
        (unless (= (point) end)
          (let ((next-char (following-char)))
            (with-current-buffer to-buffer
              (insert faceup-markup-start-char)
              (insert next-char)))
          (forward-char))))))


(defun faceup-reverse-list-and-split-property-lists (values)
  "Reverse value, and pack :keyword value pairs in a list."
  (let ((res '()))
    (while values
      (let ((value (pop values)))
        (if (listp value)
            (while value
              (let ((key (pop value)))
                ;; Note, missing value issue error!
                (push (list key (pop value)) res)))
          (push value res))))
    res))


(defun faceup-get-text-properties (pos)
  "Alist of properties and values at pos.

Face-like properties are normalized (single elements are
converted to lists and property lists are split into short (KEY
VALUE) lists)."
  (let ((res '()))
    (dolist (prop faceup-properties)
      (let ((value (get-text-property pos prop)))
        (when value
          (when (memq prop faceup-face-like-properties)
            ;; Normalize face-like properties.
            (when (or (not (listp value))
                      (or (keywordp (car value))))
              (setq value (list value)))
            (setq value (faceup-reverse-list-and-split-property-lists value)))
          (push (cons prop value) res))))
    res))


(defun faceup-markup-to-buffer (to-buffer &optional buffer)
  "Convert content of BUFFER to faceup form and insert in TO-BUFFER."
  (save-excursion
    (if buffer
        (set-buffer buffer))
    ;; Font-lock often only fontifies the visible sections. This
    ;; ensures that the entire buffer is fontified before converting
    ;; it.
    (if font-lock-mode
        (font-lock-fontify-region (point-min) (point-max)))
    (let ((last-pos (point-min))
          (pos nil)
          ;; List of (prop . value), representing open faceup blocks.
          (state '()))
      (while (setq pos (faceup-next-property-change pos))
        ;; Insert content.
        (faceup-copy-and-quote last-pos pos to-buffer)
        (setq last-pos pos)
        (let ((prop-values (faceup-get-text-properties pos)))
          (let ((next-state '()))
            (setq state (reverse state))
            ;; Find all existing sequences that should continue.
            (let ((cont t))
              (while (and state
                          prop-values
                          cont)
                (let* ((prop (car (car state)))
                       (value (cdr (car state)))
                       (pair (assq prop prop-values)))
                  (if (memq prop faceup-face-like-properties)
                      ;; Element by element.
                      (if (equal value (car (cdr pair)))
                          (setcdr pair (cdr (cdr pair)))
                        (setq cont nil))
                    ;; Full value.
                    (if (equal value (cdr pair))
                        (setq prop-values (delq pair prop-values))
                      (setq cont nil))))
                (when cont
                  (push (pop state) next-state))))
            ;; End values that should not be included in the next state.
            (while state
              (with-current-buffer to-buffer
                (insert (make-string 1 faceup-markup-end-char)))
              (pop state))
            ;; Start new ranges.
            (with-current-buffer to-buffer
              (while prop-values
                (let ((pair (pop prop-values)))
                  (if (memq (car pair) faceup-face-like-properties)
                      ;; Face-like.
                      (dolist (element (cdr pair))
                        (insert (make-string 1 faceup-markup-start-char))
                        (unless (eq (car pair) faceup-default-property)
                          (insert "(")
                          (insert (symbol-name (car pair)))
                          (insert "):"))
                        (if (symbolp element)
                            (let ((short
                                   (assq element faceup-face-short-alist)))
                              (if short
                                  (insert (cdr short) ":")
                                (insert ":" (symbol-name element) ":")))
                          (insert ":")
                          (prin1 element (current-buffer))
                          (insert ":"))
                        (push (cons (car pair) element) next-state))
                    ;; Not face-like.
                    (insert (make-string 1 faceup-markup-start-char))
                    (insert "(")
                    (insert (symbol-name (car pair)))
                    (insert "):")
                    (prin1 (cdr pair) (current-buffer))
                    (insert ":")
                    (push pair next-state)))))
            ;; Insert content.
            (setq state next-state))))
      ;; Insert whatever is left after the last face change.
      (faceup-copy-and-quote last-pos (point-max) to-buffer))))



;; Some basic facts:
;;
;; (get-text-property (point-max) ...) always return nil. To check the
;; last character in the buffer, use (- (point-max) 1).
;;
;; If a text has more than one face, the first one in the list
;; takes precedence, when being viewed in Emacs.
;;
;;   (let ((s "ABCDEF"))
;;      (set-text-properties 1 4
;;        '(face (font-lock-warning-face font-lock-variable-name-face)) s)
;;      (insert s))
;;
;;   => ABCDEF
;;
;; Where DEF is drawn in "warning" face.


(defun faceup-has-any-text-property (pos)
  "True if any properties in `faceup-properties' are defined at POS."
  (let ((res nil))
    (dolist (prop faceup-properties)
      (when (get-text-property pos prop)
        (setq res t)))
    res))


(defun faceup-next-single-property-change (pos)
  "Next position a property in `faceup-properties' changes, or nil."
  (let ((res nil))
    (dolist (prop faceup-properties)
      (let ((next (next-single-property-change pos prop)))
        (when next
          (setq res (if res
                        (min res next)
                      next)))))
    res))


(defun faceup-next-property-change (pos)
  "Next position after POS where one of the tracked properties change.

If POS is nil, also include `point-min' in the search.
If last character contains a tracked property, return `point-max'.

See `faceup-properties' for a list of tracked properties."
  (if (eq pos (point-max))
      ;; Last search returned `point-max'. There is no more to search
      ;; for.
      nil
    (if (and (null pos)
             (faceup-has-any-text-property (point-min)))
        ;; `pos' is `nil' and the character at `point-min' contains a
        ;; tracked property, return `point-min'.
        (point-min)
      (unless pos
        ;; Start from the beginning.
        (setq pos (point-min)))
      ;; Do a normal search. Compensate for that
      ;; `next-single-property-change' does not include the end of the
      ;; buffer, even when a property reach it.
      (let ((res (faceup-next-single-property-change pos)))
        (if (and (not res)              ; No more found.
                 (not (eq pos (point-max))) ; Not already at the end.
                 (not (eq (point-min) (point-max))) ; Not an empty buffer.
                 (faceup-has-any-text-property (- (point-max) 1)))
            ;; If a property goes all the way to the end of the
            ;; buffer, return `point-max'.
            (point-max)
          res)))))


;; ----------------------------------------------------------------------
;; Renderer
;;

;; Functions to convert from the faceup textual representation to text
;; with real properties.

(defun faceup-render-string (faceup)
  "Return string with properties from FACEUP written with Faceup markup."
  (with-temp-buffer
    (insert faceup)
    (faceup-render-to-string)))


;;;###autoload
(defun faceup-render-view-buffer (&optional buffer)
  "Convert BUFFER containing Faceup markup to a new buffer and display it."
  (interactive)
  (with-current-buffer (or buffer (current-buffer))
    (let ((dest-buffer (get-buffer-create "*FaceUp rendering*")))
      (with-current-buffer dest-buffer
        (delete-region (point-min) (point-max)))
      (faceup-render-to-buffer dest-buffer)
      (display-buffer dest-buffer))))


(defun faceup-render-to-string (&optional buffer)
  "Convert BUFFER containing faceup markup to a string with faces."
  (unless buffer
    (setq buffer (current-buffer)))
  (with-temp-buffer
    (faceup-render-to-buffer (current-buffer) buffer)
    (buffer-substring (point-min) (point-max))))


(defun faceup-render-to-buffer (to-buffer &optional buffer)
  "Convert BUFFER containing faceup markup into text with faces in TO-BUFFER."
  (with-current-buffer (or buffer (current-buffer))
    (goto-char (point-min))
    (let ((last-point (point))
          (state '())                   ; List of (prop . element)
          (not-markup (concat
                       "^"
                       (make-string 1 faceup-markup-start-char)
                       (make-string 1 faceup-markup-end-char))))
      (while (progn
               (skip-chars-forward not-markup)
               (if (not (eq last-point (point)))
                   (let ((text (buffer-substring-no-properties
                                last-point (point)))
                         (prop-elements-alist '()))
                     ;; Accumulate all values for each property.
                     (dolist (prop-element state)
                       (let ((property (car prop-element))
                             (element (cdr prop-element)))
                         (let ((pair (assq property prop-elements-alist)))
                           (unless pair
                             (setq pair (cons property '()))
                             (push pair prop-elements-alist))
                           (push element (cdr pair)))))
                     ;; Apply all properties.
                     (dolist (pair prop-elements-alist)
                       (let ((property (car pair))
                             (elements (reverse (cdr pair))))
                         ;; Create one of:
                         ;;    (property element) or
                         ;;    (property (element element ...))
                         (when (eq (length elements) 1)
                           ;; This ensures that non-face-like
                           ;; properties are restored to their
                           ;; original state.
                           (setq elements (car elements)))
                         (add-text-properties 0 (length text)
                                              (list property elements)
                                              text)))
                     (with-current-buffer to-buffer
                       (insert text))
                     (setq last-point (point))))
               (not (eobp)))
        (if (eq (following-char) faceup-markup-start-char)
            ;; Start marker.
            (progn
              (forward-char)
              (if (or (eq (following-char) faceup-markup-start-char)
                      (eq (following-char) faceup-markup-end-char))
                  ;; Escaped markup character.
                  (progn
                    (setq last-point (point))
                    (forward-char))
                ;; Markup sequence.
                (let ((property faceup-default-property))
                  (when (eq (following-char) ?\( )
                    (forward-char)      ; "("
                    (let ((p (point)))
                      (forward-sexp)
                      (setq property (intern (buffer-substring p (point)))))
                    (forward-char))     ; ")"
                  (let ((element
                         (if (eq (following-char) ?:)
                             ;; :element:
                             (progn
                               (forward-char)
                               (prog1
                                   (let ((p (point)))
                                     (forward-sexp)
                                     ;; Note: (read (current-buffer))
                                     ;; doesn't work, as it reads more
                                     ;; than a sexp.
                                     (read (buffer-substring p (point))))
                                 (forward-char)))
                           ;; X:
                           (prog1
                               (car (rassoc (buffer-substring-no-properties
                                             (point) (+ (point) 1))
                                            faceup-face-short-alist))
                             (forward-char 2)))))
                    (push (cons property element) state)))
                (setq last-point (point))))
          ;; End marker.
          (pop state)
          (forward-char)
          (setq last-point (point)))))))

;; ----------------------------------------------------------------------

;;;###autoload
(defun faceup-clean-buffer ()
  "Remove faceup markup from buffer."
  (interactive)
  (goto-char (point-min))
  (let ((not-markup (concat
                     "^"
                     (make-string 1 faceup-markup-start-char)
                     (make-string 1 faceup-markup-end-char))))
    (while (progn (skip-chars-forward not-markup)
                  (not (eobp)))
      (if (eq (following-char) faceup-markup-end-char)
          ;; End markers are always on their own.
          (delete-char 1)
        ;; Start marker.
        (delete-char 1)
        (if (or (eq (following-char) faceup-markup-start-char)
                (eq (following-char) faceup-markup-end-char))
            ;; Escaped markup character, delete the escape and skip
            ;; the original character.
            (forward-char)
          ;; Property name (if present)
          (if (eq (following-char) ?\( )
              (let ((p (point)))
                (forward-sexp)
                (delete-region p (point))))
          ;; Markup sequence.
          (if (eq (following-char) ?:)
              ;; :value:
              (let ((p (point)))
                (forward-char)
                (forward-sexp)
                (unless (eobp)
                  (forward-char))
                (delete-region p (point)))
            ;; X:
            (delete-char 1)             ; The one-letter form.
            (delete-char 1)))))))       ; The colon.


(defun faceup-clean-string (s)
  (with-temp-buffer
    (insert s)
    (faceup-clean-buffer)
    (buffer-substring (point-min) (point-max))))


;; ----------------------------------------------------------------------
;; Regression test support
;;

(defvar faceup-test-explain nil
  "When non-nil, tester functions returns a text description on failure.

Of course, this only work for test functions aware of this
variable, like `faceup-test-equal' and functions based on this
function.

This is intended to be used to simplify `ert' explain functions,
which could be defined as:

    (defun my-test (args...) ...)
    (defun my-test-explain (args...)
      (let ((faceup-test-explain t))
        (the-test args...)))
    (put 'my-test 'ert-explainer 'my-test-explain)

Alternative, you can use the macro `faceup-defexplainer' as follows:

    (defun my-test (args...) ...)
    (faceup-defexplainer my-test)

Test functions, like `faceup-test-font-lock-buffer', built on top
of `faceup-test-equal', and other functions that adhere to this
variable, can easily define their own explainer functions.")

(defmacro faceup-defexplainer (function)
  "Defines an Ert explainer function for FUNCTION.

FUNCTION must return an explanation when the test fails and
`faceup-test-explain' is set."
  (let ((name (intern (concat (symbol-name function) "-explainer"))))
    `(progn
       (defun ,name (&rest args)
         (let ((faceup-test-explain t))
           (apply (quote ,function) args)))
       (put (quote ,function) 'ert-explainer (quote ,name)))))


;; ------------------------------
;; Multi-line string support.
;;

(defun faceup-test-equal (lhs rhs)
  "Compares two (multi-line) strings, LHS and RHS, for equality.

This is intended to be used in Ert regression test rules.

When `faceup-test-explain' is non-nil, instead of returning nil
on inequality, a list is returned with a explanation what
differs. Currently, this function reports 1) if the number of
lines in the strings differ. 2) the lines and the line numbers on
which the string differed.

For example:
    (let ((a \"ABC\\nDEF\\nGHI\")
          (b \"ABC\\nXXX\\nGHI\\nZZZ\")
          (faceup-test-explain t))
      (message \"%s\" (faceup-test-equal a b)))

    ==> (4 3 number-of-lines-differ (on-line 2 (DEF) (XXX)))

When used in an `ert' rule, the output is as below:

    (ert-deftest faceup-test-equal-example ()
      (let ((a \"ABC\\nDEF\\nGHI\")
            (b \"ABC\\nXXX\\nGHI\\nZZZ\"))
        (should (faceup-test-equal a b))))

    F faceup-test-equal-example
        (ert-test-failed
         ((should
           (faceup-test-equal a b))
          :form
          (faceup-test-equal \"ABC\\nDEF\\nGHI\" \"ABC\\nXXX\\nGHI\\nZZZ\")
          :value nil :explanation
          (4 3 number-of-lines-differ
             (on-line 2
                      (\"DEF\")
                      (\"XXX\")))))"
  (if (equal lhs rhs)
      t
    (if faceup-test-explain
        (let ((lhs-lines (split-string lhs "\n"))
              (rhs-lines (split-string rhs "\n"))
              (explanation '())
              (line 1))
          (unless (= (length lhs-lines) (length rhs-lines))
            (setq explanation (list 'number-of-lines-differ
                                    (length lhs-lines) (length rhs-lines))))
          (while lhs-lines
            (let ((one (pop lhs-lines))
                  (two (pop rhs-lines)))
              (unless (equal one two)
                (setq explanation
                      (cons (list 'on-line line (list one) (list two))
                            explanation)))
              (setq line (+ line 1))))
          (nreverse explanation))
      nil)))

(faceup-defexplainer faceup-test-equal)


;; ------------------------------
;; Font-lock regression test support.
;;

(defun faceup-test-font-lock-buffer (mode faceup &optional buffer)
  "Verify that BUFFER is fontified as FACEUP for major mode MODE.

If BUFFER is not specified the current buffer is used.

Note that the major mode of the buffer is set to MODE and that
the buffer is fontified."
  (save-excursion
    (if buffer
        (set-buffer buffer))
    (funcall mode)
    (font-lock-fontify-region (point-min) (point-max))
    (let ((result (faceup-markup-buffer)))
      (faceup-test-equal faceup result))))

(faceup-defexplainer faceup-test-font-lock-buffer)


(defun faceup-test-font-lock-string (mode faceup)
  "True if FACEUP is re-fontified as the faceup markup for major mode MODE.

The string FACEUP is stripped from markup, inserted into a
buffer, the requested major mode activated, the buffer is
fontified, the result is again converted to the faceup form, and
compared with the original string."
  (with-temp-buffer
    (insert faceup)
    (faceup-clean-buffer)
    (faceup-test-font-lock-buffer mode faceup)))

(faceup-defexplainer faceup-test-font-lock-string)


(defun faceup-test-font-lock-file (mode file)
  "Verify that FILE is fontified as `FILE.faceup' for major mode MODE."
  (let ((faceup (with-temp-buffer
                  (insert-file-contents (concat file ".faceup"))
                  (buffer-substring-no-properties (point-min) (point-max)))))
    (with-temp-buffer
      (insert-file-contents file)
      (faceup-test-font-lock-buffer mode faceup))))

(faceup-defexplainer faceup-test-font-lock-file)


;; ------------------------------
;; Get current file directory. Test cases can use this to locate test
;; files.
;;

(defun faceup-this-file-directory ()
  "The directory of the file where the call to this function is located in.
Intended to be called when a file is loaded."
  (expand-file-name
   (if load-file-name
       ;; File is being loaded.
       (file-name-directory load-file-name)
     ;; File is being evaluated using, for example, `eval-buffer'.
     default-directory)))


;; ----------------------------------------------------------------------
;; The end
;;

(provide 'faceup)

;;; faceup.el ends here
