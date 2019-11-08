;;; langtool.el --- Grammar check utility using LanguageTool

;; Author: Masahiro Hayashi <mhayashi1120@gmail.com>
;; Keywords: docs
;; Package-Version: 2.0.0
;; URL: https://github.com/mhayashi1120/Emacs-langtool
;; Emacs: GNU Emacs 24 or later
;; Version: 2.0.0
;; Package-Requires: ((cl-lib "0.3"))

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; ## Install:

;; Install LanguageTool version 3.0 or later (and java)
;; http://www.languagetool.org/

;; Put this file into load-path'ed directory, and byte compile it if
;; desired. And put the following expression into your ~/.emacs.
;;
;;     (setq langtool-language-tool-jar "/path/to/languagetool-commandline.jar")
;;     (require 'langtool)
;;
;; Alternatively, you can set the classpath where LanguageTool's jars reside:
;;
;;     (setq langtool-java-classpath
;;           "/usr/share/languagetool:/usr/share/java/languagetool/*")
;;     (require 'langtool)
;;
;; You can use HTTP server implementation which is now testing.  This
;; is very fast, but has security risk if there is multiple user on a
;; same host. You can set both of
;; `langtool-language-tool-jar' and `langtool-language-tool-server-jar'
;; the later is prior than the former.
;; [Recommended] You should set `langtool-language-tool-jar' correctly
;;    full of completion support like available languages.
;;
;;     (setq langtool-language-tool-server-jar "/path/to/languagetool-server.jar")

;; You can change HTTP server port number like following.
;;
;;     (setq langtool-server-user-arguments '("-p" "8082"))

;; These settings are optional:

;; * Key binding if you desired.
;;
;;     (global-set-key "\C-x4w" 'langtool-check)
;;     (global-set-key "\C-x4W" 'langtool-check-done)
;;     (global-set-key "\C-x4l" 'langtool-switch-default-language)
;;     (global-set-key "\C-x44" 'langtool-show-message-at-point)
;;     (global-set-key "\C-x4c" 'langtool-correct-buffer)

;; * Default language is detected by LanguageTool automatically.
;;   Please set `langtool-default-language` if you need specific language.
;;
;;     (setq langtool-default-language "en-US")
;;
;;   Otherwise, invoke `M-x langtool-check` with `C-u` (universal-argument)

;; * Currently GNU java version is not working.
;;   Please change the variable to your favorite java executable.
;;
;;     (setq langtool-java-bin "/path/to/java")

;; * Maybe your LanguageTool have launcher. (e.g. Gentoo)
;;   You need to set `langtool-bin'.
;;   See https://github.com/mhayashi1120/Emacs-langtool/issues/24
;;
;;     (setq langtool-bin "/usr/bin/languagetool")

;; * Maybe you want to specify your mother tongue.
;;
;;     (setq langtool-mother-tongue "en")

;; * To customize LanguageTool commandline arguments.
;;
;;     (setq langtool-java-user-arguments '("-Dfile.encoding=UTF-8"))
;;
;;   You can also make the variable to buffer local like following:
;;
;;     (add-hook '**SOME**-mode-hook
;;               (lambda () (set (make-local-variable 'langtool-java-user-arguments)
;;                              '("-Dfile.encoding=UTF-8"))))
;;
;;   NOTE: Although there is no good example, `langtool-user-arguments' is
;;   a similar custom variable.

;; ## Usage:

;; * To check current buffer and show warnings.
;;
;;     M-x langtool-check
;;
;;   Check with different language. You can complete supported language
;;   with C-i/TAB
;;
;;     C-u M-x langtool-check

;; * To correct marker follow LanguageTool suggestions.
;;
;;     M-x langtool-correct-buffer

;; * Go to warning point you can see a report from LanguageTool.
;;   Otherwise:
;;
;;     M-x langtool-show-message-at-point

;; * Show LanguageTool report automatically by `popup'
;;   This idea come from:
;;   http://d.hatena.ne.jp/LaclefYoshi/20150912/langtool_popup
;;
;;     (defun langtool-autoshow-detail-popup (overlays)
;;       (when (require 'popup nil t)
;;         ;; Do not interrupt current popup
;;         (unless (or popup-instances
;;                     ;; suppress popup after type `C-g' .
;;                     (memq last-command '(keyboard-quit)))
;;           (let ((msg (langtool-details-error-message overlays)))
;;             (popup-tip msg)))))
;;
;;     (setq langtool-autoshow-message-function
;;           'langtool-autoshow-detail-popup)

;; * To finish checking. All langtool marker is removed.
;;
;;     M-x langtool-check-done

;;; TODO:

;; * process coding system (test on Windows)
;; * check only docstring (emacs-lisp-mode)
;;    or using (derived-mode-p 'prog-mode) and only string and comment
;; * java encoding <-> elisp encoding (No enough information..)
;; * change to --json argument to parse. 

;;; Code:


(require 'cl-lib)
(require 'compile)
(require 'json)
(require 'pcase)

(defgroup langtool nil
  "Customize langtool"
  :prefix "langtool-"
  :group 'applications)

;;;
;;; Variables / Faces
;;;

;;
;; constants
;;

(defconst langtool-output-regexp
  (eval-when-compile
    (concat
     "^[0-9]+\\.) Line \\([0-9]+\\), column \\([0-9]+\\), Rule ID: \\(.*\\)\n"
     "Message: \\(.*\\)\n"
     "\\(?:Suggestion: \\(.*\\)\n\\)?"
     ;; As long as i can read
     ;; src/dev/de/danielnaber/languagetool/dev/wikipedia/OutputDumpHandler.java
     "\\(\\(?:.*\\)\n\\(?:[ ^]+\\)\\)\n"
     "\n?"                              ; last result have no new-line
     )))

;;
;; externals
;;

(defvar current-prefix-arg)
(defvar unread-command-events)
(defvar locale-language-names)

;;
;; faces
;;

(defface langtool-errline
  '((((class color) (background dark)) (:background "Firebrick4"))
    (((class color) (background light)) (:background "LightPink"))
    (t (:bold t)))
  "Face used for marking error lines."
  :group 'langtool)

(defface langtool-correction-face
  '((((class mono)) (:inverse-video t :bold t :underline t))
    (t (:background "red1" :foreground "yellow" :bold t)))
  "Face used to visualize correction."
  :group 'langtool)

;;
;; customize variables
;;

(defcustom langtool-java-bin "java"
  "Executing java command."
  :group 'langtool
  :type 'file)

(defcustom langtool-bin nil
  "Executing LanguageTool command."
  :group 'langtool
  :type 'file)

(defcustom langtool-java-user-arguments nil
  "List of string which is passed to java command as arguments.
This java command holds LanguageTool process.
Otherwise, function which return above value.

e.g. ( Described at http://wiki.languagetool.org/command-line-options )
\(setq langtool-java-user-arguments '(\"-Dfile.encoding=UTF-8\"))

"
  :group 'langtool
  :type '(choice
          (repeat string)
          function))

(defcustom langtool-language-tool-jar nil
  "LanguageTool jar file.

No need to set this variable when `langtool-java-classpath' is set."
  :group 'langtool
  :type 'file)

(defcustom langtool-language-tool-server-jar nil
  "LanguageTool server jar file. **This is now TESTING**.
Very fast, but do not use it if there is unreliable user on a same host."
  :group 'langtool
  :type 'file)

(defcustom langtool-java-classpath nil
  "Custom classpath to use on special environment. (e.g. Arch Linux)
Do not set both of this variable and `langtool-language-tool-jar'.

https://github.com/mhayashi1120/Emacs-langtool/pull/12
https://github.com/mhayashi1120/Emacs-langtool/issues/8"
  :group 'langtool
  :type 'string)

(defcustom langtool-default-language nil
  "Language name pass to LanguageTool command.
This is string which indicate locale or `auto' or `nil'.
Currently `auto' and `nil' is a same meaning."
  :group 'langtool
  :type '(choice
          string
          (const auto)
          (const nil)))

(defcustom langtool-mother-tongue nil
  "Your mothertongue Language name pass to LanguageTool."
  :group 'langtool
  :type 'string)

(defcustom langtool-disabled-rules nil
  "Disabled rules pass to LanguageTool.
String that separated by comma or list of string.
"
  :group 'langtool
  :type '(choice
          (list string)
          string))

(defcustom langtool-user-arguments nil
  "Similar to `langtool-java-user-arguments' except this list is appended
 after `-jar' argument.

Valid values are described below:
http://wiki.languagetool.org/command-line-options

Do not change this variable if you don't understand what you are doing.
"
  :group 'langtool
  :type '(choice
          (repeat string)
          function))

(defcustom langtool-server-user-arguments nil
  "`langtool-language-tool-server-jar' customize arguments.
You can pass `--config' option to the server that indicate java property file.

You can see all valid arguments with following command (Replace path by yourself):
java -jar /path/to/languagetool-server.jar --help
"
  :group 'langtool
  :type '(choice
          (repeat string)
          function))

(defcustom langtool-client-filter-query-function nil
  "Filter function that accept one query form argument.
This query form is an alist will be encoded by `url-build-query-string'.
Call just before POST with `application/x-www-form-urlencoded'."
  :group 'langtool
  :type 'function)

(defcustom langtool-error-exists-hook
  '(langtool-autoshow-ensure-timer)
  "Hook run after LanguageTool process found any error(s)."
  :group 'langtool
  :type 'hook)

(defcustom langtool-noerror-hook nil
  "Hook run after LanguageTool report no error."
  :group 'langtool
  :type 'hook)

(defcustom langtool-finish-hook
  '(langtool-autoshow-cleanup-timer-maybe)
  "Hook run after cleanup buffer."
  :group 'langtool
  :type 'hook)

;;
;; local variables
;;
(defvar langtool-generic-check-predicate nil
  "Function providing per-mode customization over which regions are checked.
The \"start\" and \"end\" is passed as parameters of predicate.
Returns t to continue checking, nil otherwise.")
(make-variable-buffer-local 'langtool-generic-check-predicate)

(defvar langtool-local-disabled-rules nil)
(make-variable-buffer-local 'langtool-local-disabled-rules)

(defvar langtool-temp-file nil)
(make-variable-buffer-local 'langtool-temp-file)

(defvar langtool-buffer-process nil)
(make-variable-buffer-local 'langtool-buffer-process)

(defvar langtool-mode-line-message nil)
(make-variable-buffer-local 'langtool-mode-line-message)
(put 'langtool-mode-line-message 'risky-local-variable t)

(defvar langtool-mode-line-process nil)
(make-variable-buffer-local 'langtool-mode-line-process)
(put 'langtool-mode-line-process 'risky-local-variable t)

(defvar langtool-mode-line-server-process nil)
(put 'langtool-mode-line-server-process 'risky-local-variable t)

(defvar langtool-error-buffer-name " *LanguageTool Errors* ")

(defvar langtool--debug nil)

(defvar langtool--correction-keys
  ;; (q)uit, (c)lear, (e)dit, (i)gnore
  [?0 ?1 ?2 ?3 ?4 ?5 ?6 ?7 ?8 ?9
      ;; suggestions may over 10.
      ;; define rest of alphabet just in case.
      ?a ?b ?d ?f ?g ?h ?j ?k ?l ?m ?n
      ?o ?p ?r ?s ?t ?u ?v ?w ?x ?y ?z])

;;;
;;; Internal functions
;;;

;;
;; basic functions
;;

(defun langtool-region-active-p ()
  (cond
   ((fboundp 'region-active-p)
    (funcall 'region-active-p))
   (t
    (and transient-mark-mode mark-active))))

(defun langtool--debug (key fmt &rest args)
  (when langtool--debug
    (let ((buf (get-buffer-create "*Langtool Debug*")))
      (with-current-buffer buf
        (goto-char (point-max))
        (insert "---------- [" key "] ----------\n")
        (insert (apply 'format fmt args) "\n")))))

(defun langtool--chomp (s)
  (if (string-match "\\(?:\\(\r\n\\)+\\|\\(\n\\)+\\)\\'" s)
      (substring s 0 (match-beginning 0))
    s))

(defun langtool--make-temp-file ()
  (make-temp-file "langtool-"))

;;
;; HTTP basic
;;

(defun langtool-http--parse-response-header ()
  ;; Not a exact parser. Just a necessary. ;-)
  (save-excursion
    (goto-char (point-min))
    (unless (re-search-forward "^\r\n" nil t)
      (error "Parse error. Not found http header separator."))
    (let (status headers body-start)
      (setq body-start (point))
      (forward-line -1)
      (save-restriction
        (narrow-to-region (point-min) (point))
        (goto-char (point-min))
        (unless (looking-at "^HTTP/[0-9.]+[\s\t]+\\([0-9]+\\)")
          (error "Parse error. Not found HTTP status code"))
        (setq status (string-to-number (match-string-no-properties 1)))
        (forward-line)
        (while (not (eobp))
          (let (key value)
            (unless (looking-at "^\\([^:]+\\):")
              (error "Invalid header of HTTP response"))
            (setq key (match-string-no-properties 1))
            (goto-char (match-end 0))
            (while (looking-at "[\s\t]+\\(.*\\)\r")
              (setq value (concat value (match-string-no-properties 1)))
              (forward-line 1))
            (setq headers (cons (cons key value) headers))))
        (list status headers body-start)))))

;;
;; handle error overlay
;;

;;FIXME
;;http://sourceforge.net/tracker/?func=detail&aid=3054895&group_id=110216&atid=655717
(defun langtool--fuzzy-search (context-regexp length)
  (let* ((regexp (concat ".*?" context-regexp))
         (default (cons (point) (+ (point) length))))
    (or (and (null regexp)
             (cons (point) (+ (point) length)))
        (and (looking-at regexp)
             (cons (match-beginning 1) (match-end 1)))
        (let ((beg (min (point-at-bol) (- (point) 20))))
          (cl-loop while (and (not (bobp))
                              (<= beg (point)))
                   ;; backward just sentence length to search sentence after point
                   do (condition-case nil
                          (backward-char length)
                        (beginning-of-buffer nil))
                   if (looking-at regexp)
                   return (cons (match-beginning 1) (match-end 1))))
        default)))

(defun langtool--compute-start&end (version check)
  (let ((line (nth 0 check))
        (col (nth 1 check))
        (len (nth 2 check))
        (context (nth 7 check))
        ;; Only Server <-> Client have the data
        (offset (nth 8 check)))
    (cond
     (offset
      (let* ((start (+ (point-min) offset))
             (end (+ start len)))
        (cons start end)))
     (t
      (goto-char (point-min))
      (forward-line (1- line))
      (forward-char col)
      (cons (point) (+ (point) len))))))

(defun langtool--create-overlay (version check)
  (cl-destructuring-bind (start . end)
      (langtool--compute-start&end version check)
    (unless (and langtool-generic-check-predicate
                 (not (funcall langtool-generic-check-predicate start end)))
      (let ((ov (make-overlay start end)))
        (overlay-put ov 'langtool-simple-message (nth 4 check))
        (overlay-put ov 'langtool-message (nth 5 check))
        (overlay-put ov 'langtool-suggestions (nth 3 check))
        (overlay-put ov 'langtool-rule-id (nth 6 check))
        (overlay-put ov 'priority 1)
        (overlay-put ov 'face 'langtool-errline)))))

(defun langtool--clear-buffer-overlays ()
  (mapc
   (lambda (ov)
     (delete-overlay ov))
   (langtool--overlays-region (point-min) (point-max))))

(defun langtool--overlays-region (start end)
  (sort
   (remove
    nil
    (mapcar
     (lambda (ov)
       (when (overlay-get ov 'langtool-message)
         ov))
     (overlays-in start end)))
   (lambda (ov1 ov2)
     (< (overlay-start ov1) (overlay-start ov2)))))

(defun langtool--current-error-overlays ()
  (remove nil
          (mapcar
           (lambda (ov)
             (and (overlay-get ov 'langtool-message)
                  ov))
           (overlays-at (point)))))

(defun langtool--expire-buffer-overlays ()
  (mapc
   (lambda (o)
     (unless (overlay-get o 'face)
       (delete-overlay o)))
   (langtool--overlays-region (point-min) (point-max))))

(defun langtool--erase-overlay (ov)
  (overlay-put ov 'face nil))

(defun langtool--next-overlay (current overlays)
  (cl-loop for o in (cdr (memq current overlays))
           if (overlay-get o 'face)
           return o))

(defun langtool--prev-overlay (current overlays)
  (cl-loop for o in (cdr (memq current (reverse overlays)))
           if (overlay-get o 'face)
           return o))

(defun langtool--goto-error (overlays predicate)
  (catch 'done
    (mapc
     (lambda (ov)
       (when (funcall predicate ov)
         (goto-char (overlay-start ov))
         (throw 'done t)))
     overlays)
    nil))

(defun langtool-working-p ()
  (cl-loop with current = (current-buffer)
           for buf in (buffer-list)
           when (and (not (eq buf current))
                     (with-current-buffer buf
                       (langtool--overlays-region
                        (point-min) (point-max))))
           return buf
           finally return nil))

;;
;; utility
;;

(defun langtool-simple-error-message (overlays)
  "Textify error messages as long as simple."
  (mapconcat
   (lambda (ov)
     (format
      "[%s] %s%s"
      (overlay-get ov 'langtool-rule-id)
      (overlay-get ov 'langtool-simple-message)
      (if (overlay-get ov 'langtool-suggestions)
          (concat
           " -> ("
           (mapconcat 'identity (overlay-get ov 'langtool-suggestions) ", ")
           ")")
        "")))
   overlays "\n"))

(defun langtool-details-error-message (overlays)
  "Textify error messages."
  (mapconcat
   (lambda (ov)
     (concat
      (format "Rule ID: %s\n"
              (overlay-get ov 'langtool-rule-id))
      (format "Message: %s\n"
              (overlay-get ov 'langtool-simple-message))
      (if (overlay-get ov 'langtool-suggestions)
          (concat
           "Suggestions: "
           (mapconcat
            'identity
            (overlay-get ov 'langtool-suggestions)
            "; "))
        "")))
   overlays
   "\n\n"))

(defun langtool--current-error-messages ()
  (mapcar
   (lambda (ov)
     (overlay-get ov 'langtool-message))
   (langtool--current-error-overlays)))

;;;
;;; LanguageTool Process
;;;

;;
;; Process basic
;;

(defmacro langtool--with-java-environ (&rest form)
  `(let ((coding-system-for-read langtool-process-coding-system))
     (progn ,@form)))

(defun langtool--process-file-name (path)
  "Correct the file name depending on the underlying platform.

PATH: The file-name path to be corrected.

Currently corrects the file-name-path when running under Cygwin."
  (setq path (expand-file-name path))
  (cond
   ((eq system-type 'cygwin)
    ;; no need to catch error. (e.g. cygpath is not found)
    ;; this failure means LanguageTools is not working completely.
    (with-temp-buffer
      (call-process "cygpath" nil t nil "--windows" path)
      (langtool--chomp (buffer-string))))
   (t
    path)))

(defcustom langtool-process-coding-system
  (cond
   ((eq system-type 'cygwin)
    'dos)
   (t nil))
  "LanguageTool process coding-system.
Ordinary no need to change this."
  :group 'langtool
  :type 'coding-system)

(defun langtool--custom-arguments (var)
  (let ((value (symbol-value var))
        args)
    (cond
     ((functionp value)
      (setq args (funcall value)))
     ((consp value)
      (setq args value)))
    (copy-sequence args)))

;;
;; Command interaction
;;

(defun langtool--disabled-rules ()
  (let ((custom langtool-disabled-rules)
        (locals langtool-local-disabled-rules))
    (cond
     ((stringp custom)
      (mapconcat 'identity
                 (cons custom locals)
                 ","))
     (t
      (mapconcat 'identity
                 (append custom locals)
                 ",")))))

(defun langtool--basic-command&args ()
  (cond
   (langtool-bin
    (list langtool-bin nil))
   (t
    (let (command args)
      (setq command langtool-java-bin)
      ;; Construct arguments pass to java command
      (setq args (langtool--custom-arguments 'langtool-java-user-arguments))
      (cond
       (langtool-java-classpath
        (setq args (append
                    args
                    (list "-cp" langtool-java-classpath
                          "org.languagetool.commandline.Main")))
        (list command args))
       (langtool-language-tool-jar
        (setq args (append
                    args
                    (list "-jar" (langtool--process-file-name langtool-language-tool-jar))))
        (list command args))
       (t nil))))))

(defun langtool--process-create-client-buffer ()
  (generate-new-buffer " *Langtool* "))

(defun langtool--sentence-to-fuzzy (sentence)
  (mapconcat 'regexp-quote
             ;; this sentence is reported by LanguageTool
             (split-string sentence " +")
             ;; LanguageTool interpreted newline as space.
             "[[:space:]\n]+?"))

(defun langtool--pointed-length (message)
  (or
   (and (string-match "\n\\( *\\)\\(\\^+\\)" message)
        (length (match-string 2 message)))
   ;; never through here, but if return nil from this function make stop everything.
   1))

;;FIXME sometimes LanguageTool reports wrong column.
(defun langtool--pointed-context-regexp (message)
  (when (string-match "\\(.*\\)\n\\( *\\)\\(\\^+\\)" message)
    (let* ((msg1 (match-string 1 message))
           ;; calculate marker "^" start at column
           (pre (length (match-string 2 message)))
           ;; "^" marker length
           (len (length (match-string 3 message)))
           (end (+ pre len))
           (sentence (substring msg1 pre end))
           (regexp (cond
                    ((string-match "^[[:space:]]+$" sentence)
                     ;; invalid sentence only have whitespace,
                     ;; search with around sentence.
                     (concat
                      "\\("
                      (let* ((count (length sentence))
                             (spaces (format "[[:space:]\n]\\{%d\\}" count)))
                        spaces)
                      "\\)"
                      ;; considered truncated spaces that is caused by
                      ;; `langtool--sentence-to-fuzzy'
                      "[[:space:]]*?"
                      ;; to match the correct block
                      ;; suffix of invalid spaces.
                      (langtool--sentence-to-fuzzy
                       (let ((from (min end (length msg1))))
                         ;;TODO magic number.
                         (substring msg1 from (min (length msg1) (+ from 20)))))))
                    (t
                     (concat "\\("
                             (langtool--sentence-to-fuzzy sentence)
                             "\\)")))))
      regexp)))

;;
;; Commandline / HTTP integration
;;

(defun langtool--checker-mode ()
  (cond
   (langtool-language-tool-server-jar
    'http)
   ((or langtool-language-tool-jar
        langtool-java-classpath)
    'commandline)
   (t
    (error "There is no valid setting."))))

(defun langtool--apply-checks (proc checks)
  (let ((source (process-get proc 'langtool-source-buffer))
        (version (process-get proc 'langtool-jar-version))
        (begin (process-get proc 'langtool-region-begin))
        (finish (process-get proc 'langtool-region-finish)))
    (when (buffer-live-p source)
      (with-current-buffer source
        (save-excursion
          (save-restriction
            (when (and begin finish)
              (narrow-to-region begin finish))
            (mapc
             (lambda (check)
               (langtool--create-overlay version check))
             (nreverse checks))))))))

(defun langtool--lazy-apply-checks (proc checks)
  (let ((source (process-get proc 'langtool-source-buffer))
        (version (process-get proc 'langtool-jar-version))
        (begin (process-get proc 'langtool-region-begin))
        (finish (process-get proc 'langtool-region-finish)))
    (when (buffer-live-p source)
      (with-current-buffer source
        (save-excursion
          (save-restriction
            (when (and begin finish)
              (narrow-to-region begin finish))
            (cond
             ((consp checks)
              (langtool--create-overlay version (car checks))
              (run-with-idle-timer
               1 nil 'langtool--lazy-apply-checks
               proc (cdr checks)))
             (t
              (let ((source (process-get proc 'langtool-source-buffer)))
                (langtool--check-finish source nil))))))))))

(defun langtool--check-finish (source errmsg)
  (let (marks face)
    (when (buffer-live-p source)
      (with-current-buffer source
        (setq marks (langtool--overlays-region (point-min) (point-max)))
        (setq face (cond
                    (errmsg
                     compilation-error-face)
                    (marks
                     compilation-warning-face)
                    (t
                     compilation-info-face)))
        (setq langtool-buffer-process nil)
        (setq langtool-mode-line-process
              (propertize ":exit" 'face face))
        (cond
         (errmsg
          (message "%s" errmsg))
         (marks
          (run-hooks 'langtool-error-exists-hook)
          (message "%s"
                   (substitute-command-keys
                    "Type \\[langtool-correct-buffer] to correct buffer.")))
         (t
          (run-hooks 'langtool-noerror-hook)
          (message "LanguageTool successfully finished with no error.")))))))

;;
;; LanguageTool Commandline
;;

(defun langtool-command--check-command ()
  (cond
   (langtool-bin
    (unless (executable-find langtool-bin)
      (error "LanguageTool command not executable")))
   ((or (null langtool-java-bin)
        (not (executable-find langtool-java-bin)))
    (error "java command is not found")))
  (cond
   (langtool-java-classpath)
   (langtool-language-tool-jar
    (unless (file-readable-p langtool-language-tool-jar)
      (error "langtool jar file is not readable"))))
  (when langtool-buffer-process
    (error "Another process is running")))

(defun langtool-command--invoke-process (file begin finish &optional lang)
  (let ((version (langtool--jar-version)))
    (cl-destructuring-bind (command args)
        (langtool--basic-command&args)
      ;; Construct arguments pass to jar file.
      ;; http://wiki.languagetool.org/command-line-options
      (setq args (append
                  args
                  (list "-c" (langtool--java-coding-system
                              buffer-file-coding-system)
                        "-d" (langtool--disabled-rules))))
      (cond
       ((stringp (or lang langtool-default-language))
        (setq args (append args (list "-l" (or lang langtool-default-language)))))
       (t
        (setq args (append args (list "--autoDetect")))))
      (when langtool-mother-tongue
        (setq args (append args (list "-m" langtool-mother-tongue))))
      (setq args (append args (langtool--custom-arguments 'langtool-user-arguments)))
      (setq args (append args (list (langtool--process-file-name file))))
      (langtool--debug "Command" "%s: %s" command args)
      (let* ((buffer (langtool--process-create-client-buffer))
             (proc (langtool--with-java-environ
                    (apply 'start-process "LanguageTool" buffer command args))))
        (set-process-filter proc 'langtool-command--process-filter)
        (set-process-sentinel proc 'langtool-command--process-sentinel)
        (process-put proc 'langtool-source-buffer (current-buffer))
        (process-put proc 'langtool-region-begin begin)
        (process-put proc 'langtool-region-finish finish)
        (process-put proc 'langtool-jar-version version)
        proc))))

(defun langtool-command--process-filter (proc event)
  (langtool--debug "Filter" "%s" event)
  (with-current-buffer (process-buffer proc)
    (goto-char (point-max))
    (insert event)
    (let ((min (or (process-get proc 'langtool-process-done)
                   (point-min)))
          checks)
      (goto-char min)
      (while (re-search-forward langtool-output-regexp nil t)
        (let* ((line (string-to-number (match-string 1)))
               (column (1- (string-to-number (match-string 2))))
               (rule-id (match-string 3))
               (suggest (match-string 5))
               (msg1 (match-string 4))
               ;; rest of line. Point the raw message.
               (msg2 (match-string 6))
               (message
                (concat "Rule ID: " rule-id "\n"
                        msg1 "\n\n"
                        msg2))
               (suggestions (and suggest (split-string suggest "; ")))
               (context (langtool--pointed-context-regexp msg2))
               (len (langtool--pointed-length msg2)))
          (setq checks (cons
                         (list line column len suggestions
                               msg1 message rule-id context)
                         checks))))
      (process-put proc 'langtool-process-done (point))
      (langtool--apply-checks proc checks))))

(defun langtool-command--process-sentinel (proc event)
  (unless (process-live-p proc)
    (let ((code (process-exit-status proc))
          (pbuf (process-buffer proc))
          (source (process-get proc 'langtool-source-buffer))
          dead marks errmsg face)
      (cond
       ((buffer-live-p pbuf)
        (when (/= code 0)
          ;; Get first line of output.
          (with-current-buffer pbuf
            (goto-char (point-min))
            (setq errmsg
                  (format "LanguageTool exited abnormally with code %d (%s)"
                          code (buffer-substring (point) (point-at-eol))))))
        (kill-buffer pbuf))
       (t
        (setq errmsg "Buffer was dead")))
      (langtool--check-finish source errmsg))))

;;
;; LanguageTool HTTP Server <-> Client
;;

(defvar langtool-server--process nil)

(defun langtool-server--check-command ()
  (cond
   ((or (null langtool-java-bin)
        (not (executable-find langtool-java-bin)))
    (error "java command is not found")))
  (unless langtool-language-tool-server-jar
    (error "Please set `langtool-language-tool-server-jar'"))
  (unless (file-readable-p langtool-language-tool-server-jar)
    (error "languagetool-server jar file is not readable")))

(defun langtool-server-ensure-stop (&optional proc)
  (setq proc (or proc langtool-server--process))
  (when (processp proc)
    (let ((buffer (process-buffer proc)))
      (delete-process proc)
      (when (buffer-live-p buffer)
        (kill-buffer buffer))))
  (setq langtool-server--process nil))

(defun langtool-server--parse-initial-buffer ()
  (save-excursion
    (goto-char (point-min))
    (cond
     ((re-search-forward (eval-when-compile
                           (concat
                            "^"
                            "Starting LanguageTool "
                            "\\([0-9.]+\\)\\(?:-SNAPSHOT\\)? "
                            ".+?"
                            "server on https?://\\([^:]+\\):\\([0-9]+\\)"
                            "\.\.\."
                            "$"))
                         nil t))
     (t
      (error "Unable parse initial buffer")))
    (let ((version (match-string 1))
          (host (match-string 2))
          (port (string-to-number (match-string 3))))
      (list version host port))))

(defun langtool-server--rendezvous (proc buffer)
  (message "Waiting for server")
  (catch 'rendezvous
    (with-current-buffer buffer
      (save-excursion
        (while t
          (goto-char (point-min))
          (when (re-search-forward "^Server started" nil t)
            (cl-destructuring-bind (version host port)
                (langtool-server--parse-initial-buffer)
              (when (version< version "4.0")
                (langtool-server-ensure-stop proc)
                (error "LanguageTool Server version must be than 4.0 but now %s"
                       version))
              (process-put proc 'langtool-server-host host)
              (process-put proc 'langtool-server-port port)
              (process-put proc 'langtool-jar-version version)
              (message "%s done." (current-message))
              (throw 'rendezvous t)))
          (unless (eq (process-status proc) 'run)
            (langtool-server-ensure-stop proc)
            (error "Failed to start LanguageTool Server."))
          (message "%s." (current-message))
          (accept-process-output proc 0.1 nil t))))))

(defvar langtool-server--process-exit-hook nil)

(defun langtool-server--process-sentinel (proc event)
  (unless (process-live-p proc)
    (run-hooks 'langtool-server--process-exit-hook)))

(defun langtool-server--ensure-running ()
  (langtool-server--check-command)
  (unless (and (processp langtool-server--process)
               (eq (process-status langtool-server--process) 'run))
    (setq langtool-server--process nil)
    (let* ((args '()))
      ;; jar Default setting is "HTTPSServer" .
      ;; This application no need to use SSL since local app.
      ;; http://wiki.languagetool.org/http-server
      (setq args (append args (list "org.languagetool.server.HTTPServer")))
      (setq args (append args langtool-server-user-arguments))
      (let* ((buffer (get-buffer-create " *LangtoolHttpServer* "))
             (proc (apply
                    'start-process
                    "LangtoolHttpServer" buffer
                    langtool-java-bin
                    "-cp" (langtool--process-file-name
                           langtool-language-tool-server-jar)
                    args)))
        (langtool-server--rendezvous proc buffer)
        (set-process-sentinel proc 'langtool-server--process-sentinel)
        (setq langtool-server--process proc))))
  langtool-server--process)

(defun langtool-client--parse-response-body/json ()
  (let* ((json (json-read))
         (matches (cdr (assoc 'matches json)))
         checks)
    (cl-loop for match across matches
             do (let* ((offset (cdr (assoc 'offset match)))
                       (len (cdr (assoc 'length match)))
                       (rule (cdr (assoc 'rule match)))
                       (rule-id (cdr (assoc 'id rule)))
                       (replacements (cdr (assoc 'replacements match)))
                       (suggestions (mapcar (lambda (x) (cdr (assoc 'value x))) replacements))
                       (msg1 (cdr (assoc 'message match)))
                       ;; rest of line. Point the raw message.
                       (msg2 (cdr (assoc 'shortMessage match)))
                       (message
                        (concat "Rule ID: " rule-id "\n"
                                msg1 "\n\n"
                                msg2))
                       (context nil)
                       line column)
                  (setq checks (cons
                                 (list line column len suggestions
                                       msg1 message rule-id context
                                       offset)
                                 checks))))
    (nreverse checks)))

(defun langtool-client--parse-response-body (http-headers)
  (let ((ct (cdr (assoc-string "content-type" http-headers t))))
    (cond
     ((string= ct "application/json")
      (langtool-client--parse-response-body/json))
     (t
      (error "Not a supported Content-Type %s" ct)))))

(defun langtool-client--process-sentinel (proc event)
  (unless (process-live-p proc)
    (let ((pbuf (process-buffer proc))
          (source (process-get proc 'langtool-source-buffer))
          errmsg checks)
      (with-current-buffer pbuf
        (cl-destructuring-bind (status headers body-start)
            (langtool-http--parse-response-header)
          (goto-char body-start)
          (cond
           ((= status 200)
            (setq checks (langtool-client--parse-response-body headers)))
           (t
            (setq errmsg (buffer-substring-no-properties (point) (point-max)))))
          (kill-buffer pbuf)))
      (cond
       (errmsg
        (langtool--check-finish source errmsg))
       (t
        (langtool--lazy-apply-checks proc checks))))))

(defun langtool-client--process-filter (proc event)
  (langtool--debug "Filter" "%s" event)
  (with-current-buffer (process-buffer proc)
    (goto-char (point-max))
    (insert event)))

(defun langtool-client--make-post-data (file begin finish lang)
  (let (text)
    (with-temp-buffer
      (insert-file-contents file)
      (setq text (buffer-string)))
    (let* ((disabled-rules (langtool--disabled-rules))
           (language (cond
                      ((stringp (or lang langtool-default-language))
                       (or lang langtool-default-language))
                      (t
                       "auto")))
           (query `(
                    ("language" ,language)
                    ("text" ,text)
                    ,@(and langtool-mother-tongue
                           `(("motherTongue" ,langtool-mother-tongue)))
                    ("disabled" ,disabled-rules)
                    ))
           query-string)
      (when (and langtool-client-filter-query-function
                 (functionp langtool-client-filter-query-function))
        (setq query (funcall langtool-client-filter-query-function query)))
      ;; UTF-8 encoding if value is multibyte character
      (setq query-string (url-build-query-string query))
      query-string)))

(defun langtool-client--http-post (server data)
  (let* ((host (process-get server 'langtool-server-host))
         (port (process-get server 'langtool-server-port))
         (buffer (langtool--process-create-client-buffer))
         (url-path "/v2/check")
         (client (let ((coding-system-for-write 'binary)
                       (coding-system-for-read 'utf-8-unix))
                   (open-network-stream
                    "LangtoolHttpClient" buffer host port
                    :type 'plain))))
    (process-send-string
     client
     (concat
      (format "POST %s HTTP/1.1\r\n" url-path)
      (format "Host: %s:%d\r\n" host port)
      (format "Content-length: %d\r\n" (length data))
      (format "Content-Type: application/x-www-form-urlencoded\r\n")
      (format "\r\n")
      data))
    (process-send-eof client)
    client))

(defun langtool-client--invoke-process (file begin finish &optional lang)
  (let* ((data (langtool-client--make-post-data  file begin finish lang))
         (proc (langtool-client--http-post langtool-server--process data)))
    (set-process-sentinel proc 'langtool-client--process-sentinel)
    (set-process-filter proc 'langtool-client--process-filter)
    (process-put proc 'langtool-source-buffer (current-buffer))
    (process-put proc 'langtool-region-begin begin)
    (process-put proc 'langtool-region-finish finish)
    proc))

;;
;; HTTP or commandline interface caller
;;

(defun langtool--invoke-checker-process (file begin finish &optional lang)
  (when (listp mode-line-process)
    (add-to-list 'mode-line-process '(t langtool-mode-line-message)))
  ;; clear previous check
  (langtool--clear-buffer-overlays)
  (let (proc)
    (cl-ecase (langtool--checker-mode)
      ('commandline
       (setq proc (langtool-command--invoke-process file begin finish lang)))
      ('http
       (langtool-server--ensure-running)
       (setq langtool-mode-line-server-process
             (propertize ":server" 'face compilation-info-face))
       (add-hook 'langtool-server--process-exit-hook
                 (lambda ()
                   (setq langtool-mode-line-server-process nil)))
       (setq proc (langtool-client--invoke-process file begin finish lang))))
    (setq langtool-buffer-process proc)
    (setq langtool-mode-line-process
          (propertize ":run" 'face compilation-info-face))
    (setq langtool-mode-line-message
          (list " "
                "LT"
                'langtool-mode-line-server-process
                'langtool-mode-line-process))))

(defun langtool--cleanup-process ()
  ;; cleanup mode-line
  (let ((cell (rassoc '(langtool-mode-line-message) mode-line-process)))
    (when cell
      (remq cell mode-line-process)))
  (when (and langtool-buffer-process
             (processp langtool-buffer-process))
    ;; TODO buffer killed, error. if process is local process (e.g. urllib)
    (delete-process langtool-buffer-process))
  (kill-local-variable 'langtool-buffer-process)
  (kill-local-variable 'langtool-mode-line-message)
  (kill-local-variable 'langtool-local-disabled-rules)
  (langtool--clear-buffer-overlays)
  (run-hooks 'langtool-finish-hook))

(defun langtool--check-command ()
  (cl-ecase (langtool--checker-mode)
    ('commandline
     (langtool-command--check-command))
    ('http
     (langtool-server--check-command))))

;;FIXME
;; https://docs.oracle.com/javase/6/docs/technotes/guides/intl/encoding.doc.html
(defun langtool--java-coding-system (coding-system)
  (let* ((cs (coding-system-base coding-system))
         (csname (symbol-name cs))
         (aliases (langtool--coding-system-aliases cs))
         (names (mapcar 'symbol-name aliases))
         (case-fold-search nil)
         tmp)
    (cond
     ((string-match "utf-8" csname)
      "utf8")
     ((string-match "utf-16" csname)
      (cond
       ((memq cs '(utf-16le utf-16-le))
        "UnicodeLittleUnmarked")
       ((memq cs '(utf-16be utf-16-be))
        "UnicodeBigUnmarked")
       (t
        "utf-16")))
     ((or (string-match "euc.*jp" csname)
          (string-match "japanese-iso-.*8bit" csname))
      "euc_jp")
     ((string-match "shift.jis" csname)
      "sjis")
     ((string-match "iso.*2022.*jp" csname)
      "iso2022jp")
     ((memq cs '(euc-kr euc-corea korean-iso-8bit))
      "euc_kr")
     ((setq tmp
            (cl-loop for x in names
                     if (string-match "iso-8859-\\([0-9]+\\)" x)
                     return x))
      (concat "ISO8859_" (match-string 1 tmp)))
     ((memq cs '(binary us-ascii raw-text undecided no-conversion))
      "ascii")
     ((memq cs '(cyrillic-koi8))
      "koi8-r")
     ((memq cs '(gb2312))
      "euc_cn")
     ((string-match "\\`\\(cp\\|ibm\\)[0-9]+" csname)
      (downcase csname))
     ((setq tmp
            (cl-loop for x in names
                     if (string-match "^windows-[0-9]+$" x)
                     return x))
      tmp)
     (t
      ;; simply guessed as same name.
      (downcase csname)))))

(defun langtool--coding-system-aliases (coding-system)
  (if (fboundp 'coding-system-aliases)
      ;; deceive elint
      (funcall 'coding-system-aliases coding-system)
    (coding-system-get coding-system 'alias-coding-systems)))

(defun langtool--brief-execute (langtool-args parser)
  (pcase (langtool--basic-command&args)
    (`(,command ,args)
     ;; Construct arguments pass to jar file.
     (setq args (append args langtool-args))
     (with-temp-buffer
       (when (and command args
                  (executable-find command)
                  (= (langtool--with-java-environ
                      (apply 'call-process command nil t nil args) 0)))
         (goto-char (point-min))
         (funcall parser))))
    (_
     nil)))

(defun langtool--available-languages ()
  (langtool--brief-execute
   (list "--list")
   (lambda ()
     (let ((res '()))
       (while (re-search-forward "^\\([^\s\t]+\\)" nil t)
         (setq res (cons (match-string 1) res)))
       (nreverse res)))))

(defun langtool--jar-version-string ()
  (langtool--brief-execute
   (list "--version")
   (lambda ()
     (langtool--chomp (buffer-string)))))

(defun langtool--jar-version ()
  (let ((string (langtool--jar-version-string)))
    (cond
     ((null string) nil)
     ((string-match "version \\([0-9.]+\\)" string)
      (match-string 1 string))
     (t
      ;; Unknown version, but should not raise error in this function.
      "0.0"))))

;;
;; interactive correction
;;

(defun langtool--ignore-rule (rule overlays)
  (cl-loop for ov in overlays
           do (let ((r (overlay-get ov 'langtool-rule-id)))
                (when (equal r rule)
                  (langtool--erase-overlay ov)))))

(defun langtool--correction (overlays)
  (let ((conf (current-window-configuration)))
    (unwind-protect
        (let ((next (car overlays)))
          (while (setq next (langtool--correction-loop next overlays))))
      (langtool--expire-buffer-overlays)
      (set-window-configuration conf)
      (kill-buffer (langtool--correction-buffer)))))

(defun langtool--correction-loop (ov overlays)
  (let* ((suggests (overlay-get ov 'langtool-suggestions))
         (msg (overlay-get ov 'langtool-simple-message))
         (alist (langtool--correction-popup msg suggests)))
    (catch 'next
      (while (progn
               (goto-char (overlay-start ov))
               (let (message-log-max)
                 (message (concat "C-h or ? for more options; "
                                  "SPC to leave unchanged, "
                                  "Digit to replace word")))
               (let* ((echo-keystrokes) ; suppress echoing
                      (c (downcase (read-char)))
                      (pair (assq c alist)))
                 (cond
                  (pair
                   (let ((sug (nth 1 pair)))
                     ;;TODO when region contains newline.
                     ;; -> insert newline after suggestion.
                     (delete-region (overlay-start ov) (overlay-end ov))
                     (insert sug)
                     (langtool--erase-overlay ov))
                   nil)
                  ((memq c '(?q))
                   (keyboard-quit))
                  ((memq c '(?c))
                   (langtool--erase-overlay ov)
                   nil)
                  ((memq c '(?e))
                   (message (substitute-command-keys
                             "Type \\[exit-recursive-edit] to finish the edit."))
                   (recursive-edit)
                   ;; stay current cursor and wait next user command.
                   (throw 'next ov))
                  ((memq c '(?i))
                   (let ((rule (overlay-get ov 'langtool-rule-id)))
                     (unless (member rule langtool-local-disabled-rules)
                       (setq langtool-local-disabled-rules
                             (cons rule langtool-local-disabled-rules)))
                     (langtool--ignore-rule rule overlays))
                   nil)
                  ((memq c '(?\C-h ?\?))
                   (langtool--correction-help)
                   t)
                  ((memq c '(?\d))
                   (throw 'next (langtool--prev-overlay ov overlays)))
                  ((memq c '(?\s)) nil)
                  (t (ding) t)))))
      ;; next item
      (langtool--next-overlay ov overlays))))

(defun langtool--correction-popup (msg suggests)
  (let ((buf (langtool--correction-buffer)))
    (delete-other-windows)
    (let ((win (split-window)))
      (set-window-buffer win buf))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert msg "\n\n")
        (cl-loop for s in suggests
                 for c across langtool--correction-keys
                 do (progn
                      (insert "(" c ") ")
                      (let ((start (point)))
                        (insert s)
                        ;; colorize suggestion.
                        ;; suggestion may contains whitespace.
                        (let ((ov (make-overlay start (point))))
                          (overlay-put ov 'face 'langtool-correction-face)))
                      (insert "\n"))
                 collect (list c s))))))

(defun langtool--correction-help ()
  (let ((help-1 "[q/Q]uit correction; [c/C]lear the colorized text; ")
        (help-2 "[i/I]gnore the rule over current session.")
        (help-3 "[e/E]dit the buffer manually")
        (help-4 "SPC skip; DEL move backward;")
        )
    (save-window-excursion
      (unwind-protect
          (let ((resize-mini-windows 'grow-only))
            (select-window (minibuffer-window))
            (erase-buffer)
            (message nil)
            ;;(set-minibuffer-window (selected-window))
            (enlarge-window 2)
            (insert (concat help-1 "\n" help-2 "\n" help-3 "\n" help-4))
            (sit-for 5))
        (erase-buffer)))))

(defun langtool--correction-buffer ()
  (get-buffer-create "*Langtool Correction*"))

;;
;; Misc UI
;;

(defun langtool--show-message-buffer (msg)
  (let ((buf (get-buffer-create langtool-error-buffer-name)))
    (with-current-buffer buf
      (erase-buffer)
      (insert msg))
    (save-window-excursion
      (display-buffer buf)
      (let* ((echo-keystrokes)
             (event (read-event)))
        (setq unread-command-events (list event))))))

;;
;; initialize
;;

(defun langtool--guess-language ()
  (let ((env (or (getenv "LANG")
                 (getenv "LC_ALL")))
        (supported-langs (langtool--available-languages))
        lang country mems)
    (and env
         (string-match "\\`\\(..\\)_\\(..\\)?" env)
         (setq lang (downcase (match-string 1 env)))
         (setq country (and (match-string 2 env)
                            (upcase (match-string 2 env)))))
    (or
     (and
      lang country
      (setq mems (member (format "%s-%s" lang country) supported-langs))
      (car mems))
     (and
      lang
      (setq mems (cl-member-if
                  (lambda (x) (string-match
                               (concat "\\`" (regexp-quote lang)) x))
                  supported-langs))
      (car mems)))))

;;
;; autoshow message
;;

(defcustom langtool-autoshow-message-function
  'langtool-autoshow-default-message
  "Function with one argument which displaying error overlays reported by LanguageTool.
These overlays hold some useful properties:
 `langtool-simple-message', `langtool-rule-id', `langtool-suggestions' .
`langtool-autoshow-default-message' is a default/sample implementations.
See the Commentary section for `popup' implementation."
  :group 'langtool
  :type '(choice
          (const nil)
          function))

(defcustom langtool-autoshow-idle-delay 0.5
  "Number of seconds while idle time to wait before showing error message."
  :group 'langtool
  :type 'number)

(defvar langtool-autoshow--current-idle-delay nil)

(defvar langtool-autoshow--timer nil
  "Hold idle timer watch every LanguageTool processed buffer.")

(defun langtool-autoshow-default-message (overlays)
  ;; Do not interrupt current message
  (unless (current-message)
    (let ((msg (langtool-simple-error-message overlays)))
      (message "%s" msg))))

(defun langtool-autoshow--maybe ()
  (when langtool-autoshow-message-function
    (let ((delay (langtool-autoshow--idle-delay)))
      (cond
       ((equal langtool-autoshow--current-idle-delay delay))
       (t
        (setq langtool-autoshow--current-idle-delay delay)
        (timer-set-idle-time langtool-autoshow--timer
                             langtool-autoshow--current-idle-delay t))))
    (condition-case err
        (let ((error-overlays (langtool--current-error-overlays)))
          (when error-overlays
            (funcall langtool-autoshow-message-function error-overlays)))
      (error
       (message "langtool: %s" err)))))

(defun langtool-autoshow--idle-delay ()
  (if (numberp langtool-autoshow-idle-delay)
      langtool-autoshow-idle-delay
    (default-value 'langtool-autoshow-idle-delay)))

(defun langtool-autoshow-ensure-timer ()
  (unless (and (timerp langtool-autoshow--timer)
               (memq langtool-autoshow--timer timer-idle-list))
    (setq langtool-autoshow--timer
          (run-with-idle-timer
           (langtool-autoshow--idle-delay) t 'langtool-autoshow--maybe)))
  (add-hook 'kill-buffer-hook 'langtool-autoshow-cleanup-timer-maybe nil t))

(defun langtool-autoshow-cleanup-timer-maybe ()
  (unless (langtool-working-p)
    (when (timerp langtool-autoshow--timer)
      (cancel-timer langtool-autoshow--timer)
      (setq langtool-autoshow--timer nil))))

;;;
;;; interactive commands
;;;

(defun langtool-read-lang-name ()
  (let ((completion-ignore-case t)
        (set
         (append
          '(("auto" . auto))
          (or (mapcar 'list (langtool--available-languages))
              (mapcar (lambda (x) (list (car x))) locale-language-names)))))
    (let ((key (completing-read "Lang: " set)))
      (or (cdr (assoc key set)) key))))

(defun langtool-goto-next-error ()
  "Obsoleted function. Should use `langtool-correct-buffer'.
Go to next error."
  (interactive)
  (let ((overlays (langtool--overlays-region (point) (point-max))))
    (langtool--goto-error
     overlays
     (lambda (ov) (< (point) (overlay-start ov))))))

(defun langtool-goto-previous-error ()
  "Obsoleted function. Should use `langtool-correct-buffer'.
Goto previous error."
  (interactive)
  (let ((overlays (langtool--overlays-region (point-min) (point))))
    (langtool--goto-error
     (reverse overlays)
     (lambda (ov) (< (overlay-end ov) (point))))))

(defun langtool-show-message-at-point ()
  "Show error details at point."
  (interactive)
  (let ((ovs (langtool--current-error-overlays)))
    (if (null ovs)
        (message "No errors")
      (let ((msg (langtool-details-error-message ovs)))
        (langtool--show-message-buffer msg)))))

(defun langtool-show-brief-message-at-point ()
  "Show error brief message at point."
  (interactive)
  (let ((msgs (langtool--current-error-messages)))
    (if (null msgs)
        (message "No errors")
      (langtool--show-message-buffer
       (mapconcat 'identity msgs "\n")))))

(defun langtool-check-done ()
  "Finish LanguageTool process and cleanup existing colorized texts."
  (interactive)
  (langtool--cleanup-process)
  (force-mode-line-update)
  (message "Cleaned up LanguageTool."))

;;;###autoload
(defalias 'langtool-check 'langtool-check-buffer)

;;;###autoload
(defun langtool-check-buffer (&optional lang)
  "Check context current buffer and light up errors.
Optional \\[universal-argument] read LANG name.

You can change the `langtool-default-language' to apply all session.
Restrict to selection when region is activated.
"
  (interactive
   (when current-prefix-arg
     (list (langtool-read-lang-name))))
  (langtool--check-command)
  ;; probablly ok...
  (let* ((file (buffer-file-name))
         (region-p (langtool-region-active-p))
         (begin (and region-p (region-beginning)))
         (finish (and region-p (region-end))))
    (when region-p
      (deactivate-mark))
    (unless langtool-temp-file
      (setq langtool-temp-file (langtool--make-temp-file)))
    ;; create temporary file to pass the text contents to LanguageTool
    (when (or (null file)
              (buffer-modified-p)
              region-p
              ;; 1 is dos EOL style, this must convert to unix
              (eq (coding-system-eol-type buffer-file-coding-system) 1))
      (save-restriction
        (widen)
        (let ((coding-system-for-write
               ;; convert EOL style to unix (LF).
               ;; dos (CR-LF) style EOL may destroy position of marker.
               (coding-system-change-eol-conversion
                buffer-file-coding-system 'unix)))
          ;; BEGIN nil means entire buffer
          (write-region begin finish langtool-temp-file nil 'no-msg))
        (setq file langtool-temp-file)))
    (langtool--invoke-checker-process file begin finish lang)
    (force-mode-line-update)))

;;;###autoload
(defun langtool-switch-default-language (lang)
  "Switch `langtool-default-language' to LANG"
  (interactive (list (langtool-read-lang-name)))
  (setq langtool-default-language lang)
  (message "Now default language is `%s'" lang))

(defun langtool-correct-buffer ()
  "Execute interactive correction after `langtool-check'"
  (interactive)
  (let ((ovs (langtool--overlays-region (point-min) (point-max))))
    (if (null ovs)
        (message "No error found. %s"
                 (substitute-command-keys
                  (concat
                   "Type \\[langtool-check-done] to finish checking "
                   "or type \\[langtool-check] to re-check buffer")))
      (barf-if-buffer-read-only)
      (langtool--correction ovs))))

(defun langtool-server-stop ()
  "Terminate LanguageTool HTTP server."
  (interactive)
  (langtool-server-ensure-stop)
  (message "Server is terminated."))

(defun langtool-toggle-debug ()
  "Toggle LanguageTool debugging."
  (interactive)
  (setq langtool--debug (not langtool--debug))
  (if langtool--debug
      (message "Langtool debug ON.")
    (message "Langtool debug off.")))

;;;
;;; initialize
;;;

;; initialize custom variables guessed from environment.
(let ((mt (langtool--guess-language)))
  (unless langtool-mother-tongue
    (setq langtool-mother-tongue mt)))

(provide 'langtool)

;;; langtool.el ends here
