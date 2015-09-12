;; twelf.el  Proof General instance for Twelf
;;
;; Copyright (C) 2000 LFCS Edinburgh.
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; twelf.el,v 12.0 2011/10/13 10:54:51 da Exp
;;
;;
;; TODO:
;;   Info doc menu entry
;;   X-Symbol upgrade/test?  Mule XE better?
;;


(require 'proof-easy-config)            ; easy configure mechanism

(require 'twelf-font)			; font lock configuration
;; (require 'twelf-old)
;; FIXME: put parts of old code into twelf-syntax or similar

;;
;; User configuration settings for Twelf PG
;;
(defcustom twelf-root-dir
  "/usr/local/twelf/"
  "*Root of twelf installation.  Default /usr/local/twelf suits RPM package."
  :type 'file
  :group 'twelf)

(defcustom twelf-info-dir
  (concat twelf-root-dir "doc/info/")
  "*Directory of Twelf Infor files."
  :type 'file
  :group 'twelf)

;;
;; Instantiation of Proof General
;;
(proof-easy-config 'twelf "Twelf"
 proof-prog-name		 "twelf-server"
 proof-assistant-home-page       "http://www.cs.cmu.edu/~twelf/"

 proof-terminal-char             ?\.
 proof-script-comment-start             "%"	;; for inserting comments
 proof-script-comment-end               ""
 proof-script-comment-start-regexp	 "%[%{ \t\n\f]" ;; recognizing
 proof-script-comment-end-regexp	 "%}\\|\n"      ;; comments

 proof-shell-auto-terminate-commands nil ; server commands don't end with .
 proof-shell-strip-crs-from-input nil	 ; server needs CRs with readDecl

 proof-auto-multiple-files       t
 proof-shell-cd-cmd              "OS.chDir %s"
 proof-shell-interrupt-regexp    "interrupt"

 proof-shell-annotated-prompt-regexp "%% [OA][KB]O?R?T? %%\n"
 proof-shell-error-regexp        "Server error:"
 proof-shell-quit-cmd            "quit"
 proof-shell-restart-cmd	 "reset"

 ;; "Eager annotations" mark messages Proof General should display
 ;; or recognize while the prover is pontificating
 proof-shell-eager-annotation-start
 "^\\[Opening \\|\\[Closing "
 proof-shell-eager-annotation-end "\n"

 ;; next setting is just to prevent warning
 proof-save-command-regexp	proof-no-regexp)


;; unset: all of the interactive proof commands
;; These don't really apply, I don't think, because Twelf
;; only has fully automatic prover at the moment.
;; Also, there is no concept of "undo" to remove declarations
;; (can simply repeat them, tho.)
;; proof-goal-command-regexp       "^%theorem"
;; proof-save-command-regexp       "" ;; FIXME: empty?
;; proof-goal-with-hole-regexp     "^%theorem\w-+\\(.*\\)\w-+:"
;; proof-save-with-hole-regexp     "" ;; FIXME
;; proof-non-undoables-regexp
;; proof-goal-command              "%theorem %s."
;; proof-save-command              "%prove "
;; remaining strings are left over from Isabelle example
;; proof-kill-goal-command         "Goal \"PROP no_goal_set\";"
;; proof-showproof-command         "pr()"
;; proof-undo-n-times-cmd          "pg_repeat undo %s;"
;; proof-shell-start-goals-regexp  "Level [0-9]"
;; proof-shell-end-goals-regexp    "val it"
;; proof-shell-init-cmd
;; proof-shell-proof-completed-regexp "^No subgoals!"


;;
;; Twelf server doesn't take declarations directly:
;; we need to pre-process script input slightly
;;

(defun twelf-add-read-declaration ()
  "A hook value for `proof-shell-insert-hook'."
  (if (eq action 'proof-done-advancing)
      (setq string (concat "readDecl\n" string))))

(add-hook 'proof-shell-insert-hook 'twelf-add-read-declaration)


;;
;; Syntax table
;;

;; Taken from old Emacs mode, renamed fns to be convention compliant
(defun twelf-set-syntax (char entry)
  (modify-syntax-entry char entry twelf-mode-syntax-table))
(defun twelf-set-word  (char) (twelf-set-syntax char "w   "))
(defun twelf-set-symbol (char) (twelf-set-syntax char "_   "))

(defun twelf-map-string (func string)
  (if (string= "" string)
      ()
    (funcall func (string-to-char string))
    (twelf-map-string func (substring string 1))))

;; A-Z and a-z are already word constituents
;; For fontification, it would be better if _ and ' were word constituents
(twelf-map-string
 'twelf-set-word "!&$^+/<=>?@~|#*`;,-0123456789\\") ; word constituents
(twelf-map-string 'twelf-set-symbol "_'")         ; symbol constituents
;; Delimited comments are %{ }%, see 1234 below.
(twelf-set-syntax ?\ "    ")            ; whitespace
(twelf-set-syntax ?\t "    ")           ; whitespace
; da: this old entry is wrong: it says % always starts a comment
;(twelf-set-syntax ?% "< 14")            ; comment begin
; This next one is much better,
(twelf-set-syntax ?% ". 14")            ; comment begin/second char
(twelf-set-syntax ?\n ">   ")           ; comment end
(twelf-set-syntax ?: ".   ")            ; punctuation
(twelf-set-syntax ?. ".   ")            ; punctuation
(twelf-set-syntax ?\( "()  ")           ; open delimiter
(twelf-set-syntax ?\) ")(  ")           ; close delimiter
(twelf-set-syntax ?\[ "(]  ")           ; open delimiter
(twelf-set-syntax ?\] ")[  ")           ; close delimiter
;(twelf-set-syntax ?\{ "(}2 ")           ; open delimiter
;(twelf-set-syntax ?\} "){ 3")           ; close delimiter
;; Actually, strings are illegal but we include:
(twelf-set-syntax ?\" "\"   ")          ; string quote
;; \ is not an escape, but a word constituent (see above)
;;(twelf-set-syntax ?\\ "/   ")         ; escape



;;
;; Syntax highlighting (from twelf-old.el, NEEDS WORK)
;;
;; Highlighting is maybe a nuisance for twelf because of its funny syntax.
;; But font lock could perhaps be got to work with recent versions.
;; That would be better than the present mechanism, which doesn't lock,
;; doesn't work well with X Symbol (which really needs locking), and
;; even breaks the background colouring for some reason (presumably
;; the Twelf faces)

(require 'twelf-font)
(add-hook 'twelf-mode-hook 'twelf-mode-extra-config)

(defun twelf-mode-extra-config ()
  (make-local-hook 'font-lock-after-fontify-buffer-hook)
  (add-hook 'font-lock-after-fontify-buffer-hook
	    'twelf-font-fontify-buffer nil 'local)
  (font-lock-mode))

(defconst twelf-syntax-menu
  '("Syntax Highlighting"
    ["Highlight Declaration" twelf-font-fontify-decl t]
    ["Highlight Buffer" twelf-font-fontify-buffer t]
    ;;(, (toggle "Immediate Highlighting" 'toggle-twelf-font-immediate
    ;;'font-lock-mode))
      )
  "Menu for syntax highlighting in Twelf mode.")


;;
;; Setting Twelf options via Proof General
;;

(defpacustom chatter 1
  "Value for chatter."
  :type 'integer
  :setting "set chatter %i")

(defpacustom double-check nil
  "Double-check declarations after type reconstruction."
  :type 'boolean
  :setting "set doubleCheck %b")
(defpacustom print-implicit nil
  "Show implicit arguments."
  :type 'boolean
  :setting "set Print.implict %b")

;; etc


;;
;; Twelf menu
;;

(defpgdefault menu-entries
  (cdr twelf-syntax-menu))


(provide 'twelf)
