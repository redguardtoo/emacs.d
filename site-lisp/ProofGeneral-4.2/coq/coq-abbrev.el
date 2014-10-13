;;; coq-abbrev.el --- coq abbrev table and menus for ProofGeneral mode
;;
;; Copyright (C) 1994-2009 LFCS Edinburgh.
;; Authors: Healfdene Goguen, Pierre Courtieu
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

(require 'proof)
(require 'coq-syntax)

(defun holes-show-doc ()
  (interactive)
  (describe-function 'holes-mode))

(defun coq-local-vars-list-show-doc ()
  (interactive)
  (describe-variable 'coq-local-vars-doc))


(defconst coq-tactics-menu
  (append '("Tactics (menu)"
	    ["Intros (smart)" coq-insert-intros :help "Insert \"intros h1 .. hn.\" where hi are the default names given by Coq."])
	  (coq-build-menu-from-db (append coq-tactics-db coq-solve-tactics-db))))

(defconst coq-tactics-abbrev-table
  (coq-build-abbrev-table-from-db (append coq-tactics-db coq-solve-tactics-db)))

(defconst coq-tacticals-menu
  (append '("Tacticals (menu)")
	  (coq-build-menu-from-db coq-tacticals-db)))

(defconst coq-tacticals-abbrev-table
  (coq-build-abbrev-table-from-db coq-tacticals-db))

(defconst coq-commands-menu
  (append '("Command (menu)"
	    ;["Module/Section (smart)" coq-insert-section-or-module t]
	    ;["Require (smart)" coq-insert-requires t]
	    )
	  (coq-build-menu-from-db coq-commands-db)))

(defconst coq-commands-abbrev-table
  (coq-build-abbrev-table-from-db coq-commands-db))

(defconst coq-terms-menu
  (append '("Term (menu)"
	    ["Match (smart)" coq-insert-match t])
	  (coq-build-menu-from-db coq-terms-db)))

(defconst coq-terms-abbrev-table
  (coq-build-abbrev-table-from-db coq-terms-db))



;;; The abbrev table built from keywords tables
;#s and @{..} are replaced by holes by holes-abbrev-complete
(defun coq-install-abbrevs ()
  "install default abbrev table for coq if no other already is."
  (if (boundp 'coq-mode-abbrev-table)
      ;; da: this test will always fail.  Assume bound-->non-empty
      ;; (not (equal coq-mode-abbrev-table (make-abbrev-table))))
      (message "Coq abbrevs already exists, default not loaded")
    (define-abbrev-table 'coq-mode-abbrev-table
      (append coq-tactics-abbrev-table coq-tacticals-abbrev-table
              coq-commands-abbrev-table coq-terms-abbrev-table))
    ;; if we use default coq abbrev, never ask to save it
    ;; PC: fix trac #382 I comment this. But how to disable abbrev
    ;; saving for coq mode only?
    ;;(setq save-abbrevs nil) ; 
    ;; DA: how about above, just temporarily disable saving?
    (message "Coq default abbrevs loaded")))

(unless noninteractive
  (coq-install-abbrevs))
;;;;;

;; The coq menu partly built from tables

;; Common part (scrit, response and goals buffers)
(defconst coq-menu-common-entries
  `(
    ["Toggle 3 Windows Mode" proof-three-window-toggle
     :style toggle
     :selected proof-three-window-enable
     :help "Toggles the use of separate windows or frames for Coq responses and goals."
     ]
    ("3 Windows mode layout"
     ["smart"
      (progn
	(customize-set-variable 'proof-three-window-mode-policy 'smart)
	(proof-layout-windows))
      :style radio
      :selected (eq proof-three-window-mode-policy 'smart)
      :help "Adapt to frame width (C-c C-l to refresh)"]
     ["hybrid"
      (progn
	(customize-set-variable 'proof-three-window-mode-policy 'hybrid)
	(proof-layout-windows))
      :style radio
      :selected (eq proof-three-window-mode-policy 'hybrid)
      :help "two column mode"]
     ["horizontal"
      (progn
	(customize-set-variable 'proof-three-window-mode-policy 'horizontal)
	(proof-layout-windows))
      :style radio
      :selected (eq proof-three-window-mode-policy 'horizontal)
      :help "Three column mode"]
     ["vertical"
      (progn
	(customize-set-variable 'proof-three-window-mode-policy 'vertical)
	(proof-layout-windows))
      :style radio
      :selected (eq proof-three-window-mode-policy 'vertical)
      :help "One column mode"])
    ["Refresh Windows Layout" proof-layout-windows t]
    ["Toggle tooltips" proof-output-tooltips-toggle
     :style toggle
     :selected proof-output-tooltips
     :help "Toggles Tooltips (popup when hovering commands).\nSet `proof-output-tooltips' to nil to disable it by default."]
    ["Electric Terminator" proof-electric-terminator-toggle
     :style toggle
     :selected proof-electric-terminator-enable
     :help "Automatically send commands when terminator typed"]
    ["Double Hit Electric Terminator" coq-double-hit-toggle
     :style toggle
     :selected coq-double-hit-enable
     :help "Automatically send commands when terminator typed twiced quickly."]
    ""
    ["Print..." coq-Print :help "With prefix arg (C-u): Set Printing All first"]
    ["Check..." coq-Check :help "With prefix arg (C-u): Set Printing All first"]
    ["About..." coq-About :help "With prefix arg (C-u): Set Printing All first"]
    [ "Store Response" proof-store-response-win :help "Stores the content of response buffer in a dedicated buffer"]
    [ "Store Goal" proof-store-goals-win  :help "Stores the content of goals buffer in a dedicated buffer"]
    ("OTHER QUERIES"
     ["Print Hint" coq-PrintHint t]
     ["Show ith Goal..." coq-Show t]
     ["Show ith Goal... (show implicits)" coq-Show-with-implicits t]
     ["Show ith Goal... (show all)" coq-Show-with-all t]
     ["Show Tree" coq-show-tree t]
     ["Show Proof" coq-show-proof t]
     ["Show Conjectures" coq-show-conjectures t];; maybe not so useful with editing in PG?
     ""
     ["Print..." coq-Print :help "With prefix arg (C-u): Set Printing All first"]
     ["Print... (show implicits)" coq-Print-with-implicits t]
     ["Print... (show all)" coq-Print-with-all t]
     ["Check..." coq-Check :help "With prefix arg (C-u): Set Printing All first"]
     ["Check (show implicits)..." coq-Check-show-implicits t]
     ["Check (show all)..." coq-Check-show-all t]
     ["About..." coq-About :help "With prefix arg (C-u): Set Printing All first"]
     ["About...(show implicits)" coq-About-with-implicits t]
     ["About...(show all)" coq-About-with-all t]
     ["Search..." coq-SearchConstant t]
     ["SearchRewrite..." coq-SearchRewrite t]
     ["SearchAbout..." coq-SearchAbout t]
     ["SearchPattern..." coq-SearchIsos t]
     ["Locate constant..." coq-LocateConstant t]
     ["Locate Library..." coq-LocateLibrary t]
     ["Pwd" coq-Pwd t]
     ["Inspect..." coq-Inspect t]
     ["Print Section..." coq-PrintSection t]
     ""
     ["Locate notation..." coq-LocateNotation t]
     ["Print Implicit..." coq-Print t]
     ["Print Scope/Visibility..." coq-PrintScope t])
    ("OPTIONS"
     ["Set Printing All" coq-set-printing-all t]
     ["UnSet Printing All" coq-unset-printing-all t]
     ["Set Implicit Argument" coq-set-implicit-arguments t]
     ["Unset Implicit Argument" coq-unset-implicit-arguments t]
     ["Set Printing Synth" coq-set-printing-synth t]
     ["Unset Printing Synth" coq-unset-printing-synth t]
     ["Set Printing Coercions" coq-set-printing-coercions t]
     ["Unset Printing Coercions" coq-unset-printing-coercions t]
     ["Set Printing Wildcards" coq-set-printing-wildcards t]
     ["Unset Printing Wildcards" coq-unset-printing-wildcards t])))

(defpgdefault menu-entries
  (append coq-menu-common-entries
  `(
    ""
    ("INSERT"
     ["Intros (smart)" coq-insert-intros :help "Insert \"intros h1 .. hn.\" where hi are the default names given by Coq."]
     ""
     ["Tactic (interactive)" coq-insert-tactic t]
     ["Tactical (interactive)" coq-insert-tactical t]
     ["Command (interactive)" coq-insert-command t]
     ["Term (interactive)" coq-insert-term t]
     ""
     ,coq-tactics-menu
     ,coq-tacticals-menu
     ,coq-commands-menu
     ,coq-terms-menu
     ""
     ["Module/Section (smart)" coq-insert-section-or-module t]
     ["Require (smart)" coq-insert-requires t])
    ""
    ("ABBREVS"
     ["Expand At Point" expand-abbrev t]
     ["Unexpand Last" unexpand-abbrev t]
     ["List Abbrevs" list-abbrevs t]
     ["Edit Abbrevs" edit-abbrevs t]
     ["Abbrev Mode" abbrev-mode
      :style toggle
      :selected (and (boundp 'abbrev-mode) abbrev-mode)])
    ""
    ("COQ PROG (ARGS)"
     ["Set Coq Prog *persistently*" coq-ask-insert-coq-prog-name t]
     ["help" coq-local-vars-list-show-doc t]
     ["Compile" coq-Compile t]))))

(defpgdefault help-menu-entries
  '(["help on setting prog name persistently for a file" 
     coq-local-vars-list-show-doc t]))

(defpgdefault other-buffers-menu-entries coq-menu-common-entries)



(provide 'coq-abbrev)
