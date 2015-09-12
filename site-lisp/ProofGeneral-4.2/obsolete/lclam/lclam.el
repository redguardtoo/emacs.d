;; File name:      lclam.el        
;; Description:    Proof General instance for Lambda-CLAM
;; Author:         James Brotherston <jjb@dai.ed.ac.uk>
;; Last modified:  23 October 2001
;;
;; lclam.el,v 12.0 2011/10/13 10:54:51 da Exp

(require 'proof)            ; load generic parts
(require 'proof-syntax)     

;;
;; =========== User settings for Lambda-CLAM ============
;;

(defcustom lclam-prog-name ; "~/lambda-clam-teyjus/bin/lclam"
			   "lclam"
  "*Name of program to run Lambda-CLAM"
  :type 'file
  :group 'lclam)

(defcustom lclam-web-page
  "http://dream.dai.ed.ac.uk/software/systems/lambda-clam/"
  "URL of web page for Lambda-CLAM"
  :type 'string
  :group 'lclam-config)


;;
;; =========== Configuration of generic modes ============
;;

(defun lclam-config ()
  "Configure Proof General scripting for Lambda-CLAM."
  (setq 
   proof-terminal-string           "."
   proof-script-comment-start      "/*"
   proof-script-comment-end        "*/"
   proof-goal-command-regexp       "^pds_plan"
   proof-save-command-regexp       nil
   proof-goal-with-hole-regexp     nil
   proof-save-with-hole-regexp     nil
   proof-non-undoables-regexp      nil
   proof-undo-n-times-cmd          nil
   proof-showproof-command         nil 
   proof-goal-command              "^pds_plan %s."
   proof-save-command              nil
   proof-kill-goal-command         nil
   proof-assistant-home-page       lclam-web-page
   proof-auto-multiple-files       nil 
   ))

(defun lclam-shell-config ()
  "Configure Proof General shell for Lambda-CLAM"
  (setq
   proof-shell-annotated-prompt-regexp "^lclam:" 
   proof-shell-cd-cmd                  nil
   proof-shell-interrupt-regexp        nil
   proof-shell-error-regexp            nil
   proof-shell-start-goals-regexp      nil
   proof-shell-end-goals-regexp        nil
   proof-shell-proof-completed-regexp  "^Plan Succeeded"
   proof-shell-init-cmd                nil
   proof-shell-quit-cmd                "halt."
   proof-shell-eager-annotation-start  nil
    ))

;;
;; =========== Defining the derived modes ================
;;

(define-derived-mode lclam-proofscript-mode proof-mode
  "Lambda-CLAM script" nil
  (lclam-config)
  (proof-config-done))

(define-derived-mode lclam-shell-mode proof-shell-mode
  "Lambda-CLAM shell" nil
  (lclam-shell-config)
  (proof-shell-config-done))

(define-derived-mode lclam-response-mode proof-response-mode
  "Lambda-CLAM response" nil
  (proof-response-config-done))

(define-derived-mode lclam-goals-mode proof-goals-mode
  "Lambda-CLAM goals" nil
  (proof-goals-config-done))

;; Automatic selection of theory file or proof script mode
;; .lcm -> proof script mode
;; .def -> theory file mode

(defun lclam-mode ()
(interactive)
(cond
    ((proof-string-match "\\.def$" (buffer-file-name))
    (thy-mode))
    (t
    (lclam-proofscript-mode)))
)

;; Hook which configures settings to get the proof shell running 

(add-hook 'proof-pre-shell-start-hook 'lclam-pre-shell-start)

(defun lclam-pre-shell-start ()
  (setq proof-prog-name         lclam-prog-name)
  (setq proof-mode-for-shell    'lclam-shell-mode)
  (setq proof-mode-for-response 'lclam-response-mode)
  (setq proof-mode-for-goals    'lclam-goals-mode)
  (setq proof-shell-process-connection-type t))


;;
;; ============ Extra bits and pieces - JB ============
;;

;; Open .def files in theory mode from now on

(setq auto-mode-alist
      (cons '("\\.def$" . thy-mode) auto-mode-alist))

;; Remove redundant toolbar buttons

(eval-after-load "pg-custom"
'(progn
  (setq lclam-toolbar-entries
	(remassoc 'state lclam-toolbar-entries))
  (setq lclam-toolbar-entries
	(remassoc 'context lclam-toolbar-entries))
  (setq lclam-toolbar-entries
	(remassoc 'undo lclam-toolbar-entries))
  (setq lclam-toolbar-entries
	(remassoc 'retract lclam-toolbar-entries))
  (setq lclam-toolbar-entries
	(remassoc 'qed lclam-toolbar-entries))))

;;
;; ============ Theory file mode ==============
;;

(define-derived-mode thy-mode fundamental-mode "Lambda-CLAM theory file mode"
  (thy-add-menus))

(defvar thy-mode-map nil)

(defun thy-add-menus ()
  "Add Lambda-CLAM menu to current menu bar."  
  (require 'proof-script)    
  (require 'proof-x-symbol)
  (easy-menu-define thy-mode-pg-menu
                    thy-mode-map
                    "PG Menu for Lambda-CLAM Proof General"
                    (cons proof-general-name
                          (append
                           (list
                           ;; A couple from the toolbar that make sense here
                           ;; (also in proof-universal-keys)
                            ["Issue command" proof-minibuffer-cmd t]
                            ["Interrupt prover" proof-interrupt-process t])
			   (list proof-buffer-menu)
                           (list proof-help-menu))))

  (easy-menu-define thy-mode-lclam-menu
                    thy-mode-map
                    "Menu for Lambda-CLAM Proof General, theory file mode."
                    (cons "Theory"
                          (list
                           ["Next section" thy-goto-next-section t]
                           ["Prev section" thy-goto-prev-section t]
                           ["Insert template" thy-insert-template t]
; da: commented out this, function is incomplete
;                           ["Include definitions" match-and-assert-defs
;                            :active (proof-locked-region-empty-p)]
                           ["Process theory" process-thy-file
                            :active (proof-locked-region-empty-p)]
; da: commented out this, there's no retract function provided
;                           ["Retract theory" isa-retract-thy-file
;                            :active (proof-locked-region-full-p)]
                           ["Next error" proof-next-error t]
                           ["Switch to script" thy-find-other-file t])))

  (easy-menu-add thy-mode-pg-menu thy-mode-map)
  (easy-menu-add thy-mode-lclam-menu thy-mode-map)
)

(defun process-thy-file (file)
  "Process the theory file FILE.  If interactive, use buffer-file-name."
  (interactive (list buffer-file-name))
  (save-some-buffers)
  (update-thy-only file nil nil))

(defun update-thy-only (file try wait)
  "Process the theory file FILE."
  ;; First make sure we're in the right directory to take care of
  ;; relative "files" paths inside theory file.
  (proof-cd-sync)
  (proof-shell-invisible-command
   (proof-format-filename
    ;; %r parameter means relative (don't expand) path
    (format "use_thy \"%s%%r\"." (if try "try_" ""))
    (file-name-nondirectory file))
   wait))

;(defun match-and-assert-defs
;  "Interactively process and assert definitions in theory file"
;)

(provide 'lclam)
