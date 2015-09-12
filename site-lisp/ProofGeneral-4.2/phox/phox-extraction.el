;; Exp 2011/10/13 10:54:51 12.0
;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;; program extraction.
;;
;; note : program extraction is still experimental This file is very
;; dependant of the actual state of program extraction in phox.
;;--------------------------------------------------------------------------;;

(require 'cl)

(eval-when (compile)
  (defvar phox-prog-name nil))

(declare-function proof-shell-invisible-command "proof-shell" (str))

;; configuration :

(defvar phox-prog-orig "phox -pg" "original name of phox binary.")

(defun phox-prog-flags-modify(option)
"ask for a string that are options to pass to phox binary"
(interactive "soption :")
; pas d'analyse de la réponse,
(let ((process))
  (if  (and phox-prog-name
	    (progn (string-match " \\|$" phox-prog-name)
		   (setq process
			 (substring phox-prog-name 0 (match-beginning 0))
			 )
		   )
	    (processp (get-process process))
	  (eq (process-status process) 'run))
    (error "Error : exit phox process first !")
  )
(if (string-match "^ *$" option)
    (progn
      (message
       "no option other than default ones will be passed to phox binary.")
      (setq phox-prog-name phox-prog-orig))
  (progn
    (message (format  "option %s will be passed to phox binary." option ))
    (setq phox-prog-name (concat phox-prog-orig " " option))
    )
  )
)
)


(defun phox-prog-flags-extract()
"pass option -f to phox binary. A program can be extracted from
proof of theorem_name with :
compile theorem_name.
output."
(interactive)
(phox-prog-flags-modify "-f")
(message
"WARNING : program extraction is experimental and can disturb the prover !")
)

(defun phox-prog-flags-erase()
"no option to phox binary."
(interactive)
(phox-prog-flags-modify ""))

; encore une fonction qui devrait être redéfinie en cas d'autres
; options possibles que -f

(defun phox-toggle-extraction()
"toggle between extraction mode and ordinary mode for phox process."
(interactive)
(cond ((string-equal phox-prog-name phox-prog-orig) ;; à améliorer (espaces)
       (phox-prog-flags-extract))
      ((string-match "\-f$" phox-prog-name) (phox-prog-flags-erase))
      (t (error "option must be empty or -f, use phox-prog-flags-modify.")))
)

;; commands

; compilation
(defun phox-compile-theorem(name)
  "Interactive function :
ask for the name of a theorem and send a compile command to PhoX for it."
  (interactive "stheorem : ")
  (proof-shell-invisible-command (concat "compile " name)))

(defun phox-compile-theorem-on-cursor()
"Interactive function :
send a compile command to PhoX for the theorem which name is under the cursor."
  (interactive)
  (let (start end)
    (save-excursion
;      (modify-syntax-entry ?\. "w")
      (forward-word 1)
      (setq start (point))
      (forward-word -1)
      (setq end (point)))
    (if (char-equal (char-after (- end 1)) ?\.)(setq end (- end 1)))
    (phox-compile-theorem (buffer-substring start end))))

; extraction

(defun phox-output ()

"Interactive function :
send output command to phox in order to obtain programs
extracted from proofs of all compiled theorems."


(interactive)
(proof-shell-invisible-command  "output"))

(defun phox-output-theorem (name)
"Interactive function :
ask for the name of a theorem and send an output command to PhoX for it
in order to obtain a programm extracted from the known proof of this theorem."
  (interactive "stheorem : ")
  (proof-shell-invisible-command (concat "output " name)))

(defun phox-output-theorem-on-cursor()
"Interactive function :
send an output command to PhoX for the theorem which name is under the cursor
in order to obtain a programm extracted from the known proof of this theorem."
  (interactive)
  (let (start
	end
;	(syntax (char-to-string (char-syntax ?\.)))
	)
    (save-excursion
;      (modify-syntax-entry ?\. "w") ; à modifier globablement ?
      (forward-word 1)
      (setq start (point))
      (forward-word -1)
      (setq end (point)))
;      (modify-syntax-entry ?\.  syntax)
      (if (char-equal (char-after (- end 1)) ?\.)(setq end (- end 1)))
    (phox-output-theorem (buffer-substring start end))))

; Definitions of lambda-mu terms (tdef nom_de_term = terme.) and
; normalization (eval term.) have to be "visible" proof commands.

;; menu

  (defvar phox-extraction-menu
    '("Extraction"
      ["Program extraction enabled"
       phox-toggle-extraction
       :style radio
       :selected(string-match "\-f$" phox-prog-name)
       ]
      ["------------------------------" nil nil
       ]
      ["Compile theorem on cursor" phox-compile-theorem-on-cursor
       :active(string-match "\-f$" phox-prog-name)
       ]
      ["Extraction for theorem on cursor" phox-output-theorem-on-cursor
       :active(string-match "\-f$" phox-prog-name)
       ]
      ["Extraction for all compiled theorems" phox-output
       :active(string-match "\-f$" phox-prog-name)
       ]
      ["------------------------------" nil nil
       ]
      ["Compile theorem : " phox-compile-theorem
       :active(string-match "\-f$" phox-prog-name)
       ]
      ["Extraction for theorem : " phox-output-theorem
       :active(string-match "\-f$" phox-prog-name)
       ]
      )
"A list of menu items to deal with program extraction.
Warning, program extraction is still experimental
and can disturb the prover !"
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'phox-extraction)
