;; isar-autotest.el: tests of Isar Proof General.
;;
;; You can run these by issuing "make test.isar" in PG home dir.
;;
;; isar-autotest.el,v 12.2 2012/09/02 21:44:46 da Exp
;;

(defvar isar-long-tests nil
  "Whether or not to perform lengthy tests")

(require 'pg-autotest)

(eval-when (compile)
  (require 'cl)
  (require 'proof-site)
  (proof-ready-for-assistant 'isar))


(declare-function isar-tracing:auto-quickcheck-toggle "isar.el")
(declare-function isar-tracing:auto-solve-direct-toggle "isar.el")
(declare-function isar-proof:parallel-proofs-toggle "isar.el")

(unless noninteractive

  (pg-autotest start) ; can add 'debug flag for debug-on-error

  (pg-autotest log ".autotest.log")  ; convention

  (pg-autotest timestart 'total)

  (pg-autotest remark "Testing standard Example.thy, Example-Xsym.thy")
  (pg-autotest script-wholefile "isar/Example.thy")

  ;; Test Trac#344 (nested spans bug with old-style undo)
  ;; TODO: should test with both undo styles
  (pg-autotest eval (proof-retract-buffer))
  (proof-shell-wait)
  (goto-char 135) ; first line
  (pg-autotest eval (proof-goto-point))
  (proof-shell-wait)
  (pg-autotest eval (proof-retract-buffer))
  (proof-shell-wait)
  (goto-char 135) ; first line
  (pg-autotest eval (proof-goto-point))
  (proof-shell-wait)
  (pg-autotest eval (proof-process-buffer))
  (pg-autotest assert-full)
  

  ;; Speed up prover
  (pg-autotest eval (isar-tracing:auto-quickcheck-toggle 0))
  (pg-autotest eval (isar-tracing:auto-solve-direct-toggle 0)) ; autosolve hammers this!
  (pg-autotest eval (proof-full-annotation-toggle 0))
  (pg-autotest eval (isar-proof:parallel-proofs-toggle 0))
  (proof-shell-wait)

  (pg-autotest script-wholefile "isar/Example-Tokens.thy")

  (pg-autotest remark "Testing prove-as-you-go (not replay)")
  (find-file ".autotest.thy")
  (erase-buffer) ; just in case exists
  (setq buffer-file-name nil)
  (pg-autotest eval (proof-electric-terminator-toggle 1))
  (pg-autotest eval (insert "theory Example imports Main begin ")) ; no \n
  (proof-electric-terminator)
  (pg-autotest eval (insert "theorem and_comms: \"A & B --> B & A\"\n"))
  (proof-electric-terminator)
  (pg-autotest eval (insert "apply auto done\n"))
  (pg-autotest eval (insert "end"))
  (proof-electric-terminator)
  (pg-autotest assert-full)
  ;; Test Trac#138
  (pg-autotest eval (proof-undo-last-successful-command))
  (proof-shell-wait)
  (pg-autotest eval (proof-goto-end-of-locked))
  (pg-autotest eval (insert "(* this is a comment *)"))
  (pg-autotest eval (proof-goto-point))
  (proof-shell-wait)
  (pg-autotest eval (skip-chars-backward " \n\t"))
  (pg-autotest eval (insert " ")) ;; shouldn't give read-only error!
  (set-buffer-modified-p nil)
  (kill-buffer ".autotest.thy")

  (pg-autotest remark "Now in tokens mode")
  (pg-autotest eval (proof-unicode-tokens-toggle))
  (pg-autotest script-wholefile "isar/Example-Tokens.thy")

  (pg-autotest remark "Testing random jumps and edits")
  (pg-autotest script-randomjumps "isar/Example.thy" 8)

  (when isar-long-tests
      (pg-autotest remark "Larger files...")
      (pg-autotest script-wholefile "etc/isar/AHundredTheorems.thy")
      (pg-autotest script-wholefile "isar/ex/Tarski.thy")
      (pg-autotest script-randomjumps "isar/ex/Tarski.thy" 10)) ; better test?


  (pg-autotest remark "Testing restarting the prover")
  (pg-autotest quit-prover)


  (pg-autotest remark	         "Simple test of multiple file behaviour:")
  (pg-autotest script-wholefile  "etc/isar/multiple/C.thy")
  (pg-autotest assert-processed   "etc/isar/multiple/C.thy")
  (pg-autotest assert-processed   "etc/isar/multiple/A.thy")
  (pg-autotest assert-processed   "etc/isar/multiple/B.thy")
  (pg-autotest retract-file       "etc/isar/multiple/B.thy")
  (pg-autotest assert-unprocessed "etc/isar/multiple/B.thy")
  (pg-autotest assert-unprocessed "etc/isar/multiple/C.thy")
  (pg-autotest assert-processed   "etc/isar/multiple/A.thy")


  (pg-autotest quit-prover)
  
  (pg-autotest remark	"Complete")
  (pg-autotest timetaken 'total)

  (pg-autotest exit)

  )
