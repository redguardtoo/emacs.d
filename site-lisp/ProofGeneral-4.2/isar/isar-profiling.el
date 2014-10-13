;; isar-profiling.el: simple profiling Isar Proof General.
;;
;; You can run these tests by issuing "make profile.isar" in PG home dir.
;;
;; isar-profiling.el,v 12.0 2011/10/13 10:54:50 da Exp
;;

(eval-when-compile
  (require 'cl))

(eval-when (compile)
  (require 'proof-site)
  (proof-ready-for-assistant 'isar))  

(declare-function isar-tracing:auto-solve-toggle "isar.el")
(declare-function isar-tracing:auto-quickcheck-toggle "isar.el")
(declare-function isar-proof:parallel-proofs-toggle "isar.el")

(require 'pg-autotest)
(require 'pg-dev)

(unless noninteractive

  (pg-autotest log ".profile.log")  ; convention

  (pg-autotest timestart 'total)

  (pg-autotest-find-file "etc/isar/AHundredTheorems.thy")
  (pg-autotest eval (proof-shell-ready-prover))
  (pg-autotest eval (isar-tracing:auto-solve-toggle 0)) ; autosolve hammers this!
  (pg-autotest eval (isar-tracing:auto-quickcheck-toggle 0))
  (pg-autotest eval (isar-proof:parallel-proofs-toggle 0))
  (pg-autotest eval (proof-full-annotation-toggle 0))
  (proof-shell-wait)

  ;; Simple profiling test.  Cf TRAC #324
  (pg-autotest timestart)
  (pg-autotest process-wholefile "etc/isar/AHundredTheorems.thy")
  (pg-autotest timetaken)

  ;; Same again with profiling
  (profile-pg)
  (pg-autotest timestart)
  (pg-autotest process-wholefile "etc/isar/AHundredTheorems.thy")
  (pg-autotest timetaken)
  (pg-autotest timestart)
  (pg-autotest process-wholefile "etc/isar/AHundredTheorems.thy")
  (pg-autotest timetaken)
  (pg-autotest timestart)
  (pg-autotest process-wholefile "etc/isar/AHundredProofs.thy")
  (pg-autotest timetaken)
  (elp-results)
  (let ((results 
	 (with-current-buffer "*ELP Profiling Results*"
	   (buffer-string))))
    (with-current-buffer pg-autotest-log
      (goto-char (point-min))
      (insert "ELP Profiling Results: \n" results "\n\n")))

  (pg-autotest exit)

  )
