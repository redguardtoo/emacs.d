;; emacs.d-test.el --- unit tests for redguardtoo/emacs.d -*- coding: utf-8; lexical-binding: t; -*-


;;; Commentary:
(require 'ert)
(require 'cl-lib)

(add-to-list 'load-path
             (expand-file-name "../lisp" (file-name-directory load-file-name)))
(require 'init-spelling)

(ert-deftest test-general ()
  (should t))

(ert-deftest my-spell-check-buffer-reports-missing-backend ()
  (cl-letf (((symbol-value 'ispell-program-name) nil)
            ((symbol-function 'executable-find) (lambda (_program) nil)))
    (let ((error-data (should-error (my-spell-check-buffer) :type 'user-error)))
      (should (string-match-p "Install aspell or hunspell"
                              (error-message-string error-data))))))

(ert-deftest my-spell-check-buffer-runs-wucuo-in-normal-mode ()
  (let (checked-mode)
    (cl-letf (((symbol-value 'ispell-program-name) "aspell")
              ((symbol-function 'executable-find) (lambda (_program) "/fake/aspell"))
              ((symbol-function 'my-ensure) (lambda (_feature) t))
              ((symbol-function 'wucuo-spell-check-internal)
               (lambda () (setq checked-mode wucuo-flyspell-start-mode))))
      (my-spell-check-buffer)
      (should (equal checked-mode "normal")))))

(ert-run-tests-batch-and-exit)
