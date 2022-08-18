;; emacs.d-test.el --- unit tests for redguardtoo/emacs.d -*- coding: utf-8 -*-


;;; Commentary:
(require 'ert)

(ert-deftest test-general ()
  (should t))

(ert-run-tests-batch-and-exit)
