;; emacs.d-test.el --- unit tests for redguardtoo/emacs.d -*- coding: utf-8 -*-


;;; Commentary:
(require 'ert)

(ert-deftest test-pinyin-regex-builder ()
  (should (equal (my-pinyinlib-build-regexp-string ":[]") ":[]"))
  (should (> (length (my-pinyinlib-build-regexp-string ":ab")) 50))
  (should (string-match-p (my-pinyinlib-build-regexp-string "cs") "测试"))
  (should (string-match-p (my-pinyinlib-build-regexp-string "zyz") "朱元璋"))
  (should (string-match-p (my-pinyinlib-build-regexp-string "wm") "我们")))

(ert-run-tests-batch-and-exit)
