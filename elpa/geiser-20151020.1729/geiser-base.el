;;; geiser-base.el --- shared bits

;; Copyright (C) 2009, 2010, 2012, 2013, 2015  Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Settings and vars shared by all geiser modules, including little
;; utilities and emacsen compatibility bits.

;;; Emacs compatibility:

(require 'ring)

(eval-after-load "ring"
  '(when (not (fboundp 'ring-member))
     (defun ring-member (ring item)
       (catch 'found
         (dotimes (ind (ring-length ring) nil)
           (when (equal item (ring-ref ring ind))
             (throw 'found ind)))))))

(when (not (fboundp 'looking-at-p))
  (defsubst looking-at-p (regexp)
    (let ((inhibit-changing-match-data t))
      (looking-at regexp))))

;;; Utilities:

(defsubst geiser--chomp (str)
  (if (string-match-p ".*\n$" str) (substring str 0 -1) str))

(defun geiser--shorten-str (str len &optional sep)
  (let ((str-len (length str)))
    (if (<= str-len len)
        str
      (let* ((sep (or sep " ... "))
             (sep-len (length sep))
             (prefix-len (/ (- str-len sep-len) 2))
             (prefix (substring str 0 prefix-len))
             (suffix (substring str (- str-len prefix-len))))
        (format "%s%s%s" prefix sep suffix)))))

(defun geiser--region-to-string (begin &optional end)
  (let ((end (or end (point))))
    (when (< begin end)
      (let* ((str (buffer-substring-no-properties begin end))
             (pieces (split-string str nil t)))
        (mapconcat 'identity pieces " ")))))

(defun geiser--insert-with-face (str face)
  (let ((p (point)))
    (insert str)
    (put-text-property p (point) 'face face)))


(defmacro geiser--save-msg (&rest body)
  (let ((msg (make-symbol "msg")))
    `(let ((,msg (current-message)))
       ,@body
       (message ,msg))))

(put 'geiser--save-msg 'lisp-indent-function 0)

(defun geiser--del-dups (lst)
  (let (result)
    (dolist (e lst (nreverse result))
      (unless (member e result) (push e result)))))

(defsubst geiser--symbol-at-point ()
  (let ((thing (thing-at-point 'symbol)))
    (and thing (make-symbol thing))))

(defun geiser--cut-version (v)
  (when (string-match "\\([0-9]+\\(?:\\.[0-9]+\\)*\\).*" v)
    (match-string 1 v)))

(defun geiser--version< (v1 v2)
  (let ((v1 (geiser--cut-version v1))
        (v2 (geiser--cut-version v2)))
    (and v1 v2 (version< v1 v2))))

(provide 'geiser-base)
