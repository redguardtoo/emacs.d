;;; dianyou.el --- Analyze mails in Gnus

;; Copyright (C) 2019 Chen Bin
;;
;; Version: 0.0.1
;; Keywords: email
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: http://github.com/usrname/dianyou
;; Package-Requires: ((emacs "24.4"))

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; `dianyou-group-make-nnir-group' to search mails.

;;; Code:
(require 'gnus-group)
(require 'gnus-sum)
(require 'gnus-util)

(defvar dianyou-debug nil "Print debug information.")

(defun dianyou-read-params (x)
  "Read parameters from X."
  (nnir-read-parms (nnir-server-to-search-engine (car x))))

(defun dianyou-format-date (year month day)
  "Format date string from YEAR, MONTH, and DAY."
  (let* ((months '("Jan"
                   "Feb"
                   "Mar"
                   "Apr"
                   "May"
                   "Jun"
                   "Jul"
                   "Aug"
                   "Sep"
                   "Oct"
                   "Nov"
                   "Dec")))
    (when (stringp year)
      (setq year (string-to-number year)))
    (cond
     ((and (< year 100) (> year 90))
      (setq year (+ year 1900)))
     ((and (< year 100))
      (setq year (+ year 2000))))

    (when (stringp month)
      (setq month (string-to-number month)))

    (when (stringp day)
      (setq day (string-to-number day)))
    (format "%02d-%s-%d"
            day
            (nth (1- month) months)
            year)))

(defun dianyou-format-dash-date (date)
  "Format DATE in dash format."
  (let* ((a (split-string date "-")))
    (dianyou-format-date (nth 0 a) (nth 1 a) (nth 2 a))))

(defun dianyou-translate-date-shortcut (str)
  "Translate STR containing date shortcuts into IMAP format."
  (let* ((y 0) (m 0) (w 0) (d 0) seconds)
    (when (string-match "\\([0-9]\\{1,2\\}\\)y" str)
      (setq y (string-to-number (match-string 1 str))))
    (when (string-match "\\([0-9]\\{1,2\\}\\)m" str)
      (setq m (string-to-number (match-string 1 str))))
    (when (string-match "\\([0-9]\\{1,2\\}\\)w" str)
      (setq w (string-to-number (match-string 1 str))))
    (when (string-match "\\([0-9]\\{1,2\\}\\)d" str)
      (setq d (string-to-number (match-string 1 str))))
    (setq seconds (+ (* d 86400) ; 1 day
                     ;; 7 days
                     (* w 604800)
                     ;; 31 days
                     (* m 2678400)
                     ;; 365 days
                     (* y 31536000)))
    (dianyou-format-dash-date
     (format-time-string "%Y-%m-%d"
                         (time-subtract (current-time)
                                        (seconds-to-time seconds))))))

(defun dianyou-translate (word)
  "Translate WORD shortcuts."
  (cond
   ((string= word "f")
    "FROM")
   ((string= word "t")
    "TO")
   ((string= word "e")
    "TEXT")
   ((string= word "u")
    "SUBJECT")
   ((string= word "o")
    "OR")
   ((string= word "s")
    "SINCE")
   ((string= word "b")
    "BEFORE")
   ((string= word "c")
    "CC")
   ;; 2018-09-03 or 18-09-03
   ((string-match "^[0-9]\\{2,4\\}-[0-9]\\{1,2\\}-[0-9]\\{1,2\\}$" word)
    (dianyou-format-dash-date word))
   ;; 180903
   ((string-match "^[0-9]\\{6\\}$" word)
    (dianyou-format-date (substring word 0 2)
                         (substring word 2 4)
                         (substring word 4 6)))

   ;; 20180903
   ((string-match "^[0-9]\\{8\\}$" word)
    (dianyou-format-date (substring word 0 4)
                         (substring word 4 6)
                         (substring word 6 8)))

   ((and (not (string= word ""))
         (string-match "^\\([0-9][0-9]?y\\)?\\([0-9][0-9]?m\\)?\\([0-9][0-9]?w\\)?\\([0-9][0-9]?d\\)?$" word))
    (dianyou-translate-date-shortcut word))
  (t
    word)))

(defun dianyou-read-query ()
  "Read mail searching query."
  (interactive)
  (let* ((q (read-string "Query: " nil 'nnir-search-history))
         (words (split-string q " "))
         (query (string-join (mapcar 'dianyou-translate words) " ")))
    (if dianyou-debug (message "query=%s" query))
    query))

(defun dianyou-create-group-spec ()
  "Create group spec for searching."
  (cond
   ((eq major-mode 'gnus-summary-mode)
    (list (list
           (gnus-group-server gnus-newsgroup-name)
           (list gnus-newsgroup-name))))
   ((gnus-server-server-name)
    (list (list (gnus-server-server-name))))
   (t
    (nnir-categorize
     (or gnus-group-marked
         (if (gnus-group-group-name)
             (list (gnus-group-group-name))
           (cdr (assoc (gnus-group-topic-name) gnus-topic-alist))))
     gnus-group-server))))

;;;###autoload
(defun dianyou-group-make-nnir-group ()
  "Create an nnir group.
Prompt for search query and determine groups to search as follows:
In *Server* buffer search all groups belonging to current server;
In *Group* buffer search marked groups, or the current group,
or all the groups under the current topic;
In *Summary* buffer search the group current buffer belonging to.

The IMAP search syntax supports shortcut and more date format:
\"t\" equals \"TO\".
\"b\" equals \"BEFORE\".
\"e\" equals \"TEXT\".
\"u\" equals \"SUBJECT\".
\"o\" equals \"OR\".
\"c\" equals \"CC\".
\"f\" equals \"FROM\".
\"s\" equals \"SINCE\".
\"20180905\" or \"180905\" equals \"5-Sep-2018\".
\"2018-09-05\" or \"18-09-05\" equals \"5-Sep-2018\".
\"1y1m1w1d\" equals the date 1 year 1 month 1 week 1 day ago.
See https://tools.ietf.org/html/rfc3501#section-6.4.4 for IMAP SEARCH spec."
  (interactive)
  (let* ((group-spec (dianyou-create-group-spec))
         (query-spec (apply
                      'append
                      (list (cons 'query
                                  (dianyou-read-query)))
                      (mapcar #'dianyou-read-params group-spec))))
    (if dianyou-debug (message "group-spec=%s" group-spec))
    (gnus-group-read-ephemeral-group
     (concat "nnir-" (message-unique-id))
     (list 'nnir "nnir")
     nil
     nil
     nil
     nil
     (list
      (cons 'nnir-specs (list (cons 'nnir-query-spec query-spec)
                              (cons 'nnir-group-spec group-spec)))
      (cons 'nnir-artlist nil)))))

(defun dianyou-test-two-email-address (x y)
  "Test if email address X equals Y."
  (let* (x1 y1)
    ;; Tom W <tom.w@gmail.com> | tom.w@gmail.com (Tom W)
    (if (string-match "^[^<]*<\\([^ ]*\\)> *$" x)
        (setq x1 (match-string 1 x))
      (setq x1 (replace-regexp-in-string " *([^()]*) *" "" (if x x ""))))
    (if (string-match "^[^<]*<\\([^ ]*\\)> *$" y)
        (setq y1 (match-string 1 y))
      (setq y1 (replace-regexp-in-string " *([^ ]*) *" "" (if y y ""))))
    (string= x1 y1)))

;;;#autoload
(defun dianyou-summary-extract-mail-address(regexp)
  "Extract email address from email to/cc/from field in *Summary* buffer.
REGEXP is pattern to exclude email address.
For example, 'Tom|gmail' excludes address containing \"Tom\" or \"gmail\".
Final result is inserted into `kill-ring' and returned."
  (interactive
   (let* ((regexp (read-regexp "Regex to exclude mail address (OPTIONAL):")))
     (list regexp)))

  (let* ((rlt "") (i 0) header cc-to)
    (dolist (d gnus-newsgroup-data)
      (setq header (gnus-data-header d))
      (setq i (+ 1 i))
      (if (= (mod i 100) 0) (message "%s mails scanned ..." i))
      (when (vectorp header)
        (if (setq cc-to (mail-header-extra header))
            ;; (message "cc-to=%s cc=%s" cc-to (assoc 'Cc cc-to))
            (setq rlt (concat rlt
                              (cdr (assoc 'To cc-to))
                              ", "
                              (cdr (assoc 'Cc cc-to))
                              ", ")))
        (setq rlt (concat rlt (if (string= "" rlt) "" ", ")
                          (mail-header-from header) ", "))))
    ;; trim trailing ", "
    (setq rlt (split-string (replace-regexp-in-string (rx (* (any ", ")) eos)
                                                      ""
                                                      rlt) ", *"))

    ;; remove empty strings
    (setq rlt (delq nil (remove-if (lambda (s) (or (not s) (string= "" s)))
                                   rlt)))
    ;; remove actually duplicated mails
    (setq rlt (delq nil (remove-duplicates rlt
                                           :test 'dianyou-test-two-email-address
                                           :from-end t)))
    ;; exclude mails
    (when (and regexp (not (string= regexp "")))
      (setq rlt (delq nil (remove-if `(lambda (s)
                                        (string-match (concat "\\("
                                                              (replace-regexp-in-string "|" "\\\\|" ,regexp)
                                                              "\\)") s))
                                     rlt))))
    (cond
     ((> (length rlt) 0)
      (kill-new (mapconcat 'identity rlt ", "))
      (message "%d mail address => kill-ring" (length rlt)))
     (t
      (message "NO email address is found.")))
    rlt))

(provide 'dianyou)
;;; dianyou.el ends here