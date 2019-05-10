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
(require 'gnus-util)

(defun dianyou-read-params (x)
  (nnir-read-parms (nnir-server-to-search-engine (car x))))

(defun dianyou-format-date (year month day)
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
  (let* ((a (split-string date "-")))
    (dianyou-format-date (nth 0 a) (nth 1 a) (nth 2 a))))

(defun dianyou-translate-date-shortcut (str)
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
  (cond
   ((string= word "f")
    "FROM")
   ((string= word "t")
    "TO")
   ((string= word "s")
    "SINCE")
   ((string= word "c")
    "CC")
   ;; 2018-09-03 or 18-09-03
   ((string-match "[0-9]\\{2,4\\}-[0-9]\\{1,2\\}-[0-9]\\{1,2\\}" word)
    (dianyou-format-dash-date word))
   ;; 180903
   ((string-match "[0-9]\\{6\\}" word)
    (dianyou-format-date (substring word 0 2)
                         (substring word 2 4)
                         (substring word 4 6)))

   ;; 20180903
   ((string-match "[0-9]\\{8\\}" word)
    (dianyou-format-date (substring word 0 4)
                         (substring word 4 6)
                         (substring word 6 8)))

   ((and (not (string= word ""))
         (string-match "^\\([0-9][0-9]?y\\)?\\([0-9][0-9]?m\\)?\\([0-9][0-9]?w\\)?\\([0-9][0-9]?d\\)?$" word))
    (dianyou-translate-date-shortcut word))
  (t
    word)))

(defun dianyou-read-query ()
  (interactive)
  (let* ((q (read-string "Query: " nil 'nnir-search-history))
         (words (split-string q " ")))
    (string-join (mapcar 'dianyou-translate words) " ")))

(defun dianyou-group-make-nnir-group ()
  "Create an nnir group.  Prompt for a search query and determine
the groups to search as follows: if called from the *Server*
buffer search all groups belonging to the server on the current
line; if called from the *Group* buffer search any marked groups,
or the group on the current line, or all the groups under the
current topic. Calling with a prefix-arg prompts for additional
search-engine specific constraints."
  (interactive)
  (let* ((group-spec (if (gnus-server-server-name)
                         (list (list (gnus-server-server-name)))
                       (nnir-categorize
                        (or gnus-group-marked
                            (if (gnus-group-group-name)
                                (list (gnus-group-group-name))
                              (cdr (assoc (gnus-group-topic-name) gnus-topic-alist))))
                        gnus-group-server)))
         (query-spec (apply
                      'append
                      (list (cons 'query
                                  (dianyou-read-query)))
                      (mapcar #'dianyou-read-params group-spec))))
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

(provide 'dianyou)
;;; dianyou.el ends here