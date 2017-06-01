;;; company-statistics.el --- Sort candidates using completion history  -*- lexical-binding: t -*-

;; Copyright (C) 2014-2017  Free Software Foundation, Inc.

;; Author: Ingo Lohmar <i.lohmar@gmail.com>
;; URL: https://github.com/company-mode/company-statistics
;; Version: 0.2.3
;; Keywords: abbrev, convenience, matching
;; Package-Requires: ((emacs "24.3") (company "0.8.5"))

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; Package installed from elpa.gnu.org:
;;
;;   (add-hook 'after-init-hook #'company-statistics-mode)
;;
;; Manually installed: make sure that this file is in load-path, and
;;
;;   (require 'company-statistics)
;;   (company-statistics-mode)
;;
;; Every time a candidate is chosen using company-mode, we keep track of this
;; (for a limited amount of recent choices).  When presenting completion
;; candidates next time, they are sorted according to the score thus acquired.
;;
;; The same candidate might occur in different modes, projects, files etc., and
;; possibly has a different meaning each time.  Therefore along with the
;; completion, we store some context information.  In the default (heavy)
;; configuration, we track the overall frequency, the major-mode of the buffer,
;; the last preceding keyword, the parent symbol, and the filename (if it
;; applies), and the same criteria are used to score all possible candidates.

;;; Code:

(require 'company)

(defgroup company-statistics nil
  "Completion candidates ranking by historical statistics."
  :group 'company)

(defcustom company-statistics-size 400
  "Number of completion choices that `company-statistics' keeps track of.
As this is a global cache, making it too small defeats the purpose."
  :type 'integer
  :initialize #'custom-initialize-default
  :set #'company-statistics--log-resize)

(defcustom company-statistics-file
  (concat user-emacs-directory "company-statistics-cache.el")
  "File to save company-statistics state."
  :type 'string)

(defcustom company-statistics-auto-save t
  "Whether to save the statistics when leaving emacs."
  :type 'boolean)

(defcustom company-statistics-auto-restore t
  "Whether to restore statistics when company-statistics is enabled and has
not been used before."
  :type 'boolean)

(defcustom company-statistics-capture-context #'company-statistics-capture-context-heavy
  "Function called with single argument (t if completion started manually).
This is the place to store any context information for a completion run."
  :type 'function)

(defcustom company-statistics-score-change #'company-statistics-score-change-heavy
  "Function called with completion choice.  Using arbitrary other info,
it should produce an alist, each entry labeling a context and the
associated score update: ((ctx-a . 1) (\"str\" . 0.5) (nil . 1)).  Nil is
the global context."
  :type 'function)

(defcustom company-statistics-score-calc #'company-statistics-score-calc-heavy
  "Function called with completion candidate.  Using arbitrary other info,
eg, on the current context, it should evaluate to the candidate's score (a
number)."
  :type 'function)

;; internal vars, persistence

(defvar company-statistics--scores nil
  "Store selection frequency of candidates in given contexts.")

(defvar company-statistics--log nil
  "Ring keeping a log of statistics updates.")

(defvar company-statistics--index nil
  "Index into the log.")

(defun company-statistics--init ()
  "Initialize company-statistics."
  (setq company-statistics--scores
        (make-hash-table :test #'equal :size company-statistics-size))
  (setq company-statistics--log (make-vector company-statistics-size nil)
        company-statistics--index 0))

(defun company-statistics--initialized-p ()
  (hash-table-p company-statistics--scores))

(defun company-statistics--log-resize (_option new-size)
  (when (company-statistics--initialized-p)
    ;; hash scoresheet auto-resizes, but log does not
    (let ((new-hist (make-vector new-size nil))
          ;; use actual length, to also work for freshly restored stats
          (company-statistics-size (length company-statistics--log)))
      ;; copy newest entries (possibly nil) to new-hist
      (dolist (i (number-sequence 0 (1- (min new-size company-statistics-size))))
        (let ((old-i (mod (+ (- company-statistics--index new-size) i)
                          company-statistics-size)))
          (aset new-hist i (aref company-statistics--log old-i))))
      ;; remove discarded log entry (when shrinking) from scores
      (when (< new-size company-statistics-size)
        (dolist (i (number-sequence
                    company-statistics--index
                    (+ company-statistics-size
                       company-statistics--index
                       (1- new-size))))
          (company-statistics--log-revert (mod i company-statistics-size))))
      (setq company-statistics--log new-hist)
      (setq company-statistics--index (if (<= new-size company-statistics-size)
                                          0
                                        company-statistics-size))))
  (setq company-statistics-size new-size))

(defun company-statistics--save ()
  "Save statistics."
  (with-temp-buffer
    (set-buffer-multibyte nil)
    (let (print-level print-length)
      (encode-coding-string
       (format
        "%S"
        `(setq
          company-statistics--scores ,company-statistics--scores
          company-statistics--log ,company-statistics--log
          company-statistics--index ,company-statistics--index))
       'utf-8 nil (current-buffer))
      (let ((coding-system-for-write 'binary))
        (write-region nil nil company-statistics-file)))))

(defun company-statistics--maybe-save ()
  (when (and (company-statistics--initialized-p)
             company-statistics-auto-save)
    (company-statistics--save)))

(defun company-statistics--load ()
  "Restore statistics."
  (load company-statistics-file 'noerror nil 'nosuffix))

;; score calculation for insert/retrieval --- can be changed on-the-fly

(defun company-statistics-score-change-light (_cand)
  "Count for global score and mode context."
  (list (cons nil 1)
        (cons major-mode 1)))           ;major-mode is never nil

(defun company-statistics-score-calc-light (cand)
  "Global score, and bonus for matching major mode."
  (let ((scores (gethash cand company-statistics--scores)))
    (if scores
        ;; cand may be in scores and still have no global score left
        (+ (or (cdr (assoc nil scores)) 0)
           (or (cdr (assoc major-mode scores)) 0))
      0)))

(defvar company-statistics--context nil
  "Current completion context, a list of entries searched using `assoc'.")

(defun company-statistics--last-keyword ()
  "Return last keyword, ie, text of region fontified with the
font-lock-keyword-face up to point, or nil."
  (let ((face-pos (point)))
    (while (and (number-or-marker-p face-pos)
                (< (point-min) face-pos)
                (not (eq (get-text-property (1- face-pos) 'face)
                         'font-lock-keyword-face)))
      (setq face-pos
            (previous-single-property-change face-pos 'face nil (point-min))))
    (when (and (number-or-marker-p face-pos)
               (eq (get-text-property (max (point-min) (1- face-pos)) 'face)
                   'font-lock-keyword-face))
      (list :keyword
            (buffer-substring-no-properties
             (previous-single-property-change face-pos 'face nil (point-min))
             face-pos)))))

(defun company-statistics--parent-symbol ()
  "Return symbol immediately preceding current completion prefix, or nil.
May be separated by punctuation, but not by whitespace."
  ;; expects to be at start of company-prefix; little sense for lisps
  (let ((preceding (save-excursion
                     (unless (zerop (skip-syntax-backward "."))
                       (substring-no-properties (symbol-name (symbol-at-point)))))))
    (when preceding
      (list :symbol preceding))))

(defun company-statistics--file-name ()
  "Return buffer file name, or nil."
  (when buffer-file-name
    (list :file buffer-file-name)))

(defun company-statistics-capture-context-heavy (_manual)
  "Calculate some context, once for the whole completion run."
  (save-excursion
    (backward-char (length company-prefix))
    (setq company-statistics--context
          (delq nil
                (list (company-statistics--last-keyword)
                      (company-statistics--parent-symbol)
                      (company-statistics--file-name))))))

(defun company-statistics-score-change-heavy (_cand)
  "Count for global score, mode context, last keyword, parent symbol,
buffer file name."
  (let ((last-kwd (assoc :keyword company-statistics--context))
        (parent-symbol (assoc :symbol company-statistics--context))
        (file (assoc :file company-statistics--context)))
    (nconc                                ;when's nil is removed
     (list (cons nil 1)
           (cons major-mode 1)) ;major-mode is never nil
     ;; only add pieces of context if non-nil
     (when last-kwd (list (cons last-kwd 1)))
     (when parent-symbol (list (cons parent-symbol 1)))
     (when file (list (cons file 1))))))

(defun company-statistics-score-calc-heavy (cand)
  "Global score, and bonus for matching major mode, last keyword, parent
symbol, buffer file name."
  (let ((scores (gethash cand company-statistics--scores))
        (last-kwd (assoc :keyword company-statistics--context))
        (parent-symbol (assoc :symbol company-statistics--context))
        (file (assoc :file company-statistics--context)))
    (if scores
        ;; cand may be in scores and still have no global score left
        (+ (or (cdr (assoc nil scores)) 0)
           (or (cdr (assoc major-mode scores)) 0)
           ;; some context may not apply, make sure to not get nil context
           (or (cdr (when last-kwd (assoc last-kwd scores))) 0)
           (or (cdr (when parent-symbol (assoc parent-symbol scores))) 0)
           (or (cdr (when file (assoc file scores))) 0))
      0)))

;; score manipulation in one place --- know about hash value alist structure

(defun company-statistics--alist-update (alist updates merger &optional filter)
  "Return new alist with conses from ALIST.  Their cdrs are updated
to (merger cdr update-cdr) if the UPDATES alist contains an entry with an
equal-matching car.  If FILTER called with the result is non-nil, remove
the cons from the result.  If no matching cons exists in ALIST, add the new
one.  ALIST structure and cdrs may be changed!"
  (let ((filter (or filter 'ignore))
        (updated alist)
        (new nil))
    (mapc
     (lambda (upd)
       (let ((found (assoc (car upd) alist)))
         (if found
             (let ((result (funcall merger (cdr found) (cdr upd))))
               (if (funcall filter result)
                   (setq updated (delete found updated))
                 (setcdr found result)))
           (push upd new))))
     updates)
    (nconc updated new)))

(defun company-statistics--scores-add (cand score-updates)
  (puthash cand
           (company-statistics--alist-update
            (gethash cand company-statistics--scores)
            score-updates
            #'+)
           company-statistics--scores))

(defun company-statistics--log-revert (&optional index)
  "Revert score updates for log entry.  INDEX defaults to
`company-statistics--index'."
  (let ((hist-entry
         (aref company-statistics--log
               (or index company-statistics--index))))
    (when hist-entry                    ;ignore nil entry
      (let* ((cand (car hist-entry))
             (score-updates (cdr hist-entry))
             (new-scores
              (company-statistics--alist-update
               (gethash cand company-statistics--scores)
               score-updates
               #'-
               #'zerop)))
        (if new-scores                    ;sth left
            (puthash cand new-scores company-statistics--scores)
          (remhash cand company-statistics--scores))))))

(defun company-statistics--log-store (result score-updates)
  "Insert/overwrite result and associated score updates."
  (aset company-statistics--log company-statistics--index
        (cons result score-updates))
  (setq company-statistics--index
        (mod (1+ company-statistics--index) company-statistics-size)))

;; core functions: updater, actual sorting transformer, minor-mode

(defun company-statistics--start (manual)
  (funcall company-statistics-capture-context manual))

(defun company-statistics--finished (result)
  "After completion, update scores and log."
  (let* ((score-updates (funcall company-statistics-score-change result))
         (result (substring-no-properties result)))
    (company-statistics--scores-add result score-updates)
    (company-statistics--log-revert)
    (company-statistics--log-store result score-updates)))

(defun company-sort-by-statistics (candidates)
  "Sort candidates by historical statistics.  Stable sort, so order is only
changed for candidates distinguishable by score."
  (setq candidates
        (sort candidates
              (lambda (cand1 cand2)
                (>  (funcall company-statistics-score-calc cand1)
                    (funcall company-statistics-score-calc cand2))))))

;;;###autoload
(define-minor-mode company-statistics-mode
  "Statistical sorting for company-mode.  Ranks completion candidates by
the frequency with which they have been chosen in recent (as given by
`company-statistics-size') history.

Turning this mode on and off preserves the statistics.  They are also
preserved automatically between Emacs sessions in the default
configuration.  You can customize this behavior with
`company-statistics-auto-save', `company-statistics-auto-restore' and
`company-statistics-file'."
  nil nil nil
  :global t
  (if company-statistics-mode
      (progn
        (unless (company-statistics--initialized-p)
          (if (and company-statistics-auto-restore
                   (company-statistics--load))
              ;; maybe of different size
              (company-statistics--log-resize nil company-statistics-size)
            (company-statistics--init)))
        (add-to-list 'company-transformers
                     'company-sort-by-statistics 'append)
        (add-hook 'company-completion-started-hook
                  'company-statistics--start)
        (add-hook 'company-completion-finished-hook
                  'company-statistics--finished))
    (setq company-transformers
          (delq 'company-sort-by-statistics company-transformers))
    (remove-hook 'company-completion-started-hook
                 'company-statistics--start)
    (remove-hook 'company-completion-finished-hook
                 'company-statistics--finished)))

(add-hook 'kill-emacs-hook 'company-statistics--maybe-save)

(provide 'company-statistics)
;;; company-statistics.el ends here
