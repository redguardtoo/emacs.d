;; -*- coding: utf-8; lexical-binding: t; -*-

(my-run-with-idle-timer 2 (lambda ()
                            (require 'pdf-view)))

;; {{ grep pdf
(defvar my-pdfgrep-program "pdfgrep"
  "Pdf grep program.")

(defvar my-pdfgrep-options "-H -n"
  "Pdf grep program options.")

(defvar my-pdfgrep-ignore-case t
  "Ignore case when grepping pdf.")

(defun my-pdfgrep-in-directory ()
  "Grep pdf files in current or specific directory."
  (interactive)
  (let* ((root (read-directory-name "Directory: "))
         (default-directory root)
         (case-fold-search t)
         (keyword (read-from-minibuffer "Keyword: " (thing-at-point 'symbol)))
         (cmd (format "%s %s %s -r %s"
                      my-pdfgrep-program
                      my-pdfgrep-options
                      (if my-pdfgrep-ignore-case "-i" "")
                      keyword))
         (lines (split-string (shell-command-to-string cmd) "[\r\n]+" t))
         path
         page
         text
         cands
         selected)
    (cond
     ((and lines (> (length lines) 0))
      (dolist (line lines)
        (when (string-match "^\\(.+\\.pdf\\):\\([0-9]+\\):\\(.*\\)$" line)
          (setq path (match-string 1 line))
          (setq page (match-string 2 line))
          (setq text (match-string 3 line))
          (push (cons (format "%s:%s: %s"
                              (file-name-base path)
                              page
                              (string-trim text))
                      (list path (string-to-number page) text))
                cands)))
      (setq cands (nreverse cands))
      (when (setq selected (completing-read (format "Grep in %s:" root)
                                            cands))
        (setq selected (cdr (assoc selected cands)))
        (find-file (nth 0 selected))
        (pdf-view-goto-page (nth 1 selected))
        (my-ensure 'pdf-isearch)
        (pdf-isearch-hl-matches nil (pdf-isearch-search-page keyword) t)))

     (t
      (message "Found nothing.")))))
;; }}

(provide 'init-pdf)
;;; init-pdf.el ends here
