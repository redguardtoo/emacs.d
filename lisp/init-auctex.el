(require-package 'auctex)

(add-hook 'Latex-mode-hook
          (lambda ()
            (Latex-add-enviroments
             '("theorem" Latex-env-label)
             '("prop" Latex-env-label)
             '("lemma" Latex-env-label)
             '("definition" Latex-env-label)
             '("cor" Latex-env-label)
             '("conj" Latex-env-label)
             '("remark" Latex-env-label)
             '("axiom" Latex-env-label)
             '("eq" Latex-env-label))))
(add-hook 'LaTeX-mode-hook 'turn-on-auto-fill)

(setq TeX-auto-save t)
(setq TeX-parse-self t)
(setq-default TeX-engine 'xetex)
(setq TeX-save-query nil
;; auctex will NOT query before saving buffers, when C-c C-c
)
(setq TeX-auto-untabify t
;; convert TABs to spaces when saving a buffer, Since TABs may confuse
;; auctex's error message parsing
)
(setq TeX-electric-escape t
;; If this is non-nil when AUCTEX is loaded, the TEX escape character
;; ‘\’ will be bound to TeX-electric-macro
)
(setq reftex-plug-into-AUCTeX t
;; load reftex
)
(add-hook 'LaTeX-mode-hook 'turn-on-reftex
;; Turn on RefTeX mode for all latex files
)
(setq reftex-cite-prompt-optional-args t)
(setq reftex-auto-view-crossref 'window)
(setq reftex-ref-macro-prompt nil)
(setq reftex-label-alist
      '(("theorem" ?T "thr:" "~\\ref{%s}" t ("theorem" "th.") -3)
	("prop"    ?P "pr:"  "~\\ref{%s}" t ("proposition" "pr.") -3)
	("lemma"   ?L "lm:"  "~\\ref{%s}" t ("lemma" "lem.") -3)
	("cor"     ?C "cr:"  "~\\ref{%s}" t ("corollary" "cor.") -3)
	("conj"    ?J "cj:"  "~\\ref{%s}" t ("conjecture" "conj.") -3)
	("axiom"   ?A "ax:"  "~\\ref{%s}" t ("axiom" "axi.") -3)
	("definition" ?D "df:" "~\\ref{%s}" t ("definition" "def.") -3)
	("remark"  ?R "rmk:" "~\\ref{%s}" t ("remark" "rem.") -3)
	("eg"      ?E "eg:"  "~\\ref{%s}" t ("example" "eg.") -3)
))

;; A nice command to lauch all LaTeX compilation(s) in one step.
;; Don't know the author name by you can find the original source at
;; http://www.emacswiki.org/emacs/TN
;; (require 'tex-buf)
(defun TeX-command-default (name)
  "Next TeX command to use. Most of the code is stolen from `TeX-command-query'."
  (cond ((if (string-equal name TeX-region)
			     (TeX-check-files (concat name "." (TeX-output-extension))
					      (list name)
					      TeX-file-extensions)
			   (TeX-save-document (TeX-master-file)))
			 TeX-command-default)
			((and (memq major-mode '(doctex-mode latex-mode))
			      (TeX-check-files (concat name ".bbl")
					       (mapcar 'car
						       (LaTeX-bibliography-list))
					       BibTeX-file-extensions))
			 ;; We should check for bst files here as well.
			 TeX-command-BibTeX)
			((TeX-process-get-variable name
						   'TeX-command-next
						   TeX-command-Show))
			(TeX-command-Show)))


(defcustom TeX-texify-Show nil "Start view-command at end of TeX-texify?" :type 'boolean :group 'TeX-command)
(defcustom TeX-texify-max-runs-same-command 5 "Maximal run number of the same command" :type 'integer :group 'TeX-command)

(defun TeX-texify-sentinel (&optional proc sentinel)
  "Non-interactive! Call the standard-sentinel of the current LaTeX-process.
If there is still something left do do start the next latex-command."
  (set-buffer (process-buffer proc))
  (funcall TeX-texify-sentinel proc sentinel)
  (let ((case-fold-search nil))
    (when (string-match "\\(finished\\|exited\\)" sentinel)
      (set-buffer TeX-command-buffer)
      (unless (plist-get TeX-error-report-switches (intern (TeX-master-file)))
	(TeX-texify)))))

(defun TeX-texify ()
  "Get everything done."
  (interactive)
  (let ((nextCmd (TeX-command-default (TeX-master-file)))
	proc)
    (if (and (null TeX-texify-Show)
	     (equal nextCmd TeX-command-Show))
	(when  (called-interactively-p 'any)
	  (message "TeX-texify: Nothing to be done."))
      (TeX-command nextCmd 'TeX-master-file)
      (when (or (called-interactively-p 'any)
		(null (boundp 'TeX-texify-count-same-command))
		(null (boundp 'TeX-texify-last-command))
		(null (equal nextCmd TeX-texify-last-command)))
	(mapc 'make-local-variable '(TeX-texify-sentinel TeX-texify-count-same-command TeX-texify-last-command))
	(setq TeX-texify-count-same-command 1))
      (if (>= TeX-texify-count-same-command TeX-texify-max-runs-same-command)
	  (message "TeX-texify: Did %S already %d times. Don't want to do it anymore." TeX-texify-last-command TeX-texify-count-same-command)
	(setq TeX-texify-count-same-command (1+ TeX-texify-count-same-command))
	(setq TeX-texify-last-command nextCmd)
	(and (null (equal nextCmd TeX-command-Show))
	     (setq proc (get-buffer-process (current-buffer)))
	     (setq TeX-texify-sentinel (process-sentinel proc))
	     (set-process-sentinel proc 'TeX-texify-sentinel))))))

(add-hook 'LaTeX-mode-hook '(lambda () (local-set-key (kbd "C-c C-a") 'TeX-texify)))

;;(setq TeX-view-program-selection '((output-pdf "Okular")))
;;(setq TeX-view-program-list '(("Okular" "okular --unique %o#src:%n%b")))

(provide 'init-auctex)