;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                      PARAMÉTRAGE du MODE outline
;;--------------------------------------------------------------------------;;

(require 'outline)

(declare-function phox-lang-absurd "nofile")
(declare-function phox-lang-suppress "nofile")
(declare-function phox-lang-instance "nofile")
(declare-function phox-lang-open-instance "nofile")
(declare-function phox-lang-opendef "nofile")
(declare-function phox-lang-unlock "nofile")
(declare-function phox-lang-lock "nofile")
(declare-function phox-lang-prove "nofile")
(declare-function phox-lang-let "nofile")


(defconst phox-outline-title-regexp "\\((\\*[ \t\n]*title =\\)")
(defconst phox-outline-section-regexp "\\((\\*\\*+\\)")
(defconst phox-outline-save-regexp "\\((\\*#\\)")
(defconst
 phox-outline-theo-regexp
 "\\((\\*lem\\)\\|\\((\\*prop\\)\\|\\((\\*fact\\)\\|\\((\\*theo\\)\\|\\((\\*def\\)\\|\\((\\*cst\\)")
(defconst
 phox-outline-theo2-regexp
 "\\(lem\\)\\|\\(prop\\)\\|\\(fact\\)\\|\\(theo\\)\\|\\(def\\)\\|\\(cst\\)\\|\\(claim\\)\\|\\(new_\\)")

(defconst
  phox-outline-regexp
  (concat
   phox-outline-title-regexp "\\|"
   phox-outline-section-regexp "\\|"
   phox-outline-save-regexp "\\|"
   phox-outline-theo-regexp "\\|"
   phox-outline-theo2-regexp))

(defconst phox-outline-heading-end-regexp "\\(\\*)[ \t]*\n\\)\\|\\(\\.[ \t]*\n\\)")

;;(if phox-outline
;;    (add-hook 'phox-mode-hook (lambda () (outline-minor-mode 1)))
;;  )

(defun phox-outline-level()
  "Find the level of current outline heading in some PhoX libraries."
  (let ((retour 0))
    (save-excursion
      (cond ((looking-at phox-outline-title-regexp) 1)
	    ((looking-at phox-outline-section-regexp)
	     (min 6 (- (match-end 0) (match-beginning 0)))) ; valeur maxi 6
	    ((looking-at phox-outline-theo-regexp) 7)
	    ((looking-at  (concat phox-outline-save-regexp "\\|"
				 phox-outline-theo2-regexp )
			 ) 8)
	    )
      )))

(defun phox-setup-outline ()
  "Set up local variable for outline mode"
  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp phox-outline-heading-end-regexp)
  (make-local-variable 'outline-regexp)
  (setq outline-regexp phox-outline-regexp)
  (make-local-variable 'outline-level)
  (setq outline-level 'phox-outline-level)
  (outline-minor-mode 1)
)

(provide 'phox-outline)
