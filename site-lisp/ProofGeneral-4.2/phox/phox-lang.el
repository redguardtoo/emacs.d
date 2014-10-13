;; Exp 2012/04/06 07:05:41 12.1
;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;; messages in various languages

(provide 'phox-lang)
(require 'cl)				; for case

(defvar phox-lang
  (let* ((s (or (getenv "LC_ALL")
		(getenv "LANG")
		(getenv "LANGUAGE")))
	 (loc   (and s 
		     (> (length s) 1)
		     (substring s 0 2))))
    (cond
      ((or (string= loc "en") (string= loc "us")) 'en)
      ((string= loc "fr") 'fr)
      (t 'en))))

(defun phox-lang-absurd ()
  (case phox-lang
    (en "By absurd")
    (fr "Par l'absurde")))

(defun phox-lang-suppress (s)
  (case phox-lang
    (en (concat "Remove hypothesis " s " (if it became useless)"))
    (fr (concat  "Supprimer l'hypothèse " s " (si elle est devenue inutile)"))))

(defun phox-lang-opendef ()
  (case phox-lang
    (en "Expand the definition: ")
    (fr "Ouvre la définition : ")))

(defun phox-lang-instance (s)
  (case phox-lang
    (en (concat "Choose " s " = "))
    (fr (concat  "Choisissons " s " = "))))

(defun phox-lang-open-instance (s)
  (case phox-lang
    (en (concat "Choose " s " =  \\[ \\]"))
    (fr (concat  "Choisissons " s " = \\[ \\]"))))

(defun phox-lang-lock (s)
  (case phox-lang
    (en (concat "Lock variable " s))
    (fr (concat  "Vérouille la variable " s))))

(defun phox-lang-unlock (s)
  (case phox-lang
    (en (concat "Unlock variable " s))
    (fr (concat  "Dévérouille la variable " s))))

(defun phox-lang-prove (s)
  (case phox-lang
    (en (concat "Let us prove \\[" s "\\]"))
    (fr (concat "Prouvons \\[" s "\\]"))))

(defun phox-lang-let (s)
  (case phox-lang
    (en (concat "Let \\[ \\] = \\[" s "\\]"))
    (fr (concat "Définissons \\[ \\] = \\[" s "\\]"))))
