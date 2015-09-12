;; Exp 2011/10/13 10:54:51 12.0
;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;; the proof by rules popup menu part
;;
;; Note : program extraction is still experimental This file is very
;; dependant of the actual state of our developments
;;--------------------------------------------------------------------------;;

(require 'pg-pbrpm)

(declare-function phox-lang-absurd "nofile")
(declare-function phox-lang-suppress "nofile")
(declare-function phox-lang-instance "nofile")
(declare-function phox-lang-open-instance "nofile")
(declare-function phox-lang-opendef "nofile")
(declare-function phox-lang-unlock "nofile")
(declare-function phox-lang-lock "nofile")
(declare-function phox-lang-prove "nofile")
(declare-function phox-lang-let "nofile")
(declare-function int-char "nofile")
(declare-function char= "nofile")

;;--------------------------------------------------------------------------;;
;; Syntactic functions
;;--------------------------------------------------------------------------;;
(setq
 pg-pbrpm-start-goal-regexp "^goal \\([0-9]+\\)/[0-9]+\\( (new)\\)?$"
 pg-pbrpm-start-goal-regexp-par-num 1
 pg-pbrpm-end-goal-regexp "^$"
 pg-pbrpm-start-hyp-regexp "^\\([A-Za-z0-9_.']+\\) := "
 pg-pbrpm-start-hyp-regexp-par-num 1
 pg-pbrpm-start-concl-regexp "^ *|- "
 pg-pbrpm-auto-select-regexp "\\(\\(\\(['a-zA-Z0-9]+\\)\\|\\([][><=/~&+*^%!{}:-]+\\)\\)\\(_+\\(\\(['a-zA-Z0-9]+\\)\\|\\([][><=/~&+*^%!{}:-]+\\)\\)\\)*\\)\\|\\(\\?[0-9]+\\)"
)


; TODO : deal with future invisible parentheses (french guillemots)
(defun phox-pbrpm-left-paren-p (char)
"Retrun t if the character is a left parenthesis : '(' or a french guillemot '<<'"
   (or
   (char-equal char (int-char 40))
   (char-equal char (int-char 171)))
)

(defun phox-pbrpm-right-paren-p (char)
"Retrun t if the character is a right parenthesis ')' or a french guillemot '>>'"
   (or
   (char-equal char (int-char 41))
   (char-equal char (int-char 187)))
)


(defun phox-pbrpm-menu-from-string (order str)
  "build a menu from a string send by phox"
  (setq str (proof-shell-invisible-cmd-get-result str))
  (if (string= str "") nil
    (mapcar
     (lambda (s) (append (list order) (split-string s "\\\\-")
			      (list 'phox-pbrpm-rename-in-cmd)))
     (split-string str "\\\\\\\\"))))

(defun phox-pbrpm-rename-in-cmd (cmd spans)
  (let ((modified nil) (prev 0))
    (mapc (lambda (span)
	    (if (not (string=  (span-property span 'original-text)
			       (span-string span)))
		(setq modified (cons span modified)))) spans)
    (setq modified (reverse modified))
    (if modified
	(progn
	  (if (= 0 (span-property (car modified) 'goalnum))
	      (progn
		(while (and modified (= 0 (span-property (car modified) 'goalnum)))
		  (let ((span (pop modified)))
		    (setq cmd (concat cmd ";; rename "
				      (span-property span 'original-text) " "
				      (span-string span)))))
		(if modified (setq cmd (concat "(" cmd ")")))))
	  (if modified (setq cmd (concat cmd ";; ")))
	  (while modified
	    (let* ((span (pop modified))
		   (goalnum (span-property span 'goalnum)))
	      (while (< (+ prev 1) goalnum)
		(setq cmd (concat cmd "idt @+@ "))
		(setq prev (+ prev 1)))
	      (setq cmd (concat cmd "(rename " (span-property span 'original-text) " "
				      (span-string span)))
	      (setq prev goalnum)
	      (if (or (not modified) (< goalnum (span-property (car modified) 'goalnum)))
		  (setq cmd (concat cmd ") @+@ "))
		(setq cmd (concat cmd ";; ")))))
	  (if (> prev 0) (setq cmd (concat cmd "idt"))))))
  cmd)

(defun phox-pbrpm-get-region-name (region-info)
      (if (= (nth 0 region-info) 1) (nth 1 region-info) (nth 2 region-info)))

(defun  phox-pbrpm-escape-string (str)
  "add escape char '\'"
  (concat "\"" (replace-regexp-in-string "\\\\" "\\\\\\\\" str) "\""))

(defun phox-pbrpm-generate-menu (click-infos region-infos)
"Use informations to build a list of (name , rule)"
   ;click-infos = (goal-number, "whole"/hyp-name/"none", expression, depth-tree-list)
   ;region-infos = idem if in the goal buffer, (0, "none", expression, nil ) if in another buffer, do not display if no region available.

   (let
     ((pbrpm-rules-list nil)
      (goal-prefix
       (if (= (nth 0 click-infos) 1) ""
	 (concat "["
		 (int-to-string (nth 0 click-infos))
		 "] "))))


   ; the first goal is the selected one by default, so we prefer not to display it.

   ; if clicking in a conclusion with no selection
     (if (and (string= (nth 1 click-infos) "none") (not region-infos))
	 (setq pbrpm-rules-list
	       (append pbrpm-rules-list
		       (list
			(list 4 (phox-lang-absurd) (concat goal-prefix "by_absurd;; elim False")))
		       (phox-pbrpm-menu-from-string 0
						    (concat "menu_intro "
							    (int-to-string (nth 0 click-infos))))
		       (phox-pbrpm-menu-from-string 0
						    (concat "menu_evaluate "
							    (int-to-string (nth 0 click-infos))))
		       ); end append
	       );end setq
       );end if

   ; if clicking a conclusion with a selection
   (if (and (string= (nth 1 click-infos) "none") region-infos)
       (setq pbrpm-rules-list
	 (append pbrpm-rules-list
		 (phox-pbrpm-menu-from-string 0
			 (concat "menu_intro "
				 (int-to-string (nth 0 click-infos))
				 (let ((tmp ""))
				   (mapc (lambda (region-info)
					   (setq tmp
						 (concat tmp " " (phox-pbrpm-escape-string (nth 2 region-info)))))
					 region-infos)
				   tmp)))
	 (phox-pbrpm-menu-from-string 1
		       (concat "menu_rewrite "
			       (int-to-string (nth 0 click-infos)) " "
			       (let ((tmp ""))
				 (mapc (lambda (region-info)
					 (setq tmp
					       (concat tmp " " (phox-pbrpm-escape-string (phox-pbrpm-get-region-name region-info)))))
				       region-infos)
				 tmp))))))

    ; if clicking in an hypothesis with no selection
     (if (and
	  (not (or (string= (nth 1 click-infos) "none")
		   (string= (nth 1 click-infos) "whole")))
	  (or (string= "" (nth 2 click-infos)) (not (char= (string-to-char (nth 2 click-infos)) ??)))
	  (not region-infos))
	 (let ((r (proof-shell-invisible-cmd-get-result (concat "is_hypothesis "
								(int-to-string (nth 0 click-infos))
								" "
								(phox-pbrpm-escape-string (nth 1 click-infos))))))
	   (setq pbrpm-rules-list
		 (append pbrpm-rules-list
			 (if (char= (string-to-char r) ?t)
			     (list
			      (list 9 (phox-lang-suppress (nth 1 click-infos))
				    (concat "[" (int-to-string (nth 0 click-infos)) "] "
					    "rmh " (nth 1 click-infos))))
			   nil)
			 (phox-pbrpm-menu-from-string 1
						      (concat "menu_elim "
							      (int-to-string (nth 0 click-infos)) " "
							      (nth 1 click-infos)))
			 (phox-pbrpm-menu-from-string 1
						      (concat "menu_evaluate_hyp "
							      (int-to-string (nth 0 click-infos)) " "
							      (nth 1 click-infos)))
			 (phox-pbrpm-menu-from-string 0
						       (concat "menu_left "
							       (int-to-string (nth 0 click-infos))
							       " "
							       (nth 1 click-infos)))))))

   ; if clicking on an hypothesis with a selection
   (if (and
	(not (or (string= (nth 1 click-infos) "none")
		 (string= (nth 1 click-infos) "whole")))
	region-infos)
       (setq pbrpm-rules-list
	 (append pbrpm-rules-list
		 (phox-pbrpm-menu-from-string 1
		       (concat "menu_apply "
			       (int-to-string (nth 0 click-infos)) " "
			       (nth 1 click-infos)
			       (let ((tmp ""))
				 (mapc (lambda (region-info)
					 (setq tmp
					       (concat tmp " " (phox-pbrpm-escape-string (nth 2 region-info)))))
				       region-infos)
				 tmp)))
		 (phox-pbrpm-menu-from-string 1
		       (concat "menu_rewrite_hyp "
			       (int-to-string (nth 0 click-infos)) " "
			       (nth 1 click-infos)
			       (let ((tmp ""))
				 (mapc (lambda (region-info)
					 (setq tmp
					       (concat tmp " " (phox-pbrpm-escape-string (phox-pbrpm-get-region-name region-info)))))
				       region-infos)
				 tmp))))))

   (if (and (not (string= "" (nth 2 click-infos))) (char= (string-to-char (nth 2 click-infos)) ??)
	    region-infos (not (cdr region-infos)))
       (setq pbrpm-rules-list
	     (append pbrpm-rules-list
		     (list (list 0 (concat
				    (phox-lang-instance (nth 2 click-infos))
				    (nth 2 (car region-infos)))
				 (concat
				  "instance "
				  (nth 2 click-infos)
				  " "
				  (nth 2 (car region-infos))))))))

   (if (and (not (string= "" (nth 2 click-infos))) (char= (string-to-char (nth 2 click-infos)) ??)
	    (not region-infos))
       (setq pbrpm-rules-list
	     (append pbrpm-rules-list
		     (list (list 0 (concat
				    (phox-lang-open-instance (nth 2 click-infos)))
				 (concat
				  "instance "
				  (nth 2 click-infos)
				  " ")
			  (lambda (cmd spans)
			    (let ((span (pop spans)))
			      (concat cmd " " (span-string span)))))))))

   ; is clicking on a token with no selection
   (if (and (not region-infos) (not (string= (nth 2 click-infos) "")))
       (let ((r (proof-shell-invisible-cmd-get-result (concat "is_definition "
							      (int-to-string (nth 0 click-infos))
							      " "
							      (phox-pbrpm-escape-string (nth 2 click-infos)))))
	     (ri (proof-shell-invisible-cmd-get-result (concat "is_definition "
							      (int-to-string (nth 0 click-infos))
							      " "
							      (phox-pbrpm-escape-string (concat "$" (nth 2 click-infos)))))))
	 (if (or (char= (string-to-char r) ?t) (char= (string-to-char ri) ?t))
	     (setq pbrpm-rules-list
		   (append pbrpm-rules-list
			   (list (list 1 (concat
					(phox-lang-opendef)
					(nth 2 click-infos))
				       (concat
					goal-prefix
					(if (or (string= (nth 1 click-infos) "none")
						(string= (nth 1 click-infos) "whole"))
					    "unfold -ortho "
					  (concat "unfold_hyp " (nth 1 click-infos) " -ortho "))
					"$"
					(nth 2 click-infos))))))
	   (if (and (not (string= "" (nth 2 click-infos))) (char= (string-to-char (nth 2 click-infos)) ??))
	       (let  ((r (proof-shell-invisible-cmd-get-result (concat "is_locked "
							      (nth 2 click-infos)))))
		 (if (char= (string-to-char r) ?t)
		     (setq pbrpm-rules-list
			   (append pbrpm-rules-list
				   (list (list 0 (phox-lang-unlock (nth 2 click-infos))
					 (concat
					  goal-prefix
					  "unlock "
					  (nth 2 click-infos))))))
		     (setq pbrpm-rules-list
			   (append pbrpm-rules-list
				   (list (list 0 (phox-lang-lock (nth 2 click-infos))
					 (concat
					  goal-prefix
					  "lock "
					  (nth 2 click-infos))))))))))))

   (let ((arg (if (and region-infos (not (cdr region-infos))) (nth 2 (car region-infos)) " ")))
     (setq pbrpm-rules-list
	   (append pbrpm-rules-list
		   (list
		    (list 10 "Trivial ?" (concat goal-prefix "trivial"))
		    (list 10 (phox-lang-prove arg) (concat goal-prefix "prove")
			  (lambda (cmd spans)
			    (let ((span (pop spans)))
			      (concat cmd " " (span-string span)))))
		    (list 10 (phox-lang-let arg) (concat goal-prefix "local")
			  (lambda (cmd spans)
			    (let ((span1 (pop spans)) (span2 (pop spans)))
			      (concat cmd " " (span-string span1) " = "(span-string span2)))))))))

   pbrpm-rules-list
))


;;--------------------------------------------------------------------------;;
;; phox specific functions
;;--------------------------------------------------------------------------;;

(defalias 'proof-pbrpm-generate-menu 'phox-pbrpm-generate-menu)
(defalias 'proof-pbrpm-left-paren-p 'phox-pbrpm-left-paren-p)
(defalias 'proof-pbrpm-right-paren-p 'phox-pbrpm-right-paren-p)

;;--------------------------------------------------------------------------;;

(require 'phox-lang)
(provide 'phox-pbrpm)
;; phox-pbrpm ends here
