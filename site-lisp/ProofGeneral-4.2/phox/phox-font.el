(defvar phox-sym-lock-enabled nil)  ; da: for clean compile
(defvar phox-sym-lock-color nil)  ; da: for clean compile
(defvar phox-sym-lock-keywords nil)  ; da: for clean compile
(declare-function phox-sym-lock "phox-sym-lock")

;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                       Font lock keywords
;;--------------------------------------------------------------------------;;

(defconst phox-font-lock-keywords
  (list
;commands
   '("(\\*\\([^*]\\|\\*+[^*)]\\)*\\(\\*+)\\|\\**$\\)"
    0 'font-lock-comment-face t)
   '("\"\\([^\\\"]\\|\\\\.\\)*\""
    0 'font-lock-string-face t)
    (cons (concat "\\([ \t]\\|^\\)\\("
       "Cst\\|"
       "Data\\|"
       "I\\(mport\\|nductive\\)\\|"
       "Use\\|"
       "Sort\\|"
       "new_\\(intro\\|e\\(lim\\|quation\\)\\|rewrite\\)\\|"
       "a\\(dd_path\\|uthor\\)\\|"
       "c\\(l\\(aim\\|ose_def\\)\\|or\\(ollary\\)?\\)\\|"
       "d\\(e\\(f\\(\\(_thlist\\|rec\\)\\)?\\|l\\(_proof\\)\\)\\|ocuments\\|epend\\)\\|"
       "e\\(lim_after_intro\\|xport\\|del\\|show\\)\\|"
       "f\\(act\\|lag\\)\\|"
       "goal\\|"
       "in\\(clude\\|stitute\\)\\|"
       "lem\\(ma\\)?\\|"
       "p\\(ath\\|r\\(int\\(_sort\\)?\\|iority\\|op\\(osition\\)?\\|ove_claim\\)\\)\\|"
       "quit\\|"
       "s\\(ave\\|earch\\)\\|"
       "t\\(ex\\(_syntax\\)?\\|heo\\(rem\\)?\\|itle\\|ype\\)"
       "\\)[ \t\n\r.]")
      '(0 'font-lock-keyword-face t))
;proof command
    (cons (concat "\\([ \t]\\|^\\)\\("
       "a\\(bort\\|fter\\|nd\\|pply\\|ssume\\|xiom\\)\\|"
       "by\\(_absurd\\)?\\|"
       "constraints\\|"
       "elim\\|"
       "deduce\\|"
       "evaluate\\(_hyp\\)?\\|"
       "from\\|"
       "goals\\|"
       "in\\(tros?\\|stance\\)\\|"
       "l\\(oc\\(al\\|k\\)\\|e\\(t\\|fts?\\)\\)\\|"
       "next\\|"
       "of\\|"
       "prove\\|"
       "r\\(e\\(write\\(_hyp\\)?\\|name\\)\\|mh\\)\\|"
       "s\\(elect\\|how\\|lh\\)\\|"
       "t\\(hen\\|rivial\\)\\|"
       "u\\(se\\|n\\(do\\|fold\\(_hyp\\)?\\|lock\\)\\)\\|"
       "with"
       "\\)[ \t.]")
      '(0 'font-lock-type-face t))))
;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                       phox-sym-lock tables
;;--------------------------------------------------------------------------;;

(if (featurep 'xemacs) (require 'phox-sym-lock))

;; to change this table, xfd -fn '-adobe-symbol-*--12-*' may be
;; used to determine the symbol character codes.
(defconst phox-sym-lock-keywords-table
  '((">=" 0 1 179)
    ("<=" 0 1 163)
    ("!=" 0 1 185)
    (":<" 0 1 206)
    ("[^:]\\(:\\)[^:= \n\t\r]" 1 7 206)
    ("\\\\/" 0 1 36)
    ("/\\\\" 0 1 34)
    ("\\<or\\>" 0 3 218)
    ("\\<in\\>" 0 3 206)
    ("\\<notin\\>" 0 4 207)
    ("\\<inter\\>" 0 3 199)
    ("\\<union\\>" 0 3 200)
    ("\\<minus\\>" 0 3 45)
    ("&" 0 1 217)
    ("<->" 0 1 171)
    ("=>" 0 1 222)
    ("\\<subset\\>" 0 4 204)
    ("->" 0 1 174)
    ("~" 0 1 216)
    ("\\\\" 0 1 108)))
;  "If non nil: Overrides default Phox-Sym-Lock patterns for PhoX.")

(defun phox-sym-lock-start ()
	(if (and (featurep 'phox-sym-lock) phox-sym-lock-enabled)
	    (progn
	      (setq phox-sym-lock-color
		    (face-foreground 'font-lock-function-name-face))
	      (if (not phox-sym-lock-keywords)
		  (phox-sym-lock phox-sym-lock-keywords-table)))))


(provide 'phox-font)
