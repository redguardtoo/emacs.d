;; coq-mmm.el	  Configure MMM mode for CoqDoc elements
;;
;; Copyright     (C) 2007 David Aspinall
;; Authors:       David Aspinall <David.Aspinall@ed.ac.uk>
;; Licence:	 GPL
;;
;; coq-mmm.el,v 11.0 2010/10/10 22:56:58 da Exp
;;
;; We only spot some simple cases of embedded LaTeX/HTML/verbatim.
;;
;; At the moment, the insertion has a bad interaction with the holes
;; code which also uses skeletons: the interesting positions used
;; for MMM markup are made into holes!

(require 'mmm-auto)

(mmm-add-group
 'coq
 `((coq-text
   :submode text-mode
   :face mmm-comment-submode-face
   :front "(\\*\\*[ \t]"
   :back  "[ ]?\\*)"
   :insert ((?d coqdoc-text nil @ "(** " @ " " _ " " @ " *)" @)))

   (coq-latex
   :submode LaTeX-mode
   :face mmm-comment-submode-face
   :front "(\\*\\*[^%\\$]*[%\\$]"
   :back  "[%\\$][ \t]*\\*)"
   :insert ((?l coqdoc-latex nil @ "(** %" @ " " _ " " @ "% *)" @)))

   (coq-html
   :submode html-mode
   :face mmm-comment-submode-face
   :front "(\\*\\*[^#]*#"
   :back  "#[ \t]*\\*)"
   :insert ((?w coqdoc-html nil @ "(** #" @ " " _ " " @ "# *)" @)))

   (coq-verbatim
   :submode text-mode
   :face mmm-code-submode-face
   :front "^[ \t]*<<"
   :back  ">>"
   :insert ((?v coqdoc-verbatim nil @ "<<\n" @ " " _ " " @ "\n>>" @)))
   ))


(provide 'coq-mmm)

;;; coq-mmm.el ends here
