;;;
;;; === Test area for invisibility ===
;;;
(defvar vis nil)

(overlay-put (make-overlay 18 22) 'invisible 'smaller)
(overlay-put (make-overlay 9 43) 'invisible 'larger)

(defun toggle-invis ()
  (interactive)
  (if vis 
      (add-to-invisibility-spec '(larger . t))
    (remove-from-invisibility-spec '(larger . t)))
  (setq vis (not vis)))


;; In this buffer:

;;    M-x eval-buffer RET
;;    M-x toggle-invis

;; The smaller area remains visible, although there is a surrounding
;; overlay which has an invisibility spec which should cover the
;; revealed characters.  Arguably a bug.






