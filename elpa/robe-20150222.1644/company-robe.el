(eval-when-compile (require 'robe))

;;;###autoload
(defun company-robe (command &optional arg)
  "A `company-mode' completion back-end for `robe-mode'."
  (interactive (list 'interactive))
  (case command
    (interactive (company-begin-backend 'company-robe))
    (prefix (and (boundp 'robe-mode)
                 robe-mode robe-running
                 (company-robe--prefix)))
    (candidates (robe-complete-thing arg))
    (duplicates t)
    (meta (let ((spec (car (robe-cached-specs arg))))
            (when spec (robe-signature spec))))
    (location (let ((spec (company-robe--choose-spec arg)))
                (cons (robe-spec-file spec)
                      (robe-spec-line spec))))
    (annotation (robe-complete-annotation arg))
    (doc-buffer (let ((spec (company-robe--choose-spec arg)))
                  (when spec
                    (save-window-excursion
                      (robe-show-doc spec)
                      (message nil)
                      (get-buffer "*robe-doc*")))))))

(defun company-robe--prefix ()
  (let ((prefix (company-grab-symbol)))
    (when (robe-complete-symbol-p (- (point) (length prefix)))
      prefix)))

(defun company-robe--choose-spec (thing)
  (let ((specs (robe-cached-specs thing)))
    (when specs
      (if (cdr specs)
          (let ((alist (loop for spec in specs
                             for module = (robe-spec-module spec)
                             when module
                             collect (cons module spec))))
            (cdr (assoc (ido-completing-read "Module: " alist nil t) alist)))
        (car specs)))))

(provide 'company-robe)
