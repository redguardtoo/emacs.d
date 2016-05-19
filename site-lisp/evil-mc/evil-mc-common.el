;;; evil-mc-common.el --- Common functions

;;; Commentary:

;; This file contains common functionality

;;; Code:

(defun evil-mc-get-object-property (obj prop)
  "Get the value of PROP from OBJ."
  (let ((item (assq prop obj)))
    (when item (cdr item))))

(defun evil-mc-put-object-property (obj prop val &rest properties)
  "Return a new OBJ that has PROP set to VAL and any other PROPERTIES specified."
  (let ((obj (assq-delete-all prop obj)))
    (setq obj (cons (cons prop val) obj))
    (while properties
      (setq obj (evil-mc-put-object-property obj
                                             (pop properties)
                                             (pop properties))))
    obj))

(defun evil-mc-put-object-properties (obj &rest properties)
  "Return a new OBJ that has all the PROPERTIES specified."
  (when properties
    (apply #'evil-mc-put-object-property
           (cons obj properties))))


(defun evil-mc-column-number (pos)
  "Return the column number at POS."
  (save-excursion
    (goto-char pos)
    (current-column)))

(defun evil-mc-message (format-string &rest args)
  "Display a message given a FORMAT-STRING and ARGS."
  (apply 'message (concat (propertize "evil-mc "
                                      'face
                                      'font-lock-constant-face)
                          format-string) args))

(defun evil-mc-ends-with-newline-p (text)
  "True if TEXT ends with a newline character."
  (string-match-p "\n$" text))

(defun evil-mc-goto-char (pos)
  "Goto to POS ensuring that point does not go beyond the end of line."
  (let ((point (max (min pos (point-max)) (point-min))))
    (goto-char point)
    (when (eolp) (goto-char (max (point-at-bol)
                                 (1- (point-at-eol)))))))

(provide 'evil-mc-common)

;;; evil-mc-common.el ends here
