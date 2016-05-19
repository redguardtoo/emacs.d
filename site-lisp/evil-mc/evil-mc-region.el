;;; evil-mc-region.el --- Visual region

;;; Commentary:

;; This file contains functions for creating a visual region for a fake cursor

(require 'evil-mc-common)

;;; Code:

(defun evil-mc-put-region-property (region &rest properties)
  "Return a new region that has one or more PROPERTIES
set to the specified values."
  (apply 'evil-mc-put-object-property (cons region properties)))

(defun evil-mc-get-region-property (region name)
  "Return the value of the property with NAME from REGION."
  (when region (evil-mc-get-object-property region name)))

(defun evil-mc-get-region-overlay (region)
  "Return the overlay from REGION."
  (evil-mc-get-region-property region :overlay))

(defun evil-mc-get-region-mark (region)
  "Return the mark from REGION."
  (evil-mc-get-region-property region :mark))

(defun evil-mc-get-region-point (region)
  "Return the point from REGION."
  (evil-mc-get-region-property region :point))

(defun evil-mc-get-region-start (region)
  "Return REGION's overlay start position."
  (let ((overlay (evil-mc-get-region-overlay region)))
    (when overlay (overlay-start overlay))))

(defun evil-mc-get-region-end (region)
  "Return REGION's overlay end position."
  (let ((overlay (evil-mc-get-region-overlay region)))
    (when overlay (overlay-end overlay))))

(defun evil-mc-get-region-type (region)
  "Return the type from REGION."
  (evil-mc-get-region-property region :type))

(defun evil-mc-line-region-p (region)
  "True if REGION is of type line."
  (eq (evil-mc-get-region-type region) 'line))

(defun evil-mc-char-region-p (region)
  "True if REGION is of type char."
  (eq (evil-mc-get-region-type region) 'char))

(defun evil-mc-put-region-overlay (region overlay)
  "Return a new region with the overlay set to OVERLAY."
  (evil-mc-put-region-property region :overlay overlay))

(defun evil-mc-put-region-mark (region mark)
  "Return a new region with the mark set to MARK."
  (evil-mc-put-region-property region :mark mark))

(defun evil-mc-put-region-point (region point)
  "Return a new region with the point set to POINT."
  (evil-mc-put-region-property region :point point))

(defun evil-mc-put-region-type (region type)
  "Return a new region with the type set to TYPE."
  (evil-mc-put-region-property region :type type))

(defun evil-mc-get-pos-at-bol (pos)
  "Get the position at the beginning of the line with POS."
  (save-excursion (goto-char pos) (point-at-bol)))

(defun evil-mc-get-pos-at-eol (pos)
  "Get the position at the end of the line with POS."
  (save-excursion (goto-char pos) (point-at-eol)))

(defun evil-mc-calculate-region-bounds (prev-mark prev-point point)
  "Calculate new region bounds based on PREV-MARK PREV-POINT and current POINT."
  (let ((mark (or prev-mark prev-point)))
    (cond ((and (<= mark prev-point) (< point mark)) (setq mark (1+ mark)))
          ((and (< prev-point mark) (<= mark point)) (setq mark (1- mark))))
    (cond ((< mark point) (cons mark (1+ point)))
          ((< point mark) (cons mark point))
          (t (cons point (1+ (point)))))))

(defun evil-mc-region-overlay (start end)
  "Make a visual region overlay from START to END."
  (let ((overlay (make-overlay start end nil nil nil)))
    (overlay-put overlay 'face 'evil-mc-region-face)
    (overlay-put overlay 'priority evil-mc-region-overlay-priority)
    overlay))

(defun evil-mc-char-region-overlay (mark point)
  "Make an overlay for a visual region of type char from MARK to POINT."
  (let* ((start (if (< mark point) mark point))
         (end (if (< mark point) point mark))
         (overlay (evil-mc-region-overlay start end)))
    (overlay-put overlay 'mark mark)
    (overlay-put overlay 'point point)
    overlay))

(defun evil-mc-line-region-overlay (mark point)
  "Make an overlay for a visual region of type line from MARK to POINT."
  (let* ((start-pos (if (< mark point) mark point))
         (end-pos (if (< mark point) point mark))
         (start-line (line-number-at-pos start-pos))
         (end-line (line-number-at-pos end-pos))
         (start (evil-mc-get-pos-at-bol start-pos))
         (end (1+ (evil-mc-get-pos-at-eol end-pos)))
         (overlay (evil-mc-region-overlay start end)))
    (overlay-put overlay 'mark (if (< mark point) start end))
    (overlay-put overlay 'point (if (< mark point) end start))
    overlay))

(defun evil-mc-create-region-overlay (region)
  "Creates an overlay for REGION."
  (let ((mark (evil-mc-get-region-mark region))
        (point (evil-mc-get-region-point region)))
    (cond ((evil-mc-char-region-p region)
           (evil-mc-char-region-overlay mark point))
          ((evil-mc-line-region-p region)
           (evil-mc-line-region-overlay mark point)))))

(defun evil-mc-update-region-overlay (region)
  "Return a new region based on REGION with the overlay updated."
  (evil-mc-put-region-overlay region (evil-mc-create-region-overlay region)))

(defun evil-mc-create-region (mark point type)
  "Creates a region given MARK, POINT, and TYPE."
  (evil-mc-update-region (evil-mc-put-region-property nil
                                              :mark mark
                                              :point (or point (point))
                                              :type type)))

(defun evil-mc-update-region (region &optional point)
  "Makes a new region from REGION moved to according to POINT."
  (let* ((point (or point (point)))
         (prev-mark (evil-mc-get-region-mark region))
         (prev-point (evil-mc-get-region-point region))
         (type (evil-mc-get-region-type region))
         (bounds (evil-mc-calculate-region-bounds prev-mark prev-point point))
         (new-region (evil-mc-put-region-property nil
                                              :mark (car bounds)
                                              :point (cdr bounds)
                                              :type type)))
    (evil-mc-update-region-overlay new-region)))

(defun evil-mc-change-region-type (region new-type)
  "Returns a new region with the type set to NEW-TYPE."
  (let ((new-region (evil-mc-put-region-type region new-type)))
    (evil-mc-update-region-overlay new-region)))

(defun evil-mc-exchange-region-point-and-mark (region)
  "Return a new region identical to REGION but with point and mark exchanged."
  (let* ((mark (evil-mc-get-region-mark region))
         (point (evil-mc-get-region-point region))
         (new-region (evil-mc-put-region-property region
                                              :mark point
                                              :point mark)))
    (evil-mc-update-region-overlay new-region)))

(defun evil-mc-delete-region-overlay (region)
  "Deletes the overlay associated with REGION."
  (when region
    (let ((overlay (evil-mc-get-region-overlay region)))
      (when overlay (delete-overlay overlay)))))

(provide 'evil-mc-region)

;;; evil-mc-region.el ends here
