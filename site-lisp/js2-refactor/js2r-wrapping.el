(require 'yasnippet)

(defvar js2r--space-str " \t\n")

(defun js2r--skip-region-whitespace ()
  (let ((p-first (< (point) (mark))))
    (unless p-first
      (exchange-point-and-mark))
    (skip-chars-forward js2r--space-str)
    (exchange-point-and-mark)
    (skip-chars-backward js2r--space-str)
    (when p-first
      (exchange-point-and-mark))))

(defun js2r-unwrap ()
  (interactive)
  (js2r--guard)
  (let (beg end)
    (if (use-region-p)
        (progn
          (js2r--skip-region-whitespace)
          (setq beg (min (point) (mark)))
          (setq end (max (point) (mark))))
      (let ((stmt (js2-node-parent-stmt (js2-node-at-point))))
        (setq beg (js2-node-abs-pos stmt))
        (setq end (js2-node-abs-end stmt))))
    (let* ((ancestor (js2-node-parent-stmt
                      (js2r--first-common-ancestor-in-region beg end)))
           (abeg (js2-node-abs-pos ancestor))
           (aend (js2-node-abs-end ancestor)))
      (save-excursion
        (goto-char end)
        (delete-char (- aend end))
        (goto-char abeg)
        (delete-char (- beg abeg)))
      (indent-region (point-min) (point-max)))))

(defun js2r-wrap-in-for-loop (beg end)
  (interactive "r")
  (js2r--skip-region-whitespace)
  (setq beg (min (point) (mark)))
  (setq end (max (point) (mark)))
  (let ((yas/wrap-around-region t))
    (yas/expand-snippet "for (var i = 0, l = ${1:length}; i < l; i++) {\n$0\n}"
                        beg end)))

(provide 'js2r-wrapping)
