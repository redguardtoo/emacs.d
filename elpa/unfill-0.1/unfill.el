;;; unfill.el --- The inverse of fill-paragraph and fill-region

;; Copyright (C) 2012 Steve Purcell.

;; Author: Steve Purcell <steve@sanityinc.com>
;; Version: DEV
;; Package-Version: 0.1
;; Keywords: utilities

;; Based on Xah Lee's examples: http://xahlee.org/emacs/emacs_unfill-paragraph.html

;; This file is NOT part of GNU Emacs.

;;;###autoload
(defun unfill-paragraph ()
  "Replace newline chars in current paragraph by single spaces.
This command does the reverse of `fill-paragraph'."
  (interactive)
  (let ((fill-column most-positive-fixnum))
    (fill-paragraph nil)))

;;;###autoload
(defun unfill-region (start end)
  "Replace newline chars in region by single spaces.
This command does the reverse of `fill-region'."
  (interactive "r")
  (let ((fill-column most-positive-fixnum))
    (fill-region start end)))

(provide 'unfill)
;;; unfill.el ends here
