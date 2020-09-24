;;; lazyflymake-sdk.el --- sdk for lazyflymake  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'flymake)

(defcustom lazyflymake-debug nil
  "Output debug information when it's t."
  :type 'boolean
  :group 'lazyflymake)

(defun lazyflymake-sdk-file-exist-p ()
  "The code file does exist."
  (and buffer-file-name
       (file-exists-p buffer-file-name)))

(defun lazyflymake-sdk-code-file ()
  "Get code file to check."
  (let* ((rlt (cond
               ((and (lazyflymake-sdk-file-exist-p)
                     (not (buffer-narrowed-p)))
                ;; save a little resource to create temp file
                buffer-file-name)
               (t
                (flymake-init-create-temp-buffer-copy
                 'flymake-create-temp-inplace)))))
    ;; convert absolute path on Windows to relative path
    (setq rlt (file-relative-name rlt))
    (if lazyflymake-debug (message "lazyflymake-sdk-code-file => %s" rlt))
    rlt))

(defun lazyflymake-sdk-hint ()
  "Hint the user."
  (message "This command works when `lazyflymake-flymake-mode-on' is nil"))

(defun lazyflymake-sdk-valid-overlays (overlays)
  "Clean up and return valid OVERLAYS."
  ;; remove overlay without binding buffer
  (sort (cl-remove-if (lambda (ov) (not (overlay-start ov))) overlays)
        (lambda (a b) (< (overlay-start a) (overlay-start b)))))

(provide 'lazyflymake-sdk)
;;; lazyflymake-sdk.el ends here
