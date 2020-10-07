;;; lazyflymake-sdk.el --- sdk for lazyflymake  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'flymake)

(defcustom lazyflymake-debug nil
  "Output debug information when it's t."
  :type 'boolean
  :group 'lazyflymake)

(defvar lazyflymake-temp-source-file-name nil
  "Internal variable to store the path of temporary source file.")

(defun lazyflymake-sdk-file-exist-p ()
  "The code file does exist."
  (and buffer-file-name
       (file-exists-p buffer-file-name)))

(defun lazyflymake-sdk-code-file ()
  "Get code file to check."
  (let* ((local-file-p (and (lazyflymake-sdk-file-exist-p)
                            (not (buffer-narrowed-p))))
         (rlt (cond
               (local-file-p
                ;; save a little resource to create temp file
                buffer-file-name)
               (t
                (flymake-init-create-temp-buffer-copy
                 'flymake-create-temp-inplace)))))

    ;; Per chance clean up a function need delete the temporary file
    (unless local-file-p
      (setq lazyflymake-temp-source-file-name (file-truename rlt)))

    ;; use relative path in case running in Windows
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
