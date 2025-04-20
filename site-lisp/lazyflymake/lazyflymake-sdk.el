;;; lazyflymake-sdk.el --- sdk for lazyflymake  -*- lexical-binding: t -*-

;;; Commentary:
;;

;;; Code:

(require 'cl-lib)
(require 'flymake)
(require 'flymake-proc)

(defcustom lazyflymake-debug nil
  "Output debug information when it's t."
  :type 'boolean
  :group 'lazyflymake)

(defcustom lazyflymake-program-extra-args nil
  "Extra arguments passed to linter program.
It could be converted to buffer local variable."
  :group 'lazyflymake
  :type '(repeat sexp))

(defvar lazyflymake-temp-source-file-name nil
  "Internal variable to store the path of temporary source file.")

(defun lazyflymake-sdk-file-exist-p ()
  "The code file does exist."
  (and buffer-file-name
       (file-exists-p buffer-file-name)))

(defun lazyflymake-sdk-find-dominating-file (names)
  "Find dominating file with one of NAMES."
  (let (dir file rlt)
    (while (and (not rlt) names)
      (setq dir (locate-dominating-file default-directory
                                        (setq file (car names))))
      (when dir
        (setq rlt (concat dir (car names))))
      (setq names (cdr names)))
    rlt))

(defun lazyflymake-sdk-code-file ()
  "Get code file to check."
  (let* ((local-file-p (lazyflymake-sdk-file-exist-p))
         (rlt (cond
               ;; do not syntax check when buffer is narrowed
               ((buffer-narrowed-p)
                nil)

               ;; use current local file
               (local-file-p
                ;; save a little resource to create temp file
                buffer-file-name)

               ;; create temporary source file
               (t
                (flymake-proc-init-create-temp-buffer-copy
                 'flymake-proc-create-temp-inplace)))))

    (when rlt
      ;; clean up a function need delete the temporary file
      (unless local-file-p
        (setq lazyflymake-temp-source-file-name (file-truename rlt)))

      ;; use relative path in case running in Windows
      (setq rlt (file-relative-name rlt))
      (if lazyflymake-debug (message "lazyflymake-sdk-code-file => %s" rlt)))
    rlt))

(defun lazyflymake-sdk-hint ()
  "Hint the user."
  (message "This command works when `lazyflymake-flymake-mode-on' is nil"))

(defun lazyflymake-sdk-valid-overlays (overlays)
  "Clean up and return valid OVERLAYS."
  ;; remove overlay without binding buffer
  (sort (cl-remove-if (lambda (ov) (not (overlay-start ov))) overlays)
        (lambda (a b) (< (overlay-start a) (overlay-start b)))))

(defun lazyflymake-sdk-generate-flymake-init (program args file)
  "Generate flymake init from PROGRAM, ARGS, FILE."
  (let* ((rlt (list program (append args
                        lazyflymake-program-extra-args
                        (list file)))))
    (when lazyflymake-debug
      (message "lazyflymake-sdk-generate-flymake-init called. rlt=%s" rlt))
    rlt))

(provide 'lazyflymake-sdk)
;;; lazyflymake-sdk.el ends here
