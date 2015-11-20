;;; scratch.el --- Mode-specific scratch buffers

;; Author: Ian Eure <ian.eure@gmail.com>
;; Version: 1.1
;; Keywords: editing

;; Copyright (c) 2009-1020, 2010, 2012 Ian Eure <ian.eure@gmail.com>
;; All rights reserved.

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:

;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above
;;    copyright notice, this list of conditions and the following
;;    disclaimer in the documentation and/or other materials provided
;;    with the distribution.

;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''
;; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
;; TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
;; PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR OR
;; CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
;; USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
;; ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
;; OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
;; OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
;; SUCH DAMAGE.

;;; Commentary:
;;
;;   (autoload 'scratch "scratch" nil t)
;;

;;; History:

;; 1999 Ian Eure
;;   Initial version.

;; 2010-08-16 Ian Eure
;;   Broke out into its own file.

;; 2012-08-30 Ian Eure
;;   Dump current region into new scratch buffer

;;; Code:

(defgroup scratch nil
  "Scratch buffers."
  :prefix "scratch-"
  :group 'editing)

(defcustom scratch-mode-alist
  '((erc-mode . fundamental-mode)
    (sql-interactive-mode . sql-mode)
    (shell-mode . sh-mode))
  "Alist of mappings from major modes to major modes for SCRATCH.

Some interactive modes don't lend themselves well to scratch
buffers; this alist is used to change the mode used by SCRATCH
for those buffers."

  :type '(alist :key-type symbol :value-type symbol))

(defvar scratch-history nil
  "History of scratch buffers")

(defvar scratch-major-mode-list nil
  "List of major modes SCRATCH may use. See `scratch-list-modes'.")

(defvar scratch-buffer nil
  "Non-nil if the current buffer is a scratch buffer.")
(make-variable-buffer-local 'scratch-buffer)

(defun scratch-list-modes ()
  "List known major modes."
  (or scratch-major-mode-list
      (let ((modes))
        (mapatoms
         (lambda (sym)
           (let ((name (symbol-name sym)))
             (when (and (functionp sym)
                        (not (member sym minor-mode-list))
                        (string-match "-mode$" name))
               (push (substring name 0 -5) modes)))))
        modes)))

;;;###autoload
(defun scratch (&optional arg)
  "Get a scratch buffer for the current mode."
  (interactive "p")
  (let* ((tmp) (name)
         (mode (cond (current-prefix-arg
                      (intern (concat (setq name (completing-read
                                                  "Mode: " (scratch-list-modes)
                                                  nil t nil scratch-history))
                                      "-mode")))
                     ((setq tmp (assoc major-mode scratch-mode-alist))
                      (cdr tmp))
                     (t major-mode)))
         (name
          (format "*%s*"
                  (or name (replace-regexp-in-string "-mode$" ""
                                                     (symbol-name mode)))))
         (buf (get-buffer name)))
    (cond ((bufferp buf)
           (pop-to-buffer buf))
          (t
           (let ((contents (when (region-active-p)
                             (buffer-substring (region-beginning)
                                               (region-end)))))
             (setq buf (get-buffer-create name))
             (pop-to-buffer buf)
             (let ((scratch-buffer t))
               (funcall mode))
             (when contents (save-excursion (insert contents)))
             (setq scratch-buffer t))))))

(provide 'scratch)
;;; scratch.el ends here
