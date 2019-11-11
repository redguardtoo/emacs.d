(when (and (boundp 'startup-now) startup-now)
  (unless (featurep 'ediff) (require 'ediff))
  (defun ediff-startup-hook-setup ()
    ;; hide contron panel if it's current buffer
    (when (string-match-p (buffer-name) "\*Ediff Control Panel.*\*")
      (bury-buffer)))
  (add-hook 'ediff-startup-hook
            'ediff-startup-hook-setup))

(provide 'init-ediff)
