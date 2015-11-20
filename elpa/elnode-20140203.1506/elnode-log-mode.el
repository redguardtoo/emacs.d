;;; elnode-log-mode.el - view elnode log files nicely

;;;###autoload
(define-generic-mode 'elnode-log-mode
  nil ; comments
  nil; keywords
  `(("^\\([0-9:-]+\\) .*" 1 '(face '(italic (:foreground "blue"))))
    ("^[0-9:-]+ \\([32][0-9]\\{2\\}\\) .*" 1 '(face '(:foreground "green")))
    ("^[0-9:-]+ \\(4[0-9]\\{2\\}\\) .*" 1 '(face '(:foreground "yellow")))
    ("^[0-9:-]+ \\(5[0-9]\\{2\\}\\) .*" 1 '(face '(:foreground "red")))
    ("^.* \\(GET\\|POST\\|HEAD\\|DELETE\\|TRACE\\)" 1 '(face '(bold (:foreground "purple"))))) ; font-lock list
  nil
  '((lambda ()
      ;;(use-local-map elnode-log-mode-map)
      (setq buffer-read-only 't)
      (set-buffer-modified-p nil)
      ))
  "Elnode log viewing mode.

For viewing access log files from Elnode.")

;;; elnode-log-mode.el ends here
