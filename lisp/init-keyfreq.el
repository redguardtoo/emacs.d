(require 'keyfreq)
(keyfreq-mode 1)
(keyfreq-autosave-mode 1)
(unless (file-exists-p keyfreq-file)
  (write-region "" nil keyfreq-file))
;; And use keyfreq-show to see how many times you used a command.
(provide 'init-keyfreq)
