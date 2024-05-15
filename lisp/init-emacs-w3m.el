;; -*- coding: utf-8; lexical-binding: t; -*-

(setq w3m-coding-system 'utf-8
      w3m-file-coding-system 'utf-8
      w3m-file-name-coding-system 'utf-8
      w3m-input-coding-system 'utf-8
      w3m-output-coding-system 'utf-8
      ;; emacs-w3m will test the ImageMagick support for png32
      ;; and create files named "png32:-" everywhere
      w3m-imagick-convert-program nil
      w3m-terminal-coding-system 'utf-8
      w3m-use-cookies t
      w3m-cookie-accept-bad-cookies t
      w3m-home-page "https://www.duckduckgo.com"
      w3m-command-arguments       '("-F" "-cookie")
      w3m-mailto-url-function     'compose-mail
      browse-url-browser-function 'w3m
      ;; use shr to view html mail which is dependent on libxml
      ;; I prefer w3m. That's emacs 24.3+ default setup.
      ;; If you prefer colored mail body and other advanced features,
      ;; you can either comment out below line and let Emacs decide the
      ;; best html mail rendering engine, or "(setq mm-text-html-renderer 'shr)"
      ;; in "~/.gnus.el"
      ;; mm-text-html-renderer 'w3m ; I prefer w3m
      w3m-use-toolbar t
      ;; show images in the browser
      ;; setq w3m-default-display-inline-images t
      ;; w3m-use-tab     nil
      w3m-confirm-leaving-secure-page nil
      w3m-search-default-engine "g"
      w3m-key-binding 'info)

(defun my-w3m-mode-hook-setup ()
  "Set up w3m."
  (w3m-lnum-mode 1)
  (local-set-key (kbd "w") #'mybigword-big-words-in-current-window)
  (local-set-key (kbd ";") #'w3m-lnum-follow))
(add-hook 'w3m-mode-hook 'my-w3m-mode-hook-setup)

(provide 'init-emacs-w3m)
;;; init-emacs-w3m.el ends here
