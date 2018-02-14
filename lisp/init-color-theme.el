;; {{ work around color theme bug
;; @see https://plus.google.com/106672400078851000780/posts/KhTgscKE8PM
(defadvice load-theme (before disable-themes-first activate)
  ;; disable all themes
  (dolist (i custom-enabled-themes)
    (disable-theme i)))
;; }}

(load-theme 'monokai t)

;; This line must be after color theme setup! Don't know why.
(setq color-theme-illegal-faces "^\\(w3-\\|dropdown-\\|info-\\|linum\\|yas-\\|font-lock\\|dired-directory\\)")

(provide 'init-color-theme)
