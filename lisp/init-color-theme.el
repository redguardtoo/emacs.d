(require 'color-theme)
(require 'color-theme-molokai)

;; {{ work around color theme bug
;; @see https://plus.google.com/106672400078851000780/posts/KhTgscKE8PM
(defadvice load-theme (before disable-themes-first activate)
  ;; diable all themes
  (dolist (i custom-enabled-themes)
    (disable-theme i)))
;; }}

(color-theme-molokai)
;; This line must be after color-theme-molokai! Don't know why.
(setq color-theme-illegal-faces "^\\(w3-\\|dropdown-\\|info-\\|linum\\|yas-\\|font-lock\\)")
;; (color-theme-select 'color-theme-xp)
;; (color-theme-xp)

(provide 'init-color-theme)
