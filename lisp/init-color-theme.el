(require 'color-theme)

;; {{ work around color theme bug
;; @see https://plus.google.com/106672400078851000780/posts/KhTgscKE8PM
(defadvice load-theme (before disable-themes-first activate)
  ;; disable all themes
  (dolist (i custom-enabled-themes)
    (disable-theme i)))
;; }}


(defvar my-current-color-theme nil
  "My current color theme.")

(defun my-toggle-color-theme ()
  "Toggle between the major color theme and fallback theme.
Fallback theme is used only if the console does NOT support 256 colors."
  (interactive)
  (cond
   ((string= my-current-color-theme "favorite")
    ;; fallback color theme from color-theme library
    (unless color-theme-initialized (color-theme-initialize))
    ;; {{ fallback built in color theme
    (color-theme-deep-blue)
    ;; }}
    (setq my-current-color-theme "fallback"))
   (t
    ;; {{ enable my favourite color theme
    (unless (featurep 'color-theme-molokai)
      (require 'color-theme-molokai))
    (color-theme-molokai)
    ;; }}
    (setq my-current-color-theme "favorite"))))
;; turn on the color theme now!
(my-toggle-color-theme)

;; This line must be after color theme setup! Don't know why.
(setq color-theme-illegal-faces "^\\(w3-\\|dropdown-\\|info-\\|linum\\|yas-\\|font-lock\\|dired-directory\\)")

(provide 'init-color-theme)
