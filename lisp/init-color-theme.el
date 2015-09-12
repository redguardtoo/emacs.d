;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (require 'color-theme)								        ;;
;; (require 'color-theme-molokai)							        ;;
;; 											        ;;
;; ;; {{ work around color theme bug							        ;;
;; ;; @see https://plus.google.com/106672400078851000780/posts/KhTgscKE8PM		        ;;
;; (defadvice load-theme (before disable-themes-first activate)				        ;;
;;   ;; diable all themes								        ;;
;;   (dolist (i custom-enabled-themes)							        ;;
;;     (disable-theme i)))								        ;;
;; ;; }}										        ;;
;; 											        ;;
;; (color-theme-molokai)								        ;;
;; ;; This line must be after color-theme-molokai! Don't know why.			        ;;
;; (setq color-theme-illegal-faces "^\\(w3-\\|dropdown-\\|info-\\|linum\\|yas-\\|font-lock\\)") ;;
;; ;; (color-theme-select 'color-theme-xp)						        ;;
;; ;; (color-theme-xp)									        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; lzh: I like color-theme-sanityinc-solarized
(require 'color-theme-sanityinc-solarized)
(setq-default custom-enabled-themes '(sanityinc-solarized-dark))
(load-theme 'sanityinc-solarized-dark t)

(defun light ()
  "Activate a light color theme."
  (interactive)
  (color-theme-sanityinc-solarized-light))

(defun dark ()
  "Activate a dark color theme."
  (interactive)
  (color-theme-sanityinc-solarized-dark))


(provide 'init-color-theme)
