;; -*- coding: utf-8; lexical-binding: t; -*-

;; someone mentioned that blink cursor could slow Emacs24.4
;; I couldn't care less about cursor, so turn it off explicitly
;; https://github.com/redguardtoo/emacs.d/issues/208
;; but somebody mentioned that blink cursor is needed in dark theme
;; so it should not be turned off by default
;; (blink-cursor-mode -1)

(defun pickup-random-color-theme (themes)
  "Pickup random color theme from themes."
  (my-ensure 'counsel)
  (let* ((available-themes (mapcar 'symbol-name themes))
         (theme (nth (random (length available-themes)) available-themes)))
    (counsel-load-theme-action theme)
    (message "Color theme [%s] loaded." theme)))

;; random color theme
(defun random-color-theme ()
  "Random color theme."
  (interactive)
  (pickup-random-color-theme (custom-available-themes)))

(defun random-healthy-color-theme (&optional join-dark-side)
  "Random healthy color theme.  If JOIN-DARK-SIDE is t, use dark theme only."
  (interactive "P")
  (let* (themes
         (hour (string-to-number (format-time-string "%H" (current-time))))
         (prefer-light-p (and (not join-dark-side) (>= hour 9) (<= hour 19)) ))
    (dolist (theme (custom-available-themes))
      (let* ((light-theme-p (or (and (string-match-p "light\\|bright\\|white" (symbol-name theme))
                                     (not (string-match-p "^base16-\\|^airline-\\|^doom=\\|^alect-" (symbol-name theme)))
                                     (not (member theme '(twilight
                                                          avk-darkblue-white
                                                          sanityinc-tomorrow-bright))))
                                (member theme '(adwaita
                                                aliceblue
                                                bharadwaj
                                                black-on-gray
                                                blippblopp
                                                emacs-21
                                                emacs-nw
                                                fischmeister
                                                github
                                                greiner
                                                gtk-ide
                                                high-contrast
                                                jb-simple
                                                kaolin-breeze
                                                katester
                                                leuven
                                                marquardt
                                                mccarthy
                                                montz
                                                occidental
                                                oldlace
                                                scintilla
                                                sitaramv-nt
                                                snowish
                                                soft-stone
                                                standard
                                                tango
                                                tango-plus
                                                tangotango
                                                tao-yang
                                                vim-colors
                                                whateveryouwant
                                                wheat
                                                xemacs
                                                xp)))))
        (when (if prefer-light-p light-theme-p (not light-theme-p))
          (push theme themes))))
  (pickup-random-color-theme themes)))

(provide 'init-theme)
;;; init-theme.el ends here
