;; -*- coding: utf-8; lexical-binding: t; -*-

(defvar my-favorite-color-themes
  '(srcery
    atom-dark
    atom-one-dark
    doom-dracula
    doom-gruvbox
    doom-molokai
    doom-monokai-classic
    doom-monokai-machine
    doom-monokai-octagon
    doom-monokai-pro
    doom-monokai-ristretto
    doom-monokai-spectrum
    doom-material-dark
    doom-moonlight
    doom-gruvbox
    doom-xcode
    doom-nova
    doom-nord
    doom-material-dark
    doom-zenburn
    deeper-blue
    tango-dark
    leuven-dark
    solarized-dark-high-contrast
    sanityinc-solarized-dark
    sanityinc-tomorrow-blue
    sanityinc-tomorrow-eighties
    sanityinc-tomorrow-night
    modus-vivendi
    spacemacs-dark)
  "My favorite color themes.")

(defvar my-random-color-themes
  '(adwaita
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
    xp)
  "Random color themes.")

;; someone mentioned that blink cursor could slow Emacs24.4
;; I couldn't care less about cursor, so turn it off explicitly
;; https://github.com/redguardtoo/emacs.d/issues/208
;; but somebody mentioned that blink cursor is needed in dark theme
;; so it should not be turned off by default
;; (blink-cursor-mode -1)

(defun my-pickup-random-color-theme (themes)
  "Pickup random color theme from THEMES."
  (my-ensure 'counsel)
  (let* ((available-themes (mapcar 'symbol-name themes))
         (theme (nth (random (length available-themes)) available-themes)))
    (counsel-load-theme-action theme)
    (message "Color theme [%s] loaded." theme)))

;; random color theme
(defun my-random-favorite-color-theme ()
  "Random color theme."
  (interactive)
  (my-pickup-random-color-theme (or my-favorite-color-themes
                                    (custom-available-themes))))

(defun my-random-healthy-color-theme (&optional join-dark-side)
  "Random healthy color theme.  If JOIN-DARK-SIDE is t, use dark theme only."
  (interactive "P")
  (let* (themes
         (hour (string-to-number (format-time-string "%H" (current-time))))
         (prefer-light-p (and (not join-dark-side) (>= hour 9) (<= hour 19)) ))
    (dolist (theme (custom-available-themes))
      (let* ((light-theme-p (or (and (string-match "light\\|bright\\|white" (symbol-name theme))
                                     (not (string-match "^base16-\\|^airline-\\|^doom=\\|^alect-" (symbol-name theme)))
                                     (not (member theme '(twilight
                                                          avk-darkblue-white
                                                          sanityinc-tomorrow-bright))))
                                (member theme my-random-color-themes))))
        (when (if prefer-light-p light-theme-p (not light-theme-p))
          (push theme themes))))
  (my-pickup-random-color-theme themes)))

(defun my-theme-packages(packages)
  "Get themes from PACKAGES."
  (let* ((sorted-packages (sort packages
                                (lambda (a b)
                                  (> (cdr a) (cdr b)))))
         rlt
         (topNum 110)
         (i 0))
    (dolist (p sorted-packages)
      (let* ((name (symbol-name (car p))))
        (when (and (< i topNum)
                   (string-match "-themes?$" name)
                   (not (member name '("color-theme"
                                       "smart-mode-line-powerline-theme"))))
          (push name rlt)
          (setq i (1+ i)))))
    rlt))

(defun my-insert-popular-theme-name ()
  "Insert names of popular theme."
  (interactive)
  (let* (pkgs
         (old-names (when (region-active-p)
                      (mapcar 'string-trim
                              (split-string (my-selected-str) "\n"))))
         names)
    (with-current-buffer
        (url-retrieve-synchronously "http://melpa.org/download_counts.json" t t 30)
      (goto-char (point-min))
      (search-forward "{")
      (backward-char) ; move cursor just before the "{"
      (setq pkgs (json-read)))
    (when (and pkgs
               (setq names (nconc (my-theme-packages pkgs) old-names)))
      (setq names (delete-dups (sort names 'string<)))
      (my-delete-selected-region)
      ;; insert theme package names
      (insert (mapconcat 'identity names "\n")))))

(defvar my-enable-startup-color-theme-p nil
  "Enable color theme during Emacs startup.")

;; load color theme
(my-run-with-idle-timer 1 (lambda ()
                            (when my-enable-startup-color-theme-p
                              (my-random-favorite-color-theme))))

(provide 'init-theme)
;;; init-theme.el ends here
