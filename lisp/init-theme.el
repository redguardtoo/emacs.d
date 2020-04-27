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
                   (string-match-p "-themes?$" name)
                   (not (member '("color-theme"
                                  "smart-mode-line-powerline-theme"))))
          (push name rlt)
          (setq i (1+ i)))))
    rlt))

(defun my-insert-popular-theme-name ()
  "Insert names of popular theme."
  (interactive)
  (let* (pkgs
         (old-names (if (region-active-p) (mapcar 'string-trim
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

;; If you want to use powerline, (require 'powerline) must be
;; before (require 'moe-theme).
;; (add-to-list 'load-path "~/.emacs.d/PATH/TO/powerline/")
;(require 'powerline)

;; set theme
(require 'moe-theme)

;; Show highlighted buffer-id as decoration. (Default: nil)
    (setq moe-theme-highlight-buffer-id t)

    ;; Resize titles (optional).
    (setq moe-theme-resize-markdown-title '(1.5 1.4 1.3 1.2 1.0 1.0))
    (setq moe-theme-resize-org-title '(1.5 1.4 1.3 1.2 1.1 1.0 1.0 1.0 1.0))
    (setq moe-theme-resize-rst-title '(1.5 1.4 1.3 1.2 1.1 1.0))

;; Choose a color for mode-line.(Default: blue)
;; (Available colors: blue, orange, green ,magenta, yellow, purple, red, cyan, w/b.)
    (moe-theme-set-color 'green)

    ;; Finally, apply moe-theme now.
    ;; Choose what you like, (moe-light) or (moe-dark)
    (moe-dark)

(provide 'init-theme)
;;; init-theme.el ends here

