;; -*- coding: utf-8; lexical-binding: t; -*-

(defvar my-favorite-color-themes nil "My favorite color themes.")

;; someone mentioned that blink cursor could slow Emacs24.4
;; I couldn't care less about cursor, so turn it off explicitly
;; https://github.com/redguardtoo/emacs.d/issues/208
;; but somebody mentioned that blink cursor is needed in dark theme
;; so it should not be turned off by default
;; (blink-cursor-mode -1)

(defun my-pickup-random-color-theme (themes)
  "Pickup random color theme from THEMES."
  (let* ((available-themes themes)
         (theme (nth (random (length available-themes)) available-themes)))
    (mapc #'disable-theme custom-enabled-themes)
    (load-theme theme t)
    (message "Color theme [%s] loaded." theme)))

;; random color theme
(defun my-random-favorite-color-theme (&optional any-theme)
  "Random color theme.  If ANY-THEME is t, pick one from `(custom-available-themes)'."
  (interactive "P")
  (my-pickup-random-color-theme (if any-theme (custom-available-themes)
                                  (or my-favorite-color-themes (custom-available-themes))) ))

(defun my-current-theme ()
  "Show current theme."
  (interactive)
  (message "%S" custom-enabled-themes))

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
