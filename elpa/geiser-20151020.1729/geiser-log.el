;; geiser-log.el -- logging utilities

;; Copyright (C) 2009, 2010, 2012 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sat Feb 07, 2009 12:07



;; Some utilities for maintaining a simple log buffer, mainly for
;; debugging purposes.

(require 'geiser-popup)
(require 'geiser-base)

(require 'comint)


;;; Customization:

(defvar geiser-log--buffer-name "*geiser messages*"
  "Name of the Geiser log buffer.")

(defvar geiser-log--max-buffer-size 32000
  "Maximum size of the Geiser messages log.")

(defvar geiser-log--max-message-size 2048
  "Maximum size of individual Geiser log messages.")

(defvar geiser-log-verbose-p nil
  "Log purely informational messages. Useful for debugging.")

(defvar geiser-log--inhibit-p nil
  "Set this to t to inhibit all log messages")


;;; Log buffer and mode:

(define-derived-mode geiser-messages-mode fundamental-mode "Geiser Messages"
  "Simple mode for Geiser log messages buffer."
  (buffer-disable-undo)
  (add-hook 'after-change-functions
            '(lambda (b e len)
               (let ((inhibit-read-only t))
                 (when (> b geiser-log--max-buffer-size)
                   (delete-region (point-min) b))))
            nil t)
  (setq buffer-read-only t))

(geiser-popup--define log geiser-log--buffer-name geiser-messages-mode)


;;; Logging functions:

(defun geiser-log--msg (type &rest args)
  (unless geiser-log--inhibit-p
    (geiser-log--with-buffer
      (goto-char (point-max))
      (insert (geiser--shorten-str (format "\n%s: %s\n" type
                                           (apply 'format args))
                                   geiser-log--max-message-size)))))

(defsubst geiser-log--warn (&rest args)
  (apply 'geiser-log--msg 'WARNING args))

(defsubst geiser-log--error (&rest args)
  (apply 'geiser-log--msg 'ERROR args))

(defsubst geiser-log--info (&rest args)
  (when geiser-log-verbose-p
    (apply 'geiser-log--msg 'INFO args) ""))


;;; User commands:

(defun geiser-show-logs (&optional arg)
  "Show Geiser log messages.
With prefix, activates all logging levels."
  (interactive "P")
  (when arg (setq geiser-log-verbose-p t))
  (geiser-log--pop-to-buffer))

(defun geiser-log-clear ()
  "Clean all logs."
  (interactive)
  (geiser-log--with-buffer (delete-region (point-min) (point-max))))

(defun geiser-log-toggle-verbose ()
  "Toggle verbose logs"
  (interactive)
  (setq geiser-log-verbose-p (not geiser-log-verbose-p))
  (message "Geiser verbose logs %s"
           (if geiser-log-verbose-p "enabled" "disabled")))

(defun geiser-log--deactivate ()
  (interactive)
  (setq geiser-log-verbose-p nil)
  (when (eq (current-buffer) (geiser-log--buffer)) (View-quit)))

(define-key geiser-messages-mode-map "c" 'geiser-log-clear)
(define-key geiser-messages-mode-map "Q" 'geiser-log--deactivate)


(provide 'geiser-log)
