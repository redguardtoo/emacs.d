;; do NOT start elnode-web-server by default, prefer the manual way

;; per project setup may be better
;; (setq httpd-root "/var/www")
(setq httpd-port 4444)
(defun httpd-restart-now ()
  (interactive)
  (httpd-stop)
  (httpd-start)
  (message "http://localhost:%d/ at %s restarted"
           httpd-port httpd-root))

(defun httpd-restart-at-default-directory ()
  (interactive)
  (setq httpd-root default-directory)
  (httpd-restart-now))

(provide 'init-httpd)
