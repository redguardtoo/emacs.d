;; do NOT start elnode-web-server by default, prefer the manual way

;; per project setup may be better
;; (setq httpd-root "/var/www")
(setq httpd-port 4444)
(defun httpd-restart-now ()
  (interactive)
  (httpd-stop)
  (httpd-start))

(provide 'init-httpd)