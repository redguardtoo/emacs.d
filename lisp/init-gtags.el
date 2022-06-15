;; -*- coding: utf-8; lexical-binding: t; -*-

(defun my-gtags-produce-tags-if-needed (directory)
  "Product gtags tags file (index file) from DIRECTORY."
  (if (not (= 0 (call-process "global" nil nil nil " -p")))
      (let ((default-directory directory))
        (shell-command "gtags")
        (message "Tag file was created by GNU Global."))
    ;;  Tag file already exists; update it
    (shell-command "global -u")
    (message "Tag file was updated by GNU Global.")))

;; @see http://emacs-fu.blogspot.com.au/2008/01/navigating-through-source-code-using.html
(defun my-gtags-create-or-update ()
  "Create or update the gnu global tag file."
  (interactive)
  (my-gtags-produce-tags-if-needed (read-directory-name
                            "gtags: top of source tree:" default-directory)))

(defun my-gtags-add-gtagslibpath (libdir)
  "Add external library directory LIBDIR to gtags' environment variable.
Gtags scans that directory if needed."
  (interactive "DDirectory containing GTAGS:\nP")
  (let (sl
        (gtags-lib-path (getenv "GTAGSLIBPATH")))
    (unless (file-exists-p (concat (file-name-as-directory libdir) "GTAGS"))
      ;; create tags
      (let ((default-directory libdir))
        (shell-command "gtags")
        (message "tag file is created by GNU Global")))

    (setq libdir (directory-file-name libdir)) ;remove final slash
    (setq sl (split-string (or gtags-lib-path "")  ":" t))
    (setq sl (delete libdir sl))
    (push libdir sl)
    (setenv "GTAGSLIBPATH" (mapconcat 'identity sl ":"))))

(defun my-gtags-print-gtagslibpath ()
  "Print the gtags default library path (for debug purpose)."
  (interactive)
  (message "GTAGSLIBPATH=%s" (getenv "GTAGSLIBPATH")))

(provide 'init-gtags)
;;; init-gtags.el ends here
