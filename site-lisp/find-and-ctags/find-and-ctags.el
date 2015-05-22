;;; find-and-ctags.el --- Create and update TAGS by combining Find and Ctags for any language on Winows/Linux/OSX

;; Copyright (C) 2014 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/find-and-ctags
;; Keywords: find ctags
;; Version: 0.0.2

;; This file is not part of GNU Emacs.

;; This file is free software (GPLv3 License)

;; Usage:
;;
;; (def my-setup-develop-environment ()
;;      (interactive)
;;      (let (proj-dir
;;            FIND-OPTS
;;            CTAGS-OPTS)

;;        ;; for COOL MYPROJ
;;        ;; you can use fctags-current-full-filename-match-pattern-p instead
;;        (when (fctags-current-path-match-pattern-p "MYPROJ.*/app")
;;          (setq proj-dir (if fctags-windows-p "c:/Workspaces/MYPROJ/MACWeb/WebContent/app"
;;                      "~/projs/MYPROJ/MACWeb/WebContent/app"))
;;          (setq FIND-OPTS "-not -size +64k")
;;          (setq CTAGS-OPTS "--exclude=*.min.js --exclude=*.git*")
;;          ;; you can use setq-local instead
;;          (setq tags-table-list
;;               (list (fctags-run-ctags-if-needed proj-dir FIND-OPTS CTAGS-OPTS))))
;;        ;; for other projects
;;        ;; insert more WHENs here
;;        ))
;; ;; OPTIONAL
;; (add-hook 'after-save-hook 'fctags-auto-update-tags)
;; (add-hook 'java-mode-hook 'my-setup-develop-environment)
;; (add-hook 'emacs-lisp-mode-hook 'my-setup-develop-environment)
;; (add-hook 'org-mode-hook 'my-setup-develop-environment)
;; (add-hook 'js2-mode-hook 'my-setup-develop-environment)
;; (add-hook 'js-mode-hook 'my-setup-develop-environment)
;; (add-hook 'javascript-mode-hook 'my-setup-develop-environment)
;; (add-hook 'web-mode-hook 'my-setup-develop-environment)
;; (add-hook 'c++-mode-hook 'my-setup-develop-environment)
;; (add-hook 'c-mode-hook 'my-setup-develop-environment)
;;
;; https://github.com/redguardtoo/find-and-ctags/blob/master/README.org for more tips

;;; Code:

(defvar fctags-auto-update-tags-interval 600
  "The interval to update TAGS. It's used by fctags-auto-update-tags and in seconds format.
 Default value is 600 which equals 5 minutes.")

(defvar fctags-gnu-find-executable nil
  "The path of GNU Find. If it's nil, it will be automatically detected.")

(defvar fctags-ctags-executable nil
  "The path of Ctags. If it's nil, it will be automatically detected.")

(defvar fctags-cli-opts-hash (make-hash-table :test 'equal)
  "The options to update TAGS. The path of TAGS is key. Command line options is value.")

;; Is Microsoft Windows?
(setq fctags-windows-p (eq system-type 'windows-nt))

;; Timer to run auto-update TAGS.
(setq fctags-updated-timer nil)

(defun fctags--guess-gnu-find ()
  (let ((rlt "find"))
    (if fctags-windows-p
        (cond
         ((executable-find "c:\\\\cygwin64\\\\bin\\\\find")
          (setq rlt "c:\\\\cygwin64\\\\bin\\\\find"))
         ((executable-find "d:\\\\cygwin64\\\\bin\\\\find")
          (setq rlt "d:\\\\cygwin64\\\\bin\\\\find"))
         ((executable-find "e:\\\\cygwin64\\\\bin\\\\find")
          (setq rlt "e:\\\\cygwin64\\\\bin\\\\find"))
         ((executable-find "c:\\\\cygwin\\\\bin\\\\find")
          (setq rlt "c:\\\\cygwin\\\\bin\\\\find"))
         ((executable-find "d:\\\\cygwin\\\\bin\\\\find")
          (setq rlt "d:\\\\cygwin\\\\bin\\\\find"))
         ((executable-find "e:\\\\cygwin\\\\bin\\\\find")
          (setq rlt "e:\\\\cygwin\\\\bin\\\\find"))))
    rlt))

(defun fctags--guess-ctags ()
  (let ((rlt "ctags"))
    (if (eq system-type 'windows-nt)
        (cond
         ((executable-find "c:\\\\cygwin64\\\\bin\\\\ctags")
          (setq rlt "c:\\\\cygwin64\\\\bin\\\\ctags"))
         ((executable-find "d:\\\\cygwin64\\\\bin\\\\ctags")
          (setq rlt "d:\\\\cygwin64\\\\bin\\\\ctags"))
         ((executable-find "e:\\\\cygwin64\\\\bin\\\\ctags")
          (setq rlt "e:\\\\cygwin64\\\\bin\\\\ctags"))
         ((executable-find "c:\\\\cygwin\\\\bin\\\\ctags")
          (setq rlt "c:\\\\cygwin\\\\bin\\\\ctags"))
         ((executable-find "d:\\\\cygwin\\\\bin\\\\ctags")
          (setq rlt "d:\\\\cygwin\\\\bin\\\\ctags"))
         ((executable-find "e:\\\\cygwin\\\\bin\\\\ctags")
          (setq rlt "e:\\\\cygwin\\\\bin\\\\ctags"))))
    rlt))

;;;###autoload
(defun fctags-get-hostnmae ()
"Reliable way to get current hostname:
 - (getenv \"HOSTNAME\") won't work because $HOSTNAME is not an environment variable
 - (system-name) won't work because /etc/hosts could be modified"
  (with-temp-buffer
    (shell-command "hostname" t)
    (goto-char (point-max))
    (delete-char -1)
    (buffer-string)))

;;;###autoload
(defun fctags-run-ctags-if-needed (SRC-DIR FIND-OPTS CTAGS-OPTS &optional FORCE)
  "Ask ctags to create TAGS and return the full path of TAGS"
  ;; TODO save the CTAGS-OPTS into hash
  (let ((dir (file-name-as-directory (file-truename SRC-DIR)) )
        (find-exe (if fctags-gnu-find-executable fctags-gnu-find-executable (fctags--guess-gnu-find)))
        (ctags-exe (if fctags-ctags-executable fctags-ctags-executable (fctags--guess-ctags)))
        old-dir
        file
        cmd)
    (setq file (concat dir "TAGS"))
    (when (or FORCE (not (file-exists-p file)))
      (setq old-dir default-directory)
      ;; "cd dir && find . -name blah | ctags" will NOT work on windows cmd window
	  (cd dir)
      ;; use relative directory because TAGS is shared between Cygwin and Window
      (setq cmd (format "%s . -type f -not -name 'TAGS' %s | %s -e %s -L -"
                        find-exe
                        FIND-OPTS
                        ctags-exe
                        CTAGS-OPTS))
      (puthash file (list FIND-OPTS CTAGS-OPTS t) fctags-cli-opts-hash)
      (message "find-and-ctags running shell command: %s" cmd)
      (shell-command cmd)
      ;; restore default-directory
      (cd old-dir))
    file))

;;;###autoload
(defun fctags-current-path-match-pattern-p (REGEX)
  "Is current directory match the REGEX?"
  (let ((dir (if (buffer-file-name)
                 (file-name-directory (buffer-file-name))
               "")))
    (string-match-p REGEX dir)))

;;;###autoload
(defun fctags-current-full-filename-match-pattern-p (REGEX)
  "Is current full file name (including directory) match the REGEX?"
  (let ((dir (if (buffer-file-name) (buffer-file-name) "")))
    (string-match-p REGEX dir)))

;;;###autoload
(defun fctags-update-all-tags-force (&optional is-used-as-api)
  (interactive)
  "Check the tags in tags-table-list and re-create it"
  (let (opts)
    (dolist (tag tags-table-list)
      (setq opts (gethash tag fctags-cli-opts-hash))
      (if opts
          (apply 'fctags-run-ctags-if-needed (file-name-directory tag) opts)
        (fctags-run-ctags-if-needed (file-name-directory tag) "" "" t))
      (unless is-used-as-api
        (message "All TAGS have been updated!")))
    ))

;;;###autoload
(defun fctags-auto-update-tags()
  (interactive)
  (cond

   ((not fctags-updated-timer)
    (setq fctags-updated-timer (current-time)))

   ((< (- (float-time (current-time)) (float-time fctags-updated-timer))
       fctags-auto-update-tags-interval)
    ;; do nothing
    )

   (t
    (setq fctags-updated-timer (current-time))
    (fctags-update-all-tags-force t)
    (message "All TAGS have been updated after %d seconds!"
             (- (float-time (current-time)) (float-time fctags-updated-timer))))
   ))

(provide 'find-and-ctags)

;;; find-and-ctags.el ends here
