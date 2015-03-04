;;; find-and-ctags.el --- use `find' and `ctags' for code navigation

;; Copyright (C) 2014 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/find-and-ctags
;; Keywords: find ctags
;; Version: 0.0.1

;; This file is not part of GNU Emacs.

;; This file is free software (GPLv3 License)

;; Set up:
;;
;; https://github.com/redguardtoo/find-and-ctags/blob/master/README.org for use cases

;;; Code:

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
        (find-exe (if fctags-gnu-find-exe fctags-gnu-find-exe (fctags--guess-gnu-find)))
        (ctags-exe (if fctags-ctags-exe fctags-find-exe (fctags--guess-ctags)))
        old-dir
        file
        cmd)
    (setq file (concat dir "TAGS"))
    (when (or FORCE (not (file-exists-p file)))
      (setq old-dir default-directory)
      ;; "cd dir && find . -name blah | ctags" will NOT work on windows cmd window
      (setq default-directory dir)
      ;; use relative directory because TAGS is shared between Cygwin and Window
      (setq cmd (format "%s . -type f -not -name 'TAGS' %s | %s -e %s -L - &"
                        find-exe
                        FIND-OPTS
                        ctags-exe
                        CTAGS-OPTS))
      (puthash file (list FIND-OPTS CTAGS-OPTS t) fctags-cli-opts-hash)
      (shell-command cmd)
      ;; restore default directory
      (setq default-directory old-dir))
    file))

;;;###autoload
(defun fctags-current-path-match-pattern-p (REGEX)
  "Is current directory match the REGEX?"
  (let ((dir (if (buffer-file-name)
                 (file-name-directory (buffer-file-name))
               "")))
    (string-match-p REGEX dir)))


;;;###autoload
(defun fctags-update-all-tags-force ()
  (interactive)
  "Check the tags in tags-table-list and re-create it"
  (let (opts)
    (dolist (tag tags-table-list)
      (setq opts (get tag fctags-cli-opts-hash))
      (if opts
          (apply 'fctags-run-ctags-if-needed (file-name-directory tag) opts)
        (fctags-run-ctags-if-needed (file-name-directory tag) "" "" t)))
    ))

;;;###autoload
(defun fctags-auto-update-tags()
  (interactive)
  (cond
   ((not fctags-updated-timer)
    (setq fctags-updated-timer (current-time)))
   ((< (- (float-time (current-time)) (float-time fctags-updated-timer)) 1800)
    ;; < 300 seconds
    ;; do nothing
    )
   (t
    (setq fctags-updated-timer (current-time))
    (fctags-update-all-tags-force)
    (message "Updated TAGS after %d seconds." (- (float-time (current-time))  (float-time fctags-updated-timer))))
   ))

(provide 'find-and-ctags)

;;; find-and-ctags.el ends here
