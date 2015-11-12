;;; find-and-ctags.el --- Use ctags&find to create TAGS on Winows/Linux/OSX

;; Copyright (C) 2014 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/find-and-ctags
;; Keywords: find ctags
;; Version: 0.0.5

;; This file is not part of GNU Emacs.

;; This file is free software (GPLv3 License)

;;; Commentary:

;; Insert below setup into ~/.emacs.d/init.el:
;; (defun my-setup-develop-environment ()
;;   (interactive)
;;   (let (proj-dir
;;         find-opts
;;         ctags-opts)

;;     ;; for COOL MYPROJ
;;     ;; you can use find-and-ctags-current-full-filename-match-pattern-p instead
;;     (when (find-and-ctags-current-path-match-pattern-p "MYPROJ.*/app")
;;       (setq proj-dir (if find-and-ctags-windows-p "c:/Workspaces/MYPROJ/MACWeb/WebContent/app"
;;                        "~/projs/MYPROJ/MACWeb/WebContent/app"))
;;       ;; ignore file bigger than 64K, ignore files in "dist/"
;;       (setq find-opts "-not -size +64k -not -iwholename '*/dist/*'")
;;       (setq ctags-opts "--exclude='*.min.js' --exclude='*.git*'")
;;       ;; you can use setq-local instead
;;       (setq tags-table-list
;;             (list (find-and-ctags-run-ctags-if-needed proj-dir '((find-opts ctags-opts)
;;                                                                  ("dist/test.js" "-a"))))))
;;     ;; for other projects
;;     ;; insert more `when' statements here
;;     ))
;;
;;   ;; OPTIONAL
;;   (add-hook 'after-save-hook 'find-and-ctags-auto-update-tags)
;;   (add-hook 'prog-mode-hook 'my-setup-develop-environment)
;;   (add-hook 'org-mode-hook 'my-setup-develop-environment)
;;
;; In above setup, TAGS will be updated *automatically* every 5 minutes.
;; But you can manually update TAGS by `M-x find-and-ctags-update-all-tags-force'.
;; If you want to manually update the TAGS, `M-x find-and-ctags-update-all-tags-force'.
;;
;; After `'tags-table-list' is set, You can `M-x find-tag' to start code navigation
;;
;; You can use `(find-and-ctags-get-hostname)' for per computer setup.
;; For example, if my home PC hostname is like `AU0247589',
;; Here is sample code how I specify my C++ setup for home ONLY:
;;
;;   (if (string-match "^AU.*" (find-and-ctags-get-hostname))
;;      (setq my-default-ctags-options "--I IMPLEMENT_ABSTRACT_CLASS"))
;;
;; See https://github.com/redguardtoo/find-and-ctags/ for more tips

;;; Code:

(defvar find-and-ctags-auto-update-tags-interval 600
  "The interval to update TAGS.
It's used by `find-and-ctags-auto-update-tags' and in seconds format.
Default value is 600 which equals 5 minutes.")

(defvar find-and-ctags-gnu-find-executable nil
  "The path of GNU find.
If it's nil, it will be automatically detected.")

(defvar find-and-ctags-ctags-executable nil
  "The path of ctags.
If it's nil, it will be automatically detected.")

(defvar find-and-ctags-cli-opts-hash (make-hash-table :test 'equal)
  "The options to update TAGS.  The path of TAGS is key of hash.
Command line options is value.")

;; Is Microsoft Windows?
(defconst find-and-ctags-windows-p (eq system-type 'windows-nt))

;; Timer to run auto-update TAGS.
(defvar find-and-ctags-updated-timer nil)

(defun find-and-ctags--guess-executable (name)
  "Guess executable full path from its NAME on Windows."
  (let (rlt)
    (if find-and-ctags-windows-p
        (cond
         ((file-executable-p (setq rlt (concat "c:\\\\cygwin64\\\\bin\\\\" name ".exe"))))
         ((file-executable-p (setq rlt (concat "d:\\\\cygwin64\\\\bin\\\\" name ".exe"))))
         ((file-executable-p (setq rlt (concat "e:\\\\cygwin64\\\\bin\\\\" name ".exe"))))
         ((file-executable-p (setq rlt (concat "c:\\\\cygwin\\\\bin\\\\" name ".exe"))))
         ((file-executable-p (setq rlt (concat "d:\\\\cygwin\\\\bin\\\\" name ".exe"))))
         ((file-executable-p (setq rlt (concat "e:\\\\cygwin\\\\bin\\\\" name ".exe"))))
         (t (setq rlt nil))))
    (if rlt rlt name)))

(defun find-and-ctags--escape-options (opts)
  "Strip dangerous options."
  (setq opts (replace-regexp-in-string "\\(\\<exec\\>\\|\\<rm\\>\\|;\\||\\|&\\|`\\)" "" opts))
  opts)

(defun find-and-ctags--save-cli-options (file opts-matrix)
  "FILE as key, OPTS-LIST as value"
  (puthash file opts-matrix find-and-ctags-cli-opts-hash))

;;;###autoload
(defun find-and-ctags-get-hostname ()
  "Reliable way to get current hostname.
`(getenv \"HOSTNAME\")' won't work because $HOSTNAME is NOT an
 environment variable.
`system-name' won't work because /etc/hosts could be modified"
  (with-temp-buffer
    (shell-command "hostname" t)
    (goto-char (point-max))
    (delete-char -1)
    (buffer-string)))

;;;###autoload
(defun find-and-ctags-run-ctags-if-needed (src-dir &optional opts-matrix force)
  "Ask ctags to create TAGS and return the full path of TAGS.
SRC-DIR is the `default-directory' to run the command.
Each row of OPTS-MATRIX contains two items.
The first item is the command line options pass to `find'.
The second is the command line options pass `ctags'.
If FORCE is t, the commmand is executed without consulting the timer."
  ;; TODO save the ctags-opts into hash
  (let (find-opts
        ctags-opts
        (dir (file-name-as-directory (file-truename src-dir)) )
        (find-exe (or find-and-ctags-gnu-find-executable
                      (find-and-ctags--guess-executable "find")))
        (ctags-exe (or find-and-ctags-ctags-executable
                       (find-and-ctags--guess-executable "ctags")))
        file
        cmd
        doit)
    ;; default options for `find' and `ctags'
    (unless opts-matrix
      (setq opts-matrix '(("" ""))))
    (setq file (concat dir "TAGS"))
    (setq doit (or force (not (file-exists-p file))))

    ;; "cd dir && find . -name blah | ctags" will NOT work on windows cmd window
    ;; use relative directory because TAGS is shared between Cygwin and Window
    (let ((default-directory dir))
      (dolist (row opts-matrix)
        (setq find-opts (car row))
        (setq ctags-opts (cadr row))
        ;; (message "find-opts=%s ctags-opts=%s" find-opts ctags-opts)
        ;; always update cli options
        (find-and-ctags--save-cli-options file opts-matrix)
        (when doit
          (setq cmd (format "%s . -type f -not -name 'TAGS' %s | %s -e %s -L -"
                            find-exe
                            (find-and-ctags--escape-options find-opts)
                            ctags-exe
                            (find-and-ctags--escape-options ctags-opts)))
          (message "find-and-ctags runs: %s" cmd)
          (shell-command cmd))))
    file))

;;;###autoload
(defun find-and-ctags-current-path-match-pattern-p (regex)
  "Is current directory match the REGEX?"
  (let ((dir (if (buffer-file-name)
                 (file-name-directory (buffer-file-name))
               "")))
    (string-match-p regex dir)))

;;;###autoload
(defun find-and-ctags-current-full-filename-match-pattern-p (regex)
  "Is current full file name (including directory) match the REGEX?"
  (let ((dir (if (buffer-file-name) (buffer-file-name) "")))
    (string-match-p regex dir)))

;;;###autoload
(defun find-and-ctags-update-all-tags-force (&optional is-used-as-api)
  "Update all TAGS files listed in `tags-table-list'.
If IS-USED-AS-API is true, friendly message is suppressed"
  (interactive)
  (let (opts-matrix)
    (dolist (tag tags-table-list)
      (setq opts-matrix (gethash tag find-and-ctags-cli-opts-hash))
      (if opts-matrix
          (apply 'find-and-ctags-run-ctags-if-needed
                 ;; 1st parameter
                 (file-name-directory tag)
                 ;; 2nd and 3rd parameter
                 (list opts-matrix t))
        (find-and-ctags-run-ctags-if-needed (file-name-directory tag) '(("" "")) t))
      (unless is-used-as-api
        (message "All tag files in `tags-table-list' are updated!")))))

;;;###autoload
(defun find-and-ctags-auto-update-tags()
  (interactive)
  (cond
   ((not find-and-ctags-updated-timer)
    (setq find-and-ctags-updated-timer (current-time)))

   ((< (- (float-time (current-time)) (float-time find-and-ctags-updated-timer))
       find-and-ctags-auto-update-tags-interval)
    ;; do nothing
    )

   (t
    (setq find-and-ctags-updated-timer (current-time))
    (find-and-ctags-update-all-tags-force t)
    (message "All tag files have been updated after %d seconds!"
             (- (float-time (current-time)) (float-time find-and-ctags-updated-timer))))
   ))

(provide 'find-and-ctags)
;;; find-and-ctags.el ends here
