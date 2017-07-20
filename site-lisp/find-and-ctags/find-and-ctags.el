;;; find-and-ctags.el --- Use ctags&find to create TAGS on Winows/Linux/OSX

;; Copyright (C) 2014-2017 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/find-and-ctags
;; Keywords: find ctags
;; Version: 0.0.8

;; This file is not part of GNU Emacs.

;; This file is free software (GPLv3 License)

;;; Commentary:

;; Insert below setup into ~/.emacs.d/init.el:
;; (defun my-setup-develop-environment ()
;;   (interactive)
;;   ;; you can use `find-and-ctags-current-full-filename-match-pattern-p' instead
;;   (if (find-and-ctags-current-path-match-pattern-p "/MYPROJ")
;;     (vist-tags-table (find-and-ctags-run-ctags-if-needed "~/workspace/MYPROJ" ; project directory
;;                                                          '(("-not -size +64k" "--exclude=*.min.js") ; (find-opts ctags-opts)
;;                                                            ;; you may add more find-opts ctags-opts pair HERE to run find&ctags again to APPEND to same TAGS file
;;                                                            ;; ctags-opts must contain "-a" to append
;;                                                            ;; (find-opts "-a")
;;                                                            ))
;;                      t)))
;; (add-hook 'prog-mode-hook 'my-setup-develop-environment) ; prog-mode require emacs24+
;; (add-hook 'lua-mode-hook 'my-setup-develop-environment) ; lua-mode does NOT inherit from prog-mode
;; ;; OPTIONAL
;; (add-hook 'after-save-hook 'find-and-ctags-auto-update-tags)
;;
;; In above setup, TAGS is updated *automatically* every 5 minutes.
;; It can also be manually update by `find-and-ctags-update-all-tags-force'.
;;
;; You can use `find-and-ctags-get-hostname' for per computer setup.
;; For example, if my home PC hostname is like "AU0247589",
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
  (let* ((dir (file-name-as-directory (file-truename src-dir)) )
         (find-exe (or find-and-ctags-gnu-find-executable
                       (find-and-ctags--guess-executable "find")))
         (ctags-exe (or find-and-ctags-ctags-executable
                        (find-and-ctags--guess-executable "ctags")))

         (file (concat dir "TAGS"))
         cmd
         (doit (or force (not (file-exists-p file)))))
    ;; default options for `find' and `ctags'
    (unless opts-matrix
      (setq opts-matrix '(("" ""))))

    ;; "cd dir && find . -name blah | ctags" will NOT work on windows cmd window
    ;; use relative directory because TAGS is shared between Cygwin and Window
      (dolist (row opts-matrix)
        (let* ((default-directory dir)
               (find-opts (car row))
               (ctags-opts (cadr row))
               (cmd (format "%s . -type f -not -name 'TAGS' %s | %s -e %s -L -"
                            find-exe
                            (find-and-ctags--escape-options find-opts)
                            ctags-exe
                            (find-and-ctags--escape-options ctags-opts))))
          ;; (message "find-opts=%s ctags-opts=%s" find-opts ctags-opts)
          ;; always update cli options
          (find-and-ctags--save-cli-options file opts-matrix)
          (when doit
            (message "find&ctags runs %s at %s" cmd default-directory)
            (shell-command cmd))))
    file))

;;;#autoload
(defun find-and-ctags-generate-tags (src-dir &optional opts-matrix force)
  "Ask ctags to create TAGS and return the directory of TAGS.
SRC-DIR is the `default-directory' to run the command.
Each row of OPTS-MATRIX contains two items.
The first item is the command line options pass to `find'.
The second is the command line options pass `ctags'.
If FORCE is t, the commmand is executed without consulting the timer.

In summary, it's same as `find-and-ctags-run-ctags-if-needed' but return the directory of TAGS."
  (file-name-directory (find-and-ctags-run-ctags-if-needed)) )

(defun find-and-ctags-buffer-dir ()
  "Find a directory for current buffer.
Could be parent of `buffer-file-name' or `default-directory' or anything.
Make sure it's not nil."
  (or (if buffer-file-name (file-name-directory buffer-file-name))
      ;; buffer is created in real time
      default-directory
      ""))

;;;###autoload
(defun find-and-ctags-buffer-path ()
  "Find a path for current buffer.
Could be `buffer-file-name' or `default-directory' or anything.
Make sure it's not nil."
  (or buffer-file-name
      default-directory
      ""))

;;;###autoload
(defun find-and-ctags-current-path-match-pattern-p (regex)
  "Is current directory match the REGEX?
We use parent directory of `buffer-file-name'.
If it's nil, fallback to `default-directory'."
  (string-match-p regex (find-and-ctags-buffer-dir)))

;;;###autoload
(defun find-and-ctags-current-full-filename-match-pattern-p (regex)
  "Is buffer match the REGEX?
We use `buffer-file-name' at first.
If it's nil, fallback to `default-directory'."
  (string-match-p regex (find-and-ctags-buffer-path)))

;;;###autoload
(defun find-and-ctags-update-all-tags-force (&optional is-used-as-api)
  "Update all TAGS files listed in `tags-table-list'.
If IS-USED-AS-API is true, friendly message is suppressed"
  (interactive)
  (let* (opts-matrix
         (tags-list tags-table-list))
    (if tags-file-name
        (setq tags-list (add-to-list 'tags-list tags-file-name)))
    (dolist (tag tags-list)
      (unless (string-match-p "TAGS$" tag)
        (setq tag (concat (file-name-absolute-p tag) "TAGS")))
      (setq opts-matrix (gethash tag find-and-ctags-cli-opts-hash))
      (if opts-matrix
          (apply 'find-and-ctags-run-ctags-if-needed
                 ;; 1st parameter
                 (file-name-directory tag)
                 ;; 2nd and 3rd parameter
                 (list opts-matrix t))
        (find-and-ctags-run-ctags-if-needed (file-name-directory tag) '(("" "")) t))
      (unless is-used-as-api
        (message "Tags in `tags-file-name' and `tags-table-list' are updated!")))))

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
