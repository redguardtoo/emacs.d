;; -*- coding: utf-8; lexical-binding: t; -*-

(add-hook 'dired-mode-hook 'turn-on-stripe-buffer-mode)

;; search file name only when focus is over file
(setq dired-isearch-filenames 'dwim)
;; when there is two dired buffer, Emacs will select another buffer
;; as target buffer (target for copying files, for example).
;; It's similar to windows commander.
(setq dired-dwim-target t)
; Listing directory failed but access-file worked
(when (eq system-type 'darwin)
  (require 'ls-lisp)
  (setq ls-lisp-use-insert-directory-program nil))

(defun diredext-exec-git-command-in-shell (command &optional arg file-list)
  "Run a shell command `git COMMAND`' on the marked files.
If no files marked, always operate on current line in dired-mode."
  (interactive
   (let* ((files (dired-get-marked-files t current-prefix-arg)))
     (list
      ;; Want to give feedback whether this file or marked files are used:
      (dired-read-shell-command "git command on %s: " current-prefix-arg files)
      current-prefix-arg
      files)))
  (unless (string-match "[*?][ \t]*\\'" command)
    (setq command (concat command " *")))
  (setq command (concat "git " command))
  (dired-do-shell-command command arg file-list)
  (message command))

(defvar binary-file-name-regexp "\\.\\(avi\\|pdf\\|mp[34g]\\|mkv\\|exe\\|3gp\\|rmvb\\|rm\\)$"
  "Is binary file name?")

;; https://www.emacswiki.org/emacs/EmacsSession which is easier to setup than "desktop.el"
;; See `session-globals-regexp' in "session.el".
;; If the variable is named like "*-history", it will be automaticlaly saved.
(defvar my-dired-directory-history nil "Recent directories accessed by dired.")
;; avoid accidently edit huge media file in dired
(defadvice dired-find-file (around dired-find-file-hack activate)
  (let* ((file (dired-get-file-for-visit)))
    (cond
     ((string-match-p binary-file-name-regexp file)
      ;; confirm before open big file
      (if (yes-or-no-p "Edit binary file?") ad-do-it))
     (t
      (when (file-directory-p file)
        (add-to-list 'my-dired-directory-history file))
      ad-do-it))))

(defadvice dired-do-async-shell-command (around dired-do-async-shell-command activate)
  "Mplayer scan dvd-ripped directory in dired correctly."
  (let* ((args (ad-get-args 0))
         (first-file (file-truename (and file-list (car file-list)))))
    (cond
     ((file-directory-p first-file)
      (async-shell-command (format "%s -dvd-device %s dvd://1 dvd://2 dvd://3 dvd://4 dvd://1 dvd://5 dvd://6 dvd://7 dvd://8 dvd://9"
                                   (my-guess-mplayer-path)
                                   first-file)))
     (t
      ad-do-it))))

(defadvice dired-guess-default (after dired-guess-default-after-hack activate)
  (when (and (stringp ad-return-value)
             (string-match-p "^mplayer -quiet" ad-return-value))
    (let* ((dir (file-name-as-directory (concat default-directory
                                                "Subs")))
           (files (car (ad-get-args 0)))
           basename)
      (cond
       ((file-exists-p (concat dir "English.sub"))
        (setq ad-return-value (concat ad-return-value
                                      " -vobsub Subs/English")))
       ((file-exists-p (concat dir "Chinese.sub"))
        (setq ad-return-value (concat ad-return-value
                                      " -vobsub Subs/Chinese")))
       ((file-exists-p (concat dir (setq basename (file-name-base (car (dired-get-marked-files 'no-dir)))) ".sub"))
        (setq ad-return-value (concat ad-return-value
                                      " -vobsub Subs/" basename)))
       ((file-exists-p (concat dir "English.srt"))
        (setq ad-return-value (concat ad-return-value
                                      " -sub Subs/English.srt")))
       ((file-exists-p (concat dir "Chinese.srt"))
        (setq ad-return-value (concat ad-return-value
                                      " -sub Subs/Chinesesrt")))
       ((file-exists-p (concat dir (setq basename (file-name-base (car (dired-get-marked-files 'no-dir)))) ".sub"))
        (setq ad-return-value (concat ad-return-value
                                      " -sub Subs/" basename ".srt"))))))
  ad-return-value)

;; @see http://blog.twonegatives.com/post/19292622546/dired-dwim-target-is-j00-j00-magic
;; op open two new dired buffers side-by-side and give your new-found automagic power a whirl.
;; Now combine that with a nice window configuration stored in a register and you’ve got a pretty slick work flow.
(setq dired-dwim-target t)

(eval-after-load 'dired
  '(progn
     ;; @see https://emacs.stackexchange.com/questions/5649/sort-file-names-numbered-in-dired/5650#5650
     (setq dired-listing-switches "-laGh1v")
     ;; {{ @see https://oremacs.com/2017/03/18/dired-ediff/
     ;; -*- lexical-binding: t -*-
     (defun ora-ediff-files ()
       (interactive)
       (let* ((files (dired-get-marked-files))
              (wnd (current-window-configuration)))
         (if (<= (length files) 2)
             (let* ((file1 (car files))
                    (file2 (if (cdr files)
                               (cadr files)
                             (read-file-name
                              "file: "
                              (dired-dwim-target-directory)))))
               (if (file-newer-than-file-p file1 file2)
                   (ediff-files file2 file1)
                 (ediff-files file1 file2))
               (add-hook 'ediff-after-quit-hook-internal
                         (lambda ()
                           (setq ediff-after-quit-hook-internal nil)
                           (set-window-configuration wnd))))
           (error "no more than 2 files should be marked"))))
     (define-key dired-mode-map "e" 'ora-ediff-files)
     ;; }}
     ;; from 24.4, dired+ can show/hide dired details by press "("
     (define-key dired-mode-map "/" 'dired-isearch-filenames)
     (define-key dired-mode-map "\\" 'diredext-exec-git-command-in-shell)

     (local-require 'dired+)
     (setq dired-recursive-deletes 'always)
     (dolist (file `(((if *unix* "zathura" "open") "pdf" "dvi" "pdf.gz" "ps" "eps")
                     ("7z x" "rar" "zip" "7z") ; "e" to extract, "x" to extract with full path
                     ((if (not *is-a-mac*) (my-guess-mplayer-path) "open")  "ogm" "avi" "mpg" "rmvb" "rm" "flv" "wmv" "mkv" "mp4" "m4v" "webm" "part" "mov")
                     ((concat (my-guess-mplayer-path) " -playlist") "list" "pls")
                     ((if *unix* "feh" "open") "gif" "jpeg" "jpg" "tif" "png" )
                     ((if *unix* "libreoffice" "open") "doc" "docx" "xls" "xlsx" "odt")
                     ("djview" "djvu")
                     ("firefox" "xml" "xhtml" "html" "htm" "mht" "epub")))
       (add-to-list 'dired-guess-shell-alist-user
                    (list (concat "\\." (regexp-opt (cdr file) t) "$")
                          (car file))))))

;; {{ Write backup files to own directory
;; @see https://www.gnu.org/software/emacs/manual/html_node/tramp/Auto_002dsave-and-Backup.html
(setq backup-enable-predicate
      (lambda (name)
        (and (normal-backup-enable-predicate name)
             (not (string-match-p binary-file-name-regexp name)))))

(if (not (file-exists-p (expand-file-name "~/.backups")))
  (make-directory (expand-file-name "~/.backups")))
(setq backup-by-coping t ; don't clobber symlinks
      backup-directory-alist '(("." . "~/.backups"))
      delete-old-versions t
      version-control t  ;use versioned backups
      kept-new-versions 6
      kept-old-versions 2)

;; Donot make backups of files, not safe
;; @see https://github.com/joedicastro/dotfiles/tree/master/emacs
(setq vc-make-backup-files nil)
;; }}

;; {{ try to re-play the last dired commands
(defvar my-dired-commands-history nil
  "History of `dired-do-shell-command' arguments.")
(defun my-format-dired-args (args)
  (let* ((cmd (file-name-nondirectory (nth 0 args))))
    (format "%s %s"
            (car (split-string cmd " "))
            (nth 2 args))))

(defadvice dired-do-shell-command (before dired-do-shell-command-before-hack activate)
  (let* ((args (ad-get-args 0))
         (files (nth 2 args)))
    ;; only record command which operate on files
    (when (and (listp files)
               (> (length files) 0))
      (add-to-list 'my-dired-commands-history
                   (list (my-format-dired-args args)
                         default-directory
                         args)))))

(defun my-dired-redo-last-command ()
  "Redo last shell command."
  (interactive)
  (let* ((info (car my-dired-commands-history)))
    (when info
      (let* ((default-directory (nth 1 info))
             (args (nth 2 info)))
        (apply 'dired-do-shell-command args)))))

(defun my-dired-redo-from-commands-history ()
  "Redo one of previous shell commands."
  (interactive)
  (when my-dired-commands-history
    (ivy-read "Previous dired shell commands:"
              my-dired-commands-history
              :action
              (lambda (info)
                (let* ((default-directory (nth 1 info))
                       (args (nth 2 info)))
                  (apply 'dired-do-shell-command args))))))
;; }}

;; {{ tramp setup
(add-to-list 'backup-directory-alist
             (cons tramp-file-name-regexp nil))
(setq tramp-chunksize 8192)

;; @see https://github.com/syl20bnr/spacemacs/issues/1921
;; If you tramp is hanging, you can uncomment below line.
;; (setq tramp-ssh-controlmaster-options "-o ControlMaster=auto -o ControlPath='tramp.%%C' -o ControlPersist=no")
;; }}
(provide 'init-dired)
