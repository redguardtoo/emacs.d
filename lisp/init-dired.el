;; -*- coding: utf-8; lexical-binding: t; -*-
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

(defun my-ediff-files ()
  "@see https://oremacs.com/2017/03/18/dired-ediff/."
  (interactive)
  (let* ((files (dired-get-marked-files))
         (wnd (current-window-configuration)))
    (cond
     ((<= (length files) 2)
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
                    (set-window-configuration wnd)))))
     (t
      (error "no more than 2 files should be marked")))))


(with-eval-after-load 'dired-x
  (dolist (file `(((if *unix* "zathura" "open") "pdf" "dvi" "pdf.gz" "ps" "eps")
                  ("7z x" "rar" "zip" "7z") ; "e" to extract, "x" to extract with full path
                  ((if (not *is-a-mac*) (my-guess-mplayer-path) "open") "ogm"
                   "avi"
                   "mpg"
                   "rmvb"
                   "rm"
                   "flv"
                   "wmv"
                   "mkv"
                   "mp4"
                   "m4v"
                   "wav"
                   "webm"
                   "part"
                   "mov"
                   "3gp"
                   "crdownload"
                   "mp3")
                  ((concat (my-guess-mplayer-path) " -playlist") "list" "pls")
                  ((if *unix* "feh" "open") "gif" "jpeg" "jpg" "tif" "png" )
                  ((if *unix* "libreoffice" "open") "doc" "docx" "xls" "xlsx" "odt")
                  ("djview" "djvu")
                  ("firefox" "xml" "xhtml" "html" "htm" "mht" "epub")))
    (add-to-list 'dired-guess-shell-alist-user
                 (list (concat "\\." (regexp-opt (cdr file) t) "$")
                       (car file)))))

(defun dired-mode-hook-setup ()
  "Set up dired."
  (dired-hide-details-mode 1)
  (local-set-key  "e" 'my-ediff-files)
  (local-set-key  "/" 'dired-isearch-filenames)
  (local-set-key  "\\" 'diredext-exec-git-command-in-shell))
(add-hook 'dired-mode-hook 'dired-mode-hook-setup)

;; https://www.emacswiki.org/emacs/EmacsSession which is easier to use
;; See `session-globals-regexp'
;; If the variable is named like "*-history", it will be *automatically* saved.
(defvar my-dired-directory-history nil
  "Recent directories accessed by dired.")

(with-eval-after-load 'dired
  ;; search file name only when focus is over file
  (setq dired-isearch-filenames 'dwim)

  ;; when there is two dired buffer, Emacs will select another buffer
  ;; as target buffer (target for copying files, for example).
  ;; It's similar to windows commander.
  (setq dired-dwim-target t)

  ;; Listing directory failed but access-file worked
  (when (eq system-type 'darwin)
    (require 'ls-lisp)
    (setq ls-lisp-use-insert-directory-program nil))

  ;; @see http://blog.twonegatives.com/post/19292622546/dired-dwim-target-is-j00-j00-magic
  ;; op open two new dired buffers side-by-side and give your new-found automagic power a whirl.
  ;; Now combine that with a nice window configuration stored in a register and you’ve got a pretty slick work flow.
  (setq dired-dwim-target t)

  (my-ensure 'dired-x)
  (my-ensure 'dired-aux) ; for `dired-dwim-target-directory'

  (defun my-dired-basename ()
    (file-name-base (car (dired-get-marked-files 'no-dir))))

  (defun my-dired-guess-default-hack (orig-func &rest args)
    "Detect subtitles for mplayer."
    (let* ((rlt (apply orig-func args)))
      (message "rlt=%s" rlt)
      (when (and (stringp rlt)
                 (string-match-p "^mplayer -quiet" rlt))
        (let* ((dir (file-name-as-directory (concat default-directory
                                                    "Subs")))
               (files (car args))
               basename)
          ;; append subtitle to mplayer cli
          (cond
           ((file-exists-p (concat dir "English.sub"))
            (setq rlt (concat rlt " -vobsub Subs/English")))
           ((file-exists-p (concat dir "Chinese.sub"))
            (seq rlt (concat rlt " -vobsub Subs/Chinese")))
           ((file-exists-p (concat dir (setq basename (my-dired-basename)) ".sub"))
            (setq rlt (concat rlt " -vobsub Subs/" basename)))
           ((file-exists-p (concat dir "English.srt"))
            (setq rlt (concat rlt " -sub Subs/English.srt")))
           ((file-exists-p (concat dir "Chinese.srt"))
            (setq rlt (concat rlt " -sub Subs/Chinese.srt")))
           ((file-exists-p (concat dir (setq basename (my-dired-basename)) ".sub"))
            (setq rlt (concat rlt " -sub Subs/" basename ".srt"))))))
      rlt))
  (advice-add 'dired-guess-default :around #'my-dired-guess-default-hack)

  (defun my-dired-find-file-hack (orig-func &rest args)
    "Avoid accidentally editing huge file in dired."
    (let* ((file (dired-get-file-for-visit)))
      (cond
       ((string-match-p my-binary-file-name-regexp file)
        ;; confirm before opening big file
        (when (yes-or-no-p "Edit binary file?")
          (apply orig-func args)))
       (t
        (when (and (file-directory-p file)
                   ;; don't add directory when user pressing "^" in `dired-mode'
                   (not (string-match-p "\\.\\." file)))
          (add-to-list 'my-dired-directory-history file))
        (apply orig-func args)))))
  (advice-add 'dired-find-file :around #'my-dired-find-file-hack)

  (defun my-dired-do-async-shell-command-hack (orig-func &rest args)
    "Mplayer scan dvd-ripped directory in dired correctly."
    (let* ((command (nth 0 args))
           (arg (nth 1 args))
           (file-list (nth 2 args))
           (first-file (file-truename (and file-list (car file-list)))))
      (cond
       ((file-directory-p first-file)
        (async-shell-command (format "%s -dvd-device %s dvd://1 dvd://2 dvd://3 dvd://4 dvd://1 dvd://5 dvd://6 dvd://7 dvd://8 dvd://9"
                                     (my-guess-mplayer-path)
                                     first-file)))
       (t
        (apply orig-func args)))))
  (advice-add 'dired-do-async-shell-command :around #'my-dired-do-async-shell-command-hack)

  ;; @see https://emacs.stackexchange.com/questions/5649/sort-file-names-numbered-in-dired/5650#5650
  (setq dired-listing-switches "-laGh1v")
  (setq dired-recursive-deletes 'always))

(provide 'init-dired)
