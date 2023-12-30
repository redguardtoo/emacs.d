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

(defun my-file-usage ()
  (interactive)
  (message (shell-command-to-string "du -kh")))

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


(defun my-dired-support-program (program pattern)
  "External PROGRAM can open files matching PATTERN."
  (push (list pattern program) dired-guess-shell-alist-user))

;; Run mplayer on multiple videos
(setq async-shell-command-buffer 'new-buffer)

(with-eval-after-load 'dired-x
  (my-dired-support-program (my-guess-mplayer-path)
                            (my-file-extensions-to-regexp my-media-file-extensions))

  (my-dired-support-program (if *unix* "zathura" "open")
                            (my-file-extensions-to-regexp '("pdf"
                                                            "pdf.gz"
                                                            "dvi"
                                                            "eps"
                                                            "ps")))

  ;; "e" to extract, "x" to extract with full path
  (my-dired-support-program "7z x"
                            (my-file-extensions-to-regexp '("rar"
                                                            "zip"
                                                            "7z")))

  (my-dired-support-program (if *unix* "feh" "open")
                            (my-file-extensions-to-regexp my-image-file-extensions))

  (my-dired-support-program (if *unix* "libreoffice" "open")
                            (my-file-extensions-to-regexp '("doc"
                                                            "docx"
                                                            "xls"
                                                            "xlsx"
                                                            "odt")))

  (my-dired-support-program "djview" "\\.djvu$")

  (my-dired-support-program "firefox"
                            (my-file-extensions-to-regexp '("xml"
                                                            "xhtml"
                                                            "html"
                                                            "htm"
                                                            "mht"
                                                            "epub"))))

(defvar my-dired-new-file-first-dirs
  '("bt/finished/\\'"
    "bt/torrents?/\\'"
    "documents?/\\'"
    "music/\\'"
    "dwhelper/\\'"
    "downloads?/\\'")
  "Dired directory patterns where newest files are on the top.")

(defun my-dired-mode-hook-setup ()
  "Set up Dired."
  (when (cl-find-if (lambda (regexp)
                      (let ((case-fold-search t))
                        (string-match regexp default-directory)))
                my-dired-new-file-first-dirs)
    (setq dired-actual-switches "-lat"))

  (dired-hide-details-mode 1)
  (diredfl-mode)
  (unless dired-subdir-alist (dired-build-subdir-alist))
  (local-set-key  "r" 'dired-up-directory)
  (local-set-key  "e" 'my-ediff-files)
  (local-set-key  "/" 'dired-isearch-filenames)
  (local-set-key  "\\" 'diredext-exec-git-command-in-shell))
(add-hook 'dired-mode-hook 'my-dired-mode-hook-setup)

;; https://www.emacswiki.org/emacs/EmacsSession which is easier to use
;; See `session-globals-regexp'
;; If the variable is named like "*-history", it will be *automatically* saved.
(defvar my-dired-directory-history nil
  "Recent directories accessed by dired.")

(defvar my-dired-exclude-directory-regexp nil
  "Dired directories matching this regexp are not added into directory history.")

(defun my-shell-directories-from-fasd ()
  "Directories from fasd (https://github.com/clvv/fasd) in shell."
  (and (executable-find "fasd")
       (my-nonempty-lines (shell-command-to-string "fasd -ld"))))

(defun my-shell-directories-from-z ()
  "Directories from z (https://github.com/rupa/z) in shell."
  (mapcar #'car (shellcop-directories-from-z)))

(defvar my-shell-directory-history-function #'my-shell-directories-from-fasd
  "Return directory history in shell.  Used by `my-recent-directory'.")

(defun my-recent-directory (&optional n)
  "Goto recent directories.
If N is not nil, only list directories in current project."
  (interactive "P")
  (unless recentf-mode (recentf-mode 1))
  (let* ((cands (cl-remove-if-not
                 #'file-exists-p
                 (delete-dups
                  (append my-dired-directory-history
                          (mapcar 'file-name-directory recentf-list)
                          (and my-shell-directory-history-function
                               (funcall my-shell-directory-history-function))))))
         (root-dir (if (ffip-project-root) (file-truename (ffip-project-root)))))

    (when (and n root-dir)
      ;; return directories in project root
      (setq cands
            (cl-remove-if-not (lambda (f) (path-in-directory-p f root-dir)) cands)))

    (when my-dired-exclude-directory-regexp
      (setq cands
            (cl-remove-if (lambda (f) (string-match my-dired-exclude-directory-regexp f))
                          cands)))

    (dired (completing-read "Directories: " cands))))

(with-eval-after-load 'dired
  (setq dired-kill-when-opening-new-dired-buffer nil)

  ;; search file name only when focus is over file
  (setq dired-isearch-filenames 'dwim)

  ;; when there is two dired buffer, Emacs will select another buffer
  ;; as target buffer (target for copying files, for example).
  ;; It's similar to windows commander.
  (setq dired-dwim-target t)

  ;; @see http://blog.twonegatives.com/post/19292622546/dired-dwim-target-is-j00-j00-magic
  ;; op open two new dired buffers side-by-side and give your new-found automagic power a whirl.
  ;; Now combine that with a nice window configuration stored in a register and you’ve got a pretty slick work flow.
  (setq dired-dwim-target t)

  (my-ensure 'dired-x)
  (my-ensure 'dired-aux) ; for `dired-dwim-target-directory'

  (defun my-dired-basename ()
    (file-name-base (car (dired-get-marked-files 'no-dir))))

  (defun my-mplayer-subtitle-option (subtitle directory)
    "Return mplayer option from SUBTITLE under DIRECTORY."
    (or (when subtitle
          (let* ((vobsub-p (string-match "\.sub$" subtitle))
                 (opt (if vobsub-p "-vobsub" "-sub"))
                 (basename (file-name-base subtitle)))
            (format "%s \"%s/%s\""
                    opt
                    directory
                    (if vobsub-p basename
                      (concat basename "." (file-name-extension subtitle))))))
        ""))

  (defun my-detect-subtitle (subtitle &optional search-in-dir)
    "Find SUBTITLE file and return mplayer option.
If SEARCH-IN-DIR is t, try to find the subtitle by searching in directory."
    (let* ((sub-directory "Subs")
           (subtitle-dir (file-name-as-directory (concat default-directory sub-directory)))
           rlt)
      (cond
       ((file-exists-p (concat subtitle-dir subtitle))
        (setq rlt (my-mplayer-subtitle-option subtitle sub-directory)))
       ((and search-in-dir
             (file-exists-p subtitle-dir)
             (fboundp 'string-distance))
        (my-ensure 'find-lisp)
        (let* ((files (find-lisp-find-files-internal subtitle-dir
                                                     (lambda (file dir)
                                                       (and (not (file-directory-p (expand-file-name file dir)))
                                                            (string-match "\\.srt\\|\\.sub$" file)))
                                                     (lambda (dir parent)
                                                       (not (or (string= dir ".")
                                                                (string= dir "..")
                                                                (file-symlink-p (expand-file-name dir parent)))))))
               (target (concat (downcase (file-name-base subtitle)) "english"))
               found
               distance
               (min-distance (length subtitle)))
          ;; find the subtitle whose file name is closest to the original file name
          (when (and files (> (length files) 0))
            (dolist (f files)
              (setq distance (string-distance target (downcase (file-name-base f))))
              (when (< distance min-distance)
                (setq min-distance distance)
                (setq found f)))
            (setq rlt (my-mplayer-subtitle-option found sub-directory))))))
      rlt))

  (defun my-dired-guess-default-hack (orig-func &rest args)
    "Detect subtitles for mplayer."
    (let* ((rlt (apply orig-func args)))
      (when (and (stringp rlt)
                 (string-match "^mplayer .*-quiet" rlt))
        ;; append subtitle to mplayer cli
        (setq rlt
              (format "%s %s"
                      rlt
                      (or
                       (my-detect-subtitle "English.sub")
                       (my-detect-subtitle "Chinese.sub")
                       (my-detect-subtitle (concat (my-dired-basename) ".sub"))
                       (my-detect-subtitle "English.srt")
                       (my-detect-subtitle "Chinese.srt")
                       (my-detect-subtitle (concat (my-dired-basename) ".srt") t)
                       ""))))
      rlt))
  (advice-add 'dired-guess-default :around #'my-dired-guess-default-hack)

  (defun my-dired-find-file-hack (orig-func &rest args)
    "Avoid accidentally editing huge file in dired."
    (let* ((file (dired-get-file-for-visit)))
      (cond
       ((my-binary-file-p file)
        ;; play media file instead of editing it
        (call-interactively 'dired-do-async-shell-command))

       (t
        (when (and (file-directory-p file)
                   ;; don't add directory when user pressing "^" in `dired-mode'
                   (not (string-match "\\.\\." file)))
          (unless (and my-dired-exclude-directory-regexp
                       (string-match my-dired-exclude-directory-regexp file))
            ;; clean up old items in `my-dired-directory-history'
            ;; before adding new item
            (setq my-dired-directory-history
                  (cl-remove-if-not #'file-exists-p my-dired-directory-history))

            ;; add current directory into history
            (push file my-dired-directory-history)))
        (apply orig-func args)))))
  (advice-add 'dired-find-file :around #'my-dired-find-file-hack)

  (defun my-dired-do-async-shell-command-hack (orig-func &rest args)
    "Mplayer scan dvd-ripped directory in dired correctly."
    (let* ((command (nth 0 args))
           (arg (nth 1 args))
           (file-list (nth 2 args))
           (first-file (file-truename (and file-list (car file-list)))))
      (ignore command)
      (ignore arg)
      (cond
       ;; play dvd directory
       ((file-directory-p first-file)
        (async-shell-command (format "%s -dvd-device %s dvd://1 dvd://2 dvd://3 dvd://4 dvd://1 dvd://5 dvd://6 dvd://7 dvd://8 dvd://9"
                                     (my-guess-mplayer-path)
                                     first-file)))
       (t
        (apply orig-func args)))))
  (advice-add 'dired-do-async-shell-command :around #'my-dired-do-async-shell-command-hack)

  (unless *is-a-mac*
    ;; sort file names (numbered) in dired
    ;; @see https://emacs.stackexchange.com/questions/5649/sort-file-names-numbered-in-dired/5650#5650
    ;; "-1" options breaks dired on mac sometimes
    (setq dired-listing-switches "-laGh1v --group-directories-first"))

  (setq dired-recursive-deletes 'always))

(defun my-computer-sleep-now ()
  "Make my computer sleep now."
  (interactive)
  (let* ((cmd (cond
               (*cygwin*
                "rundll32.exe PowrProf.dll,SetSuspendState")
               (*is-a-mac*
                "pmset sleepnow")
               (t
                "sudo pm-suspend"))))
    (shell-command cmd)))

(provide 'init-dired)
