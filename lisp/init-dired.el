(autoload 'turn-on-stripe-buffer-mode "stripe-buffer" "" nil)
(autoload 'turn-on-stripe-table-mode "stripe-buffer" "" nil)
(add-hook 'dired-mode-hook 'turn-on-stripe-buffer-mode)


;; search file name only when focus is over file
(setq dired-isearch-filenames 'dwim)

(defun diredext-exec-git-command-in-shell (command &optional arg file-list)
  "Run a shell command `git COMMAND`' on the marked files.
if no files marked, always operate on current line in dired-mode
"
  (interactive
   (let ((files (dired-get-marked-files t current-prefix-arg)))
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

;; @see http://blog.twonegatives.com/post/19292622546/dired-dwim-target-is-j00-j00-magic
;; op open two new dired buffers side-by-side and give your new-found automagic power a whirl.
;; Now combine that with a nice window configuration stored in a register and you’ve got a pretty slick work flow.
(setq dired-dwim-target t)

(eval-after-load 'dired
  '(progn
     ;; from 24.4, dired+ can show/hide dired details by press "("
     (define-key dired-mode-map "/" 'dired-isearch-filenames)
     (define-key dired-mode-map "\\" 'diredext-exec-git-command-in-shell)

     (require 'dired+)
     (setq dired-recursive-deletes 'always)
     (dolist (file `(((if *unix* "zathura" "open") "pdf" "dvi" "pdf.gz" "ps" "eps")
                     ("unrar x" "rar")
                     ((if *unix* (my-guess-mplayer-path) "open")  "avi" "mpg" "rmvb" "rm" "flv" "wmv" "mkv" "mp4" "m4v" "webm")
                     ((concat (my-guess-mplayer-path) " -playlist") "list" "pls")
                     ((if *unix* "feh" "open") "gif" "jpeg" "jpg" "tif" "png" )
                     ("7z x" "7z")
                     ("djview" "djvu")
                     ("firefox" "xml" "xhtml" "html" "htm" "mht")))
       (add-to-list 'dired-guess-shell-alist-default
                    (list (concat "\\." (regexp-opt (cdr file) t) "$")
                          (car file))))
     ))

(provide 'init-dired)
