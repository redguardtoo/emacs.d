;;----------------------------------------------------------------------------
;; Some basic preferences
;;----------------------------------------------------------------------------
(setq-default
 buffers-menu-max-size 30
 case-fold-search t
 compilation-scroll-output t
 ediff-split-window-function 'split-window-horizontally
 ediff-window-setup-function 'ediff-setup-windows-plain
 grep-highlight-matches t
 grep-scroll-output t
 indent-tabs-mode nil
 line-spacing 0.2
 mouse-yank-at-point t
 set-mark-command-repeat-pop t
 tooltip-delay 1.5
 truncate-lines nil
 truncate-partial-width-windows nil
 ;; no annoying beep on errors
 visible-bell t)

;; use my own bmk if it exists
(if (file-exists-p (file-truename "~/.emacs.bmk"))
    (setq bookmark-default-file (file-truename "~/.emacs.bmk")))

(global-auto-revert-mode)
(setq global-auto-revert-non-file-buffers t
      auto-revert-verbose nil)

;; @see http://www.quora.com/Whats-the-best-way-to-edit-remote-files-from-Emacs
(setq tramp-default-method "ssh")
(setq tramp-auto-save-directory "~/.backups/tramp/")
(setq tramp-chunksize 8192)

;; But don't show trailing whitespace in SQLi, inf-ruby etc.
(add-hook 'comint-mode-hook
          (lambda () (setq show-trailing-whitespace nil)))

(transient-mark-mode t)

(define-key global-map (kbd "RET") 'newline-and-indent)

(add-to-list 'auto-mode-alist '("\\.[Cc][Ss][Vv]\\'" . csv-mode))
(autoload 'csv-mode "csv-mode" "Major mode for comma-separated value files." t)

(autoload 'find-by-pinyin-dired "find-by-pinyin-dired" "" t)

;;----------------------------------------------------------------------------
;; Don't disable narrowing commands
;;----------------------------------------------------------------------------
(put 'narrow-to-region 'disabled nil)
(put 'narrow-to-page 'disabled nil)
(put 'narrow-to-defun 'disabled nil)

;;----------------------------------------------------------------------------
;; Show matching parens
;;----------------------------------------------------------------------------
(paren-activate)     ; activating mic-paren

;;----------------------------------------------------------------------------
;; Fix per-window memory of buffer point positions
;;----------------------------------------------------------------------------
(global-pointback-mode)

;;----------------------------------------------------------------------------
;; Handy key bindings
;;----------------------------------------------------------------------------
;; To be able to M-x without meta
(global-set-key (kbd "C-x C-m") 'execute-extended-command)

(global-set-key (kbd "C-.") 'set-mark-command)
(global-set-key (kbd "C-x C-.") 'pop-global-mark)

;;----------------------------------------------------------------------------
;; Page break lines
;;----------------------------------------------------------------------------
(global-page-break-lines-mode)

;;----------------------------------------------------------------------------
;; Shift lines up and down with M-up and M-down
;;----------------------------------------------------------------------------
(move-text-default-bindings)

(defun suspend-mode-during-cua-rect-selection (mode-name)
  "Add an advice to suspend `MODE-NAME' while selecting a CUA rectangle."
  (let ((flagvar (intern (format "%s-was-active-before-cua-rectangle" mode-name)))
        (advice-name (intern (format "suspend-%s" mode-name))))
    (eval-after-load 'cua-rect
      `(progn
         (defvar ,flagvar nil)
         (make-variable-buffer-local ',flagvar)
         (defadvice cua--activate-rectangle (after ,advice-name activate)
           (setq ,flagvar (and (boundp ',mode-name) ,mode-name))
           (when ,flagvar
             (,mode-name 0)))
         (defadvice cua--deactivate-rectangle (after ,advice-name activate)
           (when ,flagvar
             (,mode-name 1)))))))

(eval-after-load 'grep
  '(progn
     (dolist (v '("auto"
                  "target"
                  "node_modules"
                  "bower_components"
                  ".sass_cache"
                  ".cache"
                  ".git"
                  ".cvs"
                  ".svn"
                  ".hg"
                  "elpa"))
       (add-to-list 'grep-find-ignored-directories v))
     ))

(add-hook 'grep-mode-hook (lambda () (toggle-truncate-lines 1)))
;;----------------------------------------------------------------------------
;; Random line sorting
;;----------------------------------------------------------------------------
(defun sort-lines-random (beg end)
  "Sort lines in region randomly."
  (interactive "r")
  (save-excursion
    (save-restriction
      (narrow-to-region beg end)
      (goto-char (point-min))
      (let ;; To make `end-of-line' and etc. to ignore fields.
          ((inhibit-field-text-motion t))
        (sort-subr nil 'forward-line 'end-of-line nil nil
                   (lambda (s1 s2) (eq (random 2) 0)))))))

(add-hook 'prog-mode-hook
          '(lambda ()
             (unless (is-buffer-file-temp)
               ;; highlight FIXME/BUG/TODO in comment
               (require 'fic-mode)
               (fic-mode 1)
               ;; enable for all programming modes
               ;; http://emacsredux.com/blog/2013/04/21/camelcase-aware-editing/
               (subword-mode)
               (if *emacs24* (electric-pair-mode 1))
               ;; eldoc, show API doc in minibuffer echo area
               (turn-on-eldoc-mode)
               ;; show trailing spaces in a programming mod
               (setq show-trailing-whitespace t)
               )))

;; turns on auto-fill-mode, don't use text-mode-hook because for some
;; mode (org-mode for example), this will make the exported document
;; ugly!
;; (add-hook 'markdown-mode-hook 'turn-on-auto-fill)
(add-hook 'change-log-mode-hook 'turn-on-auto-fill)
(add-hook 'cc-mode-hook 'turn-on-auto-fill)
(global-set-key (kbd "C-c q") 'auto-fill-mode)

;; {{ whitespace
;; (require 'whitespace)
;; (setq whitespace-style '(face empty tabs lines-tail trailing))
;; (global-whitespace-mode t)
;; }}

;; some project prefer tab, so be it
;; @see http://stackoverflow.com/questions/69934/set-4-space-indent-in-emacs-in-text-mode
(setq-default tab-width 4)
(defun toggle-indent-tab ()
  (interactive)
  (if indent-tabs-mode
      (progn
        (setq indent-tabs-mode nil))
    (progn
        (setq indent-tabs-mode t)
        (setq indent-line-function 'insert-tab)
      )))
;;----------------------------------------------------------------------------
;; Misc config - yet to be placed in separate files
;;----------------------------------------------------------------------------
;; {{ shell and conf
(add-to-list 'auto-mode-alist '("\\.[^b][^a][a-zA-Z]*rc$" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.aspell\\.en\\.pws\\'" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.meta\\'" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.ctags\\'" . conf-mode))
;; }}

;; java
(add-to-list 'auto-mode-alist '("\\.aj\\'" . java-mode))

(add-to-list 'auto-mode-alist '("archive-contents\\'" . emacs-lisp-mode))
;; makefile
(add-to-list 'auto-mode-alist '("\\.ninja$" . makefile-gmake-mode))

;; midnight mode purges buffers which haven't been displayed in 3 days
(require 'midnight)
(setq midnight-mode t)

(add-auto-mode 'tcl-mode "Portfile\\'")
(fset 'yes-or-no-p 'y-or-n-p)

(column-number-mode 1)

;; NO automatic new line when scrolling down at buffer bottom
(setq next-line-add-newlines nil)

;; @see http://stackoverflow.com/questions/4222183/emacs-how-to-jump-to-function-definition-in-el-file
(global-set-key (kbd "C-h C-f") 'find-function)

;Ctrl-X, u/l  to upper/lowercase regions without confirm
(put 'downcase-region 'disabled nil)
(put 'upcase-region 'disabled nil)

;; Write backup files to own directory
(if (not (file-exists-p (expand-file-name "~/.backups")))
    (make-directory (expand-file-name "~/.backups"))
    )
(setq
  backup-by-coping t ; don't clobber symlinks
  backup-directory-alist '(("." . "~/.backups"))
  delete-old-versions t
  kept-new-versions 6
  kept-old-versions 2
  version-control t  ;use versioned backups
  )

;; Donot make backups of files, not safe
;; @see https://github.com/joedicastro/dotfiles/tree/master/emacs
(setq vc-make-backup-files nil)

;; Don't disable narrowing commands
(put 'narrow-to-region 'disabled nil)
(put 'narrow-to-page 'disabled nil)
(put 'narrow-to-defun 'disabled nil)

(defun grep-pattern-into-list (regexp)
  (let ((s (buffer-string))
        (pos 0)
        item
        items)
    (while (setq pos (string-match regexp s pos))
      (setq item (match-string-no-properties 0 s))
      (setq pos (+ pos (length item)))
      (if (not (member item items))
          (add-to-list 'items item)
        ))
    items))

(defun grep-pattern-into-kill-ring (regexp)
  "Find all strings matching REGEXP in current buffer.
grab matched string and insert them into kill-ring"
  (interactive
   (let* ((regexp (read-regexp "grep regex:")))
     (list regexp)))
  (let (items rlt)
    (setq items (grep-pattern-into-list regexp))
    (dolist (i items)
      (setq rlt (concat rlt (format "%s\n" i)))
      )
    (kill-new rlt)
    (message "matched strings => kill-ring")
    rlt))

(defvar rimenu-position-pair nil "positions before and after imenu jump")
(add-hook 'imenu-after-jump-hook
          (lambda ()
            (let ((start-point (marker-position (car mark-ring)))
                  (end-point (point)))
              (setq rimenu-position-pair (list start-point end-point)))))

(defun rimenu-jump ()
  "jump to the closest before/after position of latest imenu jump"
  (interactive)
  (when rimenu-position-pair
    (let ((p1 (car rimenu-position-pair))
          (p2 (cadr rimenu-position-pair)))

      ;; jump to the far way point of the rimenu-position-pair
      (if (< (abs (- (point) p1))
             (abs (- (point) p2)))
          (goto-char p2)
          (goto-char p1))
      )))

(defun grep-pattern-jsonize-into-kill-ring (regexp)
  "Find all strings matching REGEXP in current buffer.
grab matched string, jsonize them, and insert into kill ring"
  (interactive
   (let* ((regexp (read-regexp "grep regex:")))
     (list regexp)))
  (let (items rlt)
    (setq items (grep-pattern-into-list regexp))
    (dolist (i items)
      (setq rlt (concat rlt (format "%s : %s ,\n" i i)))
      )
    (kill-new rlt)
    (message "matched strings => json => kill-ring")
    rlt))

(defun open-blog-on-current-month ()
  (interactive)
  (let (blog)
   (setq blog (file-truename (concat "~/blog/" (format-time-string "%Y-%m") ".org")) )
   (find-file blog)))

(defun grep-pattern-cssize-into-kill-ring (regexp)
  "Find all strings matching REGEXP in current buffer.
grab matched string, cssize them, and insert into kill ring"
  (interactive
   (let* ((regexp (read-regexp "grep regex:")))
     (list regexp)))
  (let (items rlt)
    (setq items (grep-pattern-into-list regexp))
    (dolist (i items)
      (setq i (replace-regexp-in-string "\\(class=\\|\"\\)" "" i))
      (setq rlt (concat rlt (format ".%s {\n}\n\n" i))))
    (kill-new rlt)
    (message "matched strings => json => kill-ring")
    rlt))

;; from RobinH, Time management
(setq display-time-24hr-format t)
(setq display-time-day-and-date t)
(display-time)

(global-set-key [f12] 'list-bookmarks)
(global-set-key (kbd "M-o") 'switch-window)

(when *win32*
  ;; resize frame
  (defun w32-maximize-frame ()
    "Maximize the current frame."
    (interactive)
    (w32-send-sys-command 61488)
    (global-set-key (kbd "C-c z") 'w32-restore-frame))

  (global-set-key (kbd "C-c z") 'w32-maximize-frame)

  (defun w32-restore-frame ()
    "Restore a minimized frame."
    (interactive)
    (w32-send-sys-command 61728)
    (global-set-key (kbd "C-c z") 'w32-maximize-frame))

  )

;; M-x ct ENTER
(defun ct (dir-name)
  "Create tags file."
  (interactive "DDirectory: ")
  (shell-command
   (format "ctags -f %s/TAGS -e -R %s" dir-name (directory-file-name dir-name)))
  )

; @see http://xahlee.blogspot.com/2012/01/emacs-tip-hotkey-for-repeat-complex.html
(global-set-key [f2] 'repeat-complex-command)

;effective emacs item 3
(global-set-key "\C-s" 'isearch-forward-regexp)
(global-set-key "\M-s" 'isearch-backward-regexp)
(global-set-key "\C-\M-s" 'tags-search)
(global-set-key "\C-x\C-n" 'find-file-other-frame) ;open new frame with a file

;;a no-op function to bind to if you want to set a keystroke to null
(defun void () "this is a no-op" (interactive))

;convert a buffer from dos ^M end of lines to unix end of lines
(defun dos2unix ()
  (interactive)
  (goto-char (point-min))
  (while (search-forward "\r" nil t) (replace-match "")))

;vice versa
(defun unix2dos ()
  (interactive)
  (goto-char (point-min))
  (while (search-forward "\n" nil t) (replace-match "\r\n")))

;show ascii table
(defun ascii-table ()
  "Print the ascii table. Based on a defun by Alex Schroeder <asc@bsiag.com>"
  (interactive)
  (switch-to-buffer "*ASCII*")
  (erase-buffer)
  (insert (format "ASCII characters up to number %d.\n" 254))
  (let ((i 0))
    (while (< i 254)
           (setq i (+ i 1))
           (insert (format "%4d %c\n" i i))))
  (beginning-of-buffer))


;; I'm in Australia now, so I set the locale to "en_AU"
(defun insert-date (prefix)
    "Insert the current date. With prefix-argument, use ISO format. With
   two prefix arguments, write out the day and month name."
    (interactive "P")
    (let ((format (cond
                   ((not prefix) "%d.%m.%Y")
                   ((equal prefix '(4)) "%Y-%m-%d")
                   ((equal prefix '(16)) "%d %B %Y")))
          )
      (insert (format-time-string format))))

(defun insert-blog-version ()
  "insert version of my blog post"
  (interactive)
  (insert (format-time-string "%Y%m%d"))
  )

;;compute the length of the marked region
(defun region-length ()
  "length of a region"
  (interactive)
  (message (format "%d" (- (region-end) (region-beginning)))))

(defalias 'list-buffers 'ibuffer)
;KEYBOARD SECTION
;global keyb maps
(global-set-key "\C-xc" 'clipboard-kill-ring-save)
(global-set-key "\C-cc" 'copy-region-as-kill)

;; @see http://www.emacswiki.org/emacs/BetterRegisters
;; This is used in the function below to make marked points visible
(defface register-marker-face '((t (:background "grey")))
      "Used to mark register positions in a buffer."
      :group 'faces)

;effective emacs item 7; no scrollbar, no menubar, no toolbar
(if (fboundp 'scroll-bar-mode) (scroll-bar-mode -1))
(if (fboundp 'tool-bar-mode) (tool-bar-mode -1))
;(if (fboundp 'menu-bar-mode) (menu-bar-mode -1))
;; effective emacs item 9
(defalias 'qrr 'query-replace-regexp)

(setq-default regex-tool-backend 'perl)

;; {{ work around color theme bug
;; @see https://plus.google.com/106672400078851000780/posts/KhTgscKE8PM
(defun disable-all-themes ()
  "disable all active themes."
  (dolist (i custom-enabled-themes)
    (disable-theme i)))

(defadvice load-theme (before disable-themes-first activate)
  (disable-all-themes))
;; }}

;;; {{ clipboard stuff
;; Use the system clipboard
(setq x-select-enable-clipboard t)

;; you need install xsel under Linux
;; xclip has some problem when copying under Linux
(defun copy-yank-str (msg &optional clipboard-only)
  (unless clipboard-only (kill-new msg))
  (cond
   ;; display-graphic-p need windows 23.3.1
   ((and (display-graphic-p) x-select-enable-clipboard)
    (x-set-selection 'CLIPBOARD msg))
   (t (with-temp-buffer
        (insert msg)
        (shell-command-on-region (point-min) (point-max)
                                 (cond
                                  ((eq system-type 'cygwin) "putclip")
                                  ((eq system-type 'darwin) "pbcopy")
                                  (t "xsel -ib")
                                  )))
    )))

(defun cp-filename-of-current-buffer ()
  "copy file name (NOT full path) into the yank ring and OS clipboard"
  (interactive)
  (let (filename)
    (when buffer-file-name
      (setq filename (file-name-nondirectory buffer-file-name))
      (copy-yank-str filename)
      (message "filename %s => clipboard & yank ring" filename)
      )))

(defun cp-filename-line-number-of-current-buffer ()
  "copy file:line into the yank ring and clipboard"
  (interactive)
  (let (filename linenum rlt)
    (when buffer-file-name
      (setq filename (file-name-nondirectory buffer-file-name))
      (setq linenum (save-restriction
                      (widen)
                      (save-excursion
                        (beginning-of-line)
                        (1+ (count-lines 1 (point))))))
      (setq rlt (format "%s:%d" filename linenum))
      (copy-yank-str rlt)
      (message "%s => clipboard & yank ring" rlt)
      )))

(defun cp-fullpath-of-current-buffer ()
  "copy full path into the yank ring and OS clipboard"
  (interactive)
  (when buffer-file-name
    (copy-yank-str (file-truename buffer-file-name))
    (message "file full path => clipboard & yank ring")
    ))

(defun copy-to-x-clipboard ()
  (interactive)
  (if (region-active-p)
      (progn
        (cond
         ((and (display-graphic-p) x-select-enable-clipboard)
          (x-set-selection 'CLIPBOARD (buffer-substring (region-beginning) (region-end))))
         (t (shell-command-on-region (region-beginning) (region-end)
                                     (cond
                                      (*cygwin* "putclip")
                                      (*is-a-mac* "pbcopy")
                                      (*linux* "xsel -ib")))
            ))
        (message "Yanked region to clipboard!")
        (deactivate-mark))
        (message "No region active; can't yank to clipboard!")))

(defun get-str-from-x-clipboard ()
  (let (s)
    (cond
     ((and (display-graphic-p) x-select-enable-clipboard)
      (setq s (x-selection 'CLIPBOARD)))
     (t (setq s (shell-command-to-string
                 (cond
                  (*cygwin* "getclip")
                  (*is-a-mac* "pbpaste")
                  (t "xsel -ob"))))
        ))
    s))


(defun paste-from-x-clipboard()
  "Paste string clipboard"
  (interactive)
  (insert (get-str-from-x-clipboard)))

(defun my/paste-in-minibuffer ()
  (local-set-key (kbd "M-y") 'paste-from-x-clipboard)
  )

(add-hook 'minibuffer-setup-hook 'my/paste-in-minibuffer)

(defun paste-from-clipboard-and-cc-kill-ring ()
  "paste from clipboard and cc the content into kill ring"
  (interactive)
  (let (str)
    (with-temp-buffer
      (paste-from-x-clipboard)
      (setq str (buffer-string)))
    ;; finish the paste
    (insert str)
    ;; cc the content into kill ring at the same time
    (kill-new str)
    ))
;;; }}

(eval-after-load 'speedbar '(if (load "mwheel" t)
                               ;; Enable wheelmouse support by default
                               (cond (window-system
                                       (mwheel-install)))))

; @see http://www.emacswiki.org/emacs/SavePlace
(require 'saveplace)
(setq-default save-place t)

;; {{expand-region.el
;; if emacs-nox, use C-@, else, use C-2;
(if window-system
 (progn
   (define-key global-map (kbd "C-2") 'er/expand-region)
   (define-key global-map (kbd "C-M-2") 'er/contract-region)
   )
 (progn
   (define-key global-map (kbd "C-@") 'er/expand-region)
   (define-key global-map (kbd "C-M-@") 'er/contract-region)
 )
)
;; }}

;;iedit-mode
(global-set-key (kbd "C-c ; i") 'iedit-mode-toggle-on-function)

;;align text
(global-set-key (kbd "C-c C-l") 'align-regexp)

;; my screen is tiny, so I use minimum eshell prompt
(setq eshell-prompt-function
       (lambda ()
         (concat (getenv "USER") " $ ")))

;; max frame, @see https://github.com/rmm5t/maxframe.el
(require 'maxframe)
;; (setq mf-max-width 1600) ;; Pixel width of main monitor. for dual-lcd only
(add-hook 'window-setup-hook 'maximize-frame t)

;; command-frequency
;; (require 'command-frequency)
;; (command-frequency-table-load)
;; (command-frequency-mode 1)
;; (command-frequency-autosave-mode 1)

(defun toggle-env-http-proxy ()
  "set/unset the environment variable http_proxy which w3m uses"
  (interactive)
  (let ((proxy "http://127.0.0.1:8000"))
    (if (string= (getenv "http_proxy") proxy)
        ;; clear the the proxy
        (progn
          (setenv "http_proxy" "")
          (message "env http_proxy is empty now")
          )
      ;; set the proxy
      (setenv "http_proxy" proxy)
      (message "env http_proxy is %s now" proxy)
        )
    ))

(defun strip-convert-lines-into-one-big-string (beg end)
"strip and convert selected lines into one big string which is copied into kill ring.
When transient-mark-mode is enabled, if no region is active then only the
current line is acted upon.

If the region begins or ends in the middle of a line, that entire line is
copied, even if the region is narrowed to the middle of a line.

Current position is preserved."
  (interactive "r")
  (let (str (orig-pos (point-marker)))
  (save-restriction
    (widen)
    (when (and transient-mark-mode (not (use-region-p)))
      (setq beg (line-beginning-position)
            end (line-beginning-position 2)))

    (goto-char beg)
    (setq beg (line-beginning-position))
    (goto-char end)
    (unless (= (point) (line-beginning-position))
      (setq end (line-beginning-position 2)))

    (goto-char beg)
    (setq str (replace-regexp-in-string "[ \t]*\n" "" (replace-regexp-in-string "^[ \t]+" "" (buffer-substring-no-properties beg end))))
    ;; (message "str=%s" str)
    (kill-new str)
    (goto-char orig-pos)))
  )

;; { smarter navigation to the beginning of a line
;; http://emacsredux.com/blog/2013/05/22/smarter-navigation-to-the-beginning-of-a-line/
(defun smarter-move-beginning-of-line (arg)
  "Move point back to indentation of beginning of line.

Move point to the first non-whitespace character on this line.
If point is already there, move to the beginning of the line.
Effectively toggle between the first non-whitespace character and
the beginning of the line.

If ARG is not nil or 1, move forward ARG - 1 lines first.  If
point reaches the beginning or end of the buffer, stop there."
  (interactive "^p")
  (setq arg (or arg 1))

  ;; Move lines first
  (when (/= arg 1)
    (let ((line-move-visual nil))
      (forward-line (1- arg))))

  (let ((orig-point (point)))
    (back-to-indentation)
    (when (= orig-point (point))
      (move-beginning-of-line 1))))

;; remap C-a to `smarter-move-beginning-of-line'
(global-set-key [remap move-beginning-of-line]
                'smarter-move-beginning-of-line)
;; }

(defun open-readme-in-git-root-directory ()
  (interactive)
  (let (filename
        (root-dir (locate-dominating-file (file-name-as-directory (file-name-directory buffer-file-name)) ".git"))
        )
    ;; (message "root-dir=%s" root-dir)
    (and root-dir (file-name-as-directory root-dir))
    (setq filename (concat root-dir "README.org"))
    (if (not (file-exists-p filename))
        (setq filename (concat root-dir "README.md"))
      )
    ;; (message "filename=%s" filename)
    (if (file-exists-p filename)
        (switch-to-buffer (find-file-noselect filename nil nil))
      (message "NO README.org or README.md found!"))
    ))
(global-set-key (kbd "C-c C-q") 'open-readme-in-git-root-directory)

;; from http://emacsredux.com/blog/2013/05/04/rename-file-and-buffer/
(defun vc-rename-file-and-buffer ()
  "Rename the current buffer and file it is visiting."
  (interactive)
  (let ((filename (buffer-file-name)))
    (if (not (and filename (file-exists-p filename)))
        (message "Buffer is not visiting a file!")
      (let ((new-name (read-file-name "New name: " filename)))
        (cond
         ((vc-backend filename) (vc-rename-file filename new-name))
         (t
          (rename-file filename new-name t)
          (rename-buffer new-name)
          (set-visited-file-name new-name)
          (set-buffer-modified-p nil)))))))

(defun vc-copy-file-and-rename-buffer ()
"copy the current buffer and file it is visiting.
if the old file is under version control, the new file is added into
version control automatically"
  (interactive)
  (let ((filename (buffer-file-name)))
    (if (not (and filename (file-exists-p filename)))
        (message "Buffer is not visiting a file!")
      (let ((new-name (read-file-name "New name: " filename)))
        (copy-file filename new-name t)
        (rename-buffer new-name)
        (set-visited-file-name new-name)
        (set-buffer-modified-p nil)
        (when (vc-backend filename)
          (vc-register)
         )))))

;; {{ @see http://emacsredux.com/blog/2013/04/21/edit-files-as-root/
(defun sudo-edit (&optional arg)
  "Edit currently visited file as root.
With a prefix ARG prompt for a file to visit.
Will also prompt for a file to visit if current
buffer is not visiting a file."
  (interactive "P")
  (if (or arg (not buffer-file-name))
      (find-file (concat "/sudo:root@localhost:"
                         (ido-read-file-name "Find file(as root): ")))
    (find-alternate-file (concat "/sudo:root@localhost:" buffer-file-name))))

(defadvice ido-find-file (after find-file-sudo activate)
  "Find file as root if necessary."
  (unless (and buffer-file-name
               (file-writable-p buffer-file-name))
    (find-alternate-file (concat "/sudo:root@localhost:" buffer-file-name))))
;; }}

;; {{ eval and replace anywhere
;; @see http://emacs.wordpress.com/2007/01/17/eval-and-replace-anywhere/
(defun fc-eval-and-replace ()
  "Replace the preceding sexp with its value."
  (interactive)
  (backward-kill-sexp)
  (condition-case nil
      (prin1 (eval (read (current-kill 0)))
             (current-buffer))
    (error (message "Invalid expression")
           (insert (current-kill 0)))))
(global-set-key (kbd "C-c e") 'fc-eval-and-replace)

(defun calc-eval-and-insert (&optional start end)
(interactive "r")
(let ((result (calc-eval (buffer-substring-no-properties start end))))
(goto-char (point-at-eol))
(insert " = " result)))

(defun calc-eval-line-and-insert ()
(interactive)
(calc-eval-and-insert (point-at-bol) (point-at-eol)))
(global-set-key (kbd "C-c C-e") 'calc-eval-line-and-insert)
;; }}

;; input open source license
(autoload 'legalese "legalese" "" t)

;; {{ buf-move
(autoload 'buf-move-left "buffer-move" "move buffer" t)
(autoload 'buf-move-right "buffer-move" "move buffer" t)
(autoload 'buf-move-up "buffer-move" "move buffer" t)
(autoload 'buf-move-down "buffer-move" "move buffer" t)
;; }}

;; edit confluence wiki
(autoload 'confluence-edit-mode "confluence-edit" "enable confluence-edit-mode" t)
(add-to-list 'auto-mode-alist '("\\.wiki\\'" . confluence-edit-mode))

;; {{string-edit.el
(autoload 'string-edit-at-point "string-edit" "enable string-edit-mode" t)
;; }}

;; {{ issue-tracker
(global-set-key (kbd "C-c C-t") 'issue-tracker-increment-issue-id-under-cursor)
;; }}

(defun erase-specific-buffer (num buf-name)
  (let ((message-buffer (get-buffer buf-name))
        (old-buffer (current-buffer)))
    (save-excursion
      (if (buffer-live-p message-buffer)
          (progn
            (switch-to-buffer message-buffer)
            (if (not (null num))
                (progn
                  (end-of-buffer)
                  (dotimes (i num)
                    (previous-line))
                  (set-register t (buffer-substring (point) (point-max)))
                  (erase-buffer)
                  (insert (get-register t))
                  (switch-to-buffer old-buffer))
              (progn
                (erase-buffer)
                (switch-to-buffer old-buffer))))
        (error "Message buffer doesn't exists!")
        ))))

;; {{ message buffer things
(defun erase-message-buffer (&optional num)
  "Erase the content of the *Messages* buffer in emacs.
    Keep the last num lines if argument num if given."
  (interactive "p")
  (let ((buf (cond
              ((eq 'ruby-mode major-mode) "*server*")
              (t "*Messages*"))))
    (erase-specific-buffer num buf)))

;; turn off read-only-mode in *Message* buffer, a "feature" in v24.4
(when (fboundp 'messages-buffer-mode)
  (defun messages-buffer-mode-hook-setup ()
    (message "messages-buffer-mode-hook-setup called")
    (read-only-mode -1))
  (add-hook 'messages-buffer-mode-hook 'messages-buffer-mode-hook-setup))
;; }}

;; vimrc
(autoload 'vimrc-mode "vimrc-mode")
(add-to-list 'auto-mode-alist '("\\.?vim\\(rc\\)?$" . vimrc-mode))

(autoload 'highlight-symbol-at-point "highlight-symbol" "" t)

;; {{ ack
(autoload 'ack-same "full-ack" nil t)
(autoload 'ack "full-ack" nil t)
(autoload 'ack-find-same-file "full-ack" nil t)
(autoload 'ack-find-file "full-ack" nil t)
;; }}

;; {{ show email sent by `git send-email' in gnus
(eval-after-load 'gnus
    '(progn
       (require 'gnus-article-treat-patch)
       (setq gnus-article-patch-conditions
             '( "^@@ -[0-9]+,[0-9]+ \\+[0-9]+,[0-9]+ @@" ))
       ))
;; }}

(defun toggle-full-window()
  "Toggle the full view of selected window"
  (interactive)
  ;; @see http://www.gnu.org/software/emacs/manual/html_node/elisp/Splitting-Windows.html
  (if (window-parent)
      (delete-other-windows)
    (winner-undo)
    ))

;; {{ copy the file-name/full-path in dired buffer into clipboard
;; `w` => copy file name
;; `C-u 0 w` => copy full path
(defadvice dired-copy-filename-as-kill (after dired-filename-to-clipboard activate)
  (with-temp-buffer
    (insert (current-kill 0))
    (shell-command-on-region (point-min) (point-max)
                             (cond
                              ((eq system-type 'cygwin) "putclip")
                              ((eq system-type 'darwin) "pbcopy")
                              (t "xsel -ib")
                              )))
  (message "%s => clipboard" (current-kill 0))
  )

;; }}

(defun insert-file-link-from-clipboard ()
  "Make sure the full path of file exist in clipboard. This command will convert
The full path into relative path insert it as a local file link in org-mode"
  (interactive)
  (let (str)
    (with-temp-buffer
      (paste-from-x-clipboard)
      (setq str (buffer-string)))

    ;; convert to relative path (relative to current buffer) if possible
    (let ((m (string-match (file-name-directory (buffer-file-name)) str) ))
      (when m
        (if (= 0 m )
            (setq str (substring str (length (file-name-directory (buffer-file-name)))))
          )
        )
        (insert (format "[[file:%s]]" str))
      )
    ))

(defun convert-image-to-css-code ()
  "convert a image into css code (base64 encode)"
  (interactive)
  (let (str
        rlt
        (file (read-file-name "The path of image:")))
    (with-temp-buffer
      (shell-command (concat "cat " file "|base64") 1)
      (setq str (replace-regexp-in-string "\n" "" (buffer-string)))
      )
    (setq rlt (concat "background:url(\"data:image/"
                      (car (last (split-string file "\\.")))
                      ";base64,"
                      str
                      "\") no-repeat 0 0;"
                      ))
    (kill-new rlt)
    (copy-yank-str rlt)
    (message "css code => clipboard & yank ring")
    ))

(defun current-font-face ()
  "get the font face under cursor"
  (interactive)
  (let ((rlt (format "%S" (get-text-property (- (point) 1) 'face))))
    (kill-new rlt)
    (copy-yank-str rlt)
    (message "%s => clipboard & yank ring" rlt)
      ))

(defun current-thing-at-point ()
  (interactive)
  (message "thing = %s" (thing-at-point 'symbol)))

(defun add-pwd-into-load-path ()
  "add current directory into load-path, useful for elisp developers"
  (interactive)
  (let ((dir (expand-file-name default-directory)))
    (if (not (memq dir load-path))
        (add-to-list 'load-path dir)
        )
    (message "Directory added into load-path:%s" dir)
    )
  )

;; {{ save history
(when (file-writable-p (file-truename "~/.emacs.d/history"))
  (setq history-length 8000)
  (setq savehist-additional-variables '(search-ring regexp-search-ring kill-ring))
  (savehist-mode 1))
;; }}

(setq system-time-locale "C")

;; {{ unique lines
(defun uniquify-all-lines-region (start end)
  "Find duplicate lines in region START to END keeping first occurrence."
  (interactive "*r")
  (save-excursion
    (let ((end (copy-marker end)))
      (while
          (progn
            (goto-char start)
            (re-search-forward "^\\(.*\\)\n\\(\\(.*\n\\)*\\)\\1\n" end t))
        (replace-match "\\1\n\\2")))))

(defun uniquify-all-lines-buffer ()
  "Delete duplicate lines in buffer and keep first occurrence."
  (interactive "*")
  (uniquify-all-lines-region (point-min) (point-max)))
;; }}

;; {{start dictionary lookup
;; use below commands to create dicitonary
;; mkdir -p ~/.stardict/dic
;; # wordnet English => English
;; curl http://abloz.com/huzheng/stardict-dic/dict.org/stardict-dictd_www.dict.org_wn-2.4.2.tar.bz2 | tar jx -C ~/.stardict/dic
;; # Langdao Chinese => English
;; curl http://abloz.com/huzheng/stardict-dic/zh_CN/stardict-langdao-ec-gb-2.4.2.tar.bz2 | tar jx -C ~/.stardict/dic
;;
(setq sdcv-dictionary-simple-list '("朗道英汉字典5.0"))
(setq sdcv-dictionary-complete-list '("WordNet"))
(autoload 'sdcv-search-pointer "sdcv" "show word explanation in buffer" t)
(autoload 'sdcv-search-input+ "sdcv" "show word explanation in tooltip" t)
(global-set-key (kbd "C-c ; b") 'sdcv-search-pointer)
(global-set-key (kbd "C-c ; t") 'sdcv-search-input+)
;; }}

;; {{smart-compile: http://www.emacswiki.org/emacs/SmartCompile
(autoload 'smart-compile "smart-compile" "" t)
;; }}

; {{ direx
(autoload 'direx:jump-to-directory "direx" "" t)
(global-set-key (kbd "C-x C-j") 'direx:jump-to-directory)
;; }}

;; {{ support MY packages which are not included in melpa
(autoload 'wxhelp-browse-class-or-api "wxwidgets-help" "" t)
(autoload 'issue-tracker-increment-issue-id-under-cursor "issue-tracker" "" t)
(autoload 'issue-tracker-insert-issue-list "issue-tracker" "" t)
(autoload 'elpamr-create-mirror-for-installed "elpa-mirror" "" t)
(autoload 'org2nikola-export-subtree "org2nikola" "" t)
(autoload 'org2nikola-rerender-published-posts "org2nikola" "" t)
;; }}

(setq web-mode-imenu-regexp-list
  '(("<\\(h[1-9]\\)\\([^>]*\\)>\\([^<]*\\)" 1 3 ">" nil)
    ("^[ \t]*<\\([@a-z]+\\)[^>]*>? *$" 1 " id=\"\\([a-zA-Z0-9_]+\\)\"" "#" ">")
    ("^[ \t]*<\\(@[a-z.]+\\)[^>]*>? *$" 1 " contentId=\"\\([a-zA-Z0-9_]+\\)\"" "=" ">")
    ))

;; {{ imenu
(setq imenu-max-item-length 128)
(setq imenu-max-item-length 64)
;; }}

(defun display-line-number ()
  "display current line number in mini-buffer"
  (interactive)
  (let (l)
    (setq l (line-number-at-pos))
    (message "line number:%d" l)
    ))

(defun toggle-web-js-offset ()
  "toggle js2-basic-offset"
  (interactive)
  (let ((v (if (= js2-basic-offset 2) 4 2)))
    (setq web-mode-indent-style v)
    (setq web-mode-code-indent-offset v)
    (setq web-mode-css-indent-offset v)
    (setq web-mode-markup-indent-offset v)
    (setq js2-basic-offset v)
    (message "web-mode js2-mode indent=%d" v)
    ))

(autoload 'sos "sos" "search stackoverflow" t)

;; increase and decrease font size in GUI emacs
(when (display-graphic-p)
  (global-set-key (kbd "C-=") 'text-scale-increase)
  (global-set-key (kbd "C--") 'text-scale-decrease)
  )

;; {{ which-func
(autoload 'which-function "which-func")
(autoload 'popup-tip "popup")
(defun popup-which-function ()
  (interactive)
  (let ((msg (which-function)))
    (popup-tip msg)
    (copy-yank-str msg)
    ))
;; }}

(defun latest-kill-to-clipboard ()
  (interactive)
  (copy-yank-str (current-kill 1) t))

(autoload 'vr/replace "visual-regexp")
(autoload 'vr/query-replace "visual-regexp")
;; if you use multiple-cursors, this is for you:
(autoload 'vr/mc-mark "visual-regexp")

;; @see http://www.emacswiki.org/emacs/EasyPG#toc4
;; besides, use gnupg 1.4.9 instead of 2.0
(defadvice epg--start (around advice-epg-disable-agent disable)
  "Make epg--start not able to find a gpg-agent"
  (let ((agent (getenv "GPG_AGENT_INFO")))
    (setenv "GPG_AGENT_INFO" nil)
    ad-do-it
    (setenv "GPG_AGENT_INFO" agent)))

;; {{go-mode
(require 'go-mode-load)
;; }}

;; someone mentioned that blink cursor could slow Emacs24.4
;; I couldn't care less about cursor, so turn it off explicitly
;; https://github.com/redguardtoo/emacs.d/issues/208
;; but somebody mentioned that blink cursor is needed in dark theme
;; so it should not be turned off by default
;; (blink-cursor-mode -1)

;; https://github.com/browse-kill-ring/browse-kill-ring
(require 'browse-kill-ring)
(browse-kill-ring-default-keybindings)

;; @see http://emacs.stackexchange.com/questions/3322/python-auto-indent-problem/3338#3338
(if (fboundp 'electric-indent-mode) (electric-indent-mode -1))

(provide 'init-misc)
