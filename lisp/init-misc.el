;; {{ swiper&ivy-mode
(autoload 'ivy-recentf "ivy" "" t)
(autoload 'ivy-read "ivy")
(autoload 'swiper "swiper" "" t)

(defun swiper-the-thing ()
  (interactive)
  (swiper (if (region-active-p)
              (buffer-substring-no-properties (region-beginning) (region-end))
            (thing-at-point 'symbol))))
;; }}

;; {{ shell and conf
(add-to-list 'auto-mode-alist '("\\.[^b][^a][a-zA-Z]*rc$" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.aspell\\.en\\.pws\\'" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.meta\\'" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.?muttrc\\'" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.ctags\\'" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.mailcap\\'" . conf-mode))
;; }}

;; open header file under cursor
(global-set-key (kbd "C-x C-o") 'ffap)

;; salesforce
(autoload 'apex-mode "apex-mode" nil t)
(add-to-list 'auto-mode-alist '("\\.cls\\'" . apex-mode))
(add-to-list 'auto-mode-alist '("\\.trigger\\'" . apex-mode))
;; java
(add-to-list 'auto-mode-alist '("\\.aj\\'" . java-mode))
;; makefile
(add-to-list 'auto-mode-alist '("\\.ninja$" . makefile-gmake-mode))

;; {{ support MY packages which are not included in melpa
(autoload 'wxhelp-browse-class-or-api "wxwidgets-help" "" t)
(autoload 'issue-tracker-increment-issue-id-under-cursor "issue-tracker" "" t)
(autoload 'issue-tracker-insert-issue-list "issue-tracker" "" t)
(autoload 'elpamr-create-mirror-for-installed "elpa-mirror" "" t)
(autoload 'org2nikola-export-subtree "org2nikola" "" t)
(autoload 'org2nikola-rerender-published-posts "org2nikola" "" t)
(setq org2nikola-use-verbose-metadata t) ; for nikola 7.7+
;; }}

(define-key global-map (kbd "RET") 'newline-and-indent)

;; M-x without meta
(global-set-key (kbd "C-x C-m") 'execute-extended-command)

;; {{ isearch
;; Use regex to search by default
(global-set-key (kbd "C-s") 'isearch-forward-regexp)
(global-set-key (kbd "C-r") 'isearch-backward-regexp)
(global-set-key (kbd "C-M-s") 'isearch-forward)
(global-set-key (kbd "C-M-r") 'isearch-backward)
(define-key isearch-mode-map (kbd "C-o") 'isearch-occur)
;; }}

(setq-default buffers-menu-max-size 30
              case-fold-search t
              compilation-scroll-output t
              ediff-split-window-function 'split-window-horizontally
              ediff-window-setup-function 'ediff-setup-windows-plain
              save-interprogram-paste-before-kill t
              grep-highlight-matches t
              grep-scroll-output t
              indent-tabs-mode nil
              line-spacing 0.2
              mouse-yank-at-point t
              set-mark-command-repeat-pop t
              tooltip-delay 1.5
              ;; void problems with crontabs, etc.
              ;; require-final-newline t ; bad idea, could accidentally edit others' code
              truncate-lines nil
              truncate-partial-width-windows nil
              ;; visible-bell has some issue
              ;; @see https://github.com/redguardtoo/mastering-emacs-in-one-year-guide/issues/9#issuecomment-97848938
              visible-bell nil)

;; @see http://www.emacswiki.org/emacs/SavePlace
(require 'saveplace)
(setq-default save-place t)


;; {{ find-file-in-project (ffip)
(autoload 'find-file-in-project "find-file-in-project" "" t)
(autoload 'find-file-in-project-by-selected "find-file-in-project" "" t)
(autoload 'ffip-get-project-root-directory "find-file-in-project" "" t)
(setq ffip-match-path-instead-of-filename t)

(defun neotree-project-dir ()
  "Open NeoTree using the git root."
  (interactive)
  (let ((project-dir (ffip-get-project-root-directory))
        (file-name (buffer-file-name)))
    (if project-dir
        (progn
          (neotree-dir project-dir)
          (neotree-find file-name))
      (message "Could not find git project root."))))

(defvar my-grep-extra-opts
  "--exclude-dir=.git --exclude-dir=.bzr --exclude-dir=.svn"
  "Extra grep options passed to `my-grep'")

(defun my-grep ()
  "Grep file at project root directory or current directory"
  (interactive)
  (let ((keyword (if (region-active-p)
                     (buffer-substring-no-properties (region-beginning) (region-end))
                   (read-string "Enter grep pattern: ")))
        cmd collection val 1st root)

    (let ((default-directory (setq root (or (and (fboundp 'ffip-get-project-root-directory)
                                                 (ffip-get-project-root-directory))
                                            default-directory))))
      (setq cmd (format "%s -rsn %s \"%s\" *"
                        grep-program my-grep-extra-opts keyword))
      (when (and (setq collection (split-string
                                   (shell-command-to-string cmd)
                                   "\n"
                                   t))
                 (setq val (ivy-read (format "matching \"%s\" at %s:" keyword root) collection))))
      (setq lst (split-string val ":"))
      (find-file (car lst))
      (goto-char (point-min))
      (forward-line (1- (string-to-number (cadr lst)))))))
;; }}

;; {{ groovy-mode
 (add-to-list 'auto-mode-alist '("\\.groovy\\'" . groovy-mode))
 (add-to-list 'auto-mode-alist '("\\.gradle\\'" . groovy-mode))
;; }}

;; {{ https://github.com/browse-kill-ring/browse-kill-ring
(require 'browse-kill-ring)
;; no duplicates
(setq browse-kill-ring-display-duplicates nil)
;; preview is annoying
(setq browse-kill-ring-show-preview nil)
(browse-kill-ring-default-keybindings)
;; hotkeys:
;; n/p => next/previous
;; s/r => search
;; l => filter with regex
;; g => update/refresh
;; }}

;; {{ gradle
(defun my-run-gradle-in-shell (cmd)
  (interactive "sEnter a string:")
  (let ((root-dir (locate-dominating-file default-directory
                                          "build.gradle")))
    (if root-dir
      (let ((default-directory root-dir))
        (shell-command (concat "gradle " cmd "&"))))
    ))
;; }}

;; {{ crontab
;; in shell "EDITOR='emacs -nw' crontab -e" to edit cron job
(add-to-list 'auto-mode-alist '("crontab.*\\'" . crontab-mode))
;; }}

;; cmake
(setq auto-mode-alist (append '(("CMakeLists\\.txt\\'" . cmake-mode))
                              '(("\\.cmake\\'" . cmake-mode))
                              auto-mode-alist))

(defun back-to-previous-buffer ()
  (interactive)
  (switch-to-buffer nil))

;; {{ dictionary setup
(autoload 'dictionary-new-search "dictionary" "" t nil)
(defun my-lookup-dict-org ()
  (interactive)
  (dictionary-new-search (cons (if (region-active-p)
                                   (buffer-substring-no-properties (region-beginning) (region-end))
                                 (thing-at-point 'symbol)) dictionary-default-dictionary)))

;; }}

;; {{ bookmark
;; use my own bmk if it exists
(if (file-exists-p (file-truename "~/.emacs.bmk"))
    (setq bookmark-file (file-truename "~/.emacs.bmk")))
;; }}

(defun insert-lorem ()
  (interactive)
  (insert "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Pellentesque sem mauris, aliquam vel interdum in, faucibus non libero. Asunt in anim uis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in anim id est laborum. Allamco laboris nisi ut aliquip ex ea commodo consequat."))

(defun my-gud-gdb ()
  (interactive)
  (gud-gdb (concat "gdb --fullname \"" (cppcm-get-exe-path-current-buffer) "\"")))

(defun my-overview-of-current-buffer ()
  (interactive)
  (set-selective-display (if selective-display nil 1)))

(defun lookup-doc-in-man ()
  (interactive)
  (man (concat "-k " (if (region-active-p)
       (buffer-substring-no-properties (region-beginning) (region-end))
      (thing-at-point 'symbol)))))

;; @see http://blog.binchen.org/posts/effective-code-navigation-for-web-development.html
;; don't let the cursor go into minibuffer prompt
(setq minibuffer-prompt-properties (quote (read-only t point-entered minibuffer-avoid-prompt face minibuffer-prompt)))

;; Don't echo passwords when communicating with interactive programs:
;; Github prompt is like "Password for 'https://user@github.com/':"
(setq comint-password-prompt-regexp (format "%s\\|^ *Password for .*: *$" comint-password-prompt-regexp))
(add-hook 'comint-output-filter-functions 'comint-watch-for-password-prompt)

;; {{ which-key-mode
(require 'which-key)
(setq which-key-separator ":")
(which-key-mode 1)
;; }}

(defun generic-prog-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    ;; fic-mode has performance issue on 5000 line C++, we can always use swiper instead
    ;; don't spell check double words
    (setq flyspell-check-doublon nil)
    ;; enable for all programming modes
    ;; http://emacsredux.com/blog/2013/04/21/camelcase-aware-editing/
    (subword-mode)
    (setq-default electric-pair-inhibit-predicate 'electric-pair-conservative-inhibit)
    (electric-pair-mode 1)

    ;; eldoc, show API doc in minibuffer echo area
    ;; (turn-on-eldoc-mode)
    ;; show trailing spaces in a programming mod
    (setq show-trailing-whitespace t)))

(add-hook 'prog-mode-hook 'generic-prog-mode-hook-setup)
;; some major-modes NOT inherited from prog-mode
(add-hook 'css-mode-hook 'generic-prog-mode-hook-setup)

;; {{ display long lines in truncated style (end line with $)
(defun truncate-lines-setup ()
  (toggle-truncate-lines 1))
(add-hook 'grep-mode-hook 'truncate-lines-setup)
;; (add-hook 'org-mode-hook 'truncate-lines-setup)
;; }}

;; turns on auto-fill-mode, don't use text-mode-hook because for some
;; mode (org-mode for example), this will make the exported document
;; ugly!
;; (add-hook 'markdown-mode-hook 'turn-on-auto-fill)
(add-hook 'change-log-mode-hook 'turn-on-auto-fill)
(add-hook 'cc-mode-hook 'turn-on-auto-fill)
(global-set-key (kbd "C-c q") 'auto-fill-mode)

;; some project prefer tab, so be it
;; @see http://stackoverflow.com/questions/69934/set-4-space-indent-in-emacs-in-text-mode
(setq-default tab-width 4)

(setq history-delete-duplicates t)

;;----------------------------------------------------------------------------
(fset 'yes-or-no-p 'y-or-n-p)

;; NO automatic new line when scrolling down at buffer bottom
(setq next-line-add-newlines nil)

;; @see http://stackoverflow.com/questions/4222183/emacs-how-to-jump-to-function-definition-in-el-file
(global-set-key (kbd "C-h C-f") 'find-function)

;; from RobinH, Time management
(setq display-time-24hr-format t)
(setq display-time-day-and-date t)
(display-time)

;;a no-op function to bind to if you want to set a keystroke to null
(defun void () "this is a no-op" (interactive))

(defalias 'list-buffers 'ibuffer)

;effective emacs item 7; no scrollbar, no menubar, no toolbar
(if (fboundp 'scroll-bar-mode) (scroll-bar-mode -1))
(if (fboundp 'tool-bar-mode) (tool-bar-mode -1))

(defun my-download-subtitles ()
  (interactive)
  (shell-command "periscope.py -l en *.mkv *.mp4 *.avi &"))

;; {{ @see http://emacsredux.com/blog/2013/04/21/edit-files-as-root/
(defun sudo-edit (&optional arg)
  "Edit currently visited file as root.
With a prefix ARG prompt for a file to visit.
Will also prompt for a file to visit if current
buffer is not visiting a file.
You may insert below line into ~/.authinfo.gpg to type less:
machine 127.0.0.1 login root password ****** port sudo
See \"Reusing passwords for several connections\" from INFO.
"
  (interactive "P")
  (if (or arg (not buffer-file-name))
      (find-file (concat "/sudo:root@127.0.0.1:"
                         (read-file-name "Find file(as root): ")))
    (find-alternate-file (concat "/sudo:@127.0.0.1:"
                                 buffer-file-name))))

(defadvice ido-find-file (after find-file-sudo activate)
  "Find file as root if necessary."
  (unless (and buffer-file-name
               (file-writable-p buffer-file-name))
    (find-alternate-file (concat "/sudo:root@127.0.0.1:"
                                 buffer-file-name))))
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

;; increase and decrease font size in GUI emacs
(when (display-graphic-p)
  (global-set-key (kbd "C-=") 'text-scale-increase)
  (global-set-key (kbd "C--") 'text-scale-decrease))

;; vimrc
(autoload 'vimrc-mode "vimrc-mode")
(add-to-list 'auto-mode-alist '("\\.?vim\\(rc\\)?$" . vimrc-mode))

;; {{ https://github.com/nschum/highlight-symbol.el
(autoload 'highlight-symbol "highlight-symbol" "" t)
(autoload 'highlight-symbol-next "highlight-symbol" "" t)
(autoload 'highlight-symbol-prev "highlight-symbol" "" t)
(autoload 'highlight-symbol-nav-mode "highlight-symbol" "" t)
(autoload 'highlight-symbol-query-replace "highlight-symbol" "" t)
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

(setq system-time-locale "C")

(setq imenu-max-item-length 256)

;; {{ recentf-mode
(setq recentf-keep '(file-remote-p file-readable-p))
(setq recentf-max-saved-items 2048
      recentf-exclude '("/tmp/"
                        "/ssh:"
                        "/sudo:"
                        ;; ctags
                        "/TAGS$"
                        ;; global
                        "/GTAGS$"
                        "/GRAGS$"
                        "/GPATH$"
                        ;; ~/.emacs.d/**/*.el included
                        ;; "/home/[a-z]\+/\\.[a-df-z]" ; configuration file should not be excluded
                        ))
;; }}

;; {{ popup functions
(autoload 'which-function "which-func")
(autoload 'popup-tip "popup")

(defun my-which-function ()
  ;; clean the imenu cache
  ;; @see http://stackoverflow.com/questions/13426564/how-to-force-a-rescan-in-imenu-by-a-function
  (setq imenu--index-alist nil)
  (which-function))

(defun popup-which-function ()
  (interactive)
  (let ((msg (my-which-function)))
    (popup-tip msg)
    (copy-yank-str msg)))
;; }}

;; {{ music
(defun mpc-which-song ()
  (interactive)
  (let ((msg (car (split-string (shell-command-to-string "mpc") "\n+"))))
    (message msg)
    (copy-yank-str msg)))

(defun mpc-next-prev-song (&optional prev)
  (interactive)
  (message (car (split-string (shell-command-to-string
                               (concat "mpc " (if prev "prev" "next"))) "\n+"))))
(defun lyrics()
  "Prints the lyrics for the current song"
  (interactive)
  (let ((song (shell-command-to-string "lyrics")))
    (if (equal song "")
        (message "No lyrics - Opening browser.")
      (switch-to-buffer (create-file-buffer "Lyrics"))
      (insert song)
      (goto-line 0))))
;; }}

;; @see http://www.emacswiki.org/emacs/EasyPG#toc4
;; besides, use gnupg 1.4.9 instead of 2.0
(defadvice epg--start (around advice-epg-disable-agent disable)
  "Make epg--start not able to find a gpg-agent"
  (let ((agent (getenv "GPG_AGENT_INFO")))
    (setenv "GPG_AGENT_INFO" nil)
    ad-do-it
    (setenv "GPG_AGENT_INFO" agent)))

;; https://github.com/abo-abo/ace-window
;; `M-x ace-window ENTER m` to swap window
(global-set-key (kbd "C-x o") 'ace-window)

;; {{ move focus between sub-windows
(require 'window-numbering)
(custom-set-faces '(window-numbering-face ((t (:foreground "DeepPink" :underline "DeepPink" :weight bold)))))
(window-numbering-mode 1)
;; }}

;; {{ avy, jump between texts, like easymotion in vim
;; @see http://emacsredux.com/blog/2015/07/19/ace-jump-mode-is-dead-long-live-avy/ for more tips
;; dired
(eval-after-load "dired"
  '(progn
     (define-key dired-mode-map (kbd ";") 'avy-goto-subword-1)))
;; }}

;; ANSI-escape coloring in compilation-mode
;; {{ http://stackoverflow.com/questions/13397737/ansi-coloring-in-compilation-mode
(ignore-errors
  (require 'ansi-color)
  (defun my-colorize-compilation-buffer ()
    (when (eq major-mode 'compilation-mode)
      (ansi-color-apply-on-region compilation-filter-start (point-max))))
  (add-hook 'compilation-filter-hook 'my-colorize-compilation-buffer))
;; }}

;; @see http://emacs.stackexchange.com/questions/14129/which-keyboard-shortcut-to-use-for-navigating-out-of-a-string
(defun font-face-is-similar (f1 f2)
  (let (rlt)
    ;; (message "f1=%s f2=%s" f1 f2)
    ;; in emacs-lisp-mode, the '^' from "^abde" has list of faces:
    ;;   (font-lock-negation-char-face font-lock-string-face)
    (if (listp f1) (setq f1 (nth 1 f1)))
    (if (listp f2) (setq f2 (nth 1 f2)))

    (if (eq f1 f2) (setq rlt t)
      ;; C++ comment has different font face for limit and content
      ;; f1 or f2 could be a function object because of rainbow mode
      (if (and (string-match "-comment-" (format "%s" f1)) (string-match "-comment-" (format "%s" f2)))
          (setq rlt t)))
    rlt))

;; {{ tramp setup
(add-to-list 'backup-directory-alist
             (cons tramp-file-name-regexp nil))
(setq tramp-chunksize 8192)

;; @see https://github.com/syl20bnr/spacemacs/issues/1921
;; If you tramp is hanging, you can uncomment below line.
;; (setq tramp-ssh-controlmaster-options "-o ControlMaster=auto -o ControlPath='tramp.%%C' -o ControlPersist=no")
;; }}

;; {{
(defun goto-edge-by-comparing-font-face (&optional step)
"Goto either the begin or end of string/comment/whatever.
If step is -1, go backward."
  (interactive "P")
  (let ((cf (get-text-property (point) 'face))
        (p (point))
        rlt
        found
        end)
    (unless step (setq step 1)) ;default value
    (setq end (if (> step 0) (point-max) (point-min)))
    (while (and (not found) (not (= end p)))
      (if (not (font-face-is-similar (get-text-property p 'face) cf))
          (setq found t)
        (setq p (+ p step))))
    (if found (setq rlt (- p step))
      (setq rlt p))
    ;; (message "rlt=%s found=%s" rlt found)
    (goto-char rlt)))
;; }}

(defun my-minibuffer-setup-hook ()
  ;; Use paredit in the minibuffer
  (conditionally-paredit-mode 1)
  (local-set-key (kbd "M-y") 'paste-from-x-clipboard)
  (local-set-key (kbd "C-k") 'kill-line)
  (setq gc-cons-threshold most-positive-fixnum))

(defun my-minibuffer-exit-hook ()
  ;; evil-mode also use minibuf
  (conditionally-paredit-mode -1)
  (setq gc-cons-threshold best-gc-cons-threshold))

;; @see http://bling.github.io/blog/2016/01/18/why-are-you-changing-gc-cons-threshold/
(add-hook 'minibuffer-setup-hook #'my-minibuffer-setup-hook)
(add-hook 'minibuffer-exit-hook #'my-minibuffer-exit-hook)


;; {{ string-edit-mode
(autoload 'string-edit-at-point "string-edit" "" t nil)
(defun string-edit-at-point-hook-setup ()
  (let ((major-mode-list (remove major-mode '(web-mode js2-mode js-mode css-mode emacs-lisp-mode)))
        (str (buffer-substring-no-properties (point-min) (point-max))))
    ;; (ivy-read "directories:" collection :action 'dired)
    ;; (message "original=%s" (se/find-original))
    ;; (message "major-mode-list=%s major-mode=%s" major-mode-list major-mode)
    (save-excursion
      (cond
       ((string-match-p "<[a-zA-Z]" str)
        (web-mode))
       ((string-match-p "function(\\| var \\|" str)
        (js-mode))))))
(add-hook 'string-edit-at-point-hook 'string-edit-at-point-hook-setup)
;; }}

;; Diff two regions
;; Step 1: Select a region and `M-x diff-region-tag-selected-as-a'
;; Step 2: Select another region and `M-x diff-region-compare-with-b'
;; Press "q" in evil-mode or "C-c C-c" to exit the diff output buffer
(defun diff-region-format-region-boundary (b e)
  "Make sure lines are selected and B is less than E"
  (let (tmp rlt)
    ;; swap b e, make sure b < e
    (when (> b e)
      (setq tmp b)
      (setq b e)
      (set e tmp))

    ;; select lines
    (save-excursion
      ;; Another workaround for evil-visual-line bug:
      ;; In evil-mode, if we use hotkey V or `M-x evil-visual-line` to select line,
      ;; the (line-beginning-position) of the line which is after the last selected
      ;; line is always (region-end)! Don't know why.
      (if (and (> e b)
               (save-excursion (goto-char e) (= e (line-beginning-position)))
               (boundp 'evil-state) (eq evil-state 'visual))
          (setq e (1- e)))
      (goto-char b)
      (setq b (line-beginning-position))
      (goto-char e)
      (setq e (line-end-position)))
    (setq rlt (list b e))
    rlt))

(defun diff-region-tag-selected-as-a ()
  "Select a region to compare"
  (interactive)
  (when (region-active-p)
    (let (tmp buf)
      ;; select lines
      (setq tmp (diff-region-format-region-boundary (region-beginning) (region-end)))
      (setq buf (get-buffer-create "*Diff-regionA*"))
      (save-current-buffer
        (set-buffer buf)
        (erase-buffer))
      (append-to-buffer buf (car tmp) (cadr tmp))))
  (message "Now select other region to compare and run `diff-region-compare-with-b`"))

(defun diff-region-compare-with-b ()
  "Compare current region with region selected by `diff-region-tag-selected-as-a' "
  (interactive)
  (if (region-active-p)
      (let (rlt-buf
            diff-output
            (fa (make-temp-file (expand-file-name "scor"
                                                  (or small-temporary-file-directory
                                                      temporary-file-directory))))
            (fb (make-temp-file (expand-file-name "scor"
                                                  (or small-temporary-file-directory
                                                      temporary-file-directory)))))
        ;;  save current content as file B
        (when fb
          (setq tmp (diff-region-format-region-boundary (region-beginning) (region-end)))
          (write-region (car tmp) (cadr tmp) fb))

        (when (and fa (file-exists-p fa) fb (file-exists-p fb))
          ;; save region A as file A
          (save-current-buffer
            (set-buffer (get-buffer-create "*Diff-regionA*"))
            (write-region (point-min) (point-max) fa))
          ;; diff NOW!
          ;; show the diff output
          (if (string= (setq diff-output (shell-command-to-string (format "diff -Nabur %s %s" fa fb))) "")
              ;; two regions are same
              (message "Two regions are SAME!")
            ;; show the diff
            (diff-region-open-diff-output diff-output
                                          "*Diff-region-output*")))

        ;; clean the temporary files
        (if (and fa (file-exists-p fa))
            (delete-file fa))
        (if (and fb (file-exists-p fb))
            (delete-file fb)))
    (message "Please select region at first!")))

;; cliphist.el
(setq cliphist-use-ivy t)

;; subtitles.el
(autoload 'srt-renumber-subtitles "subtitles" "" t)
(autoload 'srt-offset-subtitles "subtitles" "" t)
(autoload 'srt-mult-subtitles "subtitles" "" t)
(autoload 'srt-convert-sub-to-srt "subtitles" "" t)

;; fastdef.el
(autoload 'fastdef-insert "fastdef" nil t)
(autoload 'fastdef-insert-from-history "fastdef" nil t)

;; {{ auto-save.el
(require 'auto-save)
(auto-save-enable)
(setq auto-save-slient t)
;; }}

(provide 'init-misc)
