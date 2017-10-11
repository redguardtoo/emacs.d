;; {{ shell and conf
(add-to-list 'auto-mode-alist '("\\.[^b][^a][a-zA-Z]*rc$" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.aspell\\.en\\.pws\\'" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.editorconfig$" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.meta\\'" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.?muttrc\\'" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.mailcap\\'" . conf-mode))
;; }}


(add-to-list 'auto-mode-alist '("TAGS\\'" . text-mode))
(add-to-list 'auto-mode-alist '("\\.ctags\\'" . text-mode))

;; {{ auto-yasnippet
;; Use C-q instead tab to complete snippet
;; - `aya-create' at first, input ~ to mark the thing next
;; - `aya-expand' to expand snippet
;; - `aya-open-line' to finish
(global-set-key (kbd "C-q") #'aya-open-line)
;; }}

;; {{ ace-link
(ace-link-setup-default)
(global-set-key (kbd "M-o") 'ace-link)
;; }}

;; open header file under cursor
(global-set-key (kbd "C-x C-o") 'ffap)

;; java
(add-to-list 'auto-mode-alist '("\\.aj\\'" . java-mode))
;; makefile
(add-to-list 'auto-mode-alist '("\\.ninja$" . makefile-gmake-mode))

;; {{ support MY packages which are not included in melpa
(setq org2nikola-use-verbose-metadata t) ; for nikola 7.7+
;; }}

(define-key global-map (kbd "RET") 'newline-and-indent)

;; {{ isearch
;; Use regex to search by default
(global-set-key (kbd "C-M-s") 'isearch-forward-regexp)
(global-set-key (kbd "C-M-r") 'isearch-backward-regexp)
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
              line-spacing 0
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
(defun my-git-versions ()
  (let* ((git-cmd (concat "git --no-pager log --date=short --pretty=format:'%h|%ad|%s|%an' "
                          buffer-file-name)))
    (nconc (split-string (shell-command-to-string "git branch --no-color --all") "\n" t)
           (split-string (shell-command-to-string git-cmd) "\n" t))))

(defun my-git-diff()
  "Run 'git diff version'."
  (let* ((default-directory (locate-dominating-file default-directory ".git"))
         (line (ivy-read "diff current file:" (my-git-versions)))
         (version (replace-regexp-in-string "^ *\\*? *" "" (car (split-string line "|" t)))))
    (shell-command-to-string (format "git --no-pager diff %s" version))))


(defun my-git-diff-current-file ()
  "Run 'git diff version:current-file current-file'."
  (let* ((default-directory (locate-dominating-file default-directory ".git"))
         (line (ivy-read "diff current file:" (my-git-versions))))
    (shell-command-to-string (format "git --no-pager diff %s:%s %s"
                                     (replace-regexp-in-string "^ *\\*? *" "" (car (split-string line "|" t)))
                                     (file-relative-name buffer-file-name default-directory)
                                     buffer-file-name))))

(setq ffip-match-path-instead-of-filename t)
;; I only use git
(setq ffip-diff-backends '(my-git-diff-current-file
                           my-git-diff
                           ;; `git log -p' current file
                           ("git diff --cached" . "cd $(git rev-parse --show-toplevel) && git diff --cached")
                           ("git log -p" . (shell-command-to-string (format "cd $(git rev-parse --show-toplevel) && git --no-pager log --date=short -p '%s'"
                                                                            (buffer-file-name))))
                           ("git log -Sstring -p" . (shell-command-to-string (format "cd $(git rev-parse --show-toplevel) && git --no-pager log --date=short -S'%s' -p"
                                                            (read-string "Git search string:"))))
                           ("diff from `kill-ring'" . (car kill-ring))))

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
;; }}

;; {{ groovy-mode
 (add-to-list 'auto-mode-alist '("\\.groovy\\'" . groovy-mode))
 (add-to-list 'auto-mode-alist '("\\.gradle\\'" . groovy-mode))
;; }}

;; {{ https://github.com/browse-kill-ring/browse-kill-ring
(require 'browse-kill-ring)
;; no duplicates
(setq browse-kill-ring-display-style 'one-line
      browse-kill-ring-display-duplicates nil
      ;; preview is annoying
      browse-kill-ring-show-preview nil)
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

;; cmake
(setq auto-mode-alist (append '(("CMakeLists\\.txt\\'" . cmake-mode))
                              '(("\\.cmake\\'" . cmake-mode))
                              auto-mode-alist))

(defun back-to-previous-buffer ()
  (interactive)
  (switch-to-buffer nil))

;; {{ dictionary setup
(defun my-lookup-dict-org ()
  (interactive)
  (dictionary-new-search (cons (my-use-selected-string-or-ask "Input word for dict.org:")
                               dictionary-default-dictionary)))
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
  (man (concat "-k " (my-use-selected-string-or-ask ""))))

;; @see http://blog.binchen.org/posts/effective-code-navigation-for-web-development.html
;; don't let the cursor go into minibuffer prompt
(setq minibuffer-prompt-properties (quote (read-only t point-entered minibuffer-avoid-prompt face minibuffer-prompt)))

;; Don't echo passwords when communicating with interactive programs:
;; Github prompt is like "Password for 'https://user@github.com/':"
(setq comint-password-prompt-regexp (format "%s\\|^ *Password for .*: *$" comint-password-prompt-regexp))
(add-hook 'comint-output-filter-functions 'comint-watch-for-password-prompt)

;; {{ which-key-mode
(require 'which-key)
(setq which-key-allow-imprecise-window-fit t) ; performance
(setq which-key-separator ":")
(which-key-mode 1)
;; }}


;; smex or counsel-M-x?
(defvar my-use-smex nil
  "Use `smex' instead of `counsel-M-x' when press M-x.")
(defun my-M-x ()
  (interactive)
  (cond
    (my-use-smex
      (smex))
    ((fboundp 'counsel-M-x)
     ;; `counsel-M-x' will use `smex' to remember history
     (counsel-M-x))
    ((fboundp 'smex)
     (smex))
    (t
      (execute-extended-command))))
(global-set-key (kbd "M-x") 'my-M-x)
(global-set-key (kbd "C-x C-m") 'my-M-x)

(defun compilation-finish-hide-buffer-on-success (buf str)
  "Could be reused by other major-mode after compilation."
  (if (string-match "exited abnormally" str)
      ;;there were errors
      (message "compilation errors, press C-x ` to visit")
    ;;no errors, make the compilation window go away in 0.5 seconds
    (when (and (buffer-name buf)
               (string-match "*compilation*" (buffer-name buf)))
      ;; @see http://emacswiki.org/emacs/ModeCompile#toc2
      (bury-buffer "*compilation*")
      (winner-undo)
      (message "NO COMPILATION ERRORS!"))))

(defun generic-prog-mode-hook-setup ()
  ;; turn off `linum-mode' when there are more than 5000 lines
  (if (buffer-too-big-p) (linum-mode -1))

  (unless (is-buffer-file-temp)

    ;; @see http://xugx2007.blogspot.com.au/2007/06/benjamin-rutts-emacs-c-development-tips.html
    (setq compilation-window-height 8)
    (setq compilation-finish-functions
          '(compilation-finish-hide-buffer-on-success))

    ;; fic-mode has performance issue on 5000 line C++, we can always use swiper instead
    ;; don't spell check double words
    (setq flyspell-check-doublon nil)
    ;; enable for all programming modes
    ;; http://emacsredux.com/blog/2013/04/21/camelcase-aware-editing/
    (unless (derived-mode-p 'js2-mode)
      (subword-mode 1))

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

;; {{ time format
;; If you want to customize time format, read documantation of `format-time-string'
;; and customize `display-time-format'.
;; (setq display-time-format "%a %b %e")

;; from RobinH, Time management
(setq display-time-24hr-format t) ; the date in modeline is English too, magic!
(setq display-time-day-and-date t)
(display-time) ; show date in modeline
;; }}

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
  (if (and (not (and buffer-file-name
                     (file-writable-p buffer-file-name)))
           ;; sudo edit only physical file
           buffer-file-name
           ;; sudo edit only /etc/**/*
           (string-match-p "^/etc/" buffer-file-name))
      (find-alternate-file (concat "/sudo:root@127.0.0.1:"
                                   buffer-file-name))))
;; }}

;; edit confluence wiki
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

;; vimrc
(add-to-list 'auto-mode-alist '("\\.?vim\\(rc\\)?$" . vimrc-mode))

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
                        "recentf$"
                        "company-statistics-cache\\.el$"
                        ;; ctags
                        "/TAGS$"
                        ;; global
                        "/GTAGS$"
                        "/GRAGS$"
                        "/GPATH$"
                        ;; binary
                        "\\.mkv$"
                        "\\.mp[34]$"
                        "\\.avi$"
                        "\\.pdf$"
                        "\\.docx?$"
                        "\\.xlsx?$"
                        ;; sub-titles
                        "\\.sub$"
                        "\\.srt$"
                        "\\.ass$"
                        ;; ~/.emacs.d/**/*.el included
                        ;; "/home/[a-z]\+/\\.[a-df-z]" ; configuration file should not be excluded
                        ))
;; }}

;; {{ popup functions
(defun my-which-file ()
  "Return current file name for Yasnippets."
  (if (buffer-file-name) (format "%s:" (file-name-nondirectory (buffer-file-name)))
    ""))

(defun my-which-function ()
  "Return current function name."
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

(ace-pinyin-global-mode +1)

;; {{ avy, jump between texts, like easymotion in vim
;; @see http://emacsredux.com/blog/2015/07/19/ace-jump-mode-is-dead-long-live-avy/ for more tips
;; dired
(eval-after-load "dired"
  '(progn
     (define-key dired-mode-map (kbd ";") 'avy-goto-subword-1)))
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
  (local-set-key (kbd "M-y") 'paste-from-x-clipboard)
  (local-set-key (kbd "C-k") 'kill-line)
  (setq gc-cons-threshold most-positive-fixnum))

(defun my-minibuffer-exit-hook ()
  ;; evil-mode also use minibuf
  (setq gc-cons-threshold best-gc-cons-threshold))

;; @see http://bling.github.io/blog/2016/01/18/why-are-you-changing-gc-cons-threshold/
(add-hook 'minibuffer-setup-hook #'my-minibuffer-setup-hook)
(add-hook 'minibuffer-exit-hook #'my-minibuffer-exit-hook)

;; {{ string-edit-mode
(defun string-edit-at-point-hook-setup ()
  (let ((major-mode-list (remove major-mode '(web-mode js2-mode js-mode css-mode emacs-lisp-mode)))
        (str (my-buffer-str)))
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

;; {{ Diff two regions
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
  "Select a region to compare."
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
  (message "Now select other region to compare and run `diff-region-compare-with-b'"))

(defun diff-region-compare-with-b ()
  "Compare current region with region selected by `diff-region-tag-selected-as-a'.
If no region is selected. You will be asked to use `kill-ring' or clipboard instead.
`simpleclip' need be installed to read clipboard."
  (interactive)
  (let* (rlt-buf
         diff-output
         ;; file A
         (fa (make-temp-file (expand-file-name "scor"
                                               (or small-temporary-file-directory
                                                   temporary-file-directory))))
         ;; file B
         (fb (make-temp-file (expand-file-name "scor"
                                               (or small-temporary-file-directory
                                                   temporary-file-directory)))))
    (when (and fa (file-exists-p fa) fb (file-exists-p fb))
      (cond
       ((region-active-p)
        ;; text from selected region
        (setq tmp (diff-region-format-region-boundary (region-beginning) (region-end)))
        (write-region (car tmp) (cadr tmp) fb))
       (t
        ;; text from `kill-ring' or clipboard
        (unless (featurep 'ido) (require 'ido))
        (let* ((choice (ido-completing-read "Since no region selected, compare text in:"
                                            '("kill-ring" "clipboard")))
               (txt (cond
                     ((string= choice "kill-ring")
                      (car kill-ring))
                     ((string= choice "clipboard")
                      (unless (featurep 'simpleclip) (require 'simpleclip))
                      (my-gclip)))))
          (with-temp-file fb
            (insert txt)))))
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
                                      "*Diff-region-output*"))
      ;; clean the temporary files
      (if (and fa (file-exists-p fa))
          (delete-file fa))
      (if (and fb (file-exists-p fb))
          (delete-file fb)))))
;; }}

;; {{ cliphist.el
(setq cliphist-use-ivy t)
(defun my-select-cliphist-item (num str)
  (my-pclip str))
(setq cliphist-select-item-callback 'my-select-cliphist-item)
;; }}

(defun extract-list-from-package-json ()
  "Extract package list from package.json."
  (interactive)
  (let* ((str (my-use-selected-string-or-ask "")))
    (message "my-select-cliphist-item called => %s" str)
    (setq str (replace-regexp-in-string ":.*$\\|\"" "" str))
    ;; join lines
    (setq str (replace-regexp-in-string "[\r\n \t]+" " " str))
    (copy-yank-str str)
    (message "%s => clipboard & yank ring" str)))

(defun my-insert-absolute-path()
  "Relative path to full path."
  (interactive)
  (let* ((str (my-use-selected-string-or-ask "Input relative path:"))
         (path (file-truename str)))
    (copy-yank-str path)
    (message "%s => clipboard & yank ring" path)))

(defun my-insert-relative-path()
  "Full path to relative path."
  (interactive)
  (let* ((str (my-use-selected-string-or-ask "Input absolute path:"))
         (path (file-relative-name str)))
    (copy-yank-str path)
    (message "%s => clipboard & yank ring" path)))

;; indention management
(defun my-toggle-indentation ()
  (interactive)
  (setq indent-tabs-mode (not indent-tabs-mode))
  (message "indent-tabs-mode=%s" indent-tabs-mode))

;; {{ auto-save.el
(require 'auto-save)
(auto-save-enable)
(setq auto-save-slient t)
;; }}

;; {{ csv
(add-auto-mode 'csv-mode "\\.[Cc][Ss][Vv]\\'")
(setq csv-separators '("," ";" "|" " "))
;; }}

;; {{ regular expression tools
(defun my-create-regex-from-kill-ring (&optional n)
  "Create extended regex from first N items of `kill-ring'."
  (interactive "p")
  (when (and kill-ring (> (length kill-ring) 0))
    (if (> n (length kill-ring))
        (setq n (length kill-ring)))
    (let* ((rlt (mapconcat 'identity (subseq kill-ring 0 n) "|")))
      (setq rlt (replace-regexp-in-string "(" "\\\\(" rlt))
      (copy-yank-str rlt)
      (message (format "%s => kill-ring&clipboard" rlt)))))
;; }}


(defun my-get-total-hours ()
  (interactive)
  (let* ((str (if (region-active-p) (my-selected-str)
                (my-buffer-str)))
         (total-hours 0)
         (lines (split-string str "\n")))
    (dolist (l lines)
      (if (string-match " \\([0-9][0-9.]*\\)h[ \t]*$" l)
          (setq total-hours (+ total-hours (string-to-number (match-string 1 l))))))
    (message "total-hours=%s" total-hours)))

;; {{ emmet (auto-complete html tags)
;; @see https://github.com/rooney/zencoding for original tutorial
;; @see https://github.com/smihica/emmet for new tutorial
;; C-j or C-return to expand the line
(add-hook 'html-mode-hook 'emmet-mode)
(add-hook 'sgml-mode-hook 'emmet-mode)
(add-hook 'web-mode-hook 'emmet-mode)
(add-hook 'css-mode-hook  'emmet-mode)
(add-hook 'rjsx-mode-hook  'emmet-mode)
;; }}

(autoload 'verilog-mode "verilog-mode" "Verilog mode" t )
(add-to-list 'auto-mode-alist '("\\.[ds]?vh?\\'" . verilog-mode))

;; {{ xterm
(defun run-after-make-frame-hooks (frame)
  (select-frame frame)
  (unless window-system
    ;; Mouse in a terminal (Use shift to paste with middle button)
    (xterm-mouse-mode 1)))
(add-hook 'after-make-frame-functions 'run-after-make-frame-hooks)
;; }}

;; flymake
(setq flymake-gui-warnings-enabled nil)

;; {{ check attachments
(defun my-message-current-line-cited-p ()
  "Indicate whether the line at point is a cited line."
  (save-match-data
    (string-match (concat "^" message-cite-prefix-regexp)
                  (buffer-substring (line-beginning-position) (line-end-position)))))

(defun my-message-says-attachment-p ()
  "Return t if the message suggests there can be an attachment."
  (save-excursion
    (goto-char (point-min))
    (save-match-data
      (let (search-result)
        (while
            (and (setq search-result (re-search-forward "\\(attach\\|pdf\\|file\\|screen ?shot\\)" nil t))
                 (my-message-current-line-cited-p)))
        search-result))))

(defun my-message-has-attachment-p ()
  "Return t if the message has an attachment."
  (save-excursion
    (goto-char (point-min))
    (save-match-data
      (re-search-forward "<#part" nil t))))

(defun my-message-pre-send-check-attachment ()
  (when (and (my-message-says-attachment-p)
             (not (my-message-has-attachment-p)))
    (unless
        (y-or-n-p "The message suggests that you may want to attach something, but no attachment is found. Send anyway?")
      (error "It seems that an attachment is needed, but none was found. Aborting sending."))))
(add-hook 'message-send-hook 'my-message-pre-send-check-attachment)

;; }}

;; @see https://stackoverflow.com/questions/3417438/closing-all-other-buffers-in-emacs
(defun kill-all-but-current-buffer ()
  (interactive)
    (mapc 'kill-buffer (cdr (buffer-list (current-buffer)))))

(defun minibuffer-inactive-mode-hook-setup ()
  ;; make `try-expand-dabbrev' from `hippie-expand' work in mini-buffer
  ;; @see `he-dabbrev-beg', so we need re-define syntax for '/'
  (set-syntax-table (let* ((table (make-syntax-table)))
                      (modify-syntax-entry ?/ "." table)
                      table)))
(add-hook 'minibuffer-inactive-mode-hook 'minibuffer-inactive-mode-hook-setup)

;; {{ dumb-jump
(setq dumb-jump-selector 'ivy)
(dumb-jump-mode)
;; }}

;; {{ vc-msg
(defun vc-msg-hook-setup (vcs-type commit-info)
  ;; copy commit id to clipboard
  (my-pclip (plist-get commit-info :id)))
(add-hook 'vc-msg-hook 'vc-msg-hook-setup)

(defun vc-msg-show-code-setup ()
  ;; use `ffip-diff-mode' from package find-file-in-project instead of `diff-mode'
  (unless (featurep 'find-file-in-project)
    (require 'find-file-in-project))
  (ffip-diff-mode))

  (add-hook 'vc-msg-show-code-hook 'vc-msg-show-code-setup)
;; }}

;; {{ eacl - emacs auto complete line(s)
(global-set-key (kbd "C-x C-l") 'eacl-complete-line)
(global-set-key (kbd "C-x ;") 'eacl-complete-statement)
(global-set-key (kbd "C-x C-]") 'eacl-complete-snippet)
(global-set-key (kbd "C-x C-t") 'eacl-complete-tag)
;; }}

;; {{ wgrep and rgrep, inspired by http://oremacs.com/2015/01/27/my-refactoring-workflow/
(eval-after-load 'grep
  '(define-key grep-mode-map
     (kbd "C-x C-q") 'wgrep-change-to-wgrep-mode))
(eval-after-load 'wgrep
  '(define-key grep-mode-map
     (kbd "C-c C-c") 'wgrep-finish-edit))
;; }}

;; {{
(require 'typewriter-mode)
(defun toggle-typewriter ()
  "Turn on/off typewriter."
  (interactive)
  (if (bound-and-true-p typewriter-mode)
      (typewriter-mode -1)
    (typewriter-mode 1)))
;; }}

;; @see https://github.com/szermatt/emacs-bash-completion
(bash-completion-setup)

(provide 'init-misc)
