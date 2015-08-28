(define-key global-map (kbd "RET") 'newline-and-indent)

;; M-x without meta
(global-set-key (kbd "C-x C-m") 'execute-extended-command)
(global-set-key (kbd "C-.") 'set-mark-command)
(global-set-key (kbd "C-x C-.") 'pop-global-mark)

;; C#
(add-to-list 'auto-mode-alist '("\\.cs$" . csharp-mode))

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
              ;; require-final-newline t ; bad idea, could accidently edit others' code
              truncate-lines nil
              truncate-partial-width-windows nil
              ;; visible-bell has some issue
              ;; @see https://github.com/redguardtoo/mastering-emacs-in-one-year-guide/issues/9#issuecomment-97848938
              visible-bell nil)

;; @see http://www.emacswiki.org/emacs/SavePlace
(require 'saveplace)
(setq-default save-place t)


;; {{ find-file-in-project (ffip)
(autoload 'ivy-read "ivy")
(autoload 'find-file-in-project "find-file-in-project" "" t)
(autoload 'find-file-in-project-by-selected "find-file-in-project" "" t)
(autoload 'ffip-get-project-root-directory "find-file-in-project" "" t)

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

(defun my-vc-git-grep ()
  (interactive)
  (let ((re (if (region-active-p)
                (buffer-substring-no-properties (region-beginning) (region-end))
              (read-string "Grep pattern: ")))
        (root (ffip-get-project-root-directory)))
    (if root (vc-git-grep re "*" root))
    ))
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
  (let ((old-dir default-directory)
        (root-dir (locate-dominating-file default-directory
                                          "build.gradle")))
    (message "root-dir=%s cmd=%s" root-dir cmd)
    (when root-dir
      (cd root-dir)
      (shell-command (concat "gradle " cmd "&"))
      (cd old-dir))))
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
  (man (concat "-k " (thing-at-point 'symbol))))

;; {{ swiper
(autoload 'swiper "swiper" "" t)
(defun swiper-the-thing ()
  (interactive)
  (swiper (if (region-active-p)
              (buffer-substring-no-properties (region-beginning) (region-end))
            (thing-at-point 'symbol))))
;; }}

;; @see http://blog.binchen.org/posts/effective-code-navigation-for-web-development.html
;; don't let the cursor go into minibuffer prompt
(setq minibuffer-prompt-properties (quote (read-only t point-entered minibuffer-avoid-prompt face minibuffer-prompt)))

;;Don't echo passwords when communicating with interactive programs:
(add-hook 'comint-output-filter-functions 'comint-watch-for-password-prompt)

;; {{ guide-key-mode
(require 'guide-key)
(setq guide-key/guide-key-sequence
      '("C-x v" ; VCS commands
        "C-c"
        ",a"
        ",b"
        ",c"
        ",d"
        ",e"
        ",f"
        ",g"
        ",h"
        ",i"
        ",j"
        ",k"
        ",l"
        ",m"
        ",n"
        ",o"
        ",p"
        ",q"
        ",r"
        ",s"
        ",t"
        ",u"
        ",v"
        ",w"
        ",x"
        ",y"
        ",z"))
(guide-key-mode 1)  ; Enable guide-key-mode
(setq guide-key/recursive-key-sequence-flag t)
(setq guide-key/idle-delay 0.5)
;; }}

;; {{expand-region.el
;; if emacs-nox, use C-@, else, use C-2;
(if window-system
  (progn
    (define-key global-map (kbd "C-2") 'er/expand-region)
    (define-key global-map (kbd "C-M-2") 'er/contract-region)
    )
  (define-key global-map (kbd "C-@") 'er/expand-region)
  (define-key global-map (kbd "C-M-@") 'er/contract-region))
;; }}

(defun generic-prog-mode-hook-setup ()
  (unless (is-buffer-file-temp)
	;; highlight FIXME/BUG/TODO in comment
	(require 'fic-mode)
	(fic-mode 1)
	;; enable for all programming modes
	;; http://emacsredux.com/blog/2013/04/21/camelcase-aware-editing/
	(subword-mode)
	(electric-pair-mode 1)
	;; eldoc, show API doc in minibuffer echo area
	(turn-on-eldoc-mode)
	;; show trailing spaces in a programming mod
	(setq show-trailing-whitespace t)
	))

(add-hook 'prog-mode-hook 'generic-prog-mode-hook-setup)

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


;; {{ imenu
(setq imenu-max-item-length 128)
(setq imenu-max-item-length 64)
;; }}

;; {{ recentf-mode
(setq recentf-keep '(file-remote-p file-readable-p))
(setq recentf-max-saved-items 1000
      recentf-exclude '("/tmp/"
                        "/ssh:"
                        "/sudo:"
                        "/home/[a-z]\+/\\."))
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
;; emacs key binding, copied from avy website
(global-set-key (kbd "C-:") 'avy-goto-char)
;; evil, my favorite
(eval-after-load "evil"
  '(progn
     ;; press "d " to delete to the word
     (define-key evil-motion-state-map (kbd "SPC") #'avy-goto-subword-1)
     (define-key evil-normal-state-map (kbd "SPC") 'avy-goto-subword-1)))
;; dired
(eval-after-load "dired"
  '(progn
     (define-key dired-mode-map (kbd "SPC") 'avy-goto-subword-1)))
;; }}

;; {{ @see http://emacs.stackexchange.com/questions/14129/which-keyboard-shortcut-to-use-for-navigating-out-of-a-string
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
(provide 'init-misc)
