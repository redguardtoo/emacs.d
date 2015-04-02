(define-key global-map (kbd "RET") 'newline-and-indent)

;; M-x without meta
(global-set-key (kbd "C-x C-m") 'execute-extended-command)
(global-set-key (kbd "C-.") 'set-mark-command)
(global-set-key (kbd "C-x C-.") 'pop-global-mark)

;; C#
(add-to-list 'auto-mode-alist '("\\.cs$" . csharp-mode))

;; cmake
(setq auto-mode-alist (append '(("CMakeLists\\.txt\\'" . cmake-mode))
                              '(("\\.cmake\\'" . cmake-mode))
                              auto-mode-alist))

;; @see http://blog.binchen.org/posts/effective-code-navigation-for-web-development.html
;; don't let the cursor go into minibuffer prompt
(setq minibuffer-prompt-properties (quote (read-only t point-entered minibuffer-avoid-prompt face minibuffer-prompt)))

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

;; some project prefer tab, so be it
;; @see http://stackoverflow.com/questions/69934/set-4-space-indent-in-emacs-in-text-mode
(setq-default tab-width 4)

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


(eval-after-load 'speedbar
  '(if (load "mwheel" t)
       ;; Enable wheelmouse support by default
       (cond (window-system
              (mwheel-install)))))

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

(autoload 'highlight-symbol-at-point "highlight-symbol" "" t)

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

;; @see http://www.emacswiki.org/emacs/EasyPG#toc4
;; besides, use gnupg 1.4.9 instead of 2.0
(defadvice epg--start (around advice-epg-disable-agent disable)
  "Make epg--start not able to find a gpg-agent"
  (let ((agent (getenv "GPG_AGENT_INFO")))
    (setenv "GPG_AGENT_INFO" nil)
    ad-do-it
    (setenv "GPG_AGENT_INFO" agent)))

;; @see http://emacs.stackexchange.com/questions/3322/python-auto-indent-problem/3338#3338
(if (fboundp 'electric-indent-mode) (electric-indent-mode -1))

;; http://tapoueh.org/emacs/switch-window.html
(global-set-key (kbd "C-x o") 'switch-window)

;; move window
(require 'window-numbering)
(custom-set-faces '(window-numbering-face ((t (:foreground "DeepPink" :underline "DeepPink" :weight bold)))))
(window-numbering-mode 1)

(provide 'init-misc)
