;; -*- coding: utf-8; lexical-binding: t; -*-

;; Without this comment emacs25 adds (package-initialize) here
;; (package-initialize)

(let* ((minver "26.1"))
  (when (version< emacs-version minver)
    (error "Emacs v%s or higher is required." minver)))

(setq user-init-file (or load-file-name (buffer-file-name)))
(setq user-emacs-directory (file-name-directory user-init-file))

(defvar my-debug nil "Enable debug mode.")

(setq *is-a-mac* (eq system-type 'darwin))
(setq *win64* (eq system-type 'windows-nt))
(setq *cygwin* (eq system-type 'cygwin) )
(setq *linux* (or (eq system-type 'gnu/linux) (eq system-type 'linux)) )
(setq *unix* (or *linux* (eq system-type 'usg-unix-v) (eq system-type 'berkeley-unix)) )
(setq *emacs27* (>= emacs-major-version 27))

;; don't GC during startup to save time
(setq gc-cons-percentage 0.6)
(setq gc-cons-threshold most-positive-fixnum)

;; {{ emergency security fix
;; https://bugs.debian.org/766397
(with-eval-after-load 'enriched
  (defun enriched-decode-display-prop (start end &optional param)
    (list start end)))
;; }}

(setq *no-memory* (cond
                   (*is-a-mac*
                    ;; @see https://discussions.apple.com/thread/1753088
                    ;; "sysctl -n hw.physmem" does not work
                    (<= (string-to-number (shell-command-to-string "sysctl -n hw.memsize"))
                        (* 4 1024 1024)))
                   (*linux* nil)
                   (t nil)))

(defconst my-emacs-d (file-name-as-directory user-emacs-directory)
  "Directory of emacs.d")

(defconst my-site-lisp-dir (concat my-emacs-d "site-lisp")
  "Directory of site-lisp")

(defconst my-lisp-dir (concat my-emacs-d "lisp")
  "Directory of lisp.")

(defun my-vc-merge-p ()
  "Use Emacs for git merge only?"
  (boundp 'startup-now))

(defun require-init (pkg &optional maybe-disabled)
  "Load PKG if MAYBE-DISABLED is nil or it's nil but start up in normal slowly."
  (when (or (not maybe-disabled) (not (my-vc-merge-p)))
    (load (file-truename (format "%s/%s" my-lisp-dir pkg)) t t)))

(defun my-add-subdirs-to-load-path (lisp-dir)
  "Add sub-directories under LISP-DIR into `load-path'."
  (let* ((default-directory lisp-dir))
    (setq load-path
          (append
           (delq nil
                 (mapcar (lambda (dir)
                           (unless (string-match-p "^\\." dir)
                             (expand-file-name dir)))
                         (directory-files my-site-lisp-dir)))
           load-path))))

;; @see https://www.reddit.com/r/emacs/comments/3kqt6e/2_easy_little_known_steps_to_speed_up_emacs_start/
;; Normally file-name-handler-alist is set to
;; (("\\`/[^/]*\\'" . tramp-completion-file-name-handler)
;; ("\\`/[^/|:][^/|]*:" . tramp-file-name-handler)
;; ("\\`/:" . file-name-non-special))
;; Which means on every .el and .elc file loaded during start up, it has to runs those regexps against the filename.
(let* ((file-name-handler-alist nil))

  (require-init 'init-autoload)
  ;; `package-initialize' takes 35% of startup time
  ;; need check https://github.com/hlissner/doom-emacs/wiki/FAQ#how-is-dooms-startup-so-fast for solution
  (require-init 'init-modeline)
  (require-init 'init-utils)
  (require-init 'init-file-type)
  (require-init 'init-elpa)

  ;; for unit test
  (when my-disable-idle-timer
    (my-add-subdirs-to-load-path (file-name-as-directory my-site-lisp-dir)))

  ;; Any file use flyspell should be initialized after init-spelling.el
  (require-init 'init-spelling t)
  (require-init 'init-ibuffer t)
  (require-init 'init-ivy)
  (require-init 'init-windows)
  (require-init 'init-javascript t)
  (require-init 'init-org t)
  (require-init 'init-css t)
  (require-init 'init-python t)
  (require-init 'init-lisp t)
  (require-init 'init-elisp t)
  (require-init 'init-yasnippet t)
  (require-init 'init-cc-mode t)
  (require-init 'init-linum-mode)
  (require-init 'init-git t)
  (require-init 'init-gtags t)
  (require-init 'init-clipboard)
  (require-init 'init-ctags t)
  (require-init 'init-bbdb t)
  (require-init 'init-gnus t)
  (require-init 'init-lua-mode t)
  (require-init 'init-workgroups2 t) ; use native API in lightweight mode
  (require-init 'init-term-mode t)
  (require-init 'init-web-mode t)
  (require-init 'init-company t)
  (require-init 'init-chinese t) ;; cannot be idle-required
  ;; need statistics of keyfreq asap
  (require-init 'init-keyfreq t)
  (require-init 'init-httpd t)

  ;; projectile costs 7% startup time

  ;; don't play with color-theme in light weight mode
  ;; color themes are already installed in `init-elpa.el'
  (require-init 'init-theme)

  ;; misc has some crucial tools I need immediately
  (require-init 'init-essential)
  ;; handy tools though not must have
  (require-init 'init-misc t)

  (require-init 'init-emacs-w3m t)
  (require-init 'init-shackle t)
  (require-init 'init-dired t)
  (require-init 'init-writting t)
  (require-init 'init-hydra) ; hotkey is required everywhere
  ;; use evil mode (vi key binding)
  (require-init 'init-evil) ; init-evil dependent on init-clipboard

  ;; ediff configuration should be last so it can override
  ;; the key bindings in previous configuration
  (require-init 'init-ediff)

  ;; @see https://github.com/hlissner/doom-emacs/wiki/FAQ
  ;; Adding directories under "site-lisp/" to `load-path' slows
  ;; down all `require' statement. So we do this at the end of startup
  ;; NO ELPA package is dependent on "site-lisp/".
  (unless my-disable-idle-timer
    (my-add-subdirs-to-load-path (file-name-as-directory my-site-lisp-dir)))

  (require-init 'init-flymake t)

  (unless (my-vc-merge-p)
    ;; @see https://www.reddit.com/r/emacs/comments/4q4ixw/how_to_forbid_emacs_to_touch_configuration_files/
    ;; See `custom-file' for details.
    (setq custom-file (expand-file-name (concat my-emacs-d "custom-set-variables.el")))
    (if (file-exists-p custom-file) (load custom-file t t))

    ;; my personal setup, other major-mode specific setup need it.
    ;; It's dependent on *.el in `my-site-lisp-dir'
    (load (expand-file-name "~/.custom.el") t nil)))


;; @see https://www.reddit.com/r/emacs/comments/55ork0/is_emacs_251_noticeably_slower_than_245_on_windows/
;; Emacs 25 does gc too frequently
;; (setq garbage-collection-messages t) ; for debug
(defun my-cleanup-gc ()
  "Clean up gc."
  (setq gc-cons-threshold  67108864) ; 64M
  (setq gc-cons-percentage 0.1) ; original value
  (garbage-collect))

(run-with-idle-timer 4 nil #'my-cleanup-gc)

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(package-selected-packages
   '(org-re-reveal lsp-mode zerodark-theme zenburn-theme zen-and-art-theme yasnippet-snippets yaml-mode writeroom-mode winum white-sand-theme which-key wgrep websocket web-mode w3m vscode-dark-plus-theme visual-regexp vimrc-mode unfill undo-fu underwater-theme ujelly-theme typescript-mode twilight-theme twilight-bright-theme twilight-anti-bright-theme toxi-theme toc-org textile-mode tao-theme tangotango-theme tango-plus-theme tango-2-theme tagedit sunny-day-theme sublime-themes subatomic256-theme subatomic-theme srcery-theme spacemacs-theme spacegray-theme soothe-theme solarized-theme soft-stone-theme soft-morning-theme soft-charcoal-theme smyx-theme simple-httpd shackle seti-theme session scss-mode scratch rvm rust-mode rjsx-mode reverse-theme request regex-tool rebecca-theme rainbow-delimiters railscasts-theme pyim-wbdict purple-haze-theme professional-theme pomodoro planet-theme phoenix-dark-pink-theme phoenix-dark-mono-theme pdf-tools paredit organic-green-theme omtose-phellack-theme oldlace-theme occidental-theme obsidian-theme nvm nov nord-theme noctilux-theme neotree naquadah-theme mustang-theme monokai-theme monochrome-theme molokai-theme moe-theme minimal-theme material-theme markdown-mode majapahit-theme magit madhat2r-theme lush-theme lua-mode light-soap-theme leuven-theme legalese keyfreq kaolin-themes jump js-doc jbeans-theme jazz-theme jade-mode ivy-hydra ir-black-theme inkpot-theme iedit htmlize heroku-theme hemisu-theme hc-zenburn-theme haml-mode gruvbox-theme gruber-darker-theme groovy-mode grandshell-theme gotham-theme gnu-elpa-keyring-update gitignore-mode gitconfig-mode git-timemachine git-link gandalf-theme fringe-helper flatui-theme flatland-theme find-file-in-project find-by-pinyin-dired farmhouse-theme fantom-theme eziam-theme expand-region exotica-theme exec-path-from-shell evil-visualstar evil-surround evil-nerd-commenter evil-matchit evil-mark-replace evil-find-char-pinyin evil-exchange evil-escape esup espresso-theme emms emmet-mode elpy elpa-mirror dracula-theme doom-themes django-theme diredfl diminish dictionary darktooth-theme darkokai-theme darkmine-theme darkburn-theme dakrone-theme cyberpunk-theme csv-mode cpputils-cmake counsel-gtags counsel-css counsel-bbdb company-statistics company-native-complete company-c-headers command-log-mode color-theme-sanityinc-tomorrow color-theme-sanityinc-solarized color-theme cmake-mode clues-theme cliphist cherry-blossom-theme busybee-theme buffer-move bubbleberry-theme birds-of-paradise-plus-theme bbdb base16-theme badwolf-theme auto-yasnippet auto-package-update atom-one-dark-theme atom-dark-theme apropospriate-theme anti-zenburn-theme amx ample-zen-theme ample-theme alect-themes afternoon-theme adoc-mode ace-window ace-pinyin)))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(default ((t (:background nil)))))
 ;;; Local Variables:
;;; no-byte-compile: t
;;; End:
(put 'erase-buffer 'disabled nil)
