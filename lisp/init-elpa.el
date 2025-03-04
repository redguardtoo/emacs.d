;; -*- coding: utf-8; lexical-binding: t; -*-

(defun my-initialize-package ()
  "Package loading optimization.  No need to activate all the packages so early."
  ;; @see https://www.gnu.org/software/emacs/news/NEWS.27.1
  ;; ** Installed packages are now activated *before* loading the init file.
  ;; As a result of this change, it is no longer necessary to call
  ;; `package-initialize' in your init file.

  ;; Previously, a call to `package-initialize' was automatically inserted
  ;; into the init file when Emacs was started.  This call can now safely
  ;; be removed.  Alternatively, if you want to ensure that your init file
  ;; is still compatible with earlier versions of Emacs, change it to:

  ;; However, if your init file changes the values of `package-load-list'
  ;; or `package-user-dir', or sets `package-enable-at-startup' to nil then
  ;; it won't work right without some adjustment:
  ;; - You can move that code to the early init file (see above), so those
  ;;   settings apply before Emacs tries to activate the packages.
  ;; - You can use the new `package-quickstart' so activation of packages
  ;;   does not need to pay attention to `package-load-list' or
  ;;   `package-user-dir' any more.
  ;; "package-quickstart.el" converts path in `load-path' into
  ;; os dependent path, make it impossible to share same emacs.d between
  ;; Windows and Cygwin.
  (unless (or *win64* *cygwin*)
    ;; you need run `M-x package-quickstart-refresh' at least once
    ;; to generate file "package-quickstart.el'.
    ;; It contains the `autoload' statements for all packages.
    (setq package-quickstart t))

  ;; esup need call `package-initialize'
  ;; @see https://github.com/jschaf/esup/issues/84
  (when (or (featurep 'esup-child)
            (fboundp 'profile-dotemacs)
            (daemonp)
            my-lightweight-mode-p
            noninteractive)
    (package-initialize)))

(my-initialize-package)

;; List of visible packages from melpa-unstable (http://melpa.org).
;; Please add the package name into `melpa-include-packages'
;; if it's not visible after  `list-packages'.
(defvar melpa-include-packages
  '(ace-window ; latest stable is released on year 2014
    ace-pinyin
    pos-tip
    racket-mode
    auto-package-update
    web-mode
    kv
    helpful ; @see https://github.com/Wilfred/helpful/pull/283, need unstable version
    esxml ; nov is dependent on latest esxml
    nov
    bbdb
    esup ; Emacs start up profiler
    native-complete
    company-native-complete
    js2-mode ; need new features
    git-timemachine ; stable version is broken when git rename file
    highlight-symbol
    undo-fu
    ob-sagemath
    command-log-mode
    evil ; @see https://github.com/emacs-evil/evil/commit/19cc5f8eef8bfffdec8082b604c7129782acb332
    ;; lsp-mode ; stable version has performance issue, but unstable version sends too many warnings
    vimrc-mode
    rjsx-mode ; fixed the indent issue in jsx
    package-lint ; for melpa pull request only
    auto-yasnippet
    typescript-mode ; the stable version lacks important feature (highlight function names)
    evil-exchange
    evil-find-char-pinyin
    ;; {{ dependencies of stable realgud are too old
    load-relative
    loc-changes
    test-simple
    ;; }}
    iedit
    undo-tree
    js-doc
    ;; {{ since stable v0.13.0 released, we go back to stable version
    ;; ivy
    ;; counsel
    ;; swiper
    ;; }}
    wgrep
    ;; {{ themes in melpa unstable
    ample-theme
    molokai-theme
    spacemacs-theme
    leuven-theme
    elpy ; use latest elpy since Python package API changes
    sublime-themes
    pyim-wbdict
    tangotango-theme
    ujelly-theme
    afternoon-theme
    organic-green-theme
    inkpot-theme
    flatui-theme
    hc-zenburn-theme
    naquadah-theme
    seti-theme
    spacegray-theme
    jazz-theme
    espresso-theme
    phoenix-dark-pink-theme
    tango-plus-theme
    twilight-theme
    minimal-theme
    noctilux-theme
    soothe-theme
    heroku-theme
    hemisu-theme
    pulseaudio-control
    badger-theme
    distinguished-theme
    tao-theme
    tablist ; required by pdf-tools
    pdf-tools ; @see https://github.com/vedang/pdf-tools/issues/102
    ;; }}
    groovy-mode
    company ; I won't wait another 2 years for stable
    simple-httpd
    findr
    mwe-log-commands
    vterm
    noflet
    db
    creole
    web
    buffer-move
    regex-tool
    legalese
    htmlize
    scratch
    session
    inflections
    lua-mode
    pomodoro
    packed
    keyfreq
    gitconfig-mode
    textile-mode
    w3m
    workgroups2
    zoutline
    company-c-headers
    graphql-mode
    company-statistics)
  "Packages to install from melpa-unstable.")

(defvar melpa-stable-banned-packages nil
  "Banned packages from melpa-stable.")

;; I don't use any packages from GNU ELPA because I want to minimize
;; dependency on 3rd party web site.
(setq package-archives
      '(
        ("gnu" . "https://elpa.gnu.org/packages/")
        ("melpa" . "https://melpa.org/packages/")
        ("melpa-stable" . "https://stable.melpa.org/packages/")

        ;; Use either 163 or tsinghua mirror repository when official melpa
        ;; is slow or shutdown.

        ;; ;; {{ Option 1: 163 mirror repository:
        ;; ("gnu" . "https://mirrors.163.com/elpa/gnu/")
        ;; ("melpa" . "https://mirrors.163.com/elpa/melpa/")
        ;; ("melpa-stable" . "https://mirrors.163.com/elpa/stable-melpa/")
        ;; ;; }}

        ;; ;; {{ Option 2: tsinghua mirror repository
        ;; ;; @see https://mirror.tuna.tsinghua.edu.cn/help/elpa/ on usage:
        ;; ("gnu"   . "http://mirrors.tuna.tsinghua.edu.cn/elpa/gnu/")
        ;; ("melpa" . "http://mirrors.tuna.tsinghua.edu.cn/elpa/melpa/")
        ;; ("melpa-stable" . "http://mirrors.tuna.tsinghua.edu.cn/elpa/stable-melpa/")
        ;; }}
        ))

(defvar my-ask-elpa-mirror t)
(when (and (not noninteractive) ; no popup in batch mode
           my-ask-elpa-mirror
           (not (file-exists-p (file-truename (concat my-emacs-d "elpa"))))
           (yes-or-no-p "Switch to faster package repositories in China temporarily?
You still need modify `package-archives' in \"init-elpa.el\" to PERMANENTLY use this ELPA mirror."))
  (setq package-archives
        '(("melpa" . "https://mirrors.163.com/elpa/melpa/")
          ("melpa-stable" . "https://mirrors.163.com/elpa/stable-melpa/"))))

;; Un-comment below line if you follow "Install stable version in easiest way"
;; (setq package-archives '(("myelpa" . "~/myelpa/")))

(defun my-package-generate-autoloads-hack (pkg-desc pkg-dir)
  "Stop package.el from leaving open autoload files lying around."
  (let* ((path (expand-file-name (concat
                                  ;; pkg-desc is string in emacs 24.3.1,
                                  (if (symbolp pkg-desc) (symbol-name pkg-desc) pkg-desc)
                                  "-autoloads.el")
                                 pkg-dir)))
    (with-current-buffer (find-file-existing path)
      (kill-buffer nil))))
(advice-add 'package-generate-autoloads :after #'my-package-generate-autoloads-hack)

(defun my-package--add-to-archive-contents-hack (orig-func &rest args)
  "Some packages should be hidden."
  (let* ((package (nth 0 args))
         (archive (nth 1 args))
         (pkg-name (car package))
         (version (package--ac-desc-version (cdr package)))
         (add-to-p t))
    (cond
     ((string= archive "melpa-stable")
      (setq add-to-p
            (not (memq pkg-name melpa-stable-banned-packages))))

     ;; We still need use some unstable packages
     ((string= archive "melpa")
      (setq add-to-p
            (or (member pkg-name melpa-include-packages)
                ;; color themes are welcomed
                (string-match "-theme" (format "%s" pkg-name))))))

    (when my-debug
      (message "package name=%s version=%s package=%s" pkg-name version package))

    (when add-to-p
      ;; The package is visible through package manager
      (apply orig-func args))))
(advice-add 'package--add-to-archive-contents :around #'my-package--add-to-archive-contents-hack)

;; On-demand installation of packages
(defun require-package (package &optional min-version no-refresh)
  "Ask elpa to install given PACKAGE with MIN-VERSION.
If NO-REFRESH is nil, `package-refresh-contents' is called."
  (my-ensure 'package)
  (unless (package-installed-p package min-version)
    (unless (or (assoc package package-archive-contents) no-refresh)
      (message "Missing package: %s" package)
      (package-refresh-contents))
    (package-install package)))

;;------------------------------------------------------------------------------
;; Fire up package.el and ensure the following packages are installed.
;;------------------------------------------------------------------------------

(require-package 'compat)
(require-package 'async)
; color-theme 6.6.1 in elpa is buggy
(require-package 'amx)
(require-package 'avy)
(require-package 'popup) ; some old package need it
(require-package 'auto-yasnippet)
(require-package 'csv-mode)
(require-package 'expand-region) ; I prefer stable version
(require-package 'fringe-helper)
(require-package 'wgrep)
(require-package 'request)
(require-package 'lua-mode)
(require-package 'yaml-mode)
(require-package 'paredit)
(require-package 'findr)
(require-package 'diredfl) ; font lock for `dired-mode'
(require-package 'pinyinlib)
(require-package 'find-by-pinyin-dired)
(require-package 'jump)
(require-package 'nvm)
(require-package 'writeroom-mode)
(require-package 'haml-mode)
(require-package 'markdown-mode)
(unless *emacs28*
  (require-package 'link)
  (require-package 'connection)
  ;; dictionary requires 'link and 'connection
  (require-package 'dictionary))
(require-package 'htmlize) ; prefer stable version
(require-package 'jade-mode)
(require-package 'diminish)
(require-package 'scratch)
(require-package 'rainbow-delimiters)
(require-package 'textile-mode)
(require-package 'git-timemachine)
(require-package 'exec-path-from-shell)
(require-package 'ivy)
(require-package 'swiper)
(require-package 'counsel) ; counsel => swiper => ivy
(require-package 'find-file-in-project)
(require-package 'counsel-bbdb)
(require-package 'command-log-mode)
(require-package 'regex-tool)
(require-package 'groovy-mode)
(require-package 'emmet-mode)
(require-package 'winum)
(require-package 'session)
(require-package 'unfill)
(require-package 'w3m) ; better than eww for reading web page
(require-package 'counsel-gtags)
(require-package 'eww-lnum)
(require-package 'buffer-move)
(require-package 'ace-window)
(require-package 'cmake-mode)
(require-package 'cpputils-cmake)
(require-package 'bbdb)
(require-package 'pomodoro)
;; rvm-open-gem to get gem's code
(require-package 'rvm)
;; C-x r l to list bookmarks
(require-package 'js-doc)
(require-package 'js2-mode)
(require-package 'rjsx-mode)
(require-package 'tagedit)
(require-package 'git-link)
(require-package 'cliphist)
(require-package 'yasnippet)
(require-package 'yasnippet-snippets)
(require-package 'company)
(require-package 'native-complete)
(require-package 'company-native-complete)
(require-package 'company-c-headers)
(require-package 'company-statistics)
(require-package 'lsp-mode)
(require-package 'elpy)
(require-package 'legalese)
(require-package 'simple-httpd)
;; (require-package 'git-gutter) ; use my patched version
(require-package 'neotree)
(require-package 'hydra)
(require-package 'ivy-hydra) ; @see https://oremacs.com/2015/07/23/ivy-multiaction/
(require-package 'web-mode)
(require-package 'iedit)
(require-package 'websocket) ; for debug debugging of browsers
(require-package 'undo-tree)
(require-package 'evil)
(require-package 'evil-escape)
(require-package 'evil-exchange)
(require-package 'evil-find-char-pinyin)
(require-package 'evil-mark-replace)
(require-package 'evil-matchit)
(require-package 'evil-nerd-commenter)
(require-package 'evil-surround)
(require-package 'evil-visualstar)
(require-package 'undo-fu)
(require-package 'counsel-css)
(require-package 'auto-package-update)
(require-package 'keyfreq)
(require-package 'adoc-mode) ; asciidoc files
(require-package 'shackle)
(require-package 'toc-org)
(require-package 'elpa-mirror)
;; {{ @see https://pawelbx.github.io/emacs-theme-gallery/
(require-package 'color-theme)
(require-package 'visual-regexp) ;; Press "M-x vr-*"
(require-package 'vimrc-mode)
(require-package 'nov) ; read epub
(require-package 'rust-mode)
;; (require-package 'langtool) ; my own patched version is better
(require-package 'typescript-mode)
;; run "M-x pdf-tool-install" at debian and open pdf in GUI Emacs
(require-package 'pdf-tools)
(require-package 'pyim)
(require-package 'pyim-wbdict) ; someone may use wubi IME, not me
(require-package 'pyim-basedict)
(require-package 'esup)

;; {{ Fixed expiring GNU ELPA keys
;; GNU ELPA GPG key will expire on Sep-2019. So we need install this package to
;; update key or else users can't install packages from GNU ELPA.
;; @see https://www.reddit.com/r/emacs/comments/bn6k1y/updating_gnu_elpa_keys/
;; BTW, this setup uses MELPA only. So GNU ELPA GPG key is not used.
(require-package 'gnu-elpa-keyring-update)
;; }}

;; org => ppt
(require-package 'org-re-reveal)

(require-package 'git-modes)
(require-package 'ace-pinyin)
(require-package 'which-key)
(require-package 'highlight-symbol)
(require-package 'wc-mode)
(require-package 'helpful)
(require-package 'qrencode)
(require-package 'ws-butler)
(require-package 'sage-shell-mode)
(require-package 'graphql-mode)
(require-package 'ob-sagemath)
(require-package 'pulseaudio-control)
(require-package 'vterm)
(require-package 'dockerfile-mode)
(when *emacs28* (require-package 'ellama))

;; magit sometime use packages which not released yet
;; so we place it at the end to make sure other packages are installed first
(require-package 'magit)

(defvar my-color-themes
  '(afternoon-theme
    alect-themes
    ample-theme
    ample-zen-theme
    anti-zenburn-theme
    apropospriate-theme
    atom-dark-theme
    atom-one-dark-theme
    badwolf-theme
    base16-theme
    birds-of-paradise-plus-theme
    bubbleberry-theme
    busybee-theme
    cherry-blossom-theme
    clues-theme
    color-theme-sanityinc-solarized
    color-theme-sanityinc-tomorrow
    cyberpunk-theme
    dakrone-theme
    darkmine-theme
    darkokai-theme
    darktooth-theme
    django-theme
    doom-themes
    dracula-theme
    espresso-theme
    exotica-theme
    eziam-themes
    fantom-theme
    farmhouse-themes
    flatland-theme
    flatui-theme
    gandalf-theme
    gotham-theme
    grandshell-theme
    gruber-darker-theme
    gruvbox-theme
    hc-zenburn-theme
    hemisu-theme
    heroku-theme
    inkpot-theme
    ir-black-theme
    jazz-theme
    jbeans-theme
    kaolin-themes
    leuven-theme
    light-soap-theme
    lush-theme
    madhat2r-theme
    material-theme
    minimal-theme
    modus-themes
    moe-theme
    molokai-theme
    monochrome-theme
    monokai-theme
    mustang-theme
    naquadah-theme
    noctilux-theme
    nord-theme
    obsidian-theme
    occidental-theme
    oldlace-theme
    omtose-phellack-themes
    organic-green-theme
    phoenix-dark-mono-theme
    phoenix-dark-pink-theme
    planet-theme
    professional-theme
    purple-haze-theme
    railscasts-theme
    rebecca-theme
    reverse-theme
    seti-theme
    smyx-theme
    soft-charcoal-theme
    soft-morning-theme
    soft-stone-theme
    solarized-theme
    soothe-theme
    spacegray-theme
    spacemacs-theme
    srcery-theme
    subatomic-theme
    subatomic256-theme
    sublime-themes
    sunny-day-theme
    tango-2-theme
    tango-plus-theme
    tangotango-theme
    tao-theme
    toxi-theme
    twilight-anti-bright-theme
    twilight-bright-theme
    twilight-theme
    ujelly-theme
    underwater-theme
    vscode-dark-plus-theme
    white-sand-theme
    zen-and-art-theme
    zenburn-theme
    zerodark-theme)
  "Color themes for this setup.")


;; speed up CI
(unless my-disable-idle-timer
  ;; most popular 100 themes
  (dolist (theme my-color-themes)
    (require-package theme)))

;; }}

;; {{ trivial packages which has extra dependency
(require-package 'emms)
;; }}

;; kill buffer without my confirmation
(setq kill-buffer-query-functions (delq 'process-kill-buffer-query-function kill-buffer-query-functions))

(provide 'init-elpa)
;;; init-elpa.el ends here
