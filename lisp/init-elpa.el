;;------------------------------------------------------------------------------
;; Find and load the correct package.el
;;------------------------------------------------------------------------------

;; When switching between Emacs 23 and 24, we always use the bundled package.el in Emacs 24
(let ((package-el-site-lisp-dir (expand-file-name "~/.emacs.d/site-lisp/package")))
  (when (and (file-directory-p package-el-site-lisp-dir)
             (> emacs-major-version 23))
    (message "Removing local package.el from load-path to avoid shadowing bundled version")
    (setq load-path (remove package-el-site-lisp-dir load-path))))

(require 'package)


;;------------------------------------------------------------------------------
;; Patch up annoying package.el quirks
;;------------------------------------------------------------------------------

(defadvice package-generate-autoloads (after close-autoloads (name pkg-dir) activate)
  "Stop package.el from leaving open autoload files lying around."
  (let ((path (expand-file-name (concat
                                 ;; name is string when emacs <= 24.3.1,
                                 (if (symbolp name) (symbol-name name) name)
                                 "-autoloads.el") pkg-dir)))
    (with-current-buffer (find-file-existing path)
      (kill-buffer nil))))


;;------------------------------------------------------------------------------
;; Add support to package.el for pre-filtering available packages
;;------------------------------------------------------------------------------

(defvar package-filter-function nil
  "Optional predicate function used to internally filter packages used by package.el.

The function is called with the arguments PACKAGE VERSION ARCHIVE, where
PACKAGE is a symbol, VERSION is a vector as produced by `version-to-list', and
ARCHIVE is the string name of the package archive.")

(defadvice package--add-to-archive-contents
  (around filter-packages (package archive) activate)
  "Add filtering of available packages using `package-filter-function', if non-nil."
  (when (or (null package-filter-function)
      (funcall package-filter-function
         (car package)
         (funcall (if (fboundp 'package-desc-version)
          'package--ac-desc-version
        'package-desc-vers)
            (cdr package))
         archive))
    ad-do-it))
;;------------------------------------------------------------------------------
;; On-demand installation of packages
;;------------------------------------------------------------------------------

(defun require-package (package &optional min-version no-refresh)
  "Ask elpa to install given PACKAGE."
  (if (package-installed-p package min-version)
      t
    (if (or (assoc package package-archive-contents) no-refresh)
        (package-install package)
      (progn
        (package-refresh-contents)
        (require-package package min-version t)))))


;;------------------------------------------------------------------------------
;; Standard package repositories
;;------------------------------------------------------------------------------

;; We include the org repository for completeness, but don't use it.
;; Lock org-mode temporarily:
;; (add-to-list 'package-archives '("org" . "http://orgmode.org/elpa/"))


;; well, melpa does not bother supporting emacs23 any more, but cl-lib is still required
;; TODO: in half a year, I will remove gnu elpa because emacs 24.3 is the minimum version
(setq package-archives '(("melpa" . "http://melpa.org/packages/")
                         ("melpa-stable" . "http://stable.melpa.org/packages/")
                         ;; uncomment below line if you need use GNU ELPA
                         ;; ("gnu" . "http://elpa.gnu.org/packages/")
                         ))

;; Un-comment below line if you download zip file
;; from https://github.com/redguardtoo/myelpa/archive/master.zip
;; and extract its content into ~/myelpa/
;; (setq package-archives '(("myelpa" . "~/projs/myelpa")))

;; this is just hack to work around *emacs23* issues
(if (not *emacs24*) (add-to-list 'package-archives '("localelpa" . "~/.emacs.d/localelpa")))

;; Or Un-comment below line if you prefer installing package from https://github.com/redguardtoo/myelpa/ directly
;; (setq package-archives '(("myelpa" . "https://raw.github.com/redguardtoo/myelpa/master/")))

;; List of VISIBLE packages from melpa-unstable (http://melpa.org)
;; Feel free to add more packages!
(defvar melpa-include-packages
  '(bbdb
    json-rpc
    kv
    color-theme
    wgrep
    robe
    inf-ruby
    dsvn
    move-text
    findr
    mwe-log-commands
    dired-details
    yaml-mode
    noflet
    db
    creole
    web
    elnode
    sass-mode
    idomenu
    pointback
    buffer-move
    regex-tool
    csharp-mode
    switch-window
    sr-speedbar
    quack
    iedit
    legalese
    htmlize
    scratch
    mic-paren
    session
    crontab-mode
    bookmark+
    flymake-lua
    multi-term
    dired+
    inflections
    dropdown-list
    lua-mode
    pomodoro
    helm
    auto-compile
    packed
    gitconfig-mode
    project-local-variables
    org-fstree
    textile-mode
    w3m
    fakir
    erlang
    company-c-headers
    company-anaconda
    anaconda-mode
    ;; make all the color theme packages available
    afternoon-theme
    ahungry-theme
    alect-themes
    ample-theme
    ample-zen-theme
    anti-zenburn-theme
    atom-dark-theme
    badger-theme
    base16-theme
    basic-theme
    birds-of-paradise-plus-theme
    bliss-theme
    boron-theme
    bubbleberry-theme
    busybee-theme
    calmer-forest-theme
    cherry-blossom-theme
    clues-theme
    colonoscopy-theme
    color-theme-approximate
    color-theme-buffer-local
    color-theme-sanityinc-solarized
    color-theme-sanityinc-tomorrow
    color-theme-solarized
    colorsarenice-theme
    cyberpunk-theme
    expand-region
    dakrone-theme
    darcula-theme
    dark-krystal-theme
    darkburn-theme
    darkmine-theme
    display-theme
    distinguished-theme
    django-theme
    espresso-theme
    firebelly-theme
    firecode-theme
    flatland-black-theme
    flatland-theme
    flatui-theme
    gandalf-theme
    gotham-theme
    grandshell-theme
    gruber-darker-theme
    gruvbox-theme
    hc-zenburn-theme
    helm-themes
    hemisu-theme
    heroku-theme)
  "Don't install any Melpa packages except these packages")

;; Don't take Melpa versions of certain packages
(setq package-filter-function
      (lambda (package version archive)
        (and
         (not (memq package '(eieio)))
         (or (and (string-equal archive "melpa") (memq package melpa-include-packages))
             (not (string-equal archive "melpa")))
         )))

;; un-comment below code if you prefer use all the package on melpa (unstable) without limitation
;; (setq package-filter-function nil)

;;------------------------------------------------------------------------------
;; Fire up package.el and ensure the following packages are installed.
;;------------------------------------------------------------------------------

(package-initialize)

(require-package 'cl-lib '(0 0 5) nil)
(require-package 'kv '(0 0 19) nil)
(require-package 'dash '(2 5 0) nil)
; color-theme 6.6.1 in elpa is buggy
(require-package 'color-theme)
(require-package 'auto-compile)
(require-package 'ace-jump-mode)
(require-package 'expand-region nil) ;; use latest version if possible
(require-package 'fringe-helper)
(require-package 'haskell-mode '(13 7 0) nil)
(require-package 'magit '(1 2 0) nil)
(require-package 'git-commit-mode)
(require-package 'gitignore-mode)
(require-package 'gitconfig-mode)
(require-package 'yagist)
(require-package 'wgrep)
(require-package 'lua-mode)
(require-package 'project-local-variables)
(require-package 'robe)
(require-package 'inf-ruby '(2 3 0) nil)
(require-package 'yaml-mode)
(require-package 'paredit)
(require-package 'erlang '(20120612 0 0) nil)
(require-package 'findr)
(if *emacs24* (require-package 'jump '(2 3 0) nil))
(require-package 'writeroom-mode)
(require-package 'haml-mode)
(require-package 'sass-mode)
(require-package 'scss-mode)
(require-package 'markdown-mode)
(require-package 'dired+)
(require-package 'maxframe)
(require-package 'org-fstree)
(require-package 'htmlize)
(require-package 'diminish)
(require-package 'scratch)
(require-package 'mic-paren)
(require-package 'rainbow-delimiters)
(require-package 'textile-mode)
(when *emacs24*
  (require-package 'coffee-mode)
  (require-package 'flymake-coffee))
(require-package 'crontab-mode)
(require-package 'dsvn)
(require-package 'git-timemachine)
(require-package 'exec-path-from-shell)
(require-package 'flymake-css)
(require-package 'flymake-jslint)
(require-package 'flymake-python-pyflakes)
(require-package 'flymake-ruby)
(require-package 'flymake-sass)
(require-package 'hl-sexp)
(require-package 'ibuffer-vc)
(require-package 'less-css-mode)
(require-package 'move-text)
(require-package 'mwe-log-commands)
(require-package 'page-break-lines)
(require-package 'pointback)
(require-package 'regex-tool)
;; I don't use multiple-cursors, but js2-refactor requires it
(require-package 'multiple-cursors)
(require-package 'rinari)
(require-package 'ruby-compilation)
(require-package 'csharp-mode)
(require-package 'emmet-mode)
(require-package 'session)
;; (require-package 'tidy)
(require-package 'unfill)
(require-package 'w3m)
(require-package 'idomenu)
(if *emacs24* (require-package 'ggtags))
(require-package 'buffer-move)
(require-package 'switch-window)
(require-package 'cpputils-cmake '(0 4 22) nil)
(require-package 'flyspell-lazy)
(require-package 'bbdb '(20130421 1145 0) nil)
(require-package 'iedit)
(require-package 'pomodoro '(20130114 1543 0) nil)
(require-package 'flymake-lua)
(require-package 'dropdown-list)
(if *emacs24* (require-package 'yasnippet '(0 9 0 1) nil))
;; rvm-open-gem to get gem's code
(require-package 'rvm)
;; C-x r l to list bookmarks
(require-package 'bookmark+)
(require-package 'multi-term)
(require-package 'json-mode)
(if (and (>= emacs-major-version 24) (>= emacs-minor-version 1))
    (require-package 'js2-mode '(20140114 0 0) nil))
(require-package 'tagedit)
(require-package 'sr-speedbar)
;; company-mode drop emacs 23 support
(when (>= emacs-major-version 24)
  (require-package 'company '(0 8 5) nil)
  (require-package 'company-c-headers))
(require-package 'legalese)
(require-package 'string-edit)
(require-package 'dired-details)
(require-package 'ag)
(require-package 'fakir)
(require-package 'f)
(require-package 'elnode) ;; elnode dependent on f
(when *emacs24*
  (require-package 'git-gutter '(0 71) nil)
  (require-package 'flx-ido)
  (require-package 'projectile)
  (require-package 'anaconda-mode)
  (require-package 'company-anaconda))

(require-package 'quack) ;; for scheme

;; (require-package 'command-frequency)

(provide 'init-elpa)
