(require 'package)

;;------------------------------------------------------------------------------
;; Cutomized setup, you can tweak repository and package freely
;;------------------------------------------------------------------------------

;; List of VISIBLE packages from melpa-unstable (http://melpa.org)
;; Feel free to add more packages!
(defvar melpa-include-packages
  '(bbdb
    color-theme
    wgrep
    robe
    groovy-mode
    inf-ruby
    simple-httpd
    dsvn
    move-text
    string-edit ; looks magnars don't update stable tag frequently
    findr
    mwe-log-commands
    yaml-mode
    noflet
    db
    creole
    web
    sass-mode
    idomenu
    pointback
    buffer-move
    regex-tool
    quack
    legalese
    htmlize
    scratch
    session
    crontab-mode
    bookmark+
    flymake-lua
    multi-term
    dired+
    inflections
    dropdown-list
    lua-mode
    tidy
    pomodoro
    auto-compile
    packed
    gitconfig-mode
    textile-mode
    w3m
    erlang
    company-c-headers
    ;; make all the color theme packages available
    afternoon-theme
    define-word
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
    workgroups2
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
    pythonic
    flatland-theme
    flatui-theme
    gandalf-theme
    gotham-theme
    grandshell-theme
    gruber-darker-theme
    gruvbox-theme
    hc-zenburn-theme
    hemisu-theme
    heroku-theme)
  "Don't install any Melpa packages except these packages")

;; We include the org repository for completeness, but don't use it.
;; Lock org-mode temporarily:
;; (add-to-list 'package-archives '("org" . "http://orgmode.org/elpa/"))
(setq package-archives '(("melpa" . "http://melpa.org/packages/")
                         ("melpa-stable" . "http://stable.melpa.org/packages/")
                         ;; uncomment below line if you need use GNU ELPA
                         ;; ("gnu" . "http://elpa.gnu.org/packages/")
                         ))

;; Un-comment below line if your extract https://github.com/redguardtoo/myelpa/archive/master.zip into ~/myelpa/
;; (setq package-archives '(("myelpa" . "~/myelpa")))

;; Or Un-comment below line if you install package from https://github.com/redguardtoo/myelpa/
;; (setq package-archives '(("myelpa" . "https://raw.github.com/redguardtoo/myelpa/master/")))



;;------------------------------------------------------------------------------
;; Internal implementation, newbies should NOT touch code below this line!
;;------------------------------------------------------------------------------

;; Patch up annoying package.el quirks
(defadvice package-generate-autoloads (after close-autoloads (name pkg-dir) activate)
  "Stop package.el from leaving open autoload files lying around."
  (let ((path (expand-file-name (concat
                                 ;; name is string when emacs <= 24.3.1,
                                 (if (symbolp name) (symbol-name name) name)
                                 "-autoloads.el") pkg-dir)))
    (with-current-buffer (find-file-existing path)
      (kill-buffer nil))))

;; Add support to package.el for pre-filtering available packages
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

;; On-demand installation of packages
(defun require-package (package &optional min-version no-refresh)
  "Ask elpa to install given PACKAGE."
  (if (package-installed-p package min-version)
      t
    (if (or (assoc package package-archive-contents) no-refresh)
        (package-install package)
      (progn
        (package-refresh-contents)
        (require-package package min-version t)))))

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

(require-package 'dash)
; color-theme 6.6.1 in elpa is buggy
(require-package 'color-theme)
(require-package 'auto-compile)
(require-package 'avy)
(require-package 'expand-region) ;; I prefer stable version
(require-package 'fringe-helper)
(require-package 'haskell-mode)
(require-package 'gitignore-mode)
(require-package 'gitconfig-mode)
(require-package 'yagist)
(require-package 'wgrep)
(require-package 'lua-mode)
(require-package 'robe)
(require-package 'inf-ruby)
(require-package 'workgroups2)
(require-package 'yaml-mode)
(require-package 'paredit)
(require-package 'erlang)
(require-package 'findr)
(require-package 'jump)
(require-package 'nvm)
(require-package 'writeroom-mode)
(require-package 'haml-mode)
(require-package 'sass-mode)
(require-package 'scss-mode)
(require-package 'markdown-mode)
(require-package 'dired+)
(require-package 'link)
(require-package 'connection)
(require-package 'dictionary) ; dictionary requires 'link and 'connection
(require-package 'htmlize)
(require-package 'diminish)
(require-package 'scratch)
(require-package 'rainbow-delimiters)
(require-package 'textile-mode)
(require-package 'coffee-mode)
(require-package 'flymake-coffee)
(require-package 'crontab-mode)
(require-package 'dsvn)
(require-package 'git-timemachine)
(require-package 'exec-path-from-shell)
(require-package 'flymake-css)
(require-package 'flymake-jslint)
(require-package 'flymake-ruby)
(require-package 'flymake-sass)
(require-package 'swiper)
(require-package 'find-file-in-project)
(require-package 'elpy)
(require-package 'hl-sexp)
(require-package 'ibuffer-vc)
(require-package 'less-css-mode)
(require-package 'move-text)
(require-package 'mwe-log-commands)
(require-package 'page-break-lines)
(require-package 'pointback)
(require-package 'regex-tool)
(require-package 'rinari)
(require-package 'groovy-mode)
(require-package 'ruby-compilation)
(require-package 'emmet-mode)
(require-package 'session)
(require-package 'tidy)
(require-package 'unfill)
(require-package 'w3m)
(require-package 'idomenu)
(require-package 'ggtags)
(require-package 'buffer-move)
(require-package 'ace-window)
(require-package 'cmake-mode)
(require-package 'cpputils-cmake)
(require-package 'flyspell-lazy)
(require-package 'bbdb)
(require-package 'pomodoro)
(require-package 'flymake-lua)
(require-package 'dropdown-list)
;; rvm-open-gem to get gem's code
(require-package 'rvm)
;; C-x r l to list bookmarks
(require-package 'bookmark+)
(require-package 'multi-term)
(require-package 'js2-mode)
(require-package 's)
;; js2-refactor requires js2, dash, s, multiple-cursors, yasnippet
;; I don't use multiple-cursors, but js2-refactor requires it
(require-package 'multiple-cursors)
(require-package 'tagedit)
(require-package 'git-link)
(require-package 'cliphist)
(require-package 'yasnippet)
(require-package 'company)
(require-package 'company-c-headers)
(require-package 'legalese)
(require-package 'string-edit)
(require-package 'guide-key)
(require-package 'simple-httpd)
(require-package 'git-messenger)
(require-package 'git-gutter)
(require-package 'flx-ido)
(require-package 'neotree)
(require-package 'define-word)
(require-package 'quack) ;; for scheme
(require-package 'hydra)

(provide 'init-elpa)
