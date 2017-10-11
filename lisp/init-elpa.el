(require 'package)

;; Set it to `t' to use safer HTTPS to download packages
(defvar melpa-use-https-repo nil
  "By default, HTTP is used to download packages.
But you may use safer HTTPS instead.")

;; List of VISIBLE packages from melpa-unstable (http://melpa.org)
;; Feel free to add more packages!
(defvar melpa-include-packages
  '(ace-mc
    bbdb
    dumb-jump
    color-theme
    js-doc
    ;; {{ since stable v0.9.1 released, we go back to stable version
    ;; ivy
    ;; counsel
    ;; swiper
    ;; }}
    wgrep
    robe
    groovy-mode
    inf-ruby
    ;; company ; I won't wait another 2 years for stable
    simple-httpd
    dsvn
    move-text
    string-edit ; looks magnars don't update stable tag frequently
    findr
    mwe-log-commands
    yaml-mode
    counsel-gtags ; the stable version is never released
    noflet
    db
    creole
    web
    idomenu
    buffer-move
    regex-tool
    quack
    legalese
    htmlize
    scratch
    session
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
    workgroups2
    company-c-headers)
  "Don't install any Melpa packages except these packages")

;; We include the org repository for completeness, but don't use it.
;; Lock org-mode temporarily:
(setq package-archives
      '(;; uncomment below line if you need use GNU ELPA
        ;; ("gnu" . "https://elpa.gnu.org/packages/")
        ;; ("org" . "http://orgmode.org/elpa/") ; latest org-mode
        ("localelpa" . "~/.emacs.d/localelpa/")
        ;; ("my-js2-mode" . "https://raw.githubusercontent.com/redguardtoo/js2-mode/release/") ; github has some issue
        ("melpa" . "https://melpa.org/packages/")
        ("melpa-stable" . "https://stable.melpa.org/packages/")))

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
  (let* ((path (expand-file-name (concat
                                  ;; name is string when emacs <= 24.3.1,
                                  (if (symbolp name) (symbol-name name) name)
                                  "-autoloads.el") pkg-dir)))
    (with-current-buffer (find-file-existing path)
      (kill-buffer nil))))

(defun package-filter-function (package version archive)
  "Optional predicate function used to internally filter packages used by package.el.

  The function is called with the arguments PACKAGE VERSION ARCHIVE, where
  PACKAGE is a symbol, VERSION is a vector as produced by `version-to-list', and
  ARCHIVE is the string name of the package archive."
  (let* (rlt)
    (cond
      ((string= archive "melpa-stable")
       (setq rlt t)
       ;; don's install `request v0.0.3' which drop suppport of Emacs 24.3
       (if (string= package "request") (setq rlt nil)))
      ((string= archive "melpa")
       (cond
         ;; a few exceptions from unstable melpa
         ((or (memq package melpa-include-packages)
              ;; install all color themes
              (string-match (format "%s" package) "-theme"))
          (setq rlt t))
         (t
           ;; I don't trust melpa which is too unstable
           (setq rlt nil))))
      (t
        ;; other third party repositories I trust
        (setq rlt t)))
    rlt))

(defadvice package--add-to-archive-contents
  (around filter-packages (package archive) activate)
  "Add filtering of available packages using `package-filter-function'."
  (if (package-filter-function (car package)
                               (funcall (if (fboundp 'package-desc-version)
                                            'package--ac-desc-version
                                          'package-desc-vers)
                                        (cdr package))
                               archive)
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

;;------------------------------------------------------------------------------
;; Fire up package.el and ensure the following packages are installed.
;;------------------------------------------------------------------------------

(package-initialize)

(require-package 'async)
(require-package 'dash) ; required by string-edit
; color-theme 6.6.1 in elpa is buggy
(require-package 'color-theme)
(require-package 'auto-compile)
(require-package 'smex)
(require-package 'avy)
(require-package 'auto-yasnippet)
(require-package 'ace-link)
(require-package 'expand-region) ; I prefer stable version
(require-package 'fringe-helper)
(require-package 'haskell-mode)
(require-package 'gitignore-mode)
(require-package 'gitconfig-mode)
(unless *emacs24old* (require-package 'gist))
(require-package 'wgrep)
(require-package 'request)
(require-package 'lua-mode)
(unless *emacs24old* (require-package 'robe))
(require-package 'inf-ruby)
(require-package 'workgroups2)
(require-package 'yaml-mode)
(require-package 'paredit)
(require-package 'erlang)
(require-package 'findr)
(require-package 'pinyinlib)
(require-package 'find-by-pinyin-dired)
(require-package 'jump)
(require-package 'nvm)
(require-package 'writeroom-mode)
(require-package 'haml-mode)
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
(require-package 'dsvn)
(require-package 'git-timemachine)
(require-package 'exec-path-from-shell)
(require-package 'flymake-css)
(require-package 'flymake-jslint)
(require-package 'flymake-ruby)
(require-package 'ivy)
(require-package 'swiper)
(require-package 'counsel) ; counsel => swiper => ivy
(require-package 'find-file-in-project)
(require-package 'counsel-bbdb)
(require-package 'hl-sexp)
(require-package 'ibuffer-vc)
(require-package 'less-css-mode)
(require-package 'move-text)
(require-package 'mwe-log-commands)
(require-package 'page-break-lines)
(require-package 'regex-tool)
(require-package 'groovy-mode)
(require-package 'ruby-compilation)
(require-package 'emmet-mode)
(require-package 'session)
(require-package 'tidy)
(require-package 'unfill)
(require-package 'w3m)
(require-package 'idomenu)
(require-package 'counsel-gtags)
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
(require-package 'js-doc)
(require-package 'js2-mode)
(unless *emacs24old*
  (require-package 'rjsx-mode))
(require-package 's)
;; js2-refactor requires js2, dash, s, multiple-cursors, yasnippet
;; I don't use multiple-cursors, but js2-refactor requires it
(require-package 'multiple-cursors)
(require-package 'ace-mc)
(require-package 'tagedit)
(require-package 'git-link)
(require-package 'cliphist)
(require-package 'yasnippet)
(require-package 'company)
(require-package 'company-c-headers)
(require-package 'elpy)
(require-package 'legalese)
(require-package 'simple-httpd)
;; (require-package 'git-gutter) ; use my patched version
(require-package 'flx-ido)
(require-package 'neotree)
(require-package 'quack) ; for scheme
(require-package 'hydra)
(require-package 'ivy-hydra) ; @see https://oremacs.com/2015/07/23/ivy-multiaction/
(require-package 'pyim)
(require-package 'web-mode)
(require-package 'dumb-jump)
(require-package 'emms)
(require-package 'package-lint) ; lint package before submit it to MELPA
(require-package 'iedit)
(require-package 'ace-pinyin)
(require-package 'org-jira) ; @see https://github.com/ahungry/org-jira
(require-package 'bash-completion)

(provide 'init-elpa)
