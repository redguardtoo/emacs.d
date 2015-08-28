;; @see https://bitbucket.org/lyro/evil/issue/360/possible-evil-search-symbol-forward
;; evil 1.0.8 search word instead of symbol
(setq evil-symbol-word-search t)
;; load undo-tree and ert
(add-to-list 'load-path "~/.emacs.d/site-lisp/evil/lib")

;; @see https://bitbucket.org/lyro/evil/issue/511/let-certain-minor-modes-key-bindings
(eval-after-load 'git-timemachine
  '(progn
     (evil-make-overriding-map git-timemachine-mode-map 'normal)
     ;; force update evil keymaps after git-timemachine-mode loaded
     (add-hook 'git-timemachine-mode-hook #'evil-normalize-keymaps)))

(require 'evil)

;; @see https://bitbucket.org/lyro/evil/issue/342/evil-default-cursor-setting-should-default
;; cursor is alway black because of evil
;; here is the workaround
(setq evil-default-cursor t)

;; enable evil-mode
(evil-mode 1)

;; {{@see https://github.com/timcharper/evil-surround
(require 'evil-surround)
(global-evil-surround-mode 1)
;; }}

(require 'evil-mark-replace)

;; {{ define my own text objects, works on evil v1.0.9 using older method
;; @see http://stackoverflow.com/questions/18102004/emacs-evil-mode-how-to-create-a-new-text-object-to-select-words-with-any-non-sp
(defmacro define-and-bind-text-object (key start-regex end-regex)
  (let ((inner-name (make-symbol "inner-name"))
        (outer-name (make-symbol "outer-name")))
    `(progn
       (evil-define-text-object ,inner-name (count &optional beg end type)
         (evil-select-paren ,start-regex ,end-regex beg end type count nil))
       (evil-define-text-object ,outer-name (count &optional beg end type)
         (evil-select-paren ,start-regex ,end-regex beg end type count t))
       (define-key evil-inner-text-objects-map ,key (quote ,inner-name))
       (define-key evil-outer-text-objects-map ,key (quote ,outer-name)))))

;; between dollar signs:
(define-and-bind-text-object "$" "\\$" "\\$")
;; between pipe characters:
(define-and-bind-text-object "|" "|" "|")
;; trimmed line
(define-and-bind-text-object "l" "^ *" " *$")
;; angular template
(define-and-bind-text-object "r" "\{\{" "\}\}")
;; }}

;; {{ nearby file path as text object,
;;      - "vif" to select only basename
;;      - "vaf" to select the full path
;;
;;  example: "/hello/world" "/test/back.exe"
;;               "C:hello\\hello\\world\\test.exe" "D:blah\\hello\\world\\base.exe"
;;
;; tweak evil-filepath-is-nonname to re-define a path
(defun evil-filepath-is-separator-char (ch)
  "Check ascii table"
  (let (rlt)
    (if (or (= ch 47)
            (= ch 92))
        (setq rlt t))
    rlt))

(defun evil-filepath-not-path-char (ch)
  "Check ascii table for charctater "
  (let (rlt)
    (if (or (and (<= 0 ch) (<= ch 32))
            (= ch 34) ; double quotes
            (= ch 39) ; single quote
            (= ch 40) ; (
            (= ch 41) ; )
            (= ch 60) ; <
            (= ch 62) ; >
            (= ch 91) ; [
            (= ch 93) ; ]
            (= ch 96) ; `
            (= ch 123) ; {
            (= ch 125) ; }
            (= 127 ch))
        (setq rlt t))
    rlt))

(defun evil-filepath-char-not-placed-at-end-of-path (ch)
  (or (= 44 ch) ; ,
      (= 46 ch) ; .
      ))

(defun evil-filepath-calculate-path (b e)
  (let (rlt f)
    (when (and b e)
      (setq b (+ 1 b))
      (when (save-excursion
                (goto-char e)
                (setq f (evil-filepath-search-forward-char 'evil-filepath-is-separator-char t))
                (and f (>= f b)))
        (setq rlt (list b (+ 1 f) (- e 1)))))
    rlt))

(defun evil-filepath-get-path-already-inside ()
  (let (b e)
    (save-excursion
      (setq b (evil-filepath-search-forward-char 'evil-filepath-not-path-char t)))
    (save-excursion
      (setq e (evil-filepath-search-forward-char 'evil-filepath-not-path-char))
      (when e
        (goto-char (- e 1))
        ;; example: hello/world,
        (if (evil-filepath-char-not-placed-at-end-of-path (following-char))
            (setq e (- e 1)))
        ))
    (evil-filepath-calculate-path b e)))

(defun evil-filepath-search-forward-char (fn &optional backward)
  (let (found rlt (limit (if backward (point-min) (point-max))) out)
    (save-excursion
      (while (not out)
        ;; for the char, exit
        (if (setq found (apply fn (list (following-char))))
            (setq out t)
          ;; reach the limit, exit
          (if (= (point) limit)
              (setq out t)
            ;; keep moving
            (if backward (backward-char) (forward-char)))))
      (if found (setq rlt (point))))
    rlt))

(defun evil-filepath-extract-region ()
  "Find the closest file path"
  (let (rlt
        b
        f1
        f2)

    (if (and (not (evil-filepath-not-path-char (following-char)))
             (setq rlt (evil-filepath-get-path-already-inside)))
        ;; maybe (point) is in the middle of the path
        t
      ;; need search forward AND backward to find the right path
      (save-excursion
        ;; path in backward direction
        (when (setq b (evil-filepath-search-forward-char 'evil-filepath-is-separator-char t))
          (goto-char b)
          (setq f1 (evil-filepath-get-path-already-inside))))
      (save-excursion
        ;; path in forward direction
        (when (setq b (evil-filepath-search-forward-char 'evil-filepath-is-separator-char))
          (goto-char b)
          (setq f2 (evil-filepath-get-path-already-inside))))
      ;; pick one path as the final result
      (cond
       ((and f1 f2)
        (if (> (- (point) (nth 2 f1)) (- (nth 0 f2) (point)))
            (setq rlt f2)
          (setq rlt f1)))
       (f1
        (setq rlt f1))
       (f2
        (setq rlt f2))))

    rlt))

(evil-define-text-object evil-filepath-inner-text-object (&optional count begin end type)
  "File name of nearby path"
  (let ((selected-region (evil-filepath-extract-region)))
    (if selected-region
        (evil-range (nth 1 selected-region) (nth 2 selected-region) :expanded t))))

(evil-define-text-object evil-filepath-outer-text-object (&optional NUM begin end type)
  "Nearby path"
  (let ((selected-region (evil-filepath-extract-region)))
    (if selected-region
        (evil-range (car selected-region) (+ 1 (nth 2 selected-region)) type :expanded t))))

(define-key evil-inner-text-objects-map "f" 'evil-filepath-inner-text-object)
(define-key evil-outer-text-objects-map "f" 'evil-filepath-outer-text-object)
;; }}

;; {{ https://github.com/syl20bnr/evil-escape
(require 'evil-escape)
(setq-default evil-escape-delay 0.2)
(setq evil-escape-excluded-major-modes '(dired-mode))
(setq-default evil-escape-key-sequence "kj")
(evil-escape-mode 1)
;; }}

;; Move back the cursor one position when exiting insert mode
(setq evil-move-cursor-back t)

(defun toggle-org-or-message-mode ()
  (interactive)
  (if (eq major-mode 'message-mode)
      (org-mode)
    (if (eq major-mode 'org-mode) (message-mode))
    ))

;; (evil-set-initial-state 'org-mode 'emacs)
;; Remap org-mode meta keys for convenience
(evil-declare-key 'normal org-mode-map
  "gh" 'outline-up-heading
  "gl" 'outline-next-visible-heading
  "H" 'org-beginning-of-line ; smarter behaviour on headlines etc.
  "L" 'org-end-of-line ; smarter behaviour on headlines etc.
  "$" 'org-end-of-line ; smarter behaviour on headlines etc.
  "^" 'org-beginning-of-line ; ditto
  "-" 'org-ctrl-c-minus ; change bullet style
  "<" 'org-metaleft ; out-dent
  ">" 'org-metaright ; indent
  (kbd "TAB") 'org-cycle)

(loop for (mode . state) in
      '((minibuffer-inactive-mode . emacs)
        (ggtags-global-mode . emacs)
        (grep-mode . emacs)
        (Info-mode . emacs)
        (term-mode . emacs)
        (sdcv-mode . emacs)
        (anaconda-nav-mode . emacs)
        (log-edit-mode . emacs)
        (vc-log-edit-mode . emacs)
        (magit-log-edit-mode . emacs)
        (inf-ruby-mode . emacs)
        (direx:direx-mode . emacs)
        (yari-mode . emacs)
        (erc-mode . emacs)
        (neotree-mode . emacs)
        (w3m-mode . emacs)
        (gud-mode . emacs)
        (help-mode . emacs)
        (eshell-mode . emacs)
        (shell-mode . emacs)
        ;;(message-mode . emacs)
        (fundamental-mode . emacs)
        (weibo-timeline-mode . emacs)
        (weibo-post-mode . emacs)
        (sr-mode . emacs)
        (dired-mode . emacs)
        (compilation-mode . emacs)
        (speedbar-mode . emacs)
        (magit-commit-mode . normal)
        (magit-diff-mode . normal)
        (js2-error-buffer-mode . emacs)
        )
      do (evil-set-initial-state mode state))

(define-key evil-ex-completion-map (kbd "M-p") 'previous-complete-history-element)
(define-key evil-ex-completion-map (kbd "M-n") 'next-complete-history-element)

(define-key evil-normal-state-map "Y" (kbd "y$"))
(define-key evil-normal-state-map "+" 'evil-numbers/inc-at-pt)
(define-key evil-normal-state-map "-" 'evil-numbers/dec-at-pt)
(define-key evil-normal-state-map "go" 'goto-char)
(define-key evil-normal-state-map (kbd "M-y") 'browse-kill-ring)
(define-key evil-normal-state-map (kbd "j") 'evil-next-visual-line)
(define-key evil-normal-state-map (kbd "k") 'evil-previous-visual-line)

(require 'evil-matchit)
(global-evil-matchit-mode 1)

;; press ",xx" to expand region
;; then press "z" to contract, "x" to expand
(eval-after-load "evil"
  '(setq expand-region-contract-fast-key "z"))

;; I learn this trick from ReneFroger, need latest expand-region
;; @see https://github.com/redguardtoo/evil-matchit/issues/38
(define-key evil-visual-state-map (kbd "v") 'er/expand-region)
(define-key evil-insert-state-map (kbd "C-e") 'move-end-of-line)
(define-key evil-insert-state-map (kbd "C-k") 'kill-line)
(define-key evil-insert-state-map (kbd "M-j") 'yas-expand)
(define-key evil-emacs-state-map (kbd "M-j") 'yas-expand)
(global-set-key (kbd "C-r") 'undo-tree-redo)

;; My frequently used commands are listed here
(setq evil-leader/leader ",")
(require 'evil-leader)
(evil-leader/set-key
  "bf" 'beginning-of-defun
  "bu" 'backward-up-list
  "bb" 'back-to-previous-buffer
  "ef" 'end-of-defun
  "ddb" 'sdcv-search-pointer ; in buffer
  "ddt" 'sdcv-search-input+ ;; in tip
  "ddd" 'my-lookup-dict-org
  "ddw" 'define-word
  "ddp" 'define-word-at-point
  "mf" 'mark-defun
  "mmm" 'mpc-which-song
  "mmn" 'mpc-next-prev-song
  "mmp" '(lambda () (interactive) (mpc-next-prev-song t))
  "em" 'erase-message-buffer
  "eb" 'eval-buffer
  "sd" 'sudo-edit
  "sr" 'evil-surround-region
  "sc" 'shell-command
  "ee" 'eval-expression
  "aa" 'copy-to-x-clipboard ; used frequently
  "aw" 'ace-swap-window
  "af" 'ace-maximize-window
  "zz" 'paste-from-x-clipboard ; used frequently
  "cy" 'strip-convert-lines-into-one-big-string
  "bs" '(lambda () (interactive) (goto-edge-by-comparing-font-face -1))
  "es" 'goto-edge-by-comparing-font-face
  "ntt" 'neotree-toggle
  "ntf" 'neotree-find ; open file in current buffer in neotree
  "ntd" 'neotree-project-dir
  "nth" 'neotree-hide
  "nts" 'neotree-show
  "fl" 'cp-filename-line-number-of-current-buffer
  "fn" 'cp-filename-of-current-buffer
  "fp" 'cp-fullpath-of-current-buffer
  "dj" 'dired-jump ;; open the dired from current file
  "ff" 'toggle-full-window ;; I use WIN+F in i3
  "ip" 'find-file-in-project
  "is" 'find-file-in-project-by-selected
  "tm" 'get-term
  "tff" 'toggle-frame-fullscreen
  "tfm" 'toggle-frame-maximized
  ;; "ci" 'evilnc-comment-or-uncomment-lines
  ;; "cl" 'evilnc-comment-or-uncomment-to-the-line
  ;; "cc" 'evilnc-copy-and-comment-lines
  ;; "cp" 'evilnc-comment-or-uncomment-paragraphs
  "epy" 'emmet-expand-yas
  "epl" 'emmet-expand-line
  "rd" 'evilmr-replace-in-defun
  "rb" 'evilmr-replace-in-buffer
  "tt" 'evilmr-tag-selected-region ;; recommended
  "rt" 'evilmr-replace-in-tagged-region ;; recommended
  "yy" 'cb-switch-between-controller-and-view
  "tua" 'artbollocks-mode
  "yu" 'cb-get-url-from-controller
  "ht" 'helm-etags-select ;; better than find-tag (C-])
  "hm" 'helm-bookmarks
  "hb" 'helm-back-to-last-point
  "hh" 'browse-kill-ring
  "cg" 'helm-ls-git-ls
  "ud" 'my-gud-gdb
  "uk" 'gud-kill-yes
  "ur" 'gud-remove
  "ub" 'gud-break
  "uu" 'gud-run
  "up" 'gud-print
  "ue" 'gud-cls
  "un" 'gud-next
  "us" 'gud-step
  "ui" 'gud-stepi
  "uc" 'gud-cont
  "uf" 'gud-finish
  "kb" 'kill-buffer-and-window ;; "k" is preserved to replace "C-g"
  "it" 'issue-tracker-increment-issue-id-under-cursor
  "ls" 'highlight-symbol
  "lq" 'highlight-symbol-query-replace
  "ln" 'highlight-symbol-nav-mode ; use M-n/M-p to navigation between symbols
  "bm" 'pomodoro-start ;; beat myself
  "im" 'helm-imenu
  "ii" 'ido-imenu
  "ij" 'rimenu-jump
  "." 'evil-ex
  ;; @see https://github.com/pidu/git-timemachine
  ;; p: previous; n: next; w:hash; W:complete hash; g:nth version; q:quit
  "gm" 'git-timemachine-toggle
  ;; toggle overview,  @see http://emacs.wordpress.com/2007/01/16/quick-and-dirty-code-folding/
  "ov" 'my-overview-of-current-buffer
  "or" 'open-readme-in-git-root-directory
  "c$" 'org-archive-subtree ; `C-c $'
  "c<" 'org-promote-subtree ; `C-c C-<'
  "c>" 'org-demote-subtree ; `C-c C->'
  "cam" 'org-tags-view ; `C-c a m': search items in org-file-apps by tag
  "cxi" 'org-clock-in ; `C-c C-x C-i'
  "cxo" 'org-clock-out ; `C-c C-x C-o'
  "cxr" 'org-clock-report ; `C-c C-x C-r'
  "mq" 'lookup-doc-in-man
  "sg" 'w3m-google-by-filetype
  "sf" 'w3m-search-financial-dictionary
  "sq" 'w3m-stackoverflow-search
  "sj" 'w3m-search-js-api-mdn
  "sa" 'w3m-java-search
  "sh" 'w3mext-hacker-search ; code search in all engines with firefox
  "gg" 'my-vc-git-grep
  "gss" 'git-gutter:set-start-revision
  "gsh" 'git-gutter-reset-to-head-parent
  "gsr" 'git-gutter-reset-to-default
  "hr" 'helm-recentf
  "xc" 'save-buffers-kill-terminal
  "rr" 'steve-ido-choose-from-recentf ;; more quick than helm
  "di" 'evilmi-delete-items
  "si" 'evilmi-select-items
  "jb" 'js-beautify
  "jp" 'jsons-print-path
  "se" 'string-edit-at-point
  "xe" 'eval-last-sexp
  "x0" 'delete-window
  "x1" 'delete-other-windows
  "x2" 'split-window-vertically
  "x3" 'split-window-horizontally
  "xr" 'rotate-windows
  "xt" 'toggle-window-split
  "su" 'winner-undo
  "xu" 'winner-undo
  "to" 'toggle-web-js-offset
  "cf" 'helm-for-files ;; "C-c f"
  "sl" 'sort-lines
  "ulr" 'uniquify-all-lines-region
  "ulb" 'uniquify-all-lines-buffer
  "lo" 'moz-console-log-var
  "lj" 'moz-load-js-file-and-send-it
  "lk" 'latest-kill-to-clipboard
  "mr" 'moz-console-clear
  "rnr" 'rinari-web-server-restart
  "rnc" 'rinari-find-controller
  "rnv" 'rinari-find-view
  "rna" 'rinari-find-application
  "rnk" 'rinari-rake
  "rnm" 'rinari-find-model
  "rnl" 'rinari-find-log
  "rno" 'rinari-console
  "rnt" 'rinari-find-test
  "ss" 'swiper ; http://oremacs.com/2015/03/25/swiper-0.2.0/ for guide
  "st" 'swiper-the-thing
  "hst" 'hs-toggle-fold
  "hsa" 'hs-toggle-fold-all
  "hsh" 'hs-hide-block
  "hss" 'hs-show-block
  "hd" 'describe-function
  "hf" 'find-function
  "hk" 'describe-key
  "hv" 'describe-variable
  "gt" 'ggtags-find-tag-dwim
  "gr" 'ggtags-find-reference
  "fb" 'flyspell-buffer
  "fe" 'flyspell-goto-next-error
  "fa" 'flyspell-auto-correct-word
  "pe" 'flymake-goto-prev-error
  "ne" 'flymake-goto-next-error
  "fw" 'ispell-word
  "bc" '(lambda () (interactive) (wxhelp-browse-class-or-api (thing-at-point 'symbol)))
  "ma" 'mc/mark-all-like-this-in-defun
  "mw" 'mc/mark-all-words-like-this-in-defun
  "ms" 'mc/mark-all-symbols-like-this-in-defun
  ;; "opt" is occupied by my-open-project-todo
  ;; recommended in html
  "md" 'mc/mark-all-like-this-dwim
  "otl" 'org-toggle-link-display
  "oc" 'occur
  "om" 'toggle-org-or-message-mode
  "ut" 'undo-tree-visualize
  "ar" 'align-regexp
  "ww" 'save-buffer
  "wrn" 'httpd-restart-now
  "wrd" 'httpd-restart-at-default-directory
  "bk" 'buf-move-up
  "bj" 'buf-move-down
  "bh" 'buf-move-left
  "bl" 'buf-move-right
  "so" 'sos
  "0" 'select-window-0
  "1" 'select-window-1
  "2" 'select-window-2
  "3" 'select-window-3
  "4" 'select-window-4
  "5" 'select-window-5
  "6" 'select-window-6
  "7" 'select-window-7
  "8" 'select-window-8
  "9" 'select-window-9
  "xm" 'smex
  "mx" 'helm-M-x
  "xx" 'er/expand-region
  "xf" 'ido-find-file
  "xb" 'ido-switch-buffer
  "xo" 'helm-find-files
  "ri" 'yari-helm
  "vv" 'scroll-other-window
  "vu" 'scroll-other-window-up
  "vr" 'vr/replace
  "vq" 'vr/query-replace
  "vm" 'vr/mc-mark
  "js" 'w3mext-search-js-api-mdn
  "jde" 'js2-display-error-list
  "jte" 'js2-mode-toggle-element
  "jtf" 'js2-mode-toggle-hide-functions
  "jjeo" 'js2r-expand-object
  "jjco" 'js2r-contract-object
  "jjeu" 'js2r-expand-function
  "jjcu" 'js2r-contract-function
  "jjea" 'js2r-expand-array
  "jjca" 'js2r-contract-array
  "jjwi" 'js2r-wrap-buffer-in-iife
  "jjig" 'js2r-inject-global-in-iife
  "jjev" 'js2r-extract-var
  "jjiv" 'js2r-inline-var
  "jjrv" 'js2r-rename-var
  "jjvt" 'js2r-var-to-this
  "jjag" 'js2r-add-to-globals-annotation
  "jjsv" 'js2r-split-var-declaration
  "jjss" 'js2r-split-string
  "jjef" 'js2r-extract-function
  "jjem" 'js2r-extract-method
  "jjip" 'js2r-introduce-parameter
  "jjlp" 'js2r-localize-parameter
  "jjtf" 'js2r-toggle-function-expression-and-declaration
  "jjao" 'js2r-arguments-to-object
  "jjuw" 'js2r-unwrap
  "jjwl" 'js2r-wrap-in-for-loop
  "jj3i" 'js2r-ternary-to-if
  "jjlt" 'js2r-log-this
  "jjsl" 'js2r-forward-slurp
  "jjba" 'js2r-forward-barf
  "jjk" 'js2r-kill
  "xh" 'mark-whole-buffer
  "xk" 'ido-kill-buffer
  "xs" 'save-buffer
  "xz" 'suspend-frame
  "xvm" 'vc-rename-file-and-buffer
  "xvc" 'vc-copy-file-and-rename-buffer
  "xvv" 'vc-next-action
  "xva" 'git-add-current-file
  "xvp" 'git-push-remote-origin
  "xvu" 'git-add-option-update
  "xvg" 'vc-annotate
  "xvs" 'git-gutter:stage-hunk
  "xvr" 'git-gutter:revert-hunk
  "xvl" 'vc-print-log
  "xvb" 'git-messenger:popup-message
  "xv=" 'git-gutter:popup-hunk
  "nn" 'my-goto-next-hunk
  "pp" 'my-goto-previous-hunk
  "xnn" 'narrow-or-widen-dwim
  "xnw" 'widen
  "xnd" 'narrow-to-defun
  "xnr" 'narrow-to-region
  "ycr" 'my-yas-reload-all
  "zc" 'wg-create-workgroup
  "zk" 'wg-kill-workgroup
  "zv" 'my-wg-swich-to-workgroup
  "zj" 'my-wg-switch-to-workgroup-at-index
  "zs" 'my-wg-save-session
  "zb" 'wg-switch-to-buffer
  "zwr" 'wg-redo-wconfig-change
  "zws" 'wg-save-wconfig
  "wf" 'popup-which-function)

;; change mode-line color by evil state
(lexical-let ((default-color (cons (face-background 'mode-line)
                                   (face-foreground 'mode-line))))
  (add-hook 'post-command-hook
            (lambda ()
              (let ((color (cond ((minibufferp) default-color)
                                 ((evil-insert-state-p) '("#e80000" . "#ffffff"))
                                 ((evil-emacs-state-p)  '("#444488" . "#ffffff"))
                                 ((buffer-modified-p)   '("#006fa0" . "#ffffff"))
                                 (t default-color))))
                (set-face-background 'mode-line (car color))
                (set-face-foreground 'mode-line (cdr color))))))

(require 'evil-nerd-commenter)
(evilnc-default-hotkeys)

(provide 'init-evil)
