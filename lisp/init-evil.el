;; @see https://bitbucket.org/lyro/evil/issue/360/possible-evil-search-symbol-forward
;; evil 1.0.8 search word instead of symbol
(setq evil-symbol-word-search t)
(require 'undo-tree)
;; For the motions g; g, and for the last-change-register ., 
(require 'goto-chg)

;; @see https://bitbucket.org/lyro/evil/issue/511/let-certain-minor-modes-key-bindings
(defmacro adjust-major-mode-keymap-with-evil (m &optional r)
  `(eval-after-load (quote ,(if r r m))
    '(progn
       (evil-make-overriding-map ,(intern (concat m "-mode-map")) 'normal)
       ;; force update evil keymaps after git-timemachine-mode loaded
       (add-hook (quote ,(intern (concat m "-mode-hook"))) #'evil-normalize-keymaps))))

(adjust-major-mode-keymap-with-evil "git-timemachine")
(adjust-major-mode-keymap-with-evil "browse-kill-ring")

(require 'evil)

;; @see https://bitbucket.org/lyro/evil/issue/342/evil-default-cursor-setting-should-default
;; Cursor is alway black because of evil.
;; Here is the workaround
(setq evil-default-cursor t)

;; {{ multiple-cursors
;; step 1, select thing in visual-mode (OPTIONAL)
;; step 2, `mc/mark-all-like-dwim' or `mc/mark-all-like-this-in-defun'
;; step 3, `ace-mc-add-multiple-cursors' to remove cursor, press RET to confirm
;; step 4, press s or S to start replace
;; step 5, press C-g to quit multiple-cursors
(define-key evil-visual-state-map (kbd "mn") 'mc/mark-next-like-this)
(define-key evil-visual-state-map (kbd "ma") 'mc/mark-all-like-this-dwim)
(define-key evil-visual-state-map (kbd "md") 'mc/mark-all-like-this-in-defun)
(define-key evil-visual-state-map (kbd "mm") 'ace-mc-add-multiple-cursors)
(define-key evil-visual-state-map (kbd "ms") 'ace-mc-add-single-cursor)
;; }}

;; enable evil-mode
(evil-mode 1)

;; {{ @see https://github.com/timcharper/evil-surround for tutorial
(require 'evil-surround)
(global-evil-surround-mode 1)
(defun evil-surround-prog-mode-hook-setup ()
  (push '(47 . ("/" . "/")) evil-surround-pairs-alist)
  (push '(40 . ("(" . ")")) evil-surround-pairs-alist)
  (push '(41 . ("(" . ")")) evil-surround-pairs-alist)
  (push '(91 . ("[" . "]")) evil-surround-pairs-alist)
  (push '(93 . ("[" . "]")) evil-surround-pairs-alist))
(add-hook 'prog-mode-hook 'evil-surround-prog-mode-hook-setup)

(defun evil-surround-js-mode-hook-setup ()
  ;; ES6
  (push '(?1 . ("{`" . "`}")) evil-surround-pairs-alist)
  (push '(?2 . ("${" . "}")) evil-surround-pairs-alist)
  (push '(?4 . ("(e) => " . "(e)")) evil-surround-pairs-alist)
  ;; ReactJS
  (push '(?3 . ("classNames(" . ")")) evil-surround-pairs-alist))
(add-hook 'js-mode-hook 'evil-surround-js-mode-hook-setup)

(defun evil-surround-emacs-lisp-mode-hook-setup ()
  (push '(?` . ("`" . "'")) evil-surround-pairs-alist))
(add-hook 'emacs-lisp-mode-hook 'evil-surround-emacs-lisp-mode-hook-setup)
(defun evil-surround-org-mode-hook-setup ()
  (push '(91 . ("[" . "]")) evil-surround-pairs-alist)
  (push '(93 . ("[" . "]")) evil-surround-pairs-alist)
  (push '(?= . ("=" . "=")) evil-surround-pairs-alist))
(add-hook 'org-mode-hook 'evil-surround-org-mode-hook-setup)
;; }}

;; {{ For example, press `viW*`
(require 'evil-visualstar)
(setq evil-visualstar/persistent t)
(global-evil-visualstar-mode t)
;; }}


;; ffip-diff-mode (read only) evil setup
(defun ffip-diff-mode-hook-setup ()
    (evil-local-set-key 'normal "K" 'diff-hunk-prev)
    (evil-local-set-key 'normal "J" 'diff-hunk-next)
    (evil-local-set-key 'normal "P" 'diff-file-prev)
    (evil-local-set-key 'normal "N" 'diff-file-next)
    (evil-local-set-key 'normal "q" 'ffip-diff-quit)
    (evil-local-set-key 'normal (kbd "RET") 'ffip-diff-find-file)
    ;; "C-c C-a" is binding to `diff-apply-hunk' in `diff-mode'
    (evil-local-set-key 'normal "a" 'ffip-diff-apply-hunk)
    (evil-local-set-key 'normal "o" 'ffip-diff-find-file))
(add-hook 'ffip-diff-mode-hook 'ffip-diff-mode-hook-setup)

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
;; between equal signs
(define-and-bind-text-object "=" "=" "=")
;; between pipe characters:
(define-and-bind-text-object "|" "|" "|")
;; regular expression
(define-and-bind-text-object "/" "/" "/")
;; trimmed line
(define-and-bind-text-object "l" "^ *" " *$")
;; angular template
(define-and-bind-text-object "r" "\{\{" "\}\}")
;; }}


;; {{ nearby file path as text object,
;;      - "vif" to select base name
;;      - "vaf" to select full path
;;
;;  example:
;;    "/hello/world"
;;    "/test/back.exe"
;;    "C:hello\\hello\\world\\test.exe"
;;    "D:blah\\hello\\world\\base.exe"
(defun evil-filepath-is-separator-char (ch)
  "Check ascii table that CH is slash characters.
If the character before and after CH is space or tab, CH is NOT slash"
  (let (rlt prefix-ch postfix-ch)
    (when (and (> (point) (point-min)) (< (point) (point-max)))
        (save-excursion
          (backward-char)
          (setq prefix-ch (following-char)))
        (save-excursion
          (forward-char)
          (setq postfix-ch (following-char))))
    (if (and (not (or (= prefix-ch 32) (= postfix-ch 32)))
             (or (= ch 47) (= ch 92)) )
        (setq rlt t))
    rlt))

(defun evil-filepath-not-path-char (ch)
  "Check ascii table for charctater."
  (or (and (<= 0 ch) (<= ch 32))
      (memq ch
            '(34 ; double quotes
              ?'
              40 ; (
              41 ; )
              ?<
              ?>
              91 ; [
              93 ; ]
              ?`
              ?{
              ?}
              127))))

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
  (let* (b e)
    (save-excursion
      (setq b (evil-filepath-search-forward-char 'evil-filepath-not-path-char t)))
    (save-excursion
      (when (setq e (evil-filepath-search-forward-char 'evil-filepath-not-path-char))
        (goto-char (- e 1))
        ;; example: hello/world,
        (if (memq (following-char) '(?, ?.))
            (setq e (- e 1)))))
    (evil-filepath-calculate-path b e)))

(defun evil-filepath-search-forward-char (fn &optional backward)
  (let* (found
         rlt
         (limit (if backward (point-min) (point-max)))
         out-of-loop)
    (save-excursion
      (while (not out-of-loop)
        ;; for the char, exit
        (if (setq found (apply fn (list (following-char))))
            (setq out-of-loop t)
          ;; reach the limit, exit
          (if (= (point) limit)
              (setq out-of-loop t)
            ;; keep moving
            (if backward (backward-char) (forward-char)))))
      (if found (setq rlt (point))))
    rlt))

(defun evil-filepath-extract-region ()
  "Find the closest file path"
  (let* (rlt
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
  (let* ((selected-region (evil-filepath-extract-region)))
    (if selected-region
        (evil-range (nth 1 selected-region) (nth 2 selected-region) :expanded t))))

(evil-define-text-object evil-filepath-outer-text-object (&optional NUM begin end type)
  "Nearby path."
  (let* ((selected-region (evil-filepath-extract-region)))
    (if selected-region
        (evil-range (car selected-region) (+ 1 (nth 2 selected-region)) type :expanded t))))

(define-key evil-inner-text-objects-map "f" 'evil-filepath-inner-text-object)
(define-key evil-outer-text-objects-map "f" 'evil-filepath-outer-text-object)
;; }}

;; {{ https://github.com/syl20bnr/evil-escape
(require 'evil-escape)
(setq-default evil-escape-delay 0.5)
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
    (if (eq major-mode 'org-mode) (message-mode))))

;; (evil-set-initial-state 'org-mode 'emacs)

;; As a general RULE, mode specific evil leader keys started
;; with uppercased character or 'g' or special character except "=" and "-"
(evil-declare-key 'normal org-mode-map
  "gh" 'outline-up-heading
  "gl" 'outline-next-visible-heading
  "gj" 'outline-forward-same-level
  "gk" 'outline-backward-same-level
  "$" 'org-end-of-line ; smarter behaviour on headlines etc.
  "^" 'org-beginning-of-line ; ditto
  "<" (lambda () (interactive) (org-demote-or-promote 1)) ; out-dent
  ">" 'org-demote-or-promote ; indent
  (kbd "TAB") 'org-cycle)

(evil-declare-key 'normal markdown-mode-map
  "gh" 'outline-up-heading
  "gl" 'outline-next-visible-heading
  "gj" 'outline-forward-same-level
  "gk" 'outline-backward-same-level
  (kbd "TAB") 'org-cycle)

;; {{ specify major mode uses Evil (vim) NORMAL state or EMACS original state.
;; You may delete this setup to use Evil NORMAL state always.
(loop for (mode . state) in
      '((minibuffer-inactive-mode . emacs)
        (calendar-mode . emacs)
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
        (epa-key-list-mode . emacs)
        (fundamental-mode . emacs)
        (weibo-timeline-mode . emacs)
        (weibo-post-mode . emacs)
        (woman-mode . emacs)
        (sr-mode . emacs)
        (profiler-report-mode . emacs)
        (dired-mode . emacs)
        (compilation-mode . emacs)
        (speedbar-mode . emacs)
        (ivy-occur-mode . emacs)
        (messages-buffer-mode . normal)
        (magit-commit-mode . normal)
        (magit-diff-mode . normal)
        (browse-kill-ring-mode . normal)
        (js2-error-buffer-mode . emacs)
        )
      do (evil-set-initial-state mode state))
;; }}

;; I prefer Emacs way after pressing ":" in evil-mode
(define-key evil-ex-completion-map (kbd "C-a") 'move-beginning-of-line)
(define-key evil-ex-completion-map (kbd "C-b") 'backward-char)
(define-key evil-ex-completion-map (kbd "M-p") 'previous-complete-history-element)
(define-key evil-ex-completion-map (kbd "M-n") 'next-complete-history-element)

(define-key evil-normal-state-map "Y" (kbd "y$"))
(define-key evil-normal-state-map "go" 'goto-char)
(define-key evil-normal-state-map (kbd "M-y") 'counsel-browse-kill-ring)
(define-key evil-normal-state-map (kbd "C-]") 'counsel-etags-find-tag-at-point)
(define-key evil-visual-state-map (kbd "C-]") 'counsel-etags-find-tag-at-point)
(define-key evil-insert-state-map (kbd "C-x C-n") 'evil-complete-next-line)
(define-key evil-insert-state-map (kbd "C-x C-p") 'evil-complete-previous-line)

(require 'evil-matchit)
(global-evil-matchit-mode 1)

;; press ",xx" to expand region
;; then press "z" to contract, "x" to expand
(eval-after-load "evil"
  '(progn
     (setq expand-region-contract-fast-key "z")))

;; I learn this trick from ReneFroger, need latest expand-region
;; @see https://github.com/redguardtoo/evil-matchit/issues/38
(define-key evil-visual-state-map (kbd "v") 'er/expand-region)
(define-key evil-insert-state-map (kbd "C-e") 'move-end-of-line)
(define-key evil-insert-state-map (kbd "C-k") 'kill-line)
(define-key evil-insert-state-map (kbd "M-j") 'yas-expand)
(define-key evil-emacs-state-map (kbd "M-j") 'yas-expand)
(global-set-key (kbd "C-r") 'undo-tree-redo)

;; My frequently used commands are listed here
;; For example, for line like `"ef" 'end-of-defun`
;;   You can either press `,ef` or `M-x end-of-defun` to execute it
(require 'general)
(general-evil-setup t)

;; {{ use `,` as leader key
(nvmap :prefix ","
       "=" 'increase-default-font-height ; GUI emacs only
       "-" 'decrease-default-font-height ; GUI emacs only
       "bf" 'beginning-of-defun
       "bu" 'backward-up-list
       "bb" 'back-to-previous-buffer
       "ef" 'end-of-defun
       "mf" 'mark-defun
       "em" 'erase-message-buffer
       "eb" 'eval-buffer
       "sd" 'sudo-edit
       "sc" 'scratch
       "ee" 'eval-expression
       "aa" 'copy-to-x-clipboard ; used frequently
       "aw" 'ace-swap-window
       "af" 'ace-maximize-window
       "ac" 'aya-create
       "ae" 'aya-expand
       "zz" 'paste-from-x-clipboard ; used frequently
       "cy" 'strip-convert-lines-into-one-big-string
       "bs" '(lambda () (interactive) (goto-edge-by-comparing-font-face -1))
       "es" 'goto-edge-by-comparing-font-face
       "vj" 'my-validate-json-or-js-expression
       "kc" 'kill-ring-to-clipboard
       "mcr" 'my-create-regex-from-kill-ring
       "ntt" 'neotree-toggle
       "ntf" 'neotree-find ; open file in current buffer in neotree
       "ntd" 'neotree-project-dir
       "nth" 'neotree-hide
       "nts" 'neotree-show
       "fn" 'cp-filename-of-current-buffer
       "fp" 'cp-fullpath-of-current-buffer
       "dj" 'dired-jump ;; open the dired from current file
       "ff" 'toggle-full-window ;; I use WIN+F in i3
       "ip" 'find-file-in-project
       "kk" 'find-file-in-project-by-selected
       "kn" 'find-file-with-similar-name ; ffip v5.3.1
       "fd" 'find-directory-in-project-by-selected
       "trm" 'get-term
       "tff" 'toggle-frame-fullscreen
       "tfm" 'toggle-frame-maximized
       "ti" 'fastdef-insert
       "th" 'fastdef-insert-from-history
       ;; "ci" 'evilnc-comment-or-uncomment-lines
       ;; "cl" 'evilnc-comment-or-uncomment-to-the-line
       ;; "cc" 'evilnc-copy-and-comment-lines
       ;; "cp" 'evilnc-comment-or-uncomment-paragraphs
       "epy" 'emmet-expand-yas
       "epl" 'emmet-expand-line
       "rd" 'evilmr-replace-in-defun
       "rb" 'evilmr-replace-in-buffer
       "ts" 'evilmr-tag-selected-region ;; recommended
       "rt" 'evilmr-replace-in-tagged-region ;; recommended
       "tua" 'artbollocks-mode
       "cby" 'cb-switch-between-controller-and-view
       "cbu" 'cb-get-url-from-controller
       "ht" 'counsel-etags-find-tag-at-point ; better than find-tag C-]
       "mm" 'counsel-bookmark-goto
       "mk" 'bookmark-set
       "yy" 'counsel-browse-kill-ring
       "gf" 'counsel-git ; find file
       "gg" 'counsel-git-grep-by-selected ; quickest grep should be easy to press
       "gm" 'counsel-git-find-my-file
       "gs" 'ffip-show-diff ; find-file-in-project 5.0+
       "gd" 'ffip-show-diff-by-description ;find-file-in-project 5.3.0+
       "sf" 'counsel-git-show-file
       "sh" 'my-select-from-search-text-history
       "df" 'counsel-git-diff-file
       "rjs" 'run-js
       "jsr" 'js-send-region
       "jsb" 'js-clear-send-buffer
       "rmz" 'run-mozilla
       "rpy" 'run-python
       "rlu" 'run-lua
       "tci" 'toggle-company-ispell
       "kb" 'kill-buffer-and-window ;; "k" is preserved to replace "C-g"
       "it" 'issue-tracker-increment-issue-id-under-cursor
       "ls" 'highlight-symbol
       "lq" 'highlight-symbol-query-replace
       "ln" 'highlight-symbol-nav-mode ; use M-n/M-p to navigation between symbols
       "bm" 'pomodoro-start ;; beat myself
       "ii" 'counsel-imenu
       "ij" 'rimenu-jump
       "." 'evil-ex
       ;; @see https://github.com/pidu/git-timemachine
       ;; p: previous; n: next; w:hash; W:complete hash; g:nth version; q:quit
       "tt" 'dumb-jump-go
       "tb" 'dumb-jump-back
       "tm" 'my-git-timemachine
       "tdb" 'tidy-buffer
       "tdl" 'tidy-current-line
       ;; toggle overview,  @see http://emacs.wordpress.com/2007/01/16/quick-and-dirty-code-folding/
       "ov" 'my-overview-of-current-buffer
       "or" 'open-readme-in-git-root-directory
       "oo" 'compile
       "c$" 'org-archive-subtree ; `C-c $'
       ;; org-do-demote/org-do-premote support selected region
       "c<" 'org-do-promote ; `C-c C-<'
       "c>" 'org-do-demote ; `C-c C->'
       "cam" 'org-tags-view ; `C-c a m': search items in org-file-apps by tag
       "cxi" 'org-clock-in ; `C-c C-x C-i'
       "cxo" 'org-clock-out ; `C-c C-x C-o'
       "cxr" 'org-clock-report ; `C-c C-x C-r'
       "qq" 'counsel-etags-grep
       "xc" 'save-buffers-kill-terminal
       "rr" 'my-counsel-recentf
       "rh" 'counsel-yank-bash-history ; bash history command => yank-ring
       "rf" 'counsel-goto-recent-directory
       "da" 'diff-region-tag-selected-as-a
       "db" 'diff-region-compare-with-b
       "di" 'evilmi-delete-items
       "si" 'evilmi-select-items
       "jb" 'js-beautify
       "jp" 'my-print-json-path
       "sep" 'string-edit-at-point
       "sec" 'string-edit-conclude
       "sea" 'string-edit-abort
       "xe" 'eval-last-sexp
       "x0" 'delete-window
       "x1" 'delete-other-windows
       "x2" 'my-split-window-vertically
       "x3" 'my-split-window-horizontally
       "s2" 'ffip-split-window-vertically
       "s3" 'ffip-split-window-horizontally
       "rw" 'rotate-windows
       "ru" 'undo-tree-save-state-to-register ; C-x r u
       "rU" 'undo-tree-restore-state-from-register ; C-x r U
       "xt" 'toggle-window-split
       "uu" 'winner-undo
       "UU" 'winner-redo
       "to" 'toggle-web-js-offset
       "sl" 'sort-lines
       "ulr" 'uniquify-all-lines-region
       "ulb" 'uniquify-all-lines-buffer
       "lj" 'moz-load-js-file-and-send-it
       "mr" 'moz-console-clear
       "fs" 'ffip-save-ivy-last
       "fr" 'ffip-ivy-resume
       "fc" 'cp-ffip-ivy-last
       "ss" 'swiper-the-thing ; http://oremacs.com/2015/03/25/swiper-0.2.0/ for guide
       "hst" 'hs-toggle-fold
       "hsa" 'hs-toggle-fold-all
       "hsh" 'hs-hide-block
       "hss" 'hs-show-block
       "hd" 'describe-function
       "hf" 'find-function
       "hk" 'describe-key
       "hv" 'describe-variable
       "gt" 'counsel-gtags-dwim ; jump from reference to definition or vice versa
       "gr" 'counsel-gtags-find-symbol
       "gu" 'counsel-gtags-update-tags
       "fb" 'flyspell-buffer
       "fe" 'flyspell-goto-next-error
       "fa" 'flyspell-auto-correct-word
       "pe" 'flymake-goto-prev-error
       "ne" 'flymake-goto-next-error
       "fw" 'ispell-word
       "bc" '(lambda () (interactive) (wxhelp-browse-class-or-api (thing-at-point 'symbol)))
       "og" 'org-agenda
       "otl" 'org-toggle-link-display
       "oa" '(lambda ()
               (interactive)
               (unless (featurep 'org) (require 'org))
               (counsel-org-agenda-headlines))
       "om" 'toggle-org-or-message-mode
       "ut" 'undo-tree-visualize
       "ar" 'align-regexp
       "wrn" 'httpd-restart-now
       "wrd" 'httpd-restart-at-default-directory
       "bk" 'buf-move-up
       "bj" 'buf-move-down
       "bh" 'buf-move-left
       "bl" 'buf-move-right
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
       "xm" 'my-M-x
       "xx" 'er/expand-region
       "xf" 'ido-find-file
       "xb" 'ivy-switch-buffer-by-pinyin
       "xh" 'mark-whole-buffer
       "xk" 'ido-kill-buffer
       "xs" 'save-buffer
       "xz" 'suspend-frame
       "vm" 'vc-rename-file-and-buffer
       "vc" 'vc-copy-file-and-rename-buffer
       "xvv" 'vc-next-action ; 'C-x v v' in original
       "va" 'git-add-current-file
       "vk" 'git-checkout-current-file
       "vg" 'vc-annotate ; 'C-x v g' in original
       "vs" 'git-gutter:stage-hunk
       "vr" 'git-gutter:revert-hunk
       "vl" 'vc-print-log
       "vv" 'vc-msg-show
       "v=" 'git-gutter:popup-hunk
       "hh" 'cliphist-paste-item
       "yu" 'cliphist-select-item
       "ih" 'my-goto-git-gutter ; use ivy-mode
       "ir" 'ivy-resume
       "nn" 'my-goto-next-hunk
       "pp" 'my-goto-previous-hunk
       "ww" 'narrow-or-widen-dwim
       "xnw" 'widen
       "xnd" 'narrow-to-defun
       "xnr" 'narrow-to-region
       "ycr" 'my-yas-reload-all
       "wf" 'popup-which-function)
;; }}

;; {{ Use `SPC` as leader key
;; all keywords arguments are still supported
(nvmap :prefix "SPC"
       "ss" 'wg-create-workgroup ; save windows layout
       "se" 'evil-iedit-state/iedit-mode ; start iedit in emacs
       "sc" 'shell-command
       "ll" 'my-wg-switch-workgroup ; load windows layout
       "kk" 'scroll-other-window
       "jj" 'scroll-other-window-up
       "yy" 'hydra-launcher/body
       "hh" 'multiple-cursors-hydra/body
       "gi" 'gist-region ; only workable on my computer
       "tt" 'my-toggle-indentation
       "gs" 'git-gutter:set-start-revision
       "gh" 'git-gutter-reset-to-head-parent
       "gr" 'git-gutter-reset-to-default
       "ps" 'profiler-start
       "pr" 'profiler-report
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
       "ma" 'mc/mark-all-like-this-dwim
       "md" 'mc/mark-all-like-this-in-defun
       "mm" 'ace-mc-add-multiple-cursors
       "mn" 'mc/mark-next-like-this
       "ms" 'mc/skip-to-next-like-this
       "me" 'mc/edit-lines)

;; per-major-mode setup
(general-define-key :states '(normal motion insert emacs)
                    :keymaps 'js2-mode-map
                    :prefix "SPC"
                    :non-normal-prefix "M-SPC"
                    "de" 'js2-display-error-list
                    "nn" 'js2-next-error
                    "te" 'js2-mode-toggle-element
                    "tf" 'js2-mode-toggle-hide-functions
                    "jeo" 'js2r-expand-object
                    "jco" 'js2r-contract-object
                    "jeu" 'js2r-expand-function
                    "jcu" 'js2r-contract-function
                    "jea" 'js2r-expand-array
                    "jca" 'js2r-contract-array
                    "jwi" 'js2r-wrap-buffer-in-iife
                    "jig" 'js2r-inject-global-in-iife
                    "jev" 'js2r-extract-var
                    "jiv" 'js2r-inline-var
                    "jrv" 'js2r-rename-var
                    "jvt" 'js2r-var-to-this
                    "jag" 'js2r-add-to-globals-annotation
                    "jsv" 'js2r-split-var-declaration
                    "jss" 'js2r-split-string
                    "jef" 'js2r-extract-function
                    "jem" 'js2r-extract-method
                    "jip" 'js2r-introduce-parameter
                    "jlp" 'js2r-localize-parameter
                    "jtf" 'js2r-toggle-function-expression-and-declaration
                    "jao" 'js2r-arguments-to-object
                    "juw" 'js2r-unwrap
                    "jwl" 'js2r-wrap-in-for-loop
                    "j3i" 'js2r-ternary-to-if
                    "jlt" 'js2r-log-this
                    "jsl" 'js2r-forward-slurp
                    "jba" 'js2r-forward-barf
                    "jk" 'js2r-kill)
;; }}

;; Press `dd' to delete lines in `wgrep-mode' in evil directly
(defadvice evil-delete (around evil-delete-hack activate)
  ;; make buffer writable
  (if (and (boundp 'wgrep-prepared) wgrep-prepared)
      (wgrep-toggle-readonly-area))
  ad-do-it
  ;; make buffer read-only
  (if (and (boundp 'wgrep-prepared) wgrep-prepared)
      (wgrep-toggle-readonly-area)))

;; {{ Use `;` as leader key, for searching something
(nvmap :prefix ";"
       ;; Search character(s) at the beginning of word
       ;; See https://github.com/abo-abo/avy/issues/70
       ;; You can change the avy font-face in ~/.custom.el:
       ;;  (eval-after-load 'avy
       ;;   '(progn
       ;;      (set-face-attribute 'avy-lead-face-0 nil :foreground "black")
       ;;      (set-face-attribute 'avy-lead-face-0 nil :background "#f86bf3")))
       ";" 'avy-goto-char-2
       "w" 'avy-goto-word-or-subword-1
       "a" 'avy-goto-char-timer
       "db" 'sdcv-search-pointer ; in buffer
       "dt" 'sdcv-search-input+ ; in tip
       "dd" 'my-lookup-dict-org
       "mm" 'lookup-doc-in-man
       "gg" 'w3m-google-search
       "gf" 'w3m-google-by-filetype
       "gd" 'w3m-search-financial-dictionary
       "gj" 'w3m-search-js-api-mdn
       "ga" 'w3m-java-search
       "gh" 'w3mext-hacker-search ; code search in all engines with firefox
       "gq" 'w3m-stackoverflow-search
       "mm" 'mpc-which-song
       "mn" 'mpc-next-prev-song
       "mp" '(lambda () (interactive) (mpc-next-prev-song t)))
;; }}

;; {{ remember what we searched
;; http://emacs.stackexchange.com/questions/24099/how-to-yank-text-to-search-command-after-in-evil-mode/
(defvar my-search-text-history nil "List of text I searched.")
(defun my-select-from-search-text-history ()
  (interactive)
  (ivy-read "Search text history:" my-search-text-history
            :action (lambda (item)
                      (copy-yank-str item)
                      (message "%s => clipboard & yank ring" item))))
(defun my-cc-isearch-string ()
  (interactive)
  (if (and isearch-string (> (length isearch-string) 0))
      ;; NOT pollute clipboard who has things to paste into Emacs
      (add-to-list 'my-search-text-history isearch-string)))

(defadvice evil-search-incrementally (after evil-search-incrementally-after-hack activate)
  (my-cc-isearch-string))

(defadvice evil-search-word (after evil-search-word-after-hack activate)
  (my-cc-isearch-string))

(defadvice evil-visualstar/begin-search (after evil-visualstar/begin-search-after-hack activate)
  (my-cc-isearch-string))
;; }}

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

;; {{ evil-exchange
;; press gx twice to exchange, gX to cancel
(require 'evil-exchange)
;; change default key bindings (if you want) HERE
;; (setq evil-exchange-key (kbd "zx"))
(evil-exchange-install)
;; }}

;; {{ evil-lion
;; After pressing `glip=` or `gl2j=` (gl is the operator, ip or 2j is text object, = separator):
;; one = 1
;; three = 3
;; fifteen = 15
;;
;; will become:
;; one     = 1
;; three   = 3
;; fifteen = 15
;;
;; If the align separator is / you will be prompted for a regular expression instead of a plain character.
(require 'evil-lion)
(evil-lion-install)
;; }}

;; {{ @see https://github.com/syl20bnr/spacemacs/blob/master/doc/DOCUMENTATION.org#replacing-text-with-iedit
;; same keybindgs as spacemacs:
;;  - "SPC s e" to start `iedit-mode'
;;  - "TAB" to toggle current occurrence
;;  - "n" next, "N" previous (obviously we use "p" for yank)
;;  - "gg" the first occurence, "G" the last occurence
;;  - Please note ";;" or `avy-goto-char-timer' is also useful
(require 'evil-iedit-state)
;; }}

;; {{ Evil’s f/F/t/T commands with Pinyin supptt,
(require 'evil-find-char-pinyin)
(evil-find-char-pinyin-mode 1)
;; }}

(provide 'init-evil)
