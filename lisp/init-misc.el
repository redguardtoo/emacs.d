;; -*- coding: utf-8; lexical-binding: t; -*-

;; Avoid potential lag:
;; https://emacs.stackexchange.com/questions/28736/emacs-pointcursor-movement-lag/28746
;; `next-line' triggers the `format-mode-line' which triggers `projectile-project-name'
;; I use find-file-in-project instead of projectile. So I don't have this issue.
;; Set `auto-window-vscroll' to nil to avoid triggering `format-mode-line'.
(setq auto-window-vscroll nil)

;; {{ auto save set up
(defvar my-auto-save-exclude-major-mode-list
  '(message-mode)
  "The major modes where auto-save is disabled.")

(setq auto-save-visited-interval 2)

(defun my-auto-save-visited-predicate ()
  "Predicate to control which buffers are auto-saved."
  (and (buffer-file-name)
       (not (file-remote-p (buffer-file-name)))
       (not (my-file-too-big-p (buffer-file-name)))
       (file-writable-p (buffer-file-name))
       (not (memq major-mode my-auto-save-exclude-major-mode-list))))

(defun my-auto-save-visited-mode-setup ()
  "Auto save setup."
  ;; turn off `auto-save-visited-mode' in certain scenarios
  (when (my-auto-save-visited-predicate)
    (setq-local auto-save-visited-mode nil)))

(cond
 (*emacs29*
  (setq auto-save-visited-predicate #'my-auto-save-visited-predicate))
 (t
  (defvar auto-save-visited-predicate)
  (add-hook 'auto-save-visited-mode-hook #'my-auto-save-visited-mode-setup)))

(my-run-with-idle-timer 2 #'auto-save-visited-mode)
;; }}

;; {{ auto-yasnippet
;; Use C-q instead tab to complete snippet
;; - `aya-create' at first, input ~ to mark the thing next
;; - `aya-expand' to expand snippet
;; - `aya-open-line' to finish
(global-set-key (kbd "C-q") #'aya-open-line)
;; }}

;; open header file under cursor
(global-set-key (kbd "C-x C-o") 'ffap)

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
              compilation-scroll-output 'first-error
              ediff-split-window-function 'split-window-horizontally
              ediff-window-setup-function 'ediff-setup-windows-plain
              grep-highlight-matches t
              grep-scroll-output t
              indent-tabs-mode nil
              line-spacing 0
              mouse-yank-at-point t
              set-mark-command-repeat-pop t
              tooltip-delay 1.5
              ;; avoid problems with crontab, etc.
              ;; require-final-newline t ; bad idea, could accidentally edit others' code
              truncate-lines nil
              truncate-partial-width-windows nil
              ;; visible-bell has some issue
              ;; @see https://github.com/redguardtoo/mastering-emacs-in-one-year-guide/issues/9#issuecomment-97848938
              visible-bell nil)

;; @see http://www.emacswiki.org/emacs/SavePlace
(save-place-mode 1)

;; {{ find-file-in-project (ffip)
(with-eval-after-load 'find-file-in-project
  (defun my-search-git-reflog-code ()
    (let* ((default-directory (my-git-root-dir)))
      (shell-command-to-string (format "git --no-pager reflog --date=short -S\"%s\" -p"
                                            (read-string "Regex: ")))))
  (push 'my-search-git-reflog-code ffip-diff-backends)
  (setq ffip-match-path-instead-of-filename t))

(defun my-neotree-project-dir ()
  "Open NeoTree using the git root."
  (interactive)
  (let* ((project-dir (ffip-get-project-root-directory))
         (file-name (buffer-file-name)))
    (if project-dir
        (progn
          (neotree-dir project-dir)
          (neotree-find file-name))
      (message "Could not find git project root."))))
;; }}

;; {{ dictionary setup
(defun my-lookup-dict-org ()
  "Look up word in dict.org."
  (interactive)
  (let* ((word (my-use-selected-string-or-ask "Input word for dict.org:")))
    (when word
      (dictionary-new-search (cons word
                                   dictionary-default-dictionary)))))
;; }}

(defun my-lookup-doc-in-man ()
  "Read man by querying keyword at point."
  (interactive)
  (man (concat "-k " (my-use-selected-string-or-ask))))

;; @see http://redguardtoo.github.io/posts/effective-code-navigation-for-web-development.html
;; don't let the cursor go into minibuffer prompt
(setq minibuffer-prompt-properties
      (quote (read-only t point-entered minibuffer-avoid-prompt face minibuffer-prompt)))

(global-set-key (kbd "M-x") 'counsel-M-x)

;; hide the compilation buffer automatically is not a good idea.
;; if compiling command is a unit test command
;; It's better let user decide when to hide something
(defvar my-do-bury-compilation-buffer nil
  "Hide compilation buffer if compile successfully.")

(defun my-compilation-finish-hide-buffer-on-success (buffer str)
  "Bury BUFFER whose name marches STR.
This function can be re-used by other major modes after compilation."
  (cond
   ;;there were errors
   ((string-match "exited abnormally" str)
    (message "There IS compilation errors, press C-x ` to visit!"))

   ;;no errors, make the compilation window go away in 0.5 seconds
   (t
    (when (and my-do-bury-compilation-buffer
               (buffer-name buffer)
               (string-match "*compilation*" (buffer-name buffer)))
      ;; @see http://emacswiki.org/emacs/ModeCompile#toc2
      (bury-buffer "*compilation*")
      (winner-undo)
      (message "NO compilation error.")))))

;; {{ electric pair
(defun my-normal-word-before-point-p (position n fn)
  "A normal word exists before POSITION.
N characters before current point is checked.
FN checks these characters belong to normal word characters."
  (save-excursion
    (goto-char position)
    ;; sample N characters before POSITION
    (let* ((rlt t)
           (i 0))
      (while (and (< i n) rlt)
        (let* ((c (char-before (- (point) i))))
          (when (not (and c (funcall fn c)))
            (setq rlt nil)))
        (setq i (1+ i)))
      rlt)))

(defun my-electric-pair-inhibit (char)
  "Customize electric pair when input CHAR."
  (let* (rlt
         (quote-chars '(34 39))
         (word-fn (lambda (c)
                    (or (and (<= ?a c) (<= c ?z))
                        (and (<= ?A c) (<= c ?Z))
                        (and (<= ?0 c) (<= c ?9))))))
    (cond
     ((and (memq major-mode '(minibuffer-inactive-mode))
           (not (string-match "^Eval:" (buffer-string))))
      (setq rlt t))

     ;; Don't insert extra single/double quotes at the end of word
     ;; Also @see https://github.com/redguardtoo/emacs.d/issues/892#issuecomment-740259242
     ((and (memq (char-before (point)) quote-chars)
           (my-normal-word-before-point-p (1- (point)) 4 word-fn))
      (setq rlt t))

     (t
      (setq rlt (electric-pair-default-inhibit char))))

    rlt))

(with-eval-after-load 'elec-pair
  ;; {{ @see https://debbugs.gnu.org/cgi/bugreport.cgi?bug=55340
  ;; `new-line-indent` disables `electric-indent-mode'
  (defun my-electric-pair-open-newline-between-pairs-psif-hack (orig-func &rest args)
    (ignore orig-func args)
    (when (and (if (functionp electric-pair-open-newline-between-pairs)
                   (funcall electric-pair-open-newline-between-pairs)
                 electric-pair-open-newline-between-pairs)
               (eq last-command-event ?\n)
               (< (1+ (point-min)) (point) (point-max))
               (eq (save-excursion
                     (skip-chars-backward "\t\s")
                     (char-before (1- (point))))
                   (matching-paren (char-after))))
      (save-excursion (newline-and-indent 1))))
  (advice-add 'electric-pair-open-newline-between-pairs-psif
              :around
              #'my-electric-pair-open-newline-between-pairs-psif-hack)
  ;; }}
  (setq electric-pair-inhibit-predicate 'my-electric-pair-inhibit))
;; }}

(defvar my-disable-lazyflymake nil
  "Disable lazyflymake.")

;; {{
(defvar my-save-run-timer nil "Internal timer.")

(defvar my-save-run-rules nil
  "Rules to execute shell command when saving.
In each rule, 1st item is default directory, 2nd item is the shell command.")

(defvar my-save-run-interval 4
  "The interval (seconds) to execute shell command.")

(defun my-save-run-function ()
  "Run shell command in `after-save-hook'."
  (interactive)
  (cond
   ((or (not my-save-run-timer)
        (> (- (float-time (current-time)) (float-time my-save-run-timer))
           my-save-run-interval))

    ;; start timer if not started yet
    (setq my-save-run-timer (current-time))

    ;; start updating
    (when buffer-file-name
      (dolist (rule my-save-run-rules)
        (let* ((default-directory (nth 0 rule))
               (cmd (nth 1 rule)))
          (when (string-match (concat "^" (file-truename default-directory)) buffer-file-name)
            (my-async-shell-command cmd))))))
   (t
    ;; do nothing, can't run ctags too often
    )))
;; }}

(add-hook 'text-mode-hook #'lazyflymake-start)

;;; {{ display long lines in truncated style (end line with $)
(defun my-truncate-lines-setup ()
  (toggle-truncate-lines 1))
(add-hook 'grep-mode-hook 'my-truncate-lines-setup)
;; }}

;; turn on auto-fill-mode, don't use `text-mode-hook' because for some
;; mode (org-mode for example), this will make the exported document
;; ugly!
;; (add-hook 'markdown-mode-hook 'turn-on-auto-fill)
(add-hook 'change-log-mode-hook 'turn-on-auto-fill)
(add-hook 'cc-mode-hook 'turn-on-auto-fill)

;; some project prefer tab, so be it
;; @see http://stackoverflow.com/questions/69934/set-4-space-indent-in-emacs-in-text-mode
(setq-default tab-width 4)

(setq history-delete-duplicates t)

;; NO automatic new line when scrolling down at buffer bottom
(setq next-line-add-newlines nil)

;; @see http://stackoverflow.com/questions/4222183/emacs-how-to-jump-to-function-definition-in-el-file
(global-set-key (kbd "C-h C-f") 'find-function)

(with-eval-after-load 'time
  ;; If you want to customize time format, read document of `format-time-string'
  ;; and customize `display-time-format'.
  ;; (setq display-time-format "%a %b %e")
  (setq display-time-24hr-format t) ; the date in modeline is English too, magic!
  (setq display-time-day-and-date t))
(my-run-with-idle-timer 2 #'display-time)

(defalias 'list-buffers 'ibuffer)

(defun my-add-pwd-into-load-path ()
  "Add current directory into `load-path', useful for elisp developers."
  (interactive)
  (let* ((dir (expand-file-name default-directory)))
    (if (not (memq dir load-path))
        (add-to-list 'load-path dir))
    (message "Directory added into load-path:%s" dir)))

(setq system-time-locale "C")

(setq imenu-max-item-length 256)

;; {{ recentf-mode
(setq recentf-max-saved-items 2048
      recentf-exclude '("/tmp/"
                        ;; "/ssh:"
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
                        "\\.wav$"
                        "\\.docx?$"
                        "\\.xlsx?$"
                        ;; sub-titles
                        "\\.sub$"
                        "\\.srt$"
                        "\\.ass$"
                        ;; "/home/[a-z]\+/\\.[a-df-z]" ; configuration file should not be excluded
                        ))
;; }}

;; {{ popup functions
(defun my-which-function ()
  "Return current function name."
  ;; @see http://stackoverflow.com/questions/13426564/how-to-force-a-rescan-in-imenu-by-a-function
  ;; clean the imenu cache
  (my-rescan-imenu-items (if (my-use-tags-as-imenu-function-p)
                      'counsel-etags-imenu-default-create-index-function
                    imenu-create-index-function))
  (which-function))

(defun popup-which-function ()
  "Popup which function message."
  (interactive)
  (let* ((msg (my-which-function)))
    (when msg
      (popup-tip msg)
      (copy-yank-str msg))))
;; }}

;; {{ music
(defun mpc-which-song ()
  "Copy mpc song's name."
  (interactive)
  (let* ((msg (car (my-nonempty-lines (shell-command-to-string "mpc")))))
    (message msg)
    (copy-yank-str msg)))

(defun mpc-next-prev-song (&optional previous)
  "Select PREVIOUS song if it's not nil; or else select next song."
  (interactive)
  (message (car (my-nonempty-lines (shell-command-to-string
                                 (concat "mpc "
                                         (if previous "prev" "next")))))))
;; }}

;; ANSI-escape coloring in compilation-mode
;; {{ http://stackoverflow.com/questions/13397737/ansi-coloring-in-compilation-mode
(ignore-errors
  (defun my-colorize-compilation-buffer ()
    (when (eq major-mode 'compilation-mode)
      (my-ensure 'ansi-color)
      (ansi-color-apply-on-region compilation-filter-start (point-max))))
  (add-hook 'compilation-filter-hook 'my-colorize-compilation-buffer))
;; }}

(defun my-minibuffer-setup-hook ()
  "Set up mini buffer."
  (local-set-key (kbd "M-y") 'paste-from-x-clipboard)
  (local-set-key (kbd "C-k") 'kill-line)
  (subword-mode 1) ; enable sub-word movement in minibuffer
  (setq gc-cons-threshold most-positive-fixnum))

(defun my-minibuffer-exit-hook ()
  "Hook when exiting mini buffer."
  ;; evil-mode also use mini buffer
  (setq gc-cons-threshold 67108864))

;; @see http://bling.github.io/blog/2016/01/18/why-are-you-changing-gc-cons-threshold/
(add-hook 'minibuffer-setup-hook #'my-minibuffer-setup-hook)
(add-hook 'minibuffer-exit-hook #'my-minibuffer-exit-hook)

;; {{ cliphist.el
(defun my-select-cliphist-item (num item)
  "NUM is ignored.  Paste selected clipboard ITEM into clipboard.
So it's at the top of clipboard manager."
  (ignore num)
  (my-pclip item))
(setq cliphist-select-item-callback 'my-select-cliphist-item)
;; }}

(defun my-extract-list-from-package-json ()
  "Extract package list from package.json."
  (interactive)
  (let* ((str (my-use-selected-string-or-ask)))
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
  "Toggle indentation."
  (interactive)
  (setq indent-tabs-mode (not indent-tabs-mode))
  (message "indent-tabs-mode=%s" indent-tabs-mode))

;; {{ csv
(setq csv-separators '("," ";" "|" " "))
;; }}

;; {{ regular expression tools
(defun my-create-regex-from-kill-ring (&optional n)
  "Create extended regex from first N items of `kill-ring'."
  (interactive "p")
  (when (and kill-ring (> (length kill-ring) 0))
    (if (> n (length kill-ring))
        (setq n (length kill-ring)))
    (let* ((rlt (mapconcat 'identity (cl-subseq kill-ring 0 n) "|")))
      (setq rlt (replace-regexp-in-string "(" "\\\\(" rlt))
      (copy-yank-str rlt)
      (message (format "%s => kill-ring&clipboard" rlt)))))
;; }}


;; {{ emmet (auto-complete html tags)
;; @see https://github.com/rooney/zencoding for original tutorial
;; @see https://github.com/smihica/emmet for new tutorial
;; C-j or C-return to expand the line
(add-hook 'sgml-mode-hook 'emmet-mode) ; `sgml-mode` is parent of `html-mode'
(add-hook 'web-mode-hook 'emmet-mode)
(add-hook 'css-mode-hook  'emmet-mode)
(add-hook 'rjsx-mode-hook  'emmet-mode)
;; }}

(defun sgml-mode-hook-setup ()
  "Sgml/html mode setup."
  ;; let `web-mode' handle indentation by itself..
  ;; It does not derives from `sgml-mode'.
  (setq-local indent-region-function 'sgml-pretty-print))
(add-hook 'sgml-mode-hook 'sgml-mode-hook-setup)


;; {{ xterm
(defun my-run-after-make-frame-hook (frame)
  "Hook after create new FRAME."
  (select-frame frame)
  (unless window-system
    ;; Mouse in a terminal (Use shift to paste with middle button)
    (xterm-mouse-mode 1)))
(add-hook 'after-make-frame-functions 'my-run-after-make-frame-hook)
;; }}

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
      (let* (search-result)
        (while
            (and (setq search-result (re-search-forward "\\(attach\\|pdf\\|file\\|screen ?shot\\)" nil t))
                 (my-message-current-line-cited-p)))
        search-result))))

(defun my-message-has-attachment-p ()
  "Return t if an attachment is already attached to the message."
  (save-excursion
    (goto-char (point-min))
    (save-match-data
      (re-search-forward "<#part" nil t))))

(defun my-message-pre-send-check-attachment ()
  "Check attachment before send mail."
  (when (and (my-message-says-attachment-p)
             (not (my-message-has-attachment-p)))
    (unless
        (y-or-n-p "The message suggests that you may want to attach something, but no attachment is found.  Send anyway?")
      (error "It seems that an attachment is needed, but none was found.  Aborting sending!"))))
(add-hook 'message-send-hook 'my-message-pre-send-check-attachment)

;; }}

;; @see https://stackoverflow.com/questions/3417438/closing-all-other-buffers-in-emacs
(defun my-kill-all-but-current-buffer ()
  "Kill all other buffers, but not current buffer."
  (interactive)
  (mapc 'kill-buffer (cdr (buffer-list (current-buffer))))
  "All other buffers have been killed!")

(defun my-minibuffer-inactive-mode-hook-setup ()
  "Set up mini buffer so auto complete works."
  ;; Make `try-expand-dabbrev' from `hippie-expand' work in mini-buffer.
  ;; @see `he-dabbrev-beg', so we need re-define syntax for '/'.
  (set-syntax-table (let* ((table (make-syntax-table)))
                      (modify-syntax-entry ?/ "." table)
                      table)))
(add-hook 'minibuffer-inactive-mode-hook 'my-minibuffer-inactive-mode-hook-setup)

;; {{ vc-msg
(defun vc-msg-hook-setup (vcs-type commit-info)
  "Set up vc with VCS-TYPE and COMMIT-INFO."
  ;; copy commit id to clipboard
  (ignore vcs-type)
  (my-pclip (plist-get commit-info :id)))
(add-hook 'vc-msg-hook 'vc-msg-hook-setup)

(defun vc-msg-show-code-setup ()
  "Use `ffip-diff-mode' instead of `diff-mode'."
  (my-ensure 'find-file-in-project)
  (ffip-diff-mode))
(add-hook 'vc-msg-show-code-hook 'vc-msg-show-code-setup)
;; }}

;; {{
(defun my-toggle-typewriter ()
  "Turn on/off typewriter."
  (interactive)
  (if (bound-and-true-p typewriter-mode)
      (typewriter-mode -1)
    (typewriter-mode 1)))
;; }}

(with-eval-after-load 'grep
  ;; eacl and other general grep (rgrep, grep ...) setup
  (dolist (v '("auto"
               "target"
               "node_modules"
               "bower_components"
               "*dist"
               ".sass_cache"
               ".cache"
               ".npm"
               "elpa"))
    (add-to-list 'grep-find-ignored-directories v))
  (dolist (v '("*.min.js"
               "*.map"
               "*.bundle.js"
               "*.min.css"
               "tags"
               "TAGS"
               "GTAGS"
               "GRTAGS"
               "GPATH"
               "cscope.files"
               "*.json"
               "*.log"))
    (add-to-list 'grep-find-ignored-files v))

  ;; wgrep and rgrep, inspired by http://oremacs.com/2015/01/27/my-refactoring-workflow/
  (define-key grep-mode-map
    (kbd "C-x C-q") 'wgrep-change-to-wgrep-mode))

(defun my-wgrep-mark-deletion-hack (&optional arg)
  "After mark a line for deletion, move to next line.
ARG is ignored."
  (ignore arg)
  (forward-line))
(advice-add 'wgrep-mark-deletion :after #'my-wgrep-mark-deletion-hack)

;; wgrep and rgrep, inspired by http://oremacs.com/2015/01/27/my-refactoring-workflow/
(with-eval-after-load 'wgrep
  '(define-key grep-mode-map
     (kbd "C-c C-c") 'wgrep-finish-edit))

;; {{ https://www.emacswiki.org/emacs/EmacsSession better than "desktop.el" or "savehist".
;; Any global variable matching `session-globals-regexp' is saved *automatically*.
(setq session-save-file (expand-file-name (concat my-emacs-d ".session")))
(setq session-globals-max-size 2048)
;; can store 8Mb string
(setq session-globals-max-string (* 8 1024 1024))
(setq session-globals-include '(kill-ring
                                (session-file-alist 100 t)
                                my-dired-commands-history
                                file-name-history
                                search-ring
                                regexp-search-ring))
(setq session-save-file-coding-system 'utf-8)
(add-hook 'after-init-hook 'session-initialize)
;; }}

;; {{
(defun adoc-imenu-index ()
  "Set up imenu for `adoc-mode'."
  (let* ((patterns '((nil "^=\\([= ]*[^=\n\r]+\\)" 1))))
    (save-excursion
      (imenu--generic-function patterns))))

(defun adoc-mode-hook-setup ()
  "Set up `adoc-mode'."
  ;; Don't wrap lines because there is table in `adoc-mode'.
  (setq truncate-lines t)
  (setq imenu-create-index-function 'adoc-imenu-index))
(add-hook 'adoc-mode-hook 'adoc-mode-hook-setup)
;; }}

(with-eval-after-load 'compile
  (defun my-compile-hack (orig-func &rest args)
    (cond
     ((member major-mode '(octave-mode))
      (octave-send-buffer))
     (t
      (apply orig-func args))))
  (advice-add 'compile :around #'my-compile-hack)

  (add-to-list 'compilation-error-regexp-alist-alist
               (list 'mocha "at [^()]+ (\\([^:]+\\):\\([^:]+\\):\\([^:]+\\))" 1 2 3))
  (add-to-list 'compilation-error-regexp-alist 'mocha))

(defun my-switch-to-builtin-shell ()
  "Switch to builtin shell.
If the shell is already opened in some buffer, switch to that buffer."
  (interactive)
  (let* ((buf-name (if *win64* "*shell*" "*ansi-term*"))
         (buf (get-buffer buf-name))
         (wins (window-list))
         current-frame-p)

    (cond
     ;; A shell buffer is already opened
     ((buffer-live-p buf)
      (dolist (win wins)
        (when (string= (buffer-name (window-buffer win)) buf-name)
          (when (window-live-p win)
            (setq current-frame-p t)
            (select-window win))))
      (unless current-frame-p
        (switch-to-buffer buf)))
     ;; Windows
     (*win64*
      (shell))
     ;; Linux
     (t
      (ansi-term my-term-program)))))

(transient-mark-mode t)

(unless (or *cygwin* *win64*)
  ;; Takes ages to start Emacs.
  ;; Got error `Socket /tmp/fam-cb/fam- has wrong permissions` in Cygwin ONLY!
  ;; reproduced with Emacs 26.1 and Cygwin upgraded at 2019-02-26
  ;;
  ;; Although win64 is fine. It still slows down generic performance.
  ;; @see https://stackoverflow.com/questions/3589535/why-reload-notification-slow-in-emacs-when-files-are-modified-externally
  ;; So no auto-revert-mode on Windows/Cygwin
  (setq auto-revert-verbose nil)
  (my-run-with-idle-timer 4 #'global-auto-revert-mode))

;;----------------------------------------------------------------------------
;; Don't disable narrowing commands
;;----------------------------------------------------------------------------
(put 'narrow-to-region 'disabled nil)
(put 'narrow-to-page 'disabled nil)
(put 'narrow-to-defun 'disabled nil)

;; my screen is tiny, so I use minimum eshell prompt
(with-eval-after-load 'eshell
  (setq eshell-prompt-function
        (lambda ()
          (concat (getenv "USER") " $ "))))

(defun my-insert-date ()
  "Insert current date."
  (interactive)
  (insert (format-time-string "%Y-%m-%d")))

;; compute the length of the marked region
(defun my-region-length ()
  "Length of a selected region."
  (interactive)
  (message (format "%d" (- (region-end) (region-beginning)))))

;; show ascii table
(defun my-ascii-table ()
  "Print the ascii table."
  (interactive)
  (switch-to-buffer "*ASCII*")
  (erase-buffer)
  (insert (format "ASCII characters up to number %d.\n" 254))
  (let* ((i 0))
    (while (< i 254)
      (setq i (+ i 1))
      (insert (format "%4d %c\n" i i))))
  (goto-char (point-min)))

;; {{ unique lines
;; https://gist.github.com/ramn/796527
;; uniq-lines
(defun my-uniq-lines (start end)
  "Unique line of select region from START to END."
  (interactive "*r")
  (delete-duplicate-lines start end))
;; }}

(defun my-insert-file-link-from-clipboard ()
  "Make sure the full path of file exist in clipboard.
This command will convert full path into relative path.
Then insert it as a local file link in `org-mode'."
  (interactive)
  (insert (format "[[file:%s]]" (file-relative-name (my-gclip)))))

(defun my-dired-copy-filename-as-kill-hack (&optional arg)
  "Copy file name/path from Dired buffer into clipboard.
If ARG is not nil, copy full path.
Press \"w\" to copy file name.
Press \"C-u 0 w\" to copy full path."
  (ignore arg)
  (let ((str (current-kill 0)))
    (my-pclip str)
    (message "%s => clipboard" str)))
(advice-add 'dired-copy-filename-as-kill :after #'my-dired-copy-filename-as-kill-hack)

;; from http://emacsredux.com/blog/2013/05/04/rename-file-and-buffer/
(defun my-vc-rename-file-and-buffer ()
  "Rename the current buffer and file it is visiting."
  (interactive)
  (let* ((filename (buffer-file-name)))
    (cond
     ((not (and filename (file-exists-p filename)))
      (message "Buffer is not visiting a file!"))
     (t
      (let* ((new-name (read-file-name "New name: " filename)))
        (cond
         ((vc-backend filename) (vc-rename-file filename new-name))
         (t
          (rename-file filename new-name t)
          (rename-buffer new-name)
          (set-visited-file-name new-name)
          (set-buffer-modified-p nil))))))))

(defun my-vc-copy-file-and-rename-buffer ()
  "Copy the current buffer and file it is visiting.
If the old file is under version control, the new file is added into
version control automatically."
  (interactive)
  (let* ((filename (buffer-file-name)))
    (cond
     ((not (and filename (file-exists-p filename)))
      (message "Buffer is not visiting a file!"))
     (t
      (let* ((new-name (read-file-name "New name: " filename)))
        (copy-file filename new-name t)
        (rename-buffer new-name)
        (set-visited-file-name new-name)
        (set-buffer-modified-p nil)
        (when (vc-backend filename)
          (vc-register)))))))

(defun my-toggle-env-http-proxy ()
  "Set/unset the environment variable http_proxy used by browser."
  (interactive)
  (let* ((proxy "http://127.0.0.1:8000"))
    (cond
     ((string= (getenv "http_proxy") proxy)
      (setenv "http_proxy" "")
      (message "env http_proxy is empty now"))
     (t
      (setenv "http_proxy" proxy)
      (message "env http_proxy is %s now" proxy)))))

;; Don't disable narrowing commands
(put 'narrow-to-region 'disabled nil)
(put 'narrow-to-page 'disabled nil)
(put 'narrow-to-defun 'disabled nil)

;; Ctrl-X, u/l  to upper/lowercase regions without confirm
(put 'downcase-region 'disabled nil)
(put 'upcase-region 'disabled nil)

;; midnight mode purges buffers which haven't been displayed in 3 days
(my-run-with-idle-timer 4 #'midnight-mode)

(defun cleanup-buffer-safe ()
  "Perform a bunch of safe operations on the whitespace content of a buffer.
Does not indent buffer, because it is used for a `before-save-hook', and that
might be bad."
  (interactive)
  (untabify (point-min) (point-max))
  (delete-trailing-whitespace))

;; {{ easygpg setup
;; @see http://www.emacswiki.org/emacs/EasyPG#toc4
(with-eval-after-load 'epg
  (defun my-epg--start-hack (orig-func &rest args)
    "Make `epg--start' not able to find gpg-agent."
    (let* ((agent (getenv "GPG_AGENT_INFO")))
      (setenv "GPG_AGENT_INFO" nil)
      (apply orig-func args)
      (setenv "GPG_AGENT_INFO" agent)))
  (advice-add 'epg--start :around #'my-epg--start-hack)

  (unless (string-match "^gpg (GnuPG) 1.4"
                          (shell-command-to-string (format "%s --version" epg-gpg-program)))

    ;; "apt-get install pinentry-tty" if using emacs-nox
    ;; Create `~/.gnupg/gpg-agent.conf' which has one line
    ;; "pinentry-program /usr/bin/pinentry-curses"
    (setq epa-pinentry-mode 'loopback)))
;; }}

(with-eval-after-load 'pomodoro
  (setq pomodoro-play-sounds nil) ; *.wav is not installed
  (setq pomodoro-break-time 2)
  (setq pomodoro-long-break-time 5)
  (setq pomodoro-work-time 15)
  ;; Instead of calling `pomodoro-add-to-mode-line`
  (push '(pomodoro-mode-line-string pomodoro-mode-line-string) mode-line-format))

;; {{ epub setup
(defun nov-mode-hook-setup ()
  "Set up of `nov-mode'."
  (local-set-key (kbd "d")
		 (lambda ()
		   (interactive)
		   ;; go to end of word to workaround `nov-mode' bug
		   (forward-word)
		   (forward-char -1)
		   (my-dict-complete-definition)))
  (local-set-key (kbd ";") 'my-hydra-ebook/body)
  (local-set-key (kbd "w") 'mybigword-big-words-in-current-window))
(add-hook 'nov-mode-hook 'nov-mode-hook-setup)
;; }}

;; {{ octave
(defun octave-mode-hook-setup ()
  "Set up of `octave-mode'."
  (setq-local comment-start "%")
  (setq-local comment-add 0))
(add-hook 'octave-mode-hook 'octave-mode-hook-setup)
;; }}

;; {{ wgrep setup
(with-eval-after-load 'wgrep
  ;; save the change after wgrep finishes the job
  (setq wgrep-auto-save-buffer t)
  (setq wgrep-too-many-file-length 2024))
;; }}

(defun my-browse-file (file)
  "Browse FILE as url using `browse-url'."
  (when (and file (file-exists-p file))
    (browse-url-generic (concat "file://" file))))

(defun my-browse-current-file ()
  "Browse current file."
  (interactive)
  (my-browse-file buffer-file-name))

(defun my-browse-current-file-as-html ()
  "Browse current file as html."
  (interactive)
  (cond
   ((or (not buffer-file-name)
        (not (file-exists-p buffer-file-name))
        (not (string-match "html?$" buffer-file-name)))
    (let* ((file (make-temp-file "my-browse-file-" nil ".html")))
      (my-write-to-file (format "<html><body>%s</body></html>" (buffer-string)) file)
      (my-browse-file file)
      (my-run-with-idle-timer 4 (lambda () (delete-file file)))))
   (t
    (my-browse-file buffer-file-name))))

;; {{ which-key-mode
(defvar my-show-which-key-when-press-C-h nil)
(with-eval-after-load 'which-key
  (setq which-key-allow-imprecise-window-fit t) ; performance
  (setq which-key-separator ":")
  (setq which-key-idle-delay 1.5)
  (when my-show-which-key-when-press-C-h
    ;; @see https://twitter.com/bartuka_/status/1327375348959498240?s=20
    ;; Therefore, the which-key pane only appears if I hit C-h explicitly.
    ;; C-c <C-h> for example - by Wanderson Ferreira
    (setq which-key-idle-delay 10000)
    (setq which-key-show-early-on-C-h t))
  (setq which-key-idle-secondary-delay 0.05))
(my-run-with-idle-timer 2 #'which-key-mode)
;; }}

;; {{ Answer Yes/No automatically when asked by `y-or-n-p'
(defvar my-default-yes-no-answers nil
    "Usage: (setq my-default-yes-no-answers '((t . \"question1\") (t . \"question2\")))).")
(defun my-y-or-n-p-hack (orig-func &rest args)
  "Answer yes or no automatically for some questions with ORIG-FUNC and ARGS."
  (let* ((prompt (car args))
         rlt)
    (cond
     ((and my-default-yes-no-answers
           (listp my-default-yes-no-answers))
      (let* ((i 0) found cand)
        (while (and (setq cand (nth i my-default-yes-no-answers))
                    (not found))
          (when (string-match (cdr cand) prompt)
            (setq found t)
            (setq rlt (car cand)))
          (setq i (1+ i)))
        (unless found (setq rlt (apply orig-func args)))))
     (t
      (setq rlt (apply orig-func args))))
    rlt))
(advice-add 'y-or-n-p :around #'my-y-or-n-p-hack)
;; }}

;; {{ eldoc
(with-eval-after-load 'eldoc
  ;; multi-line message should not display too soon
  (setq eldoc-idle-delay 1)
  (setq eldoc-echo-area-use-multiline-p t))
;;}}

;; {{ use dictionary to find big word definition
(defvar my-dict-org-head-level 2)
(defun my-dict-format-bigword (word zipf)
  "Format WORD and ZIPF."
  (let* (rlt def)
    (local-require 'stardict)
    ;; 2 level org format
    (condition-case nil
        (progn
          (setq def (my-dict-search-detail word my-dict-complete my-dict-complete-cache))
          (setq def (replace-regexp-in-string "^-->.*" "" def))
          (setq def (replace-regexp-in-string "[\n\r][\n\r]+" "" def))
          (setq rlt (format "%s %s (%s)\n%s\n"
                            (make-string my-dict-org-head-level ?*)
                            word
                            zipf
                            def)))
      (error nil))
    rlt))

(defun my-lookup-bigword-definition-in-buffer ()
  "Look up big word definitions."
  (interactive)
  (local-require 'mybigword)
  (let* ((mybigword-default-format-function 'my-dict-format-bigword))
    (mybigword-show-big-words-from-current-buffer)))
;; }}

;; ;; {{ use pdf-tools to view pdf
;; (when (and (display-graphic-p) *linux*)
;;   (pdf-loader-install))
;; ;; }}


;; {{ markdown
(defun markdown-mode-hook-setup ()
  "Set up markdown."
  ;; makes markdown tables saner via `orgtbl-mode'
  ;; Stolen from http://stackoverflow.com/a/26297700
  ;; Insert org table and it will be automatically converted
  ;; to markdown table
  (my-ensure 'org-table)
  (defun cleanup-org-tables ()
    (save-excursion
      (goto-char (point-min))
      (while (search-forward "-+-" nil t) (replace-match "-|-"))))
  (add-hook 'after-save-hook 'cleanup-org-tables nil 'make-it-local)
  (orgtbl-mode 1) ; enable key bindings
  ;; don't wrap lines because there is table in `markdown-mode'
  (setq truncate-lines t))
(add-hook 'markdown-mode-hook 'markdown-mode-hook-setup)
;; }}

;; {{ pdf
(defun my-open-pdf-from-history ()
  "Open pdf and go to page from history."
  (interactive)
  (let* ((link (completing-read "Open pdf:::page: " my-pdf-view-from-history)))
    (when link
      (let* ((items (split-string link ":::"))
             (pdf-page (string-to-number (nth 1 items))))
        (my-ensure 'org)
        (my-focus-on-pdf-window-then-back
         (lambda (pdf-file)
           (when (string= (file-name-base pdf-file) (file-name-base pdf-file))
             (my-pdf-view-goto-page pdf-page))))))))

(defun my-open-pdf-scroll-or-next-page (&optional n)
  "Open pdf, scroll or go to next N page."
  (interactive "p")
  (my-focus-on-pdf-window-then-back
   (lambda (pdf-file)
     (ignore pdf-file)
     (pdf-view-scroll-up-or-next-page n))))

(defun my-open-pdf-scroll-or-previous-page (&optional n)
  "Open pdf, scroll or go to previous N page."
  (interactive "p")
  (my-focus-on-pdf-window-then-back
   (lambda (pdf-file)
     (ignore pdf-file)
     (pdf-view-scroll-down-or-previous-page n))))

(defun my-open-pdf-next-page (&optional n)
  "Open pdf, go to next N page."
  (interactive "p")
  (my-focus-on-pdf-window-then-back
   (lambda (pdf-file)
     (ignore pdf-file)
     (pdf-view-next-page n))))

(defun my-open-pdf-previous-page (&optional n)
  "Open pdf, go to previous N page."
  (interactive "p")
  (my-focus-on-pdf-window-then-back
   (lambda (pdf-file)
     (ignore pdf-file)
     (pdf-view-previous-page n))))

(defun my-open-pdf-goto-page (&optional n)
  "Open pdf and go to page N.
Org node property PDF_PAGE_OFFSET is used to calculate physical page number."
  (interactive "p")
  (let* ((page-offset (org-entry-get (point) "PDF_PAGE_OFFSET")))
    (setq page-offset (if page-offset (string-to-number page-offset) 0))
    (unless n (setq n 1))
    (setq n (+ n page-offset))
    (my-focus-on-pdf-window-then-back
     (lambda (pdf-file)
       (ignore pdf-file)
       (pdf-view-goto-page n)))))

(defun my-navigate-in-pdf ()
  "Navigate in PDF."
  (interactive)
  (my-setup-extra-keymap '(("k" my-open-pdf-scroll-or-previous-page)
                           ("j" my-open-pdf-scroll-or-next-page)
                           ("p" my-open-pdf-previous-page)
                           ("n" my-open-pdf-next-page)
                           ("g" (my-open-pdf-goto-page (read-number "Page number: " 1)))
                           ("f" my-open-pdf-from-history))
                         "PDF: [k]up [j]down [p]revious-page [n]ext-page [g]oto [f]rom-history [q]uit"
                         nil))
;; }}

;; {{ count words
(setq wc-idle-wait most-positive-fixnum)
;; minor mode sets up hotkey&modeline&timer
;; I don't use any of them
(unless (featurep 'init-modeline) (add-hook 'text-mode-hook 'wc-mode))

(defvar my-lazy-before-save-timer nil "Timer for `before-save-hook'.")
(defvar  my-lazy-before-save-update-interval 16
  "The interval (seconds) routines happen in `before-save-hook'.")
(defun lazy-before-save-hook-setup ()
  "Do something when saving current buffer.
It's also controlled by `my-lazy-before-save-timer'."
  (when (or (not my-lazy-before-save-timer)
            (> (- (float-time (current-time)) (float-time my-lazy-before-save-timer))
               my-lazy-before-save-update-interval))
    (setq my-lazy-before-save-timer (current-time))
    ;; do something
    (when (derived-mode-p 'text-mode)
      (my-ensure 'wc-mode)
      (setq wc-buffer-stats (wc-mode-update))
      (when (featurep 'init-modeline)
        (setq my-extra-mode-line-info wc-buffer-stats)))))
(add-hook 'before-save-hook 'lazy-before-save-hook-setup)
;; }}

(defvar my-gdb-history-file "~/.gdb_history")
(defun gud-gdb-mode-hook-setup ()
  "GDB setup."

  ;; Content of my "~/.gdbinit":
  ;;   set history save on
  ;;   set history filename ~/.gdb_history
  ;;   set history remove-duplicates 2048
  (when (and (ring-empty-p comint-input-ring)
             (file-exists-p my-gdb-history-file))
    (setq comint-input-ring-file-name my-gdb-history-file)
    (comint-read-input-ring t)))
(add-hook 'gud-gdb-mode-hook 'gud-gdb-mode-hook-setup)

;; {{ helpful (https://github.com/Wilfred/helpful)
;; Note that the built-in `describe-function' includes both functions
;; and macros. `helpful-function' is functions only, so we provide
;; `helpful-callable' as a drop-in replacement.
(global-set-key (kbd "C-h f") #'helpful-callable)

(global-set-key (kbd "C-h v") #'helpful-variable)

;; Lookup the current symbol at point. C-c C-d is a common keybinding
;; for this in lisp modes.
(global-set-key (kbd "C-c C-d") #'helpful-at-point)

;; Look up *F*unctions (excludes macros).
;;
;; By default, C-h F is bound to `Info-goto-emacs-command-node'. Helpful
;; already links to the manual, if a function is referenced there.
(global-set-key (kbd "C-h F") #'helpful-function)

;; Look up Commands.
;;
;; By default, C-h C is bound to describe `describe-coding-system'. I
;; don't find this very useful, but it's frequently useful to only
;; look at interactive functions.
(global-set-key (kbd "C-h C") #'helpful-command)

(with-eval-after-load 'counsel
  (setq counsel-describe-function-function #'helpful-callable)
  (setq counsel-describe-variable-function #'helpful-variable))
;; }}

(with-eval-after-load 'yaml-mode
  (setq yaml-imenu-generic-expression
        '((nil  "^\\(:?[0-9a-zA-Z_-]+\\):" 1)
          (nil  "^ *\\([A-Z][0-9A-Z_-]+\\):" 1))))

;; {{ calendar setup
(with-eval-after-load 'calendar
  ;; show holiday marker in calendar
  (setq calendar-mark-holidays-flag t)
  ; show current month's holiday in different window
  (setq calendar-view-holidays-initially-flag t))

(defvar holiday-nsw-holidays
  (mapcar 'purecopy
  '((holiday-fixed  1 26 "NSW: New Year's Day")
    (holiday-fixed  1 26 "NSW: Australia Day")
    (holiday-fixed  4 25 "NSW: ANZAC Day")
    ;; second Monday on June, don't know why the month
    ;; is zero based in `holiday-float'
    (holiday-float  5 1 7 "NSW: Queen's Birthday")
    (holiday-float 9 1 0 "NSW: Labour Day")
    (holiday-fixed 12 25 "NSW: Christmas Day")
    (holiday-fixed 12 26 "NSW: Boxing Day")))
    "NSW public holidays.")

(defun my-china-calendar (&optional arg)
  "Open Chinese Lunar calendar with ARG."
  (interactive "P")
  (unless (featurep 'cal-china-x) (local-require 'cal-china-x))
  (let* ((cal-china-x-important-holidays cal-china-x-chinese-holidays)
         (cal-china-x-general-holidays '((holiday-lunar 1 15 "元宵节")
                                         (holiday-fixed 6 1 "儿童节")
                                         (holiday-lunar 7 7 "七夕节")
                                         (holiday-lunar 9 9 "重阳节")
                                         (holiday-lunar 12 8 "腊八节")))
         (calendar-holidays (append holiday-local-holidays
                                    cal-china-x-important-holidays
                                    cal-china-x-general-holidays)))
    (calendar arg)))
;; }}

(defun my-srt-play-video-at-point ()
  "In srt file, play video from current time stamp.
Emacs 27 is required."
  (interactive)
  (my-ensure 'mybigword)
  (my-ensure 'find-lisp)
  (let* ((str (thing-at-point 'paragraph))
         (regexp  "^\\([0-9]+:[0-9]+:[0-9]+\\),[0-9]+ +-->")
         (start-time (and (string-match regexp str)
                          (match-string 1 str)))
         (videos (find-lisp-find-files-internal
                 "."
                 (lambda (file dir)
                   (and (not (file-directory-p (expand-file-name file dir)))
                        (member (file-name-extension file)
                                my-media-file-extensions)))
                 (lambda (dir parent)
                   (ignore parent)
                   (not (member dir '("." ".." ".git" "sub" "Sub"))))))
         (srt-base-name (file-name-base buffer-file-name)))

    (when srt-base-name
      (setq videos (sort videos `(lambda (a b) (< (string-distance a ,srt-base-name)
                                   (string-distance b ,srt-base-name))))))
    (when (and (> (length videos) 0) start-time)
      ;; plays the matched video
      (mybigword-run-mplayer start-time (car videos)))))

(defun my-srt-offset-subtitles-from-point (seconds)
  "Offset subtitles from point by SECONDS (float, e.g. -2.74).
Continue the video with updated subtitle."
  (interactive "NSeconds to offset (float e.g. -2.74): ")
  (my-ensure 'subtitles)
  (save-excursion
    (save-restriction
      (goto-char (car (bounds-of-thing-at-point 'paragraph)))
      (narrow-to-region (point) (point-max))
      (srt-offset-subtitles seconds)))
  (save-buffer)
  (my-srt-play-video-at-point))

(defvar org-agenda-files)
(defvar org-tags-match-list-sublevels)
(defvar my-org-agenda-files '("~/blog/")
  "My org agenda files.")
(defun my-org-tags-view (&optional match)
  "Show all headlines for org files matching a TAGS criterion.
MATCH is optional tag match."
  (interactive)
  (let* ((org-agenda-files my-org-agenda-files)
         (org-tags-match-list-sublevels nil))
    (org-tags-view nil match)))

(defun my-org-tags-view-food ()
  "Show all headlines for org files matching a TAGS criterion."
  (interactive)
  (my-org-tags-view "food"))

(defun my-today-is-weekend-p ()
  "Test if today is weekend."
  (let ((day (format-time-string "%u")))
    (or (string= day "6") (string= day "7"))))

(defun my-count-items ()
  "Count items separated by SEPARATORS.  White spaces are ignored."
  (interactive)
  (let* ((separators (read-string "Separators (default is \",\"): "))
         (str (string-trim (cond
                            ((region-active-p)
                             (buffer-substring (region-beginning) (region-end)))
                            (t
                             (buffer-string))))))
    (when (equal separators "")
      (setq separators ","))
    (setq str (string-trim str separators separators))
    (message "%s has %d words separated by \"%s\"."
             (if (region-active-p) "Buffer" "Region")
             (length (split-string str separators))
             separators)))

(defun my-mplayer-setup-extra-opts ()
  "Set up `my-mplayer-extra-opts'."
  (interactive)
  (let* ((opts '(("Clockwise 90 degree rotation" . "-vf rotate=1")
                 ("Anticlockwise 90 degree rotation" . "-vf rotate=2")))
         (selected (completing-read "Mplayer setup: " opts)))
    (when selected
      (setq selected (cdr (assoc selected opts)))
      (kill-new selected)
      (message "\"%s\" => kill-ring" selected))))

(defun my-ssh-agent-setup ()
  "Help emacsclient to find ssh-agent setup."
  (when (and (not (getenv "SSH_AGENT_PID"))
             (file-exists-p "~/.ssh/environment"))
    (let* ((str (with-temp-buffer
                  (insert-file-contents "~/.ssh/environment")
                  (buffer-string))))
      (when (string-match "SSH_AGENT_PID=\\([^ ;]+\\);" str)
        (setenv "SSH_AGENT_PID" (match-string 1 str)))
      (when (string-match "SSH_AUTH_SOCK=\\([^ ;]+\\);" str)
        (setenv "SSH_AUTH_SOCK" (match-string 1 str))))))

(defun my-generic-prog-mode-hook-setup ()
  "Generic programming mode set up."
  (when (buffer-too-big-p)
    (when (my-should-use-minimum-resource)
      (font-lock-mode -1)))

  (add-hook 'after-save-hook #'my-save-run-function nil t)

  (my-company-ispell-setup)

  (unless (my-buffer-file-temp-p)
    ;;  trim spaces from end of changed line
    (ws-butler-mode 1)

    (unless (featurep 'esup-child)
      (cond
       ((not my-disable-lazyflymake)
        (my-ensure 'lazyflymake)
        (lazyflymake-start))
       (t
        (flymake-mode 1)))

      (unless my-disable-wucuo
        (my-ensure 'wucuo)
        (setq-local ispell-extra-args (my-detect-ispell-args t))
        (wucuo-start)))

    ;; @see http://xugx2007.blogspot.com.au/2007/06/benjamin-rutts-emacs-c-development-tips.html
    (setq compilation-finish-functions
          '(my-compilation-finish-hide-buffer-on-success))

    ;; fic-mode has performance issue on 5000 line C++, use swiper instead

    ;; don't spell check double words
    (setq-local wucuo-flyspell-check-doublon nil)
    ;; @see http://emacsredux.com/blog/2013/04/21/camelcase-aware-editing/
    (unless (derived-mode-p 'js2-mode)
      (subword-mode 1))

    ;; now css-mode derives from prog-mode
    ;; see the code of `counsel-css-imenu-setup'
    (when (counsel-css-imenu-setup)
      ;; css color
      (rainbow-mode 1)
      (imenu-extra-auto-setup
       ;; post-css mixin
       '(("Function" "^ *@define-mixin +\\([^ ]+\\)" 1)))
      (setq beginning-of-defun-function
            (lambda (arg)
              (ignore arg)
              (let* ((closest (my-closest-imenu-item)))
                (when closest
                  (goto-char (cdr closest)))))))

    (my-run-with-idle-timer 2 (lambda () (electric-pair-mode 1)))

    ;; eldoc, show API doc in minibuffer echo area
    ;; (turn-on-eldoc-mode)
    ;; show trailing spaces in a programming mod
    (setq show-trailing-whitespace t)))
(add-hook 'prog-mode-hook 'my-generic-prog-mode-hook-setup)

(with-eval-after-load 'ellama
  ;; (setq ellama-language "Chinese") ; for translation
  (require 'llm-ollama)
  (setq ellama-provider
        (make-llm-ollama
         :chat-model "deepseek-r1:8b" :embedding-model "deepseek-r1:8b"))
  (setq ellama-instant-display-action-function #'display-buffer-at-bottom))
(add-hook 'org-ctrl-c-ctrl-c-hook #'ellama-chat-send-last-message)

(provide 'init-misc)
;;; init-misc.el ends here
