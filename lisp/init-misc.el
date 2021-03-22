;; -*- coding: utf-8; lexical-binding: t; -*-

;; Avoid potential lag:
;; https://emacs.stackexchange.com/questions/28736/emacs-pointcursor-movement-lag/28746
;; `next-line' triggers the `format-mode-line' which triggers `projectile-project-name'
;; I use find-file-in-project instead of projectile. So I don't have this issue at all.
;; Set `auto-window-vscroll' to nil to avoid triggering `format-mode-line'.
(setq auto-window-vscroll nil)

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
              compilation-scroll-output t
              ediff-split-window-function 'split-window-horizontally
              ediff-window-setup-function 'ediff-setup-windows-plain
              grep-highlight-matches t
              grep-scroll-output t
              indent-tabs-mode nil
              line-spacing 0
              mouse-yank-at-point t
              set-mark-command-repeat-pop t
              tooltip-delay 1.5
              ;; void problems with crontabs, etc.
              ;; require-final-newline t ; bad idea, could accidentally edit others' code
              truncate-lines nil
              truncate-partial-width-windows nil
              ;; visible-bell has some issue
              ;; @see https://github.com/redguardtoo/mastering-emacs-in-one-year-guide/issues/9#issuecomment-97848938
              visible-bell nil)

;; @see http://www.emacswiki.org/emacs/SavePlace
(cond
 ((fboundp 'save-place-mode)
  (save-place-mode 1))
 (t
  (require 'saveplace)
  (setq-default save-place t)))

;; {{ find-file-in-project (ffip)
(with-eval-after-load 'find-file-in-project
  (defun my-search-git-reflog-code ()
    (let* ((default-directory (my-git-root-dir)))
      (ffip-shell-command-to-string (format "git --no-pager reflog --date=short -S\"%s\" -p"
                                            (read-string "Regex: ")))))
  (push 'my-search-git-reflog-code ffip-diff-backends)
  (setq ffip-match-path-instead-of-filename t))

(defun neotree-project-dir ()
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


;; {{ gradle
(defun my-run-gradle-in-shell (cmd)
  (interactive "sEnter a string:")
  (let* ((root-dir (locate-dominating-file default-directory
                                           "build.gradle")))
    (if root-dir
        (let* ((default-directory root-dir))
          (shell-command (concat "gradle " cmd "&"))))))
;; }}

;; {{ dictionary setup
(defun my-lookup-dict-org ()
  (interactive)
  (dictionary-new-search (cons (my-use-selected-string-or-ask "Input word for dict.org:")
                               dictionary-default-dictionary)))
;; }}

;; {{ bookmark
;; use my own bookmark if it exists
(with-eval-after-load 'bookmark
  (if (file-exists-p (file-truename "~/.emacs.bmk"))
      (setq bookmark-file (file-truename "~/.emacs.bmk"))))
;; }}

(defun lookup-doc-in-man ()
  "Read man by querying keyword at point."
  (interactive)
  (man (concat "-k " (my-use-selected-string-or-ask))))

;; @see http://blog.binchen.org/posts/effective-code-navigation-for-web-development.html
;; don't let the cursor go into minibuffer prompt
(setq minibuffer-prompt-properties (quote (read-only t point-entered minibuffer-avoid-prompt face minibuffer-prompt)))

(global-set-key (kbd "M-x") 'counsel-M-x)
(global-set-key (kbd "C-x C-m") 'counsel-M-x)

;; hide the compilation buffer automatically is not a good idea.
;; if compiling command is a unit test command
;; It's better let user decide when to hide something
(defvar my-do-bury-compilation-buffer nil
  "Hide compilation buffer if compile successfully.")

(defun compilation-finish-hide-buffer-on-success (buffer str)
  "Bury BUFFER whose name marches STR.
This function can be re-used by other major modes after compilation."
  (if (string-match "exited abnormally" str)
      ;;there were errors
      (message "compilation errors, press C-x ` to visit")
    ;;no errors, make the compilation window go away in 0.5 seconds
    (when (and my-do-bury-compilation-buffer
               (buffer-name buffer)
               (string-match "*compilation*" (buffer-name buffer)))
      ;; @see http://emacswiki.org/emacs/ModeCompile#toc2
      (bury-buffer "*compilation*")
      (winner-undo)
      (message "NO COMPILATION ERRORS!"))))

(defun my-normal-word-before-point-p (position n fn)
  "A normal word exists before POSITION.  N characters before current point is checked.
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

(with-eval-after-load 'flymake
  (setq flymake-gui-warnings-enabled nil))

(defun generic-prog-mode-hook-setup ()
  (when (buffer-too-big-p)
    ;; Turn off `linum-mode' when there are more than 5000 lines
    (linum-mode -1)
    (when (my-should-use-minimum-resource)
      (font-lock-mode -1)))

  (company-ispell-setup)

  (unless (is-buffer-file-temp)

    (unless (featurep 'esup-child)
      (my-ensure 'lazyflymake)
      (lazyflymake-start)

      (my-ensure 'wucuo)
      (setq-local ispell-extra-args (my-detect-ispell-args t))
      (wucuo-start))

    ;; @see http://xugx2007.blogspot.com.au/2007/06/benjamin-rutts-emacs-c-development-tips.html
    (setq compilation-finish-functions
          '(compilation-finish-hide-buffer-on-success))

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

    (electric-pair-mode 1)

    ;; eldoc, show API doc in minibuffer echo area
    ;; (turn-on-eldoc-mode)
    ;; show trailing spaces in a programming mod
    (setq show-trailing-whitespace t)))

(add-hook 'prog-mode-hook 'generic-prog-mode-hook-setup)

;;; {{ display long lines in truncated style (end line with $)
(defun truncate-lines-setup ()
  (toggle-truncate-lines 1))
(add-hook 'grep-mode-hook 'truncate-lines-setup)
;; (add-hook 'org-mode-hook 'truncate-lines-setup)
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

;; {{ time format
;; If you want to customize time format, read document of `format-time-string'
;; and customize `display-time-format'.
;; (setq display-time-format "%a %b %e")

;; from RobinH, Time management
(setq display-time-24hr-format t) ; the date in modeline is English too, magic!
(setq display-time-day-and-date t)
(my-run-with-idle-timer 2 #'display-time)
;; }}

;;a no-op function to bind to if you want to set a keystroke to null
(defun void () "this is a no-op" (interactive))

(defalias 'list-buffers 'ibuffer)

(defun my-download-subtitles ()
  (interactive)
  (shell-command "periscope.py -l en *.mkv *.mp4 *.avi &"))

;; {{ show email sent by `git send-email' in gnus
(with-eval-after-load 'gnus
  (local-require 'gnus-article-treat-patch)
  (setq gnus-article-patch-conditions
        '( "^@@ -[0-9]+,[0-9]+ \\+[0-9]+,[0-9]+ @@" )))
;; }}

(defun add-pwd-into-load-path ()
  "add current directory into load-path, useful for elisp developers"
  (interactive)
  (let* ((dir (expand-file-name default-directory)))
    (if (not (memq dir load-path))
        (add-to-list 'load-path dir))
    (message "Directory added into load-path:%s" dir)))

(setq system-time-locale "C")

(setq imenu-max-item-length 256)

;; {{ recentf-mode
(setq recentf-keep '(file-remote-p file-readable-p))
(setq recentf-max-saved-items 2048
      recentf-exclude '("/tmp/"
                        "/ssh:"
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
(defun my-which-file ()
  "Return current file name for Yasnippets."
  (if (buffer-file-name) (format "%s:" (file-name-nondirectory (buffer-file-name)))
    ""))

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
  (interactive)
  (let* ((msg (car (nonempty-lines (shell-command-to-string "mpc")))))
    (message msg)
    (copy-yank-str msg)))

(defun mpc-next-prev-song (&optional prev)
  (interactive)
  (message (car (nonempty-lines (shell-command-to-string
                                 (concat "mpc "
                                         (if prev "prev" "next")))))))

(defun lyrics()
  "Prints the lyrics for the current song"
  (interactive)
  (let* ((song (shell-command-to-string "lyrics")))
    (if (equal song "")
        (message "No lyrics - Opening browser.")
      (switch-to-buffer (create-file-buffer "Lyrics"))
      (insert song)
      (goto-line 0))))
;; }}

;; {{ avy, jump between texts, like easymotion in vim
;; @see http://emacsredux.com/blog/2015/07/19/ace-jump-mode-is-dead-long-live-avy/ for more tips
;; dired
(with-eval-after-load 'dired
  (diredfl-global-mode 1)
  (define-key dired-mode-map (kbd ";") 'avy-goto-subword-1))
;; }}

;; {{start dictionary lookup
;; use below commands to create dictionary
;; mkdir -p ~/.stardict/dic
;; # wordnet English => English
;; curl http://abloz.com/huzheng/stardict-dic/dict.org/stardict-dictd_www.dict.org_wn-2.4.2.tar.bz2 | tar jx -C ~/.stardict/dic
;; # Langdao Chinese => English
;; curl http://abloz.com/huzheng/stardict-dic/zh_CN/stardict-langdao-ec-gb-2.4.2.tar.bz2 | tar jx -C ~/.stardict/dic
;;
(setq sdcv-dictionary-simple-list '("朗道英汉字典5.0"))
(setq sdcv-dictionary-complete-list '("WordNet"))
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
  (local-set-key (kbd "M-y") 'paste-from-x-clipboard)
  (local-set-key (kbd "C-k") 'kill-line)
  (subword-mode 1) ; enable subword movement in minibuffer
  (setq gc-cons-threshold most-positive-fixnum))

(defun my-minibuffer-exit-hook ()
  ;; evil-mode also use minibuf
  (setq gc-cons-threshold 67108864))

;; @see http://bling.github.io/blog/2016/01/18/why-are-you-changing-gc-cons-threshold/
(add-hook 'minibuffer-setup-hook #'my-minibuffer-setup-hook)
(add-hook 'minibuffer-exit-hook #'my-minibuffer-exit-hook)

;; {{ Diff two regions
;; Step 1: Select a region and `M-x diff-region-tag-selected-as-a'
;; Step 2: Select another region and `M-x diff-region-compare-with-b'
;; Press "q" in evil-mode or "C-c C-c" to exit the diff output buffer
(defun diff-region-format-region-boundary (b e)
  "Make sure lines are selected and B is less than E"
  (let* (tmp rlt)
    ;; swap b e, make sure b < e
    (when (> b e)
      (setq tmp b)
      (setq b e)
      (set e tmp))

    ;; select lines
    (save-excursion
      ;; Another workaround for evil-visual-line bug:
      ;; In evil-mode, if we use hotkey V or `M-x evil-visual-line` to select line,
      ;; the (line-beginning-position) of the line which is after the last selected
      ;; line is always (region-end)! Don't know why.
      (if (and (> e b)
               (save-excursion (goto-char e) (= e (line-beginning-position)))
               (boundp 'evil-state) (eq evil-state 'visual))
          (setq e (1- e)))
      (goto-char b)
      (setq b (line-beginning-position))
      (goto-char e)
      (setq e (line-end-position)))
    (setq rlt (list b e))
    rlt))

(defmacro diff-region-open-diff-output (content buffer-name)
  `(let ((rlt-buf (get-buffer-create ,buffer-name)))
    (save-current-buffer
      (switch-to-buffer-other-window rlt-buf)
      (set-buffer rlt-buf)
      (erase-buffer)
      (insert ,content)
      ;; `ffip-diff-mode' is more powerful than `diff-mode'
      (ffip-diff-mode)
      (goto-char (point-min)))))

(defun diff-region-tag-selected-as-a ()
  "Select a region to compare."
  (interactive)
  (when (region-active-p)
    (let* (tmp buf)
      ;; select lines
      (setq tmp (diff-region-format-region-boundary (region-beginning) (region-end)))
      (setq buf (get-buffer-create "*Diff-regionA*"))
      (save-current-buffer
        (set-buffer buf)
        (erase-buffer))
      (append-to-buffer buf (car tmp) (cadr tmp))))
  (message "Now select other region to compare and run `diff-region-compare-with-b'"))

(defun diff-region-compare-with-b ()
  "Compare current region with the region set by `diff-region-tag-selected-as-a'.
If no region is selected, `kill-ring' or clipboard is used instead."
  (interactive)
  (let* (rlt-buf
         diff-output
         tmp
         ;; file A
         (fa (make-temp-file (expand-file-name "diff-region"
                                               (or small-temporary-file-directory
                                                   temporary-file-directory))))
         ;; file B
         (fb (make-temp-file (expand-file-name "diff-region"
                                               (or small-temporary-file-directory
                                                   temporary-file-directory)))))
    (when (and fa (file-exists-p fa) fb (file-exists-p fb))
      (cond
       ((region-active-p)
        ;; text from selected region
        (setq tmp (diff-region-format-region-boundary (region-beginning) (region-end)))
        (write-region (car tmp) (cadr tmp) fb))
       (t
        ;; text from `kill-ring' or clipboard
        (let* ((choice (completing-read "Since no region selected, compare text in:"
                                        '("kill-ring" "clipboard")))
               (txt (cond
                     ((string= choice "kill-ring")
                      (car kill-ring))
                     ((string= choice "clipboard")
                      (my-gclip)))))
          (with-temp-file fb
            (insert txt)))))
      ;; save region A as file A
      (save-current-buffer
        (set-buffer (get-buffer-create "*Diff-regionA*"))
        (write-region (point-min) (point-max) fa))
      ;; diff NOW!
      ;; show the diff output
      (cond
       ((string= (setq diff-output (shell-command-to-string (format "%s -Nabur %s %s" diff-command fa fb))) "")
        (message "Two regions are SAME!"))
       ((executable-find "git")
        (my-ensure 'magit)
        (magit-diff-setup nil (list "--no-index" "--indent-heuristic" "--histogram")
                          nil (list (magit-convert-filename-for-git
                                     (expand-file-name fa))
                                    (magit-convert-filename-for-git
                                     (expand-file-name fb))))
        (ffip-diff-mode))
       (t
        (diff-region-open-diff-output diff-output
                                      "*Diff-region-output*")))
      ;; clean the temporary files
      (if (and fa (file-exists-p fa))
          (delete-file fa))
      (if (and fb (file-exists-p fb))
          (delete-file fb)))))
;; }}

;; {{ cliphist.el
(setq cliphist-use-ivy t)
(defun my-select-cliphist-item (num str)
  (my-pclip str))
(setq cliphist-select-item-callback 'my-select-cliphist-item)
;; }}

(defun extract-list-from-package-json ()
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
  (interactive)
  (setq indent-tabs-mode (not indent-tabs-mode))
  (message "indent-tabs-mode=%s" indent-tabs-mode))

(defvar my-auto-save-exclude-major-mode-list
  '(message-mode)
  "The major modes where auto-save is disabled.")

;; {{ auto-save.el
(defun my-check-major-mode-for-auto-save (file)
  "Check current major mode of FILE for auto save."
  (ignore file)
  (memq major-mode my-auto-save-exclude-major-mode-list))

(with-eval-after-load 'auto-save
  (push 'my-file-too-big-p auto-save-exclude)
  (push 'my-check-major-mode-for-auto-save auto-save-exclude)
  (setq auto-save-idle 2) ; 2 seconds
  (setq auto-save-slient t))
(my-run-with-idle-timer 4 #'auto-save-enable)
;; }}

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
    (let* ((rlt (mapconcat 'identity (subseq kill-ring 0 n) "|")))
      (setq rlt (replace-regexp-in-string "(" "\\\\(" rlt))
      (copy-yank-str rlt)
      (message (format "%s => kill-ring&clipboard" rlt)))))
;; }}


(defun my-get-total-hours ()
  (interactive)
  (let* ((str (if (region-active-p) (my-selected-str)
                (my-buffer-str)))
         (total-hours 0)
         (lines (nonempty-lines str)))
    (dolist (l lines)
      (if (string-match " \\([0-9][0-9.]*\\)h[ \t]*$" l)
          (setq total-hours (+ total-hours (string-to-number (match-string 1 l))))))
    (message "total-hours=%s" total-hours)))

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
  "sgml/html mode setup."
  ;; let web-mode handle indentation by itself since it does not derive from `sgml-mode'
  (setq-local indent-region-function 'sgml-pretty-print))
(add-hook 'sgml-mode-hook 'sgml-mode-hook-setup)


;; {{ xterm
(defun run-after-make-frame-hooks (frame)
  (select-frame frame)
  (unless window-system
    ;; Mouse in a terminal (Use shift to paste with middle button)
    (xterm-mouse-mode 1)))
(add-hook 'after-make-frame-functions 'run-after-make-frame-hooks)
;; }}

;; flymake
(with-eval-after-load 'flymake
  (setq flymake-gui-warnings-enabled nil))

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
        (y-or-n-p "The message suggests that you may want to attach something, but no attachment is found. Send anyway?")
      (error "It seems that an attachment is needed, but none was found. Aborting sending."))))
(add-hook 'message-send-hook 'my-message-pre-send-check-attachment)

;; }}

;; @see https://stackoverflow.com/questions/3417438/closing-all-other-buffers-in-emacs
(defun kill-all-but-current-buffer ()
  (interactive)
  (mapc 'kill-buffer (cdr (buffer-list (current-buffer)))))

(defun minibuffer-inactive-mode-hook-setup ()
  ;; Make `try-expand-dabbrev' from `hippie-expand' work in mini-buffer.
  ;; @see `he-dabbrev-beg', so we need re-define syntax for '/'.
  (set-syntax-table (let* ((table (make-syntax-table)))
                      (modify-syntax-entry ?/ "." table)
                      table)))
(add-hook 'minibuffer-inactive-mode-hook 'minibuffer-inactive-mode-hook-setup)

;; {{ vc-msg
(defun vc-msg-hook-setup (vcs-type commit-info)
  ;; copy commit id to clipboard
  (my-pclip (plist-get commit-info :id)))
(add-hook 'vc-msg-hook 'vc-msg-hook-setup)

(defun vc-msg-show-code-setup ()
  "Use `ffip-diff-mode' instead of `diff-mode'."
  (my-ensure 'find-file-in-project)
  (ffip-diff-mode))

(add-hook 'vc-msg-show-code-hook 'vc-msg-show-code-setup)
;; }}

;; {{ eacl - emacs auto complete line(s)
(global-set-key (kbd "C-x C-l") 'eacl-complete-line)
(global-set-key (kbd "C-c ;") 'eacl-complete-multiline)
(with-eval-after-load 'eacl
  ;; not interested in untracked files in git repository
  (setq eacl-git-grep-untracked nil))
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
  (let* ((patterns '((nil "^=\\([= ]*[^=\n\r]+\\)" 1))))
    (save-excursion
      (imenu--generic-function patterns))))

(defun adoc-mode-hook-setup ()
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

(defun switch-to-builtin-shell ()
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

;; {{ emms
(with-eval-after-load 'emms
  (emms-all)
  ;; use mplayer to play video in full screen mode
  (push "-fs" emms-player-mplayer-parameters)
  (setq emms-player-list '(emms-player-mplayer-playlist
                           emms-player-mplayer
                           emms-player-mpg321
                           emms-player-ogg123
                           emms-player-vlc
                           emms-player-vlc-playlist)))
;; }}

(transient-mark-mode t)

(unless (or *cygwin* *win64*)
  ;; Takes ages to start Emacs.
  ;; Got error `Socket /tmp/fam-cb/fam- has wrong permissions` in Cygwin ONLY!
  ;; reproduced with Emacs 26.1 and Cygwin upgraded at 2019-02-26
  ;;
  ;; Although win64 is fine. It still slows down generic performance.
  ;; @see https://stackoverflow.com/questions/3589535/why-reload-notification-slow-in-emacs-when-files-are-modified-externally
  ;; So no auto-revert-mode on Windows/Cygwin
  (setq global-auto-revert-non-file-buffers t
        auto-revert-verbose nil)
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

;; I'm in Australia now, so I set the locale to "en_AU"
(defun my-insert-date (prefix)
  "Insert the current date. With prefix-argument, use ISO format. With
   two prefix arguments, write out the day and month name."
  (interactive "P")
  (let* ((format (cond
                  ((not prefix) "%d.%m.%Y")
                  ((equal prefix '(4)) "%Y-%m-%d")
                  ((equal prefix '(16)) "%d %B %Y"))))
    (insert (format-time-string format))))

;;compute the length of the marked region
(defun region-length ()
  "Length of a selected region."
  (interactive)
  (message (format "%d" (- (region-end) (region-beginning)))))

;; show ascii table
(defun ascii-table ()
  "Print the ascii table."
  (interactive)
  (switch-to-buffer "*ASCII*")
  (erase-buffer)
  (insert (format "ASCII characters up to number %d.\n" 254))
  (let* ((i 0))
    (while (< i 254)
      (setq i (+ i 1))
      (insert (format "%4d %c\n" i i))))
  (beginning-of-buffer))

;; {{ unique lines
;; https://gist.github.com/ramn/796527
;; uniq-lines
(defun uniq-lines (start end)
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
  "Copy the file name or file path from dired into clipboard.
Press \"w\" to copy file name.
Press \"C-u 0 w\" to copy full path."
  (let* ((str (current-kill 0)))
    (my-pclip str)
    (message "%s => clipboard" str)))
(advice-add 'dired-copy-filename-as-kill :after #'my-dired-copy-filename-as-kill-hack)

;; from http://emacsredux.com/blog/2013/05/04/rename-file-and-buffer/
(defun vc-rename-file-and-buffer ()
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

(defun vc-copy-file-and-rename-buffer ()
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

(defun toggle-env-http-proxy ()
  "Set/unset the environment variable http_proxy used by w3m."
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
Does not indent buffer, because it is used for a before-save-hook, and that
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

  (unless (string-match-p "^gpg (GnuPG) 1.4"
                          (shell-command-to-string (format "%s --version" epg-gpg-program)))

    ;; "apt-get install pinentry-tty" if using emacs-nox
    ;; Create `~/.gnupg/gpg-agent.conf' which has one line
    ;; "pinentry-program /usr/bin/pinentry-curses"
    (setq epa-pinentry-mode 'loopback)))
;; }}

;; {{ pomodoro
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
		   (sdcv-search-input (thing-at-point 'word))))
  (local-set-key (kbd "w") 'mybigword-pronounce-word)
  (local-set-key (kbd ";") 'avy-goto-char-2))
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
        (not (string-match-p "html?$" buffer-file-name)))
    (let* ((file (make-temp-file "my-browse-file-" nil ".html")))
      (my-write-to-file (format "<html><body>%s</body></html>" (buffer-string)) file)
      (my-browse-file file)
      (my-run-with-idle-timer 4 (lambda (delete-file file)))))
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

;; {{ Answer Yes/No programmically when asked by `y-or-n-p'
(defvar my-default-yes-no-answers nil
    "Usage: (setq my-default-yes-no-answers '((t . \"question1\") (t . \"question2\")))).")
(defun my-y-or-n-p-hack (orig-func &rest args)
  "Answer yes or no automatically for some questions."
  (let* ((prompt (car args))
         rlt)
    (cond
     ((and my-default-yes-no-answers
           (listp my-default-yes-no-answers))
      (let* ((i 0) found cand)
        (while (and (setq cand (nth i my-default-yes-no-answers))
                    (not found))
          (when (string-match-p (cdr cand) prompt)
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

;; {{ fetch subtitles
(defvar my-fetch-subtitles-proxy nil
  "http proxy to fetch subtitles, like http://127.0.0.1:8118 (privoxy).")

(defun my-fetch-subtitles (&optional video-file)
  "Fetch subtitles of VIDEO-FILE.
See https://github.com/RafayGhafoor/Subscene-Subtitle-Grabber."
  (let* ((cmd-prefix "subgrab -l EN"))
    (when my-fetch-subtitles-proxy
      (setq cmd-prefix (format "http_proxy=%s https_proxy=%s %s"
                               my-fetch-subtitles-proxy
                               my-fetch-subtitles-proxy
                               cmd-prefix)))
    (cond
     (video-file
      (let* ((default-directory (file-name-directory video-file)))
        (shell-command (format "%s -m \"%s\" &"
                               cmd-prefix
                               (file-name-base video-file)))))
     (t
      (shell-command (format "%s --dir . &" cmd-prefix))))))
;; }}

(defvar my-sdcv-org-head-level 2)
;; {{ use sdcv dictionary to find big word definition
(defun my-sdcv-format-bigword (word zipf)
  "Format WORD and ZIPF using sdcv dictionary."
  (let* (rlt def)
    (local-require 'sdcv)
    ;; 2 level org format
    (condition-case nil
        (progn
          (setq def (sdcv-search-witch-dictionary word sdcv-dictionary-complete-list))
          (setq def (replace-regexp-in-string "^-->.*" "" def))
          (setq def (replace-regexp-in-string "[\n\r][\n\r]+" "" def))
          (setq rlt (format "%s %s (%s)\n%s\n"
                            (make-string my-sdcv-org-head-level ?*)
                            word
                            zipf
                            def)))
      (error nil))
    rlt))

(defun my-lookup-big-word-definition-in-buffer ()
  "Look up big word definitions."
  (interactive)
  (local-require 'mybigword)
  (let* ((mybigword-default-format-function 'my-sdcv-format-bigword))
    (mybigword-show-big-words-from-current-buffer)))
;; }}

;; {{ use pdf-tools to view pdf
(when (and (display-graphic-p) *linux*)
  (pdf-loader-install))
;; }}

;; {{ exe path
(with-eval-after-load 'exec-path-from-shell
  (dolist (var '("SSH_AUTH_SOCK" "SSH_AGENT_PID" "GPG_AGENT_INFO"))
    (push var exec-path-from-shell-variables)))

(when (and window-system (memq window-system '(mac ns)))
  ;; @see https://github.com/purcell/exec-path-from-shell/issues/75
  ;; I don't use those exec path anyway.
  (my-run-with-idle-timer 4 #'exec-path-from-shell-initialize))
;; }}

(with-eval-after-load 'elec-pair
  (setq electric-pair-inhibit-predicate 'my-electric-pair-inhibit))

;; {{ markdown
(defun markdown-mode-hook-setup ()
  ;; Stolen from http://stackoverflow.com/a/26297700
  ;; makes markdown tables saner via orgtbl-mode
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

(provide 'init-misc)
