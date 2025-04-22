;; -*- coding: utf-8; lexical-binding: t; -*-

(my-run-with-idle-timer 1 #'ivy-mode)

(with-eval-after-load 'counsel
  (setq counsel-async-command-delay 0.3)

  (defun my-counsel-git-grep-cmd-function-default (str)
    (let* ((patterns (split-string str " *!"))
           (pos-re (counsel-etags-positive-regex patterns))
           (neg-re (counsel-etags-exclusion-regex patterns))
           rlt)
      (setq rlt (format counsel-git-grep-cmd pos-re))
      (when neg-re
        (setq rlt (format "%s --and --not -e \"%s\"" rlt neg-re)))
     rlt))

  (setq counsel-git-grep-cmd-function #'my-counsel-git-grep-cmd-function-default)

  ;; automatically pick up cygwin cli tools for counsel
  (cond
   ((executable-find "rg")
    ;; ripgrep says that "-n" is enabled actually not,
    ;; so we manually add it
    (setq counsel-grep-base-command
          (concat (executable-find "rg")
                  " -n -M 512 --no-heading --color never -i \"%s\" %s")))

   (*win64*
    (let* ((cygpath (or (and (file-exists-p "c:/cygwin64/bin") "c:/cygwin64/bin")
                        (and (file-exists-p "d:/cygwin64/bin") "d:/cygwin64/bin")
                        (and (file-exists-p "e:/cygwin64/bin") "e:/cygwin64/bin"))))
      ;; `cygpath' could be nil on Windows
      (when cygpath
        (unless (string-match cygpath counsel-git-cmd)
          (setq counsel-git-cmd (concat cygpath "/" counsel-git-cmd)))

        (unless (string-match cygpath counsel-git-grep-cmd-default)
          (setq counsel-git-grep-cmd-default (concat cygpath "/" counsel-git-grep-cmd-default)))
        ;; ;; git-log does not work
        ;; (unless (string-match cygpath counsel-git-log-cmd)
        ;;   (setq counsel-git-log-cmd (concat "GIT_PAGER="
        ;;                                     cygpath
        ;;                                     "/cat "
        ;;                                     cygpath
        ;;                                     "/git log --grep '%s'")))
        (unless (string-match cygpath counsel-grep-base-command)
          (setq counsel-grep-base-command (concat cygpath "/" counsel-grep-base-command)))))))

  ;; @see https://oremacs.com/2015/07/23/ivy-multiaction/
  ;; press "M-o" to choose ivy action
  (ivy-set-actions
   'find-file
   '(("j" find-file-other-frame "other frame")
     ("d" delete-file "delete")
     ("r" counsel-find-file-as-root "open as root"))))

(global-set-key (kbd "C-x b") 'ivy-switch-buffer)

(define-key read-expression-map (kbd "C-r") 'counsel-expression-history)

(defvar my-git-recent-files-extra-options ""
  "Extra options for git recent files.
For example, could be \"---author=MyName\"")

(defmacro my-git-extract-file (n items rlt)
  "Extract Nth item from ITEMS as a file candidate.
The candidate could be placed in RLT."
  `(let* ((file (string-trim (nth ,n ,items))))
     (when (file-exists-p file)
       (push (cons file (file-truename file)) ,rlt))))

(defun my-git-recent-files ()
  "Get files in my recent git commits."
  (let* ((default-directory (my-git-root-dir))
         ;; two weeks is a sprint, minus weekend and days for sprint review and test
         (cmd (format "git --no-pager log %s --name-status --since=\"10 days ago\" --pretty=format:"
                      my-git-recent-files-extra-options))
         (lines (my-lines-from-command-output cmd))
         items
         rlt)
    (when lines
      (dolist (l lines)
        (setq items (split-string l "[ \t]+" l))
        (cond
         ((= (length items) 2)
          (my-git-extract-file 1 items rlt))
         ((= (length items) 3)
          (my-git-extract-file 1 items rlt)
          (my-git-extract-file 2 items rlt)))))
    rlt))

(defun my-counsel-recentf (&optional n)
  "Find a file on `recentf-list'.
If N is 1, only list files in current project.
If N is 2, list files in my recent 20 commits."
  (interactive "P")
  (my-ensure 'recentf)
  (unless n (setq n 0))
  (recentf-mode 1)
  (let* ((files (mapcar #'substring-no-properties recentf-list))
         (root-dir (if (ffip-project-root) (file-truename (ffip-project-root))))
         (hint "Recent files: ")
         f)
    (cond
     ((and (eq n 1) root-dir)
      (setq hint (format "Recent files in %s: " root-dir))
      (setq files (delq nil (delete-dups (mapcar (lambda (f) (path-in-directory-p f root-dir)) files)))))
     ((eq n 2)
      (setq hint (format "Files in recent Git commits: "))
      (setq files (my-git-recent-files))))

    (when (setq f (ivy-read hint
                            files
                            :initial-input (if (region-active-p) (my-selected-str))))
      ;; return file buffer if possible
      (with-ivy-window
        (find-file f)))))

;; grep by author is bad idea. Too slow

(defun my-insert-bash-history ()
  "Yank the bash history."
  (interactive)
  (shell-command "history -r") ; reload history
  (let* ((collection (nreverse (my-read-lines (file-truename "~/.bash_history"))))
         (val (completing-read "Bash history: " collection)))
  (when val
      (kill-new val)
      (message "%s => kill-ring" val)
      (insert val))))

(defun ivy-occur-grep-mode-hook-setup ()
  "Set up ivy occur grep mode."
  ;; turn on wgrep right now
  ;; (ivy-wgrep-change-to-wgrep-mode) ; doesn't work, don't know why

  (when evil-mode
    (evil-local-set-key 'normal (kbd "RET") #'ivy-occur-press-and-switch)
    ;; In ivy original key bindings, "w" changes to `wgrep-mode'
    ;; Use same key binding in EVIL.
    (evil-local-set-key 'normal "w" #'ivy-wgrep-change-to-wgrep-mode))

  ;; no syntax highlight, I only care performance when searching/replacing
  (font-lock-mode -1)
  ;; @see https://emacs.stackexchange.com/questions/598/how-do-i-prevent-extremely-long-lines-making-emacs-slow
  (column-number-mode -1))
(add-hook 'ivy-occur-grep-mode-hook 'ivy-occur-grep-mode-hook-setup)

(defun my-counsel-git-find-file ()
  "Use git to find file."
  (interactive)
  (counsel-git (and (region-active-p) (my-selected-str))))

(defun my-counsel-git-grep (&optional level)
  "Git grep in project.  If LEVEL is not nil, grep files in parent commit."
  (interactive "P")
  (let* ((str (if (region-active-p) (my-selected-str))))
    (cond
     (level
      (unless str
        (setq str (my-use-selected-string-or-ask "Grep keyword: ")))
      (when str
        (let* ((default-directory (my-git-root-dir))
               ;; C-u 1 command to grep files in HEAD
               (cmd-opts (concat (my-git-files-in-rev-command "HEAD" (1- level))
                                 " | xargs -I{} "
                                 "git --no-pager grep -n --no-color -I -e \"%s\" -- {}"))
               (cmd (format cmd-opts str)))
          (ivy-read "git grep in commit: "
                    (my-lines-from-command-output cmd)
                    :caller 'counsel-etags-grep
                    :history 'counsel-git-grep-history
                    :action #'counsel-git-grep-action))))
     (t
      (counsel-git-grep str)))))

(defun my-counsel-browse-kill-ring ()
  "If N > 1, assume just yank the Nth item in `kill-ring'."
  (interactive)
  (my-select-from-kill-ring (lambda (s)
                              (let* ((plain-str (my-insert-str s))
                                     (trimmed (string-trim plain-str)))
                                (setq kill-ring (cl-delete-if
                                                 `(lambda (e) (string= ,trimmed (string-trim e)))
                                                 kill-ring))
                                (kill-new plain-str)))))

(defun ivy-switch-buffer-matcher-pinyin (regexp candidates)
  (my-ensure 'pinyinlib)
  (ivy--switch-buffer-matcher (pinyinlib-build-regexp-string regexp) candidates))

(defun ivy-switch-buffer-by-pinyin ()
  "Switch to another buffer."
  (interactive)
  (my-ensure 'ivy)
  (let* ((this-command 'ivy-switch-buffer))
    (ivy-read "Switch to buffer: " 'internal-complete-buffer
              :matcher #'ivy-switch-buffer-matcher-pinyin
              :preselect (buffer-name (other-buffer (current-buffer)))
              :action #'ivy--switch-buffer-action
              :keymap ivy-switch-buffer-map
              :caller 'ivy-switch-buffer)))

;; {{ swiper&ivy-mode
(global-set-key (kbd "C-s") 'counsel-grep-or-swiper)
;; }}

(global-set-key (kbd "C-h v") 'counsel-describe-variable)
(global-set-key (kbd "C-h f") 'counsel-describe-function)

;; {{  C-o f to toggle case sensitive, @see https://github.com/abo-abo/swiper/issues/1104
(defun my-re-builder-extended-pattern (str)
  "Build regex compatible with pinyin from STR."
  (ivy--regex-plus (my-extended-regexp str)))
;; }}

(defun my-counsel-imenu ()
  "Jump to a buffer position indexed by imenu."
  (interactive)
  (my-ensure 'counsel)
  (cond
   ;; `counsel--imenu-candidates' was created on 2019-10-12
   ((and (fboundp 'counsel--imenu-candidates)
         (not (memq major-mode '(pdf-view-mode))))
    (let* ((cands (counsel--imenu-candidates))
           (pre-selected (thing-at-point 'symbol))
           (closest (my-closest-imenu-item-internal cands)))
      (if closest (setq pre-selected (car closest)))
      (ivy-read "imenu items: " cands
                :preselect pre-selected
                :require-match t
                :action #'counsel-imenu-action
                :keymap counsel-imenu-map
                :history 'counsel-imenu-history
                :caller 'counsel-imenu)))
   (t
    (counsel-imenu))))

(defun my-imenu-or-list-tag-in-current-file ()
  "Combine the power of counsel-etags and imenu."
  (interactive)
  (counsel-etags-push-marker-stack)
  (cond
   ((my-use-tags-as-imenu-function-p)
    ;; see code of `my-use-tags-as-imenu-function-p'. Currently we only use ctags for imenu
    ;; in typescript because `lsp-mode' is too damn slow
    (let* ((imenu-create-index-function 'counsel-etags-imenu-default-create-index-function))
      (my-counsel-imenu)))
   (t
    (my-counsel-imenu))))

(with-eval-after-load 'ivy
  ;; Add recent files and bookmarks to the `ivy-switch-buffer'
  (setq ivy-use-virtual-buffers t)

  ;; better performance on everything (especially windows), ivy-0.10.0 required
  ;; when `ivy-dynamic-exhibit-delay-ms' is a non-zero value
  ;; Setting it to a bigger value in ALL OSs is also more green energy btw.
  ;; @see https://github.com/abo-abo/swiper/issues/1218
  (setq ivy-dynamic-exhibit-delay-ms 300)

  ;; @see https://github.com/abo-abo/swiper/issues/1218#issuecomment-962516670
  ;; Thanks to Umar Ahmad (Gleek)
  (defvar my-ivy--queue-last-input nil)
  (defun my-ivy-queue-exhibit-a(f &rest args)
    (cond
     ((equal my-ivy--queue-last-input (ivy--input))
      (ivy--exhibit))
     (t
      (apply f args)))
    (setq my-ivy--queue-last-input (ivy--input)))
  (advice-add 'ivy--queue-exhibit :around #'my-ivy-queue-exhibit-a)

  ;; Press C-p and Enter to select current input as candidate
  ;; https://oremacs.com/2017/11/30/ivy-0.10.0/
  (setq ivy-use-selectable-prompt t)

  (setq ivy-re-builders-alist '((t . my-re-builder-extended-pattern)))
  ;; set actions when running C-x b
  ;; replace "frame" with window to open in new window
  (ivy-set-actions
   'ivy-switch-buffer-by-pinyin
   '(("j" switch-to-buffer-other-frame "other frame")
     ("k" kill-buffer "kill")
     ("r" ivy--rename-buffer-action "rename"))))

(defun my-counsel-company ()
  "Input code from company backend using fuzzy matching."
  (interactive)
  (company-abort)
  (let* ((company-backends '(company-ctags))
         (company-ctags-fuzzy-match-p t))
    (counsel-company)))

(provide 'init-ivy)
;;; init-ivy.el ends here
