;; some cool org tricks
;; @see http://emacs.stackexchange.com/questions/13820/inline-verbatim-and-code-with-quotes-in-org-mode

;; {{ NO spell check for embedded snippets
(defun org-mode-is-code-snippet ()
  (let* (rlt
         (begin-regexp "^[ \t]*#\\+begin_\\(src\\|html\\|latex\\|example\\)")
         (end-regexp "^[ \t]*#\\+end_\\(src\\|html\\|latex\\|example\\)")
         (case-fold-search t)
         b e)
    (save-excursion
      (if (setq b (re-search-backward begin-regexp nil t))
          (setq e (re-search-forward end-regexp nil t))))
    (if (and b e (< (point) e)) (setq rlt t))
    rlt))

;; no spell check for property
(defun org-mode-current-line-is-property ()
  (string-match "^[ \t]+:[A-Z]+:[ \t]+" (my-line-str)))

;; Please note flyspell only use ispell-word
(defadvice org-mode-flyspell-verify (after org-mode-flyspell-verify-hack activate)
  (let ((run-spellcheck ad-return-value))
    (if ad-return-value
      (cond
       ((org-mode-is-code-snippet)
        (setq run-spellcheck nil))
       ((org-mode-current-line-is-property)
        (setq run-spellcheck nil))))
    (setq ad-return-value run-spellcheck)))
;; }}

;; Org v8 change log:
;; @see http://orgmode.org/worg/org-8.0.html

;; {{ export org-mode in Chinese into PDF
;; @see http://freizl.github.io/posts/tech/2012-04-06-export-orgmode-file-in-Chinese.html
;; and you need install texlive-xetex on different platforms
;; To install texlive-xetex:
;;    `sudo USE="cjk" emerge texlive-xetex` on Gentoo Linux
(setq org-latex-to-pdf-process ;; org v7
      '("xelatex -interaction nonstopmode -output-directory %o %f"
        "xelatex -interaction nonstopmode -output-directory %o %f"
        "xelatex -interaction nonstopmode -output-directory %o %f"))
(setq org-latex-pdf-process org-latex-to-pdf-process) ;; org v8
;; }}

(defun my-setup-odt-org-convert-process ()
  (interactive)
  (let ((cmd "/Applications/LibreOffice.app/Contents/MacOS/soffice"))
    (when (and *is-a-mac* (file-exists-p cmd))
      ;; org v7
      (setq org-export-odt-convert-processes '(("LibreOffice" "/Applications/LibreOffice.app/Contents/MacOS/soffice --headless --convert-to %f%x --outdir %d %i")))
      ;; org v8
      (setq org-odt-convert-processes '(("LibreOffice" "/Applications/LibreOffice.app/Contents/MacOS/soffice --headless --convert-to %f%x --outdir %d %i"))))
    ))

(my-setup-odt-org-convert-process)

(defun narrow-to-region-indirect-buffer-maybe (start end use-indirect-buffer)
  "Indirect buffer could multiple widen on same file."
  (if (region-active-p) (deactivate-mark))
  (if use-indirect-buffer
      (with-current-buffer (clone-indirect-buffer
                            (generate-new-buffer-name
                             (concat (buffer-name) "-indirect-"
                                     (number-to-string start) "-"
                                     (number-to-string end)))
                            'display)
        (narrow-to-region start end)
        (goto-char (point-min)))
      (narrow-to-region start end)))

;; @see https://gist.github.com/mwfogleman/95cc60c87a9323876c6c
(defun narrow-or-widen-dwim (&optional use-indirect-buffer)
  "If the buffer is narrowed, it widens.
 Otherwise, it narrows to region, or Org subtree.
If use-indirect-buffer is not nil, use `indirect-buffer' to hold the widen content."
  (interactive "P")
  (cond ((buffer-narrowed-p) (widen))
        ((region-active-p)
         (narrow-to-region-indirect-buffer-maybe (region-beginning)
                                                 (region-end)
                                                 use-indirect-buffer))
        ((equal major-mode 'org-mode)
         (org-narrow-to-subtree))
        ((equal major-mode 'diff-mode)
         (let* (b e)
           (save-excursion
             (setq b (diff-beginning-of-file))
             (setq e (progn (diff-end-of-file) (point))))
           (when (and b e (< b e))
             (narrow-to-region-indirect-buffer-maybe b e use-indirect-buffer))))
        (t (error "Please select a region to narrow to"))))

;; Various preferences
(setq org-log-done t
      org-completion-use-ido t
      org-edit-src-content-indentation 0
      org-edit-timestamp-down-means-later t
      org-agenda-start-on-weekday nil
      org-agenda-span 14
      org-agenda-include-diary t
      org-agenda-window-setup 'current-window
      org-fast-tag-selection-single-key 'expert
      org-export-kill-product-buffer-when-displayed t
      ;; org v7
      org-export-odt-preferred-output-format "doc"
      ;; org v8
      org-odt-preferred-output-format "doc"
      org-tags-column 80
      ;; org-startup-indented t
      ;; {{ org 8.2.6 has some performance issue. Here is the workaround.
      ;; @see http://punchagan.muse-amuse.in/posts/how-i-learnt-to-use-emacs-profiler.html
      org-agenda-inhibit-startup t ;; ~50x speedup
      org-agenda-use-tag-inheritance nil ;; 3-4x speedup
      ;; }}
      )

;; Refile targets include this file and any file contributing to the agenda - up to 5 levels deep
(setq org-refile-targets (quote ((nil :maxlevel . 5) (org-agenda-files :maxlevel . 5))))
;; Targets start with the file name - allows creating level 1 tasks
(setq org-refile-use-outline-path (quote file))
;; Targets complete in steps so we start with filename, TAB shows the next level of targets etc
(setq org-outline-path-complete-in-steps t)

(setq org-todo-keywords
      (quote ((sequence "TODO(t)" "STARTED(s)" "|" "DONE(d!/!)")
              (sequence "WAITING(w@/!)" "SOMEDAY(S)" "PROJECT(P@)" "|" "CANCELLED(c@/!)"))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Org clock
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Change task state to STARTED when clocking in
(setq org-clock-in-switch-to-state "STARTED")
;; Save clock data and notes in the LOGBOOK drawer
(setq org-clock-into-drawer t)
;; Removes clocked tasks with 0:00 duration
(setq org-clock-out-remove-zero-time-clocks t)

;; Show the clocked-in task - if any - in the header line
(defun sanityinc/show-org-clock-in-header-line ()
  (setq-default header-line-format '((" " org-mode-line-string " "))))

(defun sanityinc/hide-org-clock-from-header-line ()
  (setq-default header-line-format nil))

(add-hook 'org-clock-in-hook 'sanityinc/show-org-clock-in-header-line)
(add-hook 'org-clock-out-hook 'sanityinc/hide-org-clock-from-header-line)
(add-hook 'org-clock-cancel-hook 'sanityinc/hide-org-clock-from-header-line)

(eval-after-load 'org-clock
  '(progn
     (define-key org-clock-mode-line-map [header-line mouse-2] 'org-clock-goto)
     (define-key org-clock-mode-line-map [header-line mouse-1] 'org-clock-menu)))

(eval-after-load 'org
  '(progn
     (setq org-imenu-depth 9)
     (require 'org-clock)
     ;; @see http://irreal.org/blog/1
     (setq org-src-fontify-natively t)))

(defun org-mode-hook-setup ()
  (setq evil-auto-indent nil)
  ;; org-mode's own flycheck will be loaded
  (enable-flyspell-mode-conditionally)

  ;; but I don't want to auto spell check when typing,
  ;; please comment out `(flyspell-mode -1)` if you prefer auto spell check
  (flyspell-mode -1)

  ;; for some reason, org8 disable odt export by default
  (add-to-list 'org-export-backends 'odt)
  ;; (add-to-list 'org-export-backends 'org) ; for org-mime

  ;; org-mime setup, run this command in org-file, than yank in `message-mode'
  (local-set-key (kbd "C-c M-o") 'org-mime-org-buffer-htmlize)

  ;; don't spell check double words
  (setq flyspell-check-doublon nil)

  ;; display wrapped lines instead of truncated lines
  (setq truncate-lines nil)
  (setq word-wrap t))
(add-hook 'org-mode-hook 'org-mode-hook-setup)

(defadvice org-open-at-point (around org-open-at-point-choose-browser activate)
  "`C-u M-x org-open-at-point` open link with `browse-url-generic-program'"
  (let* ((browse-url-browser-function
          (cond
           ;; open with `browse-url-generic-program'
           ((equal (ad-get-arg 0) '(4)) 'browse-url-generic)
           ;; open with w3m
           (t 'w3m-browse-url))))
    ad-do-it))

(defadvice org-publish (around org-publish-advice activate)
  "Stop running major-mode hook when org-publish"
  (let ((old load-user-customized-major-mode-hook))
    (setq load-user-customized-major-mode-hook nil)
    ad-do-it
    (setq load-user-customized-major-mode-hook old)))

;; {{ org2nikola set up
(setq org2nikola-output-root-directory "~/.config/nikola")
(setq org2nikola-use-google-code-prettify t)
(setq org2nikola-prettify-unsupported-language
      '(elisp "lisp"
              emacs-lisp "lisp"))
;; }}

(defun org-demote-or-promote (&optional is-promote)
  (interactive "P")
  (unless (region-active-p)
    (org-mark-subtree))
  (if is-promote (org-do-promote)
    (org-do-demote)))

;; {{ @see http://orgmode.org/worg/org-contrib/org-mime.html
(defun org-mime-html-hook-setup ()
  (org-mime-change-element-style "pre"
                                 "color:#E6E1DC; background-color:#232323; padding:0.5em;")
  (org-mime-change-element-style "blockquote"
                                 "border-left: 2px solid gray; padding-left: 4px;"))

(eval-after-load 'org-mime
  '(progn
     (setq org-mime-export-options '(:section-numbers nil :with-author nil :with-toc nil))
     (add-hook 'org-mime-html-hook 'org-mime-html-hook-setup)))

;; demo video: http://vimeo.com/album/1970594/video/13158054
(add-hook 'message-mode-hook
          (lambda ()
            (local-set-key (kbd "C-c M-o") 'org-mime-htmlize)))
;; }}

(defun org-agenda-show-agenda-and-todo (&optional arg)
  "Better org-mode agenda view."
  (interactive "P")
  (org-agenda arg "n"))

(provide 'init-org)
