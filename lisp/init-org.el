;; -*- coding: utf-8; lexical-binding: t; -*-

;; some cool org tricks
;; @see http://emacs.stackexchange.com/questions/13820/inline-verbatim-and-code-with-quotes-in-org-mode

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Org clock
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(with-eval-after-load 'org-clock
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

  (define-key org-clock-mode-line-map [header-line mouse-2] 'org-clock-goto)
  (define-key org-clock-mode-line-map [header-line mouse-1] 'org-clock-menu))

;; {{ org2nikola set up
(setq org2nikola-output-root-directory "~/.config/nikola")
;; }}

(defun org-demote-or-promote (&optional is-promote)
  "Demote or promote current org tree."
  (interactive "P")
  (unless (region-active-p)
    (org-mark-subtree))
  (if is-promote (org-do-promote) (org-do-demote)))

;; {{ @see http://orgmode.org/worg/org-contrib/org-mime.html
(with-eval-after-load 'org-mime
  (setq org-mime-export-options '(:section-numbers nil :with-author nil :with-toc nil))
  (defun org-mime-html-hook-setup ()
    (org-mime-change-element-style "pre"
                                   "color:#E6E1DC; background-color:#232323; padding:0.5em;")
    (org-mime-change-element-style "blockquote"
                                   "border-left: 2px solid gray; padding-left: 4px;"))
  (add-hook 'org-mime-html-hook 'org-mime-html-hook-setup))
;; }}

(defun org-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (setq evil-auto-indent nil)

    ;; org-mime setup, run this command in org-file, than yank in `message-mode'
    (local-set-key (kbd "C-c M-o") 'org-mime-org-buffer-htmlize)

    ;; don't spell check double words
    (setq my-flyspell-check-doublon nil)

    ;; create updated table of contents of org file
    ;; @see https://github.com/snosov1/toc-org
    (toc-org-enable)

    ;; display wrapped lines instead of truncated lines
    (setq truncate-lines nil)
    (setq word-wrap t)))
(add-hook 'org-mode-hook 'org-mode-hook-setup)

(with-eval-after-load 'org
  ;; {{
  (defvar my-org-src--saved-temp-window-config nil
    "Window layout before edit special element.")
  (defun my-org-edit-special (&optional arg)
    "Save current window layout before `org-edit' buffer is open.
ARG is ignored."
    (setq my-org-src--saved-temp-window-config (current-window-configuration)))

  (defun my-org-edit-src-exit ()
    "Restore the window layout that was saved before `org-edit-special' is called."
    (when my-org-src--saved-temp-window-config
      (set-window-configuration my-org-src--saved-temp-window-config)
      (setq my-org-src--saved-temp-window-config nil)))


  ;; org 9.3 do not restore windows layout when editing special element
  (advice-add 'org-edit-special :before 'my-org-edit-special)
  (advice-add 'org-edit-src-exit :after 'my-org-edit-src-exit)
  ;; }}

  (my-ensure 'org-clock)

  ;; org-re-reveal requires org 8.3 while Emacs 25 uses org 8.2
  (when *emacs26*
    (my-ensure 'org-re-reveal))

  ;; odt export
  (add-to-list 'org-export-backends 'odt)

  ;; markdown export
  (my-ensure 'ox-md)
  (add-to-list 'org-export-backends 'md)

  (defun org-agenda-show-agenda-and-todo (&optional arg)
    "Better org-mode agenda view."
    (interactive "P")
    (org-agenda arg "n"))


  (defun my-org-open-at-point-hack (orig-func &rest args)
    "\"C-u M-x org-open-at-point\" to open link with `browse-url-generic-program'.
It's value could be customized liked \"/usr/bin/firefox\".
\"M-x org-open-at-point\" to open the url with embedded emacs-w3m."
    (let* ((arg (nth 0 args))
           (reference-buffer (nth 1 args))
           (browse-url-browser-function
            (cond
             ;; open with `browse-url-generic-program'
             ((equal arg '(4)) 'browse-url-generic)
             ;; open with w3m
             (t 'w3m-browse-url))))
      (apply orig-func args)))
  (advice-add 'org-open-at-point :around #'my-org-open-at-point-hack)

  (defun my-org-publish-hack (orig-func &rest args)
    "Stop running `major-mode' hook when `org-publish'."
    (let* ((load-user-customized-major-mode-hook nil))
      (apply orig-func args)))
  (advice-add 'org-publish :around #'my-org-publish-hack)

  ;; {{ NO spell check for embedded snippets
  (defun my-org-mode-code-snippet-p ()
    "Code snippet embedded in org file?"
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

  (defun my-org-mode-flyspell-verify-hack (orig-func &rest args)
    "flyspell only uses `ispell-word'."
    (let* ((run-spellcheck (apply orig-func args)))
      (when run-spellcheck
        (cond
         ;; skip checking in below fonts
         ((font-belongs-to (point) '(org-verbatim org-code))
          (setq run-spellcheck nil))

         ;; skip checking property lines
         ((string-match "^[ \t]+:[A-Z]+:[ \t]+" (my-line-str))
          (setq run-spellcheck nil))

         ;; skipping checking in code snippet
         ;; slow test should be placed at last
         ((my-org-mode-code-snippet-p)
          (setq run-spellcheck nil))))
      run-spellcheck))
  (advice-add 'org-mode-flyspell-verify :around #'my-org-mode-flyspell-verify-hack)
  ;; }}

  ;; {{ convert to odt
  (defun my-setup-odt-org-convert-process ()
    (interactive)
    (let* ((cmd "/Applications/LibreOffice.app/Contents/MacOS/soffice"))
      (when (and *is-a-mac* (file-exists-p cmd))
        ;; org v8
        (setq org-odt-convert-processes
              '(("LibreOffice" "/Applications/LibreOffice.app/Contents/MacOS/soffice --headless --convert-to %f%x --outdir %d %i"))))))
  (my-setup-odt-org-convert-process)
  ;; }}

  (defun my-org-refile-hack (orig-func &rest args)
    "When `org-refile' scans org files,
skip user's own code in `org-mode-hook'."
    (let* ((force-buffer-file-temp-p t))
      (apply orig-func args)))
  (advice-add 'org-refile :around #'my-org-refile-hack)

  ;; {{ export org-mode in Chinese into PDF
  ;; @see http://freizl.github.io/posts/tech/2012-04-06-export-orgmode-file-in-Chinese.html
  ;; and you need install texlive-xetex on different platforms
  ;; To install texlive-xetex:
  ;;    `sudo USE="cjk" emerge texlive-xetex` on Gentoo Linux
  (setq org-latex-pdf-process
        '("xelatex -interaction nonstopmode -output-directory %o %f"
          "xelatex -interaction nonstopmode -output-directory %o %f"
          "xelatex -interaction nonstopmode -output-directory %o %f")) ;; org v8
  ;; }}

  ;; misc
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
        ;; org-startup-indented t
        ;; {{ org 8.2.6 has some performance issue. Here is the workaround.
        ;; @see http://punchagan.muse-amuse.in/posts/how-i-learnt-to-use-emacs-profiler.html
        org-agenda-inhibit-startup t ;; ~50x speedup
        org-agenda-use-tag-inheritance nil ;; 3-4x speedup
        ;; }}
        ;; org v8
        org-odt-preferred-output-format "doc"
        org-tags-column 80

        ;; Refile targets include this file and any file contributing to the agenda - up to 5 levels deep
        org-refile-targets '((nil :maxlevel . 5) (org-agenda-files :maxlevel . 5))
        org-refile-use-outline-path 'file
        org-outline-path-complete-in-steps nil
        org-todo-keywords (quote ((sequence "TODO(t)" "STARTED(s)" "|" "DONE(d!/!)")
                                  (sequence "WAITING(w@/!)" "SOMEDAY(S)" "PROJECT(P@)" "|" "CANCELLED(c@/!)")))
        org-imenu-depth 9
        ;; @see http://irreal.org/blog/1
        org-src-fontify-natively t))

(provide 'init-org)
