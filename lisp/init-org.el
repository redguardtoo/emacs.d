;; -*- coding: utf-8; lexical-binding: t; -*-

;; some cool org tricks
;; @see http://emacs.stackexchange.com/questions/13820/inline-verbatim-and-code-with-quotes-in-org-mode

(with-eval-after-load 'org-clock
  ;; Change task state to STARTED when clocking in
  (setq org-clock-in-switch-to-state "STARTED")
  ;; Save clock data and notes in the LOGBOOK drawer
  (setq org-clock-into-drawer t)
  ;; Removes clocked tasks with 0:00 duration
  (setq org-clock-out-remove-zero-time-clocks t)

  ;; Show the clocked-in task - if any - in the header line
  (defun my-show-org-clock-in-header-line ()
    (setq-default header-line-format '((" " org-mode-line-string " "))))

  (defun my-hide-org-clock-from-header-line ()
    (setq-default header-line-format nil))

  (add-hook 'org-clock-in-hook 'my-show-org-clock-in-header-line)
  (add-hook 'org-clock-out-hook 'my-hide-org-clock-from-header-line)
  (add-hook 'org-clock-cancel-hook 'my-hide-org-clock-from-header-line)

  (define-key org-clock-mode-line-map [header-line mouse-2] 'org-clock-goto)
  (define-key org-clock-mode-line-map [header-line mouse-1] 'org-clock-menu))

;; {{ org2nikola set up
(setq org2nikola-output-root-directory "~/.config/nikola")
;; }}

(defun org-demote-or-promote (&optional is-promote)
  "Demote or promote current org tree."
  (interactive "P")
  (save-excursion
    (beginning-of-line)
    (unless (or (region-active-p)
                (let ((line (thing-at-point 'line t)))
                  (and (string-match "^\\*+ $" line) ;; is node only one spaced
                       (= (point) (- (point-max) (length line))) ;; is line at EOF
                       )))
      (org-mark-subtree)))
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

(defun my-imenu-create-index-function-no-org-link ()
  "Imenu index function which returns items without org link."
  (let (rlt label marker)
    (dolist (elem (imenu-default-create-index-function))
      (cond
       ((and (setq label (car elem)) (setq marker (cdr elem)))
        (push (cons (replace-regexp-in-string "\\[\\[[^ ]+\\]\\[\\|\\]\\]" "" label) marker) rlt))
       (t
        (push elem rlt))))
    (nreverse rlt)))

(defun org-mode-hook-setup ()
  (unless (my-buffer-file-temp-p)
    (setq-local evil-auto-indent nil)

    ;; org-mime setup, run this command in org-file, than yank in `message-mode'
    (local-set-key (kbd "C-c M-o") 'org-mime-org-buffer-htmlize)

    ;; don't spell check double words
    (setq-local wucuo-flyspell-check-doublon nil)

    ;; create updated table of contents of org file
    ;; @see https://github.com/snosov1/toc-org
    (toc-org-enable)

    ;; default `org-indent-line' inserts extra spaces at the beginning of lines
    (setq-local indent-line-function 'indent-relative)

    ;; `imenu-create-index-function' is automatically buffer local
    (setq imenu-create-index-function 'my-imenu-create-index-function-no-org-link)

    ;; display wrapped lines instead of truncated lines
    (setq truncate-lines nil)
    (setq word-wrap t)))
(add-hook 'org-mode-hook 'org-mode-hook-setup)

(defvar my-pdf-view-from-history nil
  "PDF view FROM history which is List of (pdf-path . page-number).")

(defvar my-pdf-view-to-history nil
  "PDF view TO history which is List of (pdf-path . page-number).")

(with-eval-after-load 'org
  ;; {{
  (defvar my-org-src--saved-temp-window-config nil
    "Window layout before edit special element.")
  (defun my-org-edit-special (&optional arg)
    (ignore arg)
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

  ;; org-re-reveal requires org 8.3
  (my-ensure 'org-re-reveal)

  ;; odt export
  (push 'odt org-export-backends)

  ;; markdown export
  (my-ensure 'ox-md)
  (add-to-list 'org-export-backends 'md)

  ;; {{ org pdf link
  (defun my-org-docview-open-hack (orig-func &rest args)
    (ignore orig-func)
    (let ((link (car args)) path page pdf-from-page)
      (string-match "\\(.*?\\)\\(?:::\\([0-9]+\\)\\)?$" link)
      (setq path (match-string 1 link))
      (setq page (and (match-beginning 2)
                      (string-to-number (match-string 2 link))))

      ;; record FROM
      (my-focus-on-pdf-window-then-back
       (lambda (pdf-file)
         (when (and page (string= (file-name-base pdf-file) (file-name-base path)))
           ;; select pdf-window
           (when (and (memq major-mode '(doc-view-mode pdf-view-mode))
                      (setq pdf-from-page
                            (if (eq major-mode 'pdf-view-mode)
                                (pdf-view-current-page)
                              (doc-view-current-page)))
                      (> (abs (- page pdf-from-page)) 2))
             (my-push-if-uniq (format "%s:::%s" pdf-file pdf-from-page) my-pdf-view-from-history)))))
      ;; open pdf file
      (org-open-file path 1)
      (when page
        ;; record TO
        (my-push-if-uniq (format "%s:::%s" path page) my-pdf-view-to-history)
        ;; goto page
        (my-pdf-view-goto-page page))))
  (advice-add 'org-docview-open :around #'my-org-docview-open-hack)
  ;; }}

  (defun my-org-publish-hack (orig-func &rest args)
    "Stop running `major-mode' hook when `org-publish'."
    (let* ((my-load-user-customized-major-mode-hook nil))
      (apply orig-func args)))
  (advice-add 'org-publish :around #'my-org-publish-hack)

  ;; {{ convert from odt to other format (doc, pdf, ...)
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
    "When `org-refile' scans org files, skip user's own code in `org-mode-hook'."
    (let* ((my-force-buffer-file-temp-p t))
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

  ;; {{ org-babel
  (org-babel-do-load-languages
   'org-babel-load-languages
   '((emacs-lisp . t)
     (python . t)
     (C . t)
     (lisp . t)
     (java . t)
     (perl . t)
     (latex . t)
     (shell . t)
     (lua . t)
     (js . t)))
  ;; disable prompt when executing code block in org mode
  (setq org-confirm-babel-evaluate nil)
  ;; }}

  ;; misc
  (setq org-log-done 'time
        org-edit-src-content-indentation 0
        org-edit-timestamp-down-means-later t
        org-agenda-start-on-weekday nil ; start on the current day
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
        org-imenu-depth 9))

;; executing sage in org babel
(with-eval-after-load 'ob-sagemath
  ;; Ob-sagemath supports only evaluating with a session.
  (setq org-babel-default-header-args:sage '((:session . t)
                                             (:results . "drawer")))
  (setq sage-shell:input-history-cache-file "~/data/sage_history")
  (add-hook 'sage-shell-after-prompt-hook #'sage-shell-view-mode))

(provide 'init-org)
