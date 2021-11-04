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
  (save-excursion
    (beginning-of-line)
    (unless (or (region-active-p)
                (let ((line (thing-at-point 'line t)))
                  (and (string-match-p "^\\*+ $" line) ;; is node only one spaced
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
  (unless (is-buffer-file-temp)
    (setq evil-auto-indent nil)

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
    "Save current window layout before `org-edit' buffer is open.
ARG is ignored."
    (setq my-org-src--saved-temp-window-config (current-window-configuration)))

  (defun my-org-edit-src-exit ()
    "Restore the window layout that was saved before `org-edit-special' is called."
    (when my-org-src--saved-temp-window-config
      (set-window-configuration my-org-src--saved-temp-window-config)
      (setq my-org-src--saved-temp-window-config nil)))


  ;; org 9.3 do not restore windows layout when editing special element (advice-add 'org-edit-special :before 'my-org-edit-special)
  (advice-add 'org-edit-src-exit :after 'my-org-edit-src-exit)
  ;; }}

  (my-ensure 'org-clock)

  ;; org-re-reveal requires org 8.3
  (my-ensure 'org-re-reveal)

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

  ;; {{ org pdf link
  (defun my-org-docview-open-hack (orig-func &rest args)
    (let* ((link (car args)) path page)
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
                            (if (eq major-mode 'pdf-view-mode) (pdf-view-current-page) (doc-view-current-page)))
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
  ;; agenda
  (setq org-agenda-files '("~/org")
        org-agenda-breadcrumbs-separator " ❱ "
        org-agenda-current-time-string "⏰ ┈┈┈┈┈┈┈┈┈┈┈ now"
        org-agenda-time-grid '((weekly today require-timed)
                               (800 1000 1200 1400 1600 1800 2000)
                               "---" "┈┈┈┈┈┈┈┈┈┈┈┈┈")
        org-agenda-prefix-format '((agenda . "%i %-12:c%?-12t%b% s")
                                   (todo . " %i %-12:c")
                                   (tags . " %i %-12:c")
                                   (search . " %i %-12:c")))
  ;;capture
  (setq org-capture-templates
      '(("n" "Notes" entry
         ;; (file "~/org/inbox.org") "* %^{Description} %^g\n Added: %U\n%?")
         (file "~/org/inbox.org") "* Notes %^{Title}")
        ;; ("m" "Meeting notes" entry
        ;;  (file "~/org/meetings.org") "* TODO %^{Title} %t\n- %?")
        ("t" "TODO" entry
         (file "~/org/inbox.org") "* TODO %^{Title}")
        ;; ("e" "Event" entry
        ;;  (file "~/org/calendar.org") "* %^{Is it a todo?||TODO |NEXT }%^{Title}\n%^t\n%?")
        ("p" "PROJECT TODO" entry
         (file "~/org/project.org") "* PROJECT %^{Title}")))

  (require 'org-superstar)
  ;; Hide away leading stars on terminal.
  (setq org-superstar-leading-fallback ?\s)
  (setq org-superstar-leading-bullet "  ")
  (add-hook 'org-mode-hook (lambda () (org-superstar-mode 1)))

  ;; (with-eval-after-load 'org-superstar
  ;;   ;; Every non-TODO headline now have no bullet
  ;;   ;; (setq org-superstar-headline-bullets-list '("\u200b"))
  ;;   ;; (setq org-superstar-leading-bullet "\u200b")
  ;;   (setq org-superstar-item-bullet-alist
  ;;         '((?* . ?•)
  ;;           (?+ . ?➤)
  ;;           (?- . ?•)))
  ;;   ;; Enable custom bullets for TODO items
  ;;   (setq org-superstar-headline-bullets-list '(?\s))
  ;;   (setq org-superstar-special-todo-items t)
  ;;   ;; (setq org-superstar-remove-leading-stars t)
  ;;   (setq org-superstar-todo-bullet-alist
  ;;         '(("TODO" . ?☐)
  ;;           ("STARTED" . ?✒)
  ;;           ("PROJECT" . ?📚)
  ;;           ("SOMEDAY" . ?⏳)
  ;;           ("WAITING" . ?☕)
  ;;           ("CANCELLED" . ?✘)
  ;;           ("DONE" . ?✔)))
  ;;   (org-superstar-restart))

  ;; misc
  (setq org-log-done t
        org-log-into-drawer t
        org-completion-use-ido t
        org-edit-src-content-indentation 0
        org-edit-timestamp-down-means-later t
        org-agenda-start-on-weekday nil
        org-agenda-span 1
        org-agenda-include-diary t
        org-agenda-window-setup 'current-window
        org-fast-tag-selection-single-key 'expert
        org-export-kill-product-buffer-when-displayed t
        org-startup-folded t
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
        org-refile-allow-creating-parent-nodes 'confirm
        org-outline-path-complete-in-steps nil
        ;; https://endlessparentheses.com/changing-the-org-mode-ellipsis.html
        ;; org-ellipsis " ▼ "
        org-ellipsis "⤵"
        org-todo-keywords (quote ((sequence "TODO(t)" "STARTED(s)" "KEEP(k)" "|" "DONE(d)")
                                  (sequence "WAITING(w@/!)" "SOMEDAY(S)" "PROJECT(P)" "|" "CANCELLED(c)")))
        ;; org-todo-keywords (quote ((sequence "TODO(t)" "STARTED(s)" "KEEP(k)" "|" "DONE(d!/!)")
        ;;                           (sequence "WAITING(w@/!)" "SOMEDAY(S)" "PROJECT(P@)" "|" "CANCELLED(c@/!)")))
        org-todo-keyword-faces (quote (("TODO" :foreground "red" :weight bold)
                                       ("STARTED" :foreground "yellow" :weight bold)
                                       ("KEEP" :foreground "purple" :weight bold)
                                       ("DONE" :foreground "forest green" :weight bold)
                                       ("WAITING" :foreground "orange" :weight bold)
                                       ("SOMEDAY" :foreground "magenta" :weight bold)
                                       ("CANCELLED" :foreground "forest green" :weight bold)
                                       ("PROJECT" :foreground "blue" :weight bold)))

        org-imenu-depth 9
        ;; @see http://irreal.org/blog/1
        org-src-fontify-natively t))


(defun org-insert-src-block (src-code-type)
  "Insert a `SRC-CODE-TYPE' type source code block in org-mode."
  (interactive
   (let ((src-code-types
          '("emacs-lisp" "python" "C" "sh" "java" "js" "clojure" "C++" "css"
            "calc" "lua" "go" "asymptote" "dot" "gnuplot" "ledger" "lilypond" "mscgen"
            "octave" "oz" "plantuml" "R" "sass" "screen" "sql" "awk" "ditaa"
            "haskell" "latex" "lisp" "matlab" "ocaml" "org" "perl" "ruby"
            "scheme" "sqlite")))
     (list (ido-completing-read "Source code type: " src-code-types))))
  (progn
    (newline-and-indent)
    (insert (format "\t#+BEGIN_SRC %s\n" src-code-type))
    (newline-and-indent)
    (insert "\t#+END_SRC\n")
    (previous-line 2)
    (org-edit-src-code)))


(add-hook 'org-mode-hook '(lambda ()
                            ;; turn on flyspell-mode by default
                            ;; (flyspell-mode 1)
                            ;; C-TAB for expanding
                            ;; (local-set-key (kbd "C-<tab>")
                                           ;; 'yas/expand-from-trigger-key)
                            ;; keybinding for editing source code blocks
                            (local-set-key (kbd "C-c s e")
                                           'org-edit-src-code)
                            ;; keybinding for inserting code blocks
                            (local-set-key (kbd "C-c s i")
                                           'org-insert-src-block)
                            ))

(provide 'init-org)
