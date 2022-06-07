;; -*- coding: utf-8; lexical-binding: t; -*-

(setq w3m-coding-system 'utf-8
      w3m-file-coding-system 'utf-8
      w3m-file-name-coding-system 'utf-8
      w3m-input-coding-system 'utf-8
      w3m-output-coding-system 'utf-8
      ;; emacs-w3m will test the ImageMagick support for png32
      ;; and create files named "png32:-" everywhere
      w3m-imagick-convert-program nil
      w3m-terminal-coding-system 'utf-8
      w3m-use-cookies t
      w3m-cookie-accept-bad-cookies t
      w3m-home-page "https://www.duckduckgo.com"
      w3m-command-arguments       '("-F" "-cookie")
      w3m-mailto-url-function     'compose-mail
      browse-url-browser-function 'w3m
      ;; use shr to view html mail which is dependent on libxml
      ;; I prefer w3m. That's emacs 24.3+ default setup.
      ;; If you prefer colored mail body and other advanced features,
      ;; you can either comment out below line and let Emacs decide the
      ;; best html mail rendering engine, or "(setq mm-text-html-renderer 'shr)"
      ;; in "~/.gnus.el"
      ;; mm-text-html-renderer 'w3m ; I prefer w3m
      w3m-use-toolbar t
      ;; show images in the browser
      ;; setq w3m-default-display-inline-images t
      ;; w3m-use-tab     nil
      w3m-confirm-leaving-secure-page nil
      w3m-search-default-engine "g"
      w3m-key-binding 'info)

;; C-u S g RET <search term> RET in w3m
(with-eval-after-load 'w3m-search
  (defvar w3m-search-engine-alist) ; remove compiling warning
  (setq w3m-search-engine-alist
        '(("g" "https://www.duckduckgo.com/search?q=%s" utf-8)
          ;; stackoverflow search
          ("q" "https://www.duckduckgo.com?q=%s+site:stackoverflow.com" utf-8)
          ;; wikipedia
          ("w" "https://en.wikipedia.org/wiki/Special:Search?search=%s" utf-8)
          ;; online dictionary
          ("d" "https://dictionary.reference.com/search?q=%s" utf-8)
          ;; financial dictionary
          ("f" "https://financial-dictionary.thefreedictionary.com/%s" utf-8))))

(defvar my-w3m-global-keyword nil
  "`w3m-display-hook' searches buffer with the keyword.")

(defun my-w3m-guess-keyword (&optional encode-space-with-plus)
  "Guess keyword to search with ENCODE-SPACE-WITH-PLUS."
  (my-ensure 'w3m)
  (let* ((keyword (my-use-selected-string-or-ask "Enter keyword:"))
         (encoded-keyword (w3m-url-encode-string (setq my-w3m-global-keyword keyword))))
    ;; some search requires plus sign to replace space
    (if encode-space-with-plus
        (replace-regexp-in-string "%20" " " encoded-keyword)
      encoded-keyword)))

(defun my-w3m-customized-search-api (search-engine &optional encode-space-with-plus)
  (my-ensure 'w3m)
  (w3m-search search-engine (my-w3m-guess-keyword encode-space-with-plus)))

(defun my-w3m-stackoverflow-search ()
  (interactive)
  (my-w3m-customized-search-api "q"))

(defun my-w3m-generic-search ()
  "Google search keyword"
  (interactive)
  (my-w3m-customized-search-api "g"))

(defun my-w3m-search-financial-dictionary ()
  "Search financial dictionary."
  (interactive)
  (my-w3m-customized-search-api "f" t))

(defun my-w3m-mode-hook-setup ()
  (w3m-lnum-mode 1)
  (local-set-key (kbd ";") 'my-w3m-lnum-follow))

(add-hook 'w3m-mode-hook 'w3m-mode-hook-setup)

; {{ Search using external browser
(setq browse-url-generic-program
      (cond
       (*is-a-mac* ; mac
        "open")
       (*unix* ; linux or unix
        ;; prefer Chrome than Firefox
        (or (executable-find "google-chrome")
            (executable-find "firefox")))
       (t
        ;; Windows: you need add "firefox.exe" to environment variable PATH
        ;; @see https://en.wikipedia.org/wiki/PATH_(variable)
        (executable-find "firefox")
        ;; if you prefer chrome
        ;; (executable-find "chrome")
        )))

(setq browse-url-browser-function 'browse-url-generic)

;; use external browser to search programming stuff
(defun my-w3m-hacker-search ()
  "Search on all programming related sites in external browser"
  (interactive)
  (let ((keyword (my-w3m-guess-keyword)))
    ;; google
    (browse-url-generic (concat "https://www.duckduckgo.com/?q=%22"
                                keyword
                                "%22"
                                (if buffer-file-name
									(concat "+filetype%3A" (file-name-extension buffer-file-name))
									"")))
    ;; stackoverflow.com
    (browse-url-generic (concat "https://www.duckduckgo.com/?q="
                                keyword
                                "+site:stackoverflow.com" ))))
;; }}

(defun my-w3m-open-link-or-image-or-url ()
  "Opens current link or image or current page's uri in other browser."
  (interactive)
  (let* (url)
    (when (or (string= major-mode "w3m-mode") (string= major-mode "gnus-article-mode"))
      (setq url (w3m-anchor))
      (if (or (not url) (string= url "buffer://"))
          (setq url (or (w3m-image) w3m-current-url))))
    (browse-url-generic (if url url (car (browse-url-interactive-arg "URL: "))))))

(defun my-w3m-encode-specials (str)
  (setq str (replace-regexp-in-string "(" "%28" str))
  (setq str (replace-regexp-in-string ")" "%29" str))
  (setq str (replace-regexp-in-string ")" "%20" str)))

(defun my-w3m-open-with-mplayer ()
  "Open the media file embedded."
  (interactive)
  (let (url cmd str)
    (when (memq major-mode '(w3m-mode gnus-article-mode))
      ;; weird, `w3m-anchor' fail to extract url while `w3m-image' can
      (unless (setq url (or (w3m-anchor) (w3m-image)))
        (save-excursion
          (goto-char (point-min))
          (when (string-match "^Archived-at: <?\\([^ <>]*\\)>?" (setq str (my-buffer-str)))
            (setq url (match-string 1 str)))))
      (setq url (my-w3m-encode-specials url))
      (setq cmd (format "%s -cache 2000 %s &" (my-guess-mplayer-path) url))
      (when (string= url "buffer://")
        ;; cache 2M data and don't block UI
        (setq cmd (my-guess-image-viewer-path url t))))
    (if url (shell-command cmd))))

(defun my-w3m-subject-to-target-filename ()
  (let (rlt str)
    (save-excursion
      (goto-char (point-min))
      ;; first line in email could be some hidden line containing NO to field
      (setq str (my-buffer-str)))
    ;; (message "str=%s" str)
    (if (string-match "^Subject: \\(.+\\)" str)
        (setq rlt (match-string 1 str)))
    ;; clean the timestamp at the end of subject
    (setq rlt (replace-regexp-in-string "[ 0-9_.'/-]+$" "" rlt))
    (setq rlt (replace-regexp-in-string "'s " " " rlt))
    (setq rlt (replace-regexp-in-string "[ ,_'/-]+" "-" rlt))
    rlt))

(defun my-w3m-download-rss-stream ()
  "Download rss stream."
  (interactive)
  (when (or (string= major-mode "w3m-mode") (string= major-mode "gnus-article-mode"))
    (let* ((url (w3m-anchor)) cmd)
      (cond
       ((or (not url) (string= url "buffer://"))
        (message "This link is not video/audio stream."))
       (t
        (setq cmd (format "curl -L %s > %s.%s"  url (my-w3m-subject-to-target-filename) (file-name-extension url)))
        (kill-new cmd)
        (my-pclip cmd)
        (message "%s => clipboard/kill-ring" cmd))))))

(with-eval-after-load 'w3m
  (define-key w3m-mode-map (kbd "C-c b") 'my-w3m-open-link-or-image-or-url)
  (add-hook 'w3m-display-hook
            (lambda (url)
              (let* ((title (or w3m-current-title url)))
                (when my-w3m-global-keyword
                  ;; search keyword twice, first is url, second is your input,
                  ;; third is actual result
                  (goto-char (point-min))
                  (search-forward-regexp (replace-regexp-in-string " " ".*" my-w3m-global-keyword)  (point-max) t 3)
                  ;; move the cursor to the beginning of word
                  (backward-char (length my-w3m-global-keyword))
                  ;; cleanup for next search
                  (setq my-w3m-global-keyword nil))
                ;; rename w3m buffer
                (rename-buffer
                 (format "*w3m: %s*"
                         (substring title 0 (min 50 (length title)))) t)))))
(provide 'init-emacs-w3m)
