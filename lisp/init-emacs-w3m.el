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
      w3m-home-page "http://www.google.com.au"
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

(defun w3m-get-url-from-search-engine-alist (k l)
  (let (rlt)
    (if (listp l)
      (if (string= k (caar l))
          (setq rlt (nth 1 (car l)))
        (setq rlt (w3m-get-url-from-search-engine-alist k (cdr l)))))
    rlt))

;; C-u S g RET <search term> RET in w3m
(setq w3m-search-engine-alist
      '(("g" "http://www.google.com.au/search?q=%s" utf-8)
        ;; stackoverflow search
        ("q" "http://www.google.com.au/search?q=%s+site:stackoverflow.com" utf-8)
        ;; elisp code search
        ("s" "http://www.google.com.au/search?q=%s+filetype:el"  utf-8)
        ;; wikipedia
        ("w" "http://en.wikipedia.org/wiki/Special:Search?search=%s" utf-8)
        ;; online dictionary
        ("d" "http://dictionary.reference.com/search?q=%s" utf-8)
        ;; java google search
        ("java" "https://www.google.com.au/search?q=java+%s" utf-8)
        ;; financial dictionary
        ("f" "http://financial-dictionary.thefreedictionary.com/%s" utf-8)
        ;; javascript search on mozilla.org
        ("j" "http://www.google.com.au/search?q=%s+site:developer.mozilla.org" utf-8)))

(defun w3m-set-url-from-search-engine-alist (k l url)
    (if (listp l)
      (if (string= k (caar l))
          (setcdr (car l) (list url))
        (w3m-set-url-from-search-engine-alist k (cdr l) url))))

(defvar w3m-global-keyword nil
  "`w3m-display-hook' must search current buffer with this keyword twice if not nil")

(defun w3m-guess-keyword (&optional encode-space-with-plus)
  (unless (featurep 'w3m) (require 'w3m))
  (let* ((keyword (my-use-selected-string-or-ask "Enter keyword:"))
         (encoded-keyword (w3m-url-encode-string (setq w3m-global-keyword keyword))))
    ;; some search requires plus sign to replace space
    (if encode-space-with-plus
        (replace-regexp-in-string "%20" " " encoded-keyword)
      encoded-keyword)))

(defun w3m-customized-search-api (search-engine &optional encode-space-with-plus)
  (unless (featurep 'w3m) (require 'w3m))
  (w3m-search search-engine (w3m-guess-keyword encode-space-with-plus)))

(defun w3m-stackoverflow-search ()
  (interactive)
  (w3m-customized-search-api "q"))

(defun w3m-java-search ()
  (interactive)
  (w3m-customized-search-api "java"))

(defun w3m-google-search ()
  "Google search keyword"
  (interactive)
  (w3m-customized-search-api "g"))

(defun w3m-google-by-filetype ()
  "Google search 'keyword filetype:file-extension'"
  (interactive)
  (unless (featurep 'w3m) (require 'w3m))
  (let ((old-url (w3m-get-url-from-search-engine-alist "s" w3m-search-engine-alist))
        new-url)
    ;; change the url to search current file type
    (when buffer-file-name
      (setq new-url (replace-regexp-in-string
                     "filetype:.*"
                     (concat "filetype:" (file-name-extension buffer-file-name))
                     old-url))
      (w3m-set-url-from-search-engine-alist "s" w3m-search-engine-alist new-url))
    (w3m-customized-search-api "s")
    ;; restore the default url
    (w3m-set-url-from-search-engine-alist "s" w3m-search-engine-alist old-url)))

(defun w3m-search-financial-dictionary ()
  "Search financial dictionary"
  (interactive)
  (w3m-customized-search-api "f" t))

(defun w3m-search-js-api-mdn ()
  "Search at Mozilla Developer Network (MDN)"
  (interactive)
  (w3m-customized-search-api "j"))

(defun w3m-mode-hook-setup ()
  (w3m-lnum-mode 1))

(add-hook 'w3m-mode-hook 'w3m-mode-hook-setup)

; {{ Search using external browser
(setq browse-url-generic-program
      (cond
       (*is-a-mac* ; mac
        "open")
       (*unix* ; linux or unix
        (executable-find "firefox"))
       (t
        ;; Windows: you need add "firefox.exe" to environment variable PATH
        ;; @see https://en.wikipedia.org/wiki/PATH_(variable)
        (executable-find "firefox")
        ;; if you prefer chrome
        ;; (executable-find "chrome")
        )))

(setq browse-url-browser-function 'browse-url-generic)

;; use external browser to search programming stuff
(defun w3mext-hacker-search ()
  "Search on all programming related sites in external browser"
  (interactive)
  (let ((keyword (w3m-guess-keyword)))
    ;; google
    (browse-url-generic (concat "http://www.google.com.au/search?hl=en&q=%22"
                                keyword
                                "%22"
                                (if buffer-file-name
									(concat "+filetype%3A" (file-name-extension buffer-file-name))
									"")))
    ;; stackoverflow.com
    (browse-url-generic (concat "http://www.google.com.au/search?hl=en&q="
                                keyword
                                "+site:stackoverflow.com" ))
    ;; koders.com
    (browse-url-generic (concat "http://code.ohloh.net/search?s=\""
                                keyword
                                "\"&browser=Default&mp=1&ml=1&me=1&md=1&filterChecked=true" ))
    ))
;; }}

(defun w3mext-open-link-or-image-or-url ()
  "Opens the current link or image or current page's uri or any url-like text under cursor in firefox."
  (interactive)
  (let* (url)
    (when (or (string= major-mode "w3m-mode") (string= major-mode "gnus-article-mode"))
      (setq url (w3m-anchor))
      (if (or (not url) (string= url "buffer://"))
          (setq url (or (w3m-image) w3m-current-url))))
    (browse-url-generic (if url url (car (browse-url-interactive-arg "URL: "))))))

(defun w3mext-encode-specials (str)
  (setq str (replace-regexp-in-string "(" "%28" str))
  (setq str (replace-regexp-in-string ")" "%29" str))
  (setq str (replace-regexp-in-string ")" "%20" str)))

(defun w3mext-open-with-mplayer ()
  (interactive)
  (let (url cmd str)
    (when (or (string= major-mode "w3m-mode") (string= major-mode "gnus-article-mode"))
      ;; weird, `w3m-anchor' fail to extract url while `w3m-image' can
      (setq url (or (w3m-anchor) (w3m-image)))
      (unless url
        (save-excursion
          (goto-char (point-min))
          (when (string-match "^Archived-at: <?\\([^ <>]*\\)>?" (setq str (my-buffer-str)))
            (setq url (match-string 1 str)))))
      (setq url (w3mext-encode-specials url))
      (setq cmd (format "%s -cache 2000 %s &" (my-guess-mplayer-path) url))
      (when (string= url "buffer://")
        ;; cache 2M data and don't block UI
        (setq cmd (my-guess-image-viewer-path url t))))
    (if url (shell-command cmd))))

(defun w3mext-subject-to-target-filename ()
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

(defun w3mext-download-rss-stream ()
  (interactive)
  (let (url cmd)
    (when (or (string= major-mode "w3m-mode") (string= major-mode "gnus-article-mode"))
      (setq url (w3m-anchor))
      (cond
       ((or (not url) (string= url "buffer://"))
        (message "This link is not video/audio stream."))
       (t
        (setq cmd (format "curl -L %s > %s.%s"  url (w3mext-subject-to-target-filename) (file-name-extension url)))
        (kill-new cmd)
        (my-pclip cmd)
        (message "%s => clipd/kill-ring" cmd))))
    ))

(eval-after-load 'w3m
  '(progn
     (define-key w3m-mode-map (kbd "C-c b") 'w3mext-open-link-or-image-or-url)
     (add-hook 'w3m-display-hook
               (lambda (url)
                 (let ((title (or w3m-current-title url)))
                   (when w3m-global-keyword
                     ;; search keyword twice, first is url, second is your input,
                     ;; third is actual result
                     (goto-char (point-min))
                     (search-forward-regexp (replace-regexp-in-string " " ".*" w3m-global-keyword)  (point-max) t 3)
                     ;; move the cursor to the beginning of word
                     (backward-char (length w3m-global-keyword))
                     ;; cleanup for next search
                     (setq w3m-global-keyword nil))
                   ;; rename w3m buffer
                   (rename-buffer
                    (format "*w3m: %s*"
                            (substring title 0 (min 50 (length title)))) t))))))
(provide 'init-emacs-w3m)
