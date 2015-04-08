(setq w3m-coding-system 'utf-8
      w3m-file-coding-system 'utf-8
      w3m-file-name-coding-system 'utf-8
      w3m-input-coding-system 'utf-8
      w3m-output-coding-system 'utf-8
      w3m-terminal-coding-system 'utf-8)
(setq w3m-use-cookies t)
(setq w3m-cookie-accept-bad-cookies t)
(setq w3m-home-page
      (if (file-readable-p "~/html/home.html")
        (concat "file://" (expand-file-name "~/html/home.html"))
        "http://www.google.com.au"))

(setq w3m-use-toolbar t
      ;w3m-use-tab     nil
      w3m-key-binding 'info)

;; show images in the browser
;(setq w3m-default-display-inline-images t)

(setq w3m-search-default-engine "g")

(defun w3m-get-url-from-search-engine-alist (k l)
  (let (rlt)
    (if (listp l)
      (if (string= k (caar l))
          (setq rlt (nth 1 (car l)))
        (setq rlt (w3m-get-url-from-search-engine-alist k (cdr l)))))
    rlt))

(defun w3m-set-url-from-search-engine-alist (k l url)
    (if (listp l)
      (if (string= k (caar l))
          (setcdr (car l) (list url))
        (w3m-set-url-from-search-engine-alist k (cdr l) url))))

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
        ;; javascript seawrch on mozilla.org
        ("j" "http://www.google.com.au/search?q=%s+site:developer.mozilla.org" utf-8)))

(defun w3m-google-by-filetype ()
  (interactive)
  (unless (featurep 'w3m)
    (require 'w3m))
  (let ((thing (if (region-active-p)
                   (buffer-substring-no-properties (region-beginning) (region-end))
                 (thing-at-point 'symbol)))
        (old-url (w3m-get-url-from-search-engine-alist "s" w3m-search-engine-alist))
        new-url)
    (when buffer-file-name
      (setq new-url (replace-regexp-in-string
                     "filetype:.*"
                     (concat "filetype:" (file-name-extension buffer-file-name))
                     old-url))
      (w3m-set-url-from-search-engine-alist "s" w3m-search-engine-alist new-url))
    ;; change the url to search current file type
    (w3m-search "s" thing)
    ;; restore the default url
    (w3m-set-url-from-search-engine-alist "s" w3m-search-engine-alist old-url)))

(setq w3m-command-arguments       '("-F" "-cookie")
      w3m-mailto-url-function     'compose-mail
      browse-url-browser-function 'w3m
      mm-text-html-renderer       'w3m)

(defun w3m-mode-hook-setup ()
  (w3m-lnum-mode 1))

(add-hook 'w3m-mode-hook 'w3m-mode-hook-setup)

; external browser
(setq browse-url-generic-program
      (cond
       (*is-a-mac* "open")
       (*linux* (executable-find "firefox"))
       ))

(setq browse-url-browser-function 'browse-url-generic)

;; use external browser to search programming stuff
(defun w3mext-hacker-search ()
  "search word under cursor in google code search and stackoverflow.com"
  (interactive)
  (unless (featurep 'w3m)
    (require 'w3m))
  (let ((keyword (w3m-url-encode-string (thing-at-point 'symbol))))
    ;; google
    (browse-url-generic (concat "http://www.google.com.au/search?hl=en&q=%22"
                                keyword
                                "%22"
                                (if buffer-file-name
									(concat "+filetype%3A" (file-name-extension buffer-file-name))
									"")  ))
    (browse-url-generic (concat "http://www.google.com.au/search?hl=en&q="
                                keyword
                                "+site:stackoverflow.com" ))
    ;; koders.com
    (browse-url-generic (concat "http://code.ohloh.net/search?s=\""
                                keyword
                                "\"&browser=Default&mp=1&ml=1&me=1&md=1&filterChecked=true" ))
    ))

(defun w3mext-open-link-or-image-or-url ()
  "Opens the current link or image or current page's uri or any url-like text under cursor in firefox."
  (interactive)
  (let (url)
    (if (or (string= major-mode "w3m-mode") (string= major-mode "gnus-article-mode"))
        (setq url (or (w3m-anchor) (w3m-image) w3m-current-url)))
    (browse-url-generic (if url url (car (browse-url-interactive-arg "URL: "))))
    ))
(global-set-key (kbd "C-c b") 'w3mext-open-link-or-image-or-url)

(defun w3mext-search-js-api-mdn ()
  "search current symbol under cursor in Mozilla Developer Network (MDN)"
  (interactive)
  (let ((keyword (thing-at-point 'symbol)))
    (w3m-search "j" keyword)
    ))

(add-hook 'prog-mode-hook '( lambda () (local-set-key (kbd "C-c ; h") 'w3mext-hacker-search)))

(provide 'init-emacs-w3m)
