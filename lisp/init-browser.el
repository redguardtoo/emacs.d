;; -*- coding: utf-8; lexical-binding: t; -*-

(defvar my-browser-search-keyword nil
  "Searches keyword.")

(defun my-browser-guess-keyword ()
  "Guess keyword to search."
  (my-ensure 'url-util)
  (let* ((keyword (my-use-selected-string-or-ask "Enter keyword:"))
         (encoded-keyword (url-hexify-string (setq my-browser-search-keyword keyword))))
    encoded-keyword))

; {{ Search using external browser
(setq browse-url-generic-program
      (cond
       (*is-a-mac* ; mac
        "open")
       (*unix* ; linux or unix
        "xdg-open")
       (t
        ;; Windows: use default browser
        "start")))

(setq browse-url-browser-function 'browse-url-generic)

;; use external browser to search programming stuff
(defun my-browser-hacker-search ()
  "Search on all programming related sites in external browser"
  (interactive)
  (let ((keyword (my-browser-guess-keyword)))
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
                                "+site:stackoverflow.com"))))
;; }}

(defun my-browser-open-link-or-image-or-url ()
  "Opens current link or image or current page's uri in other browser."
  (interactive)
  (let (url)
    (when (memq major-mode '(eww-mode gnus-article-mode))
      (setq url (get-text-property (point) 'shr-url))
      (when (or (not url) (string= url "buffer://"))
        (setq url (eww-current-url))))
    (browse-url-generic (if url url (car (browse-url-interactive-arg "URL: "))))))

(defun my-browser-open-with-mplayer ()
  "Open the media file embedded."
  (interactive)
  (when (memq major-mode '(eww-mode gnus-article-mode))
    (let ((url (get-text-property (point) 'shr-url))
          cmd
          str)
      (unless url
        (save-excursion
          (goto-char (point-min))
          (when (string-match "^Archived-at: <?\\([^ <>]*\\)>?" (setq str (my-buffer-str)))
            (setq url (match-string 1 str)))))
      (my-ensure 'url-util)
      ;; cache 2M data and don't block UI
      (setq cmd (format "%s -cache 2048 %s &" (my-guess-mplayer-path) url))
      (when (string= url "buffer://")
        (setq cmd (my-guess-image-viewer-path url t)))
      (if url (shell-command cmd)))))

(defun my-browser-subject-to-target-filename ()
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

(defun my-browser-download-rss-stream ()
  "Download rss stream."
  (interactive)
  (when (memq major-mode '(eww-mode gnus-article-mode))
    (let* ((url (get-text-property (point) 'shr-url))
           cmd)
      (cond
       ((or (not url) (string= url "buffer://"))
        (message "This link is not video/audio stream."))
       (t
        (setq cmd (format "curl -L %s > %s.%s"  url (my-browser-subject-to-target-filename) (file-name-extension url)))
        (kill-new cmd)
        (my-pclip cmd)
        (message "%s => clipboard/kill-ring" cmd))))))

(with-eval-after-load 'eww
  (define-key eww-mode-map "f" 'eww-lnum-follow)
  (define-key eww-mode-map "F" 'eww-lnum-universal))

(provide 'init-browser)
