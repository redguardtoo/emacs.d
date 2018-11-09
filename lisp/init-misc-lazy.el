;; -*- coding: utf-8; lexical-binding: t; -*-

(setq auto-mode-alist
      (cons '("\\.textile\\'" . textile-mode) auto-mode-alist))

(transient-mark-mode t)

(recentf-mode 1)

(global-auto-revert-mode)
(setq global-auto-revert-non-file-buffers t
      auto-revert-verbose nil)

(add-to-list 'auto-mode-alist '("\\.[Cc][Ss][Vv]\\'" . csv-mode))

;;----------------------------------------------------------------------------
;; Don't disable narrowing commands
;;----------------------------------------------------------------------------
(put 'narrow-to-region 'disabled nil)
(put 'narrow-to-page 'disabled nil)
(put 'narrow-to-defun 'disabled nil)

;; But don't show trailing whitespace in SQLi, inf-ruby etc.
(add-hook 'comint-mode-hook
          (lambda () (setq show-trailing-whitespace nil)))

;;----------------------------------------------------------------------------
;; Page break lines
;;----------------------------------------------------------------------------
(global-page-break-lines-mode)

(column-number-mode 1)

;; my screen is tiny, so I use minimum eshell prompt
(setq eshell-prompt-function
       (lambda ()
         (concat (getenv "USER") " $ ")))


;; I'm in Australia now, so I set the locale to "en_AU"
(defun insert-date (prefix)
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
  "length of a region"
  (interactive)
  (message (format "%d" (- (region-end) (region-beginning)))))


;; {{ imenu tweakment
(defvar rimenu-position-pair nil "positions before and after imenu jump")
(add-hook 'imenu-after-jump-hook
          (lambda ()
            (let* ((start-point (marker-position (car mark-ring)))
                   (end-point (point)))
              (setq rimenu-position-pair (list start-point end-point)))))

(defun rimenu-jump ()
  "Jump to the closest before/after position of latest imenu jump."
  (interactive)
  (when rimenu-position-pair
    (let* ((p1 (car rimenu-position-pair))
           (p2 (cadr rimenu-position-pair)))

      ;; jump to the far way point of the rimenu-position-pair
      (if (< (abs (- (point) p1))
             (abs (- (point) p2)))
          (goto-char p2)
        (goto-char p1)))))
;; }}

;; {{ my blog tools
(defun open-blog-on-current-month ()
  (interactive)
  (find-file (file-truename (concat "~/blog/" (format-time-string "%Y-%m") ".org"))))

(defun insert-blog-version ()
  "Insert version of my blog post."
  (interactive)
  (insert (format-time-string "%Y%m%d")))
;; }}

;; show ascii table
(defun ascii-table ()
  "Print the ascii table. Based on a defun by Alex Schroeder <asc@bsiag.com>"
  (interactive)
  (switch-to-buffer "*ASCII*")
  (erase-buffer)
  (insert (format "ASCII characters up to number %d.\n" 254))
  (let* ((i 0))
    (while (< i 254)
      (setq i (+ i 1))
      (insert (format "%4d %c\n" i i))))
  (beginning-of-buffer))

;; {{ direx
(global-set-key (kbd "C-x C-j") 'direx:jump-to-directory)
;; }}

(defun display-line-number ()
  "Display current line number in mini-buffer."
  (interactive)
  (message "line number:%d" (line-number-at-pos)))

;; {{ unique lines
(defun uniquify-all-lines-region (start end)
  "Find duplicate lines in region START to END keeping first occurrence."
  (interactive "*r")
  (save-excursion
    (let* ((end (copy-marker end)))
      (while
          (progn
            (goto-char start)
            (re-search-forward "^\\(.*\\)\n\\(\\(.*\n\\)*\\)\\1\n" end t))
        (replace-match "\\1\n\\2")))))

(defun uniquify-all-lines-buffer ()
  "Delete duplicate lines in buffer and keep first occurrence."
  (interactive "*")
  (uniquify-all-lines-region (point-min) (point-max)))
;; }}

(defun insert-file-link-from-clipboard ()
  "Make sure the full path of file exist in clipboard.
This command will convert full path into relative path.
Then insert it as a local file link in `org-mode'."
  (interactive)
  (insert (format "[[file:%s]]" (file-relative-name (my-gclip)))))

(defun font-file-to-base64 (file)
  "Convert font file into base64 encoded string."
  (let* ((str "")
         (file-base (file-name-sans-extension file))
         (file-ext (file-name-extension file)))
    (when (file-exists-p file)
        (with-temp-buffer
          (shell-command (concat "cat " file "|base64") 1)
          (setq str (replace-regexp-in-string "\n" "" (buffer-string)))))
    str))

(defun convert-binary-to-css-code ()
  "Convert binary (image, font...) into css code."
  (interactive)
  (let* (str
        (file (read-file-name "The path of image:"))
        (file-ext (file-name-extension file))
        (file-base (file-name-sans-extension file))
        rlt)
    (cond
     ((member file-ext '("ttf" "eot" "woff"))
      (setq rlt (concat "@font-face {\n"
                        "  font-family: familarName;\n"
                        "  src: url('data:font/eot;base64," (font-file-to-base64 (concat file-base ".eot")) "') format('embedded-opentype'),\n"
                        "       url('data:application/x-font-woff;base64," (font-file-to-base64 (concat file-base ".woff")) "') format('woff'),\n"
                        "       url('data:font/ttf;base64," (font-file-to-base64 (concat file-base ".ttf")) "') format('truetype');"
                        "\n}"
                        )))
     (t
      (with-temp-buffer
        (shell-command (concat "cat " file "|base64") 1)
        (setq str (replace-regexp-in-string "\n" "" (buffer-string))))
      (setq rlt (concat "background:url(\"data:image/"
                          file-ext
                          ";base64,"
                          str
                          "\") no-repeat 0 0;"
                          ))))
    (kill-new rlt)
    (copy-yank-str rlt)
    (message "css code => clipboard & yank ring")))



(defun current-font-face ()
  "Get the font face under cursor."
  (interactive)
  (let* ((rlt (format "%S" (get-text-property (point) 'face))))
    (kill-new rlt)
    (copy-yank-str rlt)
    (message "%s => clipboard & yank ring" rlt)))

(defun current-thing-at-point ()
  "Print current thing at point."
  (interactive)
  (message "thing = %s" (thing-at-point 'symbol)))

;; {{ copy the file-name/full-path in dired buffer into clipboard
;; `w` => copy file name
;; `C-u 0 w` => copy full path
(defadvice dired-copy-filename-as-kill (after dired-filename-to-clipboard activate)
  (with-temp-buffer
    (insert (current-kill 0))
    (shell-command-on-region (point-min) (point-max)
                             (cond
                              ((eq system-type 'cygwin) "putclip")
                              ((eq system-type 'darwin) "pbcopy")
                              (t "xsel -ib"))))
  (message "%s => clipboard" (current-kill 0)))
;; }}

(defun open-readme-in-project ()
  "Open READ in project root."
  (interactive)
  (unless (featurep 'find-file-in-project) (require 'find-file-in-project))
  (let* ((root-dir (ffip-project-root))
         (filename (concat root-dir "README.org")))
    (if (not (file-exists-p filename))
        (setq filename (concat root-dir "README.md")))
    (if (file-exists-p filename)
        (switch-to-buffer (find-file-noselect filename nil nil))
      (message "NO README.org or README.md found!"))))

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

(defun strip-convert-lines-into-one-big-string (beg end)
  "Strip and convert selected lines into one string which is copied into `kill-ring'.
When `transient-mark-mode' is enabled and no region is active then only the
current line is acted upon.
If BEG or END is in the middle of a line, entire line is copied.
Current position is preserved."
  (interactive "r")
  (let* (str (orig-pos (point-marker)))
    (save-restriction
      (widen)
      (when (and transient-mark-mode (not (use-region-p)))
        (setq beg (line-beginning-position)
              end (line-beginning-position 2)))

      (goto-char beg)
      (setq beg (line-beginning-position))
      (goto-char end)
      (unless (= (point) (line-beginning-position))
        (setq end (line-beginning-position 2)))

      (goto-char beg)
      (setq str (replace-regexp-in-string "[ \t]*\n" "" (replace-regexp-in-string "^[ \t]+" "" (buffer-substring-no-properties beg end))))
      ;; (message "str=%s" str)
      (kill-new str)
      (goto-char orig-pos))))

;; Don't disable narrowing commands
(put 'narrow-to-region 'disabled nil)
(put 'narrow-to-page 'disabled nil)
(put 'narrow-to-defun 'disabled nil)

;; Ctrl-X, u/l  to upper/lowercase regions without confirm
(put 'downcase-region 'disabled nil)
(put 'upcase-region 'disabled nil)

;; midnight mode purges buffers which haven't been displayed in 3 days
(require 'midnight)
(setq midnight-mode t)

(add-auto-mode 'tcl-mode "Portfile\\'")

;; {{go-mode
(local-require 'go-mode-load)
;; }}

;; someone mentioned that blink cursor could slow Emacs24.4
;; I couldn't care less about cursor, so turn it off explicitly
;; https://github.com/redguardtoo/emacs.d/issues/208
;; but somebody mentioned that blink cursor is needed in dark theme
;; so it should not be turned off by default
;; (blink-cursor-mode -1)

(defun create-scratch-buffer ()
  "Create a new scratch buffer."
  (interactive)
  (let* ((n 0) bufname)
    (while (progn
             (setq bufname (concat "*scratch"
                                   (if (= n 0) "" (int-to-string n))
                                   "*"))
             (setq n (1+ n))
             (get-buffer bufname)))
    (switch-to-buffer (get-buffer-create bufname))
    (emacs-lisp-mode)))

(defun cleanup-buffer-safe ()
  "Perform a bunch of safe operations on the whitespace content of a buffer.
Does not indent buffer, because it is used for a before-save-hook, and that
might be bad."
  (interactive)
  (untabify (point-min) (point-max))
  (delete-trailing-whitespace))

(defun cleanup-buffer ()
  "Perform a bunch of operations on the whitespace content of a buffer.
Including indent-buffer, which should not be called automatically on save."
  (interactive)
  (cleanup-buffer-safe)
  (indent-region (point-min) (point-max)))

;; {{ easygpg setup
;; @see http://www.emacswiki.org/emacs/EasyPG#toc4
(defadvice epg--start (around advice-epg-disable-agent disable)
  "Make `epg--start' not able to find a gpg-agent."
  (let ((agent (getenv "GPG_AGENT_INFO")))
    (setenv "GPG_AGENT_INFO" nil)
    ad-do-it
    (setenv "GPG_AGENT_INFO" agent)))

(unless (string-match-p "^gpg (GnuPG) 1.4"
                        (shell-command-to-string (format "%s --version" epg-gpg-program)))

  ;; `apt-get install pinentry-tty` if using emacs-nox
  ;; Create `~/.gnupg/gpg-agent.conf' container one line `pinentry-program /usr/bin/pinentry-curses`
  (setq epa-pinentry-mode 'loopback))
;; }}

(eval-after-load "which-function"
  '(progn
     (add-to-list 'which-func-modes 'org-mode)))
(which-function-mode 1)

(provide 'init-misc-lazy)
;;; init-misc-lazy.el ends here

