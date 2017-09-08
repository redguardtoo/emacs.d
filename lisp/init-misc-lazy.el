;;; init-misc-lazy.el --- misc setup loaded later

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
  (let ((format (cond
                 ((not prefix) "%d.%m.%Y")
                 ((equal prefix '(4)) "%Y-%m-%d")
                 ((equal prefix '(16)) "%d %B %Y")))
        )
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
            (let ((start-point (marker-position (car mark-ring)))
                  (end-point (point)))
              (setq rimenu-position-pair (list start-point end-point)))))

(defun rimenu-jump ()
  "jump to the closest before/after position of latest imenu jump"
  (interactive)
  (when rimenu-position-pair
    (let ((p1 (car rimenu-position-pair))
          (p2 (cadr rimenu-position-pair)))

      ;; jump to the far way point of the rimenu-position-pair
      (if (< (abs (- (point) p1))
             (abs (- (point) p2)))
          (goto-char p2)
          (goto-char p1))
      )))
;; }}

;; {{ my blog tools
(defun open-blog-on-current-month ()
  (interactive)
  (let (blog)
   (setq blog (file-truename (concat "~/blog/" (format-time-string "%Y-%m") ".org")) )
   (find-file blog)))

(defun insert-blog-version ()
  "insert version of my blog post"
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
  (let ((i 0))
    (while (< i 254)
           (setq i (+ i 1))
           (insert (format "%4d %c\n" i i))))
  (beginning-of-buffer))

;; {{ grep and kill-ring
(defun grep-pattern-into-list (regexp)
  (let ((s (buffer-string))
        (pos 0)
        item
        items)
    (while (setq pos (string-match regexp s pos))
      (setq item (match-string-no-properties 0 s))
      (setq pos (+ pos (length item)))
      (if (not (member item items))
          (add-to-list 'items item)
        ))
    items))

(defun grep-pattern-into-kill-ring (regexp)
  "Find all strings matching REGEXP in current buffer.
grab matched string and insert them into kill-ring"
  (interactive
   (let* ((regexp (read-regexp "grep regex:")))
     (list regexp)))
  (let (items rlt)
    (setq items (grep-pattern-into-list regexp))
    (dolist (i items)
      (setq rlt (concat rlt (format "%s\n" i)))
      )
    (kill-new rlt)
    (message "matched strings => kill-ring")
    rlt))

(defun grep-pattern-jsonize-into-kill-ring (regexp)
  "Find all strings matching REGEXP in current buffer.
grab matched string, jsonize them, and insert into kill ring"
  (interactive
   (let* ((regexp (read-regexp "grep regex:")))
     (list regexp)))
  (let (items rlt)
    (setq items (grep-pattern-into-list regexp))
    (dolist (i items)
      (setq rlt (concat rlt (format "%s : %s ,\n" i i)))
      )
    (kill-new rlt)
    (message "matched strings => json => kill-ring")
    rlt))

(defun grep-pattern-cssize-into-kill-ring (regexp)
  "Find all strings matching REGEXP in current buffer.
grab matched string, cssize them, and insert into kill ring"
  (interactive
   (let* ((regexp (read-regexp "grep regex:")))
     (list regexp)))
  (let (items rlt)
    (setq items (grep-pattern-into-list regexp))
    (dolist (i items)
      (setq i (replace-regexp-in-string "\\(class=\\|\"\\)" "" i))
      (setq rlt (concat rlt (format ".%s {\n}\n\n" i))))
    (kill-new rlt)
    (message "matched strings => json => kill-ring")
    rlt))
;; }}

;; {{ direx
(global-set-key (kbd "C-x C-j") 'direx:jump-to-directory)
;; }}

(defun display-line-number ()
  "display current line number in mini-buffer"
  (interactive)
  (message "line number:%d" (line-number-at-pos)))

(eval-after-load 'grep
  '(progn
     (dolist (v '("auto"
                  "target"
                  "node_modules"
                  "bower_components"
                  ".sass_cache"
                  ".cache"
                  ".git"
                  ".cvs"
                  ".svn"
                  ".hg"
                  "elpa"))
       (add-to-list 'grep-find-ignored-directories v))
     ))

;; {{ unique lines
(defun uniquify-all-lines-region (start end)
  "Find duplicate lines in region START to END keeping first occurrence."
  (interactive "*r")
  (save-excursion
    (let ((end (copy-marker end)))
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
  "Make sure the full path of file exist in clipboard. This command will convert
The full path into relative path insert it as a local file link in org-mode"
  (interactive)
  (insert (format "[[file:%s]]" (file-relative-name (my-gclip)))))

(defun font-file-to-base64 (file)
  (let ((str "")
        (file-base (file-name-sans-extension file))
        (file-ext (file-name-extension file)))

    (if (file-exists-p file)
        (with-temp-buffer
          (shell-command (concat "cat " file "|base64") 1)
          (setq str (replace-regexp-in-string "\n" "" (buffer-string)))))
    str))

(defun convert-binary-to-css-code ()
  "Convert binary (image, font...) into css"
  (interactive)
  (let (str
        rlt
        (file (read-file-name "The path of image:"))
        file-ext
        file-base)

    (setq file-ext (file-name-extension file))
    (setq file-base (file-name-sans-extension file))
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
  "get the font face under cursor"
  (interactive)
  (let ((rlt (format "%S" (get-text-property (point) 'face))))
    (kill-new rlt)
    (copy-yank-str rlt)
    (message "%s => clipboard & yank ring" rlt)))

(defun current-thing-at-point ()
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
                              (t "xsel -ib")
                              )))
  (message "%s => clipboard" (current-kill 0)))
;; }}

(defun open-readme-in-git-root-directory ()
  (interactive)
  (let (filename
        (root-dir (locate-dominating-file (file-name-as-directory (file-name-directory buffer-file-name)) ".git"))
        )
    ;; (message "root-dir=%s" root-dir)
    (and root-dir (file-name-as-directory root-dir))
    (setq filename (concat root-dir "README.org"))
    (if (not (file-exists-p filename))
        (setq filename (concat root-dir "README.md"))
      )
    ;; (message "filename=%s" filename)
    (if (file-exists-p filename)
        (switch-to-buffer (find-file-noselect filename nil nil))
      (message "NO README.org or README.md found!"))
    ))

;; from http://emacsredux.com/blog/2013/05/04/rename-file-and-buffer/
(defun vc-rename-file-and-buffer ()
  "Rename the current buffer and file it is visiting."
  (interactive)
  (let ((filename (buffer-file-name)))
    (if (not (and filename (file-exists-p filename)))
        (message "Buffer is not visiting a file!")
      (let ((new-name (read-file-name "New name: " filename)))
        (cond
         ((vc-backend filename) (vc-rename-file filename new-name))
         (t
          (rename-file filename new-name t)
          (rename-buffer new-name)
          (set-visited-file-name new-name)
          (set-buffer-modified-p nil)))))))

(defun vc-copy-file-and-rename-buffer ()
  "copy the current buffer and file it is visiting.
if the old file is under version control, the new file is added into
version control automatically"
  (interactive)
  (let ((filename (buffer-file-name)))
    (if (not (and filename (file-exists-p filename)))
        (message "Buffer is not visiting a file!")
      (let ((new-name (read-file-name "New name: " filename)))
        (copy-file filename new-name t)
        (rename-buffer new-name)
        (set-visited-file-name new-name)
        (set-buffer-modified-p nil)
        (when (vc-backend filename)
          (vc-register)
          )))))

(defun toggle-env-http-proxy ()
  "set/unset the environment variable http_proxy which w3m uses"
  (interactive)
  (let ((proxy "http://127.0.0.1:8000"))
    (if (string= (getenv "http_proxy") proxy)
        ;; clear the the proxy
        (progn
          (setenv "http_proxy" "")
          (message "env http_proxy is empty now")
          )
      ;; set the proxy
      (setenv "http_proxy" proxy)
      (message "env http_proxy is %s now" proxy))
    ))

(defun strip-convert-lines-into-one-big-string (beg end)
  "strip and convert selected lines into one big string which is copied into kill ring.
When transient-mark-mode is enabled, if no region is active then only the
current line is acted upon.

If the region begins or ends in the middle of a line, that entire line is
copied, even if the region is narrowed to the middle of a line.

Current position is preserved."
  (interactive "r")
  (let (str (orig-pos (point-marker)))
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
      (goto-char orig-pos)))
  )

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

;; Shift lines up and down with M-up and M-down
(move-text-default-bindings)

;; {{go-mode
(require 'go-mode-load)
;; }}

;; someone mentioned that blink cursor could slow Emacs24.4
;; I couldn't care less about cursor, so turn it off explicitly
;; https://github.com/redguardtoo/emacs.d/issues/208
;; but somebody mentioned that blink cursor is needed in dark theme
;; so it should not be turned off by default
;; (blink-cursor-mode -1)


(defun create-scratch-buffer nil
  "create a new scratch buffer to work in. (could be *scratch* - *scratchX*)"
  (interactive)
  (let ((n 0)
        bufname)
    (while (progn
             (setq bufname (concat "*scratch"
                                   (if (= n 0) "" (int-to-string n))
                                   "*"))
             (setq n (1+ n))
             (get-buffer bufname)))
    (switch-to-buffer (get-buffer-create bufname))
    (emacs-lisp-mode)
    ))

(defun cleanup-buffer-safe ()
  "Perform a bunch of safe operations on the whitespace content of a buffer.
Does not indent buffer, because it is used for a before-save-hook, and that
might be bad."
  (interactive)
  (untabify (point-min) (point-max))
  (delete-trailing-whitespace)
  (set-buffer-file-coding-system 'utf-8))

(defun cleanup-buffer ()
  "Perform a bunch of operations on the whitespace content of a buffer.
Including indent-buffer, which should not be called automatically on save."
  (interactive)
  (cleanup-buffer-safe)
  (indent-buffer))

;; {{ save history
;; On Corp machines, I don't have permission to access history,
;; so safe-wrap is used
(safe-wrap
 (when (file-writable-p (file-truename "~/.emacs.d/history"))
   (setq history-length 8000)
   (setq savehist-additional-variables '(search-ring regexp-search-ring kill-ring))
   (savehist-mode 1)))
;; }}

;; {{emms
(require 'emms-setup)
(emms-all)
(emms-default-players)
;; }}
(provide 'init-misc-lazy)
;;; init-misc-lazy.el ends here

