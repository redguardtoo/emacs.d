;; -*- coding: utf-8; lexical-binding: t; -*-

;; my private snippets, should be placed before enabling yasnippet
(setq my-yasnippets (expand-file-name "~/my-yasnippets"))

(defun my-enable-yas-minor-mode ()
  "Enable `yas-minor-mode'."
  (unless (is-buffer-file-temp) (yas-minor-mode 1)))

(add-hook 'prog-mode-hook 'my-enable-yas-minor-mode)
(add-hook 'text-mode-hook 'my-enable-yas-minor-mode)
;; {{ modes do NOT inherit from prog-mode
(add-hook 'cmake-mode-hook 'my-enable-yas-minor-mode)
(add-hook 'web-mode-hook 'my-enable-yas-minor-mode)
(add-hook 'scss-mode-hook 'my-enable-yas-minor-mode)
;; }}

(defun my-yas-expand-from-trigger-key-hack (orig-func &rest args)
  "Tab key won't trigger yasnippet expand in org heading."
  (cond
   ;; skip yas expand in org heading
   ((and (eq major-mode 'org-mode)
         (string-match "^org-level-" (format "%S" (get-text-property (point) 'face))))
    (org-cycle))
   (t
    (apply orig-func args))))
(advice-add 'yas-expand-from-trigger-key :around #'my-yas-expand-from-trigger-key-hack)

(defun my-yas-reload-all ()
  "Compile and reload snippets.  Run the command after adding new snippets."
  (interactive)
  (yas-compile-directory (file-truename (concat my-emacs-d "snippets")))
  (yas-reload-all)
  (my-enable-yas-minor-mode))

(defun my-yas-field-to-statement(str sep)
  "If STR=='a.b.c' and SEP=' && ', 'a.b.c' => 'a && a.b && a.b.c'"
  (let ((a (split-string str "\\.")) rlt)
    (mapconcat 'identity
               (mapcar (lambda (elem)
                         (cond
                          (rlt
                           (setq rlt (concat rlt "." elem)))
                          (t
                           (setq rlt elem)))) a)
               sep)))

(defun my-yas-get-first-name-from-to-field ()
  (let ((rlt "AGENT_NAME") str)
    (save-excursion
      (goto-char (point-min))
      ;; first line in email could be some hidden line containing NO to field
      (setq str (my-buffer-str)))
    ;; (message "str=%s" str)
    (if (string-match "^To: \"?\\([a-zA-Z]+\\)" str)
        (setq rlt (capitalize (match-string 1 str))))
    ;; (message "rlt=%s" rlt)
    rlt))

(defun my-yas-camelcase-to-string-list (str)
  "Convert camelcase STR into string list."
  (let* ((old-case case-fold-search) rlt)
    (setq case-fold-search nil)
    (setq rlt (replace-regexp-in-string "\\([A-Z]+\\)" " \\1" str t))
    (setq rlt (replace-regexp-in-string "\\([A-Z]+\\)\\([A-Z][a-z]+\\)" "\\1 \\2" rlt t))
    ;; restore case-fold-search
    (setq case-fold-search old-case)
    (split-string rlt " ")))

(defun my-yas-camelcase-to-downcase (str)
  (let* ((l (my-yas-camelcase-to-string-list str))
         (case-fold-search nil))
    (mapconcat 'identity (mapcar (lambda (elem)
                                   (if (string-match "^[A-Z]+$" elem)
                                       elem
                                     (downcase elem)))
                                 l)
               " ")))

(defun my-yas-escape-string (s)
  (let* ((rlt (replace-regexp-in-string "'" "\\\\'" s)))
    (setq rlt (replace-regexp-in-string "\"" "\\\\\"" rlt))
    rlt))

(defun my-read-n-from-kill-ring ()
  (let* ((cands (subseq kill-ring 0 (min (read-number "fetch N `kill-ring'?" 1)
                                         (length kill-ring)))))
    (mapc (lambda (txt)
            (set-text-properties 0 (length txt) nil txt)
            txt)
          cands)))

(defun my-yas-get-var-list-from-kill-ring ()
  "Variable name is among the `kill-ring'.  Multiple major modes supported."
  (let* ((top-kill-ring (my-read-n-from-kill-ring))
         rlt)
    (cond
     ((memq major-mode '(js-mode javascript-mode js2-mode js3-mode rjsx-mode web-mode))
      (setq rlt (mapconcat (lambda (i) (format "'%s=', %s" (my-yas-escape-string i) i)) top-kill-ring ", ")))
     ((memq major-mode '(emacs-lisp-mode lisp-interaction-mode))
      (setq rlt (concat (mapconcat (lambda (i) (format "%s=%%s" i)) top-kill-ring ", ")
                        "\" "
                        (mapconcat (lambda (i) (format "%s" i)) top-kill-ring " "))))
     ((memq major-mode '(c-mode c++-mode))
      (setq rlt (concat (mapconcat (lambda (i) (format "%s=%%s" i)) top-kill-ring ", ")
                        "\\n\", "
                        (mapconcat (lambda (i) (format "%s" i)) top-kill-ring ", "))))
     (t (setq rlt "")))
    rlt))

(with-eval-after-load 'yasnippet
  ;; http://stackoverflow.com/questions/7619640/emacs-latex-yasnippet-why-are-newlines-inserted-after-a-snippet
  (setq-default mode-require-final-newline nil)
  ;; Use `yas-dropdown-prompt' if possible. It requires `dropdown-list'.
  (setq yas-prompt-functions '(yas-dropdown-prompt
                               yas-ido-prompt
                               yas-completing-prompt))

  ;; Use `yas-completing-prompt' when ONLY when "M-x yas-insert-snippet"
  ;; Thanks to capitaomorte for providing the trick.
  (defun my-yas-insert-snippet-hack (orig-func &rest args)
    "Use `yas-completing-prompt' for `yas-prompt-functions' but only here..."
    (let* ((yas-prompt-functions '(yas-completing-prompt)))
      (apply orig-func args)))
  (advice-add 'yas-insert-snippet :around #'my-yas-insert-snippet-hack)

  (when (and  (file-exists-p my-yasnippets)
              (not (member my-yasnippets yas-snippet-dirs)))
    (add-to-list 'yas-snippet-dirs my-yasnippets))

  (yas-reload-all))

(provide 'init-yasnippet)
