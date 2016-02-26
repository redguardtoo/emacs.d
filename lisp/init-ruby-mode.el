(add-auto-mode 'ruby-mode "\\.rb\\'" "Rakefile\\'" "\.rake\\'" "\.rxml\\'" "\.rjs\\'" ".irbrc\\'" "\.builder\\'" "\.ru\\'" "\.gemspec\\'" "Gemfile\\'")

(autoload 'run-ruby "inf-ruby" "Run an inferior Ruby process")
(setq ruby-use-encoding-map nil)

(defun ruby-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (require 'rinari)
    (robe-mode)
    (push 'company-robe company-backends)
    (setq compile-command "rake ")
    (flymake-ruby-load)))
(add-hook 'ruby-mode-hook 'ruby-mode-hook-setup)

;; doc look up
(autoload 'yari "yari" "" t nil)

(add-to-list 'auto-mode-alist '("\\.rhtml\\(\\.erb\\)?\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.jst\\.ejs\\'"  . web-mode))

(defun update-rails-ctags ()
  (interactive)
  (let ((default-directory (or (rinari-root) default-directory)))
    (shell-command (concat "ctags -a -e -f " rinari-tags-file-name " --tag-relative -R app lib vendor test"))))

(provide 'init-ruby-mode)
