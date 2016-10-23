(add-auto-mode 'ruby-mode "\\.rb\\'" "Rakefile\\'" "\.rake\\'" "\.rxml\\'" "\.rjs\\'" ".irbrc\\'" "\.builder\\'" "\.ru\\'" "\.gemspec\\'" "Gemfile\\'")

(setq ruby-use-encoding-map nil)

(defun ruby-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (robe-mode)
    (push 'company-robe company-backends)
    (setq-local compile-command "rake ")
    (flymake-ruby-load)))
(add-hook 'ruby-mode-hook 'ruby-mode-hook-setup)

;; Following generic project tools are more useful:
;; - find-file-in-project
;; - counsel-git-grep
;; - compile

(provide 'init-ruby-mode)
