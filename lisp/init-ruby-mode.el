;; -*- coding: utf-8; lexical-binding: t; -*-

;; minimum setup for ruby
(add-auto-mode 'ruby-mode
               "\\.\\(rb\\|rake\\|rxml\\|rjs\\|irbrc\\|builder\\|ru\\|gemspec\\)\\'"
               "\\(Rakefile\\|Gemfile\\)\\'")

;; Following generic project tools are more useful:
;; - find-file-in-project
;; - counsel-git-grep
;; - compile

(provide 'init-ruby-mode)
