;; -*- coding: utf-8; lexical-binding: t; -*-

;;; {{ shell and conf
(add-auto-mode 'conf-mode
               "\\.[^b][^a][a-zA-Z]*rc$"
               "\\.aspell\\.en\\.pws$"
               "\\.i3/config-base$"
               "\\mimeapps\\.list$"
               "\\mimeapps\\.list$"
               "\\.editorconfig$"
               "\\.meta$"
               "\\.?muttrc$"
               "\\.mailcap$")
;; }}


;; {{ lisp like language
;; racket
(add-auto-mode 'lisp-mode "\\.rkt\\'")
(add-auto-mode 'emacs-lisp-mode
               "\\.emacs-project\\'"
               "archive-contents\\'"
               "\\.emacs\\.bmk\\'" )
;; }}

;; {{ ruby
(add-auto-mode 'ruby-mode
               "\\.\\(rb\\|rake\\|rxml\\|rjs\\|irbrc\\|builder\\|ru\\|gemspec\\)$"
               "\\(Rakefile\\|Gemfile\\)$")

;; }}

;; {{ perl
;; Use cperl-mode instead of the default perl-mode
(add-auto-mode 'cperl-mode
               "\\.\\([pP][Llm]\\|al\\)$"
               "\\.\\([pP][Llm]\\|al\\)$")

(add-interpreter-mode 'cperl-mode "perl5?\\|minperl")
;; }}

(add-auto-mode 'text-mode
               "TAGS\\'"
               "\\.ctags\\'")

(add-auto-mode 'java-mode
               ;; java
               "\\.aj\\'"
               ;; makefile
               "\\.ninja$" )

(add-auto-mode 'groovy-mode
               "\\.groovy\\'"
               "\\.gradle\\'" )

(add-auto-mode 'sh-mode
               "\\.bash\\(_profile\\|_history\\|rc\\.local\\|rc\\)?$"
               "\\.z?sh$"
               "\\.env$")

(add-auto-mode 'cmake-mode
               "CMakeLists\\.txt\\'"
               "\\.cmake\\'" )

;; vimrc
(add-auto-mode 'vimrc-mode "\\.?vim\\(rc\\)?$")

(add-auto-mode 'csv-mode "\\.[Cc][Ss][Vv]\\'")

(add-auto-mode 'rust-mode "\\.rs\\'")

;; {{ verilog
(autoload 'verilog-mode "verilog-mode" "Verilog mode" t )
(add-auto-mode 'verilog-mode "\\.[ds]?vh?\\'")
;; }}

(add-auto-mode 'adoc-mode "\\.adoc\\'")

(add-auto-mode 'texile-mode "\\.textile\\'")

(add-auto-mode 'tcl-mode "Portfile\\'")

;; epub
(add-auto-mode 'nov-mode "\\.epub\\'")

(add-auto-mode 'octave-mode "\\.m$")

;; pyim
(add-auto-mode 'text-mode "\\.pyim\\'")

;; {{ web/html
(add-auto-mode 'web-mode
               "\\.\\(cmp\\|app\\|page\\|component\\|wp\\|vue\\|tmpl\\|php\\|module\\|inc\\|hbs\\|tpl\\|[gj]sp\\|as[cp]x\\|erb\\|mustache\\|djhtml\\|ftl\\|[rp]?html?\\|xul?\\|eex?\\|xml?\\|jst\\|ejs\\|erb\\|rbxlx\\)$")
;; }}

;; {{js
(add-auto-mode 'js-mode
               "\\.ja?son$"
               "\\.pac$"
               "\\.jshintrc$")

(cond
 ((not *no-memory*)
  ;; javascript
  (add-auto-mode 'js2-mode "\\.js\\(\\.erb\\)?\\'")
  ;; JSX
  (add-auto-mode 'rjsx-mode
                 "\\.jsx\\'"
                 "components\\/.*\\.js\\'")
  ;; mock file
  (add-auto-mode 'js-mode "\\.mock.js\\'")
  (add-interpreter-mode 'js2-mode "node"))
 (t
  (add-auto-mode 'js-mode
                 "\\.js\\(\\.erb\\)?\\'"
                 "\\.babelrc\\'")))

(add-auto-mode 'typescript-mode "\\.ts$")


(add-auto-mode 'markdown-mode "\\.\\(m[k]d\\|markdown\\)\\'")

(add-auto-mode 'snippet-mode "\\.yasnippet\\'")

;; python
(add-interpreter-mode 'python-mode "python")

;; roblox studio
(add-auto-mode 'roblox-mode "\\.rbxlx\\'")
;; }}
(provide 'init-file-type)
