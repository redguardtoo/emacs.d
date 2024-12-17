;; -*- coding: utf-8; lexical-binding: t; -*-

;;; {{ shell and conf
(my-add-auto-mode 'conf-mode
                  "\\.[^b][^a][a-zA-Z]*rc\\'"
                  "\\.aspell\\.en\\.pws\\'"
                  "\\.i3/config-base\\'"
                  "\\.config/systemd/user/.*\\.service\\'"
                  "\\mimeapps\\.list\\'"
                  "\\mimeapps\\.list\\'"
                  "\\.editorconfig\\'"
                  "\\.meta\\'"
                  "\\.env[0-9a-z.-]*\\'" ; ".env" or ".env.local"
                  "PKGBUILD\\'" ; archlinux
                  "\\.pgpass\\'"
                  "\\.?muttrc\\'"
                  "\\.mailcap\\'"
                  "default\\.pa\\'" ; pulseaudio configuration file
                  "yarn\\.lock\\'")
;; }}


;; {{ lisp like language
;; racket
(my-add-auto-mode 'lisp-mode "\\.rkt\\'")
(my-add-auto-mode 'emacs-lisp-mode
                  "\\.emacs-project\\'"
                  "archive-contents\\'"
                  "\\.emacs_workgroups\\'"
                  "\\.emacs\\.bmk\\'" )
;; }}

;; {{ ruby
(my-add-auto-mode 'ruby-mode
                  "\\.\\(rb\\|rake\\|rxml\\|rjs\\|irbrc\\|builder\\|ru\\|gemspec\\)\\'"
                  "\\(Rakefile\\|Gemfile\\)\\'")

;; }}

;; {{ perl
;; Use cperl-mode instead of the default perl-mode
(my-add-auto-mode 'cperl-mode
                  "\\.\\([pP][Llm]\\|al\\)\\'"
                  "\\.\\([pP][Llm]\\|al\\)\\'")

(my-add-interpreter-mode 'cperl-mode "perl5?\\|minperl")
;; }}

(my-add-auto-mode 'text-mode
                  "TAGS\\'"
                  "\\.pyim\\'"
                  "\\.ctags\\'")

(my-add-auto-mode 'java-mode
                  ;; java
                  "\\.aj\\'"
                  ;; makefile
                  "\\.ninja\\'" )

(my-add-auto-mode 'groovy-mode
                  "\\.groovy\\'"
                  "\\.gradle\\'" )

(my-add-auto-mode 'sh-mode
                  "\\.bash\\(_profile\\|_history\\|rc\\.local\\|rc\\)?\\'"
                  "\\.z?sh\\'")

(my-add-auto-mode 'cmake-mode
                  "CMakeLists\\.txt\\'"
                  "\\.cmake\\'" )

;; vimrc
(my-add-auto-mode 'vimrc-mode "\\.?vim\\(rc\\)?\\'")

(my-add-auto-mode 'csv-mode "\\.[Cc][Ss][Vv]\\'")

(my-add-auto-mode 'rust-mode "\\.rs\\'")

;; {{ verilog
(autoload 'verilog-mode "verilog-mode" "Verilog mode" t )
(my-add-auto-mode 'verilog-mode "\\.[ds]?vh?\\'")
;; }}

(my-add-auto-mode 'adoc-mode "\\.adoc\\'")

(my-add-auto-mode 'texile-mode "\\.textile\\'")

(my-add-auto-mode 'tcl-mode "Portfile\\'")

;; epub
(my-add-auto-mode 'nov-mode "\\.epub\\'")

(my-add-auto-mode 'octave-mode "\\.m\\'")

;; {{ web/html
(my-add-auto-mode 'web-mode
                  "\\.\\(cmp\\|app\\|page\\|component\\|wp\\|vue\\|tmpl\\|php\\|module\\|inc\\|hbs\\|tpl\\|[gj]sp\\|as[cp]x\\|erb\\|mustache\\|djhtml\\|ftl\\|[rp]?html?\\|xul?\\|eex?\\|xml?\\|jst\\|ejs\\|erb\\|rbxlx\\|plist\\)\\'")
;; }}

(my-add-auto-mode 'dockerfile-mode
                  "Dockerfile"
                  "\\.dockerfile"
                  "Containerfile")
(put 'dockerfile-image-name 'safe-local-variable #'stringp)

;; {{js
(my-add-auto-mode 'js-mode
                  "\\.ja?son\\'"
                  "\\.pac\\'"
                  "\\.jshintrc\\'")

(cond
 ((not *no-memory*)
  ;; javascript
  (my-add-auto-mode 'js2-mode "\\.m?js\\(\\.erb\\)?\\'")
  ;; JSX
  (my-add-auto-mode 'rjsx-mode
                    "\\.[tj]sx\\'"
                    "components\\/.*\\.js\\'")
  ;; mock file
  (my-add-auto-mode 'js-mode "\\.mock.js\\'")
  (my-add-interpreter-mode 'js2-mode "node"))
 (t
  (my-add-auto-mode 'js-mode
                    "\\.js\\(\\.erb\\)?\\'"
                    "\\.babelrc\\'")))

(my-add-auto-mode 'typescript-mode "\\.ts\\'")

(my-add-auto-mode 'lua-mode "\\.lua\\'")

(my-add-auto-mode 'markdown-mode "\\.\\(m[k]d\\|markdown\\)\\'")

(my-add-auto-mode 'snippet-mode "\\.yasnippet\\'")

;; python
(my-add-interpreter-mode 'python-mode "python")

;; roblox studio
(my-add-auto-mode 'roblox-mode "\\.rbxlx\\'")
;; }}

;; `css-mode' has better imenu support and won't force flymake to create rubbish files.
;; besides, scss/sass is outdated. We use postcss or css in js these days.
(my-add-auto-mode 'css-mode "\\.scss\\'")

(provide 'init-file-type)
