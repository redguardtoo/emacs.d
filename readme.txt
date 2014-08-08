TERM=xterm-256color emacs -nw
or add in .zshrc/.bashrc:
export TERM=xterm-256color

init.el:
add:
(setq company-clang-arguments '("-I/usr/include" "-I/usr/lib/llvm-3.4/lib/clang/3.4/include"))

init-elpa.el:
un-comment:
(setq package-archives '(("myelpa" . "~/myelpa")))

init.el:
;; changed by houzy
;; no vim mode
;; un-comment:
(require 'init-evil)
;; trun off backup
;; disable backup
(setq backup-inhibited t)
;; disable auto save
(setq auto-save-default nil)
;; turn off shell command echo
(defun my-comint-init ()
(setq comint-process-echoes t))
(add-hook 'comint-mode-hook 'my-comint-init)
;; add tags
;; (setq tags-file-name "~/ctagsFile/emacssystags")
(add-to-list 'tags-table-list (expand-file-name "~/ctagsFile/emacssystags") t)

init-misc.el:
-         (concat (getenv "USER") " $ ")))
+         (concat (getenv "USER") "@" (eshell/pwd) " $ ")))

-   ;;(format "ctags -f %s/TAGS -e -R %s" dir-name (directory-file-name dir-name)))
+   (format "ctags-exuberant -I __THROW -I __attribute_pure__ -I __nonnull -I __attribute__ --file-scope=yes --langmap=c:+.h --languages=c,c++ --links=yes --c-kinds=+p --c++-kinds=+p --fields=+iaS --extra=+q -R -e -f %s/TAGS %s" dir-name (directory-file-name dir-name)))
