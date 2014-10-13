;; Exp 2011/10/13 10:54:51 12.0
;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                         gestion des TAGS
;;--------------------------------------------------------------------------;;

; sous xemacs, visit-tags-table n'a pas d'argument optionnel. Sous gnu emacs :

; Normally M-x visit-tags-table sets the global value of `tags-file-name'.
; With a prefix arg, set the buffer-local value instead.

; mieux vaut sous gnu emacs gérer la variable tags-table-list, qui
; n'existe pas sous xemacs.
; Sous xemacs il faut gérer la variable tag-table-alist qui n'existe pas
; sous gnu emacs.


(require 'etags)

(eval-when-compile
  (defvar phox-doc-dir nil)
  (defvar phox-lib-dir nil)
  (defvar phox-etags nil))


(defun phox-tags-add-table(table)
  "add tags table"
  (interactive "D directory, location of a file named TAGS to add : ")
  (if (not (boundp 'tags-table-list)) (setq tags-table-list nil))
  (if (member table tags-table-list)
      (message "%s already loaded." table)
    ;; (make-local-variable 'tags-table-list) ; ne fonctionne pas
    (setq tags-table-list (cons table tags-table-list))))

(defun phox-tags-reset-table()
  "Set tags-table-list to nil."
  (interactive)
  (setq tags-table-list nil))

(defun phox-tags-add-doc-table()
  "Add tags in text documentation."
  (interactive)
  (phox-tags-add-table (concat phox-doc-dir "/text/TAGS"))
  )

(defun phox-tags-add-lib-table()
  "Add tags in libraries."
  (interactive)
  (phox-tags-add-table (concat phox-lib-dir "/TAGS"))
  )

(defun phox-tags-add-local-table()
  "Add the tags table created with function phox-create-local-table."
  (interactive)
  (phox-tags-add-table (concat buffer-file-name "TAGS"))
  )

(defun phox-tags-create-local-table()
  "create table on local buffer"
  (interactive)
  (shell-command (concat phox-etags
			 " -o "
			 (file-name-nondirectory (buffer-file-name))
			 "TAGS "
			 (file-name-nondirectory (buffer-file-name))))
  )


(defun phox-complete-tag()
  "Complete symbol using tags table."
  (interactive)
  (complete-tag))

;; menu

(defvar phox-tags-menu
  '("Tags"
    ["create a tags table for local buffer" phox-tags-create-local-table t]
    ["------------------" nil nil]
    ["add table"               phox-tags-add-table       t]
    ["add local table"         phox-tags-add-local-table t]
    ["add table for libraries" phox-tags-add-lib-table   t]
    ["add table for text doc"  phox-tags-add-doc-table   t]
    ["reset tags table list"   phox-tags-reset-table     t]
    ["------------------" nil nil]
    ["Find theorem, definition ..." find-tag t]
    ["complete theorem, definition ..." phox-complete-tag t]
    )
"Phox menu for dealing with tags"
)

(provide 'phox-tags)
