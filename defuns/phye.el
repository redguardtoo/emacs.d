(defun insert-src-in-orgmode (lang)
  "Insert src prefix and postfix for LANG in OrgMode"
  (interactive "sChoose your language: ")
  (newline)
  (indent-for-tab-command)
  (insert "#+begin_src " lang "\n")
  (indent-for-tab-command)
  (save-excursion
    (insert "#+end_src"))
  (org-edit-special)
  )

(add-hook 'text-mode-hook 'turn-on-auto-fill)
(cd "~/ws/OrgNotes/")

(setq-default evil-escape-key-sequence "jk")

(setq org-capture-templates
      '(("t" "Todo" entry (file+headline "~/ws/OrgNotes/gtd.org" "Tasks")
         "* TODO %?\n %i\n %a")
        ("n" "Note" entry (file+datetree "~/ws/OrgNotes/quick_notes.org")
         "* %?\nEntered on %U\n %i\n %a")))
(define-key global-map "\C-cc" 'org-capture)

(setq org-refile-targets
      '((nil :maxlevel . 5)
        (org-agenda-files :maxlevel . 5)
        ("KnowledgeBase.org" :maxlevel . 5)
        ("done.org" :maxlevel . 5)
        ("Work@Cisco.org" :maxlevel . 5)))

(eval-after-load "org"
                 '(require 'ox-odt nil t))

(setq org-export-with-sub-superscripts nil)

(setq mac-command-modifier 'meta)
(setq mac-option-modifier nil)
(setq org-export-with-properties t)

(eval-after-load "org"
                 '(require 'ox-md nil t))
