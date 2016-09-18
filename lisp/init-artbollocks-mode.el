;; @see https://github.com/sachac/.emacs.d/blob/gh-pages/Sacha.org
(require 'artbollocks-mode)
;; Avoid these phrases
(setq artbollocks-weasel-words-regex
          (concat "\\b" (regexp-opt
                         '("one of the"
                           "should"
                           "just"
                           "sort of"
                           "a lot"
                           "probably"
                           "maybe"
                           "perhaps"
                           "I think"
                           "really"
                           "pretty"
                           "nice"
                           "action"
                           "utilize"
                           "leverage") t) "\\b"))

;; Don't show the art critic words, or at least until I figure
;; out my own jargon
(setq artbollocks-jargon nil)
(add-hook 'text-mode-hook 'artbollocks-mode)


;; FIXME: disable only inside org-mode
(defun artbollocks-reading-ease-disable ()
  "Disable key-binding C-c / due to it's conflict with org-sparse-tree."
  (define-key artbollocks-mode-keymap (kbd "C-c /") nil))
(add-hook 'artbollocks-mode-hook 'artbollocks-reading-ease-disable)

(provide 'init-artbollocks-mode)
