;;; init-linum-mode.el --- line number setup -*- lexical-binding: t; -*-
;;; Code:

;; http://stackoverflow.com/questions/3875213/turning-on-linum-mode-when-in-python-c-mode
(defvar my-linum-inhibit-modes
  '(eshell-mode
    pdf-view-mode
    special-mode
    org-agenda-mode
    shell-mode
    vterm-mode
    js-comint-mode
    profiler-report-mode
    ffip-diff-mode
    dictionary-mode
    erc-mode
    dired-mode
    help-mode
    fundamental-mode
    jabber-roster-mode
    jabber-chat-mode
    inferior-js-mode
    inferior-python-mode
    ivy-occur-grep-mode ; better performance
    ivy-occur-mode ; better performance
    twittering-mode
    compilation-mode
    weibo-timeline-mode
    woman-mode
    Info-mode
    calc-mode
    calc-trail-mode
    comint-mode
    gnus-group-mode
    emms-playlist-mode
    gud-mode
    org-mode
    vc-git-log-edit-mode
    log-edit-mode
    term-mode
    w3m-mode
    speedbar-mode
    gnus-summary-mode
    gnus-article-mode
    calendar-mode)
  "Major modes without line number.")

(defun my-setup-line-number-mode ()
  "Set up line number display."
  ;; use idler to speed up emacs startup
  (unless (or (memq major-mode my-linum-inhibit-modes)
              ;; don't show line number for certain file extensions
              (my-should-use-minimum-resource))
    (display-line-numbers-mode)))

(add-hook 'prog-mode-hook #'my-setup-line-number-mode)
;; (add-hook 'text-mode-hook #'my-setup-line-number-mode)

(provide 'init-linum-mode)
;;; init-linum-mode.el ends here
