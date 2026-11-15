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

(defun my-display-line-number ()
  "Set up line number display."
  ;; use idler to speed up emacs startup
  (unless (or (apply #'derived-mode-p my-linum-inhibit-modes)
              ;; don't show line number for certain file extensions
              (my-should-use-minimum-resource))
    (display-line-numbers-mode 1)))

(add-hook 'prog-mode-hook #'my-display-line-number)
;; (add-hook 'text-mode-hook #'my-display-line-number)

(provide 'init-linum-mode)
;;; init-linum-mode.el ends here
