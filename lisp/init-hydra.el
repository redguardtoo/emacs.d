;; @see https://github.com/abo-abo/hydra

;; use similar key bindings as init-evil.el
(defhydra hydra-launcher (:color blue)
  "Launch"
  ("mq" lookup-doc-in-man"man")
  ("rr" counsel-recentf-goto "Recent files")
  ("wgt" wg-create-workgroup "New window layout")
  ("wgg" my-wg-switch-workgroup "Load window layout")
  ("tr" ansi-term "ansi-term")
  ("sgg" 'w3m-google-search "Search")
  ("sgf" 'w3m-google-by-filetype "Search by filetype")
  ("sgd" 'w3m-search-financial-dictionary "Financial dictionary")
  ("sgq" 'w3m-stackoverflow-search "StackOverflow")
  ("sgj" 'w3m-search-js-api-mdn "Javascript API")
  ("sga" 'w3m-java-search "Java")
  ("sgh" 'w3mext-hacker-search "Code search")
  ("ddb" sdcv-search-pointer "Stardict in buffer")
  ("ddt" sdcv-search-input+  "Stardict in tooltip")
  ("ddd" my-lookup-dict-org "Lookup dict.org")
  ("ddw" define-word "Lookup word")
  ("ddp" define-word-at-point "Lookup word at point")
  ("q" nil "cancel"))
(global-set-key (kbd "C-c C-r") 'hydra-launcher/body)

;; {{ mail
;; @see https://github.com/redguardtoo/mastering-emacs-in-one-year-guide/blob/master/gnus-guide-en.org
;; gnus-group-mode
(eval-after-load 'gnus-group
  '(progn
     (defhydra hydra-gnus-group (:color blue)
       "Do?"
       ("a" gnus-group-list-active "REMOTE groups A A")
       ("l" gnus-group-list-all-groups "LOCAL groups L")
       ("c" gnus-topic-catchup-articles "Read all c")
       ("G" gnus-group-make-nnir-group "Search server G G")
       ("g" gnus-group-get-new-news "Refresh g")
       ("s" gnus-group-enter-server-mode "Servers")
       ("m" gnus-group-new-mail "Compose m OR C-x m")
       ("#" gnus-topic-mark-topic "mark #")
       ("q" nil "cancel"))
     ;; y is not used by default
     (define-key gnus-group-mode-map "y" 'hydra-gnus-group/body)))

;; gnus-summary-mode
(eval-after-load 'gnus-sum
  '(progn
     (defhydra hydra-gnus-summary (:color blue)
       "Do?"
       ("n" gnus-summary-insert-new-articles "Refresh / N")
       ("f" gnus-summary-mail-forward "Forward C-c C-f")
       ("!" gnus-summary-tick-article-forward "Mail -> disk !")
       ("p" gnus-summary-put-mark-as-read "Mail <- disk")
       ("c" gnus-summary-catchup-and-exit "Read all c")
       ("e" gnus-summary-resend-message-edit "Resend S D e")
       ("R" gnus-summary-reply-with-original "Reply with original R")
       ("r" gnus-summary-reply "Reply r")
       ("W" gnus-summary-wide-reply-with-original "Reply all with original S W")
       ("w" gnus-summary-wide-reply "Reply all S w")
       ("#" gnus-topic-mark-topic "mark #")
       ("q" nil "cancel"))
     ;; y is not used by default
     (define-key gnus-summary-mode-map "y" 'hydra-gnus-summary/body)))

;; gnus-article-mode
(eval-after-load 'gnus-art
  '(progn
     (defhydra hydra-gnus-article (:color blue)
       "Do?"
       ("f" gnus-summary-mail-forward "Forward")
       ("R" gnus-article-reply-with-original "Reply with original R")
       ("r" gnus-article-reply "Reply r")
       ("W" gnus-article-wide-reply-with-original "Reply all with original S W")
       ("o" gnus-mime-save-part "Save attachment at point o")
       ("w" gnus-article-wide-reply "Reply all S w")
       ("v" w3mext-open-with-mplayer "Open video/audio at point")
       ("d" w3mext-download-rss-stream "CLI to download RSS stream")
       ("b" w3mext-open-link-or-image-or-url "Open link under cursor or page URL with browser")
       ("q" nil "cancel"))
     ;; y is not used by default
     (define-key gnus-article-mode-map "y" 'hydra-gnus-article/body)))

(eval-after-load 'message
  '(progn
     (defhydra hydra-message (:color blue)
       "Do?"
       ("ca" mml-attach-file "Attach C-c C-a")
       ("cc" message-send-and-exit "Send C-c C-c")
       ("q" nil "cancel"))
     (global-set-key (kbd "C-c y") 'hydra-message/body)))
;; }}

(provide 'init-hydra)
;;; init-hydra.el ends here

