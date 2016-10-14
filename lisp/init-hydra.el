;; @see https://github.com/abo-abo/hydra

;; use similar key bindings as init-evil.el
(defhydra hydra-launcher (:color blue)
  "?"
  ("mq" lookup-doc-in-man "man")
  ("mk" bookmark-set "New bmark")
  ("mm" counsel-bookmark-goto "Go bmark")
  ("rr" counsel-recentf-goto "Recent file")
  ("ss" wg-create-workgroup "New layout")
  ("ll" my-wg-switch-workgroup "Load layout")
  ("tr" ansi-term "Term")
  ("pp" toggle-company-ispell "Ispell input")
  ("gg" w3m-google-search "Srch")
  ("gf" w3m-google-by-filetype "Srch by File Ext")
  ("gd" w3m-search-financial-dictionary "Financial Dict")
  ("gq" w3m-stackoverflow-search "StackOverflow")
  ("gj" w3m-search-js-api-mdn "JS API")
  ("ga" w3m-java-search "Java")
  ("gh" w3mext-hacker-search "Code search")
  ("db" sdcv-search-pointer "Stardict buffer")
  ("dt" sdcv-search-input+  "Stardict tooltip")
  ("dd" my-lookup-dict-org "Lookup dict.org")
  ("dw" define-word "Lookup word")
  ("dp" define-word-at-point "Lookup on spot")
  ("q" nil "Bye"))

(defhydra multiple-cursors-hydra (:color green :hint nil)
  "
     ^Up^            ^Down^        ^Other^
----------------------------------------------
[_p_]   Next    [_n_]   Next    [_l_] Edit lines
[_P_]   Skip    [_N_]   Skip    [_a_] Mark all
[_M-p_] Unmark  [_M-n_] Unmark  [_r_] Mark by regexp
^ ^             ^ ^             [_q_] Quit
"
  ("l" mc/edit-lines :exit t)
  ("a" mc/mark-all-like-this :exit t)
  ("n" mc/mark-next-like-this)
  ("N" mc/skip-to-next-like-this)
  ("M-n" mc/unmark-next-like-this)
  ("p" mc/mark-previous-like-this)
  ("P" mc/skip-to-previous-like-this)
  ("M-p" mc/unmark-previous-like-this)
  ("r" mc/mark-all-in-region-regexp :exit t)
  ("q" nil))

;; Because in message-mode/article-mode we've already use `y' as hotkey
(global-set-key (kbd "C-c C-y") 'hydra-launcher/body)
(global-set-key (kbd "C-c C-h") 'multiple-cursors-hydra/body)
(defun org-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'hydra-launcher/body)
  (local-set-key (kbd "C-c C-h") 'multiple-cursors-hydra/body))
(add-hook 'org-mode-hook 'org-mode-hook-hydra-setup)

;; {{ mail
;; @see https://github.com/redguardtoo/mastering-emacs-in-one-year-guide/blob/master/gnus-guide-en.org
;; gnus-group-mode
(eval-after-load 'gnus-group
  '(progn
     (defhydra hydra-gnus-group (:color blue)
       "?"
       ("a" gnus-group-list-active "REMOTE groups A A")
       ("l" gnus-group-list-all-groups "LOCAL groups L")
       ("c" gnus-topic-catchup-articles "Rd all c")
       ("G" gnus-group-make-nnir-group "Srch server G G")
       ("g" gnus-group-get-new-news "Refresh g")
       ("s" gnus-group-enter-server-mode "Servers")
       ("m" gnus-group-new-mail "Compose m OR C-x m")
       ("#" gnus-topic-mark-topic "mark #")
       ("q" nil "Bye"))
     ;; y is not used by default
     (define-key gnus-group-mode-map "y" 'hydra-gnus-group/body)))

;; gnus-summary-mode
(eval-after-load 'gnus-sum
  '(progn
     (defhydra hydra-gnus-summary (:color blue)
       "?"
       ("n" gnus-summary-insert-new-articles "Refresh / N")
       ("f" gnus-summary-mail-forward "Fwd C-c C-f")
       ("!" gnus-summary-tick-article-forward "Mail -> disk !")
       ("p" gnus-summary-put-mark-as-read "Mail <- disk")
       ("c" gnus-summary-catchup-and-exit "Rd all c")
       ("e" gnus-summary-resend-message-edit "Resend S D e")
       ("R" gnus-summary-reply-with-original "Re with orig R")
       ("r" gnus-summary-reply "Re r")
       ("W" gnus-summary-wide-reply-with-original "Re all with orig S W")
       ("w" gnus-summary-wide-reply "Re all S w")
       ("#" gnus-topic-mark-topic "Mark #")
       ("q" nil "Bye"))
     ;; y is not used by default
     (define-key gnus-summary-mode-map "y" 'hydra-gnus-summary/body)))

;; gnus-article-mode
(eval-after-load 'gnus-art
  '(progn
     (defhydra hydra-gnus-article (:color blue)
       "?"
       ("f" gnus-summary-mail-forward "Fwd")
       ("R" gnus-article-reply-with-original "Re with orig R")
       ("r" gnus-article-reply "Re r")
       ("W" gnus-article-wide-reply-with-original "Re all with orig S W")
       ("o" gnus-mime-save-part "Save attachment at point o")
       ("w" gnus-article-wide-reply "Re all S w")
       ("v" w3mext-open-with-mplayer "Video/audio at point")
       ("d" w3mext-download-rss-stream "CLI to download stream")
       ("b" w3mext-open-link-or-image-or-url "Link under cursor or page URL with external browser")
       ("f" w3m-lnum-follow "Click link/button/input")
       ("F" w3m-lnum-goto "Move focus to link/button/input")
       ("q" nil "Bye"))
     ;; y is not used by default
     (define-key gnus-article-mode-map "y" 'hydra-gnus-article/body)))

;; message-mode
(eval-after-load 'message
  '(progn
     (defhydra hydra-message (:color blue)
       "?"
       ("ca" mml-attach-file "Attach C-c C-a")
       ("cc" message-send-and-exit "Send C-c C-c")
       ("q" nil "Bye"))))

(defun message-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'hydra-message/body))
(add-hook 'message-mode-hook 'message-mode-hook-hydra-setup)
;; }}

;; dired
(eval-after-load 'dired
  '(progn
     (defhydra hydra-dired (:color blue)
       "?"
       ("sa" (shell-command "periscope.py -l en *.mkv *.mp4 *.avi &") "All subtitles")
       ("s1" (shell-command (format "periscope.py -l en %s &"
                                    (dired-file-name-at-point))) "1 subtitle")
       ("cf" (let* ((f (file-truename (dired-file-name-at-point))))
               (copy-yank-str f)
               (message "filename %s => clipboard & yank ring" f)) "Copy filename")
       ("C" dired-do-copy "cp")
       ("mv" diredp-do-move-recursive "mv")
       ("mk" dired-create-directory "mkdir")
       ("q" nil "Bye"))))
(defun dired-mode-hook-hydra-setup ()
  (local-set-key (kbd "y") 'hydra-dired/body))
(add-hook 'dired-mode-hook 'dired-mode-hook-hydra-setup)
(provide 'init-hydra)
;;; init-hydra.el ends here

