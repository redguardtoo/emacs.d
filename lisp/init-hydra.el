;; -*- coding: utf-8; lexical-binding: t; -*-

;; @see https://github.com/abo-abo/hydra

;; use similar key bindings as init-evil.el
(defhydra hydra-launcher (:color blue)
  "
^Emms^       ^Misc^
------------------------------------------------
_r_andom     _t_erm             _E_nable/Disable
_n_ext       _a_utoComplete     _V_intage/Modern
_p_revious   _C_reate workgroup Open recent _f_ile
_P_ause      _l_oad workgroup   Recent _d_irectory
_O_pen       _B_ookmark         Last dired _c_ommand
_L_ Playlist Goto book_m_ark    Dired comand _h_istory
_S_huffle    Undo _v_isualize   _b_ack
_q_uit
"
  ("c" my-dired-redo-last-command)
  ("h" my-dired-redo-from-commands-history)
  ("B" bookmark-set)
  ("m" counsel-bookmark-goto)
  ("f" my-counsel-recentf)
  ("d" counsel-recent-directory)
  ("C" wg-create-workgroup)
  ("l" my-wg-switch-workgroup)
  ("t" ansi-term)
  ("a" toggle-company-ispell)
  ("E" toggle-typewriter)
  ("V" twm/toggle-sound-style)
  ("v" undo-tree-visualize)
  ("r" emms-random)
  ("n" emms-next)
  ("p" emms-previous)
  ("P" emms-pause)
  ("O" emms-play-playlist)
  ("b" back-to-previous-buffer)
  ("L" emms-playlist-mode-go)
  ("S" (progn (emms-shuffle) (emms-random)))
  ("q" nil))

(defhydra multiple-cursors-hydra (:color green :hint nil)
  "
^Up^            ^Down^          ^Other^
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
       ("s" gnus-summary-show-thread "Show thread")
       ("h" gnus-summary-hide-thread "Hide thread")
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
       ("a" counsel-bbdb-complete-mail "Mail address")
       ("ca" mml-attach-file "Attach C-c C-a")
       ("cc" message-send-and-exit "Send C-c C-c")
       ("q" nil "Bye"))))

(defun message-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'hydra-message/body))
(add-hook 'message-mode-hook 'message-mode-hook-hydra-setup)
;; }}

;; {{ dired
(eval-after-load 'dired
  '(progn
     (defhydra hydra-dired (:color blue)
       "?"
       ("sa" (shell-command "periscope.py -l en *.mkv *.mp4 *.avi &") "All subtitles")
       ("s1"
        (let* ((video-file (dired-file-name-at-point))
               (default-directory (file-name-directory video-file)))
          (shell-command (format "periscope.py -l en %s &" (file-name-nondirectory video-file))))
        "1 subtitle")
       ("cc" (let* ((f (file-truename (dired-file-name-at-point))))
               (copy-yank-str f)
               (message "filename %s => clipboard & yank ring" f)) "Copy full path")
       ("C" dired-do-copy "cp")
       ("cf" find-file "Create new file")
       ("ff" (lambda (regexp)
               (interactive "sMatching regexp: ")
               (find-lisp-find-dired default-directory regexp))  "Filter with Regex")
       ("xq" dired-toggle-read-only "Rename file(s)")
       ("mv" diredp-do-move-recursive "mv")
       ("mk" dired-create-directory "mkdir")
       ("q" nil "Bye"))))
(defun dired-mode-hook-hydra-setup ()
  (local-set-key (kbd "y") 'hydra-dired/body))
(add-hook 'dired-mode-hook 'dired-mode-hook-hydra-setup)
;; }}

;; increase and decrease font size in GUI emacs
;; @see https://oremacs.com/download/london.pdf
(when (display-graphic-p)
  ;; Since we already use GUI Emacs, f2 is definitely available
  (defhydra hydra-zoom (global-map "<f2>")
    "Zoom"
    ("g" text-scale-increase "in")
    ("l" text-scale-decrease "out")
    ("r" (text-scale-set 0) "reset")
    ("0" (text-scale-set 0) :bind nil :exit t)
    ("1" (text-scale-set 0) nil :bind nil :exit t)))
(defvar whitespace-mode nil)

;; {{ @see https://github.com/abo-abo/hydra/blob/master/hydra-examples.el
(defhydra hydra-toggle (:color pink)
  "
_a_ abbrev-mode:       %`abbrev-mode
_d_ debug-on-error:    %`debug-on-error
_f_ auto-fill-mode:    %`auto-fill-function
_t_ truncate-lines:    %`truncate-lines
_w_ whitespace-mode:   %`whitespace-mode
"
  ("a" abbrev-mode nil)
  ("d" toggle-debug-on-error nil)
  ("f" auto-fill-mode nil)
  ("t" toggle-truncate-lines nil)
  ("w" whitespace-mode nil)
  ("q" nil "quit"))
;; Recommended binding:
(global-set-key (kbd "C-c C-v") 'hydra-toggle/body)
;; }}

;; {{ @see https://github.com/abo-abo/hydra/wiki/Window-Management

;; helpers from https://github.com/abo-abo/hydra/blob/master/hydra-examples.el
(unless (featurep 'windmove)
  (require 'windmove))

(defun hydra-move-splitter-left (arg)
  "Move window splitter left."
  (interactive "p")
  (if (let* ((windmove-wrap-around))
        (windmove-find-other-window 'right))
      (shrink-window-horizontally arg)
    (enlarge-window-horizontally arg)))

(defun hydra-move-splitter-right (arg)
  "Move window splitter right."
  (interactive "p")
  (if (let* ((windmove-wrap-around))
        (windmove-find-other-window 'right))
      (enlarge-window-horizontally arg)
    (shrink-window-horizontally arg)))

(defun hydra-move-splitter-up (arg)
  "Move window splitter up."
  (interactive "p")
  (if (let* ((windmove-wrap-around))
        (windmove-find-other-window 'up))
      (enlarge-window arg)
    (shrink-window arg)))

(defun hydra-move-splitter-down (arg)
  "Move window splitter down."
  (interactive "p")
  (if (let* ((windmove-wrap-around))
        (windmove-find-other-window 'up))
      (shrink-window arg)
    (enlarge-window arg)))

(defhydra hydra-window ()
  "
Movement^^   ^Split^         ^Switch^     ^Resize^
-----------------------------------------------------
_h_ Left     _v_ertical      _b_uffer     _q_ X left
_j_ Down     _x_ horizontal  _f_ind files _w_ X Down
_k_ Top      _z_ undo        _a_ce 1      _e_ X Top
_l_ Right    _Z_ reset       _s_wap       _r_ X Right
_F_ollow     _D_elete Other  _S_ave       max_i_mize
_SPC_ cancel _o_nly this     _d_elete
"
  ("h" windmove-left )
  ("j" windmove-down )
  ("k" windmove-up )
  ("l" windmove-right )
  ("q" hydra-move-splitter-left)
  ("w" hydra-move-splitter-down)
  ("e" hydra-move-splitter-up)
  ("r" hydra-move-splitter-right)
  ("b" ivy-switch-buffer)
  ("f" counsel-find-file)
  ("F" follow-mode)
  ("a" (lambda ()
         (interactive)
         (ace-window 1)
         (add-hook 'ace-window-end-once-hook
                   'hydra-window/body)))
  ("v" (lambda ()
         (interactive)
         (split-window-right)
         (windmove-right)))
  ("x" (lambda ()
         (interactive)
         (split-window-below)
         (windmove-down)))
  ("s" (lambda ()
         (interactive)
         (ace-window 4)
         (add-hook 'ace-window-end-once-hook
                   'hydra-window/body)))
  ("S" save-buffer)
  ("d" delete-window)
  ("D" (lambda ()
         (interactive)
         (ace-window 16)
         (add-hook 'ace-window-end-once-hook
                   'hydra-window/body)))
  ("o" delete-other-windows)
  ("i" ace-delete-other-windows)
  ("z" (progn
         (winner-undo)
         (setq this-command 'winner-undo)))
  ("Z" winner-redo)
  ("SPC" nil))
(global-set-key (kbd "C-c C-w") 'hydra-window/body)
;; }}

;; {{ git-gutter, @see https://github.com/abo-abo/hydra/wiki/Git-gutter
(defhydra hydra-git-gutter (:body-pre (git-gutter-mode 1)
                                      :hint nil)
  "
Git gutter:
  _j_: next hunk     _s_tage hunk   _q_uit
  _k_: previous hunk _r_evert hunk  _Q_uit and deactivate git-gutter
  _h_: first hunk    _p_opup hunk
  _l_: last hunk     set _R_evision
"
  ("j" git-gutter:next-hunk)
  ("k" git-gutter:previous-hunk)
  ("h" (progn (goto-char (point-min))
              (git-gutter:next-hunk 1)))
  ("l" (progn (goto-char (point-min))
              (git-gutter:previous-hunk 1)))
  ("s" git-gutter:stage-hunk)
  ("r" git-gutter:revert-hunk)
  ("p" git-gutter:popup-hunk)
  ("R" git-gutter:set-start-revision)
  ("q" nil :color blue)
  ("Q" (progn (git-gutter-mode -1)
              ;; git-gutter-fringe doesn't seem to
              ;; clear the markup right away
              (sit-for 0.1)
              (git-gutter:clear))
   :color blue))
(global-set-key (kbd "C-c C-g") 'hydra-git-gutter/body)
;; }}

(defhydra hydra-search ()
  "
Dictionary^^         ^Search text^
---------------------------------
_b_ sdcv at point    _;_ 2 chars
_t_ sdcv input       _w_ (sub)word
_d_ dict.org         _a_ any chars
_g_ Google
_c_ current file ext
_f_ Finance
_q_ StackOverflow
_j_ Javascript API
_a_ Java
_h_ Code
_m_ Man
_q_ cancel
"
  ("b" sdcv-search-pointer)
  ("t" sdcv-search-input+)
  ("d" my-lookup-dict-org)
  ("g" w3m-google-search)
  ("c" w3m-google-by-filetype)
  ("f" w3m-search-financial-dictionary)
  ("q" w3m-stackoverflow-search)
  ("j" w3m-search-js-api-mdn)
  ("a" w3m-java-search)
  ("h" w3mext-hacker-search)
  ("m" lookup-doc-in-man)

  (";" avy-goto-char-2 )
  ("w" avy-goto-word-or-subword-1 )
  ("a" avy-goto-char-timer )

  ("q" nil))
(global-set-key (kbd "C-c C-s") 'hydra-search/body)
;; (global-set-key (kbd "C-c ; b") 'sdcv-search-pointer)
;; (global-set-key (kbd "C-c ; t") 'sdcv-search-input+)

(defhydra hydra-describe (:color blue :hint nil)
  "
Describe Something: (q to quit)
_a_ all help for everything screen
_b_ bindings
_B_ personal bindings
_c_ char
_C_ coding system
_f_ function
_F_ flycheck checker
_i_ input method
_k_ key briefly
_K_ key
_l_ language environment
_L_ mode lineage
_m_ major mode
_M_ minor mode
_n_ current coding system briefly
_N_ current coding system full
_o_ lighter indicator
_O_ lighter symbol
_p_ package
_P_ text properties
_s_ symbol
_t_ theme
_v_ variable
_w_ where is something defined
"
  ("b" describe-bindings)
  ("B" describe-personal-keybindings)
  ("C" describe-categories)
  ("c" describe-char)
  ("C" describe-coding-system)
  ("f" describe-function)
  ("F" flycheck-describe-checker)
  ("i" describe-input-method)
  ("K" describe-key)
  ("k" describe-key-briefly)
  ("l" describe-language-environment)
  ("L" help/parent-mode-display)
  ("M" describe-minor-mode)
  ("m" describe-mode)
  ("N" describe-current-coding-system)
  ("n" describe-current-coding-system-briefly)
  ("o" describe-minor-mode-from-indicator)
  ("O" describe-minor-mode-from-symbol)
  ("p" describe-package)
  ("P" describe-text-properties)
  ("q" nil)
  ("a" help)
  ("s" describe-symbol)
  ("t" describe-theme)
  ("v" describe-variable)
  ("w" where-is))
(global-set-key (kbd "C-c C-q") 'hydra-describe/body)

(provide 'init-hydra)
;;; init-hydra.el ends here
