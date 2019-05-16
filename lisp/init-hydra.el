;; -*- coding: utf-8; lexical-binding: t; -*-

;; @see https://github.com/abo-abo/hydra

;; use similar key bindings as init-evil.el
(defhydra hydra-launcher (:color blue)
  "
^Misc^                    ^Audio^               ^Pomodoro^
----------------------------------------------------------
[_u_] CompanyIspell       [_R_] Emms Random     [_s_] Start
[_C_] New workgroup       [_n_] Emms Next       [_t_] Stop
[_l_] Load workgroup      [_p_] Emms Previous   [_r_] Resume
[_B_] New bookmark        [_P_] Emms Pause      [_a_] Pause
[_m_] Goto bookmark       [_O_] Emms Open
[_v_] Show/Hide undo      [_L_] Emms Playlist
[_b_] Switch Gnus buffer  [_w_] Pronounce word
[_f_] Recent file
[_d_] Recent directory
[_c_] Last dired command
[_h_] Dired CMD history
[_E_] Enable typewriter
[_V_] Vintage typewriter
[_q_] Quit
"
  ("c" my-dired-redo-last-command)
  ("h" my-dired-redo-from-commands-history)
  ("B" bookmark-set)
  ("m" counsel-bookmark-goto)
  ("f" my-counsel-recentf)
  ("d" counsel-recent-directory)
  ("C" wg-create-workgroup)
  ("l" my-wg-switch-workgroup)
  ("u" toggle-company-ispell)
  ("E" toggle-typewriter)
  ("V" twm/toggle-sound-style)
  ("v" undo-tree-visualize)
  ("s" pomodoro-start)
  ("t" pomodoro-stop)
  ("r" pomodoro-resume)
  ("a" pomodoro-pause)
  ("R" emms-random)
  ("n" emms-next)
  ("w" my-pronounce-current-word)
  ("p" emms-previous)
  ("P" emms-pause)
  ("O" emms-play-playlist)
  ("b" my-switch-gnus-buffer)
  ("L" emms-playlist-mode-go)
  ("q" nil))

;; Because in message-mode/article-mode we've already use `y' as hotkey
(global-set-key (kbd "C-c C-y") 'hydra-launcher/body)
(defun org-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'hydra-launcher/body))
(add-hook 'org-mode-hook 'org-mode-hook-hydra-setup)

;; {{ mail
;; @see https://github.com/redguardtoo/mastering-emacs-in-one-year-guide/blob/master/gnus-guide-en.org
;; gnus-group-mode
(eval-after-load 'gnus-group
  '(progn
     (defhydra hydra-gnus-group (:color blue)
       "
[_A_] Remote groups (A A) [_g_] Refresh
[_L_] Local groups        [_\\^_] List servers
[_c_] Mark all read       [_m_] Compose new mail
[_G_] Search mails (G G)  [_#_] Mark mail
[_b_] Switch Gnus buffer  [_E_] Extract email address
"
       ("A" gnus-group-list-active)
       ("L" gnus-group-list-all-groups)
       ("c" gnus-topic-catchup-articles)
       ("G" dianyou-group-make-nnir-group)
       ("b" my-switch-gnus-buffer)
       ("g" gnus-group-get-new-news)
       ("^" gnus-group-enter-server-mode)
       ("m" gnus-group-new-mail)
       ("#" gnus-topic-mark-topic)
       ("E" dianyou-summary-extract-mail-address)
       ("q" nil))
     ;; y is not used by default
     (define-key gnus-group-mode-map "y" 'hydra-gnus-group/body)))

;; gnus-summary-mode
(eval-after-load 'gnus-sum
  '(progn
     (defhydra hydra-gnus-summary (:color blue)
       "
[_F_] Forward (C-c C-f)             [_s_] Show thread
[_e_] Resend (S D e)                [_h_] Hide thread
[_r_] Reply                         [_n_] Refresh (/ N)
[_R_] Reply with original           [_!_] Mail -> disk
[_w_] Reply all (S w)               [_d_] Disk -> mail
[_W_] Reply all with original (S W) [_c_] Read all
[_G_] Search current folder         [_#_] Mark
[_b_] Switch Gnus buffer            [_A_] Show Raw article
"
       ("s" gnus-summary-show-thread)
       ("h" gnus-summary-hide-thread)
       ("n" gnus-summary-insert-new-articles)
       ("F" gnus-summary-mail-forward)
       ("!" gnus-summary-tick-article-forward)
       ("b" my-switch-gnus-buffer)
       ("d" gnus-summary-put-mark-as-read-next)
       ("c" gnus-summary-catchup-and-exit)
       ("e" gnus-summary-resend-message-edit)
       ("R" gnus-summary-reply-with-original)
       ("r" gnus-summary-reply)
       ("W" gnus-summary-wide-reply-with-original)
       ("w" gnus-summary-wide-reply)
       ("#" gnus-topic-mark-topic)
       ("A" gnus-summary-show-raw-article)
       ("G" dianyou-group-make-nnir-group)
       ("q" nil))
     ;; y is not used by default
     (define-key gnus-summary-mode-map "y" 'hydra-gnus-summary/body)))

;; gnus-article-mode
(eval-after-load 'gnus-art
  '(progn
     (defhydra hydra-gnus-article (:color blue)
       "
[_o_] Save attachment        [_F_] Forward
[_v_] Play video/audio       [_r_] Reply
[_d_] CLI to dowloand stream [_R_] Reply with original
[_b_] Open external browser  [_w_] Reply all (S w)
[_f_] Click link/button      [_W_] Reply all with original (S W)
[_g_] Focus link/button      [_b_] Switch Gnus buffer
"
       ("F" gnus-summary-mail-forward)
       ("r" gnus-article-reply)
       ("R" gnus-article-reply-with-original)
       ("w" gnus-article-wide-reply)
       ("W" gnus-article-wide-reply-with-original)
       ("o" (lambda () (interactive) (let* ((file (gnus-mime-save-part))) (when file (copy-yank-str file)))))
       ("v" w3mext-open-with-mplayer)
       ("d" w3mext-download-rss-stream)
       ("b" w3mext-open-link-or-image-or-url)
       ("f" w3m-lnum-follow)
       ("g" w3m-lnum-goto)
       ("b" my-switch-gnus-buffer)
       ("q" nil))
     ;; y is not used by default
     (define-key gnus-article-mode-map "y" 'hydra-gnus-article/body)))

;; message-mode
(eval-after-load 'message
  '(progn
     (defhydra hydra-message (:color blue)
  "
[_c_] Complete mail address
[_a_] Attach file
[_s_] Send mail (C-c C-c)
[_b_] Switch Gnus buffer
"
       ("c" counsel-bbdb-complete-mail)
       ("a" mml-attach-file)
       ("s" message-send-and-exit)
       ("b" my-switch-gnus-buffer)
       ("q" nil))))

(defun message-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'hydra-message/body))
(add-hook 'message-mode-hook 'message-mode-hook-hydra-setup)
;; }}

;; {{ dired
(eval-after-load 'dired
  '(progn
     (defun my-replace-dired-base (base)
       "Change file name in `wdired-mode'"
       (let* ((fp (dired-file-name-at-point))
              (fb (file-name-nondirectory fp))
              (ext (file-name-extension fp))
              (dir (file-name-directory fp))
              (nf (concat base "." ext)))
         (when (yes-or-no-p (format "%s => %s at %s?"
                                    fb nf dir))
           (rename-file fp (concat dir nf)))))
     (defun my-copy-file-info (fn)
       (message "%s => clipboard & yank ring"
                (copy-yank-str (funcall fn (dired-file-name-at-point)))))
     (defhydra hydra-dired (:color blue)
       "
^File/Directory^    ^Copy Info^  ^Fetch Subtitles^
----------------------------------------------------
[_mv_] Move file    [_pp_] Path  [_sa_] All
[_cf_] New file     [_nn_] Name  [_s1_] One
[_rr_] Rename file  [_bb_] Base
[_ff_] Find file    [_dd_] DIR
[_mk_] New DIR
[_rb_] Replace base
[_C_]  Copy file
^^                  ^^           [_q_]  Quit
"
       ("sa" (shell-command "periscope.py -l en *.mkv *.mp4 *.avi &"))
       ("s1" (let* ((video-file (dired-file-name-at-point))
                    (default-directory (file-name-directory video-file)))
               (shell-command (format "periscope.py -l en %s &" (file-name-nondirectory video-file)))))
       ("pp" (my-copy-file-info 'file-truename))
       ("nn" (my-copy-file-info 'file-name-nondirectory))
       ("bb" (my-copy-file-info 'file-name-base))
       ("dd" (my-copy-file-info 'file-name-directory))
       ("rb" (my-replace-dired-base (car kill-ring)))
       ("C" dired-do-copy)
       ("mv" diredp-do-move-recursive)
       ("cf"find-file)
       ("rr" dired-toggle-read-only)
       ("ff" (lambda (regexp)
               (interactive "sMatching regexp: ")
               (find-lisp-find-dired default-directory regexp)))
       ("mk" dired-create-directory)
       ("q" nil))))

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
