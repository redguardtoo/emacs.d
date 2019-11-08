;; -*- coding: utf-8; lexical-binding: t; -*-

;; @see https://github.com/abo-abo/hydra

;; use similar key bindings as init-evil.el
(defhydra hydra-launcher (:color blue)
  "
^Misc^                    ^Audio^               ^Move^                          ^Pomodoro^
----------------------------------------------------------------------------------------------
[_ss_] Save workgroup     [_R_] Emms Random     [_sa_] Backward Sentence (M-a)  [_ss_] Start
[_ll_] Load workgroup     [_n_] Emms Next       [_se_] Forward Sentence (M-e)   [_st_] Stop
[_B_] New bookmark        [_p_] Emms Previous   [_la_] Backward Up List         [_sr_] Resume
[_m_] Goto bookmark       [_P_] Emms Pause      [_le_] Forward List             [_sp_] Pause
[_v_] Show/Hide undo      [_O_] Emms Open       [_pa_] Backward Paragraph (M-{)
[_b_] Switch Gnus buffer  [_L_] Emms Playlist   [_pe_] Forward Paragraph (M-})
[_f_] Recent file         [_w_] Pronounce word
[_d_] Recent directory
[_h_] Dired CMD history
[_E_] Enable typewriter
[_V_] Vintage typewriter
[_q_] Quit
"
  ("h" my-dired-redo-from-commands-history)
  ("B" bookmark-set)
  ("m" counsel-bookmark-goto)
  ("f" my-counsel-recentf)
  ("d" counsel-recent-directory)
  ("ss" wg-create-workgroup)
  ("ll" my-wg-switch-workgroup)
  ("E" toggle-typewriter)
  ("V" twm/toggle-sound-style)
  ("v" undo-tree-visualize)
  ("ss" pomodoro-start)
  ("st" pomodoro-stop)
  ("sr" pomodoro-resume)
  ("sp" pomodoro-pause)
  ("sa" backward-sentence)
  ("se" forward-sentence)
  ("la" backward-up-list)
  ("le" forward-list)
  ("pa" backward-paragraph)
  ("pe" forward-paragraph)
  ("R" emms-random)
  ("n" emms-next)
  ("w" my-pronounce-current-word)
  ("p" emms-previous)
  ("P" emms-pause)
  ("O" emms-play-playlist)
  ("b" dianyou-switch-gnus-buffer)
  ("L" emms-playlist-mode-go)
  ("q" nil))

;; Because in message-mode/article-mode we've already use `y' as hotkey
(global-set-key (kbd "C-c C-y") 'hydra-launcher/body)
(defun org-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'hydra-launcher/body))
(add-hook 'org-mode-hook 'org-mode-hook-hydra-setup)

(eval-after-load 'find-file-in-project
  '(progn
     (defhydra hydra-ffip-diff-group (:color blue)
       "
[_k_] Previous hunk
[_j_] Next hunk
[_p_] Previous file
[_n_] Next file
"
       ("k" diff-hunk-prev)
       ("j" diff-hunk-next)
       ("p" diff-file-prev)
       ("n" diff-file-next)
       ("q" nil))))
(defun ffip-diff-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'hydra-ffip-diff-group/body))
(add-hook 'ffip-diff-mode-hook 'ffip-diff-mode-hook-hydra-setup)

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
       ("b" dianyou-switch-gnus-buffer)
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
[_d_] CLI to download stream [_R_] Reply with original
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
       ("b" dianyou-switch-gnus-buffer)
       ("q" nil))
     ;; y is not used by default
     (define-key gnus-article-mode-map "y" 'hydra-gnus-article/body)))

;; message-mode
(eval-after-load 'message
  '(progn
     (defhydra hydra-message (:color blue)
  "
[_c_] Complete mail address [_H_] convert to html mail
[_a_] Attach file           [_p_] Paste image from clipboard
[_s_] Send mail (C-c C-c)
[_b_] Switch Gnus buffer
[_i_] Insert email address
"
       ("c" counsel-bbdb-complete-mail)
       ("a" mml-attach-file)
       ("s" message-send-and-exit)
       ("b" dianyou-switch-gnus-buffer)
       ("i" dianyou-insert-email-address-from-received-mails)
       ("H" org-mime-htmlize)
       ("p" dianyou-paste-image-from-clipboard)
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
     (defun my-extract-mp3-from-video ()
       "Extract mp3 from current video file using ffmpeg."
       (interactive)
       (let* ((video-file (file-name-nondirectory (dired-file-name-at-point)))
              (params (split-string (string-trim (read-string "Please input start-second [total seconds] (e.g, \"6 10\" or \"05:30 5\") or just press enter: "))
                                    " +"))
              (start (car params))
              (total (if (eq (length params) 1) "5" (nth 1 params)))
              cmd)
         (cond
          ((string= start "")
           ;; extract audio to MP3 with sample rate 44.1Khz (CD quality), stereo, and 2 channels
           (setq cmd (format "ffmpeg -i \"%s\" -vn -ar 44100 -ac 2 -ab 192 -f mp3 \"%s\""
                             video-file
                             (concat (file-name-base video-file) ".mp3"))))
          (t
           (setq cmd (format "ffmpeg -i \"%s\" -vn -ss %s -t %s -acodec copy \"%s\""
                             video-file
                             start
                             total
                             (format "%s-%s-%s.mp3" (file-name-base video-file) start total)))))
           (shell-command (concat cmd " &"))))

     (defun my-record-wav-by-mp3 ()
       "Record a wav using meta data from current mp3 file."
       (interactive)
       (let* ((mp3-file (file-name-nondirectory (dired-file-name-at-point)))
              (base (file-name-base mp3-file))
              (params (split-string base  "-"))
              (output-file (concat base ".wav"))
              (total (string-to-number (nth (1- (length params)) params)))
              cmd)
         (if (= total 0) (setq total 4))
         (setq cmd (format "arecord -fdat -d %s \"%s\""
                           total
                           output-file))
           (message "Start recording %s seconds wav ..." total)
           (my-async-shell-command cmd)))
     (defun my-play-both-mp3-and-wav ()
       "Play wav and mp3."
       (interactive)
       (let* ((audio-file (file-name-nondirectory (dired-file-name-at-point)))
              (base (file-name-base audio-file))
              (ext (file-name-extension audio-file) )
              (cmd (format "mplayer -quiet \"%s\" \"%s\""
                           audio-file
                           (concat base "." (if (string= ext "mp3") "wav" "mp3")))))
         (my-async-shell-command cmd)))
     (defun my-copy-file-info (fn)
       (message "%s => clipboard & yank ring"
                (copy-yank-str (funcall fn (dired-file-name-at-point)))))
     (defhydra hydra-dired (:color blue)
       "
^Misc^                      ^File^             ^Copy Info^
----------------------------------------------------------------
[_vv_] video2mp3            [_R_] Move         [_pp_] Path
[_aa_] Record by mp3        [_cf_] New         [_nn_] Name
[_zz_] Play wav&mp3         [_rr_] Rename      [_bb_] Base
[_cc_] Last command         [_ff_] Find        [_dd_] directory
[_sa_] Fetch all subtitles  [_C_]  Copy
[_s1_] Fetch on subtitle    [_rb_] Change base
[_+_] Create directory
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
       ("vv" my-extract-mp3-from-video)
       ("aa" my-record-wav-by-mp3)
       ("cc" my-dired-redo-last-command)
       ("zz" my-play-both-mp3-and-wav)
       ("C" dired-do-copy)
       ("R" dired-rename-file)
       ("cf"find-file)
       ("rr" dired-toggle-read-only)
       ("ff" (lambda (regexp)
               (interactive "sMatching regexp: ")
               (find-lisp-find-dired default-directory regexp)))
       ("+" dired-create-directory)
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
_u_ company-ispell     %(if (memq 'company-ispell company-backends) t)
_a_ abbrev-mode:       %`abbrev-mode
_d_ debug-on-error:    %`debug-on-error
_f_ auto-fill-mode:    %`auto-fill-function
_t_ truncate-lines:    %`truncate-lines
_w_ whitespace-mode:   %`whitespace-mode
_i_ indent-tabs-mode:   %`indent-tabs-mode
"
  ("u" toggle-company-ispell nil)
  ("a" abbrev-mode nil)
  ("d" toggle-debug-on-error nil)
  ("f" auto-fill-mode nil)
  ("t" toggle-truncate-lines nil)
  ("w" whitespace-mode nil)
  ("i" (lambda () (interactive) (setq indent-tabs-mode (not indent-tabs-mode))) nil)
  ("q" nil "quit"))
;; Recommended binding:
(global-set-key (kbd "C-c C-h") 'hydra-toggle/body)
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
 ^Search^         ^Dictionary^
-----------------------------------------
_g_ Google        _b_ English => English
_f_ Finance       _t_ English => Chinese
_s_ StackOverflow _d_ dict.org
_h_ Code
_m_ Man
"
  ("b" sdcv-search-input)
  ("t" sdcv-search-input+)
  ("d" my-lookup-dict-org)
  ("g" w3m-google-search)
  ("f" w3m-search-financial-dictionary)
  ("s" w3m-stackoverflow-search)
  ("h" w3mext-hacker-search)
  ("m" lookup-doc-in-man)
  ("q" nil))
(global-set-key (kbd "C-c C-s") 'hydra-search/body)

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
