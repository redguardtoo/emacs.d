;; -*- coding: utf-8; lexical-binding: t; -*-

;; @see https://github.com/abo-abo/hydra
;; color could: red, blue, amaranth, pink, teal

;; use similar key bindings as init-evil.el
(defhydra my-hydra-launcher (:color blue)
  "
^Misc^                    ^Study^                    ^Emms^
-------------------------------------------------------------------
[_ss_] Save workgroup     [_vv_] Pronounce word      [_R_] Random
[_ll_] Load workgroup     [_W_] Big word list        [_n_] Next
[_B_] New bookmark        [_vi_] Play word's video   [_p_] Previous
[_m_] Goto bookmark       [_im_] Image of word       [_P_] Pause
[_bb_] Switch Gnus buffer [_w_] Select big word      [_S_] Stop
[_e_] Erase buffer        [_s1_] Pomodoro tiny task  [_O_] Open
[_r_] Erase this buffer   [_s2_] Pomodoro big task   [_L_] Playlist
[_f_] Recent file         [_st_] Pomodoro stop       [_K_] Search
[_d_] Recent directory    [_sr_] Pomodoro resume     [_F_] filter
[_z_] Jump around (z.sh)  [_sp_] Pomodoro pause      [_E_] replay
[_bh_] Bash history       [_as_] Ascii table
[_hh_] Favorite theme     [_T_] Typewriter on/off
[_hr_] Random theme       [_V_] Old typewriter
[_ka_] Kill other buffers
[_ii_] Imenu
[_id_] Insert date string
[_aa_] Adjust subtitle
[_q_] Quit
"
  ("aa" my-srt-offset-subtitles-from-point)
  ("B" my-bookmark-set)
  ("m" my-bookmark-goto)
  ("f" my-counsel-recentf)
  ("d" my-recent-directory)
  ("bh" my-insert-bash-history)
  ("hh" my-random-favorite-color-theme)
  ("hr" my-random-healthy-color-theme)
  ("ii" my-counsel-imenu)
  ("ka" my-kill-all-but-current-buffer)
  ("id" my-insert-date)
  ("as" my-ascii-table)
  ("ss" wg-create-workgroup)
  ("ll" wg-open-workgroup)
  ("e" shellcop-erase-buffer)
  ("r" shellcop-reset-with-new-command)
  ("z" shellcop-jump-around)
  ("T" my-toggle-typewriter)
  ("V" twm/toggle-sound-style)

  ;; {{pomodoro
  ("s1" (pomodoro-start 15))
  ("s2" (pomodoro-start 60))
  ("st" pomodoro-stop)
  ("sr" pomodoro-resume)
  ("sp" pomodoro-pause)
  ;; }}

  ;; {{emms
  ("R" (progn (emms-shuffle) (emms-random)))
  ("F" my-emms-playlist-filter)
  ("K" my-emms-playlist-random-track)
  ("E" (emms-seek-to 0))
  ("p" emms-previous)
  ("P" emms-pause)
  ("S" emms-stop)
  ("O" emms-play-playlist)
  ("n" emms-next)
  ("L" emms-playlist-mode-go)
  ;; }}

  ("vv" mybigword-pronounce-word)
  ("w" mybigword-big-words-in-current-window)
  ("im" mybigword-show-image-of-word)
  ("W" my-lookup-bigword-definition-in-buffer)
  ("vi" mybigword-play-video-of-word-at-point)
  ("bb" dianyou-switch-gnus-buffer)
  ("q" nil :color red))

;; Because in message-mode/article-mode we've already use `y' as hotkey
(global-set-key (kbd "C-c C-y") 'my-hydra-launcher/body)
(defun org-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'my-hydra-launcher/body))
(add-hook 'org-mode-hook 'org-mode-hook-hydra-setup)

(with-eval-after-load 'find-file-in-project
  (defhydra my-hydra-diff (:color blue)
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
    ("q" nil)))
(defun ffip-diff-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'my-hydra-diff/body))
(add-hook 'ffip-diff-mode-hook 'ffip-diff-mode-hook-hydra-setup)

;; gnus-summary-mode
(with-eval-after-load 'gnus-sum
  (defhydra my-hydra-gnus-summary (:color blue)
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
  (define-key gnus-summary-mode-map "y" 'my-hydra-gnus-summary/body))

;; gnus-article-mode
(with-eval-after-load 'gnus-art
  (defhydra my-hydra-gnus-article (:color blue)
    "
[_o_] Save attachment        [_F_] Forward
[_v_] Play video/audio       [_r_] Reply
[_d_] CLI to download stream [_R_] Reply with original
[_b_] Open external browser  [_w_] Reply all (S w)
[_;_] Click link/button      [_W_] Reply all with original (S W)
[_b_] Switch Gnus buffer
"
    ("F" gnus-summary-mail-forward)
    ("r" gnus-summary-reply)
    ("R" gnus-article-reply-with-original)
    ("w" gnus-summary-wide-reply)
    ("W" gnus-article-wide-reply-with-original)
    ("o" (lambda () (interactive) (let* ((file (gnus-mime-save-part))) (when file (copy-yank-str file)))))
    ("v" my-browser-open-with-mplayer)
    ("d" my-browser-download-rss-stream)
    ("b" my-browser-open-link-or-image-or-url)
    (";" eww-lnum-follow)
    ("b" dianyou-switch-gnus-buffer)
    ("q" nil))
  ;; y is not used by default
  (define-key gnus-article-mode-map "y" 'my-hydra-gnus-article/body))

;; message-mode
(with-eval-after-load 'message
  (defhydra my-hydra-message (:color blue)
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
    ("q" nil)))

(defun message-mode-hook-hydra-setup ()
  (local-set-key (kbd "C-c C-y") 'my-hydra-message/body))
(add-hook 'message-mode-hook 'message-mode-hook-hydra-setup)

;; {{ dired
;; -*- coding: utf-8; lexical-binding: t; -*-

(with-eval-after-load 'dired
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

  (defun my-extract-mkv-subtitle ()
    "Use mkvtoolnix to extract mkv subtitle."
    (interactive)
    (let* ((file (file-name-nondirectory (dired-file-name-at-point)))
           (ext (file-name-extension file))
           (default-directory (file-name-directory (dired-file-name-at-point)))
           trunks
           track-number)
      (cond
       ((not (string= "mkv" ext))
        (message "Only mkv files can be processed."))
       ((not (executable-find "mkvextract"))
        (message "Please install mkvtoolnix."))
       (t
        ;; split output into trunks
        (setq trunks (split-string (shell-command-to-string (format "mkvinfo \"%s\"" file))
                                   "| ?\\+ [A-Z][^\n]+[\n]*"))
        ;; only interested english subtitle trunk
        (setq trunks (cl-remove-if-not
                      (lambda (trunk)
                        (string-match "Track type: subtitles" trunk))
                      trunks))
        ;; If there is more than one subtitle, process English track only
        (when (> (length trunks) 1)
          (setq trunks (cl-remove-if-not
                        (lambda (trunk)
                          (string-match "Language: eng" trunk))
                        trunks)))
        (when (and (> (length trunks) 0)
                   (string-match "Track number: \\([0-9]+\\)" (car trunks)))

          ;; only extract the track number from the first truck
          (setq track-number (1- (string-to-number (match-string 1 (car trunks)))))
          (shell-command (format "mkvextract tracks \"%s\" %s:\"%s.srt\" > /dev/null 2>&1"
                                 file
                                 track-number
                                 (file-name-base file))))))))

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
    "Copy file or directory info."
    (let* ((file-name (dired-file-name-at-point)))
      (when (file-directory-p file-name)
        (setq file-name (directory-file-name file-name)))
      (message "%s => clipboard & yank ring"
               (copy-yank-str (funcall fn file-name)))))
  (defhydra my-hydra-dired (:color blue)
    "
^Misc^                      ^File^              ^Copy Info^
-----------------------------------------------------------------
[_vv_] Video => Mp3        [_R_] Move           [_pp_] Path
[_aa_] Record by mp3       [_cf_] New           [_nn_] Name
[_zz_] Play wav&mp3        [_rr_] Rename        [_bb_] Base name
[_sa_] Fetch subtitle(s)   [_C_]  Copy          [_dd_] directory
[_se_] Extract subtitle    [_rb_] Change base
[_aa_] Recording Wav       [_df_] Diff 2 files
[_ee_] Mkv => Srt          [_ff_] Find
[_+_] Create directory     [_du_] File usage
[_mp_] Mplayer extra opts
"
    ("mp" my-mplayer-setup-extra-opts)
    ("sa" shenshou-download-subtitle)
    ("se" shenshou-extract-subtitle-from-zip)
    ("pp" (my-copy-file-info 'file-truename))
    ("nn" (my-copy-file-info 'file-name-nondirectory))
    ("bb" (my-copy-file-info 'file-name-base))
    ("dd" (my-copy-file-info 'file-name-directory))
    ("rb" (my-replace-dired-base (car kill-ring)))
    ("vv" my-extract-mp3-from-video)
    ("ee" my-extract-mkv-subtitle)
    ("aa" my-record-wav-by-mp3)
    ("zz" my-play-both-mp3-and-wav)
    ("C" dired-do-copy)
    ("R" dired-do-rename)
    ("cf" find-file)
    ("du" my-file-usage)
    ("df" my-ediff-files)
    ("rr" dired-toggle-read-only)
    ("ff" (lambda (regexp)
            (interactive "sMatching regexp: ")
            (find-lisp-find-dired default-directory regexp)))
    ("+" dired-create-directory)
    ("q" nil)))

(defun dired-mode-hook-hydra-setup ()
  (local-set-key (kbd "y") 'my-hydra-dired/body))
(add-hook 'dired-mode-hook 'dired-mode-hook-hydra-setup)
;; }}

;; increase and decrease font size in GUI emacs
;; @see https://oremacs.com/download/london.pdf
(when (display-graphic-p)
  ;; Since we already use GUI Emacs, f2 is definitely available
  (defhydra my-hydra-zoom (global-map "<f2>")
    "Zoom"
    ("g" text-scale-increase "in")
    ("l" text-scale-decrease "out")
    ("r" (text-scale-set 0) "reset")
    ("q" nil "quit")))

;; {{ @see https://github.com/abo-abo/hydra/blob/master/hydra-examples.el
(defvar whitespace-mode nil)
(defhydra my-hydra-toggle (:color pink)
  "
_u_ company-ispell     %(and (boundp 'company-backends) (memq 'company-ispell company-backends) t)
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
(global-set-key (kbd "C-c C-t") 'my-hydra-toggle/body)
;; }}

;; {{ @see https://github.com/abo-abo/hydra/wiki/Window-Management

;; helpers from https://github.com/abo-abo/hydra/blob/master/hydra-examples.el
(defun hydra-move-split-left (arg)
  "Move window split left."
  (interactive "p")
  (if (let* ((windmove-wrap-around))
        (windmove-find-other-window 'right))
      (shrink-window-horizontally arg)
    (enlarge-window-horizontally arg)))

(defun hydra-move-split-right (arg)
  "Move window split right."
  (interactive "p")
  (if (let* ((windmove-wrap-around))
        (windmove-find-other-window 'right))
      (enlarge-window-horizontally arg)
    (shrink-window-horizontally arg)))

(defun hydra-move-split-up (arg)
  "Move window split up."
  (interactive "p")
  (if (let* ((windmove-wrap-around))
        (windmove-find-other-window 'up))
      (enlarge-window arg)
    (shrink-window arg)))

(defun hydra-move-split-down (arg)
  "Move window split down."
  (interactive "p")
  (if (let* ((windmove-wrap-around))
        (windmove-find-other-window 'up))
      (shrink-window arg)
    (enlarge-window arg)))

(defhydra my-hydra-window ()
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
  ("h" windmove-left)
  ("j" windmove-down)
  ("k" windmove-up)
  ("l" windmove-right)
  ("q" hydra-move-split-left)
  ("w" hydra-move-split-down)
  ("e" hydra-move-split-up)
  ("r" hydra-move-split-right)
  ("b" ivy-switch-buffer)
  ("f" counsel-find-file)
  ("F" follow-mode)
  ("a" (ace-window 1))
  ("v" (lambda ()
         (interactive)
         (split-window-right)
         (windmove-right)))
  ("x" (lambda ()
         (interactive)
         (split-window-below)
         (windmove-down)))
  ("s" (ace-window 4))
  ("S" save-buffer)
  ("d" delete-window)
  ("D" (ace-window 16))
  ("o" delete-other-windows)
  ("i" ace-delete-other-windows)
  ("z" (progn
         (winner-undo)
         (setq this-command 'winner-undo)))
  ("Z" winner-redo)
  ("SPC" nil))
(global-set-key (kbd "C-c C-w") 'my-hydra-window/body)
;; }}

;; {{ git-gutter, @see https://github.com/abo-abo/hydra/wiki/Git-gutter
(defhydra my-hydra-git (:body-pre
                     (progn
                       (git-gutter-mode 1)
                       (setq git-link-use-commit t))
                     :after-exit (setq git-link-use-commit nil)
                     :color blue)
"
Git:
[_dd_] Diff               [_ri_] Rebase closest
[_dc_] Diff staged        [_s_] Show commit
[_dr_] Diff range         [_rr_] Reset gutter
[_au_] Add modified       [_rh_] Gutter => HEAD
[_cc_] Commit             [_l_] Log selected/file
[_ca_] Amend              [_b_] Branches
[_ja_] Amend silent       [_k_] Git commit link
[_tt_] Stash              [_Q_] Quit gutter
[_ta_] Apply stash        [_cr_] Cherry pick from reflog
[_f_] Find file in commit

"
  ("ri" my-git-rebase-interactive)
  ("rr" my-git-gutter-reset-to-default)
  ("rh" my-git-gutter-reset-to-head-parent)
  ("cb" my-git-current-branch)
  ("s" my-git-show-commit)
  ("l" magit-log-buffer-file)
  ("b" magit-show-refs)
  ("k" git-link)
  ("g" magit-status)
  ("ta" magit-stash-apply)
  ("tt" magit-stash)
  ("dd" magit-diff-dwim)
  ("dc" magit-diff-staged)
  ("dr" (magit-diff-range (my-git-commit-id)))
  ("cc" magit-commit-create)
  ("ca" magit-commit-amend)
  ("nn" my-git-commit-create)
  ("na" my-git-commit-amend)
  ("ja" (my-git-commit-amend t))
  ("au" magit-stage-modified)
  ("Q" my-git-gutter-toggle)
  ("f" my-git-find-file-in-commit)
  ("cr" my-git-cherry-pick-from-reflog)
  ("q" nil))
(global-set-key (kbd "C-c C-g") 'my-hydra-git/body)
;; }}

(defhydra my-hydra-ebook ()
  "
[_v_] Pronounce word
[_;_] Jump to word
[_w_] Display bigword in current window
"
  ("v" mybigword-pronounce-word)
  (";" avy-goto-char-2)
  ("w" mybigword-big-words-in-current-window)
  ("q" nil))

(defhydra my-hydra-search ()
  "
_b_ English => English
_t_ English => Chinese
_d_ dict.org
_m_ Man
"
  ("b" my-dict-complete-definition)
  ("t" my-dict-simple-definition)
  ("d" my-lookup-dict-org)
  ("m" my-lookup-doc-in-man)
  ("q" nil))
(global-set-key (kbd "C-c C-s") 'my-hydra-search/body)

(defhydra my-hydra-describe (:color blue :hint nil)
  "
Describe Something: (q to quit)
_a_ all help for everything screen
_b_ bindings
_c_ char
_C_ coding system
_f_ function
_i_ input method
_k_ key briefly
_K_ key
_l_ language environment
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
  ("C" describe-categories)
  ("c" describe-char)
  ("C" describe-coding-system)
  ("f" describe-function)
  ("i" describe-input-method)
  ("K" describe-key)
  ("k" describe-key-briefly)
  ("l" describe-language-environment)
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
(global-set-key (kbd "C-c C-q") 'my-hydra-describe/body)

(provide 'init-hydra)
;;; init-hydra.el ends here
