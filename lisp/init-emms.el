;; -*- coding: utf-8; lexical-binding: t; -*-

(defun my-emms-track-description (track)
  "Description of TRACK."
  (let ((desc (emms-track-simple-description track))
        (type (emms-track-type track)))
    (when (eq 'file type)
      (setq desc (my-strip-path desc 2)))
    desc))

(with-eval-after-load 'emms
  ;; minimum setup is more robust
  (emms-minimalistic)
  ;; only show file track's base name
  (setq emms-track-description-function 'my-emms-track-description)

  ;; {{ extract track's information
  ;; `emms-info-native' supports mp3,flac and requires NO cli tools
  (unless (memq 'emms-info-native emms-info-functions)
    (require 'emms-info-native)
    (push 'emms-info-native emms-info-functions))

  ;; you can add uncomment below setup to add more methods.
  ;; @see https://www.gnu.org/software/emms/manual/#Track-Information
  ;; But more methods slows down emms

  ;; (unless (memq 'emms-info-cueinfo emms-info-functions)
  ;;   (require 'emms-cue)
  ;;   (push 'emms-info-cueinfo emms-info-functions))

  ;; (when (and (not (memq 'emms-info-metaflac emms-info-functions))
  ;;            (executable-find "metaflac"))
  ;;   (require 'emms-info-metaflac)
  ;;   (push 'emms-info-metaflac emms-info-functions))

  (push 'emms-info-initialize-track emms-track-initialize-functions)
  ;; }}

  (setq emms-source-file-exclude-regexp
        (concat "\\`\\(#.*#\\|.*,v\\|.*~\\|\\.\\.?\\|\\.#.*\\|,.*\\)\\'\\|"
                "/\\(CVS\\|RCS\\|\\.dropbox.attr\\|\\.git\\|,.*\\|\\.svn\\)\\(/\\|\\'\\)"))
  (setq emms-player-list '(emms-player-mplayer
                           emms-player-vlc)))

(defun my-emms-play (&optional subdir-p)
  "Play media files which are marked or in marked sub-directories.
If SUBDIR-P is t, play videos in sub-directories too."
  (interactive "P")
  (my-ensure 'emms)
  (my-ensure 'emms-player-simple)

  (unless my-emms-mplayer-no-video-or-cover-art
    ;; no cd art
    (dolist (p '("null" "-vo" ))
      (setq emms-player-mplayer-parameters
            (delete p emms-player-mplayer-parameters))
      (setq emms-player-mplayer-playlist-parameters
            (delete p emms-player-mplayer-playlist-parameters))))

  (unless (eq major-mode 'dired-mode)
    (error "This command is only used in `dired-mode'"))

  (let* ((items (dired-get-marked-files t current-prefix-arg))
         (regexp (my-file-extensions-to-regexp my-media-file-extensions))
         found)
    (cond
     ;; at least two items are selected
     ((> (length items) 1)
      ;; clear existing playlist
      (emms-playlist-current-clear)
      (sit-for 1)

      (dolist (item items)
        (cond
         ((file-directory-p item)
          (emms-add-directory-tree item)
          (setq found t))

         ((string-match regexp item)
          ;; add media file to the playlist
          (emms-add-file item)
          (setq found t))))

      (when found
        (with-current-buffer emms-playlist-buffer-name
          (emms-playlist-current-select-first)
          (emms-start))))

     (subdir-p
      (emms-add-directory-tree default-directory)
      (with-current-buffer emms-playlist-buffer-name
        (emms-playlist-current-select-first)
        (emms-start)))

     ;; play video under current directory and default directory
     (t
      (emms-play-directory default-directory)))))

(defvar my-emms-playlist-random-track-keyword "mozart"
  "Keyword to find next random track in emms playlist.
Space in the keyword matches any characters.
 \"|\" means OR operator in regexp.")

(defvar my-emms-playlist-filter-keyword "mozart"
  "Keyword to filter tracks in emms playlist.
Space in the keyword matches any characters.
 \"|\" means OR operator in regexp.")

(defvar my-emms-track-regexp-function
  (lambda (str)
    ;; can search track with Chinese information
    (my-emms-track-regexp-internal (my-extended-regexp str)))
  "Get regexp to search track.")

(defun my-emms-track-regexp-internal (keyword)
  "Convert KEYWORD into regexp for matching tracks."
  (let* ((re (replace-regexp-in-string "|" "\\\\|" keyword)))
    (setq re (replace-regexp-in-string " +" ".*" re))))

(defun my-emms-track-match-p (track keyword)
  "Test if TRACK's information match KEYWORD."
  (let* ((case-fold-search t)
         (regexp (funcall my-emms-track-regexp-function keyword))
         s)
    (or (string-match regexp (emms-track-force-description track))
        (and (setq s (emms-track-get track 'info-genre)) (string-match regexp s))
        (and (setq s (emms-track-get track 'info-title)) (string-match regexp s))
        (and (setq s (emms-track-get track 'info-album)) (string-match regexp s))
        (and (setq s (emms-track-get track 'info-composer)) (string-match regexp s))
        (and (setq s (emms-track-get track 'info-artist)) (string-match regexp s)))))

(defun my-emms-show ()
  "Show information of current track."
  (interactive)
  (let* ((emms-track-description-function (lambda (track)
                                            (let ((composer (emms-track-get track 'info-composer))
                                                  (artist (emms-track-get track 'info-artist)))
                                              (concat (if composer (format "%s(C) => " composer))
                                                      (if artist (format "%s(A) => " artist))
                                                      (my-emms-track-description track))))))
    (emms-show)))

(defun my-emms-search-track ()
  "Search track."
  (let* ((case-fold-search t)
         (continue-p t)
         found-p
         track)
    (while continue-p
      (cond
       ((and (setq track (emms-playlist-track-at))
             (my-emms-track-match-p track my-emms-playlist-random-track-keyword))
        (emms-playlist-mode-play-current-track)
        (setq found-p t)
        (setq continue-p nil))
       (t
        (forward-line 1)
        (setq continue-p (< (point) (1- (point-max)))))))

    found-p))

(defun my-emms-playlist-random-track (&optional input-p)
  "Play random track in emms playlist.
If INPUT-P is t, `my-emms-playlist-random-track-keyword' is input by user."
  (interactive "P")
  (when input-p
    (setq my-emms-playlist-random-track-keyword
          (read-string "Keyword for random track: ")))

  (with-current-buffer emms-playlist-buffer-name
    ;; search below current track
    (forward-line 1)
    (let* ((found-p (my-emms-search-track)))
      ;; if not found, search from the beginning
      (unless found-p
        (goto-char (point-min))
        (setq found-p (my-emms-search-track)))
      (cond
       (found-p
        ;; show current track info
        (my-emms-show))
       (t
        (message "No track is found."))))))

(defun my-emms-playlist-filter (&optional input-p)
  "Filter tracks in emms playlist.
If INPUT-P is t, `my-emms-playlist-random-track-keyword' is input by user."
  (interactive "P")
  ;; shuffle the playlist
  (when input-p
    (setq my-emms-playlist-filter-keyword
          (read-string "Keyword to filter tracks in playlist: ")))
  (with-current-buffer emms-playlist-buffer-name
    (goto-char (point-min))
    (let* ((case-fold-search t)
           track)
      (while (setq track (emms-playlist-track-at))
        (cond
         ((my-emms-track-match-p track my-emms-playlist-filter-keyword)
          (forward-line 1))
         (t
          (emms-playlist-mode-kill-track))))))
  (emms-random)
  ;; show current track info
  (my-emms-show))

(defvar my-emms-mplayer-no-video-or-cover-art nil
  "Emms mplayer backend does not play video or cover art.")

(with-eval-after-load 'emms-player-simple
  (when my-emms-mplayer-no-video-or-cover-art
    (define-emms-simple-player mplayer '(file url)
      (concat "\\`\\(http[s]?\\|mms\\)://\\|"
              (apply #'emms-player-simple-regexp
                     emms-player-base-format-list))
      "mplayer" "-slave" "-quiet" "-really-quiet" "-vo" "null")

    (define-emms-simple-player mplayer-playlist '(streamlist)
      "\\`http[s]?://"
      "mplayer" "-slave" "-quiet" "-really-quiet" "-vo" "null" "-playlist")))

(defvar my-music-root-directory "~/Dropbox/music"
  "Music root directory.")

(defun my-music (&optional no-shuffle-p)
  "My music.  If NO-SHUFFLE-P is t, don't shuffle the tracks."
  (interactive "P")
  (my-ensure 'emms)
  (my-ensure 'emms-player-simple)

  (unless my-emms-mplayer-no-video-or-cover-art
    ;; no cd art
    (dolist (p '("null" "-vo" ))
      (unless (member p emms-player-mplayer-parameters)
        (push p emms-player-mplayer-parameters))
      (unless (member p emms-player-mplayer-playlist-parameters)
        (push p emms-player-mplayer-playlist-parameters))))

  (emms-stop)
  (when (bufferp emms-playlist-buffer-name)
    (kill-buffer emms-playlist-buffer-name))
  (emms-play-directory-tree my-music-root-directory)
  (unless no-shuffle-p
    (emms-shuffle))
  (emms-next))

(provide 'init-emms)
;;; init-emms.el ends here
