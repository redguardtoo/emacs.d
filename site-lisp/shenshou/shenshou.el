;;; shenshou.el --- Download&Extract subtitles from opensubtitles -*- lexical-binding: t; -*-

;; Copyright (C) 2021-2024 Chen Bin
;;
;; Version: 0.2.0

;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>
;; URL: http://github.com/redguardtoo/shenshou
;; Package-Requires: ((emacs "27.1"))
;; Keywords: convenience, tools

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; This program downloads subtitles from http://opensubtitles.com
;;
;; Please note,
;; - You MUST register an account at http://opensubtitles.com first.
;; - Command line program "curl" should exist.
;;   See `shenshou-curl-program'.
;;
;; Usage,
;;   - Set `shenshou-login-user-name' and `shenshou-login-password' first.
;;   - Run `shenshou-download-subtitle' in Dired buffer or anywhere.
;;   - Run `shenshou-logout-now' to logout.
;;   - Run `shenshou-extract-subtitle-from-zip' to extract subtitle from zip file.
;;     Subtitle is automatically renamed to match selected video file.
;;
;; Tips,
;;   - Use `shenshou-language-code-list' to set up subtitle's language.
;;     See https://en.wikipedia.org/wiki/ISO_639-1.
;;      (setq shenshou-language-code-list "en") # English
;;      (setq shenshou-language-code-list "en,zh") # English, Chinese
;;   - See `shenshou-curl-extra-options' on how to set SOCKS5 or HTTP proxy
;;   - This program gives you the freedom to select the right subtitle.

;;; Code:
;;

;; @see https://opensubtitles.stoplight.io/docs/opensubtitles-api/e3750fd63a100-getting-started for api doc
(require 'cl-lib)
(require 'json)
(require 'arc-mode)
(require 'dired)

(defgroup shenshou nil
  "Download subtitles from opensubtitles."
  :group 'tools)

(defcustom shenshou-curl-program "curl"
  "Name/path by which to invoke the curl program."
  :type 'string
  :group 'shenshou)

(defcustom shenshou-language-code-list "en"
  "Comma separated language codes (e.g. \"zh,ru,es,en\").
See https://en.wikipedia.org/wiki/ISO_639-1 for details."
  :type 'string
  :group 'shenshou)

(defcustom shenshou-curl-extra-options ""
  "Extra options pass to curl program.
Option for SOCKS proxy,  \"-x socks5h://127.0.0.1:9050\".
Option for HTTP proxy, \"-x http://username:password@127.0.0.1:8081\".
Please read curl's manual for more options."
  :type 'string
  :group 'shenshou)


(defcustom shenshou-supported-video-format
  '("mp4"
    "m4a"
    "mkv"
    "3gp"
    "mov"
    "mpeg"
    "mpg"
    "wmv"
    "ogg"
    "flv"
    "avi")
  "Supported video format."
  :type '(repeat string)
  :group 'shenshou)

(defcustom shenshou-login-user-name nil
  "User name to login opensubtitles.  It can't be empty.
Only logged-in user can download the subtitles."
  :type 'string
  :group 'shenshou)

(defcustom shenshou-zip-file-directory nil
  "Directory containing downloaded zip files."
  :type 'string
  :group 'shenshou)

(defcustom shenshou-login-password nil
  "Password to login opensubtitles.
If it's empty, user is required to provide password during login process."
  :type 'string
  :group 'shenshou)


(defcustom shenshou-api-key "9PEmFOnb2IzOHAbpbwRWcll01IsIjfFz"
  "Api key to access opensubtitles endpoint."
  :type 'string
  :group 'shenshou)

(defcustom shenshou-zip-file-directory nil
  "Directory containing downloaded zip files."
  :type 'string
  :group 'shenshou)

(defcustom shenshou-token-update-interval 60
  "The interval (minutes) to update login token."
  :group 'shenshou
  :type 'integer)

(defvar shenshou-token nil
  "Token to access opensubtitles api.  It's internally used.")

(defvar shenshou-debug nil "Debug flag.")

(defvar shenshou-tvshow-regex-1
  "\\(.*\\)s\\([0-9]\\{2\\}\\)e\\([0-9]\\{2\\}\\).\\(.*\\)"
  "Regex to extract tv show information (name, season, episode, team).")

(defvar shenshou-tvshow-regex-2
  "\\(.*\\).\\([0-9]\\{1,2\\}\\)x\\([0-9]\\{1,2\\}\\).\\(.*\\)"
  "Regex to extract tv show information (name, season, episode, team).")

(defvar shenshou-movie-regex-1
  "\\(.*\\)[.\[( ]\\{1\\}\\(19[0-9]\\{2\\}\\|20[0-9]\\{2\\}\\)\\(.*\\)"
  "Regex to extract movie show information (name, year, team).")

(defun shenshou-trim (string)
  "Trim STRING."
  (setq string (replace-regexp-in-string "^[ \t_-]+" "" string))
  (setq string (replace-regexp-in-string "[ \t_-]+$" "" string)))

(defun shenshou-json-read-string (string)
  "Read STRING into an object."
  (let (rlt)
    (with-temp-buffer
      (insert string)
      (goto-char (point-min))
      (setq rlt (json-read)))
    rlt))

(defun shenshou-value (beginning str)
  "Use eight bytes from BEGINNING of STR to get hash."
  (let ((n 0)
        (m 1)
        (j 0)
        c)
    ;; eight bytes in Little Endian order
    (while (< j 8)
      (setq c (aref str (+ j beginning)))
      (setq n (+ n (* c m)))
      (setq m (* m 256))
      (setq j (1+ j)))
    n))

(defun shenshou-hash-and-size(file)
  "Get hash and size of video FILE in the format like (hash . size).
OpenSubtitles.org uses special hash function to match subtitles against videos."
  (let (str fsize hash i rlt len)
    (setq str (with-temp-buffer
                (set-buffer-multibyte nil)
                (setq buffer-file-coding-system 'binary)
                (insert-file-contents-literally file)
                (buffer-substring-no-properties (point-min) (point-max))))
    (setq fsize (length str))
    (setq hash fsize)

    (when (> fsize 131072)
      ;; first 64k bytes
      (setq i 0)
      (while (< i 65536)
        (setq hash (logand (+ hash (shenshou-value i str)) #xFFFFFFFFFFFFFFFF))
        (setq i (+ i 8)))

      ;; last 64k bytes
      (setq i (- fsize 65536))
      (while (< i fsize)
        (setq hash (logand (+ hash (shenshou-value i str)) #xFFFFFFFFFFFFFFFF))
        (setq i (+ i 8)))

      (setq rlt (format "%016x" hash))
      ;; only last 16 digits of hash is used
      (when (> (setq len (length rlt)) 16)
        (setq rlt (substring rlt (- len 16) len))))

    (when shenshou-debug
      (message "shenshou-hash-and-size called => file=%s hash=%s size=%s" file rlt fsize))

    (when rlt
      (list :moviehash rlt :moviebytesize fsize))))

(defun shenshou-restful-call (method post-data url-params &optional http-method use-token-p)
  "Call remote api METHOD with POST-DATA or URL-PARAMS.  HTTP-METHOD is optional.
If USE-TOKEN-P is t, the access token is used."
  (let* ((url (format " --request %s --silent --location \"https://api.opensubtitles.com/api/v1/%s%s\" "
                      (or http-method "POST")
                      method
                      (if url-params (concat "?" url-params) "")))
         (cmd (concat shenshou-curl-program
                      url
                      shenshou-curl-extra-options
                      (format " -H \"Api-Key: %s\" " shenshou-api-key)
                      " -H \"User-Agent: shenshou v1\" "
                      (if use-token-p (format " -H \"Authorization: Bearer %s\" " shenshou-token) "")
                      " -H \"Content-Type: application/json\" "
                      (and post-data (format " --data '%s' " post-data))))
         (cmd-output (shell-command-to-string cmd)))
    (when shenshou-debug
      (message "shenshou-restful-call called => post-data=%s cmd=%s cmd-output=%s" post-data cmd cmd-output))

    (when (string-match "Your IP.*[^0-9.]\\([0-9.]+\\)<" cmd-output)
      (let ((ip (match-string 1 cmd-output))
            (id "unknown"))
        (when (string-match "Cloudflare Ray ID:.*>\\([0-9a-z]+\\)<" cmd-output)
          (setq id (match-string 1 cmd-output)))

        ;; output html output for debugging
        (when shenshou-debug
          (with-temp-buffer
            (insert cmd-output)
            ;; write buffer content into file
            (write-region (point-min) (point-max) "opensubtitles-captcha.html")))
        ;; some security setup only OpenSubtitles guy can help
        (error "Error: Report IP \"%s\" and Cloudflare Ray ID \"%s\" at opensubtitles to resolve the problem!"
               ip
               id)))

    (shenshou-json-read-string cmd-output)))

(defun shenshou-token-invalid-p ()
  "Test if token is invalid."
  (and (null shenshou-token)
       (> (- (float-time (current-time)) (float-time (cdr shenshou-token)))
          (* shenshou-token-update-interval 60))))

(defmacro shenshou-json-value (object key)
  "Get json OBJECT's value by KEY."
  `(cdr (assoc ,key ,object)))

;;;###autoload
(defun shenshou-login-now ()
  "Login remote opensubtitles server and set `shenshou-token'."
  (interactive)
  (when shenshou-debug
    (message "shenshou-login-now called."))
  ;; sanity check
  (cond
   ((or (not (executable-find shenshou-curl-program)))
    (error "You need install \"curl\" first"))

   ((null shenshou-login-user-name)
    (error "Please set `shenshou-login-user-name' first.  Only logged-in user can download the subtitles"))

   (t
    (unless shenshou-login-password
      (setq shenshou-login-password
            (read-passwd "Please input password for opensubtitles: ")))

    (when shenshou-login-password
      (let* ((resp (shenshou-restful-call "login"
                                          (format "{\"username\": \"%s\", \"password\": \"%s\"}"
                                                  shenshou-login-user-name
                                                  shenshou-login-password)
                                          nil))
             (user (shenshou-json-value resp 'user))
             (token (shenshou-json-value resp 'token))
             (status (shenshou-json-value resp 'status)))
        (when shenshou-debug
          (message "user=%s token=%s status=%s" user token status))
        (cond
         ((and user token (eq status 200))
          (setq shenshou-token token)
          (message "User %s logged into 'https://opensubtitles.com': user_id=%s allowed_downloads(daily)=%s level=%s token=%s"
                   shenshou-login-user-name
                   (shenshou-json-value user 'user_id)
                   (shenshou-json-value user 'allowed_downloads)
                   (shenshou-json-value user 'level)
                   token))
         (t
          (error "Login failed.  Please double check user name, password, api-key and network!"))))))))

;;;###autoload
(defun shenshou-logout-now ()
  "Logout and reset `shenshou-token'."
  (interactive)
  (let* ((resp (shenshou-restful-call "logout" nil nil "DELETE" t))
         (msg (shenshou-json-value resp 'message)))
    (message "Logout: %s" msg))
  (setq shenshou-token nil))

(defun shenshou-process-query (name)
  "Get query from video file NAME."
  (let ((query (match-string 1 name)))
    (setq query (replace-regexp-in-string "[ \t-_]*([^)]*$" "" query))
    (shenshou-trim query)))

(defun shenshou-guess-video-info (video-file)
  "Guess information from VIDEO-FILE."
  (let* ((name (downcase (file-name-base video-file)))
         dir-name
         (case-fold-search t)
         video-info)

    ;; tv show's name might appears only in directory
    (when (string-match "^ *S[0-9]+E[0-9]+" name)
      (setq dir-name (file-name-base (directory-file-name (file-name-directory video-file))))
      (setq name (concat (replace-regexp-in-string "season.?[0-9]+.*" "" dir-name)
                         " "
                         name)))

    (cond
     ((string-match shenshou-tvshow-regex-1 name)
      (setq video-info (plist-put video-info :moviekind "tv"))
      (setq video-info (plist-put video-info :query (shenshou-process-query name)))
      (setq video-info (plist-put video-info :season (match-string 2 name)))
      (setq video-info (plist-put video-info :episode (match-string 3 name))))

     ((string-match shenshou-tvshow-regex-2 name)
      (setq video-info (plist-put video-info :moviekind "tv"))
      (setq video-info (plist-put video-info :query (shenshou-process-query name)))
      (setq video-info (plist-put video-info :season (match-string 2 name))))

     ((string-match shenshou-movie-regex-1 name)
      (setq video-info (plist-put video-info :moviekind "movie"))
      (setq video-info (plist-put video-info :query (shenshou-process-query name)))
      (setq video-info (plist-put video-info :movieyear (match-string 2 name))))

     (t
      (setq video-info (plist-put video-info :moviekind "unknown"))
      (setq video-info (plist-put video-info :query name))))

    (when shenshou-debug
      (message "shenshou-guess-video-info called. name=%s video-info=%s"
               name
               video-info))

    video-info))

(defun shenshou-params-from-videos (video-file user-input-p)
  "Generate rpc parameters from VIDEO-FILE.
If USER-INPUT-P is t, user can input query."
  (let* (rlt video-info query)
    ;; guess info from base file name
    (when (setq video-info (shenshou-guess-video-info video-file))
      (setq query (plist-get video-info :query))
      (when user-input-p
        (setq query (read-string "Please input query: " query)))
      (setq rlt (format "query=%s&languages=%s"
                        (url-hexify-string query)
                        shenshou-language-code-list))

      (when (string= (plist-get video-info :moviekind) "tv")
        (setq rlt (concat rlt
                            (format "&type=episode&episode-number=%s&season_number=%s"
                                    (plist-get video-info :episode)
                                    (plist-get video-info :season))))))

    rlt))

(defun shenshou-sort-subtitles (subtitles video-name)
  "Sort SUBTITLES by measuring its string distance to VIDEO-NAME."
  (when shenshou-debug
    (message "shenshou-sort-subtitles called => %s %s" subtitles video-name))
  (when (> (length subtitles) 1)
    (setq subtitles
          (sort subtitles
                `(lambda (a b)
                   (< (string-distance (plist-get (cdr a) :moviereleasename) ,video-name)
                      (string-distance (plist-get (cdr b) :moviereleasename) ,video-name))))))

  (when shenshou-debug
    (message "shenshou-sort-subtitles called. subtitles=%s" subtitles))
  subtitles)

(defun shenshou-filter-subtitles (candidates video-file filter-level)
  "Filter subtitle CANDIDATES with VIDEO-FILE and FILTER-LEVEL.
If FILTER-LEVEL is 0, all candidates are accepted.
If FILTER-LEVEL is 1, movie name should exist.
If FILTER-LEVEL is 2, do more checking on movie name."

  (let* (subtitles
         ok-p
         (video-info (shenshou-guess-video-info video-file))
         (movie-fuzzy-name (replace-regexp-in-string "[.\[\] ()]+" ".*" (plist-get video-info :query))))

    (dotimes (i (length candidates))
      (let* (sub
             subfilename
             lang
             (item (elt candidates i))
             (attributes (shenshou-json-value item 'attributes))
             ;; OpenSubtitles hash function is not robust.
             ;; Use the MovieReleaseName to select the best candidate
             (movie-release-name (shenshou-json-value attributes 'release))
             (feature-details (shenshou-json-value attributes 'feature_details))
             (movie-year (format "%s" (shenshou-json-value feature-details 'year)))
             (movie-year-match-p (or (not (plist-get video-info :movieyear))
                                     (string= movie-year (plist-get video-info :movieyear))))
             (files (shenshou-json-value attributes 'files))
             first-file)

        ;; At least one subtitle file exists
        (when (> (length files) 0)
          (setq first-file (elt files 0))
          (when shenshou-debug
            (message "movie-year=%s movie-year-match-p=%s"
                     movie-year
                     movie-year-match-p))

          (cond
           ((eq filter-level 0)
            (setq ok-p t))
           ((eq filter-level 1)
            (setq ok-p (and movie-release-name movie-year-match-p)))
           ((eq filter-level 2)
            (when shenshou-debug
              (message "movie-fuzzy-name=%s movie-release-name=%s" movie-fuzzy-name movie-release-name))
            (setq ok-p (and movie-release-name
                            (string-match (concat "^" movie-fuzzy-name)
                                          (downcase movie-release-name))
                            movie-year-match-p))))

          (when ok-p
            (setq sub nil)
            (setq sub (plist-put sub :moviereleasename movie-release-name))
            (setq sub (plist-put sub :subfilename (setq subfilename (shenshou-json-value first-file 'file_name))))
            (setq sub (plist-put sub :file-id (shenshou-json-value first-file 'file_id)))
            (setq sub (plist-put sub :sublanguageid (setq lang (shenshou-json-value attributes 'language))))
            (push (cons (format "%s(%s)" subfilename lang) sub) subtitles)))))

    (when shenshou-debug
      (message "shenshou-filter-subtitles: candidates=%s video-file=%s filter-level=%s subtitles=%s"
               (length candidates)
               video-file
               filter-level
               (length subtitles)))

    subtitles))

(defun shenshou-search-subtitles (video-file user-input-p)
  "Search subtitles of VIDEO-FILE.
If USER-INPUT-P is t, user can input query."
  (let* ((url-params (shenshou-params-from-videos video-file user-input-p))
         (resp (shenshou-restful-call "subtitles"
                                      nil
                                      url-params
                                      "GET"))
         (candidates (shenshou-json-value resp 'data))
         subtitles)

    (cond
     ;; nothing can be done if there is no candidate
     ((eq (length candidates) 0)
      (when shenshou-debug
        (message "No subtitle candidate.")))

     ;; donot filter when there is only one candidate
     ((eq (length candidates) 1)
      (setq subtitles (shenshou-filter-subtitles candidates video-file 0))
      (when shenshou-debug
        (message "Only one subtitle candidate.  So use it anyway.")))

     ;; try most strict algorithm
     ((> (length (setq subtitles (shenshou-filter-subtitles candidates video-file 2)))
         0)
      (when shenshou-debug
        (message "filter-level=2 subtitles=%s" subtitles)))

     ;; then go easy
     ((> (length (setq subtitles (shenshou-filter-subtitles candidates video-file 1)))
         0)
      (when shenshou-debug
        (message "filter-level=0 subtitles=%s" subtitles))))
    (shenshou-sort-subtitles subtitles (file-name-base video-file))))

(defun shenshou-default-directory (video-file)
  "Get VIDEO-FILE's directory."
  (if (eq major-mode 'dired-mode) default-directory
    (file-name-directory video-file)))

(defun shenshou-subtitle-file-name (video-file)
  "Get file name of VIDEO-FILE's subtitle."
  (when video-file
    (concat (file-name-base video-file) ".srt")))

;;;###autoload
(defun shenshou-download-subtitle-internal (video-file user-input-p)
  "Download subtitle of VIDEO-FILE.
If USER-INPUT-P is t, user can input query."
  (let* (subtitles selected token-p)
    (when shenshou-debug
      (message "shenshou-download-subtitle-internal called => %s" video-file))

    (setq token-p t)
    (unless (shenshou-token-invalid-p)
      (setq token-p (shenshou-login-now)))

    (when token-p
      ;; search subtitles
      (setq subtitles (shenshou-search-subtitles video-file user-input-p))
      (when shenshou-debug
        (message "shenshou-search-subtitles returns: %s" subtitles))

      (cond
       ((> (length subtitles) 0)
        (when (setq selected (completing-read (format "Download subtitle of \"%s\": "
                                                      (file-name-nondirectory video-file))
                                              subtitles))
          (let* ((default-directory (shenshou-default-directory video-file))
                 (sub (cdr (assoc selected subtitles)))
                 (file-id (plist-get sub :file-id))
                 (resp (shenshou-restful-call "download"
                                              (format "{\"file_id\": \"%s\"}" file-id)
                                              nil
                                              "POST"
                                              t))
                 (download-link (shenshou-json-value resp 'link))
                 (file-name (shenshou-json-value resp 'file_name))
                 (remaining (shenshou-json-value resp 'remaining))
                 (reset-time (shenshou-json-value resp 'reset_time))
                 (output-file (shenshou-subtitle-file-name video-file))
                 download-cmd)

            (when (and download-link (> (length download-link) 0))
              (setq download-cmd (format "%s --silent %s --location \"%s\" > \"%s\" &"
                                         shenshou-curl-program
                                         shenshou-curl-extra-options
                                         download-link
                                         output-file))
              (when shenshou-debug
                (message "download-cmd=%s" download-cmd))

              (call-process-shell-command download-cmd)
              (message "Download \"%s\"; Remaining: %s; Reset time: %s"
                       file-name
                       remaining
                       reset-time)))))

       (t
        (message "No subtitle is found for \"%s\""
                 (file-name-nondirectory video-file)))))))

(defun shenshou-get-videos ()
  "Get video files."
  (let* (file
         (videos (cond
                  ((eq major-mode 'dired-mode)
                   (dired-get-marked-files t current-prefix-arg))

                  (t
                   (when (setq file (read-file-name "Please select a video: "))
                     (list file))))))
    ;; filter video files by their extensions
    (delq nil
          (mapcar (lambda (f)
                    (and (member (file-name-extension f)
                                 shenshou-supported-video-format)
                         f))
                  videos))))

;;;###autoload
(defun shenshou-download-subtitle (&optional user-input-p)
  "Download subtitles of video files.
If current buffer is Dired buffer, marked videos will be processed.
Or else user need specify the video to process.
If USER-INPUT-P is t, user can input query."
  (interactive "P")
  (let* ((videos (shenshou-get-videos)))

    (cond
     ((> (length videos) 0)
      (message "Fetching subtitles of %d video(s) ..."
               (length videos))

      (dolist (v videos)
        ;; make sure full path is passed because parent directory
        ;; name might be used too
        (shenshou-download-subtitle-internal (file-truename v)
                                             user-input-p)))

     (t
      (message "No video files are selected.")))))

;;;###autoload
(defun shenshou-extract-subtitle-from-zip ()
  "Extract subtitle from zip file and rename it to match selected video."
  (interactive)
  (let* ((video-file (car (shenshou-get-videos)))
         (zip-file (when video-file
                     (read-file-name "Select zip file:"
                                     shenshou-zip-file-directory)))
         (zip-summarize (when zip-file
                          (with-temp-buffer
                            (set-buffer-multibyte nil)
                            (setq buffer-file-coding-system 'binary)
                            (insert-file-contents-literally zip-file)
                            (archive-zip-summarize))))
         (enames (delq nil
                       (mapcar (lambda (e)
                                 (let ((ename (if (fboundp 'archive--file-desc-ext-file-name)
                                                  ;; emacs 28
                                                  (archive--file-desc-ext-file-name e)
                                                ;; emacs 27
                                                (aref e 0))))
                                   (when (string-match "\\.srt$" ename)
                                     ename)))
                               zip-summarize)))
         (selected-ename (when enames
                           (cond
                            ((eq 1 (length enames))
                             (car enames))
                            (t
                             (completing-read "Select subtitle to extract: "
                                              enames))))))

    (when selected-ename
      (with-temp-buffer
        (archive-zip-extract zip-file selected-ename)
        (let* ((srt-file (shenshou-subtitle-file-name video-file)))
          (write-region (point-min) (point-max) srt-file)
          (message "%s is created at %s." srt-file default-directory))))))

(provide 'shenshou)
;;; shenshou.el ends here
