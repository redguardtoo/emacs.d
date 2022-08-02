;;; shenshou.el --- Download&Extract subtitles from opensubtitles -*- lexical-binding: t; -*-

;; Copyright (C) 2021-2022 Chen Bin
;;
;; Version: 0.0.8

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

;; This program downloads subtitles from opensubtitles
;;
;; Please note,
;; - You MUST register an account at opensubtitles.com first.
;;   That's required by opensubtitles' latest policy.
;; - Command line program "curl".
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

(defcustom shenshou-strict-match-p nil
  "Download subtitles exactly matching the video files."
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
  (let* ((url (format " --request %s --silent --insecure --url \"https://api.opensubtitles.com/api/v1/%s%s\" "
                      (or http-method "POST")
                      method
                      (if url-params (concat "?" url-params) "")))
         (cmd (concat shenshou-curl-program
                      url
                      shenshou-curl-extra-options
                      (format " -H \"Api-Key: %s\" " shenshou-api-key)
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

(defun shenshou-format-struct-member (name value)
  "Format a struct member with its NAME and VALUE."
  (format "%s=%s&" name (url-hexify-string value)))

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
   ((not (executable-find shenshou-curl-program))
    (error "You need install \"curl\" first"))

   ((null shenshou-login-user-name)
    (error "Please set `shenshou-login-user-name' first.  Only logged-in user can download subtitles"))

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
          (message "User %s logged into 'https://opensubtitles.com': user_id=%s allowed_downloads(daily)=%s level=%s"
                   shenshou-login-user-name
                   (shenshou-json-value user 'user_id)
                   (shenshou-json-value user 'allowed_downloads)
                   (shenshou-json-value user 'level)))
         (t
          (error "Login failed.  Please double check user name, password, api-key and network!"))))))))

;;;###autoload
(defun shenshou-logout-now ()
  "Logout and reset `shenshou-token'."
  (interactive)
  (setq shenshou-token nil))

(defun shenshou-process-query (name)
  "Get query from video file NAME."
  (let ((query (match-string 1 name)))
    (setq query (replace-regexp-in-string "[ \t-_]*([^)]*$" "" query))
    (shenshou-trim query)))

(defun shenshou-guess-video-info (name)
  "Guess information from NAME of video."
  (let* (video-info)
    (cond
     ((string-match shenshou-tvshow-regex-1 name)
      (setq video-info (plist-put video-info :moviekind "tv"))
      (setq video-info (plist-put video-info :query (shenshou-process-query name)))
      (setq video-info (plist-put video-info :season (match-string 2 name)))
      (setq video-info (plist-put video-info :episode (match-string 3 name)))
      (setq video-info (plist-put video-info :team (shenshou-trim (match-string 4 name)))))

     ((string-match shenshou-tvshow-regex-2 name)
      (setq video-info (plist-put video-info :moviekind "tv"))
      (setq video-info (plist-put video-info :query (shenshou-process-query name)))
      (setq video-info (plist-put video-info :season (match-string 2 name)))
      (setq video-info (plist-put video-info :episode (match-string 3 name)))
      (setq video-info (plist-put video-info :team (shenshou-trim (match-string 4 name)))))

     ((string-match shenshou-movie-regex-1 name)
      (setq video-info (plist-put video-info :moviekind "movie"))
      (setq video-info (plist-put video-info :query (shenshou-process-query name)))
      (setq video-info (plist-put video-info :movieyear (match-string 2 name)))
      (setq video-info (plist-put video-info :team (shenshou-trim (match-string 3 name)))))

     (t
      (setq video-info (plist-put video-info :moviekind "unknown"))
      (setq video-info (plist-put video-info :query name))))

    video-info))

(defun shenshou-params-from-videos (video-file)
  "Generate rpc parameters from VIDEO-FILE."
  (let* (video-info
         (rlt "")
         hash-and-size)

    (cond
     ((not (file-exists-p video-file))
      (message "Video file \"%s\" does not exist. It's skipped." video-file))

     ;; strict match, use file hash and file size to search subtitles
     ((and shenshou-strict-match-p
           (setq hash-and-size (shenshou-hash-and-size video-file)))
      (setq rlt (concat rlt
                        ;; video hash
                        (shenshou-format-struct-member "moviehash"
                                                       (plist-get hash-and-size :moviehash)))))

     ;; guess info from base file name
     ((setq video-info (shenshou-guess-video-info (file-name-base video-file)))

      (setq rlt (shenshou-format-struct-member "query"
                                               (plist-get video-info :query)))

      (when (string= (plist-get video-info :moviekind) "tv")
        (setq rlt (concat rlt
                          (shenshou-format-struct-member "episode_number"
                                                         (plist-get video-info :episode))
                          (shenshou-format-struct-member "season_number"
                                                         (plist-get video-info :season)))))))

    (when rlt
      (setq rlt (concat (shenshou-format-struct-member "languages" shenshou-language-code-list)
                        (string-trim rlt nil "&"))))
    (when shenshou-debug
      (message "shenshou-params-from-videos => rlt=%s" rlt))
    rlt))

(defun shenshou-sort-subtitles (subtitles video-name)
  "Sort SUBTITLES by measuring its string distance to VIDEO-NAME."
  (when shenshou-debug
    (message "shenshou-sort-subtitles called. subtitles=%s" subtitles))
  (when (> (length subtitles) 1)
    (setq subtitles
          (sort subtitles
                `(lambda (a b)
                   (< (string-distance (plist-get (cdr a) :moviereleasename) ,video-name)
                      (string-distance (plist-get (cdr b) :moviereleasename) ,video-name)))))
    (when shenshou-debug
      (message "sorted subtitles=%s" subtitles))
    subtitles))

(defun shenshou-filter-subtitles (candidates video-file filter-level)
  "Filter subtitle CANDIDATES with VIDEO-FILE and FILTER-LEVEL.
If FILTER-LEVEL is 0, all candidates are accepted.
If FILTER-LEVEL is 1, movie name should exist.
If FILTER-LEVEL is 2, do more checking on movie name."
  (let (subtitles
        files
        ok-p
        movie-release-name
        movie-year
        all-props
        sub
        movie-fuzzy-name
        lang
        subfilename
        video-info
        movie-year-match-p)
    (message "item=%s" (car candidates))
    (dolist (item candidates)

      (setq all-props (shenshou-json-value item 'attributes))
      (setq files (shenshou-json-value all-props 'files))
      ;; ;; OpenSubtitles hash function is not robust.
      ;; ;; Use the movie name to select the best candidate
      (setq movie-release-name
            (shenshou-json-value all-props 'release))
      (setq movie-year
            (shenshou-json-value (shenshou-json-value all-props 'feature-details) 'year))
      (setq video-info
            (shenshou-guess-video-info (downcase (file-name-base video-file))))
      (setq movie-fuzzy-name
            (replace-regexp-in-string "[.\[\] ()]+" ".*" (plist-get video-info :query)))
      (setq movie-year-match-p
            (or (not (plist-get video-info :movieyear))
                (string= movie-year (plist-get video-info :movieyear))))

      (cond
       ;; subtitle files to download must exist!
       ((eq (length files) 0)
        (setq ok-p nil))
       ((eq filter-level 0)
        (setq ok-p t))
       ((eq filter-level 1)
        (setq ok-p (and movie-release-name movie-year-match-p)))
       ((eq filter-level 2)
        (setq ok-p (and movie-release-name
                        (string-match (concat "^" movie-fuzzy-name)
                                      (downcase movie-release-name))
                        movie-year-match-p))))

      (when ok-p
        (setq sub nil)
        (setq sub (plist-put sub :moviereleasename movie-release-name))
        (setq sub (plist-put sub :sublanguageid (setq lang (shenshou-json-value all-props 'language))))
        (setq sub (plist-put sub :subfilename (setq subfilename (shenshou-json-value (aref files 0) 'file_name))))
        (setq sub (plist-put sub :file_id (shenshou-json-value (aref files 0) 'file_id)))
        (push (cons (format "%s(%s)" subfilename lang) sub) subtitles)))

  (when shenshou-debug
    (message "shenshou-filter-subtitles: candidates=%s video-file=%s filter-level=%s subtitles=%s"
             (length candidates)
             video-file
             filter-level
             (length subtitles)))

    subtitles))

(defun shenshou-search-subtitles (video-file)
  "Search subtitles of VIDEO-FILE."
  ;; @see https://opensubtitles.stoplight.io/docs/opensubtitles-api/e3750fd63a100-getting-started
  (let* ((params (shenshou-params-from-videos video-file))
         (resp (shenshou-restful-call "subtitles" nil params "GET" t))
         ;; array => list
         (candidates (mapcar 'identity (shenshou-json-value resp 'data)))
         subtitles)

    (when shenshou-debug
      (message "shenshou-search-subtitles to be called => video-file=%s params=%s resp=%s" video-file params resp))

    (when candidates
      (message "candidates=%s len=%s" candidates (length candidates))
      (cond
       ;; nothing can be done if there is no candidate
       ((eq (length candidates) 0))

       ;; donot filter candidates
       ((eq (length candidates) 1)
        (setq subtitles (shenshou-filter-subtitles candidates video-file 0)))

       ;; try most strict algorithm
       ((> (length (setq subtitles (shenshou-filter-subtitles candidates video-file 2)))
           0))

       ;; then go easy
       ((> (length (setq subtitles (shenshou-filter-subtitles candidates video-file 1)))
           0))

       (t
        (setq subtitles (shenshou-filter-subtitles candidates video-file 0)))))

    (shenshou-sort-subtitles subtitles (file-name-base video-file))))

(defun shenshou-default-directory (video-file)
  "Get VIDEO-FILE's directory."
  (if (eq major-mode 'dired-mode) default-directory
    (file-name-directory video-file)))

(defun shenshou-subtitle-file-name (video-file &optional subtitle)
  "Get file name of VIDEO-FILE's SUBTITLE."
  (when video-file
    (concat (file-name-base video-file)
            "."
            (if subtitle (file-name-extension subtitle)
              "srt"))))

(defun shenshou-download-link (file-id)
  "Get subtitle download link from FILE-ID."
  (when shenshou-debug
    (message "shenshou-download-link called. file-id=%s" file-id))
  (let* ((resp (shenshou-restful-call "download"
                                     (format "{\"file_id\": %s}" file-id)
                                     nil
                                     nil
                                     t)))
    (when shenshou-debug
      (message "shenshou-download-link returned. resp=%s" resp))
    (shenshou-json-value resp 'link)))

;;;###autoload
(defun shenshou-download-subtitle-internal (video-file)
  "Download subtitle of VIDEO-FILE."
  (let* (subtitles selected)

    (when shenshou-debug
      (message "shenshou-download-subtitle-internal called => %s" video-file))

    (unless (shenshou-token-invalid-p)
      (shenshou-login-now))

    ;; search subtitles
    (setq subtitles (shenshou-search-subtitles video-file))

    (cond
     ((> (length subtitles) 0)
      (when (setq selected (completing-read (format "Download subtitle of \"%s\": "
                                                    (file-name-nondirectory video-file))
                                            subtitles))
        (let* ((default-directory (shenshou-default-directory video-file))
               (sub (cdr (assoc selected subtitles)))
               (subfilename (plist-get sub :subfilename))
               (download-link (shenshou-download-link (plist-get sub :file_id)))
               (output-file (shenshou-subtitle-file-name video-file subfilename))
               (cmd (format "%s --silent --insecure %s %s > \"%s\" &"
                            shenshou-curl-program
                            shenshou-curl-extra-options
                            download-link
                            output-file)))
          (shell-command cmd))))

     (t
      (message "No subtitle is found for \"%s\""
               (file-name-nondirectory video-file))))))

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
(defun shenshou-download-subtitle ()
  "Download subtitles of video files.
If current buffer is Dired buffer, marked videos will be processed.
Or else user need specify the video to process."
  (interactive)
  (let* ((videos (shenshou-get-videos)))

    (cond
     ((> (length videos) 0)
      (message "Fetching subtitles of %d video(s) ..." (length videos))
      (dolist (v videos)
        (shenshou-download-subtitle-internal v)))

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
