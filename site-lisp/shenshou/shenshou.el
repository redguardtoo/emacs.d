;;; shenshou.el --- Download subtitles from opensubtitles.org -*- lexical-binding: t; -*-

;; Copyright (C) 2021-2022 Chen Bin
;;
;; Version: 0.0.3

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

;; This program downloads subtitles from http://opensubtitles.org
;;
;; Please note,
;; - You MUST register at http://opensubtitles.org first.
;;   That's required by opensubtitles' latest policy.
;;   See https://forum.opensubtitles.org/viewtopic.php?f=11&t=17110 for details.
;; - Command line program "curl" and "gzip" should exist.
;;   See `shenshou-curl-program' and `shenshou-gzip-program'.
;;
;; Usage,
;;   - Set `shenshou-login-user-name' and `shenshou-login-password'.
;;   - Run `shenshou-download-subtitle' in Dired buffer or anywhere.
;;   - Run `shenshou-logout-now' to logout.
;;
;;  Tips,
;;   - See `shenshou-curl-extra-options' on how to set SOCKS5 or HTTP proxy
;;   - This program gives you the freedom to select the right subtitle.

;;; Code:
;;

(require 'cl-lib)
(require 'xml)
(require 'dired)

(defgroup shenshou nil
  "Download subtitles from opensubtitles.org."
  :group 'tools)

(defcustom shenshou-curl-program "curl"
  "Name/path by which to invoke the curl program."
  :type 'string
  :group 'shenshou)

(defcustom shenshou-gzip-program "gzip"
  "Name/path by which to invoke the gzip program."
  :type 'string
  :group 'shenshou)

(defcustom shenshou-language-code-list "eng"
  "Language codes to search for, divided by ',' (e.g. 'chi,rus,spa,eng').
See https://en.wikipedia.org/wiki/List_of_ISO_639-2_codes for details."
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

(defcustom shenshou-token-update-interval 60
  "The interval (minutes) to update login token."
  :group 'shenshou
  :type 'integer)

(defvar shenshou-token nil
  "Token to access opensubtitles XML RPC.  It's internally used.")

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
  ;; @see https://trac.opensubtitles.org/projects/opensubtitles/wiki/HashSourceCodes
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

(defun shenshou-xml-rpc-post-data (method &optional params)
  "Create post data from METHOD and PARAMS."
  (let* ((rlt (concat "<?xml version='1.0' encoding='UTF-8'?>"
                      "<methodCall><methodName>"
                      method
                      "</methodName>"
                      "<params>"
                      params
                      "</params>"
                      "</methodCall>")))
    (when shenshou-debug
      (message "shenshou-xml-rpc-post-data called => %s" rlt))
    rlt))

(defun shenshou-xml-node-children (node xpath)
  "Get NODE's children matching XPATH."
  (let (rlt
        children)
    (cond
     ((null xpath)
      (setq rlt (xml-node-children node)))

     ((eq 1 (length xpath))
      (setq rlt (xml-get-children node (car xpath))))

     (t
      (setq children (xml-get-children node (car xpath)))
      (dolist (c children)
        (setq rlt (append rlt (shenshou-xml-node-children c (cdr xpath)))))))

    rlt))

(defun shenshou-xml-get-value-by-name (node-list name-value)
  "Get value from NODE-LIST by NAME-VALUE."
  (let* ((member-node (cl-find-if (lambda (m)
                                    (let* ((name (car (xml-get-children m 'name))))
                                      (equal (nth 2 name) name-value)))
                                  node-list)))
    (nth 2 (car (shenshou-xml-node-children member-node '(value string))))))

(defun shenshou-extract-xml-tree (cmd-output)
  "Extract xml tree from CMD-OUTPUT."
  (let* ((xml-tree (car (with-temp-buffer
                          (insert cmd-output)
                          (xml-parse-region)))))
    xml-tree))

(defun shenshou-xml-rpc-call (post-data &optional raw-response-p)
  "Call remote api with POST-DATA.  If RAW-RESPONSE-P is t, return raw response."
  (let* ((cmd (concat shenshou-curl-program
                      " --silent -b --insecure https://api.opensubtitles.org:443/xml-rpc "
                      shenshou-curl-extra-options
                      " -H \"Content-Type: text/xml\" "
                      (and post-data (format " -d \"%s\" " post-data))))
         (cmd-output (shell-command-to-string cmd))
         xml-tree)
    (when shenshou-debug
      (message "shenshou-xml-rpc-call called => post-data=%s cmd=%s cmd-output=%s" post-data cmd cmd-output))

    (cond
     ((string-match "Your IP.*[^0-9.]\\([0-9.]+\\)<" cmd-output)
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
        (message "Error: Report IP \"%s\" and Cloudflare Ray ID \"%s\" at forum.opensubtitles.org to solve the problem!"
                 ip
                 id)))

     (t
      (setq xml-tree (shenshou-extract-xml-tree cmd-output))))

    (if raw-response-p cmd-output xml-tree)))

(defun shenshou-format-param (param)
  "Format PARAM."
  (format "<param><value>%s</value></param>" param))

(defun shenshou-format-struct-member (name value)
  "Format a struct member with its NAME and VALUE."
  (format "<member><name>%s</name><value>%s</value></member>" name value))

(defun shenshou-login-token-valid-p ()
  "Validate the login token."
  (and (null shenshou-token)
       (> (- (float-time (current-time)) (float-time (cdr shenshou-token)))
          (* shenshou-token-update-interval 60))))

;;;###autoload
(defun shenshou-login-now ()
  "Login remote opensubtitles server and set `shenshou-token'."
  (interactive)
  (cond
   ((or (not (executable-find shenshou-curl-program))
        (not (executable-find shenshou-gzip-program)))
    (message "You need install \"curl\" and \"gzip\" first."))

   ((null shenshou-login-user-name)
    (message "Please set `shenshou-login-user-name' first.  Only logged-in user can download the subtitles."))

   (t
    (unless shenshou-login-password
      (setq shenshou-login-password
            (read-passwd "Please input password for opensubtitles: ")))

    (when shenshou-login-password
      (let* ((post-data (shenshou-xml-rpc-post-data
                         "LogIn"
                         (mapconcat (lambda (p)
                                      (shenshou-format-param (format "<string>%s</string>" p)))
                                    (list shenshou-login-user-name
                                          shenshou-login-password
                                          "en"
                                          "shenshou")
                                    "")))
             (xml-tree (shenshou-xml-rpc-call post-data))
             response-props
             token)
        (when xml-tree
          (setq response-props (shenshou-xml-node-children xml-tree '(params param value struct member)))
          ;; @see https://trac.opensubtitles.org/projects/opensubtitles/wiki/XmlRpcIntro
          (when (setq token (shenshou-xml-get-value-by-name response-props "token"))
            (setq shenshou-token (cons token (current-time))))))))))

;;;###autoload
(defun shenshou-logout-now ()
  "Logout and reset `shenshou-token'."
  (interactive)
  (setq shenshou-token nil))

(defun shenshou-process-query (name)
  "Get query from video file NAME."
  (let ((query (match-string 1 name)))
    (replace-regexp-in-string " *([^)]*$" "" query)))

(defun shenshou-guess-video-info (name)
  "Guess information from NAME of video."
  (let* (video-info)
    (cond
     ((string-match shenshou-tvshow-regex-1 name)
      (setq video-info (plist-put video-info :moviekind "tv"))
      (setq video-info (plist-put video-info :query (shenshou-process-query name)))
      (setq video-info (plist-put video-info :season (match-string 2 name)))
      (setq video-info (plist-put video-info :episode (match-string 3 name)))
      (setq video-info (plist-put video-info :team (match-string 4 name))))

     ((string-match shenshou-tvshow-regex-2 name)
      (setq video-info (plist-put video-info :moviekind "tv"))
      (setq video-info (plist-put video-info :query (shenshou-process-query name)))
      (setq video-info (plist-put video-info :season (match-string 2 name)))
      (setq video-info (plist-put video-info :episode (match-string 3 name)))
      (setq video-info (plist-put video-info :team (match-string 4 name))))

     ((string-match shenshou-movie-regex-1 name)
      (setq video-info (plist-put video-info :moviekind "movie"))
      (setq video-info (plist-put video-info :query (shenshou-process-query name)))
      (setq video-info (plist-put video-info :movieyear (match-string 2 name)))
      (setq video-info (plist-put video-info :team (match-string 3 name))))

     (t
      (setq video-info (plist-put video-info :moviekind "unknown"))
      (setq video-info (plist-put video-info :query name))))

    video-info))

(defun shenshou-params-from-videos (video-file)
  "Generate rpc parameters from VIDEO-FILE."
  (let* (rlt video-info extra hash-and-size)

    (cond
     ((not (file-exists-p video-file))
      (message "Video file \"%s\" does not exist. It's skipped." video-file))

     ;; strict match, use file hash and file size to search subtitles
     ((and shenshou-strict-match-p
           (setq hash-and-size (shenshou-hash-and-size video-file)))
      (setq extra (concat extra
                          ;; video hash
                          (shenshou-format-struct-member "moviehash"
                                                         (format "<string>%s</string>"
                                                                 (plist-get hash-and-size :moviehash)))
                          ;; video size
                          (shenshou-format-struct-member "moviebytesize"
                                                         (format "<double>%s</double>"
                                                                 (plist-get hash-and-size :moviebytesize))))))

     ;; guess info from base file name
     ((setq video-info (shenshou-guess-video-info (file-name-base video-file)))

      (setq extra (shenshou-format-struct-member "query"
                                                 (format "<string>%s</string>"
                                                         (plist-get video-info :query))))

      (when (string= (plist-get video-info :moviekind) "tv")
        (setq extra (concat extra
                            (shenshou-format-struct-member "episode"
                                                           (format "<double>%s</double>"
                                                                   (plist-get video-info :episode)))
                            (shenshou-format-struct-member "season"
                                                           (format "<double>%s</double>"
                                                                   (plist-get video-info :season))))))))

    (when extra
      (setq rlt (concat rlt
                        "<data><value><struct>"
                        ;; language id
                        (shenshou-format-struct-member "sublanguageid"
                                                       (format "<string>%s</string>"
                                                               shenshou-language-code-list))
                        extra
                        "</struct></value></data>")))
    (shenshou-format-param (concat "<array>" rlt "</array>"))))

(defun shenshou-sort-subtitles (subtitles video-name)
  "Sort SUBTITLES by measuring its string distance to VIDEO-NAME."
  (when (> (length subtitles) 1)
    (setq subtitles
          (sort subtitles
                `(lambda (a b)
                   (< (string-distance (plist-get (cdr a) :moviereleasename) ,video-name)
                      (string-distance (plist-get (cdr b) :moviereleasename) ,video-name)))))
    (when shenshou-debug
      (message "shenshou-sort-subtitles called. subtitles=%s" subtitles))
    subtitles))

(defun shenshou-filter-subtitles (candidates video-file filter-level)
  "Filter subtitle CANDIDATES with VIDEO-FILE and FILTER-LEVEL.
If FILTER-LEVEL is 0, all candidates are accepted.
If FILTER-LEVEL is 1, movie name should exist.
If FILTER-LEVEL is 2, do more checking on movie name."

  (let (subtitles
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
    (dolist (item candidates)
      (setq all-props (shenshou-xml-node-children item '(member)))
      ;; OpenSubtitles hash function is not robust.
      ;; Use the MovieReleaseName to select the best candidate
      (setq movie-release-name
            (shenshou-xml-get-value-by-name all-props "MovieReleaseName"))
      (setq movie-year
            (shenshou-xml-get-value-by-name all-props "MovieYear"))
      (setq video-info
            (shenshou-guess-video-info (downcase (file-name-base video-file))))
      (setq movie-fuzzy-name
            (replace-regexp-in-string "[.\[\] ()]+" ".*" (plist-get video-info :query)))
      (setq movie-year-match-p
            (or (not (plist-get video-info :movieyear))
                (string= movie-year (plist-get video-info :movieyear))))
      (cond
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
        (setq sub (plist-put sub :subfilename (setq subfilename (shenshou-xml-get-value-by-name all-props "SubFileName"))))
        (setq sub (plist-put sub :sublanguageid (setq lang (shenshou-xml-get-value-by-name all-props "SubLanguageID"))))
        (setq sub (plist-put sub :subdownloadlink (shenshou-xml-get-value-by-name all-props "SubDownloadLink")))
        (setq sub (plist-put sub :moviehash (shenshou-xml-get-value-by-name all-props "MovieHash")))
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
  ;; @see https://trac.opensubtitles.org/projects/opensubtitles/wiki/XmlRpcSearchSubtitles
  (let* ((post-data (shenshou-xml-rpc-post-data "SearchSubtitles"
                                                (concat (shenshou-format-param (format "<string>%s</string>" (car shenshou-token)))
                                                        (shenshou-params-from-videos video-file))))
         (xml-tree (shenshou-xml-rpc-call post-data))
         candidates
         subtitles)

    (when shenshou-debug
      (message "shenshou-search-subtitles to be called => video-file=%s post-data=%s" video-file post-data))

    (when xml-tree
      (setq candidates
            (shenshou-xml-node-children xml-tree
                                        '(params param value struct member value array data value struct)))
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

;;;###autoload
(defun shenshou-download-subtitle-internal (video-file)
  "Download subtitle of VIDEO-FILE."
  ;; @see http://blog.likewise.org/2013/09/using-curl-to-access-bugzillas-xml-rpc-api/
  (let* (subtitles selected token-p)

    (when shenshou-debug
      (message "shenshou-download-subtitle-internal called => %s" video-file))

    (setq token-p t)
    (unless (shenshou-login-token-valid-p)
      (setq token-p (shenshou-login-now)))

    (when token-p
      ;; search subtitles
      (setq subtitles (shenshou-search-subtitles video-file))

      (cond
       ((> (length subtitles) 0)
        (when (setq selected (completing-read (format "Download subtitle of \"%s\": "
                                                      (file-name-nondirectory video-file))
                                              subtitles))
          (let* ((default-directory (if (eq major-mode 'dired-mode) default-directory
                                      (file-name-directory video-file)))
                 (sub (cdr (assoc selected subtitles)))
                 (subfilename (plist-get sub :subfilename))
                 (download-link (plist-get sub :subdownloadlink))
                 (output-file (concat (file-name-base video-file)
                                      "."
                                      (if subfilename (file-name-extension subfilename)
                                        "srt")))
                 (cmd (format "%s --silent -b --insecure %s %s | %s -q -d -c > \"%s\" &"
                              shenshou-curl-program
                              shenshou-curl-extra-options
                              download-link
                              shenshou-gzip-program
                              output-file)))
            (shell-command cmd))))

       (t
        (message "No subtitle is found for \"%s\""
                 (file-name-nondirectory video-file)))))))

;;;###autoload
(defun shenshou-download-subtitle ()
  "Download subtitles of video files.
If current buffer is Dired buffer, marked videos will be processed.
Or else user need specify the video to process."
  (interactive)
  (let* (file
         (videos (cond
                  ((eq major-mode 'dired-mode)
                   (dired-get-marked-files t current-prefix-arg))

                  (t
                   (when (setq file (read-file-name "Please select a video: "))
                     (list file))))))

    ;; filter video files by their extensions
    (setq videos
          (delq nil
                (mapcar (lambda (f)
                          (and (member (file-name-extension f)
                                       shenshou-supported-video-format)
                               f))
                        videos)))

    (cond
     ((> (length videos) 0)
      (message "Fetching subtitles of %d video(s) ..." (length videos))
      (dolist (v videos)
        (shenshou-download-subtitle-internal v)))

     (t
      (message "No video files are selected.")))))

(provide 'shenshou)
;;; shenshou.el ends here
