;;; mybigword.el --- Vocabulary builder using Zipf to extract English big words -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2020-2023 Chen Bin <chenbin DOT sh AT gmail.com>
;;
;; Author: Chen Bin <chenbin DOT sh AT gmail.com>
;; URL: https://github.com/redguardtoo/mybigword
;; Version: 0.3.0
;; Keywords: convenience
;; Package-Requires: ((emacs "26.1") (avy "0.5.0"))
;;
;; This file is not part of GNU Emacs.

;;; License:
;;
;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This program extract big words from text.
;; The words whose Zipf frequency less than `mybigword-upper-limit' are
;; big words.
;;
;; Zipf scale was proposed by Marc Brysbaert, who created the SUBTLEX lists.
;; Zipf frequency of a word is the base-10 logarithm of the number of times it
;; appears per billion words.
;;
;; A word with Zipf value 6 appears once per thousand words,for example, and a
;; word with Zipf value 3 appears once per million words.
;;
;; Reasonable Zipf values are between 0 and 8, but the minimum Zipf value
;; appearing here is 1.0.
;;
;; We use 0 as the default Zipf value for words that do not appear in the given
;; word list,although it should mean one occurrence per billion words."
;;
;; Thanks to https://github.com/LuminosoInsight/wordfreq for providing the data.
;;
;; Usage,
;;
;;   Run `mybigword-show-big-words-from-file'
;;   Run `mybigword-show-big-words-from-current-buffer'
;;   Run `mybigword-big-words-in-current-window'
;;
;;
;; Customize `mybigword-excluded-words' or `mybigword-personal-excluded-words' to
;; exclude words.
;;
;; Tips,
;;
;;   1. Customize `mybigword-default-format-function' to format the word for display.
;;   If it's `mybigword-format-with-dictionary', the `mybigword-word-definition-function',
;;   whose default value is `dictionary-definition', is used to find the definitions of
;;   all big words.
;;
;;   Sample to display the dictionary definitions of big words:
;;
;;     (let* ((mybigword-default-format-function 'mybigword-format-with-dictionary))
;;       (mybigword-show-big-words-from-current-buffer))
;;
;;   You can also set `mybigword-default-format-header-function' to add a header before
;;   displaying words.
;;
;;   Customize `mybigword-hide-word-function' to hide word for display
;;
;;
;;   2. Parse the *.srt to play the video containing the word in org file
;;   Make sure the org tree node has the property SRT_PATH.
;;   Mplayer is required to play the video.  See `mybigword-mplayer-program' for details.
;;
;;   Sample of org file:
;;    * Star Trek s06e26
;;      :PROPERTIES:
;;      :SRT_PATH: ~/Star.Trek.DS9-s06e26.Tears.of.the.Prophets.srt
;;      :END:
;;    telepathic egotist
;;
;;   Move focus over the word like "egotist".  Run "M-x mybigword-play-video-of-word-at-point".
;;   Then mplayer plays the corresponding video at the time the word is spoken.
;;   If video is missing, the mp3 with similar name is played.
;;   See `mybigword-video2mp3' on how to generate mp3 from video files.
;;
;;   Please note `mybigword-play-video-of-word-at-point' can be used in other major modes.
;;   See `mybigword-default-media-info-function' for details.
;;
;;
;;   3. Use `mybigword-pronounce-word' to pronounce the word at point.
;;   The word's audio is downloaded from https://dictionary.cambridge.org
;;   The audio download url could be customized in `mybigword-default-audio-url-function'.
;;
;;   4. Use `mybigword-show-image-of-word' to show images of the word at point
;;   in external browser.  Please note `browse-url-generic' is used in this
;;   command.
;;

;;; Code:

(require 'find-lisp)
(require 'cl-lib)
(require 'url)
(require 'browse-url)
(require 'dictionary)
(require 'avy)

(defgroup mybigword nil
  "Filter the words by the frequency usage of each word."
  :group 'tools)

(defcustom mybigword-data-file nil
  "The word frequency file whose lines are sorted alphabetically.
Each line has two fields.  The first field is the lowercase word.
The second field is the frequency usage of the word.
If nil, the default data is used."
  :group 'mybigword
  :type 'string)

(defcustom mybigword-mplayer-program "mplayer"
  "Mplayer program."
  :group 'mybigword
  :type 'string)

(defcustom mybigword-video-file-regexp "\\.\\(mp4\\|avi\\|mkv\\)$"
  "Regular expression to match video file names."
  :group 'mybigword
  :type 'string)

(defcustom mybigword-audio-file-regexp "\\.\\(mp3\\|wav\\|flac\\)$"
  "Regular expression to match audio file names."
  :group 'mybigword
  :type 'string)

(defcustom mybigword-download-directory nil
  "Directory to store downloaded files.
If it's nil, ~/.emacs.d/mybigword is is used."
  :group 'mybigword
  :type 'string)

(defcustom mybigword-mplayer-rewind-time 5
  "Rewind a few seconds when mplayer playing video."
  :group 'mybigword
  :type 'number)

(defcustom mybigword-select-visible-word-function
  'mybigword-select-visible-word-default-function
  "Function to execute after visible word is selected."
  :group 'mybigword
  :type 'function)

(defcustom mybigword-show-image-function
  'mybigword-show-image-default-function
  "Function to show image of word."
  :group 'mybigword
  :type 'function)

(defcustom mybigword-excluded-words
  '("anybody"
    "anymore"
    "anyone"
    "anyway"
    "aren"
    "brien"
    "couldn"
    "dear"
    "didn"
    "doesn"
    "ever"
    "everybody"
    "glad"
    "guess"
    "hasn"
    "hate"
    "haven"
    "hello"
    "idiot"
    "listen"
    "maybe"
    "okay"
    "our"
    "ours"
    "ourselves"
    "shouldn"
    "sorry"
    "thank"
    "theirs"
    "then"
    "wasn"
    "weren"
    "worry"
    "wouldn"
    "yourself"
    "yourselves")
  "The words being excluded."
  :group 'mybigword
  :type '(repeat string))

(defcustom mybigword-personal-excluded-words nil
  "The personal words being excluded."
  :group 'mybigword
  :type '(repeat string))

(defcustom mybigword-default-format-header-function
  (lambda (file) (ignore file) "")
  "The function to format the header before displaying big word list."
  :group 'mybigword
  :type 'function)

(defcustom mybigword-default-format-function
  'mybigword-format-word
  "The function to format big word before displaying it."
  :group 'mybigword
  :type 'function)

(defcustom mybigword-default-format-function
  'mybigword-format-word
  "The function to format big word before displaying it."
  :group 'mybigword
  :type 'function)

(defcustom mybigword-default-media-info-function
  'mybigword-org-media-info
  "The function to play the video of the big word."
  :group 'mybigword
  :type 'function)

(defcustom mybigword-default-audio-url-function
  'mybigword-cambridge-mp3-url
  "The function to get audio download url of given word."
  :group 'mybigword
  :type 'function)

(defcustom mybigword-upper-limit 4
  "The word whose zipf frequency is below this limit is big word."
  :group 'mybigword
  :type 'float)

(defcustom mybigword-hide-unknown-word t
  "Hide unknown word."
  :group 'mybigword
  :type 'boolean)

(defcustom mybigword-hide-word-function nil
  "The function to hide a word which has one parameter \" word\"."
  :group 'mybigword
  :type 'function)

(defcustom mybigword-word-definition-function 'dictionary-definition
  "The function to show word's definition.  It has one parameter \" word\"."
  :group 'mybigword
  :type 'function)

(defcustom mybigword-find-file-regexp "\\.\\(mp4\\|avi\\|mpeg\\|mkv\\)$"
  "The file found in `wucuo-spell-check-directory' matches this regex."
  :type 'string
  :group 'mybigword)

;; internal variable
(defvar mybigword-cache nil
  "Cached frequency data.")

(defvar mybigword-debug nil
  "For debug only.")

(defun mybigword-read-file (file)
  "Read FILE's content and return it."
  (with-temp-buffer
    (insert-file-contents file)
    (buffer-string)))

(declare-function dictionary-definition "dictionary")
(declare-function outline-up-heading "outline")
(declare-function org-entry-get "org")

;;;###autoload
(defun mybigword-update-cache ()
  "Update cache using `mybigword-data-file'."
  (let* ((file (or mybigword-data-file
                   (concat (file-name-directory
                            (locate-library "mybigword.el"))
                           "eng.zipf")))
         (i 0)
         (beg 0)
         end
         raw-content
         content)

    (if mybigword-debug (message "mybigword-update-cache called file=%s" file))

    (when (file-exists-p file)
      ;; initialize hash table whose key is from a...z
      (setq content (make-hash-table :test #'equal))

      ;; read content of file
      (setq raw-content (mybigword-read-file file))
      (setq i 1)
      (while (< i 26)
        (let* ((ch (+ ?a i)))
          (setq end (string-match (format "^%c" ch) raw-content beg))
          (when (and beg end (< beg end))
            (puthash (1- ch)
                     (substring-no-properties raw-content beg end)
                     content)
            (setq beg end)))
        (setq i (1+ i)))
      ;; last missing piece
      (puthash ?z
               (substring-no-properties raw-content beg (length raw-content))
               content)
      (setq mybigword-cache (list :content content
                                  :file file
                                  :timestamp (float-time (current-time))
                                  :filesize (nth 7 (file-attributes file))))
      (message "Frequency file %s is loaded." file))))


(defmacro mybigword-extract-freq (word str)
  "Extract WORD's usage frequency from STR."
  `(and (string-match (format "^%s \\([0-9.]*\\)$" ,word) ,str)
        (string-to-number (match-string 1 ,str))))

(defun mybigword-guess-original-tense (raw-word)
  "Convert RAW-WORD to the word to look up."
  (let* ((rlt raw-word))
    (cond
     ((string-match "\\([a-z]+\\)i\\(ed\\|ly\\|es\\)$" raw-word)
      (setq rlt (concat (match-string 1 raw-word) "y")))

     ((string-match "\\([a-z]+\\)\\(t\\|r\\|p\\|n\\)\\{2\\}\\(ed\\|ing\\)$" raw-word)
      (setq rlt (concat (match-string 1 raw-word) (match-string 2 raw-word))))

     ((string-match "\\([a-z]+\\)\\(ly\\|s\\|ing\\|ingly\\)$" raw-word)
      (setq rlt (match-string 1 raw-word)))

     ((string-match "\\([a-z]+\\)\\(ed\\|es\\)$" raw-word)
      (setq rlt (match-string 1 raw-word))))

    (when mybigword-debug
      (message "mybigword-guess-original-tense called => %s %s" raw-word rlt))

    rlt))

(defun mybigword-guess-original-tense-again (raw-word)
  "Convert RAW-WORD to the word to look up."
  (let* ((rlt raw-word))
    (cond
     ((string-match "\\([a-z]+e\\)\\(d\\|s\\)$" raw-word)
      (setq rlt (match-string 1 raw-word))))
    rlt))

(defun mybigword-format-word (word zipf)
  "Format WORD and ZIPF."
  (format "%s %s\n" word zipf))

(defun mybigword-format-with-dictionary (word zipf)
  "Format WORD and ZIPF by looking up in dictionary."
  (ignore zipf)
  (condition-case nil
      (concat (funcall mybigword-word-definition-function word) "\n\n\n")
    (error nil)))

(defun mybigword-show-big-words-from-content (content file)
  "Show words whose zipf frequency is below `mybigword-upper-limit' in CONTENT.
FILE is the file path."
  (unless mybigword-cache (mybigword-update-cache))
  (let* ((big-words (mybigword-extract-words content)))
    (cond
     (big-words
      ;; sort windows
      (setq big-words (sort big-words (lambda (a b) (< (cdr a) (cdr b)))))
      (switch-to-buffer-other-window "*mybigword-list*")
      (erase-buffer)
      (insert (funcall mybigword-default-format-header-function file))
      (dolist (bw big-words)
        (let* (str
               (word (car bw))
               (zipf (cdr bw)))
          (unless (or (and mybigword-hide-unknown-word (eq zipf -1))
                      (and mybigword-hide-word-function
                           (not (funcall mybigword-hide-word-function word))))
            (when (setq str (funcall mybigword-default-format-function word zipf))
              (insert str)))))
      (goto-char (point-min)))
     (t
      (message "No big word is found!")))))

(defmacro mybigword-push-cand (word dict cands)
  "Get WORD and its frequency from DICT.  Push them into CANDS."
  `(push (cons ,word (mybigword-extract-freq ,word ,dict)) ,cands))

(defmacro mybigword-push-word (word frequency result)
  "Push WORD FREQUENCY into RESULT."
  `(unless (or (member ,word mybigword-excluded-words)
               (member ,word mybigword-personal-excluded-words))
     (push (cons ,word ,frequency) ,result)))

;;;###autoload
(defun mybigword-extract-words (text)
  "Words whose usage frequency is below `mybigword-upper-limit' in TEXT."
  (let* ((raw-words (mapcar #'downcase (split-string text "[^A-Za-z]+")))
         (words (delq nil (delete-dups (sort raw-words #'string<))))
         h str
         rlt)

    (when mybigword-debug
      (message "mybigword-extract-words called. words=%s" words)
      (message "mybigword-cache file=%s size=%s"
               (plist-get mybigword-cache :file)
               (plist-get mybigword-cache :filesize)))

    (when mybigword-cache
      (setq h (plist-get mybigword-cache :content))
      (dolist (word words)
        (when (and (> (length word) 3)
                   (setq str (gethash (elt word 0) h)))
          (let* (cands (max-item '(nil . 0)))
            (mybigword-push-cand word str cands)
            (mybigword-push-cand (mybigword-guess-original-tense word) str cands)
            (mybigword-push-cand (mybigword-guess-original-tense-again word) str cands)

            ;; find the one with highest zipf frequency
            (dolist (c cands)
              (let* ((freq (cdr c)))
                (when (and freq (> freq (cdr max-item)))
                  (setq max-item c))))
            (cond
             ((car max-item)
              (when (< (cdr max-item) mybigword-upper-limit)
                (mybigword-push-word (car max-item) (cdr max-item) rlt)))
             (t
              ;; word is not found in dictionary
              (mybigword-push-word word -1 rlt)))))))
    ;; need remove duplicates
    ;; for example, "notifies" and "notify" is actually one word
    (setq rlt (delq nil (delete-dups rlt)))
    rlt))

;;;###autoload
(defun mybigword-show-big-words-from-current-buffer ()
  "Show big words in current buffer."
  (interactive)
  (mybigword-show-big-words-from-content (buffer-string) buffer-file-name))

;;;###autoload
(defun mybigword-show-big-words-from-file (file)
  "Show bug words from FILE."
  (interactive (list (read-file-name "Find file: " nil default-directory t)))
  (when (and file (file-exists-p file))
    (unless mybigword-cache (mybigword-update-cache))
    (let* ((content (mybigword-read-file file)))
      (mybigword-show-big-words-from-content content file))))

(defun mybigword-media-file-path (srt-path regexp)
  "Return video/audio path similar to SRT-PATH and whose file name match REGEXP."
  (let* ((rlt '(nil . 99999))
         (dir (file-name-directory srt-path))
         (video-files (directory-files dir t regexp))
         (base (file-name-base srt-path))
         (distance-fn (if (fboundp 'string-distance) 'string-distance
                        'org-babel-edit-distance)))
    (dolist (v video-files)
      (let* ((distance (funcall distance-fn (file-name-base v) base)))
        (when (< distance (cdr rlt))
          (setq rlt (cons v distance)))))
    (car rlt)))

(defun mybigword-mplayer-start-time (chunks word)
  "Get video start time from CHUNKS and WORD."
  (let* ((matched (cl-find-if (lambda (c) (string-match (regexp-quote word) c))
                              chunks))
         (regexp "^\\([0-9]+:[0-9]+:[0-9]+\\),[0-9]+ +-->"))
    (when (and matched (string-match regexp matched))
      (match-string 1 matched))))

(defun mybigword-adjust-start-time (start-time)
  "Rewind back START-TIME a few seconds."
  (let* ((a (mapcar #'string-to-number (split-string start-time ":")))
         h m s)
    (setq s (- (nth 2 a) mybigword-mplayer-rewind-time))
    (setq m (nth 1 a))
    (setq h (nth 0 a))
    ;; adjust second
    (when (< s 0)
      (setq s (+ 60 s))
      (setq m (1- m)))
    ;; adjust minute
    (when (< m 0)
      (setq m (+ 60 m))
      (setq h (1- h)))
    ;; adjust hour
    (when (< h 0)
      (setq s 0)
      (setq m 0))
    (format "%02d:%02d:%02d" h m s)))


(defun mybigword-async-shell-command (command)
  "Execute string COMMAND asynchronously."
  (let* ((proc (start-process "MyBigWord"
                              nil
                              shell-file-name
                              shell-command-switch
                              command)))
    (set-process-sentinel proc 'ignore)))

(defun mybigword-run-mplayer (start-time video-path &optional play-mp3-p)
  "Use START-TIME and VIDEO-PATH to run mplayer.
If PLAY-MP3-P is t, mp3 is played."
  (when start-time
    (let* ((default-directory (file-name-directory video-path))
           (cmd (format "%s -ss %s -osdlevel 2 \"%s\""
                        mybigword-mplayer-program
                        (mybigword-adjust-start-time start-time)
                        (file-name-nondirectory video-path))))
      (cond
       (play-mp3-p
        ;; open a buffer to accept key binding
        (shell-command (concat cmd " &")))
       (t
        (mybigword-async-shell-command cmd))))))

(defun mybigword-org-media-info (word)
  "Find the video information of the WORD in `org-mode'.
The information is in current org node's \"SRT_PATH\" property."
  (let* (rlt srt-path)
    (cond
     ((not (eq major-mode 'org-mode))
      (message "This function can only be used in `org-mode'."))

     ((not (setq srt-path (save-excursion (condition-case nil
                                              (outline-up-heading 1)
                                            (error nil))
                                          (org-entry-get (point) "SRT_PATH"))))
      (message "Current org node does not have SRC_PATH property"))

     ((not (file-exists-p srt-path))
      (message "File %s does not exist." srt-path))

     (t
      (let* ((chunks (split-string (mybigword-read-file srt-path)
                                   "\n\n+[0-9]+ *\n"))
             (start-time (mybigword-mplayer-start-time chunks word)))
        (when start-time
          (setq rlt (list :video-path (mybigword-media-file-path srt-path mybigword-video-file-regexp)
                          :audio-path (mybigword-media-file-path srt-path mybigword-audio-file-regexp)
                          :start-time start-time))))))
    rlt))

(defun mybigword--word-at-point ()
  "Get word at point or ask user to input word."
  (let* ((word (and (region-active-p)
                    (buffer-substring (region-beginning) (region-end)))))
    (unless word
      (cond
       ((memq major-mode '(pdf-view-mode))
        (setq word (read-string "Please input a word: ")))

       ((memq major-mode '(nov-mode))
        (save-excursion
          ;; go to end of word to workaround `nov-mode' bug
          (forward-word)
          (forward-char -1)
          ;; word at point
          (setq word (thing-at-point 'word))))

       (t
        (setq word (thing-at-point 'word)))))
    word))

(defun mybigword-mp3-path (file)
  "Get mp3 file with similar name to FILE."
  (and file
       (concat (file-name-directory file)
               (file-name-base file)
               ".mp3")))

;;;###autoload
(defun mybigword-play-video-of-word-at-point ()
  "Search video's subtitle (*.srt) and play the video of the word.
The video file should be in the same directory of subtitle.
Its file name should be similar to the subtitle's file name.
If video file is missing, the mp3 with similar name is played.
The word is either the word at point, or selected string or string from input."
  (interactive)
  (let* ((word (or (mybigword--word-at-point)
                   (read-string "Please input a word: "))))
    (when word
      (let* ((info (funcall mybigword-default-media-info-function word))
             (video (plist-get info :video-path))
             (audio (plist-get info :audio-path)))
        (cond
         ;; try to play video first
         ((and video (file-exists-p video))
          (mybigword-run-mplayer (plist-get info :start-time) video))

         ;; try to play audio
         ((and audio (file-exists-p audio))
          (mybigword-run-mplayer (plist-get info :start-time) audio t)))))))

(defun mybigword-cambridge-mp3-url (word)
  "Get URL to download mp3 of WORD."
  (let* ((url (concat "https://dictionary.cambridge.org/pronunciation/english/" word))
         (html-text (with-current-buffer
                        (url-retrieve-synchronously url) (buffer-string)))
         (regexp "<source type=\"audio/mpeg\" src=\"\\([^\"]+\\)"))
    (when (and html-text
               (not (string-match "404" html-text))
               (string-match regexp html-text))
      (concat "https://dictionary.cambridge.org" (match-string 1 html-text)))))

(defun mybigword-play-mp3-program ()
  "Program to play mp3."
  (cond
   ;; macOS
   ((eq system-type 'darwin)
    "afplay")
   ;; Windows
   ((eq system-type 'windows-nt)
    "start")
   ;; Use mplayer
   (t
    mybigword-mplayer-program)))

(defun mybigword-get-download-directory ()
  "Get download directory."
  (cond
   (mybigword-download-directory
    (file-name-as-directory mybigword-download-directory))
   (t
    (let* ((dir (concat (file-name-as-directory user-emacs-directory) "mybigword")))
      (unless (file-exists-p dir) (make-directory dir t))
      (file-name-as-directory dir)))))

;;;###autoload
(defun mybigword-pronounce-word-internal (word)
  "Use cambridge dictionary to pronounce WORD."
  (setq word (downcase word))
  (let* ((cached-mp3 (file-truename (concat (mybigword-get-download-directory) word ".mp3")))
         (player (mybigword-play-mp3-program))
         online-mp3)
    (cond
     ((file-exists-p cached-mp3)
      (mybigword-async-shell-command (format "%s %s" player cached-mp3)))
     ((setq online-mp3 (funcall mybigword-default-audio-url-function word))
      (url-copy-file online-mp3 cached-mp3)
      (mybigword-async-shell-command (format "%s %s" player cached-mp3)))
     (t
      (message "Sorry, can't find pronunciation for \"%s\"" word)))))

;;;###autoload
(defun mybigword-pronounce-word (&optional input-p)
  "Pronounce word.  If INPUT-P is t, user need input word."
  (interactive "P")
  (let* ((word (if input-p (read-string "Word: ") (mybigword--word-at-point))))
    (when word
      (mybigword-pronounce-word-internal word))))

(defun mybigword-show-image-default-function (word)
  "Default function to show image of WORD .
Please note `browse-url-generic' is used to open external browser."
  (when word
    (browse-url-generic (format "https://www.bing.com/images/search?q=%s"
                                (replace-regexp-in-string " " "%20" word)))))

;;;###autoload
(defun mybigword-show-image-of-word ()
  "Show image of word."
  (interactive)
  (funcall mybigword-show-image-function (mybigword--word-at-point)))

(defun mybigword-original-word (word)
  "Get WORD in its original tense."
  (unless mybigword-cache (mybigword-update-cache))
  (setq word (downcase word))
  (when mybigword-debug
    (message "mybigword-original-word => %s" word))
  (when (> (length word) 3)
    (let* (cands
           len
           (h (plist-get mybigword-cache :content))
           (str (gethash (elt word 0) h)))

      (mybigword-push-cand (mybigword-guess-original-tense word) str cands)
      (mybigword-push-cand (mybigword-guess-original-tense-again word) str cands)
      (cl-delete-if (lambda (e) (null (cdr e))) cands)
      (setq len (length cands))

      (cond
       ((eq len 0))

       ((or (eq len 1)
            (< (length (car (nth 0 cands))) (length (car (nth 1 cands)))))
        (setq word (car (nth 0 cands))))

       (t
        (setq word (car (nth 1 cands)))))))
  word)

(defun mybigword-select-visible-word-default-function ()
  "Default function after visible word is selected."
  (let* ((selected (mybigword--word-at-point))
         (original (mybigword-original-word selected))
         (desc (mybigword-format-with-dictionary original nil))
         outbuf)

    (when (string= "" (string-trim desc))
      ;; fallback to word at point
      (setq original selected)
      (setq desc (mybigword-format-with-dictionary original nil)))

    (mybigword-pronounce-word-internal original)

    (when mybigword-debug
      (message "mybigword-select-visible-word-default-function => selected=%s desc=%s original=%s" selected desc original))

    (when desc
      (setq outbuf (get-buffer-create "*mybigword-single*"))
      (display-buffer outbuf '(nil (allow-no-window . t)))
      (with-current-buffer outbuf
        (erase-buffer)
        (insert desc)
        (goto-char (point-min))))))

;;;###autoload
(defun mybigword-big-words-in-current-window ()
  "Show visible big words in current window.
`mybigword-select-visible-word-function' is executed if a big word is selected.
The word is pronounced and its definition is displayed."
  (interactive)
  (let* ((avy-all-windows nil)
         (start (window-start))
         ;; area from triple size of current window
         (end (+ start (* 4 (- (window-end) start))))
         (text (buffer-substring-no-properties start (min end (point-max))))
         big-words)
    (when text
      (unless mybigword-cache (mybigword-update-cache))
      (setq big-words (mybigword-extract-words text))
      (when (and big-words (> (length big-words) 0))
        (avy-with avy-goto-word-1
          (avy-jump
           (mapconcat 'car big-words "\\|"))
          (when mybigword-select-visible-word-function
            (funcall mybigword-select-visible-word-function)))))))

(defun mybigword-find-file-predicate  (file dir)
  "True if FILE does match `mybigword-find-file-regexp'.
DIR is the directory containing FILE."
  (and (not (file-directory-p (expand-file-name file dir)))
       (string-match mybigword-find-file-regexp file)))

(defun mybigword-find-directory-predicate  (dir parent)
  "True if DIR is not a dot file, and not a symlink.
PARENT is the parent directory of DIR."
  ;; Skip current and parent directories
  (not (or (member dir '("." ".." ".git" ".svn"))
           ;; Skip directories which are symlinks
           ;; Easy way to circumvent recursive loops
           (file-symlink-p (expand-file-name dir parent)))))

;;;###autoload
(defun mybigword-video2mp3 (directory &optional quiet)
  "Convert videos in DIRECTORY into mp3.
If QUIET is t, no message output."
  (interactive "DVideo directory: ")
  (let* ((video-files (and directory
                           (find-lisp-find-files-internal
                            directory
                            #'mybigword-find-file-predicate
                            #'mybigword-find-directory-predicate)))
         (cnt (length video-files))
         (i 0))
    (when (> cnt 0)
      (unless quiet (message "Start conversion ..."))
      (while (< i cnt)
        (let* ((v (nth i video-files)))
          (unless quiet (message "%d/%d video is converted." (1+ i) cnt))
          (shell-command (format "%s -dumpaudio -dumpfile \"%s\" \"%s\""
                                 mybigword-mplayer-program
                                 (mybigword-mp3-path v)
                                 v)))
        (setq i (1+ i))))))

(provide 'mybigword)
;;; mybigword.el ends here
