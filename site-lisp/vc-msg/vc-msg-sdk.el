;;; vc-msg-sdk.el --- SDK for plugins of vc-msg

;; Copyright (C) 2017  Free Software Foundation, Inc.
;;
;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:
;;

;;; Code:

(defun vc-msg-sdk-short-id (id)
  "Format commit ID."
  (substring id 0 8))

(defun vc-msg-sdk-format-datetime (seconds)
  "Format SECONDS to date and time."
  (current-time-string (seconds-to-time (string-to-number seconds))))

(defun vc-msg-sdk-format-timezone (timezone)
  "Format TIMEZONE and show city as extra information."
  (concat timezone
          " "
          (cond
           ((string= timezone "-1200")
            "Eniwetok")
           ((string= timezone "-1100")
            "Midway Island")
           ((string= timezone "-1000")
            "Hawaii")
           ((string= timezone "-0900")
            "Alaska")
           ((string= timezone "-0800")
            "Los Angeles")
           ((string= timezone "-0700")
            "Salt Lake City")
           ((string= timezone "-0600")
            "Chicago")
           ((string= timezone "-0500")
            "Boston")
           ((string= timezone "-0400")
            "Caracas")
           ((string= timezone "-0300")
            "Rio")
           ((string= timezone "-0200")
            "Mid-Atlantic")
           ((string= timezone "-0100")
            "Azores")
           ((string= timezone "+0100")
            "Berlin")
           ((string= timezone "+0200")
            "Cario")
           ((string= timezone "+0300")
            "Moscow")
           ((string= timezone "+0400")
            "Baku")
           ((string= timezone "+0500")
            "New Dehli")
           ((string= timezone "+0600")
            "Kathmandu")
           ((string= timezone "+0700")
            "Bangkok")
           ((string= timezone "+0800")
            "Shanghai")
           ((string= timezone "+0900")
            "Tokyo")
           ((string= timezone "+1000")
            "Sydney")
           ((string= timezone "+1100")
            "Solomon Island")
           ((string= timezone "+1200")
            "Auckland")
           (t
            ""))))

(defun vc-msg-sdk-extract-id-from-output (line-num pattern output)
  "Go to LINE-NUM.  Use PATTERN to extract commit id from OUTPUT.
Return either id or nil."
  (let* (id cur-line)
    (if (string-match-p pattern output)
      (with-temp-buffer
        (insert output)
        (goto-line line-num)
        (setq cur-line (buffer-substring-no-properties (line-beginning-position)
                                                       (line-end-position)))
        (if (string-match pattern cur-line)
            (setq id (match-string 1 cur-line)))))
    id))

(defun vc-msg-sdk-trim (str)
  "Trim STR."
  (setq str (replace-regexp-in-string "[ \t\r\n]*\\'" "" str))
  (replace-regexp-in-string "\\`[ \t\r\n]*" "" str))

(defun vc-msg-sdk-quit-window ()
  "Quit window."
  (interactive)
  (quit-window t))

(defun vc-msg-sdk-get-or-create-buffer (buf-name content)
  "Get or create buffer with BUF-NAME.
CONTENT is inserted into buffer."
  (let* (rlt-buf)
    (if (get-buffer buf-name)
        (kill-buffer buf-name))
    (setq rlt-buf (get-buffer-create buf-name))
    (save-current-buffer
      (switch-to-buffer-other-window rlt-buf)
      (set-buffer rlt-buf)
      (erase-buffer)
      (insert content)

      (diff-mode)
      (goto-char (point-min))

      ;; quit easily
      (local-set-key (kbd "q") 'vc-msg-sdk-quit-window)
      (if (and (boundp 'evil-mode) evil-mode)
          (evil-local-set-key 'normal "q" 'vc-msg-sdk-quit-window))

      ;; You can run `ffip-diff-mode' which inherits from `diff-mode' but is better
      ;; `ffip-diff-mode' is from package find-file-in-project v5.3.2
      (run-hook-with-args 'vc-msg-show-code-hook))))

(defun vc-msg-sdk-extract-summary (pattern output)
  "PATTERN is the beginning of summary extracted from OUTPUT.
PATTERN itself is not part of summary."
  (let* ((summary-beg (+ (string-match pattern output)
                         (length pattern)))
         (summary (substring-no-properties output
                                           summary-beg)))

    ;; remove leading white space
    (setq summary (replace-regexp-in-string "^[ \t]+\\|[ \t]+$" ""
                                            summary))
    ;; strip summary
    (vc-msg-sdk-trim summary)))
;;; vc-msg-sdk.el ends here

(provide 'vc-msg-sdk)
