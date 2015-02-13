;;; issue-tracker.el --- Create an issue id from current issue id. Current issue id could be any text under cursor in the Emacs buffer.

;; Copyright (C) 2013 Chen Bin
;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/issue-tracker.el
;; Keywords: issue tracker bug jira
;; Version: 0.0.1

;; This file is not part of GNU Emacs.

;; This file is free software (GPLv3 License)

;; How to set it up:
;; See README.org which is distributed with this file

;;; Code:

(defvar issue-tracker-id-regexp
  "^\\(.*[^0-9]\\)\\([0-9]+\\)$"
  "The issue id regex which should end with digits")

(defun issue-tracker-analyze-id (id)
  (let (prefix num)
    (when (string-match issue-tracker-id-regexp id)
      (setq prefix (match-string 1 id))
      (setq num (string-to-number (match-string 2 id)))
      (list prefix num))
    ))

(defun issue-tracker-share-str (msg)
  (kill-new msg)
  (with-temp-buffer
    (insert msg)
    (shell-command-on-region (point-min) (point-max)
                             (cond
                              ((eq system-type 'cygwin) "putclip")
                              ((eq system-type 'darwin) "pbcopy")
                              (t "xsel -ib")
                              )))
  )

(defun issue-tracker-bounds-of-bigword-under-cursor ()
  (interactive)
  (let ((big-word-chars " \t\r\n")
        (old-position (point))
        (b (line-beginning-position))
        (e (line-end-position)))
    (re-search-backward "[ \t\r\n]" nil t)
    (goto-char (+ (point) 1))
    (setq b (point))
    (re-search-forward "[ \t\r\n]" nil t)
    ;; (message "c=%c" (char-after (point)))
    (setq e (- (point) 1))
    ;; restore the position
    (goto-char old-position)
    ;; (message "b=%d e=%d" b e)
    (if (> b e)
        (setq e (buffer-end 1))
        )
    (list b e)
    ))

;;;###autoload
(defun issue-tracker-increment-issue-id-under-cursor ()
  "increment current issue id under cursor and copy it to yank-ring/clipboard "
  (interactive)
  (let ((bounds (issue-tracker-bounds-of-bigword-under-cursor))
        ;; (id (buffer-substring (car bounds) (nth 1 bounds)))
        rlt
        id
        nid
        num)
    (setq id (buffer-substring (car bounds) (nth 1 bounds)))
    ;; (message "id=%s" id)
    ;; get symbol under cursor
    (if (setq rlt (issue-tracker-analyze-id id))
        (progn
          (setq num (1+ (cadr rlt)))
          (setq nid (concat (car rlt) (number-to-string num))))
      (setq nid (concat id "1")))

    (issue-tracker-share-str nid)
    ;; change current issue id under cursor into new id
    (delete-region (car bounds) (nth 1 bounds))
    (insert nid)
    (goto-char (car bounds))
    ))

;;;###autoload
(defun issue-tracker-insert-issue-list (id)
  "Insert the issue list"
  (interactive "sHighest issue id:")
  (let (rlt i upper)
    (when (setq rlt (issue-tracker-analyze-id id))
      (setq upper (cadr rlt))
      (setq i 0)
      (if upper
          (while (and upper (< i upper))
            (insert (format "- [ ] %s%d\n" (car rlt) (1+ i)))
            (setq i (1+ i)))))
    ))

;;; issue-tracker.el ends here
