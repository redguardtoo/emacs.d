(defvar p4-file-to-url '("" "")
  "(car p4-file-to-url) is the original file prefix
(cadr p4-file-to-url) is the url prefix")

(defun p4-convert-file-to-url (file)
  (replace-regexp-in-string (car p4-file-to-url)
                            (cadr p4-file-to-url)
                            file))

(defun p4-covert-current-file-to-url ()
  (p4-convert-file-to-url buffer-file-name))

(defun p4-convert-dir-to-url (dir)
  "Convert directory to p4 url."
  (replace-regexp-in-string (car p4-file-to-url)
                            (cadr p4-file-to-url)
                            (concat (file-name-as-directory dir) "...")))

(defun p4-generate-cmd (opts &optional not-current-file)
  (format "p4 %s %s" opts (if not-current-file "..."
                            (p4-covert-current-file-to-url))))

(defun p4edit ()
  "p4 edit current file."
  (interactive)
  (shell-command (p4-generate-cmd "edit"))
  (read-only-mode -1))

(defun p4submit (&optional file-opened)
  "p4 submit current file.
If FILE-OPENED, current file is still opened."
  (interactive "P")
  (let* ((msg (read-string "Say (ENTER to abort):"))
         (open-opts (if file-opened "-f leaveunchanged+reopen -r" ""))
         (full-opts (format "submit -d '%s' %s" msg open-opts)))
    (if (string= "" msg)
        (message "Abort submit.")
      (shell-command (p4-generate-cmd full-opts))
      (unless file-opened (read-only-mode 1))
      (message (format "%s submitted."
                       (file-name-nondirectory buffer-file-name))))))

(defun p4url ()
  "Get Perforce depot url of the file."
  (interactive)
  (let* ((url (p4-covert-current-file-to-url)))
    (copy-yank-str url)
    (message "%s => clipboard & yank ring" url)))

(defun p4unshelve ()
  "Unshelve files from selected change."
  (interactive)
  (let* ((user-info (shell-command-to-string "p4 user -o"))
         (user (if (string-match "^User:[ \t]+\\([a-zA-Z0-9-_]+\\)" user-info)
                   (match-string 1 user-info)))
         (changes (split-string (shell-command-to-string (format "p4 changes -s pending -u %s" user)) "\n") ))
    (ivy-read "p4 shelved changes:"
              changes
              :preselect 0
              :action (lambda (line)
                        (if (string-match "^Change \\([0-9]+\\) " line)
                            (let* ((chg (match-string 1 line)))
                              (shell-command-to-string (format "p4 unshelve -s %s" chg))
                              (kill-new chg)
                              (message "Change %s unshelved and copied into kill-ring!" chg)))))))

(defun p4--extract-changenumber (line)
  (if (string-match "^Change \\([0-9]+\\) " line)
      (match-string 1 line)))

(defun p4revert ()
  "p4 revert current file."
  (interactive)
  (shell-command (p4-generate-cmd "revert"))
  (read-only-mode 1))

(defun p4add ()
  "p4 add current file."
  (interactive)
  (shell-command (p4-generate-cmd "add")))

(defun p4-show-changelist-patch (chg &optional not-current-file)
  (let* ((url (if not-current-file (p4-convert-dir-to-url (ffip-project-root))
                (p4-covert-current-file-to-url)))
         (pattern "^==== //.*====$")
         sep
         seps
         (start 0)
         (original (if chg (shell-command-to-string (format "p4 describe -du %s" chg)) ""))
         rlt)

    (cond
     (not-current-file
      (setq rlt original))
     (t
      (while (setq sep (string-match pattern original start))
        (let* ((str (match-string 0 original)))
          (setq start (+ sep (length str)))
          (add-to-list 'seps (list sep str) t)))
      (setq rlt (substring original 0 (car (nth 0 seps))))
      (let* ((i 0) found)
        ;; search patch for current file
        (while (and (not found)
                    (< i (length seps)))
          (when (string-match url (cadr (nth i seps)))
            (setq rlt (concat rlt (substring original
                                             (car (nth i seps))
                                             (if (= i (- (length seps) 1))
                                                 (length original)
                                               (car (nth (+ 1 i) seps))))))
            ;; out of loop now since current file patch found
            (setq found t))
          (setq i (+ 1 i))))))

    ;; remove p4 verbose bullshit
    (setq rlt (replace-regexp-in-string "^\\(Affected\\|Moved\\) files \.\.\.[\r\n]+\\(\.\.\. .*[\r\n]+\\)+"
                                        ""
                                        rlt))
    (setq rlt (replace-regexp-in-string "Differences \.\.\.[\r\n]+" "" rlt))
    ;; one line short description of change list
    (setq rlt (replace-regexp-in-string "Change \\([0-9]+\\) by \\([^ @]+\\)@[^ @]+ on \\([^ \r\n]*\\).*[\r\n \t]+\\([^ \t].*\\)" "\\1 by \\2@\\3 \\4" rlt))
    rlt))

(defvar p4-imenu-parse-hunk-header-rules
  '((nil "^==== *//depot/\\(.*\\) *====" 1))
  "Rules to extract hunk header in diff for imenu usage.")

(defun p4--create-buffer (buf-name content &optional enable-imenu force-default-directory)
  (let* (rlt-buf)
    (if (get-buffer buf-name)
        (kill-buffer buf-name))
    (setq rlt-buf (get-buffer-create buf-name))
    (save-current-buffer
      (if force-default-directory
          (setq default-directory force-default-directory))
      (switch-to-buffer-other-window rlt-buf)
      (set-buffer rlt-buf)
      (erase-buffer)
      (insert content)
      (diff-mode)
      (goto-char (point-min))
      ;; nice imenu output
      (cond
       ((= enable-imenu 1)
        (setq imenu-create-index-function
              (lambda ()
                (save-excursion
                  (imenu--generic-function '((nil "^[0-9]+ by .*" 0)))))))
       ((= enable-imenu 2)
        (setq imenu-create-index-function
              (lambda ()
                (save-excursion
                  (imenu--generic-function p4-imenu-parse-hunk-header-rules))))))

      ;; quit easily in evil-mode
      (evil-local-set-key 'normal "q" (lambda () (interactive) (quit-window t))))))

(defun p4-changes (just-lines current-file)
  (let* ((cmd (if current-file (p4-generate-cmd "changes")
                (format "p4 changes %s" (p4-convert-dir-to-url (ffip-project-root)))))
         (lines (split-string (shell-command-to-string cmd) "\n")))
    (if just-lines lines
      (delq nil (mapcar #'p4--extract-changenumber lines)))))

(defun p4diff ()
  "Show diff of current file like `git diff'."
  (interactive)
  (let* ((content (shell-command-to-string (p4-generate-cmd "diff -du -db"))))
    (p4--create-buffer "*p4diff*" content)))

(defun p4show()
  "p4 show change."
  (interactive)
  (let* ((lines (p4-changes t nil)))
    ;; According to Perforce documenation of `p4 describe`:
    ;; If a changelist is pending, it is flagged as such in the output,
    ;; and the list of open files is shown.
    ;; (Diffs for pending changelists are not displayed because the
    ;; files have yet to be submitted to the server.)
    (ivy-read "p4 submitted changes"
              lines
              :preselect 0
              :action (lambda (line)
                        (p4--create-buffer "*p4show*"
                                           (p4-show-changelist-patch (p4--extract-changenumber line) t)
                                           2
                                           (ffip-project-root))))))

(defun p4edit-in-wgrep-buffer()
  (interactive)
  (save-restriction
    (let* ((start (wgrep-goto-first-found))
           (end (wgrep-goto-end-of-found))
           fn-accessed)
      (narrow-to-region start end)
      (goto-char (point-min))
      (unless (featurep 'wgrep) (require 'featurep))
      (while (not (eobp))
        (if (looking-at wgrep-line-file-regexp)
            (let* ((fn (match-string-no-properties 1)))
              (unless (string= fn fn-accessed)
                (setq fn-accessed fn)
                (shell-command ("p4 edit %s" fn)))))
        (forward-line 1)))))

(defun p4history ()
  "Show history of current file like `git log -p'."
  (interactive)
  (let* ((content (mapconcat #'p4-show-changelist-patch
                             (p4-changes nil t)
                             "\n\n")))
   (p4--create-buffer "*p4log*" content 1 default-directory)))

;; Used in my patched emacs-git-messenger:
;; (setq git-messenger:exp-to-create-commit-details 'p4-create-commit-details)
(defun p4-create-commit-details ()
  "Return '(commit-id author msg)"
  (let* ((content (shell-command-to-string (p4-generate-cmd "annotate -c -q")))
         (line-num (line-number-at-pos))
         filelog-content
         cur-line
         changelist
         commit-msg
         rlt)

    (with-temp-buffer
      (insert content)
      (goto-line line-num)
      (setq cur-line (buffer-substring-no-properties (line-beginning-position)
                                                     (line-end-position)))
      (if (string-match "^\\([0-9]+\\): " cur-line)
          (setq changelist (match-string 1 cur-line))))

    (when changelist
      (setq content (shell-command-to-string (p4-generate-cmd "p4 changes -l")))
      (let* ((b (string-match (format "^Change %s on" changelist) filelog-content))
             (e (string-match "^Change [0-9]+ on" filelog-content b)))
        (if (or (not e) (<= e b))
            (setq e (length filelog-content)))
        (setq commit-msg (substring-no-properties filelog-content b e))))

    ;; We need extract information from below text:
    ;; Change 299998 on 2017/04/05 by somebody
    ;;
    ;;     test1 blah
    (if (and commit-msg
             (string-match "Change \\([0-9]+\\) on.* by \\([^ ]+\\)$" commit-msg))
        (setq rlt (list (match-string 1 commit-msg)
                        (match-string 2 commit-msg)
                        commit-msg)))
    ;; (message "rlt=%s" rlt)
    rlt))

(provide 'init-perforce)
