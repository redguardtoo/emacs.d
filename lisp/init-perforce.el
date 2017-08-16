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

(defun p4-generate-cmd (opts &optional in-project)
  (format "p4 %s %s" opts (if in-project (p4-convert-dir-to-url (ffip-project-root))
                            (p4-covert-current-file-to-url))))

(defun p4edit ()
  "p4 edit current file."
  (interactive)
  (shell-command (p4-generate-cmd "edit"))
  (read-only-mode -1))

(defun p4-edit-file-and-make-buffer-writable(file)
  "p4 edit FILE and make corresponding buffer writable."
  (shell-command (format "p4 edit %s" (p4-convert-file-to-url file)))
  ;; make sure the buffer is readable
  (let* ((buf (get-file-buffer file)))
    (if buf
        (with-current-buffer buf
          ;; turn off read-only since we've already `p4 edit'
          (read-only-mode -1)))))

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

(defun p4-show-changelist-patch (chg &optional in-project)
  (let* ((url (if in-project (p4-convert-dir-to-url (ffip-project-root))
                (p4-covert-current-file-to-url)))
         (pattern "^==== //.*====$")
         sep
         seps
         (start 0)
         (original (if chg (shell-command-to-string (format "p4 describe -du %s" chg)) ""))
         rlt)

    (cond
     (in-project
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

    ;; clean the verbose summary
    (setq rlt (replace-regexp-in-string "^\\(Affected\\|Moved\\) files \.\.\.[\r\n]+"
                                        ""
                                        rlt))
    (setq rlt (replace-regexp-in-string "Differences \.\.\.[\r\n]+" "" rlt))
    ;; one line short description of change list
    (setq rlt (replace-regexp-in-string "Change \\([0-9]+\\) by \\([^ @]+\\)@[^ @]+ on \\([^ \r\n]*\\).*[\r\n \t]+\\([^ \t].*\\)" "\\1 by \\2@\\3 \\4" rlt))
    ;; `diff-mode' friendly format
    (setq rlt (replace-regexp-in-string "^==== \\(.*\\)#[0-9]+ (text) ====[\r\n]+" "--- \\1\n+++ \\1\n" rlt))
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
      ;; `ffip-diff-mode' inherits from `diff-mode'
      (ffip-diff-mode)
      (goto-char (point-min))
      ;; we want to see change list instead
      (if enable-imenu
          (setq imenu-create-index-function
                (lambda ()
                  (save-excursion
                    (imenu--generic-function '((nil "^[0-9]+ by .*" 0)))))))

      ;; quit easily in evil-mode
      (evil-local-set-key 'normal "q" (lambda () (interactive) (quit-window t))))))

(defun p4-changes (&optional just-lines in-project)
  "Show changelists.  IF JUST-LINES is t, show the lines instead of changelists.
IF IN-PROJECT is t, show changelists of current project instead current file."
  (let* ((cmd (p4-generate-cmd "changes" in-project))
         (lines (split-string (shell-command-to-string cmd) "\n")))
    (if just-lines lines
      (delq nil (mapcar #'p4--extract-changenumber lines)))))

(defun p4diff (&optional in-project)
  "Show diff of current file like `git diff'.
If IN-PROJECT is t, operate in project root."
  (interactive "P")
  (let* ((content (shell-command-to-string (p4-generate-cmd "diff -du -db" in-project))))
    (p4--create-buffer "*p4diff*" content)))

(defun p4show(&optional in-project)
  "p4 show changes of current file.
If IN-PROJECT is t, operate in project root."
  (interactive "P")
  (let* ((lines (p4-changes t in-project)))
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
                                           nil
                                           (ffip-project-root))))))

(defun p4--edit-file (filename &optional fn-accessed)
  "'p4 edit' FILENAME unless it equals FN-ACCESSED."
  (unless (string= filename fn-accessed)
    (shell-command (format "p4 edit %s" filename))
    (if (setq buf (get-file-buffer filename))
        (with-current-buffer buf
          ;; turn off read-only since we've already `p4 edit'
          (read-only-mode -1)))))

(defun p4edit-in-wgrep-buffer()
  "'p4 edit' files in wgrep buffer.
Turn off `read-only-mode' of opened files."
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
            (let* ((filename (match-string-no-properties 1)) buf)
              (p4--edit-file filename fn-accessed)
              (setq fn-accessed filename)))
        (forward-line 1)))))


(defun p4edit-in-diff-mode()
  "'p4 edit' files in `diff-mode'.
Turn off `read-only-mode' of opened files."
  (interactive)
  (unless (featurep 'imenu)
    (require 'imenu nil t))
  (let* ((imenu-auto-rescan t)
         (imenu-auto-rescan-maxout (if current-prefix-arg
                                       (buffer-size)
                                     imenu-auto-rescan-maxout))
         (items (imenu--make-index-alist t))
         fn-accessed)
    (setq items (delete nil (delete-dups (mapcar #'car (delete (assoc "*Rescan*" items) items)))))
    (save-restriction
     (dolist (filename items)
       (p4--edit-file filename fn-accessed)
       (setq fn-accessed filename)))))

(defun p4history (&optional num)
  "Show history of current file like `git log -p'.
NUM default values i 10.  Show the latest NUM changes."
  (interactive "P")
  (unless num
    (setq num 10))
  (let* ((content (mapconcat #'p4-show-changelist-patch
                             (let* ((chgs (p4-changes)))
                               (if (and num (< num (length chgs))) (subseq chgs 0 num)
                                 chgs))
                   "\n\n")))
    (p4--create-buffer "*p4history*" content t)))

(provide 'init-perforce)
