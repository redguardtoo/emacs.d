;;; init-ai.el --- AI setup  -*- lexical-binding: t -*-

;;; Code:
(defun my-gptel-mode-setup ()
  "Setup of gptel."
  ;; Auto-scroll responses.
  (setq-local window-point-insertion-type t)
  ;; Wrap lines.
  (visual-line-mode 1))
(use-package gptel
  :bind
  (("C-c RET" . gptel-send))

  :custom
  (gptel-default-mode 'org-mode)
  (gptel-include-reasoning nil)

  :hook
  (gptel-mode . my-gptel-mode-setup)

  :config
  (require 'macher)
  (dolist (p '((english . "Translate the following to English")
               (chinese . "Translate the following to Chinese:")
               (mathematician . "I want you to act as a mathematician. I will type mathematical expressions and you will respond with the result of calculating the expressions. Use latex notation inside \\( and \\) when appropriate. When I need to tell you something in English, I'll do it by putting the text inside curly braces {like this}.")
               (rewrite-tech-english . "You are a professional English writer. Please rewrite in professional technical English.")
               (snippet . "You are a multilingual software engineer. Based on the user's request, generate clean, idiomatic code in the specified language, and briefly explain how it works.")
               (typo . "Fix typos, grammar and style of the following:")))
    (push p gptel-directives)))

(use-package macher
  :after gptel
  :custom
  ;; The org UI has structured conversations and nice content folding.
  (macher-action-buffer-ui 'org)

  :config
  ;; Recommended - register macher tools and presets with gptel.
  (macher-install)

  ;; Recommended - enable macher infrastructure for tools/prompts in
  ;; any buffer.  (Actions and presets will still work without this.)
  (macher-enable))

;; @see https://github.com/tninja/aider.el
(use-package aider
  :bind
  (("C-c a" . aider-transient-menu)))

(defun my-gptel-add-project-context ()
  "Add the current Git project as context."
  (interactive)
  (my-ensure 'gptel)
  (let ((project-root (locate-dominating-file default-directory ".git")))
    (when project-root
      (gptel-add-file project-root)
      (message "Project context added to GPTel session."))))


(defun my-gptel-analyze-commit (&optional pick-p)
  "Analyze code commit in the current git project using GPTel.
When PICK-P is not nil, commit for diff start need be picked up by users.
If current buffer is in diff format, buffer context is regarded as one commit;
Or else latest git commit is used.,
Adds project context and explicitly specifies the project root in the prompt.
Displays the response in Org mode."
  (interactive "P")
  (my-ensure 'gptel)
  (let* ((project-root (locate-dominating-file "." ".git"))
         (default-directory project-root)
         (start (cond
                 (pick-p
                  (my-git-commit-id))
                 (t
                  "HEAD")))
         diff-output
         prompt)
    (when start
      (setq diff-output (cond
                         ((derived-mode-p 'diff-mode)
                          (buffer-string))
                         (t
                          (shell-command-to-string (format "git --no-pager diff --unified=10 %s^..HEAD"
                                                           start)))))
      (setq prompt (concat
                    "You are analyzing code from a Git project located at: " project-root "\n\n"
                    "Please analyze the following code changes from the Git commit. "
                    "Consider the overall project context and provide insights on logic improvements, "
                    "potential issues, or optimization suggestions. "
                    "Format your response using Org mode syntax:\n\n"
                    diff-output))
      (gptel-request prompt
        :callback (lambda (response info)
                    (ignore info)
                    (cond
                     ((stringp response)
                      (with-current-buffer (get-buffer-create "*GPTel Commit Analysis*")
                        (erase-buffer)
                        (org-mode)
                        (insert response)
                        (pop-to-buffer (current-buffer))))
                     (t
                      (message "No response is given."))))))))

(provide 'init-ai)
;;; init-ai.el ends here
