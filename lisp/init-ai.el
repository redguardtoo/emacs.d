;; init-ai.el --- AI setup  -*- lexical-binding: t -*-
;
(global-set-key (kbd "C-c RET") #'gptel-send)
(with-eval-after-load 'gptel
  (setq gptel-default-mode 'org-mode)
  (defvar my-deepseek-backend
    (gptel-make-ollama "AI deepseek-r1"
      :host "localhost:11434"
      :stream t
      :models '(deepseek-r1:latest))
    "Deepseek backend.")

  (defvar my-gemma3n-backend
    (gptel-make-ollama "AI gemma3n"
      :host "localhost:11434"
      :stream t
      :models '(gemma3n:latest))
    "Gemma3n backend.")

  (dolist (p '((english . "Translate the following to English")
               (chinese . "Translate the following to Chinese:")
               (mathematician . "I want you to act as a mathematician. I will type mathematical expressions and you will respond with the result of calculating the expressions. Use latex notation inside \\( and \\) when appropriate. When I need to tell you something in English, I'll do it by putting the text inside curly braces {like this}.")
               (rewrite-tech-english "You are a professional English writer. Please rewrite in professional technical English.")
               (snippet . "You are a multilingual software engineer. Based on the user's request, generate clean, idiomatic code in the specified language, and briefly explain how it works.")
               (typo . "Fix typos, grammar and style of the following:")))
    (push p gptel-directives))

  ;; don't display reasoning
  (setq gptel-include-reasoning nil)

  (gptel-make-preset "AI deepseek-r1"
    :backend my-deepseek-backend)

  (gptel-make-preset "AI gemma3n"
    :backend my-gemma3n-backend)

  ;; set up default model and backend
  (setq gptel-model 'deepseek-r1:latest
        gptel-backend my-deepseek-backend))

;; @see https://github.com/tninja/aider.el
(global-set-key (kbd "C-c a") 'aider-transient-menu) ;
(with-eval-after-load 'aider
  ;; (setq aider-args '("--model" "ollama_chat/gemma3n:latest")) ; google light weight model
  (setq aider-args '("--model" "ollama_chat/deepseek-r1:latest"))) ; deepseek

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
