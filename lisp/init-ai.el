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


(defun my-gptel-analyze-latest-commit ()
  "Analyze latest commit diff."
  (interactive)
  (my-ensure 'gptel)
  (let* ((default-directory (locate-dominating-file "." ".git"))
         (diff-output (shell-command-to-string "git show HEAD"))
         (prompt (concat
                  "Please analyze the following code changes from the latest Git commit. "
                  "Consider the overall project context and provide insights on logic improvements, "
                  "potential issues, or optimization suggestions:\n\n"
                  diff-output)))
    (gptel-request prompt
      :callback (lambda (response info)
                  (ignore info)
                  (cond
                   (response
                    (with-current-buffer (get-buffer-create "*GPTel Commit Analysis*")
                      (erase-buffer)
                      (insert response)
                      (pop-to-buffer (current-buffer))))
                   (t
                    (message "No response is given.")))))))

(provide 'init-ai)
;;; init-ai.el ends here
