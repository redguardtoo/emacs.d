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
  (when my-emacs30-p (require 'macher))
  (dolist (p '((english . "Translate the following to English")
               (chinese . "Translate the following to Chinese:")
               (mathematician . "I want you to act as a mathematician. I will type mathematical expressions and you will respond with the result of calculating the expressions. Use latex notation inside \\( and \\) when appropriate. When I need to tell you something in English, I'll do it by putting the text inside curly braces {like this}.")
               (rewrite-tech-english . "You are a professional English writer. Please rewrite in professional technical English.")
               (snippet . "You are a multilingual software engineer. Based on the user's request, generate clean, idiomatic code in the specified language, and briefly explain how it works.")
               (typo . "Fix typos, grammar and style of the following:")))
    (add-to-list 'gptel-directives p)))

(when my-emacs30-p
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
    (macher-enable)))

(defun my-gptel-add-project-context ()
  "Add the current Git project as context."
  (interactive)
  (my-ensure 'gptel)
  (let ((project-root (locate-dominating-file default-directory ".git")))
    (when project-root
      (gptel-add-file project-root)
      (message "Project context added to GPTel session."))))

(with-eval-after-load 'agent-shell
  ;; (setq agent-shell-transcript-file-path-function
  ;;       (lambda (subdir)
  ;;         (let* ((cache-dir "~/.cache/agent-shell/"))
  ;;           (unless (file-exists-p cache-dir) (make-directory cache-dir))
  ;;           (expand-file-name subdir))))

  (defun my-deepseek-harness-make-agent-config ()
    "为 DeepSeek Harness 创建 agent-shell 配置。"
    (agent-shell-make-agent-config
     :identifier 'deepseek-harness
     :mode-line-name "DeepSeek"
     :buffer-name "DeepSeek"
     :shell-prompt "DS> "
     :shell-prompt-regexp "DS> "
     :client-maker (lambda (buffer)
                     (agent-shell--make-acp-client
                      :command "npx"
                      :command-params '("@deepseek-ai/dsh" "--profile" "acp")
                      :context-buffer buffer))
     :needs-authentication nil
     :install-instructions "Make sure CLI 'npx @deepseek-ai/dsh --profile acp' works!"))

  (add-to-list 'agent-shell-agent-configs #'my-deepseek-harness-make-agent-config))

(provide 'init-ai)
;;; init-ai.el ends here
