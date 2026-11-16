;; -*- coding: utf-8; lexical-binding: t; -*-

;;; Code:

(defun my-python-mode-setup ()
  "Setup Python editing."
  (unless (or (my-buffer-file-temp-p)
              (not buffer-file-name)
              (string-equal (file-name-extension buffer-file-name) "org"))
    (when (boundp 'electric-indent-chars)
      ;; http://emacs.stackexchange.com/questions/3322/python-auto-indent-problem/3338#3338
      ;; emacs 24.4+
      (setq-local electric-indent-chars
                  (delq ?: (copy-sequence electric-indent-chars))))))
(add-hook 'python-mode-hook #'my-python-mode-setup)
(add-hook 'python-ts-mode-hook #'my-python-mode-setup)

(defvar my-python-venv-directories
  '("~/.venv")
  "Directories of python venv.")

(defun my-activate-python-venv (directory)
  "Activate python venv in DIRECTORY."
  (my-ensure 'pyvenv)
  (let* ((python (or (and  pyvenv-virtualenvwrapper-python
                           (executable-find pyvenv-virtualenvwrapper-python))
                     (executable-find "python3")))
         (venv-dir (expand-file-name directory)))

    (cond
     ((null python)
      (message "No Python executable found."))
     ((not (file-directory-p venv-dir))
      (message "Directory \"%s\" is missing." venv-dir))
     (t
      (let* ((pyvenv-virtualenvwrapper-python python))
        (pyvenv-activate venv-dir))))))

(defun my-select-python-venv ()
  "Activate python venv."
  (interactive)
  (let* ((venv-dir (completing-read "Select Python venv: "
                                    my-python-venv-directories)))
    (when venv-dir
      (my-activate-python-venv venv-dir))))

;; treesit for smart syntax highlight
(add-to-list 'treesit-extra-load-path
             (expand-file-name "~/.emacs.d/tree-sitter"))
(when (treesit-language-available-p 'python)
  (push '(python-mode . python-ts-mode) major-mode-remap-alist))

;; LSP client
(add-hook 'python-mode-hook #'eglot-ensure)
(add-hook 'python-ts-mode-hook #'eglot-ensure)


(provide 'init-python)
;;; init-python.el ends here
