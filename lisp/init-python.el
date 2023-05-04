;; -*- coding: utf-8; lexical-binding: t; -*-

(with-eval-after-load 'python
  ;; run command `pip install jedi flake8 importmagic` in shell,
  ;; or just check https://github.com/jorgenschaefer/elpy
  (unless (or (my-buffer-file-temp-p)
              (not buffer-file-name)
              ;; embed python code in org file
              (string= (file-name-extension buffer-file-name) "org"))
    (setq elpy-shell-command-prefix-key "C-c C-f")
    (elpy-enable)
    ;; If you don't like any hint or error report from elpy,
    ;; set `elpy-disable-backend-error-display' to t.
    (setq elpy-disable-backend-error-display nil))
  ;; http://emacs.stackexchange.com/questions/3322/python-auto-indent-problem/3338#3338
  ;; emacs 24.4+
  (setq electric-indent-chars (delq ?: electric-indent-chars)))

(defvar my-python-venv-directories
  '("~/.emacs.d/elpy/rpc-venv"
    "~/.venv")
  "Directories of python venv.")

(defun my-activate-python-venv (directory)
  "Activate python venv in DIRECTORY."
  (my-ensure 'pyvenv)
  (let* ((venv-dir directory)
         (python pyvenv-virtualenvwrapper-python))

    (setq python (and (executable-find python) (executable-find "python3")))
    (cond
     ((null python)
      (message "Python executable \"%s\" is missing." python))
     ((not (file-exists-p venv-dir))
      (message "Directory \"%s\" is missing." venv-dir))
     (t
      (let* ((pyvenv-virtualenvwrapper-python python))
        (pyvenv-activate venv-dir))))))

(defun my-select-python-venv-and-restart-elpy ()
  "Activate python venv."
  (interactive)
  (let* ((venv-dir (completing-read "Select Python venv: "
                                    my-python-venv-directories)))
    (when venv-dir
      (my-activate-python-venv venv-dir)
      (elpy-disable)
      (elpy-shell-kill-all)
      (elpy-enable))))

(provide 'init-python)
;;; init-python.el ends here
