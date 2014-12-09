;;; cb.el --- tools for http://www.chicagoboss.org/

;; Copyright (C) 2014 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/cb
;; Keywords: mvc cb chicagoboss erlang
;; Version: 0.0.1

;; This file is not part of GNU Emacs.

(defun cb--parent-dirname (dir)
  (cadr (nreverse (split-string dir "/"))))

(defun cb--root-dir ()
  (locate-dominating-file (file-name-as-directory (file-name-directory buffer-file-name)) ".git"))

;;; Code:
(defun cb-switch-between-controller-and-view ()
  (interactive)
  (let (f)
    (setq f (file-name-nondirectory (buffer-file-name)))
    ;; open the html of controller
    (when (string= (file-name-extension f) "erl")
      (let (namespace ctrlname type info len wf)
        (setq info (split-string f "_"))
        (setq len (length info))
        (when (and (> len 2) (which-function))
          (setq wf (replace-regexp-in-string "/[0-9]+$" "" (which-function)))
          (setq ctrlname (nth (- len 2) info))
          (setq type (file-name-base (nth (- len 1) info)))
          (setq namespace (replace-regexp-in-string
                           (concat ctrlname "_" type ".erl$") "" f))
          (find-file (concat (cb--root-dir) "src/view/" ctrlname "/" wf ".html"))
          )))
    (when (string= (file-name-extension f) "html")
      (let (namespace ctrlname type info len wf)
        (setq namespace (cb--parent-dirname (cb--root-dir)))
        (setq ctrlname (cb--parent-dirname (file-name-directory (buffer-file-name))))
        (setq wf (file-name-base f))
        (find-file (concat (cb--root-dir)
                           "src/controller/"
                           namespace
                           "_"
                           ctrlname
                           "_controller.erl"))
          ;; goto function definition
        (goto-char (point-min))
        (re-search-forward (concat "^" wf " *("))
        ))
    ))

(provide 'cb)

;;; cb.el ends here