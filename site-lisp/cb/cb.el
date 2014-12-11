;;; cb.el --- tools for http://www.chicagoboss.org/

;; Copyright (C) 2014 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/cb
;; Keywords: mvc cb chicagoboss erlang
;; Version: 0.0.1

;; This file is not part of GNU Emacs.

;;; Code:

(defvar cb-app-url-prefix "http://127.0.0.1:8001/")

(defun cb--parent-dirname (dir)
  (cadr (nreverse (split-string dir "/"))))

(defun cb--root-dir ()
  (locate-dominating-file (file-name-as-directory (file-name-directory buffer-file-name)) ".git"))

(defun cb--copy-yank-str (msg &optional clipboard-only)
  (unless clipboard-only (kill-new msg))
  (cond
   ;; display-graphic-p need windows 23.3.1
   ((and (display-graphic-p) x-select-enable-clipboard)
    (x-set-selection 'CLIPBOARD msg))
   (t (with-temp-buffer
        (insert msg)
        (shell-command-on-region (point-min) (point-max)
                                 (cond
                                  ((eq system-type 'cygwin) "putclip")
                                  ((eq system-type 'darwin) "pbcopy")
                                  (t "xsel -ib")
                                  )))
    )))

;;;###autoload
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
          (let ((view-dir (concat (cb--root-dir) "src/view/" ctrlname)))
            (unless (file-exists-p view-dir)
              (make-directory view-dir))
            (find-file (concat view-dir "/" wf ".html")))
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

;;;###autoload
(defun cb-get-url-from-controller ()
  (interactive)
  (let (f)
    (setq f (file-name-nondirectory (buffer-file-name)))
    ;; open the html of controller
    (when (string= (file-name-extension f) "erl")
      (let (namespace ctrlname type info len wf paras-cnt)
        (setq info (split-string f "_"))
        (setq len (length info))
        (when (and (> len 2) (which-function))
          (setq wf (which-function))
          (setq ctrlname (nth (- len 2) info))
          (setq type (file-name-base (nth (- len 1) info)))
          (if (string-match ".*\/\\([0-9]+\\)$" wf)
            (setq paras-cnt (match-string 1 wf)))
          (let ((app-url (concat (file-name-as-directory cb-app-url-prefix)
                                 ctrlname
                                 "/"
                                 (replace-regexp-in-string "/[0-9]+$" "" (which-function))
                                 "/"
                                 (if (and (string= paras-cnt "1") (string= paras-cnt "0"))
                                     ""
                                     paras-cnt)
                                 )))
            (cb--copy-yank-str app-url)
            (message "%s => clipboard" app-url))
          )))
    ))

(provide 'cb)

;;; cb.el ends here