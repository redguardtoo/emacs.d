;;; my-byte-compile.el --- syntax check the code  -*- lexical-binding: t -*-

;; Copyright (C) 2022 Chen Bin
;;
;; Author: Chen Bin <chenbin.sh@gmail.com>

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, see <https://www.gnu.org/licenses/>.

;;; Commentary:
;;  Syntax check the code.  It's used in Emacs cli.
;;

;;; Code:

(require 'find-lisp)
(require 'scroll-bar)
(require 'ivy)
(require 'counsel)
(require 'eww)
(require 'ibuffer)
(require 'org)
(require 'diff-mode)
(require 'cliphist)
(require 'eacl)
(require 'tramp)
(require 'dired)
(require 'shellcop)
(require 'counsel-etags)
(require 'typewriter-mode)
(require 'pomodoro)
(require 'emms)
(require 'emms-playlist-mode)
(require 'gnus)
(require 'gnus-sum)
(require 'gnus-msg)
(require 'gnus-topic)
(require 'magit)
(require 'magit-refs)
(require 'gnus-art)
(require 'git-link)
(require 'ace-window)
(require 'js2-mode)
(require 'yasnippet)
(require 'ediff)
(require 'company)
(require 'evil-nerd-commenter)
(require 'git-timemachine)
(require 'pyim)
(require 'cal-china-x)
(require 'wucuo)
(require 'langtool)
(require 'web-mode)
(require 'bbdb)
(require 'gmail2bbdb)
(require 'org-mime)
(require 'pdf-tools)
(require 'recentf)
(require 'bookmark)
(require 'find-file-in-project)
(require 'flymake)
(require 'elec-pair)
(require 'elpy)
(require 'rjsx-mode)
(require 'simple-httpd)
(require 'vc)
(require 'stardict)
(require 'wgrep)
(require 'mybigword)
(require 'yaml-mode)
(require 'octave)
(require 'undo-fu)
(require 'wc-mode)
(require 'exec-path-from-shell)
(require 'dictionary)
(require 'company-ispell)
(require 'company-ctags)
(require 'lsp-mode)
(require 'ob-sagemath)

(let ((files (find-lisp-find-files-internal
              "."
              (lambda (file dir)
                (and (not (file-directory-p (expand-file-name file dir)))
                     (string-match "\\.el$" file)
                     (not (member file '(".dir-locals.el"
                                         "package-quickstart.el"
                                         "company-statistics-cache.el"
                                         "custom-set-variables.el"
                                         "init-misc.el"
                                         "early-init.el")))))
              (lambda (dir parent)
                (member dir '("lisp"))))))
  (dolist (file files)
    ;; (message "file=%s" file)
    (byte-compile-file file)))

(provide 'my-byte-compile)
;;; my-byte-compile.el ends here
