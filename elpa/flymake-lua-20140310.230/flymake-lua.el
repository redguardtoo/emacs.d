;;; flymake-lua.el --- Flymake for Lua

;; Copyright (C) 2009-2014 Sébastien Roccaserra

;; Author: Sébastien Roccaserra (format "<%s%s@%s.%s>" "s" "roccaserra" "yahoo" "com")
;; Created: 07 Dec 2009
;; Keywords: lua
;; Package-Version: 20140310.230

;; This file is not part of GNU Emacs.

;; Licensed under the Apache License, Version 2.0 (the "License");
;; you may not use this file except in compliance with the License.
;; You may obtain a copy of the License at

;;     http://www.apache.org/licenses/LICENSE-2.0

;; Unless required by applicable law or agreed to in writing, software
;; distributed under the License is distributed on an "AS IS" BASIS,
;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;; See the License for the specific language governing permissions and
;; limitations under the License.

;;; Commentary:

;; Usage:
;;   (require 'flymake-lua)
;;   (add-hook 'lua-mode-hook 'flymake-lua-load)
;;
;; Note: literally stolen from Steve Purcell's Flymake Ruby.
;; See http://github.com/purcell/flymake-ruby

;;; Code:

(require 'flymake)

(defgroup flymake-lua nil
  "Flymake Lua Customizations")

(defcustom flymake-luac-program "luac"
  "How to invoke luac. Other possible value: /usr/local/bin/luac."
  :type 'file
  :group 'flymake-lua)

(defun flymake-create-temp-in-system-tempdir (filename prefix)
  (make-temp-file (or prefix "flymake-lua")))

(defun flymake-lua-init ()
  (list flymake-luac-program
        (list "-p" (flymake-init-create-temp-buffer-copy
                    'flymake-create-temp-in-system-tempdir))))

(defvar flymake-lua-allowed-file-name-masks '(("\\.lua\\'" flymake-lua-init)))
(defvar flymake-lua-err-line-patterns '(("^.*luac[0-9.]*\\(.exe\\)?: *\\(.*\\):\\([0-9]+\\): \\(.*\\)$"
                                    2 3 nil 4)))

;;;###autoload
(defun flymake-lua-load ()
  (interactive)
  (when (and (not (null buffer-file-name)) (file-writable-p buffer-file-name))
    (set (make-local-variable 'flymake-allowed-file-name-masks) flymake-lua-allowed-file-name-masks)
    (set (make-local-variable 'flymake-err-line-patterns) flymake-lua-err-line-patterns)
    (flymake-mode t)))

(provide 'flymake-lua)
;;; flymake-lua.el ends here
