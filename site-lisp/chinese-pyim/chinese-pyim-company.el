;;; chinese-pyim-company.el --- Integrate company-mode with Chinese-pyim
;;; Header:
;; Copyright  2015 Feng Shu

;; Author: Feng Shu <tumashu@163.com>
;; URL: https://github.com/tumashu/chinese-pyim
;; Version: 0.0.1
;; Keywords: convenience, Chinese, pinyin, input-method, complete

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:
;; 这个包为 `Chinese-pyim' 添加中文词条 *联想* 功能，其使用方式：

;; #+BEGIN_EXAMPLE
;; (require 'chinese-pyim-company)
;; #+END_EXAMPLE

;;; Code:
;; #+BEGIN_SRC emacs-lisp
(require 'chinese-pyim)
(require 'company)
(require 'company-dabbrev)

(defcustom pyim-company-predict-words-number 10
  "设置最多可以搜索多少个联想词条，如果设置为 nil
或者 0 时，关闭联想功能。"
  :group 'chinese-pyim
  :type 'number)

(defcustom pyim-company-variables
  `((company-backends ,(nconc '((pyim-company-predict-words pyim-company-dabbrev))
                              company-backends))
    (company-idle-delay  0.1)
    (company-minimum-prefix-length  2)
    (company-selection-wrap-around  t)
    (company-show-numbers t)
    (company-dabbrev-downcase nil)
    (company-dabbrev-ignore-case nil)
    (company-require-match nil))
  "`company-mode' 与 `Chinese-pyim' 配合时需要特别设置，
这个 list 包含了需要设置的 `company-mode' 变量。"
  :group 'chinese-pyim)
;; #+END_SRC

;; #+BEGIN_SRC emacs-lisp
(defun pyim-company-backup-variable (variable)
  "创建变量 `pyim-<variale>-backup' ，用来保存变量 `variable' 原来的设定"
  (if (boundp variable)
      (set (intern (concat "pyim-" (symbol-name variable) "-backup"))
           (symbol-value variable))
    (error "Company-mode 默认变量备份失败！请确保 Company-mode 优先加载。")))

(defun pyim-company-revert-variable (variable)
  "将变量 `variable' 设置为 `pyim-<variale>-backup' 的值。"
  (when (boundp variable)
    (let ((variable-backup (intern (concat "pyim-" (symbol-name variable) "-backup"))))
      (if (boundp variable-backup)
          (set variable (symbol-value variable-backup))
        (message "变量还原失败,没有找到备份变量！")))))
;; #+END_SRC

;; #+BEGIN_SRC emacs-lisp
(defun pyim-company-revert-to-default-settings (x)
  "`company-mode' 补全完成或者取消后，恢复 `company-mode' 原来的设置。"
  (mapc 'pyim-company-revert-variable
        (mapcar 'car pyim-company-variables))
  (remove-hook 'company-completion-cancelled-hook
               'pyim-company-revert-to-default-setting t)
  (remove-hook 'company-completion-finished-hook
               'pyim-company-revert-to-default-setting t))
;; #+END_SRC

;; #+BEGIN_SRC emacs-lisp
;;;###autoload
(defun pyim-company-complete ()
  "`company-mode' 补全命令的包装函数，专门用户 `chinese-pyim'"
  (interactive)
  (unless company-mode (company-mode))
  ;; 保存 `company-mode' 变量原来的设定。
  (mapc 'pyim-company-backup-variable
        (mapcar 'car pyim-company-variables))
  ;; 设置 `company-mode' 变量
  (dolist (list pyim-company-variables)
    (set (car list) (car (cdr list))))
  ;; 当 `company-mode' 补全完成或者取消时，恢复原来设置。
  (add-hook 'company-completion-cancelled-hook
            'pyim-company-revert-to-default-settings t)
  (add-hook 'company-completion-finished-hook
            'pyim-company-revert-to-default-settings t)
  (company-manual-begin))
;; #+END_SRC

;; #+BEGIN_SRC emacs-lisp
;; `Chinese-pyim' 选词结束后，调用 `pyim-company-complete'.
(add-hook 'pyim-select-word-finish-hook 'pyim-company-complete)
;; #+END_SRC

;; #+BEGIN_SRC emacs-lisp
(defun pyim-company-dabbrev (command &optional arg &rest ignored)
  "`company-mode' dabbrev 补全后端，是 `company-dabbrev'
的中文优化版，通过与 Chinese-pyim 配合来补全中文。

`pyim-company-dabbrev' 可以和 `company-dabbrev' 配合使用。具体细节请
参考 Company-mode group backends 相关文档。"
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'pyim-company-dabbrev))
    (prefix
     (and (featurep 'chinese-pyim)
          ;; 光标前字符是否时汉字？
          (string-match-p "\\cc" (char-to-string (char-before)))
          (string-match-p "\\cc" pyim-current-str)
          pyim-current-str))
    (candidates
     (let* ((case-fold-search company-dabbrev-ignore-case)
            (words (company-dabbrev--search
                    ;; 最多补全六个中文字符，得到太长的中文字符串用处不大。
                    (format "%s[^[:punct:][:blank:]\n]\\{1,6\\}" arg)
                    company-dabbrev-time-limit
                    (pcase company-dabbrev-other-buffers
                      (`t (list major-mode))
                      (`all `all))))
            (downcase-p
             (if (eq company-dabbrev-downcase 'case-replace)
                 case-replace
               company-dabbrev-downcase)))
       (if downcase-p
           (mapcar 'downcase words)
         words)))
    (ignore-case company-dabbrev-ignore-case)
    (duplicates t)))
;; #+END_SRC

;; #+BEGIN_SRC emacs-lisp
(defun pyim-get-predict-words (pinyin word)
  "获取所有词库中以 `word' 开头的中文词条，用于拼音联想输入。
`pinyin' 选项是为了在词库中快速定位，减少搜索时间。"
  (when (and pyim-company-predict-words-number
             (> pyim-company-predict-words-number 0)
             (> (length pinyin) 0)
             (> (length word) 0))
    (let* ((limit pyim-company-predict-words-number)
           (regexp (concat " +\\(" (regexp-quote word) "\\cc+\\)"))
           (count 0)
           predict-words)
      (dolist (buf pyim-buffer-list)
        (with-current-buffer (cdr (assoc "buffer" buf))
          (pyim-bisearch-word pinyin (point-min) (point-max))
          (save-excursion
            (forward-line (- 0 limit))
            (while (and (re-search-forward regexp nil t)
                        (< count (* 2 limit)))
              (setq predict-words (delete-dups
                                   (append predict-words
                                           (list (match-string 1)))))
              (goto-char (match-end 0))
              (setq count (1+ count))))))
      predict-words)))
;; #+END_SRC

;; #+BEGIN_SRC emacs-lisp
(defun pyim-company-predict-words (command &optional arg &rest ignore)
  "`company-mode' 补全后端，只用于 Chinese-pyim 联想词补全，无其他
作用。"
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'pyim-company-backend))
    (prefix
     (and (featurep 'chinese-pyim)
          ;; 光标前字符是否时汉字？
          (string-match-p "\\cc" (char-to-string (char-before)))
          (string-match-p "\\cc" pyim-current-str)
          pyim-current-key
          pyim-current-str))
    (candidates
     (pyim-get-predict-words pyim-current-key
                             pyim-current-str))))
;; #+END_SRC

;;; Footer:
;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim-company)

;; Local Variables:
;; no-byte-compile: t
;; coding: utf-8-unix
;; tab-width: 4
;; indent-tabs-mode: nil
;; lentic-init: lentic-orgel-org-init
;; End:

;;; chinese-pyim.el ends here
;; #+END_SRC
