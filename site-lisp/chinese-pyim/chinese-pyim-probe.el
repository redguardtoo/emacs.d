;;; chinese-pyim-probe.el --- Auto-Switch-to-English-Input probes for Chinese-pyim

;; * Header
;; Copyright 2015 Feng Shu

;; Author: Feng Shu <tumashu@163.com>
;; URL: https://github.com/tumashu/chinese-pyim

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

;; * 使用说明                                                              :doc:
;; ** 简介
;; 这个文件包含了许多探针函数，用于实现两个功能：

;; 1. 根据环境自动切换到英文输入模式
;; 2. 根据环境自动切换到半角标点输入模式

;; ** 设置
;; *** 根据环境自动切换到英文输入模式
;; 用户将探针函数添加到 `pyim-english-input-switch-functions' 后, 就可以激活这个
;; 探针函数，比如：

;; #+BEGIN_EXAMPLE
;; (setq-default pyim-english-input-switch-functions
;;               '(pyim-probe-dynamic-english
;;                 pyim-probe-isearch-mode
;;                 pyim-probe-program-mode))
;; #+END_EXAMPLE

;; 只要上述 *函数列表* 中，任意一个函数返回值为 t, Chinese-pyim 就自动切换到
;; 英文输入模式。

;; *** 根据环境自动切换到半角标点输入模式
;; 用户将探针函数添加到 `pyim-punctuation-half-width-functions' 后, 就可以激活这个
;; 探针函数。

;;; Code:
;; * 代码                                                                 :code:
;; ** 根据环境自动切换到英文输入模式
;; #+BEGIN_SRC emacs-lisp
(defun pyim-probe-program-mode ()
  "激活这个 Chinese-pyim 探针函数后，只能在字符串和 comment 中输入中文。
注：仅仅影响 `prog-mode' 衍生的 mode 。

用于：`pyim-english-input-switch-functions' 。"
  (interactive)
  (when (derived-mode-p 'prog-mode)
    (let* ((pos (point))
           (ppss (syntax-ppss pos)))
      (not
       (or (car (setq ppss (nthcdr 3 ppss)))
           (car (setq ppss (cdr ppss)))
           (nth 3 ppss))))))

(defun pyim-probe-org-speed-commands ()
  "激活这个 Chinese-pyim 探针函数后，可以解决 org-speed-commands 与 Chinese-pyim 冲突问题。

用于：`pyim-english-input-switch-functions' 。"
  (and (string= major-mode "org-mode")
       (bolp)
       (looking-at org-heading-regexp)
       org-use-speed-commands))

(defun pyim-probe-isearch-mode ()
  "激活这个 Chinese-pyim 探针函数后，使用 isearch 搜索时，禁用中文输入，强制英文输入。

用于：`pyim-english-input-switch-functions' 。"
  (and pyim-isearch-enable-pinyin-search
       ;; isearch 启动的时候，会设置一个 buffer variable: `isearch-mode'
       ;; 检测所有 buffer 中 `isearch-mode' 的取值，如果任何一个
       ;; 取值为 t, 就说明 isearch 已经启动。
       (cl-some #'(lambda (buf)
                    (buffer-local-value 'isearch-mode buf))
                (buffer-list))))

(defun pyim-probe-org-structure-template ()
  "激活这个 Chinese-pyim 探针函数后，输入 org-structure-template 时，不会开启中文输入。

用于：`pyim-english-input-switch-functions' 。"
  (when (eq major-mode 'org-mode)
    (let ((line-string (buffer-substring (point-at-bol) (point))))
      (and (looking-at "[ \t]*$")
           (string-match "^[ \t]*<\\([a-zA-Z]*\\)$" line-string)))))

(defun pyim-probe-dynamic-english ()
  "激活这个 Chinese-pyim 探针函数后，使用下面的规则动态切换中英文输入：

1. 当前字符为中文字符时，输入下一个字符时默认开启中文输入
2. 当前字符为其他字符时，输入下一个字符时默认开启英文输入
3. 使用 `pyim-convert-pinyin-at-point' 可以将光标前的拼音字符串转换为中文，
   所以用户需要给 `pyim-convert-pinyin-at-point' 绑定一个快捷键，比如：

   #+BEGIN_SRC elisp
   (global-set-key (kbd \"M-i\") 'pyim-convert-pinyin-at-point)
   #+END_SRC

这个函数用于：`pyim-english-input-switch-functions' 。"
  (let ((str-before-1 (pyim-char-before-to-string 0)))
    (unless (string= (buffer-name) " *temp*") ; Make sure this probe can work with exim of exwm.
      (if (<= (point) (save-excursion (back-to-indentation)
				      (point)))
	  (not (or (pyim-string-match-p "\\cc" (save-excursion
						 ;; 查找前一个非空格字符。
						 (if (re-search-backward "[^[:space:]\n]" nil t)
						     (char-to-string (char-after (point))))))
		   (> (length pyim-current-key) 0)))
	(not (or (pyim-string-match-p "\\cc" str-before-1)
		 (> (length pyim-current-key) 0)))))))
;; #+END_SRC

;; ** 根据环境自动切换到半角标点输入模式
;; #+BEGIN_SRC emacs-lisp
(defun pyim-probe-punctuation-line-beginning (char)
  "激活这个 Chinese-pyim 探针函数后，行首输入标点时，强制输入半角标点。

用于：`pyim-punctuation-half-width-functions' 。"
  (let ((line-string (buffer-substring (point-at-bol) (point))))
    (unless (string= (buffer-name) " *temp*") ; Make sure this probe can work with exim of exwm.
      (and (member (char-to-string char)
                   (mapcar 'car pyim-punctuation-dict))
           (string-match "^[ \t]*$" line-string)))))

(defun pyim-probe-punctuation-after-punctuation (char)
  "激活这个 Chinese-pyim 探针函数后，半角标点后再输入一个标点符号时，强制输入半角标点。

用于：`pyim-punctuation-half-width-functions' 。"
  (let ((str-before-1 (pyim-char-before-to-string 0))
        (puncts (mapcar 'car pyim-punctuation-dict)))
    (and (member str-before-1 puncts)
         (member (char-to-string char) puncts))))
;; #+END_SRC

;; * Footer
;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim-probe)

;;; chinese-pyim-probe.el ends here
;; #+END_SRC
