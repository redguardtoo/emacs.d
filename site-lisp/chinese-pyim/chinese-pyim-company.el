;;; chinese-pyim-company.el --- Integrate company-mode with Chinese-pyim

;; * Header
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

;; * 说明文档                                                           :doc:
;; 通过 Chinese-pyim 让 Company-dabbrev 更好的处理中文。

;; 1. 配置 company-mode, 具体可以参考：[[https://github.com/tumashu/emacs-helper/blob/master/eh-complete.el][emacs-helper's company configure]]
;; 2. 配置 chinese-pyim-company
;;    #+BEGIN_EXAMPLE
;;    (require 'chinese-pyim-company)
;;    (setq pyim-company-max-length 6)
;;    #+END_EXAMPLE

;;; Code:

;; * 代码                                                               :code:
;; ** Require + defcustom
;; #+BEGIN_SRC emacs-lisp
(require 'chinese-pyim)
(require 'company)
(require 'company-dabbrev)

(defcustom pyim-company-complete-chinese-enable t
  "设置 Company 是否补全中文"
  :group 'chinese-pyim)

(defcustom pyim-company-max-length 6
  "这个用来设置 Company 补全中文时，候选中文词条的最大长度。"
  :group 'chinese-pyim)
;; #+END_SRC

;; 判断 Company-mode 是否在补全中文，如果光标前的一个字符为中文字符
;; 则返回 `t', 反之，返回 nil.
;; #+BEGIN_SRC emacs-lisp
(defun pyim-company-chinese-complete-p ()
  (let ((string (pyim-char-before-to-string 0)))
    (pyim-string-match-p "\\cc" string)))
;; #+END_SRC

;; `company-dabbrev' 补全命令的简单流程是：
;; 1. 提取光标前的一个字符串，作为搜索的 `prefix',
;;    具体细节见： `company-grab-word'
;; 2. 对 `prefix' 进行进一步处理，生成一个搜索用的 `regexp'.
;;    具体细节见： `company-dabbrev--make-regexp'
;; 3. 使用生成的 `regexp' 搜索特定的 buffer.
;; 4. 将搜索得到的结果进行处理，生成一个候选词条的 `list'.
;;    具体细节见： `company-dabbrev--search'
;; 5. 使用菜单显示

;; 中文和英文的书写习惯有很大的不同，对 company-mode 影响最大的一条是：

;; #+BEGIN_EXAMPLE
;; 中文的词语与词语之间没有 *强制* 的用空格隔开，
;; #+END_EXAMPLE

;; 这个书写习惯影响上面三个函数的 *正常* 运行。

;; ** 让 company-grab-word 正确的处理中文

;; `company-grab-word' 可以获取光标处的一个英文词语，但只能获取
;; 光标处的一个 *中文句子* ，使用一个句子来搜索，得到的备选词条往往很少，
;; 并且用处不大（很少人在一篇文章中重复的写一个句子）。

;; 这里为 `company-grab-word' 添加了一个 advice: 当 company-dabbrev 补全中文时，
;; 用 `pyim-grab-chinese-word' 函数获取光标前的一个 *中文词条* ，如果获取失败，
;; 则返回光标前的 *中文字符* 。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-company-grab-word (orig-fun)
  (if (pyim-company-chinese-complete-p)
      (when pyim-company-complete-chinese-enable
        (or (pyim-grab-chinese-word)
            (pyim-char-before-to-string 0)))
    (funcall orig-fun)))
;; #+END_SRC

;; ** 让 pyim-company-dabbrev--make-regexp 生成合适中文搜索的 regexp

;; 用 `pyim-company-dabbrev--make-regexp' 得到的 regexp, 搜索中文时，会搜索到一个
;; *中文句子* ， 不太实用，这里添加了一个 advice:

;; 当 company-dabbrev 补全中文时，将搜索得到的结果截取前 `pyim-company-max-length' 个字符，
;; 默认为6个，这对中文而言应该够用了。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-company-dabbrev--make-regexp (orig-fun)
  (if (pyim-company-chinese-complete-p)
      (format "[^[:punct:][:blank:]\n]\\{1,%s\\}" pyim-company-max-length)
    (funcall orig-fun)))
;; #+END_SRC

;; ** TODO 让 pyim-company-dabbrev--search 更好的处理中文

;; 本来打算在这个地方对 *候选词条列表* 做一些筛选，比如，用 Chinese-pyim 自带
;; 的分词函数对候选词条进行分词，然后只提取第一个 *有效* 的中文词语，但由于
;; 分词函数速度太慢，导致补全时卡顿明显，所以暂时没有这么处理。


;; #+BEGIN_SRC emacs-lisp
(defun pyim-company-dabbrev--search (orig-fun regexp &optional limit other-buffer-modes
                                              ignore-comments)
  (if (pyim-company-chinese-complete-p)
      (when pyim-company-complete-chinese-enable
        (funcall orig-fun regexp limit other-buffer-modes ignore-comments))
    (funcall orig-fun regexp limit other-buffer-modes ignore-comments)))
;; #+END_SRC


;; #+BEGIN_SRC emacs-lisp
(advice-add 'company-grab-word :around #'pyim-company-grab-word)
(advice-add 'company-dabbrev--make-regexp :around #'pyim-company-dabbrev--make-regexp)
(advice-add 'company-dabbrev--search :around #'pyim-company-dabbrev--search)
;; #+END_SRC

;; * Footer

;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim-company)

;; Local Variables:
;; no-byte-compile: t
;; End:

;;; chinese-pyim.el ends here
;; #+END_SRC
