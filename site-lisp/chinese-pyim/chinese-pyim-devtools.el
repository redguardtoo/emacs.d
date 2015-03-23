;;; chinese-pyim-devtools.el --- Tools for Chinese-pyim developers

;;; Header:
;; Copyright 2015 Feng Shu

;; Author: Feng Shu <tumashu@163.com>
;; URL: https://github.com/tumashu/chinese-pyim
;; Version: 0.0.1
;; Keywords: convenience, Chinese, pinyin, input-method

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
;; 这个文件包含开发 Chinese-pyim 时需要的函数和命令。

;;; Code:

;; ** 加载必要的库文件
;; #+BEGIN_SRC emacs-lisp
(require 'chinese-pyim)
(require 'org)
(require 'org-table)
(require 'ox-publish)
(require 'ox-html)
(require 'lentic)
(require 'lentic-org)
(require 'lentic-doc)
(require 'ox-gfm)
;; #+END_SRC

;; ** 定义一个 org 导出过滤器，处理中文文档中的多余空格
;; 当本文档导出为 README 文档时，中文与中文之间的回车符会转化为空格符，对于中文而言，
;; 这些空格这是多余的，这里定义了一个导出过滤器，当 org 文件导出为 html 以及 markdown
;; 格式时，自动删除中文与中文之间不必要的空格。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-devtools-org-clean-space (text backend info)
  "在export为HTML时，删除中文之间不必要的空格"
  (when (org-export-derived-backend-p backend 'html)
    (let ((regexp "[[:multibyte:]]")
          (string text))
      ;; org默认将一个换行符转换为空格，但中文不需要这个空格，删除。
      (setq string
            (replace-regexp-in-string
             (format "\\(%s\\) *\n *\\(%s\\)" regexp regexp)
             "\\1\\2" string))
      ;; 删除粗体之前的空格
      (setq string
            (replace-regexp-in-string
             (format "\\(%s\\) +\\(<\\)" regexp)
             "\\1\\2" string))
      ;; 删除粗体之后的空格
      (setq string
            (replace-regexp-in-string
             (format "\\(>\\) +\\(%s\\)" regexp)
             "\\1\\2" string))
      string)))

;; #+END_SRC

;; ** 用于生成 chinese-pyim 相关文档的命令
;; 1. 生成 Github README
;; 2. 生成 Chinese-pyim 代码的说明文档（html文档），帮助开发者理解代码。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-devtools-generate-documents ()
  (interactive)
  (pyim-devtools-generate-readme-document)
  (pyim-devtools-generate-devel-document))

(defun pyim-devtools-generate-readme-document ()
  (interactive)
  (lentic-doc-orgify-package 'chinese-pyim)
  (with-current-buffer
      (find-file-noselect
       (concat (f-parent (locate-library (symbol-name 'chinese-pyim)))
               "/chinese-pyim.org"))
    (let ((org-export-filter-paragraph-functions '(pyim-devtools-org-clean-space))
          (org-export-select-tags '("README"))
          (indent-tabs-mode nil)
          (tab-width 4))
      (org-export-to-file 'gfm "README.md"))))

(defun pyim-devtools-generate-devel-document ()
  (interactive)
  (lentic-doc-orgify-package 'chinese-pyim)
  (let* ((directory (f-parent (locate-library (symbol-name 'chinese-pyim))))
         (org-export-filter-paragraph-functions '(pyim-devtools-org-clean-space))
         (indent-tabs-mode nil)
         (tab-width 4)
         (org-publish-project-alist
          `(("chinese-pyim-doc"
             :base-directory ,directory
             :base-extension "org"
             :select-tags ("devel")
             :exclude "autoloads"
             :with-toc t
             :makeindex nil
             :auto-sitemap nil
             :sitemap-ignore-case t
             :html-extension "html"
             :publishing-directory ,directory
             :publishing-function (org-html-publish-to-html)
             :headline-levels 7
             :auto-preamble t
             :htmlized-source nil
             :section-numbers t
             :table-of-contents t
             :recursive t))))
    (org-publish-project "chinese-pyim-doc" t)
    (copy-file "chinese-pyim.html" "index.html" t)))

(defvar pyim-devtools-devel-document-file
  (concat
   (f-parent
    (locate-library "chinese-pyim.el"))
   "/chinese-pyim.html"))

;;;###autoload
(defun pyim-devtools-view-devel-document ()
  (interactive)
  (pyim-devtools-generate-documents)
  (browse-url-of-file pyim-devtools-devel-document-file))
;; #+END_SRC

;;; Footer:
;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim-devtools)

;; Local Variables:
;; no-byte-compile: t
;; coding: utf-8-unix
;; tab-width: 4
;; indent-tabs-mode: nil
;; lentic-init: lentic-orgel-org-init
;; End:

;;; chinese-pyim-devtools.el ends here
;; #+END_SRC
