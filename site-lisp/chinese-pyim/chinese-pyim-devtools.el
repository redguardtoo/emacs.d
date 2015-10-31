;;; chinese-pyim-devtools.el --- Tools for Chinese-pyim developers

;; * Header
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

;; * 说明文档                                                              :doc:
;; 这个文件包含了 Chinese-pyim 开发相关的命令，比如：
;; 1. 生成 GitHub README
;; 2. 生成代码 html 文档
;; 3. 其它


;;; Code:

;; * 代码                                                                 :code:
;; ** 加载必要的库文件
;; #+BEGIN_SRC emacs-lisp
(require 'chinese-pyim)
(require 'org-webpage)
(require 'owp-web-server)
(require 'lentic)
(require 'lentic-org)
(require 'lentic-doc)
(require 'ox-gfm)
(require 'ox-org)
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

(defun pyim-devtools-org-preprocess (backend)
  "This function delete useless string."
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^;;; +Commentary:.*" nil t)
      (replace-match "" nil t))
    (goto-char (point-min))
    (while (re-search-forward "^;;; +Code:.*" nil t)
      (replace-match "" nil t))))
;; #+END_SRC

;; ** 用于生成 chinese-pyim 相关文档的命令
;; 1. 生成 Github README
;; 2. 生成 Chinese-pyim 代码的说明文档（html文档），帮助开发者理解代码。

;; #+BEGIN_SRC emacs-lisp
(defvar pyim-website-repository-directory
  "~/project/emacs-packages/chinese-pyim/")

(defun pyim-website-update-owp-config ()
  (interactive)
  (add-to-list
   'owp/project-config-alist
   `("chinese-pyim"
     :repository-directory ,pyim-website-repository-directory
     :remote (git "https://github.com/tumashu/chinese-pyim.git" "gh-pages")
     :site-domain "http://tumashu.github.com/chinese-pyim"
     :site-main-title "Chinese-pyim"
     :site-sub-title "(一个 emacs 环境下的中文拼音输入法)"
     :default-category "documents"
     :theme (worg killjs)
     :force-absolute-url t
     :source-browse-url ("GitHub" "https://github.com/tumashu/chinese-pyim")
     :personal-avatar "/media/img/horse.jpg"
     :personal-duoshuo-shortname "tumashu-website"
     :preparation-function pyim-preparation-org-files
     :org-export-function pyim-org-export-function
     :web-server-port 9876)))

(pyim-website-update-owp-config)

(defun pyim-devtools-generate-readme-and-index ()
  (interactive)
  (let* ((el-file (concat (file-name-as-directory
                           pyim-website-repository-directory)
                          "/chinese-pyim.el"))
         (org-file (concat (file-name-sans-extension el-file) ".org"))
         (el-file-buffer (get-file-buffer el-file))
         (org-file-buffer (get-file-buffer org-file)))
    (when el-file-buffer
      (kill-buffer el-file-buffer))
    (when org-file-buffer
      (kill-buffer org-file-buffer))
    (lentic-doc-orgify-if-necessary el-file)
    (if (file-exists-p org-file)
        (with-current-buffer (find-file-noselect org-file)
          (let ((org-export-filter-paragraph-functions '(pyim-devtools-org-clean-space))
                (org-export-before-processing-hook '(pyim-devtools-org-preprocess))
                (org-export-select-tags '("README"))
                (indent-tabs-mode nil)
                (tab-width 4))
            (org-export-to-file 'gfm "README.md")
            (org-export-to-file 'org "index.org")))
      (message "Generate README fail!!!"))))

(defun pyim-org-export-function ()
  "A function with can export org file to html."
  (let ((org-export-before-processing-hook
         '(pyim-devtools-org-preprocess))
        (org-export-filter-paragraph-functions
         '(pyim-devtools-org-clean-space))
        (org-export-select-tags '("README" "devel" "doc" "code"))
        (indent-tabs-mode nil)
        (tab-width 4))
    (org-export-as 'html nil nil t nil)))

(defun pyim-orgify-if-necessary (file)
  (let* ((target (concat
                  (file-name-sans-extension file)
                  ".org"))
         (locked (or (file-locked-p file)
                     (file-locked-p target)))
         (open (or (get-file-buffer file)
                   (get-file-buffer target))))
    (unless (or locked open)
      (when (file-newer-than-file-p file target)
        (let ((lentic-kill-retain t))
          (lentic-batch-clone-and-save-with-config
           file 'lentic-el2org-init))))))

(defun pyim-preparation-org-files ()
  "Generate org files by lentic."
  (message "Generating org files by lentic ...")
  (let ((el-files (directory-files pyim-website-repository-directory t "\\.el$")))
    (mapc #'(lambda (el-file)
              (let* ((org-file (concat (file-name-sans-extension el-file) ".org"))
                     (el-buffer (get-file-buffer el-file))
                     (org-buffer (get-file-buffer org-file)))
                (when el-buffer
                  (kill-buffer el-buffer))
                (when org-buffer
                  (kill-buffer org-buffer)))
              (pyim-orgify-if-necessary el-file))
          el-files))
  (pyim-devtools-generate-readme-and-index))
;; #+END_SRC

;; * Footer

;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim-devtools)

;; Local Variables:
;; no-byte-compile: t
;; coding: utf-8-unix
;; tab-width: 4
;; indent-tabs-mode: nil
;; lentic-init: lentic-el2org-init
;; End:

;;; chinese-pyim-devtools.el ends here
;; #+END_SRC
