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
;; 这个文件包含了与 Chinese-pyim 开发相关的配置或者工具，比如：

;; 1. org-webpage config for chinese-pyim

;;; Code:

;; * 代码                                                                 :code:
;; #+BEGIN_SRC emacs-lisp
(require 'chinese-pyim)
(require 'org-webpage)
(require 'owp-web-server)
(require 'owp-lentic)

(defvar pyim-website-repository-directory
  "~/project/emacs-packages/chinese-pyim/")

(owp/add-project-config
 '("chinese-pyim"
   :repository-directory (:eval pyim-website-repository-directory)
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
   :preparation-function owp/lentic-preparation-function
   :org-export-function owp/lentic-org-export-function
   :lentic-doc-sources ("chinese-pyim-.*\\.el$")
   :lentic-readme-sources ("chinese-pyim.el")
   :lentic-index-sources ("chinese-pyim.el")
   :web-server-port 9876))
;; #+END_SRC

;; * Footer

;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim-devtools)

;; Local Variables:
;; no-byte-compile: t
;; End:

;;; chinese-pyim-devtools.el ends here
;; #+END_SRC
