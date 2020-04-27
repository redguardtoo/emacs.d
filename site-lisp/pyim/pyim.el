;;; pyim.el --- A Chinese input method support quanpin, shuangpin, wubi and cangjie.

;; * Header
;; Copyright 2006 Ye Wenbin
;;           2014-2019 Feng Shu

;; Author: Ye Wenbin <wenbinye@163.com>
;;         Feng Shu <tumashu@163.com>
;; URL: https://github.com/tumashu/pyim
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

;; * pyim 使用说明                                          :README:doc:
;; ** 截图
;; [[./snapshots/pyim-linux-x-with-toolkit.png]]

;; ** 简介
;; pyim 是 Emacs 环境下的一个中文输入法，最初它只支持全拼输入，所以当时
;; "pyim" 代表 "Chinese Pinyin Input Method" 的意思，后来根据同学的提议，
;; 添加了五笔的支持，再叫 “拼音输入法” 就不太合适了，所以你现在可以将它理解
;; 为 “PengYou input method”： 平时像朋友一样帮助你，偶尔也像朋友一样犯二 。。。

;; ** 背景
;; pyim 的代码源自 emacs-eim。

;; emacs-eim 是 Emacs 环境下的一个中文输入法框架， 支持拼音，五笔，仓颉以及二笔等
;; 多种输入法，但遗憾的是，2008 年之后它就停止了开发，我认为主要原因是外部中文输入法快速发展。

;; 虽然外部输入法功能强大，但不能和 Emacs 默契的配合，这一点极大的损害了 Emacs 那种 *行云流水*
;; 的感觉。而本人在使用（或者叫折腾） emacs-eim 的过程中发现：

;; 1. *当 emacs-eim 词库词条超过 100 万时，选词频率大大降低，中文体验增强。*
;; 3. *随着使用时间的延长，emacs-eim 会越来越好用（个人词库的积累）。*

;; 于是我 fork 了 emacs-eim 输入法的部分代码, 创建了一个项目：pyim。

;; ** 目标
;; pyim 的目标是： *尽最大的努力成为一个好用的 Emacs 中文输入法* ，
;; 具体可表现为三个方面：

;; 1. Fallback:     当外部输入法不能使用时，比如在 console 或者 cygwin 环境
;;    下，尽最大可能让 Emacs 用户不必为输入中文而烦恼。
;; 2. Integration:  尽最大可能减少输入法切换频率，让中文输入不影响 Emacs
;;    的体验。
;; 3. Exchange:     尽最大可能简化 pyim 使用其他优秀输入法的词库
;;    的难度和复杂度。

;; ** 特点
;; 1. pyim 支持全拼，双拼，五笔和仓颉，其中对全拼的支持最好。
;; 2. pyim 通过添加词库的方式优化输入法。
;; 3. pyim 使用文本词库格式，方便处理。

;; ** 安装
;; 1. 配置 melpa 源，参考：http://melpa.org/#/getting-started
;; 2. M-x package-install RET pyim RET
;; 3. 在 Emacs 配置文件中（比如: ~/.emacs）添加如下代码：
;;    #+BEGIN_EXAMPLE
;;    (require 'pyim)
;;    (require 'pyim-basedict) ; 拼音词库设置，五笔用户 *不需要* 此行设置
;;    (pyim-basedict-enable)   ; 拼音词库，五笔用户 *不需要* 此行设置
;;    (setq default-input-method "pyim")
;;    #+END_EXAMPLE

;; ** 配置

;; *** 配置实例
;; 对 pyim 感兴趣的同学，可以看看本人的 pyim 配置（总是适用于最新版的 pyim）:

;; #+BEGIN_EXAMPLE
;; (use-package pyim
;;   :ensure nil
;;   :demand t
;;   :config
;;   ;; 激活 basedict 拼音词库，五笔用户请继续阅读 README
;;   (use-package pyim-basedict
;;     :ensure nil
;;     :config (pyim-basedict-enable))

;;   (setq default-input-method "pyim")

;;   ;; 我使用全拼
;;   (setq pyim-default-scheme 'quanpin)

;;   ;; 设置 pyim 探针设置，这是 pyim 高级功能设置，可以实现 *无痛* 中英文切换 :-)
;;   ;; 我自己使用的中英文动态切换规则是：
;;   ;; 1. 光标只有在注释里面时，才可以输入中文。
;;   ;; 2. 光标前是汉字字符时，才能输入中文。
;;   ;; 3. 使用 M-j 快捷键，强制将光标前的拼音字符串转换为中文。
;;   (setq-default pyim-english-input-switch-functions
;;                 '(pyim-probe-dynamic-english
;;                   pyim-probe-isearch-mode
;;                   pyim-probe-program-mode
;;                   pyim-probe-org-structure-template))

;;   (setq-default pyim-punctuation-half-width-functions
;;                 '(pyim-probe-punctuation-line-beginning
;;                   pyim-probe-punctuation-after-punctuation))

;;   ;; 开启拼音搜索功能
;;   (pyim-isearch-mode 1)

;;   ;; 使用 popup-el 来绘制选词框, 如果用 emacs26, 建议设置
;;   ;; 为 'posframe, 速度很快并且菜单不会变形，不过需要用户
;;   ;; 手动安装 posframe 包。
;;   (setq pyim-page-tooltip 'popup)

;;   ;; 选词框显示5个候选词
;;   (setq pyim-page-length 5)

;;   :bind
;;   (("M-j" . pyim-convert-string-at-point) ;与 pyim-probe-dynamic-english 配合
;;    ("C-;" . pyim-delete-word-from-personal-buffer)))
;; #+END_EXAMPLE

;; *** 添加词库文件
;; pyim 当前的默认的拼音词库是 pyim-basedict, 这个词库的词条量
;; 8 万左右，是一个 *非常小* 的拼音词库，词条的来源有两个：

;; 1. libpinyin 项目的内置词库
;; 2. pyim 用户贡献的个人词库

;; 如果 pyim-basedict 不能满足需求，用户可以使用其他方式为 pyim 添加拼音词库，
;; 具体方式请参考 [[如何添加自定义拼音词库]] 小结。

;; *** 激活 pyim

;; #+BEGIN_EXAMPLE
;; (setq default-input-method "pyim")
;; (global-set-key (kbd "C-\\") 'toggle-input-method)
;; #+END_EXAMPLE

;; ** 使用
;; *** 常用快捷键
;; | 输入法快捷键          | 功能                       |
;; |-----------------------+----------------------------|
;; | C-n 或 M-n 或 + 或 .  | 向下翻页                   |
;; | C-p 或 M-p 或 - 或 ,  | 向上翻页                   |
;; | C-f                   | 选择下一个备选词           |
;; | C-b                   | 选择上一个备选词           |
;; | SPC                   | 确定输入                   |
;; | RET 或 C-m            | 字母上屏                   |
;; | C-c                   | 取消输入                   |
;; | C-g                   | 取消输入并保留已输入的中文 |
;; | TAB                   | 模糊音调整                 |
;; | DEL 或 BACKSPACE      | 删除最后一个字符           |
;; | C-DEL 或  C-BACKSPACE | 删除最后一个拼音           |
;; | M-DEL 或  M-BACKSPACE | 删除最后一个拼音           |

;; *** 使用双拼模式
;; pyim 支持双拼输入模式，用户可以通过变量 `pyim-default-scheme' 来设定：

;; #+BEGIN_EXAMPLE
;; (setq pyim-default-scheme 'pyim-shuangpin)
;; #+END_EXAMPLE

;; 注意：
;; 1. pyim 支持微软双拼（microsoft-shuangpin）和小鹤双拼（xiaohe-shuangpin）。
;; 2. 用户可以使用变量 `pyim-schemes' 添加自定义双拼方案。
;; 3. 用户可能需要重新设置 `pyim-translate-trigger-char'。

;; *** 通过 pyim 来支持 rime 所有输入法

;; 1. 安裝配置 liberime 和 pyim, 方式见：[[https://github.com/merrickluo/liberime][liberime]].
;; 2. 将 liberime 的 page_size 设置为 100, 这样 pyim 一次可以获取 100
;;    个候选词，然后自己处理分页。用户可以按 TAB 键切换到辅助输入
;;    法来输入 100 以后的词条。

;;    手动设置方式是： 在 `liberime-user-data-dir'/default.custom.yaml
;;    文件中添加类似下面的内容：

;;    #+BEGIN_EXAMPLE
;;    patch:
;;         "menu/page_size": 100
;;         "speller/auto_select": false
;;         "speller/auto_select_unique_candidate": false
;;    #+END_EXAMPLE

;; 3. 使用 rime 全拼输入法的用户，也可以使用 rime-quanpin scheme,
;;    这个 scheme 是专门针对 rime 全拼输入法定制的，支持全拼v快捷键。
;;    #+BEGIN_EXAMPLE
;;    (setq pyim-default-scheme 'rime-quanpin)
;;    #+END_EXAMPLE
;; 4. 如果通过 rime 使用微软双拼，可以用以下设置：
;;    #+BEGIN_EXAMPLE
;;    (liberime-select-schema "double_pinyin_mspy")
;;    (setq pyim-default-scheme 'rime-microsoft-shuangpin)
;;    #+END_EXAMPLE
;;    默认是用繁体中文，想要改成简体中文的话，可以参考 [[https://github.com/rime/home/wiki/CustomizationGuide#%E4%B8%80%E4%BE%8B%E5%AE%9A%E8%A3%BD%E7%B0%A1%E5%8C%96%E5%AD%97%E8%BC%B8%E5%87%BA][rime wiki]]，或者[[http://wenshanren.org/?p=1070#orgc7dbd8e][这篇博客]]
;; *** 使用五笔输入
;; pyim 支持五笔输入模式，用户可以通过变量 `pyim-default-scheme' 来设定：

;; #+BEGIN_EXAMPLE
;; (setq pyim-default-scheme 'wubi)
;; #+END_EXAMPLE

;; 在使用五笔输入法之前，请用 pyim-dicts-manager 添加一个五笔词库，词库的格式类似：

;; #+BEGIN_EXAMPLE
;;; -*- coding: utf-8-unix -*-
;; .aaaa 工
;; .aad 式
;; .aadk 匿
;; .aadn 慝 葚
;; .aadw 萁
;; .aafd 甙
;; .aaff 苷
;; .aaht 芽
;; .aak 戒
;; #+END_EXAMPLE

;; 最简单的方式是从 melpa 中安装 pyim-wbdict 包，然后根据它的
;; [[https://github.com/tumashu/pyim-wbdict][README]] 来配置。

;; 另外 Ye FeiYu 同学维护着 pyim-wbdict 的一个 fork, 里面包含着极点
;; 五笔和清歌五笔的词库，不做发布，有兴趣的同学可以了解一下：

;;     https://github.com/yefeiyu/pyim-wbdict

;; 如果用户在使用五笔输入法的过程中，忘记了某个字的五笔码，可以按 TAB
;; 键临时切换到辅助输入法来输入，选词完成之后自动退出。辅助输入法可以
;; 通过 `pyim-assistant-scheme' 来设置。

;; *** 使用仓颉输入法
;; pyim 支持仓颉输入法，用户可以通过变量 `pyim-default-scheme' 来设定：

;; #+BEGIN_EXAMPLE
;; (setq pyim-default-scheme 'cangjie)
;; #+END_EXAMPLE

;; 在使用仓颉输入法之前，请用 pyim-dicts-manager 添加一个仓颉词库，词库的格式类似：

;; #+BEGIN_EXAMPLE
;;; -*- coding: utf-8-unix -*-
;; @a 日
;; @a 曰
;; @aa 昌
;; @aa 昍
;; @aaa 晶
;; @aaa 晿
;; @aaah 曑
;; #+END_EXAMPLE

;; 如果用户使用仓颉第五代，最简单的方式是从 melpa 中安装 pyim-cangjie5dict 包，
;; 然后根据它的 [[https://github.com/erstern/pyim-cangjie5dict][README]] 来配置。
;; pyim 支持其它版本的仓颉，但需要用户自己创建词库文件。

;; 用户可以使用命令：`pyim-search-word-code' 来查询当前选择词条的仓颉编码

;; *** 让选词框跟随光标
;; 用户可以通过下面的设置让 pyim 在 *光标处* 显示一个选词框：

;; 1. 使用 popup 包来绘制选词框 （emacs overlay 机制）
;;    #+BEGIN_EXAMPLE
;;    (setq pyim-page-tooltip 'popup)
;;    #+END_EXAMPLE
;; 2. 使用 posframe 来绘制选词框
;;    #+BEGIN_EXAMPLE
;;    (setq pyim-page-tooltip 'posframe)
;;    #+END_EXAMPLE
;;    注意：pyim 不会自动安装 posframe, 用户需要手动安装这个包，

;; *** 调整 tooltip 选词框的显示样式
;; pyim 的 tooltip 选词框默认使用 *双行显示* 的样式，在一些特
;; 殊的情况下（比如：popup 显示的菜单错位），用户可以使用 *单行显示*
;; 的样式：

;; #+BEGIN_EXAMPLE
;; (setq pyim-page-style 'one-line)
;; #+END_EXAMPLE

;; 注：用户可以添加函数 pyim-page-style:STYLENAME 来定义自己的选词框格式。

;; *** 设置模糊音
;; 可以通过设置 `pyim-fuzzy-pinyin-alist' 变量来自定义模糊音。

;; *** 使用魔术转换器
;; 用户可以将待选词条作 “特殊处理” 后再 “上屏”，比如 “简体转繁体” 或者
;; “输入中文，上屏英文” 之类的。

;; 用户需要设置 `pyim-magic-converter', 比如：下面这个例子实现，
;; 输入 “二呆”，“一个超级帅的小伙子” 上屏 :-)
;; #+BEGIN_EXAMPLE
;; (defun my-converter (string)
;;   (if (equal string "二呆")
;;       "“一个超级帅的小伙子”"
;;     string))
;; (setq pyim-magic-converter #'my-converter)
;; #+END_EXAMPLE

;; *** 切换全角标点与半角标点

;; 1. 第一种方法：使用命令 `pyim-punctuation-toggle'，全局切换。
;;    这个命令主要用来设置变量： `pyim-punctuation-translate-p', 用户也可以
;;    手动设置这个变量， 比如：
;;    #+BEGIN_EXAMPLE
;;    (setq pyim-punctuation-translate-p '(yes no auto))   ;使用全角标点。
;;    (setq pyim-punctuation-translate-p '(no yes auto))   ;使用半角标点。
;;    (setq pyim-punctuation-translate-p '(auto yes no))   ;中文使用全角标点，英文使用半角标点。
;;    #+END_EXAMPLE
;; 2. 第二种方法：使用命令 `pyim-punctuation-translate-at-point' 只切换光
;;    标处标点的样式。
;; 3. 第三种方法：设置变量 `pyim-translate-trigger-char' ，输入变量设定的
;;    字符会切换光标处标点的样式。

;; *** 手动加词和删词

;; 1. `pyim-create-Ncchar-word-at-point 这是一组命令，从光标前提取N个汉
;;    字字符组成字符串，并将其加入个人词库。
;; 2. `pyim-translate-trigger-char' 以默认设置为例：在“我爱吃红烧肉”后输
;;    入“5v” 可以将“爱吃红烧肉”这个词条保存到用户个人词库。
;; 3. `pyim-create-word-from-selection', 选择一个词条，运行这个命令后，就
;;    可以将这个词条添加到个人词库。
;; 4. `pyim-delete-word' 从个人词库中删除当前高亮选择的词条。

;; *** pyim 高级功能
;; 1. 根据环境自动切换到英文输入模式，使用 pyim-english-input-switch-functions 配置。
;; 2. 根据环境自动切换到半角标点输入模式，使用 pyim-punctuation-half-width-functions 配置。

;; 注意：上述两个功能使用不同的变量设置， *千万不要搞错* 。

;; **** 根据环境自动切换到英文输入模式

;; | 探针函数                          | 功能说明                                                                          |
;; |-----------------------------------+-----------------------------------------------------------------------------------|
;; | pyim-probe-program-mode           | 如果当前的 mode 衍生自 prog-mode，那么仅仅在字符串和 comment 中开启中文输入模式   |
;; |-----------------------------------+-----------------------------------------------------------------------------------|
;; | pyim-probe-org-speed-commands     | 解决 org-speed-commands 与 pyim 冲突问题                                          |
;; | pyim-probe-isearch-mode           | 使用 isearch 搜索时，强制开启英文输入模式                                         |
;; |                                   | 注意：想要使用这个功能，pyim-isearch-mode 必须激活                                |
;; |-----------------------------------+-----------------------------------------------------------------------------------|
;; | pyim-probe-org-structure-template | 使用 org-structure-template 时，关闭中文输入模式                                  |
;; |-----------------------------------+-----------------------------------------------------------------------------------|
;; |                                   | 1. 当前字符为中文字符时，输入下一个字符时默认开启中文输入                         |
;; | pyim-probe-dynamic-english        | 2. 当前字符为其他字符时，输入下一个字符时默认开启英文输入                         |
;; |                                   | 3. 使用命令 pyim-convert-string-at-point 可以将光标前的拼音字符串强制转换为中文。   |
;; |-----------------------------------+-----------------------------------------------------------------------------------|

;; 激活方式：

;; #+BEGIN_EXAMPLE
;; (setq-default pyim-english-input-switch-functions
;;               '(probe-function1 probe-function2 probe-function3))
;; #+END_EXAMPLE

;; 注：上述函数列表中，任意一个函数的返回值为 t 时，pyim 切换到英文输入模式。

;; **** 根据环境自动切换到半角标点输入模式

;; | 探针函数                                 | 功能说明                   |
;; |------------------------------------------+----------------------------|
;; | pyim-probe-punctuation-line-beginning    | 行首强制输入半角标点       |
;; |------------------------------------------+----------------------------|
;; | pyim-probe-punctuation-after-punctuation | 半角标点后强制输入半角标点 |
;; |------------------------------------------+----------------------------|

;; 激活方式：

;; #+BEGIN_EXAMPLE
;; (setq-default pyim-punctuation-half-width-functions
;;               '(probe-function4 probe-function5 probe-function6))
;; #+END_EXAMPLE

;; 注：上述函数列表中，任意一个函数的返回值为 t 时，pyim 切换到半角标点输入模式。

;; ** 捐赠
;; 您可以通过小额捐赠的方式支持 pyim 的开发工作，具体方式：

;; 1. 通过支付宝收款账户：tumashu@163.com
;; 2. 通过支付宝钱包扫描：

;;    [[file:snapshots/QR-code-for-author.jpg]]


;; ** Tips

;; *** 关闭输入联想词功能 (默认开启)

;; #+BEGIN_EXAMPLE
;; (setq pyim-enable-shortcode nil)
;; #+END_EXAMPLE

;; *** 如何将个人词条相关信息导入和导出？

;; 1. 导入使用命令： pyim-import
;; 2. 导出使用命令： pyim-export

;; *** pyim 出现错误时，如何开启 debug 模式

;; #+BEGIN_EXAMPLE
;; (setq debug-on-error t)
;; #+END_EXAMPLE

;; *** 如何查看 pyim 文档。
;; pyim 的文档隐藏在 comment 中，如果用户喜欢阅读 html 格式的文档，
;; 可以查看在线文档；

;;   http://tumashu.github.io/pyim/

;; *** 将光标处的拼音或者五笔字符串转换为中文 (与 vimim 的 “点石成金” 功能类似)
;; #+BEGIN_EXAMPLE
;; (global-set-key (kbd "M-i") 'pyim-convert-string-at-point)
;; #+END_EXAMPLE

;; *** 如何使用其它字符翻页
;; #+BEGIN_EXAMPLE
;; (define-key pyim-mode-map "." 'pyim-page-next-page)
;; (define-key pyim-mode-map "," 'pyim-page-previous-page)
;; #+END_EXAMPLE

;; *** 如何用 ";" 来选择第二个候选词
;; #+BEGIN_EXAMPLE
;; (define-key pyim-mode-map ";"
;;   (lambda ()
;;     (interactive)
;;     (pyim-page-select-word-by-number 2)))
;; #+END_EXAMPLE

;; *** 如何添加自定义拼音词库
;; pyim 默认没有携带任何拼音词库，用户可以使用下面几种方式，获取
;; 质量较好的拼音词库：

;; **** 第一种方式 (懒人推荐使用)

;; 获取其他 pyim 用户的拼音词库，比如，某个同学测试 pyim
;; 时创建了一个中文拼音词库，词条数量大约60万。

;;    http://tumashu.github.io/pyim-bigdict/pyim-bigdict.pyim.gz

;; 下载上述词库后，运行 `pyim-dicts-manager' ，按照命令提示，将下载得到的词库
;; 文件信息添加到 `pyim-dicts' 中，最后运行命令 `pyim-restart' 或者重启
;; emacs，这个词库使用 `utf-8-unix' 编码。

;; **** 第二种方式 (Windows 用户推荐使用)

;; 使用词库转换工具将其他输入法的词库转化为pyim使用的词库：这里只介绍windows平
;; 台下的一个词库转换软件：

;; 1. 软件名称： imewlconverter
;; 2. 中文名称： 深蓝词库转换
;; 3. 下载地址： https://github.com/studyzy/imewlconverter
;; 4. 依赖平台： Microsoft .NET Framework (>= 3.5)

;; 使用方式：

;; [[file:snapshots/imewlconverter-basic.gif]]

;; 如果生成的词库词频不合理，可以按照下面的方式处理（非常有用的功能）：

;; [[file:snapshots/imewlconverter-wordfreq.gif]]

;; 生成词库后，运行 `pyim-dicts-manager' ，按照命令提示，将转换得到的词库文件的信息添加到 `pyim-dicts' 中，
;; 完成后运行命令 `pyim-restart' 或者重启emacs。

;; **** 第三种方式 (Linux & Unix 用户推荐使用)
;; E-Neo 同学编写了一个词库转换工具: [[https://github.com/E-Neo/scel2pyim][scel2pyim]] ,
;; 可以将一个搜狗词库转换为 pyim 词库。

;; 1. 软件名称： scel2pyim
;; 2. 下载地址： https://github.com/E-Neo/scel2pyim
;; 3. 编写语言： C语言

;; *** 如何手动安装和管理词库
;; 这里假设有两个词库文件：

;; 1. /path/to/pyim-dict1.pyim
;; 2. /path/to/pyim-dict2.pyim

;; 在~/.emacs文件中添加如下一行配置。

;; #+BEGIN_EXAMPLE
;; (setq pyim-dicts
;;       '((:name "dict1" :file "/path/to/pyim-dict1.pyim")
;;         (:name "dict2" :file "/path/to/pyim-dict2.pyim")))
;; #+END_EXAMPLE

;; 注意事项:
;; 1. 只有 :file 是 *必须* 设置的。
;; 2. 必须使用词库文件的绝对路径。
;; 3. 词库文件的编码必须为 utf-8-unix，否则会出现乱码。

;; *** Emacs 启动时加载 pyim 词库

;; #+BEGIN_EXAMPLE
;; (add-hook 'emacs-startup-hook
;;           #'(lambda () (pyim-restart-1 t)))
;; #+END_EXAMPLE

;; *** 将汉字字符串转换为拼音字符串
;; 下面两个函数可以将中文字符串转换的拼音字符串或者列表，用于 emacs-lisp
;; 编程。

;; 1. `pyim-hanzi2pinyin' （考虑多音字）
;; 2. `pyim-hanzi2pinyin-simple'  （不考虑多音字）

;; *** 中文分词
;; pyim 包含了一个简单的分词函数：`pyim-cstring-split-to-list', 可以
;; 将一个中文字符串分成一个词条列表，比如：

;; #+BEGIN_EXAMPLE
;;                   (("天安" 5 7)
;; 我爱北京天安门 ->  ("天安门" 5 8)
;;                    ("北京" 3 5)
;;                    ("我爱" 1 3))
;; #+END_EXAMPLE

;; 其中，每一个词条列表中包含三个元素，第一个元素为词条本身，第二个元素为词条
;; 相对于字符串的起始位置，第三个元素为词条结束位置。

;; 另一个分词函数是 `pyim-cstring-split-to-string', 这个函数将生成一个新的字符串，
;; 在这个字符串中，词语之间用空格或者用户自定义的分隔符隔开。

;; 注意，上述两个分词函数使用暴力匹配模式来分词，所以， *不能检测出* pyim
;; 词库中不存在的中文词条。

;; *** 获取光标处的中文词条
;; pyim 包含了一个简单的命令：`pyim-cwords-at-point', 这个命令
;; 可以得到光标处的 *英文* 或者 *中文* 词条的 *列表*，这个命令依赖分词函数：
;; `pyim-cstring-split-to-list'。

;; *** 让 `forward-word' 和 `back-backward’ 在中文环境下正常工作
;; 中文词语没有强制用空格分词，所以 Emacs 内置的命令 `forward-word' 和 `backward-word'
;; 在中文环境不能按用户预期的样子执行，而是 forward/backward “句子” ，pyim
;; 自带的两个命令可以在中文环境下正常工作：

;; 1. `pyim-forward-word
;; 2. `pyim-backward-word

;; 用户只需将其绑定到快捷键上就可以了，比如：

;; #+BEGIN_EXAMPLE
;; (global-set-key (kbd "M-f") 'pyim-forward-word)
;; (global-set-key (kbd "M-b") 'pyim-backward-word)
;; #+END_EXAMPLE

;; *** 为 isearch 相关命令添加拼音搜索支持
;; pyim 安装后，可以通过下面的设置开启拼音搜索功能：

;; #+BEGIN_EXAMPLE
;; (pyim-isearch-mode 1)
;; #+END_EXAMPLE

;; 注意：这个功能有一些限制，搜索字符串中只能出现 “a-z” 和 “’”，如果有
;; 其他字符（比如 regexp 操作符），则自动关闭拼音搜索功能。

;; 开启这个功能后，一些 isearch 扩展有可能失效，如果遇到这种问题，
;; 只能禁用这个 Minor-mode，然后联系 pyim 的维护者，看有没有法子实现兼容。

;; 用户激活这个 mode 后，可以使用下面的方式 *强制关闭* isearch 搜索框中文输入
;; （即使在 pyim 激活的时候）。

;; #+BEGIN_EXAMPLE
;; (setq-default pyim-english-input-switch-functions
;;               '(pyim-probe-isearch-mode))
;; #+END_EXAMPLE

;;; Code:

;; * 核心代码                                                           :code:
;; ** require + defcustom + defvar
(require 'subr-x)
(require 'cl-lib)
(require 'help-mode)
(require 'popup nil t)
(require 'posframe nil t)
(require 'pyim-pymap)
(require 'pyim-common)
(require 'xr) ;Used by pyim-cregexp-build
(require 'rx) ;Used by pyim-cregexp-build

(defgroup pyim nil
  "Pyim is a Chinese input method support quanpin, shuangpin, wubi and cangjie."
  :group 'leim)

(defcustom pyim-dicts nil
  "一个列表，用于保存 `pyim' 的词库信息.
每一个 element 都代表一条词库的信息, 用户可以使用词库管理命令
`pyim-dicts-manager' 来添加词库信息，每一条词库信息都使用一个
plist 来表示，比如：

    (:name \"100万大词库\" :file \"/path/to/pinyin-bigdict.pyim\")

其中：
1. `:name'      代表词库名称，用户可以按照喜好来确定（可选项）。
2. `:file'      表示词库文件，

另外一个与这个变量功能类似的变量是： `pyim-extra-dicts', 专门
用于和 elpa 格式的词库包集成。"
  :group 'pyim
  :type 'list)

(defcustom pyim-enable-shortcode t
  "启用输入联想词功能."
  :group 'pyim
  :type 'boolean)

(defcustom pyim-punctuation-dict
  '(("'" "‘" "’")
    ("\"" "“" "”")
    ("_" "——")
    ("^" "…")
    ("]" "】")
    ("[" "【")
    ("@" "◎")
    ("?" "？")
    (">" "》")
    ("=" "＝")
    ("<" "《")
    (";" "；")
    (":" "：")
    ("/" "、")
    ("." "。")
    ("-" "－")
    ("," "，")
    ("+" "＋")
    ("*" "×")
    (")" "）")
    ("(" "（")
    ("&" "※")
    ("%" "％")
    ("$" "￥")
    ("#" "＃")
    ("!" "！")
    ("`" "・")
    ("~" "～")
    ("}" "』")
    ("|" "÷")
    ("{" "『"))
  "标点符号表."
  :group 'pyim
  :type 'list)

(defcustom pyim-default-scheme 'quanpin
  "设置 pyim 使用哪一种输入法方案，默认使用全拼输入."
  :group 'pyim)

(defcustom pyim-assistant-scheme 'quanpin
  "设置辅助输入法方案.

这个功能主要用于五笔等形码输入法，在忘记编码的情况下，
临时激活某种辅助输入法（比如：拼音输入法）来输入汉字。"
  :group 'pyim)

(defcustom pyim-schemes
  '((quanpin
     :document "全拼输入法方案（不可删除）。"
     :class quanpin
     :first-chars "abcdefghijklmnopqrstuwxyz"
     :rest-chars "vmpfwckzyjqdltxuognbhsrei'-a"
     :prefer-trigger-chars "v")
    (rime
     :document
     "rime 输入法。

这个 scheme 适用于 librime 支持的所有输入法，通用性较好，但无法支
持 trigger-chars, 所以类似 pyim 全拼支持的v快捷键将无法使用。"
     :class rime
     :first-chars "abcdefghijklmnopqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz'-a"
     :prefer-trigger-chars nil)
    (rime-quanpin
     :document
     "rime 全拼输入法。

这个 scheme 专门用于 librime 全拼输入法，同时支持 trigger-chars,
也就是v快捷键，使用 rime 全拼的朋友建议使用这个 scheme。"
     :class rime
     :first-chars "abcdefghjklmnopqrstwxyz"
     :rest-chars "vmpfwckzyjqdltxuognbhsrei'-a"
     :prefer-trigger-chars "v")
    (rime-microsoft-shuangpin
     :document "rime 微软双拼输入法。"
     :class rime
     :first-chars "abcdefghijklmnopqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz;"
     :prefer-trigger-chars nil)
    (wubi
     :document "五笔输入法。"
     :class xingma
     :first-chars "abcdefghijklmnopqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz'"
     :code-prefix "." ;五笔词库中所有的 code 都以 "." 开头，防止和拼音词库冲突。
     :code-split-length 4 ;默认将用户输入切成 4 个字符长的 code 列表（不计算 code-prefix）
     :code-maximum-length 4 ;五笔词库中，code 的最大长度（不计算 code-prefix）
     :prefer-trigger-chars nil)
    (cangjie
     :document "倉頡输入法。"
     :class xingma
     :first-chars "abcdefghijklmnopqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz"
     :code-prefix "@" ;仓颉输入法词库中所有的 code 都以 "@" 开头，防止词库冲突。
     :code-split-length 5 ;默认将用户输入切成 5 个字符长的 code 列表（不计算 code-prefix）
     :code-maximum-length 5 ;仓颉词库中，code 的最大长度（不计算 code-prefix）
     :prefer-trigger-chars nil)
    (pyim-shuangpin
     :document "与 pyim 配合良好的双拼输入法方案，源自小鹤双拼方案。"
     :class shuangpin
     :first-chars "abcdefghijklmnpqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz"
     :prefer-trigger-chars "o"
     :keymaps
     (("a" "a" "a")
      ("b" "b" "in")
      ("c" "c" "ao")
      ("d" "d" "ai")
      ("e" "e" "e")
      ("f" "f" "en")
      ("g" "g" "eng")
      ("h" "h" "ang")
      ("i" "ch" "i")
      ("j" "j" "an")
      ("k" "k" "ing" "uai")
      ("l" "l" "iang" "uang")
      ("m" "m" "ian")
      ("n" "n" "iao")
      ("o" "o" "uo" "o")
      ("p" "p" "ie")
      ("q" "q" "iu")
      ("r" "r" "uan")
      ("s" "s" "iong" "ong")
      ("t" "t" "ue" "ve")
      ("u" "sh" "u")
      ("v" "zh" "v" "ui")
      ("w" "w" "ei")
      ("x" "x" "ia" "ua")
      ("y" "y" "un")
      ("z" "z" "ou")
      ("aa" "a")
      ("aj" "an")
      ("ad" "ai")
      ("ac" "ao")
      ("ah" "ang")
      ("ee" "e")
      ("ew" "ei")
      ("ef" "en")
      ("er" "er")
      ("eg" "eng")
      ("ag" "ng")
      ("ao" "o")
      ("au" "ou")))
    (ziranma-shuangpin
     :document "自然码双拼方案。"
     :class shuangpin
     :first-chars "abcdefghijklmnopqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz"
     :prefer-trigger-chars nil
     :keymaps
     (("a" "a" "a")
      ("b" "b" "ou")
      ("c" "c" "iao")
      ("d" "d" "uang" "iang")
      ("e" "e" "e")
      ("f" "f" "en")
      ("g" "g" "eng")
      ("h" "h" "ang")
      ("i" "ch" "i")
      ("j" "j" "an")
      ("k" "k" "ao")
      ("l" "l" "ai")
      ("m" "m" "ian")
      ("n" "n" "in")
      ("o" "o" "uo" "o")
      ("p" "p" "un")
      ("q" "q" "iu")
      ("r" "r" "uan" "er")
      ("s" "s" "iong" "ong")
      ("t" "t" "ue" "ve")
      ("u" "sh" "u")
      ("v" "zh" "v" "ui")
      ("w" "w" "ia" "ua")
      ("x" "x" "ie")
      ("y" "y" "uai" "ing")
      ("z" "z" "ei")
      ("aa" "a")
      ("an" "an")
      ("ai" "ai")
      ("ao" "ao")
      ("ah" "ang")
      ("ee" "e")
      ("ei" "ei")
      ("en" "en")
      ("er" "er")
      ("eg" "eng")
      ("oo" "o")
      ("ou" "ou")))
    (microsoft-shuangpin
     :document "微软双拼方案。"
     :class shuangpin
     :first-chars "abcdefghijklmnopqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz;"
     :prefer-trigger-chars nil
     :keymaps
     (("a" "a" "a")
      ("b" "b" "ou")
      ("c" "c" "iao")
      ("d" "d" "uang" "iang")
      ("e" "e" "e")
      ("f" "f" "en")
      ("g" "g" "eng")
      ("h" "h" "ang")
      ("i" "ch" "i")
      ("j" "j" "an")
      ("k" "k" "ao")
      ("l" "l" "ai")
      ("m" "m" "ian")
      ("n" "n" "in")
      ("o" "o" "uo" "o")
      ("p" "p" "un")
      ("q" "q" "iu")
      ("r" "r" "uan" "er")
      ("s" "s" "iong" "ong")
      ("t" "t" "ue")
      ("u" "sh" "u")
      ("v" "zh" "ve" "ui")
      ("w" "w" "ia" "ua")
      ("x" "x" "ie")
      ("y" "y" "uai" "v")
      ("z" "z" "ei")
      (";" ";" "ing")
      ("oa" "a")
      ("oj" "an")
      ("ol" "ai")
      ("ok" "ao")
      ("oh" "ang")
      ("oe" "e")
      ("oz" "ei")
      ("of" "en")
      ("or" "er")
      ("og" "eng")
      ("oo" "o")
      ("ob" "ou")))
    (zhinengabc-shuangpin
     :document "智能ABC双拼方案"
     :class shuangpin
     :first-chars "abcdefghjklmnopqrstvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz"
     :prefer-trigger-chars nil
     :keymaps
     (("q" "q" "ei")
      ("w" "w" "ian")
      ("e" "ch" "e")
      ("r" "r" "iu" "er")
      ("t" "t" "uang" "iang")
      ("y" "y" "ing")
      ("u" "u" "u")
      ("i" "i" "i")
      ("o" "o" "o" "uo")
      ("p" "p" "uan" "van")
      ("a" "zh" "a")
      ("s" "s" "ong" "iong")
      ("d" "d" "ua" "ia")
      ("f" "f" "en")
      ("g" "g" "eng")
      ("h" "h" "ang")
      ("j" "j" "an")
      ("k" "k" "ao")
      ("l" "l" "ai")
      ("z" "z" "iao")
      ("x" "x" "ie")
      ("c" "c" "in" "uai")
      ("v" "sh" "v")
      ("b" "b" "ou")
      ("n" "n" "un")
      ("m" "m" "ue" "ui")
      ("oa" "a")
      ("oj" "an")
      ("ol" "ai")
      ("ok" "ao")
      ("oh" "ang")
      ("oe" "e")
      ("oz" "ei")
      ("of" "en")
      ("or" "er")
      ("og" "eng")
      ("oo" "o")
      ("ob" "ou")))
    (xiaohe-shuangpin
     :document "小鹤双拼输入法方案。"
     :class shuangpin
     :first-chars "abcdefghijklmnopqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz"
     :prefer-trigger-chars nil
     :keymaps
     (("a" "a" "a")
      ("b" "b" "in")
      ("c" "c" "ao")
      ("d" "d" "ai")
      ("e" "e" "e")
      ("f" "f" "en")
      ("g" "g" "eng")
      ("h" "h" "ang")
      ("i" "ch" "i")
      ("j" "j" "an")
      ("k" "k" "ing" "uai")
      ("l" "l" "iang" "uang")
      ("m" "m" "ian")
      ("n" "n" "iao")
      ("o" "o" "uo" "o")
      ("p" "p" "ie")
      ("q" "q" "iu")
      ("r" "r" "uan")
      ("s" "s" "iong" "ong")
      ("t" "t" "ue" "ve")
      ("u" "sh" "u")
      ("v" "zh" "v" "ui")
      ("w" "w" "ei")
      ("x" "x" "ia" "ua")
      ("y" "y" "un")
      ("z" "z" "ou")
      ("aa" "a")
      ("an" "an")
      ("ai" "ai")
      ("ao" "ao")
      ("ah" "ang")
      ("ee" "e")
      ("ei" "ei")
      ("en" "en")
      ("er" "er")
      ("eg" "eng")
      ("og" "ng")
      ("oo" "o")
      ("ou" "ou"))))
  "Pyim 支持的所有拼音方案.")

(defcustom pyim-translate-trigger-char "v"
  "用于触发特殊操作的字符，相当与单字快捷键.

输入中文的时候，我们需要快速频繁的执行一些特定的命令，最直接的方
法就是将上述命令绑定到一个容易按的快捷键上，但遗憾的是 emacs 大多
数容易按的快捷键都 *名花有主* 了，甚至找一个 “Ctrl＋单字符”的快
捷键都不太容易，特殊功能触发字符，可以帮助我们实现“单字符”快捷
键，类似 org-mode 的 speed key。

默认情况下，我们可以使用特殊功能触发字符执行下面几个操作（假设触
发字符为 v）：

1. 快速切换中英文标点符号的样式：当光标前的字符是一个标点符号时，
   按 \"v\" 可以切换这个标点的样式。比如：光标在A处的时候，按
   \"v\" 可以将A前面的全角逗号转换为半角逗号。

        你好，-A-

   按 \"v\" 后

        你好,-A-

2. 快速将光标前的词条添加到词库：当光标前的字符是中文字符时，按
   \"num\" + \"v\" 可以将光标前 num 个中文汉字组成的词条添加到个
   人词频文件中，比如：当光标在A处时，按\"4v\"可以将“的红烧肉”
   这个词条加入个人词频文件，默认num不超过9。

        我爱吃美味的红烧肉-A-

值得注意的是，这种方式如果添加的功能太多，会造成许多潜在的冲突。

用户可以使用变量 `pyim-translate-trigger-char' 来设置触发字符，默
认的触发字符是：\"v\", 选择这个字符的理由基于全拼输入法的：

1. \"v\" 不是有效的声母，不会对中文输入造成太大的影响。
2. \"v\" 字符很容易按。

pyim 使用函数 `pyim-translate' 来处理特殊功能触发字符。当待输入的
字符是触发字符时，`pyim-translate' 根据光标前的字符的不同来调用不
同的功能，具体见 `pyim-translate' ：

单字快捷键受到输入法方案的限制，比如：全拼输入法可以将其设置为v,
但双拼输入法下设置 v 可能就不行，所以，pyim 首先会检查当前输入法
方案下，这个快捷键设置是否合理有效，如果不是一个合理的设置，则使
用拼音方案默认的 :prefer-trigger-chars 。

具体请参考 `pyim-translate-get-trigger-char' 。"
  :group 'pyim
  :type 'character)

(defcustom pyim-exhibit-delay-ms 0
  "输入或者删除拼音字符后等待多少毫秒后才显示可选词
当用户快速输入连续的拼音时可提升用户体验.
如果为 0 或者 nil, 则不等待立刻显示可选词."
  :group 'pyim
  :type 'integer)

(defcustom pyim-fuzzy-pinyin-alist
  '(("en" "eng")
    ("in" "ing")
    ("un" "ong"))
  "设定糢糊音."
  :group 'pyim)

(defface pyim-preview-face '((t (:underline t)))
  "设置光标处预览字符串的 face."
  :group 'pyim)

(defcustom pyim-english-input-switch-functions nil
  "让 pyim 开启英文输入功能.

这个变量的取值为一个函数列表，这个函数列表中的任意一个函数的
运行结果为 t 时，pyim 开启英文输入功能。"
  :group 'pyim)

(defcustom pyim-punctuation-half-width-functions nil
  "让 pyim 输入半角标点.

取值为一个函数列表，这个函数列表中的任意一个函数的运行结果为 t 时，
pyim 输入半角标点，函数列表中每个函数都有一个参数：char ，表示
最后输入的一个字符，具体见: `pyim-translate' 。"
  :group 'pyim)

(defcustom pyim-wash-function 'pyim-wash-current-line-function
  "清洗光标前面的文字内容.
这个函数与『单字快捷键配合使用』，当光标前面的字符为汉字字符时，
按 `pyim-translate-trigger-char' 对应字符，可以调用这个函数来清洗
光标前面的文字内容。"
  :group 'pyim
  :type 'function)

(defcustom pyim-page-length 5
  "每页显示的词条数目.

细节信息请参考 `pyim-page-refresh' 的 docstring."
  :group 'pyim
  :type 'number)

(defcustom pyim-page-tooltip 'popup
  "如何绘制 pyim 选词框.

1. 当这个变量取值为 posframe 时，使用 posframe 包来绘制选词框；
2. 当这个变量取值为 minibuffer 时，使用 minibuffer 做为选词框；
3. 当这个变量取值为 popup 时，使用 popup-el 包来绘制选词框；"
  :group 'pyim)

(defcustom pyim-page-style 'two-lines
  "这个变量用来控制选词框的格式.

pyim 内建的有三种选词框格式：

1. one-line  单行选词框
2. two-lines 双行选词框
3. vertical  垂直选词框"
  :group 'pyim
  :type 'symbol)

(defcustom pyim-page-select-finish-hook nil
  "Pyim 选词完成时运行的 hook."
  :group 'pyim
  :type 'hook)

(defcustom pyim-page-select-word-by-number t
  "使用数字键来选择词条.

如果设置为 nil, 将直接输入数字，适用于使用数字做为
编码的输入法。"
  :group 'pyim)

(defcustom pyim-magic-converter nil
  "将 “待选词条” 在 “上屏” 之前自动转换为其他字符串.
这个功能可以实现“简转繁”，“输入中文得到英文”之类的功能。"
  :group 'pyim)

(defcustom pyim-posframe-border-width 0
  "posframe的内间距。
只有当用户使用 posframe 来显示候选词时才有效。"
  :group 'pyim
  :type 'integer)

(defcustom pyim-autoselector '(pyim-autoselector-xingma)
  "已经启用的自动上屏器.

自动上屏器是一个函数，如果这个函数返回t, 那么当前的词条就会自动
上屏，不需要手动选择。"
  :group 'pyim)

(defcustom pyim-posframe-min-width (* pyim-page-length 7)
  "使用 posframe 做为选词框时，设置选词框的最小宽度."
  :group 'pyim
  :type 'integer)

(defface pyim-page
  '((t (:inherit default :background "#333333" :foreground "#dcdccc")))
  "Face used for the pyim page."
  :group 'pyim)

(defface pyim-page-border
  '((t (:inherit pyim-page)))
  "Face used for the pyim page border.
Only useful when use posframe."
  :group 'pyim)

(defface pyim-page-selection
  '((t (:background "gray44")))
  "选词框中已选词条的 face

注意：当使用 minibuffer 为选词框时，这个选项才有用处。"
  :group 'pyim)

(defvar pyim-dcache-backend 'pyim-dhashcache
  "词库后端引擎.负责缓冲词库并提供搜索词的算法.
可选项为 `pyim-dhashcache' 或 `pyim-dregcache'.
前者搜索单词速度很快,消耗内存多.  后者搜索单词速度较快,消耗内存少.

`pyim-dregcache' 速度和词库大小成正比.  当词库接近100M大小时,
在六年历史的笔记本上会有一秒的延迟. 这时建议换用 `pyim-dhashcache'.")

;;;###autoload
(defvar pyim-title "灵通" "Pyim 在 mode-line 中显示的名称.")
(defvar pyim-extra-dicts nil "与 `pyim-dicts' 类似, 用于和 elpa 格式的词库包集成。.")

(defvar pyim-pinyin-shenmu
  '("b" "p" "m" "f" "d" "t" "n" "l" "g" "k" "h"
    "j" "q" "x" "z" "c" "s" "zh" "ch" "sh" "r" "y" "w"))

(defvar pyim-pinyin-yunmu
  '("a" "o" "e" "i" "u" "v" "ai" "ei" "ui" "ao" "ou" "iu"
    "ie" "ia" "ua" "ve" "er" "an" "en" "in" "un" "vn" "ang" "iong"
    "eng" "ing" "ong" "uan" "uang" "ian" "iang" "iao" "ue"
    "uai" "uo"))

(defvar pyim-pinyin-valid-yunmu
  '("a" "o" "e" "ai" "ei" "ui" "ao" "ou" "er" "an" "en"
    "ang" "eng"))

(defvar pyim-entered-buffer " *pyim-entered-buffer*"
  "一个 buffer，用来处理用户已经输入的字符串： entered。

用户 *已经* 输入的字符组成的字符串，在 pyim 里面，叫做 entered,
说白了就是 input, 选择 entered 而不选择 input 的原因是：

1. input 太常见了， 和其它词语组和起来容易产生歧义，比如：
   pyim-entered-output 就比 pyim-input-output 更加容易理解。
2. entered 这个词语很少见，只要明白它代表的概念，就不容易产生混乱。

pyim 使用一个 buffer 来处理 entered, 以实现 “用户输入字符串” 编
辑等高级功能：

1. 如果输入的字符串有错误，可以修改，不用取消重新输入；
2. 如果光标不在行首，pyim 只使用光标前的字符串来查找词条，
   如果词条上屏，词条对应的输入就从 buffer 中清除，然后
   继续处理后面的输入，这种方式方便长词的输入；
3. 如果光标在行首，则处理整行。")

(defvar pyim-imobjs nil
  "Imobj (Input method object) 组成的 list.

imobj 在 pyim 里面的概念，类似与编译器里面的语法树，
它代表 pyim 输入的字符串 entered 解析得到的一个结构化对象，
以全拼输入法的为例：

1. entered: nihaoma
2. imobj: ((\"n\" \"i\" \"n\" \"i\") (\"h\" \"ao\" \"h\" \"ao\") (\"m\" \"a\" \"m\" \"a\"))

而 imobjs 是 imobj 组成的一个列表，因为有糢糊音等概念的存在，一个
entered 需要以多种方式或者多步骤解析，得到多种可能的 imobj, 这些
imobj 组合构成在一起，构成了 imobjs 这个概念。比如：

1. entered: guafeng (设置了糢糊音 en -> eng)
2. imobj-1: ((\"g\" \"ua\" \"g\" \"ua\") (\"f\" \"en\" \"f\" \"eng\"))
3. imobj-2: ((\"g\" \"ua\" \"g\" \"ua\") (\"f\" \"eng\" \"f\" \"eng\"))
4. imobjs:  (((\"g\" \"ua\" \"g\" \"ua\") (\"f\" \"en\" \"f\" \"eng\"))
             ((\"g\" \"ua\" \"g\" \"ua\") (\"f\" \"eng\" \"f\" \"eng\")))

这个变量用来保存解析得到的 imobjs。

解析完成之后，pyim 会为每一个 imobj 创建对应 code 字符串, 然后在词库
中搜索 code 字符串来得到所需要的词条，最后使用特定的方式将得到的
词条组合成一个候选词列表：`pyim-candidates' 并通过 pyim-page 相关
功能来显示选词框，供用户选择词条，比如：

1. imobj: ((\"g\" \"ua\" \"g\" \"ua\") (\"f\" \"en\" \"f\" \"en\"))
2. code: gua-fen

从上面的说明可以看出，imobj 本身也是有结构的：

1. imobj: ((\"g\" \"ua\" \"g\" \"ua\") (\"f\" \"en\" \"f\" \"en\"))

我们将 (\"g\" \"ua\" \"g\" \"ua\") 这些子结构，叫做 imelem (IM element), *大
多数情况下*, 一个 imelem 能够代表一个汉字，这个概念在编辑 entered
的时候，非常有用。

另外要注意的是，不同的输入法， imelem 的内部结构是不一样的，比如：
1. quanping:  (\"g\" \"ua\" \"g\" \"ua\")
2. shuangpin: (\"h\" \"ao\" \"h\" \"c\")
3. wubi:      (\"aaaa\")")

(defvar pyim-candidates nil
  "所有备选词条组成的列表.")

(defvar pyim-preview-overlay nil
  "用于保存光标处预览字符串的 overlay.")

(defvar pyim-outcome-history nil
  "记录 pyim outcome 的变化的历史

在 pyim 中 outcome 代表用户通过输入法选择，并最终插入到 buffer
的字符串。

“一次确认就生成的词条” , 当前变量一般只有一个元素，比如：
1. 输入： nihao
2. 输出： 你好
2. 变量取值为： (\"你好\")

“多次确认才能生成词条” , 当前变量记录了选择的历史，比如：

1. 输入： yiersansi
2. 输出： 一二三四
3. 第一次选择：一二
4. 第二次选择：三
5. 第三次选择：四
6. 变量取值为： (\"一二三四\" \"一二三\" \"一二\")")

(defvar pyim-assistant-scheme-enable nil
  "设置临时 scheme, 用于五笔等形码输入法临时拼音输入。")

(defvar pyim-input-ascii nil
  "是否开启 pyim 英文输入模式.")

(defvar pyim-force-input-chinese nil
  "是否强制开启中文输入模式.

这个变量只用于 `pyim-convert-string-at-point', 不要
在其它地方使用。")

(defvar pyim-candidate-position nil
  "当前选择的词条在 ‘pyim-candidates’ 中的位置.

细节信息请参考 `pyim-page-refresh' 的 docstring.")

(defvar pyim-last-created-word nil
  "记录最近一次创建的词条， 用于实现快捷删词功能： `pyim-delete-last-word' .")

(defvar pyim-translating nil
  "记录是否在转换状态.")

(defvar pyim-magic-convert-cache nil
  "用来临时保存 `pyim-magic-convert' 的结果.
从而加快同一个字符串第二次的转换速度。")

(defvar pyim-load-hook nil)
(defvar pyim-active-hook nil)

(defvar pyim-punctuation-translate-p '(auto yes no)
  "这个变量的第一个元素的取值用于控制标点符号全角半角模式切换.

1. 当第一个元素为 'yes 时，输入全角标点。
2. 当第一个元素为 'no 时，输入半角标点。
3. 当第一个元素为 'auto 时，根据中英文环境，自动切换。")

(defvar pyim-punctuation-pair-status
  '(("\"" nil) ("'" nil))
  "成对标点符号切换状态.")

(defvar pyim-punctuation-escape-list (number-sequence ?0 ?9)
  "Punctuation will not insert after this characters.

If you don't like this function, set the variable to nil")

(defvar pyim-pinyin2cchar-cache1 nil
  "拼音查汉字功能需要的变量.")
(defvar pyim-pinyin2cchar-cache2 nil
  "拼音查汉字功能需要的变量.")
(defvar pyim-pinyin2cchar-cache3 nil
  "拼音查汉字功能需要的变量.")
(defvar pyim-cchar2pinyin-cache nil
  "汉字转拼音功能需要的变量.")

(defvar pyim-dcache-auto-update t
  "是否自动创建和更新词库对应的 dcache 文件.

这个变量默认设置为 t, 如果有词库文件添加到 `pyim-dicts' 或者
`pyim-extra-dicts' 时，pyim 会自动生成相关的 dcache 文件。

一般不建议将这个变量设置为 nil，除非有以下情况：

1. 用户的词库已经非常稳定，并且想通过禁用这个功能来降低
pyim 对资源的消耗。
2. 自动更新功能无法正常工作，用户通过手工从其他机器上拷贝
dcache 文件的方法让 pyim 正常工作。")

(defvar pyim-page-tooltip-posframe-buffer " *pyim-page-tooltip-posframe-buffer*"
  "这个变量用来保存做为 page tooltip 的 posframe 的 buffer.")

(defconst pyim-shuangpin-invalid-pinyin-regexp
  "^\\([qtghkzcsdn]o\\|[ypfbmw]uo\\|[qj]ong\\|[rtysdghklzcn]iong\\|[qtypdjlxbnm]uai\\|[ghk]ing?\\|[qjlxn]uang\\|[dgh]iang\\|[qjlx]ua\\|[hkg]ia\\|[rtsdghkzc]v\\|[jl]ui\\)$"
  "双拼可能自动产生的无效拼音. 例如输入 kk 得到有效拼音 kuai .
但同时产生了无效拼音 king .  用户手动输入的无效拼音无需考虑.
因为用户有即时界面反馈,不可能连续输入无效拼音.")

(defvar pyim-rime-limit 50
  "当 pyim 使用 `liberime-search' 来获取词条时，这个变量用来限制
`liberime-search' 返回词条的数量。")

(defvar pyim-mode-map
  (let ((map (make-sparse-keymap))
        (i ?\ ))
    (while (< i 127)
      (define-key map (char-to-string i) 'pyim-self-insert-command)
      (setq i (1+ i)))
    (setq i 128)
    (while (< i 256)
      (define-key map (vector i) 'pyim-self-insert-command)
      (setq i (1+ i)))
    (dolist (i (number-sequence ?0 ?9))
      (define-key map (char-to-string i) 'pyim-page-select-word-by-number))
    (define-key map " " 'pyim-page-select-word)
    (define-key map (kbd "C-SPC") 'pyim-page-select-word-simple)
    (define-key map [backspace] 'pyim-entered-delete-backward-char)
    (define-key map [delete] 'pyim-entered-delete-forward-char)
    (define-key map "\C-d" 'pyim-entered-delete-forward-char)
    (define-key map [M-backspace] 'pyim-entered-delete-backward-imelem)
    (define-key map [M-delete] 'pyim-entered-delete-forward-imelem)
    (define-key map [C-backspace] 'pyim-entered-delete-backward-imelem)
    (define-key map [C-delete] 'pyim-entered-delete-forward-imelem)
    (define-key map [?\t]      'pyim-toggle-assistant-scheme)
    (define-key map (kbd "TAB") 'pyim-toggle-assistant-scheme)
    (define-key map "\177" 'pyim-entered-delete-backward-char)
    (define-key map "\C-f" 'pyim-entered-forward-point)
    (define-key map "\C-b" 'pyim-entered-backward-point)
    (define-key map "\M-f" 'pyim-entered-forward-imelem)
    (define-key map "\M-b" 'pyim-entered-backward-imelem)
    (define-key map "\C-e" 'pyim-entered-end-of-line)
    (define-key map "\C-a" 'pyim-entered-beginning-of-line)
    (define-key map "=" 'pyim-page-next-page)
    (define-key map "-" 'pyim-page-previous-page)
    (define-key map "\C-n" 'pyim-page-next-word)
    (define-key map "\C-p" 'pyim-page-previous-word)
    (define-key map "\M-n" 'pyim-page-next-page)
    (define-key map "\M-p" 'pyim-page-previous-page)
    (define-key map "\C-m" 'pyim-quit-no-clear)
    (define-key map [return] 'pyim-quit-no-clear)
    (define-key map "\C-c" 'pyim-quit-clear)
    map)
  "Pyim 的 Keymap.")

;; ** 将变量转换为 local 变量
(defvar pyim-local-variable-list
  '(pyim-imobjs
    pyim-outcome-history
    pyim-preview-overlay
    pyim-candidates
    pyim-candidate-position
    pyim-input-ascii
    pyim-english-input-switch-functions
    pyim-punctuation-half-width-functions
    pyim-translating
    pyim-last-created-word

    input-method-function
    inactivate-current-input-method-function
    describe-current-input-method-function

    pyim-punctuation-translate-p
    pyim-punctuation-pair-status
    pyim-punctuation-escape-list)
  "A list of buffer local variable.")

(defvar pyim--exhibit-timer nil)

(dolist (var pyim-local-variable-list)
  (make-variable-buffer-local var)
  (put var 'permanent-local t))

(defmacro pyim-with-entered-buffer (&rest forms)
  (declare (indent 0) (debug t))
  `(with-current-buffer (get-buffer-create pyim-entered-buffer)
     ,@forms))

(defun pyim-entered-get ()
  "从 `pyim-entered-buffer' 中获取拼音字符串"
  (pyim-with-entered-buffer
    (buffer-string)))

(defun pyim-entered-erase-buffer ()
  "清除 `pyim-entered-buffer' 的内容"
  (pyim-with-entered-buffer
    (erase-buffer)))

;; pyim-entered-buffer 中进行光标移动的函数
;; point move function in `pyim-entered-buffer'
(defun pyim-entered-forward-point ()
  "`pyim-entered-buffer' 中光标前移"
  (interactive)
  (pyim-with-entered-buffer
    (ignore-errors
      (forward-char)))
  (pyim-entered-refresh t))

(defun pyim-entered-backward-point ()
  "`pyim-entered-buffer' 中光标后移"
  (interactive)
  (pyim-with-entered-buffer
    (ignore-errors
      (backward-char)))
  (pyim-entered-refresh t))

(defun pyim-entered-backward-imelem (&optional search-forward)
  "`pyim-entered-buffer’ 中光标向后移动一个 imelem 对应的字符串

在全拼输入法中，就是向前移动一个拼音"
  (interactive)
  (let* ((position (pyim-entered-next-imelem-position 1 search-forward)))
    (pyim-with-entered-buffer
      (goto-char position))
    (pyim-entered-refresh t)))

(defun pyim-entered-forward-imelem ()
  "`pyim-entered-buffer’ 中光标向前移动一个 imelem 对应的字符串"
  (interactive)
  (pyim-entered-backward-imelem t))

(defun pyim-entered-end-of-line ()
  "`pyim-entered-buffer' 中光标移至行尾"
  (interactive)
  (pyim-with-entered-buffer
    (end-of-line))
  (pyim-entered-refresh t))

(defun pyim-entered-beginning-of-line ()
  "`pyim-entered-buffer' 中光标移至行首"
  (interactive)
  (pyim-with-entered-buffer
    (beginning-of-line))
  (pyim-entered-refresh t))

;; ** "汉字 -> 拼音" 以及 "拼音 -> 汉字" 的转换函数
(defun pyim-pinyin2cchar-cache-create (&optional force)
  "构建 pinyin 到 chinese char 的缓存.

用于加快搜索速度，这个函数将缓存保存到 `pyim-pinyin2cchar-cache' 变量中，
如果 FORCE 设置为 t, 强制更新索引。"
  (when (or force (or (not pyim-pinyin2cchar-cache1)
                      (not pyim-pinyin2cchar-cache2)))
    (setq pyim-pinyin2cchar-cache1
          (make-hash-table :size 50000 :test #'equal))
    (setq pyim-pinyin2cchar-cache2
          (make-hash-table :size 50000 :test #'equal))
    (setq pyim-pinyin2cchar-cache3
          (make-hash-table :size 50000 :test #'equal))
    (dolist (x pyim-pymap)
      (let* ((py (car x))
             (cchars (cdr x))
             (n (min (length py) 7)))
        (puthash py cchars pyim-pinyin2cchar-cache1)
        (puthash py (cdr (split-string (car cchars) ""))
                 pyim-pinyin2cchar-cache2)
        (dotimes (i n)
          (let* ((key (substring py 0 (+ i 1)))
                 (orig-value (gethash key pyim-pinyin2cchar-cache3)))
            (puthash key (delete-dups `(,@orig-value ,@cchars))
                     pyim-pinyin2cchar-cache3)))))))

(defun pyim-pinyin2cchar-get (pinyin &optional equal-match return-list include-seperator)
  "获取拼音与 PINYIN 想匹配的所有汉字.

比如：

“man” -> (\"忙茫盲芒氓莽蟒邙漭硭\" \"满慢漫曼蛮馒瞒蔓颟谩墁幔螨鞔鳗缦熳镘\")

如果 EQUAL-MATCH 是 non-nil, 获取和 PINYIN 完全匹配的汉字。
如果 RETURN-LIST 是 non-nil, 返回一个由单个汉字字符串组成的列表。

(\"满\" \"慢\" \"漫\"  ...)

如果 INCLUDE-SEPERATOR 是 non-nil, 返回的列表包含一个 ‘|’ 号，pyim 用这个分隔符
来区分 3500 个常用汉字和生僻字。"
  (pyim-pinyin2cchar-cache-create)
  (when (and pinyin (stringp pinyin))
    (let ((output
           (if equal-match
               (if return-list
                   (gethash pinyin pyim-pinyin2cchar-cache2)
                 (gethash pinyin pyim-pinyin2cchar-cache1))
             (gethash pinyin pyim-pinyin2cchar-cache3))))
         (delete "" output)
      (if include-seperator
          output
          (delete "|" output)))))

(defun pyim-cchar2pinyin-get (char-or-str)
  "获取字符或者字符串 CHAR-OR-STR 对应的拼音 code.

pyim 在特定的时候需要读取一个汉字的拼音，这个工作由此完成，函数
从 `pyim-cchar2pinyin-cache' 查询得到一个汉字字符的拼音， 例如：

(pyim-cchar2pinyin-get ?我)

结果为:

(\"wo\")"
  (pyim-cchar2pinyin-cache-create)
  (let ((key (if (characterp char-or-str)
                 (char-to-string char-or-str)
               char-or-str)))
    (when (= (length key) 1)
      (gethash key pyim-cchar2pinyin-cache))))

(defun pyim-cchar2pinyin-cache-create (&optional force)
  "Build pinyin cchar->pinyin hashtable from `pyim-pymap'.

If FORCE is non-nil, FORCE build."
  (when (or force (not pyim-cchar2pinyin-cache))
    (setq pyim-cchar2pinyin-cache
          (make-hash-table :size 50000 :test #'equal))
    (dolist (x pyim-pymap)
      (let ((py (car x))
            (cchar-list (string-to-list (car (cdr x)))))
        (dolist (cchar cchar-list)
          (let* ((key (char-to-string cchar))
                 (cache (gethash key pyim-cchar2pinyin-cache)))
            (if cache
                (puthash key (append (list py) cache) pyim-cchar2pinyin-cache)
              (puthash key (list py) pyim-cchar2pinyin-cache))))))))

;; ** 注册 Pyim 输入法
;;;###autoload
(register-input-method "pyim" "euc-cn" 'pyim-start pyim-title)

;;;###autoload
(defun pyim-start (name &optional active-func restart save-personal-dcache refresh-common-dcache)
  "pyim 启动函数.
  TODO: Document NAME ACTIVE-FUNC RESTART SAVE-PERSONAL-DCACHE REFRESH-COMMON-DCACHE

pyim 是使用 `pyim-start' 来启动输入法，这个命令主要做如下工作：
1. 重置 `pyim-local-variable-list' 中所有的 local 变量。
2. 使用 `pyim-cchar2pinyin-create-cache' 创建汉字到拼音的 hash table 对应表。
3. 运行hook： `pyim-load-hook'。
4. 将 `pyim-dcache-save-caches' 命令添加到 `kill-emacs-hook' , emacs 关闭
之前将用户选择过的词生成的缓存和词频缓存保存到文件，供以后使用。
5. 设定变量：
1. `input-method-function'
2. `deactivate-current-input-method-function'
6. 运行 `pyim-active-hook'

pyim 使用函数 `pyim-start' 启动输入法的时候，会将变量
`input-method-function' 设置为 `pyim-input-method' ，这个变量会影
响 `read-event' 的行为。

当输入字符时，`read-event' 会被调用，`read-event' 调用的过程中，
会执行 `pyim-input-method' 这个函数。`pyim-input-method' 又调用函
数`pyim-start-translation'."
  (interactive)
  (mapc 'kill-local-variable pyim-local-variable-list)
  (mapc 'make-local-variable pyim-local-variable-list)
  (when (and restart save-personal-dcache)
    (pyim-dcache-save-caches))

  (pyim-dcache-init-variables)

  (when pyim-dcache-auto-update
    (pyim-dcache-call-api 'update-personal-words restart))

  (pyim-cchar2pinyin-cache-create)
  (pyim-pinyin2cchar-cache-create)
  (run-hooks 'pyim-load-hook)

  (when pyim-dcache-auto-update
    (pyim-dcache-update-code2word refresh-common-dcache)
    ;; 这个命令 *当前* 主要用于五笔输入法。
    (pyim-dcache-call-api 'update-shortcode2word restart))

  (unless (member 'pyim-dcache-save-caches kill-emacs-hook)
    (add-to-list 'kill-emacs-hook 'pyim-dcache-save-caches))
  (setq input-method-function 'pyim-input-method)
  (setq deactivate-current-input-method-function 'pyim-inactivate)
  ;; (setq describe-current-input-method-function 'pyim-help)
  ;; If we are in minibuffer, turn off the current input method
  ;; before exiting.
  (when (eq (selected-window) (minibuffer-window))
    (add-hook 'minibuffer-exit-hook 'pyim-exit-from-minibuffer))
  (run-hooks 'pyim-active-hook)
  (when (and (memq pyim-page-tooltip '(posframe child-frame))
             (not (pyim-posframe-valid-p)))
    (message "PYIM: posframe 没有正确安装或者当前 emacs 版本不支持 posframe。"))
  (when restart
    (message "pyim 重启完成。"))
  nil)

(defun pyim-exit-from-minibuffer ()
  "Pyim 从 minibuffer 退出."
  (deactivate-input-method)
  (when (<= (minibuffer-depth) 1)
    (remove-hook 'minibuffer-exit-hook 'quail-exit-from-minibuffer)))

(defun pyim-restart ()
  "重启 pyim，不建议用于编程环境.

这个函数用于重启 pyim，其过程和 `pyim-start' 类似，只是在输入法重
启之前，询问用户，是否保存个人词频信息。"
  (interactive
   (let ((save-personal-dcache
          (yes-or-no-p "重启 pyim 前，需要保存个人词频信息吗？ "))
         (refresh-common-dcache
          (yes-or-no-p "需要强制刷新词库缓存吗？ ")))
     (pyim-restart-1 save-personal-dcache refresh-common-dcache))))

(defun pyim-restart-1 (&optional save-personal-dcache refresh-common-dcache)
  "重启 pyim，用于编程环境.

当 SAVE-PERSONAL-DCACHE 是 non-nil 时，保存个人词库文件。
当 REFRESH-COMMON-DCACHE 是 non-nil 时，强制刷新词库缓存。"
  (pyim-start "pyim" nil t
              save-personal-dcache refresh-common-dcache))

(defun pyim-create-dicts-md5 (dict-files)
  (let* ((version "v1") ;当需要强制更新 dict 缓存时，更改这个字符串。
         (dicts-md5 (md5 (prin1-to-string
                          (mapcar #'(lambda (file)
                                      (list version file (nth 5 (file-attributes file 'string))))
                                  dict-files)))))
    dicts-md5))

(defun pyim-dcache-call-api (api-name &rest api-args)
  "Get backend API named API-NAME then call it with arguments API-ARGS."
  ;; make sure the backend is load
  (unless (featurep pyim-dcache-backend)
    (require pyim-dcache-backend))
  (let ((func (intern (concat (symbol-name pyim-dcache-backend)
                              "-" (symbol-name api-name)))))
    (if (functionp func)
        (apply func api-args)
      (when pyim-debug
        (message "%S 不是一个有效的 dcache api 函数." (symbol-name func))
        ;; Need to return nil
        nil))))

(defun pyim-dcache-update-code2word (&optional force)
  "读取并加载词库.

读取 `pyim-dicts' 和 `pyim-extra-dicts' 里面的词库文件，生成对应的
词库缓冲文件，然后加载词库缓存。

如果 FORCE 为真，强制加载。"
  (let* ((dict-files (mapcar #'(lambda (x)
                                 (unless (plist-get x :disable)
                                   (plist-get x :file)))
                             `(,@pyim-dicts ,@pyim-extra-dicts)))
         (dicts-md5 (pyim-create-dicts-md5 dict-files)))
    (pyim-dcache-call-api 'update-code2word dict-files dicts-md5 force)))

(defun pyim-dcache-init-variables ()
  "初始化 dcache 缓存相关变量."
  (pyim-dcache-call-api 'init-variables))

(defun pyim-dcache-save-caches ()
  "保存 dcache.

  将用户选择过的词生成的缓存和词频缓存的取值
  保存到它们对应的文件中.

  这个函数默认作为 `kill-emacs-hook' 使用。"
  (interactive)
  (pyim-dcache-call-api 'save-personal-dcache-to-file)
  t)

(defun pyim-export (file &optional confirm)
  "将个人词条以及词条对应的词频信息导出到文件 FILE.

  如果 FILE 为 nil, 提示用户指定导出文件位置, 如果 CONFIRM 为 non-nil，
  文件存在时将会提示用户是否覆盖，默认为覆盖模式"
  (interactive "F将词条相关信息导出到文件: ")
  (with-temp-buffer
    (insert ";;; -*- coding: utf-8-unix -*-\n")
    (pyim-dcache-call-api 'insert-export-content)
    (pyim-dcache-write-file file confirm)))

(defun pyim-export-personal-words (file &optional confirm)
  "将用户选择过的词生成的缓存导出为 pyim 词库文件.

如果 FILE 为 nil, 提示用户指定导出文件位置, 如果 CONFIRM 为 non-nil，
文件存在时将会提示用户是否覆盖，默认为覆盖模式。

注： 这个函数的用途是制作 pyim 词库，个人词条导入导出建议使用：
`pyim-import' 和 `pyim-export' ."
  (interactive "F将个人缓存中的词条导出到文件：")
  (pyim-dcache-call-api 'export-personal-words file confirm))

(defun pyim-import (file &optional merge-method)
  "从 FILE 中导入词条以及词条对应的词频信息。

MERGE-METHOD 是一个函数，这个函数需要两个数字参数，代表
词条在词频缓存中的词频和待导入文件中的词频，函数返回值做为合并后的词频使用，
默认方式是：取两个词频的最大值。"
  (interactive "F导入词条相关信息文件: ")
  (with-temp-buffer
    (let ((coding-system-for-read 'utf-8-unix))
      (insert-file-contents file))
    (goto-char (point-min))
    (forward-line 1)
    (while (not (eobp))
      (let* ((content (pyim-dline-parse))
             (word (car content))
             (count (string-to-number
                     (or (car (cdr content)) "0"))))
        (pyim-create-word
         word nil
         (lambda (x)
           (funcall (or merge-method #'max)
                    (or x 0)
                    count))))
      (forward-line 1)))
  ;; 保存一下用户选择过的词生成的缓存和词频缓存，
  ;; 因为使用 async 机制更新 dcache 时，需要从 dcache 文件
  ;; 中读取变量值, 然后再对用户选择过的词生成的缓存排序，如果没
  ;; 有这一步骤，导入的词条就会被覆盖，使用 emacs-thread 机制来更新 dcache
  ;; 不存在此问题。
  (unless pyim-prefer-emacs-thread
    (pyim-dcache-save-caches))
  ;; 更新相关的 dcache
  (pyim-dcache-call-api 'update-personal-words t)

  (message "pyim: 词条相关信息导入完成！"))

;; ** 从词库中搜索中文词条
(defun pyim-dcache-get (code &optional from)
  "从 FROM 对应的 dcache 中搜索 CODE, 得到对应的词条.

当词库文件加载完成后，pyim 就可以用这个函数从词库缓存中搜索某个
code 对应的中文词条了."
  (pyim-dcache-call-api 'get code from))

(defun pyim-pinyin-build-regexp (pinyin &optional match-beginning first-equal all-equal)
  "从 PINYIN 构建一个 regexp，用于搜索联想词，
比如：ni-hao-si-j --> ^ni-hao[a-z]*-si[a-z]*-j[a-z]* , when FIRST-EQUAL set to `t'
                  --> ^ni[a-z]*-hao[a-z]*-si[a-z]*-j[a-z]* , when FIRST-EQUAL set to `nil'"
  (when (and pinyin (stringp pinyin))
    (let ((pinyin-list (split-string pinyin "-"))
          (count 0))
      (concat (if match-beginning "^" "")
              (mapconcat
               #'(lambda (x)
                   (setq count (+ count 1))
                   (if (or (not first-equal) (> count 1))
                       (if all-equal
                           x
                         (concat x "[a-z]*"))
                     x))
               pinyin-list "-")))))

(defun pyim-insert-word-into-icode2word (word pinyin prepend)
  (pyim-dcache-call-api 'insert-word-into-icode2word word pinyin prepend))

(defun pyim-create-word (word &optional prepend wordcount-handler)
  "将中文词条 WORD 添加编码后，保存到用户选择过的词生成的缓存中。

词条 WORD 默认会追加到已有词条的后面，如果 PREPEND 设置为 t,
词条就会放到已有词条的最前面。

根据当前输入法，决定是调用 `pyim-hanzi2pinyin' 还是
`pyim-hanzi2xingma' 来获取中文词条的编码。

WORDCOUNT-HANDLER 可以是一个数字，代表将此数字设置为 WORD 的新词频，
WORDCOUNT-HANDLER 也可以是一个函数，其返回值将设置为 WORD 的新词频，
而这个函数的参数则表示 WORD 当前词频，这个功能用于：`pyim-import',
如果 WORDCOUNT-HANDLER 设置为其他, 则表示让 WORD 当前词频加1.

BUG：拼音无法有效地处理多音字。
"
  (when (and (> (length word) 0)
             (< (length word) 11) ;十个汉字以上的词条，加到个人词库里面用处不大，忽略。
             (not (pyim-string-match-p "\\CC" word)))
    ;; 记录最近创建的词条，用于快速删词功能。
    (setq pyim-last-created-word word)
    (let* ((scheme-name (pyim-scheme-name))
           (class (pyim-scheme-get-option scheme-name :class))
           (code-prefix (pyim-scheme-get-option scheme-name :code-prefix))
           (codes (if (eq class 'xingma)
                      (pyim-hanzi2xingma word scheme-name t)
                    ;;拼音使用了多音字校正
                    (pyim-hanzi2pinyin word nil "-" t nil t))))
      ;; 保存对应词条的词频
      (when (> (length word) 0)
        (pyim-dcache-call-api
         'update-iword2count
         word
         prepend
         wordcount-handler))
      ;; 添加词条到个人缓存
      (dolist (code codes)
        (unless (pyim-string-match-p "[^ a-z-]" code)
          (pyim-insert-word-into-icode2word word
                                            (concat (or code-prefix "") code)
                                            prepend)))
      ;; TODO, 排序个人词库?
      )))

(defun pyim-hanzi2xingma (string scheme-name &optional return-list)
  "返回汉字 STRING 对应形码方案 SCHEME-NAME 的 code (不包括
code-prefix)。当RETURN-LIST 设置为 t 时，返回一个 code list。"
  (let* ((fun (intern (concat "pyim-hanzi2xingma:" (symbol-name scheme-name))))
         (code (and fun (funcall fun string))))
    (when code
      (if return-list
          (list code)
        code))))

(defun pyim-hanzi2xingma:wubi (string)
  "返回汉字 STRING 的五笔编码(不包括 code-prefix)。当RETURN-LIST
设置为 t 时，返回一个编码列表。"
  (when (string-match-p "^\\cc+\\'" string)
    (let ((code (pyim-code-search string 'wubi))
          (len (length string)))
      (when (string-empty-p code)
        (when (= len 1)
          (error "No code found for %s" string))
        (setq string (split-string string "" t)
              code
              (cl-case len
                ;; 双字词，分别取两个字的前两个编码
                (2 (concat (substring (pyim-hanzi2xingma:wubi (nth 0 string)) 0 2)
                           (substring (pyim-hanzi2xingma:wubi (nth 1 string)) 0 2)))
                ;; 三字词，取前二字的首编码，及第三个字的前两个编码
                (3 (concat (substring (pyim-hanzi2xingma:wubi (nth 0 string)) 0 1)
                           (substring (pyim-hanzi2xingma:wubi (nth 1 string)) 0 1)
                           (substring (pyim-hanzi2xingma:wubi (nth 2 string)) 0 2)))
                ;; 四字词及以上，分别前三个字及最后一个字的首编码
                (t (concat (substring (pyim-hanzi2xingma:wubi (nth 0 string)) 0 1)
                           (substring (pyim-hanzi2xingma:wubi (nth 1 string)) 0 1)
                           (substring (pyim-hanzi2xingma:wubi (nth 2 string)) 0 1)
                           (substring (pyim-hanzi2xingma:wubi (nth (1- len) string)) 0 1))))))
      code)))

(defun pyim-list-merge (a b)
  "Join list A and B to a new list, then delete dups."
  (let ((a (if (listp a)
               a
             (list a)))
        (b (if (listp b)
               b
             (list b))))
    (delete-dups `(,@a ,@b))))

(defun pyim-cstring-at-point (&optional number)
  "获取光标一个中文字符串，字符数量为：NUMBER."
  (save-excursion
    (let* ((point (point))
           (begin (- point number))
           (begin (if (> begin 0)
                      begin
                    (point-min)))
           (string (buffer-substring-no-properties
                    point begin)))
      (when (and (stringp string)
                 (= (length string) number)
                 (not (pyim-string-match-p "\\CC" string)))
        string))))

(defun pyim-create-word-at-point (&optional number silent)
  "将光标前字符数为 NUMBER 的中文字符串添加到个人词库中
当 SILENT 设置为 t 是，不显示提醒信息。"
  (let* ((string (pyim-cstring-at-point (or number 2))))
    (when string
      (pyim-create-word string)
      (unless silent
        (message "将词条: \"%s\" 加入 personal 缓冲。" string)))))

(defun pyim-create-2cchar-word-at-point ()
  "将光标前2个中文字符组成的字符串加入个人词库。"
  (interactive)
  (pyim-create-word-at-point 2))

(defun pyim-create-3cchar-word-at-point ()
  "将光标前3个中文字符组成的字符串加入个人词库。"
  (interactive)
  (pyim-create-word-at-point 3))

(defun pyim-create-4cchar-word-at-point ()
  "将光标前4个中文字符组成的字符串加入个人词库。"
  (interactive)
  (pyim-create-word-at-point 4))

;; ** 删词功能
(defun pyim-create-word-from-selection ()
  "Add the selected text as a Chinese word into the personal dictionary."
  (interactive)
  (when (region-active-p)
    (let ((string (buffer-substring-no-properties (region-beginning) (region-end))))
      (if (> (length string) 6)
          (error "词条太长")
        (if (not (string-match-p "^\\cc+\\'" string))
            (error "不是纯中文字符串")
          (pyim-create-word string)
          (message "将词条: %S 插入 personal file。" string))))))

(defun pyim-search-word-code ()
  "选择词条，然后反查它的 code. 这个功能对五笔用户有用。"
  (interactive)
  (when (region-active-p)
    (let* ((string (buffer-substring-no-properties (region-beginning) (region-end)))
           code)
      (if (not (string-match-p "^\\cc+\\'" string))
          (error "不是纯中文字符串")
        (setq code (pyim-dcache-call-api 'search-word-code string))
        (if code
            (message "%S -> %S " string code)
          (message "没有找到 %S 对应的编码。" string))))))

(defun pyim-delete-words-in-file (file)
  "从个人词库缓存中批量删除 FILE 文件中列出的词条.

FILE 的格式与 `pyim-export' 生成的文件格式相同，
另外这个命令也可以识别没有词频的行，比如：

   ;;; -*- coding: utf-8-unix -*-
   词条1
   词条2"
  (interactive "F记录待删词条的文件: ")
  (with-temp-buffer
    (let ((coding-system-for-read 'utf-8-unix))
      (insert-file-contents file))
    (goto-char (point-min))
    (forward-line 1)
    (while (not (eobp))
      (let ((word (car (pyim-dline-parse))))
        (when (and word (not (pyim-string-match-p "\\CC" word)))
          (pyim-delete-word-1 word)))
      (forward-line 1)))
  (message "pyim: 批量删词完成！"))

(defun pyim-delete-last-word ()
  "从个人词库中删除最新创建的词条。"
  (interactive)
  (when pyim-last-created-word
    (pyim-delete-word-1 pyim-last-created-word)
    (message "pyim: 从个人词库中删除词条 “%s” !" pyim-last-created-word)))

(defun pyim-delete-word-at-point (&optional number silent)
  "将光标前字符数为 NUMBER 的中文字符串从个人词库中删除
当 SILENT 设置为 t 是，不显示提醒信息。"
  (let* ((string (pyim-cstring-at-point (or number 2))))
    (when string
      (pyim-delete-word-1 string)
      (unless silent
        (message "词条: \"%s\" 已经从个人词库缓冲中删除。" string)))))

(defun pyim-delete-word ()
  "将高亮选择的词条从个人词库中删除。"
  (interactive)
  (if mark-active
      (let ((string (buffer-substring-no-properties
                     (region-beginning) (region-end))))
        (when (and (< (length string) 6)
                   (> (length string) 0))
          (pyim-delete-word-1 string)
          (message "将词条: %S 从 personal 缓冲中删除。" string)))
    (message "请首先高亮选择需要删除的词条。")))

(defun pyim-delete-word-1 (word)
  "将中文词条 WORD 从个人词库中删除"
  (pyim-dcache-call-api 'delete-word word))

;; ** 处理用户输入字符的相关函数
(defun pyim-input-method (key)
  "得到需要插入到 buffer 的字符串, 并将其插入到待输入 buffer.

这个函数会处理用户输入的字符，并最终的得到需要插入 buffer 的字符
串。这个字符串会被分解为 event list, 通过 emacs 低层函数
`read-event' 来将这些 list 插入到 *待输入buffer*。"
  (if (or buffer-read-only
          overriding-terminal-local-map
          overriding-local-map)
      (list key)
    ;; (message "call with key: %S" key-or-string)
    (pyim-preview-setup-overlay)
    (with-silent-modifications
      (unwind-protect
          (let ((input-string (pyim-start-translation key)))
            ;; (message "input-string: %s" input-string)
            (when (and (stringp input-string)
                       (> (length input-string) 0))
              (if input-method-exit-on-first-char
                  (list (aref input-string 0))
                (mapcar 'identity input-string))))
        (pyim-preview-delete-overlay)
        (pyim-entered-erase-buffer)))))

(defun pyim-magic-convert (str)
  "用于处理 `pyim-magic-convert' 的函数。"
  (if (functionp pyim-magic-converter)
      (or (cdr (assoc str pyim-magic-convert-cache))
          (let ((result (funcall pyim-magic-converter str)))
            (setq pyim-magic-convert-cache
                  `((,str . ,result)))
            result))
    str))

(defun pyim-start-translation (key)
  "Start translation of the typed character KEY-OR-STRING by pyim.
Return the input string.

`pyim-start-translation' 这个函数较复杂，作许多低层工作，但它的一
个重要流程是：

1. 使用函数 `read-key-sequence' 得到 key-sequence
2. 使用函数 `lookup-key' 查询 `pyim-mode-map' 中，与上述 key-sequence 对应
   的命令。
3. 如果查询得到的命令是 `pyim-self-insert-command' 时，
   `pyim-start-translation' 会调用这个函数。
4. 这个函数最终会返回需要插入到 buffer 的字符串。

这个部份的代码涉及许多 emacs 低层函数，相对复杂，不容易理解，有兴
趣的朋友可以参考：
1. `quail-input-method' 相关函数。
2. elisp 手册相关章节:
   1. Invoking the Input Method
   2. Input Methods
   3. Miscellaneous Event Input Features
   4. Reading One Event"
  ;; Check the possibility of translating KEY.
  ;; If KEY is nil, we can anyway start translation.
  (if (or (integerp key) (null key))
      ;; OK, we can start translation.
      (let* ((echo-keystrokes 0)
             (help-char nil)
             (overriding-terminal-local-map pyim-mode-map)
             (generated-events nil)
             (input-method-function nil)
             ;; Quail package 用这个变量来控制是否在 buffer 中
             ;; 插入 preview string, pyim *强制* 将其设置为 nil
             (input-method-use-echo-area nil)
             (modified-p (buffer-modified-p))
             last-command-event last-command this-command)

        (setq pyim-translating t)
        (pyim-entered-erase-buffer)
        (pyim-outcome-handle "")

        (when key
          (setq unread-command-events
                (cons key unread-command-events)))

        (while pyim-translating
          (set-buffer-modified-p modified-p)
          (let* ((keyseq (read-key-sequence nil nil nil t))
                 (cmd (lookup-key pyim-mode-map keyseq)))
            ;; (message "key: %s, cmd:%s\nlcmd: %s, lcmdv: %s, tcmd: %s"
            ;;          key cmd last-command last-command-event this-command)
            (if (if key
                    (commandp cmd)
                  (eq cmd 'pyim-self-insert-command))
                (progn
                  ;; (message "keyseq: %s" keyseq)
                  (setq last-command-event (aref keyseq (1- (length keyseq)))
                        last-command this-command
                        this-command cmd)
                  (setq key t)
                  (condition-case-unless-debug err
                      (call-interactively cmd)
                    (error (message "pyim 出现错误: %S , 开启 debug-on-error 后可以了解详细情况。" err)
                           (beep))))
              ;; KEYSEQ is not defined in the translation keymap.
              ;; Let's return the event(s) to the caller.
              (setq unread-command-events
                    (string-to-list (this-single-command-raw-keys)))
              ;; (message "unread-command-events: %s" unread-command-events)
              (pyim-terminate-translation))))
        ;; (message "return: %s" (pyim-outcome-get))
        (pyim-magic-convert (pyim-outcome-get)))
    ;; Since KEY doesn't start any translation, just return it.
    ;; But translate KEY if necessary.
    (char-to-string key)))

(defun pyim-auto-switch-english-input-p ()
  "判断是否 *根据环境自动切换* 为英文输入模式，这个函数处理变量：
`pyim-english-input-switch-functions'"
  (let* ((func-or-list pyim-english-input-switch-functions))
    (and (cl-some #'(lambda (x)
                      (if (functionp x)
                          (funcall x)
                        nil))
                  (cond ((functionp func-or-list) (list func-or-list))
                        ((listp func-or-list) func-or-list)
                        (t nil)))
         (setq current-input-method-title
               (concat pyim-title
                       (if pyim-input-ascii
                           "-英文"
                         "-AU英"))))))

(defun pyim-input-chinese-p ()
  "确定 pyim 是否需要启动中文输入模式."
  (let* ((scheme-name (pyim-scheme-name))
         (first-chars (pyim-scheme-get-option scheme-name :first-chars))
         (rest-chars (pyim-scheme-get-option scheme-name :rest-chars)))
    (and (or pyim-force-input-chinese
             (and (not pyim-input-ascii)
                  (not (pyim-auto-switch-english-input-p))))
         (if (not (string< "" (pyim-entered-get)))
             (member last-command-event
                     (mapcar 'identity first-chars))
           (member last-command-event
                   (mapcar 'identity rest-chars)))
         (setq current-input-method-title pyim-title))))

(defun pyim-autoselector-xingma (&rest args)
  "适用于型码输入法的自动上屏器.

比如：五笔等型码输入法，重码率很低，90%以上的情况都是选择第一个词
条，自动选择可以减少按空格强制选词的机会。"
  (let* ((scheme-name (pyim-scheme-name))
         (class (pyim-scheme-get-option scheme-name :class))
         (n (pyim-scheme-get-option scheme-name :code-split-length)))
    (and (eq class 'xingma)
         (= (length (pyim-entered-get)) n))))

(defun pyim-self-insert-command ()
  "Pyim 版本的 self-insert-command."
  (interactive "*")
  (cond
   ;; 自动上屏器设置： 自动上屏器是一个函数，如果这个函数返回t, 就自
   ;; 动上屏。
   ((cl-some #'(lambda (x)
                 (when (functionp x)
                   (funcall x)))
             pyim-autoselector)
    (push last-command-event unread-command-events)
    (unless (equal pyim-candidates (list (pyim-entered-get)))
      (pyim-outcome-handle 'candidate))
    (pyim-terminate-translation))
   ((pyim-input-chinese-p)
    (pyim-with-entered-buffer
      (insert (char-to-string last-command-event)))
    (pyim-entered-refresh))
   (pyim-candidates
    (pyim-outcome-handle 'candidate-and-last-char)
    (pyim-terminate-translation))
   (t
    (pyim-outcome-handle 'last-char)
    (pyim-terminate-translation))))

(defun pyim-entered-refresh-1 ()
  "查询 `pyim-entered-buffer' 光标前的拼音字符串（如果光标在行首则为光标后的）, 显示备选词等待用户选择。"
  (let* ((scheme-name (pyim-scheme-name))
         pinyin-to-translate)
    (pyim-with-entered-buffer
      (setq pinyin-to-translate
            (if (equal 1 (point))
                (buffer-string)
              (buffer-substring-no-properties 1 (point)))))
    (setq pyim-imobjs (pyim-imobjs-create pinyin-to-translate scheme-name))
    (setq pyim-candidates
          (or (delete-dups (pyim-candidates-create pyim-imobjs scheme-name))
              (list pinyin-to-translate)))
    (setq pyim-candidate-position 1)
    (pyim-preview-refresh)
    (pyim-page-refresh)))

(defun pyim-entered-refresh (&optional no-delay)
  "延迟 `pyim-exhibit-delay-ms' 显示备选词等待用户选择。"
  (if (= (length (pyim-entered-get)) 0)
      (pyim-terminate-translation)
    (when pyim--exhibit-timer
      (cancel-timer pyim--exhibit-timer))
    (cond
     ((or no-delay
          (not pyim-exhibit-delay-ms)
          (eq pyim-exhibit-delay-ms 0))
      (pyim-entered-refresh-1))
     (t (setq pyim--exhibit-timer
              (run-with-timer (/ pyim-exhibit-delay-ms 1000.0)
                              nil
                              #'pyim-entered-refresh-1))))))

(defun pyim-terminate-translation ()
  "Terminate the translation of the current key."
  (setq pyim-translating nil)
  (pyim-preview-delete-string)
  (setq pyim-candidates nil)
  (setq pyim-assistant-scheme-enable nil)
  (setq pyim-force-input-chinese nil)
  (when (and (memq pyim-page-tooltip '(posframe child-frame))
             (pyim-posframe-valid-p))
    (posframe-hide pyim-page-tooltip-posframe-buffer))
  (pyim-entered-erase-buffer))

;; 分解拼音的相关函数
(defun pyim-pinyin-get-shenmu (pinyin)
  "从一个拼音字符串 PINYIN 中提出第一个声母。"
  (let ((i (min (length pinyin) 2))
        shenmu)
    (while (> i 0)
      (setq shenmu (substring pinyin 0 i))
      (if (member shenmu pyim-pinyin-shenmu)
          (setq i 0)
        (setq i (1- i))
        (setq shenmu "")))
    (cons shenmu
          (substring pinyin (length shenmu)))))

(defun pyim-pinyin-get-charpy (pinyin)
  "将拼音字符串 PINYIN 分解成声母，韵母和剩余部分."
  (let* ((x (pyim-pinyin-get-shenmu pinyin))
         (shenmu (car x))
         (yunmu-and-rest (cdr x))
         (i (min (length yunmu-and-rest) 5))
         yunmu rest result)
    (cl-flet ((pinyin-valid-p
               (shenmu yunmu)
               (cl-some
                #'(lambda (char-pinyin)
                    (pyim-pinyin2cchar-get char-pinyin t))
                (mapcar #'(lambda (x)
                            (concat (nth 0 x) (nth 1 x)))
                        (pyim-imobjs-find-fuzzy:quanpin-1
                         (list shenmu yunmu shenmu yunmu))))))
      (while (> i 0)
        (setq yunmu (substring yunmu-and-rest 0 i))
        (setq rest (substring yunmu-and-rest i))
        (if (member yunmu pyim-pinyin-yunmu)
            (cond (;; 如果声母和韵母组成的拼音不是一个有效的拼音，
                   ;; 就继续缩短，如果是，就进一步检测。
                   (not (pinyin-valid-p shenmu yunmu))
                   (setq i (1- i))
                   (setq yunmu ""))
                  ((and (string< "" rest)
                        ;; 截取后剩余的字符串 rest 找不出声母
                        (equal (car (pyim-pinyin-get-shenmu rest)) "")
                        ;; 截取后的韵母最后一个字符是一个有效声母
                        (member (substring yunmu -1) pyim-pinyin-shenmu)
                        ;; 截取得到的韵母如果去掉最后一个字符，还是有效的韵母
                        (member (substring yunmu 0 -1) pyim-pinyin-yunmu))
                   (if (not (pinyin-valid-p shenmu (substring yunmu 0 -1)))
                       ;; 如果去掉韵母最后一个字符后，无法组成一个有效的拼音。
                       ;; 就不要缩短了。
                       (setq i 0)
                     (setq i (1- i))
                     (setq yunmu "")))
                  (t (setq i 0)))
          (setq i (1- i))
          (setq yunmu ""))))
    (cons (list shenmu yunmu shenmu yunmu)
          (substring yunmu-and-rest (length yunmu)))))

(defun pyim-pinyin-split (pinyin)
  "将一个代表拼音的字符串 PINYIN, 分解为声母韵母对组成的列表.

这个过程通过循环的调用 `pyim-pinyin-get-charpy' 来实现，整个过程
类似用菜刀切黄瓜片，将一个拼音字符串逐渐切开。"
  (let ((py pinyin)
        charpy spinyin)
    (while (when (string< "" pinyin)
             (setq charpy (pyim-pinyin-get-charpy pinyin))
             (if (and (equal (nth 0 (car charpy)) "")
                      (equal (nth 1 (car charpy)) ""))
                 (progn
                   (setq spinyin nil)
                   (setq pinyin ""))
               (setq spinyin (append spinyin (list (car charpy))))
               (setq pinyin (cdr charpy)))))
    (or spinyin
        ;; 如果无法按照拼音的规则来分解字符串，
        ;; 就将字符串简单的包装一下，然后返回。
        ;; 目前这个功能用于： 以u或者i开头的词库 #226
        ;; https://github.com/tumashu/pyim/issues/226
        (list (list "" py "" py)))))

(defun pyim-scheme-get (scheme-name)
  "获取名称为 SCHEME-NAME 的输入法方案。"
  (assoc scheme-name pyim-schemes))

(defun pyim-scheme-name (&optional default)
  "获取输入法 scheme"
  (let (scheme-name)
    (if (and pyim-assistant-scheme-enable
             (not default))
        (setq scheme-name
              (or pyim-assistant-scheme
                  pyim-default-scheme))
      (setq scheme-name pyim-default-scheme))
    (if (assq scheme-name pyim-schemes)
        scheme-name
      (message "Pyim: invalid scheme, fallback to quanpin scheme.")
      'quanpin)))

(defun pyim-toggle-assistant-scheme ()
  "临时切换到辅助输入法.

这个功能一般用于五笔等形码输入法，在忘记编码的时候临时用拼音输入
中文。"
  (interactive)
  (if (= (length (pyim-entered-get)) 0)
      (progn
        (pyim-outcome-handle 'last-char)
        (pyim-terminate-translation))
    (setq pyim-assistant-scheme-enable
          (not pyim-assistant-scheme-enable))
    (pyim-entered-refresh)))

(defun pyim-scheme-get-option (scheme-name option)
  "获取名称为 SCHEME-NAME 的输入法方案，并提取其属性 OPTION 。"
  (let ((scheme (pyim-scheme-get scheme-name)))
    (when scheme
      (plist-get (cdr scheme) option))))

(defun pyim-imobjs-create (entered &optional scheme-name)
  "按照 SCHEME-NAME 对应的输入法方案，从 ENTERED 字符串中创建一个
或者多个 imobj 组成的列表，不同的输入法，imobj 的结构也是不一样的。"
  (let ((class (pyim-scheme-get-option scheme-name :class)))
    (when class
      (funcall (intern (format "pyim-imobjs-create:%S" class))
               entered scheme-name))))

(defun pyim-imobjs-create:quanpin (entered &optional -)
  "从用户输入的字符串 ENTERED 创建一个输入法内部对象列表: imobjs.

这个 imobjs 可能包含一个 imobj, 也可能包含多个，每个 imobj 都包含
声母和韵母的相关信息，比如：

    (pyim-imobjs-create:quanpin \"woaimeinv\" 'quanpin)

结果为:

    (((\"w\" \"o\" \"w\" \"o\") (\"\" \"ai\" \"\" \"ai\") (\"m\" \"ei\" \"m\" \"ei\") (\"n\" \"v\" \"n\" \"v\")))

如果字符串无法正确处理，则返回 nil, 比如：

   (pyim-imobjs-create \"ua\" 'quanpin)

全拼输入法的 imelem 是四个字符串组成的 list, 类似：

  (\"w\" \"o\" \"w\" \"o\")

代表：

  (声母1, 韵母1, 声母2, 韵母2)

声母1和声母2一般用来生成 code 字符串，用于词库中寻找词条。声母2和
韵母2一般用来反向构建 entered 字符串，用于“多次选择生成词条”这个
功能。

大多数情况，声母1 = 声母2, 韵母1 = 韵母2, 只有在使用糢糊音的时候，
才可能出现不一致的情况。"
  (when (and entered (string< "" entered))
    (let* ((str-list (remove "" (split-string entered "'")))
           (n (length str-list))
           output)
      (dotimes (i n)
        (let* ((str (nth i str-list))
               (x (pyim-pinyin-split str)))
          (if (not x)
              (setq output nil)
            (when (> i 0)
              ;; 将强制分割符号附加到封分割符后面的声母开头，
              ;; 类似： ("'n" "i" "n" "i"), 用于 `pyim-page-preview-create' 函数。
              (setf (caar x)
                    (concat "'" (caar x))))
            (setq output (append output x)))))
      (when output
        (pyim-imobjs-find-fuzzy:quanpin (list output))))))

;; "nihc" -> (((\"n\" \"i\" \"n\" \"i\") (\"h\" \"ao\" \"h\" \"c\")))
(defun pyim-imobjs-create:shuangpin (entered &optional scheme-name)
  (let ((keymaps (pyim-scheme-get-option scheme-name :keymaps))
        (list (string-to-list (replace-regexp-in-string "-" "" entered)))
        results)
    (while list
      (let* ((sp-sm (pop list))
             (sp-ym (pop list))
             (sp-sm (when sp-sm (char-to-string sp-sm)))
             (sp-ym (when sp-ym (char-to-string sp-ym)))
             (sm (nth 1 (assoc sp-sm keymaps)))
             (ym (or (cdr (cdr (assoc sp-ym keymaps))) (list "")))
             one-word-pinyins)

        (dolist (x ym)
          (let* ((y (concat sp-sm (or sp-ym " ")))
                 (z (cadr (assoc y keymaps)))
                 (py (if z (list "" z sp-sm sp-ym) (list sm x sp-sm sp-ym))))
            (unless (string-match-p pyim-shuangpin-invalid-pinyin-regexp
                                    (concat (nth 0 py) (nth 1 py)))
              (push py one-word-pinyins))))

        (when (and one-word-pinyins (> (length one-word-pinyins) 0))
          (push one-word-pinyins results))))
    (pyim-imobjs-find-fuzzy:quanpin
     (pyim-permutate-list (nreverse results)))))

(defun pyim-imobjs-create:xingma (entered &optional scheme-name)
  (let ((n (pyim-scheme-get-option scheme-name :code-split-length)))
    (let (output)
      (mapc (lambda (x)
              (while (not (string-empty-p x))
                (if (< (length x) n)
                    (progn
                      (push x output)
                      (setq x ""))
                  (push (substring x 0 n) output)
                  (setq x (substring x n)))))
            (split-string entered "'"))
      (list (nreverse output)))))

(defun pyim-imobjs-create:rime (entered &optional -)
  (list (list entered)))

(defun pyim-imobjs-find-fuzzy:quanpin (imobjs)
  "用于处理模糊音的函数。"
  (let (fuzzy-imobjs result1 result2)
    (dolist (imobj imobjs)
      (setq fuzzy-imobjs
            (pyim-permutate-list
             (mapcar 'pyim-imobjs-find-fuzzy:quanpin-1 imobj)))
      (push (car fuzzy-imobjs) result1)
      (setq result2 (append result2 (cdr fuzzy-imobjs))))
    (append result1 result2)))

;; (\"f\" \"en\" \"f\" \"en\") -> ((\"f\" \"en\" \"f\" \"en\") (\"f\" \"eng\" \"f\" \"en\"))
(defun pyim-imobjs-find-fuzzy:quanpin-1 (imelem)
  "Find all fuzzy pinyins."
  (cl-labels ((find-list (str list)
                         (let (result)
                           (dolist (x list)
                             (when (member str x)
                               (setq list nil)
                               (setq result
                                     (delete-dups
                                      `(,str ,@(cl-copy-list x))))))
                           (or result (list str)))))
    (let* ((fuzzy-alist pyim-fuzzy-pinyin-alist)
           (sm-list (find-list (nth 0 imelem) fuzzy-alist))
           (ym-list (find-list (nth 1 imelem) fuzzy-alist))
           result)
      (dolist (a sm-list)
        (dolist (b ym-list)
          (push `(,a ,b ,@(nthcdr 2 imelem)) result)))
      (reverse result))))

(defun pyim-entered-next-imelem-position (num &optional search-forward start)
  "从 `pyim-entered-buffer' 的当前位置，找到下一个或者下 NUM 个 imelem 对应的位置

如果 SEARCH-FORWARD 为 t, 则向前搜索，反之，向后搜索。"
  (pyim-with-entered-buffer
    (let* ((scheme-name (pyim-scheme-name))
           (start (or start (point)))
           (end-position start)
           (string (buffer-substring-no-properties (point-min) start))
           (orig-imobj-len (length (car (pyim-imobjs-create string scheme-name))))
           imobj)
      (if search-forward
          ;; "ni|haoshijie" -> "nihao|shijie"
          (progn
            (setq pos (point-max))
            (while (and (> pos start) (= end-position start))
              (setq string (buffer-substring-no-properties (point-min) pos)
                    imobj (car (pyim-imobjs-create string scheme-name)))
              (if (>= (+ orig-imobj-len num) (length imobj))
                  (setq end-position pos)
                (cl-decf pos))))
        ;; "nihao|shijie" -> "ni|haoshijie"
        (if (<= orig-imobj-len num)
            (setq end-position (point-min))
          (setq pos start)
          (while (and (>= pos (point-min)) (= end-position start))
            (setq string (buffer-substring-no-properties (point-min) pos)
                  imobj (car (pyim-imobjs-create string scheme-name)))
            (if (= (- orig-imobj-len num) (length imobj))
                (setq end-position pos)
              (cl-decf pos)))))
      end-position)))

(defun pyim-codes-create (imobj scheme-name &optional first-n)
  "按照 SCHEME-NAME 对应的输入法方案，从一个 IMOBJ 创建一个列表 codes, 这个列表
包含一个或者多个 code 字符串，这些 code 字符串用于从词库中搜索词条."
  (let ((class (pyim-scheme-get-option scheme-name :class)))
    (when class
      (funcall (intern (format "pyim-codes-create:%S" class))
               imobj scheme-name first-n))))

(defun pyim-codes-create:quanpin (imobj scheme-name &optional first-n)
  "从IMOBJ 创建一个 code 列表：codes.

列表 codes 中包含一个或者多个 code 字符串，这些 code 字符串用于从
词库中搜索相关词条。

    (pyim-codes-create '((\"w\" \"o\" \"w\" \"o\") (\"\" \"ai\" \"\" \"ai\") (\"m\" \"ei\" \"m\" \"ei\") (\"n\"  \"v\" \"n\"  \"v\")) 'quanpin)

结果为:

   (\"wo\" \"ai\" \"mei\" \"nv\")"
  (mapcar
   #'(lambda (w)
       (let ((py (replace-regexp-in-string ;去掉分隔符，在词库中搜索候选词不需要分隔符
                  "'" "" (concat (nth 0 w) (nth 1 w)))))
         (if (numberp first-n)
             (substring py 0 (min first-n (length py)))
           py)))
   imobj))

(defun pyim-codes-create:shuangpin (imobj scheme-name &optional first-n)
  (pyim-codes-create:quanpin imobj 'quanpin first-n))

(defun pyim-codes-create:xingma (imobj scheme-name &optional first-n)
  (when scheme-name
    (let ((code-prefix (pyim-scheme-get-option scheme-name :code-prefix)))
      (mapcar
       #'(lambda (x)
           (concat (or code-prefix "")
                   (if (numberp first-n)
                       (substring x 0 (min first-n (length x)))
                     x)))
       imobj))))

(defun pyim-codes-create:rime (imobj scheme-name &optional _first-n)
  (when scheme-name
    imobj))

(defun pyim-code-search (word scheme-name)
  "从 SCHEME-NAME 对应的输入法词库中，搜索 WORD 对应的 code.

返回最长的 code."
  (when (and (stringp word)
             (> (length word) 0))
    (let* ((prefix (pyim-scheme-get-option scheme-name :code-prefix))
           (code
            (cl-find-if
             #'(lambda (x)
                 (equal (substring (or x " ") 0 1) prefix))
             (sort
              (cl-copy-list (pyim-dcache-call-api 'search-word-code word))
              #'(lambda (a b) (> (length a) (length b)))))))
      (substring (or code " ") 1))))

;; ** 获取备选词列表
(defun pyim-candidates-create (imobjs scheme-name)
  "按照 SCHEME-NAME 对应的输入法方案， 从输入法内部对象列表:
IMOBJS 获得候选词条。"
  (when imobjs
    (let ((class (pyim-scheme-get-option scheme-name :class)))
      (when class
        (funcall (intern (format "pyim-candidates-create:%S" class))
                 imobjs scheme-name)))))

(defun pyim-candidates-create:xingma (imobjs scheme-name)
  "`pyim-candidates-create' 处理五笔仓颉等形码输入法的函数."
  (let (result)
    (dolist (imobj imobjs)
      (let* ((codes (reverse (pyim-codes-create imobj scheme-name)))
             (output1 (car codes))
             (output2 (reverse (cdr codes)))
             output3 str)

        (when output2
          (setq str (mapconcat
                     #'(lambda (code)
                         (car (pyim-dcache-get code)))
                     output2 "")))
        (setq output3
              (remove "" (or (mapcar #'(lambda (x)
                                         (concat str x))
                                     (pyim-dcache-get output1 '(code2word shortcode2word icode2word)))
                             (list str))))
        (setq result (append result output3))))
    (when (car result)
      result)))

(defun pyim-candidates-create:rime (imobjs scheme-name)
  "`pyim-candidates-create' 处理 rime 输入法的函数."
  (when (functionp 'liberime-clear-composition)
    (liberime-clear-composition)
    (let ((s (replace-regexp-in-string
              "-" "" (car (pyim-codes-create (car imobjs) scheme-name)))))
      (dolist (key (string-to-list s))
        (liberime-process-key key))
      (let* ((context (liberime-get-context))
             (menu (alist-get 'menu context))
             (candidates (alist-get 'candidates menu)))
        candidates))))

(defun pyim-candidates-create:quanpin (imobjs scheme-name)
  "`pyim-candidates-create' 处理全拼输入法的函数."
  (let* (;; 如果输入 "ni-hao" ，搜索 code 为 "n-h" 的词条做为联想词。
         ;; 搜索首字母得到的联想词太多，这里限制联想词要大于两个汉字并且只搜索
         ;; 个人文件。
         (jianpin-words
          (when (and (> (length (car imobjs)) 1) pyim-enable-shortcode)
            (pyim-dcache-get
             (mapconcat #'identity
                        (pyim-codes-create (car imobjs) scheme-name 1)
                        "-")
             '(ishortcode2word))))
         znabc-words
         pinyin-chars
         personal-words
         common-words)

    ;; 智能ABC模式，得到尽可能的拼音组合，查询这些组合，得到的词条做
    ;; 为联想词。
    (let* ((codes (pyim-codes-create (car imobjs) scheme-name))
           (n (- (length codes) 1))
           output)
      (dotimes (i (- n 1))
        (let ((lst (cl-subseq codes 0 (- n i))))
          (push (mapconcat #'identity lst "-") output)))
      (dolist (code (reverse output))
        (setq znabc-words (append znabc-words (pyim-dcache-get code)))))

    (dolist (imobj imobjs)
      (setq personal-words
            (append personal-words
                    (pyim-dcache-get
                     (mapconcat #'identity
                                (pyim-codes-create imobj scheme-name)
                                "-")
                     (if pyim-enable-shortcode
                         '(icode2word ishortcode2word)
                       '(icode2word)))))

      (setq common-words (delete-dups common-words))
      (setq common-words
            (let* ((cands (pyim-dcache-get
                           (mapconcat #'identity
                                      (pyim-codes-create imobj scheme-name)
                                      "-")
                           (if pyim-enable-shortcode
                               '(code2word shortcode2word)
                             '(code2word)))))
              (cond
               ((and (> (length cands) 0)
                     (> (length common-words) 0)
                     (or (eq 1 (length imobj))
                         (eq 2 (length imobj))))
                ;; 两个单字或者两字词序列合并,确保常用字词在前面
                (let* ((size (min (length cands) (length common-words)))
                       new-common-words
                       (i 0))
                  ;; 两个序列轮流取出一个元素输入新序列
                  (while (< i size)
                    (push (nth i common-words) new-common-words)
                    (push (nth i cands) new-common-words)
                    (setq i (1+ i)))
                  ;; 较长序列的剩余元素加入新序列
                  (append (nreverse new-common-words)
                          (nthcdr size (cond
                                        ((< size (length cands))
                                         cands)
                                        ((< size (length common-words))
                                         common-words))))))
               (t
                (append common-words cands)))))

      (setq pinyin-chars
            (append pinyin-chars
                    (pyim-dcache-get
                     (car (pyim-codes-create imobj scheme-name))))))

    ;; 使用词频信息，对个人词库得到的候选词排序，
    ;; 第一个词的位置比较特殊，不参与排序，
    ;; 具体原因请参考 `pyim-page-select-word' 中的 comment.
    (setq personal-words
          `(,(car personal-words)
            ,@(pyim-dcache-call-api
               'sort-words (cdr personal-words))))

    ;; Debug
    (when pyim-debug
      (princ (list :imobjs imobjs
                   :personal-words personal-words
                   :common-words common-words
                   :jianpin-words jianpin-words
                   :znabc-words znabc-words
                   :pinyin-chars pinyin-chars)))

    (delete-dups
     (delq nil
           `(,@personal-words
             ,@common-words
             ,@jianpin-words
             ,@znabc-words
             ,@pinyin-chars)))))

(defun pyim-candidates-create:shuangpin (imobjs scheme-name)
  "`pyim-candidates-create' 处理双拼输入法的函数."
  (pyim-candidates-create:quanpin imobjs 'quanpin))

;; ** 待输入字符串预览
(defun pyim-preview-setup-overlay ()
  "设置 pyim 光标处实时预览功能所需要的 overlay.

这个函数会在 `pyim-input-method' 中调用，用于创建 overlay ，并将
其保存到 `pyim-preview-overlay' 变量，overlay 的 face 属性设置为
`pyim-preview-face' ，用户可以使用这个变量来自定义 face"
  (let ((pos (point)))
    (if (overlayp pyim-preview-overlay)
        (move-overlay pyim-preview-overlay pos pos)
      (setq pyim-preview-overlay (make-overlay pos pos))
      (if input-method-highlight-flag
          (overlay-put pyim-preview-overlay 'face 'pyim-preview-face)))))

(defun pyim-preview-delete-overlay ()
  "删除 pyim 光标处实时预览功能所需要的 overlay.

这个函数会在 `pyim-input-method' 中调用，用于删除
`pyim-preview-overlay' 中保存的 overlay。"
  (if (and (overlayp pyim-preview-overlay) (overlay-start pyim-preview-overlay))
      (delete-overlay pyim-preview-overlay)))

(defun pyim-preview-refresh ()
  "刷新光标处预览.

pyim 会使用 emacs overlay 机制在 *待输入buffer* 光标处高亮显示一
个预览字符串，让用户可以查看将要输入的字符串，这个函数用于更新这
个字符串的内容。"
  (let* ((class (pyim-scheme-get-option (pyim-scheme-name) :class))
         (end (pyim-page-end))
         (start (1- (pyim-page-start)))
         (candidates pyim-candidates)
         (pos (1- (min pyim-candidate-position (length candidates))))
         (preview
          (concat (pyim-outcome-get)
                  (pyim-candidate-parse (nth pos candidates)))))
    (when (memq class '(quanpin))
      (let ((rest (mapconcat
                   #'(lambda (py)
                       (concat (nth 0 py) (nth 1 py)))
                   (nthcdr (length preview) (car pyim-imobjs))
                   "'")))
        (when (string< "" rest)
          (setq preview (concat preview rest)))))
    (setq preview (pyim-magic-convert preview))
    ;; Delete old preview string.
    (pyim-preview-delete-string)
    ;; Insert new preview string.
    (insert preview)
    ;; Highlight new preview string.
    (move-overlay pyim-preview-overlay
                  (overlay-start pyim-preview-overlay) (point))))

(defun pyim-preview-delete-string ()
  "删除已经插入 buffer 的 preview 预览字符串。"
  (if (overlay-start pyim-preview-overlay)
      (delete-region (overlay-start pyim-preview-overlay)
                     (overlay-end pyim-preview-overlay))))

;; ** 选词框相关函数
(defun pyim-candidate-parse (candidate)
  (let ((output
         (if (consp candidate)
             (car candidate)
           candidate)))
    (if (stringp output)
        (car (split-string output ":"))
      output)))

(defun pyim-page-current-page ()
  "计算当前选择的词条在第几页面.

细节信息请参考 `pyim-page-refresh' 的 docstring."
  (1+ (/ (1- pyim-candidate-position) pyim-page-length)))

(defun pyim-page-total-page ()
  "计算 page 总共有多少页.

细节信息请参考 `pyim-page-refresh' 的 docstring."
  (1+ (/ (1- (length pyim-candidates)) pyim-page-length)))

(defun pyim-page-start ()
  "计算当前所在页的第一个词条的位置.

细节信息请参考 `pyim-page-refresh' 的 docstring."
  (let ((pos (min (length pyim-candidates) pyim-candidate-position)))
       (1+ (* (/ (1- pos) pyim-page-length) pyim-page-length))))

(defun pyim-page-end (&optional finish)
  "计算当前所在页的最后一个词条的位置，

如果 pyim-candidates 用完，则检查是否有补全。如果 FINISH 为
non-nil，说明，补全已经用完了.

细节信息请参考 `pyim-page-refresh' 的 docstring."
  (let* ((whole (length pyim-candidates))
         (len pyim-page-length)
         (pos pyim-candidate-position)
         (last (* (/ (+ (1- pos) len) len) len)))
    (if (< last whole)
        last
      (if finish
          whole
        (pyim-page-end t)))))

(defun pyim-page-refresh (&optional hightlight-current)
  "刷新 page 页面的函数.

这个函数主要用来处理选词框选词后，刷新显示问题，pyim 使用
`pyim-candidates' 来保存 *待选词列表* ，\"nihao\" 对应的
`pyim-candidates' 的值类似：

     (\"你好\" \"倪皓\" \"泥\" \"你\"  ...  \"慝\")

*待选词列表* 一般都很长，不可能在一页中完全显示，所以 pyim 使用了
page 的概念，比如，上面的 “nihao” 的 *待选词列表* 就可以逻辑的
分成5页：


  第1页   你好  倪皓  泥  你  呢  拟  逆  腻  妮
  第2页   怩    溺    尼  禰  齯  麑  鲵  蜺  衵
  第3页   薿    旎    睨  铌  昵  匿  倪  霓  暱
  第4页   柅    猊    郳  輗  坭  惄  堄  儗  伲
  第5页   祢    慝

`pyim-candidate-position' 的取值以及 `pyim-page-length' 的设定值
（默认设置为9），共同决定了 pyim 需要显示哪一页，比如：

  第1页  你好  倪皓   泥    你  呢  拟  逆  腻  妮
  第2页  怩    溺     尼    禰  齯  麑  鲵  蜺  衵
  第3页  薿[B] 旎     睨[A] 铌  昵  匿  倪  霓  暱[E]
  第4页  柅    猊     郳    輗  坭  惄  堄  儗  伲
  第5页  祢    慝

假设当前选择的词条为 \"睨\", 那么 `pyim-candidate-position' 的取
值为 A 所在的位置。那么：

1. 函数 `pyim-page-current-page' 返回值为3， 说明当前 page 为第3页。
2. 函数 `pyim-page-total-page'  返回值为5，说明 page 共有5页。
3. 函数 `pyim-page-start' 返回 B 所在的位置。
4. 函数 `pyim-page-end' 返回 E 所在的位置。
5. 函数 `pyim-page-refresh' 会从 `pyim-candidates' 中提取一个 sublist:

     (\"薿\" \"旎\" \"睨\" \"铌\" \"昵\" \"匿\" \"倪\" \"霓\" \"暱\")

   这个 sublist 的起点为 `pyim-page-start' 的返回值，终点为
   `pyim-page-end' 的返回值。并保存到一个 hashtable 的
   :candidates 关键字对应的位置，这个 hastable 最终会做为参数传递
   给 `pyim-page-style' 相关的函数，用于生成用于在选词框中显示的
   字符串。"
  (let* ((end (pyim-page-end))
         (start (1- (pyim-page-start)))
         (candidates pyim-candidates)
         (candidate-showed
          (mapcar #'(lambda (x)
                      (if (stringp x)
                          (replace-regexp-in-string ":" "" x)
                        x))
                  (cl-subseq candidates start end)))
         (pos (- (min pyim-candidate-position (length candidates)) start))
         (page-info (make-hash-table)))
    (puthash :current-page (pyim-page-current-page) page-info)
    (puthash :total-page (pyim-page-total-page) page-info)
    (puthash :candidates candidate-showed page-info)
    (puthash :position pos page-info)
    ;; Show page.
    (when (and (null unread-command-events)
               (null unread-post-input-method-events))
      (if (eq (selected-window) (minibuffer-window))
          ;; 在 minibuffer 中输入中文时，使用当前输入的
          ;; 下一行来显示候选词。
          (pyim-minibuffer-message
           (concat "\n" (pyim-page-style:minibuffer page-info)))
        ;; 在普通 buffer 中输入中文时，使用 `pyim-page-tooltip'
        ;; 指定的方式来显示候选词。
        (let ((message-log-max nil))
          (cond
           ((equal (buffer-name) " *temp*")
            ;; when exwm-xim is used, page should be showed
            ;; in minibuffer.
            (message (pyim-page-style:exwm page-info)))
           (pyim-page-tooltip
            (pyim-page-tooltip-show
             (let ((func (intern (format "pyim-page-style:%S" pyim-page-style))))
               (if (functionp func)
                   (funcall func page-info)
                 (pyim-page-style:two-lines page-info)))
             (overlay-start pyim-preview-overlay)))
           (t (message (pyim-page-style:minibuffer page-info)))))))))

(defun pyim-minibuffer-message (string)
  "当在 minibuffer 中使用 pyim 输入中文时，需要将
minibuffer 原来显示的信息和 pyim 选词框整合在一起显示
这个函数就是作这个工作。"
  (message nil)
  (let ((inhibit-quit t)
        point-1)
    (save-excursion
      (insert string)
      (setq point-1 (point)))
    (sit-for 1000000)
    (delete-region (point) point-1)
    (when quit-flag
      (setq quit-flag nil
            unread-command-events '(7)))))

(defun pyim-page-next-page (arg)
  "Pyim page 翻页命令.

原理是：改变 `pyim-candidate-position' 的取值，假设一次只翻一页，
那么这个函数所做的工作就是：
1. 首先将 `pyim-candidate-position' 增加 `pyim-page-length' ，确
   保其指定的位置在下一页。
2. 然后将 `pyim-candidate-position' 的值设定为 `pyim-page-start'
   的返回值，确保 `pyim-candidate-position' 的取值为下一页第一个
   词条的位置。
3. 最后调用 `pyim-page-refresh' 来重新刷新页面。"
  (interactive "p")
  (if (= (length (pyim-entered-get)) 0)
      (progn
        (pyim-outcome-handle 'last-char)
        (pyim-terminate-translation))
    (let ((new (+ pyim-candidate-position (* pyim-page-length arg) 1)))
      (setq maxpos (length pyim-candidates))
      (setq pyim-candidate-position
            (if (> new 0)
                (if (> new maxpos) 1 new)
                maxpos)
            pyim-candidate-position (pyim-page-start))
      (pyim-preview-refresh)
      (pyim-page-refresh))))

(defun pyim-page-previous-page (arg)
  (interactive "p")
  (pyim-page-next-page (- arg)))

(defun pyim-page-next-word (arg)
  (interactive "p")
  (if (= (length (pyim-entered-get)) 0)
      (progn
        (pyim-outcome-handle 'last-char)
        (pyim-terminate-translation))
    (let ((new (+ pyim-candidate-position arg)))
      (setq len (length pyim-candidates))
      (setq pyim-candidate-position
        (if (>= len new)
            (if (> new 0) new len)
            1))
      (pyim-preview-refresh)
      (pyim-page-refresh t))))

(defun pyim-page-previous-word (arg)
  (interactive "p")
  (pyim-page-next-word (- arg)))

(defun pyim-page-preview-create (&optional separator)
  "这个函数用于创建在 page 中显示的预览字符串。

这个预览是在 page 中显示，而 `pyim-preview-refresh' 对应的预览
是在 buffer 光标处显示，两者要做区别。"
  (let* ((scheme-name (pyim-scheme-name))
         (class (pyim-scheme-get-option scheme-name :class)))
    (when class
      (funcall (intern (format "pyim-page-preview-create:%S" class)) separator))))

(defun pyim-page-preview-create:quanpin (&optional separator)
  (let* ((separator (or separator " "))
         (translated (mapconcat #'identity
                                (mapcar
                                 #'(lambda (w)
                                     (concat (nth 0 w) (nth 1 w)))
                                 (car pyim-imobjs))
                                separator)))
    (concat
     ;; | 显示光标位置的字符
     (pyim-with-entered-buffer
       (if (equal 1 (point))
           (concat "|" translated)
         (concat (replace-regexp-in-string (concat separator "'") "'" translated)
                 " |" (buffer-substring-no-properties (point) (point-max)))))
     ;; 用于标记辅助输入法
     (when (and (eq pyim-assistant-scheme 'quanpin)
                (eq pyim-assistant-scheme-enable t))
       (let ((code (pyim-code-search
                    (pyim-candidate-parse
                     (nth (1- pyim-candidate-position)
                          pyim-candidates))
                    (pyim-scheme-name 'default))))
         (if (> (length code) 0)
             (format " [%s](A)" code)
           " (A)"))))))

(defun pyim-page-preview-create:shuangpin (&optional separator)
  (let ((keymaps (pyim-scheme-get-option (pyim-scheme-name) :keymaps))
        result)
    (dolist (w (car pyim-imobjs))
      (let ((sm (nth 0 w))
            (ym (nth 1 w)))
        (if (equal sm "")
            (push (car (rassoc (list ym) keymaps)) result)
          (push
           (concat (cl-some
                    #'(lambda (x)
                        (when (equal sm (nth 1 x))
                          (car x)))
                    keymaps)
                   (cl-some
                    #'(lambda (x)
                        (when (or (equal ym (nth 2 x))
                                  (equal ym (nth 3 x)))
                          (car x)))
                    keymaps))
           result))))
    (mapconcat 'identity
               (reverse result)
               (or separator " "))))

(defun pyim-page-preview-create:rime (&optional _separator)
  (let* ((context (liberime-get-context))
         (composition (alist-get 'composition context))
         (preedit (alist-get 'preedit composition)))
    (or preedit "")))

(defun pyim-page-preview-create:xingma (&optional separator)
  (let* ((scheme-name (pyim-scheme-name)))
    (cl-flet* ((segment (x)
                        (mapconcat #'identity
                                   (car (pyim-imobjs-create x scheme-name))
                                   (or separator " ")))
               (fmt (x)
                    (mapconcat #'segment
                               (split-string x "'")
                               "'")))
      ;; | 显示光标位置的字符
      (pyim-with-entered-buffer
        (if (equal (point) (point-max))
            (fmt (buffer-substring-no-properties (point-min) (point-max)))
          (concat (fmt (buffer-substring-no-properties (point-min) (point)))
                  "| "
                  (fmt (buffer-substring-no-properties (point) (point-max)))))))))

(defun pyim-page-menu-create (candidates position &optional separator)
  "这个函数用于创建在 page 中显示的备选词条菜单。"
  (let ((i 0) result)
    (dolist (candidate candidates)
      (let ((str (if (consp candidate)
                     (concat (car candidate) (cdr candidate))
                   candidate)))
        (setq i (1+ i))
        ;; 高亮当前选择的词条，用于 `pyim-page-next-word'
        (push
         (if (and hightlight-current
                  (= i position))
             (format "%d%s" i
                     (propertize
                      (format "[%s]" str)
                      'face 'pyim-page-selection))
           (format "%d.%s " i str))
         result)))
    (mapconcat #'identity
               (reverse result)
               (or separator ""))))

(defun pyim-page-style:two-lines (page-info)
  "将 PAGE-INFO 格式化为选词框中显示的字符串.

样式类似：

+----------------------------+
| ni hao [1/9]               |
| 1.你好 2.你号 ...          |
+----------------------------+"
  (format "=> %s [%s/%s]: \n%s"
          (pyim-page-preview-create)
          (gethash :current-page page-info)
          (gethash :total-page page-info)
          (pyim-page-menu-create
           (gethash :candidates page-info)
           (gethash :position page-info))))

(defun pyim-page-style:one-line (page-info)
  "将 PAGE-INFO 格式化为选词框中显示的字符串.

样式类似：

+-----------------------------------+
| [ni hao]: 1.你好 2.你号 ... (1/9) |
+-----------------------------------+"
  (format "[%s]: %s(%s/%s)"
          (pyim-page-preview-create " ")
          (pyim-page-menu-create
           (gethash :candidates page-info)
           (gethash :position page-info))
          (gethash :current-page page-info)
          (gethash :total-page page-info)))

(defun pyim-page-style:vertical (page-info)
  "将 PAGE-INFO 格式化为选词框中显示的字符串.

样式类似：

+--------------+
| ni hao [1/9] |
| 1.你好       |
| 2.你号 ...   |
+--------------+"
  (format "=> %s [%s/%s]: \n%s"
          (pyim-page-preview-create)
          (gethash :current-page page-info)
          (gethash :total-page page-info)
          (pyim-page-menu-create
           (gethash :candidates page-info)
           (gethash :position page-info)
           "\n")))

(defun pyim-page-style:minibuffer (page-info)
  "将 PAGE-INFO 格式化为选词框中显示的字符串.

样式类似：

+------------------------------------+
| [ni hao]: 1.你好 2.你号 ...  (1/9) |
+------------------------------------+"
  (format "[%s]: %s(%s/%s)"
          (pyim-page-preview-create)
          (pyim-page-menu-create
           (gethash :candidates page-info)
           (gethash :position page-info))
          (gethash :current-page page-info)
          (gethash :total-page page-info)))

(defun pyim-page-style:exwm (page-info)
  "专门用于 exwm 环境的 page style."
  (format "[%s]: %s(%s/%s)"
          (let ((class (pyim-scheme-get-option (pyim-scheme-name) :class))
                (preview (pyim-outcome-get)))
            (when (memq class '(quanpin))
              (let ((rest (mapconcat
                           #'(lambda (py)
                               (concat (nth 0 py) (nth 1 py)))
                           (nthcdr (length preview) (car pyim-imobjs))
                           " ")))
                (when (string< "" rest)
                  (setq preview (concat preview rest)))))
            preview)
          (pyim-page-menu-create
           (gethash :candidates page-info)
           (gethash :position page-info))
          (gethash :current-page page-info)
          (gethash :total-page page-info)))

(defun pyim-page-tooltip-show (string position)
  "在 POSITION 位置，使用 posframe 或者 popup 显示字符串 STRING."
  (let ((frame (window-frame (selected-window)))
        (length (* pyim-page-length 10))
        (tooltip pyim-page-tooltip))
    (cond ((and (memq tooltip '(posframe child-frame))
                (pyim-posframe-valid-p))
           (posframe-show pyim-page-tooltip-posframe-buffer
                          :string string
                          :position position
                          :min-width pyim-posframe-min-width
                          :background-color (face-attribute 'pyim-page :background)
                          :foreground-color (face-attribute 'pyim-page :foreground)
                          :internal-border-width pyim-posframe-border-width
                          :internal-border-color (face-attribute 'pyim-page-border :background)))
          ((eq tooltip 'minibuffer)
           (let ((max-mini-window-height (+ pyim-page-length 2)))
             (message string)))
          (t (popup-tip string :point position :margin 1)))))

(defun pyim-posframe-valid-p ()
  "Test posframe's status."
  (and (>= emacs-major-version 26)
       (featurep 'posframe)
       (not (or noninteractive
                emacs-basic-display
                (not (display-graphic-p))))))

(defun pyim-outcome-get (&optional n)
  "获取 outcome"
  (nth (or n 0) pyim-outcome-history))

(defun pyim-outcome-handle (type)
  "依照 TYPE, 获取 pyim 的 outcome，并将其加入 `pyim-outcome-history'."
  (cond ((not enable-multibyte-characters)
         (pyim-entered-erase-buffer)
         (setq pyim-outcome-history nil)
         (error "Can't input characters in current unibyte buffer"))
        ((equal type "")
         (setq pyim-outcome-history nil))
        ((eq type 'last-char)
         (push
          (concat (pyim-outcome-get)
                  (pyim-translate last-command-event))
          pyim-outcome-history))
        ((eq type 'candidate)
         (let* ((candidate
                 (pyim-candidate-parse
                  (nth (1- pyim-candidate-position)
                       pyim-candidates))))
           (push
            (concat (pyim-outcome-get) candidate)
            pyim-outcome-history)))
        ((eq type 'candidate-and-last-char)
         (let* ((candidate
                 (pyim-candidate-parse
                  (nth (1- pyim-candidate-position)
                       pyim-candidates))))
           (push
            (concat (pyim-outcome-get)
                    candidate
                    (pyim-translate last-command-event))
            pyim-outcome-history)))
        ((eq type 'pyim-entered)
         (push (pyim-entered-get) pyim-outcome-history))
        (t (error "Pyim: invalid outcome"))))

(defun pyim-page-select-word-simple ()
  "从选词框中选择当前词条.
这个函数与 `pyim-page-select-word' 的区别是：
这个函数不会将选择的词条加入个人词库，主要的使用场景是：
当用户需要输入一个生僻字时，输入包含该字的一个词条，
然后再删除不需要的字，由于这个词条不是常用词条，所以
不需要保存到个人词库。"
  (interactive)
  (if (null pyim-candidates)
      (pyim-outcome-handle 'last-char)
    (pyim-outcome-handle 'candidate))
  (pyim-terminate-translation))

(defun pyim-page-select-word ()
  "从选词框中选择当前词条，然后删除该词条对应拼音。"
  (interactive)
  (if (null pyim-candidates)  ; 如果没有选项，输入空格
      (progn
        (pyim-outcome-handle 'last-char)
        (pyim-terminate-translation))
    (cl-case (pyim-scheme-get-option (pyim-scheme-name) :class)
      (rime (call-interactively #'pyim-page-select-word:rime))
      (xingma (call-interactively #'pyim-page-select-word:xingma))
      (t (call-interactively #'pyim-page-select-word:pinyin)))))

(defun pyim-page-select-word:pinyin ()
  "从选词框中选择当前词条，然后删除该词条对应拼音。"
  (interactive)
  (pyim-outcome-handle 'candidate)
  (let* ((imobj (car pyim-imobjs))
         (length-selected-word
          ;; 获取 *这一次* 选择词条的长度， 在“多次选择词条才能上屏”的情况下，
          ;; 一定要和 outcome 的概念作区别。
          ;; 比如： xiaolifeidao
          ;; 第一次选择：小李， outcome = 小李
          ;; 第二次选择：飞，   outcome = 小李飞
          ;; 第三次选择：刀，   outcome = 小李飞刀
          (- (length (pyim-outcome-get))
             (length (pyim-outcome-get 1))))
         ;; pyim-imobjs 包含 *pyim-entered-buffer* 里面光标前面的字符串，
         ;; 某些情况只有部分被翻译，剩余部分保存在下面这个变量
         (to-be-translated (mapconcat #'identity
                                      (mapcar
                                       #'(lambda (w)
                                           (concat (nth 2 w) (nth 3 w)))
                                       (nthcdr length-selected-word imobj))
                                      "")))
    ;; 在使用全拼输入法输入长词的时候，可能需要多次选择，才能够将
    ;; 这个词条上屏，这个地方用来判断是否是 “最后一次选择”，如果
    ;; 不是最后一次选择，就需要截断 entered, 准备下一轮的选择。

    ;; 判断方法：entered 为 xiaolifeidao, 本次选择 “小李” 之后，
    ;; 需要将 entered 截断，“小李” 这个词条长度为2, 就将 entered
    ;; 从头开始缩减 2 个 imelem 对应的字符，变成 feidao, 为下一次
    ;; 选择 “飞” 做准备。

    ;; 注意事项： 这里有一个假设前提是： 一个 imelem 对应一个汉字，
    ;; 在全拼输入法中，这个假设大多数情况是成立的，但在型码输入法
    ;; 中，比如五笔输入法，就不成立，好在型码输入法一般不需要多次
    ;; 选择。
    (if (or (< length-selected-word (length imobj))
            (pyim-with-entered-buffer (< (point) (point-max))))
        (progn
          (pyim-with-entered-buffer
            ;; 把本次已经选择的词条对应的子 entered, 从 entered
            ;; 字符串里面剪掉。
            (delete-region (point-min) (point))
            (insert to-be-translated)
            ;; 为下一次选词作准备，一般情况下词库里面的词条不会超过20
            ;; 个汉字，所以这里一次递归的处理20个 imelem. 这种方式
            ;; 可能比逐字选择更加好用。
            (goto-char (pyim-entered-next-imelem-position 20 t 1)))
          (pyim-entered-refresh))
      ;; pyim 词频调整策略：
      ;; 1. 如果一个词条是用户在输入过程中，自己新建的词条，那么就将这个词条
      ;;    添加到个人词库的后面（不放置前面是为了减少误输词条的影响）。
      ;; 2. 如果输入的词条，先前已经在候选词列表中，就自动将其放到第一位。
      ;;    这样的话，一个新词要输入两遍之后才可能出现在第一位。
      ;; 3. pyim 在启动的时候，会使用词频信息，对个人词库作一次排序。
      ;;    用作 pyim 下一次使用。
      (if (member (pyim-outcome-get) pyim-candidates)
          (pyim-create-word (pyim-outcome-get) t)
        (pyim-create-word (pyim-outcome-get)))

      (pyim-terminate-translation)
      ;; pyim 使用这个 hook 来处理联想词。
      (run-hooks 'pyim-page-select-finish-hook))))

(defun pyim-page-select-word:xingma ()
  "从选词框中选择当前词条，然后删除该词条对应编码。"
  (interactive)
  (pyim-outcome-handle 'candidate)
  (if (pyim-with-entered-buffer
        (and (> (point) 1)
             (< (point) (point-max))))
      (progn
        (pyim-with-entered-buffer
          ;; 把本次已经选择的词条对应的子 entered, 从 entered
          ;; 字符串里面剪掉。
          (delete-region (point-min) (point)))
        (pyim-entered-refresh))
    (when (string-empty-p (pyim-code-search (pyim-outcome-get)
                                            (pyim-scheme-name)))
      (pyim-create-word (pyim-outcome-get) t))
    (pyim-terminate-translation)
    ;; pyim 使用这个 hook 来处理联想词。
    (run-hooks 'pyim-page-select-finish-hook)))

(defun pyim-page-select-word:rime ()
  "从选词框中选择当前词条， 专门用于 rime 输入法支持。"
  (interactive)
  (if (null pyim-candidates)  ; 如果没有选项，输入空格
      (progn
        (pyim-outcome-handle 'last-char)
        (pyim-terminate-translation))
    ;; pyim 告诉 liberime 选择其他的词条
    (liberime-select-candidate (- pyim-candidate-position 1))
    (let* ((context (liberime-get-context))
           imobjs)
      (pyim-outcome-handle 'candidate)
      (if (not context)
          (progn
            (unless (member (pyim-outcome-get) pyim-candidates)
              (pyim-create-word (pyim-outcome-get)))
            (pyim-terminate-translation)
            ;; pyim 使用这个 hook 来处理联想词。
            (run-hooks 'pyim-page-select-finish-hook))
        ;; BUG: 默认 liberime 得到的 candidate 是分页的，一页只包含5个词条，
        ;; pyim 需要 liberime 不分页，或者一页包含尽可能多个词。
        (setq pyim-candidates
              (let* ((menu (alist-get 'menu context))
                     (candidates (alist-get 'candidates menu)))
                candidates))
        (setq pyim-candidate-position 1)
        (pyim-preview-refresh)
        (pyim-page-refresh)))))

(defun pyim-page-select-word-by-number (&optional n)
  "使用数字编号来选择对应的词条。"
  (interactive)
  (if (or pyim-page-select-word-by-number n)
      (if (null pyim-candidates)
          (progn
            (pyim-outcome-handle 'last-char)
            (pyim-terminate-translation))
        (let ((index (if (numberp n)
                         (- n 1)
                       (- last-command-event ?1)))
              (end (pyim-page-end)))
          (if (= index -1) (setq index 9) nil)
          (if (> (+ index (pyim-page-start)) end)
              (pyim-page-refresh)
            (setq pyim-candidate-position (+ pyim-candidate-position index))
            (pyim-page-select-word))))
    ;; 有些输入法使用数字键编码，这种情况下，数字键就
    ;; 不能用来选词了。
    (call-interactively #'pyim-self-insert-command)))

;; ** 处理标点符号
(defun pyim-translate-get-trigger-char ()
  "检查 `pyim-translate-trigger-char' 是否为一个合理的 trigger char 。

pyim 的 translate-trigger-char 要占用一个键位，为了防止用户
自定义设置与输入法冲突，这里需要检查一下这个键位设置的是否合理，
如果不合理，就返回输入法默认设定。"
  (let* ((user-trigger-char pyim-translate-trigger-char)
         (user-trigger-char
          (if (characterp user-trigger-char)
              (char-to-string user-trigger-char)
            (when (= (length user-trigger-char) 1)
              user-trigger-char)))
         (first-char (pyim-scheme-get-option
                      (pyim-scheme-name)
                      :first-chars))
         (prefer-trigger-chars (pyim-scheme-get-option
                                (pyim-scheme-name)
                                :prefer-trigger-chars)))
    (if (pyim-string-match-p (regexp-quote user-trigger-char) first-char)
        (progn
          ;; (message "注意：pyim-translate-trigger-char 设置和当前输入法冲突，使用推荐设置：\"%s\""
          ;;          prefer-trigger-chars)
          prefer-trigger-chars)
      user-trigger-char)))

(defun pyim-translate (char)
  "Pyim 字符转换函数，主要用于处理标点符号.

pyim 在运行过程中调用这个函数来进行标点符号格式的转换。

常用的标点符号数量不多，所以 pyim 没有使用文件而是使用一个变量
`pyim-punctuation-dict' 来设置标点符号对应表，这个变量是一个
alist 列表。"
  (let* ((str (char-to-string char))
         ;; 注意：`str' 是 *待输入* 的字符对应的字符串。
         (str-before-1 (pyim-char-before-to-string 0))
         (str-before-2 (pyim-char-before-to-string 1))
         (str-before-3 (pyim-char-before-to-string 2))
         (str-before-4 (pyim-char-before-to-string 3))
         ;; 从标点词库中搜索与 `str' 对应的标点列表。
         (punc-list (assoc str pyim-punctuation-dict))
         ;; 从标点词库中搜索与 `str-before-1' 对应的标点列表。
         (punc-list-before-1
          (cl-some (lambda (x)
                     (when (member str-before-1 x) x))
                   pyim-punctuation-dict))
         ;; `str-before-1' 在其对应的标点列表中的位置。
         (punc-posit-before-1
          (cl-position str-before-1 punc-list-before-1
                       :test #'equal))
         (trigger-str (pyim-translate-get-trigger-char)))
    (cond
     ;; 空格之前的字符什么也不输入。
     ((< char ? ) "")

     ;; 这个部份与标点符号处理无关，主要用来快速删除用户自定义词条。
     ;; 比如：在一个中文字符串后输入 2-v，可以将光标前两个中文字符
     ;; 组成的字符串，从个人词库删除。
     ((and (eq (char-before) ?-)
           (pyim-string-match-p "[0-9]" str-before-2)
           (pyim-string-match-p "\\cc" str-before-3)
           (equal str trigger-str))
      (delete-char -2)
      (pyim-delete-word-at-point
       (string-to-number str-before-2))
      "")
     ;; 这个部份与标点符号处理无关，主要用来快速保存用户自定义词条。
     ;; 比如：在一个中文字符串后输入 2v，可以将光标前两个中文字符
     ;; 组成的字符串，保存到个人词库。
     ((and (member (char-before) (number-sequence ?2 ?9))
           (pyim-string-match-p "\\cc" str-before-2)
           (equal str trigger-str))
      (delete-char -1)
      (pyim-create-word-at-point
       (string-to-number str-before-1))
      "")

     ;; 光标前面的字符为中文字符时，按 v 清洗当前行的内容。
     ((and (not (numberp punc-posit-before-1))
           (pyim-string-match-p "\\cc" str-before-1)
           (equal str trigger-str))
      (funcall pyim-wash-function)
      "")

     ;; 关闭标点转换功能时，只插入英文标点。
     ((not (pyim-punctuation-full-width-p))
      str)

     ;; 当用户使用 org-mode 以及 markdown 等轻量级标记语言撰写文档时，
     ;; 常常需要输入数字列表，比如：

     ;; 1. item1
     ;; 2. item2
     ;; 3. item3

     ;; 在这种情况下，数字后面输入句号必须是半角句号而不是全角句号，
     ;; pyim 调用 `pyim-translate' 时，会检测光标前面的字符，如果这个
     ;; 字符属于 `pyim-punctuation-escape-list' ，pyim 将输入半角标点，
     ;; 具体细节见：`pyim-translate'
     ((member (char-before)
              pyim-punctuation-escape-list)
      str)

     ;; 当 `pyim-punctuation-half-width-functions' 中
     ;; 任意一个函数返回值为 t 时，插入英文标点。
     ((cl-some #'(lambda (x)
                   (if (functionp x)
                       (funcall x char)
                     nil))
               pyim-punctuation-half-width-functions)
      str)

     ;; 当光标前面为英文标点时， 按 `pyim-translate-trigger-char'
     ;; 对应的字符后， 自动将其转换为对应的中文标点。
     ((and (numberp punc-posit-before-1)
           (= punc-posit-before-1 0)
           (equal str trigger-str))
      (pyim-punctuation-translate 'full-width)
      "")

     ;; 当光标前面为中文标点时， 按 `pyim-translate-trigger-char'
     ;; 对应的字符后， 自动将其转换为对应的英文标点。
     ((and (numberp punc-posit-before-1)
           (> punc-posit-before-1 0)
           (equal str trigger-str))
      (pyim-punctuation-translate 'half-width)
      "")

     ;; 正常输入标点符号。
     (punc-list
      (pyim-punctuation-return-proper-punct punc-list))

     ;; 当输入的字符不是标点符号时，原样插入。
     (t str))))

(defun pyim-char-before-to-string (num)
  "得到光标前第 `num' 个字符，并将其转换为字符串。"
  (let* ((point (point))
         (point-before (- point num)))
    (when (and (> point-before 0)
               (char-before point-before))
      (char-to-string (char-before point-before)))))

(defun pyim-char-after-to-string (num)
  "得到光标后第 `num' 个字符，并将其转换为字符串。"
  (let* ((point (point))
         (point-after (+ point num)))
    (when (char-after point-after)
      (char-to-string (char-after point-after)))))

(defun pyim-wash-current-line-function ()
  "清理当前行的内容，比如：删除不必要的空格，等。"
  (interactive)
  (let* ((begin (line-beginning-position))
         (end (point))
         (string (buffer-substring-no-properties begin end))
         new-string)
    (when (> (length string) 0)
      (delete-region begin end)
      (setq new-string
            (with-temp-buffer
              (insert string)
              (goto-char (point-min))
              (while (re-search-forward "\\([，。；？！；、）】]\\)  +\\([[:ascii:]]\\)" nil t)
                (replace-match (concat (match-string 1) (match-string 2))  nil t))
              (goto-char (point-min))
              (while (re-search-forward "\\([[:ascii:]]\\)  +\\([（【]\\)" nil t)
                (replace-match (concat (match-string 1) (match-string 2))  nil t))
              (goto-char (point-min))
              (while (re-search-forward "\\([[:ascii:]]\\)  +\\(\\cc\\)" nil t)
                (replace-match (concat (match-string 1) " " (match-string 2))  nil t))
              (goto-char (point-min))
              (while (re-search-forward "\\(\\cc\\)  +\\([[:ascii:]]\\)" nil t)
                (replace-match (concat (match-string 1) " " (match-string 2))  nil t))
              (buffer-string)))
      (insert new-string))))

;; ** 切换中英文标点符号
(defun pyim-punctuation-full-width-p ()
  "判断是否需要切换到全角标点输入模式

输入标点的样式的改变（全角或者半角）受三个方面影响：

1. 用户是否手动切换了标点样式？
2  用户是否手动切换到英文输入模式？
3. pyim 是否根据环境自动切换到英文输入模式？

三方面的综合结果为： 只要当前的输入模式是英文输入模式，那么输入的
标点符号 *必定* 是半角标点，如果当前输入模式是中文输入模式，那么，
输入标点的样式用户可以使用 `pyim-punctuation-toggle'手动控制，具
体请参考 `pyim-punctuation-full-width-p'。"
  (cl-case (car pyim-punctuation-translate-p)
    (yes t)
    (no nil)
    (auto
     ;; 如果用户手动或者根据环境自动切换为英文输入模式，
     ;; 那么标点符号也要切换为半角模式。
     (and (not pyim-input-ascii)
          (not (pyim-auto-switch-english-input-p))))))

(defun pyim-punctuation-toggle ()
  "Pyim 标点符号全角半角模式切换命令.

每次运行 `pyim-punctuation-toggle' 命令，都会调整变量
`pyim-punctuation-translate-p' 的取值，`pyim-translate' 根据
`pyim-punctuation-full-width-p' 函数的返回值，来决定是否转换标点
符号：

1. 当返回值为 'yes 时，`pyim-translate' 转换标点符号，从而输入全角标点。
2. 当返回值为 'no 时，`pyim-translate' 忽略转换，从而输入半角标点。
3. 当返回值为 'auto 时，根据中英文环境，自动切换。"
  (interactive)
  (setq pyim-punctuation-translate-p
        `(,@(cdr pyim-punctuation-translate-p)
          ,(car pyim-punctuation-translate-p)))
  (message
   (cl-case (car pyim-punctuation-translate-p)
     (yes "开启全角标点输入模式。")
     (no "开启半角标点输入模式。")
     (auto "开启全半角标点自动转换模式。"))))

(defun pyim-punctuation-translate-at-point ()
  "切换光标处标点的样式(全角 or 半角).

用户也可以使用命令 `pyim-punctuation-translate-at-point' 来切换
 *光标前* 标点符号的样式。"
  (interactive)
  (let* ((current-char (char-to-string (preceding-char)))
         (punc-list
          (cl-some (lambda (x)
                     (when (member current-char x) x))
                   pyim-punctuation-dict)))
    (when punc-list
      (delete-char -1)
      (if (equal current-char (car punc-list))
          (insert (pyim-punctuation-return-proper-punct punc-list))
        (insert (car punc-list))))))

(defun pyim-flatten-list (my-list)
  (cond
   ((null my-list) nil)
   ((atom my-list) (list my-list))
   (t (append (pyim-flatten-list (car my-list))
              (pyim-flatten-list (cdr my-list))))))

(defun pyim-punctuation-translate (&optional punct-style)
  "将光标前1个或前后连续成对的n个标点符号进行全角/半角转换.

当 PUNCT-STYLE 设置为 'full-width 时，所有的标点符号转换为全角符
号，设置为 'half-width 时，转换为半角符号。"
  (interactive)
  (let ((punc-list (pyim-flatten-list pyim-punctuation-dict))
        (punct-style
         (or punct-style
             (intern (completing-read
                      "将光标处的标点转换为" '("full-width" "half-width")))))
        ;; lnum : puncts on the left (before point)
        (lnum 0)
        ;; rnum : puncts on the right (after point)
        (rnum 0)
        (point (point))
        last-puncts result)
    (catch 'break
      (while t
        (let ((str (pyim-char-after-to-string rnum)))
          (if (member str punc-list)
              (cl-incf rnum)
            (throw 'break nil)))))
    (catch 'break
      (while (<= lnum rnum)
        (let ((str (pyim-char-before-to-string lnum)))
          (if (member str punc-list)
              (cl-incf lnum)
            (throw 'break nil)))))
    ;; 右侧与左侧成对匹配
    (setq rnum (min lnum rnum))
    (setq last-puncts (buffer-substring (- point lnum) (+ point rnum)))
    ;; 删除旧的标点符号
    (delete-char rnum)
    (delete-char (- 0 lnum))
    (dolist (punct (split-string last-puncts ""))
      (dolist (puncts pyim-punctuation-dict)
        (let ((position (cl-position punct puncts :test #'equal)))
          (when position
            (cond
             ((eq punct-style 'full-width)
              (if (= position 0)
                  (push (pyim-punctuation-return-proper-punct puncts) result)
                (push punct result)))
             ((eq punct-style 'half-width)
              (if (= position 0)
                  (push punct result)
                (push (car puncts) result))))))))
    (insert (mapconcat #'identity (reverse result) ""))
    (backward-char rnum)))

(defun pyim-punctuation-return-proper-punct (punc-list &optional before)
  "返回合适的标点符号，PUNCT-LIST 为标点符号列表.

这个函数用于处理成对的全角标点符号，简单来说：如果第一次输入的标
点是：（‘）时，那么下一次输入的标点就是（’）。

PUNCT-LIST 格式类似：

   `(\",\" \"，\") 或者：`(\"'\" \"‘\" \"’\")

当 BEFORE 为 t 时，只返回切换之前的结果，这个用来获取切换之前的
标点符号。

函数 `pyim-punctuation-return-proper-punct' 内部，我们使用变量
`pyim-punctuation-pair-status' 来记录 “成对” 中文标点符号的状态。"
  (let* ((str (car punc-list))
         (punc (cdr punc-list))
         (switch-p (cdr (assoc str pyim-punctuation-pair-status))))
    (if (= (safe-length punc) 1)
        (car punc)
      (if before
          (setq switch-p (not switch-p))
        (setf (cdr (assoc str pyim-punctuation-pair-status))
              (not switch-p)))
      (if switch-p
          (car punc)
        (nth 1 punc)))))

;; ** 与拼音输入相关的用户命令
(defun pyim-entered-delete-backward-char (&optional n)
  "在pyim-entered-buffer中向后删除1个字符"
  (interactive)
  (pyim-with-entered-buffer
    (ignore-errors
      (delete-char (- 0 (or n 1)))))
  (if (> (length (pyim-entered-get)) 0)
      (pyim-entered-refresh t)
    (pyim-outcome-handle "")
    (pyim-terminate-translation)))

(defun pyim-entered-delete-forward-char ()
  "在pyim-entered-buffer中向前删除1个字符"
  (interactive)
  (pyim-entered-delete-backward-char -1))

(defun pyim-entered-delete-backward-imelem (&optional search-forward)
  "`pyim-entered-buffer’ 中向后删除一个 imelem 对应的字符串"
  (interactive)
  (let ((position (pyim-entered-next-imelem-position 1 search-forward)))
    (pyim-with-entered-buffer
      (delete-region (point) position))
    (pyim-entered-refresh t)))

(defun pyim-entered-delete-forward-imelem ()
  "`pyim-entered-buffer’ 中向前删除一个 imelem 对应的字符串"
  (interactive)
  (pyim-entered-delete-backward-imelem t))

(define-obsolete-function-alias
  'pyim-convert-code-at-point 'pyim-convert-string-at-point)

;;;###autoload
(defun pyim-convert-string-at-point (&optional return-cregexp)
  "将光标前的用户输入的字符串转换为中文.

如果 RETURN-CREGEXP 为真, pyim 会把用户输入的字符串当作
拼音，依照这个拼音来构建一个 regexp, 用户可以用这个 regexp
搜索拼音对应的汉字。"
  (interactive "P")
  (unless (equal input-method-function 'pyim-input-method)
    (activate-input-method 'pyim))
  (if return-cregexp
      (pyim-convert-cregexp-at-point t)
    (let* ((case-fold-search nil)
           (scheme-name (pyim-scheme-name))
           (first-chars (pyim-scheme-get-option scheme-name :first-chars))
           (rest-chars (pyim-scheme-get-option scheme-name :rest-chars))
           (string (if mark-active
                       (buffer-substring-no-properties
                        (region-beginning) (region-end))
                     (buffer-substring (point) (line-beginning-position))))
           (length 0)
           code length)
      (cond ((string-match
              ;; 创建一个 regexp, 用于提取出光标处一个适合
              ;; 转换的字符串。
              (format "[%s]+ *$"
                      (cl-delete-duplicates
                       (concat first-chars rest-chars "'-")))
              string)
             (setq code
                   ;; 一些编程语言使用单引号 ' 做为字符串的标记，这里需要特殊处理。
                   (replace-regexp-in-string
                    "^[-']" ""
                    (match-string 0 string)))
             (setq length (length code))
             (setq code (replace-regexp-in-string " +" "" code))
             (when mark-active
               (delete-region
                (region-beginning) (region-end)))
             (when (and (not mark-active) (> length 0))
               (delete-char (- 0 length)))
             (when (> length 0)
               (setq unread-command-events
                     (append (listify-key-sequence code)
                             unread-command-events))
               (setq pyim-force-input-chinese t)))
            ((pyim-string-match-p "[[:punct:]：－]" (pyim-char-before-to-string 0))
             ;; 当光标前的一个字符是标点符号时，半角/全角切换。
             (call-interactively 'pyim-punctuation-translate-at-point))
            ((and nil ;; 暂时还没有准备启用这个功能
                  (eq pyim-default-scheme 'quanpin)
                  (string-match "\\cc *$" string))
             ;; 如果光标处是汉字，就用汉字的拼音来重新启动输入法
             (setq string
                   (if mark-active
                       string
                     (match-string 0 string)))
             (setq length (length string))
             (when mark-active
               (delete-region
                (region-beginning) (region-end)))
             (when (and (not mark-active) (> length 0))
               (delete-char (- 0 length)))
             (setq code (pyim-hanzi2pinyin
                         (replace-regexp-in-string " " "" string)
                         nil "-" nil t))
             (when (> length 0)
               (setq unread-command-events
                     (append (listify-key-sequence code)
                             unread-command-events))
               (setq pyim-force-input-chinese t)))
            (t (message "Pyim: pyim-convert-string-at-point do noting."))))))

(defun pyim-quit-clear ()
  "取消当前输入的命令."
  (interactive)
  (pyim-outcome-handle "")
  (pyim-terminate-translation))

(defun pyim-quit-no-clear ()
  "字母上屏命令."
  (interactive)
  (pyim-outcome-handle 'pyim-entered)
  (pyim-terminate-translation))

(defun pyim-inactivate ()
  "取消 pyim 的激活状态."
  (interactive)
  (mapc 'kill-local-variable pyim-local-variable-list))

(defun pyim-toggle-input-ascii ()
  "pyim 切换中英文输入模式。同时调整标点符号样式。"
  (interactive)
  (setq pyim-input-ascii
        (not pyim-input-ascii)))

;; ** 让 isearch-mode 通过 pinyin 搜索中文
(defun pyim-cregexp-build (string)
  "根据 STRING 构建一个中文 regexp, 用于 \"拼音搜索汉字\".
比如：\"nihao\" -> \"[你呢...][好号...] \\| nihao\""
  (or (ignore-errors
        (rx-to-string (pyim-cregexp-build-from-rx
                       (lambda (x)
                         (if (stringp x)
                             (xr (pyim-cregexp-build-1 x))
                           x))
                       (xr string))))
      string))

(defun pyim-cregexp-build-from-rx (fn rx-form)
  (cond
   ((not rx-form) nil)
   ((and (listp rx-form)
         (not (listp (cdr rx-form))))
    (funcall fn rx-form))
   ((and (listp rx-form)
         (not (eq 'any (car rx-form))))
    (mapcar (lambda (x)
              (pyim-cregexp-build-from-rx fn x))
            rx-form))
   ((and (listp rx-form)
         (eq 'any (car rx-form)))
    rx-form)
   (t (funcall fn rx-form))))

(defun pyim-cregexp-build-1 (string)
  (let* ((scheme-name (pyim-scheme-name))
         (class (pyim-scheme-get-option scheme-name :class)))
    ;; 确保 pyim 词库加载
    (pyim-dcache-init-variables)
    ;; pyim 暂时只支持全拼和双拼搜索
    (when (not (member class '(quanpin shuangpin)))
      (setq scheme-name 'quanpin))
    (if (or (pyim-string-match-p "[^a-z']+" string))
        string
      (let* ((imobjs
              ;; 如果一个字符串以'结尾,就按照拼音首字母字符串处理。
              (if (pyim-string-match-p "'$" string)
                  (list (mapcar #'(lambda (x)
                                    (list (char-to-string x)))
                                (string-to-list string)))
                ;; Slowly operating, need to improve.
                (pyim-imobjs-create string scheme-name)))
             (regexp-list
              (mapcar
               #'(lambda (imobj)
                   (pyim-cregexp-build:quanpin imobj))
               imobjs))
             (regexp
              (when regexp-list
                (mapconcat #'identity
                           (delq nil regexp-list)
                           "\\|")))
             (regexp
              (if (> (length regexp) 0)
                  (concat string "\\|" regexp)
                string)))
        regexp))))

(defun pyim-cregexp-build:quanpin (imobj &optional match-beginning
                                         first-equal all-equal)
  "从 IMOBJ 创建一个搜索中文的 regexp."
  (let* ((imobj
          (mapcar #'(lambda (x)
                      (concat (nth 0 x) (nth 1 x)))
                  imobj))
         (cchar-list
          (let ((n 0) results)
            (dolist (py imobj)
              (let* ((equal-match
                      (or all-equal
                          (and first-equal (= n 0))))
                     (cchars
                      ;; 只取常用字，不常用的汉字忽略，防止生成的
                      ;; regexp 太长而无法搜索
                      (mapconcat #'(lambda (x)
                                     (car (split-string x "|")))
                                 (pyim-pinyin2cchar-get py equal-match nil t) "")))
                (push cchars results))
              (setq n (+ 1 n)))
            (nreverse results)))
         (regexp
          (mapconcat #'(lambda (x)
                         (when (pyim-string-match-p "\\cc" x)
                           (format "[%s]" x)))
                     cchar-list "")))
    (unless (equal regexp "")
      (concat (if match-beginning "^" "") regexp))))

(defun pyim-isearch-search-fun ()
  "这个函数为 isearch 相关命令添加中文拼音搜索功能，
做为 `isearch-search-fun' 函数的 advice 使用。"
  (funcall
   (lambda ()
     `(lambda (string &optional bound noerror count)
        (funcall (if ,isearch-forward
                     're-search-forward
                   're-search-backward)
                 (pyim-cregexp-build string) bound noerror count)))))

;;;###autoload
(define-minor-mode pyim-isearch-mode
  "这个 mode 为 isearch 添加拼音搜索功能."
  :global t
  :group 'pyim
  :require 'pyim
  :lighter " pyim-isearch"
  (if pyim-isearch-mode
      (progn
        (advice-add 'isearch-search-fun :override #'pyim-isearch-search-fun)
        (message "PYIM: `pyim-isearch-mode' 已经激活，激活后，一些 isearch 扩展包有可能失效。"))
    (advice-remove 'isearch-search-fun #'pyim-isearch-search-fun)))

(defun pyim-convert-cregexp-at-point (&optional insert-only)
  "将光标前的字符串按拼音的规则转换为一个搜索中文的 regexp.
用于实现拼音搜索中文的功能。

在 minibuffer 中，这个命令默认会自动运行 `exit-minibuffer'.
这个可以使用 INSERT-ONLY 参数控制。"
  (interactive "P")
  (unless (equal input-method-function 'pyim-input-method)
    (activate-input-method 'pyim))
  (let* ((buffer-string
          (buffer-substring (point-min) (point-max)))
         (string (if mark-active
                     (buffer-substring-no-properties
                      (region-beginning) (region-end))
                   (buffer-substring
                    (point)
                    (save-excursion
                      (skip-syntax-backward "w")
                      (point)))))
         (length (length string))
         (cregexp (pyim-cregexp-build string)))
    (delete-char (- 0 length))
    (cond
     ;; Deal with `org-search-view'
     ((and (window-minibuffer-p)
           (string-match-p
            (regexp-quote "[+-]Word/{Regexp}") buffer-string))
      (insert (format "{%s}" cregexp)))
     (t (insert cregexp)))
    (when (and (not insert-only)
               (window-minibuffer-p))
      (exit-minibuffer))))

;; ** 让 forward/backward 支持中文
(defun pyim-forward-word (&optional arg)
  "向前移动 ARG 英文或者中文词，向前移动时基于 *最长* 的词移动。"
  (interactive "P")
  (or arg (setq arg 1))
  (dotimes (i arg)
    (let* ((words (pyim-cwords-at-point t))
           (max-length
            (cl-reduce #'max
                       (cons 0 (mapcar #'(lambda (word)
                                           (nth 2 word))
                                       words))))
           (max-length (max (or max-length 1) 1)))
      (forward-char max-length))))

(defun pyim-backward-word (&optional arg)
  "向后移动 ARG 个英文或者中文词，向后移动时基于 *最长* 的词移动。"
  (interactive "P")
  (or arg (setq arg 1))
  (dotimes (i arg)
    (let* ((words (pyim-cwords-at-point))
           (max-length
            (cl-reduce #'max
                       (cons 0 (mapcar #'(lambda (word)
                                           (nth 1 word))
                                       words))))
           (max-length (max (or max-length 1) 1)))
      (backward-char max-length))))

(defun pyim-cwords-at-point (&optional end-of-point)
  "获取光标当前的词条列表，当 END-OF-POINT 设置为 t 时，获取光标后的词条列表。
词条列表的每一个元素都是列表，这些列表的第一个元素为词条，第二个元素为光标处到词条
头部的距离，第三个元素为光标处到词条尾部的距离。

其工作原理是：

1. 使用 `thing-at-point' 获取当前光标处的一个字符串，一般而言：英文会得到
   一个单词，中文会得到一个句子。
2. 英文单词直接返回这个单词的列表。
3. 中文句子首先用 `pyim-cstring-split-to-list' 分词，然后根据光标在中文句子
   中的位置，筛选出符合要求的中文词条。得到并返回 *一个* 或者 *多个* 词条
   的列表。"
  ;;
  ;;                                光标到词 光标到词
  ;;                                首的距离 尾的距离
  ;;                                       | |
  ;; 获取光标当前的词<I>条列表 -> (("的词" 2 0) ("词条" 1 1))
  ;;
  (let* ((case-fold-search t)
         (current-pos (point))
         (current-char
          (if end-of-point
              (string (following-char))
            (string (preceding-char))))
         (str (thing-at-point 'word t))
         (str-length (length str))
         (str-boundary (bounds-of-thing-at-point 'word))
         (str-beginning-pos (when str-boundary
                              (car str-boundary)))
         (str-end-pos (when str-boundary
                        (cdr str-boundary)))
         (str-offset
          (when (and str-beginning-pos str-end-pos)
            (if (= current-pos str-end-pos)
                (1+ (- str-end-pos str-beginning-pos))
              (1+ (- current-pos str-beginning-pos)))))
         str-offset-adjusted words-alist results)

    ;; 当字符串长度太长时， `pyim-cstring-split-to-list'
    ;; 的速度比较慢，这里确保待分词的字符串长度不超过10.
    (when (and str (not (pyim-string-match-p "\\CC" str)))
      (if (> str-offset 5)
          (progn (setq str-offset-adjusted 5)
                 (setq str (substring str
                                      (- str-offset 5)
                                      (min (+ str-offset 5) str-length))))
        (setq str-offset-adjusted str-offset)
        (setq str (substring str 0 (min 9 str-length)))))

    (cond
     ((and str (not (pyim-string-match-p "\\CC" str)))
      (setq words-alist
            (pyim-cstring-split-to-list str))
      (dolist (word-list words-alist)
        (let ((word-begin (nth 1 word-list))
              (word-end (nth 2 word-list)))
          (if (if end-of-point
                  (and (< str-offset-adjusted word-end)
                       (>= str-offset-adjusted word-begin))
                (and (<= str-offset-adjusted word-end)
                     (> str-offset-adjusted word-begin)))
              (push (list (car word-list)
                          (- str-offset-adjusted word-begin) ;; 例如： ("你好" 1 1)
                          (- word-end str-offset-adjusted))
                    results))))
      (or results
          (list (if end-of-point
                    (list current-char 0 1)
                  (list current-char 1 0)))))
     (str (list (list str
                      (- current-pos str-beginning-pos)
                      (- str-end-pos current-pos)))))))

(defun pyim-cstring-split-to-list (chinese-string &optional max-word-length)
  "一个基于 pyim 的中文分词函数。这个函数可以将中文字符
串 CHINESE-STRING 分词，得到一个词条 alist，这个 alist 的元素
都是列表，其中第一个元素为分词得到的词条，第二个元素为词条相对于
字符串中的起始位置，第三个元素为结束位置。分词时，默认词条不超过
6个字符，用户可以通过 MAX-WORD-LENGTH 来自定义，但值得注意的是：
这个值设置越大，分词速度越慢。

注意事项：
1. 这个工具使用暴力匹配模式来分词，*不能检测出* pyim 词库中不存在
   的中文词条。
2. 这个函数的分词速度比较慢，仅仅适用于中文短句的分词，不适用于
   文章分词。根据评估，20个汉字组成的字符串需要大约0.3s， 40个
   汉字消耗1s，随着字符串长度的增大消耗的时间呈几何倍数增加。"
  ;;                   (("天安" 5 7)
  ;; 我爱北京天安门 ->  ("天安门" 5 8)
  ;;                    ("北京" 3 5)
  ;;                    ("我爱" 1 3))
  (cl-labels
      ((get-possible-words-internal
        ;; 内部函数，功能类似：
        ;; ("a" "b" "c" "d") -> ("abcd" "abc" "ab")
        (my-list number)
        (cond
         ((< (length my-list) 2) nil)
         (t (append
             (let* ((str (mapconcat #'identity my-list ""))
                    (length (length str)))
               (when (<= length (or max-word-length 6))
                 (list (list str number (+ number length)))))
             (get-possible-words-internal
              (reverse (cdr (reverse my-list))) number)))))
       (get-possible-words
        ;; 内部函数，功能类似：
        ;; ("a" "b" "c" "d") -> ("abcd" "abc" "ab" "bcd" "bc" "cd")
        (my-list number)
        (cond
         ((null my-list) nil)
         (t (append (get-possible-words-internal my-list number)
                    (get-possible-words (cdr my-list) (1+ number)))))))

    ;; 如果 pyim 词库没有加载，加载 pyim 词库，
    ;; 确保 `pyim-dcache-get' 可以正常运行。
    (pyim-dcache-init-variables)

    (let ((string-alist
           (get-possible-words
            (mapcar #'char-to-string
                    (string-to-vector chinese-string)) 1))
          words-list result)
      (dolist (string-list string-alist)
        (let ((pinyin-list (pyim-hanzi2pinyin (car string-list) nil "-" t)))
          (dolist (pinyin pinyin-list)
            (let ((words (pyim-dcache-get pinyin '(code2word)))) ; 忽略个人词库可以提高速度
              (dolist (word words)
                (when (equal word (car string-list))
                  (push string-list result)))))))
      result)))

;; (let ((str "医生随时都有可能被患者及其家属反咬一口"))
;;   (benchmark 1 '(pyim-cstring-split-to-list str)))

;; (let ((str "医生随时都有可能被患者及其家属反咬一口"))
;;   (pyim-cstring-split-to-list str))

(defun pyim-cstring-split-to-string (string &optional prefer-short-word
                                            separator max-word-length)
  "将中文字符串 STRING 分词.

在分词的位置插入空格或者自定义分隔符 SEPERATERS，默认情况下较长的
词条优先使用，如果 PREFER-SHORT-WORD 设置为 t，则优先使用较短的
词条。默认最长词条不超过6个字符，用户可以通 MAX-WORD-LENGTH 来
自定义词条的最大长度，但值得注意的是，这个值设置越大，分词速度越
慢。"
  (let ((string-list
         (if (pyim-string-match-p "\\CC" string)
             (split-string
              (replace-regexp-in-string
               "\\(\\CC+\\)" "@@@@\\1@@@@" string) "@@@@")
           (list string))))
    (mapconcat
     #'(lambda (str)
         (when (> (length str) 0)
           (if (not (pyim-string-match-p "\\CC" str))
               (pyim-cstring-split-to-string-1
                str prefer-short-word separator max-word-length)
             (concat " " str " "))))
     string-list "")))

(defun pyim-cstring-split-to-string-1 (chinese-string &optional prefer-short-word
                                                      separator max-word-length)
  "`pyim-cstring-split-to-string' 内部函数。"
  (let ((str-length (length chinese-string))
        (word-list (cl-delete-duplicates
                    ;;  判断两个词条在字符串中的位置
                    ;;  是否冲突，如果冲突，仅保留一个，
                    ;;  删除其它。
                    (pyim-cstring-split-to-list chinese-string max-word-length)
                    :test #'(lambda (x1 x2)
                              (let ((begin1 (nth 1 x1))
                                    (begin2 (nth 1 x2))
                                    (end1 (nth 2 x1))
                                    (end2 (nth 2 x2)))
                                (not (or (<= end1 begin2)
                                         (<= end2 begin1)))))
                    :from-end prefer-short-word))
        position-list result)

    ;; 提取词条相对于字符串的位置信息。
    (dolist (word word-list)
      (push (nth 1 word) position-list)
      (push (nth 2 word) position-list))

    ;; 将位置信息由小到大排序。
    (setq position-list
          (cl-delete-duplicates (sort position-list #'<)))

    ;; 在分词的位置插入空格或者用户指定的分隔符。
    (dotimes (i str-length)
      (when (member (1+ i) position-list)
        (push (or separator " ") result))
      (push (substring chinese-string i (1+ i))  result))
    (setq result (nreverse result))
    (mapconcat #'identity result "")))

(defun pyim-cstring-split-buffer ()
  "将一个 buffer 中的中文文章，进行分词操作。"
  (interactive)
  (message "分词开始！")
  (goto-char (point-min))
  (while (not (eobp))
    (let ((string (buffer-substring-no-properties
                   (line-beginning-position)
                   (line-end-position))))
      (delete-region (line-beginning-position)
                     (min (+ (line-end-position) 1) (point-max)))
      (insert (pyim-cstring-split-to-string string))
      (insert "\n")))
  (goto-char (point-min))
  (message "分词完成！"))

;; ** 汉字到拼音的转换工具
;;;###autoload
(defun pyim-hanzi2pinyin (string &optional shou-zi-mu separator
                                 return-list ignore-duo-yin-zi adjust-duo-yin-zi)
  "将汉字字符串转换为对应的拼音字符串的工具.

如果 SHOU-ZI-MU 设置为 t, 转换仅得到拼音首字母字符串。当
RETURN-LIST 设置为 t 时，返回一个拼音列表，这个列表包含词条的一个
或者多个拼音（词条包含多音字时）；如果 IGNORE-DUO-YIN-ZI 设置为
t, 遇到多音字时，只使用第一个拼音，其它拼音忽略；当
ADJUST-DUO-YIN-Zi 设置为 t 时, `pyim-hanzi2pinyin' 会使用 pyim 已
安装的词库来校正多音字，但这个功能有一定的限制:

1. pyim 普通词库中不存在的词条不能较正
2. 多音字校正速度比较慢，实时转换会产生卡顿。

BUG: 当 STRING 中包含其它标点符号，并且设置 SEPERATER 时，结果会
包含多余的连接符：比如： '你=好' --> 'ni-=-hao'"
  (if (not (pyim-string-match-p "\\cc" string))
      (if return-list
          (list string)
        string)
    (let (string-list pinyins-list pinyins-list-permutated pinyins-list-adjusted)

      ;; 将汉字字符串转换为字符list，英文原样输出。
      ;; 比如： “Hello银行” -> ("Hello" "银" "行")
      (setq string-list
            (if (pyim-string-match-p "\\CC" string)
                ;; 处理中英文混合的情况
                (split-string
                 (replace-regexp-in-string
                  "\\(\\cc\\)" "@@@@\\1@@@@" string)
                 "@@@@")
              ;; 如果词条只包含中文，使用`string-to-vector'
              ;; 这样处理速度比较快。
              (string-to-vector string)))

      ;; 将上述汉字字符串里面的所有汉字转换为与之对应的拼音list。
      ;; 比如： ("Hello" "银" "行") -> (("Hello") ("yin") ("hang" "xing"))
      (mapc
       #'(lambda (str)
           ;; `string-to-vector' 得到的是 char vector, 需要将其转换为 string。
           (when (numberp str)
             (setq str (char-to-string str)))
           (cond
            ((> (length str) 1)
             (push (list str) pinyins-list))
            ((and (> (length str) 0)
                  (pyim-string-match-p "\\cc" str))
             (push (or (pyim-cchar2pinyin-get (string-to-char str))
                       (list str))
                   pinyins-list))
            ((> (length str) 0)
             (push (list str) pinyins-list))))
       string-list)
      (setq pinyins-list (nreverse pinyins-list))

      ;; 通过排列组合的方式, 重排 pinyins-list。
      ;; 比如：(("Hello") ("yin") ("hang" "xing")) -> (("Hello" "yin" "hang") ("Hello" "yin" "xing"))
      (setq pinyins-list-permutated (pyim-permutate-list2 pinyins-list))

      ;; 使用 pyim 的安装的词库来校正多音字。
      (when adjust-duo-yin-zi
        ;; 确保 pyim 词库加载
        (pyim-dcache-init-variables)
        (dolist (pinyin-list pinyins-list-permutated)
          (let* ((py-str (mapconcat #'identity pinyin-list "-"))
                 (words-from-dicts
                  ;; pyim-buffer-list 中第一个 buffer 对应的是个人词库文件
                  ;; 个人词库文件中的词条，极有可能存在 *多音字污染*。
                  ;; 这是由 pyim 保存词条的机制决定的。
                  (pyim-dcache-get py-str '(code2word))))
            (when (member string words-from-dicts)
              (push pinyin-list pinyins-list-adjusted))))
        (setq pinyins-list-adjusted
              (nreverse pinyins-list-adjusted)))

      ;; 返回拼音字符串或者拼音列表
      (let* ((pinyins-list
              (or pinyins-list-adjusted
                  pinyins-list-permutated))
             (list (mapcar
                    #'(lambda (x)
                        (mapconcat
                         #'(lambda (str)
                             (if shou-zi-mu
                                 (substring str 0 1)
                               str))
                         x separator))
                    (if ignore-duo-yin-zi
                        (list (car pinyins-list))
                      pinyins-list))))
        (if return-list
            list
          (mapconcat #'identity list " "))))))

(defun pyim-permutate-list (list)
  "使用排列组合的方式重新排列 LIST.
这个函数由 ‘二中’ 提供，`pyim-hanzi2pinyin' 没有使用这个函数
(速度稍微有点慢)。"
  (let ((list-head (car list))
        (list-tail (cdr list)))
    (cond ((null list-tail)
           (cl-loop for element0 in list-head
                    append (cons (cons element0 nil) nil)))
          (t (cl-loop for element in list-head
                      append (mapcar (lambda (l) (cons element l))
                                     (pyim-permutate-list list-tail)))))))

(defun pyim-permutate-list2 (list)
  "使用排列组合的方式重新排列 LIST.
这个函数由 ’翀/ty‘ 提供，`pyim-hanzi2pinyin' 默认使用这个函数。"
  (if (= (length list) 1)
      (mapcar #'list (car list))
    (pyim-permutate-list2-internal (car list) (cdr list))))

(defun pyim-permutate-list2-internal (one two)
  "`pyim-permutate-list2' 的内部函数。"
  (let (return)
    (if (null (car two))
        one
      (dolist (x1 one)
        (dolist (x2 (car two))
          (push (if (listp x1)
                    (append x1 (list x2))
                  (list x1 x2))
                return)))
      (setq one return)
      (pyim-permutate-list2-internal one (cdr two)))))

;;;###autoload
(defun pyim-hanzi2pinyin-simple (string &optional shou-zi-mu separator return-list)
  "简化版的 `pyim-hanzi2pinyin', 不处理多音字。"
  (pyim-hanzi2pinyin string shou-zi-mu separator return-list t))

;; ** pyim 词库管理工具
(defvar pyim-dm-buffer "*pyim-dict-manager*")

(defun pyim-dm-refresh ()
  "Refresh the contents of the *pyim-dict-manager* buffer."
  (interactive)
  (with-current-buffer pyim-dm-buffer
    (let ((inhibit-read-only t)
          (dicts-list pyim-dicts)
          (format-string "%-4s %-4s %-60s\n")
          (face-attr '((foreground-color . "DarkOrange2")
                       (bold . t)))
          (i 1))
      (erase-buffer)
      (insert (propertize (format format-string "序号" "启用" "词库文件")
                          'face face-attr))
      (insert (propertize (format format-string
                                  "----" "----"
                                  "----------------------------------------------------------------------\n")
                          'face face-attr))
      (if (not pyim-dicts)
          (insert "拼音词库是 pyim 使用顺手与否的关键。根据经验估计：

1. 当词库词条超过100万时 (词库文件>20M)，pyim 选词频率大大降低。
2. 当词库词条超过100万时，pyim 中文输入体验可以达到搜狗输入法的 80%。

想快速体验 pyim 输入法的用户, 可以使用 pyim-basedict：

     (require 'pyim-basedict)
     (pyim-basedict-enable)

喜欢折腾的用户可以从下面几个途径获得 pyim 更详细的信息。
1. 使用 `C-h v pyim-dicts' 了解 pyim 词库文件格式。
2. 了解如何导入其它输入法的词库。
   1. 使用 package 管理器查看 pyim 包的简介
   2. 阅读 pyim.el 文件 Commentary
   3. 查看 pyim 在线 README：https://github.com/tumashu/pyim\n")
        (dolist (dict dicts-list)
          (let ((disable (plist-get dict :disable))
                (file (plist-get dict :file)))
            (insert (propertize (format format-string
                                        i (if disable "NO" "YES") file)
                                'id i 'disable disable 'file file)))
          (setq i (1+ i))))
      (insert (propertize "
操作命令：[A] 添加词库  [D] 删除词库   [P] 向上移动   [N] 向下移动  [g] 刷新页面
          [s] 保存配置  [R] 重启输入法 [C-c C-c] 禁用/启用当前词库"
                          'face face-attr)))))

(defun pyim-dm-toggle-dict (&optional enable)
  "启用当前行对应的词库。"
  (interactive)
  (when (equal (buffer-name) pyim-dm-buffer)
    (let* ((id (get-text-property (point) 'id))
           (disable (get-text-property (point) 'disable))
           (dict (cl-copy-list (nth (1- id) pyim-dicts)))
           (disable (plist-get dict :disable))
           (line (line-number-at-pos)))
      (setf (nth (1- id) pyim-dicts) (plist-put dict :disable (not disable)))
      (if (not disable)
          (message "禁用当前词库")
        (message "启用当前词库"))
      (pyim-dm-refresh)
      (goto-char (point-min))
      (forward-line (- line 1)))))

(defun pyim-dm-delete-dict ()
  "从 `pyim-dicts' 中删除当前行对应的词库信息。"
  (interactive)
  (when (equal (buffer-name) pyim-dm-buffer)
    (let ((id (get-text-property (point) 'id))
          (file (get-text-property (point) 'file))
          (line (line-number-at-pos)))
      (when (yes-or-no-p "确定要删除这条词库信息吗? ")
        (setq pyim-dicts (delq (nth (1- id) pyim-dicts) pyim-dicts))
        (pyim-dm-refresh)
        (goto-char (point-min))
        (forward-line (- line 1))))))

(defun pyim-dm-dict-position-up ()
  "向上移动词库。"
  (interactive)
  (when (equal (buffer-name) pyim-dm-buffer)
    (let* ((id (get-text-property (point) 'id))
           (dict1 (nth (- id 1) pyim-dicts))
           (dict2 (nth (- id 2) pyim-dicts))
           (length (length pyim-dicts))
           (line (line-number-at-pos)))
      (when (> id 1)
        (setf (nth (- id 1) pyim-dicts) dict2)
        (setf (nth (- id 2) pyim-dicts) dict1)
        (pyim-dm-refresh)
        (goto-char (point-min))
        (forward-line (- line 2))))))

(defun pyim-dm-dict-position-down ()
  "向下移动词库。"
  (interactive)
  (when (equal (buffer-name) pyim-dm-buffer)
    (let* ((id (get-text-property (point) 'id))
           (dict1 (nth (- id 1) pyim-dicts))
           (dict2 (nth id pyim-dicts))
           (length (length pyim-dicts))
           (line (line-number-at-pos)))
      (when (< id length)
        (setf (nth (1- id) pyim-dicts) dict2)
        (setf (nth id pyim-dicts) dict1)
        (pyim-dm-refresh)
        (goto-char (point-min))
        (forward-line line)))))

(defun pyim-dm-save-dict-info ()
  "使用 `customize-save-variable' 函数将 `pyim-dicts' 保存到 '~/.emacs' 文件中。"
  (interactive)
  ;; 将`pyim-dict'的设置保存到emacs配置文件中。
  (customize-save-variable 'pyim-dicts pyim-dicts)
  (message "将 pyim 词库配置信息保存到 ~/.emacs 文件。"))

(defun pyim-dm-add-dict ()
  "为 `pyim-dicts' 添加词库信息。"
  (interactive)
  (when (equal (buffer-name) pyim-dm-buffer)
    (let ((line (line-number-at-pos))
          dict name file coding first-used dict-type)
      (setq name (read-from-minibuffer "请输入词库名称： "))
      (setq file (read-file-name "请选择词库文件： " "~/"))
      (setq first-used  (yes-or-no-p "是否让 pyim 优先使用词库？ "))
      (setq dict `(:name ,name :file ,file))
      (if first-used
          (add-to-list 'pyim-dicts dict)
        (add-to-list 'pyim-dicts dict t))
      (pyim-dm-refresh)
      (goto-char (point-min))
      (forward-line (- line 1)))))

(define-derived-mode pyim-dm-mode special-mode "pyim-dicts-manager"
  "Major mode for managing pyim dicts"
  (read-only-mode)
  (define-key pyim-dm-mode-map (kbd "D") 'pyim-dm-delete-dict)
  (define-key pyim-dm-mode-map (kbd "g") 'pyim-dm-refresh)
  (define-key pyim-dm-mode-map (kbd "A") 'pyim-dm-add-dict)
  (define-key pyim-dm-mode-map (kbd "N") 'pyim-dm-dict-position-down)
  (define-key pyim-dm-mode-map (kbd "P") 'pyim-dm-dict-position-up)
  (define-key pyim-dm-mode-map (kbd "s") 'pyim-dm-save-dict-info)
  (define-key pyim-dm-mode-map (kbd "C-c C-c") 'pyim-dm-toggle-dict)
  (define-key pyim-dm-mode-map (kbd "R") 'pyim-restart))

;;;###autoload
(defun pyim-dicts-manager ()
  "pyim 词库管理器。

使用这个词库管理器可以方便的执行下列命令：
1. 添加词库。
2. 删除词库。
3. 向上和向下移动词库。
4. 保存词库设置。
5. 重启输入法。"
  (interactive)
  (let ((buffer (get-buffer-create pyim-dm-buffer)))
    (pyim-dm-refresh)
    (switch-to-buffer buffer)
    (pyim-dm-mode)
    (setq truncate-lines t)))

(defun pyim-extra-dicts-add-dict (new-dict)
  "添加 `new-dict' 到 `pyim-extra-dicts'.

其中 NEW-DICT 的格式为：

   (:name \"XXX\" :file \"/path/to/XXX.pyim\")

这个函数用于制作 elpa 格式的词库 ，不建议普通用户使用。"
  (let (replace result)
    (dolist (dict pyim-extra-dicts)
      (if (equal (plist-get dict :name)
                 (plist-get new-dict :name))
          (progn (push new-dict result)
                 (setq replace t))
        (push dict result)))
    (setq result (reverse result))
    (setq pyim-extra-dicts
          (if replace result `(,@result ,new-dict)))
    (message "Add pyim dict %S to `pyim-extra-dicts'." (plist-get new-dict :name))
    t))

(defun pyim-dict-name-available-p (dict-name)
  "查询 `pyim-dicts' 中 `:name' 为 DICT-NAME 的词库信息是否存在。
这个函数主要用于词库 package。"
  (cl-some (lambda (x)
             (let ((name (plist-get x :name)))
               (equal name dict-name)))
           pyim-dicts))

(defun pyim-dict-file-available-p (dict-file)
  "查询 `pyim-dicts' 中 `:file' 为 DICT-FILE 的词库信息是否存在。
这个函数主要用于词库 package。"
  (cl-some (lambda (x)
             (let ((file (plist-get x :file)))
               (equal (expand-file-name file)
                      (expand-file-name dict-file))))
           pyim-dicts))

;; ** pyim 探针程序
(require 'pyim-probe)

;; * Footer
(provide 'pyim)

;;; pyim.el ends here
