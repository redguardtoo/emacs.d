;;; chinese-pyim.el --- Chinese pinyin input method

;; * Header
;; Copyright 2015 Feng Shu

;; Author: Feng Shu <tumashu@163.com>
;; URL: https://github.com/tumashu/chinese-pyim
;; Version: 0.0.1
;; Package-Requires: ((cl-lib "0.5")(pos-tip "0.4"))
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

;; * Chinese-pyim 使用说明                                          :README:doc:
;; ** 截图
;; [[./snapshots/pyim-linux-x-with-toolkit.png]]

;; ** 简介
;; Chinese-pyim (Chinese Pinyin Input Method) 是 emacs 环境下的一个中文拼
;; 音输入法。


;; ** 背景
;; Chinese-pyim 的代码源自 emacs-eim。

;; emacs-eim 是一个 emacs 中文输入法框架，本身包含了多种中文输入法，比如：
;; 五笔输入法，仓颉输入法以及二笔输入法等等。但遗憾的是，emacs-eim 并没有
;; 发展起来，2008 年之后几乎停止了开发。一个主要的原因是外部中文输入法的
;; 高速发展，比如：Window平台下的搜狗输入法，baidu输入法以及QQ输入法，
;; linux平台下的fcitx，ibus等等。

;; 但外部输入法与 emacs 配合不够默契，极大的损害了 emacs 那种 *行云流水*
;; 的体验。而本人在使用（或者叫折腾） emacs-eim 的过程中发现：

;; 1. *当 emacs-eim 拼音词库词条超过100万时，选词频率大大降低。*
;; 2. *当 emacs-eim 拼音词库词条超过100万时，中文输入体验可以达到搜狗输入法的80%。*
;; 3. *随着使用时间的延长，emacs-eim会越来越好用（个人词库的积累）。*

;; 所以，本人认为 emacs-eim 非常适合作为 *备用* 中文输入法，于是我 fork
;; emacs-eim 的代码, 更改名称为：chinese-pyim。

;; ** 目标
;; Chinese-pyim 的目标是： *尽最大的努力成为一个好用的 emacs 备用中文拼音
;; 输入法* 。具体可表现为三个方面：

;; 1. Fallback:     当外部输入法不能使用时，比如在 console或者cygwin环境
;;    下，尽最大可能让 emacs 用户不必为输入中文而烦恼。
;; 2. Integration:  尽最大可能减少输入法切换频率，让中文输入不影响 emacs
;;    的体验。
;; 3. Exchange:     尽最大可能简化 Chinese-pyim 使用其他优秀输入法的词库
;;    的难度和复杂度。

;; ** 特点
;; 1. Chinese-pyim 只是一个拼音输入法，安装配置方便快捷，默认只通过添加词
;;    库的方式优化输入法。
;; 2. Chinese-pyim 只使用最简单的文本词库格式，可以快速方便的利用其他输入
;;    法的词库。

;; ** 安装
;; 1. 配置melpa源，参考：http://melpa.org/#/getting-started
;; 2. M-x package-install RET chinese-pyim RET
;; 3. 在emacs配置文件中（比如: ~/.emacs）添加如下代码：

;; #+BEGIN_EXAMPLE
;; (require 'chinese-pyim)
;; #+END_EXAMPLE

;; ** 配置
;; *** 添加词库文件
;; 用户可以使用三种方法为 Chinese-pyim 添加拼音词库，具体方式请参考 [[如何添加自定义拼音词库]] 小结。

;; 注意：每一个词库文件必须按行排序（准确的说，是按每一行的拼音code排序），
;; 因为`Chinese-pyim' 寻找词条时，使用二分法来优化速度，而二分法工作的前提
;; 就是对文件按行排序。具体细节请参考：`pyim-bisearch-word' 。
;; 所以，当词库排序不正确时（比如：用户手动调整词库文件后），记得运行函数
;; `pyim-update-dict-file' 重新对文件排序。

;; *** 激活 Chinese-pyim

;; #+BEGIN_EXAMPLE
;; (setq default-input-method "chinese-pyim")
;; (global-set-key (kbd "C-<SPC>") 'toggle-input-method)
;; (global-set-key (kbd "C-;") 'pyim-toggle-full-width-punctuation)
;; #+END_EXAMPLE

;; ** 使用
;; *** 常用快捷键
;; | 输入法快捷键    | 功能             |
;; |-----------------+------------------|
;; | C-n 或 M-n 或 + | 向下翻页         |
;; | C-p 或 M-p 或 - | 向上翻页         |
;; | C-f             | 选择下一个备选词 |
;; | C-b             | 选择上一个备选词 |
;; | SPC             | 确定输入         |
;; | RET 或 C-m      | 字母上屏         |
;; | C-c 或 C-g      | 取消输入         |
;; | TAB             | 模糊音调整       |

;; *** 让选词框跟随光标
;; Chinese-pyim 可以使用 emacs tooltip 功能在 *光标处* 显示一个选词框，
;; 用户可以通过下面的设置来开启这个功能。

;; #+BEGIN_EXAMPLE
;; (setq pyim-use-tooltip t)
;; #+END_EXAMPLE

;; *** 设置模糊音
;; Chinese-pyim 使用一个比较 *粗糙* 的方法处理 *模糊音* ，要了解具体细节，
;; 请运行：

;; #+BEGIN_EXAMPLE
;; C-h v pyim-fuzzy-pinyin-adjust-function
;; #+END_EXAMPLE

;; *** 动态中英文切换
;; Chinese-pyim  可以根据输入内容动态的切换中英文输入，
;; 基本规则是：

;; 1. 当前字符为英文字符时，输入下一个字符时默认开启英文输入
;; 2. 当前字符为中文字符时，输入下一个字符时默认开启中文输入
;; 3. 当前字符为中文字符时，输入1个空格后，仍然输入中文
;; 4. 当前字符为英文字符时，输入1个空格后，仍然输入英文
;; 5. 当前字符为中文字符时，输入2个空格后，切换到英文输入
;; 6. 当前字符为英文字符时，输入2个空格后，切换到中文输入

;; 激活方法：

;; #+BEGIN_EXAMPLE
;; (setq-default pyim-english-input-switch-function
;;               'pyim-dynamic-english-input-function)
;; #+END_EXAMPLE

;; *** 词语联想
;; Chinese-pyim *内置* 了4种词语联想方式：

;; 1. `pinyin-similar' 搜索拼音类似的词条做为联想词，
;;     如果输入 "ni-hao" ，那么搜索拼音与 "ni-hao" 类似的词条
;;     （比如："ni-hao-a"）作为联想词。
;; 2. `pinyin-shouzimu' 搜索拼音首字母对应的词条做为联想词，
;;     如果输入 "ni-hao" ，那么同时搜索 code 为 "n-h" 的词条做为联想词。
;; 3. `pinyin-znabc' 类似智能ABC的词语联想(源于 emacs-eim)。
;; 4. `guess-words' 以上次输入的词条为 code，然后在 guessdict 中搜索，
;;     用搜索得到的词条来提高输入法识别精度。

;;     注意：这个方法需要用户安装 guessdict 词库，guessdict 词库文件可以
;;     用 `pyim-article2dict-guessdict' 命令生成，不想折腾的用户也可以从
;;     下面的地址下载样例词库：(注意：请使用另存为，不要直接点击链接)。

;;     1. http://tumashu.github.io/chinese-pyim-guessdict/pyim-guessdict-a.gpyim
;;     2. http://tumashu.github.io/chinese-pyim-guessdict/pyim-guessdict-b.gpyim

;; Chinese-pyim 默认开启了词语联想功能，但用户可以通过下面的代码来调整设置，比如：

;; #+BEGIN_EXAMPLE
;; (setq pyim-enable-words-predict '(pinyin-similar pinyin-shouzimu guess-words))
;; #+END_EXAMPLE

;; 开启词语联想功能有时候会导致输入法卡顿，用户可以通过下面的方式关闭：

;; #+BEGIN_EXAMPLE
;; (setq pyim-enable-words-predict nil)
;; #+END_EXAMPLE

;; 另外，Chinese-pyim 也可以通过 Company 框架来实现词语联想，
;; 具体请参考： [[使用 Company 框架来补全联想词（实验特性）]]

;; *** 切换全角标点与半角标点

;; 1. 第一种方法：使用命令 `pyim-toggle-full-width-punctuation'，全局切换。
;; 2. 第二种方法：使用命令 `pyim-punctuation-translate-at-point' 只切换光
;;    标处标点的样式。
;; 3. 第三种方法：设置变量 `pyim-translate-trigger-char'。输入变量设定的
;;    字符会切换光标处标点的样式。

;; *** 手动加词和删词

;; 1. `pyim-create-word-without-pinyin' 直接将一个中文词条加入个人词库的
;;    函数，用于编程环境。
;; 2. `pyim-create-word-at-point:<N>char' 这是一组命令，从光标前提取N个汉
;;    字字符组成字符串，并将其加入个人词库。
;; 3. `pyim-translate-trigger-char' 以默认设置为例：在“我爱吃红烧肉”后输
;;    入“5v” 可以将“爱吃红烧肉”这个词条保存到用户个人词频文件。
;; 4. `pyim-delete-word-from-personal-buffer' 从个人词频文件对应的 buffer
;;    中删除当前高亮选择的词条。

;; *** 快速切换词库
;; 用户可以自定义类似的命令来实现快速切换拼音词库。

;; #+BEGIN_EXAMPLE
;; (defun pyim-use-dict:bigdict ()
;;   (interactive)
;;   (setq pyim-dicts
;;         '((:name "BigDict"
;;                  :file "/path/to/pyim-bigdict.txt"
;;                  :coding utf-8-unix)))
;;   (pyim-restart-1 t))
;; #+END_EXAMPLE

;; *** 使用 Company 框架来补全联想词（实验特性）

;; `Chinese-pyim' 增加了两个 `company-mode' 后端来实现 *联想词* 输入功能：

;; 1. `pyim-company-dabbrev' 是 `company-dabbrev' 的中文优化版，适用于补全其它 buffer 中的中文词语。
;; 2. `pyim-company-predict-words' 可以从 Chinese-pyim 词库中搜索与当前中文词条相近的词条。

;; 安装和使用方式：

;; 1. 安装 `company-mode' 扩展包。
;; 2. 在 emacs 配置中添加如下几行代码：

;; #+BEGIN_EXAMPLE
;; (require 'chinese-pyim-company)
;; #+END_EXAMPLE

;; 可以通过 pyim-company-predict-words-number 来设置联想词的数量，
;; 比如：从词库中搜索10个联想词可以设置为：

;; #+BEGIN_EXAMPLE
;; (setq pyim-company-predict-words-number 10)
;; #+END_EXAMPLE

;; ** Tips

;; *** 选词框弹出位置不合理或者选词框内容显示不全
;; 可以通过设置 `pyim-tooltip-width-adjustment' 变量来手动校正。

;; 1. 选词框内容显示不全：增大变量值
;; 2. 选词框弹出位置不合理：减小变量值

;; *** 如何查看 Chinese-pyim 文档。
;; Chinese－-pyim 开发使用 lentic 文学编程模式，代码文档隐藏在comment中，如
;; 果用户喜欢阅读 html 格式的文档，可以查看在线文档；

;;   http://tumashu.github.io/chinese-pyim/

;; *** 如何添加自定义拼音词库
;; Chinese-pyim 默认没有携带任何拼音词库，用户可以使用下面三种方式，获取
;; 质量较好的拼音词库：

;; **** 第一种方式 (懒人推荐使用)

;; 获取其他 Chinese-pyim 用户的拼音词库，比如，某个同学测试 Chinese-pyim
;; 时创建了一个中文拼音词库，词条数量大约60万，文件大约20M，(注意：请使用
;; 另存为，不要直接点击链接)。

;;    http://tumashu.github.io/chinese-pyim-bigdict/pyim-bigdict.pyim

;; 下载上述词库后，运行 `pyim-dicts-manager' ，按照命令提示，将下载得到的词库
;; 文件信息添加到 `pyim-dicts' 中，最后运行命令 `pyim-restart' 或者重启
;; emacs，这个词库使用 `utf-8-unix' 编码。

;; **** 第二种方式 (Windows 用户推荐使用)

;; 使用词库转换工具将其他输入法的词库转化为Chinese-pyim使用的词库：这里只介绍windows平
;; 台下的一个词库转换软件：

;; 1. 软件名称： imewlconverter
;; 2. 中文名称： 深蓝词库转换
;; 3. 下载地址： https://github.com/studyzy/imewlconverter
;; 4. 依赖平台： Microsoft .NET Framework 2.0

;; 首先从其他拼音输入法网站上获取所需词库，使用下述自定义输出格式转换词库文件，然后将转
;; 换得到的内容保存到文件中。

;; #+BEGIN_EXAMPLE
;; shen,lan,ci,ku 深蓝词库
;; #+END_EXAMPLE

;; 将文件中所有","替换为"-"，得到的文件每一行都类似：

;; #+BEGIN_EXAMPLE
;; shen-lan-ci-ku 深蓝词库
;; #+END_EXAMPLE

;; 最后，运行 `pyim-dicts-manager' ，按照命令提示，将转换得到的词库文件的信息添加到 `pyim-dicts' 中，
;; 完成后运行命令 `pyim-restart' 或者重启emacs。

;; **** 第三种方式 (Linux & Unix 用户推荐使用)
;; E-Neo 同学编写了一个简单的词库转换工具: [[https://github.com/E-Neo/scel2pyim][scel2pyim]] ,
;; 这个小工具可以直接将搜狗输入法的细胞词库转换为 Chinese-pyim 使用的文本词库，
;; pyim-dicts-manager 中 “导入搜狗输入法细胞词库” 功能就是依靠这个工具实现。

;; 1. 软件名称： scel2pyim
;; 2. 下载地址： https://github.com/E-Neo/scel2pyim
;; 3. 编写语言： C语言

;; 按照说明安装好 scel2pyim 后，将scel2pyim命令所在的目录添加到系统PATH，或者在 emacs 配置文件中
;; 添加代码：

;; #+BEGIN_EXAMPLE
;; (setq pyim-dicts-manager-scel2pyim-command "/path/to/scel2pyim")
;; #+END_EXAMPLE

;; **** 第四种方式 (喜欢折腾的人推荐使用)
;; 获取中文词条，然后使用命令为词条添加拼音code。中文词条的获取途径很多，比如：

;; 1. 从其它输入法中导出。
;; 2. 获取中文文章，通过分词系统分词得到。
;; 3. 中文处理工具自带的dict。
;; 4. 其它。

;; 相关命令有三个：

;; 1. `pyim-article2dict-chars' 将文章中游离汉字字符转换为拼音词库。
;; 2. `pyim-article2dict-words' 将文章中中文词语转换为拼音词库。
;; 3. `pyim-article2dict-misspell-words' 将文章中连续的游离词组成字符串后，
;;    转换为拼音词库。
;; 4. `pyim-article2dict-guessdict' 将文章中词条转换为 guessdict词库。

;; 注意：在运行上述两个命令之前，必须确保待转换的文章中，中文词汇已经使用
;; *空格* 强制隔开。

;; 最后将生成的词库按上述方法添加到 Chinese-pyim 中就可以了。

;; *** 如何手动安装和管理词库
;; 这里假设有两个词库文件：

;; 1. /path/to/pyim-dict1.txt
;; 2. /path/to/pyim-dict2.txt

;; 在~/.emacs文件中添加如下一行配置。

;; #+BEGIN_EXAMPLE
;; (setq pyim-dicts
;;       '((:name "dict1" :file "/path/to/pyim-dict1.txt" :coding gbk-dos)
;;         (:name "dict2" :file "/path/to/pyim-dict2.txt" :coding gbk-dos)))
;; #+END_EXAMPLE

;; 注意事项:
;; 1. 必须使用词库文件的绝对路径。
;; 2. 正确设置coding，否则会出现乱码。

;; *** 将汉字字符串转换为拼音字符串
;; 下面两个函数可以将中文字符串转换的拼音字符串或者列表，用于 emacs-lisp
;; 编程。

;; 1. `pyim-hanzi2pinyin' （考虑多音字）
;; 2. `pyim-hanzi2pinyin-simple'  （不考虑多音字）

;; *** 中文分词
;; Chinese-pyim 包含了一个简单的分词函数：`pyim-split-chinese-string'. 这个函数
;; 使用暴力匹配模式来分词，所以，*不能检测出* Chinese-pyim 词库中不存在的中文词条。
;; 另外，这个函数的分词速度比较慢，仅仅适用于中文短句的分词，不适用于文章分词。
;; 根据评估，20个汉字组成的字符串需要大约0.3s， 40个汉字消耗1s，随着字符串长度的
;; 增大消耗的时间呈几何倍数增加。

;; 举例来说：

;; #+BEGIN_EXAMPLE
;;                   (("天安" 5 7)
;; 我爱北京天安门 ->  ("天安门" 5 8)
;;                    ("北京" 3 5)
;;                    ("我爱" 1 3))
;; #+END_EXAMPLE

;; 其中，每一个词条列表中包含三个元素，第一个元素为词条本身，第二个元素为词条
;; 相对于字符串的起始位置，第三个元素为词条结束位置。

;; 另外一个分词相关的函数是 `pyim-split-chinese-string2string', 这个函数仅仅将一个
;; 中文字符串分词，在分词的位置用空格或者用户自定义的分隔符隔开，然后返回新的字符串。

;; 用户可以通过运行命令 `pyim-cache-dict-buffer' 来缓存 Chinese-pyim 的词库 buffer，
;; 使用缓存可以提高分词的速度。

;; 注：仅仅对一般词库有效，个人文件和 guessdict 词库无效。


;; *** 获取光标处的中文词条
;; Chinese-pyim 包含了一个简单的命令：`pyim-get-words-list-at-point', 这个命令
;; 可以得到光标处的 *英文* 或者 *中文* 词条的 *列表*，这个命令依赖分词函数：
;; `pyim-split-chinese-string'。

;; *** 让 `forward-word' 和 `back-backward’ 在中文环境下正常工作
;; 中文词语没有强制用空格分词，所以 emacs 内置的命令 `forward-word' 和 `backward-word'
;; 在中文环境不能按用户预期的样子执行，而是 forward/backward “句子” ，Chinese-pyim
;; 自带的两个命令可以在中文环境下正常工作：

;; 1. `pyim-forward-word
;; 2. `pyim-backward-word

;; 用户只需将其绑定到快捷键上就可以了，比如：

;; #+BEGIN_EXAMPLE
;; (global-set-key (kbd "M-f") 'pyim-forward-word)
;; (global-set-key (kbd "M-b") 'pyim-backward-word)
;; #+END_EXAMPLE


;;; Code:
;; * 代码                                                                 :code:
;; #+BEGIN_SRC emacs-lisp
(require 'chinese-pyim-pymap)
(require 'chinese-pyim-core)
(require 'chinese-pyim-dictools)
(require 'chinese-pyim-utils)
;; #+END_SRC

;; * Footer
;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim)

;; Local Variables:
;; coding: utf-8-unix
;; tab-width: 4
;; indent-tabs-mode: nil
;; lentic-init: lentic-el2org-init
;; End:

;;; chinese-pyim.el ends here
;; #+END_SRC
