;;; chinese-pyim-core.el --- The core of Chinese pinyin input method

;; * Header
;; Copyright 2006 Ye Wenbin
;;           2014-2015 Feng Shu

;; Author: Ye Wenbin <wenbinye@163.com>, Feng Shu <tumashu@163.com>
;; URL: https://github.com/tumashu/chinese-pyim
;; Version: 0.0.1
;; Package-Requires: ((cl-lib "0.5") (pos-tip "0.4") (popup "0.1"))
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

;; * 说明文档                                                           :doc:
;; Chinese pyim 输入法的核心文件，包含了输入法的基本功能函数，比如：
;; 1. 加载和搜索词库
;; 2. 处理拼音字符串
;; 3. 处理备选词条
;; 4. 显示备选词条
;; 5. 其它

;;; Code:

;; * 核心代码                                                           :code:
;; ** require + defcustom + defvar
;; #+BEGIN_SRC emacs-lisp
(require 'cl-lib)
(require 'help-mode)
(require 'pos-tip)
(require 'popup)
(require 'chinese-pyim-pymap)

(defgroup chinese-pyim nil
  "Chinese pinyin input method"
  :group 'leim)

(defcustom pyim-directory (locate-user-emacs-file "pyim/")
  "一个目录，用于保存与 Chinese-pyim 相关的文件。"
  :group 'chinese-pyim)

(defcustom pyim-personal-file
  (concat (file-name-as-directory pyim-directory)
          "pyim-personal.txt")
  "这个文件用来保存用户曾经输入过的中文词条，和这些词条输入的先后顺序。"
  :group 'chinese-pyim
  :type 'file)

(defcustom pyim-dicts nil
  "一个列表，用于保存 `Chinese-pyim' 的词库信息，每一个 element 都代表一条词库的信息。
用户可以使用词库管理命令 `pyim-dicts-manager' 来添加词库信息，每一条词库信息都使用一个
plist 来表示，比如：

    (:name \"100万大词库\"
     :file \"/path/to/pinyin-bigdict.txt\"
     :coding utf-8-unix
     :dict-type pinyin-dict)

其中：
1. `:name'      代表词库名称，用户可以按照喜好来确定。
2. `:coding'    表示词库文件使用的编码。
3. `:file'      表示词库文件，
4. `:dict-type' 表示词库文件是普通词库文件还是 guessdict 词库文件。"
  :group 'chinese-pyim
  :type 'list)

(defcustom pyim-dicts-directory
  (concat (file-name-as-directory pyim-directory)
          "dicts/")
  "一个目录，用于保存 Chinese-pyim 词库管理器下载或者导入的词库文件"
  :group 'chinese-pyim)

(defcustom pyim-punctuation-dict
  '(("'" "‘" "’")
    ("\"" "“" "”")
    ("_" "―")
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
  "标点符号表。"
  :group 'chinese-pyim
  :type 'list)

(defcustom pyim-default-pinyin-scheme 'default
  "设置 Chinese-pyim 使用哪一种拼音方案，默认使用全拼输入。"
  :group 'chinese-pyim)

(defcustom pyim-pinyin-schemes
  '((default
      :document "全拼输入法方案（不可删除）。"
      :class quanpin
      :first-chars "abcdefghjklmnopqrstwxyz"
      :rest-chars "vmpfwckzyjqdltxuognbhsrei'-a"
      :prefer-trigger-chars "v")
    (pyim-shuangpin
     :document "与 Chinese-pyim 配合良好的双拼输入法方案，源自小鹤双拼方案。"
     :class shuangpin
     :first-chars "abcdefghijklmnpqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz"
     :prefer-trigger-chars "o"
     :keymaps-general (("a" "a" "a")
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
                       ("z" "z" "ou"))
     :keymaps-special ((("a" . "a") ("" . "a"))
                       (("a" . "j") ("" . "an"))
                       (("a" . "d") ("" . "ai"))
                       (("a" . "c") ("" . "ao"))
                       (("a" . "h") ("" . "ang"))
                       (("e" . "e") ("" . "e"))
                       (("e" . "w") ("" . "ei"))
                       (("e" . "f") ("" . "en"))
                       (("e" . "r") ("" . "er"))
                       (("e" . "g") ("" . "eng"))
                       (("a" . "g") ("" . "ng"))
                       (("a" . "o") ("" . "o"))
                       (("a" . "u") ("" . "ou"))))
    (xiaohe-shuangpin
     :document "小鹤双拼输入法方案。"
     :class shuangpin
     :first-chars "abcdefghijklmnopqrstuvwxyz"
     :rest-chars "abcdefghijklmnopqrstuvwxyz"
     :prefer-trigger-chars nil
     :keymaps-general (("a" "a" "a")
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
                       ("z" "z" "ou"))
     :keymaps-special ((("a" . "a") ("" . "a"))
                       (("a" . "j") ("" . "an"))
                       (("a" . "d") ("" . "ai"))
                       (("a" . "c") ("" . "ao"))
                       (("a" . "h") ("" . "ang"))
                       (("e" . "e") ("" . "e"))
                       (("e" . "w") ("" . "ei"))
                       (("e" . "f") ("" . "en"))
                       (("e" . "r") ("" . "er"))
                       (("e" . "g") ("" . "eng"))
                       (("o" . "g") ("" . "ng"))
                       (("o" . "o") ("" . "o"))
                       (("o" . "u") ("" . "ou")))))
  "Chinese-pyim 支持的所有拼音方案。")

(defcustom pyim-translate-trigger-char "v"
  "用于触发特殊操作的字符，相当与单字快捷键。

Chinese-pyim 内建的功能有：
1. 光标前面的字符为标点符号时，按这个字符可以切换前面的标
   点符号的样式（半角/全角）
2. 当光标前面为中文字符串时，输入 <num>v 可以用于保存自定义词条。
3. 其它。

注意：单字快捷键受到拼音方案的限制，比如：全拼输入法可以将其设置为v,
但双拼输入法下设置 v 可能就不行，所以，Chinese-pyim 首先会检查
当前拼音方案下，这个快捷键设置是否合理有效，如果不是一个合理的设置，
则使用拼音方案默认的 :prefer-trigger-chars 。

具体请参考 `pyim-get-translate-trigger-char' 。"
  :group 'chinese-pyim
  :type 'character)

(defcustom pyim-fuzzy-pinyin-adjust-function
  'pyim-fuzzy-pinyin-adjust-1
  "设定糢糊音处理函数"
  :group 'chinese-pyim
  :type 'function)

(defcustom pyim-enable-words-predict
  '(dabbrev pinyin-shouzimu pinyin-similar pinyin-znabc guess-words)
  "一个 list，用于设置词语联想方式，当前支持：

1. `pinyin-similar' 搜索拼音类似的词条做为联想词。
2. `pinyin-shouzimu' 搜索拼音首字母对应的词条做为联想词。
3. `pinyin-znabc' 类似智能ABC的词语联想(源于 emacs-eim)。
4. `guess-words' 以上次输入的词条为 code，然后在 guessdict 中搜索，
                 用搜索得到的词条来提高输入法识别精度。

                 注意：这个方法需要用户安装 guessdict 词库，
                       guessdict 词库文件可以用 `pyim-article2dict-guessdict'
                       命令生成。
5. `dabbrev'  搜索当前 buffer, 或者其他 buffer 中已经存在的中文文本，得到匹配的
              候选词，通过这些候选词来提高输入法的识别精度。

              注意：如果用户打开的 buffer 太多或者太大，输入法 *可能* 会出现 *卡顿* 。

当这个变量设置为 nil 时，关闭词语联想功能。"
  :group 'chinese-pyim)

(defcustom pyim-dabbrev-other-buffers 'all
  "设置 dabbrev 词语联想需要搜索的 buffer，如果设置为 `all', 搜索所有的 buffer,
如果设置为 t, 搜索所有和当前 buffer 模式相同的 buffer, 如果设置为 nil, 则只搜索
当前 buffer."
  :group 'chinese-pyim)

(defcustom pyim-dabbrev-ignore-buffers '("\\`[ *]" "\\.pyim" "\\.gpyim")
  "Regexp list, matching the names of buffers to ignore."
  :type 'list)

(defcustom pyim-isearch-enable-pinyin-search nil
  "设置是否开启 isearch 中文拼音搜索功能。"
  :group 'chinese-pyim
  :type 'boolean)

(defcustom pyim-page-length 5
  "每页显示的词条数目"
  :group 'chinese-pyim
  :type 'number)

(defface pyim-string-face '((t (:underline t)))
  "Face to show current string"
  :group 'chinese-pyim)

(defface pyim-minibuffer-string-face '((t (:background "gray40")))
         "Face to current string show in minibuffer"
         :group 'chinese-pyim)

(defcustom pyim-english-input-switch-functions nil
  "这个变量的取值为一个函数列表，这个函数列表中的任意一个函数的运行结果为 t 时，
Chinese-pyim 也开启英文输入功能。"
  :group 'chinese-pyim)

(defalias 'pyim-english-input-switch-function 'pyim-english-input-switch-functions)
(make-obsolete 'pyim-english-input-switch-function 'pyim-english-input-switch-functions
               "Chinese-pyim 1.0")

(defcustom pyim-punctuation-half-width-functions nil
  "取值为一个函数列表，这个函数列表中的任意一个函数的运行结果为 t 时，
Chinese-pyim 输入半角标点，函数列表中每个函数都有一个参数：char ，表示
最后输入的一个字符，具体见: `pyim-translate' 。"
  :group 'chinese-pyim)

(defcustom pyim-select-word-finish-hook nil
  "Chinese-pyim 选词完成时运行的hook，"
  :group 'chinese-pyim
  :type 'hook)

(defcustom pyim-wash-function 'pyim-wash-current-line-function
  "这个函数与『单字快捷键配合使用』，当光标前面的字符为汉字字符时，
按 `pyim-translate-trigger-char' 对应字符，可以调用这个函数来清洗
光标前面的文字内容。"
  :group 'chinese-pyim
  :type 'function)

(defcustom pyim-use-tooltip 'popup
  "如何绘制 Chinese-pyim 选词框。

1. 当这个变量取值为 t 或者 'popup 时，使用 popup-el 包来绘制选词框；
2. 当取值为 pos-tip 时，使用 pos-tip 包来绘制选词框；
3. 当取值为 nil 时，将 minibuffer 做为选词框；"
  :group 'chinese-pyim)

(defcustom pyim-tooltip-width-adjustment 1.2
  "校正 tooltip 选词框宽度的数值，表示校正后的宽度是未校正前宽度的倍数。

由于字体设置等原因，pos-tip 选词框实际宽度会比 *预期宽度* 偏大或者偏小，
这时，有可能会出现选词框词条显示不全或者选词框弹出位置不合理等问题。用户可以通过
增大或者减小这个变量来改变 tooltip 选词框的宽度，取值大概在 0.5 ~ 2.0 范围之内。

注：这个选项只适用于 `pyim-use-tooltip' 取值为 'pos-tip 的时候。"
  :group 'chinese-pyim)

(defcustom pyim-line-content-limit 1000
  "限制词库文件中的行长度。如果行太长，在windows平台下会出现严重的性能问题。"
  :group 'chinese-pyim)

(defvar pyim-debug nil)
(defvar pyim-title "灵拼" "Chinese-pyim 在 mode-line 中显示的名称。")
(defvar pyim-buffer-name " *Chinese-pyim*")
(defvar pyim-buffer-list nil
  "一个列表，用来保存词库文件与 buffer 的对应信息。
1. 每个元素都是一个 alist。
2. 每一个 alist 都包含两个部份：
   1. buffer 词库文件导入时创建的 buffer (用户不可见)。
   2. file   词库文件的路径。")

(defvar pyim-buffer-cache-list nil
  "一个列表，用来缓存 `pyim-buffer-list' 中的普通词库 buffer，以加快访问速度。

1. 每个元素都是一个 alist。
2. 每一个 alist 都包含两个部份：
   1. buffer 词库文件导入时创建的 buffer (用户不可见)。
   2. buffer-cache 从词库 buffer 中构建的一个 hashtable。

注意： *不缓存* 个人词库文件 buffer 和 guessdict 词库文件 buffer。")

(defvar pyim-shen-mu
  '("b" "p" "m" "f" "d" "t" "n" "l" "g" "k" "h"
    "j" "q" "x" "z" "c" "s" "zh" "ch" "sh" "r" "y" "w"))

(defvar pyim-yun-mu
  '("a" "o" "e" "i" "u" "v" "ai" "ei" "ui" "ao" "ou" "iu"
    "ie" "ia" "ua" "ve" "er" "an" "en" "in" "un" "vn" "ang" "iong"
    "eng" "ing" "ong" "uan" "uang" "ian" "iang" "iao" "ue"
    "uai" "uo"))

(defvar pyim-valid-yun-mu
  '("a" "o" "e" "ai" "ei" "ui" "ao" "ou" "er" "an" "en"
    "ang" "eng"))

(defvar pyim-char-table (make-vector 1511 nil))

(defvar pyim-current-key "" "已经输入的代码")
(defvar pyim-current-str "" "当前选择的词条")
(defvar pyim-last-input-word "" "保存上一次输入过的词条，用于实现某种词语联想功能。")
(defvar pyim-input-ascii nil
  "是否开启 Chinese-pyim 英文输入模式。")

(defvar pyim-current-choices nil
  "所有可选的词条，是一个list。
1. CAR 部份是可选的词条，一般是一个字符串列表。
   也可以含有list。但是包含的list第一个元素必须是将要插入的字符串。
2. CDR 部分是一个 Association list。通常含有这样的内容：
   1. pos 上次选择的位置
   2. completion 下一个可能的字母（如果 pyim-do-completion 为 t）")

(defvar pyim-translating nil "记录是否在转换状态")

(defvar pyim-overlay nil "显示当前选择词条的 overlay")

(defvar pyim-pinyin-position nil)
(defvar pyim-pylist-list nil
  "Chinese-pyim 会将一个拼音字符串分解为一个或者多个 pylist （常见于双拼模式）,
这个变量用于保存分解得到的结果。")

(defvar pyim-guidance-str "" "显示可选词条的字符串")
(defvar pyim-current-pos nil "当前选择的词条在 pyim-current-choices 中的位置")

(defvar pyim-load-hook nil)
(defvar pyim-active-hook nil)

(defvar pyim-punctuation-translate-p t
  "*Non-nil means will translate punctuation.")

(defvar pyim-pair-punctuation-status
  '(("\"" nil) ("'" nil))
  "成对标点符号切换状态")

(defvar pyim-punctuation-escape-list (number-sequence ?0 ?9)
  "Punctuation will not insert after this characters.
If you don't like this funciton, set the variable to nil")

(defvar pyim-dabbrev-time-limit .1
  "Determines how many seconds should look for dabbrev matches.")

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
    (dolist (i (number-sequence ?1 ?9))
      (define-key map (char-to-string i) 'pyim-number-select))
    (define-key map " " 'pyim-select-current)
    (define-key map [backspace] 'pyim-delete-last-char)
    (define-key map (kbd "M-DEL") 'pyim-backward-kill-py)
    (define-key map [tab] 'pyim-fuzzy-pinyin-adjust)
    (define-key map (kbd "TAB") 'pyim-fuzzy-pinyin-adjust)
    (define-key map "\M-g" 'pyim-fuzzy-pinyin-adjust)
    (define-key map [delete] 'pyim-delete-last-char)
    (define-key map "\177" 'pyim-delete-last-char)
    (define-key map "\C-n" 'pyim-next-page)
    (define-key map "\C-p" 'pyim-previous-page)
    (define-key map "\C-f" 'pyim-next-word)
    (define-key map "\C-b" 'pyim-previous-word)
    (define-key map "=" 'pyim-next-page)
    (define-key map "-" 'pyim-previous-page)
    (define-key map "\M-n" 'pyim-next-page)
    (define-key map "\M-p" 'pyim-previous-page)
    (define-key map "\C-m" 'pyim-quit-no-clear)
    (define-key map [return] 'pyim-quit-no-clear)
    (define-key map "\C-c" 'pyim-quit-clear)
    (define-key map "\C-g" 'pyim-quit-clear)
    map)
  "Keymap")
;; #+END_SRC

;; ** 将变量转换为 local 变量
;; #+BEGIN_SRC emacs-lisp
(defvar pyim-local-variable-list
  '(pyim-current-key
    pyim-current-str
    pyim-current-choices
    pyim-current-pos
    pyim-input-ascii
    pyim-english-input-switch-function ;; obsolete
    pyim-english-input-switch-functions
    pyim-punctuation-half-width-functions
    pyim-guidance-str
    pyim-translating
    pyim-overlay

    pyim-load-hook
    pyim-active-hook

    input-method-function
    inactivate-current-input-method-function
    describe-current-input-method-function

    pyim-punctuation-translate-p
    pyim-pair-punctuation-status
    pyim-punctuation-escape-list

    pyim-pylist-list
    pyim-pinyin-position)
  "A list of buffer local variable")

(dolist (var pyim-local-variable-list)
  (make-variable-buffer-local var)
  (put var 'permanent-local t))
;; #+END_SRC
;; ** 输入法启动和重启
;; Chinese-pyim 使用 emacs 官方自带的输入法框架来启动输入法和重启输入法。
;; 所以我们首先需要使用 emacs 自带的命令 `register-input-method' 注册一个
;; 输入法。

;; #+BEGIN_SRC emacs-lisp
;;; 注册输入法
(register-input-method "chinese-pyim" "euc-cn" 'pyim-start pyim-title)
;; #+END_SRC

;; 真正启动 Chinese-pyim 的命令是 `pyim-start' ，这个命令做如下工作：
;; 1. 重置 `pyim-local-variable-list' 中所有的 local 变量。
;; 2. 使用 `pyim-load-file’加载词库文件，具体细节请参考：[[#load-dicts]]
;; 3. 使用 `pyim-make-char-table' 创建汉字到拼音的 hash table，具体细节请
;;    参考：[[#make-char-table]]
;; 4. 运行hook： `pyim-load-hook'。
;; 5. 将 `pyim-save-personal-file' 命令添加到 `kill-emacs-hook' emacs 关
;;    闭之前将个人词频 buffer 的内容保存到个人词频文件。具体细节请参考：
;;    [[save-personal-file]]。
;; 6. 设定变量：
;;    1. `input-method-function'
;;    2. `deactivate-current-input-method-function'
;; 7. 运行 `pyim-active-hook'

;; `pyim-start' 先后会运行两个 hook，所以我们需要事先定义：

;; `pyim-restart' 用于重启 Chinese-pyim，其过程和 `pyim-start' 类似，不同
;; 之处有：

;; 1. 输入法重启之前会询问用户，是否保存个人词频信息。
;; 2. 重启之前会使用函数 `pyim-kill-buffers' 删除所有的词库 buffer，具体
;;    请参考： [[pyim-kill-buffers]]

;; #+BEGIN_SRC emacs-lisp
(defun pyim-start (name &optional active-func restart save-personal-file)
  (interactive)
  (mapc 'kill-local-variable pyim-local-variable-list)
  (mapc 'make-local-variable pyim-local-variable-list)
  ;; 重启时，kill 所有已经打开的 buffer。
  (when (and restart save-personal-file)
    (pyim-save-personal-file))
  (when restart
    (pyim-kill-buffers)
    (setq pyim-buffer-list nil))
  (unless (and pyim-buffer-list
               (pyim-check-buffers)
               (not restart))
    (setq pyim-buffer-list (pyim-load-file))
    (pyim-make-char-table)
    (run-hooks 'pyim-load-hook)
    (message nil))

  (unless (member 'pyim-save-personal-file kill-emacs-hook)
    (add-to-list 'kill-emacs-hook 'pyim-save-personal-file))

  (setq input-method-function 'pyim-input-method)
  (setq deactivate-current-input-method-function 'pyim-inactivate)
  ;; (setq describe-current-input-method-function 'pyim-help)
  ;; If we are in minibuffer, turn off the current input method
  ;; before exiting.
  (when (eq (selected-window) (minibuffer-window))
    (add-hook 'minibuffer-exit-hook 'pyim-exit-from-minibuffer))
  (run-hooks 'pyim-active-hook)
  (when restart
    (message "Chinese-pyim 重启完成。")))

(defun pyim-exit-from-minibuffer ()
  (deactivate-input-method)
  (when (<= (minibuffer-depth) 1)
    (remove-hook 'minibuffer-exit-hook 'quail-exit-from-minibuffer)))

(defun pyim-restart ()
  "重启 Chinese-pyim，不建议用于编程环境。"
  (interactive)
  (let ((file-save-p
         (yes-or-no-p "正在重启 Chinese-pyim，需要保存 personal 文件的变动吗？ ")))
    (pyim-restart-1 file-save-p)))

(defun pyim-restart-1 (save-personal-file)
  "重启 Chinese-pyim，用于编程环境。"
  (pyim-start "Chinese-pyim" nil t save-personal-file))
;; #+END_SRC
;; ** 处理词库文件
;; *** 自定义词库
;; **** 词库文件格式
;; Chinese-pyim 使用词库文件来保存各个拼音对应的中文词条，每一个词库文件都
;; 是简单的文本文件，其结构类似：

;; #+BEGIN_EXAMPLE
;; ni-bu-hao 你不好
;; ni-hao  你好 妮好 你豪
;; #+END_EXAMPLE

;; 第一个空白字符之前的内容为拼音code，空白字符之后为中文词条列表。
;; 拼音词库 *不处理* 中文标点符号。

;; 注意：词库文件必须按行排序（准确的说，是按每一行的 code 排序），因为
;; `Chinese-pyim' 为优化搜索速度，使用二分法寻找词条，而二分法工作的前提就是对
;; 文件按行排序。具体细节请参考：`pyim-bisearch-word' 。当用户手动调整词库文
;; 件后，记得运行 `pyim-update-dict-file' 来对文件排序。

;; **** 个人词频文件
;; 虽然 Chinese-pyim 只使用一种词库文件格式，但定义了两种词库类型，用于不
;; 同的目的：
;; 1. 个人词频文件
;; 2. 普通词库文件
;; 3. Guessdict词库文件

;; 个人词频文件用来保存用户曾经输入过的中文词条以及这些词条输入的先后顺序
;; （也就是词频信息）。Chinese-pyim 搜索中文词条时，个人词频文件里的词条
;; 优先显示。我们使用变量 `pyim-personal-file' 来保存个人词频文件的路径:

;; 个人词频文件使用上述词库文件的格式来保存上述信息，将其独立出来的原因是：
;; 1. 随着 `Chinese-pyim' 使用时间的延长，个人词频文件会保存越来越多的用
;;    户常用的词条，属于用户隐私（提醒用户不要随意将这个文件泄露他人）。
;; 2. 个人词频文件的内容在 Chinese-pyim 使用过程中频繁的变动。
;; 3. 随着个人词频文件的积累，Chinese-pyim 会越来越顺手，所以个人词频文件
;;    需要用户经常备份。

;; 值得注意的是：不建议用户 *手动编辑* 这个文件，因为：每次 emacs 关闭之
;; 前，emacs 会运行命令：`pyim-save-personal-file' 来更新这个文件，编辑过
;; 的内容将会被覆盖。

;; BUG：当用户错误的将这个变量设定为其他重要文件时，也存在文件内容破坏的风险。

;; 当这个文件中的词条数量增长到一定程度，用户可以直接将这个文件转换为词库。

;; **** 普通词库文件 和 Guessdict词库
;; 普通词库文件，也可以叫做共享词库文件，与个人词频文件相比，普通词库文件
;; 有如下特点：
;; 1. 词条数量巨大：普通词库文件中往往包含大量的词条信息（可能超过50万）。
;; 2. 内容变化很小：用户一般不需要编辑普通词库文件（开发词库的用户除外），
;;    所以普通词库文件的内容一般不会发生改变。
;; 3. 普通词库文件适宜制作词库包，在用户之间共享。

;; Guessdict词库用于词语联想，它与普通词库文件有类似的特征，唯一不同的是：
;; Guessdict词库的 code 是中文，而不是拼音。

;; #+BEGIN_EXAMPLE
;; 我爱 北京 美女 旅游
;; 我们 去哪 去看海
;; #+END_EXAMPLE

;; 我们使用变量 `pyim-dicts' 来设定普通词库文件和 guessdict 词库的信息：
;; 1. `:name' 用户给词库设定的名称，暂时没有用处，未来可能用于构建词库包。
;; 2. `:file' 词库文件的绝对路径。
;; 3. `:coding' 词库文件的编码，词库文件是一个文本文件，window系统一般使
;;    用 GBK 编码来保存中文，而Linux系统一般使用 UTF-8 编码来保存中文，
;;    emacs 似乎不能自动识别中文编码，所以要求用户明确告知词库文件使用什
;;    么编码来保存。
;; 4. `:dict-type' 当前词库文件是普通词库还是 guessdict 词库，普通词库
;;     设置为 pinyin-dict，guessdict 词库设置为 guess-dict。

;; *** 加载词库
;;    :PROPERTIES:
;;    :CUSTOM_ID: load-dicts
;;    :END:
;; Chinese-pyim 激活时，首先会使用 `pyim-load-file' 加载个人词频文件和普
;; 通词库文件，如果个人词频文件不存在时，Chinese-pyim 会使用函数：
;; `pyim-create-template-dict' 自动创建这个文件。如果用户没有设定
;; `pyim-dicts'， `pyim-load-file' 会弹出警告信息，告知用户安装词库的命令。

;; `pyim-load-file' 加载词库简单来说就是：创建一个buffer，然后将词
;; 库文件的内容插入新创建的这个buffer，同时得到buffer和file的对应表。
;; 具体过程为：
;; 1. 首先创建一个 buffer，buffer 的名称源自 `pyim-buffer-name'，
;;    Chinese-pyim 默认创建的 buffer 名称类似：
;;    #+BEGIN_EXAMPLE
;;    -空格-*Chinese-pyim*
;;    -空格-*Chinese-pyim*-10000
;;    #+END_EXAMPLE
;;    这些buffer的名称前面都包含一个空格，所以在 emacs buffer列表中 *不可见* 。
;; 2. 将个人词频文件 `pyim-personal-file' 的内容插入到已经创建的 buffer。
;; 3. 使用类似上述方法，递归的为每个普通词库文件创建 buffer 并插入对应词
;;    库文件的内容，忽略不存在的文件和已经加载过的文件。
;; 4. 在运行的过程中，`pyim-load-file' 会创建一个词库文件名与 buffer 的对
;;    应表，其结构类似：
;;    #+BEGIN_EXAMPLE
;;    ((("buffer" . #<buffer  *Chinese-pyim*>) ("file" . "/path/to/pyim-personal.txt"))
;;     (("buffer" . #<buffer  *Chinese-pyim*-431862>) ("file" . "/path/to/pyim-bigdict.txt"))
;;     (("buffer" . #<buffer  *Chinese-pyim*-208698>) ("file" . "/path/to/chinese-pyim-prettydict-2.txt"))
;;     (("buffer" . #<buffer  *Chinese-pyim*-810662>) ("file" . "/path/to/chinese-pyim-prettydict-1.txt")))
;;    #+END_EXAMPLE
;; 5. 函数执行结束后，返回值为上述对应表。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-create-template-dict (file)
  "生成模版词库。"
  (condition-case error
      (unless (file-exists-p file)
        (with-temp-buffer
          (erase-buffer)
          (insert ";; -*- coding: utf-8 -*-\n")
          (make-directory (file-name-directory file) t)
          (write-file (expand-file-name file))
          (message "自动创建 Chinese-pyim 文件: %s" file)))
    (error
     (warn "`Chinese-pyim' 模版词库创建失败！" ))))

(defun pyim-show-help (string)
  "显示 Chinese-pyim 帮助信息，让用户快速的了解如何安装词库。"
  (let ((buffer-name "*Chinese-pyim-dict-help*"))
    (with-output-to-temp-buffer buffer-name
      (set-buffer buffer-name)
      (when (featurep 'org)
        (org-mode))
      (setq truncate-lines 1)
      (insert string)
      (goto-char (point-min)))))

;;;  read file functions
(defun pyim-load-file ()
  "为每一个词库文件创建一个buffer(这些buffer用户不可见)，然后将各个词库文件的内容插入
与之对应的buffer。最后返回一个包含所有buffer对象以及词库文件名的alist。

`pyim-personal-file' 文件最先导入。然后按照先后顺序导入 `pyim-dicts' 中定义的词库
排在最前面的词库首先被加载，相同的词库文件只加载一次。"
  (let ((personal-file (expand-file-name pyim-personal-file))
        (dicts-list pyim-dicts)
        (bufname pyim-buffer-name)
        buflist buf file coding disable dict-type)
    (save-excursion
      (unless (file-exists-p personal-file)
        ;; 如果 `pyim-personal-file' 对应的文件不存在，
        ;; 创建一个模版文件。
        (pyim-create-template-dict personal-file))
      (setq buf (pyim-read-file personal-file bufname))
      (setq buflist (append buflist (list buf)))
      (if dicts-list
          (dolist (dict dicts-list)
            (setq file (expand-file-name (plist-get dict :file)))
            (setq coding (plist-get dict :coding))
            (setq disable (plist-get dict :disable))
            (setq dict-type (plist-get dict :dict-type))
            (if (and (not disable)
                     (file-exists-p file)
                     (not (pyim-file-load-p file buflist)))
                (setq buflist (append buflist (list (pyim-read-file file bufname coding dict-type))))
              (message "忽略导入重复的词库文件：%s。" file)))
        ;; 当用户没有设置词库信息时，弹出帮助信息。
        (warn "Chinese-pyim 没有安装词库，请运行词库管理命令 `pyim-dicts-manager' 来安装词库。")))
    buflist))

(defun pyim-file-load-p (file buflist)
  "判断 file 是否已经加载"
  (cl-some (lambda (x)
             (rassoc file x))
           buflist))

(defun pyim-read-file (file name &optional coding dict-type)
  (with-current-buffer (generate-new-buffer name)
    (if coding
        (let ((coding-system-for-read coding))
          (insert-file-contents file))
      (insert-file-contents file))
    `(("buffer" . ,(current-buffer))
      ("file" . ,file)
      ("dict-type" . ,dict-type))))
;; #+END_SRC

;; 当使用 `pyim-start' 或者 `pyim-restart' 命令激活  Chinese-pyim 时，上述对应表保存到变量 `pyim-buffer-list'。
;; 供 Chinese-pyim 后续使用。

;; `pyim-buffer-list' 包含的第一个buffer，永远对应着个人词频文件，Chinese-pyim 使用 `pyim-save-personal-file'
;; 将 `pyim-buffer-list' 第一个 buffer 的内容保存到个人词频文件，这个命令用于更新个人词频文件。
;; <<save-personal-file>>

;; #+BEGIN_SRC emacs-lisp
(defun pyim-save-personal-file ()
  "与 `pyim-personal-file' 文件对应的buffer在 `Chinese-pyim' 使用期间不断更新。
这个函数将更新后的内容保存到`pyim-personal-file' 文件中，

这个函数默认作为`kill-emacs-hook'使用。"
  (interactive)
  (let* ((element (car pyim-buffer-list))
         (buffer (cdr (assoc "buffer" element)))
         (file (cdr (assoc "file" element))))
    (when (buffer-live-p buffer)
      (with-current-buffer buffer
        (save-restriction
          (if (file-exists-p file)
              (progn (write-region (point-min) (point-max) file)
                     (message "更新 Chinese-pyim 文件：%s。" file))
            (message "Chinese-pyim 文件：%s 不存在。" file)))))))

;; #+END_SRC

;; `pyim-check-buffers' 函数会检查 `pyim-buffer-list' 中的所有 buffer 是否存在，如果某个 buffer 不存在，
;; 这个函数会重新创建一个buffer，并插入对应词库文件的内容，如果对应词库文件也不存在，那么这个函数会删除这条记录。

;; 而 `pyim-kill-buffers' 会删除 `pyim-buffer-list' 中所有的 buffer。这个函数用于重新启动输入法前的清理工作。
;; <<pyim-kill-buffers>>

;; #+BEGIN_SRC emacs-lisp
(defun pyim-check-buffers ()
  "检查所有的 buffer 是否还存在，如果不存在，重新打开文件，如果文件不
存在，从 buffer-list 中删除这个 buffer"
  (let ((buflist pyim-buffer-list)
        (bufname pyim-buffer-name)
        buffer file)
    (dolist (buf buflist)
      (setq buffer (assoc "buffer" buf))
      (setq file (cdr (assoc "file" buf)))
      (unless (buffer-live-p (cdr buffer))
        (if (file-exists-p file)
            (with-current-buffer (generate-new-buffer bufname)
              (insert-file-contents file)
              (setcdr buffer (current-buffer)))
          (message "%s for %s is not exists!" file bufname)
          (setq buflist (remove buf buflist)))))
    t))

(defun pyim-kill-buffers ()
  "删除所有词库文件对应的 buffer ，用于重启 Chinese-pyim 。"
  (let ((buflist pyim-buffer-list)
        buffer)
    (dolist (buf buflist)
      (setq buffer (cdr (assoc "buffer" buf)))
      (when (buffer-live-p buffer)
        (kill-buffer buffer)))))
;; #+END_SRC

;; *** 从词库中搜索中文词条
;; 当个人词频文件以及普通词库文件加载完成后， Chinese-pyim 就可以搜索某个
;; 拼音字符串对应的中文词条了，这个工作由函数 `pyim-get' 完成，其基本原理
;; 是：递归的搜索 `pyim-buffer-list' 中所有的 buffer，将得到的搜索结果汇
;; 总成一个列表，去除重复元素后返回。

;; 在搜索 buffer 之前，Chinese-pyim 会使用函数 `pyim-dict-buffer-valid-p'
;; 大致的判断当前 buffer 是否是一个有效的词库 buffer，判断标准为：

;; 1. buffer 必须多于5行。
;; 2. buffer 中间一行必须包含空格或者TAB。
;; 2. buffer 中间一行必须包含中文字符(\\cc)。

;; 由于 chinese-pyim 文本词库没有包含 meta 信息，所以这个函数只能粗略的做
;; 出判断，另外这个函数使用 `count-lines' 计算行数，我限定其参数 END 不超
;; 过 20000, 这样可以优化性能，防止输入法卡顿。

;; BUG: 这个函数需要进一步优化，使其判断更准确。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-get (code &optional search-from-guessdict ignore-personal-buffer search-personal-buffer-only)
  (let ((persional-file-buffer (car pyim-buffer-list))
        (other-buffer-list (cdr pyim-buffer-list))
        (search-dicts-buffer-p t) ;用来决定是否需要搜索词库 buffer
        words nearby-codes-positions buffer-list)
    (when (and (stringp code) (string< "" code))
      (when (and pyim-buffer-cache-list
                 (not search-personal-buffer-only))
        ;; 直接从 buffer cache 中查询词条，速度很快。
        (dolist (buf-cache pyim-buffer-cache-list)
          (setq words
                (append words
                        (car (gethash code
                                      (cdr (assoc "buffer-cache" buf-cache)))))))

        ;; 如果用户将所有的个人词库都缓存了，即使找不到词条，
        ;; 也没有必要继续搜索词库 buffer 了。
        (when (eq (cdr (assoc "buffer-cache-mode"
                              (car pyim-buffer-cache-list))) 'full)
          (setq search-dicts-buffer-p nil))

        ;; 如果从缓存中找不到 code 对应的词条，则获取 code 所在的范围，
        ;; 比如： 如果搜索 ni-hao, 那么，搜索 n 和 o 两个 code 在 buffer
        ;; 中的位置，这两个 code 的位置可以减少后面搜索词库 buffer 花费的时间。
        (when search-dicts-buffer-p
          (dolist (buf-cache pyim-buffer-cache-list)
            (unless words
              (let* ((begin (string-to-char (substring code 0 1)))
                     (end (1+ begin))
                     (words-ht  (cdr (assoc "buffer-cache" buf-cache))))
                (push `(,(cdr (assoc "buffer" buf-cache))
                        ,(cadr (gethash (string begin) words-ht))
                        ,(cadr (gethash (string end) words-ht)))
                      nearby-codes-positions))))))

      ;; 直接用二分法搜索 *普通词库* buffer（速度比较慢）。
      (when (and (not words)
                 (not search-personal-buffer-only)
                 search-dicts-buffer-p)
        (dolist (buf other-buffer-list)
          (let ((dict-type (cdr (assoc "dict-type" buf))))
            ;; Search from dict
            (when (and (not search-from-guessdict)
                       (or (null dict-type)
                           (eq dict-type 'pinyin-dict)))
              (push buf buffer-list))
            ;; Search from guessdict
            (when (and search-from-guessdict
                       (eq dict-type 'guess-dict))
              (push buf buffer-list))))
        (setq buffer-list (reverse buffer-list))
        (dolist (buf buffer-list)
          (let* ((buffer (cdr (assoc "buffer" buf)))
                 (positions (cdr (assoc buffer nearby-codes-positions)))
                 (point1 (car positions)) ;从缓存中获取的上界限
                 (point2 (cadr positions))) ;从缓存中获取的下界限
            (with-current-buffer buffer
              (if (pyim-dict-buffer-valid-p)
                  (setq words (append words
                                      (cdr
                                       (pyim-bisearch-word code
                                                           (or point1 (point-min))
                                                           (or point2 (point-max))))))
                (message "%s 可能不是一个有效的词库 buffer，忽略。" (buffer-name)))))))

      (when (or search-personal-buffer-only
                (not (or search-from-guessdict
                         ignore-personal-buffer)))
        ;; 设置 `ignore-personal-buffer' 为 t 时，用于多音字校正。
        ;; pyim-buffer-list 中第一个 buffer 对应的是个人词库文件
        ;; 个人词库文件中的词条极有可能存在 *多音字污染*。
        ;; 不适合用于多音字校正，这是由 Chinese-pyim 保存词条的
        ;; 机制决定的。
        (with-current-buffer (cdr (assoc "buffer" persional-file-buffer))
          (if (pyim-dict-buffer-valid-p)
              (setq words (append (cdr
                                   (pyim-bisearch-word code
                                                       (point-min)
                                                       (point-max)))
                                  words))
            (message "个人词库文件 buffer 存在问题，忽略加载！"))))
      (delete-dups words))))

;; Shameless steal from company-dabbrev.el in `company' package
(defmacro pyim-get-dabbrev-time-limit-while (test start limit &rest body)
  (declare (indent 3) (debug t))
  `(let ((pyim-time-limit-while-counter 0))
     (catch 'done
       (while ,test
         ,@body
         (and ,limit
              (eq (cl-incf pyim-time-limit-while-counter) 25)
              (setq pyim-time-limit-while-counter 0)
              (> (float-time (time-since ,start)) ,limit)
              (throw 'done 'pyim-time-out))))))

;; Shameless steal from company-dabbrev.el in `company' package
(defun pyim-get-dabbrev-search-buffer (regexp pos symbols start
                                              limit ignore-comments)
  (save-excursion
    (cl-labels ((maybe-collect-match
                 ()
                 (let ((match (match-string-no-properties 0)))
                   (when (>= (length match) 2)
                     (push match symbols)))))
      (goto-char (if pos (1- pos) (point-min)))
      ;; Search before pos.
      (let ((tmp-end (point)))
        (pyim-get-dabbrev-time-limit-while
            (not (bobp)) start limit
          (ignore-errors
            (forward-char -10000))
          (forward-line 0)
          (save-excursion
            ;; Before, we used backward search, but it matches non-greedily, and
            ;; that forced us to use the "beginning/end of word" anchors in
            ;; search regexp.
            (while (re-search-forward regexp tmp-end t)
              (if (and ignore-comments (save-match-data (company-in-string-or-comment)))
                  (re-search-forward "\\s>\\|\\s!\\|\\s\"" tmp-end t)
                (maybe-collect-match))))
          (setq tmp-end (point))))
      (goto-char (or pos (point-min)))
      ;; Search after pos.
      (pyim-get-dabbrev-time-limit-while
          (re-search-forward regexp nil t) start limit
        (if (and ignore-comments (save-match-data (company-in-string-or-comment)))
            (re-search-forward "\\s>\\|\\s!\\|\\s\"" nil t)
          (maybe-collect-match)))
      symbols)))

;; Shameless steal from company-dabbrev.el in `company' package
(defun pyim-get-dabbrev (regexp &optional limit other-buffer-modes
                                ignore-comments)
  (when (and regexp
             (stringp regexp)
             (not (equal regexp "")))
    (let* ((start (current-time))
           (symbols (pyim-get-dabbrev-search-buffer
                     regexp (point) nil start limit ignore-comments)))
      (when other-buffer-modes
        (cl-dolist (buffer (delq (current-buffer) (buffer-list)))
          (with-current-buffer buffer
            (when (if (eq other-buffer-modes 'all)
                      (not (cl-some
                            #'(lambda (regexp)
                                (pyim-string-match-p regexp (buffer-name)))
                            pyim-dabbrev-ignore-buffers))
                    (apply #'derived-mode-p other-buffer-modes))
              (setq symbols
                    (pyim-get-dabbrev-search-buffer
                     regexp nil symbols start limit ignore-comments))))
          (and limit
               (> (float-time (time-since start)) limit)
               (cl-return))))
      symbols)))

(defun pyim-string-match-p (regexp string &optional start)
  (and (stringp regexp)
       (stringp string)
       (string-match-p regexp string start)))

(defun pyim-get-pinyin-similar-words (code &optional search-from-guessdict search-personal-buffer-only)
  "得到 `code' 对应的联想词。"
  (let ((regexp (pyim-build-pinyin-regexp code t t))
        buffer-list words-list predicted-words)
    (when (and (stringp code)
               (string< "" code)
               (pyim-string-match-p "[a-z]+-[a-z]+" code))
      (if search-personal-buffer-only
          (setq buffer-list (list (car pyim-buffer-list)))
        (dolist (buf pyim-buffer-list)
          (let ((dict-type (cdr (assoc "dict-type" buf))))
            (when (and (not search-from-guessdict)
                       (or (null dict-type)
                           (eq dict-type 'pinyin-dict)))
              (push buf buffer-list))
            (when (and search-from-guessdict
                       (eq dict-type 'guess-dict))
              (push buf buffer-list))))
        (setq buffer-list (reverse buffer-list)))
      (dolist (buf buffer-list)
        (with-current-buffer (cdr (assoc "buffer" buf))
          (when (pyim-dict-buffer-valid-p)
            (pyim-bisearch-word code (point-min) (point-max))
            (let* ((begin (when (re-search-forward regexp nil t)
                            (beginning-of-line)
                            (point)))
                   ;; 提取20行内容来获取分析联想词，太多的联想词
                   ;; 用处不大，还会使输入法响应速度减慢(经验数字)。
                   (end (progn (forward-line 20)
                               (end-of-line)
                               (point))))
              (when begin
                (setq words-list
                      (append words-list
                              (pyim-multiline-content begin end))))))))
      (dolist (line-words words-list)
        (when (pyim-string-match-p regexp (car line-words))
          (let ((line-words (cdr line-words)))
            (dolist (word line-words)
              (when (and (stringp word)
                         (> (length word) 0))
                (push word predicted-words))))))
      (delete-dups (reverse predicted-words)))))

(defun pyim-build-pinyin-regexp (code &optional match-beginning first-equal all-equal)
  "从`code' 构建一个 regexp，用于搜索联想词，
比如：ni-hao-si-j --> ^ni-hao[a-z]*-si[a-z]*-j[a-z]* , when `first-equal' set to `t'
                  --> ^ni[a-z]*-hao[a-z]*-si[a-z]*-j[a-z]* , when `first-equal' set to `nil'"
  (when (and code (stringp code))
    (let ((pylist (split-string code "-"))
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
               pylist "-")))))

(defun pyim-dict-buffer-valid-p ()
  "粗略地确定当前 buffer 是否是一个有效的词库产生的 buffer。
确定标准：

1. buffer 必须多于5行。
2. buffer 中间一行必须包含空格或者TAB。
2. buffer 中间一行必须包含中文字符(\\cc)。

BUG: 这个函数需要进一步优化，使其判断更准确。"
  (when (> (count-lines (point-min)
                        (min 20000 (point-max))) 5)
    (save-excursion
      (let ((mid (/ (+ (point-min) (point-max)) 2))
            ccode)
        (goto-char mid)
        (beginning-of-line)
        (and (re-search-forward "[ \t]" (line-end-position) t)
             (re-search-forward "\\cc" (line-end-position) t))))))
;; #+END_SRC

;; #+BEGIN_SRC emacs-lisp
(defun pyim-cache-dict-buffer ()
  "根据个人词库文件中的 codes，来构建普通词库文件的缓存，用于加快查询速度，
主要用于对访问速度要求高的中文字符串分词功能。"
  (interactive)
  (let ((cache-all-codes (yes-or-no-p "请选择缓存模式：[Yes] 缓存所有的词条; [No] 缓存常用的词条;  "))
        (max-word-length (read-number "缓存词条的最大长度为： ")))
    ;; 如果 Chinese-pyim 词库没有加载，加载 Chinese-pyim 词库，
    ;; 确保 pyim-get 可以正常运行。
    (unless pyim-buffer-list
      (setq pyim-buffer-list (pyim-load-file)))
    (message "正在缓存词库，请稍等。。。")
    (pyim-cache-dict-buffer-internal cache-all-codes max-word-length)
    (message "词库缓存完成！")))

(defun pyim-cache-dict-buffer-internal (&optional cache-all-codes max-word-length)
  "构建普通词库文件的缓存，用于加快查询速度，主要用于对访问速度要求高的中文字符串分词功能。
当 `cache-all-codes' 设置为 t 时，缓存普通词库 buffer 中存在的所有词条，如果设置为 nil， 仅仅
缓存常用的 codes 对应的词条，常用 codes 从个人文件中提取，具体请参考：`pyim-get-codes-in-personal-buffer'
`max-word-length' 用来设置缓存词条的最大长度。"
  (interactive)
  (let ((all-buffer-list pyim-buffer-list)
        (codes-used-freq (pyim-get-codes-in-personal-buffer))
        buffer-cache-mode result)
    ;; 清空原来的缓存。
    (setq pyim-buffer-cache-list nil)
    (dolist (buf all-buffer-list)
      ;; 这里仅仅 cache 普通词库 buffer，忽略 cache 个人词库文件 buffer 和
      ;; guessdict 词库 buffer。其主要原因是：
      ;; 1. 个人词库频繁变动，cache 很快会过期
      ;; 2. guessdict 词库的查询速度基本可以满足输入法的要求，
      ;;    不需要 cache。
      ;; 3. 当对中文字符串分词时，要求极其快速的查询个人词库,
      ;;    使用缓存可以极大的提高分词速度。
      (let ((dict-type (cdr (assoc "dict-type" buf)))
            (buffer (cdr (assoc "buffer" buf))))
        (when (or (null dict-type)
                  (eq dict-type 'pinyin-dict))
          (with-current-buffer buffer
            (goto-char (point-min))
            (let ((index-table (make-hash-table :size 50000 :test #'equal)))
              (when (pyim-dict-buffer-valid-p)
                (if cache-all-codes
                    (progn
                      (while (not (eobp))
                        (let* ((code (pyim-code-at-point))
                               (code-length (length (split-string code "-")))
                               (words (cdr (pyim-line-content))))
                          (when (<= code-length (or max-word-length 6))
                            (puthash code
                                     (list words)
                                     index-table)))
                        (forward-line 1))
                      (setq buffer-cache-mode 'full))
                  (dolist (code codes-used-freq)
                    (puthash code
                             (list (cdr (pyim-bisearch-word code
                                                            (point-min)
                                                            (point-max)))
                                   (point))
                             index-table))
                  (setq buffer-cache-mode 'partly))
                (push `(("buffer" . ,buffer)
                        ("buffer-cache" . ,index-table)
                        ("buffer-cache-mode" . ,buffer-cache-mode))
                      pyim-buffer-cache-list)))))))))

(defun pyim-get-codes-in-personal-buffer ()
  (let ((buffer (cdr (assoc "buffer" (car pyim-buffer-list))))
        result)
    (with-current-buffer buffer
      (goto-char (point-min))
      (while (not (eobp))
        (push (pyim-code-at-point) result)
        (forward-line 1)))
    ;; 加入26个字母code，用于缩小搜索范围。
    (setq result
          (append (mapcar
                   #'(lambda (x)
                       (string x))
                   "abcdefghjklmnopqrstwxyz")
                  result))
    (cl-delete-duplicates (nreverse result)
                          :test #'equal :from-end t)))
;; #+END_SRC

;; `pyim-buffer-list' 中每一个 buffer 都使用函数：`pyim-bisearch-word' 来
;; 搜索，其具体方式是：

;; 1. 获取 buffer 的 max-point 和 min-point
;; 2. 将光标移动到上述两个值的中间。
;; 3. 使用 `pyim-code-at-point' 获取当前行的拼音字符串。
;; 4. 比较上述拼音字符串和待搜索的字符串，来决定搜索 buffer 的上半部份还
;;    是下半部份。
;; 5. 这样递归的操作，最终会将光标移动到 buffer 的某一行，这一行中的拼音
;;    字符串和待搜索的拼音字符串一致。
;; 6. 最后使用 `pyim-line-content' 返回当前行的内容，其结果是一个列表，类
;;    似：
;;    #+BEGIN_EXAMPLE
;;    ("ni-hao" "你好" "你号" ...)
;;    #+END_EXAMPLE

;; #+BEGIN_SRC emacs-lisp
(defun pyim-bisearch-word (code start end)
  (let ((mid (/ (+ start end) 2))
        ccode)
    (goto-char mid)
    (beginning-of-line)
    (setq ccode (pyim-code-at-point))
    ;;    (message "%d, %d, %d: %s" start mid end ccode)
    (if (equal ccode code)
        (pyim-line-content)
      (if (> mid start)
          (if (string< ccode code)
              (pyim-bisearch-word code mid end)
            (pyim-bisearch-word code start mid))))))

(defun pyim-code-at-point ()
  "Before calling this function, be sure that the point is at the
beginning of line"
  (save-excursion
    (if (re-search-forward "[ \t]" (line-end-position) t)
        (buffer-substring-no-properties (line-beginning-position) (1- (point)))
      (error "文件类型错误！%s 的第 %d 行没有词条！" (buffer-name) (line-number-at-pos)))))

(defun pyim-line-content (&optional seperaters omit-nulls)
  "用 SEPERATERS 分解当前行，所有参数传递给 split-string 函数"
  (let* ((begin (line-beginning-position))
         (end (line-end-position))
         (end (if (> (- end begin) pyim-line-content-limit)
                  (+ begin pyim-line-content-limit)
                end))
         (items (split-string
                 (buffer-substring-no-properties begin end)
                 seperaters)))
    (if omit-nulls
        (cl-delete-if 'pyim-string-emptyp items)
      items)))

(defun pyim-multiline-content (begin end &optional seperaters omit-nulls)
  "将当前 buffer 中，`begin' 到 `end' 之间的内容分解，生成一个 list，
这个函数用于搜索联想词函数 `pyim-get-pinyin-similar-words' 。"
  ;;  ni-hao 你好 倪浩         (("ni-hao" "你好" "倪浩")
  ;;  ni-hao-a 你好啊    -->    ("ni-hao-a" "你好啊")
  ;;  ni-hao-b 你好吧           ("ni-hao-ba" "你好吧"))
  (let ((items (split-string
                (buffer-substring-no-properties
                 (if (> begin (point-min))
                     begin
                   (point-min))
                 (if (< end (point-max))
                     end
                   (point-max))) "\n")))
    (mapcar
     #'(lambda (x)
         (let ((line-items (split-string x (or seperaters " "))))
           (if omit-nulls
               (cl-delete-if 'pyim-string-emptyp line-items)
             line-items)))
     items)))

(defun pyim-string-emptyp (str)
  (not (string< "" str)))
;; #+END_SRC

;; `pyim-bisearch-word' 是 Chinese-pyim 搜索词条的最基本最核心的函数，只
;; 要涉及到搜索词条，必须调用这个函数。

;; *** 保存词条，删除词条以及调整词条位置
;; Chinese-pyim 不会更改普通词库文件的内容，只会将运行过程中的词频信息保存到个人词频文件，这个过程
;; 分为两步：
;; 1. 调整个人词频文件对应的 buffer 的内容，这个过程的核心函数是 `pyim-intern-word'。
;; 2. 将 buffer 的内容保存到个人词频文件，这个使用函数 `pyim-save-personal-file' 完成。

;; `pyim-intern-word' 的工作原理和 `pyim-get' 类似， 只不过
;; `pyim-intern-word' 只搜索个人词频文件对应的 buffer ，搜索到结果后做如
;; 下工作：

;; 1. 获取当前行的信息，并其格式为一个list
;; 2. 将参数 `word' 对应的词条和上述list合并
;;    1. 向前追加（用于词频调整功能）
;;    2. 向后追加（用于造词功能）
;;    3. 从list中删除word （用于删词功能）
;; 3. 使用 `pyim-delete-line' 删除当前行
;; 4. 将合并后的list转换为词库格式后，再写入当前行。

;; 围绕着 `pyim-intern-word'，Chinese-pyim 构建了3类命令：
;; 1. 将一个中文词条加入个人词频文件（造词功能）
;; 2. 将一个中文词条从个人词频文件中删除（删词功能）
;; 3. 调整一个中文词条选项的位置（词频调整功能）

;; **** 造词功能和词频调整功能
;; 1. `pyim-create-or-rearrange-word' 当用户选择了一个词库中不存在的中文词条时，
;;    `pyim-select-current' 会调用这个函数来自动造词。其工作流程是：
;;     1. 使用 `chinese-hanzi2pinyin' 获取中文词条的拼音。
;;     2. 然后调用 `pyim-intern-word' 保存词条，多音字重复操作，比如：

;;        #+BEGIN_EXAMPLE
;;        yin-hang 银行
;;        yin-xing 银行
;;        #+END_EXAMPLE

;;     另外，这个函数也用于 *词频调整*  。

;;     BUG：这种处理方式最大的问题是 *无法正确处理* 多音字，从而导致
;;     chinese-pyim 个人文件 *不纯洁*  :-)，但不影响使用。Emacs-eim
;;     使用的方式不存在这种问题，但其增加了代码的复杂度，并且灵活性太差
;;     增加高级功能，比如 “词语联想”，时存在问题。

;; 2. `pyim-create-word-at-point' 这个命令会提取光标前 `number' 个中文字
;;     符，将其组成字符串后，调用 `pyim-create-word' 将其加入个人词频文件。
;; 3. `pyim-create-word-at-point:<NUM>char' 这组命令是
;;    `pyim-create-word-at-point' 的包装命令。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-delete-line ()
  (delete-region (line-beginning-position) (min (+ (line-end-position) 1)
                                                (point-max))))

(defun pyim-intern-word (word py &optional append delete)
  "这个函数用于保存用户词频，将参数拼音 `py' 对应的中文词条 `word'
保存到 personal-file 对应的 buffer。

当 `append' 设置为 t 时，新词追加到已有词的后面。

当`delete' 设置为 t 时，从上述 buffer 中删除参数拼音 `py' 对应
的中文词条 `word'。"
  (let((buf (cdr (assoc "buffer" (car pyim-buffer-list))))
       words)
    (with-current-buffer buf
      (pyim-bisearch-word py (point-min) (point-max))
      (if (equal (pyim-code-at-point) py)
          (progn
            (setq words (pyim-line-content))
            (if delete
                (setq words (remove word words))
              (setq words
                    (cons (car words)
                          (delete-dups
                           (if append
                               (append (cdr words) (list word))
                             (append (list word) (cdr words)))))))
            ;; (message "delete: %s" words))
            (pyim-delete-line))
        (forward-line 1)
        (setq words (list py word)))
      ;;    (message "insert: %s" words)
      (when (> (length words) 1)
        (insert (mapconcat 'identity words " ") "\n")))))

(defun pyim-create-or-rearrange-word (word &optional rearrange-word)
  "将中文词条 `word' 添加拼音后，保存到 personal-file 对应的
buffer中，当前词条追加到已有词条之后。`pyim-create-or-rearrange-word'会调用
`pyim-hanzi2pinyin' 来获取中文词条的拼音code。

BUG：无法有效的处理多音字。"
  (let ((pinyins (pyim-hanzi2pinyin word nil "-" t nil t))) ;使用了多音字校正
    (mapc #'(lambda (py)
              (unless (pyim-string-match-p "[^ a-z-]" py)
                ;; 添加词库： ”拼音“ - ”中文词条“
                (pyim-intern-word word py (not rearrange-word))
                ;; 添加词库： ”拼音首字母“ - ”中文词条“
                (pyim-intern-word word
                                  (mapconcat
                                   #'(lambda (x)
                                       (substring x 0 1))
                                   (split-string py "-")
                                   "-")
                                  (not rearrange-word))))
          pinyins)))

(defun pyim-chinese-string-at-point (&optional number)
  "获取光标一个中文字符串，字符数量为：`number'"
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
  "将光标前字符数为 `number' 的中文字符串添加到个人词库中
当 `silent' 设置为 t 是，不显示提醒信息。"
  (let* ((string (pyim-chinese-string-at-point (or number 2))))
    (when string
      (pyim-create-or-rearrange-word string)
      (unless silent
        (message "将词条: \"%s\" 插入 personal file。" string)))))

(defun pyim-create-word-at-point:2char ()
  "将光标前2个中文字符组成的字符串加入个人词库。"
  (interactive)
  (pyim-create-word-at-point 2))

(defun pyim-create-word-at-point:3char ()
  "将光标前3个中文字符组成的字符串加入个人词库。"
  (interactive)
  (pyim-create-word-at-point 3))

(defun pyim-create-word-at-point:4char ()
  "将光标前4个中文字符组成的字符串加入个人词库。"
  (interactive)
  (pyim-create-word-at-point 4))
;; #+END_SRC

;; **** 删词功能
;; `pyim-delete-word-from-personal-buffer' 从个人词频 buffer 中删除用户高
;; 亮选择的词条。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-delete-word (word)
  "将中文词条 `word' 从 personal-file 对应的 buffer 中删除"
  (mapc (lambda (py)
          (unless (pyim-string-match-p "[^ a-z-]" py)
            (pyim-intern-word word py nil t)))
        (pyim-hanzi2pinyin word nil "-" t)))

(defun pyim-delete-word-from-personal-buffer ()
  "将高亮选择的字符从 personel-file 对应的 buffer 中删除。"
  (interactive)
  (if mark-active
      (let ((string (buffer-substring-no-properties
                     (region-beginning) (region-end))))
        (when (and (< (length string) 6)
                   (> (length string) 0))
          (pyim-delete-word string)
          (message "将词条: \"%s\" 从 personal file中删除。" string)))
    (message "请首先高亮选择需要删除的词条。")))
;; #+END_SRC

;; ** 生成 `pyim-current-key' 并插入 `pyim-current-str'
;; *** 生成拼音字符串 `pyim-current-key'
;; Chinese-pyim 使用函数 `pyim-start' 启动输入法的时候，会将变量
;; `input-method-function' 设置为 `pyim-input-method' ，这个变量
;; 会影响 `read-event' 的行为。

;; 当输入字符时，`read-event' 会被调用，`read-event' 调用的过程中，
;; 会执行 `pyim-input-method' 这个函数。`pyim-input-method' 又调用函数
;; `pyim-start-translation'

;; `pyim-start-translation' 这个函数较复杂，作许多低层工作，但它的一个重
;; 要流程是：
;; 1. 使用函数 `read-key-sequence' 得到 key-sequence
;; 2. 使用函数 `lookup-key' 查询 pyim-mode-map 中，上述 key-sequence 对应
;;    的命令。
;; 3. 如果查询得到的命令是 'pyim-self-insert-command' 时，
;;    `pyim-start-translation' 会调用这个函数。

;; `pyim-self-insert-command' 这个函数的核心工作就是将用户输入的字符，组
;; 合成拼音字符串并保存到变量 `pyim-current-key' 中。

;; 中英文输入模式切换功能也是在 'pyim-self-insert-command' 中实现。

;; 这个部份的代码涉及许多 emacs 低层函数，相对复杂，不容易理解，有兴趣的
;; 朋友可以参考：
;; 1. `quail-input-method' 相关函数。
;; 2. elisp 手册相关章节:
;;    1. Invoking the Input Method
;;    2. Input Methods
;;    3. Miscellaneous Event Input Features
;;    4. Reading One Event

;; *** 在待输入 buffer 中插入 `pyim-current-str'
;; `pyim-self-insert-command' 会调用 `pyim-handle-string' 来处理
;; `pyim-current-key'，得到对应的 `pyim-current-str'，然后，
;; `pyim-start-translation' 返回 `pyim-current-str' 的取值。

;; 在 `pyim-input-method' 函数内部，`pyim-start-translation' 返回值分解为
;; event list。

;; 最后，emacs 低层函数 read-event 将这个 list 插入 *待输入buffer* 。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-input-method (key)
  (if (or buffer-read-only
          overriding-terminal-local-map
          overriding-local-map)
      (list key)
    ;; (message "call with key: %c" key)
    (pyim-setup-overlays)
    (with-silent-modifications
      (unwind-protect
          (let ((input-string (pyim-start-translation key)))
            ;; (message "input-string: %s" input-string)
            (setq pyim-guidance-str "")
            (when (and (stringp input-string)
                       (> (length input-string) 0))
              (if input-method-exit-on-first-char
                  (list (aref input-string 0))
                (mapcar 'identity input-string))))
        (pyim-delete-overlays)))))

(defun pyim-start-translation (key)
  "Start translation of the typed character KEY by Chinese-pyim.
Return the input string."
  ;; Check the possibility of translating KEY.
  ;; If KEY is nil, we can anyway start translation.
  (if (or (integerp key) (null key))
      ;; OK, we can start translation.
      (let* ((echo-keystrokes 0)
             (help-char nil)
             (overriding-terminal-local-map pyim-mode-map)
             (generated-events nil)
             (input-method-function nil)
             (modified-p (buffer-modified-p))
             last-command-event last-command this-command)
        (setq pyim-current-str ""
              pyim-current-key ""
              pyim-translating t)
        (if key
            (setq unread-command-events
                  (cons key unread-command-events)))
        (while pyim-translating
          (set-buffer-modified-p modified-p)
          (let* ((prompt (if input-method-use-echo-area
                             (format "%s%s %s"
                                     (or input-method-previous-message "")
                                     pyim-current-key
                                     pyim-guidance-str)))
                 (keyseq (read-key-sequence prompt nil nil t))
                 (cmd (lookup-key pyim-mode-map keyseq)))
            ;;             (message "key: %s, cmd:%s\nlcmd: %s, lcmdv: %s, tcmd: %s"
            ;;                      key cmd last-command last-command-event this-command)
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
                    (error (message "Chinese-pyim 出现错误: %s , 开启 debug-on-error 后可以了解详细情况。"
                                    (cdr err)) (beep))))
              ;; KEYSEQ is not defined in the translation keymap.
              ;; Let's return the event(s) to the caller.
              (setq unread-command-events
                    (string-to-list (this-single-command-raw-keys)))
              ;; (message "unread-command-events: %s" unread-command-events)
              (pyim-terminate-translation))))
        ;;    (1message "return: %s" pyim-current-str)
        pyim-current-str)
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
  "确定 Chinese-pyim 是否启动中文输入模式"
  (let* ((pinyin-scheme-name pyim-default-pinyin-scheme)
         (first-chars (pyim-get-pinyin-scheme-option pinyin-scheme-name :first-chars))
         (rest-chars (pyim-get-pinyin-scheme-option pinyin-scheme-name :rest-chars)))
    (and (not pyim-input-ascii)
         (not (pyim-auto-switch-english-input-p))
         (if (pyim-string-emptyp pyim-current-key)
             (member last-command-event
                     (mapcar 'identity first-chars))
           (member last-command-event
                   (mapcar 'identity rest-chars)))
         (setq current-input-method-title pyim-title))))

(defun pyim-self-insert-command ()
  "如果在 pyim-first-char 列表中，则查找相应的词条，否则停止转换，插入对应的字符"
  (interactive "*")
  ;; (message "%s" (current-buffer))
  (if (pyim-input-chinese-p)
      (progn (setq pyim-current-key
                   (concat pyim-current-key (char-to-string last-command-event)))
             (pyim-handle-string))
    (pyim-append-string (pyim-translate last-command-event))
    (pyim-terminate-translation)))

(defun pyim-terminate-translation ()
  "Terminate the translation of the current key."
  (setq pyim-translating nil)
  (pyim-delete-region)
  (setq pyim-current-choices nil)
  (setq pyim-guidance-str ""))
;; #+END_SRC

;; ** 处理拼音字符串 `pyim-current-key'
;; *** 拼音字符串 -> 待选词列表
;; 从一个拼音字符串获取其待选词列表，大致可以分成3个步骤：
;; 1. 分解这个拼音字符串，得到一个拼音列表。
;;    #+BEGIN_EXAMPLE
;;    woaimeinv -> (("w" . "o") ("" . "ai") ("m" . "ei") ("n" . "v"))
;;    #+END_EXAMPLE
;; 2. 将拼音列表排列组合，得到多个词语的拼音，并用列表表示。
;;    #+BEGIN_EXAMPLE
;;    (("p" . "in") ("y" . "in") ("sh" . "") ("r" . ""))
;;    => ("pin-yin"  ;; 完整的拼音
;;        ("p-y-sh" ("p" . "in") ("y" . "in") ("sh" . "")) ;; 不完整的拼音
;;        ("p-y-sh-r" ("p" . "in") ("y" . "in") ("sh" . "") ("r" . "")) ;; 不完整的拼音
;;        )
;;    #+END_EXAMPLE
;; 3. 递归的查询上述多个词语拼音，将得到的结果合并为待选词列表。
;; **** 分解拼音字符串
;; 拼音字符串操作主要做两方面的工作：
;; 1. 将拼音字符串分解为拼音列表。
;; 2. 将拼音列表合并成拼音字符串。

;; 在这之前，Chinese-pyim 定义了三个变量：
;; 1. 声母表： `pyim-shen-mu'
;; 2. 韵母表：`pyim-yun-mu'
;; 3. 有效韵母表： `pyim-valid-yun-mu'

;; Chinese-pyim 使用函数 `pyim-split-string' 将拼音字符串分解为一个由声母和韵母组成的拼音列表，比如：

;; #+BEGIN_EXAMPLE
;; (pyim-split-string "woaimeinv" 'default)
;; #+END_EXAMPLE

;; 结果为:
;; : ((("w" . "o") ("" . "ai") ("m" . "ei") ("n" . "v")))

;; 这个过程通过递归的调用 `pyim-get-charpy' 来实现，整个过程类似用菜刀切黄瓜片，将一个拼音字符串逐渐切开。比如：

;; #+BEGIN_EXAMPLE
;; (pyim-get-charpy "woaimeinv")
;; #+END_EXAMPLE

;; 结果为:
;; : (("w" . "o") . "aimeinv")

;; 一个完整的递归过程类似：
;; #+BEGIN_EXAMPLE
;; "woaimeinv"
;; (("w" . "o") . "aimeinv")
;; (("w" . "o") ("" . "ai") . "meinv")
;; (("w" . "o") ("" . "ai") ("m" . "ei" ) . "nv")
;; (("w" . "o") ("" . "ai") ("m" . "ei" ) ("n" . "v"))
;; #+END_EXAMPLE

;; `pyim-get-charpy' 由两个基本函数配合实现：
;; 1. pyim-get-sm 从一个拼音字符串中提出第一个声母
;; 2. pyim-get-ym 从一个拼音字符串中提出第一个韵母

;; #+BEGIN_EXAMPLE
;; (pyim-get-sm "woaimeinv")
;; #+END_EXAMPLE

;; 结果为:
;; : ("w" . "oaimeinv")

;; #+BEGIN_EXAMPLE
;; (pyim-get-ym "oaimeinv")
;; #+END_EXAMPLE

;; 结果为:
;; : ("o" . "aimeinv")

;; 当用户输入一个错误的拼音时，`pyim-split-string' 会产生一个声母为空而韵母又不正确的拼音列表 ，比如：

;; #+BEGIN_EXAMPLE
;; (pyim-split-string "ua" 'default)
;; #+END_EXAMPLE

;; 结果为:
;; : ((("" . "ua")))

;; 这种错误可以使用函数 `pyim-validp' 来检测。
;; #+BEGIN_EXAMPLE
;; (list (pyim-validp (car (pyim-split-string "ua" 'default)))
;;       (pyim-validp (car (pyim-split-string "a" 'default)))
;;       (pyim-validp (car (pyim-split-string "wa" 'default)))
;;       (pyim-validp (car (pyim-split-string "wua" 'default))))
;; #+END_EXAMPLE

;; 结果为:
;; : (nil t t t)

;; Chinese-pyim 使用函数 `pyim-pylist-to-string' 将一个拼音列表合并为拼音
;; 字符串，这个可以认为是 `pyim-split-string' 的反向操作。构建得到的拼音
;; 字符串用于搜索词条。

;; #+BEGIN_EXAMPLE
;; (pyim-pylist-to-string '(("w" . "o") ("" . "ai") ("m" . "ei") ("n" . "v")) nil 'default)
;; #+END_EXAMPLE

;; 结果为:
;; : "wo-ai-mei-nv"

;; 最后： `pyim-user-divide-pos' 和 `pyim-restore-user-divide' 用来处理隔
;; 音符，比如： xi'an

;; #+BEGIN_SRC emacs-lisp
;; 将汉字的拼音分成声母和其它
(defun pyim-get-sm (py)
  "从一个拼音字符串中提出第一个声母。"
  (when (and py (string< "" py))
    (let (shenmu yunmu len)
      (if (< (length py) 2)
          (if (member py pyim-shen-mu)
              (cons py "")
            (cons "" py))
        (setq shenmu (substring py 0 2))
        (if (member shenmu pyim-shen-mu)
            (setq py (substring py 2))
          (setq shenmu (substring py 0 1))
          (if (member shenmu pyim-shen-mu)
              (setq py (substring py 1))
            (setq shenmu "")))
        (cons shenmu py)))))

(defun pyim-get-ym (py)
  "从一个拼音字符串中提出第一个韵母"
  (when (and py (string< "" py))
    (let (yunmu len)
      (setq len (min (length py) 5))
      (setq yunmu (substring py 0 len))
      (while (and (not (member yunmu pyim-yun-mu))
                  (> len 0))
        (setq yunmu (substring py 0 (setq len (1- len)))))
      (setq py (substring py len))
      (if (and (string< "" py)
               (not (member (substring py 0 1) pyim-shen-mu))
               (member (substring yunmu -1) pyim-shen-mu)
               (member (substring yunmu 0 -1) pyim-yun-mu))
          (setq py (concat (substring yunmu -1) py)
                yunmu (substring yunmu 0 -1)))
      (cons yunmu py))))

(defun pyim-get-charpy (py)
  "分解一个拼音字符串成声母和韵母。"
  (when (and py (string< "" py))
    (let* ((sm (pyim-get-sm py))
           (ym (pyim-get-ym (cdr sm)))
           (chpy (concat (car sm) (car ym))))
      (if (or (null ym)                 ; 如果韵母为空
              (and (string< "" (car ym)) (not (pyim-get chpy)))) ; 错误的拼音
          (cons sm "")
        (cons (cons (car sm) (car ym)) (cdr ym))))))

;;; 处理输入的拼音
(defun pyim-get-pinyin-scheme (pinyin-scheme-name)
  "获取名称为 `pinyin-scheme-name' 的拼音方案。"
  (assoc pinyin-scheme-name pyim-pinyin-schemes))

(defun pyim-get-pinyin-scheme-option (pinyin-scheme-name option)
  "获取名称为 `pinyin-scheme-name' 的拼音方案，并提取其属性 `option' 。"
  (let ((pinyin-scheme (pyim-get-pinyin-scheme pinyin-scheme-name)))
    (when pinyin-scheme
      (plist-get (cdr pinyin-scheme) option))))

(defun pyim-split-string (str &optional pinyin-scheme-name)
  "按照 `pinyin-scheme-name' 对应的拼音方案，把一个全拼或者双拼字符串分解为 *一个或者多个* pylist,
返回所有 pylist 的组成的一个 *列表* 。

注：1, 每一个 pylist 都有类似的结构: ((\"n\" . \"i\")(\"h\" . \"ao\"))
    2. 使用这么复杂的list的原因是为了支持双拼，因为一个双拼字符串有可能转换为多个有效的全拼。
    3. 变量 `pyim-pinyin-schemes' 保存所有可用的 pinyin-scheme 。"
  (let ((pinyin-class (pyim-get-pinyin-scheme-option pinyin-scheme-name :class)))
    (when pinyin-class
      (funcall (intern (concat "pyim-split-string:"
                               (symbol-name pinyin-class)))
               str pinyin-scheme-name))))

(defun pyim-split-string:quanpin (py &optional pinyin-scheme-name)
  "把一个拼音字符串分解。如果含有 '，优先在这个位置中断，否则，自动分
解成声母和韵母的组合，可选参数 `pinyin-scheme' 只是一个虚参数，暂时没有
用处。"
  (when (and py (string< "" py))
    (list (apply 'append
                 (mapcar (lambda (p)
                           (let (chpy pylist)
                             (setq p (replace-regexp-in-string "[ -]" "" p))
                             (while (when (string< "" p)
                                      (setq chpy (pyim-get-charpy p))
                                      (setq pylist (append pylist (list (car chpy))))
                                      (setq p (cdr chpy))))
                             pylist))
                         (split-string py "'"))))))

;; "nihc" -> (((\"n\" . \"i\") (\"h\" . \"ao\")))
(defun pyim-split-string:shuangpin (str &optional pinyin-scheme-name)
  "按照 `pyim-scheme-name' 对应的拼音方案，把一个双拼字符串分解成一个 pylist 组成的列表。"
  (let ((keymaps-general (pyim-get-pinyin-scheme-option pinyin-scheme-name :keymaps-general))
        (keymaps-special (pyim-get-pinyin-scheme-option pinyin-scheme-name :keymaps-special))
        (list (string-to-list
               (replace-regexp-in-string "-" ""str)))
        results)
    (while list
      (let* ((sp-sm (pop list))
             (sp-ym (pop list))
             (sp-sm (when sp-sm (char-to-string sp-sm)))
             (sp-ym (when sp-ym (char-to-string sp-ym)))
             (sm (nth 1 (assoc sp-sm keymaps-general)))
             (ym (cdr (cdr (assoc sp-ym keymaps-general)))))
        (push (mapcar
               #'(lambda (x)
                   (let* ((y (cons sp-sm sp-ym))
                          (z (car (cdr (assoc y keymaps-special)))))
                     (or z (cons sm x))))
               (or ym (list ""))) results)))
    (pyim-permutate-list (nreverse results))))

(defun pyim-validp (pylist)
  "检查得到的拼音是否含有声母为空，而韵母又不正确的拼音"
  (let ((valid t) py)
    (while (progn
             (setq py (car pylist))
             (if (and (not (string< "" (car py)))
                      (not (member (cdr py) pyim-valid-yun-mu)))
                 (setq valid nil)
               (setq pylist (cdr pylist)))))
    valid))

(defun pyim-user-divide-pos (py)
  "检测出用户分割的位置"
  (setq py (replace-regexp-in-string "-" "" py))
  (let (poslist (start 0))
    (while (string-match "'" py start)
      (setq start (match-end 0))
      (setq poslist (append poslist (list (match-beginning 0)))))
    poslist))

(defun pyim-restore-user-divide (py pos)
  "按检测出的用户分解的位置，重新设置拼音"
  (let ((i 0) (shift 0) cur)
    (setq cur (car pos)
          pos (cdr pos))
    (while (and cur (< i (length py)))
      (if (= (aref py i) ?-)
          (if (= i (+ cur shift))
              (progn
                (aset py i ?')
                (setq cur (car pos)
                      pos (cdr pos)))
            (setq shift (1+ shift))))
      (setq i (1+ i)))
    (if cur (setq py (concat py "'")))  ; the last char is `''
    py))

(defun pyim-pylist-to-string (pylist &optional shou-zi-mu pinyin-scheme-name)
  "按照 `pinyin-scheme' 对应的拼音方案，把一个拼音列表合并为一个全拼字符串
或者双拼字符串，常常用于搜索。"
  (let ((pinyin-class (pyim-get-pinyin-scheme-option pinyin-scheme-name :class)))
    (when pinyin-class
      (funcall (intern (concat "pyim-pylist-to-string:"
                               (symbol-name pinyin-class)))
               pylist shou-zi-mu pinyin-scheme-name))))

(defun pyim-pylist-to-string:quanpin (pylist &optional shou-zi-mu pinyin-scheme-name)
  "把一个拼音列表合并为一个全拼字符串，当 `shou-zi-mu' 设置为 t
时，生成拼音首字母字符串，比如 p-y。"
  (mapconcat 'identity
             (mapcar
              #'(lambda (w)
                  (let ((py (concat (car w) (cdr w))))
                    (if shou-zi-mu
                        (substring py 0 1)
                      py)))
              pylist)
             "-"))

(defun pyim-pylist-to-string:shuangpin (pylist &optional shou-zi-mu pinyin-scheme-name)
  "把一个拼音列表合并为一个双拼字符串，当 `shou-zi-mu' 设置为 t 时，
生成双拼首字母字符串，比如 p-y。"
  (when pinyin-scheme-name
    (let* ((keymaps-general (pyim-get-pinyin-scheme-option pinyin-scheme-name :keymaps-general))
           (keymaps-special (pyim-get-pinyin-scheme-option pinyin-scheme-name :keymaps-special)))
      (mapconcat 'identity
                 (mapcar
                  #'(lambda (w)
                      (let ((special
                             (car (rassoc (list w)
                                          keymaps-special)))
                            (sm (car w))
                            (ym (cdr w)))
                        (if special
                            (concat (car special) (cdr special))
                          (concat (cl-some
                                   #'(lambda (x)
                                       (when (equal sm (nth 1 x))
                                         (car x))) keymaps-general)
                                  (unless shou-zi-mu
                                    (cl-some
                                     #'(lambda (x)
                                         (when (or (equal ym (nth 2 x))
                                                   (equal ym (nth 3 x)))
                                           (car x))) keymaps-general))))))
                  pylist)
                 "-"))))
;; #+END_SRC

;; **** 获得词语拼音并进一步查询得到备选词列表
;; #+BEGIN_SRC emacs-lisp
(defun pyim-get-choices (list-of-pylist)
  "得到可能的词组和汉字。"
  ;; 全拼输入模式下，list-of-pylist 一般只包含一个 pylist, 所以没有 *子候选词列表* 合并问题，
  ;; 但在双拼输入模式下，由于一个双拼字符串可能分解为多个有效的全拼，所以 list-of-pylist
  ;; 可能包含多个 pylist, 从而得到多个子候选词列表，如何将多个 *子候选词列表* 合理的合并，
  ;; 是一个麻烦的事情。

  ;; 当前的合并模式是：将子候选词列表按照 length 排序，length 最大的放到最前面，然后将所有的
  ;; 子列表连接起来形成最终得候选词列表。

  ;; 注：这个地方需要进一步得改进。
  (let ((candidates-list
         (sort (mapcar
                #'pyim-get-choices-internal
                list-of-pylist)
               #'(lambda (x y)
                   (> (length x) (length y)))))
        results)
    (dolist (candidate candidates-list)
      (setq results (append results candidate)))
    results))

(defun pyim-get-choices-internal (pylist)
  "得到可能的词组和汉字。例如：

 (pyim-get-choices-internal  (car (pyim-split-string \"pin-yin\" 'default)))
  => (\"拼音\" \"拼\" \"品\" \"贫\" \"苹\" \"聘\" \"频\" \"拚\" \"颦\" \"牝\" \"嫔\" \"姘\" \"嚬\")

 (pyim-get-choices-internal  (car (pyim-split-string \"pin-yin\" 'default)))
 => (\"拼音\" \"贫铀\" \"聘用\" \"拼\" \"品\" \"贫\" \"苹\" \"聘\" \"频\" \"拚\" \"颦\" \"牝\" \"嫔\" \"姘\" \"嚬\")"
  (let ((py-str (pyim-pylist-to-string pylist nil 'default))
        (py-str-shouzimu (pyim-pylist-to-string pylist t 'default))
        (length-pylist (length pylist))
        choice words word
        guess-words-accurate guess-words-similar
        dabbrev-words-accurate-1 dabbrev-words-similar-1
        dabbrev-words-accurate-2 dabbrev-words-similar-2
        words-predicted chars wordspy)

    ;; 搜索严格匹配输入拼音的词条。
    (setq words (pyim-get py-str))

    ;; 如果输入 "ni-hao" ，搜索拼音与 "ni-hao" 类似的词条作为联想词。
    ;; 搜索相似词得到的联想词太多，这里限制只搜索个人文件。
    (when (member 'pinyin-similar pyim-enable-words-predict)
      (push `(pinyin-similar ,@(pyim-get-pinyin-similar-words py-str nil t)) words-predicted))

    ;; 如果输入 "ni-hao" ，搜索 code 为 "n-h" 的词条做为联想词。
    ;; 搜索首字母得到的联想词太多，这里限制联想词要大于三个汉字并且只搜索
    ;; 个人文件。
    (when (and (member 'pinyin-shouzimu pyim-enable-words-predict)
               (> length-pylist 2))
      (push `(pinyin-shouzimu ,@(pyim-get py-str-shouzimu nil nil t)) words-predicted))

    ;; 如果上一次输入词条 "你好" ，那么以 “你好” 为 code，从 guessdict 词库中搜索词条
    ;; 将搜索得到的词条的拼音与 *当前输入的拼音* 进行比较，类似或者精确匹配的词条作为联想词。
    (when (member 'guess-words pyim-enable-words-predict)
      (let* ((prefix (pyim-grab-chinese-word
                      (length pyim-current-str) pyim-last-input-word))
             (length-prefix (length prefix))
             (words (pyim-get prefix t))
             (count 0))
        ;; 光标前获取的 prefix 字符串长度大于1并且小于5时，
        ;; 才进行 guess-words 词语联想，prefix 长度太小时，搜索
        ;; 得到的词条太多，处理起来容易卡顿，prefix 长度太大时，
        ;; 词库中大多数没有，搜索是浪费时间。
        (when (and (> length-prefix 1)
                   (< length-prefix 5))
          (while words
            (setq word (pop words))
            ;; 下面功能使用函数 `pyim-match-chinese-with-pylist' 实现比较直接，
            ;; `pyim-match-chinese-with-pylist' 这个函数 benchmark 显示速度比较快，
            ;; 但用到这个地方后，chinese-pyim 卡顿明显，暂时找不到原因。
            (let ((pinyins (pyim-hanzi2pinyin word nil "-" t))
                  boundary)
              (when (cl-some
                     #'(lambda (x)
                         (setq boundary (pyim-pinyin-match py-str x t t)))
                     pinyins)
                (push word guess-words-similar))
              ;; 搜索拼音与 py-list "^" 匹配的词条，比如:
              ;; 拼音 "ni-hao" 就匹配 "你好我的家乡"，然后根据拼音的长度，
              ;; 提取一个子字符串作为词条，比如：字符串 "你好我的家乡" 的子字符串
              ;; "你好" 会被提取出来。
              (when (cl-some
                     #'(lambda (x)
                         (setq boundary (pyim-pinyin-match py-str x t t t)))
                     pinyins)
                (push (substring word (car boundary) (cdr boundary))
                      guess-words-accurate)))
            (setq count (1+ count))
            ;; 当 `words' 包含的元素太多时，后面处理会极其缓慢，
            ;; 这里通过限制循环次数来提高输入法的响应，经验数值。
            (when (> count 200)
              (setq words nil)))))

      (setq guess-words-accurate (reverse guess-words-accurate))
      ;; 合并到联想词一起处理，这样用户就可以通过 `pyim-enable-words-predict'
      ;; 来决定哪一类联想词优先显示。
      (push `(guess-words ,@(reverse guess-words-similar)) words-predicted))

    ;; 在当前 buffer 或者其他 buffer 中，搜索光标处的中文词语，得到
    ;; 所有 *可能* 的候选词语，依靠这些候选词语，来提高输入法的识别精度。
    (when (member 'dabbrev pyim-enable-words-predict)
      (let* ((prefix (pyim-grab-chinese-word (length pyim-current-str) pyim-last-input-word))
             (prefix-length (length prefix))
             (words (when (> prefix-length 0)
                      ;; prefix 为光标前的一个中文字符串：我们根据 prefix 构建一个 regexp,
                      ;; 在指定的 buffer 中搜索词条，得到的结果保存到 words 变量中, 假如 prefix 为 “你好”，
                      ;; 则搜索 “你好<1-10个字符>” ，后面的代码会从这 “1-10个字符” 中提取符合
                      ;; 要求的字符串作为联想词。
                      (delete-dups
                       (pyim-get-dabbrev
                        (format "%s[^[:punct:][:blank:]\n]\\{1,10\\}" prefix)
                        pyim-dabbrev-time-limit
                        (pcase pyim-dabbrev-other-buffers
                          (`t (list major-mode))
                          (`all `all))))))
             (words-searched
              ;; 在所有指定的 buffer 中，搜索拼音匹配 `pylist' 中文词条，
              ;; 搜索得到的结果作为联想词。
              (when (> length-pylist 1)
                (delete-dups
                 (pyim-get-dabbrev
                  (pyim-build-chinese-regexp-for-pylist pylist nil nil t)
                  pyim-dabbrev-time-limit
                  (pcase pyim-dabbrev-other-buffers
                    (`t (list major-mode))
                    (`all `all))))))
             (count 0))
        (while words
          ;; 搜索得到的候选词条都包含 prefix, 需要剔除。
          (setq word (substring (pop words) prefix-length))
          (unless (pyim-string-match-p "\\CC" word)
            (let ((pinyins (pyim-hanzi2pinyin word nil "-" t))
                  boundary)
              ;; 请参考 guess-words 处的 comment
              (when (cl-some
                     #'(lambda (x)
                         (setq boundary (pyim-pinyin-match py-str x)))
                     pinyins)
                (push (substring word (car boundary) (cdr boundary))
                      dabbrev-words-accurate-1)
                (push (substring word 0 (cdr boundary))
                      dabbrev-words-similar-1))
              (when (cl-some
                     #'(lambda (x)
                         (setq boundary (pyim-pinyin-match py-str x t)))
                     pinyins)
                (push (substring word (car boundary) (cdr boundary))
                      dabbrev-words-accurate-1))))
          (setq count (1+ count))
          (when (> count 500)
            (setq words nil)))

        (while words-searched
          (setq word (pop words-searched))
          ;; 从 buffer 中搜索得到的中文字符串，可能是一个无意义的的中文词语，这里做一下分类，
          ;; 如果这个字符串在词库中存在，那就说明这个字符串是精确匹配的候选词，优先显示；
          ;; 如果从词库中搜索不到，那么这个词只能作为类似词，放到稍微靠后的位置显示，
          (if (member word (pyim-get py-str))
              (push word dabbrev-words-accurate-2)
            (push word dabbrev-words-similar-2))
          (setq count (1+ count))
          (when (> count 500)
            (setq words-searched nil)))

        (setq dabbrev-words-accurate-1 (reverse dabbrev-words-accurate-1))
        (setq dabbrev-words-accurate-2 (reverse dabbrev-words-accurate-2))
        (setq dabbrev-words-similar-2 (reverse dabbrev-words-similar-2))
        (push `(dabbrev ,@(reverse dabbrev-words-similar-1)) words-predicted)))

    ;; debug
    (when pyim-debug
      (dolist (var '(words
                     guess-words-accurate
                     guess-words-similar
                     dabbrev-words-accurate-1
                     dabbrev-words-accurate-2
                     dabbrev-words-similar-1
                     dabbrev-words-similar-2))
        (when var
          (princ (format (concat (symbol-name var) ": %S\n")
                         (symbol-value var))))))

    ;; 将输入的拼音按照声母和韵母打散，得到尽可能多的拼音组合，
    ;; 查询这些拼音组合，得到的词条做为联想词。
    (setq wordspy (pyim-possible-words-py pylist))
    (when (and wordspy (member 'pinyin-znabc pyim-enable-words-predict))
      (push `(pinyin-znabc ,@(pyim-possible-words wordspy)) words-predicted))

    ;; 依次搜索每个拼音对应的汉字。
    (setq chars (pyim-get (concat (caar pylist) (cdar pylist))))

    ;; 将上述搜索得到的词条合并。
    (setq choice `(,@dabbrev-words-accurate-1
                   ,@dabbrev-words-accurate-2
                   ,@guess-words-accurate
                   ,(car words)
                   ;; 从 buffer 中搜索到的类似词，即使是 *类似* 的，也
                   ;; 非常有用
                   ,@dabbrev-words-similar-2
                   ,@words
                   ;; 没有精确匹配的词条时，设置第一个被选词为字符，
                   ;; 这样可以减少不可预期的联想词带来的视觉压力。
                   ,@(unless words
                       (list (car chars)))
                   ;; 联想词
                   ,@(pyim-flatten-list
                      (mapcar
                       #'(lambda (x)
                           (cdr (assoc x words-predicted)))
                       pyim-enable-words-predict))
                   ;; 汉字字符
                   ,@chars))
    (delete-dups (delq nil choice))))

(defun pyim-grab-chinese-word (&optional backward-char-number fallback)
  "获取光标处一个 *有效的* 中文词语，较长的词语优先。
如果提取不到合适的中文词语，就返回 `pyim-last-input-word' 的值。"
  (unless (featurep 'chinese-pyim-utils)
    (require 'chinese-pyim-utils))
  (let* ((backward-char-number (or backward-char-number 0))
         (string (replace-regexp-in-string
                  ".*\\CC" ""
                  (buffer-substring
                   (save-excursion
                     ;; 在输入中文的时候，`pyim-current-str' 也会
                     ;; 插入到光标处，跳过。。。
                     (backward-char backward-char-number)
                     (point))
                   (save-excursion
                     (backward-char backward-char-number)
                     (skip-syntax-backward "w")
                     (point)))))
         (string
          ;; 我们先提取一个中文字符串，然后将这个字符串分词，得到所需词语。
          ;; 因为长字符串分词消耗的时间较长，影响输入法响应速度，所以这里限制
          ;; 字符串长度为6，经验数值。
          (if (> (length string) 6)
              (substring string -6)
            string))
         (length (+ (length string) 1)))
    (or (cl-some
         #'(lambda (x)
             (if (= (nth 2 x) length)
                 (car x)))
         (nreverse (pyim-split-chinese-string string)))
        (or fallback ""))))

(defun pyim-pinyin-match (pinyin1 pinyin2 &optional match-beginning first-equal all-equal)
  "判断拼音 `pinyin1' 是否和拼音 `pinyin2' 相匹配，如果匹配，
则返回匹配的起点与终点，通过起点和终点，可以方便的从 `pinyin2'
对应的汉字字符串中提取拼音为 `pinyin1' 的子字符串。比如：

shi-shui 与  ni-shi-shui-ya 匹配，这个函数的返回值为 (1 . 3),
我们可以使用下面这一个语句：

       (substring \"你是谁啊\" 1 3)

得到拼音 shi-shui 对应的子字符串: “是谁”。"
  (when (and (stringp pinyin1)
             (stringp pinyin2)
             (> (length pinyin1) 0)
             (> (length pinyin2) 0))
    (let* ((long-pinyin (pyim-string-match-p "-" pinyin1))
           (regexp (pyim-build-pinyin-regexp
                    pinyin1
                    match-beginning
                    ;; 当 `pinyin1' 为一个汉字的拼音时，强制 equal 匹配
                    (if long-pinyin
                        first-equal
                      t)
                    all-equal))
           (regexp
            ;; 当 `pinyin1' 为一个汉字的拼音时，
            ;; 强制尾端匹配，这样可以清除许多不需要的候选词。
            ;; 比如：“jia” 匹配到 “将”。
            (if long-pinyin
                regexp
              (format "%s$\\|%s[-]+" regexp regexp)))
           (match (pyim-string-match-p regexp pinyin2))
           (substring (when match
                        (substring pinyin2 0 match)))
           (begin (when substring
                    (length (replace-regexp-in-string
                             "[a-z]" "" substring))))
           (length
            (when pinyin1
              (+ 1 (length (replace-regexp-in-string
                            "[a-z]" "" pinyin1))))))
      (when (and begin length)
        (cons begin (+ begin length))))))

(defun pyim-build-chinese-regexp-for-pylist (pylist &optional match-beginning
                                                    first-equal all-equal)
  "这个函数生成一个 regexp ，用这个 regexp 可以搜索到
拼音匹配 `pylist' 的中文字符串。"
  (let* ((pylist (mapcar
                  #'(lambda (x)
                      (concat (car x) (cdr x)))
                  pylist))
         (cchar-list
          (let ((n 0) results)
            (dolist (py pylist)
              (push
               (mapconcat #'identity
                          (pyim-pinyin-pymap-get-pinyin-matched-char
                           py
                           (or all-equal
                               (and first-equal
                                    (= n 0)))) "")
               results)
              (setq n (+ 1 n)))
            (nreverse results)))
         (regexp
          (mapconcat
           #'(lambda (x)
               (when (pyim-string-match-p "\\cc" x)
                 (format "[%s]" x)))
           cchar-list
           "")))
    (unless (equal regexp "")
      (concat (if match-beginning "^" "")
              regexp))))

(defun pyim-match-chinese-with-pylist (pylist chinese-string &optional match-beginning
                                              first-equal all-equal)
  "从中文字符串 `chinese-string' 中搜索一个拼音与 `pylist' 匹配的子字符串，
然后返回匹配的起点与终点组成的 cons，通过起点和终点，可以方便的提取匹配的子字符串
或者其他相关的子字符串。"
  (when (and (listp pylist)
             (stringp chinese-string))
    (let* ((length-pylist (length pylist))
           (length-str (length chinese-string))
           (regexp (pyim-build-chinese-regexp-for-pylist
                    pylist match-beginning first-equal all-equal))
           (begin (pyim-string-match-p regexp chinese-string)))
      (when begin
        (cons begin
              (min length-str
                   (+ begin length-pylist)))))))

(defun pyim-sublist (list start end)
  "Return a section of LIST, from START to END.
Counting starts at 1."
  (let (rtn (c start))
    (setq list (nthcdr (1- start) list))
    (while (and list (<= c end))
      (push (pop list) rtn)
      (setq c (1+ c)))
    (nreverse rtn)))

(defun pyim-flatten-list (my-list)
  (cond
   ((null my-list) nil)
   ((atom my-list) (list my-list))
   (t (append (pyim-flatten-list (car my-list))
              (pyim-flatten-list (cdr my-list))))))

(defun pyim-possible-words (wordspy)
  "根据拼音得到可能的词组。例如：
  (pyim-possible-words '((\"p-y\" (\"p\" . \"in\") (\"y\" . \"\"))))
    => (\"拼音\" \"贫铀\" \"聘用\")
"
  (let (words)
    (dolist (word (reverse wordspy))
      (if (listp word)
          (setq words (append words (pyim-get (car word))))
        (setq words (append words (pyim-get word)))))
    words))

(defun pyim-possible-words-py (pylist)
  "所有可能的词组拼音。从第一个字开始，每个字断开形成一个拼音。如果是
完整拼音，则给出完整的拼音，如果是给出声母，则为一个 CONS CELL，CAR 是
拼音，CDR 是拼音列表。例如：

 (setq foo-pylist (pyim-split-string \"pin-yin-sh-r\" 'default))
  => ((\"p\" . \"in\") (\"y\" . \"in\") (\"sh\" . \"\") (\"r\" . \"\"))

 (pyim-possible-words-py foo-pylist)
  => (\"pin-yin\" (\"p-y-sh\" (\"p\" . \"in\") (\"y\" . \"in\") (\"sh\" . \"\")) (\"p-y-sh-r\" (\"p\" . \"in\") (\"y\" . \"in\") (\"sh\" . \"\") (\"r\" . \"\")))
 "
  (let (pys fullpy smpy wordlist (full t))
    (if (string< "" (cdar pylist))
        (setq fullpy (concat (caar pylist) (cdar pylist))
              smpy (pyim-essential-py (car pylist)))
      (setq smpy (caar pylist)
            full nil))
    (setq wordlist (list (car pylist)))
    (dolist (py (cdr pylist))
      (setq wordlist (append wordlist (list py)))
      (if (and full (string< "" (cdr py)))
          (setq fullpy (concat fullpy "-" (car py) (cdr py))
                smpy (concat smpy "-" (pyim-essential-py py))
                pys (append pys (list fullpy)))
        (setq full nil
              smpy (concat smpy "-" (pyim-essential-py py))
              pys (append pys (list (cons smpy wordlist))))))
    ;; (message "%s: %s" pys wordlist))
    pys))

(defun pyim-essential-py (py)
  "一个拼音中的主要部分，如果有声母返回声母，否则返回韵母"
  (if (string< "" (car py))
      (car py)
    (cdr py)))
;; #+END_SRC

;; *** 核心函数：拼音字符串处理函数
;; `pyim-handle-string' 这个函数是一个重要的 *核心函数* ，其大致工作流程为：
;; 1. 查询拼音字符串 `pyim-current-key' 得到： 待选词列表
;;    `pyim-current-choices' 和 当前选择的词条 `pyim-current-key'
;; 2. 显示备选词条和选择备选词等待用户选择。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-handle-string ()
  (let ((pinyin-scheme-name pyim-default-pinyin-scheme)
        (str pyim-current-key)
        userpos wordspy)
    (setq pyim-pylist-list (pyim-split-string str pinyin-scheme-name)
          pyim-pinyin-position 0)
    (unless (and (pyim-validp (car pyim-pylist-list))
                 (progn
                   (setq userpos (pyim-user-divide-pos str)
                         pyim-current-key (pyim-restore-user-divide
                                           (pyim-pylist-to-string (car pyim-pylist-list) nil pinyin-scheme-name)
                                           userpos))
                   (setq pyim-current-choices (list (delete-dups (pyim-get-choices pyim-pylist-list))))
                   (when  (car pyim-current-choices)
                     (setq pyim-current-pos 1)
                     (pyim-update-current-str)
                     (pyim-format-page)
                     (pyim-show)
                     t)))
      (setq pyim-current-str (replace-regexp-in-string "-" "" pyim-current-key))
      (setq pyim-guidance-str (format "%s"
                                      (replace-regexp-in-string
                                       "-" " " pyim-current-key)))
      (pyim-show))))

;; #+END_SRC

;; ** 处理当前需要插入字符串 `pyim-current-str'
;; Chinese-pyim 使用变量 `pyim-current-str' 保存 *当前需要在 buffer 中插
;; 入的字符串* 。

;; 处理 `pyim-current-str' 的代码分散在多个函数中，可以按照下面的方式分类：
;; 1. 英文字符串：Chinese-pyim 没有找到相应的候选词时（比如：用户输入错
;;    误的拼音），`pyim-current-str' 的值与 `pyim-current-key' 大致相同。
;;    相关代码很简单，分散在 `pyim-handle-string' 或者
;;    `pyim-append-string' 等相关函数。
;; 2. 汉字或者拼音和汉字的混合：当 Chinese-pyim 找到相应的候选词条时，
;;    `pyim-current-str' 的值可以是完全的中文词条，比如：
;;    #+BEGIN_EXAMPLE
;;    你好
;;    #+END_EXAMPLE
;;    或者中文词条＋拼音的混合新式，比如：
;;    #+BEGIN_EXAMPLE
;;    你好bj
;;    #+END_EXAMPLE
;;    这部份代码相对复杂，使用 `pyim-update-current-key' 专门处理。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-append-string (str)
  "append STR to pyim-current-str"
  (setq pyim-current-str (concat pyim-current-str str)))

(defun pyim-update-current-str ()
  "update `pyim-current-str'"
  (let* ((end (pyim-page-end))
         (start (1- (pyim-page-start)))
         (choices (car pyim-current-choices))
         (choice (pyim-subseq choices start end))
         (pos (1- (min pyim-current-pos (length choices))))
         rest)
    (setq pyim-current-str (concat (substring pyim-current-str 0 pyim-pinyin-position)
                                   (pyim-choice (nth pos choices)))
          rest (mapconcat (lambda (py)
                            (concat (car py) (cdr py)))
                          (nthcdr (length pyim-current-str) (car pyim-pylist-list))
                          "'"))
    (if (string< "" rest)
        (setq pyim-current-str (concat pyim-current-str rest)))))
;; #+END_SRC

;; Chinese-pyim 会使用 emacs overlay 机制在 *待输入buffer* 光标处高亮显示
;; `pyim-current-str'，让用户快速了解当前输入的字符串，具体方式是：
;; 1. 在 `pyim-input-method' 中调用 `pyim-setup-overlays' 创建 overlay ，并
;;    使用变量 `pyim-overlay' 保存，创建时将 overlay 的 face 属性设置为
;;    `pyim-string-face' ，用户可以使用这个变量来自定义 face。
;; 2. 使用函数 `pyim-show' 高亮显示 `pyim-current-str'
;;    1. 清除光标处原来的字符串。
;;    2. 插入 `pyim-current-str'
;;    3. 使用 `move-overlay' 函数调整变量 `pyim-overlay' 中保存的 overlay，
;;       让其符合新插入的字符串。
;; 3. 在 `pyim-input-method' 中调用 `pyim-delete-overlays' ，删除
;;    `pyim-overlay' 中保存的 overlay，这个函数同时也删除了 overlay 中包
;;    含的文本 `pyim-current-str'。

;; 真正在 *待输入buffer* 插入 `pyim-current-str' 字符串的函数是
;; `read-event'，具体见 `pyim-input-method' 相关说明。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-setup-overlays ()
  (let ((pos (point)))
    (if (overlayp pyim-overlay)
        (move-overlay pyim-overlay pos pos)
      (setq pyim-overlay (make-overlay pos pos))
      (if input-method-highlight-flag
          (overlay-put pyim-overlay 'face 'pyim-string-face)))))

(defun pyim-delete-overlays ()
  (if (and (overlayp pyim-overlay) (overlay-start pyim-overlay))
      (delete-overlay pyim-overlay)))
;; #+END_SRC

;; ** 显示和选择备选词条
;; *** 构建词条菜单字符串： `pyim-guidance-str' 。
;; Chinese-pyim 内建两种方式显示选词框：

;; 1. 使用 `pyim-minibuffer-message' 函数在 minibuffer 中显示选词框。
;; 2. 使用 `pyim-tooltip-show' 函数在光标处创建一个 tooltip 来显示选词框。

;; 两种方式的基本原理相同：通过 *待选词列表* 构建为一个字符串，然后显示这个字符串。
;; 用户可以根据这个字符串的提示，来执行相应的动作，比如按空格确认当前选择的词条或
;; 者按数字选择这个数字对应的词条。比如：

;; #+BEGIN_EXAMPLE
;; "1. 你好 2. 倪皓 3. 你 4.泥 ..."
;; #+END_EXAMPLE

;; Chinese-pyim 使用 `pyim-current-choices' 来保存 *待选词列表* ，我们以
;; "nihao" 对应的 `pyim-current-choices' 的值为例，来说明选词框相关的操作
;; 函数。

;; #+BEGIN_EXAMPLE
;; (#("你好" 0 2 (py ("ni-hao"))) #("倪皓" 0 2 (py ("ni-hao"))) "泥" "你" "呢" "拟" "逆" "腻" "妮" "怩" "溺" "尼" "禰" "齯" "麑" "鲵" "蜺" "衵" "薿" "旎" "睨" "铌" "昵" "匿" "倪" "霓" "暱" "柅" "猊" "郳" "輗" "坭" "惄" "堄" "儗" "伲" "祢" "慝")
;; #+END_EXAMPLE

;; 变量 `pyim-guidance-str' 用来保存需要在 minibuffer 选词框中显示的词条
;;  菜单字符串，而变量 `pyim-current-pos' 纪录当前选择的词条在
;;  `pyim-current-choices' 中的位置，如果当前选择的词条为“倪皓”，那么其取
;;  值为2，如果当前选择的词条为“腻”，其取值为8。

;;  *待选词列表* 一般都很长，不可能在一行中完全显示，所以 Chinese-pyim 使
;;  用了 page 的概念，比如，上面的 “nihao” 的 *待选词列表* 就可以逻辑的分
;;  成5页：

;; #+BEGIN_EXAMPLE
;; ("你好"  倪皓"  "泥"  "你"  "呢"  "拟"  "逆"  "腻"  "妮"   ;第1页
;;  "怩"    "溺"   "尼"  "禰"  "齯"  "麑"  "鲵"  "蜺"  "衵"   ;第2页
;;  "薿"    "旎"   "睨"  "铌"  "昵"  "匿"  "倪"  "霓"  "暱"   ;第3页
;;  "柅"    "猊"   "郳"  "輗"  "坭"  "惄"  "堄"  "儗"  "伲"   ;第4页
;;  "祢"    "慝"                                              ;第5页)
;; #+END_EXAMPLE

;; 用户可以使用变量 `pyim-page-length' 自定义每一页显示词条的数量，默认设
;; 置为9。

;; `pyim-current-pos' 的取值以及 `pyim-page-length' 的设定值，共同决定了
;; Chinese-pyim 需要显示哪一页，我们以一个表格来表示上述 *待选词列表* ：

;; |       |          |       |         |      |      |      |      |      |          |
;; |-------+----------+-------+---------+------+------+------+------+------+----------|
;; | 第1页 | "你好"   | 倪皓" | "泥"    | "你" | "呢" | "拟" | "逆" | "腻" | "妮"     |
;; | 第2页 | "怩"     | "溺"  | "尼"    | "禰" | "齯" | "麑" | "鲵" | "蜺" | "衵"     |
;; | 第3页 | -B- "薿" | "旎"  | -A-"睨" | "铌" | "昵" | "匿" | "倪" | "霓" | -E- "暱" |
;; | 第4页 | "柅"     | "猊"  | "郳"    | "輗" | "坭" | "惄" | "堄" | "儗" | "伲"     |
;; | 第5页 | "祢"     | "慝"  |         |      |      |      |      |      |          |

;; 假设 `pyim-current-pos' 为 A 所在的位置。那么：
;; 1. 函数 `pyim-current-page' 返回值为3， 说明当前 page 为第3页。
;; 2. 函数 `pyim-total-page'  返回值为5，说明 page 共有5页。
;; 3. 函数 `pyim-page-start' 返回 B 所在的位置。
;; 4. 函数 `pyim-page-end' 返回 E 所在的位置。
;; 5. 函数 `pyim-format-page' 会从 `pyim-current-choices' 中提取一个
;;    sublist:
;;    #+BEGIN_EXAMPLE
;;    ("薿" "旎" "睨" "铌" "昵" "匿" "倪" "霓" "暱")
;;    #+END_EXAMPLE
;;    这个 sublist 的起点为  `pyim-page-start' 的返回值，终点为
;;    `pyim-page-end' 的返回值。然后使用这个 sublist 来构建类似下面的字符
;;    串，并保存到变量 `pyim-guidance-str' 。
;;    #+BEGIN_EXAMPLE
;;    "1. 薿 2.旎 3.睨 4.铌 5.昵 6.匿 7.倪 8.霓 9.暱"
;;    #+END_EXAMPLE

;; `pyim-next-page' 这个命令用来翻页，其原理是：改变 `pyim-current-pos'的
;; 取值，假设一次只翻一页，那么这个函数所做的工作就是：
;; 1. 首先将 `pyim-current-pos' 增加 `pyim-page-length' ，确保其指定的位
;;    置在下一页。
;; 2. 然后将 `pyim-current-pos' 的值设定为 `pyim-page-start' 的返回值，确
;;    保 `pyim-current-pos' 的取值为下一页第一个词条的位置。
;; 3. 最后调用 `pyim-format-page' 来重新设置 `pyim-guidance-str' 。

;; #+BEGIN_SRC emacs-lisp
;;;  page format
(defun pyim-subseq (list from &optional to)
  (if (null to) (nthcdr from list)
    (butlast (nthcdr from list) (- (length list) to))))

(defun pyim-mod (x y)
  "like `mod', but when result is 0, return Y"
  (let ((base (mod x y)))
    (if (= base 0)
        y
      base)))

(defun pyim-choice (choice)
  (if (consp choice)
      (car choice)
    choice))

(defun pyim-current-page ()
  (1+ (/ (1- pyim-current-pos) pyim-page-length)))

(defun pyim-total-page ()
  (1+ (/ (1- (length (car pyim-current-choices))) pyim-page-length)))

(defun pyim-page-start ()
  "计算当前所在页的第一个词条的位置"
  (let ((pos (min (length (car pyim-current-choices)) pyim-current-pos)))
    (1+ (- pos (pyim-mod pos pyim-page-length)))))

(defun pyim-page-end (&optional finish)
  "计算当前所在页的最后一个词条的位置，如果 pyim-current-choices 用
完，则检查是否有补全。如果 FINISH 为 non-nil，说明，补全已经用完了"
  (let* ((whole (length (car pyim-current-choices)))
         (len pyim-page-length)
         (pos pyim-current-pos)
         (last (+ (- pos (pyim-mod pos len)) len)))
    (if (< last whole)
        last
      (if finish
          whole
        (pyim-page-end t)))))

(defun pyim-format-page (&optional hightlight-current)
  "按当前位置，生成候选词条"
  (let* ((end (pyim-page-end))
         (start (1- (pyim-page-start)))
         (choices (car pyim-current-choices))
         (choice (pyim-subseq choices start end))
         (pos (- (min pyim-current-pos (length choices)) start))
         (i 0))
    (setq pyim-guidance-str
          (format "%s[%d/%d]: %s"
                  (replace-regexp-in-string "-" " " pyim-current-key)
                  (pyim-current-page) (pyim-total-page)
                  (mapconcat 'identity
                             (mapcar
                              (lambda (c)
                                (setq i (1+ i))
                                (let (str)
                                  (setq str (if (consp c)
                                                (concat (car c) (cdr c))
                                              c))
                                  ;; 高亮当前选择的词条，用于 `pyim-next-word'
                                  (if (and hightlight-current
                                           (= i pos))
                                      (format "%d[%s]" i
                                              (propertize str 'face 'pyim-minibuffer-string-face))
                                    (format "%d.%s " i str))))
                              choice) "")))))

(defun pyim-next-page (arg)
  (interactive "p")
  (if (= (length pyim-current-key) 0)
      (progn
        (pyim-append-string (pyim-translate last-command-event))
        (pyim-terminate-translation))
    (let ((new (+ pyim-current-pos (* pyim-page-length arg) 1)))
      (setq pyim-current-pos (if (> new 0) new 1)
            pyim-current-pos (pyim-page-start))
      (pyim-update-current-str)
      (pyim-format-page)
      (pyim-show))))

(defun pyim-previous-page (arg)
  (interactive "p")
  (pyim-next-page (- arg)))

(defun pyim-next-word (arg)
  (interactive "p")
  (if (= (length pyim-current-key) 0)
      (progn
        (pyim-append-string (pyim-translate last-command-event))
        (pyim-terminate-translation))
    (let ((new (+ pyim-current-pos arg)))
      (setq pyim-current-pos (if (> new 0) new 1))
      (pyim-update-current-str)
      (pyim-format-page t)
      (pyim-show))))

(defun pyim-previous-word (arg)
  (interactive "p")
  (pyim-next-word (- arg)))
;; #+END_SRC

;; *** 显示选词框
;; 当`pyim-guidance-str' 构建完成后，Chinese-pyim 使用函数 `pyim-show' 重
;; 新显示选词框，`pyim-show' 会根据 `pyim-use-tooltip' 的取值来决定使用
;; 哪种方式来显示选词框（minibuffer 或者 tooltip ）。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-show ()
  (unless enable-multibyte-characters
    (setq pyim-current-key nil
          pyim-current-str nil)
    (error "Can't input characters in current unibyte buffer"))
  (pyim-delete-region)
  (insert pyim-current-str)
  (move-overlay pyim-overlay (overlay-start pyim-overlay) (point))
  ;; Then, show the guidance.
  (when (and (not input-method-use-echo-area)
             (null unread-command-events)
             (null unread-post-input-method-events))
    (if (eq (selected-window) (minibuffer-window))
        ;; Show the guidance in the next line of the currrent
        ;; minibuffer.
        (pyim-minibuffer-message
         (format "  [%s]\n%s"
                 current-input-method-title pyim-guidance-str))
      ;; Show the guidance in echo area without logging.
      (let ((message-log-max nil))
        (if pyim-use-tooltip
            (let ((pos (string-match ": " pyim-guidance-str)))
              (if pos
                  (setq pyim-guidance-str
                        (format "=> %s\n%s"
                                (substring pyim-guidance-str 0 pos)
                                (substring pyim-guidance-str (+ pos 2)))))
              (pyim-tooltip-show pyim-guidance-str (overlay-start pyim-overlay)))
          (message "%s" pyim-guidance-str))))))

(defun pyim-delete-region ()
  "Delete the text in the current translation region of E+."
  (if (overlay-start pyim-overlay)
      (delete-region (overlay-start pyim-overlay)
                     (overlay-end pyim-overlay))))

(defun pyim-tooltip-show (string position)
  "在 `position' 位置，使用 pos-tip 或者 popup 显示字符串 `string' 。"
  (let ((frame (window-frame (selected-window)))
        (length (* pyim-page-length 10))
        (tooltip pyim-use-tooltip)
        (pos-tip-usable-p (pyim-tooltip-pos-tip-usable-p)))
    (cond ((or (eq tooltip t)
               (eq tooltip 'popup)
               (and (eq tooltip 'pos-tip)
                    (not pos-tip-usable-p)))
           (popup-tip string :point position :margin 1))
          ((and pos-tip-usable-p
                (eq tooltip 'pos-tip))
           (pos-tip-show-no-propertize pyim-guidance-str
                                       nil
                                       position nil 15
                                       (round (* (pos-tip-tooltip-width length (frame-char-width frame))
                                                 pyim-tooltip-width-adjustment))
                                       (pos-tip-tooltip-height 2 (frame-char-height frame) frame)
                                       nil nil 35))
          (t (error "`pyim-use-tooltip' 设置不对，请重新设置。")))))

(defun pyim-minibuffer-message (string)
  (message nil)
  (let ((point-max (point-max))
        (inhibit-quit t))
    (save-excursion
      (goto-char point-max)
      (insert string))
    (sit-for 1000000)
    (delete-region point-max (point-max))
    (when quit-flag
      (setq quit-flag nil
            unread-command-events '(7)))))

(defun pyim-tooltip-pos-tip-usable-p ()
  "测试当前环境下 pos-tip 是否可用。"
  (not (or noninteractive
           emacs-basic-display
           (not (display-graphic-p))
           (not (fboundp 'x-show-tip)))))
;; #+END_SRC

;; *** 选择备选词
;; #+BEGIN_SRC emacs-lisp
(defun pyim-select-current ()
  (interactive)
  (if (null (car pyim-current-choices))  ; 如果没有选项，输入空格
      (progn
        (setq pyim-current-str (pyim-translate last-command-event))
        (pyim-terminate-translation))
    (let ((str (pyim-choice (nth (1- pyim-current-pos) (car pyim-current-choices))))
          pylist)
      (pyim-create-or-rearrange-word str t)
      (setq pyim-pinyin-position (+ pyim-pinyin-position (length str)))
      (if (>= pyim-pinyin-position (length (car pyim-pylist-list)))
                                        ; 如果是最后一个，检查
                                        ; 是不是在文件中，没有的话，创
                                        ; 建这个词
          (progn
            (if (not (member pyim-current-str (car pyim-current-choices)))
                (pyim-create-or-rearrange-word pyim-current-str))
            (setq pyim-last-input-word pyim-current-str)
            (pyim-terminate-translation)
            ;; Chinese-pyim 使用这个 hook 来处理联想词。
            (run-hooks 'pyim-select-word-finish-hook))
        (setq pylist (nthcdr pyim-pinyin-position (car pyim-pylist-list)))
        (setq pyim-current-choices (list (pyim-get-choices (list pylist)))
              pyim-current-pos 1)
        (pyim-update-current-str)
        (pyim-format-page)
        (pyim-show)))))

(defun pyim-number-select ()
  "如果没有可选项，插入数字，否则选择对应的词条"
  (interactive)
  (if (car pyim-current-choices)
      (let ((index (- last-command-event ?1))
            (end (pyim-page-end)))
        (if (> (+ index (pyim-page-start)) end)
            (pyim-show)
          (setq pyim-current-pos (+ pyim-current-pos index))
          (setq pyim-current-str (concat (substring pyim-current-str 0
                                                    pyim-pinyin-position)
                                         (pyim-choice
                                          (nth (1- pyim-current-pos)
                                               (car pyim-current-choices)))))
          (pyim-select-current)))
    (pyim-append-string (char-to-string last-command-event))
    (pyim-terminate-translation)))
;; #+END_SRC

;; ** 处理标点符号
;; 常用的标点符号数量不多，所以 Chinese-pyim 没有使用文件而是使用一个变量
;; `pyim-punctuation-dict' 来设置标点符号对应表，这个变量是一个 alist 列表。

;; Chinese-pyim 在运行过程中调用函数 `pyim-translate' 进行标点符号格式的转换。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-get-translate-trigger-char ()
  "检查 `pyim-translate-trigger-char' 是否为一个合理的 trigger char 。

Chinese-pyim 的 translate-trigger-char 要占用一个键位，为了防止用户
自定义设置与输入法冲突，这里需要检查一下这个键位设置的是否合理，
如果不合理，就返回输入法默认设定。"
  (let* ((user-trigger-char pyim-translate-trigger-char)
         (user-trigger-char
          (if (characterp user-trigger-char)
              (char-to-string user-trigger-char)
            (when (= (length user-trigger-char) 1)
              user-trigger-char)))
         (first-char (pyim-get-pinyin-scheme-option
                      pyim-default-pinyin-scheme
                      :first-chars))
         (prefer-trigger-chars (pyim-get-pinyin-scheme-option
                                pyim-default-pinyin-scheme
                                :prefer-trigger-chars)))
    (if (pyim-string-match-p user-trigger-char first-char)
        (progn
          ;; (message "注意：pyim-translate-trigger-char 设置和当前输入法冲突，使用推荐设置：\"%s\""
          ;;          prefer-trigger-chars)
          prefer-trigger-chars)
      user-trigger-char)))

(defun pyim-translate (char)
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
         (trigger-str (pyim-get-translate-trigger-char)))
    (cond
     ;; 空格之前的字符什么也不输入。
     ((< char ? ) "")

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
      ;; `pyim-last-input-word' 保存的词条用于词语联想，
      ;; 逻辑上，当输入标点符号后，保存的词条已经失效，
      ;; 应该将其清空。
      (setq pyim-last-input-word nil)
      str)

     ;; 当前字符属于 `pyim-punctuation-escape-list'时，
     ;; 插入英文标点。
     ((member (char-before)
              pyim-punctuation-escape-list)
      (setq pyim-last-input-word nil)
      str)

     ;; 当 `pyim-punctuation-half-width-functions' 中
     ;; 任意一个函数返回值为 t 时，插入英文标点。
     ((cl-some #'(lambda (x)
                   (if (functionp x)
                       (funcall x char)
                     nil))
               pyim-punctuation-half-width-functions)
      (setq pyim-last-input-word nil)
      str)

     ;; 当光标前面为英文标点时， 按 `pyim-translate-trigger-char'
     ;; 对应的字符后， 自动将其转换为对应的中文标点。
     ((and (numberp punc-posit-before-1)
           (= punc-posit-before-1 0)
           (equal str trigger-str))
      (setq pyim-last-input-word nil)
      (pyim-punctuation-translate-last-n-punctuations 'full-width)
      "")

     ;; 当光标前面为中文标点时， 按 `pyim-translate-trigger-char'
     ;; 对应的字符后， 自动将其转换为对应的英文标点。
     ((and (numberp punc-posit-before-1)
           (> punc-posit-before-1 0)
           (equal str trigger-str))
      (setq pyim-last-input-word nil)
      (pyim-punctuation-translate-last-n-punctuations 'half-width)
      "")

     ;; 正常输入标点符号。
     (punc-list
      (setq pyim-last-input-word nil)
      (pyim-return-proper-punctuation punc-list))

     ;; 当输入的字符不是标点符号时，原样插入。
     (t str))))

(defun pyim-char-before-to-string (num)
  "得到光标前第 `num' 个字符，并将其转换为字符串。"
  (let* ((point (point))
         (point-before (- point num)))
    (when (and (> point-before 0)
               (char-before point-before))
      (char-to-string (char-before point-before)))))

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

;; #+END_SRC

;; 当用户使用 org-mode 以及 markdown 等轻量级标记语言撰写文档时，常常需要输入数字列表，比如：

;; #+BEGIN_EXAMPLE
;; 1. item1
;; 2. item2
;; 3. item3
;; #+END_EXAMPLE

;; 在这种情况下，数字后面输入句号必须是半角句号而不是全角句号，Chinese-pyim 调用 `pyim-translate' 时，
;; 会检测光标前面的字符，如果这个字符属于 `pyim-punctuation-escape-list' ，Chinese-pyim 将输入
;; 半角标点，具体细节见：`pyim-translate'

;; 输入标点的样式的改变（全角或者半角）受三个方面影响：

;; 1. 用户是否手动切换了标点样式？
;; 2  用户是否手动切换到英文输入模式？
;; 3. Chinese-pyim 是否根据环境自动切换到英文输入模式？

;; 三方面的综合结果为： 只要当前的输入模式是英文输入模式，那么输入的标点符号 *必定* 是半角标点，
;; 如果当前输入模式是中文输入模式，那么，输入标点的样式用户可以使用 `pyim-toggle-full-width-punctuation'
;; 手动控制，具体请参考 `pyim-punctuation-full-width-p'。

;; #+BEGIN_SRC emacs-lisp
;;; 切换中英文标点符号
(defun pyim-punctuation-full-width-p ()
  "判断是否需要切换到全角标点输入模式"
  (and pyim-punctuation-translate-p
       ;; 如果用户手动或者根据环境自动切换为英文输入模式，
       ;; 那么标点符号也要切换为半角模式。
       (not pyim-input-ascii)
       (not (pyim-auto-switch-english-input-p))))

(defun pyim-toggle-full-width-punctuation (arg &optional silent)
  (interactive "P")
  (setq pyim-punctuation-translate-p
        (if (null arg)
            (not pyim-punctuation-translate-p)
          (> (prefix-numeric-value arg) 0)))
  (unless silent
    (if pyim-punctuation-translate-p
        (message "开启标点转换功能（使用全角标点）")
      (message "关闭标点转换功能（使用半角标点）"))))
;; #+END_SRC

;; 每次运行 `pyim-toggle-full-width-punctuation' 命令，都会反转变量 `pyim-punctuation-translate-p'
;; 的取值，`pyim-translate' 会检测 `pyim-punctuation-full-width-p' 函数的返回值，当返回值为 t 时，
;; `pyim-translate' 转换标点符号，从而输入全角标点，反之，`pyim-translate' 忽略转换，
;; 从而输入半角标点。

;; 用户也可以使用命令 `pyim-punctuation-translate-at-point' 来切换 *光标前* 标点符号的样式。


;; #+BEGIN_SRC emacs-lisp
;; 切换光标处标点的样式（全角 or 半角）
(defun pyim-punctuation-translate-at-point ()
  (interactive)
  (let* ((current-char (char-to-string (preceding-char)))
         (punc-list
          (cl-some (lambda (x)
                     (when (member current-char x) x))
                   pyim-punctuation-dict)))
    (when punc-list
      (delete-char -1)
      (if (equal current-char (car punc-list))
          (insert (pyim-return-proper-punctuation punc-list t))
        (insert (car punc-list))))))

(defun pyim-punctuation-translate-last-n-punctuations (&optional punct-style)
  "将光标前面连续的n个标点符号进行全角/半角转换，当 `punct-style' 设置为 `full-width' 时，
所有的标点符号转换为全角符号，设置为 `half-width' 时，转换为半角符号。"
  (interactive)
  (let ((punc-list (pyim-flatten-list pyim-punctuation-dict))
        (punct-style
         (or punct-style
             (intern (completing-read
                      "将光标前的标点转换为" '("full-width" "half-width")))))
        (count 0)
        number last-puncts result)
    (while count
      (let ((str (pyim-char-before-to-string count)))
        (if (member str punc-list)
            (progn
              (push str last-puncts)
              (setq count (+ count 1)))
          (setq number count)
          (setq count nil))))
    ;; 删除旧的标点符号
    (delete-char (- 0 number))
    (dolist (punct last-puncts)
      (dolist (puncts pyim-punctuation-dict)
        (let ((position (cl-position punct puncts :test #'equal)))
          (when position
            (cond
             ((eq punct-style 'full-width)
              (if (= position 0)
                  (push (pyim-return-proper-punctuation puncts) result)
                (push punct result)))
             ((eq punct-style 'half-width)
              (if (= position 0)
                  (push punct result)
                (push (car puncts) result))))))))
    (insert (mapconcat #'identity (reverse result) ""))))
;; #+END_SRC

;; 使用上述命令切换光标前标点符号的样式时，我们使用函数 `pyim-return-proper-punctuation'
;; 来处理成对的全角标点符号， 比如：

;; #+BEGIN_EXAMPLE
;; “”
;; ‘’
;; #+END_EXAMPLE
;; 这个函数的参数是一个标点符号对应表，类似：

;; #+BEGIN_EXAMPLE
;; ("." "。")
;; #+END_EXAMPLE

;; 第一个元素为半角标点，第二个和第三个元素（如果有）为对应的全角标点。

;; #+BEGIN_EXAMPLE
;; (list (pyim-return-proper-punctuation '("'" "‘" "’"))
;;       (pyim-return-proper-punctuation '("'" "‘" "’")))
;; #+END_EXAMPLE

;; 结果为:
;; : ("’" "‘")

;; 简单来说，定义这个函数的目的是为了实现类似的功能：如果第一次输入的标点是：（‘）时，
;; 那么下一次输入的标点就是（’）。


;; #+BEGIN_SRC emacs-lisp
;; 处理标点符号
(defun pyim-return-proper-punctuation (punc-list &optional before)
  "返回合适的标点符号，`punc-list'为标点符号列表，其格式类似：
      `(\",\" \"，\") 或者：`(\"'\" \"‘\" \"’\")
当 `before' 为 t 时，只返回切换之前的结果，这个用来获取切换之前
的标点符号。"
  (let* ((str (car punc-list))
         (punc (cdr punc-list))
         (switch-p (cdr (assoc str pyim-pair-punctuation-status))))
    (if (= (safe-length punc) 1)
        (car punc)
      (if before
          (setq switch-p (not switch-p))
        (setf (cdr (assoc str pyim-pair-punctuation-status))
              (not switch-p)))
      (if switch-p
          (car punc)
        (nth 1 punc)))))

;; #+END_SRC

;; 函数 `pyim-return-proper-punctuation' 内部，我们使用变量 `pyim-pair-punctuation-status'
;; 来记录“成对”中文标点符号的状态。

;; ** 处理特殊功能触发字符（单字符快捷键）
;; 输入中文的时候，我们需要快速频繁的执行一些特定的命令，
;; 最直接的方法就是将上述命令绑定到一个容易按的快捷键上，但遗憾的是 emacs 大多数容易按
;; 的快捷键都 *名花有主* 了，甚至找一个 “Ctrl＋单字符”的快捷键都不太容易，特殊功能触发
;; 字符，可以帮助我们实现“单字符”快捷键，类似 org-mode 的 speed key。

;; 默认情况下，我们可以使用特殊功能触发字符执行下面两个操作：
;; 1. 快速切换中英文标点符号的样式：当光标前的字符是一个标点符号时，按"v"可以切换这个标点的样式。
;;    比如：光标在A处的时候，按 "v" 可以将A前面的全角逗号转换为半角逗号。
;;    #+BEGIN_EXAMPLE
;;    你好，-A-
;;    #+END_EXAMPLE
;;    按 "v" 后
;;    #+BEGIN_EXAMPLE
;;    你好,-A-
;;    #+END_EXAMPLE
;; 2. 快速将光标前的词条添加到词库：当光标前的字符是中文字符时，按 "num" + "v" 可以将光标前 num 个中文汉字
;;    组成的词条添加到个人词频文件中，比如：当光标在A处时，按"4v"可以将“的红烧肉”这个词条加入个人词频文件，默认
;;    num不超过9。
;;    #+BEGIN_EXAMPLE
;;    我爱吃美味的红烧肉-A-
;;    #+END_EXAMPLE

;; 值得注意的是，这种方式如果添加的功能太多，会造成许多潜在的冲突。

;; 用户可以使用变量 `pyim-translate-trigger-char' 来设置触发字符，
;; 默认的触发字符是："v", 选择这个字符的理由是：

;; 1. "v" 不是有效的声母，不会对中文输入造成太大的影响。
;; 2. "v" 字符很容易按。

;; Chinese-pyim 使用函数 `pyim-translate' 来处理特殊功能触发字符。
;; 当待输入的字符是触发字符时，`pyim-translate' 根据光标前的字符的不同
;; 来调用不同的功能，具体见 `pyim-translate' ：

;; ** 查询某个汉字的拼音code
;;   :PROPERTIES:
;;   :CUSTOM_ID: make-char-table
;;   :END:
;; Chinese-pyim 在特定的时候需要读取一个汉字的拼音，这个工作由下面几个函数完成：

;; 函数 `pyim-get-char-code' 从 `pyim-char-table' 查询得到一个汉字字符的拼音， 例如：
;; #+BEGIN_EXAMPLE
;; (pyim-get-char-code ?我)
;; #+END_EXAMPLE

;; 结果为:
;; : ("wo")

;; 函数 `pyim-make-char-table-1' 参数 `chars’的形式类似：
;; #+BEGIN_EXAMPLE
;; (("ni" "你尼呢腻")
;;  ("wo" "我握涡卧龌"))
;; #+END_EXAMPLE

;; 最终得到一个汉字到拼音的 *hash table* ，用 *一个列表* 直观的表示为：
;; #+BEGIN_EXAMPLE
;; (('我 '("wo"))
;;  ('你 '("ni"))
;;  ('行 '("xing" "hang"))
;;  ('大 '("da")))
;; #+END_EXAMPLE

;; 我们用全局变量 `pyim-char-table' 来保存这个 *hash table* 。

;; 函数 `pyim-make-char-table-quail/PY' 是函数 `pyim-make-char-table-1' 的包装，
;; 这个函数是一个 *历史函数* ，已经没有作用了，仅仅用于学习，其运行过程大体为：
;; 1. 使用 regexp 解析  "quail/PY.el" 文件中的汉字拼音信息，这个文件的结构类似：
;;    #+BEGIN_EXAMPLE
;;    (quail-define-rules
;;    ("a" "阿啊呵腌嗄锕吖")
;;    ("ai" "爱哀挨碍埃癌艾唉矮哎皑蔼隘暧霭捱嗳瑷嫒锿嗌砹")
;;    ("an" "安案按暗岸俺谙黯鞍氨庵桉鹌胺铵揞犴埯")
;;    ("ang" "昂肮盎")
;;    ("ao" "奥澳傲熬敖凹袄懊坳嗷拗鏖骜鳌翱岙廒遨獒聱媪螯鏊")
;;    ("ba" "把八吧巴爸罢拔叭芭霸靶扒疤跋坝笆耙粑灞茇菝魃岜捌钯鲅")
;;    ("bai" "百白败摆伯拜柏呗掰捭佰稗")
;;    ("ban" "办半版般班板伴搬扮斑颁瓣拌扳绊阪坂瘢钣舨癍")
;;    ...
;;    )
;;    #+END_EXAMPLE
;; 2. 将上述汉字拼音信息 *按行处理* ，转换为下述类似的列表结构。
;;    #+BEGIN_EXAMPLE
;;    (("ni" "你尼呢腻"))
;;    #+END_EXAMPLE
;; 3. 使用 `pyim-make-char-table-1' 处理得到的列表。

;; 函数 `pyim-make-char-table' 也是函数 `pyim-make-char-table-1' 的包装，
;; 其过程简单来说就是使用 `pyim-make-char-table-1' 函数处理变量
;; `pyim-pinyin-pymap' 中保存的拼音汉字对应信息。

;; 这个例子中的语句用于调试上述三个函数。
;; #+BEGIN_EXAMPLE
;; (setq pyim-char-table nil)
;; (pyim-make-char-table-1 '(("ni" "你呢泥")))
;; (pyim-make-char-table)
;; (pyim-get-char-code ?你)
;; #+END_EXAMPLE


;; #+BEGIN_SRC emacs-lisp
(defun pyim-get-char-code (char)
  "Get the code of the character CHAR"
  (symbol-value (intern-soft (char-to-string char) pyim-char-table)))

(defun pyim-make-char-table-1 (chars)
  (dolist (char chars)
    (let ((code (car char)))
      (mapc (lambda (c)
              (let* ((str (char-to-string c))
                     (s (intern-soft str pyim-char-table))
                     (py (and s (symbol-value s))))
                (set (intern str pyim-char-table)
                     (cl-remove-duplicates
                      (append py (list code)) :test #'equal))))
            (car (cdr char))))))

(defun pyim-make-char-table ()
  "Build pinyin char hashtable from `pyim-pinyin-pymap'
in package `chinese-pyim-pymap'"
  (pyim-make-char-table-1 pyim-pinyin-pymap))

(defun pyim-make-char-table-from-quail/PY ()
  "Build pinyin char hashtable from quail/PY.el，
这个函数暂时没有用处。"
  (interactive)
  (let ((file (locate-library "quail/PY.el")))
    (if file
        (with-temp-buffer
          (insert-file-contents file)
          (goto-char (point-min))
          (while (re-search-forward
                  "^[[:space:]]*([[:space:]]*\"\\([a-z]+\\)\"[[:space:]]*\"\\([^\"]+\\)\"[[:space:]]*)[[:space:]]*$" nil t)
            (let ((pinyin (match-string 1))
                  (hanzi-string (substring-no-properties (match-string 2))))
              (pyim-make-char-table-1 `((,pinyin ,hanzi-string))))))
      (warn "没有找到 Emacs 自带文件: quail/PY.el，用户可能没有安装 emacs<VERSION>-el 软件包。
此时， Chinese-pyim 可以正常输入词条，但下面几个功能失效：
1. 词频调整功能
2. 汉字到拼音转换功能
3. 词条添加和删除功能"))))
;; #+END_SRC

;; ** 与拼音输入相关的用户命令
;; *** 删除拼音字符串最后一个字符
;; #+BEGIN_SRC emacs-lisp
(defun pyim-delete-last-char ()
  (interactive)
  (if (> (length pyim-current-key) 1)
      (progn
        (setq pyim-current-key (substring pyim-current-key 0 -1))
        (pyim-handle-string))
    (setq pyim-current-str "")
    (pyim-terminate-translation)))
;; #+END_SRC

;; *** 删除拼音字符串最后一个拼音
;; #+BEGIN_SRC emacs-lisp
(defun pyim-backward-kill-py ()
  (interactive)
  (string-match "['-][^'-]+$" pyim-current-key)
  (setq pyim-current-key
        (replace-match "" nil nil pyim-current-key))
  (pyim-handle-string))
;; #+END_SRC

;; *** 取消当前输入
;; #+BEGIN_SRC emacs-lisp
(defun pyim-quit-clear ()
  (interactive)
  (setq pyim-current-str "")
  (pyim-terminate-translation))
;; #+END_SRC
;; *** 字母上屏
;; #+BEGIN_SRC emacs-lisp
(defun pyim-quit-no-clear ()
  (interactive)
  (setq pyim-current-str (replace-regexp-in-string "-" ""
                                                   pyim-current-key))
  (pyim-terminate-translation))
;; #+END_SRC
;; *** 处理模糊音
;; 'Chinese-pyim的核心并不能处理模糊音，这里提供了一个比较 *粗糙* 的方法来处理模糊音。

;; 假如：用户需要输入“应该”，其拼音为“ying-gai”，但用户确输入了一个错误的拼音“yin-gai”，
;; 这时，用户可以通过快捷键运行 `pyim-fuzzy-pinyin-adjust' ，将“in” 替换为 “ing”，得到
;; “ying-gai”对应的词语，用户可以通过设置变量 `pyim-fuzzy-pinyin-adjust-function' 来自定义模
;; 糊音处理函数。

;; 这种处理方式能力有限，一次不能处理太多的模糊音，用户需要根据自己的需要，自定义模糊音处理函数。
;; 具体可以参考函数 `pyim-pinyin-fuzzy-adjust-1' 的定义。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-fuzzy-pinyin-adjust ()
  (interactive)
  (funcall pyim-fuzzy-pinyin-adjust-function))

(defun pyim-fuzzy-pinyin-adjust-1 ()
  (interactive)
  (when (stringp pyim-current-key)
    (cond
     ((pyim-string-match-p "eng" pyim-current-key)
      (setq pyim-current-key
            (replace-regexp-in-string "eng" "en" pyim-current-key)))
     ((pyim-string-match-p "en[^g]*" pyim-current-key)
      (setq pyim-current-key
            (replace-regexp-in-string "en" "eng" pyim-current-key))))
    (cond
     ((pyim-string-match-p "ing" pyim-current-key)
      (setq pyim-current-key
            (replace-regexp-in-string "ing" "in" pyim-current-key)))
     ((pyim-string-match-p "in[^g]*" pyim-current-key)
      (setq pyim-current-key
            (replace-regexp-in-string "in" "ing" pyim-current-key))))
    (cond
     ((pyim-string-match-p "un" pyim-current-key)
      (setq pyim-current-key
            (replace-regexp-in-string "un" "ong" pyim-current-key)))
     ((pyim-string-match-p "ong" pyim-current-key)
      (setq pyim-current-key
            (replace-regexp-in-string "ong" "un" pyim-current-key))))
    (pyim-handle-string)))
;; #+END_SRC

;; *** Chinese-pyim 取消激活
;; #+BEGIN_SRC emacs-lisp
(defun pyim-inactivate ()
  (interactive)
  (mapc 'kill-local-variable pyim-local-variable-list))
;; #+END_SRC

;; *** 切换中英文输入模式
;; #+BEGIN_SRC emacs-lisp
(defun pyim-toggle-input-ascii ()
  "Chinese-pyim 切换中英文输入模式。同时调整标点符号样式。"
  (interactive)
  (setq pyim-input-ascii
        (not pyim-input-ascii)))
;; #+END_SRC

;; *** 为 isearch 添加拼音搜索功能
;; #+BEGIN_SRC emacs-lisp
(defun pyim-isearch-build-search-regexp (pystr)
  "这个函数用于 isearch 中文 *拼音* 搜索，
根据 str 构建一个 regexp, 比如：

\"nihao\" -> \"[你呢...][好号...] \\| nihao\""
  (if (pyim-string-match-p "[^a-z']+" pystr)
      pystr
    ;; 确保 pyim 词库已经加载
    (unless pyim-buffer-list
      (setq pyim-buffer-list (pyim-load-file)))
    (let* ((pylist-list
            ;; Slowly operating, need to improve.
            (pyim-split-string pystr pyim-default-pinyin-scheme))
           (regexp-list
            (mapcar
             #'(lambda (pylist)
                 (pyim-build-chinese-regexp-for-pylist pylist))
             pylist-list))
           (regexp
            (when regexp-list
              (mapconcat #'identity
                         (delq nil regexp-list)
                         "\\|")))
           (regexp
            (if (> (length regexp) 0)
                (concat pystr "\\|" regexp)
              pystr)))
      regexp)))

(defun pyim-isearch-pinyin-search-function ()
  "这个函数为 isearch 相关命令添加中文拼音搜索功能，
用于 `isearch-search-fun-function' 。"
  (if pyim-isearch-enable-pinyin-search
      ;; Return the function to use for pinyin search
      `(lambda (string &optional bound noerror count)
         (funcall (if ,isearch-forward
                      're-search-forward
                    're-search-backward)
                  (pyim-isearch-build-search-regexp string) bound noerror count))
    ;; Return default function
    (isearch-search-fun-default)))

(setq isearch-search-fun-function 'pyim-isearch-pinyin-search-function)
;; #+END_SRC


;; * Footer
;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim-core)

;;; chinese-pyim-core.el ends here
;; #+END_SRC
