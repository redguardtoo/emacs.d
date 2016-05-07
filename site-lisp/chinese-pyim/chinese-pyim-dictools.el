;;; chinese-pyim-dictools.el --- Tools for Chinese-pyim pinyin dict

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
;; 这个文件主要包含与词库文件管理相关的一些命令和函数，比如：
;; 1. 词库管理器
;; 2. 词库文件制作
;; 3. 词库文件更新
;; 4. 汉字转拼音
;; 5. 其它


;;; Code:

;; * 代码                                                                 :code:
;; ** Require
;; #+BEGIN_SRC emacs-lisp
(require 'cl-lib)
(require 'chinese-pyim-pymap)
(require 'chinese-pyim-core)
;; #+END_SRC

;; ** 汉字到拼音的转换工具
;; `pyim-hanzi2pinyin' 和 `pyim-hanzi2pinyin-simple' 可以将一个中文字符串转换为拼音字符串
;; 或者拼音列表，也可以将一个中文字符串转换为拼音首字母字符串或者首字母列表。

;; 在转换的过程中，`pyim-hanzi2pinyin' 考虑多音字，所以适用于制作词库，Chinese-pyim 使用
;; 这个函数来制作词库。而 `pyim-hanzi2pinyin-simple' 不考虑多音字，可以用于添加拼音索引。

;; 例如：
;; #+BEGIN_SRC emacs-lisp
;; (list (pyim-hanzi2pinyin "银行")
;;       (pyim-hanzi2pinyin "银行" t)
;;       (pyim-hanzi2pinyin "银行" nil "-")
;;       (pyim-hanzi2pinyin "银行" nil "-" t)
;;       (pyim-hanzi2pinyin "银行" t "-" t))
;; #+END_SRC

;; #+RESULTS:
;; : ("yinhang yinxing" "yh yx" "yin-hang yin-xing" ("yin-hang" "yin-xing") ("y-h" "y-x"))

;; #+BEGIN_SRC emacs-lisp
;; (list (pyim-hanzi2pinyin-simple "行长")
;;       (pyim-hanzi2pinyin-simple "行长" t)
;;       (pyim-hanzi2pinyin-simple "行长" nil "-")
;;       (pyim-hanzi2pinyin-simple "行长" nil "-" t)
;;       (pyim-hanzi2pinyin-simple "行长" t "-" t))
;; #+END_SRC

;; #+RESULTS:
;; : ("hangchang" "hc" "hang-chang" ("hang-chang") ("h-c"))


;; `pyim-hanzi2pinyin' 函数使用 “排列组合” 函数 `pyim-permutate-list' 来处理多音字，
;; 这个函数所做工作类似：

;; #+BEGIN_EXAMPLE
;; (cl-prettyprint
;;  (pyim-permutate-list
;;   '(("a" "b")
;;     ("c" "d")
;;     ("e" "f" "g"))))

;; OUTPUT:

;; (("a" "c" "e")
;;  ("a" "c" "f")
;;  ("a" "c" "g")
;;  ("a" "d" "e")
;;  ("a" "d" "f")
;;  ("a" "d" "g")
;;  ("b" "c" "e")
;;  ("b" "c" "f")
;;  ("b" "c" "g")
;;  ("b" "d" "e")
;;  ("b" "d" "f")
;;  ("b" "d" "g"))
;; #+END_EXAMPLE


;; #+BEGIN_SRC emacs-lisp
;;;###autoload
(defun pyim-hanzi2pinyin (string &optional shou-zi-mu separator
                                 return-list ignore-duo-yin-zi adjuct-duo-yin-zi)
  "将汉字字符串转换为对应的拼音字符串, 如果 `shou-zi-mu' 设置为t,转换仅得到拼音
首字母字符串。当 `return-list' 设置为 t 时，返回一个拼音列表，这个列表包含词条的一个
或者多个拼音（词条包含多音字时）；如果 `ignore-duo-yin-zi' 设置为t, 遇到多音字时，
只使用第一个拼音，其它拼音忽略；当 `adjuct-duo-yin-zi' 设置为t时，pyim-hanzi2pinyin
会使用 Chinese-pyim 已安装的词库来校正多音字，但这个功能有一定的限制:

1. Chinese-pyim 普通词库中不存在的词条不能较正
2. 多音字校正速度比较慢，实时转换会产生卡顿。

BUG: 当 `string' 中包含其它标点符号，并且设置 `separator' 时，结果会包含多余的连接符：
比如： '你=好' --> 'ni-=-hao'"
  (if (not (pyim-string-match-p "\\cc" string))
      string
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

      ;; 使用 Chinese-pyim 的安装的词库来校正多音字。
      (when adjuct-duo-yin-zi
        (unless pyim-buffer-list ;确保 pyim-get 可以正常运行
          (setq pyim-buffer-list (pyim-load-file)))
        (dolist (pinyin-list pinyins-list-permutated)
          (let* ((py-str (mapconcat #'identity pinyin-list "-"))
                 (words-from-dicts
                  ;; pyim-buffer-list 中第一个 buffer 对应的是个人词库文件
                  ;; 个人词库文件中的词条，极有可能存在 *多音字污染*。
                  ;; 这是由 Chinese-pyim 保存词条的机制决定的。
                  (pyim-get py-str '(pinyin-dict))))
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
  "使用排列组合的方式重新排列 `list'，这个函数由 ‘二中’ 提供。
注：`pyim-hanzi2pinyin' 没有使用这个函数(速度稍微有点慢)。"
  (let ((list-head (car list))
        (list-tail (cdr list)))
    (cond ((null list-tail)
           (cl-loop for element0 in list-head
                    append (cons (cons element0 nil) nil)))
          (t (cl-loop for element in list-head
                      append (mapcar (lambda (l) (cons element l))
                                     (pyim-permutate-list list-tail)))))))

(defun pyim-permutate-list2 (list)
  "使用排列组合的方式重新排列 `list'，这个函数由 ’翀/ty‘ 提供。
`pyim-hanzi2pinyin' 默认使用这个函数。"
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
;; #+END_SRC

;; ** 词库文件生成工具
;; #+BEGIN_SRC emacs-lisp
(defun pyim-sort-by-freq (words-list)
  "按照词条出现频率对词条列表排序，频率高词条的排在最前面。"
  (let ((count-table (make-hash-table :test #'equal)))
    (dolist (x words-list)
      (let ((value (gethash x count-table)))
        (if value
            (puthash x (1+ value) count-table)
          (puthash x 1 count-table))))
    (sort words-list (lambda (a b) (> (gethash a count-table)
                                      (gethash b count-table))))))

(defun pyim-remove-duplicates-word (&optional sort-by-freq)
  "制作拼音词库时，删除当前行重复出现的词条，
当 `sort-by-freq' 为 t 时，首先按照当前行词条出现频率对词条排序，
然后再删除重复词条，用于：从中文文章构建词库。"
  (interactive)
  (let* ((line-content (pyim-line-content " "))
         (code (car line-content)) ;; 编码和词条分开操作，因为在guessdict词库中，编码是中文。
         (words-list (cdr line-content))
         (length (length words-list)))
    ;; 从文章中构建词库时，首先会将词条按照出现频率
    ;; 排序，这样频率高的词条就会排在前面。
    (when sort-by-freq
      (setq words-list
            (pyim-sort-by-freq words-list)))

    ;; 删除重复词条的时候，要注意删除顺序。
    (setq words-list
          (cl-delete-duplicates
           words-list
           :test #'equal :from-end t))

    (when (> length (length words-list))
      (pyim-delete-line)
      (insert code)
      (insert " ")
      (insert (mapconcat 'identity words-list " "))
      (insert "\n")
      (goto-char (line-beginning-position)))))

;;;###autoload
(defun pyim-update-dict-file (&optional force sort-by-freq)
  "手动调整 Chinese-pyim 词库文件后，执行此命令可以：
1. 按照每行拼音对文件进行排序。
2. 删除重复的词条。

当我们明确无误的知道此命令的使用条件已经符合时。可以将 `force' 设置
为 t ，此时，就不需要用户进一步确认是否执行此命令。

当 `sort-by-freq' 设置位 t 时，删除每一行的重复词条之前，首先将词条按照
词条出现的频率大小排序，这个选项适用于：从文章构建词库，文章中词条出现
频率可以代表此词条的使用频率。"
  (interactive)
  (when (or force
            (yes-or-no-p "注意：当前 buffer *必须* 为词库文件 buffer，是否继续？"))
    (save-restriction
      (let ((lastw "")
            first-char total-char currw)
        (goto-char (point-min))
        (perform-replace "[ \t]+$" "" nil t nil nil nil (point-min) (point-max))
        (pyim-sort-dict-region (point-min)
                               (point-max))

        (goto-char (point-min))
        (while (not (eobp))
          (let* ((line-content (pyim-line-content))
                 (length (length line-content)))
            (if (or (> length 1) ;; 删除只包含 code，但没有词条的行
                    (pyim-string-match-p " *^;+" (car line-content)))
                (forward-line 1)
              (pyim-delete-line))))

        (goto-char (point-min))
        (while (not (eobp))
          (if (looking-at "^[ \t]*$")     ; 如果有空行，删除
              (pyim-delete-line)
            (setq currw (pyim-code-at-point))
            (if (equal currw lastw)
                (delete-region (1- (point)) (+ (point) (length currw))))
            (setq lastw currw)
            (forward-line 1)))

        (goto-char (point-min))
        (while (not (eobp))
          (pyim-remove-duplicates-word sort-by-freq)
          (forward-line 1))
        (if (looking-at "^$")
            (delete-char -1))))))

(defun pyim-sort-dict-region (start end)
  "将词库 buffer 中 `start' 和 `end' 范围内的词条信息按照拼音code排序
当 unix 工具 sort 存在时，优先使用这个工具，否则使用emacs自带函数
`sort-regexp-fields'。"
  (if (and (eq system-type 'gnu/linux)
           (executable-find "sort")
           (executable-find "env"))
      (call-process-region start end
                           "env" t t nil "LC_ALL=C"
                           "sort" "-k1,1" "-s")
    (sort-regexp-fields nil "^.*$" "[a-z-]+[ ]+" start end)))

(defun pyim-convert-current-line-to-dict-format ()
  "将当前行对应的汉语词条转换为 Chinese-pyim 可以识别的词库格式（ni-hao 你好）。"
  (interactive)
  (let (line-content pinyin-list insert-string)
    (setq line-content
          (buffer-substring-no-properties
           (line-beginning-position) (line-end-position)))
    (setq line-content
          (replace-regexp-in-string
           "^ +\\| +$" "" line-content))
    (setq pinyin-list
          (pyim-hanzi2pinyin
           (car (split-string line-content)) nil "-" t))
    (delete-region (line-beginning-position) (line-end-position))
    (setq insert-string
          (mapconcat
           #'(lambda (x)
               ;; 拼音中不能有中文字符。
               ;; 中文词条中必须有中文字符，并且不能有ascii字符。
               (unless (or (pyim-string-match-p "[^a-z-]" x)
                           (pyim-string-match-p "[:ascii:]" line-content)
                           (not (pyim-string-match-p "\\cc" line-content)))
                 (format "%s  %s" x line-content)))
           pinyin-list "\n"))
    (when (> (length insert-string) 1)
      (insert insert-string))))

;;                          (("a" "b")
;;                           ("b" "c")
;; ("a" "b" "c" "d" "e") ->  ("c" "d")
;;                           ("d" "e")
;;                           ("e" nil))
(defun pyim-guessdict-list-convert (my-list)
  (cond
   ((null my-list) nil)
   ((atom my-list) (list my-list))
   (t (append (list (list (car my-list) (car (cdr my-list))))
              (pyim-guessdict-list-convert (cdr my-list))))))

;;                      你好 天空
;; "你好 天空 大地" ->  天空 大地
;;                      大地
(defun pyim-convert-current-line-to-guessdict-format ()
  (interactive)
  (let* ((string (mapconcat
                  #'(lambda (x)
                      (let ((pinyin-list (pyim-hanzi2pinyin
                                          (car x) nil "-" t)))
                        (mapconcat
                         #'(lambda (pinyin)
                             (concat pinyin "  " (mapconcat #'identity x " ")))
                         pinyin-list "\n")))
                  (pyim-guessdict-list-convert (pyim-line-content nil t))
                  "\n")))
    (delete-region (line-beginning-position) (line-end-position))
    (insert string)))

;;;###autoload
(defun pyim-article2dict-chars ()
  "将一篇中文文章转换为 Chinese-pyim 可以识别的拼音词库。
这个命令只将文章中 *非词语* 中文字符转化为词库。

这个命令可以得到一篇文章中常用单字词语的词频信息。"
  (interactive)
  (pyim-article2dict 'chars))

;;;###autoload
(defun pyim-article2dict-words ()
  "将一篇中文文章转换为 Chinese-pyim 可以识别的拼音词库。
这个命令将文章中 *正确词语*，转化为词库。

这个命令使用频率很低，原因有两点：
1. 寻找准确的中文词条非常容易，一般不需要从一篇文章中通过分词的手段获得。
2. 文章很大时，这个命令运行速度太慢。

这个命令最大的用途就是为没有拼音的中文词库添加拼音code。"
  (interactive)
  (pyim-article2dict 'words))

;;;###autoload
(defun pyim-article2dict-misspell-words ()
  "将一篇中文文章转换为 Chinese-pyim 可以识别的拼音词库。
这个命令将文章中 *连续出现的独立汉字* 组合成中文字符串，
然后将其转化为词库，例如：

   “哪  狗  天”

会被转换为：

   “哪狗天”

有一句话说：“对的都一样，错的万万千”，对用户来说，这个命令可能
最有用处，它可以增加许多新词，也许这些新词毫无意义，但其代表了一种
输入习惯，可以提高输入体验。"
  (interactive)
  (pyim-article2dict 'misspell-words))

;;;###autoload
(defun pyim-article2dict-guessdict ()
  "将一篇中文文章转换为 Chinese-pyim 可以识别的 guessdict。

Guessdict 词库是 Chinese-pyim 用于词语联想的一种词库，其结构与普通词库
类似，唯一不同的是，guessdict 词库的 code 是中文，而不是拼音，例如：

   我爱 北京 美女 旅游
   我们 去哪 去看海

Guessdict 用来保存，一个中文词条（code）后面经常跟随出现的词条。当用户输入
前一次输入：我爱，再输入拼音 lv 时，Chinese-pyim 会匹配词条： 旅游。这样就
可以降低用户翻页的频率不同。"
  (interactive)
  (pyim-article2dict 'guessdict))

(defun pyim-article2dict (object)
  "将一篇中文文章转换为 Chinese-pyim 可以识别的拼音词库。
其步骤为：
1. 清除所有非汉语内容。
2. 使用分词系统将文章分词。
3. 将词条与词条之间用换行符分开（对于普通词库）。
4. 为每一行的词条添加拼音（对于普通词库）。"
  (save-excursion
    (pyim-show-help
     "将一篇中文文章转换为 Chinese-pyim 可以识别的拼音词库。
1. 准备材料：准备好所需要的中文文章，比如：一本网络小说，将其转换为文本文件。
2. 分词处理：使用分词工具将上述文件中的中文词语用空格分开，这里只介绍（jieba）结巴分词工具。
   1. 安装教程请参考： https://github.com/fxsjy/jieba
   2. 使用命令： python -m jieba -d \" \" 源文件.txt  > 目标文件.txt
   3. 命令帮助： python -m jieba --help
   注意：如果词条已经使用 *空格* 或者 *换行符* 隔开，可以跳过 “分词处理” 这一步。
3. 添加拼音：运行下面4个命令
   1. `pyim-article2dict-chars'
   2. `pyim-article2dict-words'
   3. `pyim-article2dict-misspell-words'
   3. `pyim-article2dict-guessdict'
4. 保存文件

另外，使用分词工具的目的是确保中文词语与词语之间用 *空格* 强制隔开。比如：

    \"你好 吃饭 中文\"

分词这个步骤不是必须步骤，如果你获得的文件已经满足上述条件，那么直接运行当前命令就可以了。

注意事项：当文件很大时，这个命令需要执行较长时间，据估计：生成5万词条的词库大约需要15分钟。"))
  (when (yes-or-no-p "您上述准备工作是否已经完成？如果完成，请输入 yes 继续执行命令：")
    (let ((file (read-file-name "请选择需要转换的文本文件：")))
      (with-temp-buffer
        (insert-file-contents file)
        ;; 删除所有英文单词以及标点符号。
        (goto-char (point-min))
        (while (re-search-forward "[[:punct:]a-zA-Z0-9]+" nil t)
          (replace-match "\n"))
        ;; 当 `accuracy' 为 nil 时，`pyim-article2dict' 会将连续出现的
        ;; 单个汉字字符合并成汉字字符串，比如： “哪  狗  天” 会被转换
        ;; 为 “哪狗天”。增加词条量的同时也会产生许多无意义的词汇。
        (cond ((eq object 'chars)
               (goto-char (point-min))
               (while (re-search-forward "\\cc\\cc+" nil t)
                 (replace-match ""))
               ;; 将词条使用换行符隔开。
               (goto-char (point-min))
               (while (re-search-forward "[[:blank:]]+" nil t)
                 (replace-match "\n")))
              ((eq object 'words)
               (goto-char (point-min))
               ;; 删除所有单个汉字字符，单个汉字字符的拼音词库非常容易获得。
               ;; 将其删除后，将极大的减少词库转换时间。
               (while (re-search-forward "\\CC\\cc\\CC" nil t)
                 (replace-match "\n"))
               ;; 将词条使用换行符隔开。
               (goto-char (point-min))
               (while (re-search-forward "[[:blank:]]+" nil t)
                 (replace-match "\n"))
               (goto-char (point-min))
               (while (re-search-forward "\n\\cc\n" nil t)
                 (replace-match "\n")))
              ((eq object 'misspell-words)
               (goto-char (point-min))
               ;; 删除现有词条，只保留单个汉语字符，将单个的汉语字符
               ;; 组成字符串后，有可能得到新的词语，虽然这些词语可能
               ;; 没有实际意义，但可以提升拼音输入法的体验。
               (while (re-search-forward "\\cc\\cc+" nil t)
                 (replace-match "\n"))
               (goto-char (point-min))
               (while (re-search-forward "[[:blank:]]+" nil t)
                 (replace-match ""))
               (goto-char (point-min))
               (while (re-search-forward "[[:blank:]\n]+\\cc[[:blank:]\n]+" nil t)
                 (replace-match ""))
               (goto-char (point-min))
               ;; 删除大于4个字符的中文字符串，没什么用处。
               (while (re-search-forward "\\cc\\{5,\\}" nil t)
                 (replace-match "\n")))
              ((eq object 'guessdict) t))
        ;; 删除多余空白行。
        (goto-char (point-min))
        (while (re-search-forward "\n+" nil t)
          (replace-match "\n"))
        ;; `pyim-article2dict' 处理大文件时运行时间很长
        ;; 分阶段保存内容可以防止数据丢失。
        (pyim-article2dict-write-stage-file file "CleanStage-" t)
        ;; 为每一行的词条添加拼音code
        (goto-char (point-min))
        (while (not (eobp))
          (if (eq object 'guessdict)
              (pyim-convert-current-line-to-guessdict-format)
            (pyim-convert-current-line-to-dict-format))
          (forward-line 1))
        (pyim-article2dict-write-stage-file file "ConvertStage-" t)
        ;; 将文件按行排序，并删除重复的词条，运行两次。
        (pyim-update-dict-file t t)
        (pyim-article2dict-write-stage-file file "SortStage-" t)
        (pyim-update-dict-file t t)
        (pyim-article2dict-write-stage-file file "FinishStage-" t)))))

(defun pyim-article2dict-write-stage-file (file stage force)
  "将当前 buffer 的内容另存为一个 stage 文件。
用于 `pyim-article2dict' 分阶段保存内容。"
  (let ((file (expand-file-name file))
        stage-file)
    (when (and file stage force)
      (setq stage-file
            (concat (file-name-directory file)
                    (make-temp-name stage) "-"
                    (file-name-nondirectory file)))
      (write-region (point-min) (point-max) stage-file)
      (message "将此阶段转换的结果另存为文件：%s" stage-file))))
;; #+END_SRC

;; ** Chinese-pyim 词库管理工具
;; 为 Chinese-pyim 添加一个简单的词库管理工具 `pyim-dicts-manager' ，可以方便的执行下列命令：
;; 1. 添加词库。
;; 2. 删除词库。
;; 3. 向上和向下移动词库。
;; 4. 保存词库设置。
;; 5. 重启输入法。

;; #+BEGIN_SRC emacs-lisp
(defvar pyim-dicts-manager-buffer-name "*pyim-dict-manager*")
(defvar pyim-dicts-manager-scel2pyim-command "scel2pyim" "设置 scel2pyim 命令")

(defun pyim-dicts-manager-refresh ()
  "Refresh the contents of the *pyim-dict-manager* buffer."
  (interactive)
  (with-current-buffer pyim-dicts-manager-buffer-name
    (let ((inhibit-read-only t)
          (dicts-list pyim-dicts)
          (format-string "%-4s %-4s %-11s %-25s %-60s %-4s\n")
          (face-attr '((foreground-color . "DarkOrange2")
                       (bold . t)))
          (i 1))
      (erase-buffer)
      (insert (propertize (format format-string "序号" "启用" "Coding"    "词库名称" "词库文件" "词库类型")
                          'face face-attr))
      (insert (propertize (format format-string
                                  "----" "----" "----------"
                                  "---------------"
                                  "------------------------------------------"
                                  "--------------\n")
                          'face face-attr))
      (if (not pyim-dicts)
          (insert "拼音词库是 Chinese-pyim 使用顺手与否的关键。根据经验估计：

1. 当词库词条超过100万时 (词库文件>20M)，Chinese-pyim 选词频率大大降低。
2. 当词库词条超过100万时，Chinese-pyim 中文输入体验可以达到搜狗输入法的80%。

想快速体验 Chinese-pyim 输入法的用户可以使用词库导入命令下载安装样例词库
或者导入搜狗输入法词库。

喜欢折腾的用户可以从下面几个途径获得 Chinese-pyim 更详细的信息。
1. 使用 `C-h v pyim-dicts' 了解 `Chinese-pyim' 词库文件格式。
2. 了解如何导入其它输入法的词库。
   1. 使用 package 管理器查看 Chinese-pyim 包的简介
   2. 阅读 chinese-pyim.el 文件 Commentary
   3. 查看 Chinese-pyim 在线 README：https://github.com/tumashu/chinese-pyim\n")
        (dolist (dict dicts-list)
          (let ((disable (plist-get dict :disable))
                (name (plist-get dict :name))
                (file (plist-get dict :file))
                (coding (plist-get dict :coding))
                (dict-type (plist-get dict :dict-type)))
            (insert (propertize (format format-string i
                                        (if disable "no" "yes")
                                        coding name file dict-type)
                                'id i 'disable disable 'name name 'file file 'coding coding dict-type 'dict-type)))
          (setq i (1+ i))))
      (insert (propertize "
操作命令：[A] 添加词库  [D] 删除词库   [P] 向上移动   [N] 向下移动  [g] 刷新页面
          [s] 保存配置  [R] 重启输入法 [C-c C-c] 禁用/启用当前词库
          [M] 将所有的词库文件合并为一个词库文件

词库导入：[i e] 下载并安装样例词库(用于测试)
          [i f] 导入一个搜狗输入法词库
          [i d] 导入一个目录中所有的搜狗输入法词库"
                          'face face-attr)))))

(defun pyim-dicts-manager-toggle-enable-dict (&optional enable)
  "启用当前行对应的词库。"
  (interactive)
  (when (equal (buffer-name) pyim-dicts-manager-buffer-name)
    (let* ((id (get-text-property (point) 'id))
           (disable (get-text-property (point) 'disable))
           (dict (cl-copy-list (nth (1- id) pyim-dicts)))
           (disable (plist-get dict :disable))
           (line (line-number-at-pos)))
      (setf (nth (1- id) pyim-dicts) (plist-put dict :disable (not disable)))
      (if (not disable)
          (message "禁用当前词库")
        (message "启用当前词库"))
      (pyim-dicts-manager-refresh)
      (goto-char (point-min))
      (forward-line (- line 1)))))

(defun pyim-dicts-manager-delete-dict ()
  "从 `pyim-dicts' 中删除当前行对应的词库信息。"
  (interactive)
  (when (equal (buffer-name) pyim-dicts-manager-buffer-name)
    (let ((id (get-text-property (point) 'id))
          (file (get-text-property (point) 'file))
          (line (line-number-at-pos)))
      (when (yes-or-no-p "确定要删除这条词库信息吗? ")
        (setq pyim-dicts (delq (nth (1- id) pyim-dicts) pyim-dicts))
        (when (and (file-exists-p file)
                   (yes-or-no-p "确定要删除对应的词库文件吗？"))
          (delete-file file))
        (pyim-dicts-manager-refresh)
        (goto-char (point-min))
        (forward-line (- line 1))))))

(defun pyim-dicts-manager-dict-position-up ()
  "向上移动词库。"
  (interactive)
  (when (equal (buffer-name) pyim-dicts-manager-buffer-name)
    (let* ((id (get-text-property (point) 'id))
           (dict1 (nth (- id 1) pyim-dicts))
           (dict2 (nth (- id 2) pyim-dicts))
           (length (length pyim-dicts))
           (line (line-number-at-pos)))
      (when (> id 1)
        (setf (nth (- id 1) pyim-dicts) dict2)
        (setf (nth (- id 2) pyim-dicts) dict1)
        (pyim-dicts-manager-refresh)
        (goto-char (point-min))
        (forward-line (- line 2))))))

(defun pyim-dicts-manager-dict-position-down ()
  "向下移动词库。"
  (interactive)
  (when (equal (buffer-name) pyim-dicts-manager-buffer-name)
    (let* ((id (get-text-property (point) 'id))
           (dict1 (nth (- id 1) pyim-dicts))
           (dict2 (nth id pyim-dicts))
           (length (length pyim-dicts))
           (line (line-number-at-pos)))
      (when (< id length)
        (setf (nth (1- id) pyim-dicts) dict2)
        (setf (nth id pyim-dicts) dict1)
        (pyim-dicts-manager-refresh)
        (goto-char (point-min))
        (forward-line line)))))

(defun pyim-dicts-manager-save-dict-info ()
  "使用 `customize-save-variable' 函数将 `pyim-dicts' 保存到 ~/.emacs 文件中。"
  (interactive)
  ;; 将`pyim-dict'的设置保存到emacs配置文件中。
  (customize-save-variable 'pyim-dicts pyim-dicts)
  (message "将 Chinese-pyim 词库配置信息保存到 ~/.emacs 文件。"))

(defun pyim-dicts-manager-import-sogou-dict-directory ()
  "导入某个目录中所有搜狗细胞词库的命令。"
  (interactive)
  (when (equal (buffer-name) pyim-dicts-manager-buffer-name)
    (let* ((line (line-number-at-pos))
           (dir (read-directory-name "请选择搜狗细胞词库所在的目录： " "~/"))
           (files (directory-files dir t ".*\\.scel")))
      (dolist (file files)
        (pyim-dicts-manager-import-sogou-dict-file-1 file))
      (pyim-dicts-manager-refresh)
      (goto-char (point-min))
      (forward-line (- line 1)))))

(defun pyim-dicts-manager-import-sogou-dict-file ()
  "导入搜狗细胞词库文件的命令"
  (interactive)
  (when (equal (buffer-name) pyim-dicts-manager-buffer-name)
    (let ((line (line-number-at-pos))
          (file (read-file-name "请选择需要导入的搜狗细胞词库文件： " "~/")))
      (pyim-dicts-manager-import-sogou-dict-file-1 file)
      (pyim-dicts-manager-refresh)
      (goto-char (point-min))
      (forward-line (- line 1)))))

(defun pyim-dicts-manager-import-sogou-dict-file-1 (file)
  (let* ((input-file (expand-file-name file))
         (input-filename (file-name-base input-file))
         (output-file (expand-file-name
                       (concat (file-name-as-directory
                                pyim-dicts-directory)
                               input-filename ".pyim"))))
    (if (not (pyim-dict-file-available-p output-file))
        (if (and (call-process pyim-dicts-manager-scel2pyim-command
                               nil "*pyim-dicts-import*" nil input-file output-file)
                 (file-exists-p output-file))
            (add-to-list 'pyim-dicts
                         `(:name ,input-filename :file ,output-file :coding utf-8 :dict-type pinyin-dict) t)
          (message "搜狗词库文件：%s 转换失败。" input-file))
      (message "这个词库文件似乎已经导入。"))))

(defun pyim-dicts-manager-add-dict ()
  "为 `pyim-dicts' 添加词库信息。"
  (interactive)
  (when (equal (buffer-name) pyim-dicts-manager-buffer-name)
    (let ((line (line-number-at-pos))
          dict name file coding first-used dict-type)
      (setq name (read-from-minibuffer "请输入词库名称： "))
      (setq file (read-file-name "请选择词库文件： " "~/"))
      (setq coding (completing-read "词库文件编码: "
                                    '("utf-8-unix" "cjk-dos" "gb18030-dos")
                                    nil t nil nil "utf-8-unix"))
      (setq dict-type (completing-read "词库类型: "
                                       '("pinyin-dict" "guess-dict")
                                       nil t nil nil "pinyin-dict"))
      (setq first-used  (yes-or-no-p "是否让 Chinese-pyim 优先使用词库？ "))
      (setq dict `(:name ,name
                         :file ,file
                         :coding ,(intern coding)
                         :dict-type ,(intern dict-type)))
      (if first-used
          (add-to-list 'pyim-dicts dict)
        (add-to-list 'pyim-dicts dict t))
      (pyim-dicts-manager-refresh)
      (goto-char (point-min))
      (forward-line (- line 1)))))

(defun pyim-dicts-manager-add-example-dict ()
  "下载并安装用于测试目的的样例词库。"
  (interactive)
  (when (equal (buffer-name) pyim-dicts-manager-buffer-name)
    (let ((dict-name "BigDict-01")
          (dict-url "http://tumashu.github.io/chinese-pyim-bigdict/pyim-bigdict.pyim")
          (dict-file (expand-file-name
                      (concat (file-name-as-directory
                               pyim-dicts-directory)
                              "pyim-bigdict.pyim"))))
      (when (yes-or-no-p (format "从网址 (%s) 下载安装样例词库？ " dict-url))
        (unless (file-exists-p dict-file)
          (url-copy-file dict-url dict-file))
        (when (and (file-exists-p dict-file)
                   (not (pyim-dict-file-available-p dict-file)))
          (add-to-list 'pyim-dicts
                       `(:name ,dict-name
                               :file ,dict-file
                               :coding utf-8-unix
                               :dict-type pinyin-dict) t))
        (pyim-dicts-manager-refresh)))))

(defun pyim-dicts-manager-merge-all ()
  "将词库管理器中所有词库合并，并添加生成的词库文件。
词库合并可以优化 Chinese-pyim 的速度。"
  (interactive)
  (let ((dicts-list pyim-dicts)
        (dict-name "Dicts-Merged")
        (buffer (get-buffer-create "*pyim-merged-dict*"))
        (dict-file (expand-file-name
                    (concat (file-name-as-directory
                             pyim-dicts-directory)
                            "pyim-dicts-merged.pyim")))
        file coding disable dict-type)
    (when (and dicts-list (yes-or-no-p "确定将所有词库合并为一个词库吗? "))
      (dolist (dict dicts-list)
        (setq file (expand-file-name (plist-get dict :file)))
        (setq coding (plist-get dict :coding))
        (setq disable (plist-get dict :disable))
        (setq dict-type (plist-get dict :dict-type))
        (if (and (not disable)
                 (eq dict-type 'dict)
                 (file-exists-p file))
            (with-current-buffer buffer
              (if coding
                  (let ((coding-system-for-read coding))
                    (insert-file-contents file))
                (insert-file-contents file))
              (goto-char (point-max))
              (insert "\n"))))

      (with-current-buffer buffer
        (goto-char (point-min))
        (while (re-search-forward "^;+.*coding:.*" nil t)
          (replace-match "" nil t))
        (goto-char (point-min))
        (pyim-update-dict-file t)
        (goto-char (point-min))
        (pyim-update-dict-file t)
        (goto-char (point-min))
        (insert";; -*- coding: utf-8 -*-\n")
        (write-file dict-file)
        (kill-buffer))

      (setq pyim-dicts
            `((:name ,dict-name
                     :file ,dict-file
                     :coding utf-8-unix
                     :dict-type dict)))
      (pyim-dicts-manager-refresh))))

(define-derived-mode pyim-dicts-manager-mode special-mode "pyim-dicts-manager"
  "Major mode for managing Chinese-pyim dicts"
  (read-only-mode)
  (define-key pyim-dicts-manager-mode-map (kbd "D") 'pyim-dicts-manager-delete-dict)
  (define-key pyim-dicts-manager-mode-map (kbd "g") 'pyim-dicts-manager-refresh)
  (define-key pyim-dicts-manager-mode-map (kbd "A") 'pyim-dicts-manager-add-dict)
  (define-key pyim-dicts-manager-mode-map (kbd "i f") 'pyim-dicts-manager-import-sogou-dict-file)
  (define-key pyim-dicts-manager-mode-map (kbd "i d") 'pyim-dicts-manager-import-sogou-dict-directory)
  (define-key pyim-dicts-manager-mode-map (kbd "i e") 'pyim-dicts-manager-add-example-dict)
  (define-key pyim-dicts-manager-mode-map (kbd "N") 'pyim-dicts-manager-dict-position-down)
  (define-key pyim-dicts-manager-mode-map (kbd "P") 'pyim-dicts-manager-dict-position-up)
  (define-key pyim-dicts-manager-mode-map (kbd "s") 'pyim-dicts-manager-save-dict-info)
  (define-key pyim-dicts-manager-mode-map (kbd "C-c C-c") 'pyim-dicts-manager-toggle-enable-dict)
  (define-key pyim-dicts-manager-mode-map (kbd "R") 'pyim-restart)
  (define-key pyim-dicts-manager-mode-map (kbd "M") 'pyim-dicts-manager-merge-all))

;;;###autoload
(defun pyim-dicts-manager ()
  "Chinese-pyim 词库管理器。"
  (interactive)
  (unless (file-exists-p pyim-dicts-directory)
    (make-directory pyim-dicts-directory t))
  (let ((buffer (get-buffer-create pyim-dicts-manager-buffer-name)))
    (pyim-dicts-manager-refresh)
    (switch-to-buffer buffer)
    (pyim-dicts-manager-mode)
    (setq truncate-lines t)))
;; #+END_SRC

;; ** TODO 词库 package 制作工具
;; 每一个流行的拼音输入法制定了自己的词库包格式，比如：搜狗拼音输入法的细胞词库，QQ输入法的QQ词库等，
;; Chinese-pyim 打算使用 emacs package 来分发词库包。

;; #+BEGIN_SRC emacs-lisp
(defun pyim-dict-name-available-p (dict-name)
  "查询 `pyim-dicts' 中 `:name' 为 `dict-name' 的词库信息是否存在。
  这个函数主要用于词库 package。"
  (cl-some (lambda (x)
             (let ((name (plist-get x :name)))
               (equal name dict-name)))
           pyim-dicts))

(defun pyim-dict-file-available-p (dict-file)
  "查询 `pyim-dicts' 中 `:file' 为 `dict-file' 的词库信息是否存在。
  这个函数主要用于词库 package。"
  (cl-some (lambda (x)
             (let ((file (plist-get x :file)))
               (equal (expand-file-name file)
                      (expand-file-name dict-file))))
           pyim-dicts))
;; #+END_SRC

;; * Footer
;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim-dictools)

;;; chinese-pyim-dictools.el ends here
;; #+END_SRC
