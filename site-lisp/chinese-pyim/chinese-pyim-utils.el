;;; chinese-pyim-utils.el --- Useful tools which are based chinese-pyim

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
;; * 说明文档                                                              :doc:
;; 这个文件包含一些有用工具，这些工具都依赖 Chinese-pyim 的内部特性。

;; #+BEGIN_EXAMPLE
;; (require 'chinese-pyim-utils)
;; #+END_EXAMPLE

;;; Code:
;; * 代码                                                                 :code:
;; #+BEGIN_SRC emacs-lisp
(require 'cl-lib)
(require 'chinese-pyim-pymap)
(require 'chinese-pyim-core)


(defun pyim-forward-word (&optional arg)
  "向前移动 `arg' 英文或者中文词，向前移动时基于 *最长* 的词移动。"
  (interactive "P")
  (or arg (setq arg 1))
  (dotimes (i arg)
    (let* ((words (pyim-get-words-list-at-point t))
           (max-length
            (cl-reduce #'max
                       (cons 0 (mapcar #'(lambda (word)
                                           (nth 2 word))
                                       words))))
           (max-length (max (or max-length 1) 1)))
      (forward-char max-length))))

(defun pyim-backward-word (&optional arg)
  "向后移动 `arg' 个英文或者中文词，向后移动时基于 *最长* 的词移动。"
  (interactive "P")
  (or arg (setq arg 1))
  (dotimes (i arg)
    (let* ((words (pyim-get-words-list-at-point))
           (max-length
            (cl-reduce #'max
                       (cons 0 (mapcar #'(lambda (word)
                                           (nth 1 word))
                                       words))))
           (max-length (max (or max-length 1) 1)))
      (backward-char max-length))))

(defun pyim-get-words-list-at-point (&optional end-of-point)
  "获取光标当前的词条列表，当 `end-of-point' 设置为 t 时，获取光标后的词条列表。
词条列表的每一个元素都是列表，这些列表的第一个元素为词条，第二个元素为光标处到词条
头部的距离，第三个元素为光标处到词条尾部的距离。

其工作原理是：

1. 使用 `thing-at-point' 获取当前光标处的一个字符串，一般而言：英文会得到
   一个单词，中文会得到一个句子。
2. 英文单词直接返回这个单词的列表。
3. 中文句子首先用 `pyim-split-chinese-string' 分词，然后根据光标在中文句子
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

    ;; 当字符串长度太长时， `pyim-split-chinese-string'
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
            (pyim-split-chinese-string str))
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

(defun pyim-split-chinese-string (chinese-string &optional max-word-length)
  "一个基于 Chinese-pyim 的中文分词函数。这个函数可以将中文字符
串 `chinese-string' 分词，得到一个词条 alist，这个 alist 的元素
都是列表，其中第一个元素为分词得到的词条，第二个元素为词条相对于
字符串中的起始位置，第三个元素为结束位置。分词时，默认词条不超过
6个字符，用户可以通过 `max-word-length' 来自定义，但值得注意的是：
这个值设置越大，分词速度越慢。

注意事项：
1. 这个工具使用暴力匹配模式来分词，*不能检测出* Chinese-pyim 词库
   中不存在的中文词条。
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

    ;; 如果 Chinese-pyim 词库没有加载，加载 Chinese-pyim 词库，
    ;; 确保 pyim-get 可以正常运行。
    (unless pyim-buffer-list
      (setq pyim-buffer-list (pyim-load-file)))

    (let ((string-alist
           (get-possible-words
            (mapcar #'char-to-string
                    (string-to-vector chinese-string)) 1))
          words-list result)
      (dolist (string-list string-alist)
        (let ((pinyin-list (pyim-hanzi2pinyin (car string-list) nil "-" t)))
          (dolist (pinyin pinyin-list)
            (let ((words (pyim-get pinyin '(pinyin-dict)))) ; 忽略个人词库 buffer 可以提高速度
              (dolist (word words)
                (when (equal word (car string-list))
                  (push string-list result)))))))
      result)))

;; (let ((str "医生随时都有可能被患者及其家属反咬一口"))
;;   (benchmark 1 '(pyim-split-chinese-string str)))

;; (let ((str "医生随时都有可能被患者及其家属反咬一口"))
;;   (pyim-split-chinese-string str))

(defun pyim-split-chinese-string2string (string &optional prefer-short-word
                                                separator max-word-length)
  "将一个中文字符串分词，并且在分词的位置插入空格或者自定义分隔符 `separator'，
较长的词条优先使用，如果 `prefer-short-word' 设置为 t，则优先使用较短的词条。
最长词条默认不超过6个字符，用户可以通 `max-word-length' 来自定义词条的最大长度，
但值得注意的是，这个值设置越大，分词速度越慢。"
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
               (pyim-split-chinese-string2string-internal
                str prefer-short-word separator max-word-length)
             (concat " " str " "))))
     string-list "")))

(defun pyim-split-chinese-string2string-internal (chinese-string &optional prefer-short-word
                                                                 separator max-word-length)
  "`pyim-split-chinese-string2string' 内部函数。"
  (let ((str-length (length chinese-string))
        (word-list (cl-delete-duplicates
                    ;;  判断两个词条在字符串中的位置
                    ;;  是否冲突，如果冲突，仅保留一个，
                    ;;  删除其它。
                    (pyim-split-chinese-string chinese-string max-word-length)
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

(defun pyim-split-chinese-buffer ()
  "将一个 buffer 中的中文文章，进行分词操作。"
  (interactive)
  (message "分词开始！")
  (goto-char (point-min))
  (while (not (eobp))
    (let ((string (buffer-substring-no-properties
                   (line-beginning-position)
                   (line-end-position))))
      (pyim-delete-line)
      (insert (pyim-split-chinese-string2string string))
      (insert "\n")))
  (goto-char (point-min))
  (message "分词完成！"))

;; #+END_SRC

;; * Footer
;; #+BEGIN_SRC emacs-lisp
(provide 'chinese-pyim-utils)

;;; chinese-pyim-utils.el ends here
;; #+END_SRC
