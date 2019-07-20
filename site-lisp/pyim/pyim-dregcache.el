;;; pyim-dregcache --- map dictionary to plain cache and use regular expression to search

;; * Header
;; Copyright 2019 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>

;; This file maps dictionary into plain memory. Regular expression is used to find words.

;;; Commentary:

;; * 说明文档                                                              :doc:
;; 这个文件将词典直接映射到内存.使用正则表达式(Regular Expression)搜索词库.
;; 搜索速度较快,消耗内存极少.
;;
;; 可以 (setq pyim-dcache-backend 'pyim-dregcache) 然后重启输入法启用此引擎

;;; Code:
;; * 代码                                                                 :code:
(require 'pyim-common)
(defvar pyim-dregcache-cache nil)
(defvar pyim-dregcache-icode2word nil)
(defvar pyim-dregcache-iword2count nil)
(defvar pyim-dregcache-dicts-md5 nil)

(defun pyim-dregcache-variable-file (variable)
  "Get VARIABLE dcache file path."
  (concat (file-name-as-directory pyim-dcache-directory)
          (symbol-name variable)))

(defun pyim-dregcache-save-variable (variable value)
  "Save VARIABLE with its VALUE."
  (let* ((file (pyim-dregcache-variable-file variable))
         (save-silently t))
    (make-directory (file-name-directory file) t)
    (with-temp-buffer
      (insert value)
      (pyim-dcache-write-file file))))

(defun pyim-dregcache-load-variable (variable)
  "载入 VARIABLE 对应的文件内容."
  (let* ((file (pyim-dregcache-variable-file variable)))
    (when (and file (file-exists-p file))
      (with-temp-buffer
        (insert-file-contents file)
        (buffer-string)))))

(defun pyim-dregcache-sort-icode2word ()
  "对个人词库排序."
  (setq pyim-dregcache-icode2word
        (sort pyim-dregcache-icode2word
              #'(lambda (a b)
                  (> (or (gethash (nth 1 (split-string a " "))
                                  pyim-dregcache-iword2count) 0)
                     (or (gethash (nth 1 (split-string b " "))
                                  pyim-dregcache-iword2count) 0))))))

(defun pyim-dregcache-create-cache-content (raw-content)
  "将 RAW-CONTENT 划分成可以更高效搜索的缓冲区."
  (let* (rlt)
    (cond
     ;; 小于1M的词库不用划分"子搜索区域"
     ((< (length raw-content) (* 1 1024 1024))
      (setq rlt (list :content raw-content)))
     (t
      (let* ((chars "bcdefghjklmnopqrstwxyz")
             pattern
             (i 0)
             (dict-sorted t)
             (content-segments '())
             (start 0)
             end)
        ;; 将字典缓存划分成多个"子搜索区域"
        (while (and dict-sorted (< i (length chars)))
          (setq pattern (concat "^" (string (elt chars i))))
          (setq end (string-match pattern raw-content start))
          (cond
           (end
            (setq content-segments
                  (add-to-list 'content-segments
                               (substring-no-properties raw-content start end)
                               t)))
           (t
            (setq dict-sorted nil)))
          (setq start end)
          (setq i (1+ i)))

        (cond
         ;; attach segments
         (dict-sorted
          (setq content-segments
                (add-to-list 'content-segments
                             (substring-no-properties raw-content start)
                             t))
          (setq rlt (list :content content-segments)))
         (t
          (setq rlt (list :content raw-content)))))))
    rlt))

(defun pyim-dregcache-load-dictionary-file (dict-file)
  "READ from DICT-FILE."
  (let* ((raw-content (with-temp-buffer
                        (insert-file-contents dict-file)
                        (buffer-string))))
    (setq pyim-dregcache-cache
          ;; use string type as key, so have to use `lax-plist-put'
          ;; @see https://www.gnu.org/software/emacs/manual/html_node/elisp/Plist-Access.html#Plist-Access
          (lax-plist-put pyim-dregcache-cache
                         (file-truename dict-file)
                         (pyim-dregcache-create-cache-content raw-content)))))

(defun pyim-dregcache-update:code2word (dict-files dicts-md5 &optional force)
  "读取并加载词库.

读取 `pyim-dicts' 和 `pyim-extra-dicts' 里面的词库文件，生成对应的
词库缓冲文件，然后加载词库缓存。

DICT-FILES 是词库文件列表. DICTS-MD5 是词库的MD5校验码.

如果 FORCE 为真，强制加载。"
  (interactive)
  (when (or force (not (equal dicts-md5 pyim-dregcache-dicts-md5)))
    ;; no hashtable i file mapping algorithm
    (dolist (file dict-files)
      (pyim-dregcache-load-dictionary-file file))
    (setq pyim-dregcache-dicts-md5 dicts-md5)))

(defmacro pyim-dregcache-shenmu2regexp (char)
  "将声母 CHAR 转换为通用正则表达式匹配所有以该声母开头的汉字."
  `(concat ,char "[a-z]*"))

(defmacro pyim-dregcache-is-shenmu (code)
  "判断CODE 是否是一个声母."
  `(and (eq (length ,code) 1)
        (not (string-match ,code "aeo"))))

(defun pyim-dregcache-code2regexp (code)
  "将 CODE 转换成正则表达式用来搜索辞典缓存中的匹配项目.
单个声母会匹配所有以此生母开头的单个汉字."
  (let* (arr)
    (cond
     ((pyim-dregcache-is-shenmu code)
      ;; 用户输入单个声母如 "w", "y", 将该声母转换为
      ;; 通用正则表达式匹配所有以该声母开头的汉字
      (pyim-dregcache-shenmu2regexp code))

     ((eq (length (setq arr (split-string code "-"))) 1)
      ;; 用户输入单个汉字的声母和韵母如 "wan", "dan", 不做任何处理
      code)

     (t
      ;; 用户输入多字词的code,如果某个字只提供了首个声母,将该声母转换为
      ;; 通用正则表达式匹配所有以该声母开头的汉字
      (let* ((s (mapconcat (lambda (e)
                             (if (pyim-dregcache-is-shenmu e)
                                 (pyim-dregcache-shenmu2regexp e)
                               e))
                           arr
                           "-")))
        ;; 当输入3字拼音时,也搜索前3字包含此拼音的更长的词.
        ;; 三字词很少(可 grep -rEsoh "^[a-z]+(-[a-z]+){2}( [^ ]+){2,6}" 验证)
        ;; 用户通常输入4字或更多字的词.
        ;; 例如符合 bei-jin-tian 的词很少, "北京天安门"是更可能匹配的词
        ;; `pyim-dregcache' 搜索算法可以保证更长的词在靠后的位置
        (cond
         ((< (length arr) 3)
          s)
         ((eq ?* (elt s (1- (length s))))
          ;; 简化正则表达式, tian-an-m[a-z]* => tian-an-m[a-z]?[a-z-]*
          (concat (substring s 0 (1- (length s))) "?[a-z-]*"))
         (t
          ;; tian-an-men => tian-an-men[a-z-]*
          (concat s "[a-z-]*"))))))))

(defmacro pyim-dregcache-match-line (code)
  `(concat "^" (pyim-dregcache-code2regexp ,code) " \\(.+\\)"))

(defun pyim-dregcache-all-dict-files ()
  "所有词典文件."
  (let* (rlt)
    (dolist (item pyim-dregcache-cache)
      (when (stringp item)
        (push item rlt)))
    rlt))

(defun pyim-dregcache-get-content (code file-info)
  "找到 CODE 对应的字典子缓冲区.  FILE-INFO 是字典文件的所有信息."
  (let* ((rlt (plist-get file-info :content))
         idx
         (ch (elt code 0)))
    (when (listp rlt)
      (cond
       ((<= ch ?h)
        (setq idx (- ch ?a)))
       ((<= ch ?t)
        ;; 'i' could not be first character of pinyin code
        (setq idx (- ch ?a 1)))
       (t
        ;; 'i', 'u', 'v' could not be first character of pinyin code
        (setq idx (- ch ?a 3))))
      ;; fetch segment using the first character of pinyin code
      (setq rlt (nth idx rlt)))
    rlt))

(defun pyim-dregcache-get (code &optional dcache-list)
  "从 `pyim-dregcache-cache' 搜索 CODE, 得到对应的词条.
DCACHE-LIST 只是符号而已,并不代表真实的缓存数据."
  (when pyim-dregcache-cache
    (let* ((pattern (pyim-dregcache-match-line code))
           (dict-files (pyim-dregcache-all-dict-files))
           result)
      (when pyim-debug (message "pyim-dregcache-get is called. code=%s pattern=%s dict-files=%s" code pattern dict-files))
      (dolist (file dict-files)
        (let* ((case-fold-search t)
               (start 0)
               (file-info (lax-plist-get pyim-dregcache-cache file))
               (content (pyim-dregcache-get-content code file-info))
               (content-size (length content))
               word)
          (while (and (< start content-size)
                      (setq start (string-match pattern content start)))
            ;; 提取词
            (setq word (match-string-no-properties 1 content))
            (cond
             ((string-match "^[^ ]+$" word)
              ;; 单个词
              (add-to-list 'result word t))
             (t
              ;; 多个字
              (setq result (append result (split-string word " +")))))
            ;; 继续搜索
            (setq start (+ start 2 (length code) (length word))))))
      `(,@result ,@(pyim-pinyin2cchar-get code t t)))))

(defun pyim-dregcache-update-personal-words (&optional force)
  "载入 `pyim-dregcache-icode2word' . 加载排序后的结果.

在这个过程中使用了 `pyim-dregcache-iword2count' 中记录的词频信息。
如果 FORCE 为真，强制排序"
  (let* ((content (pyim-dregcache-load-variable 'pyim-dregcache-icode2word))
         (lines (and content (split-string content "\n"))))
    (when (and lines (> (length lines) 0))
      (setq pyim-dregcache-icode2word
            ;; unique list
            (delq nil (delete-dups (append pyim-dregcache-icode2word lines)))))
    (when (and force pyim-dregcache-icode2word)
      (pyim-dregcache-sort-icode2word))))

(defun pyim-dregcache-update:shortcode2word (&optional restart)
  "Dummy function."
  )

(defun pyim-dregcache-init-variables ()
  "初始化 cache 缓存相关变量."
  ;; (pyim-dcache-set-variable 'pyim-dregcache-icode2word)
  (pyim-dcache-set-variable
   'pyim-dregcache-iword2count
   nil
   ;; dregcache 引擎也需要词频信息，第一次使用 dregcache 引擎的时候，
   ;; 自动导入 dhashcache 引擎的词频信息，以后两个引擎的词频信息就
   ;; 完全分开了。
   (let ((file (concat (file-name-as-directory pyim-dcache-directory)
                       "pyim-dhashcache-iword2count")))
     (pyim-dcache-get-value-from-file file))))

(defun pyim-dregcache-icode2word-formatted ()
  "个人词库格式化以便存入文件."
  (mapconcat 'identity pyim-dregcache-icode2word "\n"))

(defun pyim-dregcache-save-personal-dcache-to-file ()
  "保存缓存内容到默认目录."
  (when pyim-debug (message "pyim-dregcache-save-personal-dcache-to-file called"))
  ;; 用户选择过的词存为标准辞典格式保存
  (pyim-dregcache-save-variable 'pyim-dregcache-icode2word
                                (pyim-dregcache-icode2word-formatted))
  ;; 词频
  (pyim-dcache-save-variable 'pyim-dregcache-iword2count))

(defun pyim-dregcache-insert-export-content ()
  "TODO"
  )

(defun pyim-dregcache-put-iword2count (word &optional prepend wordcount-handler)
  "保存词频到缓存."
  (when pyim-debug (message "pyim-dregcache-put-iword2count. word=%s" word))
  (let* ((orig-value (gethash word pyim-dregcache-iword2count))
         (new-value (cond
                     ((functionp wordcount-handler)
                      (funcall wordcount-handler orig-value))
                     ((numberp wordcount-handler)
                      wordcount-handler)
                     (t (+ (or orig-value 0) 1)))))
    (unless (equal orig-value new-value)
      (puthash word new-value pyim-dregcache-iword2count))))

(defun pyim-dregcache-delete-word-1 (word)
  "TODO"
  )

(defun pyim-dregcache-insert-word-into-icode2word (word code prepend)
  "保存个人词到缓存."
  (when pyim-debug
    (message "pyim-dregcache-insert-word-into-icode2word called => %s %s %s"
             word
             code
             prepend))
  (let* ((cand (format "%s %s" code word)))
    (unless (member cand pyim-dregcache-icode2word)
      (add-to-list 'pyim-dregcache-icode2word
                   ;; 和其他词库缓存一行的格式一样以共享正则搜索算法
                   cand
                   (not prepend)))))

(defun pyim-dregcache-search-word-code (string)
  "TODO"
  )

(defun pyim-dregcache-get-code2word-shortcode2word (code)
  "以 CODE 搜索词和联想词.  正则表达式搜索词库,不需要为联想词开单独缓存."
  (when pyim-debug (message "pyim-dregcache-get-code2word-shortcode2word called => %s" code))
  (pyim-dregcache-get code))

(defun pyim-dregcache-get-code2word (code)
  "以 CODE 现有词库搜索词."
  (when pyim-debug (message "pyim-dregcache-get-code2word called => %s" code))
  (pyim-dregcache-get code))

(defun pyim-dregcache-get-icode2word-ishortcode2word (code)
  "以 CODE 搜索个人词和个人联想词.  正则表达式搜索词库,不需要为联想词开单独缓存."
  (when pyim-debug (message "pyim-dregcache-get-icode2word-ishortcode2word called => %s" code))
  (let* ((pattern (pyim-dregcache-match-line code))
         rlt)
    ;; pattern already matches BOTH code and shortcode
    (when pyim-dregcache-icode2word
      (dolist (line pyim-dregcache-icode2word)
        (when (string-match pattern line)
          (add-to-list 'rlt (nth 1 (split-string line " ")) t))))
    rlt))

(defun pyim-dregcache-get-icode2word (code)
  "以 CODE 搜索个人词.  正则表达式搜索词库,不需要为联想词开单独缓存."
  (when pyim-debug (message "pyim-dregcache-get-icode2word called => %s" code))
  (pyim-dregcache-get-icode2word-ishortcode2word code))

(defun pyim-dregcache-get-ishortcode2word (code)
  "以 CODE 搜索个人联想词.  正则表达式搜索词库,不需要为联想词开单独缓存."
  (when pyim-debug (message "pyim-dregcache-get-ishortcode2word called => %s" code))
  (pyim-dregcache-get-icode2word-ishortcode2word code))

(defun pyim-dregcache-export-personal-words (file &optional confirm)
  "将个人词库存入 FILE."
  (with-temp-buffer
    (insert (pyim-dregcache-icode2word-formatted))
    (pyim-dcache-write-file file confirm)))

;; * Footer

(provide 'pyim-dregcache)
;;; pyim-dregcache.el ends here
