(defcustom pyim-hashtable-directory (locate-user-emacs-file "pyim/dcache/")
  "一个目录，用于保存 pyim 词库对应的 cache 文件."
  :type 'directory
  :group 'pyim)

(defvar pyim-iword2count nil)

(defun pyim-hashtable-set-variable (variable &optional force-restore fallback-value)
  "设置变量.

如果 VARIABLE 的值为 nil, 则使用 ‘pyim-hashtable-directory’ 中对应文件的内容来设置
VARIABLE 变量，FORCE-RESTORE 设置为 t 时，强制恢复，变量原来的值将丢失。
如果获取的变量值为 nil 时，将 VARIABLE 的值设置为 FALLBACK-VALUE ."
  (when (or force-restore (not (symbol-value variable)))
    (let ((file (concat (file-name-as-directory pyim-hashtable-directory)
                        (symbol-name variable))))
      (set variable (or (pyim-dcache-get-value-from-file file)
                        fallback-value
                        (make-hash-table :test #'equal))))))

(defun pyim-dcache-save-variable (variable)
  "将 VARIABLE 变量的取值保存到 `pyim-hashtable-directory' 中对应文件中."
  (let ((file (concat (file-name-as-directory pyim-hashtable-directory)
                      (symbol-name variable)))
        (value (symbol-value variable)))
    (pyim-dcache-save-value-to-file value file)))

(provide 'pyim-sdk)
;;; pyim-sdk.el ends here

