

(cua-selection-mode 1)
;;(menu-bar-mode 0)
(fset 'zerlier-insert-newline-down [?\C-e return]) ;;向下插入新行
(global-unset-key "\C-j") ;; 取消C-j的绑定，让他也绑定到向下插入新行中
(global-set-key "\C-j" 'zerlier-insert-newline-down) ;; 取消C-j的绑定，让他也绑定到向下插入新行中

(defun copy-line (&optional arg)
  "Save current line into Kill-Ring without mark the line"
  (interactive "P")
   (let ((beg (line-beginning-position))
		 (end (line-end-position arg)))
     (copy-region-as-kill beg end))
   )

(defun copy-word (&optional arg)
  "Copy words at point"
  (interactive "P")
   (let ((beg (progn (if (looking-back "[a-zA-Z0-9]" 1) (backward-word 1)) (point)))
		 (end (progn (forward-word arg) (point))))
     (copy-region-as-kill beg end))
   )

(defun jr-duplicate-line ()
  "重复当行"
  (interactive)
  (save-excursion
    (let ((line-text (buffer-substring-no-properties
                      (line-beginning-position)
                      (line-end-position))))
      (move-end-of-line 1)
      (newline)
      (insert line-text))))
(global-set-key (kbd "C-c l")         (quote copy-line))
(global-set-key "\C-cd" 'jr-duplicate-line)

; find file at point
(global-set-key (kbd "C-c f")         'find-file-at-point)
(global-set-key [f9] 'call-last-kbd-macro) ;; 运行上一个宏


(defun copy-file-name (&optional full)
  "Copy file name of current-buffer.
If FULL is t, copy full file name."
  (interactive "P")
  (let ((file (buffer-name)))
    (if full
        (setq file (expand-file-name file)))
    (kill-new file)
    (message "File `%s' copied." file)))


;; 用C-M-o将窗口设置为一个
(global-set-key "\C-\M-o" 'delete-other-windows)
(global-unset-key "\C-o")
(global-set-key "\C-o" 'other-window)

;;--------------------------------------------------------------------
;; Lines enabling gnuplot-mode

;; move the files gnuplot.el to someplace in your lisp load-path or
;; use a line like
;;  (setq load-path (append (list "/path/to/gnuplot") load-path))

;; these lines enable the use of gnuplot mode
(autoload 'gnuplot-mode "gnuplot" "gnuplot major mode" t)
(autoload 'gnuplot-make-buffer "gnuplot" "open a buffer in gnuplot mode" t)

;; this line automatically causes all files with the .gp extension to
;; be loaded into gnuplot mode
(setq auto-mode-alist (append '(("\\.gp$" . gnuplot-mode)) auto-mode-alist))

;; This line binds the function-9 key so that it opens a buffer into
;; gnuplot mode 
(global-set-key [(f9)] 'gnuplot-make-buffer)

;; end of line for gnuplot-mode
;;--------------------------------------------------------------------


(provide 'lyzh-custom)

