;; Console.log stuff at point (or region)

(defun js2r-log-this ()
  (interactive)
  (js2r--guard)
  (let* ((log-info (js2r--figure-out-what-to-log-where))
         (stmt (car log-info))
         (pos (cdr log-info)))
    (save-excursion
      (goto-char pos)
      (when (looking-at "[;{]")
        (forward-char 1))
      (newline-and-indent)
      (insert "console.log(\"" stmt " = \", " stmt ");"))))

(defun js2r--figure-out-what-to-log-where ()
  (let ((parent-stmt (js2-node-parent-stmt (js2-node-at-point))))

    (if (use-region-p)
        (cons (buffer-substring (region-beginning) (region-end))
              (js2r--find-suitable-log-position-around parent-stmt))

      (let* ((node (js2r--name-node-at-point))
             (parent (js2-node-parent node)))

        (cond

         ((js2-function-node-p parent)
          (cons (js2-name-node-name node)
                (js2-node-abs-pos (js2-function-node-body parent))))

         ((js2-prop-get-node-p parent)
          (cons (buffer-substring (js2-node-abs-pos parent) (js2-node-abs-end parent))
                (js2r--find-suitable-log-position-around parent-stmt)))

         (:else
          (cons (js2-name-node-name node)
                (js2r--find-suitable-log-position-around parent-stmt))))))))

(defun js2r--find-suitable-log-position-around (parent-stmt)
  (if (js2-return-node-p parent-stmt)
      (save-excursion
        (goto-char (js2-node-abs-pos parent-stmt))
        (beginning-of-line)
        (forward-char -1)
        (point))
    (js2-node-abs-end parent-stmt)))

(defun js2r-split-string ()
  "Split the string node at point. If the string is already
split, join it instead."
  (interactive)
  (when (js2r--point-inside-string-p)
    (let ((delimiter (js2r--string-delimiter (js2-node-at-point))))
     (if (looking-back " \"")
         (progn
           (forward-char -2)
           (insert "  +")
           (forward-char -2))
       (if (looking-at (regexp-quote (format "%s + %s" delimiter delimiter)))
           (delete-char 5)
         (insert (format "%s + %s" delimiter delimiter)))))))

(defun js2r--string-delimiter (node)
  "Return the delimiter character of the string node NODE. It can
  be a single or double quote."
  (save-excursion
    (goto-char (js2-node-abs-pos node))
    (char-to-string (following-char))))

;; Make sure commas are placed correctly when moving a line up or down
;; in an object or array literal.

(defun move-line-down ()
  (interactive)
  (let ((col (current-column)))
    (save-excursion
      (forward-line)
      (transpose-lines 1))
    (forward-line)
    (move-to-column col)))

(defun move-line-up ()
  (interactive)
  (let ((col (current-column)))
    (save-excursion
      (forward-line)
      (transpose-lines -1))
    (move-to-column col)))

(defun js2r--current-line-is-prefixed-with-list-item-start ()
  (save-excursion
    (back-to-indentation)
    (looking-back "\\({\\|\\[\\|,\\)\\(\s\\|\n\\|\t\\)*"))) ; { or [ or , then space

(defun js2r--current-line-is-postfixed-with-list-item-end ()
  (save-excursion
    (end-of-line)
    (or (looking-back ",\s*") ; line ends in comma
        (looking-at "\\(\s\\|\n\\|\t\\)*\\(\\]\\|}\\)")))) ; space then ] or }

(defun js2r--current-line-is-a-list-item ()
  (and (js2r--current-line-is-prefixed-with-list-item-start)
       (js2r--current-line-is-postfixed-with-list-item-end)))

(defun js2r--next-line-is-a-list-item ()
  (save-excursion
    (forward-line)
    (js2r--current-line-is-a-list-item)))

(defun js2r--previous-line-is-a-list-item ()
  (save-excursion
    (forward-line -1)
    (js2r--current-line-is-a-list-item)))

(defun js2r--current-line-has-comma ()
  (save-excursion
    (end-of-line)
    (looking-back ",\s*")))

(defun js2r--previous-line-has-comma ()
  (save-excursion
    (forward-line -1)
    (js2r--current-line-has-comma)))

(defun js2r--move-line-down-as-list-item ()
  (move-line-down)
  (if (not (js2r--previous-line-has-comma))
      (save-excursion
        (end-of-line)
        (delete-char -1)
        (forward-line -1)
        (end-of-line)
        (insert ","))))

(defun js2r--move-line-up-as-list-item ()
  (move-line-up)
  (if (not (js2r--current-line-has-comma))
      (save-excursion
        (end-of-line)
        (insert ",")
        (forward-line)
        (end-of-line)
        (delete-char -1))))

(defun js2r-move-line-down ()
  (interactive)
  (if (and (js2r--current-line-is-a-list-item)
           (js2r--next-line-is-a-list-item))
      (js2r--move-line-down-as-list-item)
    (move-line-down))
  (funcall indent-line-function))

(defun js2r-move-line-up ()
  (interactive)
  (if (and (js2r--current-line-is-a-list-item)
           (js2r--previous-line-is-a-list-item))
      (js2r--move-line-up-as-list-item)
    (move-line-up))
  (funcall indent-line-function))

(provide 'js2r-conveniences)
