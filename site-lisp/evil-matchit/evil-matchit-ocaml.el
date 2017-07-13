(defvar evilmi-ocaml-keywords
  '((("struct" "begin" "sig" "object") ("end"))
    (("if") ("then"))
    (("match") ("with"))
    (("match" "try") ("with"))
    (("while" "for") ("done"))
    (("let") ("in"))
    ())
  "Ocaml keywords.")

(defvar evilmi-ocaml-keywords-regex
  (let ((all-keywords (apply 'append (apply 'append evilmi-ocaml-keywords))))
    (format "\\<\\(%s\\)\\>" (mapconcat 'identity all-keywords "\\|")))
  "Regexp to find next/previous keyword.")

;; jumps to next keyword. Returs nil if there's no next word
(defun evilmi-ocaml-next-word (direction)
  (if (= direction 0)
      (let ((new-point (save-excursion
          (forward-char)
          (if (search-forward-regexp evilmi-ocaml-keywords-regex nil t)
              (search-backward-regexp evilmi-ocaml-keywords-regex)
            nil)
        )))
        (if new-point (goto-char new-point)))
    (search-backward-regexp evilmi-ocaml-keywords-regex nil t)))

(defun evilmi-ocaml-end-word ()
  (save-excursion
    (search-forward-regexp "\\>")
    (point)))

(defun evilmi-ocaml-get-word ()
  (buffer-substring-no-properties (point) (evilmi-ocaml-end-word)))

(defun evilmi-ocaml-is-keyword (l keyword)
  "Checks if the keyword belongs to a row."
  (find-if (lambda (w) (string-equal w keyword)) (apply 'append l)))

(defun evilmi-ocaml-get-tag-info (keyword)
  "Find the row in the evilmi-ocaml-keywords."
  (find-if (lambda (l) (evilmi-ocaml-is-keyword l keyword)) evilmi-ocaml-keywords))

;; 0 - forward
;; 1 - backward
(defun evilmi-ocaml-go (tag-info level direction)
  (if (= level 0)
      (point)
    (if (evilmi-ocaml-next-word direction)
        (progn
          (setq keyword (evilmi-ocaml-get-word))

          (if (evilmi-ocaml-is-keyword tag-info keyword)
              ;; interesting tag
              (if (member keyword (nth direction tag-info))
                  (evilmi-ocaml-go tag-info (+ level 1) direction)
                (evilmi-ocaml-go tag-info (- level 1) direction))

            ;; other tag
            (evilmi-ocaml-go tag-info level direction)))
      nil)))

(defun evilmi-ocaml-goto-word-beginning ()
  ;; this is so that when the cursor is on the first character we don't jump to previous word
  (forward-char)
  (search-backward-regexp "\\<"))

;;;###autoload
(defun evilmi-ocaml-get-tag ()
  "Return information of current tag: (list position-of-word word)."
  (save-excursion
    (evilmi-ocaml-goto-word-beginning)
    (list (car (bounds-of-thing-at-point 'word))
          (evilmi-ocaml-get-word))))

;;;###autoload
(defun evilmi-ocaml-jump (rlt num)
  (let* ((keyword (cadr rlt))
         (tag-info (evilmi-ocaml-get-tag-info keyword))
         (direction (if (member keyword (car tag-info)) 0 1)))
    (let ((new-point (save-excursion
                       (evilmi-ocaml-goto-word-beginning)
                       (evilmi-ocaml-go tag-info 1 direction))))
      (if new-point (goto-char new-point)))))

(provide 'evil-matchit-ocaml)
