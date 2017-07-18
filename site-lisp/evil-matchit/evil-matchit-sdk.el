(defvar evilmi-sdk-extract-keyword-howtos
  '(("^[ \t]*\\([a-z]+\!?\\)\\( .*\\| *\\)$" 1)
    ("^.* \\(do\\) |[a-z0-9A-Z,|]+|$" 1))
  "The list of HOWTO on extracting keyword from current line.
Each howto is actually a pair. The first element of pair is the regular
expression to match the current line. The second is the index of sub-matches
to extract the keyword which starts from one. The sub-match is the match defined
between '\\(' and '\\)' in regular expression.")

;; slower but I don't care
;; @see http://ergoemacs.org/emacs/modernization_elisp_lib_problem.html
(defun evilmi-sdk-trim-string (string)
  (replace-regexp-in-string "\\`[ \t\n]*" "" (replace-regexp-in-string "[ \t\n]*\\'" "" string)))

(defun evilmi-sdk-keyword (info)
  (nth 3 info))

(defun evilmi-sdk-tags-is-matched (level orig-tag-info cur-tag-info match-tags)
  (let* (rlt
         (orig-keyword (evilmi-sdk-keyword orig-tag-info))
         (cur-keyword (evilmi-sdk-keyword cur-tag-info))
         (orig-row-idx (nth 0 orig-tag-info))
         (cur-row-idx (nth 0 cur-tag-info))
         (orig-type (nth 1 orig-tag-info))
         (cur-type (nth 1 cur-tag-info)))
    ;; handle function exit point
    (when (= 1 level)
      ;; end tag could be the same
      (if (and (evilmi--is-strictly-type cur-tag-info orig-tag-info)
               (not (evilmi--exactly-same-type cur-tag-info orig-tag-info)))
          ;; just pass
          (setq rlt nil)
        (cond
         ((and (< orig-type 2) (= cur-type 2))
          (setq rlt (evilmi-sdk-member cur-keyword (nth 2 (nth orig-row-idx match-tags)))))

         ((and (< cur-type 2) (= orig-type 2))
          (setq rlt (evilmi-sdk-member orig-keyword (nth 2 (nth cur-row-idx match-tags)))))

         (t
          (setq rlt (= (nth 0 orig-tag-info) (nth 0 cur-tag-info)))))))
    rlt))

;;;###autoload
(defun evilmi-sdk-curline ()
  (buffer-substring-no-properties
   (line-beginning-position)
   (line-end-position)))

;;;###autoload
(defun evilmi-sdk-member (keyword keyword-list)
  "Check if KEYWORD exist in KEYWORD-LIST."
  (let* (rlt)
    (cond
     ((not keyword)
      (setq rlt nil))

     ((not keyword-list)
      (setq rlt nil))

     ((stringp keyword-list)
      (setq rlt (string-match (concat "^" keyword-list "$") keyword)))

     ((stringp (car keyword-list))
      (unless (setq rlt (string-match (concat "^" (car keyword-list) "$") keyword))
        (setq rlt (evilmi-sdk-member keyword (cdr keyword-list)))))

     ((listp (car keyword-list))
      (unless (setq rlt (evilmi-sdk-member keyword (car keyword-list)))
        (setq rlt (evilmi-sdk-member keyword (cdr keyword-list)))))

     (t
      ;; just ignore first element
      (setq rlt (evilmi-sdk-member keyword (cdr keyword-list)))))

     (if (and evilmi-debug rlt) (message "evilmi-sdk-member called => %s %s. rlt=%s" keyword keyword-list rlt))
    rlt))


;;;###autoload
(defun evilmi-sdk-get-tag-info (keyword match-tags)
  "Return (row column is-function-exit-point keyword).
The row and column marked position in evilmi-mylang-match-tags
is-function-exit-point could be unknown status"
  (let* (rlt
         elems
         elem
         found
         (i 0)
         j)

    (while (and (< i (length match-tags)) (not found))
      (setq elems (nth i match-tags))
      (setq j 0)
      (while (and (not found) (< j (length elems)))
        (setq elem (nth j elems))
        (setq found (and (or (stringp elem) (listp elem))
                         (evilmi-sdk-member keyword elem)))
        (if (not found)
            (setq j (1+ j))))
      (if (not found) (setq i (1+ i))))
    (when found
      ;; function exit point maybe?
      (if (nth 3 (nth i match-tags))
          (setq rlt (list i
                          j
                          (nth 3 (nth i match-tags))
                          keyword))
        (setq rlt (list i j nil keyword))))
  (if evilmi-debug (message "evilmi-sdk-get-tag-info called => %s %s. rlt=%s" keyword match-tags rlt))
    rlt))

(defun evilmi--sdk-extract-keyword (cur-line match-tags howtos)
  "Extract keyword from CUR-LINE.  Keyword is defined in MATCH-TAGS."
  (let* (keyword howto (i 0))
    (while (and (not keyword) (< i (length howtos)))
      (setq howto (nth i howtos))
      (when (string-match (nth 0 howto) cur-line)
        ;; keyword should be trimmed because FORTRAN use "else if"
        (setq keyword (evilmi-sdk-trim-string (match-string (nth 1 howto) cur-line) ))
        ;; (message "keyword=%s" keyword)

        ;; keep search keyword by using next howto (regex and match-string index)
        (if (not (evilmi-sdk-member keyword match-tags)) (setq keyword nil)))
      (setq i (1+ i)))
    keyword))

(defun evilmi--is-monogamy (tag-info)
  (and (nth 2 tag-info) (string= (nth 2 tag-info) "MONOGAMY")))

(defun evilmi--exactly-same-type (crt orig)
  (= (nth 0 crt) (nth 0 orig)))

(defun evilmi--is-strictly-type (crt orig)
  (or (evilmi--is-monogamy crt) (evilmi--is-monogamy orig)))

(defun evilmi--same-type (crt orig)
  (let* (rlt)
    (if (and crt orig)
        ;; crt and orig should be at same row if either of them is monogamy
        (if (evilmi--is-strictly-type crt orig)
            (setq rlt (evilmi--exactly-same-type crt orig))
          (setq rlt t)))
    rlt))

;;;###autoload
(defun evilmi-sdk-get-tag (match-tags howtos)
  "Return '(start-point ((row column is-function-exit-point keyword))."
  (let* (rlt
         (cur-line (evilmi-sdk-curline))
         (keyword (evilmi--sdk-extract-keyword cur-line match-tags howtos))
         (tag-info (if keyword (evilmi-sdk-get-tag-info keyword match-tags))))

    ;; since we mixed ruby and lua mode here
    ;; maybe we should be strict at the keyword
    (if tag-info
        ;; 0 - open tag; 1 - middle tag; 2 - close tag;
        (setq rlt (list (if (= 2 (nth 1 tag-info))
                            (line-end-position)
                          (line-beginning-position))
                        tag-info)))
    rlt))

;;;###autoload
(defun evilmi-sdk-jump (rlt num match-tags howtos)
  (let* ((orig-tag-type (nth 1 (nth 1 rlt)))
         (orig-tag-info (nth 1 rlt))
         cur-tag-type
         cur-tag-info
         (level 1)
         (cur-line (evilmi-sdk-curline))
         keyword
         found
         where-to-jump-in-theory)
    (if evilmi-debug (message "evilmi-sdk-jump called => %s" rlt))

    (while (not found)
      (forward-line (if (= orig-tag-type 2) -1 1))
      (setq cur-line (evilmi-sdk-curline))
      (setq keyword (evilmi--sdk-extract-keyword cur-line match-tags howtos))
      (if evilmi-debug (message "keyword=%s cur-line=%s" keyword cur-line))

      (when keyword
        (setq cur-tag-info (evilmi-sdk-get-tag-info keyword match-tags))
        (when (evilmi--same-type cur-tag-info orig-tag-info)

          (setq cur-tag-type (nth 1 cur-tag-info))

          ;; key algorithm
          (cond
           ;; handle open tag
           ;; open (0) -> mid (1)  found when level is one else ignore
           ((and (= orig-tag-type 0) (= cur-tag-type 1))
            (when (evilmi-sdk-tags-is-matched level orig-tag-info cur-tag-info match-tags)
              (back-to-indentation)
              (setq where-to-jump-in-theory (1- (line-beginning-position)))
              (setq found t)))

           ;; open (0) -> closed (2) found when level is zero, level--
           ((and (= orig-tag-type 0) (= cur-tag-type 2))

            (when (evilmi-sdk-tags-is-matched level orig-tag-info cur-tag-info match-tags)
              (goto-char (line-end-position))
              (setq where-to-jump-in-theory (line-end-position))
              (setq found t))
            (setq level (1- level)))

           ;; open (0) -> open (0) level++
           ((and (= orig-tag-type 0) (= cur-tag-type 0))
            (setq level (1+ level)))

           ;; now handle mid tag
           ;; mid (1) -> mid (1) found if:
           ;;   1. level is one
           ;;   2. the open tag and middle tag are in the same row in evilmi-mylang-match-tags
           ;; else: just ignore
           ;; level is one means we are not in some embedded loop/conditional statements
           ((and (= orig-tag-type 1) (= cur-tag-type 1))

            (when (evilmi-sdk-tags-is-matched level orig-tag-info cur-tag-info match-tags)
              (back-to-indentation)
              (setq where-to-jump-in-theory (1- (line-beginning-position)))
              (setq found t)
              )
            )
           ;; mid (1) -> closed (2) found when level is zero, level --
           ((and (= orig-tag-type 1) (= cur-tag-type 2))
            (when (evilmi-sdk-tags-is-matched level orig-tag-info cur-tag-info match-tags)
              (goto-char (line-end-position))
              (setq where-to-jump-in-theory (line-end-position))
              (setq found t)
              )
            (setq level (1- level))
            )
           ;; mid (1) -> open (0) level++
           ((and (= orig-tag-type 1) (= cur-tag-type 0))
            (setq level (1+ level))
            )

           ;; now handle closed tag
           ;; closed (2) -> mid (1) ignore,impossible
           ((and (= orig-tag-type 2) (= cur-tag-type 1))
            )
           ;; closed (2) -> closed (2) level++
           ((and (= orig-tag-type 2) (= cur-tag-type 2))
            (setq level (1+ level))
            )
           ;; closed (2) -> open (0) found when level is zero, level--
           ((and (= orig-tag-type 2) (= cur-tag-type 0))
            (when (evilmi-sdk-tags-is-matched level orig-tag-info cur-tag-info match-tags)
              (setq where-to-jump-in-theory (line-beginning-position))
              (back-to-indentation)
              (setq found t)
              )
            (setq level (1- level))
            )
           (t (message "why here?"))
           )
          )
        )

      ;; we will stop at end or beginning of buffer anyway
      (if (or (= (line-end-position) (point-max))
              (= (line-beginning-position) (point-min))
              )
          (setq found t)
        ))
    where-to-jump-in-theory))

(defun evilmi-count-matches (regexp str)
  (let* ((count 0)
         (start 0))
    (unless start (setq start 0))
    (while (string-match regexp str start)
      (setq count (1+ count))
      (setq start (match-end 0)))
    count))

(provide 'evil-matchit-sdk)
