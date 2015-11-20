;;; json-mode.el --- Major mode for editing JSON files
;;; Author: Josh Johnston
;;; URL: https://github.com/joshwnj/json-mode
;; Package-Version: 1.1.0
;;; Version: 1.1.0

;;;;
;; extend the builtin js-mode's syntax highlighting

(defvar json-mode-hook nil)

(defconst json-quoted-key-re "\\(\"[^\"]+?\"[ ]*:\\)")
(defconst json-quoted-string-re "\\(\".*?\"\\)")
(defconst json-number-re "[^\"]\\([0-9]+\\(\\.[0-9]+\\)?\\)[^\"]")
(defconst json-keyword-re "\\(true\\|false\\|null\\)")

(defconst json-font-lock-keywords-1
  (list
   (list json-quoted-key-re 1 font-lock-keyword-face)
   (list json-quoted-string-re 1 font-lock-string-face)
   (list json-keyword-re 1 font-lock-constant-face)
   (list json-number-re 1 font-lock-constant-face)
   )
  "Level one font lock.")

(defconst python2-beautify-json "python2 -c \"import sys,json,collections; data=json.loads(sys.stdin.read(),object_pairs_hook=collections.OrderedDict); print json.dumps(data,sort_keys=%s,indent=4,separators=(',',': ')).decode('unicode_escape').encode('utf8','replace')\"")
(defconst python3-beautify-json "python3 -c \"import sys,json,codecs,collections; data=json.loads(sys.stdin.read(),object_pairs_hook=collections.OrderedDict); print((codecs.getdecoder('unicode_escape')(json.dumps(data,sort_keys=%s,indent=4,separators=(',',': '))))[0])\"")

(defun beautify-json_ (sort-keys)
  (let ((b (if mark-active (min (point) (mark)) (point-min)))
        (e (if mark-active (max (point) (mark)) (point-max))))
    ;; Beautify json with support for non-ascii characters.
    ;; Thanks to https://github.com/jarl-dk for this improvement.
    (shell-command-on-region b e
                             (concat (if (executable-find "env") "env " "")
                                     (format (if (executable-find "python2") python2-beautify-json python3-beautify-json) sort-keys))
                             (current-buffer) t)))

(defun beautify-json ()
  (interactive)
  (beautify-json_ "True"))

(defun ordered-beautify-json ()
  (interactive)
  (beautify-json_ "False"))

;;;###autoload
(define-derived-mode json-mode javascript-mode "JSON"
  "Major mode for editing JSON files"
  (set (make-local-variable 'font-lock-defaults) '(json-font-lock-keywords-1 t)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.json$" . json-mode))

(define-key json-mode-map (kbd "C-c C-f") 'beautify-json)

(provide 'json-mode)
;;; json-mode.el ends here
