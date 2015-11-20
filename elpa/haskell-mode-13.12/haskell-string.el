;;;###autoload
(defun haskell-trim (string)
  (replace-regexp-in-string
   "^[ \t\n]+" ""
   (replace-regexp-in-string
    "[ \t\n]+$" ""
    string)))

;;;###autoload
(defun haskell-string-take (string n)
  "Take n chars from string."
  (substring string
             0
             (min (length string) n)))

(defun haskell-string ())

(provide 'haskell-string)
