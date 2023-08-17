;;; init-bookmark.el ---  book mark setup -*- lexical-binding: t -*-
;;; Code:

(defun my-bookmark-set ()
  "Set and save bookmark.
If bookmark with same file name already exists, override it quietly."
  (interactive)
  (my-ensure 'bookmark)
  (bookmark-maybe-load-default-file)

  (let* ((filename (cond
                    ((eq major-mode 'eww-mode)
                     (eww-current-url))
                    (t
                     buffer-file-name)))
         existing-bookmark)
    (when (setq existing-bookmark
                (cl-find-if (lambda (b)
                              (let* ((f (cdr (assoc 'filename (cdr b)))))
                                (when (and f (file-exists-p f))
                                  (setq f (file-truename f)))
                                (string= f filename)))
                            bookmark-alist))
      ;; extract name of existing bookmark
      (setq existing-bookmark (car existing-bookmark)))
    (bookmark-set existing-bookmark)

    ;; save bookmark now
    (bookmark-save)

    (when existing-bookmark
      (message "Saved into existing bookmark \"%s\"" existing-bookmark))))

(defun my-bookmark-goto ()
  "Open ANY bookmark."
  (interactive)
  (my-ensure 'bookmark)
  (bookmark-maybe-load-default-file)
  ;; do the real thing
  (let* ((cands (delq nil (mapcar #'my-build-bookmark-candidate
                                  (and (boundp 'bookmark-alist)
                                       bookmark-alist))))
         (selected (completing-read "bookmarks:" cands)))
    (when selected
      (bookmark-jump (cdr (assoc selected cands))))))

(with-eval-after-load 'bookmark
  (defun my-build-bookmark-candidate (bookmark)
    "Re-shape BOOKMARK."
    (let* ((key (cond
                 ((and (assoc 'filename bookmark) (cdr (assoc 'filename bookmark)))
                  (format "%s (%s)" (car bookmark) (cdr (assoc 'filename bookmark))))
                 ((and (assoc 'location bookmark) (cdr (assoc 'location bookmark)))
                  (format "%s (%s)" (car bookmark) (cdr (assoc 'location bookmark))))
                 (t
                  (car bookmark)))))
      ;; key will be displayed
      ;; re-shape the data so full bookmark be passed to ivy-read
      (cons key bookmark)))

  ;; use my own bookmark if it exists
  (let ((file "~/.emacs.bmk"))
    (when (file-exists-p file)
      (setq bookmark-default-file file))))

(provide 'init-bookmark)
;;; init-bookmark.el ends here
