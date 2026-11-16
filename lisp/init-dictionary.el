;; -*- coding: utf-8; lexical-binding: t; -*-

;;; Code:

(defvar my-dict-buffer-name "*MYDICT*"
  "The buffer buffer of my dictionary lookup.")

;; {{ Please provide directory and dictionary file base name
;; English => Chinese
(defvar my-dict-simple
  '("~/.stardict/dic/stardict-langdao-ec-gb-2.4.2" "langdao-ec-gb"))

;; WordNet English => English
(defvar my-dict-complete
  '("~/.stardict/dic/stardict-dictd_www.dict.org_wn-2.4.2" "dictd_www.dict.org_wn"))
;; }}

(defvar my-dict-simple-cache nil "Internal variable.")
(defvar my-dict-complete-cache nil "Internal variable.")

(defun my-dict-prompt-input ()
  "Prompt input for translate."
  (let* ((initial  (if (use-region-p)
                       (buffer-substring-no-properties (region-beginning)
                                                       (region-end))
                     (thing-at-point 'word)))
         (word (read-string (format "Word (%s): " (or initial ""))
                            nil
                            nil
                            initial)))
    (when (and word (not (string-empty-p (string-trim word))))
      (downcase (string-trim word)))))

(defun my-dict-quit-window ()
  "Quit window."
  (interactive)
  (quit-window t))

(defmacro my-dict-search-detail (word dict cache)
  "Return WORD's definition with DICT, CACHE."
  `(when (and ,word (not (string-empty-p ,word)))
     (my-ensure 'stardict)
     (unless ,cache
       (setq ,cache
             (stardict-open (nth 0 ,dict) (nth 1 ,dict) t)))
     (stardict-lookup ,cache ,word)))

(defun my-dict-complete-definition ()
  "Show dictionary lookup in buffer."
  (interactive)
  (let* ((word (my-dict-prompt-input))
         (def (my-dict-search-detail word my-dict-complete my-dict-complete-cache))
         buf
         win)
    (when def
      (setq buf (get-buffer-create my-dict-buffer-name))
      (with-current-buffer buf
        (let ((inhibit-read-only t))
          (erase-buffer)
          (insert def)
          (goto-char (point-min))
          (setq buffer-read-only t))

        ;; quit easily
        (local-set-key (kbd "q") #'my-dict-quit-window)
        (when (bound-and-true-p evil-local-mode)
          (evil-local-set-key 'normal "q" #'my-dict-quit-window)))

      (unless (eq (current-buffer) buf)
        (if (null (setq win (get-buffer-window buf)))
            (switch-to-buffer-other-window buf)
          (select-window win))))))

(defun my-dict-simple-definition ()
  "Show dictionary lookup in popup."
  (interactive)
  (let* ((word (my-dict-prompt-input))
         (def (my-dict-search-detail word my-dict-simple my-dict-simple-cache)))
    (when def
      (my-ensure 'popup)
      (popup-tip def))))

(provide 'init-dictionary)
;;; init-dictionary.el ends here
