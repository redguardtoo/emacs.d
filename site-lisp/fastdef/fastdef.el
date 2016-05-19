;;; fastdef.el --- Insert terminology from Google top search results

;; Copyright (C) 2016 Chen Bin
;;
;; Version: 0.1.0
;; Keywords: terminology org-mode markdown
;; Author: Chen Bin <chenin DOT sh AT gmail DOT com>
;; URL: http://github.com/redguardtoo/fastdef
;; Package-Requires: ((swiper "0.7.0") (w3m "0.0"))

;; This file is not part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; This program insert terminology from top Google search results.
;; It requires w3m (http://w3m.sourceforge.net/).
;;
;; Usage,
;; `M-x fastdef-insert' to insert terminology from Google.
;; `M-x fastdef-insert-from-history' to re-use previous results.
;;
;; `fastdef-text-template' decides the format of inserted content.
;;
;; Change `fastdef-search-engine' and `fastdef-regexp-extract-url'
;; to switch search engine.

;;; Code:

(require 'w3m)
(require 'ivy)

(defvar fastdef-text-template "[[%%url][%%term]]"
  "The text template to insert term.")

(defvar fastdef-search-engine "http://www.google.com/search?q=%s"
  "The search engine.  %s will be replaced with keyword.")

(defvar fastdef-regexp-extract-url "\?q=\\(http[^&]*\\)"
  "The regex to extract actual URL.
Search engine place it in URL parameter.")

(defvar fastdef-urls-limit 10
  "Limit of URLs for one terminology.")

(defvar fastdef-history nil
  "Items inserted.")

(defvar fastdef-keyword nil
  "Keyword inputted.  Internal usage.")

(defvar fastdef-w3m-buffer nil
  "Current w3m buffer.  Internal usage.")

(defvar fastdef-original-buffer nil
  "Original editor buffer.")

;;;###autoload
(defun fastdef-get-text-with-same-font ()
  "Get text with the same font."
  (let ((pt (point))
         (cff (get-text-property (point) 'face))
         b e rlt)
    (setq b (1- pt))
    (setq e (1+ pt))
    (save-excursion
      (while (and (< (point-min) b)
                  (equal (get-text-property b 'face) cff))
        (setq b (1- b)))
      (setq b (1+ b))
      (while (and (< e (point-max))
                  (equal (get-text-property e 'face) cff))
        (setq e (1+ e)))
      (setq rlt (buffer-substring b e)))
    rlt))

(defun fastdef-w3m-fontify-after-hook-setup ()
  "Hookup after w3m buffer is fully rendered."
  (when fastdef-keyword
    (let (collection
          (case-fold-search nil)
          (cnt fastdef-urls-limit)
          url
          url-text
          faces)
      (goto-char (point-min))
      (search-forward-regexp "About .* results")
      (while (and (w3m-next-anchor)
                  (> cnt 0))
        (when (and (setq faces (get-text-property (point) 'face))
                   (listp faces)
                   (memq 'w3m-anchor faces)
                   (memq 'w3m-bold faces)
                   (setq url-text (fastdef-get-text-with-same-font))
                   (string-match fastdef-regexp-extract-url (w3m-anchor))
                   (setq url (match-string 1 (w3m-anchor))))
          (setq cnt (1- cnt))
          (add-to-list 'collection (format "%s => %s" url-text url) t)))

      (ivy-read "URL(s):"
                collection
                :action (lambda (line)
                          (let* ((url (nth 1 (split-string line " => ")))
                                 rlt)
                            ;; create content from text template
                            (setq rlt (replace-regexp-in-string "%%url" url fastdef-text-template))
                            (setq rlt (replace-regexp-in-string "%%term" fastdef-keyword rlt))
                            ;; remember in history
                            (add-to-list 'fastdef-history
                                         (cons fastdef-keyword (list fastdef-keyword url))
                                         t)
                            ;; actually insert content
                            (when fastdef-original-buffer
                              (with-current-buffer fastdef-original-buffer
                                (insert rlt)))
                            )))
      ;; done
      (setq fastdef-keyword nil))))

(add-hook 'w3m-fontify-after-hook 'fastdef-w3m-fontify-after-hook-setup)

;;;###autoload
(defun fastdef-insert ()
  "Insert terminology with URL."
  (interactive)
  (setq fastdef-original-buffer (current-buffer))
  (save-window-excursion
    (setq fastdef-keyword (read-string "Enter terminology:"))
    (if fastdef-w3m-buffer
        (w3m-process-stop fastdef-w3m-buffer))
    (w3m-goto-url (format fastdef-search-engine
                          (w3m-url-encode-string fastdef-keyword)))
    (setq fastdef-w3m-buffer (current-buffer))))

;;;###autoload
(defun fastdef-insert-from-history()
  "Insert terminology from history."
  (interactive)
  (if fastdef-history
      (ivy-read (format "Previous terminology:")
              fastdef-history
              :action (lambda (item)
                        (let (rlt)
                          (setq rlt (replace-regexp-in-string "%%url" (cadr item) fastdef-text-template))
                          (setq rlt (replace-regexp-in-string "%%term" (car item) rlt))
                          (insert rlt))))
    (message "terminology history is empty!")))

(provide 'fastdef)
;;; fastdef.el ends here

