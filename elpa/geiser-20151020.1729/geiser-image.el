;; geiser-image.el -- support for image display

;; Copyright (c) 2012, 2015 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Authors: Michael Wilber, Jose Antonio Ortega Ruiz <jao@gnu.org>
;; Start date: Sun Sep 02, 2012 00:00



(require 'geiser-custom)
(require 'geiser-base)
(require 'geiser-impl)


;;; Customization:

(defgroup geiser-image nil
  "Options for image displaying."
  :group 'geiser)

(geiser-custom--defcustom geiser-image-viewer "display"
  "Which system image viewer program to invoke upon M-x
`geiser-view-last-image'."
  :type 'string
  :group 'geiser-image)

(geiser-custom--defcustom geiser-image-cache-keep-last 10
  "How many images to keep in geiser's image cache."
  :type 'integer
  :group 'geiser-image)

(geiser-custom--defcustom geiser-image-cache-dir nil
  "Default directory where generated images are stored.

If nil,the system wide tmp dir will be used."
  :type 'path
  :group 'geiser-image)

(geiser-custom--defface image-button
  'button geiser-image "image buttons in terminal buffers")

(geiser-impl--define-caller geiser-image--cache-dir image-cache-dir ()
  "Directory where generated images are stored.  If this function
returns nil, no images are generated.")



(defun geiser-image--list-cache ()
  "List all the images in the image cache."
  (let ((cdir (geiser-image--cache-dir nil)))
    (and cdir
         (file-directory-p cdir)
         (let ((files (directory-files-and-attributes cdir t
                                                      "geiser-img-[0-9]*.png")))
           (mapcar 'car (sort files (lambda (a b)
                                      (< (float-time (nth 6 a))
                                         (float-time (nth 6 b))))))))))

(defun geiser-image--clean-cache ()
  "Clean all except for the last `geiser-image-cache-keep-last'
images in `geiser-image--cache-dir'."
  (interactive)
  (dolist (f (butlast (geiser-image--list-cache) geiser-image-cache-keep-last))
    (delete-file f)))

(defun geiser-image--display (file)
  (start-process "Geiser image view" nil geiser-image-viewer file))

(defun geiser-image--button-action (button)
  (let ((file (button-get button 'geiser-image-file)))
    (when (file-exists-p file) (geiser-image--display file))))

(define-button-type 'geiser-image--button
  'action 'geiser-image--button-action
  'follow-link t)

(defun geiser-image--insert-button (file)
  (insert-text-button "[image]"
                      :type 'geiser-image--button
                      'face 'geiser-font-lock-image-button
                      'geiser-image-file file
                      'help-echo "Click to display image"))

(defun geiser-image--replace-images (inline-images-p auto-p)
  "Replace all image patterns with actual images"
  (let ((seen 0))
    (with-silent-modifications
      (save-excursion
        (goto-char (point-min))
        (while (re-search-forward "\"?#<Image: \\([-+.\\\\/_:0-9a-zA-Z]+\\)>\"?"
                                  nil t)
          (setq seen (+ 1 seen))
          (let* ((file (match-string 1))
                 (begin (match-beginning 0))
                 (end (match-end 0)))
            (delete-region begin end)
            (goto-char begin)
            (if (and inline-images-p (display-images-p))
                (insert-image (create-image file) "[image]")
              (geiser-image--insert-button file)
              (when auto-p (geiser-image--display file)))))))
    seen))

(defun geiser-view-last-image (n)
  "Open the last displayed image in the system's image viewer.

With prefix arg, open the N-th last shown image in the system's
image viewer."
  (interactive "p")
  (let ((images (reverse (geiser-image--list-cache))))
    (if (>= (length images) n)
        (geiser-image--display (nth (- n 1) images))
      (error "There aren't %d recent images" n))))


(provide 'geiser-image)
