;;; auto-save.el --- Auto save files when idle

;; Filename: auto-save.el
;; Description: Auto save files when idle
;; Author: Andy Stewart lazycat.manatee@gmail.com
;;; Maintainer: Chen Bin (redguardtoo) <chenbin.sh AT gmail DOT com>
;; Copyright (C) 2013 ~ 2014, Andy Stewart, all rights reserved.
;; Created: 2013-12-31 00:32:00
;; Version: 1.0
;; URL:
;; Keywords: autosave
;; Compatibility: GNU Emacs 23.0.60.1
;;
;; Features that might be required by this library:
;;
;;
;;

;;; This file is NOT part of GNU Emacs

;;; License
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; Auto save file when emacs idle
;;

;;; Installation:
;;
;; Put auto-save.el to your load-path.
;; The load-path is usually ~/elisp/.
;; It's set in your ~/.emacs like this:
;; (add-to-list 'load-path (expand-file-name "~/elisp"))
;;
;; And the following to your ~/.emacs startup file.
;;
;; (require 'init-auto-save)
;; (auto-save-enable)
;;
;; Set `auto-save-slient' with non-nil if want emacs save files slient:
;; (setq auto-save-slient t)
;;
;; No need more.

;;; Change log:
;;
;; 2014/01/04
;;      * Add new function `auto-save-enable' to enable auto-save in user config file.
;;      * Add options: `auto-save-idle' and `auto-save-slient'
;;
;; 2008/10/20
;;      First released.
;;

;;; Acknowledgements:
;;
;;
;;

;;; TODO
;;
;;
;;

;;; Require


;;; Code:

(defgroup auto-save nil
  "Auto save file when emacs idle."
  :group 'auto-save)

(defcustom auto-save-idle 2
  "The idle seconds to auto save file."
  :type 'integer
  :group 'auto-save)

(defcustom auto-save-slient nil
  "Nothing to dirty minibuffer if this option is non-nil."
  :type 'boolean
  :group 'auto-save)

(defcustom auto-save-exclude
  '("\\.avi"
    "\\.mpeg"
    "\\.3gp"
    "\\.mp4"
    "\\.mp3"
    "\\.mkv"
    "\\.rm"
    "\\.rmvb"
    "\\.pdf"
    "\\.jpg"
    "\\.jpeg"
    "\\.png"
    "\\.gif"
    "\\.gz"
    "\\.svg"
    "\\.ico"
    "\\.gpg"
    "archive-contents")
  "List of regexps and predicates for filenames excluded from the auto save list.
When a filename matches any of the regexps or satisfies any of the
predicates it is excluded from the auto save list.
A predicate is a function that is passed a filename to check and that
must return non-nil to exclude it."
  :group 'auto-save)

;; Emacs' default auto-save is stupid to generate #foo# files!
(setq auto-save-default nil)

(defun auto-save-include-p (filename)
  "Return non-nil if FILENAME should be included.
That is, if it doesn't match any of the `auto-save-exclude' checks."
  (let* ((case-fold-search nil)
         (include-p t)
         (i 0)
         check)
    (while (and (< i (length auto-save-exclude)) include-p)
      ;; If there was an error in a predicate, err on the side of
      ;; keeping the file.
      (setq check (nth i auto-save-exclude))
      (condition-case nil
          (progn
            (cond
             ((stringp check)
              ;; A regexp
              (setq include-p (not (string-match-p check filename))))
             ((functionp check)
              ;; A predicate
              (setq include-p (not (funcall check filename))))))
        (error nil))
      (setq i (1+ i)))

    include-p))

(defun auto-save-buffers ()
  "Auto save all buffer."
  (interactive)
  (let* (autosave-buffer-list)
    (save-excursion
      (dolist (buf (buffer-list))
        (set-buffer buf)
        (when (and (buffer-file-name)
                   (buffer-modified-p)
                   (file-writable-p (buffer-file-name))
                   (auto-save-include-p (buffer-file-name)))
          (push (buffer-name) autosave-buffer-list)
          (if auto-save-slient
              (with-temp-message ""
                (basic-save-buffer))
            (basic-save-buffer))))
      ;; Tell user when auto save files.
      (unless auto-save-slient
        (cond
         ;; It's stupid tell user if nothing to save.
         ((= (length autosave-buffer-list) 1)
          (message "# Saved %s" (car autosave-buffer-list)))
         ((> (length autosave-buffer-list) 1)
          (message "# Saved %d files: %s"
                   (length autosave-buffer-list)
                   (mapconcat 'identity autosave-buffer-list ", ")))))
      )))

(defun auto-save-enable ()
  "Enable auto save."
  (interactive)
  (run-with-idle-timer auto-save-idle t #'auto-save-buffers))

(provide 'auto-save)

;;; auto-save.el ends here
