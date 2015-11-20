;;; dired-details.el --- make file details hide-able in dired

;; Copyright (C) 2003-2011 Rob Giardina

;; Version: 1.3.2
;; Package-Version: 20130824.1158
;; Keywords: dired, hide
;; Author: Rob Giardina <rob.giardina.ohmmanepadmespam@oracle.com>
;; Maintainer: Rob Giardina
;; Last updated: Aug 17, 2012
;; Contributors: Harold Maier, Klaus Berndl

;; This file is not part of GNU Emacs.

;; This is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;; or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
;; License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; `dired-details-hide' makes dired buffers that look like this:
;;
;;  /private/rgiardin/lispHome:
;;  used 1264 available files
;;
;;  drwxr-xr-x   5 rgiardin g632         512 Jan 19  2003 ..
;;  -rw-r--r--   1 rgiardin svrtech     4141 Aug 23 17:07 dired-details.el
;;  -rw-r--r--   1 rgiardin svrtech     4141 Aug 23 17:07 my-really-really-long-I-mean-really-long-filename.el
;;  -rw-r--r--   1 rgiardin svrtech       56 Aug 23 17:07 linked-file.el -> /var/tmp/checkouts/linked-file.el
;;
;; look like this:
;;
;;  /private/rgiardin/lispHome/emacs.config:
;;  used 1264 available files
;;
;;  [...] ..
;;  [...] dired-details.el
;;  [...] my-really-really-long-I-mean-really-long-filename.el
;;  [...] linked-file.el -> [...]
;;
;; The function `dired-details-toggle' will toggle details on and off.
;;
;;
;; INSTALLATION:
;;
;; To apply `dired-details-hide' to all new dired buffers, add the
;; following to your .emacs:
;;
;; (require 'dired-details)
;; (dired-details-install)
;;
;; This also binds the following keys in dired buffers:
;;
;;   ) - dired-details-show
;;   ( - dired-details-hide
;;
;; CHANGES:
;;
;; * 1.3.2: Added sr-mode to dired-details-hide function to make it word with
;;          Sunrise Commander
;; * 1.3.1: Allow "misc lines (total used, find-dired statuses, etc)" to be hidden;
;;          suggested by Chris Poole
;; * 1.3: dired-details-toggle and customization support added by Klaus Berndl
;; * 1.2.4: Setup hide and show keybindings earlier than the first hide.
;; * 1.2.3: add dired-details-initially-hide customization as suggested by Harold Maier
;; * 1.2.2: extensive change to support subdirs in dired buffers
;; * 1.2.1: respect current hidden state (not initial state) when inserting subdirs
;;
;; TODO:
;; * add a hook for dired-add-file to hide new entries as necessary
;;

;;; customizable vars

(defgroup dired-details nil
  "Settings for the dired-details package."
  :group 'dired
  :prefix "dired-details-")

(defcustom dired-details-hidden-string "[...]"
  "*This string will be shown in place of file details and symbolic links."
  :group 'dired-details
  :type 'string)

(defcustom dired-details-hide-link-targets t
  "*Hide symbolic link target paths."
  :group 'dired-details
  :type 'boolean)

(defcustom dired-details-initially-hide t
  "*Hide dired details on entry to dired buffers."
  :group 'dired-details
  :type 'boolean)

(defcustom dired-details-hide-extra-lines t
  "*Hides lines matching any regex in `dired-details-invisible-lines'.
Changing this variable will not affect existing dired buffers."
  :group 'dired-details
  :type 'boolean)

(defcustom dired-details-invisible-lines
  '("total used in directory" "^\\s-*$" "find finished" "find \\." "  wildcard ")
  "*Hide dired details on entry to dired buffers."
  :group 'dired-details
  :type 'list)

;;; implementation

(defvar dired-details-debug nil)

(defvar dired-details-internal-overlay-list nil)
(make-variable-buffer-local 'dired-details-internal-overlay-list)

(defvar dired-details-state nil
  "Three possible values: nil (has not been set), 'hidden (details are
hidden), 'shown (details are visible).")
(make-variable-buffer-local 'dired-details-state)

(defun dired-details-install ()
  (eval-after-load "dired"
    '(progn
       (add-hook 'dired-after-readin-hook 'dired-details-activate)

       (define-key dired-mode-map "(" 'dired-details-hide)
       (define-key dired-mode-map ")" 'dired-details-show)

       (defadvice dired-revert (before remember-the-details activate)
         (dired-details-delete-overlays)))))

(defun dired-details-activate ()
  "Set up dired-details in the current dired buffer. Called by
dired-after-readin-hook on initial display and when a subdirectory is
inserted (with `i')."
  ;;if a state has been chosen in this buffer, respect it
  (if dired-details-state
    (when (eq 'hidden dired-details-state)
      (dired-details-hide))
    ;;otherwise, use the default state
    (when dired-details-initially-hide
      (dired-details-hide))))

(defun dired-details-delete-overlays ()
  (mapc '(lambda (list) (mapc 'delete-overlay
                             (cdr list)))
        dired-details-internal-overlay-list)
  (setq dired-details-internal-overlay-list nil))

(defun dired-details-toggle ( &optional arg default-too )
  "Toggle visibility of dired details.
With positive prefix argument ARG hide the details, with negative
show them."
  (interactive "P")
  (let ((hide (if (null arg)
                (not (eq 'hidden dired-details-state))
                (> (prefix-numeric-value arg) 0))))
    (if default-too
      (setq dired-details-initially-hide hide))
    (if hide (dired-details-hide)
        (dired-details-show))))

(defun dired-details-hide ()
  "Make an invisible, evaporable overlay for each file-line's details
in this dired buffer."
  (interactive)
  (unless (memq major-mode '(dired-mode vc-dired-mode sr-mode))
    (error "dired-details-hide can only be called in dired mode"))

  (when dired-details-debug
    (let ((b (get-buffer-create "dired-details-debug")))
      (append-to-buffer b (point) (point-max))))

  ;;NOTE - we call this even if we're already hidden. There may be a
  ;;new subdirectory inserted that we have to deal with. Pre-existing
  ;;subdirectories will reuse their cached overlays.
  (save-excursion
    (save-restriction
      (widen)
      ;;hide each displayed subdirectory
      (mapc
       '(lambda (dir-and-pos)
          (let ((cached-overlays (assoc (car dir-and-pos)
                                        dired-details-internal-overlay-list)))
            (if cached-overlays
              ;;reuse the existing overlays
              (dired-details-frob-overlays t)
              ;;no existing overlays for this subdir, make 'em
              (let ((cache (list (car dir-and-pos)))
                    (subdir-start (cdr dir-and-pos))
                    (subdir-end (1- (dired-get-subdir-max dir-and-pos))))
                (goto-char subdir-start)
                (forward-line 1) ;;always skip the dir line
                ;;v1.3 (dired-goto-next-file)
                (while (< (point) subdir-end)
                  (dired-details-make-current-line-overlay cache)
                  (forward-line 1))
                  ;;v1.3 (dired-next-line 1))
                (setq dired-details-internal-overlay-list
                      (cons cache dired-details-internal-overlay-list))))))
       dired-subdir-alist)))
  (setq dired-details-state 'hidden))

(defun dired-details-show ()
  "Show whatever details a call to `dired-details-hide' may have
hidden in this buffer."
  (interactive)
  (dired-details-frob-overlays nil)
  (setq dired-details-state 'shown))

(defun dired-details-make-current-line-overlay ( cache )
  (let* ((bol (progn (beginning-of-line) (point)))
         (totally-hide nil)
         (details              ;hide flags, size, owner, date, etc.
          (cond ((ignore-errors (dired-move-to-filename t))
                 (make-overlay (+ 2 bol) (point)))
                ((and dired-details-hide-extra-lines
                      (let ((line (buffer-substring (point-at-bol) (point-at-eol))))
                        (when (delq nil (mapcar (lambda (x) (string-match x line))
                                                dired-details-invisible-lines))
                          (let ((o (make-overlay bol (1+ (point-at-eol)))))
                            ;;this is delayed so that the hide-link bit below doesn't bork
                            (overlay-put o 'make-intangible t)
                            (overlay-put o 'suppress-before t)
                            o)))))))
         (ln-target            ;hide symlink dest
          (when dired-details-hide-link-targets
            (if (progn (beginning-of-line)
                       (search-forward-regexp
                        "-> \\(.*\\)"
                        (save-excursion (end-of-line) (point)) t))
              (make-overlay (match-beginning 1) (match-end 1))))))
    
    (when details
      (overlay-put details 'evaporate t)
      (dired-details-hide-overlay details)

      (when ln-target
        (overlay-put ln-target 'evaporate t)
        (dired-details-hide-overlay ln-target))

      (setcdr cache (append (if ln-target
                              (list ln-target details)
                              (list details))
                            (cdr cache))))))

(defun dired-details-hide-overlay (o)
  (overlay-put o 'invisible t)
  (if (overlay-get o 'make-intangible) (overlay-put o 'intangible t))
  (unless (overlay-get o 'suppress-before)
    (overlay-put o 'before-string dired-details-hidden-string)))

(defun dired-details-show-overlay (o)
  (overlay-put o 'invisible nil)
  (overlay-put o 'before-string nil))

(defun dired-details-frob-overlays ( hide )
  (if dired-details-internal-overlay-list
    (mapc '(lambda (list)
             (mapc (if hide 'dired-details-hide-overlay 'dired-details-show-overlay)
                   (cdr list)))
          dired-details-internal-overlay-list)))

(provide 'dired-details)

;;; dired-details.el ends here
