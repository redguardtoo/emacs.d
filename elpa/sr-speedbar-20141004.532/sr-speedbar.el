;;; sr-speedbar.el --- Same frame speedbar

;; Author: Sebastian Rose <sebastian_rose@gmx.de>
;; Maintainer: Sebastian Rose <sebastian_rose@gmx.de>
;;             Peter Lunicks <plunix@users.sourceforge.net>
;; Copyright (C) 2008, 2009, Sebastian Rose, all rights reserved.
;; Copyright (C) 2008, 2009, Andy Stewart, all rights reserved.
;; Copyright (C) 2009, Peter Lunicks, all rights reversed.
;; Created: 2008
;; Version: 20140914.2339
;; Package-Version: 20141004.532
;; X-Original-Version: 0.1.10
;; Last-Updated: 2014-08-03 11:30:00
;; URL: http://www.emacswiki.org/emacs/download/sr-speedbar.el
;; Keywords: speedbar, sr-speedbar.el
;; Compatibility: GNU Emacs 22 ~ GNU Emacs 24
;;
;; Features required by this library:
;;
;;  `speedbar' `advice' `cl'
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
;; The sr-speedbar.el was created just because I could not believe what I
;; read on http://www.emacswiki.org/cgi-bin/wiki/Speedbar.  They wrote there
;; that it is not possible to show the speedbar in the same frame.  But, as
;; we all know, ecb had this already.  So I started as some kind of joke :)
;; But when I found it useful and use it all the time.
;;
;; Now you type windows key with 's' (`s-s' in Emacs) will show the speedbar
;; in an extra window, same frame.  You can customize the initial width of the
;; speedbar window.
;;
;; Below are commands you can use:
;;
;; `sr-speedbar-open'                   Open `sr-speedbar' window.
;; `sr-speedbar-close'                  Close `sr-speedbar' window.
;; `sr-speedbar-toggle'                 Toggle `sr-speedbar' window.
;; `sr-speedbar-select-window'          Select `sr-speedbar' window.
;; `sr-speedbar-refresh-turn-on'        Turn on refresh speedbar content.
;; `sr-speedbar-refresh-turn-off'       Turn off refresh speedbar content.
;; `sr-speedbar-refresh-toggle'         Toggle refresh speedbar content.
;;
;; Enjoy! ;)
;;

;;; Installation:
;;
;; Copy sr-speedbar.el to your load-path and add to your ~/.emacs
;;
;;  (require 'sr-speedbar)
;;  (global-set-key (kbd "s-s") 'sr-speedbar-toggle)
;;
;; ... or any key binding you like.
;;

;;; Customize:
;;
;;      M-x customize-group RET sr-speedbar RET

;;; Change log:
;;
;; * 15 Sep 2014:
;;   * Tu, Do Hoang <tuhdo1710@gmail.com>
;;      * define `sr-speedbar-handle-other-window-advice' and `ad-advised-definition-p'
;;      before defining `sr-speedbar-skip-other-window-p'. Othewise, `sr-speedbar'
;;      fails to load at this stage.
;;
;;      * Do not used advised `pop-to-buffer' when helm window is
;;      alive. Otherwise another horizontal buffer is created inside
;;      Helm buffer.
;;
;;   * Uwe Koloska <kolewu@koloro.de>
;;      * define `ad-advised-definition-p' only if it's not defined
;;        fixes an error on Emacs 24.3 where `macrop' ist still named
;;        `ad-macro-p'
;;
;; * 03 Aug 2014:
;;   * Reuben Thomas <rrt@sc3d.org>:
;;      * Reduce to a single width preference, and make it work properly on
;;        startup.
;;      * Miscellaneous tidying of documentation and comments.
;;      * Remove version constant; should be using the package header, and it
;;        was already way out of date.
;;
;; * 08 Jun 2014:
;;   * Gregor Zattler:
;;      * test if symbol `ad-advised-definition-p' is defined,
;;        since Christian Brassats version test failed on emacs
;;        23.3.91.1
;;
;; * 05 May 2014:
;;   * Christian Brassat:
;;      * `ad-advised-definition-p' is not supported since Emacs 24.4.
;;
;; * 09 Mar 2013:
;;   * Tharre:
;;      * Remove Emacs 21 compatibility code as it fails to compile on Emacs 24.
;;
;; * 20 July 2009:
;;   * Peter Lunicks:
;;      * Add new option `sr-speedbar-right-side' to control which
;;        side of the frame the speedbar appears on.
;;
;; * 18 Feb 2009:
;;   * Andy Stewart:
;;      * Fix bug between ECB and `sr-speedbar-close'.
;;
;; * 29 Jan 2009:
;;   * Andy Stewart:
;;      * Fix doc.
;;
;; * 13 Jan 2009:
;;   * Andy Stewart:
;;      * Use `emacs-major-version' instead comment for Emacs 21 compatibility.
;;      * Rewrite advice for `pop-to-buffer' to avoid `pop-to-buffer' not effect
;;        when have many dedicated window in current frame.
;;      * Rewrite advice for `delete-other-windows' to avoid use common variable
;;        `delete-protected-window-list' and use `window-dedicated-p' instead.
;;        Remove variable `delete-protected-window-list' and function
;;        `sr-speedbar-dedicated-match-protected-window-p'.
;;
;; * 04 Jan 2009:
;;   * Andy Stewart:
;;      * Add new option `sr-speedbar-auto-refresh' control refresh content.
;;      * Add new functions:
;;        `sr-speedbar-refresh-turn-on',
;;        `sr-speedbar-refresh-turn-off',
;;        `sr-speedbar-refresh-toggle'.
;;      * Fix doc.
;;
;; * 30 Dec 2008:
;;   * Andy Stewart:
;;      * Rewrite advice for `delete-other-windows' for fix the bug
;;        with window configuration save and revert.
;;      * Rewrite advice for `delete-window', now just remember window
;;        width before deleted, and can use `delete-window' do same effect
;;        as command `sr-speedbar-close'.
;;      * Add new option `sr-speedbar-max-width'.
;;        Remember window width before hide, except larger than value of
;;        `sr-speedbar-max-width'.
;;      * Add new variable `delete-protected-window-list', for protected
;;        special window don't deleted.
;;        This variable is common for any extension that use dedicated
;;        window.
;;      * Fix doc.
;;
;; * 29 Dec 2008:
;;   * Andy Stewart:
;;      * Pick-up and refactory code that use `buffer-live-p' or `window-live-p',
;;        and replace with `sr-speedbar-buffer-exist-p' and
;;        `sr-speedbar-window-exist-p'.
;;      * Rename some function with prefix `sr-speedbar-' to avoid
;;        conflict with other functions.
;;      * Pick-up the code that handle advice for `other-window',
;;        and replace with function `sr-speedbar-handle-other-window-advice'.
;;      * Clean up code, make more clear.
;;
;; * 21 Dec 2008:
;;   * Andy Stewart:
;;      * Fix the bug `sr-speedbar-open' and `sr-speedbar-close'.
;;      * Fix doc.
;;
;; * 20 Dec 2008
;;   * Andy Stewart:
;;      * Fix `ad-advised-definition-p' error.
;;      * Fix doc.
;;
;; * 17 Dec 2008
;;   * Andy Stewart:
;;      * Add new option `sr-speedbar-skip-other-window-p' and new advice
;;        for `other-window', make user skip select `sr-speedbar' window
;;        when use command `other-window'.
;;      * Fix the name of advice, make more clear.
;;      * Fix the bug `sr-speedbar-select-window' when no live window exist.
;;      * Fix doc.
;;
;; * 16 Dec 2008:
;;   * Andy Stewart:
;;      * Fix the bug of `sr-speedbar-refresh', use `default-directory'
;;        get refresh directory instead through function in `dired'.
;;      * Fix `window-live-p' bug, check window valid value before use
;;        `window-live-p' test `sr-speedbar-window'.
;;      * Fix `buffer-live-p' bug, check buffer valid value before use
;;        `buffer-live-p' test `speedbar-buffer'.
;;      * Add advice `pop-to-buffer' to make function `display-buffer'
;;        can pop-up window when just have two windows (one is `sr-speedbar'
;;        window) in current frame.
;;      * Add group `sr-speedbar'.
;;        More better customize interface through `customize-group'.
;;
;; * 28 Sep 2008:
;;   * Andy Stewart:
;;      * Fix a bug, when `sr-speedbar-toggle' many times, window width
;;        will increment automatically.
;;      * Use around advices replace, make code simple.
;;      * Use `sr-speedbar-open' replace `sr-speedbar-no-separate-frame'.
;;      * Clean up code.
;;
;; * 28 Sep 2008:
;;   * Sebastian:
;;      * set `sr-speedbar-delete-windows' to nil to avoid
;;        the removal of other windows.
;;
;; * 26 Jun 2008:
;;   * Sebastian:
;;      * Added Andy Stewart's patch to refresh the speedbar's contents.
;;        Thanks for this one!
;;
;; * Init:
;;   * Sebastian:
;;      * Added some lines to get it working:
;;      * splitting the window and remember it,
;;      * changing the way speedbar finds a file.
;;      * File view of speedbar is now working all right.
;;      * C-x 1 in other window deletes speedbar-window, just calling
;;        M-x sr-speedbar-no-separate-frame again is fine now.
;;      * Toggle speedbar works, width is save when toggling.
;;      * Recalculate speedbar width if window-width - speedbar-width <= 0
;;      * Speedbar window is now dedicated to speedbar-buffer.
;;

;;; Acknowledgements:
;;
;;      All emacsers ... :)
;;

;;; Bug
;;
;;

;;; TODO
;;
;;
;;

;;; Require
(require 'speedbar)
(require 'advice)
(require 'cl)

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; User Customization ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defgroup sr-speedbar nil
  "Same frame speedbar."
  :group 'speedbar)

(defcustom sr-speedbar-default-width 40
  "Initial width of `sr-speedbar-window' under window system."
  :type 'integer
  :group 'sr-speedbar)

(defcustom sr-speedbar-max-width 50
  "The max width limit that window allowed.
Default, if hide `sr-speedbar' window will remember
window width, except the window width larger than
this value."
  :type 'integer
  :group 'sr-speedbar)

(defcustom sr-speedbar-auto-refresh t
  "Automatically refresh speedbar content when changed directory.
Default is t."
  :type 'boolean
  :set (lambda (symbol value)
         (set symbol value))
  :group 'sr-speedbar)

(defcustom sr-speedbar-right-side t
  "Show the speedbar to the right side of the current window.
If nil, the speedbar will appear on the left.
Default is t."
  :type 'boolean
  :set (lambda (symbol value)
         (set symbol value))
  :group 'sr-speedbar)

(defcustom sr-speedbar-delete-windows nil
  "Allow the speedbar to delete other windows before showing up.
If nil, speedbar will not touch your window configuration.
Otherwise `delete-other-windows' will be called before showing
the speedbar.

Default is nil."
  :type 'boolean
  :group 'sr-speedbar)

(if (not (fboundp 'ad-advised-definition-p))
    (defun ad-advised-definition-p (definition)
      "Return non-nil if DEFINITION was generated from advice information."
      (if (or (ad-lambda-p definition)
              (macrop definition)
              (ad-compiled-p definition))
          (let ((docstring (ad-docstring definition)))
            (and (stringp docstring)
                 (get-text-property 0 'dynamic-docstring-function docstring))))))

(defun sr-speedbar-handle-other-window-advice (activate)
  "Handle advice for function `other-window'.
If ACTIVATE is `non-nil' enable advice `sr-speedbar-other-window-advice'.
Otherwise disable it."
  (if activate
      (ad-enable-advice 'other-window 'after 'sr-speedbar-other-window-advice)
    (ad-disable-advice 'other-window 'after 'sr-speedbar-other-window-advice))
  (ad-activate 'other-window))

(defcustom sr-speedbar-skip-other-window-p nil
  "Whether skip `sr-speedbar' window with `other-window'.
Default, can use `other-window' select window in cyclic
ordering of windows.  But sometimes we don't want select
`sr-speedbar' window use `other-window'.
Just want make `sr-speedbar' window as a view sidebar.

So please turn on this option if you want skip
`sr-speedbar' window with `other-window'.

Default is nil."
  :type 'boolean
  :set (lambda (symbol value)
         (set symbol value)
         (if (fboundp 'ad-advised-definition-p)
             (when (ad-advised-definition-p 'other-window)
               (sr-speedbar-handle-other-window-advice value))
           (when (ad-is-advised 'other-window)
             (sr-speedbar-handle-other-window-advice value))))
  :group 'sr-speedbar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Constant ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defconst sr-speedbar-buffer-name "*SPEEDBAR*"
  "The buffer name of sr-speedbar.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Variables ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar sr-speedbar-width sr-speedbar-default-width
  "Initial width of speedbar-window.")

(defvar sr-speedbar-window nil
  "Speedbar window.")

(defvar sr-speedbar-last-refresh-dictionary nil
  "The last refresh dictionary record of 'sr-speedbar-refresh'.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Interactive functions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;###autoload
(defun sr-speedbar-toggle ()
  "Toggle sr-speedbar window.
Toggle visibility of sr-speedbar by resizing
the `sr-speedbar-window' to a minimal width
or the last width when visible.
Use this function to create or toggle visibility
of a speedbar-window.  It will be created if necessary."
  (interactive)
  (if (sr-speedbar-exist-p)
      (sr-speedbar-close)
    (sr-speedbar-open)))

;;;###autoload
(defun sr-speedbar-open ()
  "Create `sr-speedbar' window."
  (interactive)
  (if (not (sr-speedbar-exist-p))
      (let ((current-window (selected-window)))
        ;; Ensure only one window is there
        ;; when `sr-speedbar-delete-windows' is non-nil
        (if sr-speedbar-delete-windows
            (delete-other-windows))
        ;; Whether activate `other-window' advice
        ;; to skip `sr-speedbar' window when use `other-window'.
        (sr-speedbar-handle-other-window-advice sr-speedbar-skip-other-window-p)
        ;; Switch buffer
        (if (sr-speedbar-buffer-exist-p speedbar-buffer)
            (unless (sr-speedbar-window-exist-p sr-speedbar-window)
              (sr-speedbar-get-window))
          (if (<= (sr-speedbar-current-window-take-width) sr-speedbar-width)
              (setq sr-speedbar-width sr-speedbar-default-width))
          (sr-speedbar-get-window)             ;get `sr-speedbar' window that split current window
          (setq speedbar-buffer (get-buffer-create sr-speedbar-buffer-name)
                speedbar-frame (selected-frame)
                dframe-attached-frame (selected-frame)
                speedbar-select-frame-method 'attached
                speedbar-verbosity-level 0 ;don't say anything, i don't like ... :)
                speedbar-last-selected-file nil)
          (set-buffer speedbar-buffer)
          (buffer-disable-undo speedbar-buffer) ;make disable in speedbar buffer, otherwise will occur `undo-outer-limit' error
          (speedbar-mode)
          (speedbar-reconfigure-keymaps)
          (speedbar-update-contents)
          (speedbar-set-timer 1)
          ;; Add speedbar hook.
          (add-hook 'speedbar-before-visiting-file-hook 'sr-speedbar-before-visiting-file-hook t)
          (add-hook 'speedbar-before-visiting-tag-hook 'sr-speedbar-before-visiting-tag-hook t)
          (add-hook 'speedbar-visiting-file-hook 'sr-speedbar-visiting-file-hook t)
          (add-hook 'speedbar-visiting-tag-hook 'sr-speedbar-visiting-tag-hook t)
          ;; Add `kill-buffer-hook'.
          (add-hook 'kill-buffer-hook 'sr-speedbar-kill-buffer-hook) ;add `kill-buffer-hook'
          ;; Auto refresh speedbar content
          ;; if option `sr-speedbar-auto-refresh' is non-nil
          (sr-speedbar-handle-auto-refresh sr-speedbar-auto-refresh))
        (set-window-buffer sr-speedbar-window (get-buffer sr-speedbar-buffer-name))
        (set-window-dedicated-p sr-speedbar-window t) ;make `sr-speedbar-window' dedicated to speedbar-buffer.
        (select-window current-window))
    (message "`sr-speedbar' window has exist.")))

(defun sr-speedbar-close ()
  "Close `sr-speedbar' window and save window width."
  (interactive)
  (if (sr-speedbar-exist-p)
      (let ((current-window (selected-window)))
        ;; Remember window width.
        (sr-speedbar-select-window)
        (sr-speedbar-remember-window-width)
        ;; Close window.
        (if (and (require 'ecb nil t)
                 ecb-activated-window-configuration)
            ;; Toggle ECB window when ECB window activated.
            (progn
              (ecb-deactivate)
              (ecb-activate))
          ;; Otherwise delete dedicated window.
          (delete-window sr-speedbar-window)
          (if (sr-speedbar-window-exist-p current-window)
              (select-window current-window))))
    (message "`sr-speedbar' window is not exist.")))

(defun sr-speedbar-select-window ()
  "Force the windows that contain `sr-speedbar'."
  (interactive)
  (if (sr-speedbar-exist-p)
      (select-window sr-speedbar-window)
    (message "`sr-speedbar' window is not exist.")))

(defun sr-speedbar-refresh-turn-on ()
  "Turn on refresh content automatically."
  (interactive)
  (setq sr-speedbar-auto-refresh t)
  (sr-speedbar-handle-auto-refresh sr-speedbar-auto-refresh t))

(defun sr-speedbar-refresh-turn-off ()
  "Turn off refresh content automatically."
  (interactive)
  (setq sr-speedbar-auto-refresh nil)
  (sr-speedbar-handle-auto-refresh sr-speedbar-auto-refresh t))

(defun sr-speedbar-refresh-toggle ()
  "Toggle refresh content status."
  (interactive)
  (setq sr-speedbar-auto-refresh (not sr-speedbar-auto-refresh))
  (sr-speedbar-handle-auto-refresh sr-speedbar-auto-refresh t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; utilise functions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun sr-speedbar-exist-p ()
  "Return `non-nil' if `sr-speedbar' is exist.
Otherwise return nil."
  (and (sr-speedbar-buffer-exist-p speedbar-buffer)
       (sr-speedbar-window-exist-p sr-speedbar-window)))

(defun sr-speedbar-window-p ()
  "Return `non-nil' if current window is `sr-speedbar' window.
Otherwise return nil."
  (equal sr-speedbar-buffer-name (buffer-name (window-buffer))))

(defun sr-speedbar-remember-window-width ()
  "Remember window width."
  (let ((win-width (sr-speedbar-current-window-take-width)))
    (if (and (sr-speedbar-window-p)
             (> win-width 1)
             (<= win-width sr-speedbar-max-width))
        (setq sr-speedbar-width win-width))))

(defun sr-speedbar-get-window ()
  "Get `sr-speedbar' window."
  (let ((current-window (selected-window))
        ;; Get split new window.
        (new-window (split-window
                     (selected-window)
                     (if sr-speedbar-right-side
                         (- (sr-speedbar-current-window-take-width) sr-speedbar-width)
                       sr-speedbar-width)
                     t)))
    ;; Select split window.
    (setq sr-speedbar-window
          (if sr-speedbar-right-side
              ;; Select right window when `sr-speedbar-right-side' is enable.
              new-window
            ;; Otherwise select left widnow.
            current-window))))

(defun sr-speedbar-before-visiting-file-hook ()
  "Function that hook `speedbar-before-visiting-file-hook'."
  (select-window (previous-window)))

(defun sr-speedbar-before-visiting-tag-hook ()
  "Function that hook `speedbar-before-visiting-tag-hook'."
  (select-window (previous-window)))

(defun sr-speedbar-visiting-file-hook ()
  "Function that hook `speedbar-visiting-file-hook'."
  (select-window (previous-window)))

(defun sr-speedbar-visiting-tag-hook ()
  "Function that hook `speedbar-visiting-tag-hook'."
  (select-window (previous-window)))

(defun sr-speedbar-kill-buffer-hook ()
  "Function that hook `kill-buffer-hook'."
  (when (eq (current-buffer) speedbar-buffer)
    (setq speedbar-frame nil
          dframe-attached-frame nil
          speedbar-buffer nil)
    (speedbar-set-timer nil)
    (remove-hook 'speedbar-before-visiting-file-hook 'sr-speedbar-before-visiting-file-hook)
    (remove-hook 'speedbar-before-visiting-tag-hook 'sr-speedbar-before-visiting-tag-hook)
    (remove-hook 'speedbar-visiting-file-hook 'sr-speedbar-visiting-file-hook)
    (remove-hook 'speedbar-visiting-tag-hook 'sr-speedbar-visiting-tag-hook)))

(defun sr-speedbar-refresh ()
  "Refresh the context of speedbar."
  (when (and (not (equal default-directory sr-speedbar-last-refresh-dictionary)) ;if directory is change
             (not (sr-speedbar-window-p))) ;and is not in speedbar buffer
    (setq sr-speedbar-last-refresh-dictionary default-directory)
    (speedbar-refresh)))

(defun sr-speedbar-handle-auto-refresh (activate &optional echo-show)
  "Automatically refresh speedbar content when changed directory.
Do nothing if option ACTIVATE is nil.
Will display message if ECHO-SHOW is non-nil."
  (if activate
      (progn
        (add-hook 'speedbar-timer-hook 'sr-speedbar-refresh)
        (if echo-show (message "Turn on speedbar content refresh automatically.")))
    (remove-hook 'speedbar-timer-hook 'sr-speedbar-refresh)
    (if echo-show (message "Turn off speedbar content refresh automatically."))))

(defun sr-speedbar-current-window-take-width (&optional window)
  "Return the width that WINDOW take up.
If WINDOW is nil, get current window."
  (let ((edges (window-edges window)))
    (- (nth 2 edges) (nth 0 edges))))

(defun sr-speedbar-window-dedicated-only-one-p ()
  "Only have one non-dedicated window."
  (interactive)
  (let ((window-number 0)
        (dedicated-window-number 0))
    (walk-windows
     (lambda (w)
       (with-selected-window w
         (incf window-number)
         (if (window-dedicated-p w)
             (incf dedicated-window-number)))))
    (if (and (> dedicated-window-number 0)
             (= (- window-number dedicated-window-number) 1))
        t nil)))

(defun sr-speedbar-window-exist-p (window)
  "Return `non-nil' if WINDOW is exist.
Otherwise return nil."
  (and window (window-live-p window)))

(defun sr-speedbar-buffer-exist-p (buffer)
  "Return `non-nil' if BUFFER is exist.
Otherwise return nil."
  (and buffer (buffer-live-p buffer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Advices ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defadvice delete-other-windows (around sr-speedbar-delete-other-window-advice activate)
  "This advice to make `sr-speedbar' window can't deleted by command `delete-other-windows'."
  (let ((sr-speedbar-active-p (sr-speedbar-window-exist-p sr-speedbar-window)))
    (if sr-speedbar-active-p
        (let ((current-window (selected-window)))
          (dolist (win (window-list))
            (when (and (window-live-p win)
                       (not (eq current-window win))
                       (not (window-dedicated-p win)))
              (delete-window win))))
      ad-do-it)))

(defadvice delete-window (before sr-speedbar-delete-window-advice activate)
  "This advice to remember `sr-speedbar' window width before deleted.
Use `delete-window' delete `sr-speedbar' window have same effect as `sr-speedbar-close'."
  ;; Remember window width before deleted.
  (sr-speedbar-remember-window-width))

(defadvice pop-to-buffer (before sr-speedbar-pop-to-buffer-advice activate)
  "This advice is to fix `pop-to-buffer' problem with dedicated window.
Default, function `display-buffer' can't display buffer in select window
if current window is `dedicated'.

So function `display-buffer' conflict with `sr-speedbar' window, because
`sr-speedbar' window is `dedicated' window.

That is to say, when current frame just have one `non-dedicated' window,
any functions that use `display-buffer' can't split windows
to display buffer, even option `pop-up-windows' is enable.

And the example function that can occur above problem is `pop-to-buffer'."
  (when (and pop-up-windows                            ;`pop-up-windows' is enable
             (sr-speedbar-window-dedicated-only-one-p) ;just have one `non-dedicated' window
             (sr-speedbar-window-exist-p sr-speedbar-window)
             (not (sr-speedbar-window-p)) ;not in `sr-speedbar' window
             (if (featurep 'helm)
		 (not helm-alive-p)
	       t))
    (split-window-vertically)
    (windmove-down)))

(defadvice other-window (after sr-speedbar-other-window-advice)
  "Default, can use `other-window' select window in cyclic ordering of windows.
But sometimes we don't want select `sr-speedbar' window use `other-window'.
Just want make `sr-speedbar' window as a view sidebar.

This advice can make `other-window' skip `sr-speedbar' window."
  (let ((count (or (ad-get-arg 0) 1)))
    (when (and (sr-speedbar-window-exist-p sr-speedbar-window)
               (eq sr-speedbar-window (selected-window)))
      (other-window count))))

(provide 'sr-speedbar)

;;; sr-speedbar.el ends here
