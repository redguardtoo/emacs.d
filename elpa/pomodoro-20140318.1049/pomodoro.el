;;; pomodoro.el --- A timer for the Pomodoro Technique
;;;   (http://www.pomodorotechnique.com)

;; Author: David Kerschner <dkerschner@gmail.com>
;; Created: Aug 25, 2010
;; Version: 0.2
;; Package-Version: 20140318.1049

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Code:

(eval-when-compile
  (require 'cl))

(defgroup pomodoro nil
  "Timer for the Pomodoro Technique in emacs"
  :prefix "pomodoro-"
  :group 'tools)

(defcustom pomodoro-work-time 25
  "Length of time in minutes for a work period"
  :group 'pomodoro
  :type 'integer)

(defcustom pomodoro-break-time 5
  "Length of time in minutes for a break period"
  :group 'pomodoro
  :type 'integer)

(defcustom pomodoro-long-break-time 15
  "Length of time in minutes for a long break period"
  :group 'pomodoro
  :type 'integer)

(defcustom pomodoro-nth-for-longer-break 4
  "Number of work cycles before a longer break"
  :group 'pomodoro
  :type 'integer)

(defcustom pomodoro-extra-time 2
  "Number of minutes to add onto a timer when avoiding a cycle change"
  :group 'pomodoro
  :type 'integer)

(defcustom pomodoro-break-start-message "Break time!"
  "Message show when a break period starts"
  :group 'pomodoro
  :type 'string)

(defcustom pomodoro-play-sounds t
  "Should pomodoro play sounds when starting a new time period"
  :group 'pomodoro
  :type 'boolean)

(defcustom pomodoro-break-start-sound ""
  "Sound played when a break period starts"
  :group 'pomodoro
  :type 'string)

(defcustom pomodoro-sound-player "mplayer"
  "Music player used to play sounds"
  :group 'pomodoro
  :type 'string)

(defcustom pomodoro-work-start-message "Back to work, slave!"
  "Message to show when a work period starts"
  :group 'pomodoro
  :type 'string)

(defcustom pomodoro-work-start-sound ""
  "Sound played when a work period starts"
  :group 'pomodoro
  :type 'string)

(defcustom pomodoro-long-break-start-message "Time for a longer break!"
  "Message to show when a long break starts"
  :group 'pomodoro
  :type 'string)

(defcustom pomodoro-work-cycle "w"
  "String to display in mode line for a work cycle"
  :group 'pomodoro
  :type 'string)

(defcustom pomodoro-break-cycle "b"
  "String to display in mode line for a break cycle"
  :group 'pomodoro
  :type 'string)

(defcustom pomodoro-time-format "%.2m:%.2s "
  "Time string to display in mode line for countdowns.
Formatted with `format-seconds'."
  :group 'pomodoro
  :type 'string)

(defcustom pomodoro-show-number nil
  "Whether the number of the pomodoro in the series should be shown in the modeline"
  :group 'pomodoro
  :type 'boolean)


(defvar pomodoro-timer nil)
(with-no-warnings (defvar pomodoros 0))
(defvar pomodoro-current-cycle nil)
(defvar pomodoro-mode-line-string "")
(defvar pomodoro-end-time) ; the data type should be time instead of integer
(defvar pomodoro-time-remaining) ;used to pause pomodoro timers

(defun pomodoro-set-end-time (minutes)
  "Set how long the pomodoro timer should run"
  ;; no slave can work 2^16 seconds without rest!
  (setq pomodoro-end-time (time-add (current-time) (list 0 (* minutes 60) 0))))

(defun pomodoro-tick ()
  (let ((time (round (float-time (time-subtract pomodoro-end-time (current-time))))))
    (if (<= time 0)
        (if (string= pomodoro-current-cycle pomodoro-work-cycle)
            (progn
              (incf pomodoros)
              (let ((p (if (= 0 (mod pomodoros
                                     pomodoro-nth-for-longer-break))
                           (cons pomodoro-long-break-time
                                 pomodoro-long-break-start-message)
                         (cons pomodoro-break-time
                               pomodoro-break-start-message))))
                (if pomodoro-play-sounds
                    (play-pomodoro-break-sound))
                (cond ((yes-or-no-p (cdr p))
                       (setq pomodoro-current-cycle pomodoro-break-cycle)
                       (pomodoro-set-end-time (car p)))
                      (t
                       (decf pomodoros)
                       (pomodoro-set-end-time pomodoro-extra-time)))))
          (if pomodoro-play-sounds
              (play-pomodoro-work-sound))
          (if (not (yes-or-no-p pomodoro-work-start-message))
              (pomodoro-set-end-time pomodoro-extra-time)
            (setq pomodoro-current-cycle pomodoro-work-cycle)
            (pomodoro-set-end-time pomodoro-work-time))))
    (setq pomodoro-mode-line-string
          (format (concat "%s"
						  (when pomodoro-show-number
							(format "%s-" (+ 1 (mod pomodoros pomodoro-nth-for-longer-break))))
						  (format-seconds pomodoro-time-format time))
                  pomodoro-current-cycle))
    (force-mode-line-update)))

;;;###autoload
(defun pomodoro-start (arg)
  (interactive "P")
  (let* ((timer (or (if (listp arg)
                        (car arg))
                    arg
                    pomodoro-work-time)))
    (setq pomodoro-current-cycle pomodoro-work-cycle)
    (when pomodoro-timer
      (cancel-timer pomodoro-timer))
    (setq pomodoro-work-time timer)
    (pomodoro-set-end-time pomodoro-work-time)
    (setq pomodoro-timer (run-with-timer 0 1 'pomodoro-tick))))

(defun pomodoro-pause ()
  (interactive)
  (cancel-timer pomodoro-timer)
  (setq pomodoro-time-remaining (round (float-time (time-subtract pomodoro-end-time (current-time)))))
  (force-mode-line-update))

(defun pomodoro-resume ()
  (interactive)
  (setq pomodoro-end-time (time-add (current-time) (seconds-to-time pomodoro-time-remaining)))
  (setq pomodoro-timer (run-with-timer 0 1 'pomodoro-tick))) 

(defun pomodoro-stop ()
  (interactive)
  (cancel-timer pomodoro-timer)
  (setq pomodoro-mode-line-string "")
  (setq pomodoro-current-cycle pomodoro-work-cycle)
  (force-mode-line-update))

(defun play-pomodoro-sound (sound)
  "Play sound for pomodoro"
  (call-process pomodoro-sound-player nil 0 nil (expand-file-name sound)))

(defun play-pomodoro-break-sound ()
  "Play sound for break"
  (interactive)
  (play-pomodoro-sound pomodoro-break-start-sound))

(defun play-pomodoro-work-sound ()
  "Play sound for work"
  (interactive)
  (play-pomodoro-sound pomodoro-work-start-sound))

(defun pomodoro-add-to-mode-line ()
  (setq-default mode-line-format
                (cons '(pomodoro-mode-line-string pomodoro-mode-line-string)
                      mode-line-format)))

(provide 'pomodoro)
;;; pomodoro.el ends here
