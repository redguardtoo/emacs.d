;;; subtitles.el - work on .srt (subripper) subtitle files
;; Copyright (C) 2009 Ehud karni <address@hidden>

;; This file is NOT part of GNU Emacs, distribution conditions below.
;;
;;              EHUD   KARNI
;;              Ben Gurion
;;              Kfar - Sava
;;              ==================================;;
;; address@hidden   972-9-7659599
;;              ==================================
;;     RCS: $Id: subtitles.el,v 1.100 2009/05/16 14:10:45 ehud Exp $

;;  $Log: subtitles.el,v $
;;  Revision 1.100  2009/05/16 14:10:45  ehud
;;  Initial RCS version
;;

;; some functions to manipulate the times on an .srt (subripper) subtitle file
;;
;; An .srt file is composed of groups like that:
;;
;; line    content          * <-- column 1
;;   1   subtitle number    6
;;   2   subtitle times     00:01:34,920 --> 00:01:36,560
;;  3-+  subtitle value     ---any value in any language ---
;; last  separator          (empty)
;;
;; The user (interactive) functions are:
;;
;;   srt-renumber-subtitles - renumber all subtitles from 1 (no time change)
;;
;;   srt-offset-subtitles - change times by number of seconds (e.g. -2.74)
;;
;;   srt-mult-subtitles - change times linearly by multiplying (e.g. 1.04167)
;;         srt-23976-to-25-subtitles === (srt-mult-subtitles 25/23.976)
;;         srt-25-to-23976-subtitles === (srt-mult-subtitles 23.976/25)
;;
;;   srt-convert-sub-to-srt (fps) - convert a .sub file (microdvd) format to
;;                                  the .srt (subripper) format.
;;
;;  Ehud Karni 16/5/2009

;;  This program is free software; you can redistribute it and/or modify
;;  it under the terms of the GNU General Public License as published by
;;  the Free Software Foundation; either version 2 of the License, or
;;  (at your option) any later version.
;;
;;  This program is distributed in the hope that it will be useful,
;;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;  GNU General Public License for more details.
;;
;;  You should have received a copy of the GNU General Public License
;;  along with this program; if not, write to the Free Software
;;  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA



(defun srt-next-N-time ()
  "Find the next srt subtitle number & times.
returns a list with 3 elements : number, start-time (milliseconds), stop-time"
       (let ((time-rgx "\\(0[0-9]:[0-5][0-9]:[0-5][0-9],[0-9][0-9][0-9]\\)")
;; HH:mm:ss.nnn
             N strt stop)
           (and (re-search-forward (concat "^\\([0-9]+\\)\n"  time-rgx " --> "
time-rgx "$")
                                  nil t)               ;; search for next
               (setq N (string-to-number (match-string 1))
                     strt (srt-time-string-2-milli (match-string 2))
                     stop (srt-time-string-2-milli (match-string 3)))
               (list N strt stop))))


(defun srt-time-string-2-milli (time)
  "Convert srt TIME string (HH:MM:SS.mmm) to milliseconds"
       (let ((HH (string-to-number (substring time 0 2)))
             (MM (string-to-number (substring time 3 5)))
             (SS (string-to-number (substring time 6 8)))
             (ms (string-to-number (substring time 9 12))))
           (+ (* (+ (* (+ (* HH 60) MM) 60) SS) 1000) ms)))


(defun srt-time-milli-2-string (time)
  "Convert srt TIME in milliseconds to string (HH:MM:SS.mmm)"
       (let ((HH (/ time 3600000))
             (MM (% (/ time 60000) 60))
             (SS (% (/ time 1000) 60))
             (ms (% time 1000)))
           (format "%02d:%02d:%02d,%03d" HH MM SS ms)))


(defun srt-time-string-replace (N strt stop)
  "Replace last matched subtitle header by new values. 3 args:
N - subtitle number, STRT - start time in milliseconds, STOP - stop time."
       (replace-match (format "%d\n%s --> %s" N
                              (srt-time-milli-2-string strt)
                              (srt-time-milli-2-string stop)) t t))


(defun srt-renumber-subtitles ()
  "Renumber all subtitles starting with 1"
  (interactive)
       (let ((NEW 1)
             (svd-pos (point))         ;; saved position
             sub-va)                   ;; subtitle values
           (goto-char (point-min))
           (while (setq sub-va (srt-next-N-time))
               (srt-time-string-replace NEW (nth 1 sub-va) (nth 2 sub-va))
               (setq NEW (1+ NEW)))
           (goto-char svd-pos)))


(defun srt-offset-subtitles (seconds)
  "Offset all subtitles by some SECONDS (float, e.g. -2.74).
You could narrow down region at first"
  (interactive "NSeconds to offset (float e.g. -2.74)  ")
       (let ((off (truncate (* 1000 seconds)))     ;; offset in milliseconds
             (svd-pos (point))                     ;; saved position
             sub-va)                               ;; subtitle values
           (goto-char (point-min))
           (while (setq sub-va (srt-next-N-time))
               (srt-time-string-replace (car sub-va)
                                        (+ (nth 1 sub-va) off)
                                        (+ (nth 2 sub-va) off)))
           (goto-char svd-pos)))


(defun srt-mult-subtitles (rate)
  "Multiply all subtitles time by this value (float, e.g. 1.042709, 0.959040)"
  (interactive "NStrech time by (float e.g. 1.042709, 0.959040)  ")
       (let ((svd-pos (point))                     ;; saved position
             sub-va)                               ;; subtitle values
           (goto-char (point-min))
           (while (setq sub-va (srt-next-N-time))
               (srt-time-string-replace (car sub-va)
                                        (truncate (* (nth 1 sub-va) rate))
                                        (truncate (* (nth 2 sub-va) rate))))
           (goto-char svd-pos)))



(defun srt-25-to-23976-subtitles ()
  "Convert all subtitles time from 25 fps to 23.976 fps"
  (interactive)
       (srt-mult-subtitles 0.95904))

(defun srt-23976-to-25-subtitles ()
  "Convert all subtitles time from 23.976 fps to 25 fps"
  (interactive)
       (srt-mult-subtitles 1.042709376))


(defun srt-convert-sub-to-srt (fps)
  "Convert a .sub file (microdvd) to an .srt format.
1 arg: FPS - frames per second."
;; .sub (microdvd) format is:
;; {start-frame}{stop-frame}line1_text|line2_text
  (interactive "NFrames per second (float e.g. 23.976, 25)  ")
       (let ((svd-pos (point-marker))              ;; saved position
             (NEW 1)                               ;; subtitle number
             strt stop text)
           (setq fps (/ 1000.0 fps))               ;; frame time in ms (float)
           (goto-char (point-min))
           (while (re-search-forward "^{\\([0-9]+\\)}{\\([0-9]+\\)}\\(.*\\)$"
nil t)   ;; search for next
               (setq strt (truncate (* fps (string-to-number (match-string
1)))))
               (setq stop (truncate (* fps (string-to-number (match-string
2)))))
               (setq text (match-string 3))
               (srt-time-string-replace NEW strt stop)
               (insert "\n" text "\n")
               (setq NEW (1+ NEW)))
           (goto-char (point-min))
           (while (search-forward "|" nil t)
               (replace-match "\n"))
           (goto-char svd-pos)))

(provide 'subtitles)
;;; subtitles.el ends here
