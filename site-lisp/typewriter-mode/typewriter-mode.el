;;; typewriter-mode.el --- typewriter sounds fx when typing

;; Copyright (C) 2013  Tung Dao

;; Author: Tung Dao <me@tungdao.com>
;; Keywords:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Minor mode for playing typewriter sounds when typing.

;;; Code:

(defcustom twm/sound-file
  "typewriter-key-modern.wav"
  "Sound file."
  :type 'string
  :group 'typewriter-mode)

(defcustom twm/play-command
  nil
  "Command to play sound file.  It's automatically set if nil."
  :type 'string
  :group 'typewriter-mode)

(defcustom twm/quiet-major-modes
  nil
  "Major modes to be quiet."
  :type '(repeat sexp)
  :group 'typewriter-mode)

(defconst twm/sound-file-dir
 (file-name-directory load-file-name)
  "The directory of sound files.")

(defun twm/play-typewriter-sound ()
  "Play sound."
  (unless (and twm/quiet-major-modes
               (apply 'derived-mode-p twm/quiet-major-modes))
    (let* ((cmd twm/play-command))
      ;; guess player
      (unless cmd
        (setq cmd
              (cond
               ((eq system-type 'darwin)
                "afplay %s")
               ((eq system-type 'windows-nt)
                "powershell -c (New-Object Media.SoundPlayer \"%s\").PlaySync();")
               ((eq system-type 'gnu/linux)
                ;; pulseaudio or alsa
                (if (executable-find "paplay") "paplay %s" "aplay %s")))))
      (start-process-shell-command
       "*play-typewriter-sound*" nil
       (format cmd (concat twm/sound-file-dir twm/sound-file))))))

(defun twm/toggle-sound-style ()
  "Change typewriter sound between vintage and modern."
  (interactive)
  (let* ((is-vintage (string-match-p "vintage.wav" twm/sound-file)))
    (setq twm/sound-file (format "typewriter-key-%s.wav"
                                 (if is-vintage "modern" "vintage")))))

;;;###autoload
(define-minor-mode typewriter-mode
  "Minor mode to generate typewriter sounds when typing."
  :lighter ""
  :global t
  :group 'typewriter-mode
  (cond
   (typewriter-mode
    (add-hook 'post-self-insert-hook #'twm/play-typewriter-sound))
   (t
    (remove-hook 'post-self-insert-hook #'twm/play-typewriter-sound))))

(provide 'typewriter-mode)
;;; typewriter-mode.el ends here
