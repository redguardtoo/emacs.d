;;; haskell-bot.el --- A Lambdabot interaction mode

;; Copyright (C) 2004, 2005, 2006, 2007  Free Software Foundation, Inc.
;; Copyright (C) 2001  Chris Webb
;; Copyright (C) 1998, 1999  Guy Lapalme

;; Keywords: inferior mode, Bot interaction mode, Haskell

;;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.


;;; Commentary:

;; Purpose:
;;
;; To send a Haskell buffer to another buffer running a Bot
;; interpreter.
;;
;; This mode is derived from version 1.1 of Guy Lapalme's
;; haskell-hugs.el, which can be obtained from:
;;
;;   http://www.iro.umontreal.ca/~lapalme/Hugs-interaction.html
;;
;; This in turn was adapted from Chris Van Humbeeck's hugs-mode.el,
;; which can be obtained from:
;;
;;   http://www-i2.informatik.rwth-aachen.de/Forschung/FP/Haskell/hugs-mode.el
;;
;;
;; Installation:
;;
;; To use with Moss and Thorn's haskell-mode.el
;;
;;   http://www.haskell.org/haskell-mode
;;
;; add this to .emacs:
;;
;;   (add-hook 'haskell-mode-hook 'turn-on-haskell-bot)
;;
;;
;; Customisation:
;;
;; The name of the Bot interpreter is in haskell-bot-program-name.
;;
;; Arguments can be sent to the Bot interpreter when it is started by
;; setting haskell-bot-program-args (empty by default) to a list of
;; string args to pass it.  This value can be set interactively by
;; calling C-c C-s with an argument (i.e. C-u C-c C-s).
;;
;; `haskell-bot-hook' is invoked in the *bot* buffer once Bot is
;; started.
;;
;; All functions/variables start with `turn-{on,off}-haskell-bot' or
;; `haskell-bot-'.

;;; Code:

(require 'comint)

(defgroup haskell-bot nil
  "Major mode for interacting with an inferior Bot session."
  :group 'haskell
  :prefix "haskell-bot-")

(define-derived-mode haskell-bot-mode comint-mode "Lambdabot")

;; Bot interface:

(require 'comint)
(require 'shell)

(defvar haskell-bot-process nil
  "The active Bot subprocess corresponding to current buffer.")

(defvar haskell-bot-process-buffer nil
  "*Buffer used for communication with Bot subprocess for current buffer.")

(defcustom haskell-bot-program-name "lambdabot"
  "*The name of the Bot interpreter program."
  :type 'string
  :group 'haskell-bot)

(defcustom haskell-bot-program-args nil
  "*A list of string args to pass when starting the Bot interpreter."
  :type '(repeat string)
  :group 'haskell-bot)

(defvar haskell-bot-load-end nil
  "Position of the end of the last load command.")

(defvar haskell-bot-error-pos nil
  "Position of the end of the last load command.")

(defvar haskell-bot-send-end nil
  "Position of the end of the last send command.")

(defvar haskell-bot-comint-prompt-regexp
  "^lambdabot> "
  "A regexp that matches the Bot prompt.")

(defun haskell-bot-start-process (arg)
  "Start a Bot process and invoke `haskell-bot-hook' if not nil.
Prompt for a list of args if called with an argument."
  (interactive "P")
  (if arg
      ;; XXX [CDW] Fix to use more natural 'string' version of the
      ;; XXX arguments rather than a sexp.
      (setq haskell-bot-program-args
            (read-minibuffer (format "List of args for %s:"
                                     haskell-bot-program-name)
                             (prin1-to-string haskell-bot-program-args))))

  ;; Start the Bot process in a new comint buffer.
  (message "Starting Lambdabot process `%s'." haskell-bot-program-name)
  (setq haskell-bot-process-buffer
        (apply 'make-comint
               "lambdabot" haskell-bot-program-name nil
               haskell-bot-program-args))
  (setq haskell-bot-process
        (get-buffer-process haskell-bot-process-buffer))

  ;; Select Bot buffer temporarily.
  (set-buffer haskell-bot-process-buffer)
  (haskell-bot-mode)
  (setq comint-prompt-regexp haskell-bot-comint-prompt-regexp)

  ;; History syntax of comint conflicts with Haskell, e.g. !!, so better
  ;; turn it off.
  (setq comint-input-autoexpand nil)
  (setq comint-process-echoes nil)
  (run-hooks 'haskell-bot-hook)

  ;; Clear message area.
  (message ""))

(defun haskell-bot-wait-for-output ()
  "Wait until output arrives and go to the last input."
  (while (progn
	   (goto-char comint-last-input-end)
	   (not (re-search-forward comint-prompt-regexp nil t)))
    (accept-process-output haskell-bot-process)))

(defun haskell-bot-send (&rest string)
  "Send `haskell-bot-process' the arguments (one or more strings).
A newline is sent after the strings and they are inserted into the
current buffer after the last output."
  (haskell-bot-wait-for-output)        ; wait for prompt
  (goto-char (point-max))               ; position for this input
  (apply 'insert string)
  (comint-send-input)
  (setq haskell-bot-send-end (marker-position comint-last-input-end)))

(defun haskell-bot-show-bot-buffer ()
  "Go to the *bot* buffer."
  (interactive)
  (if (or (not haskell-bot-process-buffer)
          (not (buffer-live-p haskell-bot-process-buffer)))
      (haskell-bot-start-process nil))
  (pop-to-buffer  haskell-bot-process-buffer))

(provide 'haskell-bot)

;;; haskell-bot.el ends here
