;;; evil-numbers.el --- increment/decrement numbers like in vim

;; Copyright (C) 2011 by Michael Markert
;; Author: Michael Markert <markert.michael@googlemail.com>
;; Contributors:
;;               Matthew Fidler <matthew.fidler@gmail.com>
;;               Michael Markert <markert.michael@gmail.com>
;; URL: http://github.com/cofi/evil-numbers
;; Git-Repository: git://github.com/cofi/evil-numbers.git
;; Created: 2011-09-02
;; Version: 0.4
;; Keywords: numbers increment decrement octal hex binary

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
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

;; Increment / Decrement binary, octal, decimal and hex literals

;; works like C-a/C-x in vim, i.e. searches for number up to eol and then
;; increments or decrements and keep zero padding up

;; Known Bugs:
;; See http://github.com/cofi/evil-numbers/issues

;; Install:

;; (require 'evil-numbers)

;; and bind, for example:

;; (global-set-key (kbd "C-c +") 'evil-numbers/inc-at-pt)
;; (global-set-key (kbd "C-c -") 'evil-numbers/dec-at-pt)

;; or only in evil's normal and visual state:

;; (define-key evil-normal-state-map (kbd "C-c +") 'evil-numbers/inc-at-pt)
;; (define-key evil-visual-state-map (kbd "C-c +") 'evil-numbers/inc-at-pt)
;;
;; (define-key evil-normal-state-map (kbd "C-c -") 'evil-numbers/dec-at-pt)
;; (define-key evil-visual-state-map (kbd "C-c -") 'evil-numbers/dec-at-pt)

;; Usage:
;; Go and play with your numbers!

;;; Code:

;;;###autoload
(defun evil-numbers/inc-at-pt (amount &optional no-region)
  "Increment the number at point or after point before end-of-line by `amount'.
When region is selected, increment all numbers in the region by `amount'

NO-REGION is internal flag that allows
`evil-numbers/inc-at-point' to be called recursively when
applying the regional features of `evil-numbers/inc-at-point'.

"
  (interactive "p*")
  (cond
   ((and (not no-region) (region-active-p))
    (let (deactivate-mark
          (rb (region-beginning))
          (re (region-end)))
      (save-excursion
        (save-match-data
          (goto-char rb)
          (while (re-search-forward "\\(?:0\\(?:[Bb][01]+\\|[Oo][0-7]+\\|[Xx][0-9A-Fa-f]+\\)\\|-?[0-9]+\\)" re t)
            (evil-numbers/inc-at-pt amount 'no-region)
            ;; Undo vim compatability.
            (forward-char 1)))))
    (setq deactivate-mark t))
   (t
    (save-match-data
      (if (not (evil-numbers/search-number))
          (error "No number at point or until end of line")
        (or
         ;; find binary literals
         (evil-numbers/search-and-replace "0[bB][01]+" "01" "\\([01]+\\)" amount 2)

         ;; find octal literals
         (evil-numbers/search-and-replace "0[oO][0-7]+" "01234567" "\\([0-7]+\\)" amount 8)

         ;; find hex literals
         (evil-numbers/search-and-replace "0[xX][0-9a-fA-F]*"
                                          "0123456789abcdefABCDEF"
                                          "\\([0-9a-fA-F]+\\)" amount 16)

         ;; find decimal literals
         (progn
           (skip-chars-backward "0123456789")
           (skip-chars-backward "-")
           (when (looking-at "-?\\([0-9]+\\)")
             (replace-match
              (format (format "%%0%dd" (- (match-end 1) (match-beginning 1)))
                      (+ amount (string-to-number (match-string 0) 10))))
             ;; Moves point one position back to conform with Vim
             (forward-char -1)
             t))
         (error "No number at point or until end of line")))))))

;;;###autoload
(defun evil-numbers/dec-at-pt (amount)
  "Decrement the number at point or after point before end-of-line by `amount'.

If a region is active, decrement all the numbers at a point by `amount'.

This function uses `evil-numbers/inc-at-pt'"
  (interactive "p*")
  (evil-numbers/inc-at-pt (- amount)))

;;; utils

(defun evil-numbers/search-number ()
  "Return non-nil if a binary, octal, hexadecimal or decimal literal at or after point.
If point is already within or after a literal it stays.

The literals have to be in the following forms:
binary: 0[bB][01]+, e.g. 0b101 or 0B0
octal: 0[oO][0-7]+, e.g. 0o42 or 0O5
hexadecimal 0[xX][0-9a-fA-F]+, e.g. 0xBEEF or 0Xcafe
decimal: [0-9]+, e.g. 42 or 23"
  (or
   ;; numbers or format specifier in front
   (looking-back (rx (or (+? digit)
                        (and "0" (or (and (in "bB") (*? (in "01")))
                                  (and (in "oO") (*? (in "0-7")))
                                  (and (in "xX") (*? (in digit "A-Fa-f"))))))))
   ;; search for number in rest of line
   ;; match 0 of specifier or digit, being in a literal and after specifier is
   ;; handled above
   (and
	(re-search-forward "[[:digit:]]" (point-at-eol) t)
	(or
	 (not (memq (char-after) '(?b ?B ?o ?O ?x ?X)))
	 (/= (char-before) ?0)
	 (and (> (point) 2)				; Should also take bofp into consideration
		  (not (looking-back "\\W0" 2)))
	 ;; skip format specifiers and interpret as bool
	 (<= 0 (skip-chars-forward "bBoOxX"))))))

(defun evil-numbers/search-and-replace (look-back skip-back search-forward inc base)
  "When looking back at `LOOK-BACK' skip chars `SKIP-BACK'backwards and replace number incremented by `INC' in `BASE' and return non-nil."
  (when (looking-back look-back)
    (skip-chars-backward skip-back)
    (search-forward-regexp search-forward)
    (replace-match (evil-numbers/format (+ inc (string-to-number (match-string 1) base))
                                        (length (match-string 1))
                                        base))
	;; Moves point one position back to conform with Vim
	(forward-char -1)
    t))

(defun evil-numbers/format (num width base)
  "Format `NUM' with at least `WIDTH' space in `BASE'"
  (cond
   ((= base 2) (evil-numbers/format-binary num width))
   ((= base 8) (format (format "%%0%do" width) num))
   ((= base 16) (format (format "%%0%dX" width) num))
   (t "")))

(defun evil-numbers/format-binary (number &optional width fillchar)
  "Format `NUMBER' as binary.
Fill up to `WIDTH' with `FILLCHAR' (defaults to ?0) if binary
representation of `NUMBER' is smaller."
  (let (nums
        (fillchar (or fillchar ?0)))
    (while (> number 0)
      (push (number-to-string (% number 2)) nums)
      (setq number (truncate number 2)))
    (let ((len (length nums)))
      (apply #'concat
             (if (and width (< len width))
                 (make-string (- width len) fillchar)
               "")
             nums))))

(provide 'evil-numbers)
;;; evil-numbers.el ends here
