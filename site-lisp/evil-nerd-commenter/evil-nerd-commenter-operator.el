;;; evil-nerd-commenter-operator --- Provides an evil operator for evil-nerd-commenter

;; Copyright (C) 2013 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/evil-nerd-commenter
;; Version: 1.5.11
;; Keywords: commenter vim line evil
;;
;; This file is not part of GNU Emacs.

;;; License:

;; This file is part of evil-nerd-commenter
;;
;; evil-nerd-commenter is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; evil-nerd-commenter is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; Provides an operator for evil-mode.

;;; Code:

(require 'evil)

(evil-define-operator evilnc-comment-operator (beg end type register yank-handler)
  "Comments text from BEG to END with TYPE.
Save in REGISTER or in the kill-ring with YANK-HANDLER."
  (interactive "<R><x><y>")
  (unless register
    (let ((text (filter-buffer-substring beg end)))
      (unless (string-match-p "\n" text)
        ;; set the small delete register
        (evil-set-register ?- text))))
  (evil-yank beg end type register yank-handler)
  (cond
   ((eq type 'block)
    (let ((newpos (evilnc--extend-to-whole-comment beg end) ))
      (evil-apply-on-block #'evilnc--comment-or-uncomment-region (nth 0 newpos) (nth 1 newpos) nil)
      )
    )
   ((and (eq type 'line)
         (= end (point-max))
         (or (= beg end)
             (/= (char-before end) ?\n))
         (/= beg (point-min))
         (=  (char-before beg) ?\n))
    (evilnc--comment-or-uncomment-region (1- beg) end))
   ((eq type 'line)
    (evilnc--comment-or-uncomment-region beg end))
   (t
    (let ((newpos (evilnc--extend-to-whole-comment beg end) ))
      (evilnc--comment-or-uncomment-region (nth 0 newpos) (nth 1 newpos))
      )
    ))
  ;; place cursor on beginning of line
  (when (and (evil-called-interactively-p)
             (eq type 'line))
    (evil-first-non-blank)))

(define-key evil-normal-state-map evilnc-hotkey-comment-operator 'evilnc-comment-operator)
(define-key evil-visual-state-map evilnc-hotkey-comment-operator 'evilnc-comment-operator)

(provide 'evil-nerd-commenter-operator)

;;; evil-nerd-commenter-operator.el ends here
