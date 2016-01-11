;;; evil-nerd-commenter.el --- Comment/uncomment lines efficiently. Like Nerd Commenter in Vim

;; Copyright (C) 2013-2015, Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/evil-nerd-commenter
;; Version: 2.3
;; Keywords: commenter vim line evil
;;
;; This file is not part of GNU Emacs.

;;; Credits:

;; - Lally Oppenheimer added the support for text-object in Evil
;; - Tom Willemse provided the fix to make Emacs 24.4 work

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
;; This program emulates nerd-commenter.vim by Marty Grenfell.
;;
;; It helps you comment/uncomment multiple lines without selecting them.
;;
;; `M-x evilnc-default-hotkeys` assigns hotkey `M-;` to `evilnc-comment-or-uncomment-lines`
;;
;; `M-x evilnc-comment-or-uncomment-lines` comment or uncomment lines.
;;
;; `M-x evilnc-quick-comment-or-uncomment-to-the-line` will comment/uncomment
;; from current line to specified line.
;; The last digit(s) of line number is parameter of the command.
;;
;; For example, `C-u 9 evilnc-quick-comment-or-uncomment-to-the-line` comments
;; code from current line to line 99 if you current line is 91.
;;
;; Though this program could be used *independently*, though I highly recommend
;; using it with Evil (https://bitbucket.org/lyro/evil/)
;;
;; Evil makes you take advantage of power of Vi to comment lines.
;; For example, you can press key `99,ci` to comment out 99 lines.
;;
;; Setup:
;;
;; Use case 1,
;; If you use comma as leader key, as most Vim users do, setup is one liner,
;; (evilnc-default-hotkeys)
;;
;; Use case 2,
;; If you use evil-leader and its default leader key,
;; insert below setup into your ~/.emacs instead,
;;
;; (global-set-key (kbd "M-;") 'evilnc-comment-or-uncomment-lines)
;;
;; (require 'evil-leader)
;; (global-evil-leader-mode)
;; (evil-leader/set-key
;;   "ci" 'evilnc-comment-or-uncomment-lines
;;   "cl" 'evilnc-quick-comment-or-uncomment-to-the-line
;;   "ll" 'evilnc-quick-comment-or-uncomment-to-the-line
;;   "cc" 'evilnc-copy-and-comment-lines
;;   "cp" 'evilnc-comment-or-uncomment-paragraphs
;;   "cr" 'comment-or-uncomment-region
;;   "cv" 'evilnc-toggle-invert-comment-line-by-line
;;   "\\" 'evilnc-comment-operator
;;   )
;;
;; See https://github.com/redguardtoo/evil-nerd-commenter for more use cases.

;;; Code:

(autoload 'count-lines "simple")

(defvar evilnc-invert-comment-line-by-line nil
  "If t then invert region comment status line by line.
Please note it has NOT effect on evil text object!")

(defvar evilnc-comment-both-snippet-html nil
  "Comment both embedded snippet and HTML tag if they are mixed in one line.
`web-mode' required.")

(defun evilnc--count-lines (beg end)
  "Assume BEG less than END."
  (let (rlt)
    (setq rlt (count-lines beg end))
    (save-excursion
      (goto-char beg)
      (if (> beg (line-beginning-position))
          (setq rlt (1+ rlt))))
    rlt))

(defun evilnc--goto-line (line-num)
  "Shamelessly copied from `goto-line'.  Goto line with LINE-NUM."
  (save-restriction
    (widen)
    (goto-char (point-min))
    (if (eq selective-display t)
      (re-search-forward "[\n\C-m]" nil 'end (1- line-num))
      (forward-line (1- line-num)))))

(defun evilnc--web-mode-is-comment (&optional pos)
  "Check whether the code at POS is comment.
`web-mode' removes its API, so create our own."
  (unless pos (setq pos (point)))
  (not (null (or (eq (get-text-property pos 'tag-type) 'comment)
                 (eq (get-text-property pos 'block-token) 'comment)
                 (eq (get-text-property pos 'part-token) 'comment)))))

(defun evilnc--fix-buggy-major-modes ()
  "Fix major modes whose comment regex is buggy.
See http://lists.gnu.org/archive/html/bug-gnu-emacs/2013-03/msg00891.html."
  (if (eq major-mode 'autoconf-mode)
    ;; since comment-use-syntax is nil in autoconf.el, the comment-start-skip need
    ;; make sure its first parenthesized expression match the string exactly before
    ;; the "dnl", check the comment-start-skip in lisp-mode for sample.
    ;; See code in (defun comment-search-forward) from emacs 24.2.3:
    ;; (if (not comment-use-syntax)
    ;;     (if (re-search-forward comment-start-skip limit noerror)
    ;;     (or (match-end 1) (match-beginning 0)))
    ;;     (do-something))
    ;; My regex makes sure (match-end 1) return the position of comment starter
    (if (and (boundp 'comment-use-syntax) (not comment-use-syntax))
        ;; Maybe autoconf.el will (setq comment-use-syntax t) in the future?
        (setq comment-start-skip "^\\(\\s*\\)\\(dnl\\|#\\) +"))))

(defun evilnc--operation-on-lines-or-region (fn &optional num)
  "Apply FN on NUM lines or selected region."
  (cond
   ;; NO region is selected
   ((not (region-active-p))
    (let ((b (line-beginning-position)) e)
      (save-excursion
        (forward-line (- num 1))
        (setq e (line-end-position)))
      (funcall fn b e)))

   ;; Select region inside ONE line
   ((and (<= (line-beginning-position) (region-beginning))
          (<= (region-end) (line-end-position)))
    (cond
     ;; Well, looks current comment syntax is NOT fit for comment out a region.
     ;; So we also need hack the comment-start and comment-end
     ((and (string= "" comment-end)
           (member major-mode '(java-mode
                                javascript-mode
                                js-mode
                                js2-mode
                                js3-mode
                                c++-mode
                                objc-mode)))
      (let ((comment-start-old comment-start)
            (comment-end-old comment-end)
            (comment-start-skip-old comment-start-skip)
            (comment-end-skip-old comment-end-skip))

        ;; use C comment syntax temporarily
        (setq comment-start "/* ")
        (setq comment-end " */")
        (setq comment-start-skip "\\(//+\\|/\\*+\\)\\s *")
        (setq comment-end-skip "[ 	]*\\(\\s>\\|\\*+/\\)")

        (funcall fn (region-beginning) (region-end))

        ;; Restore the original comment syntax
        (setq comment-start comment-start-old)
        (setq comment-end comment-end-old)
        (setq comment-start-skip comment-start-skip-old)
        (setq comment-end-skip comment-end-skip-old)))
     ;; just comment out the region
     (t (funcall fn (region-beginning) (region-end)))))

   ;; Select more than one line
   (t
    ;; selected region spans MORE than one line
    (save-excursion
      (let ((b (region-beginning))
            (e (region-end)))
        ;; Another work around for evil-visual-line bug:
        ;; In evil-mode, if we use hotkey V or `M-x evil-visual-line` to select line,
        ;; the (line-beginning-position) of the line which is after the last selected
        ;; line is always (region-end)! Don't know why.
        (if (and (> e b)
                 (save-excursion (goto-char e) (= e (line-beginning-position)))
                 (boundp 'evil-state) (eq evil-state 'visual))
            (setq e (1- e)))

        (goto-char b)
        (setq b (line-beginning-position))
        (goto-char e)
        (setq e (line-end-position))
        (funcall fn b e)
        )))
   ))

(defun evilnc--get-one-paragraph-region ()
  "Select a paragraph which has NO empty line."
  (let (b e)
    (save-excursion
      (setq b (re-search-backward "^[ \t]*$" nil t))
      (if b (progn
              (forward-line)
              (setq b (line-beginning-position))
              )
        (setq b 1)
        ))
    (save-excursion
      (setq e (re-search-forward "^[ \t]*$" nil t))
      (if e (progn
              (forward-line -1)
              (setq e (line-end-position))
              )
        (setq e (point-max))
        ))

    (list b e)
    ))

(defun evilnc--in-comment-p (pos)
  "Check whether the code at POS is comment by comparing font face."
  (interactive)
  (let ((fontfaces (get-text-property pos 'face)))
    (when (not (listp fontfaces))
      (setf fontfaces (list fontfaces)))
    (delq nil
          (mapcar #'(lambda (f)
                      ;; learn this trick from flyspell
                      (or (eq f 'font-lock-comment-face)
                          (eq f 'font-lock-comment-delimiter-face)))
                  fontfaces))))

(defun evilnc--extend-to-whole-comment (beg end)
  "Extend the comment region defined by BEG and END so ALL comment is included."
  (interactive)
  (if (evilnc--in-comment-p beg)
      (save-excursion
        (let ((newbeg beg)
              (newend end))

          ;; extend the beginning
          (goto-char newbeg)
          (while (and (>= newbeg (line-beginning-position)) (evilnc--in-comment-p newbeg))
            (setq newbeg (1- newbeg)))

          ;; make sure newbeg is at the beginning of the comment
          (if (< newbeg beg) (setq newbeg (1+ newbeg)))

          ;; extend the end
          (goto-char newend)
          (while (and (<= newend (line-end-position)) (evilnc--in-comment-p newend))
            (setq newend (1+ newend)))
          ;; make sure newend is at the end of the comment
          (if (> newend end) (setq newend (1- newend)))

          (list newbeg newend)
          ))
    (list beg end)
    ))

(defun evilnc--invert-comment (beg end)
  "Scan the region from BEG to END line by line, invert its comment status."
  (let (done b e)
    (save-excursion
      (goto-char end)
      ;; comment (line-beginning-position line-end-position)
      ;; (setq old-b (line-beginning-position)
      ;; (forward-line -1)
      ;; (if (= old-b (line-beginning-position)) we did not move, out of loop
      ;; (if (<= (line-end-position) beg)), out of region, out of loop
      (while (not done)
        (setq b (line-beginning-position))
        (setq e (line-end-position))
        (funcall (if (comment-only-p b e)
                     'uncomment-region 'comment-region)
                 b e)

        (forward-line -1)
        (if (or (= (line-beginning-position) b) (< (line-end-position) beg))
          (setq done t))
        ))))

(defun evilnc--working-on-region (beg end fn)
  "Region from BEG to END is applied with operation FN.
Code snippets embedded in Org-mode is identified and right `major-mode' is used."
  (let (pos
        info
        lang
        lang-f
        old-flag)
    (when (and (eq major-mode 'org-mode)
               (fboundp 'org-edit-src-find-region-and-lang))
      (setq info (org-edit-src-find-region-and-lang)))

    (when info
      (setq lang (or (cdr (assoc (nth 2 info) org-src-lang-modes))
                     (nth 2 info)))
      (setq lang (if (symbolp lang) (symbol-name lang) lang))
      (setq lang-f (intern (concat lang "-mode"))))

    ;; turn on 3rd party language's major-mode temporarily
    (if lang-f (funcall lang-f))

    (if evilnc-invert-comment-line-by-line
        (evilnc--invert-comment beg end)
      (funcall fn beg end))

    ;; turn off  3rd party language's major-mode temporarily and clean the shit
    (when lang-f
      ;; avoid org file automatically collapsed
      (setq pos (point))
      (org-mode)
      ;; just goto the root element
      (condition-case nil
          (outline-up-heading 1)
        (error
       (message "in the beginning ...")))
      ;; expand current node because by default (org-mode) will collapse all nodes
      (org-show-subtree)
      (goto-char pos))
    ))

(defun evilnc--warn-on-web-mode (is-comment)
  (let ((comment-operation (concat "web-mode-"
                                   (if is-comment "comment-" "uncomment-")
                                   web-mode-engine
                                   "-block")))
    (unless (intern-soft comment-operation)
      (message "defun %s NOT implemented in web-mode! DIY or raise issue to its maintainer."
               comment-operation))
    is-comment))

(defun evilnc--web-mode-is-region-comment (beg end)
  (let (rlt)
    (setq rlt (and (save-excursion
                     (goto-char beg)
                     (goto-char (line-end-position))
                     (re-search-backward "^\\|[^[:space:]]")
                     (evilnc--web-mode-is-comment))
                   (evilnc--web-mode-is-comment (/ (+ beg end) 2))
                   (save-excursion
                     (goto-char end)
                     (back-to-indentation)
                     (evilnc--web-mode-is-comment))))
    rlt))

(defun evilnc--web-mode-do-current-line ()
  "In `web-mode', have to select whole line to comment."
  (let (first-char-is-snippet e)

    (save-excursion
      (goto-char (line-beginning-position))
      (skip-chars-forward "[:space:]" (line-end-position))
      (setq first-char-is-snippet (get-text-property (point) 'block-side)))

    ;; comment the snippet block at first
    (when (and evilnc-comment-both-snippet-html (not first-char-is-snippet))
      (save-excursion
        (let (fired)
          (goto-char (line-beginning-position))
          ;; please note (line-beginning-position) is changing in (while)
          (while (< (point) (line-end-position))
            (forward-char)
            (if (get-text-property (point) 'block-side)
                (when (not fired)
                  (save-excursion
                    (push-mark (1+ (point)) t t)
                    (goto-char (point))
                    (web-mode-comment-or-uncomment))
                  (setq fired t))
              (setq fired nil))))))

    ;; comment the html line
    ;; To comment one line ONLY, you need select a line at first,
    ;; in order to work around web-mode "feature".
    (push-mark (setq e (line-end-position)) t t)
    (goto-char (line-beginning-position))
    (skip-chars-forward "[:space:]" e)
    (evilnc--warn-on-web-mode (evilnc--web-mode-is-region-comment (point) e))
    (web-mode-comment-or-uncomment)))

(defun evilnc--web-mode-comment-or-uncomment (beg end)
  "Comment/uncomment line by line from BEG to END.
DO-COMMENT decides we comment or uncomment."

  ;; end will change when you comment line by line
  (let (line-cnt tmp)
    ;; make sure beg <= end
    (when (> beg end)
      (setq tmp beg)
      (setq beg end)
      (setq end tmp))

    ;; start (un)comment
    (save-excursion
      (setq line-cnt (evilnc--count-lines beg end))
      (goto-char beg)
      (while (> line-cnt 0)
        (evilnc--web-mode-do-current-line)
        (forward-line)
        (setq line-cnt (1- line-cnt))))))

(defun evilnc--comment-or-uncomment-region (beg end)
  "Comment or uncommment region from BEG to END."
  (cond
   ((eq major-mode 'web-mode)
    ;; elixir is not supported in web-mode for now
    (unless (fboundp 'web-mode-comment-elixir-block)
      (defalias 'web-mode-comment-elixir-block 'web-mode-comment-erb-block)
      (defalias 'web-mode-uncomment-elixir-block 'web-mode-uncomment-erb-block))
    (evilnc--web-mode-comment-or-uncomment beg end))
   (t
    (evilnc--working-on-region beg end 'comment-or-uncomment-region))))

(defun evilnc--current-line-num ()
  "Get current line number."
  (save-restriction
    (widen)
    (save-excursion
      (beginning-of-line)
      (1+ (count-lines 1 (point))))))

(defun evilnc--find-dst-line-num (UNITS)
  "Find closet line whose line number ends with digit UNITS.
Given UNITS as 5, line 5, line 15, and line 25 are good candidates.
If UNITS is 16, line 16, line 116, and line 216 are good candidates."
  (let ((cur-line-num (evilnc--current-line-num))
        dst-line-num
        (r 1)
        (l (length (number-to-string UNITS))))
    (while (> l 0)
      (setq r (* r 10))
      (setq l (- l 1)))
    (if (>= (mod cur-line-num r) UNITS)
        (setq UNITS (+ UNITS r))
      )
    (setq dst-line-num (+ cur-line-num (- UNITS (mod cur-line-num r))))
    ))

;; ==== below this line are public commands

;;;###autoload
(defun evilnc-comment-or-uncomment-paragraphs (&optional NUM)
  "Comment or uncomment NUM paragraph(s).
A paragraph is a continuation non-empty lines.
Paragraphs are separated by empty lines."
  (interactive "p")
  (let ((i 0)
        rlt
        (b (point-max))
        (e 0)
        )
    (catch 'break
      (while (< i NUM)
        (setq i (1+ i))
        (setq rlt (evilnc--get-one-paragraph-region))
        (setq b (if (< (nth 0 rlt) b) (nth 0 rlt) b))
        (setq e (if (> (nth 1 rlt) e) (nth 1 rlt) e))

        ;; prepare for the next paragraph
        (if (and rlt (< i NUM))
            (progn
              ;; e should be the end of last non-empty line
              (goto-char e)

              ;; move to an empty line
              (forward-line)

              ;; move to next non-empty line
              (re-search-forward "^[ \t]*[^ \t]" nil t)

              (if (<= (line-beginning-position) e)
                  (throw 'break i)))
          (throw 'break i))
        ))

    (when (<= b e)
      (save-excursion
        (evilnc--fix-buggy-major-modes)
        (evilnc--comment-or-uncomment-region b e)))
    ))

;;;###autoload
(defun evilnc-comment-or-uncomment-to-the-line (&optional LINENUM)
  "Comment or uncomment from current line to LINENUM line."
  (interactive "nLine: ")
  (if (not (region-active-p))
      (let ((b (line-beginning-position))
            (e (line-end-position)))
        (save-excursion
          (evilnc--goto-line LINENUM)
          (if (< (line-beginning-position) b)
              (setq b (line-beginning-position)))
          (if (> (line-end-position) e)
              (setq e (line-end-position)))
          (evilnc--fix-buggy-major-modes)
          (evilnc--comment-or-uncomment-region b e)
          ))))

;;;###autoload
(defun evilnc-quick-comment-or-uncomment-to-the-line (&optional UNITS)
  "Comment/uncomment to line number by last digit(s) whose value is UNITS.
For exmaple, you can use either \
\\<M-53>\\[evilnc-quick-comment-or-uncomment-to-the-line] \
or \\<M-3>\\[evilnc-quick-comment-or-uncomment-to-the-line] \
to comment to the line 6453"
  (interactive "p")
  (let ((dst-line-num (evilnc--find-dst-line-num UNITS)))
    (evilnc-comment-or-uncomment-to-the-line dst-line-num)
    (evilnc--goto-line (+ 1 dst-line-num))
    ))

;;;###autoload
(defun evilnc-toggle-invert-comment-line-by-line ()
  "Please note this command may NOT work on complex evil text objects."
  (interactive)
  (if evilnc-invert-comment-line-by-line
      (setq evilnc-invert-comment-line-by-line nil)
    (setq evilnc-invert-comment-line-by-line t)
    )
  (message (if evilnc-invert-comment-line-by-line
               "Each line's comment status will be inverted"
             "Each line's comment status will NOT be inverted")))

;;;###autoload
(defun evilnc-toggle-comment-empty-lines ()
  "Toggle the flag which decide wether empty line will be commented."
  (interactive)
  (if comment-empty-lines
      (setq comment-empty-lines nil)
    (setq comment-empty-lines t)
    )
  (message (if comment-empty-lines
               "Empty line(s) will be commented"
             "Empty line(s) will NOT be commented")))

;;;###autoload
(defun evilnc-comment-or-uncomment-lines (&optional NUM)
  "Comment or uncomment NUM lines.  NUM could be negative.

Case 1: If no region selected, comment/uncomment on current line.
If NUM>1, comment/uncomment extra N-1 lines from next line.

Case 2: Selected region is expanded to make it contain whole lines.
Then we comment/uncomment the expanded region.  NUM is ignored.

Case 3: If a region inside of ONE line is selected,
we comment/uncomment that region.
CORRECT comment syntax will be used for C++/Java/Javascript."
  (interactive "p")
  ;; donot move the cursor
  ;; support negative number
  (cond
   ((and (= 1 NUM) (string-match "^[ \t]*$" (buffer-substring-no-properties (line-beginning-position) (line-end-position))))
    ;; comment on current empty line
    (comment-dwim nil))
   (t
    (save-excursion
      (when (< NUM 0)
        (forward-line (1+ NUM))
        (setq NUM (- 0 NUM)))
      (evilnc--operation-on-lines-or-region '(lambda (b e)
                                               (evilnc--fix-buggy-major-modes)
                                               (evilnc--comment-or-uncomment-region b e))
                                            NUM))
    )))

;;;###autoload
(defun evilnc-copy-and-comment-lines (&optional NUM)
  "Copy&paste NUM lines and comment out original lines.
NUM could be negative.

Case 1: If no region selected, operate on current line.
if NUM>1, comment/uncomment extra N-1 lines from next line

Case 2: Selected region is expanded to make it contain whole lines.
Then we operate the expanded region.  NUM is ignored."
  (interactive "p")
  ;; support negative number
  (when (< NUM 0)
    (forward-line (1+ NUM))
    (setq NUM (- 0 NUM)))

  (evilnc--operation-on-lines-or-region
   '(lambda (beg end)
      (evilnc--fix-buggy-major-modes)
      (let ((str (buffer-substring-no-properties beg end)))
        (goto-char end)
        (newline 1)
        (insert-before-markers str)
        (comment-region beg end)
        ))
   NUM))

;; {{ for non-evil user only
;;;###autoload
(defun evilnc-copy-to-line (&optional LINENUM)
  "Copy from the current line to LINENUM line.  For non-evil user only."
  (interactive "nCopy to line: ")
  (if (not (region-active-p))
      (let ((b (line-beginning-position))
            (e (line-end-position)))
        (save-excursion
          (evilnc--goto-line LINENUM)
          (if (< (line-beginning-position) b)
              (setq b (line-beginning-position)))
          (if (> (line-end-position) e)
              (setq e (line-end-position)))
          (kill-new (buffer-substring-no-properties b e))
          ))))

;;;###autoload
(defun evilnc-kill-to-line (&optional LINENUM)
  "Kill from the current line to the LINENUM line.  For non-evil user only."
  (interactive "NKill to line: ")
  (if (not (region-active-p))
      (let ((b (line-beginning-position))
            (e (line-end-position)))
        (save-excursion
          (evilnc--goto-line LINENUM)
          (if (< (line-beginning-position) b)
              (setq b (line-beginning-position)))
          (if (> (line-end-position) e)
              (setq e (line-end-position)))
          ;; +1 because we need remove the CR
          (setq e (+ 1 e))
          (if (> e (point-max)) (setq e (point-max)))
          (kill-region b e)
          ))))

;;;###autoload
(defun evilnc-version ()
  "The version number."
  (interactive)
  (message "2.3"))

;;;###autoload
(defun evilnc-default-hotkeys ()
  "Set the hotkeys of evil-nerd-comment."
  (interactive)

  ;; Install hotkeys for Emacs mode
  (global-set-key (kbd "M-;") 'evilnc-comment-or-uncomment-lines)
  (global-set-key (kbd "C-c l") 'evilnc-quick-comment-or-uncomment-to-the-line)
  (global-set-key (kbd "C-c c") 'evilnc-copy-and-comment-lines)
  (global-set-key (kbd "C-c p") 'evilnc-comment-or-uncomment-paragraphs)

  ;; Install key bindings for evil
  (eval-after-load 'evil
    '(progn
       (define-key evil-normal-state-map ",ci" 'evilnc-comment-or-uncomment-lines)
       (define-key evil-normal-state-map ",cl" 'evilnc-quick-comment-or-uncomment-to-the-line)
       (define-key evil-normal-state-map ",ll" 'evilnc-quick-comment-or-uncomment-to-the-line)
       (define-key evil-normal-state-map ",cc" 'evilnc-copy-and-comment-lines)
       (define-key evil-normal-state-map ",cp" 'evilnc-comment-or-uncomment-paragraphs)
       (define-key evil-normal-state-map ",cr" 'comment-or-uncomment-region)
       (define-key evil-normal-state-map ",cv" 'evilnc-toggle-invert-comment-line-by-line)))

  ;; Install operator for evil text objects
  (eval-after-load 'evil-nerd-commenter-operator
    '(progn
       (define-key evil-normal-state-map ",," 'evilnc-comment-operator)
       (define-key evil-visual-state-map ",," 'evilnc-comment-operator)))
  )

;; Attempt to define the operator on first load.
;; Will only work if evil has been loaded
(eval-after-load 'evil
  '(require 'evil-nerd-commenter-operator))

(provide 'evil-nerd-commenter)

;;; evil-nerd-commenter.el ends here
