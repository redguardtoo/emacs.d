;;; ace-pinyin.el --- Jump to Chinese characters using avy or ace-jump-mode

;; Copyright (C) 2015  Junpeng Qiu

;; Author: Junpeng Qiu <qjpchmail@gmail.com>
;; URL: https://github.com/cute-jumper/ace-pinyin
;; Version: 0.2
;; Package-Requires: ((avy "0.2.0") (pinyinlib "0.1.0"))
;; Keywords: extensions

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

;;                              _____________

;;                                ACE-PINYIN

;;                               Junpeng Qiu
;;                              _____________


;; Table of Contents
;; _________________

;; 1 Setup
;; 2 Usage
;; 3 Supported Commands
;; 4 Traditional Chinese Characters Support
;; 5 Disable Word Jumping Support
;; 6 Disable Punctuations Translation
;; 7 Other available commands
;; .. 7.1 `ace-pinyin-dwim'
;; .. 7.2 `ace-pinyin-jump-word'
;; 8 Demos
;; 9 Change Log
;; 10 Related Packages


;; [[file:http://melpa.org/packages/ace-pinyin-badge.svg]]
;; [[file:http://stable.melpa.org/packages/ace-pinyin-badge.svg]]

;; Jump to Chinese characters using `ace-jump-mode' or `avy'.

;; 使用 `avy' 或者 `ace-jump-mode' 跳转到中文字符。

;; [[file:http://melpa.org/packages/ace-pinyin-badge.svg]]
;; http://melpa.org/#/ace-pinyin

;; [[file:http://stable.melpa.org/packages/ace-pinyin-badge.svg]]
;; http://stable.melpa.org/#/ace-pinyin


;; 1 Setup
;; =======

;;   Install via [melpa].

;;   Or if you prefer to install this package manually:
;;   ,----
;;   | (add-to-list 'load-path "/path/to/ace-pinyin.el")
;;   | (require 'ace-pinyin)
;;   `----


;; [melpa] http://melpa.org/#/ace-pinyin


;; 2 Usage
;; =======

;;   By default this package is using `avy'. If you want to use
;;   `ace-jump-mode', set `ace-pinyin-use-avy' to `nil'.

;;   Note `ace-pinyin-use-avy' variable should be set *BEFORE* you call
;;   `ace-pinyin-global-mode' or `turn-on-ace-pinyin-mode'.

;;   Example config to use `ace-pinyin' globally:
;;   ,----
;;   | ;; (setq ace-pinyin-use-avy nil) ;; uncomment if you want to use `ace-jump-mode'
;;   | (ace-pinyin-global-mode +1)
;;   `----


;; 3 Supported Commands
;; ====================

;;   When using `avy', all `avy' commands (as of 05/06/2016) related to
;;   char/word jumping are supported:
;;   - `avy-goto-char'
;;   - `avy-goto-char-2'
;;   - `avy-goto-char-in-line'
;;   - `avy-goto-word-0'
;;   - `avy-goto-word-1'
;;   - `avy-goto-subword-0'
;;   - `avy-goto-subword-1'
;;   - `avy-goto-word-or-subword-1'

;;   When using `ace-jump-mode', the following command is supported:
;;   - `ace-jump-char-mode'

;;   When the `ace-pinyin-mode' is enabled, the supported commands will be
;;   able to jump to both Chinese and English characters/words. That is,
;;   you don't need remember extra commands or create extra key bindings in
;;   order to jump to Chinese characters. All you need to do is to enable
;;   the minor mode and use your `avy' or `ace-jump-mode' key bindings to
;;   jump to Chinese characters.

;;   In addition, you can also use English punctuations to jump to
;;   Chinese/English punctuations. For example, use `.' to jump to both `。'
;;   and `.', and `<' to jump to both `《' and `<' etc. Behind the scene,
;;   `ace-pinyin' uses [pinyinlib.el] to translate the letter to
;;   Simplified/Traditional Chinese characters and English punctuations to
;;   Chinese punctuations. To see the full list of punctuations that are
;;   supported, see [pinyinlib.el].

;;   Besides, all other packages using `ace-jump-mode' (or `avy') will also
;;   be able to handle Chinese characters. For example, if you've installed
;;   [ace-jump-zap], it will also be able to zap to a Chinese character by
;;   the first letter of pinyin. Note `ace-jump-zap' is implemented by
;;   using `ace-jump-mode', so you can't use `avy' in this case. You can
;;   check out my fork of `ace-jump-zap' using `avy': [avy-zap].


;; [pinyinlib.el] https://github.com/cute-jumper/pinyinlib.el

;; [ace-jump-zap] https://github.com/waymondo/ace-jump-zap

;; [avy-zap] https://github.com/cute-jumper/avy-zap


;; 4 Traditional Chinese Characters Support
;; ========================================

;;   By default, `ace-pinyin' only supports simplified Chinese characters.
;;   You can make `ace-pinyin' aware of traditional Chinese characters by
;;   the following setting:
;;   ,----
;;   | (setq ace-pinyin-simplified-chinese-only-p nil)
;;   `----


;; 5 Disable Word Jumping Support
;; ==============================

;;   By default, `ace-pinyin' will remap both word jumping and character
;;   jumping methods in `avy'. If you only want to remap character jumping
;;   methods, use:
;;   ,----
;;   | (setq ace-pinyin-treat-word-as-char nil)
;;   `----

;;   After setting this, the following commands in `avy' are not able to
;;   jump to Chinese characters:
;;   - `avy-goto-word-0'
;;   - `avy-goto-word-1'
;;   - `avy-goto-subword-0'
;;   - `avy-goto-subword-1'
;;   - `avy-goto-word-or-subword-1'


;; 6 Disable Punctuations Translation
;; ==================================

;;   If you don't like the punctuation support(/i.e./, using English
;;   punctuations to jump to both Chinese/English punctuations), use the
;;   following code to disable it:
;;   ,----
;;   | (setq ace-pinyin-enable-punctuation-translation nil)
;;   `----


;; 7 Other available commands
;; ==========================

;;   These commands are not provided in either `avy' or `ace-jump-mode'.
;;   They're provided in this package in case someone finds them useful.
;;   You need to assign key bindings for the commands if you want to use
;;   them.


;; 7.1 `ace-pinyin-dwim'
;; ~~~~~~~~~~~~~~~~~~~~~

;;   If called with no prefix, it can jump to both Chinese characters and
;;   English letters. If called with prefix, it can only jump to Chinese
;;   characters.


;; 7.2 `ace-pinyin-jump-word'
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~

;;   Using this command, you can jump to the start of a sequence of Chinese
;;   characters(/i.e./ Chinese word) by typing the sequence of the first
;;   letters of these character's pinyins. If called without prefix, this
;;   command will read user's input with a default timeout 1 second(You can
;;   customize the timeout value). If called with prefix, then it will read
;;   input from the minibuffer and starts search after you press enter.


;; 8 Demos
;; =======

;;   *WARNING*: The following demos are a little bit outdated.

;;   Enable `ace-pinyin-mode' and use `ace-jump-char-mode' to jump to
;;   Chinese characters: [./screencasts/ace-pinyin-jump-char.gif]

;;   If you have installed [ace-jump-zap], then enabling `ace-pinyin-mode'
;;   will also make `ace-jump-zap-to-char' capable of handling Chinese
;;   characters. [./screencasts/ace-jump-zap.gif]


;; [ace-jump-zap] https://github.com/waymondo/ace-jump-zap


;; 9 Change Log
;; ============

;;   UPDATE(2015-11-26): Now jumping to traditional Chinese characters is
;;   supported by setting `ace-pinyin-simplified-chinese-only-p' to `nil'.

;;   UPDATE(2016-05-01): Now `ace-pinyin' uses `avy' by default. If you
;;   want to use `ace-jump-mode', use:
;;   ,----
;;   | (setq ace-pinyin-use-avy nil)
;;   `----

;;   UPDATE(2016-05-02): A new variable `ace-pinyin-treat-word-as-char' is
;;   added and its default value is `t'. When this variable is `t',
;;   `ace-pinyin' remaps both word and character jumping commands in `avy'
;;   or `ace-jump-mode'. For example, if you're using `avy', setting this
;;   variable to `t' will make `avy-goto-word-*' and `avy-goto-subword-*'
;;   be able to jump to Chinese characters as well as English words.

;;   UPDATE(2015-05-05): Add `ace-pinyin-enable-punctuation-translation'.

;;   UPDATE(2015-05-05): Now `ace-pinyin' depends on [pinyinlib.el].


;; [pinyinlib.el] https://github.com/cute-jumper/pinyinlib.el


;; 10 Related Packages
;; ===================

;;   - [evil-find-char-pinyin]
;;   - [pinyinlib.el]
;;   - [fcitx.el]


;; [evil-find-char-pinyin]
;; https://github.com/cute-jumper/evil-find-char-pinyin

;; [pinyinlib.el] https://github.com/cute-jumper/pinyinlib.el

;; [fcitx.el] https://github.com/cute-jumper/fcitx.el

;;; Code:

(require 'avy)
(require 'pinyinlib)
(require 'ace-jump-mode nil t)

(eval-when-compile
  (declare-function subword-backward "subword"))

(defgroup ace-pinyin nil
  "Jump to Chinese characters using `avy' or `ace-jump-mode'."
  :group 'avy)

(defcustom ace-pinyin--jump-word-timeout 1
  "Seconds to wait for input."
  :type 'number
  :group 'ace-pinyin)

(defvar ace-pinyin-use-avy t
  "Use `avy' or `ace-jump-mode'. Default value is to use `avy'.
Changed since 2016-05-01.")

(defvar ace-pinyin-simplified-chinese-only-p t
  "Whether `ace-pinyin' should use only simplified Chinese or not.
Default value is only using simplified Chinese characters.")

(defvar ace-pinyin-treat-word-as-char t
  "Whether word related `avy-*' commands should be remampped.")

(defvar ace-pinyin-enable-punctuation-translation t
  "Enable punctuation support or not. ")

(defvar ace-pinyin--original-ace (symbol-function 'ace-jump-char-mode)
  "Original definition of `ace-jump-char-mode'.")

(defvar ace-pinyin--original-ace-word (symbol-function 'ace-jump-word-mode)
  "Original definition of `ace-jump-word-mode'.")

(defvar ace-pinyin--original-avy (symbol-function 'avy-goto-char)
  "Original definition of `avy-goto-char'.")

(defvar ace-pinyin--original-avy-2 (symbol-function 'avy-goto-char-2)
  "Original definition of `avy-goto-char-2'.")

(defvar ace-pinyin--original-avy-in-line (symbol-function 'avy-goto-char-in-line)
  "Original definition of `avy-goto-char-in-line'.")

(defvar ace-pinyin--original-avy-word-0 (symbol-function 'avy-goto-word-0)
  "Original definition of `avy-goto-word-0'.")

(defvar ace-pinyin--original-avy-word-1 (symbol-function 'avy-goto-word-1)
  "Original definition of `avy-goto-word-1'.")

(defvar ace-pinyin--original-avy-subword-0 (symbol-function 'avy-goto-subword-0)
  "Original definition of `avy-goto-subword-0'.")

(defvar ace-pinyin--original-avy-subword-1 (symbol-function 'avy-goto-subword-1)
  "Original definition of `avy-goto-subword-1'.")

(defun ace-pinyin--build-regexp (query-char &optional prefix)
  (pinyinlib-build-regexp-char query-char
                               (not ace-pinyin-enable-punctuation-translation)
                               (not ace-pinyin-simplified-chinese-only-p)
                               prefix))

(defun ace-pinyin--jump-impl (query-char &optional prefix)
  "Internal implementation of `ace-pinyin-jump-char'."
  (let ((regexp (ace-pinyin--build-regexp query-char prefix)))
    (if ace-pinyin-use-avy
        (avy-with avy-goto-char
          (avy--generic-jump regexp nil))
      (if ace-jump-current-mode (ace-jump-done))
      (if (eq (ace-jump-char-category query-char) 'other)
          (error "[AceJump] Non-printable character"))
      ;; others : digit , alpha, punc
      (setq ace-jump-query-char query-char)
      (setq ace-jump-current-mode 'ace-jump-char-mode)
      (ace-jump-do regexp))))

(defun ace-pinyin-jump-char (query-char)
  "AceJump with pinyin by QUERY-CHAR."
  (interactive (list (if ace-pinyin-use-avy
                         (read-char "char: ")
                       (read-char "Query Char:"))))
  (cond (ace-pinyin-mode
         (ace-pinyin--jump-impl query-char))
        (ace-pinyin-use-avy
         (funcall ace-pinyin--original-avy query-char))
        (t
         (funcall ace-pinyin--original-ace query-char))))

(defun ace-pinyin-jump-char-2 (char1 char2 &optional arg)
  "Ace-pinyin replacement of `avy-goto-char-2'."
  (interactive (list (read-char "char 1: ")
                     (read-char "char 2: ")
                     current-prefix-arg))
  (avy-with avy-goto-char-2
    (avy--generic-jump
     (pinyinlib-build-regexp-string (string char1 char2)
                                    (not ace-pinyin-enable-punctuation-translation)
                                    (not ace-pinyin-simplified-chinese-only-p))
     arg)))

(defun ace-pinyin-jump-char-in-line (char)
  "Ace-pinyn replacement of `avy-goto-char-in-line'."
  (interactive (list (read-char "char: " t)))
  (avy-with avy-goto-char
    (avy--generic-jump
     (ace-pinyin--build-regexp char nil)
     avy-all-windows
     (line-beginning-position)
     (line-end-position))))

(defun ace-pinyin-goto-word-0 (arg)
  "Ace-pinyin replacement of `avy-goto-word-0'."
  (interactive "P")
  (let ((avy-goto-word-0-regexp "\\b\\sw\\|\\cc"))
    (funcall ace-pinyin--original-avy-word-0 arg)))

(defun ace-pinyin-goto-word-1 (char &optional arg)
  "Ace-pinyin replacement of `avy-goto-word-1'."
  (interactive (list (read-char "char: " t)
                     current-prefix-arg))
  (avy-with avy-goto-word-1
    (let* ((str (string char))
           (regex (cond ((string= str ".")
                         "\\.")
                        ((and avy-word-punc-regexp
                              (string-match avy-word-punc-regexp str))
                         (regexp-quote str))
                        (t
                         (concat
                          "\\b"
                          str
                          (let ((chinese-regexp (ace-pinyin--build-regexp char t)))
                            (unless (string= chinese-regexp "")
                              (concat "\\|" chinese-regexp))))))))
      (avy--generic-jump regex arg))))

(defun ace-pinyin-goto-subword-0 (&optional arg predicate)
  "Ace-pinyin replacement of `avy-goto-subword-0'."
  (interactive "P")
  (require 'subword)
  (avy-with avy-goto-subword-0
    (let ((case-fold-search nil)
          (subword-backward-regexp
           "\\(\\(\\W\\|[[:lower:][:digit:]]\\)\\([!-/:@`~[:upper:]]+\\W*\\)\\|\\W\\w+\\|.\\cc\\)")
          candidates)
      (avy-dowindows arg
        (let ((syn-tbl (copy-syntax-table)))
          (dolist (char avy-subword-extra-word-chars)
            (modify-syntax-entry char "w" syn-tbl))
          (with-syntax-table syn-tbl
            (let ((ws (window-start))
                  window-cands)
              (save-excursion
                (goto-char (window-end (selected-window) t))
                (subword-backward)
                (while (> (point) ws)
                  (when (or (null predicate)
                            (and predicate (funcall predicate)))
                    (unless (get-char-property (point) 'invisible)
                      (push (cons (point) (selected-window)) window-cands)))
                  (subword-backward))
                (and (= (point) ws)
                     (or (null predicate)
                         (and predicate (funcall predicate)))
                     (not (get-char-property (point) 'invisible))
                     (push (cons (point) (selected-window)) window-cands)))
              (setq candidates (nconc candidates window-cands))))))
      (avy--process candidates (avy--style-fn avy-style)))))

(defun ace-pinyin-goto-subword-1 (char &optional arg)
  "Ace-pinyin replacement of `avy-goto-subword-1'."
  (interactive (list (read-char "char: " t)
                     current-prefix-arg))
  (avy-with avy-goto-subword-1
    (let* ((char (downcase char))
           (chinese-regexp (ace-pinyin--build-regexp char t)))
      (ace-pinyin-goto-subword-0
       arg (lambda () (or (eq (downcase (char-after)) char)
                      (string-match-p chinese-regexp (string (char-after)))))))))

(defun ace-pinyin--jump-word-1 (query)
  (let ((regexp
         (pinyinlib-build-regexp-string
          query
          (not ace-pinyin-enable-punctuation-translation)
          (not ace-pinyin-simplified-chinese-only-p))))
    (if ace-pinyin-use-avy
        (avy-with avy-goto-char
          (avy--generic-jump regexp nil))
      (if ace-jump-current-mode (ace-jump-done))

      (let ((case-fold-search nil))
        (when (string-match-p "[^a-z]" query)
          (error "[AcePinyin] Non-lower case character")))

      (setq ace-jump-current-mode 'ace-jump-char-mode)
      (ace-jump-do regexp))))

;;;###autoload
(defun ace-pinyin-jump-word (arg)
  "Jump to Chinese word.
If ARG is non-nil, read input from Minibuffer."
  (interactive "P")
  (if arg
      ;; Read input from minibuffer
      (ace-pinyin--jump-word-1 (read-string "Query Word: "))
    ;; Read input by using timer
    (message "Query word: ")
    (let (char string)
      (while (setq char (read-char nil nil ace-pinyin--jump-word-timeout))
        (setq string (concat string (char-to-string char)))
        (message (concat "Query word: " string)))
      (if string
          (ace-pinyin--jump-word-1 string)
        (error "[AcePinyin] Empty input, timeout")))))

;;;###autoload
(defun ace-pinyin-dwim (&optional prefix)
  "With PREFIX, only search Chinese.
Without PREFIX, search both Chinese and English."
  (interactive "P")
  (let ((query-char (if ace-pinyin-use-avy
                        (read-char "char: ")
                      (read-char "Query Char:"))))
    (ace-pinyin--jump-impl query-char prefix)))

;;;###autoload
(define-minor-mode ace-pinyin-mode
  "Toggle `ace-pinyin-mode'."
  nil
  " AcePY"
  :group ace-pinyin
  (if ace-pinyin-mode
      (if ace-pinyin-use-avy
          (progn
            (fset 'avy-goto-char 'ace-pinyin-jump-char)
            (fset 'avy-goto-char-2 'ace-pinyin-jump-char-2)
            (fset 'avy-goto-char-in-line 'ace-pinyin-jump-char-in-line)
            (when ace-pinyin-treat-word-as-char
              (fset 'avy-goto-word-0 'ace-pinyin-goto-word-0)
              (fset 'avy-goto-word-1 'ace-pinyin-goto-word-1)
              (fset 'avy-goto-subword-0 'ace-pinyin-goto-subword-0)
              (fset 'avy-goto-subword-1 'ace-pinyin-goto-subword-1)))
        (fset 'ace-jump-char-mode 'ace-pinyin-jump-char))
    (if ace-pinyin-use-avy
        (progn
          (fset 'avy-goto-char ace-pinyin--original-avy)
          (fset 'avy-goto-char-2 ace-pinyin--original-avy-2)
          (fset 'avy-goto-char-in-line ace-pinyin--original-avy-in-line)
          (fset 'avy-goto-word-0 ace-pinyin--original-avy-word-0)
          (fset 'avy-goto-word-1 ace-pinyin--original-avy-word-1)
          (fset 'avy-goto-subword-0 ace-pinyin--original-avy-subword-0)
          (fset 'avy-goto-subword-1 ace-pinyin--original-avy-subword-1))
      (fset 'ace-jump-char-mode ace-pinyin--original-ace))))

;;;###autoload
(define-globalized-minor-mode ace-pinyin-global-mode
  ace-pinyin-mode
  turn-on-ace-pinyin-mode
  :group 'ace-pinyin
  :require 'ace-pinyin)

;;;###autoload
(defun turn-on-ace-pinyin-mode ()
  "Turn on `ace-pinyin-mode'."
  (interactive)
  (ace-pinyin-mode +1))

;;;###autoload
(defun turn-off-ace-pinyin-mode ()
  "Turn off `ace-pinyin-mode'."
  (interactive)
  (ace-pinyin-mode -1))

(provide 'ace-pinyin)
;;; ace-pinyin.el ends here
