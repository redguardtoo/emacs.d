;; -*- coding: utf-8; lexical-binding: t; -*-

;; avoid spell-checking doublon (double word) in certain major modes
(defvar flyspell-check-doublon t
  "Check doublon (double word) when calling `flyspell-highlight-incorrect-region'.")
 (make-variable-buffer-local 'flyspell-check-doublon)

(defvar my-default-spell-check-language "en_US"
  "Language used by aspell and hunspell CLI.")

(with-eval-after-load 'flyspell
  ;; {{ flyspell setup for web-mode
  (defun web-mode-flyspell-verify ()
    (let* ((f (get-text-property (- (point) 1) 'face))
           rlt)
      (cond
       ;; Check the words with these font faces, possibly.
       ;; This *blacklist* will be tweaked in next condition
       ((not (memq f '(web-mode-html-attr-value-face
                       web-mode-html-tag-face
                       web-mode-html-attr-name-face
                       web-mode-constant-face
                       web-mode-doctype-face
                       web-mode-keyword-face
                       web-mode-comment-face ;; focus on get html label right
                       web-mode-function-name-face
                       web-mode-variable-name-face
                       web-mode-css-property-name-face
                       web-mode-css-selector-face
                       web-mode-css-color-face
                       web-mode-type-face
                       web-mode-block-control-face)))
        (setq rlt t))
       ;; check attribute value under certain conditions
       ((memq f '(web-mode-html-attr-value-face))
        (save-excursion
          (search-backward-regexp "=['\"]" (line-beginning-position) t)
          (backward-char)
          (setq rlt (string-match "^\\(value\\|class\\|ng[A-Za-z0-9-]*\\)$"
                                  (thing-at-point 'symbol)))))
       ;; finalize the blacklist
       (t
        (setq rlt nil)))
      rlt))
  (put 'web-mode 'flyspell-mode-predicate 'web-mode-flyspell-verify)
  ;; }}

  ;; better performance
  (setq flyspell-issue-message-flag nil)

  ;; flyspell-lazy is outdated and conflicts with latest flyspell
  ;; It only improves the performance of flyspell so it's not essential.

  (defadvice flyspell-highlight-incorrect-region (around flyspell-highlight-incorrect-region-hack activate)
    (if (or flyspell-check-doublon (not (eq 'doublon (ad-get-arg 2))))
        ad-do-it)))

;; Logic:
;; If (aspell is installed) { use aspell}
;; else if (hunspell is installed) { use hunspell }
;; English dictionary is used.
;;
;; I prefer aspell because:
;; - aspell is older
;; - looks Kevin Atkinson still get some road map for aspell:
;; @see http://lists.gnu.org/archive/html/aspell-announce/2011-09/msg00000.html
(defun flyspell-detect-ispell-args (&optional run-together)
  "If RUN-TOGETHER is true, spell check the CamelCase words.
Please note RUN-TOGETHER makes aspell less capable.  So it should be used in `prog-mode-hook' only."
  (let* (args)
    (when ispell-program-name
      (cond
       ;; use aspell
       ((string-match "aspell$" ispell-program-name)
        ;; force the English dictionary, support Camel Case spelling check (tested with aspell 0.6)
        ;; For aspell's option "--lang", "two letter ISO 3166 country code after a underscore" is OPTIONAL.
        (setq args (list "--sug-mode=ultra" (format "--lang=%s" my-default-spell-check-language)))
        ;; "--run-together-min" could not be 3, see `check` in "speller_impl.cpp".
        ;; The algorithm is not precise.
        ;; Run `echo tasteTableConfig | aspell --lang=en_US -C --run-together-limit=16  --encoding=utf-8 -a` in shell.
        (when run-together
          (cond
           ;; Kevin Atkinson said now aspell supports camel case directly
           ;; https://github.com/redguardtoo/emacs.d/issues/796
           ((string-match-p "--camel-case"
                            (shell-command-to-string (concat ispell-program-name " --help")))
            (setq args (append args '("--camel-case"))))

           ;; old aspell uses "--run-together". Please note we are not dependent on this option
           ;; to check camel case word. wucuo is the final solution. This aspell options is just
           ;; some extra check to speed up the whole process.
           (t
            (setq args (append args '("--run-together" "--run-together-limit=16")))))))

       ;; use hunspell
       ((string-match "hunspell$" ispell-program-name)
        (setq args nil))))
    args))

;; Aspell Setup (recommended):
;; It's easy to set up aspell. So the details are skipped.
;;
;; Hunspell Setup:
;; 1. Install hunspell from http://hunspell.sourceforge.net/
;;
;; 2. Download openoffice dictionary extension from
;; http://extensions.openoffice.org/en/project/english-dictionaries-apache-openoffice
;;
;; 3. Say `dict-en.oxt' is downloaded. Rename it to `dict-en.zip' and unzip
;; the contents to a temporary folder. Got "en_US.dic" and "en_US.aff" in
;; that folder.
;;
;; 4. Hunspell's option "-d en_US" means finding dictionary "en_US"
;; Set `ispell-local-dictionary-alist' to set that option of hunspell
;;
;; 5. Copy "en_US.dic" and "en_US.aff" from that temporary folder to
;; the place for dictionary files. I use "~/usr_local/share/hunspell/".
;;
;; 6. Add that folder to shell environment variable "DICPATH"
;;
;; 7. Restart emacs so when hunspell is run by ispell/flyspell to make
;; DICPATH take effect
;;
;; hunspell searches a dictionary named "en_US" in the path specified by
;; `$DICPATH' by default.

(defvar my-force-to-use-hunspell nil
  "Force to use hunspell.  If nil, try to detect aspell&hunspell.")

(cond
 ;; use aspell
 ((and (not my-force-to-use-hunspell) (executable-find "aspell"))
  (setq ispell-program-name "aspell"))

 ;; use hunspell
 ((executable-find "hunspell")
  (setq ispell-program-name "hunspell")
  (setq ispell-local-dictionary "hunspelldict")
  (setq ispell-local-dictionary-alist
        (list (list "hunspelldict" "[[:alpha:]]" "[^[:alpha:]]" "[']" nil (list "-d" my-default-spell-check-language) nil 'utf-8))))
 (t (setq ispell-program-name nil)
    (message "You need install either aspell or hunspell for ispell")))

;; `ispell-cmd-args' contains *extra* arguments appending to CLI process
;; when (ispell-send-string). Useless!
;; `ispell-extra-args' is *always* used when start CLI aspell process
(setq-default ispell-extra-args (flyspell-detect-ispell-args t))

(defadvice ispell-word (around my-ispell-word activate)
  (let* ((old-ispell-extra-args ispell-extra-args))
    (ispell-kill-ispell t)
    ;; use emacs original arguments
    (setq ispell-extra-args (flyspell-detect-ispell-args))
    ad-do-it
    ;; restore our own ispell arguments
    (setq ispell-extra-args old-ispell-extra-args)
    (ispell-kill-ispell t)))

(defadvice flyspell-auto-correct-word (around my-flyspell-auto-correct-word activate)
  (let* ((old-ispell-extra-args ispell-extra-args))
    (ispell-kill-ispell t)
    ;; use emacs original arguments
    (setq ispell-extra-args (flyspell-detect-ispell-args))
    ad-do-it
    ;; restore our own ispell arguments
    (setq ispell-extra-args old-ispell-extra-args)
    (ispell-kill-ispell t)))

(defun text-mode-hook-setup ()
  ;; Turn off RUN-TOGETHER option when spell check text-mode
  (setq-local ispell-extra-args (flyspell-detect-ispell-args)))
(add-hook 'text-mode-hook 'text-mode-hook-setup)

(defun enable-flyspell-mode-conditionally (&optional turn-off)
  "Enable `flyspell-mode'.  If TURN-OFF is t, turn off it at the end."
  (when (and (not *no-memory*)
             ispell-program-name
             (executable-find ispell-program-name))
    ;; I don't use flyspell in text-mode because I often use Chinese.
    ;; I'd rather manually spell check the English text
    (flyspell-mode 1)
    ;; The purpose to turn on and turn off `flyspell-mode' is to load some
    ;; major mode's own predicate
    (if turn-off (flyspell-mode -1))))

;; You can also use "M-x ispell-word" or hotkey "M-$". It pop up a multiple choice
;; @see http://frequal.com/Perspectives/EmacsTip03-FlyspellAutoCorrectWord.html
(global-set-key (kbd "C-c s") 'flyspell-auto-correct-word)

(defun my-clean-aspell-dict ()
  "Clean ~/.aspell.pws (dictionary used by aspell)."
  (interactive)
  (let* ((dict (file-truename "~/.aspell.en.pws"))
         (lines (read-lines dict))
         ;; sort words
         (aspell-words (sort (cdr lines) 'string<)))
    (with-temp-file dict
      (insert (format "%s %d\n%s"
                        "personal_ws-1.1 en"
                        (length aspell-words)
                        (mapconcat 'identity aspell-words "\n"))))))

;; {{ langtool setup
(with-eval-after-load 'langtool
  (setq langtool-generic-check-predicate
        '(lambda (start end)
           ;; set up for `org-mode'
           (let* ((begin-regexp "^[ \t]*#\\+begin_\\(src\\|html\\|latex\\|example\\|quote\\)")
                  (end-regexp "^[ \t]*#\\+end_\\(src\\|html\\|latex\\|example\\|quote\\)")
                  (case-fold-search t)
                  (ignored-font-faces '(org-verbatim
                                        org-block-begin-line
                                        org-meta-line
                                        org-tag
                                        org-link
                                        org-table
                                        org-level-1
                                        org-document-info))
                  (rlt t)
                  ff
                  th
                  b e)
             (save-excursion
               (goto-char start)

               ;; get current font face
               (setq ff (get-text-property start 'face))
               (if (listp ff) (setq ff (car ff)))

               ;; ignore certain errors by set rlt to nil
               (cond
                ((memq ff ignored-font-faces)
                 ;; check current font face
                 (setq rlt nil))
                ((or (string-match "^ *- $" (buffer-substring (line-beginning-position) (+ start 2)))
                     (string-match "^ *- $" (buffer-substring (line-beginning-position) (+ end 2))))
                 ;; dash character of " - list item 1"
                 (setq rlt nil))

                ((and (setq th (thing-at-point 'evil-WORD))
                      (or (string-match "^=[^=]*=[,.]?$" th)
                          (string-match "^\\[\\[" th)
                          (string-match "^=(" th)
                          (string-match ")=$" th)
                          (string= "w3m" th)))
                 ;; embedded code like =code= or org-link [[http://google.com][google]] or [[www.google.com]]
                 ;; langtool could finish checking before major mode prepare font face for all texts
                 (setq rlt nil))
                (t
                 ;; inside source block?
                 (setq b (re-search-backward begin-regexp nil t))
                 (if b (setq e (re-search-forward end-regexp nil t)))
                 (if (and b e (< start e)) (setq rlt nil)))))
             ;; (if rlt (message "start=%s end=%s ff=%s" start end ff))
             rlt))))
;; }}

(with-eval-after-load 'wucuo
  ;; {{ wucuo is used to check camel cased code.  Code is usually written
  ;; in English. If your code uses other language (Spanish?),
  ;; Un-comment and modify below two lines:

  ;; (setq wucuo-aspell-language-to-use "en")
  ;; (setq wucuo-hunspell-dictionary-base-name "en_US")

  ;; }}

  ;; do NOT turn on `flyspell-mode' automatically.
  ;; use `flyspell-buffer' instead
  (setq wucuo-flyspell-start-mode "lite")
  ;; spell check buffer every 10 mins
  (setq wucuo-update-interval 600))

(provide 'init-spelling)
