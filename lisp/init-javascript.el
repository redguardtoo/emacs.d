;; looks nodejs is more popular, if you prefer rhino, change to "js"
(setq inferior-js-program-command "node --interactive")

(require 'js-comint)
;; if use node.js, we need nice output
(setenv "NODE_NO_READLINE" "1")

;; may be in an arbitrary order
(eval-when-compile (require 'cl))

;; json
(setq auto-mode-alist (cons '("\\.json$" . json-mode) auto-mode-alist))
(setq auto-mode-alist (cons '("\\.jason$" . json-mode) auto-mode-alist))

;; {{ js2-mode or javascript-mode
(setq js2-use-font-lock-faces t
      js2-mode-must-byte-compile nil
      js2-idle-timer-delay 0.5 ;; could not be too big for real time syntax check
      js2-indent-on-enter-key t
      js2-skip-preprocessor-directives t
      js2-auto-indent-p t
      js2-bounce-indent-p t)

(setq javascript-common-imenu-regex-list
      '(("Controller" "\.controller( *'\\([^']+\\)" 1)
        ("Filter" "\.filter( *'\\([^']+\\)" 1)
        ("Factory" "\.factory( *'\\([^']+\\)" 1)
        ("Service" "\.service( *'\\([^']+\\)" 1)
        ("Directive" "\.directive( *'\\([^']+\\)" 1)
        ("Event" "\.\$on( *'\\([^']+\\)" 1)
        ("Config" "\.config( *function *( *\\([^\)]+\\)" 1)
        ("Config" "\.config( *\\[ *'\\([^']+\\)" 1)
        ("OnChange" " *\$('\\([^']*\\)').*\.change *( *function" 1)
        ("OnClick" " *\$('\\([^']*\\)').*\.click *( *function" 1)
        ("OnChange" "^ *\\([a-zA-Z0-9\.]+\\)\.change *( *function" 1)
        ("OnClick" "^ *\\([a-zA-Z0-9\.]+\\)\.click *( *function" 1)
        ("Watch" "\.\$watch( *'\\([^']+\\)" 1)
        ("Function" "function\\s-+\\([^ ]+\\) *(" 1)
        ("Function" " \\([^ ]+\\)\\s-*=\\s-*function\\s-*(" 1)))

;; js-mode imenu enhancement
;; @see http://stackoverflow.com/questions/20863386/idomenu-not-working-in-javascript-mode
(defun mo-js-imenu-make-index ()
  (save-excursion
    (imenu--generic-function javascript-common-imenu-regex-list)))

(defun flymake-jshint-init ()
  (let* ((temp-file (flymake-init-create-temp-buffer-copy
                     'flymake-create-temp-inplace))
         (local-file (file-relative-name
                      temp-file
                      (file-name-directory buffer-file-name)))
         (arglist (list local-file)))
    (list "jshint" arglist)))

(defun mo-js-mode-hook ()
  (setq imenu-create-index-function 'mo-js-imenu-make-index)
  (setq flymake-err-line-patterns
        (cons '(".*: line \\([[:digit:]]+\\), col \\([[:digit:]]+\\), \\(.*\\)$"
                nil 1 2 3)
              flymake-err-line-patterns))

  (add-to-list 'flymake-allowed-file-name-masks
               '("\\.js\\'" flymake-jshint-init)
               '("\\.json\\'" flymake-jshint-init))
  (flymake-mode 1))

(add-hook 'js-mode-hook 'mo-js-mode-hook)

;; {{ patching imenu in js2-mode
(setq js2-imenu-extra-generic-expression javascript-common-imenu-regex-list)

(defvar js2-imenu-original-item-lines nil
  "List of line infomration of original imenu items.")

(defun js2-imenu--get-line-start-end (pos)
  (let (b e)
    (save-excursion
      (goto-char pos)
      (setq b (line-beginning-position))
      (setq e (line-end-position)))
    (list b e)))

(defun js2-imenu--get-pos (item)
  (let (val)
    (cond
     ((integerp item)
      (setq val item))

     ((markerp item)
      (setq val (marker-position item))))

    val))

(defun js2-imenu--get-extra-item-pos (item)
  (let (val)
    (cond
     ((integerp item)
      (setq val item))

     ((markerp item)
      (setq val (marker-position item)))

     ;; plist
     ((and (listp item) (listp (cdr item)))
      (setq val (js2-imenu--get-extra-item-pos (cadr item))))

     ;; alist
     ((and (listp item) (not (listp (cdr item))))
      (setq val (js2-imenu--get-extra-item-pos (cdr item)))))

    val))

(defun js2-imenu--extract-line-info (item)
  "Recursively parse the original imenu items created by js2-mode.
The line numbers of items will be extracted."
  (let (val)
    (if item
      (cond
       ;; Marker or line number
       ((setq val (js2-imenu--get-pos item))
        (push (js2-imenu--get-line-start-end val)
              js2-imenu-original-item-lines))

       ;; The item is Alist, example: (hello . 163)
       ((and (listp item) (not (listp (cdr item))))
        (setq val (js2-imenu--get-pos (cdr item)))
        (if val (push (js2-imenu--get-line-start-end val)
                      js2-imenu-original-item-lines)))

       ;; The item is a Plist
       ((and (listp item) (listp (cdr item)))
        (js2-imenu--extract-line-info (cadr item))
        (js2-imenu--extract-line-info (cdr item)))

       ;;Error handling
       (t (message "Impossible to here! item=%s" item)
          )))
    ))

(defun js2-imenu--item-exist (pos lines)
  "Try to detect does POS belong to some LINE"
  (let (rlt)
    (dolist (line lines)
      (if (and (< pos (cadr line)) (>= pos (car line)))
          (setq rlt t)))
    rlt))

(defun js2-imenu--is-item-already-created (item)
  (unless (js2-imenu--item-exist
           (js2-imenu--get-extra-item-pos item)
           js2-imenu-original-item-lines)
    item))

(defun js2-imenu--check-single-item (r)
  (cond
   ((and (listp (cdr r)))
    (let (new-types)
      (setq new-types
            (delq nil (mapcar 'js2-imenu--is-item-already-created (cdr r))))
      (if new-types (setcdr r (delq nil new-types))
        (setq r nil))))
   (t (if (js2-imenu--item-exist (js2-imenu--get-extra-item-pos r)
                                 js2-imenu-original-item-lines)
          (setq r nil))))
  r)

(defun js2-imenu--remove-duplicate-items (extra-rlt)
  (delq nil (mapcar 'js2-imenu--check-single-item extra-rlt)))

(defun js2-imenu--merge-imenu-items (rlt extra-rlt)
  "RLT contains imenu items created from AST.
EXTRA-RLT contains items parsed with simple regex.
Merge RLT and EXTRA-RLT, items in RLT has *higher* priority."
  ;; Clear the lines.
  (set (make-variable-buffer-local 'js2-imenu-original-item-lines) nil)
  ;; Analyze the original imenu items created from AST,
  ;; I only care about line number.
  (dolist (item rlt)
    (js2-imenu--extract-line-info item))

  ;; @see https://gist.github.com/redguardtoo/558ea0133daa72010b73#file-hello-js
  ;; EXTRA-RLT sample:
  ;; ((function ("hello" . #<marker 63>) ("bye" . #<marker 128>))
  ;;  (controller ("MyController" . #<marker 128))
  ;;  (hellworld . #<marker 161>))
  (setq extra-rlt (js2-imenu--remove-duplicate-items extra-rlt))
  (append rlt extra-rlt))

(eval-after-load 'js2-mode
  '(progn
     (defadvice js2-mode-create-imenu-index (around my-js2-mode-create-imenu-index activate)
       (let (rlt extra-rlt)
         ad-do-it
         (setq extra-rlt
               (save-excursion
                 (imenu--generic-function js2-imenu-extra-generic-expression)))
         (setq ad-return-value (js2-imenu--merge-imenu-items ad-return-value extra-rlt))
         ad-return-value))
     (require 'js2-refactor)
     (js2r-add-keybindings-with-prefix "C-c C-m")))
;; }}

(defun my-js2-mode-setup()
  (js2-imenu-extras-mode)
  (setq mode-name "JS2")
  (require 'js-doc)
  (define-key js2-mode-map "\C-cd" 'js-doc-insert-function-doc)
  (define-key js2-mode-map "@" 'js-doc-insert-tag))

(cond
 ((and (>= emacs-major-version 24) (>= emacs-minor-version 1) (not *no-memory*))
  (setq auto-mode-alist (cons '("\\.js\\(\\.erb\\)?\\'" . js2-mode) auto-mode-alist))
  (autoload 'js2-mode "js2-mode" nil t)
  (add-hook 'js2-mode-hook 'my-js2-mode-setup)
  (add-to-list 'interpreter-mode-alist (cons "node" 'js2-mode)))
 (t
  (setq auto-mode-alist (cons '("\\.js\\(\\.erb\\)?\\'" . js-mode) auto-mode-alist))
  ))
;; }}

(if *emacs24* (add-hook 'coffee-mode-hook 'flymake-coffee-load))

;; @see https://github.com/Sterlingg/json-snatcher
(autoload 'jsons-print-path "json-snatcher" nil t)

;; {{ js-beautify
(defun js-beautify ()
  "Beautify a region of javascript using the code from jsbeautify.org.
sudo pip install jsbeautifier"
  (interactive)
  (let ((orig-point (point)))
    (unless (mark)
      (mark-defun))
    (shell-command-on-region (point)
                             (mark)
                             (concat "js-beautify"
                                     " --stdin "
                                     " --jslint-happy --brace-style=end-expand --keep-array-indentation "
                                     (format " --indent-size=%d " js2-basic-offset))
                             nil t)
    (goto-char orig-point)))
;; }}

;; After js2 has parsed a js file, we look for jslint globals decl comment ("/* global Fred, _, Harry */") and
;; add any symbols to a buffer-local var of acceptable global vars
;; Note that we also support the "symbol: true" way of specifying names via a hack (remove any ":true"
;; to make it look like a plain decl, and any ':false' are left behind so they'll effectively be ignored as
;; you can;t have a symbol called "someName:false"
(add-hook 'js2-post-parse-callbacks
          (lambda ()
            (when (> (buffer-size) 0)
              (let ((btext (replace-regexp-in-string
                            ": *true" " "
                            (replace-regexp-in-string "[\n\t ]+" " " (buffer-substring-no-properties 1 (buffer-size)) t t))))
                (mapc (apply-partially 'add-to-list 'js2-additional-externs)
                      (split-string
                       (if (string-match "/\\* *global *\\(.*?\\) *\\*/" btext) (match-string-no-properties 1 btext) "")
                       " *, *" t))
                ))))


(provide 'init-javascript)
