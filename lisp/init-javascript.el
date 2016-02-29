;; may be in an arbitrary order
(eval-when-compile (require 'cl))

;; {{ js2-mode or javascript-mode
(setq-default js2-use-font-lock-faces t
              js2-mode-must-byte-compile nil
              js2-idle-timer-delay 0.5 ; NOT too big for real time syntax check
              js2-auto-indent-p nil
              js2-indent-on-enter-key nil ; annoying instead useful
              js2-skip-preprocessor-directives t
              js2-strict-inconsistent-return-warning nil ; return <=> return null
              js2-enter-indents-newline nil
              js2-bounce-indent-p t)

(setq javascript-common-imenu-regex-list
      '(("Controller" "[. \t]controller([ \t]*['\"]\\([^'\"]+\\)" 1)
        ("Controller" "[. \t]controllerAs:[ \t]*['\"]\\([^'\"]+\\)" 1)
        ("Filter" "[. \t]filter([ \t]*['\"]\\([^'\"]+\\)" 1)
        ("State" "[. \t]state([ \t]*['\"]\\([^'\"]+\\)" 1)
        ("Factory" "[. \t]factory([ \t]*['\"]\\([^'\"]+\\)" 1)
        ("Service" "[. \t]service([ \t]*['\"]\\([^'\"]+\\)" 1)
        ("Module" "[. \t]module( *['\"]\\([a-zA-Z0-9_.]+\\)['\"], *\\[" 1)
        ("ngRoute" "[. \t]when(\\(['\"][a-zA-Z0-9_\/]+['\"]\\)" 1)
        ("Directive" "[. \t]directive([ \t]*['\"]\\([^'\"]+\\)" 1)
        ("Event" "[. \t]\$on([ \t]*['\"]\\([^'\"]+\\)" 1)
        ("Config" "[. \t]config([ \t]*function *( *\\([^\)]+\\)" 1)
        ("Config" "[. \t]config([ \t]*\\[ *['\"]\\([^'\"]+\\)" 1)
        ("OnChange" "[ \t]*\$(['\"]\\([^'\"]*\\)['\"]).*\.change *( *function" 1)
        ("OnClick" "[ \t]*\$([ \t]*['\"]\\([^'\"]*\\)['\"]).*\.click *( *function" 1)
        ("Watch" "[. \t]\$watch( *['\"]\\([^'\"]+\\)" 1)
        ("Function" "function[ \t]+\\([a-zA-Z0-9_$.]+\\)[ \t]*(" 1)
        ("Function" "^[ \t]*\\([a-zA-Z0-9_$.]+\\)[ \t]*=[ \t]*function[ \t]*(" 1)
        ("Task" "[. \t]task([ \t]*['\"]\\([^'\"]+\\)" 1)
        ))

;; js-mode imenu enhancement
;; @see http://stackoverflow.com/questions/20863386/idomenu-not-working-in-javascript-mode
(defun mo-js-imenu-make-index ()
  (save-excursion
    (imenu--generic-function javascript-common-imenu-regex-list)))

(defun mo-js-mode-hook ()
  (when (and  (not (is-buffer-file-temp)) (not (derived-mode-p 'js2-mode)))
    ;; js-mode only setup, js2-mode inherit from js-mode since v20150909
    (setq imenu-create-index-function 'mo-js-imenu-make-index)
    ;; https://github.com/illusori/emacs-flymake
    ;; javascript support is out of the box
    ;; DONOT jslint json
    ;; (add-to-list 'flymake-allowed-file-name-masks
    ;;              '("\\.json\\'" flymake-javascript-init))
    (message "mo-js-mode-hook called")
    (flymake-mode 1)))

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

;; {{ print json path, will be removed when latest STABLE js2-mode released
(defun js2-get-element-index-from-array-node (elem array-node &optional hardcoded-array-index)
  "Get index of ELEM from ARRAY-NODE or 0 and return it as string."
  (let ((idx 0) elems (rlt hardcoded-array-index))
    (setq elems (js2-array-node-elems array-node))
    (if (and elem (not hardcoded-array-index))
        (setq rlt (catch 'nth-elt
                    (dolist (x elems)
                      ;; We know the ELEM does belong to ARRAY-NODE,
                      (if (eq elem x) (throw 'nth-elt idx))
                      (setq idx (1+ idx)))
                    0)))
    (format "[%s]" rlt)))

(defun js2-print-json-path (&optional hardcoded-array-index)
  "Print the path to the JSON value under point, and save it in the kill ring.
If HARDCODED-ARRAY-INDEX provided, array index in JSON path is replaced with it."
  (interactive "P")
  (let (previous-node current-node
        key-name
        rlt)

    ;; The `js2-node-at-point' starts scanning from AST root node.
    ;; So there is no way to optimize it.
    (setq current-node (js2-node-at-point))

    (while (not (js2-ast-root-p current-node))
      (cond
       ;; JSON property node
       ((js2-object-prop-node-p current-node)
        (setq key-name (js2-prop-node-name (js2-object-prop-node-left current-node)))
        (if rlt (setq rlt (concat "." key-name rlt))
          (setq rlt (concat "." key-name))))

       ;; Array node
       ((or (js2-array-node-p current-node))
        (setq rlt (concat (js2-get-element-index-from-array-node previous-node
                                                                 current-node
                                                                 hardcoded-array-index)
                          rlt)))

       ;; Other nodes are ignored
       (t))

      ;; current node is archived
      (setq previous-node current-node)
      ;; Get parent node and continue the loop
      (setq current-node (js2-node-parent current-node)))

    (cond
     (rlt
      ;; Clean the final result
      (setq rlt (replace-regexp-in-string "^\\." "" rlt))
      (kill-new rlt)
      (message "%s => kill-ring" rlt))
     (t
      (message "No JSON path found!")))

    rlt))
;; }}

(eval-after-load 'js2-mode
  '(progn
     (defadvice js2-mode-create-imenu-index (around my-js2-mode-create-imenu-index activate)
       (let (rlt extra-rlt)
         ad-do-it
         (setq extra-rlt
               (save-excursion
                 (imenu--generic-function js2-imenu-extra-generic-expression)))
         (setq ad-return-value (js2-imenu--merge-imenu-items ad-return-value extra-rlt))
         ad-return-value))))
;; }}

(defun my-js2-mode-setup()
  (unless (is-buffer-file-temp)
    ;; looks nodejs is more popular
    (require 'js-comint)
    ;; if use node.js we need nice output
    (js2-imenu-extras-mode)
    (setq mode-name "JS2")
    (require 'js2-refactor)
    (js2-refactor-mode 1)
    (flymake-mode -1)
    (require 'js-doc)
    (define-key js2-mode-map "\C-cd" 'js-doc-insert-function-doc)
    (define-key js2-mode-map "@" 'js-doc-insert-tag)))

(autoload 'js2-mode "js2-mode" nil t)
(add-hook 'js2-mode-hook 'my-js2-mode-setup)

(setq auto-mode-alist (cons '("\\.json$" . js-mode) auto-mode-alist))
(setq auto-mode-alist (cons '("\\.jason$" . js-mode) auto-mode-alist))
(setq auto-mode-alist (cons '("\\.jshintrc$" . js-mode) auto-mode-alist))

(cond
 ((not *no-memory*)
  (setq auto-mode-alist (cons '("\\.js\\(\\.erb\\)?\\'" . js2-mode) auto-mode-alist))
  (setq auto-mode-alist (cons '("\\.ts\\'" . js2-mode) auto-mode-alist))
  (add-to-list 'interpreter-mode-alist (cons "node" 'js2-mode)))
 (t
  (setq auto-mode-alist (cons '("\\.js\\(\\.erb\\)?\\'" . js-mode) auto-mode-alist))
  (setq auto-mode-alist (cons '("\\.ts\\'" . js-mode) auto-mode-alist))
  ))
;; }}

(add-hook 'coffee-mode-hook 'flymake-coffee-load)

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

(setq-default js2-additional-externs
              '("$"
                "$A" ; salesforce lightning component
                "$LightningApp" ; salesforce
                "AccessifyHTML5"
                "KeyEvent"
                "Raphael"
                "React"
                "_content" ; Keysnail
                "angular"
                "app"
                "beforeEach"
                "browser"
                "by"
                "clearInterval"
                "clearTimeout"
                "command" ; Keysnail
                "content" ; Keysnail
                "define"
                "describe"
                "display" ; Keysnail
                "element"
                "expect"
                "ext" ; Keysnail
                "gBrowser" ; Keysnail
                "goDoCommand" ; Keysnail
                "hook" ; Keysnail
                "inject"
                "it"
                "jQuery"
                "jasmine"
                "key" ; Keysnail
                "ko"
                "log"
                "module"
                "plugins" ; Keysnail
                "process"
                "require"
                "setInterval"
                "setTimeout"
                "shell" ; Keysnail
                "tileTabs" ; Firefox addon
                "util" ; Keysnail
                "utag"))

(provide 'init-javascript)
