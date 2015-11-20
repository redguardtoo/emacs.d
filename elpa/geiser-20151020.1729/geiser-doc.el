;;; geiser-doc.el -- accessing scheme-provided documentation

;; Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sat Feb 14, 2009 14:09



(require 'geiser-edit)
(require 'geiser-impl)
(require 'geiser-completion)
(require 'geiser-autodoc)
(require 'geiser-eval)
(require 'geiser-syntax)
(require 'geiser-menu)
(require 'geiser-popup)
(require 'geiser-custom)
(require 'geiser-base)

(require 'button)


;;; Customization:

(defgroup geiser-doc nil
  "Options for documentation buffers."
  :group 'geiser)

(geiser-custom--defface doc-title
  'bold geiser-doc "article titles in documentation buffers")

(geiser-custom--defface doc-link
  'link geiser-doc "links in documentation buffers")

(geiser-custom--defface doc-button
  'button geiser-doc "buttons in documentation buffers")


;;; Implementation
(geiser-impl--define-caller geiser-doc--external-help external-help
                            (symbol module)
  "By default, Geiser will display help about an identifier in a
help buffer, after collecting the associated signature and
docstring. You can provide an alternative function for displaying
help (e.g. browse an HTML page) implementing this method.")


;;; Documentation browser history:

(defvar geiser-doc-history-size 50)
(defvar geiser-doc--history nil)

(defun geiser-doc--make-history ()
  (list nil                                   ; current
        (make-ring geiser-doc-history-size)   ; previous
        (make-ring geiser-doc-history-size))) ; next

(setq geiser-doc--history (geiser-doc--make-history))

(eval-after-load "session"
  '(add-to-list 'session-globals-exclude 'geiser-doc--history))

(defsubst geiser-doc--history-current ()
  (car geiser-doc--history))

(defsubst geiser-doc--history-previous-link ()
  (ring-ref (cadr geiser-doc--history) 0))

(defsubst geiser-doc--history-next-link ()
  (ring-ref (caddr geiser-doc--history) 0))

(defun geiser-doc--history-push (link)
  (unless (or (null link) (equal link (geiser-doc--history-current)))
    (when (not (null (geiser-doc--history-current)))
      (let ((next (geiser-doc--history-next)))
        (unless (equal link next)
          (when next (geiser-doc--history-previous))
          (ring-insert (nth 1 geiser-doc--history)
                       (car geiser-doc--history)))))
    (setcar geiser-doc--history link))
  link)

(defsubst geiser-doc--history-next-p ()
  (not (ring-empty-p (nth 2 geiser-doc--history))))

(defun geiser-doc--history-next (&optional forget-current)
  (when (geiser-doc--history-next-p)
    (when (and (car geiser-doc--history) (not forget-current))
      (ring-insert (nth 1 geiser-doc--history) (car geiser-doc--history)))
    (setcar geiser-doc--history (ring-remove (nth 2 geiser-doc--history) 0))))

(defsubst geiser-doc--history-previous-p ()
  (not (ring-empty-p (nth 1 geiser-doc--history))))

(defun geiser-doc--history-previous (&optional forget-current)
  (when (geiser-doc--history-previous-p)
    (when (and (car geiser-doc--history) (not forget-current))
      (ring-insert (nth 2 geiser-doc--history) (car geiser-doc--history)))
    (setcar geiser-doc--history (ring-remove (nth 1 geiser-doc--history) 0))))


;;; Links

(defsubst geiser-doc--make-link (target module impl)
  (list target module impl))

(defsubst geiser-doc--link-target (link)
  (nth 0 link))

(defsubst geiser-doc--link-module (link)
  (nth 1 link))

(defsubst geiser-doc--link-impl (link)
  (nth 2 link))

(defun geiser-doc--follow-link (link)
  (let ((target (geiser-doc--link-target link))
        (module (geiser-doc--link-module link))
        (impl (geiser-doc--link-impl link)))
    (when (and (or target module) impl)
      (with--geiser-implementation impl
        (if (null target)
            (geiser-doc-module module impl)
          (let ((geiser-eval--get-module-function (lambda (x) module)))
            (geiser-doc-symbol target module impl)))))))

(make-variable-buffer-local
 (defvar geiser-doc--buffer-link nil))

(defsubst geiser-doc--implementation ()
  (geiser-doc--link-impl geiser-doc--buffer-link))

(defun geiser-doc--button-action (button)
  (let ((link (button-get button 'geiser-link)))
    (when link (geiser-doc--follow-link link))))

(define-button-type 'geiser-doc--button
  'action 'geiser-doc--button-action
  'follow-link t)

(defun geiser-doc--make-module-button (beg end module impl)
  (let ((link (geiser-doc--make-link nil module impl))
        (help (format "Help for module %s" module)))
    (make-text-button beg end :type 'geiser-doc--button
                      'face 'geiser-font-lock-doc-link
                      'geiser-link link
                      'help-echo help)))

(defun geiser-doc--insert-button (target module impl &optional sign)
  (let ((link (geiser-doc--make-link target module impl))
        (text (format "%s" (or (and sign
                                    (geiser-autodoc--str* sign))
                               target
                               module)))
        (help (format "%smodule %s"
                      (if target (format "%s in " target) "")
                      (or module "<unknown>"))))
    (insert-text-button text
                        :type 'geiser-doc--button
                        'face 'geiser-font-lock-doc-link
                        'geiser-link link
                        'help-echo help)))

(defun geiser-doc--xbutton-action (button)
  (when geiser-doc--buffer-link
    (let ((kind (or (button-get button 'x-kind) 'source))
          (target (geiser-doc--link-target geiser-doc--buffer-link))
          (module (geiser-doc--link-module geiser-doc--buffer-link))
          (impl (geiser-doc--link-impl geiser-doc--buffer-link)))
      (with--geiser-implementation impl
        (cond ((eq kind 'source)
               (if target (geiser-edit-symbol target nil (point-marker))
                 (geiser-edit-module module)))
              ((eq kind 'manual)
               (geiser-doc--external-help impl
                                          (or target module)
                                          module)))))))

(define-button-type 'geiser-doc--xbutton
  'action 'geiser-doc--xbutton-action
  'face 'geiser-font-lock-doc-button
  'follow-link t)

(defun geiser-doc--insert-xbutton (&optional manual)
  (let ((label (if manual "[manual]" "[source]"))
        (help (if manual "Look up in Scheme manual" "Go to definition")))
  (insert-text-button label
                      :type 'geiser-doc--xbutton
                      'help-echo help
                      'x-kind (if manual 'manual 'source))))

(defun geiser-doc--insert-xbuttons (impl)
  (when (geiser-impl--method 'external-help impl)
    (geiser-doc--insert-xbutton t)
    (insert " "))
  (geiser-doc--insert-xbutton))

(defun geiser-doc--insert-nav-button (next)
  (let* ((lnk (if next (geiser-doc--history-next-link)
                (geiser-doc--history-previous-link)))
         (what (geiser-doc--link-target lnk))
         (what (or what (geiser-doc--link-module lnk)))
         (action (if next '(lambda (b) (geiser-doc-next))
                   '(lambda (b) (geiser-doc-previous)))))
    (insert-text-button (if next "[forward]" "[back]")
                        'action action
                        'help-echo (format "Previous help item (%s)" what)
                        'face 'geiser-font-lock-doc-button
                        'follow-link t)))


;;; Auxiliary functions:

(defun geiser-doc--manual-available-p ()
  (geiser-impl--method 'external-help geiser-impl--implementation))

(defun geiser-doc--module (&optional mod impl)
  (let ((impl (or impl (geiser-doc--link-impl geiser-doc--buffer-link)))
        (mod (or mod (geiser-doc--link-module geiser-doc--buffer-link))))
    (geiser-impl--call-method 'find-module impl mod)))

(defun geiser-doc--insert-title (title)
  (let ((p (point)))
    (insert (format "%s" title))
    (fill-paragraph nil)
    (let ((indent-line-function 'lisp-indent-line))
      (indent-region p (point)))
    (put-text-property p (point) 'face 'geiser-font-lock-doc-title)
    (newline)))

(defun geiser-doc--insert-list (title lst module impl)
  (when lst
    (geiser-doc--insert-title title)
    (newline)
    (dolist (w lst)
      (let ((name (car w))
            (signature (cdr (assoc "signature" w)))
            (info (cdr (assoc "info" w))))
        (insert "\t- ")
        (if module
            (geiser-doc--insert-button name module impl signature)
          (geiser-doc--insert-button nil name impl))
        (when info (insert (format "  %s" info)))
        (newline)))
    (newline)))

(defun geiser-doc--insert-footer (impl)
  (newline 2)
  (geiser-doc--insert-xbuttons impl)
  (let* ((prev (and (geiser-doc--history-previous-p) 8))
         (nxt (and (geiser-doc--history-next-p) 10))
         (len (max 1 (- (window-width)
                        (- (point) (line-beginning-position))
                        (or prev 0)
                        (or nxt 0)))))
    (when (or prev nxt)
      (insert (make-string len ?\ )))
    (when prev
      (geiser-doc--insert-nav-button nil)
      (insert " "))
    (when nxt
      (geiser-doc--insert-nav-button t))))


;;; Commands:

(defun geiser-doc--get-docstring (symbol module)
  (geiser-eval--send/result
   `(:eval (:ge symbol-documentation ',symbol) ,module)))

(defun geiser-doc--get-module-exports (module)
  (geiser-eval--send/result
   `(:eval (:ge module-exports '(:module ,module)) :f)))

(defun geiser-doc--buttonize-modules (impl)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "in module \\([^.\n]+\\)[.\n ]" nil t)
      (geiser-doc--make-module-button (match-beginning 1)
                                      (match-end 1)
                                      (geiser-doc--module (match-string 1)
                                                          impl)
                                      impl))))

(defun geiser-doc--render-docstring
  (docstring symbol &optional module impl)
  (erase-buffer)
  (geiser-doc--insert-title
   (geiser-autodoc--str* (cdr (assoc "signature" docstring))))
  (newline)
  (insert (or (cdr (assoc "docstring" docstring)) ""))
  (geiser-doc--buttonize-modules impl)
  (setq geiser-doc--buffer-link
        (geiser-doc--history-push (geiser-doc--make-link symbol
                                                         module
                                                         impl)))
  (geiser-doc--insert-footer impl)
  (goto-char (point-min)))

(defun geiser-doc-symbol (symbol &optional module impl)
  (let* ((impl (or impl geiser-impl--implementation))
         (module (geiser-doc--module (or module (geiser-eval--get-module))
                                     impl)))
    (let ((ds (geiser-doc--get-docstring symbol module)))
      (if (or (not ds) (not (listp ds)))
          (message "No documentation available for '%s'" symbol)
        (geiser-doc--with-buffer
          (geiser-doc--render-docstring ds symbol module impl))
        (geiser-doc--pop-to-buffer)))))

(defun geiser-doc-symbol-at-point (&optional arg)
  "Get docstring for symbol at point.
With prefix argument, ask for symbol (with completion)."
  (interactive "P")
  (let ((symbol (or (and (not arg) (geiser--symbol-at-point))
                    (geiser-completion--read-symbol
                     "Symbol: " (geiser--symbol-at-point)))))
    (when symbol (geiser-doc-symbol symbol))))

(defun geiser-doc-look-up-manual (&optional arg)
  "Look up manual for symbol at point.
With prefix argument, ask for the lookup symbol (with completion)."
  (interactive "P")
  (unless (geiser-doc--manual-available-p)
    (error "No manual available"))
  (let ((symbol (or (and (not arg) (geiser--symbol-at-point))
                    (geiser-completion--read-symbol "Symbol: "))))
    (geiser-doc--external-help geiser-impl--implementation
                               symbol
                               (geiser-eval--get-module))))

(defconst geiser-doc--sections '(("Procedures:" "procs")
                                 ("Syntax:" "syntax")
                                 ("Variables:" "vars")
                                 ("Submodules:" "modules" t)))

(defconst geiser-doc--sections-re
  (format "^%s\n" (regexp-opt (mapcar 'car geiser-doc--sections))))

(defun geiser-doc-module (&optional module impl)
  "Display information about a given module."
  (interactive)
  (let* ((impl (or impl geiser-impl--implementation))
         (module (geiser-doc--module (or module
                                         (geiser-completion--read-module))
                                     impl))
         (msg (format "Retrieving documentation for %s ..." module))
         (exports (progn
                    (message "%s" msg)
                    (geiser-doc--get-module-exports module))))
    (if (not exports)
        (message "No information available for %s" module)
      (geiser-doc--with-buffer
        (erase-buffer)
        (geiser-doc--insert-title (format "%s" module))
        (newline)
        (dolist (g geiser-doc--sections)
          (geiser-doc--insert-list (car g)
                                   (cdr (assoc (cadr g) exports))
                                   (and (not (cddr g)) module)
                                   impl))
        (setq geiser-doc--buffer-link
              (geiser-doc--history-push
               (geiser-doc--make-link nil module impl)))
        (geiser-doc--insert-footer impl)
        (goto-char (point-min)))
      (message "%s done" msg)
      (geiser-doc--pop-to-buffer))))

(defun geiser-doc-next-section ()
  "Move to next section in this page."
  (interactive)
  (forward-line)
  (re-search-forward geiser-doc--sections-re nil t)
  (forward-line -1))

(defun geiser-doc-previous-section ()
  "Move to previous section in this page."
  (interactive)
  (re-search-backward geiser-doc--sections-re nil t))

(defun geiser-doc-next (&optional forget-current)
  "Go to next page in documentation browser.
With prefix, the current page is deleted from history."
  (interactive "P")
  (let ((link (geiser-doc--history-next forget-current)))
    (unless link (error "No next page"))
    (geiser-doc--follow-link link)))

(defun geiser-doc-previous (&optional forget-current)
  "Go to previous page in documentation browser.
With prefix, the current page is deleted from history."
  (interactive "P")
  (let ((link (geiser-doc--history-previous forget-current)))
    (unless link (error "No previous page"))
    (geiser-doc--follow-link link)))

(defun geiser-doc-kill-page ()
  "Kill current page if a previous or next one exists."
  (interactive)
  (condition-case nil
      (geiser-doc-previous t)
    (error (geiser-doc-next t))))

(defun geiser-doc-refresh ()
  "Refresh the contents of current page."
  (interactive)
  (when geiser-doc--buffer-link
    (geiser-doc--follow-link geiser-doc--buffer-link)))

(defun geiser-doc-clean-history ()
  "Clean up the document browser history."
  (interactive)
  (when (y-or-n-p "Clean browsing history? ")
    (setq geiser-doc--history (geiser-doc--make-history))
    (geiser-doc-refresh))
  (message ""))


;;; Documentation browser and mode:

(defun geiser-doc-edit-symbol-at-point ()
  "Open definition of symbol at point."
  (interactive)
  (let* ((impl (geiser-doc--implementation))
         (module (geiser-doc--module)))
    (unless (and impl module)
      (error "I don't know what module this buffer refers to."))
    (with--geiser-implementation impl
      (geiser-edit-symbol-at-point))))

(defvar geiser-doc-mode-map nil)
(setq geiser-doc-mode-map
      (let ((map (make-sparse-keymap)))
        (suppress-keymap map)
        (set-keymap-parent map button-buffer-map)
        map))

(defun geiser-doc-switch-to-repl ()
  (interactive)
  (switch-to-geiser nil nil (current-buffer)))

(geiser-menu--defmenu doc geiser-doc-mode-map
  ("Next link" ("n") forward-button)
  ("Previous link" ("p") backward-button)
  ("Next section" ("N") geiser-doc-next-section)
  ("Previous section" ("P") geiser-doc-previous-section)
  --
  ("Next page" ("f") geiser-doc-next "Next item"
   :enable (geiser-doc--history-next-p))
  ("Previous page" ("b") geiser-doc-previous "Previous item"
   :enable (geiser-doc--history-previous-p))
  --
  ("Go to REPL" ("z" "\C-cz" "\C-c\C-z") geiser-doc-switch-to-repl)
  ("Refresh" ("g" "r") geiser-doc-refresh "Refresh current page")
  --
  ("Edit symbol" ("." "\M-.") geiser-doc-edit-symbol-at-point
   :enable (geiser--symbol-at-point))
  --
  ("Kill item" "k" geiser-doc-kill-page "Kill this page")
  ("Clear history" "c" geiser-doc-clean-history)
  --
  (custom "Browser options" geiser-doc)
  --
  ("Quit" nil View-quit))

(defun geiser-doc-mode ()
  "Major mode for browsing scheme documentation.
\\{geiser-doc-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (buffer-disable-undo)
  (setq truncate-lines t)
  (use-local-map geiser-doc-mode-map)
  (set-syntax-table scheme-mode-syntax-table)
  (setq mode-name "Geiser Doc")
  (setq major-mode 'geiser-doc-mode)
  (setq geiser-eval--get-module-function 'geiser-doc--module)
  (setq buffer-read-only t))

(geiser-popup--define doc "*Geiser documentation*" geiser-doc-mode)


(provide 'geiser-doc)
