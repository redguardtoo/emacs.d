;; geiser-xref.el -- utilities for cross-referencing

;; Copyright (C) 2009, 2010, 2012 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Thu Mar 05, 2009 23:03



(require' geiser-edit)
(require 'geiser-autodoc)
(require 'geiser-eval)
(require 'geiser-popup)
(require 'geiser-custom)
(require 'geiser-base)

(require 'button)
(require 'lisp-mode)


;;; Customization:
(defgroup geiser-xref nil
  "Options for cross-referencing commands."
  :group 'geiser)

(geiser-edit--define-custom-visit
 geiser-xref-follow-link-method geiser-xref
 "How to visit buffers when following xrefs.")

(geiser-custom--defface xref-link
  'link geiser-xref "links in cross-reference buffers")

(geiser-custom--defface xref-header
  'bold geiser-xref "headers in cross-reference buffers")


;;; Ref button:

(define-button-type 'geiser-xref--button
  'action 'geiser-xref--button-action
  'face 'geiser-font-lock-xref-link
  'follow-link t)

(defun geiser-xref--button-action (button)
  (let ((location (button-get button 'location))
        (name (button-get button 'name)))
    (when location
      (geiser-edit--try-edit-location name
                                      location
                                      geiser-xref-follow-link-method))))

(defun geiser-xref--insert-button (xref)
  (let* ((location (cdr (assoc "location" xref)))
         (file (geiser-edit--location-file location))
         (signature (cdr (assoc "signature" xref)))
         (signature-txt (and signature
                             (geiser-autodoc--str* signature)))
         (module (cdr (assoc "module" xref)))
         (p (point)))
    (when signature
      (insert "   - ")
      (if (stringp file)
          (insert-text-button signature-txt
                              :type 'geiser-xref--button
                              'location location
                              'name (car signature)
                              'help-echo (format "%s in %s"
                                                 (car signature) file))
        (insert (format "%s" signature-txt)))
      (fill-region p (point))
      (save-excursion (goto-char p) (indent-sexp))
      (newline))))

(defun geiser-xref--module< (xr1 xr2)
  (let ((m1 (format "%s" (cdr (assoc "module" xr1))))
        (m2 (format "%s" (cdr (assoc "module" xr2)))))
    (cond ((equal m1 m2)
           (string< (format "%s" (cdr (assoc "signature" xr1)))
                    (format "%s" (cdr (assoc "signature" xr2)))))
          ((null m1) (not m2))
          ((null m2))
          (t (string< (format "%s" m1) (format "%s" m2))))))

(defun geiser-xref--display-xrefs (header xrefs)
  (geiser-xref--with-buffer
   (erase-buffer)
   (geiser--insert-with-face header 'geiser-font-lock-xref-header)
   (newline)
   (let ((last-module))
     (dolist (xref (sort xrefs 'geiser-xref--module<))
       (let ((module (format "%s" (cdr (assoc "module" xref)))))
         (when (not (equal module last-module))
           (insert "\n  In module ")
           (geiser--insert-with-face (format "%s" module)
                                     'geiser-font-lock-xref-header)
           (newline 2)
           (setq last-module module))
         (geiser-xref--insert-button xref)))))
  (geiser-xref--pop-to-buffer)
  (goto-char (point-min)))

(defun geiser-xref--read-name (ask prompt)
  (let ((name (or (and (not ask) (geiser--symbol-at-point))
                  (read-string prompt nil nil (geiser--symbol-at-point)))))
    (and name (format "%s" name))))

(defun geiser-xref--fetch-xrefs (ask kind rkind proc)
  (let* ((name (geiser-xref--read-name ask (format "%s: " (capitalize kind))))
         (res (and name (geiser-eval--send/result
                         `(:eval (:ge ,proc (quote (:scm ,name))))))))
    (message "Retrieving %ss list for '%s'..." rkind name)
    (if (or (not res) (not (listp res)))
        (message "No %ss found for '%s'" rkind name)
      (message "")
      (geiser-xref--display-xrefs (format "%ss for '%s'"
                                          (capitalize rkind)
                                          name)
                                  res))))


;;; Buffer and mode:

(geiser-popup--define xref "*Geiser xref*" geiser-xref-mode)

(defvar geiser-xref-mode-map
  (let ((map (make-sparse-keymap)))
    (suppress-keymap map)
    (set-keymap-parent map button-buffer-map)
    map))

(defun geiser-xref-mode ()
  "Major mode for displaying cross-references.
\\{geiser-xref-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (buffer-disable-undo)
  (use-local-map geiser-xref-mode-map)
  (set-syntax-table scheme-mode-syntax-table)
  (setq mode-name "Geiser Xref")
  (setq major-mode 'geiser-xref-mode)
  (setq buffer-read-only t))


;;; Commands:

(defun geiser-xref-generic-methods (&optional arg)
  "Display information about known methods of a given generic.
With prefix, ask for the name of the generic."
  (interactive "P")
  (geiser-xref--fetch-xrefs arg "generic" "method" 'generic-methods))

(defun geiser-xref-callers (&optional arg)
  "Display list of callers for procedure at point.
With prefix, ask for the procedure."
  (interactive "P")
  (geiser-xref--fetch-xrefs arg "procedure" "caller" 'callers))

(defun geiser-xref-callees (&optional arg)
  "Display list of callees for procedure at point.
With prefix, ask for the procedure."
  (interactive "P")
  (geiser-xref--fetch-xrefs arg "procedure" "callee" 'callees))


(provide 'geiser-xref)
