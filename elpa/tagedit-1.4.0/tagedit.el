;;; tagedit.el --- Some paredit-like features for html-mode

;; Copyright (C) 2012 Magnar Sveen <magnars@gmail.com>

;; Author: Magnar Sveen <magnars@gmail.com>
;; Version: 1.4.0
;; Package-Version: 1.4.0
;; Keywords: convenience
;; Package-Requires: ((s "1.3.1") (dash "1.0.3"))

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; A collection of paredit-like functions for editing in html-mode.

;; ## Installation
;;
;; I highly recommended installing tagedit through elpa.
;;
;; It's available on [marmalade](http://marmalade-repo.org/) and
;; [melpa](http://melpa.milkbox.net/):
;;
;;     M-x package-install tagedit
;;
;; You can also install the dependencies on your own, and just dump
;; tagedit in your path somewhere:
;;
;;  - <a href="https://github.com/magnars/s.el">s.el</a>
;;  - <a href="https://github.com/magnars/dash.el">dash.el</a>

;; ## Functions
;;
;; This is it at the moment:
;;
;;  - `tagedit-forward-slurp-tag` moves the next sibling into this tag.
;;  - `tagedit-forward-barf-tag` moves the last child out of this tag.
;;  - `tagedit-raise-tag` replaces the parent tag with this tag.
;;  - `tagedit-kill` kills to the end of the line, while preserving the structure.
;;
;; Not part of paredit:
;;
;;  - `tagedit-kill-attribute` kills the html attribute at point.

;; ## Setup
;;
;; If you want tagedit to bind to the same keys as paredit, there's this:
;;
;; ```cl
;; (eval-after-load "sgml-mode"
;;   '(progn
;;      (require 'tagedit)
;;      (tagedit-add-paredit-like-keybindings)
;;      (add-hook 'html-mode-hook (lambda () (tagedit-mode 1)))))
;; ```
;;
;; Or you can cherry-pick functions and bind them however you want:
;;
;; ```cl
;; (define-key tagedit-mode-map (kbd "C-<right>") 'tagedit-forward-slurp-tag)
;; (define-key tagedit-mode-map (kbd "C-<left>") 'tagedit-forward-barf-tag)
;; (define-key tagedit-mode-map (kbd "M-r") 'tagedit-raise-tag)
;; (define-key tagedit-mode-map (kbd "C-k") 'tagedit-kill)
;; (define-key tagedit-mode-map (kbd "s-k") 'tagedit-kill-attribute)
;; ```

;; ## Experimental tag editing
;;
;; I am currently working on automatically updating the closing tag when
;; you edit the starting tag. It is an experimental feature, since it is quite new
;; and I'm sure it breaks some things.
;;
;; This also inserts `<></>` when you type `<`, and expands it to
;; `<div></div>` as you type.
;;
;; You can turn on experimental features using:
;;
;; ```cl
;; (tagedit-add-experimental-features)
;; ```

;; ## Other conveniences
;;
;; It also expands one-line tags into multi-line tags for you, when you
;; press refill-paragraph. Like this:
;;
;; ```html
;; <p>My one very long text inside a tag that I'd like to refill</p>
;; ```
;;
;; then after `M-q`:
;;
;; ```html
;; <p>
;;   My one very long text inside a tag that
;;   I'd like to refill
;; </p>
;; ```
;;
;; You can disable this behavior by setting
;; `tagedit-expand-one-line-tags` to nil.

;;; Code:

;; Vocabulary
;;
;; - a tag can be self-closing or consist of an open tag and a closing tag.
;; - a tag that is not self-closing has contents
;; - a tag has innards between < and >
;; - a tag has details between <tag and >
;;
;; TODO: fix old methods to use a consistent vocabulary

(require 'assoc)
(require 's)
(require 'dash)
(require 'sgml-mode)

;;;###autoload
(defun tagedit-add-paredit-like-keybindings ()
  (interactive)

  ;; paredit lookalikes
  (define-key tagedit-mode-map (kbd "C-<right>") 'tagedit-forward-slurp-tag)
  (define-key tagedit-mode-map (kbd "C-)") 'tagedit-forward-slurp-tag)
  (define-key tagedit-mode-map (kbd "C-<left>") 'tagedit-forward-barf-tag)
  (define-key tagedit-mode-map (kbd "C-}") 'tagedit-forward-barf-tag)
  (define-key tagedit-mode-map (kbd "M-r") 'tagedit-raise-tag)

  ;; no paredit equivalents
  (define-key tagedit-mode-map (kbd "s-k") 'tagedit-kill-attribute)
  (define-key tagedit-mode-map (kbd "s-<return>") 'tagedit-toggle-multiline-tag))

;;;###autoload
(defun tagedit-add-experimental-features ()
  (setq tagedit-experimental-features-on? t)
  (te/maybe-turn-on-tag-editing)
  (define-key tagedit-mode-map (kbd "<") 'tagedit-insert-lt)
  (define-key tagedit-mode-map (kbd ">") 'tagedit-insert-gt)
  (define-key tagedit-mode-map (kbd ".") 'tagedit-insert-dot)
  (define-key tagedit-mode-map (kbd "#") 'tagedit-insert-hash)
  )

;;;###autoload
(defun tagedit-disable-experimental-features ()
  (setq tagedit-experimental-features-on? nil)
  (te/turn-off-tag-editing)
  (define-key tagedit-mode-map (kbd "<") nil)
  (define-key tagedit-mode-map (kbd ">") nil))

;;;###autoload
(defun tagedit-insert-equal ()
  (interactive)
  (if (and (not (te/point-inside-string?))
           (te/point-inside-tag-details?)
           (looking-back "\\sw")
           (not (looking-at "\"")))
      (progn (insert "=\"\"")
             (forward-char -1))
    (self-insert-command 1)))

;;;###autoload
(defun tagedit-insert-quote ()
  (interactive)
  (unless (and (eq last-command 'tagedit-insert-equal)
               (looking-back "\""))
    (self-insert-command 1)))

;;;###autoload
(defun tagedit-insert-lt ()
  (interactive)
  (when (fboundp 'autopair-mode)
    (autopair-mode -1))
  (if (or (te/point-inside-string?)
          (te/point-inside-tag-innards?))
      (self-insert-command 1)
    (insert "<></>")
    (forward-char -1)
    (te/create-mirror (point) (point))
    (forward-char -3)
    (te/create-master (point) (point))))

;;;###autoload
(defun tagedit-insert-hash ()
  (interactive)
  (if (te/eligible-for-auto-attribute-insert?)
      (if (te/has-attribute "id" (te/current-tag))
          (te/mark-current-id-attribute)
        (te/insert-attribute "id"))
    (self-insert-command 1)))

;;;###autoload
(defun tagedit-insert-dot ()
  (interactive)
  (if (te/eligible-for-auto-attribute-insert?)
      (if (te/has-attribute "class" (te/current-tag))
          (te/expand-current-class-attribute)
        (te/insert-attribute "class"))
    (self-insert-command 1)))

(defun te/eligible-for-auto-attribute-insert? ()
  (and (te/point-inside-tag-innards?)
       (not (te/point-inside-string?))
       (not (te/point-inside-comment?))))

(defun te/expand-current-class-attribute ()
  (te/goto-attribute-end "class" (te/current-tag))
  (unless (looking-back " ")
    (insert " ")))

(defun te/mark-current-id-attribute ()
  (te/goto-attribute-end "id" (te/current-tag))
  (set-mark (point))
  (forward-char 1)
  (backward-sexp 1)
  (forward-char 1))

(defun te/has-attribute (attr tag)
  (save-excursion
    (goto-char (aget tag :beg))
    (search-forward (concat attr "=\"") (aget tag :end) t)))

(defun te/goto-attribute-end (attr tag)
  (goto-char (aget tag :beg))
  (search-forward (concat attr "=") (aget tag :end) t)
  (forward-sexp 1)
  (forward-char -1))

(defun te/insert-attribute (name)
  (unless (looking-back " ")
    (insert " "))
  (insert name "=\"\"")
  (unless (looking-at "[ >/]")
    (insert " ")
    (forward-char -1))
  (forward-char -1))

(defvar tagedit-experimental-features-on? nil)

(defun te/maybe-turn-on-tag-editing ()
  (when (and tagedit-mode tagedit-experimental-features-on?)
    (add-hook 'before-change-functions 'te/before-change-handler nil t)
    (add-hook 'post-command-hook 'te/maybe-start-tag-edit nil t)))

(defun te/turn-off-tag-editing ()
  (remove-hook 'before-change-functions 'te/before-change-handler t)
  (remove-hook 'post-command-hook 'te/maybe-start-tag-edit t))

(defun te/before-change-handler (beg end)
  (when (and te/master
             (< beg (overlay-start te/master))
             (> end (overlay-end te/master)))
    (te/delete-master)
    (te/delete-mirror)))

(defun te/maybe-start-tag-edit (&rest ignore)
  (ignore-errors
    (when (and (not te/master)
               (not te/mirror)
               (te/point-at-tag-name))
      (let ((tag (te/current-tag)))
        (unless (te/is-unmatched-open tag)
          (te/create-master (1+ (aget tag :beg))
                            (te/tag-details-beg tag))
          (unless (te/is-self-closing tag)
            (te/create-mirror (- (aget tag :end) (length (aget tag :name)) 1)
                              (- (aget tag :end) 1))))))))

(defvar tagedit-mode-map nil
  "Keymap for tagedit minor mode.")

(unless tagedit-mode-map
  (setq tagedit-mode-map (make-sparse-keymap)))

(--each '(("C-k" . tagedit-kill)
          ("="   . tagedit-insert-equal)
          ("!"   . tagedit-insert-exclamation-mark)
          ("\""  . tagedit-insert-quote))
  (define-key tagedit-mode-map (read-kbd-macro (car it)) (cdr it)))

(define-minor-mode tagedit-mode
  "Minor mode for pseudo-structurally editing html."
  nil " Tagedit" tagedit-mode-map
  (if tagedit-mode
      (te/maybe-turn-on-tag-editing)
    (te/turn-off-tag-editing)))

;;;###autoload
(defun tagedit-insert-gt ()
  (interactive)
  (if (te/point-inside-tag-innards?)
      (search-forward ">")
    (self-insert-command 1)))

(defvar te/tags-that-cannot-self-close '("div" "span" "script"))

;;;###autoload
(defun tagedit-insert-exclamation-mark ()
  (interactive)
  (when (and (looking-back "<")
             (looking-at "></>"))
    (te/delete-mirror-end-tag)
    (te/conclude-tag-edit))
  (self-insert-command 1))

;;;###autoload
(defun tagedit-maybe-insert-slash ()
  (interactive)
  (let ((tag (te/current-tag)))
    (if (and (member (aget tag :name) te/tags-that-cannot-self-close)
             (looking-at ">"))
        (message "Cannot self-close %ss." (aget tag :name))
      (self-insert-command 1))))

;;;###autoload
(defun tagedit-kill ()
  (interactive)
  (when (and (te/point-at-tag-name) ;; skip past tagname if inside to avoid mangling the document. Even
             (looking-at "\\sw"))   ;; better would be to update the closing tag, but that's for
    (skip-syntax-forward "w"))      ;; another day
  (let ((current-tag (te/current-tag)))
    (cond
     ((looking-at "\\s *$")
      (kill-line))

     ((te/point-inside-string?)
      (te/kill-to-end-of-string))

     ((te/point-inside-tag-details?)
      (if (te/tag-details-ends-on-this-line?)
          (te/kill-to-end-of-tag-details)
        (te/kill-remaining-attributes-on-line)))

     ((and current-tag
           (not (te/looking-at-tag current-tag))
           (te/tag-ends-on-this-line? current-tag))
      (te/kill-to-end-of-tag-contents current-tag))

     (:else (te/kill-remaining-tags-on-line)))))

;;;###autoload
(defun tagedit-forward-slurp-tag ()
  (interactive)
  (te/conclude-tag-edit)
  (when (te/is-self-closing (te/current-tag))
    (save-excursion (te/open-self-closing-tag (te/current-tag))))
  (save-excursion
    (let* ((current-tag (te/current-tag))
           (next-sibling (te/next-sibling current-tag)))
      (if next-sibling
          (te/move-end-tag current-tag (aget next-sibling :end))
        (let ((parent (te/parent-tag current-tag)))
          (if (not parent)
              (error "Nothing to slurp")
            (goto-char (aget parent :beg))
            (tagedit-forward-slurp-tag))))))
  (save-excursion (te/ensure-proper-multiline (te/current-tag)))
  (te/indent (te/current-tag)))

;;;###autoload
(defun tagedit-forward-barf-tag ()
  (interactive)
  (te/conclude-tag-edit)
  (save-excursion
    (let* ((current-tag (te/current-tag))
           (last-child (te/last-child current-tag)))
      (if (not last-child)
          (error "Nothing to barf")
        (goto-char (aget last-child :beg))
        (skip-syntax-backward " >")
        (te/move-end-tag current-tag (point)))))
  (save-excursion (te/ensure-proper-multiline (te/current-tag)))
  (te/indent (te/parent-tag (te/current-tag))))

;;;###autoload
(defun tagedit-kill-attribute ()
  (interactive)
  (when (and (te/inside-tag)
             (not (looking-at ">")))
    (te/select-attribute)
    (kill-region (1- (region-beginning)) (region-end))
    (just-one-space)
    (when (looking-at ">")
      (delete-char -1))))

;;;###autoload
(defun tagedit-toggle-multiline-tag ()
  (interactive)
  (te/conclude-tag-edit)
  (let ((current-tag (te/current-tag)))
    (if (te/is-self-closing current-tag)
        (message "Can't toggle multiline for self-closing tags.")
      (if (te/is-one-line-tag current-tag)
          (te/one->multi-line-tag current-tag)))))

;;;###autoload
(defun tagedit-raise-tag ()
  (interactive)
  (te/conclude-tag-edit)
  (let* ((current (te/current-tag))
         (contents (te/contents current))
         (parent (te/parent-tag current)))
    (save-excursion
      (te/delete parent)
      (let ((beg (point)))
        (insert contents)
        (indent-region beg (point))))))

(defun te/looking-at-tag (tag)
  (= (point) (aget tag :beg)))

(defvar te/master nil)
(defvar te/mirror nil)

(make-variable-buffer-local 'te/master)
(make-variable-buffer-local 'te/mirror)

(defface te/master-face
  `((((class color) (background light))
     (:underline  "#777777"))
    (((class color) (background dark))
     (:underline "#777777"))
    (t (:underline t)))
  "The face used to highlight master"
  :group 'tagedit)

(defface te/mirror-face
  `((((class color) (background light))
     (:underline  "#777777"))
    (((class color) (background dark))
     (:underline "#777777"))
    (t (:underline t)))
  "The face used to highlight mirror"
  :group 'tagedit)

(defun te/delete-mirror ()
  (when te/mirror
    (delete-overlay te/mirror)
    (setq te/mirror nil)))

(defun te/create-mirror (beg end)
  (te/delete-mirror)
  (setq te/mirror (make-overlay beg end nil nil t))
  (overlay-put te/mirror 'priority 100)
  (overlay-put te/mirror 'face 'te/mirror-face))

(defun te/delete-master ()
  (when te/master
    (delete-overlay te/master)
    (setq te/master nil)))

(defvar te/master-keymap (make-sparse-keymap))
(define-key te/master-keymap (kbd "TAB") 'tagedit-insert-gt)
(define-key te/master-keymap (kbd "/") 'tagedit-maybe-insert-slash)

(defun te/create-master (beg end)
  (if (or (< (point) beg)
          (> (point) end))
      (error "Point must be inside master region"))
  (te/delete-master)
  (setq te/master (make-overlay beg end nil nil t))
  (overlay-put te/master 'priority 100)
  (overlay-put te/master 'face 'te/master-face)
  (overlay-put te/master 'keymap te/master-keymap)
  (overlay-put te/master 'modification-hooks '(te/on-master-modification))
  (overlay-put te/master 'insert-in-front-hooks '(te/on-master-modification))
  (overlay-put te/master 'insert-behind-hooks '(te/on-master-modification))
  (add-hook 'before-revert-hook 'te/conclude-tag-edit nil t)
  (add-hook 'post-command-hook 'te/post-command-handler nil t))

(defun te/conclude-tag-edit ()
  (when (and te/mirror
             te/master
             (save-excursion
               (goto-char (overlay-start te/master))
               (te/is-self-closing (te/current-tag))))
    (te/delete-mirror-end-tag))
  (te/delete-master)
  (te/delete-mirror)
  (remove-hook 'before-revert-hook 'te/conclude-tag-edit t)
  (remove-hook 'post-command-hook 'te/post-command-handler t))

(defun te/delete-mirror-end-tag ()
  (save-excursion
    (goto-char (overlay-start te/mirror))
    (search-backward "<")
    (te/delete-to (search-forward ">"))))

(defun te/point-is-outside-of-master ()
  "Is point outside of master?"
  (or (null te/master)
      (< (point) (overlay-start te/master))
      (> (point) (overlay-end te/master))))

(defun te/active-region-is-outside-of-master ()
  "Is region active and mark outside master?"
  (and (region-active-p)
       (or (< (mark) (overlay-start te/master))
           (> (mark) (overlay-end te/master)))))

(defun te/point-at-tag-name ()
  (looking-back "<[[:lower:][:upper:]0-9\-:]*"))

(defun te/master-string ()
  (buffer-substring (overlay-start te/master)
                    (overlay-end te/master)))

(defun te/post-command-handler ()
  "Clear all marks if point or region is outside of master"
  (if (or (te/point-is-outside-of-master)
          (te/active-region-is-outside-of-master)
          (not (te/point-at-tag-name)))
      (te/conclude-tag-edit)))

(defun te/on-master-modification (overlay after? beg end &optional length)
  (when after?
    (save-excursion
      (goto-char (overlay-start te/master))
      (let ((master (te/current-tag)))
        (if te/mirror
            (if (te/is-self-closing master)
                (te/remove-closing-tag-and-mirror master)
              (te/update-mirror-from-master master))
          (te/insert-closing-tag-with-mirror master))))))

(defun te/insert-closing-tag-with-mirror (master)
  (let ((name (aget master :name)))
    (goto-char (aget master :end))
    (insert "</" name ">")
    (te/create-mirror (- (point) 1 (length name))
                      (- (point) 1))))

(defun te/remove-closing-tag-and-mirror (master)
  (te/delete-mirror-end-tag)
  (te/delete-mirror))

(defun te/update-mirror-from-master (master)
  (goto-char (overlay-start te/mirror))
  (delete-char (- (overlay-end te/mirror)
                  (overlay-start te/mirror)))
  (insert (aget master :name)))

(defun te/tag-ends-on-this-line? (tag)
  (save-excursion
    (= (line-number-at-pos)
       (progn (goto-char (aget tag :end))
              (forward-list -1)
              (line-number-at-pos)))))

(defmacro te/kill-to (&rest body)
  `(let ((beg (point)))
     ,@body
     (kill-region beg (point))))

(defmacro te/delete-to (&rest body)
  `(let ((beg (point)))
     ,@body
     (delete-region beg (point))))

(defun te/kill-remaining-tags-on-line ()
  (let ((line (line-number-at-pos)))
    (te/kill-to
     (while (and (= line (line-number-at-pos))
                 (not (eolp))
                 (search-forward-regexp "\\(<\\|$\\)" nil t))
       (when (looking-back "<")
         (forward-char -1)
         (sgml-skip-tag-forward 1))))))

(defun te/kill-to-end-of-tag-contents (tag)
  (te/kill-to (goto-char (aget tag :end))
              (forward-list -1)))

(defun te/kill-remaining-attributes-on-line ()
  (let ((line (line-number-at-pos)))
    (te/kill-to
     (while (and (= line (line-number-at-pos))
                 (not (looking-at "\\s *$")))
       (te/goto-end-of-attribute)))))

(defun te/point-inside-tag-details? ()
  (let ((tag (te/current-tag)))
    (and tag
         (<= (te/tag-details-beg tag) (point))
         (<= (point) (te/tag-details-end tag)))))

(defun te/point-inside-tag-innards? ()
  (let ((tag (te/current-tag)))
    (and tag
         (< (aget tag :beg) (point))
         (<= (point) (te/tag-details-end tag)))))

(defun te/tag-details-beg (tag)
  (+ (aget tag :beg) 1 (length (aget tag :name))))

(defun te/tag-details-end (tag)
  (save-excursion
    (goto-char (aget tag :beg))
    (forward-list 1)
    (if (looking-back "/>")
        (- (point) 2)
      (- (point) 1))))

(defun te/tag-details-ends-on-this-line? ()
  (= (line-number-at-pos)
     (line-number-at-pos (te/tag-details-end (te/current-tag)))))

(defun te/kill-to-end-of-tag-details ()
  (te/kill-to
   (goto-char (te/tag-details-end (te/current-tag)))))

(defun te/kill-to-end-of-string ()
  (te/kill-to
   (te/move-point-forward-out-of-string)
   (forward-char -1)))

(defun te/point-inside-string? ()
  (nth 3 (syntax-ppss)))

(defun te/point-inside-comment? ()
  (nth 4 (syntax-ppss)))

(defun te/move-point-forward-out-of-string ()
  "Move point forward until it exits the current quoted string."
  (while (te/point-inside-string?) (forward-char)))

(defun te/open-self-closing-tag (tag)
  (when (sgml-empty-tag-p (aget tag :name))
    (error "Cannot open empty tag %s." (aget tag :name)))
  (goto-char (aget tag :end))
  (forward-char -1)
  (when (looking-back "/")
    (delete-char -1))
  (forward-char 1)
  (te/insert-closing-tag tag))

(defun te/ensure-proper-multiline (tag)
  (when (te/is-multiline tag)
    (goto-char (aget tag :end))
    (unless (looking-at "$")
      (newline))
    (backward-sexp)
    (unless (looking-back "^\s*")
      (newline))
    (goto-char (aget tag :beg))
    (unless (looking-back "^\s*")
      (newline))
    (forward-sexp)
    (unless (looking-at "$")
      (newline))))

(defun te/is-multiline (tag)
  (not (= (line-number-at-pos (aget tag :beg))
          (line-number-at-pos (aget tag :end)))))

(defun te/insert-closing-tag (tag)
  (insert "</" (aget tag :name) ">"))

(defun te/move-end-tag (tag pos)
  (let ((tag-start-line (line-number-at-pos (point))))
    (goto-char pos)
    (save-excursion
      (te/delete-end-tag tag))
    (te/insert-closing-tag tag)))

(defun te/delete-end-tag (tag)
  (goto-char (aget tag :end))
  (if (save-excursion ;; end tag is alone on line
        (beginning-of-line)
        (looking-at (concat "^\s*</" (aget tag :name) ">$")))
      (delete-char (- 0 (current-column) 1)) ;; then delete entire line
    (backward-sexp)
    (delete-region (point) (aget tag :end)))) ;; otherwise just the end tag

(defun te/indent (tag)
  (indent-region (aget tag :beg)
                 (aget tag :end)))

(defun te/is-self-closing (tag)
  (or (eq :t (aget tag :self-closing))
      (sgml-empty-tag-p (aget tag :name))))

(defun te/is-unmatched-open (tag)
  (and (= (te/inner-beg tag) (aget tag :end))
       (not (te/is-self-closing tag))))

(defun te/goto-end-of-attribute ()
  (search-forward "\"")
  (when (nth 3 (syntax-ppss)) ; inside string
    (forward-char -1)
    (forward-sexp 1)))

(defun te/select-attribute ()
  (search-forward "\"")
  (when (nth 3 (syntax-ppss)) ; inside string
    (forward-char -1)
    (forward-sexp 1))
  (set-mark (point))
  (forward-sexp -1)
  (search-backward " ")
  (forward-char 1))

(defun te/inside-tag ()
  (let ((context (save-excursion (te/get-context))))
    (and context
         (> (point) (sgml-tag-start context))
         (< (point) (sgml-tag-end context)))))


(defvar tagedit-expand-one-line-tags t
  "Should tagedit change one-line tags into multi-line tags?
This happens when you press refill-paragraph.")

(defadvice fill-paragraph (before tagedit-maybe-expand-tag activate)
  (te/maybe-expand-tag))

(defun te/maybe-expand-tag ()
  (when (and tagedit-expand-one-line-tags
             (derived-mode-p 'sgml-mode))
    (let ((current-tag (te/current-tag)))
      (when (te/is-one-line-tag current-tag)
        (te/one->multi-line-tag current-tag)))))

(defun te/is-one-line-tag (tag)
  (when tag
    (save-excursion
      (goto-char (aget tag :beg))
      (= (line-number-at-pos)
         (progn
           (goto-char (aget tag :end))
           (line-number-at-pos))))))

(defun te/one->multi-line-tag (tag)
  (save-excursion
    (goto-char (te/inner-end tag))
    (let ((end (point)))
      (insert "\n")
      (goto-char (te/inner-beg tag))
      (insert "\n")
      (indent-region (point) (+ 3 end)))))

(defun te/parent-tag (tag)
  (save-excursion
    (goto-char (1- (aget tag :beg)))
    (let ((parent (te/current-tag)))
      (when (and parent
                 (not (= (aget parent :beg)
                         (aget tag :beg))))
        parent))))

(defun te/just-one-blank-line ()
  (newline 2)
  (forward-line -1)
  (delete-blank-lines))

(defun te/contents (tag)
  (buffer-substring (aget tag :beg)
                    (aget tag :end)))

(defun te/inner-contents (tag)
  (if (te/is-self-closing tag)
      ""
    (buffer-substring (te/inner-beg tag)
                      (te/inner-end tag))))

(defun te/delete (tag)
  (goto-char (aget tag :beg))
  (delete-region (aget tag :beg)
                 (aget tag :end)))

(defun te/inner-beg (tag)
  (save-excursion
    (goto-char (aget tag :beg))
    (forward-list 1)
    (point)))

(defun te/inner-end (tag)
  (- (aget tag :end)
     (length (aget tag :name))
     3))

(defvar te/self-closing-tag-types
  '(empty jsp))

(defun te/tag-name-from-context (context)
  (or (sgml-tag-name context)
      (save-excursion
        (forward-char 1)
        (let ((beg (point)))
          (search-forward-regexp "[ >]")
          (buffer-substring-no-properties beg (- (point) 1))))))

(defun te/current-tag ()
  (ignore-errors
    (save-excursion
      (let* ((context (te/get-context))
             (name (te/tag-name-from-context context))
             (type (if (looking-back "^\\s *") :block :inline))
             (beg (sgml-tag-start context))
             (end (progn (sgml-skip-tag-forward 1) (point)))
             (self-closing (if (memq (sgml-tag-type context) te/self-closing-tag-types)
                               :t :f)))
        `((:name . ,(if self-closing (s-chop-suffix "/" name) name))
          (:type . ,type)
          (:self-closing . ,self-closing)
          (:beg . ,beg)
          (:end . ,end))))))

(defun te/current-text-node ()
  (save-excursion
    (let* ((beg (progn
                  (search-backward ">")
                  (forward-char 1)
                  (skip-syntax-forward " >")
                  (point)))
           (type (if (looking-back "^\\s *") :block :inline))
           (end (progn
                  (search-forward "<")
                  (forward-char -1)
                  (skip-syntax-backward " >")
                  (point))))
      `((:name . "text-node")
        (:type . ,type)
        (:self-closing :t)
        (:beg . ,beg)
        (:end . ,end)))))

(defun te/get-context ()
  (when (looking-at "<") (forward-char 1))
  (let ((context (car (sgml-get-context))))
    (when (and context (string= "close" (sgml-tag-type context)))
      (forward-char 1)
      (sgml-skip-tag-backward 1)
      (forward-char 1)
      (setq context (car (sgml-get-context))))
    context))

(defun te/last-child (tag)
  (unless (te/empty-tag tag)
    (save-excursion
      (goto-char (aget tag :end))
      (backward-sexp)
      (skip-syntax-backward " >")
      (if (looking-back ">")
          (progn
            (backward-char 1)
            (te/current-tag))
        (te/current-text-node)))))

(defun te/empty-tag (tag)
  (equal "" (s-trim (te/inner-contents tag))))

(defun te/looking-at-parents-end-tag (tag)
  (save-excursion
    (let ((here (point))
          (parent (te/parent-tag tag)))
      (when parent
        (goto-char (aget parent :end))
        (backward-sexp)
        (= here (point))))))

(defun te/next-sibling (tag)
  (save-excursion
    (goto-char (aget tag :end))
    (skip-syntax-forward " >")
    (unless (eobp)
      (if (looking-at "<")
          (unless (te/looking-at-parents-end-tag tag)
            (forward-char 1)
            (te/current-tag))
        (te/current-text-node)))))

(provide 'tagedit)

;;; tagedit.el ends here
