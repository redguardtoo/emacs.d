;;; evil-exchange.el --- Exchange text more easily within Evil

;; Copyright (C) 2013-2016 by Dewdrops

;; Author: Dewdrops <v_v_4474@126.com>
;; URL: http://github.com/Dewdrops/evil-exchange
;; Version: 0.40
;; Keywords: evil, plugin
;; Package-Requires: ((evil "1.2.8") (cl-lib "0.3"))

;; This file is NOT part of GNU Emacs.

;;; License:
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; Port of vim-exchange by Tom McDonald (https://github.com/tommcdo/vim-exchange)
;;
;; Installation:
;;
;; put evil-exchange.el somewhere in your load-path and add these
;; lines to your .emacs:
;; (require 'evil-exchange)
;; ;; change default key bindings (if you want) HERE
;; ;; (setq evil-exchange-key (kbd "zx"))
;; (evil-exchange-install)

;;; Code:

(require 'evil)

(defgroup evil-exchange nil
  "Easy text exchange operator for Evil."
  :prefix "evil-exchange"
  :group 'evil)

(defcustom evil-exchange-key (kbd "gx")
  "Default binding for evil-exchange."
  :type `,(if (get 'key-sequence 'widget-type)
              'key-sequence
            'sexp)
  :group 'evil-exchange)

(defcustom evil-exchange-cancel-key (kbd "gX")
  "Default binding for evil-exchange-cancel."
  :type `,(if (get 'key-sequence 'widget-type)
              'key-sequence
            'sexp)
  :group 'evil-exchange)

(defcustom evil-exchange-highlight-face 'highlight
  "Face used to highlight marked area."
  :type 'sexp
  :group 'evil-exchange)

(defvar evil-exchange--position nil "Text position which will be exchanged")

(defvar evil-exchange--overlays nil "Overlays used to highlight marked area")


(defun evil-exchange--highlight (beg end)
  (let ((o (make-overlay beg end nil t nil)))
    (overlay-put o 'face evil-exchange-highlight-face)
    (add-to-list 'evil-exchange--overlays o)))

(defun evil-exchange--clean ()
  (setq evil-exchange--position nil)
  (mapc 'delete-overlay evil-exchange--overlays)
  (setq evil-exchange--overlays nil))

;;;###autoload
(autoload 'evil-exchange "evil-exchange"
  "Exchange two regions with evil motion." t)

(evil-define-operator evil-exchange (beg end type)
  "Exchange two regions with evil motion."
  :move-point nil
  (interactive "<R>")
  (let ((beg-marker (copy-marker beg t))
        (end-marker (copy-marker end nil)))
    (if (null evil-exchange--position)
        ;; call without evil-exchange--position set: store region
        (progn
          (setq evil-exchange--position (list (current-buffer) beg-marker end-marker type))
          ;; highlight area marked to exchange
          (if (eq type 'block)
              (evil-apply-on-block #'evil-exchange--highlight beg end nil)
            (evil-exchange--highlight beg end)))
      ;; secondary call: do exchange
      (cl-destructuring-bind
          (orig-buffer orig-beg orig-end orig-type) evil-exchange--position
        (cond
         ;; exchange block region
         ((and (eq orig-type 'block) (eq type 'block))
          (evil-exchange--do-swap (current-buffer) orig-buffer
                                  beg-marker end-marker
                                  orig-beg orig-end
                                  #'delete-extract-rectangle #'insert-rectangle
                                  nil))
         ;; signal error if regions incompatible
         ((or (eq orig-type 'block) (eq type 'block))
          (user-error "Can't exchange block region with non-block region"))
         ;; exchange normal region
         (t
          (evil-exchange--do-swap (current-buffer) orig-buffer
                                  beg-marker end-marker
                                  orig-beg orig-end
                                  #'delete-and-extract-region #'insert
                                  t))))))
  ;; place cursor on beginning of line
  (when (and (evil-called-interactively-p) (eq type 'line))
    (evil-first-non-blank)))

(defun evil-exchange--do-swap (curr-buffer orig-buffer curr-beg curr-end orig-beg
                                           orig-end extract-fn insert-fn not-block)
  ;; This function does the real exchange work. Here's the detailed steps:
  ;; 1. call extract-fn with orig-beg and orig-end to extract orig-text.
  ;; 2. call extract-fn with curr-beg and curr-end to extract curr-text.
  ;; 3. go to orig-beg and then call insert-fn with curr-text.
  ;; 4. go to curr-beg and then call insert-fn with orig-text.
  ;; After step 2, the two markers of the same beg/end pair (curr or orig)
  ;; will point to the same position. So if orig-beg points to the same position
  ;; of curr-end initially, orig-beg and curr-beg will point to the same position
  ;; before step 3. Because curr-beg is a marker which moves after insertion, the
  ;; insertion in step 3 will push it to the end of the newly inserted text,
  ;; thus resulting incorrect behaviour.
  ;; To fix this edge case, we swap two extracted texts before step 3 to
  ;; effectively reverse the (problematic) order of two `evil-exchange' calls.
  (if (eq curr-buffer orig-buffer)
      ;; in buffer exchange
      (let ((adjacent (and not-block (equal (marker-position orig-beg) (marker-position curr-end))))
            (orig-text (funcall extract-fn orig-beg orig-end))
            (curr-text (funcall extract-fn curr-beg curr-end)))
        ;; swaps two texts if adjacent is set
        (let ((orig-text (if adjacent curr-text orig-text))
              (curr-text (if adjacent orig-text curr-text)))
          (save-excursion
            (goto-char orig-beg)
            (funcall insert-fn curr-text)
            (goto-char curr-beg)
            (funcall insert-fn orig-text))))
    ;; exchange across buffers
    (let ((orig-text (with-current-buffer orig-buffer
                       (funcall extract-fn orig-beg orig-end)))
          (curr-text (funcall extract-fn curr-beg curr-end)))
      (save-excursion
        (with-current-buffer orig-buffer
          (goto-char orig-beg)
          (funcall insert-fn curr-text))
        (goto-char curr-beg)
        (funcall insert-fn orig-text))))
  (evil-exchange--clean))

;;;###autoload
(defun evil-exchange-cancel ()
  "Cancel current pending exchange."
  (interactive)
  (if (null evil-exchange--position)
      (message "No pending exchange")
    (evil-exchange--clean)
    (message "Exchange cancelled")))

;;;###autoload
(defun evil-exchange-install ()
  "Setting evil-exchange key bindings."
  (define-key evil-normal-state-map evil-exchange-key 'evil-exchange)
  (define-key evil-visual-state-map evil-exchange-key 'evil-exchange)
  (define-key evil-normal-state-map evil-exchange-cancel-key 'evil-exchange-cancel)
  (define-key evil-visual-state-map evil-exchange-cancel-key 'evil-exchange-cancel))


(defun evil-exchange/cx ()
  (interactive)
  (when (memq evil-this-operator '(evil-change evil-cp-change))
    (setq evil-inhibit-operator t)
    (define-key evil-operator-shortcut-map "c" 'evil-exchange-cancel)
    (call-interactively #'evil-exchange)
    (define-key evil-operator-shortcut-map "c" nil)))

;;;###autoload
(defun evil-exchange-cx-install ()
  "Setting evil-exchange key bindings in a vim-compatible way"
  (interactive)
  (define-key evil-operator-state-map "x" 'evil-exchange/cx)
  (define-key evil-visual-state-map "X" 'evil-exchange))


(provide 'evil-exchange)
;;; evil-exchange.el ends here
