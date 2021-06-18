;;; nadvice.el --- Forward compatibility for Emacs-24.4's nadvice

;; Copyright (C) 2018  Free Software Foundation, Inc.

;; Author: Stefan Monnier <monnier@iro.umontreal.ca>
;; Version: 0.3
;; Keywords:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This package tries to re-implement some of nadvice.el's functionality
;; on top of the old defadvice system, to help users of defadvice
;; move to the new advice system without dropping support for Emacs<24.4.
;;
;; Limitations;
;; - only supports `advice-add' and `advice-remove';
;; - only handles the :before, :after, :override, and :around kinds of advice;
;; - requires a named rather than anonymous function;
;; - and does not support any additional properties like `name' or `depth'.
;;
;; It was tested on Emacs-22 and I can't see any obvious reason why it
;; wouldn't work on older Emacsen.

;;; Code:

(declare-function ad-remove-advice "advice")

(unless (fboundp 'add-function)
  ;; If `add-function' is defined, we're presumably running on
  ;; an Emacs that comes with the real nadvice.el, so let's be careful
  ;; to do nothing in that case!

  ;; Load `advice' manually, in case `advice-remove' is called first,
  ;; since ad-remove-advice is not autoloaded.
  (require 'advice)

;;;###autoload
(defun advice-add (symbol where function &optional props)
  (when props
    (error "This version of nadvice.el does not support PROPS"))
  (unless (symbolp function)
    (error "This version of nadvice.el requires FUNCTION to be a symbol"))
  (let ((body (cond
               ((eq where :before)
                `(progn (apply #',function (ad-get-args 0)) ad-do-it))
               ((eq where :after)
                `(progn ad-do-it (apply #',function (ad-get-args 0))))
               ((eq where :override)
                `(setq ad-return-value (apply #',function (ad-get-args 0))))
               ((eq where :around)
                `(setq ad-return-value
                       (apply #',function
                              (lambda (&rest nadvice--rest-arg)
                                (ad-set-args 0 nadvice--rest-arg)
                                ad-do-it)
                              (ad-get-args 0))))
               (t (error "This version of nadvice.el does not handle %S"
                         where)))))
    (ad-add-advice symbol
                   `(,function nil t (advice lambda () ,body))
                   'around
                   nil)
    (ad-activate symbol)))

;;;###autoload
(defun advice-remove (symbol function)
  ;; Just return nil if there is no advice, rather than signaling an
  ;; error.
  (condition-case nil
      (ad-remove-advice symbol 'around function)
    (error nil))
  (condition-case nil
      (ad-activate symbol)
    (error nil)))

)

;;;; ChangeLog:

;; 2018-09-15  Thomas Fitzsimmons	<fitzsim@fitzsim.org>
;; 
;; 	packages/nadvice: Fix advice-remove behaviour
;; 
;; 	* packages/nadvice/nadvice.el: Bump version to 0.3.
;; 	(advice-remove): Do not signal an error if the function already has no
;; 	advice.
;; 
;; 2018-09-12  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* nadvice.el: ad-remove-advice is not autoloaded
;; 
;; 2018-09-12  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* nadvice.el: Fix typo
;; 
;; 2018-09-12  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* nadvice/nadvice.el (advice-add): Add support for :override
;; 
;; 2018-09-12  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* nadvice.el: Fix copyright!
;; 
;; 2018-09-12  Stefan Monnier  <monnier@iro.umontreal.ca>
;; 
;; 	* nadvice: New forward compatibility package
;; 


(provide 'nadvice)
;;; nadvice.el ends here
