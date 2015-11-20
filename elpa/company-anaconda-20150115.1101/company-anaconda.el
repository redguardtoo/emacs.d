;;; company-anaconda.el --- Anaconda backend for company-mode

;; Copyright (C) 2013-2015 by Artem Malyshev

;; Author: Artem Malyshev <proofit404@gmail.com>
;; URL: https://github.com/proofit404/anaconda-mode
;; Package-Version: 20150115.1101
;; Version: 0.1.0
;; Package-Requires: ((company "0.8.0") (anaconda-mode "0.1.0") (cl-lib "0.5.0"))

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; See the README for more details.

;;; Code:

(require 'cl-lib)
(require 'company)
(require 'anaconda-mode)

(defvar company-anaconda-compact-annotation t
  "Show only the first character of type in annotations.")

(defun company-anaconda-init ()
  "Initialize company-anaconda buffer."
  (setq-local company-tooltip-align-annotations t))

(defun company-anaconda-prefix ()
  "Grab prefix at point.
Properly detect strings, comments and attribute access."
  (and anaconda-mode
       (not (company-in-string-or-comment))
       (or (company-grab-symbol-cons "\\." 1)
           'stop)))

(defun company-anaconda-candidates ()
  "Obtain candidates list from anaconda."
  (--map (propertize (plist-get it :name) 'item it)
         (anaconda-mode-complete)))

(defun company-anaconda-get-property (property candidate)
  "Return the property PROPERTY of completion candidate CANDIDATE."
  (let ((item (get-text-property 0 'item candidate)))
    (plist-get item property)))

(defun company-anaconda-doc-buffer (candidate)
  "Return documentation buffer for chosen CANDIDATE."
  (let ((doc (company-anaconda-get-property :doc candidate)))
    (and doc (anaconda-mode-doc-buffer doc))))

(defun company-anaconda-meta (candidate)
  "Return short documentation string for chosen CANDIDATE."
  (company-anaconda-get-property :info candidate))

(defun company-anaconda-annotation (candidate)
  "Return annotation string for chosen CANDIDATE."
  (let ((annotation (company-anaconda-get-property :type candidate)))
    (if company-anaconda-compact-annotation
        (substring annotation 0 1)
      annotation)))

(defun company-anaconda-location (candidate)
  "Return location (path . line) for chosen CANDIDATE."
  (-when-let* ((path (company-anaconda-get-property :path candidate))
               (line (company-anaconda-get-property :line candidate)))
    (cons path line)))

;;;###autoload
(defun company-anaconda (command &optional arg)
  "Anaconda backend for company-mode.
See `company-backends' for more info about COMMAND and ARG."
  (interactive (list 'interactive))
  (cl-case command
    (init (company-anaconda-init))
    (interactive (company-begin-backend 'company-anaconda))
    (prefix (company-anaconda-prefix))
    (candidates (company-anaconda-candidates))
    (doc-buffer (company-anaconda-doc-buffer arg))
    (meta (company-anaconda-meta arg))
    (annotation (company-anaconda-annotation arg))
    (location (company-anaconda-location arg))
    (sorted t)))

(provide 'company-anaconda)

;;; company-anaconda.el ends here
