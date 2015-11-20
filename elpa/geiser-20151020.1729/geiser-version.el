;;; geiser-version.el.in -- geiser's version

;; Copyright (C) 2009 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.



(defvar geiser-version-string "@PACKAGE_STRING@"
  "Geiser's version as a string.")

(defun geiser-version ()
  "Echoes Geiser's version."
  (interactive)
  (message "%s" geiser-version-string))

(provide 'geiser-version)
