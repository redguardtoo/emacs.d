;;; colir.el --- Color blending library -*- lexical-binding: t -*-

;; Copyright (C) 2015  Free Software Foundation, Inc.

;; Author: Oleh Krehel <ohwoeowho@gmail.com>

;; This file is part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This package solves the problem of adding a face with a background
;; to text which may already have a background.  In all conflicting
;; areas, instead of choosing either the original or the new
;; background face, their blended sum is used.
;;
;; The blend mode functions are taken from http://en.wikipedia.org/wiki/Blend_modes.

;;; Code:

(require 'color)

(defcustom colir-compose-method 'colir-compose-alpha
  "Select a method to compose two color channels."
  :type '(choice
          (const colir-compose-alpha)
          (const colir-compose-overlay)
          (const colir-compose-soft-light))
  :group 'ivy)

(defun colir-compose-soft-light (a b)
  "Compose A and B channels."
  (if (< b 0.5)
      (+ (* 2 a b) (* a a (- 1 b b)))
    (+ (* 2 a (- 1 b)) (* (sqrt a) (- (* 2 b) 1)))))

(defun colir-compose-overlay (a b)
  "Compose A and B channels."
  (if (< a 0.5)
      (* 2 a b)
    (- 1 (* 2 (- 1 a) (- 1 b)))))

(defun colir-compose-alpha (a b &optional alpha gamma)
  "Compose A and B channels."
  (setq alpha (or alpha 0.5))
  (setq gamma (or gamma 2.2))
  (+ (* (expt a gamma) alpha) (* (expt b gamma) (- 1 alpha))))

(defun colir-blend (c1 c2)
  "Blend the two colors C1 and C2 using `colir-compose-method'.
C1 and C2 are triples of floats in [0.0 1.0] range."
  (apply #'color-rgb-to-hex
         (cl-mapcar
          colir-compose-method
          c1 c2)))

(defun colir-blend-face-background (start end face &optional object)
  "Append to the face property of the text from START to END the face FACE.
When the text already has a face with a non-plain background,
blend it with the background of FACE.
Optional argument OBJECT is the string or buffer containing the text.
See also `font-lock-append-text-property'."
  (let (next prev)
    (while (/= start end)
      (setq next (next-single-property-change start 'face object end)
            prev (get-text-property start 'face object))
      (if prev
          (let ((background-prev (face-background prev)))
            (progn
              (put-text-property
               start next 'face
               (if background-prev
                   (cons `(background-color
                           . ,(colir-blend
                               (color-name-to-rgb background-prev)
                               (color-name-to-rgb (face-background face nil t))))
                         prev)
                 (list face prev))
               object)))
        (put-text-property start next 'face face object))
      (setq start next))))

(provide 'colir)

;;; colir.el ends here
