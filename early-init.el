;;; early-init.el ---   -*- lexical-binding: t -*-

;; Copyright (C) 2022 Chen Bin
;;
;; Keywords: keyword1 keyword2
;; Author: Chen Bin <chenbin@gmail.com>

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;;

;;; Code:

(when (or (featurep 'esup-child)
          (fboundp 'profile-dotemacs)
          (daemonp)
          (boundp 'startup-now)
          noninteractive)
  (setq package-enable-at-startup nil))

(defvar my-computer-has-smaller-memory-p nil
  "Installing&Compiling many packages could cost too much memory.")

;; @see https://www.reddit.com/r/emacs/comments/ofhket/further_boost_start_up_time_with_a_simple_tweak/
;; 10% speed up of startup for my configuration
(unless my-computer-has-smaller-memory-p
  (setq gc-cons-percentage 0.6)
  (setq gc-cons-threshold most-positive-fixnum))

(setq inhibit-startup-message t)

;; no menu bar, toolbar, scroll bar
(setq default-frame-alist
      '((menu-bar-lines . 0)
        (tool-bar-lines . 0)
        (horizontal-scroll-bars)
        (vertical-scroll-bars)))

(provide 'early-init)
;;; early-init.el ends here
