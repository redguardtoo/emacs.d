;;; diff-lisp-myers.el --- basic greedy diff algorithm  -*- lexical-binding: t -*-

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

(require 'diff-lisp-sdk)

(defmacro diff-lisp-myers-get-v (v index offset)
  "Get V's element at INDEX offset by OFFSET."
  `(aref ,v (+ ,index ,offset)))

(defmacro diff-lisp-myers-set-v (v index offset value)
  "Set V's element at INDEX offset by OFFSET to VALUE."
  `(aset ,v (+ ,index ,offset) ,value))

(defun diff-lisp-myers-find-middle-snake (a a-start n b b-start m)
  "Find middle snake of two sequences.
First sequence is subsequence of A, which starts from A-START with length N.
Second sequence is subsequence of B, which starts from B-START with length M."
  (let* (rlt
         (delta (- n m))
         (delta-odd-p (cl-oddp delta))
         (max-d (/ (+ n m) 2))
         ;; forward D-path
         (v1 (make-vector (+ n m 1) nil))
         ;; reverse D-path.
         (v2 (make-vector (+ n m 1) nil))
         (v1-offset (/ (+ n m) 2))
         (v2-offset (- v1-offset delta))
         path-found
         last-forward-snake-x
         last-forward-snake-y
         last-backward-snake-x
         last-backward-snake-y
         last-snake
         d
         k
         inverse-k ; k+delta
         x
         y)

    ;; initialize start point of the first forward D-path: x = 0, y = 1
    (diff-lisp-myers-set-v v1 1 v1-offset 0)
    ;; initialize start point of the first reverse D-path: x = n+1, y = m
    (diff-lisp-myers-set-v v2 (+ 1 (- n m)) v2-offset (1+ n))

    (setq d 0)
    (while (and (not path-found) (<= d max-d))
      ;; forward d-path reaching
      (setq k (- d))
      (while (and (not path-found) (<= k d))
        (cond
         ((or (eq k (- d))
              (and (not (eq k d))
                   (< (diff-lisp-myers-get-v v1 (1- k) v1-offset)
                      (diff-lisp-myers-get-v v1 (1+ k) v1-offset))))
          ;; move down from D-path in above diagonal
          (setq x (diff-lisp-myers-get-v v1 (1+ k) v1-offset)))

         (t
          ;; move right from D-path in below diagonal
          (setq x (1+ (diff-lisp-myers-get-v v1 (1- k) v1-offset)))))

        (setq y (- x k))

        (setq last-forward-snake-x x)
        (setq last-forward-snake-y y)
        (while (and (< x n)
                    (< y m)
                    ;; Not a[1+x] or b[1+y] because of zero-origin indexing
                    (diff-lisp-string-equal a b (+ a-start x) (+ b-start y)))
          (setq x (1+ x))
          (setq y (1+ y)))

        (diff-lisp-myers-set-v v1 k v1-offset x)


        (when (and delta-odd-p
                   (>= k (- delta (1- d)))
                   (<= k (+ delta (1- d))))
          ;; Overlaps furthest reaching reverse (D-1)-path in diagonal k?
          ;; Right now the reverse (D-1)-path are stored in v2.
          (when (>= x (diff-lisp-myers-get-v v2 k v2-offset))
            (setq path-found t)
            (setq last-snake (list last-forward-snake-x last-forward-snake-y x y))
            ;; TODO, the last snake of the forward path is the middle snake
            (let ((u (diff-lisp-myers-get-v v2 k v2-offset)))
              (setq rlt (list :difference (+ d d -1)
                              :snake last-snake)))))

        (setq k (+ k 2)))

      ;; reverse d-path reaching
      (setq k (- d))
      (while (and (not path-found) (<= k d))
        (setq inverse-k (+ k delta))
        (cond
         ((or (eq inverse-k (- delta d))
              (and (not (eq inverse-k (+ delta d)))
                   (<= (diff-lisp-myers-get-v v2 (1+ inverse-k) v2-offset)
                       (diff-lisp-myers-get-v v2 (1- inverse-k) v2-offset))))
          ;; move left from D-path in above diagonal
          (setq x (1- (diff-lisp-myers-get-v v2 (1+ inverse-k) v2-offset))))

         (t
          ;; move up from D-path in below diagonal
          (setq x (diff-lisp-myers-get-v v2 (1- inverse-k) v2-offset))))

        (setq y (- x inverse-k))

        (setq last-backward-snake-x x)
        (setq last-backward-snake-y y)
        (while (and (> x 0)
                    (> y 0)
                    ;; Not "a[x]" or "b[y]" because of zero-origin indexing
                    (diff-lisp-string-equal a b (+ a-start x -1) (+ b-start y -1)))
          (setq x (1- x))
          (setq y (1- y)))

        (diff-lisp-myers-set-v v2 inverse-k v2-offset x)


        (when (and (not delta-odd-p)
                   (>= inverse-k (- d))
                   (<= inverse-k d))
          ;; If the path overlaps the furthest reaching forward D-path in diagonal inverse-k?
          ;; Right now the forward D-path are stored in v1.
          (when (<= x (diff-lisp-myers-get-v v1 inverse-k v1-offset))
            (setq path-found t)
            (setq last-snake (list x y last-backward-snake-x last-backward-snake-y))
            ;; the last snake of the reverse path is the middle snake
            (let ((u (diff-lisp-myers-get-v v1 inverse-k v1-offset)))
              (setq rlt (list :difference (+ d d)
                              :snake last-snake)))))

        ;; If the path overlaps the furthest reaching forward D-path in diagonal inverse-k?
        (setq k (+ k 2)))

      (setq d (1+ d)))

    rlt))

(defun diff-lisp-myers-find-all-snakes (a a-start n b b-start m)
  "Find all snakes from  two sequences.
First sequence is subsequence of A, which starts from A-START with length N.
Second sequence is subsequence of B, which starts from B-START with length M."
  (when diff-lisp-debug
      (message "diff-lisp-myers-find-all-snakes called => %s %s %s %s" a-start n b-start m))

  (let (all-snakes d snake x y u v s1 s2 middle-snake)
    (when (and (> n 0) (> m 0))
      ;; Use a-start and b-start is to avoid copy sequences.
      (setq middle-snake (diff-lisp-myers-find-middle-snake a a-start n b b-start m))

      (setq d (plist-get middle-snake :difference))
      (setq snake (plist-get middle-snake :snake))
      (setq x (nth 0 snake))
      (setq y (nth 1 snake))
      (setq u (nth 2 snake))
      (setq v (nth 3 snake))
      (cond
       ((and d (> d 1))
        (setq s1 (diff-lisp-myers-find-all-snakes a a-start x b b-start y))
        (setq s2 (diff-lisp-myers-find-all-snakes a (+ a-start u) (- n u) b (+ b-start v) (- m v)))
        (setq all-snakes (append s1 s2))
        (push (list (+ x a-start) (+ y b-start) (+ u a-start) (+ v b-start)) all-snakes))

       ((> m n)
        ;; If d = 1, there are two cases:
        ;;    Case 1       Case 2
        ;;  x---x---x    x---x---x
        ;;  | \ |   |    |   |   |
        ;;  x---x---x    x---x---x
        ;;  |   | \ |    | \ |   |
        ;;  x---x---x    x---x---x
        ;;  |   |   |    |   | \ |
        ;;  x---x---x    x---x---x
        ;; In Case 1, right bottom corner is returned as the middle snake.
        (cond
         ((and (eq x u) (eq y v))
          (push (list a-start b-start (+ n a-start) (+ n b-start)) all-snakes))
         (t
          (push (list (+ x a-start) (+ y b-start) (+ u a-start) (+ v b-start)) all-snakes))))

       (t
        ;; If d = 1, there are two cases:
        ;;     Case 1            Case 2
        ;;  x---x---x---x     x---x---x---x
        ;;  | \ |   |   |     |   | \ |   |
        ;;  x---x---x---x     x---x---x---x
        ;;  |   | \ |   |     |   |   | \ |
        ;;  x---x---x---x     x---x---x---x
        ;; In Case 1, right bottom corner is returned as the middle snake.
        (cond
         ((and (eq x u) (eq y v))
          (push (list a-start b-start (+ m a-start) (+ m b-start)) all-snakes))
         (t
          (push (list (+ x a-start) (+ y b-start) (+ u a-start) (+ v b-start)) all-snakes))))))

    all-snakes))

(defun diff-lisp-myers-do-diff (a n b m)
  "Diff sequence A with length N and sequence B with length M."
  (let* ((all-snakes (diff-lisp-myers-find-all-snakes a 0 n b 0 m)))

    (setq all-snakes (cl-delete-if (lambda (snake)
                                     ;; snake is (x, y, u, v)
                                     ;; x,y is the snake start point, u, v is the end point
                                     (and (eq (nth 0 snake) (nth 2 snake))
                                          (eq (nth 1 snake) (nth 3 snake))))
                                   all-snakes))

    (cl-sort all-snakes (lambda (s1 s2) (< (car s1) (car s2))))))

(provide 'diff-lisp-myers)
;;; diff-lisp-myers.el ends here
