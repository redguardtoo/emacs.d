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

(defsubst diff-lisp-myers-get-v (v index-plus-offset)
  "Get V's element at INDEX-PLUS-OFFSET."
  (aref v index-plus-offset))

(defsubst diff-lisp-myers-set-v (v index-plus-offset value)
  "Set V's element at INDEX-PLUS-OFFSET to VALUE."
  (aset v index-plus-offset value))

(defsubst diff-lisp-create-snake (difference x y u v)
  "Create a snake using DIFFERENCE X Y U V."
  (list x y u v difference))

(defun diff-lisp-myers-find-middle-snake (a a-start n b b-start m)
  "Find middle snake of two sequences.
First sequence is subsequence of A, which starts from A-START with length N.
Second sequence is subsequence of B, which starts from B-START with length M."
  (let* (rlt
         (delta (- n m))
         (sum (+ n m))
         (delta-odd-p (= (logand delta 1) 1))
         (max-d (floor sum 2))
         ;; forward D-path
         (v1 (make-vector (+ sum 1) -1))
         ;; reverse D-path.
         (v2 (make-vector (+ sum 1) -1))
         (v1-offset (floor sum 2))
         (v2-offset (- v1-offset delta))
         path-found
         last-forward-snake-x
         last-forward-snake-y
         last-backward-snake-x
         last-backward-snake-y
         d
         k
         inverse-k ; k+delta
         k-plus-v1-offset
         inverse-k-plus-v2-offset
         x
         y
         neg-d
         d-minus-one)

    ;; initialize start point of the first forward D-path: x = 0, y = 1
    (diff-lisp-myers-set-v v1 (1+ v1-offset) 0)
    ;; initialize start point of the first reverse D-path: x = n+1, y = m
    (diff-lisp-myers-set-v v2 (+ 1 delta v2-offset) (1+ n))

    (setq d 0)
    (while (and (not path-found) (<= d max-d))
      (setq neg-d (- d))
      (setq d-minus-one (1- d))
      ;; forward d-path reaching
      (setq k neg-d)
      (while (and (not path-found) (<= k d))
        (setq k-plus-v1-offset (+ k v1-offset))
        (cond
         ((or (= k neg-d)
              (and (/= k d)
                   (< (diff-lisp-myers-get-v v1 (1- k-plus-v1-offset))
                      (diff-lisp-myers-get-v v1 (1+ k-plus-v1-offset)))))
          ;; move down from D-path in above diagonal
          (setq x (diff-lisp-myers-get-v v1 (1+ k-plus-v1-offset))))

         (t
          ;; move right from D-path in below diagonal
          (setq x (1+ (diff-lisp-myers-get-v v1 (1- k-plus-v1-offset))))))

        (setq y (- x k))

        (setq last-forward-snake-x x)
        (setq last-forward-snake-y y)
        (while (and (< x n)
                    (< y m)
                    ;; Not a[1+x] or b[1+y] because of zero-origin indexing
                    (diff-lisp-string-equal a b (+ a-start x) (+ b-start y)))
          (setq x (1+ x))
          (setq y (1+ y)))

        (diff-lisp-myers-set-v v1 k-plus-v1-offset x)

        (when (and delta-odd-p
                   (>= k (- delta d-minus-one))
                   (<= k (+ delta d-minus-one)))
          ;; Overlaps furthest reaching reverse (D-1)-path in diagonal k?
          ;; Right now the reverse (D-1)-path are stored in v2.
          (when (>= x (diff-lisp-myers-get-v v2 (+ k v2-offset)))
            (setq path-found t)
            ;; TODO, the last snake of the forward path is the middle snake
            (setq rlt (diff-lisp-create-snake (+ d d-minus-one)
                                              last-forward-snake-x
                                              last-forward-snake-y
                                              x
                                              y))))

        (setq k (+ k 2)))

      ;; reverse d-path reaching
      (setq k neg-d)
      (while (and (not path-found) (<= k d))
        (setq inverse-k (+ k delta))
        (setq inverse-k-plus-v2-offset (+ inverse-k v2-offset))
        (cond
         ((or (= inverse-k (- delta d))
              (and (/= inverse-k (+ delta d))
                   (<= (diff-lisp-myers-get-v v2 (1+ inverse-k-plus-v2-offset))
                       (diff-lisp-myers-get-v v2 (1- inverse-k-plus-v2-offset)))))
          ;; move left from D-path in above diagonal
          (setq x (1- (diff-lisp-myers-get-v v2 (1+ inverse-k-plus-v2-offset)))))

         (t
          ;; move up from D-path in below diagonal
          (setq x (diff-lisp-myers-get-v v2 (1- inverse-k-plus-v2-offset)))))

        (setq y (- x inverse-k))

        (setq last-backward-snake-x x)
        (setq last-backward-snake-y y)
        (while (and (> x 0)
                    (> y 0)
                    ;; Not "a[x]" or "b[y]" because of zero-origin indexing
                    (diff-lisp-string-equal a b (+ a-start x -1) (+ b-start y -1)))
          (setq x (1- x))
          (setq y (1- y)))

        (diff-lisp-myers-set-v v2 inverse-k-plus-v2-offset x)


        (when (and (not delta-odd-p)
                   (>= inverse-k neg-d)
                   (<= inverse-k d))
          ;; If the path overlaps the furthest reaching forward D-path in diagonal inverse-k?
          ;; Right now the forward D-path are stored in v1.
          (when (<= x (diff-lisp-myers-get-v v1 (+ inverse-k v1-offset)))
            (setq path-found t)
            ;; the last snake of the reverse path is the middle snake
            (setq rlt (diff-lisp-create-snake (+ d d)
                                              x
                                              y
                                              last-backward-snake-x
                                              last-backward-snake-y))))

        ;; If the path overlaps the furthest reaching forward D-path in diagonal inverse-k?
        (setq k (+ k 2)))

      (setq d (1+ d)))

    rlt))

(defun diff-lisp-myers-find-all-snakes (a a-start n b b-start m)
  "Find all snakes from two sequences.
First sequence is subsequence of A, which starts from A-START with length N.
Second sequence is subsequence of B, which starts from B-START with length M."
  (when diff-lisp-debug
      (message "diff-lisp-myers-find-all-snakes called => %s %s %s %s" a-start n b-start m))

  (when (and (> n 0) (> m 0))
    (let* (all-snakes
           ;; Use a-start and b-start is to avoid copy sequences.
           (middle-snake (diff-lisp-myers-find-middle-snake a a-start n b b-start m)))

      (when middle-snake
        (pcase-let ((`(,x ,y ,u ,v ,d) middle-snake))
          (cond
           ((and d (> d 1))
            (setq all-snakes
                  (nconc (diff-lisp-myers-find-all-snakes a a-start x b b-start y)
                         (diff-lisp-myers-find-all-snakes a (+ a-start u) (- n u) b (+ b-start v) (- m v))))
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
             ((and (= x u) (= y v))
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
             ((and (= x u) (= y v))
              (push (list a-start b-start (+ m a-start) (+ m b-start)) all-snakes))
             (t
              (push (list (+ x a-start) (+ y b-start) (+ u a-start) (+ v b-start)) all-snakes)))))))
      all-snakes)))


(defsubst diff-lisp--not-empty-snake-p (snake)
  "Test if SNAKE is not empty."
  ;; snake = (x y u v)
  ;; Test x == u and y == v ?
  (if (or (/= (nth 0 snake) (nth 2 snake))
          (/= (nth 1 snake) (nth 3 snake)))
      snake))


(defun diff-lisp-myers-do-diff (a n b m)
  "Diff sequence A with length N and sequence B with length M.
Return snakes sorted by start index."
  (let ((snakes (diff-lisp-myers-find-all-snakes a 0 n b 0 m)))
    (setq snakes (delete nil
                         (mapcar #'diff-lisp--not-empty-snake-p
                                 snakes)))
    (sort snakes (lambda (x y) (< (car x) (car y))))))

(provide 'diff-lisp-myers)
;;; diff-lisp-myers.el ends here
