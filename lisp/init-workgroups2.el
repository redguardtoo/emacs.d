;; -*- coding: utf-8; lexical-binding: t; -*-

(setq wg-use-default-session-file nil)
;; don't open last workgroup automatically in `wg-open-session',
;; I only want to check available workgroups! Nothing more.
(setq wg-load-last-workgroup nil)
(setq wg-open-this-wg nil)


;(workgroups-mode 1) ; put this one at the bottom of .emacs
;; by default, the sessions are saved in "~/.emacs_workgroups"
(defun my-wg-read-session-file ()
  (read
   (with-temp-buffer
     (insert-file-contents (file-truename wg-session-file))
     (buffer-string))))

(defun my-wg-switch-workgroup ()
  (interactive)
  (my-ensure 'workgroups2)
  (my-ensure 'ivy)
  (let* ((group-names (mapcar (lambda (group)
                                ;; re-shape list for the ivy-read
                                (cons (wg-workgroup-name group) group))
                              (wg-session-workgroup-list
                               (my-wg-read-session-file)))))

    (ivy-read "Select work group: "
              group-names
              :action (lambda (e)
                        (wg-find-session-file wg-default-session-file)
                        ;; ivy8 & ivy9
                        (if (stringp (car e)) (setq e (cdr e)))
                        (wg-switch-to-workgroup e)))))

(provide 'init-workgroups2)
