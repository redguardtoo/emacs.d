;; -*- coding: utf-8; lexical-binding: t; -*-

(setq wg-use-default-session-file nil)
;; don't open last workgroup automatically in `wg-open-session',
;; I only want to check available workgroups! Nothing more.
(setq wg-load-last-workgroup nil)
(setq wg-open-this-wg nil)


;; by default, the sessions are saved in "~/.emacs_workgroups"
(defun wg-switch-workgroup ()
  "Switch to specific workgroup."
  (interactive)
  (let* ((group-names (mapcar (lambda (group)
                                ;; re-shape list for the ivy-read
                                (cons (wg-workgroup-name group) group))
                              (wg-session-workgroup-list
                               (read (wg-read-text wg-session-file)))))
         (selected-group (completing-read "Select work group: " group-names)))

    (when selected-group
      (wg-find-session-file wg-session-file)
      (wg-switch-to-workgroup selected-group))))

(provide 'init-workgroups2)
