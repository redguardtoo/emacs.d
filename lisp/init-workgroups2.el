(setq wg-use-default-session-file nil)
;; don't open last workgroup automatically in `wg-open-session',
;; I only want to check available workgroups! Nothing more.
(setq wg-load-last-workgroup nil)
(setq wg-open-this-wg nil)

;(workgroups-mode 1) ; put this one at the bottom of .emacs
;; by default, the sessions are saved in "~/.emacs_workgroups"
(autoload 'wg-create-workgroup "workgroups2" nil t)

(defun my-wg-switch-workgroup ()
  (interactive)
  (let (group-names selected-group)
    (unless (featurep 'workgroups2)
      (require 'workgroups2))
    (setq group-names
          (mapcar (lambda (group)
                    ;; re-shape list for the ivy-read
                    (cons (wg-workgroup-name group) group))
                  (wg-session-workgroup-list (read (f-read-text (file-truename wg-session-file))))))
    (ivy-read "work groups" group-names
              :action (lambda (group)
                        (wg-find-session-file wg-default-session-file)
                        (wg-switch-to-workgroup group)))))

(eval-after-load 'workgroups2
  '(progn
     ;; make sure wg-create-workgroup always success
     (defadvice wg-create-workgroup (around wg-create-workgroup-hack activate)
       (unless (file-exists-p (wg-get-session-file))
         (wg-reset t)
         (wg-save-session t))

       (unless wg-current-session
         ;; code extracted from `wg-open-session'.
         ;; open session but do NOT load any workgroup.
         (let ((session (read (f-read-text (file-truename wg-session-file)))))
           (setf (wg-session-file-name session) wg-session-file)
           (wg-reset-internal (wg-unpickel-session-parameters session))))
       ad-do-it
       ;; save the session file in real time
       (wg-save-session t))

     (defadvice wg-reset (after wg-reset-hack activate)
       (wg-save-session t))

     ;; I'm fine to to override the original workgroup
     (defadvice wg-unique-workgroup-name-p (around wg-unique-workgroup-name-p-hack activate)
       (setq ad-return-value t))))

(provide 'init-workgroups2)
