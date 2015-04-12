(setq wg-use-default-session-file nil)
;(workgroups-mode 1) ; put this one at the bottom of .emacs
;; by default, the sessions are saved in "~/.emacs_workgroups"
(autoload 'wg-create-workgroup "workgroups2" nil t)
(autoload 'wg-kill-workgroup "workgroups2" nil t)
(autoload 'wg-find-session-file "workgroups2" nil t)
(autoload 'wg-read-workgroup-name "workgroups2" nil t)
(autoload 'wg-switch-to-workgroup "workgroups2" nil t)
(autoload 'wg-switch-to-workgroup-at-index "workgroups2" nil t)
(autoload 'wg-save-session "workgroups2" nil t)
(autoload 'wg-switch-to-buffer "workgroups2" nil t)
(autoload 'wg-switch-to-workgroup-left "workgroups2" nil t)
(autoload 'wg-switch-to-workgroup-right "workgroups2" nil t)
(autoload 'wg-undo-wconfig-change "workgroups2" nil t)
(autoload 'wg-redo-wconfig-change "workgroups2" nil t)
(autoload 'wg-save-wconfig "workgroups2" nil t)

(defun my-wg-swich-to-workgroup (wg)
  (interactive (list (progn (wg-find-session-file wg-default-session-file)
                            (wg-read-workgroup-name))))
  (wg-switch-to-workgroup wg))

(defun my-wg-switch-to-workgroup-at-index (index)
  (interactive (list (progn (wg-find-session-file wg-default-session-file)
                            (wg-read-workgroup-index))))
  (wg-switch-to-workgroup-at-index index))

(defun my-wg-save-session()
  (interactive)
  (wg-save-session t))

(provide 'init-workgroups2)
