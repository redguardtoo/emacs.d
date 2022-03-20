;;; workgroups2-support.el --- load/unload 3rd party buffers  -*- lexical-binding: t -*-


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

(require 'workgroups2-sdk)
(require 'dframe)

(defmacro wg-switch-to-buffer (buffer &rest body)
  "Switch to BUFFER and eval BODY."
  `(let ((new-buffer (switch-to-buffer ,buffer)))
     ,@body
     new-buffer))

(defun wg-switch-to-shell-buffer (buffer)
  "Switch to a shell BUFFER."
  (wg-switch-to-buffer buffer
                       (goto-char (point-max))))

(defmacro wg-support (mode pkg params)
  "Macro to create (de)serialization functions for a buffer.
You need to save/restore a specific MODE which is loaded from a
package PKG.  In PARAMS you give local variables to save and a
deserialization function."
  (declare (indent 2))
  `(let ((mode-str (symbol-name ,mode))
         (args ,params))

     ;; Fix compile warn.
     (ignore args)

     (eval
      `(defun ,(intern (format "wg-deserialize-%s-buffer" mode-str)) (buffer)
         "DeSerialization function created with `wg-support'.
Gets saved variables and runs code to restore a BUFFER."
         (when (require ',,pkg nil (unless wg-debug 'noerror))
           (wg-dbind (this-function variables) (wg-buf-special-data buffer)
             (let ((default-directory (car variables))
                   (df (cdr (assoc 'deserialize ',,params)))
                   (user-vars (cadr variables)))
               (if df
                   (funcall df buffer user-vars)
                 (get-buffer-create wg-default-buffer))))))
      t)

     (eval
      `(defun ,(intern (format "wg-serialize-%s-buffer" mode-str)) (buffer)
         "Serialization function created with `wg-support'.
Saves some variables to restore a BUFFER later."
         (when (get-buffer buffer)
           (with-current-buffer buffer
             (when (eq major-mode ',,mode)
               (let ((sf (cdr (assoc 'serialize ',,params)))
                     rlt)
                 (list ',(intern (format "wg-deserialize-%s-buffer" mode-str))
                       (list default-directory
                             (when sf
                               (setq rlt (funcall sf buffer))
                               (cond
                                ((bufferp rlt)
                                 (buffer-name rlt))
                                (t
                                 rlt))))))))))
      t)

     ;; Add function to `wg-special-buffer-serdes-functions'
     (eval
      `(add-to-list 'wg-special-buffer-serdes-functions
                    ',(intern (format "wg-serialize-%s-buffer" mode-str)) t)
      t)))

;; Dired
(wg-support 'dired-mode
            'dired
            `((deserialize . ,(lambda (_buffer)
                                (ignore _buffer)
                                (when (or wg-restore-remote-buffers
                                          (not (file-remote-p default-directory)))
                                  (let ((d (wg-get-first-existing-dir)))
                                    (if (file-directory-p d) (dired d))))))))

(wg-support 'Info-mode
            'info
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (list Info-current-file Info-current-node)))
              (deserialize . ,(lambda (_buffer vars)
                                (if vars
                                    (if (fboundp 'Info-find-node)
                                        (apply #'Info-find-node vars))
                                  (info)
                                  (wg-switch-to-buffer (wg-buf-name _buffer)))))))

(defun wg-support-help-mode-serialize (_buffer)
  "Serialize `help-mode' data in _BUFFER."
  (ignore _buffer)
  (list (mapcar (lambda (e)
                  (cond
                   ((and (functionp e) (not (symbolp e)))
                    ;; convert compiled function into symbol
                    (wg-symbol-of-compiled-function e))
                   (t
                    e)))
                ;; Only need first two items.
                ;; Other items could be file buffers which breaks the session file
                ;; See bug #29
                (and help-xref-stack-item
                     (if (> (length help-xref-stack-item) 2) (cl-subseq help-xref-stack-item 0 2)
                       help-xref-stack-item)))))

(defun wg-support-help-mode-deserialize (_buffer vars)
  "Deserialize `help-mode' data in _BUFFER with VARS."
  (ignore _buffer)
  (wg-dbind (item) vars
            (condition-case err
                (funcall (nth 0 item) (nth 1 item))
              (error (message "error=%s" err)))
            (wg-switch-to-buffer "*Help*")))

(wg-support 'help-mode
            'help-mode
            `((serialize . wg-support-help-mode-serialize)
              (deserialize . wg-support-help-mode-deserialize)))

;; ielm
(wg-support 'inferior-emacs-lisp-mode
            'ielm
            `((deserialize . ,(lambda (_buffer vars)
                                (ignore _buffer vars)
                                (ielm)
                                (wg-switch-to-buffer "*ielm*")))))

;; Magit status
(wg-support 'magit-status-mode
            'magit
            `((deserialize . ,(lambda (_buffer vars)
                                (ignore _buffer vars)
                                (if (file-directory-p default-directory)
                                    (magit-status-setup-buffer default-directory)
                                  (let ((d (wg-get-first-existing-dir)))
                                    (if (file-directory-p d) (dired d))))))))

;; Shell
(wg-support 'shell-mode
            'shell
            `((deserialize . ,(lambda (_buffer vars)
                                (ignore vars)
                                (shell (wg-buf-name _buffer))))))

;; org-agenda buffer
(defun wg-get-org-agenda-view-commands ()
  "Return commands to restore the state of Agenda buffer.
Can be restored using \"(eval commands)\"."
  (interactive)
  (when (and  (boundp 'org-agenda-buffer-name)
              (get-buffer org-agenda-buffer-name))
    (wg-switch-to-buffer
     org-agenda-buffer-name
     (let* ((p (or (and (looking-at "\\'") (1- (point))) (point)))
            (series-redo-cmd (get-text-property p 'org-series-redo-cmd))
            (rlt (or series-redo-cmd
                     (get-text-property p 'org-redo-cmd))))
       (when wg-debug
         (message "wg-get-org-agenda-view-commands called rlt=%s" rlt))
       rlt))))

(defun wg-run-agenda-cmd (f)
  "Run commands F in Agenda buffer.
You can get these commands using `wg-get-org-agenda-view-commands'."
  (when (and (boundp 'org-agenda-buffer-name)
             (fboundp 'org-current-line)
             (fboundp 'org-goto-line))
    (if (get-buffer org-agenda-buffer-name)
        (save-window-excursion
          (wg-switch-to-buffer org-agenda-buffer-name
            (let* ((line (org-current-line)))
              (if f (eval f t))
              (org-goto-line line)))))))

(wg-support 'org-agenda-mode
            'org-agenda
            '((serialize . (lambda (_buffer)
                             (ignore _buffer)
                             (wg-get-org-agenda-view-commands)))
              (deserialize . (lambda (_buffer vars)
                               (ignore _buffer)
                               (org-agenda-list)
                               (wg-switch-to-buffer org-agenda-buffer-name
                                                    (wg-run-agenda-cmd vars))))))

;; eshell
(wg-support 'eshell-mode
 'esh-mode
 '((deserialize . (lambda (_buffer vars)
                    (ignore vars)
                    (eshell t)
                    (rename-buffer (wg-buf-name _buffer) t)
                    (current-buffer)))))

;; term-mode
;;
;; This should work for `ansi-term's, too, as there doesn't seem to
;; be any difference between the two except how the name of the
;; buffer is generated.
;;
(wg-support 'term-mode
            'term
            `((serialize . ,(lambda (_buffer)
                              (if (get-buffer-process _buffer)
                                  (car (last (process-command (get-buffer-process _buffer))))
                                "/bin/bash")))
              (deserialize . ,(lambda (_buffer vars)
                                (cl-labels ((term-window-width () 80)
                                            (window-height () 24))
                                  (prog1 (term vars)
                                    (rename-buffer (wg-buf-name _buffer) t)))))))

;; `inferior-python-mode'
(wg-support 'inferior-python-mode
            'python
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (list python-shell-interpreter python-shell-interpreter-args)))
              (deserialize . ,(lambda (_buffer vars)
                                (ignore _buffer)
                                (wg-dbind (pythoncmd pythonargs) vars
                                          (python-shell-make-comint (concat pythoncmd " " pythonargs)
                                                                    (python-shell-get-process-name nil)
                                                                    t)
                                          (wg-switch-to-shell-buffer (process-buffer (python-shell-get-process))))))))


;; Sage shell ;;
(wg-support 'inferior-sage-mode
            'sage-mode
            `((deserialize . ,(lambda (_buffer vars)
                                (ignore vars)
                                (save-window-excursion
                                  (if (boundp' sage-command)
                                      (run-sage t sage-command t)))
                                (when (and (boundp 'sage-buffer) sage-buffer)
                                  (set-buffer sage-buffer)
                                  (wg-switch-to-shell-buffer sage-buffer))))))

;; `inferior-ess-mode'     M-x R
(defvar ess-history-file)
(defvar ess-ask-about-transfile)
(defvar ess-ask-for-ess-directory)

(wg-support 'inferior-ess-mode
            'ess-inf
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (list inferior-ess-program)))
              (deserialize . ,(lambda (_buffer vars)
                                (wg-dbind (_cmd) vars
                                          (let ((ess-ask-about-transfile nil)
                                                (ess-ask-for-ess-directory nil)
                                                (ess-history-file nil))
                                            (R)
                                            (get-buffer (wg-buf-name _buffer))))))))

;; `inferior-octave-mode'
(wg-support 'inferior-octave-mode
            'octave
            `((deserialize . ,(lambda (_buffer vars)
                                (ignore vars)
                                (prog1 (run-octave)
                                  (rename-buffer (wg-buf-name _buffer) t))))))

;; `prolog-inferior-mode'
(wg-support 'prolog-inferior-mode
            'prolog
            `((deserialize . ,(lambda (_buffer vars)
                                (save-window-excursion
                                  (run-prolog nil))
                                (wg-switch-to-shell-buffer "*prolog*")))))

;; `ensime-inf-mode'
(wg-support 'ensime-inf-mode
            'ensime
            `((deserialize . ,(lambda (_buffer vars)
                                (ignore _buffer vars)
                                (save-window-excursion
                                  (ensime-inf-switch))
                                (when (boundp 'ensime-inf-buffer-name)
                                  (wg-switch-to-shell-buffer ensime-inf-buffer-name))))))

;; compilation-mode
;;
;; I think it's not a good idea to compile a program just to switch
;; workgroups. So just restoring a buffer name.
(wg-support 'compilation-mode
            'compile
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (if (boundp' compilation-arguments) compilation-arguments)))
              (deserialize . ,(lambda (_buffer vars)
                                (save-window-excursion
                                  (get-buffer-create (wg-buf-name _buffer)))
                                (with-current-buffer (wg-buf-name _buffer)
                                  (when (boundp' compilation-arguments)
                                    (make-local-variable 'compilation-arguments)
                                    (setq compilation-arguments vars)))
                                (wg-switch-to-shell-buffer (wg-buf-name _buffer))))))

;; grep-mode
;; see grep.el - `compilation-start' - it is just a compilation buffer
;; local variables:
;; `compilation-arguments' == (cmd mode nil nil)
(wg-support 'grep-mode
            'grep
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (if (boundp' compilation-arguments) compilation-arguments)))
              (deserialize . ,(lambda (_buffer vars)
                                (ignore _buffer)
                                (compilation-start (car vars) (nth 1 vars))
                                (wg-switch-to-buffer "*grep*")))))

(defun wg-deserialize-slime-buffer (buf)
  "Deserialize `slime' buffer BUF."
  (when (require 'slime nil 'noerror)
    (wg-dbind (_this-function args) (wg-buf-special-data buf)
      (let ((default-directory (car args))
            (arguments (nth 1 args)))
        (when (and (fboundp 'slime-start*)
                   (fboundp 'slime-process))
          (save-window-excursion
            (slime-start* arguments))
          (wg-switch-to-buffer (process-buffer (slime-process))))))))

;; `comint-mode'  (general mode for all shells)
;;
;; It may have different shells. So we need to determine which shell is
;; now in `comint-mode' and how to restore it.
;;
;; Just executing `comint-exec' may be not enough because we can miss
;; some hooks or any other stuff that is executed when you run a
;; specific shell.
(defun wg-serialize-comint-buffer (buffer)
  "Serialize comint BUFFER."
  (with-current-buffer buffer
    (when (eq major-mode 'comint-mode)
      ;; `slime-inferior-lisp-args' var is used when in `slime'
      (when (and (boundp 'slime-inferior-lisp-args)
                 slime-inferior-lisp-args)
        (list 'wg-deserialize-slime-buffer
              (list default-directory slime-inferior-lisp-args))))))

;; inf-mongo
;; https://github.com/tobiassvn/inf-mongo
;; `mongo-command' - command used to start inferior mongo
(wg-support 'inf-mongo-mode
            'inf-mongo
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (if (boundp 'inf-mongo-command) inf-mongo-command)))
              (deserialize . ,(lambda (_buffer vars)
                                (ignore _buffer)
                                (save-window-excursion
                                  (when (fboundp 'inf-mongo)
                                    (inf-mongo vars)))
                                (when (get-buffer "*mongo*")
                                  (wg-switch-to-shell-buffer "*mongo*"))))))

(defun wg-temporarily-rename-buffer-if-exists (buffer)
  "Rename BUFFER if it exists."
  (when (get-buffer buffer)
    (with-current-buffer buffer
      (rename-buffer "*wg--temp-buffer*" t))))

;; SML shell
;; Functions to serialize deserialize inferior sml buffer
;; `inf-sml-program' is the program run as inferior sml, is the
;; `inf-sml-args' are the extra parameters passed, `inf-sml-host'
;; is the host on which sml was running when serialized
(wg-support 'inferior-sml-mode
            'sml-mode
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (list (if (boundp 'sml-program-name) sml-program-name)
                                    (if (boundp 'sml-default-arg) sml-default-arg)
                                    (if (boundp 'sml-host-name) sml-host-name))))
              (deserialize . ,(lambda (_buffer vars)
                                (wg-dbind (program args host) vars
                                          (save-window-excursion
                                            ;; If a inf-sml buffer already exists rename it temporarily
                                            ;; otherwise `run-sml' will simply switch to the existing
                                            ;; buffer, however we want to create a separate buffer with
                                            ;; the serialized name
                                            (let* ((inf-sml-buffer-name (concat "*"
                                                                                (file-name-nondirectory program)
                                                                                "*"))
                                                   (existing-sml-buf (wg-temporarily-rename-buffer-if-exists
                                                                      inf-sml-buffer-name)))
                                              (with-current-buffer (run-sml program args host)
                                                (rename-buffer (wg-buf-name _buffer) t)

                                                ;; re-rename the previously renamed buffer
                                                (when existing-sml-buf
                                                  (with-current-buffer existing-sml-buf
                                                    (rename-buffer inf-sml-buffer-name t))))))
                                          (wg-switch-to-shell-buffer (wg-buf-name _buffer)))))))

;; Geiser repls
;; http://www.nongnu.org/geiser/
(wg-support 'geiser-repl-mode
            'geiser
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (list geiser-impl--implementation)))
              (deserialize . ,(lambda (_buffer vars)
                                (when (fboundp 'run-geiser)
                                  (wg-dbind (impl) vars
                                            (run-geiser impl)
                                            (goto-char (point-max))))
                                (wg-switch-to-shell-buffer (wg-buf-name _buffer))))))

;; w3m-mode
(wg-support 'w3m-mode
            'w3m
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (list w3m-current-url)))
              (deserialize . ,(lambda (_buffer vars)
                                (ignore _buffer)
                                (wg-dbind (url) vars
                                          (w3m-goto-url url))))))

(wg-support 'eww-mode
            'eww
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              (list (plist-get eww-data :url))))
              (deserialize . ,(lambda (_buffer vars)
                                (ignore _buffer)
                                (wg-dbind (url) vars
                                          (eww url))))))

(wg-support 'notmuch-hello-mode
            'notmuch
            `((deserialize . ,(lambda (_buffer vars)
                                (ignore vars)
                                (notmuch)
                                (wg-switch-to-buffer (wg-buf-name _buffer))))))

(defvar dired-sidebar-display-alist)
(wg-support 'dired-sidebar-mode
            'dired-sidebar
            `((serialize . ,(lambda (_buffer)
                              (ignore _buffer)
                              dired-sidebar-display-alist))
              (deserialize . ,(lambda (_buffer saved-display-alist)
                                (ignore _buffer)
                                (when (and (or wg-restore-remote-buffers
                                               (not (file-remote-p default-directory)))
                                           ;; Restore buffer only if `dired-sidebar-show-sidebar'
                                           ;; will place it in the same side window as before.
                                           (equal dired-sidebar-display-alist saved-display-alist))
                                  (let ((dir (wg-get-first-existing-dir)))
                                    (when (file-directory-p dir)
                                      (let ((buffer (dired-sidebar-get-or-create-buffer dir)))
                                        ;; Set up the buffer by calling `dired-sidebar-show-sidebar'
                                        ;; for side effects only, discarding the created window. We
                                        ;; don't want to add extra new windows during the session
                                        ;; restoration process.
                                        (save-window-excursion (dired-sidebar-show-sidebar buffer))
                                        ;; HACK: Replace the just-restored window after session is
                                        ;; restored. This ensures that we perform any additional
                                        ;; window setup that was not done by deserialization. The
                                        ;; point is to avoid depending too closely on the
                                        ;; implementation details of dired-sidebar. Rather than
                                        ;; serialize every detail, we let `dired-sidebar-show-sidebar'
                                        ;; do the work.
                                        (let ((frame (selected-frame)))
                                          (run-at-time 0 nil
                                                       (lambda ()
                                                         (with-selected-frame frame
                                                           (dired-sidebar-hide-sidebar)
                                                           (dired-sidebar-show-sidebar buffer)))))
                                        buffer))))))))

(wg-support 'ivy-occur-grep-mode
            'ivy
            `((serialize . ,(lambda (_buffer)
                              (when wg-debug
                                (message "ivy-occur-grep-mode serialize is called => %s" _buffer))
                              (list (base64-encode-string (buffer-string) t))))
              (deserialize . ,(lambda (_buffer vars)
                                (when wg-debug
                                  (message "ivy-occur-grep-mode deserialize is called => %s" file))
                                (wg-switch-to-buffer (wg-buf-name _buffer)
                                                     (insert (base64-decode-string (nth 0 vars)))
                                                     (goto-char (point-min))
                                                     ;; easier than `ivy-occur-grep-mode' to set up
                                                     (grep-mode))))))

(wg-support 'pdf-view-mode
            'pdf-tools
            `((serialize . ,(lambda (_buffer)
                              (when wg-debug
                                (message "pdf-view-mode serialize is called => %s" _buffer))
                              (list (pdf-view-current-page) pdf-view-display-size)))
              (deserialize . ,(lambda (_buffer vars)
                                (let ((file (wg-buf-file-name _buffer))
                                      buffer)
                                  (when wg-debug
                                    (message "pdf-view-mode deserialize is called => %s" file))
                                  (when (and file (file-exists-p file))
                                    (condition-case err
                                        (progn
                                          (when (setq buffer (find-file-noselect file nil nil nil))
                                            (with-current-buffer buffer
                                              (rename-buffer (wg-buf-name _buffer) t)
                                              (wg-set-buffer-uid-or-error (wg-buf-uid _buffer)))
                                            (switch-to-buffer buffer)
                                            (let* ((page (nth 0 vars))
                                                   (view-display-size (nth 1 vars)))
                                              (when page
                                                (pdf-view-goto-page page))
                                              (when view-display-size
                                                (setq pdf-view-display-size view-display-size)
                                                (cond
                                                 ((eq pdf-view-display-size 'fit-height)
                                                  (image-set-window-vscroll 0))
                                                 ((eq pdf-view-display-size 'fit-width)
                                                  (image-set-window-hscroll 0))
                                                 (t
                                                  (image-set-window-vscroll 0)
                                                  (image-set-window-hscroll 0)))
                                                (pdf-view-redisplay t)))))
                                      (error
                                       (wg-file-buffer-error file (error-message-string err)))))
                                  buffer)))))

(wg-support 'speedbar-mode
            'speedbar
            `((deserialize . ,(lambda (_buffer vars)
                                (ignore vars)
                                (setq speedbar-buffer (switch-to-buffer (wg-buf-name _buffer)))
                                (speedbar-reconfigure-keymaps)
                                (speedbar-update-contents)
                                (speedbar-set-timer dframe-update-speed)
                                speedbar-buffer))))

(provide 'workgroups2-support)
;;; workgroups2-support.el ends here
