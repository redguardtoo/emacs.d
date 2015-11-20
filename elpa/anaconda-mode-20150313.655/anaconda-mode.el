;;; anaconda-mode.el --- Code navigation, documentation lookup and completion for Python

;; Copyright (C) 2013-2015 by Artem Malyshev

;; Author: Artem Malyshev <proofit404@gmail.com>
;; URL: https://github.com/proofit404/anaconda-mode
;; Version: 0.1.0
;; Package-Requires: ((emacs "24") (json-rpc "0.0.1") (cl-lib "0.5.0") (dash "2.6.0") (f "0.16.2"))

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; See the README for more details.

;;; Code:

(require 'python)
(require 'json-rpc)
(require 'tramp)
(require 'cl-lib)
(require 'dash)
(require 'f)


;;; Server.

(defvar anaconda-mode-server
  (f-join (f-dirname load-file-name) "anaconda_mode.py")
  "Script file with anaconda_mode server.")

(defvar anaconda-mode-remote-p nil
  "Determine whatever connect to remove server or a local machine.")

(defvar anaconda-mode-host "localhost"
  "Target host with anaconda_mode server.")

(defvar anaconda-mode-port nil
  "Port for anaconda_mode connection.")

(defvar anaconda-mode-process nil
  "Currently running anaconda_mode process.")

(defvar anaconda-mode-process-pythonpath nil
  "PYTHONPATH value used to start anaconda_mode server last time.")

(defvar anaconda-mode-connection nil
  "Json Rpc connection to anaconda_mode process.")

(defvaralias 'anaconda-mode-virtualenv-variable (if (version< emacs-version "25.1")
                                                    'python-shell-virtualenv-path
                                                  'python-shell-virtualenv-root)
  "Alias to `python.el' virtualenv variable.")

(defun anaconda-mode-python ()
  "Detect python executable."
  (let ((python (if (eq system-type 'windows-nt) "pythonw" "python"))
        (bin-dir (if (eq system-type 'windows-nt) "Scripts" "bin")))
    (--if-let anaconda-mode-virtualenv-variable
        (f-join it bin-dir python)
      python)))

(defun anaconda-mode-pythonpath ()
  "Get current PYTHONPATH value."
  (getenv "PYTHONPATH"))

(defun anaconda-mode-start ()
  "Start anaconda_mode.py server."
  (when (anaconda-mode-need-restart)
    (anaconda-mode-stop))
  (unless (anaconda-mode-running-p)
    (anaconda-mode-bootstrap)))

(defun anaconda-mode-stop ()
  "Stop anaconda_mode.py server."
  (when (anaconda-mode-running-p)
    (kill-process anaconda-mode-process)
    (setq anaconda-mode-process nil)))

(defun anaconda-mode-running-p ()
  "Check for running anaconda_mode server."
  (and anaconda-mode-process
       (process-live-p anaconda-mode-process)))

(defun anaconda-mode-need-restart ()
  "Check if current `anaconda-mode-process' need restart with new args.
Return nil if it run under proper environment."
  (or (anaconda-mode-virtualenv-has-been-changed)
      (anaconda-mode-pythonpath-has-been-changed)))

(defun anaconda-mode-virtualenv-has-been-changed ()
  "Determine if virtual environment has been changed."
  (and (anaconda-mode-running-p)
       (not (equal (car (process-command anaconda-mode-process))
                   (anaconda-mode-python)))))

(defun anaconda-mode-pythonpath-has-been-changed ()
  "Determine if PYTHONPATH has been changed."
  (and (anaconda-mode-running-p)
       (not (equal anaconda-mode-process-pythonpath
                   (anaconda-mode-pythonpath)))))

(defun anaconda-mode-bootstrap ()
  "Run anaconda-mode-command process."
  (unless (executable-find "pip")
    (error "Unable to find pip executable"))
  (setq anaconda-mode-process
        (start-process
         "anaconda_mode"
         "*anaconda-mode*"
         (anaconda-mode-python)
         anaconda-mode-server))
  (setq anaconda-mode-process-pythonpath (anaconda-mode-pythonpath))
  (set-process-filter anaconda-mode-process 'anaconda-mode-process-filter)
  (while (null anaconda-mode-port)
    (accept-process-output anaconda-mode-process)
    (unless (anaconda-mode-running-p)
      (error "Unable to run anaconda-mode server")))
  (set-process-filter anaconda-mode-process nil)
  (set-process-query-on-exit-flag anaconda-mode-process nil))

(defun anaconda-mode-process-filter (process output)
  "Set `anaconda-mode-port' from PROCESS OUTPUT."
  (--when-let (s-match "anaconda_mode port \\([0-9]+\\)" output)
    (setq anaconda-mode-port (string-to-number (cadr it))))
  ;; Mimic default filter.
  (when (buffer-live-p (process-buffer process))
    (with-current-buffer (process-buffer process)
      (save-excursion
        (goto-char (process-mark process))
        (insert output)
        (set-marker (process-mark process) (point))))))


;;; Connection.

(defun anaconda-mode-connect ()
  "Connect to anaconda_mode.py server."
  (when (anaconda-mode-need-reconnect)
    (anaconda-mode-disconnect))
  (unless (anaconda-mode-connected-p)
    (setq anaconda-mode-connection
          (json-rpc-connect anaconda-mode-host anaconda-mode-port))
    (set-process-query-on-exit-flag
     (json-rpc-process anaconda-mode-connection) nil)))

(defun anaconda-mode-disconnect ()
  "Disconnect from anaconda_mode.py server."
  (when (anaconda-mode-connected-p)
    (json-rpc-close anaconda-mode-connection)
    (setq anaconda-mode-connection nil)))

(defun anaconda-mode-connected-p ()
  "Check if `anaconda-mode' connected to server."
  (and anaconda-mode-connection
       (json-rpc-live-p anaconda-mode-connection)))

(defun anaconda-mode-need-reconnect ()
  "Check if current `anaconda-mode-connection' need to be reconnected."
  (and (anaconda-mode-connected-p)
       (or (not (equal (json-rpc-host anaconda-mode-connection)
                       anaconda-mode-host))
           (not (equal (json-rpc-port anaconda-mode-connection)
                       anaconda-mode-port)))))


;;; Interaction.

;;;###autoload
(defun anaconda-mode-remote (host port)
  "Suggest anaconda_mode.py running on HOST at PORT."
  (interactive (list (read-string "Host: ") (read-number "Port: ")))
  (setq anaconda-mode-remote-p t
        anaconda-mode-host host
        anaconda-mode-port port))

;;;###autoload
(defun anaconda-mode-local ()
  "Suggest anaconda_mode.py running on localhost."
  (interactive)
  (setq anaconda-mode-remote-p nil
        anaconda-mode-host "localhost"
        anaconda-mode-port nil))

(defun anaconda-mode-call (command)
  "Make remote procedure call for COMMAND."
  (unless anaconda-mode-remote-p
    (anaconda-mode-start))
  (anaconda-mode-connect)
  ;; use list since not all dash functions operate on vectors
  (let ((json-array-type 'list))
    (json-rpc
     anaconda-mode-connection
     command
     (buffer-substring-no-properties (point-min) (point-max))
     (line-number-at-pos (point))
     (- (point) (line-beginning-position))
     (anaconda-mode-file-name))))

(defun anaconda-mode-file-name ()
  "Return appropriate buffer file name both for local and tramp files."
  (if (tramp-tramp-file-p (buffer-file-name))
      (tramp-file-name-localname
       (tramp-dissect-file-name
        (buffer-file-name)))
    (buffer-file-name)))


;;; Code completion.

(defun anaconda-mode-complete-at-point ()
  "Complete at point with anaconda_mode."
  (let* ((bounds (bounds-of-thing-at-point 'symbol))
         (start (or (car bounds) (point)))
         (stop (or (cdr bounds) (point))))
    (list start stop
          (completion-table-dynamic
           'anaconda-mode-complete-thing))))

(defun anaconda-mode-complete-thing (&rest ignored)
  "Complete python thing at point.
Do nothing in comments block.
IGNORED parameter is the string for which completion is required."
  (unless (python-syntax-comment-or-string-p)
    (--map (plist-get it :name)
           (anaconda-mode-complete))))

(defun anaconda-mode-complete ()
  "Request completion candidates."
  (anaconda-mode-call "complete"))


;;; View documentation.

(defun anaconda-mode-view-doc ()
  "Show documentation for context at point."
  (interactive)
  (pop-to-buffer
   (anaconda-mode-doc-buffer
    (or (anaconda-mode-call "doc")
        (error "No documentation found")))))

(defun anaconda-mode-doc-buffer (doc)
  "Display documentation buffer with contents DOC."
  (let ((buf (get-buffer-create "*anaconda-doc*")))
    (with-current-buffer buf
      (view-mode -1)
      (erase-buffer)
      (insert doc)
      (goto-char (point-min))
      (view-mode 1)
      buf)))


;;; Usages.

(defun anaconda-mode-usages ()
  "Show usages for thing at point."
  (interactive)
  (anaconda-nav-navigate
   (or (anaconda-mode-call "usages")
       (error "No usages found"))))


;;; Definitions and assignments.

(defun anaconda-mode-goto-definitions ()
  "Goto definition for thing at point."
  (interactive)
  (anaconda-nav-navigate
   (or (anaconda-mode-call "goto_definitions")
       (error "No definition found"))
   t))

(defun anaconda-mode-goto-assignments ()
  "Goto assignment for thing at point."
  (interactive)
  (anaconda-nav-navigate
   (or (anaconda-mode-call "goto_assignments")
       (error "No assignment found"))
   t))

(defun anaconda-mode-goto ()
  "Goto definition or fallback to assignment for thing at point."
  (interactive)
  (anaconda-nav-navigate
   (or (anaconda-mode-call "goto_definitions")
       (anaconda-mode-call "goto_assignments")
       (error "No definition found"))
   t))


;;; Anaconda navigator mode

(defvar anaconda-nav--last-marker nil)
(defvar anaconda-nav--markers ())

(defun anaconda-nav-pop-marker ()
  "Switch to buffer of most recent marker."
  (interactive)
  (unless anaconda-nav--markers
    (error "No marker available"))
  (let* ((marker (pop anaconda-nav--markers))
         (buffer (marker-buffer marker)))
    (unless (buffer-live-p buffer)
      (error "Buffer no longer available"))
    (switch-to-buffer buffer)
    (goto-char (marker-position marker))
    (set-marker marker nil)
    (anaconda-nav--cleanup-buffers)))

(defun anaconda-nav--push-last-marker ()
  "Add last marker to markers."
  (when (markerp anaconda-nav--last-marker)
    (push anaconda-nav--last-marker anaconda-nav--markers)
    (setq anaconda-nav--last-marker nil)))

(defun anaconda-nav--all-markers ()
  "Markers including last-marker."
  (if anaconda-nav--last-marker
      (cons anaconda-nav--last-marker anaconda-nav--markers)
    anaconda-nav--markers))

(defvar anaconda-nav--window-configuration nil)
(defvar anaconda-nav--created-buffers ())

(defun anaconda-nav--cleanup-buffers ()
  "Kill unmodified buffers (without markers) created by anaconda-nav."
  (let* ((marker-buffers (-map 'marker-buffer (anaconda-nav--all-markers)))
         (result (--separate (-contains? marker-buffers it)
                             anaconda-nav--created-buffers)))
    (setq anaconda-nav--created-buffers (car result))
    (-each (cadr result) 'kill-buffer-if-not-modified)))

(defun anaconda-nav--get-or-create-buffer (path)
  "Get buffer for PATH, and record if buffer was created."
  (or (find-buffer-visiting path)
      (let ((created-buffer (find-file-noselect path)))
        (anaconda-nav--cleanup-buffers)
        (push created-buffer anaconda-nav--created-buffers)
        created-buffer)))

(defun anaconda-nav--restore-window-configuration ()
  "Restore window configuration."
  (when anaconda-nav--window-configuration
    (set-window-configuration anaconda-nav--window-configuration)
    (setq anaconda-nav--window-configuration nil)))

(defun anaconda-nav-navigate (result &optional goto-if-single-item)
  "Navigate RESULT, jump if only one item and GOTO-IF-SINGLE-ITEM is non-nil."
  (setq anaconda-nav--last-marker (point-marker))
  (if (and goto-if-single-item (= 1 (length result)))
      (progn (anaconda-nav--push-last-marker)
             (switch-to-buffer (anaconda-nav--item-buffer (car result))))
    (setq anaconda-nav--window-configuration (current-window-configuration))
    (delete-other-windows)
    (switch-to-buffer-other-window (anaconda-nav--prepare-buffer result))))

(defun anaconda-nav--prepare-buffer (result)
  "Render RESULT in the navigation buffer."
  (with-current-buffer (get-buffer-create "*anaconda-nav*")
    (setq buffer-read-only nil)
    (erase-buffer)
    (setq-local overlay-arrow-position nil)
    (--> result
      (--group-by (cons (plist-get it :module)
                        (plist-get it :path)) it)
      (--each it (apply 'anaconda-nav--insert-module it)))
    (goto-char (point-min))
    (anaconda-nav-mode)
    (current-buffer)))

(defun anaconda-nav--insert-module (header &rest items)
  "Insert a module consisting of a HEADER with ITEMS."
  (insert (propertize (car header)
                      'face 'bold
                      'anaconda-nav-module t)
          "\n")
  (--each items (insert (anaconda-nav--format-item it) "\n"))
  (insert "\n"))

(defun anaconda-nav--format-item (item)
  "Format ITEM as a row."
  (propertize
   (concat (propertize (format "%7d " (plist-get item :line))
                       'face 'compilation-line-number)
           (anaconda-nav--get-item-description item))
   'anaconda-nav-item item
   'follow-link t
   'mouse-face 'highlight))

(defun anaconda-nav--get-item-description (item)
  "Format description of ITEM."
  (cl-destructuring-bind (&key column name description type &allow-other-keys) item
    (cond ((string= type "module") "«module definition»")
          (t (let ((to (+ column (length name))))
               (when (string= name (substring description column to))
                 (put-text-property column to 'face 'highlight description))
               description)))))

(defun anaconda-nav-next-error (&optional argp reset)
  "Move to the ARGP'th next match, searching from start if RESET is non-nil."
  (interactive "p")
  (with-current-buffer (get-buffer "*anaconda-nav*")
    (goto-char (cond (reset (point-min))
                     ((cl-minusp argp) (line-beginning-position))
                     ((cl-plusp argp) (line-end-position))
                     ((point))))

    (--dotimes (abs argp)
      (anaconda-nav--goto-property 'anaconda-nav-item (cl-plusp argp)))

    (setq-local overlay-arrow-position (copy-marker (line-beginning-position)))
    (--when-let (get-text-property (point) 'anaconda-nav-item)
      (pop-to-buffer (anaconda-nav--item-buffer it)))))

(defun anaconda-nav--goto-property (prop forwardp)
  "Goto next property PROP in direction FORWARDP."
  (--if-let (anaconda-nav--find-property prop forwardp)
      (goto-char it)
    (error "No more matches")))

(defun anaconda-nav--find-property (prop forwardp)
  "Find next property PROP in direction FORWARDP."
  (let ((search (if forwardp #'next-single-property-change
                  #'previous-single-property-change)))
    (-when-let (pos (funcall search (point) prop))
      (if (get-text-property pos prop) pos
        (funcall search pos prop)))))

(defun anaconda-nav--item-buffer (item)
  "Get buffer of ITEM and position the point."
  (cl-destructuring-bind (&key line column name path &allow-other-keys) item
    (with-current-buffer (anaconda-nav--get-or-create-buffer path)
      (goto-char (point-min))
      (forward-line (1- line))
      (forward-char column)
      (anaconda-nav--highlight name)
      (current-buffer))))

(defun anaconda-nav--highlight (name)
  "Highlight NAME or line at point."
  (isearch-highlight (point)
                     (if (string= (symbol-at-point) name)
                         (+ (point) (length name))
                       (point-at-eol)))
  (run-with-idle-timer 0.5 nil 'isearch-dehighlight))

(defvar anaconda-nav-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [mouse-2] 'anaconda-nav-goto-item)
    (define-key map (kbd "RET") 'anaconda-nav-goto-item)
    (define-key map (kbd "n") 'next-error)
    (define-key map (kbd "p") 'previous-error)
    (define-key map (kbd "N") 'anaconda-nav-next-module)
    (define-key map (kbd "P") 'anaconda-nav-previous-module)
    (define-key map (kbd "q") 'anaconda-nav-quit)
    map)
  "Keymap for `anaconda-nav-mode'.")

(defun anaconda-nav-next-module ()
  "Visit first error of next module."
  (interactive)
  (anaconda-nav--goto-property 'anaconda-nav-module t)
  (next-error))

(defun anaconda-nav-previous-module ()
  "Visit first error of previous module."
  (interactive)
  (anaconda-nav--goto-property 'anaconda-nav-item nil)
  (anaconda-nav--goto-property 'anaconda-nav-module nil)
  (next-error))

(defun anaconda-nav-quit ()
  "Quit `anaconda-nav-mode' and restore window configuration."
  (interactive)
  (quit-window)
  (anaconda-nav--restore-window-configuration))

(defun anaconda-nav-goto-item (&optional event)
  "Go to the location of the item from EVENT."
  (interactive (list last-input-event))
  (when event (goto-char (posn-point (event-end event))))
  (-when-let (buffer (anaconda-nav-next-error 0))
    (anaconda-nav--restore-window-configuration)
    (anaconda-nav--push-last-marker)
    (switch-to-buffer buffer)))

(define-derived-mode anaconda-nav-mode special-mode "anaconda-nav"
  "Major mode for navigating a list of source locations."
  (use-local-map anaconda-nav-mode-map)
  (setq next-error-function 'anaconda-nav-next-error)
  (setq next-error-last-buffer (current-buffer))
  (next-error-follow-minor-mode 1))


;;; Eldoc.

(defvar anaconda-eldoc-as-single-line nil
  "If not nil, trim eldoc string to frame width.")

(defun anaconda-eldoc-format-params (args index)
  "Build colorized ARGS string with current arg pointed to INDEX."
  (apply
   'concat
   (->> args
     (--map-indexed
      (if (= index it-index)
          (propertize it 'face 'eldoc-highlight-function-argument)
        it))
     (-interpose ", "))))

(cl-defun anaconda-eldoc-format (&key name index params)
  (concat
   (propertize name 'face 'font-lock-function-name-face)
   "("
   (anaconda-eldoc-format-params params index)
   ")"))

(defun anaconda-eldoc-function ()
  "Show eldoc for context at point."
  (ignore-errors
    (-when-let* ((res (anaconda-mode-call "eldoc"))
                 (doc (apply 'anaconda-eldoc-format res)))
      (if anaconda-eldoc-as-single-line
          (substring doc 0 (min (frame-width) (length doc)))
        doc))))


;;; Anaconda minor mode.

(defvar anaconda-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "M-?") 'anaconda-mode-view-doc)
    (define-key map (kbd "M-r") 'anaconda-mode-usages)
    (define-key map [remap find-tag] 'anaconda-mode-goto)
    (define-key map [remap pop-tag-mark] 'anaconda-nav-pop-marker)
    map)
  "Keymap for `anaconda-mode'.")

;;;###autoload
(define-minor-mode anaconda-mode
  "Code navigation, documentation lookup and completion for Python.

\\{anaconda-mode-map}"
  :lighter " Anaconda"
  :keymap anaconda-mode-map
  (if anaconda-mode
      (turn-on-anaconda-mode)
    (turn-off-anaconda-mode)))

(defun turn-on-anaconda-mode ()
  "Turn on `anaconda-mode'."
  (add-hook 'completion-at-point-functions
            'anaconda-mode-complete-at-point nil t)
  (make-local-variable 'eldoc-documentation-function)
  (setq-local eldoc-documentation-function 'anaconda-eldoc-function))

(defun turn-off-anaconda-mode ()
  "Turn off `anaconda-mode'."
  (remove-hook 'completion-at-point-functions
               'anaconda-mode-complete-at-point t)
  (kill-local-variable 'eldoc-documentation-function))

(provide 'anaconda-mode)

;;; anaconda-mode.el ends here
