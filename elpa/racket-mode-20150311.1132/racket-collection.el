;;; racket-collection.el

;; Copyright (c) 2013-2015 by Greg Hendershott.
;; Portions Copyright (C) 1985-1986, 1999-2013 Free Software Foundation, Inc.

;; Author: Greg Hendershott
;; URL: https://github.com/greghendershott/racket-mode

;; License:
;; This is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version. This is distributed in the hope that it will be
;; useful, but without any warranty; without even the implied warranty
;; of merchantability or fitness for a particular purpose. See the GNU
;; General Public License for more details. See
;; http://www.gnu.org/licenses/ for details.

(require 'racket-util)
(require 'racket-repl)
(require 'ido)
(require 'tq)
(require 'racket-custom) ;for `racket-racket-program'


;;; racket-find-collection

(defun racket-find-collection (&optional prefix)
  "Given a collection name, try to find its directory and files.

Takes a collection name from point (or, with a prefix, prompts you).

If only one directory is found, `ido-find-file-in-dir' lets you
pick a file there.

If more than one directory is found, `ido-completing-read' lets
you pick one, then `ido-find-file-in-dir' lets you pick a file
there.

Note: This requires the `raco-find-collection' package to be
installed. To install it, in `shell' enter:

    raco pkg install raco-find-collection

Tip: This works best with `ido-enable-flex-matching' set to t.
Also handy is the `flx-ido' package from MELPA.

See also: `racket-visit-module' and `racket-open-require-path'."
  (interactive "P")
  (let* ((coll  (racket--symbol-at-point-or-prompt prefix "Collection name: "))
         (paths (racket--repl-cmd/sexpr (format ",find-collection \"%s\"\n" coll))))
    (cond ((eq 'find-collection-not-installed paths)
           ;; FIXME? Offer to run this for them?
           (error "Run `raco pkg install raco-find-collection'"))
          ((not paths)
           (error "Collection not found"))
          ((= 1 (length paths))
           (racket--find-file-in-dir (car paths)))
          (t
           (let ((done nil))
             (while (not done)
               ;; `(ido-find-file-in-dir (ido-completing-read paths))`
               ;; -- except we want to let the user press C-g inside
               ;; ido-find-file-in-dir to back up and pick a different
               ;; module path.
               (let ((dir (ido-completing-read "Directory: " paths)))
                 (condition-case ()
                     (progn (racket--find-file-in-dir dir)
                            (setq done t))
                   (quit nil)))))))))

(defun racket--find-file-in-dir (dir)
  "Like `ido-find-file-in-dir', but allows C-d to `dired' as does `ido-find-file'."
  (ido-file-internal ido-default-file-method nil dir))


;;; racket-open-require-path


;; From looking at ido-mode and ido-vertical-mode:
;;
;; Just use read-from-minibuffer.
;;
;; We're doing vertical mode, so we don't need var like ido-eoinput.
;; We can simply look for the first \n in the minibuffer -- that's the
;; end of user input.
;;
;; Everything after the input and first \n, is the candiates we
;; display, \n separated. The minibuffer automatically grows
;; vertically.
;;
;; Have some maximum number of candidates to display (10?). If > 10, print
;; last line 10 as "...", like ido-vertical-mode.
;;
;; Also use a keymap for commands:
;; - C-n and C-p, which move through the candidates
;; - ENTER
;;   - on a dir will add its contents to the candidates (like DrR's
;;    "Enter Subsellection" button.
;;   - on a file will exit and open the file.
;;
;; Remember that typing a letter triggers `self-insert-command'.
;; Therefore the pre and post command hooks will run then, too.
;;
;; Early version of this used racket--eval/sexpr. Couldn't keep up
;; with typing. Instead: run dedicated Racket process and more direct
;; pipe style; the process does a read-line and responds with each
;; choice on its own line, terminated by a blank like (like HTTP
;; headers).

(defvar racket--orp/tq nil
  "tq queue")
(defvar racket--orp/active nil ;;FIXME: Use minibuffer-exit-hook instead?
  "Is `racket-open-require-path' using the minibuffer?")
(defvar racket--orp/input ""
  "The current user input. Unless user C-g's this persists, as with DrR.")
(defvar racket--orp/matches nil
  "The current user matches. Unless user C-g's this persists, as with DrR.")
(defvar racket--orp/match-index 0
  "The index of the current match selected by the user.")
(defvar racket--orp/max-height 10
  "The maximum height of the minibuffer.")
(defvar racket--orp/keymap
  (racket--easy-keymap-define
   '((("RET" "C-j")    racket--orp/enter)
     ("C-g"            racket--orp/quit)
     (("C-p" "<up>")   racket--orp/prev)
     (("C-n" "<down>") racket--orp/next)
     ;; Some keys should be no-ops.
     (("SPC" "TAB" "C-v" "<next>" "M-v" "<prior>" "M-<" "<home>" "M->" "<end>")
      racket--orp/nop))))

(defvar racket-find-module-path-completions-rkt
  (expand-file-name "find-module-path-completions.rkt"
                    (file-name-directory (or load-file-name (buffer-file-name))))
  "Path to find-module-path-completions.rkt")

(defun racket--orp/begin ()
  (let ((proc (start-process "racket-find-module-path-completions-process"
                             "*racket-find-module-path-completions*"
                             racket-racket-program
                             racket-find-module-path-completions-rkt)))
    (setq racket--orp/tq (tq-create proc))))

(defun racket--orp/request-tx-matches (input)
  "Request matches from the Racket process; delivered to `racket--orp/rx-matches'."
  (when racket--orp/tq
    (tq-enqueue racket--orp/tq
                (concat input "\n")
                ".*\n\n"
                (current-buffer)
                'racket--orp/rx-matches)))

(defun racket--orp/rx-matches (buffer answer)
  "Completion proc; receives answer to request by `racket--orp/request-tx-matches'."
  (when racket--orp/active
    (setq racket--orp/matches (split-string answer "\n" t))
    (setq racket--orp/match-index 0)
    (with-current-buffer buffer
      (racket--orp/draw-matches))))

(defun racket--orp/end ()
  (when racket--orp/tq
    (tq-close racket--orp/tq)
    (setq racket--orp/tq nil)))

(defun racket-open-require-path ()
  "Like Dr Racket's Open Require Path.

Type (or delete) characters that are part of a module path name.
\"Fuzzy\" matches appear. For example try typing \"t/t/r\".

Choices are displayed in a vertical list. The current choice is
at the top, marked with \"->\".

- C-n and C-p move among the choices.
- RET on a directory adds its contents to the choices.
- RET on a file exits doing `find-file'.
- C-g aborts.

Note: This requires Racket 6.1.1.6 or newer. Otherwise it won't
error, it will just never return any matches."
  (interactive)
  (racket--orp/begin)
  (setq racket--orp/active t)
  (setq racket--orp/match-index 0)
  ;; We do NOT initialize `racket--orp/input' or `racket--orp/matches'
  ;; here. Like DrR, we remember from last time invoked. We DO
  ;; initialize them in racket--orp/quit i.e. user presses C-g.
  (add-hook 'minibuffer-setup-hook 'racket--orp/minibuffer-setup)
  (condition-case ()
      (progn
        (read-from-minibuffer "Open require path: "
                              racket--orp/input
                              racket--orp/keymap)
        (when racket--orp/matches
          (find-file (elt racket--orp/matches racket--orp/match-index))))
    (error (setq racket--orp/input "")
           (setq racket--orp/matches nil)))
  (setq racket--orp/active nil)
  (racket--orp/end))

(defun racket--orp/minibuffer-setup ()
  (add-hook 'pre-command-hook  'racket--orp/pre-command  nil t)
  (add-hook 'post-command-hook 'racket--orp/post-command nil t)
  (when racket--orp/active
    (racket--orp/draw-matches)))

(defun racket--orp/eoinput ()
  "Return position where user input ends, i.e. the first \n before the
candidates or (point-max)."
  (save-excursion
    (goto-char (point-min))
    (condition-case ()
        (1- (re-search-forward "\n"))
      (error (point-max)))))

(defun racket--orp/get-user-input ()
  "Get the user's input from the mini-buffer."
  (buffer-substring-no-properties (minibuffer-prompt-end)
                                  (racket--orp/eoinput)))

(defun racket--orp/pre-command ()
  nil)

(defun racket--orp/post-command ()
  "Update matches if input changed.
Also constrain point in case user tried to navigate past
`racket--orp/eoinput'."
  (when racket--orp/active
    (let ((input (racket--orp/get-user-input)))
      (when (not (string-equal input racket--orp/input))
        (racket--orp/on-input-changed input)))
    (let ((eoi (racket--orp/eoinput)))
      (when (> (point) eoi)
        (goto-char eoi)))))

(defun racket--orp/on-input-changed (input)
  (setq racket--orp/input input)
  (cond ((string-equal input "") ;"" => huge list; ignore like DrR
         (setq racket--orp/match-index 0)
         (setq racket--orp/matches nil)
         (racket--orp/draw-matches))
        (t (racket--orp/request-tx-matches input))))

(defun racket--orp/draw-matches ()
  (save-excursion
    (let* ((inhibit-read-only t)
           (eoi (racket--orp/eoinput))
           (len (length racket--orp/matches))
           (n   (min racket--orp/max-height len))
           (i   racket--orp/match-index))
      (delete-region eoi (point-max)) ;delete existing
      (while (> n 0)
        (insert "\n")
        (cond ((= i racket--orp/match-index) (insert "-> "))
              (t                             (insert "   ")))
        (insert (elt racket--orp/matches i))
        (setq n (1- n))
        (cond ((< (1+ i) len) (setq i (1+ i)))
              (t              (setq i 0))))
      (when (< racket--orp/max-height len)
        (insert "\n   ..."))
      (put-text-property eoi (point-max) 'read-only 'fence))))

(defun racket--orp/enter ()
  "On a dir, adds its contents to choices. On a file, opens the file."
  (interactive)
  (when racket--orp/active
    (let ((match (and racket--orp/matches
                      (elt racket--orp/matches racket--orp/match-index))))
      (cond (;; Pressing RET on a directory inserts its contents, like
             ;; "Enter subcollection" button in DrR.
             (and match (file-directory-p match))
             (racket--trace "enter" 'add-subdir)
             (setq racket--orp/matches
                   (delete-dups ;if they RET same item more than once
                    (sort (append racket--orp/matches
                                  (directory-files match t "[^.]+$"))
                          #'string-lessp)))
             (racket--orp/draw-matches))
            (;; Pressing ENTER on a file selects it. We exit the
             ;; minibuffer; our main function treats non-nil
             ;; racket--orp/matches and racket--orp/match-index as a
             ;; choice (as opposed to quitting w/o a choice.
             t
             (racket--trace "enter" 'exit-minibuffer)
             (exit-minibuffer))))))

(defun racket--orp/quit ()
  "Our replacement for `keyboard-quit'."
  (interactive)
  (when racket--orp/active
    (racket--trace "quit")
    (setq racket--orp/input "")
    (setq racket--orp/matches nil)
    (exit-minibuffer)))

(defun racket--orp/next ()
  "Select the next match."
  (interactive)
  (when racket--orp/active
    (setq racket--orp/match-index (1+ racket--orp/match-index))
    (when (>= racket--orp/match-index (length racket--orp/matches))
      (setq racket--orp/match-index 0))
    (racket--orp/draw-matches)))

(defun racket--orp/prev ()
  "Select the previous match."
  (interactive)
  (when racket--orp/active
    (setq racket--orp/match-index (1- racket--orp/match-index))
    (when (< racket--orp/match-index 0)
      (setq racket--orp/match-index (max 0 (1- (length racket--orp/matches)))))
    (racket--orp/draw-matches)))

(defun racket--orp/nop ()
  "A do-nothing command target."
  (interactive)
  nil)

(provide 'racket-collection)

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:

;; racket-collection.el ends here
