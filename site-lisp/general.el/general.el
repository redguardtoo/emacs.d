;;; general.el --- Convenience wrappers for keybindings.

;; Author: Fox Kiester <noct@openmailbox.org>
;; URL: https://github.com/noctuid/general.el
;; Created: February 17, 2016
;; Keywords: vim, evil, leader, keybindings, keys
;; Package-Requires: ((cl-lib "0.5"))
;; Version: 0.1

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
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
;; This package provides convenient wrappers for more succinctly defining
;; keybindings. It allows defining multiple keys at once, specifying an
;; arbitrary number of named prefix keys to be used in key definitions,
;; implicitly wrapping key strings with (kbd ...), and more. It provides a
;; single function for standard emacs key definitions as well as evil key
;; definitions for any evil state and any keymap. It also provides a setup
;; function to generate "nmap", "vmap", etc. keybinding functions for evil.

;; For more information see the README in the online repository.

;;; Code:
(require 'cl-lib)

(defgroup general nil
  "Gives convenient wrappers for key definitions."
  :group 'convenience
  :prefix 'general)

(defcustom general-implicit-kbd t
  "Whether to implicitly wrap a (kbd) around keybindings.
This applies to the prefix key as well."
  :group 'general
  :type 'boolean)

(defcustom general-default-prefix nil
  "The default prefix key sequence to use."
  :group 'general
  :type 'string)

(defcustom general-default-non-normal-prefix nil
  "The default prefix key sequence to use for the 'emacs and 'insert states.
Note that this setting is only useful for evil-users and will only have an
effect when binding keys in the 'emacs and/or 'insert states or in the
'evil-insert-state-map and/or 'evil-emacs-state-map keymaps. When this is not
specified, `general-default-prefix' will be the default prefix for any states
and keymaps. If this is specified `general-default-prefix' or the arg to :prefix
will not be used when binding keys in the insert and emacs states."
  :group 'general
  :type 'string)

(defcustom general-default-global-prefix nil
  "The default prefix key sequence to use for all evil states.
This setting is only useful for evil users. Note that like with
`general-default-non-normal-prefix', if this or :global-prefix is specified,
`general-default-prefix' or the arg to :prefix will not be used for binding
keys in the insert and emacs states. If you don't need a different or extra
prefix for one or both state types (insert and emacs vs. the other states),
just use `general-default-prefix'/:prefix by itself."
  :group 'general
  :type 'string)

(defcustom general-default-states nil
  "The default evil state to make mappings in.
Non-evil users should keep this nil."
  :group 'general
  :type '(repeat :tag "States"
                 (choice
                  (const :tag "Normal state" normal)
                  (const :tag "Insert state" insert)
                  (const :tag "Visual state" visual)
                  (const :tag "Replace state" replace)
                  (const :tag "Operator state" operator)
                  (const :tag "Motion state" motion)
                  (const :tag "Emacs state" emacs)
                  (const :tag "Use define-key not evil-define-key" nil))))

(defcustom general-default-keymaps 'global
  "The default keymap to bind keys in."
  :group 'general)

;;; Helpers
(defun general--apply-prefix-and-kbd (prefix maps)
  "Prepend the PREFIX sequence to all MAPS.
Adds a (kbd ...) if `general-implicit-kbd' is non-nil."
  (let ((prefix (or prefix "")))
    (mapcar (lambda (elem)
              (if (stringp elem)
                  (if general-implicit-kbd
                      (kbd (concat prefix " " elem))
                    (concat prefix elem))
                elem))
            maps)))

;; http://endlessparentheses.com/define-context-aware-keys-in-emacs.html
(defun general--apply-predicate (predicate maps)
  "Apply PREDICATE to the commands in MAPS."
  (mapcar (lambda (maybe-command)
            (if (not (stringp maybe-command))
                `(menu-item "" nil
                            :filter (lambda (&optional _)
                                      (when ,predicate
                                        (,maybe-command))))
              maybe-command))
          maps))

;; don't force non-evil user to require evil for one function (this is evil-delay)
(defun general--delay (condition form hook &optional append local name)
  "Execute FORM when CONDITION becomes true, checking with HOOK.
NAME specifies the name of the entry added to HOOK. If APPEND is
non-nil, the entry is appended to the hook. If LOCAL is non-nil,
the buffer-local value of HOOK is modified."
  (declare (indent 2))
  (if (and (not (booleanp condition)) (eval condition))
      (eval form)
    (let* ((name (or name (format "general-delay-form-in-%s" hook)))
           (fun (make-symbol name))
           (condition (or condition t)))
      (fset fun `(lambda (&rest args)
                   (when ,condition
                     (remove-hook ',hook #',fun ',local)
                     ,form)))
      (put fun 'permanent-local-hook t)
      (add-hook hook fun append local))))

;;; define-key and evil-define-key Wrappers
;; TODO better way to do this?
;; https://www.reddit.com/r/emacs/comments/1582uo/bufferlocalsetkey_set_a_key_in_one_buffer_only/
(defvar general--blm nil)

(defun general--generate-keymap-name (sym)
  "Generate a map name from SYM."
  (symbol-value (intern (concat (symbol-name sym) "-map"))))

(defun general--emacs-local-set-key (key func)
  "Bind KEY to FUNC for the current buffer only using a minor mode."
  (if general--blm
      (define-key (general--generate-keymap-name general--blm) key func)
    (let* ((mode-name-loc (cl-gensym "general-blm")))
      (eval `(define-minor-mode ,mode-name-loc nil nil nil (make-sparse-keymap)))
      (setq-local general--blm mode-name-loc)
      (funcall mode-name-loc 1)
      (define-key (general--generate-keymap-name general--blm) key func))))

;; this works but will make it so that keys defined for the major mode will no longer affect
;; (use-local-map (copy-keymap (current-local-map)))
;; (local-set-key (kbd "C-c y") 'helm-apropos)

(defun general--emacs-define-key (keymap &rest maps)
  "Wrapper for `define-key' and general's `general--emacs-local-set-key'.
KEYMAP determines which keymap the MAPS will be defined in. When KEYMAP is
is 'local, the MAPS will be bound only in the current buffer. MAPS is any
number of paired keys and commands"
  (declare (indent 1))
  (let (key func)
    (while (setq key (pop maps)
                 func (pop maps))
      (if (eq keymap 'local)
          (general--emacs-local-set-key key func)
        (define-key keymap key func)))))

;; can't apply evil-define-key since it is a macro
;; either need to use eval or splice (,@) with defmacro
;; or not make use of evil-define-key's &rest and repeatedly call it

;; (defmacro general-evil-define-key (prefix-key state keymap &rest maps)
;;   ;; needs special indent
;;   "A wrapper."
;;   (declare (indent 3))
;;   (setq prefix-key (or prefix-key ""))
;;   (setq maps (--map-when (stringp it ) (concat prefix-key it) maps))
;;   `(eval-after-load 'evil
;;      (evil-define-key ,state ,keymap ,@maps)))

(defun general--evil-define-key (state keymap &rest maps)
  "A wrapper for `evil-define-key' and `evil-local-set-key'.
STATE is the evil state to bind the keys in. `evil-local-set-key' is used when
KEYMAP is 'local. MAPS is any number of keys and commands to bind."
  (declare (indent defun))
  (eval-after-load 'evil
    `(let ((maps ',maps)
           (keymap ',keymap)
           (state ',state)
           key
           func)
       (while (setq key (pop maps)
                    func (pop maps))
         (if (eq keymap 'local)
             ;; has no &rest
             (evil-local-set-key state key func)
           (evil-define-key state keymap key func))))))

;;; Functions With Keyword Arguments
;;;###autoload
(cl-defun general-define-key
    (&rest maps &key (prefix general-default-prefix)
           (non-normal-prefix general-default-non-normal-prefix)
           (global-prefix general-default-global-prefix)
           (states general-default-states)
           (keymaps general-default-keymaps)
           (predicate)
           &allow-other-keys)
  "The primary key definition function provided by general.

PREFIX corresponds to a prefix key and defaults to none. STATES corresponds to
the evil state(s) to bind the keys in. Non-evil users should not set STATES.
When STATES is non-nil, `evil-define-key' will be used. Otherwise `define-key'
will be used. Evil users may also want to leave STATES nil and set KEYMAPS to
a keymap such as `evil-normal-state-map' for global mappings. KEYMAPS defaults
to `global-map'. Note that STATES and KEYMAPS can either be a list or a single
symbol. If any keymap does not exist, the keybindings will be deferred until
the keymap does exist, so using `eval-after-load' is not necessary with this
function.

If NON-NORMAL-PREFIX is specified, this prefix will be used for emacs and insert
state keybindings instead of PREFIX. This argument will only have an effect if
'insert and/or 'emacs is one of the STATES or if 'evil-insert-state-map and/or
'evil-emacs-state-map is one of the KEYMAPS. Alternatively, GLOBAL-PREFIX can be
used with PREFIX and/or NON-NORMAL-PREFIX to bind keys in all states under a
specified prefix. Like with NON-NORMAL-PREFIX, GLOBAL-PREFIX will prevent PREFIX
from applying to insert and emacs states. Note that these keywords are only
useful for evil users.

Unlike with normal key definitions functions, the keymaps in KEYMAPS should be
quoted (this makes it easy to check if there is only one keymap instead of a
list of keymaps)."
  (let (non-normal-prefix-maps
        global-prefix-maps)
    ;; remove keyword arguments from rest var
    (setq maps
          (cl-loop for (key value) on maps by 'cddr
                   when (not (member key (list :prefix :states :keymaps :predicate
                                               :non-normal-prefix :global-prefix)))
                   collect key
                   and collect value))
    ;; don't force the user to wrap a single state or keymap in a list
    ;; luckily nil is a list
    (unless (listp states)
      (setq states (list states)))
    (unless (listp keymaps)
      (setq keymaps (list keymaps)))
    (when predicate
      (setq maps (general--apply-predicate predicate maps)))
    (when non-normal-prefix
      (setq non-normal-prefix-maps
            (general--apply-prefix-and-kbd non-normal-prefix maps)))
    (when global-prefix
      (setq global-prefix-maps
            (general--apply-prefix-and-kbd global-prefix maps)))
    ;; last so not applying prefix twice
    (setq maps (general--apply-prefix-and-kbd prefix maps))
    (dolist (keymap keymaps)
      (general--delay `(or (eq ',keymap 'local)
                           (eq ',keymap 'global)
                           (and (boundp ',keymap)
                                (keymapp ,keymap)))
          `(let ((keymap (cond ((eq ',keymap 'local)
                                ;; keep keymap quoted if it was 'local
                                'local)
                               ((eq ',keymap 'global)
                                (current-global-map))
                               (t
                                ,keymap))))
             (if ',states
                 (dolist (state ',states)
                   (cond ((and (or ',non-normal-prefix-maps
                                   ',global-prefix-maps)
                               (member state '(insert emacs)))
                          (when ',non-normal-prefix-maps
                            (apply #'general--evil-define-key state keymap
                                   ',non-normal-prefix-maps)))
                         (t
                          (apply #'general--evil-define-key state keymap
                                 ',maps)))
                   (when ',global-prefix-maps
                     (apply #'general--evil-define-key state keymap
                            ',global-prefix-maps)))
               (cond ((and (or ',non-normal-prefix-maps
                               ',global-prefix-maps)
                           (member 'keymap (list 'evil-insert-state-map
                                                 'evil-emacs-state-map)))
                      (when ',non-normal-prefix-maps
                        (apply #'general--emacs-define-key keymap
                               ',non-normal-prefix-maps)))
                     (t
                      (apply #'general--emacs-define-key keymap ',maps)))
               (when ',global-prefix-maps
                 (apply #'general--emacs-define-key keymap
                        ',global-prefix-maps))))
        'after-load-functions t nil
        (format "general-define-key-in-%s" keymap)))))

;;;###autoload
(defmacro general-create-definer (name &rest args)
  "A helper macro to create key definitions functions.
This allows the creation of key definition functions that
will use a certain keymap, evil state, and/or prefix key by default.
NAME will be the function name and ARGS are the keyword arguments that
are intended to be the defaults."
  `(defun ,name (&rest args)
     ;; can still override keywords afterwards
     (apply #'general-define-key (append args (list ,@args)))))

;;;###autoload
(defun general-emacs-define-key (keymaps &rest args)
  "A wrapper for `general-define-key' that is similar to `define-key'.
It has a positional argument for KEYMAPS. It acts the same as
`general-define-key', and ARGS can contain keyword arguments in addition to
keybindings."
  (declare (indent 1))
  (apply #'general-define-key (append args (list :keymaps keymaps)) ))

;;;###autoload
(defun general-evil-define-key (states keymaps &rest args)
  "A wrapper for `general-define-key' that is similar to `evil-define-key'.
It has positional arguments for STATES and KEYMAPS. It acts the same as
`general-define-key', and ARGS can contain keyword arguments in addition to
keybindings."
  (declare (indent defun))
  (apply #'general-define-key
         (append args (list :states states :keymaps keymaps))))

;;; Optional Setup
;;;###autoload
(defun general-evil-setup (&optional short-names)
  "Set up some basic equivalents for vim mapping functions.
This creates global key definition functions for the evil states.
Specifying SHORT-NAMES as non-nil will create non-prefixed function
aliases such as `nmap' for `general-nmap'."
  (general-create-definer general-nmap :keymaps 'evil-normal-state-map)
  (general-create-definer general-imap :keymaps 'evil-insert-state-map)
  (general-create-definer general-vmap :keymaps 'evil-visual-state-map)
  (general-create-definer general-rmap :keymaps 'evil-replace-state-map)
  (general-create-definer general-omap :keymaps 'evil-operator-state-map)
  (general-create-definer general-mmap :keymaps 'evil-motion-state-map)
  (general-create-definer general-emap :keymaps 'evil-emacs-state-map)
  (general-create-definer general-otomap :keymaps 'evil-outer-text-objects-map)
  (general-create-definer general-itomap :keymaps 'evil-inner-text-objects-map)
  (general-create-definer general-nvmap :keymaps '(evil-normal-state-map
                                                   evil-visual-state-map))
  (general-create-definer general-iemap :keymaps '(evil-insert-state-map
                                                   evil-emacs-state-map))
  (general-create-definer general-tomap
                          :keymaps '(evil-outer-text-objects-map
                                     evil-inner-text-objects-map))
  (when short-names
    (defalias 'nmap 'general-nmap)
    (defalias 'imap 'general-imap)
    (defalias 'vmap 'general-vmap)
    (defalias 'rmap 'general-rmap)
    (defalias 'omap 'general-omap)
    (defalias 'emap 'general-emap)
    (defalias 'otomap 'general-otomap)
    (defalias 'itomap 'general-itomap)
    (defalias 'nvmap 'general-nvmap)
    (defalias 'iemap 'general-iemap)
    (defalias 'tomap 'general-tomap)))

(provide 'general)
;;; general.el ends here
