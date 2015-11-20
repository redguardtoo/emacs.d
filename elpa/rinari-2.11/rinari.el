;;; rinari.el --- Rinari Is Not A Rails IDE

;; Copyright (C) 2008 Phil Hagelberg, Eric Schulte

;; Author: Phil Hagelberg, Eric Schulte
;; URL: https://github.com/eschulte/rinari
;; Package-Version: 2.11
;; Version: DEV
;; Created: 2006-11-10
;; Keywords: ruby, rails, project, convenience, web
;; EmacsWiki: Rinari
;; Package-Requires: ((ruby-mode "1.0") (inf-ruby "2.2.5") (ruby-compilation "0.16") (jump "2.0"))

;; This file is NOT part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Rinari Is Not A Ruby IDE.

;; Well, ok it kind of is.  Rinari is a set of Emacs Lisp modes that is
;; aimed towards making Emacs into a top-notch Ruby and Rails
;; development environment.

;; Rinari can be installed through ELPA (see http://tromey.com/elpa/)

;; To install from source, copy the directory containing this file
;; into your Emacs Lisp directory, assumed here to be ~/.emacs.d.  Add
;; these lines of code to your .emacs file:

;; ;; rinari
;; (add-to-list 'load-path "~/.emacs.d/rinari")
;; (require 'rinari)
;; (global-rinari-mode)

;; Whether installed through ELPA or from source you probably want to
;; add the following lines to your .emacs file:

;; ;; ido
;; (require 'ido)
;; (ido-mode t)

;; Note: if you cloned this from a git repo, you will have to grab the
;; submodules which can be done by running the following commands from
;; the root of the rinari directory

;;  git submodule init
;;  git submodule update

;;; Code:
;;;###begin-elpa-ignore
(let* ((this-dir (file-name-directory (or load-file-name buffer-file-name)))
       (util-dir (file-name-as-directory (expand-file-name "util" this-dir)))
       (inf-ruby-dir (file-name-as-directory (expand-file-name "inf-ruby" util-dir)))
       (jump-dir (file-name-as-directory (expand-file-name "jump" util-dir))))
  (dolist (dir (list util-dir inf-ruby-dir jump-dir))
    (when (file-exists-p dir)
      (add-to-list 'load-path dir))))
;;;###end-elpa-ignore
(require 'ruby-mode)
(require 'inf-ruby)
(require 'ruby-compilation)
(require 'jump)
(require 'cl)
(require 'easymenu)

;; fill in some missing variables for XEmacs
(when (eval-when-compile (featurep 'xemacs))
  ;;this variable does not exist in XEmacs
  (defvar safe-local-variable-values ())
  ;;find-file-hook is not defined and will otherwise not be called by XEmacs
  (define-compatible-variable-alias 'find-file-hook 'find-file-hooks))

(defgroup rinari nil
  "Rinari customizations."
  :prefix "rinari-"
  :group 'rinari)

(defcustom rinari-major-modes nil
  "Major Modes from which to launch Rinari."
  :type '(repeat symbol)
  :group 'rinari)

(defcustom rinari-exclude-major-modes nil
  "Major Modes in which to never launch Rinari."
  :type '(repeat symbol)
  :group 'rinari)

(defcustom rinari-tags-file-name
  "TAGS"
  "Path to your TAGS file inside of your rails project.  See `tags-file-name'."
  :group 'rinari)

(defcustom rinari-fontify-rails-keywords t
  "When non-nil, fontify keywords such as 'before_filter', 'url_for'.")

(defcustom rinari-controller-keywords
  '("logger" "polymorphic_path" "polymorphic_url" "mail" "render" "attachments"
    "default" "helper" "helper_attr" "helper_method" "layout" "url_for"
    "serialize" "exempt_from_layout" "filter_parameter_logging" "hide_action"
    "cache_sweeper" "protect_from_forgery" "caches_page" "cache_page"
    "caches_action" "expire_page" "expire_action" "rescue_from" "params"
    "request" "response" "session" "flash" "head" "redirect_to"
    "render_to_string" "respond_with" "before_filter" "append_before_filter"
    "prepend_before_filter" "after_filter" "append_after_filter"
    "prepend_after_filter" "around_filter" "append_around_filter"
    "prepend_around_filter" "skip_before_filter" "skip_after_filter" "skip_filter")
  "List of keywords to highlight for controllers"
  :group 'rinari
  :type '(repeat string))

(defcustom rinari-migration-keywords
  '("create_table" "change_table" "drop_table" "rename_table" "add_column"
    "rename_column" "change_column" "change_column_default" "remove_column"
    "add_index" "remove_index" "rename_index" "execute")
  "List of keywords to highlight for migrations"
  :group 'rinari
  :type '(repeat string))

(defcustom rinari-model-keywords
  '("default_scope" "named_scope" "scope" "serialize" "belongs_to" "has_one"
    "has_many" "has_and_belongs_to_many" "composed_of" "accepts_nested_attributes_for"
    "before_create" "before_destroy" "before_save" "before_update" "before_validation"
    "before_validation_on_create" "before_validation_on_update" "after_create"
    "after_destroy" "after_save" "after_update" "after_validation"
    "after_validation_on_create" "after_validation_on_update" "around_create"
    "around_destroy" "around_save" "around_update" "after_commit" "after_find"
    "after_initialize" "after_rollback" "after_touch" "attr_accessible"
    "attr_protected" "attr_readonly" "validates" "validate" "validate_on_create"
    "validate_on_update" "validates_acceptance_of" "validates_associated"
    "validates_confirmation_of" "validates_each" "validates_exclusion_of"
    "validates_format_of" "validates_inclusion_of" "validates_length_of"
    "validates_numericality_of" "validates_presence_of" "validates_size_of"
    "validates_uniqueness_of" "validates_with")
  "List of keywords to highlight for models"
  :group 'rinari
  :type '(repeat string))

(defvar rinari-minor-mode-hook nil
  "*Hook for customising Rinari.")

(defcustom rinari-rails-env nil
  "Use this to force a value for RAILS_ENV when running rinari.
Leave this set to nil to not force any value for RAILS_ENV, and
leave this to the environment variables outside of Emacs.")

(defvar rinari-minor-mode-prefixes
  (list ";" "'")
  "List of characters, each of which will be bound (with control-c) as a prefix for `rinari-minor-mode-map'.")

(defvar rinari-partial-regex
  "render \\(:partial *=> \\)?*[@'\"]?\\([A-Za-z/_]+\\)['\"]?"
  "Regex that matches a partial rendering call.")

(defadvice ruby-compilation-do (around rinari-compilation-do activate)
  "Set default directory to the rails root before running ruby processes."
  (let ((default-directory (or (rinari-root) default-directory)))
    ad-do-it
    (rinari-launch)))

(defadvice ruby-compilation-rake (around rinari-compilation-rake activate)
  "Set default directory to the rails root before running rake processes."
  (let ((default-directory (or (rinari-root) default-directory)))
    ad-do-it
    (rinari-launch)))

(defadvice ruby-compilation-cap (around rinari-compilation-cap activate)
  "Set default directory to the rails root before running cap processes."
  (let ((default-directory (or (rinari-root) default-directory)))
    ad-do-it
    (rinari-launch)))

(defun rinari-parse-yaml ()
  "Parse key/value pairs out of a simple yaml file."
  (let ((end (save-excursion (re-search-forward "^[^:]*$" nil t) (point)))
        pairs)
    (while (re-search-forward "^ *\\(.*\\): \\(.*\\)$" end t)
      (push (cons (match-string 1) (match-string 2)) pairs))
    pairs))

(defun rinari-root (&optional dir home)
  "Return the root directory of the project within which DIR is found.
Optional argument HOME is ignored."
  (let ((default-directory (or dir default-directory)))
    (when (file-directory-p default-directory)
      (if (file-exists-p (expand-file-name "environment.rb" (expand-file-name "config")))
          default-directory
        ;; regexp to match windows roots, tramp roots, or regular posix roots
        (unless (string-match "\\(^[[:alpha:]]:/$\\|^/[^\/]+:/?$\\|^/$\\)" default-directory)
          (rinari-root (expand-file-name (file-name-as-directory ".."))))))))

(defun rinari-highlight-keywords (keywords)
  "Highlight the passed KEYWORDS in current buffer.
Use `font-lock-add-keywords' in case of `ruby-mode' or
`ruby-extra-keywords' in case of Enhanced Ruby Mode."
  (if (boundp 'ruby-extra-keywords)
      (progn
        (setq ruby-extra-keywords (append ruby-extra-keywords keywords))
        (ruby-local-enable-extra-keywords))
    (font-lock-add-keywords
     nil
     (list (list
            (concat "\\(^\\|[^_:.@$]\\|\\.\\.\\)\\b"
                    (regexp-opt keywords t)
                    (eval-when-compile (if (string-match "\\_>" "ruby")
                                           "\\_>"
                                         "\\>")))
            (list 2 'font-lock-builtin-face))))))

(defun rinari-apply-keywords-for-file-type ()
  "Apply extra font lock keywords specific to models, controllers etc."
  (when (and rinari-fontify-rails-keywords (buffer-file-name))
    (loop for (re keywords) in `(("_controller\\.rb$"   ,rinari-controller-keywords)
                                 ("app/models/.+\\.rb$" ,rinari-model-keywords)
                                 ("db/migrate/.+\\.rb$" ,rinari-migration-keywords))
          do (when (string-match-p re (buffer-file-name))
               (rinari-highlight-keywords keywords)))))


(add-hook 'ruby-mode-hook 'rinari-apply-keywords-for-file-type)

;;--------------------------------------------------------------------------------
;; user functions

(defun rinari-rake (&optional task edit-cmd-args)
  "Select and run a rake TASK using `ruby-compilation-rake'."
  (interactive "P")
  (ruby-compilation-rake task edit-cmd-args
                         (when rinari-rails-env
                           (list (cons "RAILS_ENV" rinari-rails-env)))))

(defun rinari-rake-migrate-down (path &optional edit-cmd-args)
  "Perform a down migration for the migration with PATH."
  (interactive "fMigration: ")
  (let* ((file (file-name-nondirectory path))
         (n (if (string-match "^\\([0-9]+\\)_[^/]+$" file)
                (match-string 1 file)
              (error "Couldn't determine migration number"))))
    (ruby-compilation-rake "db:migrate:down"
                           edit-cmd-args
                           (list (cons "VERSION" n)))))

(defun rinari-cap (&optional task edit-cmd-args)
  "Select and run a capistrano TASK using `ruby-compilation-cap'."
  (interactive "P")
  (ruby-compilation-cap task edit-cmd-args
                        (when rinari-rails-env
                          (list (cons "RAILS_ENV" rinari-rails-env)))))

(defun rinari--discover-rails-commands ()
  "Return a list of commands supported by the main rails script."
  (let ((rails-script (rinari--rails-path)))
    (when rails-script
      (ruby-compilation-extract-output-matches rails-script "^ \\([a-z]+\\)[[:space:]].*$"))))

(defvar rinari-rails-commands-cache nil
  "Cached values for commands that can be used with 'script/rails' in Rails 3.")

(defun rinari-get-rails-commands ()
  "Return a cached list of commands supported by the main rails script."
  (when (null rinari-rails-commands-cache)
    (setq rinari-rails-commands-cache (rinari--discover-rails-commands)))
  rinari-rails-commands-cache)

(defun rinari-script (&optional script)
  "Select and run SCRIPT from the script/ directory of the rails application."
  (interactive)
  (let* ((completions (append (directory-files (rinari-script-path) nil "^[^.]")
                              (rinari-get-rails-commands)))
         (script (or script (jump-completing-read "Script: " completions)))
         (ruby-compilation-error-regexp-alist ;; for jumping to newly created files
          (if (equal script "generate")
              '(("^ +\\(create\\) +\\([^[:space:]]+\\)" 2 3 nil 0 2)
                ("^ +\\(exists\\) +\\([^[:space:]]+\\)" 2 3 nil 0 1)
                ("^ +\\(conflict\\) +\\([^[:space:]]+\\)" 2 3 nil 0 0))
            ruby-compilation-error-regexp-alist))
         (script-path (concat (rinari--wrap-rails-command script) " ")))
    (when (string-match-p "^\\(db\\)?console" script)
      (error "Use the dedicated rinari function to run this interactive script"))
    (ruby-compilation-run (concat script-path " " (read-from-minibuffer (concat script " ")))
                          nil
                          (concat "rails " script))))

(defun rinari-test (&optional edit-cmd-args)
  "Run the current ruby function as a test, or run the corresponding test.
If current function is not a test,`rinari-find-test' is used to
find the corresponding test.  Output is sent to a compilation buffer
allowing jumping between errors and source code.  Optional prefix
argument EDIT-CMD-ARGS lets the user edit the test command
arguments."
  (interactive "P")
  (or (rinari-test-function-name)
      (string-match "test" (or (ruby-add-log-current-method)
                               (file-name-nondirectory (buffer-file-name))))
      (rinari-find-test))
  (let* ((fn (rinari-test-function-name))
         (path (buffer-file-name))
         (ruby-options (list "-I" (expand-file-name "test" (rinari-root)) path))
         (default-command (mapconcat
                           'identity
                           (append (list path) (when fn (list "--name" (concat "/" fn "/"))))
                           " "))
         (command (if edit-cmd-args
                      (read-string "Run w/Compilation: " default-command)
                    default-command)))
    (if path
        (ruby-compilation-run command ruby-options)
      (message "no test available"))))

(defun rinari-test-function-name()
  "Return the name of the test function at point, or nil if not found."
  (save-excursion
    (when (re-search-backward (concat "^[ \t]*\\(def\\|test\\)[ \t]+"
                                      "\\([\"'].*?[\"']\\|" ruby-symbol-re "*\\)"
                                      "[ \t]*") nil t)
      (let ((name (match-string 2)))
        (if (string-match "^[\"']\\(.*\\)[\"']$" name)
            (replace-regexp-in-string
             "\\?" "\\\\\\\\?"
             (replace-regexp-in-string " +" "_" (match-string 1 name)))
          (when (string-match "^test" name)
            name))))))

(defun rinari--rails-path ()
  "Return the path of the 'rails' command, or nil if not found."
  (let* ((script-rails (expand-file-name "rails" (rinari-script-path)))
         (bin-rails (expand-file-name "rails" (rinari-bin-path))))
    (cond
     ((file-exists-p bin-rails) bin-rails)
     ((file-exists-p script-rails) script-rails)
     (t (executable-find "rails")))))

(defun rinari--wrap-rails-command (command)
  "Given a COMMAND such as 'console', return a suitable command line.
Where the corresponding script is executable, it will be run
as-is.  Otherwise, as can be the case on Windows, the command will
be prepended with `ruby-compilation-executable'."
  (let* ((default-directory (rinari-root))
         (script (rinari-script-path))
         (script-command (expand-file-name command script))
         (command-line
          (if (file-exists-p script-command)
              script-command
            (concat (rinari--rails-path) " " command))))
    (if (file-executable-p (first (split-string-and-unquote command-line)))
        command-line
      (concat ruby-compilation-executable " " command-line))))

(defun rinari-console (&optional edit-cmd-args)
  "Run a Rails console in a compilation buffer.
The buffer will support command history and links between errors
and source code.  Optional prefix argument EDIT-CMD-ARGS lets the
user edit the console command arguments."
  (interactive "P")
  (let* ((default-directory (rinari-root))
         (command (rinari--wrap-rails-command "console")))

    ;; Start console in correct environment.
    (when rinari-rails-env
      (setq command (concat command " " rinari-rails-env)))

    ;; For customization of the console command with prefix arg.
    (setq command (if edit-cmd-args
                      (read-string "Run Ruby: " (concat command " "))
                    command))
    (with-current-buffer (run-ruby command "rails console")
      (rinari-launch))))

(defun rinari-sql ()
  "Browse the application's database.
Looks up login information from your conf/database.sql file."
  (interactive)
  (let* ((environment (or rinari-rails-env (getenv "RAILS_ENV") "development"))
         (existing-buffer (get-buffer (concat "*SQL: " environment "*"))))
    (if existing-buffer
        (pop-to-buffer existing-buffer)
      (let* ((database-alist (save-excursion
                               (with-temp-buffer
                                 (insert-file-contents
                                  (expand-file-name
                                   "database.yml"
                                   (file-name-as-directory
                                    (expand-file-name "config" (rinari-root)))))
                                 (goto-char (point-min))
                                 (re-search-forward (concat "^" environment ":"))
                                 (rinari-parse-yaml))))
             (adapter (or (cdr (assoc "adapter" database-alist)) "sqlite"))
             (server (or (cdr (assoc "host" database-alist)) "localhost"))
             (port (cdr (assoc "port" database-alist))))
        (with-temp-buffer
          (set (make-local-variable 'sql-user) (or (cdr (assoc "username" database-alist)) "root"))
          (set (make-local-variable 'sql-password) (or (cdr (assoc "password" database-alist)) ""))
          (set (make-local-variable 'sql-password) (when (> (length sql-password) 0) sql-password))
          (set (make-local-variable 'sql-database) (or (cdr (assoc "database" database-alist))
                                                       (concat (file-name-nondirectory (rinari-root))
                                                               "_" environment)))
          (set (make-local-variable 'sql-server) (if port (concat server ":" port) server))
          (funcall
           (intern (concat "sql-"
                           (cond
                            ((string-match "mysql" adapter)
                             "mysql")
                            ((string-match "sqlite" adapter)
                             "sqlite")
                            ((string-match "postgresql" adapter)
                             "postgres")
                            (t adapter))))
           environment))))
    (rinari-launch)))

(defun rinari-web-server (&optional edit-cmd-args)
  "Start a Rails webserver.
Dumps output to a compilation buffer allowing jumping between
errors and source code.  Optional prefix argument EDIT-CMD-ARGS
lets the user edit the server command arguments."
  (interactive "P")
  (let* ((default-directory (rinari-root))
         (command (rinari--wrap-rails-command "server")))

    ;; Start web server in correct environment.
    (when rinari-rails-env
      (setq command (concat command " -e " rinari-rails-env)))

    ;; For customization of the web server command with prefix arg.
    (setq command (if edit-cmd-args
                      (read-string "Run Ruby: " (concat command " "))
                    command))

    (ruby-compilation-run command nil "server"))
  (rinari-launch))

(defun rinari-web-server-restart (&optional edit-cmd-args)
  "Ensure a fresh `rinari-web-server' is running, first killing any old one.
Optional prefix argument EDIT-CMD-ARGS lets the user edit the
server command arguments."
  (interactive "P")
  (let ((rinari-web-server-buffer "*server*"))
    (when (get-buffer rinari-web-server-buffer)
      (set-process-query-on-exit-flag (get-buffer-process rinari-web-server-buffer) nil)
      (kill-buffer rinari-web-server-buffer))
    (rinari-web-server edit-cmd-args)))

(defun rinari-insert-erb-skeleton (no-equals)
  "Insert an erb skeleton at point.
With optional prefix argument NO-EQUALS, don't include an '='."
  (interactive "P")
  (insert "<%")
  (insert (if no-equals "  -" "=  "))
  (insert "%>")
  (backward-char (if no-equals 4 3)))

(defun rinari-extract-partial (begin end partial-name)
  "Extracts the region from BEGIN to END into a partial called PARTIAL-NAME."
  (interactive "r\nsName your partial: ")
  (let ((path (buffer-file-name))
        (ending (rinari-ending)))
    (if (string-match "view" path)
        (let ((partial-name
               (replace-regexp-in-string "[[:space:]]+" "_" partial-name)))
          (kill-region begin end)
          (if (string-match "\\(.+\\)/\\(.+\\)" partial-name)
              (let ((default-directory (expand-file-name (match-string 1 partial-name)
                                                         (expand-file-name ".."))))
                (find-file (concat "_" (match-string 2 partial-name) ending)))
            (find-file (concat "_" partial-name ending)))
          (yank) (pop-to-buffer nil)
          (rinari-insert-partial partial-name ending))
      (message "not in a view"))))

(defun rinari-insert-output (ruby-expr ending)
  "Insert view code which outputs RUBY-EXPR, suitable for the file's ENDING."
  (let ((surround
         (cond
          ((string-match "\\.erb" ending)
           (cons "<%= " " %>"))
          ((string-match "\\.haml" ending)
           (cons "= " " ")))))
    (insert (concat (car surround) ruby-expr (cdr surround) "\n"))))

(defun rinari-insert-partial (partial-name ending)
  "Insert a call to PARTIAL-NAME, formatted for the file's ENDING.

Supported markup languages are: Erb, Haml"
  (rinari-insert-output (concat "render :partial => \"" partial-name "\"") ending))

(defun rinari-goto-partial ()
  "Visits the partial that is called on the current line."
  (interactive)
  (let ((line (buffer-substring-no-properties (line-beginning-position) (line-end-position))))
    (when (string-match rinari-partial-regex line)
      (setq line (match-string 2 line))
      (let ((file
             (if (string-match "/" line)
                 (concat (rinari-root) "app/views/"
                         (replace-regexp-in-string "\\([^/]+\\)/\\([^/]+\\)$" "\\1/_\\2" line))
               (concat default-directory "_" line))))
        (find-file (concat file (rinari-ending)))))))

(defvar rinari-rgrep-file-endings
  "*.[^l]*"
  "Ending of files to search for matches using `rinari-rgrep'.")

(defun rinari-rgrep (&optional arg)
  "Search through the rails project for a string or `regexp'.
With optional prefix argument ARG, just run `rgrep'."
  (interactive "P")
  (grep-compute-defaults)
  (if arg
      (call-interactively 'rgrep)
    (let ((query (if mark-active
                     (buffer-substring-no-properties (point) (mark))
                   (thing-at-point 'word))))
      (funcall 'rgrep (read-from-minibuffer "search for: " query)
               rinari-rgrep-file-endings (rinari-root)))))

(defun rinari-ending ()
  "Return the file extension of the current file."
  (let* ((path (buffer-file-name))
         (ending
          (and (string-match ".+?\\(\\.[^/]*\\)$" path)
               (match-string 1 path))))
    ending))

(defun rinari-script-path ()
  "Return the absolute path to the script folder."
  (concat (file-name-as-directory (expand-file-name "script" (rinari-root)))))

(defun rinari-bin-path ()
  "Return the absolute path to the bin folder."
  (concat (file-name-as-directory (expand-file-name "bin" (rinari-root)))))

;;--------------------------------------------------------------------
;; rinari movement using jump.el

(defun rinari-generate (type name)
  "Run the generate command to generate a TYPE called NAME."
  (let* ((default-directory (rinari-root))
         (command (rinari--wrap-rails-command "generate")))
    (message (shell-command-to-string (concat command " " type " " (read-from-minibuffer (format "create %s: " type) name))))))

(defvar rinari-ruby-hash-regexp
  "\\(:[^[:space:]]*?\\)[[:space:]]*\\(=>[[:space:]]*[\"\':]?\\([^[:space:]]*?\\)[\"\']?[[:space:]]*\\)?[,){}\n]"
  "Regexp to match subsequent key => value pairs of a ruby hash.")

(defun rinari-ruby-values-from-render (controller action)
  "Return (CONTROLLER . ACTION) after adjusting for the hash values at point."
  (let ((end (save-excursion
               (re-search-forward "[^,{(]$" nil t)
               (1+ (point)))))
    (save-excursion
      (while (and (< (point) end)
                  (re-search-forward rinari-ruby-hash-regexp end t))
        (when (> (length (match-string 3)) 1)
          (case (intern (match-string 1))
            (:partial
             (let ((partial (match-string 3)))
               (if (string-match "\\(.+\\)/\\(.+\\)" partial)
                   (progn
                     (setf controller (match-string 1 partial))
                     (setf action (concat "_" (match-string 2 partial))))
                 (setf action (concat "_" partial)))))
            (:action  (setf action (match-string 3)))
            (:controller (setf controller (match-string 3)))))))
    (cons controller action)))

(defun rinari-which-render (renders)
  "Select and parse one of the RENDERS supplied."
  (let ((path (jump-completing-read
               "Follow: "
               (mapcar (lambda (lis)
                         (concat (car lis) "/" (cdr lis)))
                       renders))))
    (string-match "\\(.*\\)/\\(.*\\)" path)
    (cons (match-string 1 path) (match-string 2 path))))

(defun rinari-follow-controller-and-action (controller action)
  "Follow CONTROLLER and ACTION through to the final controller or view.
The user is prompted to follow through any intermediate renders
and redirects."
  (save-excursion ;; if we can find the controller#action pair
    (if (and (jump-to-path (format "app/controllers/%s_controller.rb#%s" controller action))
             (equalp (jump-method) action))
        (let ((start (point)) ;; demarcate the borders
              (renders (list (cons controller action))) render view)
          (ruby-forward-sexp)
          ;; collect redirection options and pursue
          (while (re-search-backward "re\\(?:direct_to\\|nder\\)" start t)
            (add-to-list 'renders (rinari-ruby-values-from-render controller action)))
          (let ((render (if (equalp 1 (length renders))
                            (car renders)
                          (rinari-which-render renders))))
            (if (and (equalp (cdr render) action)
                     (equalp (car render) controller))
                (list controller action) ;; directed to here so return
              (rinari-follow-controller-and-action (or (car render)
                                                       controller)
                                                   (or (cdr render)
                                                       action)))))
      ;; no controller entry so return
      (list controller action))))

(defvar rinari-jump-schema
 '((model
    "m"
    (("app/controllers/\\1_controller.rb#\\2$" . "app/models/\\1.rb#\\2")
     ("app/views/\\1/.*"                       . "app/models/\\1.rb")
     ("app/helpers/\\1_helper.rb"              . "app/models/\\1.rb")
     ("db/migrate/.*create_\\1.rb"             . "app/models/\\1.rb")
     ("spec/models/\\1_spec.rb"                . "app/models/\\1.rb")
     ("spec/controllers/\\1_controller_spec.rb". "app/models/\\1.rb")
     ("spec/views/\\1/.*"                      . "app/models/\\1.rb")
     ("spec/fixtures/\\1.yml"                  . "app/models/\\1.rb")
     ("test/functional/\\1_controller_test.rb" . "app/models/\\1.rb")
     ("test/unit/\\1_test.rb#test_\\2$"        . "app/models/\\1.rb#\\2")
     ("test/unit/\\1_test.rb"                  . "app/models/\\1.rb")
     ("test/fixtures/\\1.yml"                  . "app/models/\\1.rb")
     (t                                        . "app/models/"))
    (lambda (path)
      (rinari-generate "model"
                       (and (string-match ".*/\\(.+?\\)\.rb" path)
                            (match-string 1 path)))))
   (controller
    "c"
    (("app/models/\\1.rb"                      . "app/controllers/\\1_controller.rb")
     ("app/views/\\1/\\2\\..*"                 . "app/controllers/\\1_controller.rb#\\2")
     ("app/helpers/\\1_helper.rb"              . "app/controllers/\\1_controller.rb")
     ("db/migrate/.*create_\\1.rb"             . "app/controllers/\\1_controller.rb")
     ("spec/models/\\1_spec.rb"                . "app/controllers/\\1_controller.rb")
     ("spec/controllers/\\1_spec.rb"           . "app/controllers/\\1.rb")
     ("spec/views/\\1/\\2\\.*_spec.rb"         . "app/controllers/\\1_controller.rb#\\2")
     ("spec/fixtures/\\1.yml"                  . "app/controllers/\\1_controller.rb")
     ("test/functional/\\1_test.rb#test_\\2$"  . "app/controllers/\\1.rb#\\2")
     ("test/functional/\\1_test.rb"            . "app/controllers/\\1.rb")
     ("test/unit/\\1_test.rb#test_\\2$"        . "app/controllers/\\1_controller.rb#\\2")
     ("test/unit/\\1_test.rb"                  . "app/controllers/\\1_controller.rb")
     ("test/fixtures/\\1.yml"                  . "app/controllers/\\1_controller.rb")
     (t                                        . "app/controllers/"))
    (lambda (path)
      (rinari-generate "controller"
                       (and (string-match ".*/\\(.+?\\)_controller\.rb" path)
                            (match-string 1 path)))))
   (view
    "v"
    (("app/models/\\1.rb"                      . "app/views/\\1/.*")
     ((lambda () ;; find the controller/view
        (let* ((raw-file (and (buffer-file-name)
                              (file-name-nondirectory (buffer-file-name))))
               (file (and raw-file
                          (string-match "^\\(.*\\)_controller.rb" raw-file)
                          (match-string 1 raw-file))) ;; controller
               (raw-method (ruby-add-log-current-method))
               (method (and file raw-method ;; action
                            (string-match "#\\(.*\\)" raw-method)
                            (match-string 1 raw-method))))
          (when (and file method) (rinari-follow-controller-and-action file method))))
      . "app/views/\\1/\\2.*")
     ("app/controllers/\\1_controller.rb"      . "app/views/\\1/.*")
     ("app/helpers/\\1_helper.rb"              . "app/views/\\1/.*")
     ("db/migrate/.*create_\\1.rb"             . "app/views/\\1/.*")
     ("spec/models/\\1_spec.rb"                . "app/views/\\1/.*")
     ("spec/controllers/\\1_spec.rb"           . "app/views/\\1/.*")
     ("spec/views/\\1/\\2_spec.rb"             . "app/views/\\1/\\2.*")
     ("spec/fixtures/\\1.yml"                  . "app/views/\\1/.*")
     ("test/functional/\\1_controller_test.rb" . "app/views/\\1/.*")
     ("test/unit/\\1_test.rb#test_\\2$"        . "app/views/\\1/_?\\2.*")
     ("test/fixtures/\\1.yml"                  . "app/views/\\1/.*")
     (t                                        . "app/views/.*"))
    t)
   (test
    "t"
    (("app/models/\\1.rb#\\2$"                 . "test/unit/\\1_test.rb#test_\\2")
     ("app/controllers/\\1.rb#\\2$"            . "test/functional/\\1_test.rb#test_\\2")
     ("app/views/\\1/_?\\2\\..*"               . "test/functional/\\1_controller_test.rb#test_\\2")
     ("app/helpers/\\1_helper.rb"              . "test/functional/\\1_controller_test.rb")
     ("db/migrate/.*create_\\1.rb"             . "test/unit/\\1_test.rb")
     ("test/functional/\\1_controller_test.rb" . "test/unit/\\1_test.rb")
     ("test/unit/\\1_test.rb"                  . "test/functional/\\1_controller_test.rb")
     (t                                        . "test/.*"))
    t)
   (rspec
    "r"
    (("app/\\1\\.rb"                           . "spec/\\1_spec.rb")
     ("app/\\1$"                               . "spec/\\1_spec.rb")
     ("spec/views/\\1_spec.rb"                 . "app/views/\\1")
     ("spec/\\1_spec.rb"                       . "app/\\1.rb")
     (t                                        . "spec/.*"))
    t)
   (fixture
    "x"
    (("app/models/\\1.rb"                      . "test/fixtures/\\1.yml")
     ("app/controllers/\\1_controller.rb"      . "test/fixtures/\\1.yml")
     ("app/views/\\1/.*"                       . "test/fixtures/\\1.yml")
     ("app/helpers/\\1_helper.rb"              . "test/fixtures/\\1.yml")
     ("db/migrate/.*create_\\1.rb"             . "test/fixtures/\\1.yml")
     ("spec/models/\\1_spec.rb"                . "test/fixtures/\\1.yml")
     ("spec/controllers/\\1_controller_spec.rb". "test/fixtures/\\1.yml")
     ("spec/views/\\1/.*"                      . "test/fixtures/\\1.yml")
     ("test/functional/\\1_controller_test.rb" . "test/fixtures/\\1.yml")
     ("test/unit/\\1_test.rb"                  . "test/fixtures/\\1.yml")
     (t                                        . "test/fixtures/"))
    t)
   (rspec-fixture
    "z"
    (("app/models/\\1.rb"                      . "spec/fixtures/\\1.yml")
     ("app/controllers/\\1_controller.rb"      . "spec/fixtures/\\1.yml")
     ("app/views/\\1/.*"                       . "spec/fixtures/\\1.yml")
     ("app/helpers/\\1_helper.rb"              . "spec/fixtures/\\1.yml")
     ("db/migrate/.*create_\\1.rb"             . "spec/fixtures/\\1.yml")
     ("spec/models/\\1_spec.rb"                . "spec/fixtures/\\1.yml")
     ("spec/controllers/\\1_controller_spec.rb". "spec/fixtures/\\1.yml")
     ("spec/views/\\1/.*"                      . "spec/fixtures/\\1.yml")
     ("test/functional/\\1_controller_test.rb" . "spec/fixtures/\\1.yml")
     ("test/unit/\\1_test.rb"                  . "spec/fixtures/\\1.yml")
     (t                                        . "spec/fixtures/"))
    t)
   (helper
    "h"
    (("app/models/\\1.rb"                      . "app/helpers/\\1_helper.rb")
     ("app/controllers/\\1_controller.rb"      . "app/helpers/\\1_helper.rb")
     ("app/views/\\1/.*"                       . "app/helpers/\\1_helper.rb")
     ("app/helpers/\\1_helper.rb"              . "app/helpers/\\1_helper.rb")
     ("db/migrate/.*create_\\1.rb"             . "app/helpers/\\1_helper.rb")
     ("spec/models/\\1_spec.rb"                . "app/helpers/\\1_helper.rb")
     ("spec/controllers/\\1_spec.rb"           . "app/helpers/\\1_helper.rb")
     ("spec/views/\\1/.*"                      . "app/helpers/\\1_helper.rb")
     ("test/functional/\\1_controller_test.rb" . "app/helpers/\\1_helper.rb")
     ("test/unit/\\1_test.rb#test_\\2$"        . "app/helpers/\\1_helper.rb#\\2")
     ("test/unit/\\1_test.rb"                  . "app/helpers/\\1_helper.rb")
     (t                                        . "app/helpers/"))
    t)
   (migration
    "i"
    (("app/controllers/\\1_controller.rb"      . "db/migrate/.*create_\\1.rb")
     ("app/views/\\1/.*"                       . "db/migrate/.*create_\\1.rb")
     ("app/helpers/\\1_helper.rb"              . "db/migrate/.*create_\\1.rb")
     ("app/models/\\1.rb"                      . "db/migrate/.*create_\\1.rb")
     ("spec/models/\\1_spec.rb"                . "db/migrate/.*create_\\1.rb")
     ("spec/controllers/\\1_spec.rb"           . "db/migrate/.*create_\\1.rb")
     ("spec/views/\\1/.*"                      . "db/migrate/.*create_\\1.rb")
     ("test/functional/\\1_controller_test.rb" . "db/migrate/.*create_\\1.rb")
     ("test/unit/\\1_test.rb#test_\\2$"        . "db/migrate/.*create_\\1.rb#\\2")
     ("test/unit/\\1_test.rb"                  . "db/migrate/.*create_\\1.rb")
     (t                                        . "db/migrate/"))
    (lambda (path)
      (rinari-generate "migration"
                       (and (string-match ".*create_\\(.+?\\)\.rb" path)
                            (match-string 1 path)))))
   (cells
    "C"
    (("app/cells/\\1_cell.rb"                  . "app/cells/\\1/.*")
     ("app/cells/\\1/\\2.*"                    . "app/cells/\\1_cell.rb#\\2")
     (t                                        . "app/cells/"))
    (lambda (path)
      (rinari-generate "cells"
                       (and (string-match ".*/\\(.+?\\)_cell\.rb" path)
                            (match-string 1 path)))))
   (features "F" ((t . "features/.*feature")) nil)
   (steps "S" ((t . "features/step_definitions/.*")) nil)
   (environment "e" ((t . "config/environments/")) nil)
   (application "a" ((t . "config/application.rb")) nil)
   (routes "R" ((t . "config/routes.rb")) nil)
   (configuration "n" ((t . "config/")) nil)
   (script "s" ((t . "script/")) nil)
   (lib "l" ((t . "lib/")) nil)
   (log "o" ((t . "log/")) nil)
   (worker "w" ((t . "lib/workers/")) nil)
   (public "p" ((t . "public/")) nil)
   (stylesheet "y" ((t . "public/stylesheets/.*")
                    (t . "app/assets/stylesheets/.*")) nil)
   (sass "Y" ((t . "public/stylesheets/sass/.*")
              (t . "app/stylesheets/.*")) nil)
   (javascript "j" ((t . "public/javascripts/.*")
                    (t . "app/assets/javascripts/.*")) nil)
   (plugin "u" ((t . "vendor/plugins/")) nil)
   (mailer "M" ((t . "app/mailers/")) nil)
   (file-in-project "f" ((t . ".*")) nil)
   (by-context
    ";"
    (((lambda () ;; Find-by-Context
        (let ((path (buffer-file-name)))
          (when (string-match ".*/\\(.+?\\)/\\(.+?\\)\\..*" path)
            (let ((cv (cons (match-string 1 path) (match-string 2 path))))
              (when (re-search-forward "<%=[ \n\r]*render(? *" nil t)
                (setf cv (rinari-ruby-values-from-render (car cv) (cdr cv)))
                (list (car cv) (cdr cv)))))))
      . "app/views/\\1/\\2.*"))))
 "Jump schema for rinari.")

(defun rinari-apply-jump-schema (schema)
  "Define the rinari-find-* functions by passing each element SCHEMA to `defjump'."
  (mapcar
   (lambda (type)
     (let ((name (first type))
           (specs (third type))
           (make (fourth type)))
       (eval `(defjump
                ,(intern (format "rinari-find-%S" name))
                ,specs
                rinari-root
                ,(format "Go to the most logical %S given the current location" name)
                ,(when make `(quote ,make))
                'ruby-add-log-current-method))))
   schema))
(rinari-apply-jump-schema rinari-jump-schema)

;;--------------------------------------------------------------------
;; minor mode and keymaps

(defvar rinari-minor-mode-map
  (let ((map (make-sparse-keymap)))
    map)
  "Key map for Rinari minor mode.")

(defun rinari-bind-key-to-func (key func)
  "Bind KEY to FUNC with each of the `rinari-minor-mode-prefixes'."
  (dolist (prefix rinari-minor-mode-prefixes)
    (eval `(define-key rinari-minor-mode-map
             ,(format "\C-c%s%s" prefix key) ,func))))

(defvar rinari-minor-mode-keybindings
  '(("s" . 'rinari-script)              ("q" . 'rinari-sql)
    ("e" . 'rinari-insert-erb-skeleton) ("t" . 'rinari-test)
    ("r" . 'rinari-rake)                ("c" . 'rinari-console)
    ("w" . 'rinari-web-server)          ("g" . 'rinari-rgrep)
    ("x" . 'rinari-extract-partial)     ("p" . 'rinari-goto-partial)
    (";" . 'rinari-find-by-context)     ("'" . 'rinari-find-by-context)
    ("d" . 'rinari-cap))
  "Alist mapping of keys to functions in `rinari-minor-mode-map'.")

(dolist (el (append (mapcar (lambda (el)
                              (cons (concat "f" (second el))
                                    (read (format "'rinari-find-%S" (first el)))))
                            rinari-jump-schema)
                    rinari-minor-mode-keybindings))
  (rinari-bind-key-to-func (car el) (cdr el)))

(easy-menu-define rinari-minor-mode-menu rinari-minor-mode-map
  "Rinari menu"
  '("Rinari"
    ["Search" rinari-rgrep t]
    "---"
    ["Find file in project" rinari-find-file-in-project t]
    ["Find file by context" rinari-find-by-context t]
    ("Jump to..."
     ["Model" rinari-find-model t]
     ["Controller" rinari-find-controller t]
     ["View" rinari-find-view t]
     ["Helper" rinari-find-helper t]
     ["Worker" rinari-find-worker t]
     ["Mailer" rinari-find-mailer t]
     "---"
     ["Javascript" rinari-find-javascript t]
     ["Stylesheet" rinari-find-stylesheet t]
     ["Sass" rinari-find-sass t]
     ["public/" rinari-find-public t]
     "---"
     ["Test" rinari-find-test t]
     ["Rspec" rinari-find-rspec t]
     ["Fixture" rinari-find-fixture t]
     ["Rspec fixture" rinari-find-rspec-fixture t]
     ["Feature" rinari-find-features t]
     ["Step" rinari-find-steps t]
     "---"
     ["application.rb" rinari-find-application t]
     ["config/" rinari-find-configuration t]
     ["environments/" rinari-find-environment t]
     ["migrate/" rinari-find-migration t]
     ["lib/" rinari-find-lib t]
     ["script/" rinari-find-script t]
     ["log/" rinari-find-log t])
    "---"
    ("Web server"
     ["Start" rinari-web-server t]
     ["Restart" rinari-web-server-restart t])
    ["Console" rinari-console t]
    ["SQL prompt" rinari-sql t]
    "---"
    ["Script" rinari-script t]
    ["Rake" rinari-rake t]
    ["Cap" rinari-cap t]))

;;;###autoload
(defun rinari-launch ()
  "Call function `rinari-minor-mode' if inside a rails project.
Otherwise, disable that minor mode if currently enabled."
  (interactive)
  (let ((root (rinari-root)))
    (if root
        (let ((r-tags-path (concat root rinari-tags-file-name)))
          (set (make-local-variable 'tags-file-name)
               (and (file-exists-p r-tags-path) r-tags-path))
          (rinari-minor-mode t))
      (when rinari-minor-mode
        (rinari-minor-mode -1)))))

(defun rinari-launch-maybe ()
  "Call `rinari-launch' if customized to do so.
Both `rinari-major-modes' and `rinari-exclude-major-modes' will
be used to make the decision.  When the global rinari mode is
active, the default is to try to launch rinari in any major
mode.  If `rinari-major-modes' is non-nil, then launching will
happen only in the listed modes.  Major modes listed in
`rinari-exclude-major-modes' will never have rinari
auto-launched, but `rinari-launch' can still be used to manually
enable rinari in buffers using those modes."
  (when (and (not (minibufferp))
             (or (null rinari-major-modes)
                 (memq major-mode rinari-major-modes))
             (or (null rinari-exclude-major-modes)
                 (not (memq major-mode rinari-exclude-major-modes))))
    (rinari-launch)))

(add-hook 'mumamo-after-change-major-mode-hook 'rinari-launch)

(defadvice cd (after rinari-on-cd activate)
  "Call `rinari-launch' when changing directories.
This will activate/deactivate rinari as necessary when changing
into and out of rails project directories."
  (rinari-launch))

;;;###autoload
(define-minor-mode rinari-minor-mode
  "Enable Rinari minor mode to support working with the Ruby on Rails framework."
  nil
  " Rinari"
  rinari-minor-mode-map)

;;;###autoload
(define-global-minor-mode global-rinari-mode
  rinari-minor-mode rinari-launch-maybe)

(provide 'rinari)

;; Local Variables:
;; coding: utf-8
;; indent-tabs-mode: nil
;; byte-compile-warnings: (not cl-functions)
;; eval: (checkdoc-minor-mode 1)
;; End:

;;; rinari.el ends here
