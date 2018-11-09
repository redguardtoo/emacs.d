;; -*- coding: utf-8; lexical-binding: t; -*-
(autoload 'gmail2bbdb-import-file "gmail2bbdb" "" t)
(autoload 'ivy-recentf "ivy" "" t)
(autoload 'ivy-read "ivy")
(autoload 'simpleclip-get-contents "simpleclip" "" t)
(autoload 'simpleclip-set-contents "simpleclip" "" t)
(autoload 'rainbow-mode "rainbow-mode" nil t)
(autoload 'csv-mode "csv-mode" "Major mode for editing comma-separated value files." t)
(autoload 'csv-nav-mode "csv-nav-mode" "Major mode for navigating comma-separated value files." t)
(autoload 'counsel-etags-find-tag-at-point "counsel-etags" "" t nil)
(autoload 'counsel-etags-scan-code "counsel-etags" "" t nil)
(autoload 'counsel-etags-grep "counsel-etags" "" t nil)
(autoload 'counsel-etags-grep-symbol-at-point "counsel-etags" "" t nil)
(autoload 'counsel-etags-recent-tag "counsel-etags" "" t nil)
(autoload 'turn-on-stripe-buffer-mode "stripe-buffer" "" nil)
(autoload 'turn-on-stripe-table-mode "stripe-buffer" "" nil)
(autoload 'markdown-mode "markdown-mode" "Mode for editing Markdown documents" t)
(autoload 'csv-mode "csv-mode" "Major mode for comma-separated value files." t)
(autoload 'sdcv-search-pointer "sdcv" "show word explanation in buffer" t)
(autoload 'sdcv-search-input+ "sdcv" "show word explanation in tooltip" t)
(autoload 'vr/replace "visual-regexp")
(autoload 'vr/query-replace "visual-regexp")
(autoload 'vr/mc-mark "visual-regexp")
(autoload 'issue-tracker-increment-issue-id-under-cursor "issue-tracker" "" t)
(autoload 'issue-tracker-insert-issue-list "issue-tracker" "" t)
(autoload 'elpamr-create-mirror-for-installed "elpa-mirror" "" t)
(autoload 'org2nikola-export-subtree "org2nikola" "" t)
(autoload 'org2nikola-rerender-published-posts "org2nikola" "" t)
(autoload 'dictionary-new-search "dictionary" "" t nil)
(autoload 'legalese "legalese" "" t)
(autoload 'buf-move-left "buffer-move" "move buffer" t)
(autoload 'buf-move-right "buffer-move" "move buffer" t)
(autoload 'buf-move-up "buffer-move" "move buffer" t)
(autoload 'buf-move-down "buffer-move" "move buffer" t)
(autoload 'confluence-edit-mode "confluence-edit" "enable confluence-edit-mode" t)
(autoload 'vimrc-mode "vimrc-mode")
(autoload 'highlight-symbol "highlight-symbol" "" t)
(autoload 'highlight-symbol-next "highlight-symbol" "" t)
(autoload 'highlight-symbol-prev "highlight-symbol" "" t)
(autoload 'highlight-symbol-nav-mode "highlight-symbol" "" t)
(autoload 'highlight-symbol-query-replace "highlight-symbol" "" t)
(autoload 'which-function "which-func")
(autoload 'popup-tip "popup")
(autoload 'string-edit-at-point "string-edit" "" t nil)
(autoload 'srt-renumber-subtitles "subtitles" "" t)
(autoload 'srt-offset-subtitles "subtitles" "" t)
(autoload 'srt-mult-subtitles "subtitles" "" t)
(autoload 'srt-convert-sub-to-srt "subtitles" "" t)
(autoload 'fastdef-insert "fastdef" nil t)
(autoload 'fastdef-insert-from-history "fastdef" nil t)
(autoload 'org-mime-htmlize "org-mime" nil t)
(autoload 'org-mime-org-buffer-htmlize "org-mime" nil t)
(autoload 'org-mime-org-subtree-htmlize "org-mime" nil t)
(autoload 'doctest-mode "doctest-mode" "Python doctest editing mode." t)
(autoload 'run-ruby "inf-ruby" "Run an inferior Ruby process")
(autoload 'textile-mode "textile-mode" "Mode for editing Textile documents" t)
(autoload 'find-library-name "find-func")
(autoload 'web-mode "web-mode")
(autoload 'wg-create-workgroup "workgroups2" nil t)
(autoload 'snippet-mode "yasnippet" "")
(autoload 'run-js "js-comint" "")
(autoload 'vc-msg-show "vc-msg" "")
(autoload 'eacl-complete-line "eacl" "")
(autoload 'eacl-complete-statement "eacl" "")
(autoload 'eacl-complete-snippet "eacl" "")
(autoload 'eacl-complete-tag "eacl" "")
(autoload 'dropdown-list "dropdown-list" "")
(autoload 'magit-commit-popup "magit" "")

;; {{ my perforce tools
(autoload 'p4edit "p4tools" "\
p4 edit current file.

\(fn)" t nil)

(autoload 'p4submit "p4tools" "\
p4 submit current file.
If FILE-OPENED, current file is still opened.

\(fn &optional FILE-OPENED)" t nil)

(autoload 'p4url "p4tools" "\
Get Perforce depot url of the file.

\(fn)" t nil)

(autoload 'p4unshelve "p4tools" "\
Unshelve files from selected change.

\(fn)" t nil)

(autoload 'p4revert "p4tools" "\
p4 revert current file.

\(fn)" t nil)

(autoload 'p4add "p4tools" "\
p4 add current file.

\(fn)" t nil)

(autoload 'p4diff "p4tools" "\
Show diff of current file like `git diff'.
If IN-PROJECT is t, operate in project root.

\(fn &optional IN-PROJECT)" t nil)

(autoload 'p4show "p4tools" "\
p4 show changes of current file.
If IN-PROJECT is t, operate in project root.

\(fn &optional IN-PROJECT)" t nil)

(autoload 'p4edit-in-wgrep-buffer "p4tools" "\
'p4 edit' files in wgrep buffer.
Turn off `read-only-mode' of opened files.

\(fn)" t nil)

(autoload 'p4edit-in-diff-mode "p4tools" "\
'p4 edit' files in `diff-mode'.
Turn off `read-only-mode' of opened files.

\(fn)" t nil)

(autoload 'p4history "p4tools" "\
Show history of current file like `git log -p'.
NUM default values i 10.  Show the latest NUM changes.

\(fn &optional NUM)" t nil)
;; }}

(provide 'init-autoload)
;;; init-autoload.el ends here

