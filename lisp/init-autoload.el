;; -*- coding: utf-8; lexical-binding: t; -*-
(autoload 'xclip-set-selection "xclip" "" t)
(autoload 'xclip-get-selection "xclip" "" t)
(autoload 'langtool-check "langtool" "" t)
(autoload 'langtool-check-buffer "langtool" "" t)
(autoload 'dianyou-group-make-nnir-group "dianyou" "" t)
(autoload 'dianyou-summary-extract-email-address "dianyou" "" t)
(autoload 'dianyou-switch-gnus-buffer "dianyou" "" t)
(autoload 'dianyou-insert-email-address-from-received-mails "dianyou" "" t)
(autoload 'dianyou-paste-image-from-clipboard "dianyou" "" t)
(autoload 'gmail2bbdb-import-file "gmail2bbdb" "" t)
(autoload 'gmail2bbdb-import-file "gmail2bbdb" "" t)
(autoload 'mybigword-show-big-words-from-file "mybigword" "" t)
(autoload 'mybigword-show-big-words-from-current-buffer "mybigword" "" t)
(autoload 'mybigword-play-video-of-word-at-point "mybigword" "" t)
(autoload 'mybigword-pronounce-word "mybigword" "" t)
(autoload 'ivy-recentf "ivy" "" t)
(autoload 'ivy-read "ivy")
(autoload 'rainbow-mode "rainbow-mode" nil t)
(autoload 'workgroups-mode "workgroups2" nil t)
(autoload 'roblox-mode "roblox-mode" nil t)
(autoload 'csv-mode "csv-mode" "Major mode for editing comma-separated value files." t)
(autoload 'csv-nav-mode "csv-nav-mode" "Major mode for navigating comma-separated value files." t)
(autoload 'counsel-etags-find-tag-at-point "counsel-etags" "" t nil)
(autoload 'counsel-etags-list-tag-in-current-file "counsel-etags" "" t nil)
(autoload 'counsel-etags-push-marker-stack "counsel-etags" "" t nil)
(autoload 'counsel-etags-scan-code "counsel-etags" "" t nil)
(autoload 'counsel-etags-grep "counsel-etags" "" t nil)
(autoload 'counsel-etags-recent-tag "counsel-etags" "" t nil)
(autoload 'markdown-mode "markdown-mode" "Mode for editing Markdown documents" t)
(autoload 'csv-mode "csv-mode" "Major mode for comma-separated value files." t)
(autoload 'sdcv-search-pointer "sdcv" "show word explanation in buffer" t)
(autoload 'sdcv-search-input+ "sdcv" "show word explanation in tooltip" t)
(autoload 'sdcv-search-input "sdcv" "show word explanation in tooltip" t)
(autoload 'elpamr-create-mirror-for-installed "elpa-mirror" "" t)
(autoload 'org2nikola-export-subtree "org2nikola" "" t)
(autoload 'org2nikola-rerender-published-posts "org2nikola" "" t)
(autoload 'dictionary-new-search "dictionary" "" t nil)
(autoload 'legalese "legalese" "" t)
(autoload 'buf-move-left "buffer-move" "move buffer" t)
(autoload 'buf-move-right "buffer-move" "move buffer" t)
(autoload 'buf-move-up "buffer-move" "move buffer" t)
(autoload 'buf-move-down "buffer-move" "move buffer" t)
(autoload 'highlight-symbol "highlight-symbol" "" t)
(autoload 'highlight-symbol-next "highlight-symbol" "" t)
(autoload 'highlight-symbol-prev "highlight-symbol" "" t)
(autoload 'highlight-symbol-nav-mode "highlight-symbol" "" t)
(autoload 'highlight-symbol-query-replace "highlight-symbol" "" t)
(autoload 'which-function "which-func")
(autoload 'popup-tip "popup")
(autoload 'srt-renumber-subtitles "subtitles" "" t)
(autoload 'srt-offset-subtitles "subtitles" "" t)
(autoload 'srt-mult-subtitles "subtitles" "" t)
(autoload 'srt-convert-sub-to-srt "subtitles" "" t)
(autoload 'fastdef-insert "fastdef" nil t)
(autoload 'fastdef-insert-from-history "fastdef" nil t)
(autoload 'org-mime-htmlize "org-mime" nil t)
(autoload 'org-mime-edit-mail-in-org-mode "org-mime" nil t)
(autoload 'org-mime-revert-to-plain-text-mail "org-mime" nil t)
(autoload 'org-mime-org-buffer-htmlize "org-mime" nil t)
(autoload 'org-mime-org-subtree-htmlize "org-mime" nil t)
(autoload 'doctest-mode "doctest-mode" "Python doctest editing mode." t)
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

