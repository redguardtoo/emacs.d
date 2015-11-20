;;; w3m-filter.el --- filtering utility of advertisements on WEB sites -*- coding: utf-8 -*-

;; Copyright (C) 2001-2008, 2012-2015 TSUCHIYA Masatoshi <tsuchiya@namazu.org>

;; Authors: TSUCHIYA Masatoshi <tsuchiya@namazu.org>
;; Keywords: w3m, WWW, hypermedia

;; This file is a part of emacs-w3m.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.


;;; Commentary:

;; w3m-filter.el is the add-on utility to filter advertisements on WEB
;; sites.


;;; Code:

(provide 'w3m-filter)

(eval-when-compile
  (require 'cl))

(require 'w3m)

(defcustom w3m-filter-configuration
  `((t
     ("Strip Google's click-tracking code from link urls"
      "Google の click-tracking コードをリンクの url から取り除きます")
     "\\`https?://[a-z]+\\.google\\."
     w3m-filter-google-click-tracking)
    (t
     ("Align table columns vertically to shrink the table width in Google"
      "Google 検索結果のテーブルを縦方向で揃えて幅を狭めます")
     "\\`http://\\(www\\|images\\|news\\|maps\\|groups\\)\\.google\\."
     w3m-filter-google-shrink-table-width)
    (t
     ("Add name anchors that w3m can handle in all pages"
      "すべてのページに w3m が扱える name アンカーを追加します")
     ""
     w3m-filter-add-name-anchors)
    (t
     ("Substitute disabled attr with readonly attr in forms"
      "フォーム中の disabled 属性を readonly 属性で代用します")
     ""
     w3m-filter-subst-disabled-with-readonly)
    (nil
     ("Render <tfoot>...</tfoot> after <tbody>...</tbody>"
      "テーブル内の <tfoot> を <tbody> の後に描画します")
     ""
     w3m-filter-fix-tfoot-rendering)
    (nil
     ("Remove garbage in http://www.geocities.co.jp/*"
      "http://www.geocities.co.jp/* でゴミを取り除きます")
     "\\`http://www\\.geocities\\.co\\.jp/"
     (w3m-filter-delete-regions
      "<DIV ALIGN=CENTER>\n<!--*/GeoGuide/*-->" "<!--*/GeoGuide/*-->\n</DIV>"))
    (nil
     ("Remove ADV in http://*.hp.infoseek.co.jp/*"
      "http://*.hp.infoseek.co.jp/* で広告を取り除きます")
     "\\`http://[a-z]+\\.hp\\.infoseek\\.co\\.jp/"
     (w3m-filter-delete-regions "<!-- start AD -->" "<!-- end AD -->"))
    (nil
     ("Remove ADV in http://linux.ascii24.com/linux/*"
      "http://linux.ascii24.com/linux/* で広告を取り除きます")
     "\\`http://linux\\.ascii24\\.com/linux/"
     (w3m-filter-delete-regions
      "<!-- DAC CHANNEL AD START -->" "<!-- DAC CHANNEL AD END -->"))
    (nil
     "A filter for Google"
     "\\`http://\\(www\\|images\\|news\\|maps\\|groups\\)\\.google\\."
     w3m-filter-google)
    (nil
     "A filter for Amazon"
     "\\`https?://\\(?:www\\.\\)?amazon\\.\
\\(?:com\\|co\\.\\(?:jp\\|uk\\)\\|fr\\|de\\)/"
     w3m-filter-amazon)
    (nil
     ("A filter for Mixi.jp"
      "ミクシィ用フィルタ")
     "\\`https?://mixi\\.jp" w3m-filter-mixi)
    (nil
     "A filter for http://eow.alc.co.jp/*/UTF-8*"
     "\\`http://eow\\.alc\\.co\\.jp/[^/]+/UTF-8" w3m-filter-alc)
    (nil
     ("A filter for Asahi Shimbun"
      "朝日新聞用フィルタ")
     "\\`http://www\\.asahi\\.com/" w3m-filter-asahi-shimbun)
    (nil
     "A filter for http://imepita.jp/NUM/NUM*"
     "\\`http://imepita\\.jp/[0-9]+/[0-9]+" w3m-filter-imepita)
    (nil
     "A filter for http://allatanys.jp/*"
     "\\`http://allatanys\\.jp/" w3m-filter-allatanys)
    (nil
     "A filter for Wikipedia"
     "\\`http://.*\\.wikipedia\\.org/" w3m-filter-wikipedia)
    (nil
     ("Remove inline frames in all pages"
      "すべてのページでインラインフレームを取り除きます")
     ""
     w3m-filter-iframe))
  "List of filter configurations applied to web contents.
Each filter configuration consists of the following form:

\(FLAG DESCRIPTION REGEXP FUNCTION)

FLAG
  Non-nil means this filter is enabled.
DESCRIPTION
  Describe what this filter does.  The value may be a string or a list
  of two strings; in the later case, those descriptions are written in
  English and Japanese respectively, and only either one is displayed
  in the customization buffer according to `w3m-language'.
REGEXP
  Regular expression to restrict this filter so as to run only on web
  contents of which the url matches.
FUNCTION
  Filter function to run on web contents.  The value may be a function
  or a list of a function and rest argument(s).  A function should take
  at least one argument, a url of contents retrieved then, as the first
  argument even if it is useless.  Use the later (i.e. a function and
  arguments) if the function requires rest arguments."
  :group 'w3m
  :type '(repeat
	  :convert-widget w3m-widget-type-convert-widget
	  (let ((locker (lambda (fn)
			  `(lambda (&rest args)
			     (when (and (not inhibit-read-only)
					(eq (get-char-property (point) 'face)
					    'widget-inactive))
			       (when (and (not debug-on-error)
					  (eventp (cadr args))
					  (memq 'down
						(event-modifiers (cadr args))))
				 (setq before-change-functions
				       `((lambda (from to)
					   (setq before-change-functions
						 ',before-change-functions)))))
			       (error "The widget here is not active"))
			     (apply #',fn args)))))
	    `((group
	       :indent 2

	       ;; Work around a widget bug: the default value of `choice'
	       ;; gets nil regardless of the type of items if it is within
	       ;; (group :inline t ...).  Fixed in Emacs 24.4 (Bug#12670).
	       :default-get (lambda (widget) '(t "Not documented" ".*" ignore))

	       :value-create
	       (lambda (widget)
		 (widget-group-value-create widget)
		 (unless (car (widget-value widget))
		   (let ((children (widget-get widget :children)))
		     (widget-specify-inactive
		      (cadr (widget-get widget :args))
		      (widget-get (car children) :to)
		      (widget-get (car (last children)) :to)))))
	       (checkbox
		:format "\n%[%v%]"
		:action
		(lambda (widget &optional event)
		  (let ((widget-edit-functions
			 (lambda (widget)
			   (let* ((parent (widget-get widget :parent))
				  (child (cadr (widget-get parent :args))))
			     (if (widget-value widget)
				 (progn
				   (widget-specify-active child)
				   (widget-put child :inactive nil))
			       (widget-specify-inactive
				child
				(widget-get widget :to)
				(widget-get
				 (car (last
				       (widget-get
					(car (last
					      (widget-get parent :children)))
					:children))) :to)))))))
		    (widget-checkbox-action widget event))))
	       (group
		:inline t
		(choice
		 :format " %v"
		 (string :format "%v")
		 (group ,@(if (equal "Japanese" w3m-language)
			      '((sexp :format "") (string :format "%v"))
			    '((string :format "%v") (sexp :format ""))))
		 (const :format "Not documented\n" nil))
		(regexp :format "Regexp matching url: %v")
		(choice
		 :tag "Type" :format "Function %[Type%]: %v"
		 :action ,(funcall locker 'widget-choice-action)
		 (function :tag "Function with no rest arg" :format "%v")
		 (group
		  :tag "Function and rest arg(s)" :indent 0 :offset 4
		  (function :format "%v")
		  (editable-list
		   :inline t
		   :entry-format "%i %d Arg: %v"
		   :insert-before
		   ,(funcall locker 'widget-editable-list-insert-before)
		   :delete-at
		   ,(funcall locker 'widget-editable-list-delete-at)
		   (sexp :format "%v"))))))))))

(defcustom w3m-filter-rules nil
  "Rules to filter advertisements on WEB sites.
This variable is semi-obsolete; use `w3m-filter-configuration' instead."
  :group 'w3m
  :type '(repeat
	  (group :format "%v" :indent 2
		 (regexp :format "Regexp: %v\n" :value ".*" :size 0)
		 (choice
		  :tag "Filtering Rule"
		  (group :inline t
			 :tag "Delete regions surrounded with these patterns"
			 (const :format "Function: %v\n"
				w3m-filter-delete-regions)
			 (string :format "Start: %v\n" :size 0
				 :value "not a regexp")
			 (string :format "  End: %v\n" :size 0
				 :value "not a regexp"))
		  (function :tag "Filter with a user defined function"
			    :format "Function: %v\n" :size 0)))))

(defcustom w3m-filter-google-use-utf8
  (or (featurep 'un-define) (fboundp 'utf-translate-cjk-mode)
      (and (not (equal "Japanese" w3m-language))
	   (w3m-find-coding-system 'utf-8)))
  "*Use the converting rule to UTF-8 on the site of Google."
  :group 'w3m
  :type 'boolean)

(defcustom w3m-filter-google-use-ruled-line  t
  "*Use the ruled line on the site of Google."
  :group 'w3m
  :type 'boolean)

(defcustom w3m-filter-google-separator "<hr>"
  "Field separator for Google's search results ."
  :group 'w3m
  :type 'string)

(defcustom w3m-filter-amazon-regxp
  (concat
   "\\`\\(https?://\\(?:www\\.\\)?amazon\\."
   "\\(?:com\\|co\\.\\(?:jp\\|uk\\)\\|fr\\|de\\)"
   ;; "Joyo.com"
   "\\)/"
   "\\(?:"
   "\\(?:exec/obidos\\|o\\)/ASIN"
   "\\|"
   "gp/product"
   "\\|"
   "\\(?:[^/]+/\\)?dp"
   "\\)"
   "/\\([0-9]+\\)")
  "*Regexp to extract ASIN number for Amazon."
  :group 'w3m
  :type '(string :size 0))

(defcustom w3m-filter-amazon-short-url-bottom nil
  "*Amazon short URLs insert bottom position."
  :group 'w3m
  :type 'boolean)

;;;###autoload
(defun w3m-filter (url)
  "Apply filtering rule of URL against a content in this buffer."
  (save-match-data
    (dolist (elem (append w3m-filter-rules
			  (delq nil
				(mapcar
				 (lambda (config)
				   (when (car config)
				     (if (consp (nth 3 config))
					 (cons (nth 2 config) (nth 3 config))
				       (list (nth 2 config) (nth 3 config)))))
				 w3m-filter-configuration))))
      (when (string-match (car elem) url)
	(apply (cadr elem) url (cddr elem))))))

(defun w3m-filter-delete-regions (url start end)
  "Delete regions surrounded with a START pattern and an END pattern."
  (goto-char (point-min))
  (let (p (i 0))
    (while (and (search-forward start nil t)
		(setq p (match-beginning 0))
		(search-forward end nil t))
      (delete-region p (match-end 0))
      (incf i))
    (> i 0)))

(defun w3m-filter-replace-regexp (url regexp to-string)
  "Replace all occurrences of REGEXP with TO-STRING."
  (goto-char (point-min))
  (while (re-search-forward regexp nil t)
    (replace-match to-string nil nil)))

;; Filter functions:
(defun w3m-filter-google-click-tracking (url)
  "Strip Google's click-tracking code from link urls"
  (goto-char (point-min))
  (while (re-search-forward "\\(<a[\t\n ]+\\(?:[^\t\n >]+[\t\n ]+\\)*\
href=\"\\)\\(?:[^\"]+\\)?/\\(?:imgres\\?imgurl\\|url\\?\\(?:q\\|url\\)\\)=\
\\([^&]+\\)[^>]+>" nil t)
    ;; In a search result Google encodes some special characters like "+"
    ;; and "?" to "%2B" and "%3F" in a real url, so we need to decode them.
    (insert (w3m-url-decode-string
	     (prog1
		 (concat (match-string 1) (match-string 2) "\">")
	       (delete-region (match-beginning 0) (match-end 0)))))))

(defun w3m-filter-google-shrink-table-width (url)
  "Align table columns vertically to shrink the table width."
  (let ((case-fold-search t)
	last)
    (goto-char (point-min))
    (while (re-search-forward "<tr[\t\n\r >]" nil t)
      (when (w3m-end-of-tag "tr")
	(save-restriction
	  (narrow-to-region (goto-char (match-beginning 0))
			    (match-end 0))
	  (setq last nil)
	  (while (re-search-forward "<td[\t\n\r >]" nil t)
	    (when (w3m-end-of-tag "td")
	      (setq last (match-end 0))
	      (replace-match "<tr>\\&</tr>")))
	  (when last
	    (goto-char (+ 4 last))
	    (delete-char 4))
	  (goto-char (point-max)))))
    ;; Remove rowspan and width specs, and <br>s.
    (goto-char (point-min))
    (while (re-search-forward "<table[\t\n\r >]" nil t)
      (when (w3m-end-of-tag "table")
	(save-restriction
	  (narrow-to-region (goto-char (match-beginning 0))
			    (match-end 0))
	  (while (re-search-forward "\
\[\t\n\r ]*\\(?:\\(?:rowspan\\|width\\)=\"[^\"]+\"\\|<br>\\)[\t\n\r ]*"
				    nil t)
	    ;; Preserve a space at the line-break point.
	    (replace-match " "))
	  ;; Insert a space between ASCII and non-ASCII characters
	  ;; and after a comma.
	  (goto-char (point-min))
	  (while (re-search-forward "\
\\([!-;=?-~]\\)\\([^ -~]\\)\\|\\([^ -~]\\)\\([!-;=?-~]\\)\\|\\(,\\)\\([^ ]\\)"
				    nil t)
	    (forward-char -1)
	    (insert " ")
	    (forward-char))
	  (goto-char (point-max)))))))

(defun w3m-filter-add-name-anchors (url)
  ;;  cf. [emacs-w3m:11153] [emacs-w3m:12339] [emacs-w3m:12422]
  "Add name anchors that w3m can handle.
This function adds ``<a name=\"FOO_BAR\"></a>'' in front of
``<TAG ... id=\"FOO_BAR\" ...>FOO BAR</TAG>'' in the current buffer."
  (let ((case-fold-search t)
	(maxregexps 10)
	names regexp i st nd)
    (goto-char (point-min))
    (while (re-search-forward "<a[\t\n\r ]+\\(?:[^\t\n\r >]+[\t\n\r ]+\\)*\
href=\"#\\([a-z][-.0-9:_a-z]*\\)\"" nil t)
      (add-to-list 'names (match-string 1)))
    (setq case-fold-search nil)
    (while names
      (setq regexp "[\t\n\r ]+[Ii][Dd]=\"\\("
	    i maxregexps)
      (while (and names (> i 0))
	(setq regexp (concat regexp (regexp-quote (pop names)) "\\|")
	      i (1- i)))
      (setq regexp (concat (substring regexp 0 -1) ")\""))
      (goto-char (point-min))
      (while (re-search-forward "<[^>]+>" nil t)
	(setq st (match-beginning 0)
	      nd (match-end 0))
	(goto-char st)
	(if (re-search-forward regexp nd t)
	    (progn
	      (goto-char st)
	      (insert "<a name=" (match-string 1) "></a>")
	      (goto-char (+ nd (- (point) st))))
	  (goto-char nd))))))

(defun w3m-filter-subst-disabled-with-readonly (url)
  ;;  cf. [emacs-w3m:12146] [emacs-w3m:12222]
  "Substitute disabled attr with readonly attr in forms."
  (let ((case-fold-search t) st opt nd val default)
    (goto-char (point-min))
    (while (and (re-search-forward "\
<\\(?:input\\|\\(option\\)\\|textarea\\)[\t\n ]" nil t)
		(progn
		  (setq st (match-beginning 0)
			opt (match-beginning 1))
		  (search-forward ">" nil t))
		(progn
		  (setq nd (match-end 0))
		  (goto-char st)
		  (re-search-forward "[\t\n ]\
\\(?:\\(disabled\\(=\"[^\"]+\"\\)?\\)\\|\\(readonly\\(?:=\"[^\"]+\"\\)?\\)\\)"
				     nd t)))
      (setq val (if (match-beginning 1)
		    (if (match-beginning 2)
			"readonly=\"readonly\""
		      "readonly")
		  (match-string 3)))
      (if opt
	  ;; Unfortunately w3m doesn't support readonly attr in select forms,
	  ;; so we replace them with read-only input forms.
	  (if (and (re-search-backward "<select[\t\n ]" nil t)
		   (w3m-end-of-tag "select")
		   (< st (match-end 0)))
	      (save-restriction
		(narrow-to-region (match-beginning 0) (match-end 0))
		(goto-char (+ (match-beginning 0) 8))
		(w3m-parse-attributes (id name)
		  (if (and id name)
		      (progn
			(goto-char (point-min))
			(setq default
			      (when (re-search-forward "<option\
\\(?:[\t\n ]+[^\t\n >]+\\)*[\t\n ]selected\\(?:=\"[^\"]+\"\\)?\
\\(?:[\t\n ]+[^\t\n >]+\\)*[\t\n /]*>[\t\n ]*\\([^<]+\\)" nil t)
				(goto-char (match-end 1))
				(skip-chars-backward "\t\n ")
				(buffer-substring (match-beginning 1) (point))))
			(delete-region (point-min) (point-max))
			(insert "<input id=\"" id "\" name=\"" name "\""
				(if default
				    (concat " value=\"" default "\" ")
				  " ")
				val
				;; Fit the width to that of the select form.
				" size=\"13\">"))
		    (goto-char (point-max)))))
	    (goto-char nd))
	(if (match-beginning 1)
	    (save-restriction
	      (narrow-to-region st nd)
	      (delete-region (goto-char (match-beginning 1)) (match-end 1))
	      (insert val)
	      (goto-char (point-max)))
	  (goto-char nd))))))

(defun w3m-filter-fix-tfoot-rendering (url &optional recursion)
  "Render <tfoot>...</tfoot> after <tbody>...</tbody>."
  (let ((table-exists recursion)
	(mark "!-- emacs-w3m-filter ")
	(tbody-end (make-marker))
	tfoots)
    (goto-char (if table-exists (match-end 0) (point-min)))
    (while (or table-exists (re-search-forward "<table[\t\n\r >]" nil t))
      (setq table-exists nil)
      (save-restriction
	(if (w3m-end-of-tag "table")
	    (narrow-to-region (match-beginning 0) (match-end 0))
	  (narrow-to-region (match-beginning 0) (point-max)))
	(goto-char (1+ (match-beginning 0)))
	(insert mark)
	(while (re-search-forward "<table[\t\n\r >]" nil t)
	  (w3m-filter-fix-tfoot-rendering url t))
	(goto-char (point-min))
	(while (search-forward "</tbody>" nil t)
	  (set-marker tbody-end (match-end 0))
	  (goto-char (1+ (match-beginning 0)))
	  (insert mark))
	(unless (bobp)
	  (setq tfoots nil)
	  (goto-char (point-min))
	  (while (re-search-forward "<tfoot[\t\n\r >]" nil t)
	    (when (w3m-end-of-tag "tfoot")
	      (push (match-string 0) tfoots)
	      (delete-region (match-beginning 0) (match-end 0))))
	  (when tfoots
	    (goto-char tbody-end)
	    (dolist (tfoot (nreverse tfoots))
	      (insert "<" mark (substring tfoot 1)))))
	(goto-char (point-max))))
    (set-marker tbody-end nil)
    (unless recursion
      (goto-char (point-min))
      (while (search-forward mark nil t)
	(delete-region (match-beginning 0) (match-end 0))))))

(defun w3m-filter-asahi-shimbun (url)
  "Convert entity reference of UCS."
  (when w3m-use-mule-ucs
    (goto-char (point-min))
    (let ((case-fold-search t)
	  end ucs)
      (while (re-search-forward "alt=\"\\([^\"]+\\)" nil t)
	(goto-char (match-beginning 1))
	(setq end (set-marker (make-marker) (match-end 1)))
	(while (re-search-forward "&#\\([0-9]+\\);" (max end (point)) t)
	  (setq ucs (string-to-number (match-string 1)))
	  (delete-region (match-beginning 0) (match-end 0))
	  (insert-char (w3m-ucs-to-char ucs) 1))))))

(defun w3m-filter-google (url)
  "Insert separator within items."
  (goto-char (point-min))
  (let ((endm (make-marker))
	(case-fold-search t)
	pos beg end)
    (when (and w3m-filter-google-use-utf8
	       (re-search-forward "\
<a class=. href=\"http://\\(www\\|images\\|news\\|maps\\|groups\\)\\.google\\."
				  nil t)
	       (setq pos (match-beginning 0))
	       (search-backward "<table" nil t)
	       (setq beg (match-beginning 0))
	       (search-forward "</table" nil t)
	       (set-marker endm (match-end 0))
	       (< pos (marker-position endm)))
      (goto-char beg)
      (while (re-search-forward "[?&][io]e=\\([^&]+\\)&" endm t)
	(replace-match "UTF-8" nil nil nil 1))
      (setq end (marker-position endm)))
    (when (string-match "\\`http://www\\.google\\.[^/]+/search\\?" url)
      (goto-char (point-max))
      (when (and w3m-filter-google-use-ruled-line
		 (search-backward "<div class=" end t)
		 (search-forward "</div>" nil t))
	(insert w3m-filter-google-separator))
      (if w3m-filter-google-use-ruled-line
	  (while (search-backward "<div class=" end t)
	    (insert w3m-filter-google-separator))
	(while (search-backward "<div class=" end t)
	  (insert "<p>"))))))

(defun w3m-filter-amazon (url)
  "Insert Amazon short URIs."
  (when (string-match w3m-filter-amazon-regxp url)
    (let* ((base (match-string 1 url))
	   (asin (match-string 2 url))
	   (shorturls `(,(concat base "/dp/" asin "/")
			,(concat base "/o/ASIN/" asin "/")
			,(concat base "/gp/product/" asin "/")))
	   (case-fold-search t)
	   shorturl)
      (goto-char (point-min))
      (setq url (file-name-as-directory url))
      (when (or (and (not w3m-filter-amazon-short-url-bottom)
		     (search-forward "<body" nil t)
		     (search-forward ">" nil t))
		(and w3m-filter-amazon-short-url-bottom
		     (search-forward "</body>" nil t)
		     (goto-char (match-beginning 0))))
	(insert "\n")
	(while (setq shorturl (car shorturls))
	  (setq shorturls (cdr shorturls))
	  (unless (string= url shorturl)
	    (insert (format "Amazon Short URL: <a href=\"%s\">%s</a><br>\n"
			    shorturl shorturl))))
	(insert "\n")))))

(defun w3m-filter-mixi (url)
  "Direct jump to the external diary."
  (goto-char (point-min))
  (let (newurl)
    (while (re-search-forward "<a href=\"?view_diary\\.pl\\?url=\\([^>]+\\)>"
			      nil t)
      (setq newurl (match-string 1))
      (when newurl
	(delete-region (match-beginning 0) (match-end 0))
	(when (string-match "&owner_id=[0-9]+\"?\\'" newurl)
	  (setq newurl (substring newurl 0 (match-beginning 0))))
	(insert (format "<a href=\"%s\">"
			(w3m-url-readable-string newurl)))))))

(defun w3m-filter-alc (url)
  (let ((baseurl "http://eow.alc.co.jp/%s/UTF-8/")
	curl cword beg tmp1)
    (when (string-match "\\`http://eow\\.alc\\.co\\.jp/\\([^/]+\\)/UTF-8/" url)
      (setq curl (match-string 0 url))
      (setq cword (match-string 1 url))
      (setq cword (car (split-string (w3m-url-decode-string cword 'utf-8)
				     " ")))
      (goto-char (point-min))
      (while (search-forward "データの転載は禁じられています" nil t)
	(delete-region (line-beginning-position) (line-end-position))
	(insert "<br>"))
      (goto-char (point-min))
      (when (search-forward "<body" nil t)
	(forward-line 1)
	(insert "<h1>英辞朗 on the WEB<h1>\n")
	(setq beg (point))
	(when (search-forward "<!-- ▼検索文字列 -->" nil t)
	  (forward-line 1)
	  (delete-region beg (point)))
	(when (search-forward "<!-- ▼ワードリンク 履歴 -->" nil t)
	  (forward-line 1)
	  (setq beg (point))
	  (when (search-forward "</body>" nil t)
	    (delete-region beg (match-beginning 0))))
	(insert "<br>＊データの転載は禁じられています。")
	;; next/previous page
	(goto-char (point-min))
	(while (re-search-forward
		"<a href='javascript:goPage(\"\\([0-9]+\\)\")'>"
		nil t)
	  (setq tmp1 (match-string 1))
	  (delete-region (match-beginning 0) (match-end 0))
	  (insert (format "<a href=\"%s?pg=%s\">" curl tmp1)))
	;; wordlink
	(goto-char (point-min))
	(while (re-search-forward
		"<span class=\"wordlink\">\\([^<]+\\)</span>"
		nil t)
	  (setq tmp1 (match-string 1))
	  (delete-region (match-beginning 0) (match-end 0))
	  (insert (format "<a href=\"%s\">%s</a>" (format baseurl tmp1) tmp1)))
	;; goGradable/goFairWord
	(goto-char (point-min))
	(while (re-search-forward
		"<a href='javascript:\\(goGradable\\|goFairWord\\)(\"\\([^\"]+\\)\")'>"
		nil t)
	  (setq tmp1 (match-string 2))
	  (delete-region (match-beginning 0) (match-end 0))
	  (insert (format "<a href=\"%s\">" (format baseurl tmp1))))
	;; remove spacer
	(goto-char (point-min))
	(while (search-forward "img/spacer.gif" nil t)
	  (delete-region (line-beginning-position) (line-end-position)))
	(goto-char (point-min))
	;; remove ワードリンク
	(when (search-forward "alt=\"ワードリンク\"" nil t)
	  (delete-region (line-beginning-position) (line-end-position)))
	;; 全文を表示するは無理
	(goto-char (point-min))
	(while (re-search-forward
		(concat "<br */> *⇒<strong>"
			"<a href='javascript:goFullText(\"[^\"]+\", \"[^\"]+\")'>"
			"全文を表示する</a>")
		nil t)
	  (delete-region (match-beginning 0) (match-end 0)))
	;; Java Document write... ;_;
	;; (while (re-search-forward
	;; 	"<a href='javascript:goFullText(\"\\([^\"]+\\)\", \"\\([^\"]+\\)\")'>"
	;; 	nil t)
	;;   (setq tmp1 (match-string 1))
	;;   (setq tmp2 (match-string 2))
	;;   (delete-region (match-beginning 0) (match-end 0))
	;;   ;; &dk=JE, &dk=EJ
	;;   (insert (format "<a href=\"%s?ref=ex&exp=%s&dn=%s&dk=%s\">"
	;; 		  curl tmp1 tmp2
	;; 		  (if (string-match "\\Cj" cword) "JE" "EJ"))))
	))))

(defun w3m-filter-imepita (url)
  "JavaScript emulation."
  (goto-char (point-min))
  (let (tmp)
    (when (re-search-forward
	   (concat "<script><!--\ndocument.write('\\([^\n]*\\)');\r\n//--></script>\n"
		   "<noscript>.*</noscript>")
	   nil t)
      (setq tmp (match-string 1))
      (delete-region (match-beginning 0) (match-end 0))
      (insert tmp))))

(defun w3m-filter-iframe (url)
  (goto-char (point-min))
  (while (re-search-forward "<iframe [^>]*src=\"\\([^\"]*\\)\"[^>]*>" nil t)
    (insert (concat "[iframe:<a href=\"" (match-string 1) "\">" (match-string 1) "</a>]"))))

(defun w3m-filter-allatanys (url)
  "JavaScript emulation."
  (goto-char (point-min))
  (let (aturl atexpurl)
    (if (re-search-forward
	 (concat "<body[ \t\r\f\n]+onload=\"window\\.top\\.location\\.replace('"
		 w3m-html-string-regexp
		 "');\">")
	 nil t)
	(progn
	  (setq aturl (match-string 1))
	  (setq atexpurl (w3m-expand-url aturl url))
	  (delete-region (match-beginning 0) (match-end 0))
	  (insert "<body>\n"
		  "<hr>"
		  "Body has a <b>url=window.top.location.replace()</b><br><br>\n"
		  (format "Goto: <a href=%s>%s</a>\n" aturl atexpurl)
		  "<hr>")
	  (goto-char (point-min))
	  (insert (format "<meta HTTP-EQUIV=\"Refresh\" CONTENT=\"0;URL=%s\">\n"
			  aturl)))
      (while (re-search-forward (concat "<a[ \t\r\l\n]+href=\"javascript:[^(]+('"
					"\\([^']+\\)')\">")
				nil t)
	(setq aturl (match-string 1))
	(delete-region (match-beginning 0) (match-end 0))
	(insert (format "<a href=\"%s\">" aturl))))))

(defun w3m-filter-wikipedia (url)
  "Make anchor reference to work."
  (goto-char (point-min))
  (let (matched-text refid)
    (while (re-search-forward 
	    "<\\(?:sup\\|cite\\) id=\"\\([^\"]*\\)\"" nil t)
      (setq matched-text (match-string 0)
	    refid        (match-string 1))
      (delete-region (match-beginning 0) (match-end 0))
      (insert (format "<a name=\"%s\"></a>%s" refid matched-text)))))

;;; w3m-filter.el ends here
