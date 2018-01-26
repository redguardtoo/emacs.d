;;; bookmark+-doc.el - Documentation for package Bookmark+.
;;
;; Filename: bookmark+-doc.el
;; Description: Documentation for package Bookmark+
;; Author: Drew Adams
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2017, Drew Adams, all rights reserved.
;; Created: Fri Sep 15 07:58:41 2000
;; Last-Updated: Sat Nov 11 10:24:36 2017 (-0800)
;;           By: dradams
;;     Update #: 15243
;; URL: https://www.emacswiki.org/emacs/download/bookmark%2b-doc.el
;; Doc URL: http://www.emacswiki.org/BookmarkPlus
;; Keywords: bookmarks, bookmark+, placeholders, annotations, search,
;;           info, url, eww, w3m, gnus
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Documentation for the Bookmark+ package, which provides
;;    extensions to standard library `bookmark.el'.
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) library
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit.el' - (optional) code for highlighting bookmarks
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (bmenu)
;;    `bookmark+-1.el'   - other required code (non-bmenu)
;;    `bookmark+-key.el' - key and menu bindings
;;
;;    `bookmark+-doc.el' - documentation (comment-only - this file)
;;    `bookmark+-chg.el' - change log (comment-only file)
;;
;;    The documentation includes how to byte-compile and install
;;    Bookmark+.  It is also available in these ways:
;;
;;    1. From the bookmark list (`C-x p e' or `C-x r l'):
;;       Use `?' to show the current bookmark-list status and general
;;       help, then click link `Doc in Commentary' or link `Doc on the
;;       Web'.
;;
;;    2. From the Emacs-Wiki Web site:
;;       http://www.emacswiki.org/BookmarkPlus.
;;    
;;    3. From the Bookmark+ group customization buffer:
;;       `M-x customize-group bookmark-plus', then click link
;;       `Commentary'.
;;
;;    (The commentary links in #1 and #3 work only if put you this
;;    library, `bookmark+-doc.el', in your `load-path'.)
;;
;;    More Bookmark+ description below.
;;
;;    To report Bookmark+ bugs: `M-x customize-group bookmark-plus'
;;    and then follow (e.g. click) the link `Send Bug Report', which
;;    helps you prepare an email to me.
;;
;;
;;    ****** NOTE ******
;;
;;      On 2010-06-18, I changed the prefix used by package Bookmark+
;;      from `bookmarkp-' to `bmkp-'.  THIS IS AN INCOMPATIBLE CHANGE.
;;      I apologize for the inconvenience, but the new prefix is
;;      preferable for a number of reasons, including easier
;;      distinction from standard `bookmark.el' names.
;;
;;      This change means that YOU MUST MANUALLY REPLACE ALL
;;      OCCURRENCES of `bookmarkp-' by `bmkp-' in the following
;;      places, if you used Bookmark+ prior to this change:
;;
;;      1. In your init file (`~/.emacs') or your `custom-file', if
;;         you have one.  This is needed if you customized any
;;         Bookmark+ features.
;;
;;      2. In your default bookmark file, `bookmark-default-file'
;;         (`~/.emacs.bmk'), and in any other bookmark files you might
;;         have.
;;
;;      3. In your `*Bookmark List*' state file,
;;         `bmkp-bmenu-state-file' (`~/.emacs-bmk-bmenu-state.el').
;;
;;      4. In your `*Bookmark List*' commands file,
;;         `bmkp-bmenu-commands-file' (`~/.emacs-bmk-bmenu-commands.el'),
;;         if you have one.
;;
;;      You can do this editing in a virgin Emacs session (`emacs
;;      -Q'), that is, without loading Bookmark+.
;;
;;      Alternatively, you can do this editing in an Emacs session
;;      where Bookmark+ has been loaded, but in that case you must
;;      TURN OFF AUTOMATIC SAVING of both your default bookmark file
;;      and your `*Bookmark List*' state file.  Otherwise, when you
;;      quit Emacs your manually edits will be overwritten.
;;
;;      To turn off this automatic saving, you can use `M-~' and
;;      `C-M-~' in buffer `*Bookmark List*' (commands
;;      `bmkp-toggle-saving-bookmark-file' and
;;      `bmkp-toggle-saving-menu-list-state' - they are also in the
;;      `Bookmark+' menu).
;;
;;      Again, sorry for this inconvenience.
 
;;(@> "Index")
;;
;;  Index
;;  -----
;;
;;  If you have library `linkd.el' and Emacs 22 or later, load
;;  `linkd.el' and turn on `linkd-mode' now.  It lets you easily
;;  navigate around the sections of this doc.  Linkd mode will
;;  highlight this Index, as well as the cross-references and section
;;  headings throughout this file.  You can get `linkd.el' here:
;;  http://www.emacswiki.org/emacs/download/linkd.el.
;;
;;  (@> "Documentation")
;;    (@> "Installing Bookmark+")
;;      (@> "Bookmark+ Load Order and Option `bookmark-default-file'")
;;    (@> "Bookmark+ Features")
;;    (@> "Bookmark Basics")
;;    (@> "Different Types of Jump Commands")
;;    (@> "Bookmark Annotations")
;;    (@> "Bookmark Tags")
;;      (@> "Bookmark Tags Can Have Values")
;;      (@> "Hierarchical Structures of Bookmarks?")
;;    (@> "Function, Sequence, Variable-List,... Bookmarks")
;;      (@> "Little Persistent Named Nothings")
;;    (@> "Editing Bookmarks")
;;      (@> "Bookmark Records: What A Bookmark Looks Like")
;;    (@> "Bookmark-List Views - Saving and Restoring State")
;;      (@> "Quitting Saves the Bookmark-List State")
;;      (@> "State-Restoring Commands and Bookmarks")
;;    (@> "Bookmarking without Visiting the Target")
;;      (@> "Bookmarking a File or a URL")
;;      (@> "Bookmarking the Marked Files in Dired")
;;      (@> "Bookmarking Compilation, Grep, and Occur Hits")
;;      (@> "Bookmarking Files That You Cannot Visit with Emacs")
;;      (@> "Opening Bookmarks Using Windows File Associations")
;;      (@> "Autofile Bookmarks")
;;      (@> "A Type-Aware `find-file'")
;;    (@> "Tagging Files")
;;    (@> "Using Multiple Bookmark Files")
;;      (@> "Bookmark-File Bookmarks")
;;    (@> "The Bookmark List Display")
;;      (@> "Jumping To Bookmarks from the Bookmark List Display")
;;      (@> "Tag Commands and Keys")
;;      (@> "Tags: Sets of Bookmarks")
;;      (@> "Open Dired for the Marked File Bookmarks")
;;      (@> "Marking and Unmarking Bookmarks")
;;      (@> "Filtering Bookmarks (Hiding and Showing)")
;;      (@> "Only Visible Bookmarks Are Affected")
;;      (@> "Omitting Bookmarks from Display")
;;      (@> "Sorting Bookmarks")
;;    (@> "Bookmarks for Specific Files or Buffers")
;;    (@> "Cycling, Navigation List")
;;      (@> "The Bookmark Navigation List")
;;      (@> "Cycling the Navigation List")
;;      (@> "Cycling Dynamic Sets of Bookmarks")
;;      (@> "Cycling in the Current File/Buffer")
;;    (@> "Autonamed Bookmarks - Easy Come Easy Go")
;;    (@> "Temporary Bookmarks")
;;      (@> "Temporary Bookmarking Mode")
;;      (@> "Making Bookmarks Temporary")
;;    (@> "Automatic Bookmarking")
;;      (@> "Automatic Info Bookmarking")
;;      (@> "Automatic Idle-Period Bookmarking")
;;    (@> "Highlighting Bookmark Locations")
;;      (@> "Defining How to Highlight")
;;      (@> "Highlighting On Demand")
;;      (@> "Highlighting Automatically")
;;    (@> "Using Highlighted Bookmarks")
;;    (@> "Bookmark Links")
;;      (@> "Org Mode Links that Jump To Bookmarks")
;;    (@> "Use Bookmark+ with Icicles")
;;    (@> "Bookmark Compatibility with Vanilla Emacs (`bookmark.el')")
;;    (@> "New Bookmark Structure")
 
;;(@* "Documentation")
;;
;;  Documentation
;;  -------------
;;
;;(@* "Installing Bookmark+")
;;  ** Installing Bookmark+ **
;;
;;  The main Bookmark+ library is `bookmark+.el'.  The other required
;;  libraries are `bookmark+-mac.el', `bookmark+-bmu.el',
;;  `bookmark+-1.el', and `bookmark+-key.el'.  If you want to be able
;;  to highlight bookmarks then you will also need library
;;  `bookmark+-lit.el'.  I recommend that you byte-compile all of the
;;  libraries, after loading the source files (in particular, load
;;  `bookmark+-mac.el').
;;
;;  Put the directory of these libraries in your `load-path' and add
;;  this to your init file (~/.emacs):
;;
;;  (require 'bookmark+)
;;
;;  That will load all of the Bookmark+ libraries.  If you do not care
;;  about bookmark highlighting then simply do not put
;;  `bookmark+-lit.el' in your `load-path'.
;;
;;  By default (see option `bmkp-crosshairs-flag'), when you visit a
;;  bookmark that has no region it is highlighted temporarily using
;;  crosshairs, for easy recognition.  (This temporary highlighting is
;;  independent of the highlighting provided by `bookmark+-lit.el'.)
;;
;;  For this optional crosshairs feature you also need library
;;  `crosshairs.el', which in turn requires libraries `col-highlight',
;;  `hl-line', `hl-line+', and `vline'.  Library `hl-line' comes with
;;  vanilla Emacs.  The others are available from the Emacs Wiki web
;;  site: http://www.emacswiki.org/.  You also need Emacs 22 or later
;;  for this feature.
;;
;;
;;(@* "Bookmark+ Load Order and Option `bookmark-default-file'")
;;  *** Bookmark+ Load Order and Option `bookmark-default-file' ***
;;
;;  Standard option `bookmark-default-file' defines the default
;;  location of your bookmark file.  Bookmark+ does not change the
;;  value.  You can change the value, of course, either by customizing
;;  it (recommended) or using Lisp code (including in your init file).
;;
;;  However, the value of `bookmark-default-file' is used when you
;;  load Bookmark+ to initialize some other variables, in particular
;;  option `bmkp-last-as-first-bookmark-file' and internal variable
;;  `bmkp-current-bookmark-file'.
;;
;;  This means that if you modify `bookmark-default-file' in your init
;;  file, and you want your new value to be take into account by
;;  Bookmark+, then modify it before you load Bookmark+.
;;
;;  Be aware also that another library that you load might, itself,
;;  load Bookmark+, in which case you will for the same reason want to
;;  load that library after you have modified `bookmark-default-file'.
;;  An example of this is Icicles, which loads Bookmark+ if Bookmark+
;;  is in your `load-path'.
;;
;;  In general, with Bookmark+ I recommend that you simply set option
;;  `bookmark-default-file' once and for all at the outset, preferably
;;  by customizing it.  You can use `bmkp-switch-bookmark-file-create'
;;  at any time to switch to a different bookmark file - it is bound
;;  to `C-x p L'.  You can also invoke it in your init file, provided
;;  Bookmark+ has already been loaded.
;;
;;  See Also: (@> "Using Multiple Bookmark Files")
 
;;(@* "Bookmark+ Features")
;;  ** Bookmark+ Features **
;;
;;  Here is an overview of some of the features that Bookmark+
;;  provides.  Some of these are detailed in other sections, below.
;;
;;  * Richer bookmarks.  They record more.  They are more accurate.
;;
;;     - An optional bookmark annotation is user-supplied text that is
;;       saved as part of the bookmark.  You can use any text you
;;       like, and you can use it for any purpose you like.  In
;;       Bookmark+, the mode for viewing and editing a bookmark
;;       annotation is Org mode, by default.
;;
;;     - In addition, Bookmark+ lets you optionally use a separate
;;       file, URL, or bookmark to annotate any bookmark.  Accessing
;;       ("showing") such an external annotation visits its
;;       destination.  So for example, you can use bookmarks to one or
;;       more Org files to annotate one or more bookmarks.  The
;;       annotation saved with the bookmark itself just specifies the
;;       destination.  See (@> "Bookmark Annotations").
;;
;;     - You can tag bookmarks, a la del.icio.us.  In effect, tags
;;       define bookmark sets.  A bookmark can have any number of
;;       tags, and multiple bookmarks can have the same tag.  You can
;;       sort, show/hide, or mark bookmarks based on their tags.
;;
;;     - Bookmark+ tags can be more than just names.  They can be
;;       full-fledged user-defined attributes, with Emacs-Lisp objects
;;       as their values.
;;
;;     - You can have multiple bookmarks with the same name.  This is
;;       particularly useful for autofile bookmarks, which are
;;       bookmarks that have the same name as their target files.
;;       They give you the effect of using files themselves as
;;       bookmarks.  In particular, they let you, in effect, tag
;;       files.  See (@> "Autofile Bookmarks") and
;;       (@> "Tagging Files").
;;
;;       (In vanilla Emacs you can also, in theory, have multiple
;;       bookmarks with the same name.  But you cannot really use them
;;       in any practical way.  Vanilla Emacs cannot distinguish among
;;       them: the most recent one shadows all others with the same
;;       name.)
;;
;;     - Bookmarks record the number of times you have visited them
;;       and the time of the last visit.  You can sort, show/hide, or
;;       mark bookmarks based on this info.
;;
;;     - You can combine bookmarks, to make composite, or sequence,
;;       bookmarks.  Invoking a sequence bookmark invokes each of its
;;       component bookmarks in turn.  A component bookmark can itself
;;       be a sequence bookmark.
;;
;;     - You can bookmark a region of text, not just a position.  When
;;       you jump to a bookmark that records a region, the region is
;;       activated (see option `bmkp-use-region').  (Region activation
;;       is not supported for Gnus bookmarks.)
;;
;;       You can define your own region handler for bookmarks that
;;       record regions.  (This is in addition to being able to define
;;       bookmark handlers.)  Use option `bmkp-handle-region-function'
;;       for this.  As one example, command
;;       `bmkp-region-jump-narrow-indirect-other-window' binds the
;;       option to a function that narrows the targeted region in a
;;       cloned indirect buffer.  (You need library
;;       `narrow-indirect.el' for this command.)
;;
;;     - Bookmarks are relocated better than for vanilla Emacs when
;;       the contextual text changes.
;;
;;  * Additional types of bookmarks.
;;
;;     - Autofile bookmarks.  You can bookmark a file without visiting
;;       it or naming the bookmark.  The bookmark name is the same as
;;       the file name (non-directory part).  You can have multiple
;;       such bookmarks with the same name, to bookmark files with the
;;       same name but in different directories.
;;
;;     - Dired bookmarks.  You can bookmark a Dired buffer, recording
;;       and restoring its `ls' switches, which files are marked,
;;       which subdirectories are inserted, and which (sub)directories
;;       are hidden.
;;
;;     - Dired-tree bookmarks.  A set of Dired bookmarks that
;  ;     represent a directory hierarchy and are opened together.
;;
;;     - Bookmark-list bookmarks.  You can bookmark the current state
;;       of buffer `*Bookmark List*' - a list of bookmarks.  Jumping
;;       to such a bookmark restores the recorded sort order,
;;       markings, filter, title, and omit list.
;;       See (@> "Omitting Bookmarks from Display").
;;
;;     - Bookmark-file bookmarks.  You can bookmark a bookmark file.
;;       Jumping to such a bookmark loads the bookmarks in the file.
;;       See (@> "Bookmark-File Bookmarks").
;;
;;     - Desktop bookmarks.  You can bookmark the current Emacs
;;       desktop, as defined by library `desktop.el' - use command
;;       `bmkp-set-desktop-bookmark' (`C-x p K').  You can "jump" to a
;;       desktop bookmark (that is, restore its saved desktop).  A
;;       desktop includes:
;;
;;         - Some global variables.  To exclude variables normally
;;           saved, see option `bmkp-desktop-no-save-vars'.
;; 	   - The current set of buffers and their associated files.
;;           For each: its mode, point, mark, & some local variables.
;;
;;       If option `bmkp-desktop-jump-save-before-flag' is non-`nil',
;;       and if the current desktop was made current by jumping to a
;;       bookmark, then it is saved before jumping to the next
;;       desktop.  If you want to save the last desktop jumped to when
;;       you quit Emacs, then add `bmkp-desktop-save-as-last' to
;;       `kill-emacs-hook'.
;;
;;     - Gnus bookmarks.  You can bookmark a Gnus article, a URL, a
;;       PDF file (DocView), a UNIX manual page (from the output of
;;       Emacs command `man' or `woman'), an image, or a piece of
;;       music.
;;
;;     - Non-file (buffer) bookmarks.  You can bookmark a buffer that
;;       is not associated with a file.
;;
;;     - Function bookmarks.  A bookmark can represent a Lisp
;;       function, which is invoked when you "jump" to the bookmark.
;;
;;     - Sequence (composite) bookmarks.  A bookmark can represent a
;;       sequence of other bookmarks.
;;
;;     - Keyboard-macro bookmarks, bookmarks for sets of keyboard
;;       macros, and sequence bookmarks that combine another bookmark
;;       with a keyboard macro.
;;
;;     - Lisp variable bookmarks.  A bookmark can represent a set of
;;       variables and their values.
;;
;;     - Snippet bookmarks.  Select some some text and give it a
;;       (bookmark) name.  Then copy it to the `kill-ring' anytime, in
;;       any Emacs session.
;;
;;     - Icicles search-hits bookmarks.  (You need library Icicles to
;;       use this feature.)  During Icicles search you can use `C-x
;;       C-M->' to save the current set of completion candidates
;;       (search hits matching your current input) as an Icicles
;;       search-hits bookmark.  During a later Icicles search you can
;;       retrieve those search hits saved in the bookmark, by using
;;       `C-x C-M-<`.  You can add to (instead of replacing) the
;;       current set of hits with hits retrieved from a bookmark using
;;       `C-x C-<'.  This is the only way you can "jump" to such a
;;       bookmark.
;;
;;     In particular, note that you can use the following kinds of
;;     bookmarks to quickly switch among different projects (sets of
;;     bookmarks): Dired, Dired tree, bookmark-list, bookmark-file,
;;     and desktop bookmarks.
;;
;;  * Additional ways to bookmark.
;;
;;     - You can bookmark the file or URL named at point (or any other
;;       file or URL), without first visiting it.
;;
;;     - You can bookmark the targets of the hits in a compilation
;;       buffer or an `occur' buffer, without first visiting them.
;;
;;     - You can bookmark all of the marked files in Dired at once.
;;
;;  * Extensive menus.
;;
;;     - In the `*Bookmark List*' display, a `mouse-3' popup menu has
;;       actions for the individual bookmark that you point to when
;;       you click the mouse.
;;
;;     - In the `*Bookmark List*' display, a complete menu-bar menu,
;;       `Bookmark+', is available.  The same menu is available on
;;       `C-mouse-3'.  It has submenus `Jump To', `Mark', `Omit',
;;       `Show', `Sort', `Tags', `Highlight' (needs library
;;       `bookmark+-lit.el), and `Define Command'.
;;
;;     - The vanilla `Bookmarks' menu, which is typically a submenu of
;;       the menu-bar `Edit' menu, is modified by adding several items
;;       from the `Bookmark+' menu, including submenus `Jump To',
;;       `Tags', and `Highlight'.
;;
;;  * Improvements for the bookmark-list display.
;;
;;    This is buffer `*Bookmark List*', aka the bookmark "menu list"
;;    (a misnomer), which you display using `C-x p e' (or `C-x r l').
;;    See (@> "The Bookmark List Display").
;;
;;     - The last display state is saved (by default), and is restored
;;       the next time you show the list.  (Tip: Use the bookmark list
;;       as your "Home" page at Emacs startup.)
;;
;;     - You can save the current bookmark-list state at any time and
;;       return to it later.  There are a few ways to do this,
;;       including bookmarking the list itself.
;;       See (@> "Bookmark-List Views - Saving and Restoring State").
;;
;;     - Marking/unmarking is enhanced.  It is similar to Dired's.
;;
;;     - You can easily mark or show different classes of bookmarks.
;;
;;     - Faces distinguish bookmarks by type.
;;
;;     - You can sort bookmarks in many ways.  You can easily define
;;       your own sort orders, even complex ones.
;;
;;     - You can regexp-search (`M-a') or query-replace (`M-q') the
;;       targets (destination file or buffers) of the marked
;;       bookmarks, in the current bookmark-list sort order.  For
;;       Emacs 23 and later, you can even search incrementally (`M-s a
;;       C-s', or `M-s a C-M-s' for regexp).
;;
;;     - You can use `M-d >' to open Dired for just the local file
;;       bookmarks that are marked (`>').
;;
;;     - If you use Emacs on Microsoft Windows, you can open bookmarks
;;       according to Windows file associations.  (You will also need
;;       library `w32-browser.el'.)
;;
;;     - You can use (lax) completion when you set a bookmark using
;;       `C-x r m' (`bmkp-bookmark-set-confirm-overwrite'), choosing
;;       from existing bookmarks for the same buffer.  This makes it
;;       easy to update a nearby bookmark (e.g. relocate it).  With a
;;       numeric prefix argument (or if there are no bookmarks for the
;;       buffer), you can choose from all bookmarks.
;;
;;     - You can edit a bookmark: its name and file name/location, its
;;       tags, or its complete defining internal Lisp record.
;;
;;     - The mode line shows the number of bookmarks that are marked
;;       (`>'), flagged for deletion (`D'), tagged (`t'), temporary
;;       (`X'), annotated (`a'), and modified (unsaved) (`*').  It
;;       also shows the current sort order.
;;
;;       For each of the number indicators (e.g., the number marked):
;;
;;       If the current line has the indicator (e.g. `>') and there
;;       are other lines with the same indicator that are listed after
;;       the current line, then the indicator shows `N/M', where N is
;;       the number indicated through the current line and M is the
;;       total number indicated.  Otherwise, it shows just `N'.
;;
;;       This feature is available starting with Emacs 24.3.  (For
;;       prior versions I removed it because Emacs bug #12867 can
;;       cause Emacs to crash.)
;;
;;  * Multiple bookmark files.
;;
;;     - Although vanilla Emacs lets you load different bookmark
;;       files, it does not support this feature well, and the
;;       behavior can even be contradictory.  With Bookmark+ you can
;;       easily (a) switch among alternative bookmark files or (b)
;;       load multiple files into the same session, accumulating their
;;       bookmark definitions.  The last file you used is the default
;;       when you choose a file to switch to, so it is easy to go back
;;       and forth between two bookmark files.
;;       See (@> "Using Multiple Bookmark Files").
;;
;;  * Type-specific jump commands.
;;
;;     - When you want to jump to a bookmark of a specific type
;;       (e.g. Dired), you can use a command that offers only such
;;       bookmarks as completion candidates.
;;
;;  * Dedicated keymaps as prefix keys.
;;
;;     - Prefix `C-x p' is used for bookmark keys, in general.  The
;;       vanilla keys on prefix `C-x r' are still available also, but
;;       that prefix is shared with register commands, making it less
;;       convenient for bookmarks.  Using `C-x p' lets you focus on
;;       bookmarks.
;;
;;     - Prefix `C-x p c' is for setting various kinds of bookmarks.
;;
;;     - Prefixes `C-x j' and `C-x 4 j' (for other-window) are used
;;       for bookmark jump commands.  Again, a dedicated prefix key
;;       helps you focus on one kind of action (jumping).
;;
;;     All of these prefix keys correspond to prefix-map variables, so
;;     you need not use these particular prefixes.  You can bind these
;;     maps to any prefix keys you want.  These are the maps, together
;;     with their predefined bindings.
;;
;;       `bookmark-map'               - `C-x p'
;;       `bmkp-set-map'               - `C-x p c'
;;       `bmkp-tags-map'              - `C-x p t'
;;       `bmkp-jump-map'              - `C-x j'
;;       `bmkp-jump-other-window-map' - `C-x 4 j'
;;
;;     Those are the prefix keys that are available by default.  To
;;     change them, just customize these user options, each of which
;;     is a list of the key sequences to use as prefix key.
;;
;;     - `bmkp-bookmark-map-prefix-keys'          - default: ("^Xp")
;;     - `bmkp-jump-map-prefix-keys'              - default: ("^Xj")
;;     - `bmkp-jump-other-window-map-prefix-keys' - default: ("^X4j")
;;
;;     (`^X' here is actually the Control-X character.)
;;
;;     Keymaps `bmkp-set-map' and `bmkp-tags-map' are always on
;;     `bookmark-map', whatever prefix keys it is on.  So if, for
;;     example, you customize `bmkp-bookmark-map-prefix-keys' to be
;;     ("^Xp" [f9]) then the keys in `bmkp-set-map' have both prefix
;;     `C-x p c' and prefix `<f9> c'.
;;
;;     In addition to keys on Bookmark+ keymaps, Bookmark+ binds some
;;     mode-specific bookmarking commands in some other modes: Occur,
;;     Compilation (including Grep), Buffer-menu, EWW, Gnus, Info,
;;     Man, Woman, W3M, and Dired (if you use library `Dired+').
;;     These keys let you set or jump to bookmarks specific to the
;;     modes.
;;
;;  * Helpful help.
;;
;;     - Information about individual bookmarks.
;;
;;       . Anywhere in Emacs, `C-x p ?'  (command
;;         `bmkp-describe-bookmark') describes any bookmark.  With a
;;         prefix argument, it shows you the full information that
;;         defines it (internal form).
;;
;;       . In the bookmark list, `C-h RET' (or `C-h C-RET') describes
;;         the bookmark under the cursor.  The description is as
;;         complete as possible - for example, for an image-file
;;         bookmark the complete EXIF image metadata is shown.  (This
;;         is only for Emacs 22 and later, and only if you have
;;         command-line tool `exiftool' installed.  See standard Emacs
;;         library `image-dired.el' for more information about
;;         `exiftool'.)
;;
;;         And again, a prefix arg (`C-u C-h RET') means show the full
;;         (internal) bookmark information.
;;
;;         `C-h >' shows the same information that `C-h RET' shows,
;;         but for all of the marked bookmarks, in the current sort
;;         order.  That is, it describes each of the marked bookmarks.
;;
;;         `C-down' and `C-up' move the cursor down and up a line,
;;         respectively, but they also show the description of the
;;         bookmark corresponding to the new cursor location.  This is
;;         a quick way to cycle among bookmark descriptions, in the
;;         current sort order.
;;
;;     - General Bookmark+ documentation.
;;
;;       . Anywhere in Emacs, `M-x bmkp-bmenu-mode-status-help' shows
;;         detailed information about the current state of the
;;         bookmark list.  Click button `Doc in Commentary' or button
;;         `Doc on the Web' to access the complete documentation.
;;
;;         (Use button `Customize' to customize all Bookmark+
;;         faces and options.)
;;
;;       . In the bookmark list, `?' and `C-h m' are the same as `M-x
;;         bmkp-bmenu-mode-status-help'.  (`C-h m' in the bookmark
;;         list does not show you info about minor modes.  If you want
;;         that, use `M-x describe-mode'.)
;;
;;       . In the `bookmark-plus' group customization buffer (`M-x
;;         customize-group bookmark-plus'), click button `Commentary'.
;;
;;       . From the Emacs-Wiki Web site,
;;         http://www.emacswiki.org/BookmarkPlus.
;;
;;     - It is easy to recognize orphaned and invalid bookmarks.
;;
;;       . Invalid bookmarks are shown in a special face in the
;;         bookmark-list display.
;;
;;       . You can easily mark all of the orphaned bookmarks, that is,
;;         those whose recorded files have been renamed or deleted.
;;         You can then relocate or delete those bookmarks.
;;
;;     - It is easy to recognize modified (i.e., unsaved) bookmarks.
;;       They are marked with `*'.  Likewise, bookmarks that have tags
;;       (marked with `t'); bookmarks that have annotations (`a'); and
;;       bookmarks that are temporary (`X'), meaning that they will
;;       not be saved.
;;
;;  * Jump-destination highlighting.
;;
;;     - When you jump to a bookmark, the destination (position) is
;;       highlighted temporarily using crosshairs, to make it stand
;;       out.  Option `bmkp-crosshairs-flag' controls this, and this
;;       feature is available only if you also use library
;;       `crosshairs.el'.
;;
;;  * Visual bookmarks (highlighting).
;;
;;     - You can highlight the locations of bookmarks, either
;;       automatically or on demand.  You control what kind of
;;       highlighting, if any, is used for which bookmarks.  This
;;       feature requires that you have library `bookmark+-lit.el' in
;;       your `load-path' (it will then be loaded by `bookmark+.el).
;;
;;  * Better, user-configurable bookmark-name defaults.
;;
;;     See the doc strings of command `bookmark-set' (Bookmark+
;;     version) and options `bmkp-new-bookmark-default-names' and
;;     `bmkp-default-bookmark-name'.
;;
;;  * Synergy with `Icicles'.
;;
;;     - `Icicles' works with Bookmark+ to provide enhanced bookmark
;;       jumping (visiting), setting, and help.  It gives you a
;;       bookmark browser, and lets you bookmark and tag files on the
;;       fly.  See (@> "Use Bookmark+ with Icicles") and
;;       http://www.emacswiki.org/Icicles.
 
;;(@* "Bookmark Basics")
;;  ** Bookmark Basics **
;;
;;  Bookmark+ builds on vanilla Emacs bookmarks.  If you are familiar
;;  with the latter, then you can skip this section, which mostly
;;  reviews the former.  However, this section also introduces some
;;  Bookmark+ concepts and features that are detailed in other
;;  sections.
;;
;;  In Emacs bookmarking these three things are different but related:
;;
;;  1. the bookmark list
;;  2. the bookmark file
;;  3. the bookmark-list display (buffer `*Bookmark List*', aka the
;;     bookmark "menu list", a misnomer)
;;
;;  It is important to keep these three straight and understand their
;;  differences in practice, in particular, when they do and do not
;;  represent the same set of bookmarks.
;;
;;  #1 is in memory.  It is the current set of bookmarks.  When you
;;  add, rename, delete, etc. a bookmark, this list is updated.
;;
;;  #2 is on disk.  It is a persistent record of a set of bookmarks.
;;
;;  The bookmark list (#1) is the current value of internal variable
;;  `bookmark-alist'.  The bookmark file (#2) can be anywhere.  Its
;;  default filename is the value of user option
;;  `bookmark-default-file'.
;;
;;  The bookmark list is typically initialized from the bookmark file
;;  - referred to as loading your bookmarks, but you can also create
;;  bookmarks (adding them to the list) without ever saving them to
;;  disk.
;;
;;  The bookmark list can be saved to the bookmark file - referred to
;;  as saving your bookmarks - either automatically or on demand.  But
;;  it is not necessarily saved.  Even if it has been saved in the
;;  past, that does not mean that at any given time the bookmark list
;;  corresponds exactly to the bookmark file.
;;
;;  The list and the file can often become out of sync.  In an Emacs
;;  session, the bookmark list rules.  After an Emacs session, the
;;  bookmark file rules (it is all there is).  You can use `C-x p L'
;;  (`bmkp-switch-bookmark-file-create') to sync (revert) the list to
;;  reflect the file - just accept the default value, "switching" to
;;  the same file.
;;
;;  The bookmark-list display (#3) is a snapshot view of the bookmarks
;;  in the bookmark list.  As such, what you see there reflects the
;;  state of the bookmark list at some point in time.  So here again,
;;  the two, list and display, can be out of sync.  Hitting `g' in the
;;  bookmark-list display refreshes it to accurately reflect the
;;  current bookmark list (#1).  Some other operations in the display
;;  also keep it synced with the list.
;;
;;  Using a prefix argument (`C-u g') syncs the display (#3) and the
;;  list (#1) to the file (#2).  This can be useful when some other
;;  process (e.g., another Emacs session) updates the bookmark file or
;;  when you want to abandon changes to the current bookmark list and
;;  any of the current bookmarks.  Outside the bookmark-list display,
;;  you can use command `bmkp-revert-bookmark-file' to do this.
;;
;;  You can load different bookmark files, either adding their
;;  bookmarks to those already in the current bookmark list or
;;  replacing them.
;;
;;  The most important takeaway from this section is that #1 (list),
;;  #2 (file), and #3 (display) can be out of sync, and they often
;;  are.  And that can be useful.
;;
;;  Until now, everything said in this section is true of vanilla
;;  Emacs as well as Bookmark+.  Bookmark+ adds some flexibility
;;  regarding the use of multiple bookmark files, and it can save the
;;  last state of the bookmark-list display for later reuse.
;;
;;  The saved state of the display is restored when you show the
;;  display after quitting it (`q') in the same session or quitting
;;  Emacs, but only if the bookmark file whose location it recorded is
;;  the same as the current bookmark file.
;;
;;  It would not make sense to display a completely different set of
;;  bookmarks from those that are currently loaded.  The display must
;;  always reflect the current bookmark list (even if it sometimes
;;  reflects it imperfectly, because it is a snapshot).  So if the
;;  bookmark file that is loaded is different from the one that was
;;  recorded for the display state, the recorded state is ignored.
;;
;;
;;(@* "Automatic Saving")
;;  *** Automatic Saving ***
;;
;;  Before getting into the topic of automatic saving, let me say this
;;  clearly once: BACK UP YOUR BOOKMARK FILE(S)!
;;
;;  (Bookmark+ creates backups when your bookmark file is saved.
;;  Until bug #12507 is fixed, vanilla Emacs does not.)
;;
;;  I recommend that you set option `bookmark-version-control' to `t',
;;  so that you get numbered backups.
;;
;;  If you do use numbered backups then you might also want to
;;  customize option `delete-old-versions', setting the value to `t',
;;  so that you are not bothered by this prompt each time bookmarks
;;  are saved:
;;
;;    Delete excess backup versions of <YOUR-INIT-FILE>? (y or n)
;;
;;  See also nodes `Backup Names' and `Backup Deletion' in the Emacs
;;  manual.
;;
;;  User option `bookmark-save-flag' controls whether and how often to
;;  automatically save the bookmark list to the bookmark file, thus
;;  syncing the two.  You can toggle this option using `M-~' in the
;;  bookmark-list display.
;;
;;  In the bookmark-list display, you can tell whether individual
;;  bookmarks have been modified since the last save: they are marked
;;  with `*'.  I believe that this indication is robust and accurate
;;  (if not, please report a bug), but a word of caution: do not
;;  depend on it.  The only way to be sure that your bookmarks have
;;  been saved is to save them. ;-)
;;
;;  Is there a way to unmodify a single bookmark that you have
;;  changed?  No, not unless it is the only one you modified.  If you
;;  revert to the bookmarks as last saved, then all changes to all
;;  bookmarks (including addition and removal of bookmarks) are lost.
;;  If you want to work carefully when making multiple changes, then
;;  save any modifications you are sure of before you move on to
;;  others.  If only one bookmark is modified then reverting to the
;;  bookmark file effectively unmodifies that bookmark.
;;
;;  When you consult the doc for option `bookmark-save-flag' you see
;;  that besides values of `nil' and `t', meaning off and on, it can
;;  have a value that is the number of bookmark modifications to allow
;;  before automatically saving.  If the value is 10, for instance,
;;  then the 11th modification triggers automatic saving.
;;
;;  But a modification means any change to any bookmark.  Typically,
;;  you are more interested in considering all of the changes caused
;;  by a given command as one modification.  Why?  Suppose you use a
;;  command such as `T > +' (`bmkp-bmenu-add-tags-to-marked'), which
;;  adds a set of tags to each of the marked bookmarks.  Even if there
;;  have been no other modifications since you last saved bookmarks,
;;  if there are more marked bookmarks than your setting of
;;  `bookmark-save-flag' then automatic saving will kick in in the
;;  middle of the command.  Some of the bookmarks with the added tags
;;  will be automatically saved.  And that does not give you an
;;  opportunity to cancel the changes (e.g., by quitting without
;;  saving).
;;
;;  This is the reason for option `bmkp-count-multi-mods-as-one-flag',
;;  whose default value is `t', which means count all of a sequence of
;;  modifications together as one modification, as far as
;;  `bookmark-save-flag' is concerned.
 
;;(@* "Different Types of Jump Commands")
;;  ** Different Types of Jump Commands **
;;
;;  When you jump to a bookmark, you can use completion to specify the
;;  bookmark name.  `bookmark-jump' and `bookmark-jump-other-window',
;;  bound to `C-x j j' and `C-x 4 j j', are general commands.  Their
;;  completion candidates include all of your bookmarks.  With
;;  Bookmark+ you can easily have a large number of bookmarks.
;;
;;  To provide more specificity, Bookmark+ provides many different
;;  bookmark jump commands.  If you want to jump to a bookmark of a
;;  specific type, such as Info, you can use a Bookmark+ command that
;;  is specific to bookmarks of that type: only those bookmarks are
;;  completion candidates.
;;
;;  There are thus type-specific commands: `bmkp-dired-jump',
;;  `bmkp-info-jump', and so on, bound to `C-x j d', `C-x j i', and so
;;  on.  There are also commands to jump to bookmarks for the current
;;  buffer or for particular buffers or files
;;  (see (@> "Bookmarks for Specific Files or Buffers")).
;;
;;  All bookmark jump commands are bound to keys that have the prefix
;;  `C-x j'.  There is an other-window version of most jump commands,
;;  and it is bound to the same key as the same-window command, except
;;  the prefix is `C-x 4 j', not `C-x j'.  For instance,
;;  `bmkp-dired-jump-other-window' is bound to `C-x 4 j d'.
;;
;;  (In the bookmark-list display, you can use just `j' instead of
;;  `C-x 4 j', and just `J' (uppercase) instead of `C-x j'.)
;;
;;  More precisely, the bookmark jump commands are on the prefix maps
;;  `bmkp-jump-map' and `bmkp-jump-other-window-map', which have the
;;  default bindings `C-x j' and `C-x 4 j'.  You can bind these maps
;;  to any keys you like, by customizing options
;;  `bmkp-jump-map-prefix-keys' and
;;  `bmkp-jump-other-window-map-prefix-keys'.
;;
;;  If you do not remember the different type-specfic bindings, you
;;  can use commands `bmkp-jump-to-type' and
;;  `bmkp-jump-to-type-other-window' (`C-x j :' and `C-x 4 j :').
;;  They work for any type, prompting you first for the type, then for
;;  a bookmark of that type (only).
;;
;;  There are several commands for jumping to a bookmark with tags.
;;  The completion candidates can be those bookmarks that have all
;;  tags in a given set, some tags in a given set, all tags matching a
;;  regexp, or some tags matching a regexp.  You are prompted for the
;;  set of tags or the regexp to match.
;;
;;  These commands all have the prefix key `C-x j t'.  The suffix key
;;  is `*' for "all" and `+' for "some".  The regexp-matching commands
;;  precede the suffix key with `%'.  For example, `C-x j t % +' jumps
;;  to a bookmark you choose that has one or more tags that match the
;;  regexp you input.
;;
;;  There are some type-specific jump commands for bookmarks with
;;  tags.  The key sequences for these include a key that indicates
;;  the bookmark type, after the `t' indicating tags.  For example,
;;  commands for jumping to a file or directory bookmark having
;;  certain tags use the prefix `C-x j t f' (`f' for file).  Similar
;;  commands for autofile bookmarks have prefix `C-x j t a' (`a' for
;;  autofile).
;;
;;  For example, `C-x j t f % *' jumps to a file or directory bookmark
;;  you choose, where all of its tags match a regexp, and `C-x j t a
;;  +' finds a file tagged with at least one of the tags you input.
;;
;;  In addition to the ordinary autofile "jump" commands, there are
;;  `find-file' versions: they read a file name using
;;  `read-file-name', instead of completing a bookmark name.  - see
;;  (@> "Autofile Bookmarks").  These commands are available starting
;;  with Emacs 22.
;;
;;  Bookmark names are global.  File names are not; that is, the
;;  non-directory portion is not.  Suppose you have two similar
;;  directories with some like-named files, perhaps tagged in similar
;;  ways.  Imagine image files of your vacations organized in
;;  different directories by year.  It is sometimes useful to narrow
;;  your focus to the file bookmarks in one directory.
;;
;;  Commands such as `bmkp-file-this-dir-jump' (`C-x j . f') offer as
;;  completion candidates only bookmarks for files and subdirs in the
;;  current directory (`default-directory').  For tags, there are
;;  equivalent commands.  For example, `C-x j t . % *' is the same as
;;  `C-x j t f % *', but the destinations are limited to files in the
;;  current directory.  All of the "this-dir" file jump commands are
;;  bound to the same keys as the general file jump commands, but with
;;  `.' instead of `f'.
;;
;;  Remember that Bookmark+ collects lots of commands on only a few
;;  predefined prefix keys, primarily as a mnemonic device.  Nothing
;;  requires you to use the long key sequence `C-x j t f % *' to visit
;;  a file that has a given set of tags.  It is expected that you will
;;  bind short key sequences to commands that you use often.
;;
;;  The `C-x j' and `C-x 4 j' bindings are global.  In addition, in
;;  some modes `j' is bound to the corresponding type-specific jump
;;  command.  For example, in Info mode, `j' is bound to
;;  `bmkp-info-jump'.  (Dired is an exception here: `J' is used
;;  instead of `j', since `j' is already taken for `dired-goto-file'.)
;;  These commands are also added to the mode's menu-bar menu.
;;
;;  In Dired mode, `C-j' is bound to a special Dired-specific jump
;;  command, `bmkp-dired-this-dir-jump', whose destinations all use
;;  the current directory (`default-directory').  The aim of `C-j' is
;;  not to change directories but to change to a different set of
;;  Dired markings, switches, inserted subdirectories, or hidden
;;  subdirectories for the same Dired directory.
;;
;;  In addition to the predefined bookmark types, which you can use as
;;  described above, you can define a "type"-specific jump command for
;;  any set of bookmarks.  That is, you can use any specific set of
;;  bookmarks as the completion candidates for a new jump command.
;;  Such a set is really only a pseudo-type: the actual bookmarks can
;;  each be of any type.
;;
;;  You could use this feature, for example, to define a jump command
;;  for the bookmarks that belong to a given project.
;;
;;  One way to define such a command is to first mark the bookmarks
;;  that you want to be the completion candidates, then use `C-c C-j'
;;  (command `bmkp-bmenu-define-jump-marked-command') in the bookmark
;;  list.
;;
;;  The `*Bookmark List*' display defines a set of bookmarks, even
;;  without markings.  So does each bookmark of type bookmark list,
;;  that is, a bookmark corresponding to a particular `*Bookmark
;;  List*' display state - see
;;  (@> "State-Restoring Commands and Bookmarks").
;;
;;  You can capture the set of bookmarks corresponding to a `*Bookmark
;;  List*' display for use in navigation, that is, as the current
;;  "navigation list".  Navigation here includes jumping and cycling
;;  - see (@> "Cycling, Navigation List").
;;
;;  To capture in the navigation list the bookmarks corresponding to
;;  either the current `*Bookmark List*' display or a bookmark-list
;;  bookmark, use `C-x p B', which is bound to command
;;  `bmkp-choose-navlist-from-bookmark-list'.  To then jump to a
;;  bookmark from such a navigation list, use `C-x j N' or `C-x 4 j N'
;;  (`bmkp-jump-in-navlist' or `bmkp-jump-in-navlist-other-window').
 
;;(@* "Bookmark Annotations")
;;  ** Bookmark Annotations **
;;
;;  With Bookmark+ you can bookmark many kinds of Emacs object.
;;  Bookmarks record locations - that is their primary purpose.  They
;;  can also record annotations: general free-text descriptions of
;;  your choosing.  An annotation is thus metadata that is associated
;;  with a bookmark.  You can use it for any purpose you like.
;;
;;  Command `bookmark-show-annotation' shows an annotation in
;;  read-only mode.  You can use `C-x C-q' in the annotation buffer to
;;  switch to edit mode (and back again).
;;
;;  You can use command `bookmark-edit-annotation' or `bmkp-annotate'
;;  anywhere to edit the annotation for a bookmark.  For
;;  `bookmark-edit-annotation', you can choose among the bookmarks
;;  that already have annotations.  With a prefix arg, you can choose
;;  any bookmark (and so create an annotation).  Using `bmkp-annotate'
;;  is the same as using `bookmark-edit-annotation' with a prefix arg.
;;
;;  In the annotation edit buffer, make your changes and then use `C-c
;;  C-c' to save the result.  Use `C-x C-k' if you do not want to save
;;  the changes.  You can also use `C-x C-q' and then `y' to confirm
;;  reverting the changes.
;;
;;  Non-`nil' user option `bookmark-automatically-show-annotations'
;;  means that a bookmark's annotation is popped up whenever you jump
;;  to the bookmark.  If the non-`nil' value is `edit' then the
;;  annotation buffer is in edit mode; if it is any other non-`nil'
;;  value then the buffer is in show (read-only) mode.
;;
;;  In the `*Bookmark List*' display, you can use `a' to show or (with
;;  a prefix arg) edit the existing annotation for the bookmark on the
;;  current line.  (Bookmarks with annotations are marked by an `a' to
;;  the left of the bookmark name.)
;;
;;  A bookmark annotation is stored as part of the bookmark itself.
;;  For this reason, you typically want to keep the text fairly short.
;;  In Bookmark+, the mode for viewing and editing a bookmark
;;  annotation is Org mode, by default.  (To change the mode used,
;;  customize option `bmkp-annotation-modes-inherit-from'.)
;;
;;  You can obtain the effect of using longer annotations, and some
;;  other advantages as well, by using "external annotations".  These
;;  are annotations that are short and serve only as pointers to
;;  external files, URLs, or other bookmarks.
;;
;;  Whenever you show the annotation of a bookmark (via `a' in the
;;  `*Bookmark List*' display, `bookmark-show-annotation', or
;;  `bookmark-automatically-show-annotations') and the annotation is
;;  such a pointer, the effect is to visit the destination.
;;
;;  So for example, you can use bookmarks to one or more Org files to
;;  annotate (provide metadata for) one or more other bookmarks.
;;
;;  You create an external annotation for a bookmark by using one of
;;  these forms as the annotation text.
;;
;;     bmkp-annot-url: "FILE"
;;     bmkp-annot-url: "URL"
;;     bmkp-annot-url: "BOOKMARK"
;;
;;  * FILE is an absolute file name.  It is handled by
;;    `find-file-other-window'.
;;  * URL is a URL.  It is handled by `browse-url'.
;;  * BOOKMARK is the name of a bookmark in the current bookmark
;;    alist.
;;
;;  The double-quote characters are necessary here, so that you can
;;  include characters such as `SPC' in the name.  The text must be on
;;  the first line of the annotation (not counting the commented
;;  instruction lines).  It can be preceded only by whitespace.
;;
;;  You can include other text in the annotation, after the
;;  destination specification, and you can see or edit it when you
;;  edit the annotation (e.g., using `C-u a' in buffer `*Bookmark
;;  List*'), but it is ignored when the annotation is "shown" (e.g.,
;;  using `a').
;;
;;  In the `*Bookmark List*' display, `M-down' and `M-up' move the
;;  cursor down and up a line, respectively, but they also show the
;;  annotation, if any, of the bookmark at the new cursor location.
 
;;(@* "Bookmark Tags")
;;  ** Bookmark Tags **
;;
;;  In addition to annotating bookmarks with arbitrary metadata,
;;  Bookmark+ bookmarks can also be tagged, as a way to organize them,
;;  which also means as a way to organize the objects that are
;;  bookmarked.
;;
;;  By "tagging" and "tag" in this context is meant associating
;;  keywords or other text with an object, typically in order to
;;  classify or characterize it.  Tags are metadata about an object.
;;  This notion of tagging is sometimes called "delicious" tagging
;;  after the Web site www.delicious.com that popularized it
;;  (`http://en.wikipedia.org/wiki/Delicious_(website)').
;;
;;  Be aware that there is another notion of "tag" associated with
;;  Emacs: that involving Emacs tags files, which record the locations
;;  of function, variable, etc. definitions in source files.  There is
;;  no relation between the two notions of "tag".
;;
;;  A bookmark tag is a string (or a cons whose car is a string - see
;;  (@> "Bookmark Tags Can Have Values")).  You can add as many tags
;;  as you like to any bookmark, and multiple bookmarks can have the
;;  same tag(s).  In fact, that's the whole idea behind using them for
;;  organizing.
;;
;;  This feature is unrelated to the fact that bookmarks record
;;  locations and are useful for navigating.  You can, if you want,
;;  use bookmarks to tag files in various ways purely for purposes of
;;  organizing them (e.g. into projects), whether or not you ever use
;;  the bookmarks as a way to visit them.
;;
;;  For example, if you use `Dired+' (library `dired+.el'), then you
;;  can use `M-b' (`diredp-do-bookmark') in Dired to create an
;;  autofile bookmark for each of the marked files in the Dired
;;  buffer.  Even if you never use those bookmarks for navigating to
;;  the files, you can use them with tags to organize the files and
;;  thus operate on subsets of them.
;;
;;  And if you use libraries `Dired+' and `highlight.el' then
;;  autofiles are highlighted specially in Dired, and the highlighting
;;  indicates whether the file is tagged.
;;
;;  By default, you create bookmarks without tags and add tags to them
;;  later.  If you prefer, you can customize option
;;  `bmkp-prompt-for-tags-flag' to non-`nil' so that you are prompted
;;  to add tags immediately whenever you set (create or update) a
;;  bookmark.  
;;
;;  There are also some commands, such as `bmkp-tag-a-file' (`C-x p t
;;  + a') and `bmkp-untag-a-file' (`C-x p t - a'), that always prompt
;;  for tags to add or remove.  (In general, the key `a' is used in
;;  key sequences for autofile bookmarks.)
;;
;;  When you are prompted to enter a tag, you type some text then hit
;;  `RET'.  If you want to include a newline character in the tag
;;  itself, use `C-q C-j' (`C-j' is the newline character).  You can
;;  use `C-q' this way to enter any character.  If you do use complex
;;  strings as tags then you might prefer to simply edit a bookmark's
;;  tags in a separate buffer.  You can do that using `C-x p t e' (or
;;  `T e' in the bookmark-list display).
;;
;;  Whenever you are prompted for a tag you can use completion.  The
;;  completion candidates available are the tag names defined by
;;  option `bmkp-tags-for-completion'.  The default value of this
;;  option is `current', meaning use only the tags from the bookmarks
;;  in the current bookmark list as candidates.  You can customize the
;;  option to include specific tags or the tags from bookmarks in
;;  specific bookmark files.
;;
;;  You can use command `bmkp-list-all-tags' to list all of the tags
;;  defined by option `bmkp-tags-for-completion' or, with a numeric
;;  prefix argument, only the tags corresponding to the current
;;  bookmark file.  You can list the tag names only or (using a
;;  non-negative prefix arg) show the full tag definitions, which
;;  include any associated tag values (see (@> "Bookmark Tags Can Have Values")
;;  for information about tag values).
;;
;;  To make tags more useful, Bookmark+ provides *lots* of commands:
;;  commands for adding, removing, copying, pasting, and renaming
;;  tags; commands for jumping to bookmarks with particular sets of
;;  tags; and commands for marking or unmarking (in buffer `*Bookmark
;;  List*') bookmarks that are tagged in various ways.
;;
;;  Most commands pertaining to tags are by default on prefix key `C-x
;;  p t' - use `C-x p t C-h' to see them.  In buffer `*Bookmark
;;  List*', commands pertaining to tags are on prefix key `T' - use `T
;;  C-h' to see them.  And remember that you can use `C-h >' to
;;  describe all of the marked bookmarks, in the current sort order.
;;  The bookmark descriptions include the tags.
;;
;;  When combined with other Bookmark+ commands (e.g. search,
;;  query-replace) that apply to the marked bookmarks in the
;;  `*Bookmark List*' window, you can really do quite a lot using
;;  bookmark tags.  Use your imagination!
;;
;;  See Also:
;;
;;  * (@> "Bookmark Records: What A Bookmark Looks Like")
;;  * (@> "Bookmarking the Marked Files in Dired")
;;  * (@> "Opening Bookmarks Using Windows File Associations")
;;  * (@> "Tag Commands and Keys")
;;
;;
;;(@* "Bookmark Tags Can Have Values")
;;  *** Bookmark Tags Can Have Values ***
;;
;;  Bookmark tags are simply names (strings) when you create them.
;;  Nearly all of the predefined operations that use tags use these
;;  names: sorting, marking, jumping, and so on.  But you can in fact
;;  add an associated value to any tag.  This means that a tag can act
;;  just like an object attribute or property: it can be a name/value
;;  pair.
;;
;;  To add a value to a tag that has none, or to change the current
;;  value of a tag, you use command `bmkp-set-tag-value', which is
;;  bound to `T v' in the bookmark list and bound to `C-x p t v'
;;  globally.  You are prompted for the bookmark, the tag, and the new
;;  value.
;;
;;  A tag value can be a number, symbol, string, list, vector, and so
;;  on.  It can be as complex as you like.  It can be any Emacs-Lisp
;;  object that has read syntax, that is, that is readable by the Lisp
;;  reader.  (Everything that is saved as part of a bookmark must be
;;  readable; otherwise, your bookmark file could not be read
;;  (loaded).)
;;
;;  Because tag values can be pretty much anything, you are pretty
;;  much on your own when it comes to making use of them.  Bookmark+
;;  does not provide predefined functions for using tag values.  In
;;  general, tag values are something you will use with home-grown
;;  Lisp code for your own purposes.
;;
;;  However, you can easily make some interactive use of tag values
;;  with little effort.  You can, for example, define a predicate that
;;  tests whether a bookmark has a tag value that satisfies some
;;  property (e.g. is a number greater than 3.14159265358979), and
;;  then you can use command `bmkp-bmenu-mark-bookmarks-satisfying' to
;;  mark those bookmarks.
;;
;;  Tags that have the prefix "bmkp-" are reserved - do not name your
;;  own tags using this prefix.
;;
;;  Currently, "bmkp-jump" is the only predefined bookmark tag.  You
;;  can give this tag a value that is a function - it is called
;;  whenever the tagged bookmark is visited.  Any Lisp-readable
;;  function value is allowed: a symbol or a lambda expression.
;;
;;  For example, to display `Hello!' when a bookmark is visited you
;;  can use this:
;;
;;    T v bookmark-jump RET (lambda () (message "Hello!"))
;;
;;  The function that is the value of a "bmkp-jump" tag is called just
;;  after the the standard hook `bookmark-after-jump-hook' is invoked.
;;  You can use this tag to invoke functions that are specific to
;;  individual bookmarks; bookmarks can thus have their own, extra
;;  jump functions.
;;
;;
;;(@* "Hierarchical Structures of Bookmarks?")
;;  *** Hierarchical Structures of Bookmarks? ***
;;
;;  You can use tags to organize sets of bookmarks in various ways.
;;  But what about a simple, hierarchical (tree-shaped) structure like
;;  the one that you use for bookmarks in a web browser?  You can get
;;  a similar effect with Bookmark+ by just using a tag-naming
;;  convention such as this:
;;
;;  vacation/
;;  vacation/2017/
;;  vacation/2017/winter/
;;  vacation/2017/winter/photos/
;;  vacation/2017/summer/
;;  vacation/2017/summer/photos/
;;  vacation/2018/
;;  ...
;;
;;  You need not tag any bookmarks with any particular part of such a
;;  pseudo-hierarchy.  For example, you might tag some bookmarks with
;;  vacation/2017/winter/ and some with vacation/2017/winter/photos/,
;;  without bothering to have any that are tagged with just vacation/
;;  or just vacation/2017/.
;;
;;  You are not limited to a single tree.  You can have a tag such as
;;  vacation/2017/winter/ and a tag such as work/projects/2017/alpha/,
;;  without any need for those to have a common ancestor.
;;
;;  How can you use such a tagging scheme?
;;
;;  When you jump to a bookmark using a command that asks for tags,
;;  such as `C-x j t +' (`bmkp-some-tags-jump'), you can use
;;  completion.  So you can, for example, type `vac TAB' to show all
;;  of your vacation tags (in `*Completions*'), and drill down,
;;  completing more, to pick whichever particular vacation tag you're
;;  interested in.  This is similar to traversing a web-browser
;;  tree-like bookmarks menu.  But jump commands that use tags let you
;;  match any number of tags at the same time, not just one.
;;
;;  Completion against the set of existing tags is also available when
;;  you add tags to a bookmark.  And if option
;;  `bmkp-prompt-for-tags-flag' is non-`nil' then you are prompted to
;;  add tags whenever you create or update a bookmark.  But unlike the
;;  case for web-browser bookmark creation, classifying a bookmark
;;  when you create it or update it is optional.  You can always add
;;  tags later, or not at all.
;;
;;  Such a purely conventional, pseudo-hierarchy might sound like a
;;  silly hack, but it is at least as quick to use as is adding a
;;  bookmark to your tree of browser bookmarks.  And it is more
;;  useful, because the organization is more flexible and you can have
;;  multiple, independent hierarchies.
;;
;;  The tagging scheme just described can help you keep track of
;;  things, even though it is very simple.  There is nothing special
;;  about it.  You might come up with other conventions for
;;  classifying tags, which you find more convenient or more powerful.
;;  And remember that tags can be more than just names.  They give you
;;  the full power of Lisp values - do with them whatever you like.
 
;;(@* "Function, Sequence, Variable-List,... Bookmarks")
;;  ** Function, Sequence, Variable-List,... Bookmarks **
;;
;;  Bookmarks are typically thought of only as recorded locations.
;;  Invoking a bookmark, called "jumping" to it, traditionally means
;;  just visiting its location.  Bookmark+ looks at bookmarks in a
;;  more general way than that.  A bookmark is a shortcut of some kind
;;  - nothing more.  It is typically persistent, but it need not be
;;  (see (@> "Temporary Bookmarks")).
;;
;;  A given type of bookmark is defined by its handler function, which
;;  can do anything you like.  We've already seen the examples of
;;  region bookmarks, which restore the active region, and Dired
;;  bookmarks, which restore Dired markings, switches, inserted
;;  subdirectories, and hidden (sub)directories.
;;
;;  A "function bookmark" simply invokes some function - any function.
;;  You can, for instance, define a window or frame configuration and
;;  record the configuration as a bookmark.  Then jump to the bookmark
;;  to switch contexts.  (You can also bookmark a desktop and jump to
;;  that.)
;;
;;  Function bookmarks might not seem too interesting, since there are
;;  other ways to invoke functions in Emacs.  But the other features
;;  of Bookmark+ combine with this feature.  You can, for instance,
;;  tag function bookmarks.
;;
;;  And you can combine them, invoking the functions sequentially.
;;  This is a particular case of using a "sequence bookmark", which
;;  simply records a sequence of bookmarks.  The bookmarks in a
;;  sequence can be of any kind, including other sequence bookmarks.
;;
;;  Command `bmkp-make-function-bookmark' (`C-x p c F') creates a
;;  function bookmark - you give it a function symbol or a lambda
;;  expression.
;;
;;  A function bookmark can invoke a keyboard macro instead of a
;;  function.  With a prefix argument, `bmkp-make-function-bookmark'
;;  creates a function bookmark from the last keyboard macro.  Jumping
;;  to the bookmark executes the keyboard macro.  A bookmark is thus
;;  one way to make a keyboard macro persistent.
;;
;;  If you provide a prefix argument to the bookmark jump command or
;;  key that invokes a function bookmark, it is passed along to the
;;  function.  If the bookmark invokes a keyboard macro then the
;;  prefix argument determines how many times the macro is invoked.
;;
;;  The most general way to create or update a sequence bookmark is
;;  using command `bmkp-set-sequence-bookmark' (`C-x p c s').  You are
;;  prompted for the sequence bookmark name and the names of the
;;  bookmarks that form its sequence and are thus invoked by it
;;  sequentially.
;;
;;  If the sequence bookmark already exists then a prefix argument
;;  determines whether the bookmarks you name are added to the
;;  existing sequence or replace it, and if added, whether before or
;;  after the bookmarks already in the sequence.
;;
;;  Command `bmkp-wrap-bookmark-with-last-kbd-macro' (`C-x p c C-k')
;;  returns a sequence bookmark that invokes a bookmark you name and
;;  then invokes the last keyboard macro.  You are prompted for the
;;  names of both bookmarks.  If the sequence bookmark does not yet
;;  exist then it is created.  (The bookmark to be added to the
;;  sequence need not exist yet, and it is not created by adding its
;;  name to the sequence.)
;;
;;  If you enter the same name for the sequence bookmark and the
;;  bookmark to wrap with the keyboard macro, then the macro is simply
;;  added to that (sequence) bookmark.
;;
;;  For example, if you enter `my-seq' for both of the
;;  `bmkp-wrap-bookmark-with-last-kbd-macro' prompts, then the last
;;  keyboard macro is added to sequence bookmark `my-seq'. Bookmark
;;  `my-seq' need not exist yet, in which case it is created, with the
;;  keyboard macro as its only member bookmark.
;;
;;  If the bookmark to add to the sequence is itself a different
;;  (existing) sequence bookmark, then its member bookmarks are added
;;  to the sequence being updated (or created), either before or after
;;  its existing members, according to the prefix arg (which is passed
;;  to `bmkp-set-sequence-bookmark').
;;
;;  Command `bmkp-bmenu-make-sequence-from-marked' creates a sequence
;;  bookmark from the marked bookmarks in the bookmark-list display,
;;  in their current order.
;;
;;  If you use library `Dired+' (`dired+.el') then you can use command
;;  `diredp-do-bookmark-dirs-recursive' to create a Dired bookmark for
;;  the current Dired buffer and each of its marked subdirectories.
;;  Each of those subdirectories is handled similarly, and so on,
;;  recursively.  This command also creates a sequence bookmark that
;;  includes all of these Dired bookmarks, so that it represents a
;;  tree (hierarchy) of Dired buffers that are opened together.  This
;;  provides an alternative to inserting all of the relevant
;;  subdirectories into the same Dired buffer.  With a prefix arg, all
;;  of the descendent Dired buffers are included, whether or not they
;;  are marked.
;;
;;  You can also create a function bookmark directly from a keyboard
;;  macro, using command `bmkp-set-kmacro-bookmark'.  And you can save
;;  the current set of keyboard macros as a bookmark, using command
;;  `bmkp-set-kmacro-list-bookmark' - jumping to it restores all of
;;  the macros'.
;;
;;  A variable-list bookmark saves and restores the values of a set of
;;  variables.  Command `bmkp-set-variable-list-bookmark' prompts you
;;  for the variables to include in the list and then sets the
;;  bookmark.  Command `bmkp-jump-variable-list' (`C-x j v') restores
;;  the recorded variable values for the bookmark's buffer.  You can
;;  also create variable-list bookmarks non-interactively, using
;;  function `bmkp-create-variable-list-bookmark'.
;;
;;  If you use library `zones.el', then you can move among multiple
;;  restrictions (narrowings) in a buffer.  The restrictions are
;;  stored in buffer-local variable `zz-izones'.  Command
;;  `bmkp-set-izones-bookmark' bookmarks this value for the current
;;  buffer.  Jumping to such a bookmark restores the saved ring/stack
;;  of restrictions.
;;
;;
;;(@* "Little Persistent Named Nothings")
;;  *** Little Persistent Named Nothings ***
;;
;;  OK, so a bookmark need not "go" anywhere.  Function, sequence,
;;  variable-list, and some other kinds of bookmarks have no real
;;  "location" to move to or restore.  But the bookmarks talked about
;;  so far at least have an associated action: you can "jump" to them,
;;  even if "jump" can mean a arbitrary action that might have nothing
;;  to do with reaching a destination.
;;
;;  You can also have a *non-invokable* bookmark, that is, one that
;;  you cannot jump to.  This is a bookmark whose handler is the
;;  function `ignore', which does nothing.
;;
;;  What's the point of that?  To record something persistently,
;;  without needing to manage the file(s) you record it in, and to be
;;  able to access that something by name.
;;
;;  As an example, library Isearch+ provides one such use case.  It
;;  lets you interactively add, modify, and remove Isearch filter
;;  predicates on the fly, providing more power and flexibility in
;;  searching.
;;
;;  (A filter predicate is a function that accepts the current
;;  search-hit limits as arguments.  If it returns `nil' then that
;;  search hit is excluded from searching; otherwise it is included.)
;;
;;  You can also, on the fly, encapsulate the current suite of filter
;;  predicates as a new filter predicate.  That is, you can manipulate
;;  a complex sequence of filters as a single predicate, using a
;;  simple name.  And you can save the definition of that new
;;  predicate in a file, so you can use it again in future Emacs
;;  sessions.
;;
;;  Alternatively, you can just bookmark the search predicate.  The
;;  data saved in the bookmark is the suite of filters that is the
;;  advised value of `isearch-filter-predicate' at the time of
;;  bookmarking.
;;
;;  Then, in a future Emacs session, while Isearching you can hit a
;;  key and enter the bookmark name (with completion), to apply that
;;  suite of filters again.
;;
;;  Bookmarking is easier than defining a new predicate and bothering
;;  with a file to save it in.  This is the kind of thing that
;;  bookmarks are for: persistently saving named bits of data for
;;  later retrieval by name.
;;
;;  Because the saved data in this case (the filter definition) has no
;;  use outside the context of searching, there is no way to invoke it
;;  - no jump action.  Its handler is `ignore'.
;;
;;  You can apply all Bookmark+ features to non-invokable bookmarks:
;;  sort, edit, tag - whatever.  Use Bookmark+ to organize them, even
;;  if you cannot invoke them.
;;
;;  Non-invokable bookmarks are shown using face `bmkp-no-jump' in the
;;  bookmark-list display.
;;
;;  It is also possible for a bookmark to have a handler other than
;;  `ignore', so that it is invokable, but that its jump action is
;;  appropriate only in certain contexts.  This is the case, for
;;  instance, for an Icicles search-hits bookmark.  You cannot invoke
;;  it outside the context of Icicles searching.  For this reason,
;;  these bookmarks are also shown with face `bmkp-no-jump' in the
;;  bookmark-list display.
 
;;(@* "Editing Bookmarks")
;;  ** Editing Bookmarks **
;;
;;  In vanilla Emacs, you can edit the annotation associated with a
;;  bookmark.  And you can rename a bookmark.  But that is all.  There
;;  is no easy way to really edit a bookmark.
;;
;;  With Bookmark+:
;;
;;  * You can use `r' in the bookmark-list display (or `C-x p r'
;;    elsewhere) to edit the name and the target file name (bookmarked
;;    location) of a bookmark.  You are prompted for the new names.
;;
;;  * You can use `e' in the bookmark-list display (or `C-x p E'
;;    elsewhere) to edit a complete bookmark - all of its information.
;;    You edit the internal Lisp sexp that represents the bookmark
;;    record.  This is the same internal definition that you see when
;;    you use `C-u C-h RET' in the bookmark list.
;;
;;  * You can use `E' in the bookmark-list display to edit the
;;    bookmark records of all of the marked bookmarks.  Again, this
;;    means editing their internal Lisp sexps.  In particular, this
;;    gives you an easy way to edit tags across multiple bookmarks.
;;    All of the editing power of Emacs is available.
;;
;;  * You can use `T e' in the bookmark list (or `C-x p t e'
;;    elsewhere), to edit a bookmark's tags.
;;
;;  For all but the first of these, you are placed in a separate
;;  editing buffer.  Use `C-c C-c' when you are done editing, to save
;;  your changes.  (To cancel, just kill the buffer: `C-x k'.)
;;
;;  There are many more keys and commands for editing bookmark tags.
;;  You can copy tags (`C-x p t c') from one bookmark and paste them
;;  to others, either replacing the original tags (`C-x p t C-y') or
;;  adding to them (`C-x p t q').  You can be prompted for some tags
;;  to add (`T +') or remove (`T -') from a bookmark.  You can delete
;;  a tag from all bookmarks (`T d').  You can rename a tag everywhere
;;  (`T r').  And you can set a tag's value.
;;
;;  As usual, all such commands are also available on the Bookmark+
;;  menus.  The menus provide quick reminders of the available keys,
;;  as does the help from `?' in the bookmark-list display.
;;
;;
;;(@* "Bookmark Records: What A Bookmark Looks Like")
;;  *** Bookmark Records: What A Bookmark Looks Like ***
;;
;;  It's worth dispelling some of the mystery about what a bookmark is
;;  by mentioning what it looks like.  This can help when you edit a
;;  bookmark record.  The first thing to mention is that the basic
;;  structure of a bookmark record is described in the doc string of
;;  variable `bookmark-alist' - but I'll repeat some of that info
;;  here.
;;
;;  A bookmark record is nothing more than a list whose first element
;;  is a string, the bookmark name.  The other list elements are
;;  properties: key+value pairs that define the bookmark data.  Each
;;  such pair is a cons: a nonempty list or a dotted list.
;;
;;  The car of the property is its name (a Lisp symbol).  The cdr is
;;  its value.  What the value can be depends on the property - in
;;  general it can be any Lisp value (number, string, list, symbol,
;;  etc.).  A property with a null cdr means the same thing as having
;;  no such property present.  For example, having the empty property
;;  `(tags)' is the same as having no `tags' property at all.
;;
;;  There is nothing more to it: properties can be anything you like,
;;  provided you provide some code to recognize them and do something
;;  with them.
;;
;;  Of course, the types of properties you use most (maybe always) are
;;  predefined, and the vanilla `bookmark.el' code and the Bookmark+
;;  code recognize and use them.  The most important and most typical
;;  property is this: `(filename . "/some/file/name.txt")', that is, a
;;  cons whose car is the symbol `filename' and whose cdr is the name
;;  (a string) of the bookmarked file.
;;
;;  With that in mind, you can see that renaming a bookmark just means
;;  changing the string that is its car.  And relocating a bookmark
;;  just means changing the string that is its `filename' - e.g., from
;;  `(filename . "/home/foo.el")' to `(filename . "/some/other.xml")'.
;;
;;  If you already have a bookmark file, typically `~/.emacs.bmk',
;;  take a look at the bookmark records in it.  A typical bookmark
;;  also has these properties, in addition to `filename': `position',
;;  `front-context-string', and `rear-context-string'.  You can guess
;;  what they are - if not, see the doc string of `bookmark-alist'.
;;
;;  A Bookmark+ bookmark typically has some additional properties that
;;  you can also guess.  Properties `time' and `visits' are updated
;;  automatically each time you access the bookmark.
;;
;;  Some bookmarks have a `handler' property whose value is a function
;;  that "jumps" to the bookmark "location".  I put those two terms in
;;  quotes here because a handler is really just any function - it can
;;  do anything you like, and there need not be any associated
;;  location.
;;
;;  Some Bookmark+ bookmarks, including autofile bookmarks, just
;;  "jump" to a file.  The position in the file is unimportant, and
;;  "jumping" does not necessarily mean visiting the file with Emacs.
;;  In effect, such bookmarks are just wrappers around the file,
;;  letting you get the advantage of Bookmark+ features (tags etc.)
;;  for a file.  Such bookmarks, which you can create using `C-x p c
;;  a' or `C-x p c f', contain a `file-handler' property instead of a
;;  `handler' property.  The difference between the two is that the
;;  `file-handler' value is a function (Lisp function or shell
;;  command) to be applied to the file, not to the bookmark.
;;
;;  Remember: A bookmark is just a persistent bit of information,
;;  typically meta-information about a file and a position in that
;;  file.
;;
;;  I'm mentioning all of this to make the point that you cannot
;;  really hurt anything if you edit a bookmark record and you mess
;;  things up.  The worst you can do is mess up all of your bookmarks
;;  by making the file unreadable as Lisp data.  (It's always a good
;;  idea to back up your bookmark file from time to time.)
;;
;;  And if each bookmark record after you edit it is a cons with a
;;  string car then your bookmarks are generally OK, even if you might
;;  have ruined the details of one or two of them.  Suppose you
;;  somehow mistakenly delete the `a' in a `filename' property, for
;;  instance.  No big deal - that bookmark no longer has a
;;  recognizable target location, but the other bookmarks are still
;;  OK.
;;
;;  The most important property for Bookmark+ users (aside from
;;  `filename') is probably `tags'.  Its value (the cdr) is a list of
;;  strings or conses - the bookmark's tags.  When you create a tag,
;;  it is typically a string (just its name) - e.g. "blue".  If you
;;  then give it a value as well, it becomes a cons with that string
;;  (the name) as car and the value as cdr - e.g. `("blue" . 42)' or
;;  `("blue" moonbeam 42)' - here the cdr is the list `(moonbeam 42)'.
;;  Here is an example of a `tags' property: `(tags "hegel" ("blue"
;;  . honeypot) "darwin")'.  Most of the time you will use strings as
;;  tags.  See also (@> "Bookmark Tags Can Have Values").
;;
;;  When you edit bookmark records, just try to stay away from
;;  changing any properties that you are not familiar with.  And make
;;  sure that when you're done you have a proper Lisp list (open
;;  parens closed etc.).  If you've never played with Lisp before, do
;;  not panic.
;;
;;  Be aware if you see dots (`.') that they are important, and they
;;  must be surrounded by whitespace: ` . '.  The amount of whitespace
;;  never matters in Lisp (except inside a string etc.).
;;
;;  Such a dot just separates the car of a cons from its cdr.  (What's
;;  a cons?  Just a car with a cdr!)  If the cdr is a list then we
;;  typically drop the dot and the list's parens: We write `(b)'
;;  instead of `(b . ())' and `(a b)' instead of `(a . (b))' or `(a
;;  . (b . ()))'.
;;
;;  Finally, remember that when you set an existing bookmark again,
;;  e.g., you use `C-x r m' and provide the name of an existing
;;  bookmark, the existing properties are generally lost.  Some are
;;  automatically updated.  Any that you might have added by editing
;;  are lost, and any that are provided by default by the bookmark
;;  handler are replaced.  The only exceptions to this are the
;;  properties listed in option `bmkp-properties-to-keep', which by
;;  default means properties `tags' and `annotation'.  Any existing
;;  tags and annotation are preserved when you update a bookmark.
 
;;(@* "Bookmark-List Views - Saving and Restoring State")
;;  ** Bookmark-List Views - Saving and Restoring State **
;;
;;  The bookmark list (buffer `*Bookmark List*') provides a view into
;;  the set of bookmarks.  You can mark, sort, and hide (filter, omit)
;;  bookmarks - see (@> "The Bookmark List Display").  The state of
;;  the displayed bookmark list can thus change.
;;
;;  At different times, and in different contexts, different views can
;;  be useful.  Bookmark+ lets you save the current state of the
;;  displayed list and later restore it.  There are a couple of
;;  different ways to do this.
;;
;;
;;(@* "Quitting Saves the Bookmark-List State")
;;  *** Quitting Saves the Bookmark-List State ***
;;
;;  If option `bmkp-bmenu-state-file' is non-`nil', which it is by
;;  default, then Bookmark+ remembers the last state of the bookmark
;;  list when you quit it or you quit Emacs, and it restores that
;;  state when you show the list again (which could be in the next
;;  Emacs session).  You can think of this feature as your "Home" page
;;  for bookmarks, giving you a stepping stone to the files and
;;  directories you use most.
;;
;;  If, for example, when you quit the bookmark list you are showing
;;  only bookmarks to Info nodes and UNIX manual pages, sorted in a
;;  particular way, and with some of them marked with `>' for
;;  particular processing, then the next time you open the list the
;;  same state is restored: the same set of bookmarks is shown, in the
;;  same order, with the same markings.  Deletion flags (`D') and
;;  modification indicators (`*') are purposefully not saved as part
;;  of the display state - they are lost when you quit the display.
;;
;;  You can turn off this automatic bookmark-list display state
;;  saving, if you want, by customizing option `bmkp-bmenu-state-file'
;;  to `nil'.  And you can toggle this option at any time, using
;;  `C-M-~' in the bookmark list (command
;;  `bmkp-toggle-saving-menu-list-state').  In particular, if you want
;;  your next visit to the bookmark list to start out with a
;;  previously recorded state instead of the current state, just hit
;;  `C-M-~' before quitting the bookmark list.
;;
;;
;;(@* "State-Restoring Commands and Bookmarks")
;;  *** State-Restoring Commands and Bookmarks ***
;;
;;  In addition to automatically saving/restoring the final
;;  bookmark-list display state, you can save this state at any time,
;;  any number of times, for later restoration.  This gives you the
;;  ability to create multiple persistent views of your bookmarks.
;;
;;  There are two ways to do this:
;;
;;  * Create a bookmark for the `*Bookmark List*' buffer itself: a
;;    bookmark-list bookmark.
;;
;;  * Define a command that restores the bookmark-list state.
;;
;;  When you use `C-x r m' (`bmkp-bookmark-set-confirm-overwrite') in
;;  buffer `*Bookmark List*' to create a bookmark-list bookmark, the
;;  current sort order, filter, regexp pattern, title, and omit list
;;  are saved as part of the bookmark.  (These concepts are described
;;  below - see (@> "Bookmark List Display").)  Jumping to such a
;;  bookmark restores all of these.
;;
;;  Alternatively, you can define a command that does the same thing,
;;  but without creating another bookmark - use `C-c C-c'
;;  (`bmkp-bmenu-define-command') in the bookmark list to do this.
;;  You are prompted for the name of the new command.  Use the command
;;  anytime (including in another Emacs session) to restore the
;;  bookmark list.
;;
;;  Define any number of such commands for the views you use.  The
;;  file for saving the definitions (see option
;;  `bmkp-bmenu-commands-file') is never overwritten, so you can also
;;  add other code to it manually, if you want.  The file is read the
;;  first time the bookmark list is displayed in a given Emacs
;;  session.
;;
;;  The state that is saved and restored using a bookmark-list
;;  bookmark or a command defined using `c' is only a partial state.
;;  The current set of markings and some other information are not
;;  saved, in order to save disk space and save/restore time.
;;
;;  Sometimes, however, you really want to save the entire
;;  bookmark-list state, creating a full snapshot.  You can use `C-c
;;  C-C' (aka `C-c C-S-c', `bmkp-bmenu-define-full-snapshot-command')
;;  to do that.  This defines a command that restores the bookmark
;;  list completely.  That is the same thing that happens
;;  automatically (by default) whenever you quit the bookmark list (or
;;  Emacs), but defining snapshot commands lets you have multiple
;;  saved states and switch to them at will.
;;
;;  Be aware, however, that full-snapshot command definitions can be
;;  quite large, since they each contain a copy of the current
;;  bookmark list and any accessory lists (hidden and marked bookmarks
;;  etc.).
;;
;;  Whether you use `c' or `C' to define a state-restoring command or
;;  you create a bookmark-list bookmark, you can create a sequence
;;  bookmark that combines such bookmark-list restoration with
;;  activation of other bookmarks.  (To include a state-restoring
;;  command in a sequence, you need to first create a function
;;  bookmark that uses the command, and then include that bookmark in
;;  the sequence.)
 
;;(@* "Bookmarking without Visiting the Target")
;;  ** Bookmarking without Visiting the Target **
;;
;;  There are several use cases for bookmarking a target without
;;  visiting it:
;;
;;  1. In an Emacs buffer you come across a reference or a link to a
;;     file or a URL.  You bookmark the target without bothering to
;;     visit it first.  You do not really care which position in the
;;     file is bookmarked.
;;
;;  2. In Dired, you mark certain files and then bookmark all (each)
;;     of them, in one operation.
;;
;;  3. In a compilation buffer (e.g. `*grep*', `*compile*') or an
;;     occur or multi-occur buffer (`*Occur*'), you bookmark one or
;;     more of the hits.  Such a bookmark takes you to the appropriate
;;     position in the target file or buffer.
;;
;;  4. You bookmark a file that you might not even be able to visit in
;;     Emacs (in the sense of editing it in a buffer) - for example, a
;;     music file.  "Jumping" to the bookmark performs an operation
;;     appropriate to the file - for example, playing music.
;;
;; 
;;(@* "Bookmarking a File or a URL")
;;  *** Bookmarking a File or a URL ***
;;
;;  You can use commands `bmkp-file-target-set' and
;;  `bmkp-url-target-set', bound by default to `C-x p c f' and `C-x p
;;  c u', to bookmark any file or URL.  Completion is available, the
;;  default file name or URL being determined by the text at point.
;;  In addition to the file or URL, you are prompted for the bookmark
;;  name.  (In general, the keys `f' and `u' are used in key sequences
;;  for file and URL bookmarks, respectively.)
;;
;;  
;;(@* "Bookmarking the Marked Files in Dired")
;;  *** Bookmarking the Marked Files in Dired ***
;;
;;  If you use `Dired+' (library `dired+.el'), then you can bookmark
;;  all of the marked files in a Dired buffer at once, as autofiles,
;;  even if you normally do not or cannot visit those files in Emacs.
;;  These keys are available in Dired:
;;
;;    `M-b'                   - Bookmark each marked file
;;    `C-M-S-b' (aka `C-M-B') - Bookmark each marked file in a
;;                              bookmark-file that you specify
;;    `C-M-b'                 - Bookmark each marked file in a
;;                              bookmark-file you specify, and create
;;                              a bookmark for that bookmark-file
;;
;;  Each of these commands bookmarks each of the marked files as an
;;  autofile.  By default, the bookmark file used for the latter two
;;  commands is in the current directory.
;;
;;  If you use multiple `C-u' as a prefix arg for these commands, then
;;  you can bookmark all of the files in Dired, regardless of
;;  markings, as follows:
;;
;;    `C-u C-u'         - Use all files in Dired, except directories
;;    `C-u C-u C-u'     - Use all files and dirs, except `.' and `..'
;;    `C-u C-u C-u C-u' - Use all files and all directories
;;
;;  `C-M-b' not only bookmarks each of the marked files, it also
;;  creates a bookmark-file bookmark for that set of bookmarks.  See
;;  (@> "Bookmark-File Bookmarks"), below.
;;
;;  You can later "jump" to that bookmark to load its set of
;;  bookmarks.  If you use `C-u' when you jump to it, then you switch
;;  bookmark files, so that `C-x p e' (or `C-x r l') displays only the
;;  bookmarks created from the marked files.  Without `C-u', jumping
;;  to the bookmark-file bookmark simply loads its bookmarks into the
;;  current set of bookmarks.
;;
;;  
;;(@* "Bookmarking Compilation, Grep, and Occur Hits")
;;  *** Bookmarking Compilation, Grep, and Occur Hits ***
;;
;;  In a similar way, you can bookmark the file or buffer positions of
;;  selected hits in a compilation buffer (including `*grep*') or an
;;  `occur' or `multi-occur' buffer.
;;
;;  `C-c C-b' in such a buffer bookmarks the target of the hit at
;;  point.  `C-c C-M-b' bookmarks the target of each hit in the
;;  buffer.
;;
;;  `C-c C-M-b' in these buffers is thus similar to `M-b' in a Dired
;;  buffer.  Unlike Dired, however, there is no way to mark such hits.
;;  Every hit is bookmarked.
;;
;;  Nevertheless, you can get the same effect.  Just use `C-x C-q' to
;;  make the buffer writable (e.g. temporarily), and then remove any
;;  hits that you do not want to bookmark.  You can remove hits anyway
;;  you like, including by `C-k' and by regexp (`M-x flush-lines' or
;;  `M-x keep-lines').
;;
;;  See also: (@> "Autonamed Bookmarks - Easy Come Easy Go"),
;;  bookmarking occur hits using autonamed bookmarks.
;;
;;
;;(@* "Bookmarking Files That You Cannot Visit with Emacs")
;;  *** Bookmarking Files That You Cannot Visit with Emacs ***
;;
;;  You use lots of files that you never visit using Emacs, but that
;;  you might like to keep track of or access in other ways: music
;;  files, image files, whatever.
;;
;;  You can define a new kind of bookmark for any file type you are
;;  interested in, implementing a bookmark handler for it that
;;  performs the appropriate action on it when you "jump" to it.  That
;;  action needs to be expressible using an Emacs function, but it
;;  need not have anything to do with visiting the file in Emacs.
;;
;;  When you bookmark a target file that Emacs recognizes as an image
;;  or sound file, an appropriate handler is used automatically.
;;
;;  After you create individual bookmarks for, say, music or image
;;  files, you can use `P B' in the bookmark-list display to show only
;;  those bookmarks, and then use `C-x r m' to bookmark that state of
;;  the bookmark-list.
;;
;;  That bookmark-list bookmark in effect becomes a music playlist or
;;  an image library or slideshow.  Jump to it anytime you want to
;;  listen to that set of music pieces or view those images.  And you
;;  can use `C-x p B' and then `C-x p next' to cycle among the music
;;  pieces or images (slideshow).  (See (@> "Cycling the Navigation List").)
;;
;;  Together with the use of bookmark tags, this gives you a handy way
;;  to organize and access objects of any kind.  See (@> "Bookmark Tags").
;;
;;  You use option `bmkp-default-handlers-for-file-types' to control
;;  which operation (handler) to use for which file type.  This is a
;;  set of associations (an alist) with each key being a regexp
;;  matching a file name, and with each associated value being a Lisp
;;  sexp that evaluates to either a shell command (a string) or an
;;  Emacs function (a symbol or lambda form).
;;
;;  You can think of `bmkp-default-handlers-for-file-types' as
;;  somewhat analogous to `auto-mode-alist'.  But it maps file-name
;;  patterns to file actions instead of mapping them to buffer modes.
;;  And it has an effect only when you use certain commands.
;;
;;  The handler for the bookmark created invokes the shell command or
;;  the Emacs function with the file name as argument.
;;
;;  Here is an example option value:
;;
;;   (("\\.ps$"    . "gsview32.exe")
;;    ("\\.html?$" . browse-url)
;;    ("\\.doc$"   . w32-browser))
;;
;;  This value causes creation of bookmarks that, when you jump to
;;  them, invoke:
;;
;;   * shell command `gsview32.exe' on the bookmark's
;;     target file if it is PostScript (extension `.ps')
;;
;;   * Emacs Lisp function `browse-url' on the file if it is HTML
;;     (extension `.htm' or `.html')
;;
;;   * Emacs Lisp function `w32-browser' on the file if the file
;;     extension is `.doc' (e.g., a Microsoft Word file)
;;
;;  The default value of `bmkp-default-handlers-for-file-types' is
;;  taken from the value of option `dired-guess-shell-alist-user'
;;  (from Dired X).
;;
;;  The associations are checked in order, and the first one that
;;  matches the given file name is used.  You can thus order them to
;;  deal with overlapping file-name patterns.
;;
;;  If no matching file association is found in
;;  `bmkp-default-handlers-for-file-types', and if option
;;  `bmkp-guess-default-handler-for-file-flag' is non-`nil' (it is
;;  `nil' by default), then Bookmark+ will guess a shell command to
;;  use.  It does this by matching the file name against
;;  `dired-guess-shell-alist-default' (also from Dired X).  In Emacs
;;  23 and later, if it finds no shell command that way then it
;;  guesses one based on mailcap entries.
;;
;;  When a bookmark is created using `C-x p c f' or `C-x p c a' for a
;;  file that matches `bmkp-default-handlers-for-file-types', the
;;  shell command or Lisp function that "jumps to" (opens) the file is
;;  saved in the bookmark as property `file-handler' (not `handler').
;;
;;
;;(@* "Opening Bookmarks Using Windows File Associations")
;;  *** Opening Bookmarks Using Windows File Associations ***
;;
;;  If you use Microsoft Windows there is no need to define new
;;  bookmark types and handlers, if the action you want is the one
;;  that Windows associates with the file.  You already have a set of
;;  file/program associations, and Bookmark+ recognizes these as
;;  alternative handlers.
;;
;;  You can thus take advantage of Windows file associations to open
;;  bookmarks for files of all kinds.  To do this, you also need
;;  library `w32-browser.el'.  In the bookmark list, the following
;;  keys are bound to commands that open bookmarks using the
;;  associated Windows `Open' applications:
;;
;;    `M-RET'     - `bmkp-bmenu-w32-open'
;;    `M-mouse-2' - `bmkp-bmenu-w32-open-with-mouse'
;;    `M-o'       - `bmkp-bmenu-w32-jump-to-marked'
;;
;;  Windows file associations are always available to you, in addition
;;  to any other file associations that you define using
;;  `bmkp-default-handlers-for-file-types' (see
;;  (@> "Bookmarking Files That You Cannot Visit with Emacs")).
;;
;;  You can thus have two different programs associated with the same
;;  kind of file.  Your MS Windows file association for PostScript
;;  might, for example, use Adobe Distiller to create a PDF file from
;;  PostScript, while your `bmkp-default-handlers-for-file-types'
;;  association for PostScript might use GhostView to display it
;;  directly.
;;
;;  Besides using `M-RET' etc. in buffer `*Bookmark List*', if in
;;  `bmkp-default-handlers-for-file-types' you register `w32-browser'
;;  as the association to use for a given file pattern, then you can
;;  use command `bmkp-w32-browser-jump' (not bound, by default)
;;  anywhere to open a bookmark whose file name matches that pattern,
;;  using its Windows file-association program.
;;
;;  You can also specify `w32-browser' as the bookmark "type" when you
;;  use command `bmkp-jump-to-type' (`C-x j :').  Either of these
;;  approaches gives you a way to use completion to choose a bookmark
;;  to open using a Windows file association.
;;
;;  Specifying such an association in
;;  `bmkp-default-handlers-for-file-types' means that bookmarks for
;;  such a file will have a `file-handler' value of `w32-browser', to
;;  "jump" to (i.e., open) the file.
;;
;;  To set up a given file extension for use this way, add an entry
;;  (REGEXP . w32-browser) to option
;;  `bmkp-default-handlers-for-file-types', where REGEXP matches the
;;  file extension.
;;
;;  For example, to make a command such as `bmkp-bookmark-a-file'
;;  (`C-x p c a') automatically bookmark `*.doc' files using the
;;  associated MS Windows program (typically MS Word), add this entry:
;;  ("\\.doc$" . w32-browser).
;;
;;
;;(@* "Autofile Bookmarks")
;;  *** Autofile Bookmarks ***
;;
;;  An autofile bookmark, or just an autofile, is a bookmark that uses
;;  the non-directory part of its file name as its bookmark name.
;;
;;  You can look at an autofile bookmark as just a file wrapper: a way
;;  to attach meta information (such as tags) to a file.  But you can
;;  use an autofile bookmark much as you would use a file.
;;
;;  To create a new autofile bookmark, you can use
;;  `bmkp-bookmark-a-file' (aka `bmkp-autofile-set'), which is bound
;;  by default to `C-x p c a'.  (In general, the key `a' is used in
;;  key sequences for autofile bookmarks.)
;;
;;  If user option `bmkp-propertize-bookmark-names-flag' is non-`nil',
;;  which it is by default with Emacs 21 and later, then you can have
;;  multiple bookmarks with the same name.  This is important for
;;  autofile bookmarks because the bookmark name is only the
;;  non-directory part of the file name.  This Bookmark+ feature lets
;;  you have different autofile bookmarks for files of the same name
;;  in different directories.
;;
;;  In addition to the single autofile bookmark that you can create
;;  for a given absolute file location, you can of course create
;;  additional bookmarks to the same file, using different bookmark
;;  names.  Among other things, this lets you tag the same file in
;;  different ways.
;;
;;  You can use `C-x j a' (`bmkp-autofile-jump') or `C-x 4 j a'
;;  (`bmkp-autofile-jump-other-window') to visit an autofile bookmark.
;;  And there are commands for visiting an autofile that is tagged in
;;  certain ways.  For example, `bmkp-autofile-some-tags-regexp-jump'
;;  (`C-x j t a % +') jumps to an autofile bookmark that has at least
;;  one tag matching a given regexp.  See (@> "Tagging Files").
;;
;;  You can create autofiles automatically whenever you use an Emacs
;;  file-cache command, by customizing user option
;;  `bmkp-autofile-filecache'.  See the Emacs manual, node `File Name
;;  Cache'.
;;
;;  This optional bookmark creation can replace adding the file to the
;;  cache, or it can be in addition to caching the file.  This is done
;;  by advising command `file-cache-add-file', which means that it
;;  affects also the other Emacs file-cache commands that use that
;;  function, directly or indirectly:
;;
;;  * `file-cache-add-directory'
;;  * `file-cache-add-directory-list'
;;  * `file-cache-add-directory-recursively'
;;  * `file-cache-add-directory-using-find'
;;  * `file-cache-add-directory-using-locate'
;;  * `file-cache-add-file-list'
;;
;;  See the Emacs manual, node `File Name Cache'.
;;
;;  If option `bmkp-autofile-access-invokes-bookmark-flag' is
;;  non-`nil' then regular access of a file (e.g. `find-file') invokes
;;  the associated autofile bookmark, if there is one.  This has the
;;  effect of updating the bookmark data, such as the number of
;;  visits.  The default value of the option is `nil'.  To set the
;;  option value, either use Customize interactively or use a
;;  Customize function.
;;
;;  Finally, if you use libraries `Dired+' and `highlight.el' then
;;  autofiles are highlighted specially in Dired, and the highlighting
;;  indicates whether the file is tagged.
;;
;;
;;(@* "A Type-Aware `find-file'")
;;  *** A Type-Aware `find-file' ***
;;
;;  User option `bmkp-default-handlers-for-file-types' (see
;;  (@> "Bookmarking Files That You Cannot Visit with Emacs")) gives
;;  you a way to associate a file type, as determined by the file
;;  name (typically its extension) with a default file action.  This
;;  is like MS Windows file associations, but it is specific to Emacs
;;  and Bookmark+.  And it is useful for more than just bookmarks.
;;
;;  Commands `bmkp-find-file' (`C-x j C-f') and
;;  `bmkp-find-file-other-window' (`C-x 4 j C-f') take advantage of
;;  this association to open files.  If a file name matches no pattern
;;  in `bmkp-default-handlers-for-file-types' then these commands act
;;  like `find-file' and `find-file-other-window'.  Otherwise, the
;;  invoke the associated file handler in
;;  `bmkp-default-handlers-for-file-types'.
;;
;;  Invoking the handler is just what the ordinary autofile jump
;;  commands (e.g. `C-x j a') do.  But `bmkp-find-file' is different
;;  in a couple of ways.
;;
;;  Like vanilla `find-file' (`C-x C-f'), `C-x j C-f' and `C-x 4 j
;;  C-f' use `read-file-name' to prompt you for the file name.  The
;;  completion candidates are the names of all of the files in the
;;  current directory (`default-directory'), that is, the directory of
;;  your current minibuffer input.  This includes the names of any
;;  autofile bookmarks in the same directory.  And like `C-x C-f' you
;;  can change directory, navigating up and down the file hierarchy.
;;  In sum, these commands are file-aware.
;;
;;  The ordinary autofile jump commands on the other hand use
;;  `completing-read' to complete your input against all autofile
;;  bookmark names, regardless of directory.  And since the bookmark
;;  names reflect only the relative file names, it is not so easy to
;;  distinguish two autofiles with the same name but in different
;;  directories.  (`Icicles' can help here, BTW.)
;;
;;  There is a `bmkp-find-file-' command that corresponds to each
;;  `bmkp-autofile-' command.  For example,
;;  `bmkp-find-file-some-tags-regexp' (`C-x j t C-f % +') corresponds
;;  to `bmkp-autofile-some-tags-regexp-jump' (`C-x j t a % +').  All
;;  `bmkp-find-file' commands use `C-f' in their key bindings, as a
;;  reminder of their reading file names a la `find-file'.
;;
;;  But whereas `C-x j C-f' and `C-x 4 j C-f' let you access any file,
;;  the other `bmkp-find-file-' commands, which find files that have
;;  certain tags, provide only autofiles as completion candidates.
;;  That's obvious, since files are tagged by bookmarking them.
;;
;;  You can thus use the `C-f' commands to take advantage of
;;  file-action associations that you define.  But if you want to
;;  associate metadata (e.g. tags) with files, then you will want to
;;  create autofiles.  You can do this when you invoke these commands,
;;  by providing a prefix argument.  Thus, for example, `C-u C-x j C-f
;;  foo.doc' opens file `foo.doc', respecting any handler recorded for
;;  it via option `bmkp-default-handlers-for-file-types' - but it also
;;  creates an autofile bookmark for it.
;;
;;  Whenever an autofile bookmark is used, regardless of whether you
;;  access it using a `bmkp-autofile*' command or a `bmkp-find-file*'
;;  command, the full bookmark record (including handler) is taken
;;  into account.
;;
;;  Note, however, that the `C-f' tag commands differ from the `a' tag
;;  commands in how the completion candidates are filtered.
;;
;;  For the former, `read-file-name' is passed a predicate that is
;;  applied to each file name in the directory, filtering out any such
;;  candidates that do not satisfy it (e.g., do not have the required
;;  tags).
;;
;;  This happens before you type any input to match the file name.
;;  The predicate checks for a corresponding autofile and checks its
;;  tags (depending on the command).  If there are lots of files in
;;  the current directory, this can take a while.
;;
;;  For the latter, similar tests are made, but instead of testing
;;  each file in the current directory, these commands test each
;;  bookmark in the current bookmark list.  If there are lots of
;;  bookmarks this can take a while.
;;
;;  In some cases a `C-f' command is quicker; in some cases a `a'
;;  command is quicker.
;;
;;  If you use `Icicles', then the performance hit for `C-f' when
;;  there are lots of files in a directory is greatly reduced.  This
;;  is because `Icicles' applies the filtering predicate after, not
;;  before, you type text in the minibuffer.  In other words, instead
;;  of testing each file in the directory, it tests only the files
;;  that match your input.  (In addition, if you use `Icicles' then
;;  you get multi-command versions of each of these bookmark commands,
;;  which means that you can visit more than one file per command
;;  invocation.)
 
;;(@* "Tagging Files")
;;  ** Tagging Files **
;;
;;  Section (@> "Tags: Sets of Bookmarks") covers bookmark tags, which
;;  are persistent metadata that you define to help you organize
;;  bookmarks into meaningful sets.
;;
;;  Section (@> "Autofile Bookmarks") describes autofile bookmarks,
;;  which, in effect, let you treat files generally as if they were
;;  bookmarks.  You can choose a file to visit or act on by its name
;;  and location, but also by its bookmark metadata.
;;
;;  In particular, you can tag a file - that is, specify tags for its
;;  associated autofile bookmark.  And you can then visit a file that
;;  has a given set of tags.  Bookmark+ provides file commands that
;;  automatically create and manipulate autofile bookmarks, that is,
;;  bookmarks that have the same name as the files they tag.
;;
;;  Command `bmkp-tag-a-file' (aka `bmkp-autofile-add-tags'), bound by
;;  default to `C-x p t + a', prompts you for a set of tags and a file
;;  location, and creates or sets the corresponding autofile bookmark.
;;  Command `bmkp-untag-a-file' (aka `bmkp-autofile-remove-tags'),
;;  bound by default to `C-x p t - a', similarly lets you remove
;;  specified tags from a file.
;;
;;  If you also use library `Icicles', then you can act on multiple
;;  files during the same command (a "multi-command").  You can thus
;;  all at once tag a set of files the same way, or act on a set of
;;  files that are tagged similarly.  `Icicles' also lets you create
;;  autofiles or add or remove tags, on the fly, whenever you use
;;  commands (e.g. `C-x C-f') that access files.
;;
;;  If you also use library `Dired+' (`dired+.el') then you can use
;;  `C-+' to add tags to the marked files and `C--' to remove tags
;;  from them.  You can use `C-M-+' and `C-M--' to do the same thing
;;  for the current file.  You can also use items from the Dired menus
;;  to do these things.
;;
;;  Bookmark+ provides two kinds of command for visiting files
;;  associated with bookmarks that have tags.
;;
;;  The first kind uses bookmarks directly: you choose a bookmark
;;  name, not a file name, but the candidates are only file and
;;  directory bookmarks.  These commands have the prefix `bmkp-file-'
;;  or `bmkp-autofile-'.
;;
;;  As a special case, commands with the prefix `bmkp-file-this-dir-'
;;  limit the choices to bookmarks for files and subdirectories of the
;;  current directory.  By default, the commands across all
;;  directories are on prefix key `C-x j t f', and those for the
;;  current directory only are on prefix key `C-x j t .'.  See
;;  (@> "Different Types of Jump Commands") for more about these
;;  commands.
;;
;;  The second kind of command is for visiting tagged files, that is,
;;  autofile bookmarks, just like the commands with prefix
;;  `bmkp-autofile-'.  However, these commands do not handle the
;;  bookmark as such, but only its file name.  They recognize its
;;  tags, but they pay no attention to any special handler or other
;;  recorded information.
;;
;;  These commands have the prefix `bmkp-find-file-', and they are on
;;  the prefix key `C-x j t C-f'.  The `C-f' here is intended to
;;  remind you of command `find-file' (`C-x C-f').  Like `find-file',
;;  they use `read-file-name' to read the bookmark's file name,
;;  instead of using `completing-read' to read the bookmark name.
;;
;;  Yes, for an autofile bookmark the bookmark name and the (relative)
;;  file name are the same.  But `read-file-name' is file-aware, and
;;  lets you browse up and down the directory hierarchy.
;;
;;  The `bmkp-find-file-' commands are available only for Emacs 22 and
;;  later (because they use `read-file-name' with a PREDICATE
;;  argument).
;;
;;  For example:
;;
;;    `C-x j t f   % +' is `bmkp-file-some-tags-regexp-jump'
;;    `C-x j t .   % +' is `bmkp-file-this-dir-some-tags-regexp-jump'
;;    `C-x j t a   % +' is `bmkp-autofile-some-tags-regexp-jump'
;;    `C-x j t C-f % +' is `bmkp-find-file-some-tags-regexp'
;;
;;  * The first of these visits any file bookmark that has at least
;;    one tag among the tags you specify, and you choose among
;;    bookmark names.  The files can be in any directories.
;;
;;  * The second is similar to the first, but only bookmarks for files
;;    in the current directory are completion candidates.
;;
;;  * The third is similar to the first, but only autofile bookmarks
;;    are completion candidates.
;;
;;  * The fourth is similar to the third regarding tags, but it uses
;;    `read-file-name', so you can browse up and down the file
;;    hierarchy.  The completion candidates are file names, not
;;    bookmark names.
;;
;;  If you use `Icicles', there are similar sets of commands, but they
;;  all let you act on multiple files at the same time
;;  (multi-commands).  For example, you can delete (or byte-compile
;;  or...) a set of files according to their tags.
;;
;;  Remember that you can create multiple bookmarks for the same file,
;;  providing them with different sets of tags.  (Only one of the
;;  bookmarks is the autofile bookmark.)
;;
;;  You can also use multiple bookmark files (the files that record
;;  bookmarks).  Different projects can thus have different tags for
;;  the same sets of files, even using just autofile bookmarks.  See
;;  (@> "Using Multiple Bookmark Files").
;;
;;  A file bookmark can have any number of tags, and multiple file
;;  bookmarks can have the same tag.  You can sort, show/hide, or mark
;;  files based on their tags.
 
;;(@* "Using Multiple Bookmark Files")
;;  ** Using Multiple Bookmark Files **
;;
;;  Bookmark-list views (see
;;  (@> "Bookmark-List Views - Saving and Restoring State")) provide
;;  one way to switch among various sets of bookmarks that you use.
;;  But that feature affects only the bookmarks that you see displayed
;;  in buffer `*Bookmark List*', not the actual set of available
;;  bookmarks.
;;
;;  The bookmarks available to you are defined in a bookmark file.  By
;;  default, they are stored in the file named by option
;;  `bmkp-last-as-first-bookmark-file', if non-`nil', otherwise in the
;;  file named by option `bookmark-default-file' (`~/.emacs.bmk', by
;;  default).
;;
;;  If you use only one bookmark file then you never need to load or
;;  save it manually.  Emacs does that for you automatically.
;;
;;  But you can have multiple bookmark files if you want, and at any
;;  time you can change the bookmark file that is current.  To do
;;  that, use `C-x p L' (or just `L' in the bookmark-list display),
;;  which is bound to command `bmkp-switch-bookmark-file-create'.
;;  Having multiple bookmark files gives you an added degree of
;;  flexibility.
;;
;;  By default, the last bookmark file you used, in your last Emacs
;;  session, is the initial bookmark file that is loaded automatically
;;  in your next session.  But if you prefer, you can make Bookmark+
;;  always start with the same bookmark file
;;  (`bookmark-default-file').  User option
;;  `bmkp-last-as-first-bookmark-file' controls this.
;;
;;  You can easily see which bookmark file is current at any time: It
;;  is shown at the top of buffer `*Bookmark List*', and it is near
;;  the top of the help output from command
;;  `bmkp-bmenu-mode-status-help', which is what is bound to `?' and
;;  `C-h m' in buffer `*Bookmark List*'.
;;
;;  When you switch to another bookmark file, the default choice for
;;  the file to switch to is the last bookmark file you used (in the
;;  same session).  So it is trivial to toggle back and forth between
;;  two bookmark files: just hit `RET' to accept the default.
;;
;;  When bookmarks are saved automatically, or when you save them
;;  using `bookmark-save' (`S' in the bookmark-list display or `C-x p
;;  s' globally) and you don't use a prefix argument, they are saved
;;  in the current bookmark file.
;;
;;  You can turn off the automatic saving of the current bookmark
;;  file, by customizing option `bookmark-save-flag' to `nil'.  And
;;  you can toggle this option at any time, using `M-~' in the
;;  bookmark list (command `bmkp-toggle-saving-bookmark-file').
;;
;;  Besides using multiple bookmark files as *alternatives*, you can
;;  combine them, using them as component bookmark subsets (like
;;  modules).  To do that, use command `C-x p l' (lowercase `l'),
;;  which is bound to `bookmark-load', and do not use a prefix
;;  argument.  (Using a prefix argument with `C-x p l' is the same as
;;  using `C-x p L': it switches bookmark files.)  Here too the
;;  default is the name of the last bookmark file that you used.
;;
;;  In the `*Bookmark List*' display you can use `M-l' to load all of
;;  the bookmark files corresponding to the marked bookmark-file
;;  bookmarks, in the order in which they are displayed.  Any non
;;  bookmark-file bookmarks that are marked are ignored.  Before
;;  loading, if any of your currently loaded bookmarks have been
;;  modified then you are asked if you want to save them first, before
;;  loading the others.
;;
;;  After loading, to avoid confusion and possible mistakes, automatic
;;  saving to the current bookmark file is turned off.  You can always
;;  use `M-~' to turn it back on again.  And remember that, as long as
;;  you have not saved bookmarks after loading, you can always use
;;  `C-u g' to revert to the bookmarks saved in the bookmark file.
;;
;;  To create additional bookmark files, to use either as alternatives
;;  or as components, you can either copy an existing bookmark file or
;;  use `bmkp-empty-file' (`C-x p 0') to create a new, empty bookmark
;;  file.  If you use `C-x p 0' with an existing bookmark file, then
;;  its bookmarks are all deleted - it is emptied.
;;
;;  Instead of simply copying a bookmark file, you can use
;;  `bookmark-save' with a prefix argument, or use `bookmark-write'
;;  (bound to `C-x p w'), to save the currently defined bookmarks to a
;;  different bookmark file.
;;
;;  However a bookmark file was created, you can switch to it and then
;;  add or delete bookmarks selectively, to change its content.
;;  Remember too that you can delete bookmarks from the current set
;;  using command `bookmark-delete' (`C-x p d') or, in the bookmark
;;  list, using `d' plus `x' or marking then `D'.
;;
;;  Deleting bookmarks from a bookmark file is one way of editing it.
;;  Another is to copy or move bookmarks from one bookmark file to
;;  another.  In the bookmark-list display, you can copy or move the
;;  marked bookmarks (or the current bookmark, if none are marked)
;;  from the current bookmark file to another that you name, using `Y
;;  > +' (`bmkp-bmenu-copy-marked-to-bookmark-file') and `Y > -'
;;  (`bmkp-bmenu-move-marked-to-bookmark-file'), respectively.  And
;;  you can use `Y > 0'
;;  (`bmkp-bmenu-create-bookmark-file-from-marked') to create a new
;;  bookmark file by copying the marked bookmarks.  With a prefix arg,
;;  `Y > 0' creates also a bookmark-file bookmark.
;;
;;  NOTE:
;;
;;    Unlike the other ways of organizing bookmarks into sets (tags,
;;    bookmark-list bookmarks, etc.) bookmark files represent
;;    physical, not logical, groupings of bookmarks.  A bookmark file
;;    contains complete bookmark records.
;;
;;    If you copy a bookmark from one bookmark file to another, the
;;    copy is an independent bookmark: it has no relation to the
;;    bookmark it was copied from.  Changes to the copy or the
;;    bookmark it was copied from do not affect each other.
;;
;;    This means that to use bookmark files for organizing bookmarks
;;    you will typically move, not copy, bookmarks between them (or
;;    copy and later delete).  Remember that you can load multiple
;;    bookmark files to access their bookmarks together in a session.
;;    Think of your bookmark files as independent modules that you can
;;    combine.
;;
;;  See Also: (@> "Bookmark+ Load Order and Option `bookmark-default-file'").
;;
;;
;;(@* "Bookmark-File Bookmarks")
;;  *** Bookmark-File Bookmarks ***
;;
;;  A bookmark file is an excellent, persistent way to represent a set
;;  of bookmarks.  In particular, it can represent a project or a
;;  project component.  Switch among bookmark files to access
;;  different projects.  Load project components as you need them.
;;
;;  You can load a bookmark file using `C-x p L' (switch) or `C-x p l'
;;  (accumulate).  As a convenience, you can also load a bookmark file
;;  by jumping to a bookmark-file bookmark.
;;
;;  You use command `bmkp-set-bookmark-file-bookmark', bound to `C-x p
;;  y', to create a bookmark-file bookmark.  Jumping to such a
;;  bookmark just loads the bookmark file that it records.  With `C-u'
;;  (e.g. `C-u C-x j y project-foo'), jumping switches bookmark files.
;;  Without `C-u' it accumulates the loaded bookmarks.
;;
;;  A bookmark-file bookmark is not only an added convenience.  You
;;  can also use it in combination with other Bookmark+ features, such
;;  as tagging.
;;
;;  As a shortcut, in Dired (if you use library `Dired+'), `C-M-b'
;;  creates a bookmark-file bookmark.  The bookmark file that it
;;  records contains autofile bookmarks to each of the files that was
;;  marked in Dired at the time it was created.  Jumping to that
;;  bookmark-file bookmark makes those (marked) files available as
;;  bookmarks.  See also
;;  (@> "Use Dired to Bookmark Files without Visiting Them").
;;
;;  Note that the bookmark file in which a bookmark-file bookmark is
;;  recorded is not the same as the bookmark file recorded in that
;;  bookmark.
;;
;;  For example, when you use `C-M-b' in Dired, the bookmark-file for
;;  the marked files is, by default, file `.emacs.bmk' in the Dired
;;  directory.  So if you are in directory `/foo/bar' the default
;;  bookmark file for the marked files is `/foo/bar/.emacs.bmk'.  But
;;  the new bookmark-file bookmark created is recorded in the current
;;  bookmark file, whatever that might be (e.g. `~/.emacs.bmk').
 
;;(@* "The Bookmark List Display")
;;  ** The Bookmark List Display **
;;
;;  Bookmark+ enhances the bookmark list (aka the bookmark "menu
;;  list", a misnomer) that is displayed in buffer `*Bookmark List*'
;;  when you use `C-x p e' or `C-x r l' (command
;;  `bookmark-bmenu-list').
;;
;;  At the top of the bookmark-list display is this header
;;  information:
;;
;;  * The bookmark file used currently.  This is important because
;;    Bookmark+ makes it easy for you to have multiple bookmark files
;;    and switch among them.
;;
;;  * A title that describes the kinds of bookmarks listed, that is,
;;    it reflects athe current filtering, if any.
;;
;;  For example, this header indicates that the current bookmark file
;;  is `c:/.emacs.bmk' and only file and directory bookmarks are
;;  shown:
;;
;;    Bookmark file:
;;    c:/.emacs.bmk
;;
;;    File and Directory Bookmarks
;;    ----------------------------
;;
;;  (Bookmark+ does not use the sliding header line of vanilla Emacs
;;  24+, which means that option `bookmark-bmenu-use-header-line' has
;;  no effect.  You do not need to see `Bookmark' and `File' column
;;  headers as you scroll.)
;;
;;  Bookmarks are highlighted to indicate their type. You can mark and
;;  unmark bookmarks, show or hide bookmarks of particular types, and
;;  more.  Bookmarks that have tags are marked with a `t'.  Bookmarks
;;  that have an annotation are marked with an `a' (not with a `*' as
;;  in vanilla `bookmark.el').  Bookmarks that have been modified
;;  since the last save of the bookmark file are marked with a `*'.
;;  Bookmarks that have bookmark-highlight override settings (see
;;  (@> "Defining How to Highlight")) are marked with a one-character
;;  pink background.
;;
;;  Use `?' or `C-h m' in buffer `*Bookmark List*' for more
;;  information about the bookmark list, including the following:
;;
;;  * The current status of sorting, filtering, and marking.
;;
;;  * A legend for the faces used for different bookmark types.
;;
;;
;;(@* "Jumping To Bookmarks from the Bookmark List Display")
;;  *** Jumping To Bookmarks from the Bookmark List Display ***
;;
;;  Bookmark visiting (jumping) commands are globally on prefix keys
;;  `C-x j' and `C-x 4 j'.  In the bookmark-list display they are
;;  additionally on `j' (other window) and `J' (same window).  In
;;  addition, `j >' is bound to `bmkp-bmenu-jump-to-marked', which
;;  jumps to each of the marked bookmarks in other windows.
;;
;;
;;(@* "Tag Commands and Keys")
;;  *** Tag Commands and Keys ***
;;
;;  There are lots of tag-related bookmark commands, and most are
;;  bound to keys in buffer `*Bookmark List*' as well as to other keys
;;  outside it.  How can you keep the commands straight or remember
;;  their keys?
;;
;;  In the bookmark list display, tags-command keys begin with prefix
;;  key `T'.  Elsewhere, they begin with prefix key `C-x p t' (or `C-x
;;  j t', for jump commands - see (@> "Different Types of Jump Commands")).
;;
;;  `C-h m' (or `?') is your friend, of course.  Likewise `T C-h',
;;  `C-x p t C-h', and `C-h >' (which describes the marked bookmarks).
;;  Beyond that, the tag-related keys that are more than two
;;  keystrokes are organized as follows:
;;
;;    They all have the prefix key `T'.
;;
;;    `m' means mark
;;    `u' means unmark
;;    `>' stands for the marked bookmarks
;;    `*' means AND (set intersection; all)
;;    `+' means OR  (set union; some/any)
;;    `~' means NOT (set complement)
;;
;;  The key `T m *', for instance, marks (`m') the bookmarks that are
;;  tagged with all (`*' = AND) of a given set of tags.  It prompts you
;;  for one or more tags that the bookmarks must have, and it marks
;;  all bookmarks that have all of the tags you enter.
;;
;;  The key `T u ~ +' unmarks (`u') the bookmarks that do not (`~')
;;  have any (`+' = OR) of the tags you specify.  And so on.
;;
;;  The marking and unmarking commands for tags compare the tags a
;;  bookmark has with tags that you enter.  Any bookmarks that have no
;;  tags are ignored - they are neither marked nor unmarked by these
;;  commands.
;;
;;  `+' and `-' can also mean add and remove tags, respectively, and
;;  `>' stands for the marked bookmarks.  So `T > +' adds (`+') one or
;;  more tags to each of the marked (`>') bookmarks.
;;
;;  In general, the tag-related commands let you enter a set of tags,
;;  one at a time.  Thus, instead of having a command that adds a
;;  single tag to the current bookmark, you have a command that adds
;;  any number of tags to it.  To add just a single tag, hit `RET'
;;  twice: once to enter the tag, and once again to indicate that it
;;  is the last (i.e., the only) one.
;;
;;  If you just hit `RET' immediately, specifying an empty set of
;;  tags, then each of the commands does something appropriate.  For
;;  `T m *', for instance, an empty list of tags means to mark (only)
;;  the bookmarks that have any tags at all.
;;
;;  Finally, for the marking/unmarking tags commands, a prefix
;;  argument flips the sense of the command, in this way:
;;
;;  "some are" -> "some are NOT", i.e., "not all are" (and vice versa)
;;  "all are"  -> "all are NOT",  i.e., "none are"    (and vice versa)
;;
;;  In other words:
;;
;;    C-u T m *    =  T m ~ +  (all are NOT      = not some are)
;;    C-u T m ~ +  =  T m *    (not some are NOT = all are)
;;    C-u T m +    =  T m ~ *  (some are NOT     = not all are)
;;    C-u T m ~ *  =  T m +    (not all are NOT  = some are)
;;
;;  You'll figure it out ;-).
;;
;;  Other important keys pertaining to tags (the keys in parentheses
;;  work in any buffer, not just buffer `*Bookmark List*'):
;;
;;  * `C-h RET' (`C-x p ?') shows you the tags that belong to a
;;    bookmark.  With a prefix argument it shows you the full internal
;;    form of the tags, that is, the name+value pairs.
;;
;;  * `C-h >' describes all of the marked bookmarks, in the current
;;    sort order.  The descriptions include the tags.  (You can use `T
;;    m * RET' to mark all of the tagged bookmarks.)
;;
;;  * `T e' (`C-x p t e') lets you edit a bookmark's tags.
;;
;;  * `T l' (`C-x p t l') lists all tags currently known to Emacs
;;     (across all bookmarks).
;;
;;  * `T +' (`C-x p t + b') adds some tags to a bookmark.
;;    `T -' (`C-x p t - b') removes some tags from a bookmark.
;;    `T 0' (`C-x p t 0) removes all tags from a bookmark.
;;    `T d' (`C-x p t d) removes a set of tags from all bookmarks.
;;
;;  In the bookmark list display you can also sort bookmarks according
;;  to how they are tagged, even in complex ways.  See
;;  (@> "Sorting Bookmarks").
;;
;;
;;(@* "Tags: Sets of Bookmarks")
;;  *** Tags: Sets of Bookmarks ***
;;
;;  The best way to think about tags is as names of sets.  All
;;  bookmarks tagged `blue' constitute the bookmark set named `blue'.
;;
;;  The bookmarks visible in the bookmark list at any time also
;;  constitute an unnamed set.  Likewise, the marked bookmarks and the
;;  unmarked bookmarks are unnamed sets.  Bookmark+ is all about
;;  helping you act on sets of Emacs objects.  Bookmarks are named,
;;  persistent pointers to objects such as files and file sets.
;;  Bookmark tags are named, persistent sets of bookmarks (and hence
;;  of their target objects).
;;
;;  The marking commands make it easy to combine sets as unions or
;;  intersections.  And you can give the result a name for quick
;;  access later, just by adding a new tag.  in other words, do the
;;  set-definition work only once, and name the result.
;;
;;  How would you tag as `Java IDE Projects' the bookmarks that are
;;  already tagged both `Java' and `ide'?
;;
;;  1. `T m * Java RET ide RET RET', to mark them.
;;  2. `T > + Java IDE Projects RET RET, to tag them.
;;
;;  How would you sort your bookmarks, to show all those tagged both
;;  `blue' and `moon' first?
;;
;;  1. `T m * blue RET moon RET RET', to mark them.
;;  2. `s >' to sort the marked bookmarks first
;;     (see (@> "Sorting Bookmarks"), below).
;;
;;  If you wanted to show only the marked bookmarks, instead of
;;  sorting to put them first in the list, you would use `>'
;;  instead of `s >'.
;;
;;  How would you query-replace the set of files that are tagged with
;;  any of the tags `alpha', `beta', and `gamma', but are not tagged
;;  `blue' or `moon'?
;;
;;    1. `F S', to show only the file bookmarks.
;;    2. `T m + alpha RET beta RET gamma RET RET', to mark the
;;       bookmarks that have at least one of those tags.
;;    3. `T u + blue RET moon RET RET', to unmark those that are
;;       tagged `blue' or `moon'.
;;    4. `M-q' to query-replace the marked files.
;;
;;  If that were a set of files that you used often, then you would
;;  name the set by giving the files a new tag.
;;
;;  The point is that bookmarks, and bookmark tags in particular, let
;;  you define and manipulate sets of Emacs objects.  It doesn't
;;  matter how you define such a set: regexp matching (marking,
;;  filtering), by object type, by tag combinations...  Sets need not
;;  be named to act on them, but you can provide them with persistent
;;  names (tags) to avoid redefining them over and over.  Manipulation
;;  of bookmarked objects includes visiting, searching, and
;;  query-replacing.  And you can define your own bookmark types
;;  (using bookmark handlers) and associated manipulations.
;;
;;
;;(@* "Open Dired for the Marked File Bookmarks")
;;  *** Open Dired for the Marked File Bookmarks ***
;;
;;  You've seen that the bookmark list has many features that are
;;  similar to Dired features.  But Dired is specialized for files and
;;  directories, and it has many more features for manipulating them.
;;  The bookmark list is not intended to replace Dired.
;;
;;  You can, however, use the bookmark list to take advantage of
;;  arbitrary Dired features for file and directory bookmarks.
;;  Command `bmkp-bmenu-dired-marked' (`M-d >') weds Bookmark+'s
;;  set-defining and set-manipulating features (tagging, marking,
;;  filtering etc.) to Dired's file-manipulating features.
;;
;;  `M-d >' opens a Dired buffer that is specialized for just the
;;  files and directories whose bookmarks are marked in the bookmark
;;  list.  (Other marked bookmarks are ignored by the command.)  The
;;  files and directories can be located anywhere; they need not be in
;;  the same directory.  They are listed in Dired using absolute file
;;  names.
;;
;;  (In Emacs versions prior to release 23.2, only local files and
;;  directories can be handled, due to Emacs bug #5478.  In such
;;  versions, remote-file bookmarks are ignored by `M-d >'.)
;;
;;  This Bookmark+ feature makes sets of files and directories
;;  immediately amenable to all of the operations provided by Dired.
;;
;;  It is particularly useful in conjunction with tags.  Use bookmark
;;  tags and marks to define a possibly complex set of file and
;;  directory bookmarks.  Then hit `M-d >' to list them in a Dired
;;  buffer.  Then use any Dired commands you want to act on any of
;;  them.
;;
;;  For example, to compress bookmarked files that are tagged with
;;  both `blue' and `moon':
;;
;;  1. Mark them using `T m * blue RET moon RET RET'.
;;  2. Open Dired for them using `M-d >'.
;;  3. Mark them in Dired, then compress them using `Z'.
;;
;;  Since tags are persistent, Bookmark+ gives you a good way to
;;  define an arbitrary set of files as a project and then open them
;;  in Dired at any time to operate on them.
;;
;;  If you use `Dired+' (library `dired+.el'), then a similar feature
;;  is available for the marked files and directories: You can use
;;  `C-M-*' in Dired to open a separate Dired buffer for them only.
;;  You can of course then bookmark that resulting Dired buffer, if
;;  you like.
;;
;;  If you use `Icicles', then whenever you use a command that reads a
;;  file (or directory) name, you can use `M-|' during file-name
;;  completion to open Dired on the currently matching set of file
;;  names.  That is, this is the same kind of special Dired buffer
;;  that is provided for file and directory bookmarks by `M-d >' in
;;  the bookmark list.
;;
;;
;;(@* "Marking and Unmarking Bookmarks")
;;  *** Marking and Unmarking Bookmarks ***
;;
;;  Bookmark+ enhances the marking and unmarking of bookmarks in the
;;  bookmark list in several ways.  These enhancements are similar to
;;  features offered by Dired and Dired-X.  You can use:
;;
;;  * `% m' to mark the bookmarks that match a regexp.  The entire
;;    line in the bookmark list is checked for a match, that is, both
;;    the bookmark name and the file name, if shown.
;;
;;  * `M-DEL' (or `U') to unmark all bookmarks, or all that are marked
;;    `>', or all that are flagged `D' for deletion.
;;
;;  * `t' to toggle (swap) the marked and unmarked bookmarks: those
;;    that are marked become unmarked, and vice versa.
;;
;;  * `>' to show only the marked bookmarks or `<' to show only the
;;    unmarked bookmarks.  Repeat to show them all again.
;;
;;  * `F M', `I M' etc. to mark only the file bookmarks, Info
;;    bookmarks etc.  (The first key here is the same as the
;;    corresponding filter key, e.g. `F' for files - see next topic.)
;;
;;  * `O M' to mark the orphaned bookmarks, that is, those whose
;;    recorded files have been renamed or deleted.  You can then
;;    relocate or delete the bookmarks, as appropriate.
;;
;;
;;(@* "Filtering Bookmarks (Hiding and Showing)")
;;  *** Filtering Bookmarks (Hiding and Showing) ***
;;
;;  There are three ways to show only certain bookmarks.
;;
;;  1. Filter by bookmark type.
;;
;;  2. Filter bookmarks incrementally and temporarily, using pattern
;;     matching.
;;
;;  3. Filter out the marked or unmarked bookmarks.
;;
;;  * Filtering by bookmark type
;;
;;    The commands that show only bookmarks of a particular type are
;;    bound to keys that end in `S' (for "show").  For example, `I S'
;;    shows only Info bookmarks, and `X S' shows only temporary
;;    bookmarks.
;;
;;    The type filter is reflected in the bookmark-list display title.
;;    It says `All Bookmarks' if no type filter is used.  Otherwise it
;;    tells you what kind of bookmarks are listed: `Autonamed
;;    Bookmarks', `File and Directory Bookmarks', and so on.
;;
;;    Note: It is only filtering by bookmark type that is remembered
;;    when you save a bookmark-list display state or you create a
;;    bookmark-list bookmark.  See (@> "State-Restoring Commands and Bookmarks").
;;
;;  * Filtering incrementally by pattern matching
;;
;;    These commands show only bookmarks that in some way match a
;;    pattern (regexp) that you type.  The bookmarks are filtered
;;    incrementally as you type the pattern.  Hit any non-inserting
;;    key, such as `RET', to finish defining the pattern.
;;
;;    The commands for this are bound to keys that start with `P' (for
;;    "pattern").  For example, `P B' shows only bookmarks whose names
;;    match the regexp, `P F' shows those whose file names match, and
;;    `P T' shows those that have one or more tags that match.
;;    (See (@> "Bookmark Tags"), above, for information about tags.)
;;
;;  * Filtering based on marking
;;
;;    Just as in Dired, you can use `% m' to mark the bookmarks that
;;    match a regexp.  Then use `>' to show only the marked bookmarks.
;;    See (@> "Marking and Unmarking Bookmarks"), above.
;;
;;    This method has the advantage that you can show the complement,
;;    the bookmarks that do *not* match the regexp, by using `<'
;;    instead of `>'.  It also has the advantage that matching checks
;;    the combination of bookmark name and file name (use `M-t' to
;;    toggle showing file names).
;;
;;
;;(@* "Only Visible Bookmarks Are Affected")
;;  *** Only Visible Bookmarks Are Affected ***
;;
;;  Commands that operate on the current bookmark or on the marked or
;;  the unmarked bookmarks act only on bookmarks that are displayed
;;  (not hidden).  This includes the commands that mark or unmark
;;  bookmarks.  This means that you can easily define any given set of
;;  bookmarks.
;;
;;  For example:
;;
;;    Use `F S' to show only bookmarks associated with files.
;;    Use `% m' to mark those that match a particular regexp.
;;    Use `R S' to show only bookmarks that have regions.
;;    Use `m' to mark some of those region bookmarks individually.
;;    Use `.' to show all bookmarks.
;;    Use `t' to swap marked and unmarked (so unmarked are now marked)
;;    Use `D' to delete all of the marked bookmarks (after confirming)
;;
;;  Together, steps 1-7 delete all file bookmarks that match the
;;  regexp and all region bookmarks that you selectively marked.
;;
;;
;;(@* "Omitting Bookmarks from Display")
;;  *** Omitting Bookmarks from Display ***
;;
;;  In sections (@> "Marking and Unmarking Bookmarks") and
;;  (@> "Filtering Bookmarks (Hiding and Showing)") you learned how
;;  to hide and show bookmarks in the bookmark list.  This section is
;;  about a different kind of hiding, called "omitting".
;;
;;  Omitted bookmarks are not shown in the bookmark list, no matter
;;  what filtering is used.  The only way to show omitted bookmarks is
;;  to show all of them and only them, using `- S', which is bound to
;;  command `bmkp-bmenu-show-only-omitted'.
;;
;;  Omitted bookmarks are still available even if they are not shown,
;;  and you can still jump to them (e.g. using `C-x r b').  You just
;;  don't see them in the bookmark list.  And that's the reason for
;;  this feature: to hide those bookmarks that you don't care to see.
;;
;;  One use for this feature is to hide the component bookmarks that
;;  make up a sequence bookmark (see
;;  (@> "Function, Sequence, Variable-List,... Bookmarks")).  The
;;  default behavior when you create a sequence bookmark is in fact to
;;  omit its component bookmarks from the displayed list.
;;
;;  You can omit any bookmarks by marking them and then using `- >'
;;  (`bmkp-bmenu-omit/unomit-marked').  If you are looking at the
;;  omitted bookmarks (after using `- S'), then `- >' un-omits the
;;  bookmarks marked there.  Think of two complementary spaces: the
;;  normal bookmark list and the omitted bookmark list.  When you use
;;  `- >', the marked bookmarks that are currently shown are moved to
;;  the opposite space.
;;
;;  You can un-omit all of the omitted bookmarks at once, using `- U'
;;  (`bmkp-unomit-all').  You can also call this command from outside
;;  the bookmark-list display.
;;
;;  Omitted bookmarks that are marked are generally not included when
;;  you use a command that acts on the marked bookmarks.  However, if
;;  you use a negative prefix argument with the command then they are.
;;
;;  For some commands this is relaxed so that any prefix arg has this
;;  effect.  For other commands a non-negative prefix arg has a
;;  different effect.  In some cases, a non-negative prefix arg has
;;  one effect and a non-positive prefix arg has the effect of
;;  including omitted marked bookmarks, so that a zero prefix arg has
;;  both effects.  For any given command, consult the doc string for
;;  full information.
;;
;;
;;(@* "Sorting Bookmarks")
;;  *** Sorting Bookmarks ***
;;
;;  Filtering hides certain kinds of bookmarks.  Sometimes, you want
;;  to see bookmarks of various kinds, but you want them to be grouped
;;  or sorted in different ways, for easy recognition, comparison, and
;;  access.
;;
;;  Bookmarks shown in the bookmark list are sorted using the current
;;  value of option `bmkp-sort-comparer'.  (If that is `nil', they are
;;  unsorted, which means they appear in reverse chronological order
;;  of their creation.)
;;
;;  You can use `s s'... (repeat hitting the `s' key) to cycle among
;;  the various sort orders possible, updating the display
;;  accordingly.  By default, you cycle among all available sort
;;  orders, but you can shorten the cycling list by customizing option
;;  `bmkp-sort-orders-for-cycling-alist'.
;;
;;  You can also change directly to one of the main sort orders
;;  (without cycling) using `s >', `s n', `s f n', etc.  There are
;;  many such predefined sort orders bound to keys with the prefix `s'
;;  - use `C-h m' or `?'  for more info.
;;
;;  You can reverse the current sort direction (ascending/descending)
;;  using `s r'.  Also, repeating any of the main sort-order commands
;;  (e.g. `s n') cycles among that order, the reverse, and unsorted.
;;
;;  For a complex sort, which involves composing several sorting
;;  conditions, you can also use `s C-r' to reverse the order of
;;  bookmark sorting groups or the order within each group (depending
;;  on whether `s r' is also used).  Try it, for example, together
;;  with sorting by bookmark kind (`s k').
;;
;;  Be aware that `s C-r' can be a bit unintuitive.  If it does not do
;;  what you expect or want, or if it confuses you, then don't use it
;;  ;-).  (`s C-r' has no noticeable effect on simple sorting.)
;;
;;  Remember that you can combine sorting with filtering different
;;  sets of bookmarks - bookmarks of different kinds (e.g. Info) or
;;  bookmarks that are marked or unmarked.
;;
;;  Finally, you can easily define your own sorting commands and sort
;;  orders.  See macro `bmkp-define-sort-command' and the
;;  documentation for option `bmkp-sort-comparer'.  (Bookmark+ uses
;;  option `bmkp-sort-comparer'; it *ignores* vanilla Emacs option
;;  `bookmark-sort-flag'.)
;;
;;  Of particular note is that you can interactively define commands
;;  that sort by a given list of tags - you use keys `T s' (command
;;  `bmkp-define-tags-sort-command') to do that.  You are prompted for
;;  the tags to sort by.  Bookmarks are sorted first according to
;;  whether they are tagged with the first tag, then the second tag,
;;  and so on.  Otherwise, sorting is by bookmark name.
;;
;;  The tags you specify are used, in order, in the name of the new
;;  command.  For example, if you enter tags `alpha', `beta', and
;;  `gamma', in that order, then the sorting command created is
;;  `bmkp-bmenu-sort-alpha-beta-gamma'.  The new command is saved in
;;  your bookmark commands file (`bmkp-bmenu-commands-file').
;;
;;  Note that because you can add a new tag to all bookmarks that have
;;  some given set of tags, you can use that single (new) tag to
;;  represent the entire tag set.  Sorting by that tag is then the
;;  same as sorting by the tag set.  You can of course use overlapping
;;  sets in the composite sort command.  You can, for example, sort
;;  first according to tag `tag1', which represents the set of tags
;;  `alpha', `beta', `gamma', `delta', and then sort according to tag
;;  `tag2', which represents the set of tags `beta', `delta'.
;;
;;  See also (@> "Use Bookmark+ with Icicles") - the same technique is
;;  used in `Icicles' for sorting bookmarks as completion candidates.
 
;;(@* "Bookmarks for Specific Files or Buffers")
;;  ** Bookmarks for Specific Files or Buffers **
;;
;;  A bookmark typically records a position or a region in a file or
;;  buffer.  Sometimes you are interested in accessing or examining
;;  only the bookmarks for particular files or buffers.  For example,
;;  you might want to navigate among the bookmarks for the current
;;  buffer.  Or you might want to search the regions recorded in the
;;  bookmarks for a particular file.
;;
;;  For a bookmark, the recorded file and buffer name differ in that
;;  the file name is absolute.  Bookmarks for buffer `foo.el' include
;;  all files named `foo.el', whereas bookmarks for file
;;  `/project1/lisp/foo.el' include only the files in that one
;;  directory.
;;
;;  Another important difference is that when multiple buffers visit
;;  different files that have the same relative file name (i.e., in
;;  different directories), Emacs makes the buffer names unique by
;;  appending `<N>' as needed, where `N' is 2, 3,...  When you create
;;  a bookmark, the current buffer name is recorded as the bookmark's
;;  buffer.  If the current buffer is not visiting a file, then the
;;  bookmark created is a non-file bookmark.  In that case, to use the
;;  bookmark later you must have a buffer of the same name
;;  (e.g. `foo.el<2>').
;;
;;  Bookmark+ provides commands to handle these different use cases:
;;  specific files and specific buffers.  The keys bound to these
;;  commands use `f' for file and `b' for buffer.  In the
;;  bookmark-list display, the following keys affect the bookmarks for
;;  a particular file or buffer whose name you provide (with
;;  completion).
;;
;;  * `= f M' and `= b M' - mark 
;;  * `= f S' and `= b S' - show (only)
;;
;;  For navigation, the following keys jump to bookmarks for
;;  particular files or buffers.  (Use `C-x 4 j' for other-window.)
;;
;;  * `C-x j ,,'                  - current buffer
;;  * `C-x j = f' and `C-x j = b' - specified file(s) or buffer(s)
;;
;;  For the `=' keys you are prompted for one or more file names or
;;  buffer names.
;;
;;  Finally, because the bookmarks in the current buffer can be of
;;  particular interest, `C-x p ,' opens the bookmark-list display for
;;  only those bookmarks.  (`,' stands generally for "this-buffer" in
;;  Bookmark+ key bindings.)
 
;;(@* "Cycling, Navigation List")
;;  ** "Cycling, Navigation List" **
;;
;;  Using completion to jump to a bookmark is handy.  It lets you
;;  choose a bookmark by its name and gives you direct ("random")
;;  access to it.
;;
;;  Sometimes, however, you don't much care what a bookmark is named,
;;  and you want to cycle quickly among relatively few, related
;;  bookmarks.  Obviously, the smaller the number of bookmarks in the
;;  set, the more convenient cycling is - with many bookmarks cycling
;;  can become tedious.
;;
;;  An analogy: If your TV has lots of channels, then the channel
;;  up/down buttons on the remote control are not so useful: 32, 33,
;;  34, ..., 79!  Unless the channel you want happens to be near the
;;  current channel, cycling around a huge ring of channels is not the
;;  way to go.  And just because your TV receives lots of channels
;;  does not mean that you watch them all or that you are equally
;;  interested in them all.
;;
;;  Some TV remote controls have a feature that mitigates this
;;  problem.  You can define a ring of favorite channels, and there
;;  are two additional buttons that let you cycle forward and backward
;;  around the ring, skipping the channels in between.  The number of
;;  favorites is relatively small, so cycling is not tedious.  More
;;  importantly, all of the channels in the ring are ones you are
;;  interested in.
;;
;;  Extend this idea to allow for assigning different sets of channels
;;  to the favorites ring at different times: choose the ring you want
;;  at any time: sports, music, films, science, art, history, and so
;;  on.  Add the possibility of sorting those sets in various ways, to
;;  further facilitate cycling, and you arrive at the idea behind the
;;  Bookmark+ navigation list.
;;
;;  Another analogy is a music playlist.  You can use Bookmark+ as a
;;  simple music player by bookmarking music files.  Similarly, you
;;  can use Bookmark+ to create slideshows by bookmarking image files.
;;  Cycle the navigation list to move through the slide show.
;;
;;  If you use MS Windows, you can take advantage of your existing
;;  file associations to open your bookmarks using the appropriate
;;  program - no need to define a new bookmark type and handler.  See
;;  (@> "Bookmarking Files That You Cannot Visit with Emacs").
;;
;;  Note: The default value of option `bmkp-use-region' is `t', not
;;  `cycling-too', which means that when you cycle to a bookmark its
;;  recorded region (if any) is not activated.  This is probably what
;;  you want most of the time.  Cycling is a repetitive action, and if
;;  you cycle to a bookmark with no recorded region then an already
;;  active region is just extended.  Customize the value to
;;  `cycling-too' if you prefer that behavior.
;;
;;
;;(@* "The Bookmark Navigation List")
;; *** "The Bookmark Navigation List ***
;;
;;  Bookmark+ is all about letting you define and manipulate sets of
;;  bookmarks.  When a bookmark set can be used for cycling (as well
;;  as jumping) it is called the "navigation list" or "navlist", for
;;  short.
;;
;;  In other words, Bookmark+ lets you cycle among any set of
;;  bookmarks.  When you cycle, it is the set that currently
;;  constitutes the navigation list that is cycled.
;;
;;  Here are two ways to define the navigation list:
;;
;;  * `C-x p :' (`bmkp-choose-navlist-of-type') - As the set of all
;;    bookmarks of a certain type (`any' or empty input means use all
;;    bookmarks).
;;
;;  * `C-x p B' (`bmkp-choose-navlist-from-bookmark-list') - As the
;;    set of all bookmarks corresponding to a bookmark-list bookmark,
;;    that is the bookmarks corresponding to a given recorded state of
;;    buffer `*Bookmark List*'.
;;
;;  Each of these lets you choose a set of bookmarks using completion.
;;  For `C-x p :' you are prompted for the type of bookmark
;;  (e.g. `dired').
;;
;;  For `C-x p B' you are prompted for the name of a bookmark-list
;;  bookmark that you created.  But you can also choose the candidate
;;  `CURRENT *Bookmark List*' to capture the bookmarks that would be
;;  shown currently in the `*Bookmark List*' (even if the list is not
;;  displayed now).  See (@> "State-Restoring Commands and Bookmarks")
;;  for information about bookmark-list bookmarks.
;;
;;  If you do not define the navigation list before you start cycling,
;;  it is automatically defined as follows:
;;
;;  * If you cycle using a current-file/buffer cycling key such as
;;    `C-x p down' (see (@> "Cycling in the Current File/Buffer"))
;;    then the bookmarks in the current file or buffer are used as the
;;    navlist.
;;
;;  * Otherwise, a snapshot is taken of the the bookmarks currently in
;;    the global bookmark list (the value of variable
;;    `bookmark-alist') as the navlist.
;;
;;  However the navlist is defined, it is important to remember this:
;;  it is a static snapshot of some set of bookmarks taken at a given
;;  time.  Subsequent changes to the bookmark list that was copied are
;;  not reflected in the navlist.  If you add a bookmark it will not
;;  be among those cycled.  But see also
;;  (@> "Cycling Dynamic Sets of Bookmarks") for how to cycle dynamic
;;  sets.
;;
;;  You can update the navlist at any time by taking another snapshot
;;  of the same bookmark list you used for the last snapshot.  For the
;;  global bookmark list just use `C-x p : RET'.  (You can of course
;;  bind that action to a shorter key sequence if you like.)
;;
;;  Besides cycling among the bookmarks of the navlist (see next),
;;  once you have defined the navigation list you can use `C-x j N' or
;;  `C-x 4 j N' to jump to its bookmarks, as mentioned in section
;;  (@> "Different Types of Jump Commands").
;;
;;  Note that just because you might have used `C-x p B' to define the
;;  navlist using a particular bookmark-list bookmark or the current
;;  `*Bookmark List*' state, that does not mean that the `*Bookmark
;;  List*' state at any given time necessarily reflects the navlist
;;  bookmarks.  The two are separate.  You can, however, open the
;;  `*Bookmark List*' so that it reflects the bookmarks currently in
;;  the navigation list, using `C-x p N' (`bmkp-navlist-bmenu-list').
;;  
;;
;;(@* "Cycling the Navigation List")
;; *** "Cycling the Navigation List" ***
;;
;;  So you choose a navigation list.  How do you then cycle among its
;;  bookmarks?
;;
;;  Commands `bmkp-next-bookmark' and `bmkp-previous-bookmark' cycle
;;  to the next and previous bookmark in the navigation list (with
;;  wraparound).  (There are also other-window versions of these
;;  commands.)
;;
;;  You can bind these to any keys you like, but it's obviously better
;;  to choose keys that are easily repeatable (e.g. by holding them
;;  pressed).  Some people who are used to using MS Visual Studio
;;  might want to use `f2' and `S-f2' to cycle forward and backward.
;;
;;  Bookmark+ does not define such key bindings, but you can.  What it
;;  does is define repeatable keys on the `bookmark-map' keymap, which
;;  by default has prefix `C-x p'.  To do this it binds similar
;;  commands that can be repeated by simply repeating the key-sequence
;;  suffix.  These are the (default) keys:
;;
;;  Forward:  `C-x p f', `C-x p C-f', `C-x p right'
;;  Backward: `C-x p b', `C-x p C-b', `C-x p left'
;;
;;  (If you use an Emacs version prior to Emacs 22, you cannot use
;;  this prefix-key repeatable feature.)
;;
;;  In addition, if you use MS Windows then you can invoke the Windows
;;  `Open' action on each bookmark when you cycle, to act on its file
;;  using the program associated with the file type.  This lets you
;;  play music or display images in a playlist or slideshow fashion.
;;  These are the keys to do that:
;;
;;  Forward:  `C-x p next'   (PageDown key)
;;  Backward: `C-x p prior'  (PageUp key)
;;
;;  Being able to cycle among an arbitrary set of bookmarks is the
;;  most important feature of Bookmark+ cycling.  The other important
;;  feature is that if the navigation list is defined by `*Bookmark
;;  List*' then the characteristics of that bookmark display are
;;  respected for navigation.  Only the bookmarks visible in
;;  `*Bookmark List*' are included, and the `*Bookmark List*' sort
;;  order is used for navigation.
;;
;;  So you can not only choose any set of bookmarks for cycling at any
;;  given time, you can also cycle among them in an order you choose.
;;  For example, if in the bookmark list display (`C-x p e' or `C-x r
;;  l') you show only those file bookmarks that belong to a given
;;  project, and you have them sorted by file size, then cycling moves
;;  among only those files, in file-size order.
;;
;;  This is a main reason you will want to define bookmark-list
;;  bookmarks, which record a specific set of bookmarks and their sort
;;  order: to later choose given sets in different contexts for
;;  cycling.
;;
;;
;;(@* "Cycling Dynamic Sets of Bookmarks")
;; *** "Cycling Dynamic Sets of Bookmarks" ***
;;
;;  The fact that the navlist is a static snapshot is a useful
;;  feature, but sometimes you might want to cycle among a particular
;;  dynamic set of bookmarks, that is, to have cycling take changes to
;;  the bookmark set into account automatically.  For that, Bookmark+
;;  provides separate cycling commands for most types of bookmark.
;;
;;  By default, these different kinds of cycling commands are not
;;  bound to any keys, with the exception of the commands for cycling
;;  the current fle or buffer.  This exception includes cycling all
;;  bookmarks for the current file/buffer
;;  (see (@> "Cycling in the Current File/Buffer")
;;  and cycling only the highlighted bookmarks for the current
;;  file/buffer (see (@> "Using Highlighted Bookmarks")).  Keys `C-x p
;;  down' and `C-x p C-down' are defined for these two kinds of
;;  current-buffer cycling.
;;
;;  If you often want to cycle among the bookmarks of some other
;;  particular kind (e.g. only the autonamed bookmarks), then you can
;;  bind the relevant commands
;;  (e.g. `bmkp-next-autonamed-bookmark-repeat',
;;  `bmkp-previous-autonamed-bookmark-repeat', or their other-window
;;  versions) to handy keys.  Otherwise, you can just use the cycling
;;  commands without binding them.
;;
;;
;;(@* "Cycling in the Current File/Buffer")
;; *** "Cycling in the Current File/Buffer" ***
;;
;;  You can navigate the bookmarks in the current file or buffer by
;;  cycling as well as jumping.  It is convenient to have dedicated
;;  keys for this, separate from the keys to cycle the navigation
;;  list.  The following keys are defined, corresponding to commands
;;  `bmkp-next-bookmark-this-file/buffer-repeat' and
;;  `bmkp-previous-bookmark-this-file/buffer-repeat':
;;
;;  Next:     `C-x p n', `C-x p C-n', `C-x p down'
;;  Previous: `C-x p p', `C-x p C-p', `C-x p up'
;;
;;  Starting with Emacs 23.3 (Emacs fix for bug #6256), you can also
;;  use the mouse wheel to cycle: `C-x p' then just rotate the wheel.
;;
;;  Again, you can bind any keys you want to these commands
;;  (e.g. `f2', `S-f2').  If you do not need to use a prefix key, then
;;  bind commands `bmkp-next-bookmark-this-file/buffer' and
;;  `bmkp-previous-bookmark-this-file/buffer' (no -repeat).
;;
;;  You can also cycle among just the highlighted bookmarks in the
;;  current file or buffer - see (@> "Using Highlighted Bookmarks").
;;
;;  Cycling among bookmarks for the current file or buffer (whether
;;  all or only the highlighted ones) is dynamic: the current set of
;;  bookmarks is cycled, not a static snapshot taken at some point in
;;  past.  The navlist is automatically updated to the current dynamic
;;  set each time you cycle.  This is different from the usual cycling
;;  of the navlist, where it is taken as a static snapshot -
;;  see (@> "The Bookmark Navigation List").
;;
;;  By default, you cycle among the bookmarks for the current file or
;;  buffer in order of their buffer positions, top to bottom.  If you
;;  want a different order, you can customize option
;;  `bmkp-this-file/buffer-cycle-sort-comparer'.
;;
;;  Alternatively, you can use `C-x p ,' to display the `*Bookmark
;;  List*' with only the current file/buffer's bookmarks, sort them
;;  there, and then use `C-x p B' to set the navigation list to
;;  `CURRENT *Bookmark List*'.  In that case, you use the navlist
;;  cycling keys (e.g. `C-x p f', not `C-x p n'), and the cycled set
;;  is a static snapshot.
;;
;;  Note that the keys mentioned here cycle bookmarks for the current
;;  file if visiting a file, or the current buffer otherwise.  There
;;  are also commands (unbound to keys) for cycling bookmarks for the
;;  current file only or the current buffer only.
;;
;;  The bookmarks for the current buffer are those that were created
;;  in a buffer of exactly the same name.  If one buffer visits a file
;;  `foo.el', and another buffer visits a different file of the same
;;  name (i.e., in a different directory), the second buffer will have
;;  the name `foo.el<2>'.  The buffer name is recorded when you create
;;  a bookmark.  If you later use same-buffer cycling then the
;;  bookmarks cycled are only those created with the same buffer name
;;  as the current buffer.
;;
;;  This is the reason why the `*-file/buffer*' commands are bound to
;;  keys.  They are usually what you want.  They try first to work
;;  with bookmarks for the same file as the current buffer, if it is
;;  visiting a file.
 
;;(@* "Autonamed Bookmarks - Easy Come Easy Go")
;; ** "Autonamed Bookmarks - Easy Come Easy Go" **
;;
;;  Sometimes it is convenient to quickly create and delete bookmarks
;;  whose names you don't really care about.  That is the purpose of
;;  "autonamed" bookmarks.  An autonamed bookmark has a simple name
;;  provided automatically, and it does not record any region
;;  information - it records only a position.  An autonamed bookmark
;;  is nevertheless an ordinary, persistent bookmark.
;;
;;  `C-x p RET' creates a bookmark at point without prompting you for
;;  the name.  It is named using the current buffer name preceded by
;;  the position in the buffer.  For example, the default name of the
;;  autonamed bookmark in buffer `foo.el' at position 58356 is
;;  `000058356 foo.el'.
;;
;;  When you jump to any bookmark, the actual destination can differ
;;  from the recorded position, because the buffer text might have
;;  changed.  In that case, the position you jump to has been
;;  automatically relocated using the recorded bookmark context (some
;;  buffer text surrounding the original position).
;;
;;  If option `bmkp-save-new-location-flag' is non-`nil' then, after
;;  jumping, the recorded position of the bookmark is automatically
;;  updated to reflect the new location jumped to.  This is true for
;;  any bookmark.
;;
;;  In the case of an autonamed bookmark, the bookmark name typically
;;  reflects the recorded position when you create it.  And when you
;;  jump to it, both the name and the recorded position are updated to
;;  reflect the jump destination.  So jumping to an autonamed bookmark
;;  keeps its persistent record in sync with the buffer location.
;;
;;  You will thus notice that the names of autonamed bookmarks can
;;  change as you visit them (e.g. cycling).  The bookmarks are
;;  automatically repositioned following their recorded contexts, and
;;  their names reflect that repositioning.
;;
;;  It is only when you jump to a bookmark that it is repositioned
;;  this way, and only if needed.  It is normal that some bookmarks
;;  become somewhat out of sync with their original positions as you
;;  edit the text in the buffer.  In addition, if you highlight
;;  bookmarks then you will notice the highlighting move as you edit
;;  nearby text.  The recorded bookmark has not changed, but its
;;  highlight has moved.  The highlight moves more or less as if it
;;  were an Emacs marker. When you jump to the bookmark and it is thus
;;  updated, the highlight moves back to the recorded position,
;;  adjusted perhaps to fit the recorded context.
;;
;;  `C-x p RET' is `bmkp-toggle-autonamed-bookmark-set/delete', and it
;;  does double duty.  If an autonamed bookmark is under the cursor,
;;  then `C-x p RET' deletes it.  Easy creation, easy deletion.
;;  Because of this toggle behavior, there is at most one autonamed
;;  bookmark at any given buffer position.
;;
;;  `C-x p RET' has a third use: With a prefix argument, it prompts
;;  you to confirm the deletion of *ALL* autonamed bookmarks for the
;;  current buffer.
;;
;;  (You can also use `C-x p delete' (that's the `delete' key), bound
;;  to `bmkp-delete-bookmarks', to delete individual bookmarks under
;;  the cursor or all bookmarks in the buffer.  This is not limited to
;;  autonamed bookmarks.)
;;
;;  In addition to `C-x p RET', you can create autonamed bookmarks
;;  using these commands:
;;
;;  * `bmkp-set-autonamed-bookmark-at-line' - At a line beginning
;;  * `bmkp-set-autonamed-regexp-buffer'    - At buffer matches
;;  * `bmkp-set-autonamed-regexp-region'    - At region matches
;;  * `bmkp-occur-create-autonamed-bookmarks' (`C-c b' in `*Occur*') -
;;    At `occur' and `multi-occur' hits
;;
;;  Autonamed bookmarks are normal bookmarks.  In particular, they are
;;  persisted.  If you do not care to persist them, you can ensure
;;  that they are automatically deleted by adding
;;  `bmkp-delete-autonamed-this-buffer-no-confirm' to
;;  `kill-buffer-hook' and `bmkp-delete-autonamed-no-confirm' to
;;  `kill-emacs-hook':
;;
;;    (add-hook 'kill-buffer-hook
;;              'bmkp-delete-autonamed-this-buffer-no-confirm)
;;    (add-hook 'kill-emacs-hook
;;              'bmkp-delete-autonamed-no-confirm)
;;
;;  You can customize the format of autonamed bookmarks using options
;;  `bmkp-autoname-bookmark-function' and `bmkp-autoname-format'.
;;
;;  For example, if you want autonamed bookmarks to show the line and
;;  column numbers, in the form `L<num>,C<num> <buffer>', where <num>
;;  is a sequence of decimal digits and <buffer> is the buffer name,
;;  then you can use a function such as this as the value of
;;  `bmkp-autoname-bookmark-function':
;;
;;    (defun my-auto-l+c-name (position)
;;      "Return a name for POSITION that uses line & column numbers."
;;      (let ((line  (line-number-at-pos position))
;;            (col   (save-excursion
;;                     (goto-char position) (current-column))))
;;        (format "L%d,C%d %s" col line (buffer-name))))
;;
;;  To enable Bookmark+ to recognize such bookmarks as autonamed, you
;;  would then set `bmkp-autoname-format' to the format specification
;;  "^L[0-9]+,C[0-9]+ %B", to match their names.  Here, the `%B' is a
;;  Bookmark+ format specifier that corresponds to the buffer name.
;;
;;  Recognizing the buffer name in an autonamed bookmark is important
;;  or commands that act only on autonamed bookmarks for a specific
;;  buffer.  That includes commands `bmkp-autonamed-this-buffer-jump'
;;  and `bmkp-delete-all-autonamed-for-this-buffer'.
;;
;;  You use the special format specifier `%B' for the buffer name,
;;  instead of just `%s', because the format can have multiple `%'
;;  sequences, and the buffer name could be anywhere in the bookmark
;;  name.  Depending on the buffer, the buffer name could thus be
;;  confused with other text in the bookmark name, unless you use `%B'
;;  to show where it is.  You can use just `%s' for it if there is no
;;  risk of ambiguity.  (Use `%s' in `bmkp-autoname-bookmark-function'
;;  to insert the buffer name.)
 
;;(@* "Temporary Bookmarks")
;;  ** Temporary Bookmarks **
;;
;;  Autonamed bookmarks are easy-come-easy-go in the sense that `C-x p
;;  RET' either sets (creates) one or deletes the one under the
;;  cursor.  But what about temporary bookmarks in general?  What if
;;  you want only bookmarks that are temporary, that is, not saved to
;;  disk?  Or what if you want certain kinds of bookmarks to always be
;;  temporary?  Or what if you want to toggle whether particular
;;  bookmarks get saved automatically?
;;
;;
;;(@* "Temporary Bookmarking Mode")
;;  *** Temporary Bookmarking Mode ***
;;
;;  As always, you can control whether the bookmarks in the current
;;  bookmark list are saved automatically using option
;;  `bookmark-save-flag'.  Remember that you can toggle this option
;;  using command `bmkp-toggle-saving-bookmark-file' (bound to `M-~'
;;  in the bookmark-list buffer).  Remember too that you can at any
;;  time change the set of available bookmarks (the bookmark list),
;;  which means also changing the set of bookmarks that are
;;  susceptible to being saved.
;;
;;  You could, for example:
;;
;;  1. Use `C-x p 0' (`bmkp-empty-file') to create a new, empty
;;     bookmark file.
;;
;;  2. Use `C-x p L' (`bmkp-switch-bookmark-file-create') to switch to
;;     using that new, empty bookmark file.
;;
;;  3. Use `M-x bmkp-toggle-saving-bookmark-file' to turn off
;;     auto-saving bookmarks to disk.
;;
;;  This is essentially what the minor-mode toggle command
;;  `bmkp-temporary-bookmarking-mode' does.  When in this minor mode,
;;  bookmarks that you create are stored on the new bookmark list,
;;  which is not automatically saved to disk.  If you do not
;;  explicitly save it yourself then the bookmarks are lost when your
;;  Emacs session ends - they are only temporary.
;;
;;  This command is bound to `M-L' in the bookmark-list display buffer
;;  (`*Bookmark List*').  The suffix `L' indicates that this has to do
;;  with loading a bookmark file.  See (@> "Using Multiple Bookmark Files").
;;
;;  In the bookmark-list display, temporary bookmarking mode is
;;  indicated in the mode line by `TEMPORARY Bookmarking' in place of
;;  `Bookmarks' as the mode name.
;;
;;
;;(@* "Making Bookmarks Temporary")
;;  *** Making Bookmarks Temporary ***
;;
;;  Instead of simply switching to a temporary bookmark list, so that
;;  *all* bookmarking is only temporary, you more often want to have
;;  some bookmarks be temporary while still ensuring that others get
;;  saved.  Or you temporarily want all new bookmarks that you create
;;  and all bookmarks that you update to be temporary, without
;;  affecting other, unchanged bookmarks.
;;
;;  You can control this at the level of individual bookmarks, types
;;  of bookmarks, or all bookmarks whenever they are set (created or
;;  updated).
;;
;;  * At the individual-bookmark level, commands
;;    `bmkp-make-bookmark-temporary' and `bmkp-make-bookmark-savable'
;;    prompt you for a bookmark name and then set its
;;    temporary/savable status.  Command
;;    `bmkp-toggle-temporary-bookmark' combines these commands,
;;    toggling the status for a given bookmark.
;;
;;    In the bookmark list, this toggle is bound to `C-M-X'.  There
;;    are also commands in the bookmark-list display to toggle the
;;    temporary/savable status of the marked bookmarks (`M-X'), to
;;    mark the temporary bookmarks (`X M'), and to show only the
;;    temporary bookmarks (`X S').
;;
;;  * At the bookmark-type level, you can customize user option
;;    `bmkp-autotemp-bookmark-predicates'.  It is a list of bookmark
;;    predicates - typically type predicates - that define which
;;    bookmarks are automatically made temporary whenever they are
;;    set.
;;
;;    The default value includes the type predicates for autonamed
;;    bookmarks: `bmkp-autonamed-bookmark-p' and
;;    `bmkp-autonamed-this-buffer-bookmark-p'.  This means that (only)
;;    autonamed bookmarks are made temporary whenever they are created
;;    or updated.
;;
;;    The doc string for the option lists the predefined bookmark type
;;    predicates, but you can use any bookmark predicates.
;;
;;  * Finally, you can toggle whether *all* bookmarks become temporary
;;    whenever they are created or updated, using command
;;    `bmkp-toggle-autotemp-on-set', which is bound globally to `C-x p
;;    x'.
;;
;;  You can delete all such temporary bookmarks from the current
;;  bookmark list using command `bmkp-delete-all-temporary-bookmarks'
;;  (or by using `X M' to mark them in the bookmark-list display and
;;  then hitting `D' to delete thems).
;;
;;  In the bookmark-list display (buffer `*Bookmark List*'), temporary
;;  bookmarks are indicated with the mark `X' in the same column where
;;  the annotation mark `a' would otherwise appear.
 
;;(@* "Automatic Bookmarking")
;;  ** Automatic Bookmarking **
;;
;;  You might find automatic bookmarking useful.  The idea is that
;;  Emacs sets a bookmark for you automatically.
;;
;;  Bookmark+ can do this either when you perform some action (besides
;;  explicitly bookmarking) or whenever you are idle for a given
;;  period of time (option `bmkp-auto-idle-bookmark-mode-delay').
;;  
;;
;;(@* Automatic Info Bookmarking)
;;  *** Automatic Info Bookmarking ***
;;
;;  The former feature is currently limited to Info bookmarks.  When
;;  global minor mode `bmkp-info-auto-bookmark-mode' is enabled, each
;;  Info node you visit can be bookmarked automatically, using the
;;  default bookmark name, which is the Info manual name plus the node
;;  name.  For example, node `Lisp Data Types' in the Elisp manual
;;  gives you a bookmark named `(elisp) Lisp Data Types'.
;;
;;  When the mode is enabled and an Info node is visited, an existing
;;  such bookmark is always updated.  If no such bookmark exists then
;;  a new one is created if option `bmkp-info-auto-type' has value
;;  `create-or-replace'.  If it has value `update-only' then no new
;;  bookmark is created.  The default option value is `update-only'.
;;  You can toggle the value using command
;;  `bmkp-toggle-info-auto-type'.
;;
;;  With mode `bmkp-info-auto-bookmark-mode' enabled, even if you
;;  create Info bookmarks with the given names (i.e., the default
;;  names) only manually, they are updated automatically.  In
;;  particular, updating a bookmark increments the recorded number of
;;  visits to the Info node and the time of the last visit.
;;
;;  You can sort bookmarks in the bookmark-list display by the time of
;;  last visit, using `s d', or by the number of visits, using `s v'.
;;
;;  This gives you an easy way to see which parts of the manuals you
;;  have visited most recently and how much you have visited them.
;;  Showing only Info bookmarks gives you the effect of a persistent
;;  mini-manual of just the visited Info nodes.  Turn the mode off
;;  anytime you do not want to record Info visits.
;;
;;  Also useful in this context, though not related to bookmarking, is
;;  the ability to save your Info history persistently, so links to
;;  visited nodes are shown using a different face.  This makes it
;;  easy to see which parts of a manual you have already looked at.
;;  (And checking a bookmark to a visited node shows you how much you
;;  have visited it.)
;;
;;  If you use library `info+.el' then you have this complementary
;;  ability save your Info history list persistently.  Just enable
;;  minor mode `Info-persist-history-mode'.
;;
;;
;;(@* Automatic Idle-Period Bookmarking)
;;  *** Automatic Idle-Period Bookmarking ***
;;
;;  Automatic idle-period bookmarking uses autonamed bookmarks (see
;;  (@> "Autonamed Bookmarks - Easy Come Easy Go")).  It lets you
;;  navigate among them to visit spots where you spent some time
;;  (idly).
;;
;;  How many such automatic bookmarks would you want?  And where?
;;  Bookmark+ tries to provide some user options that let you get the
;;  behavior you want.
;;
;;  In general, you probably do not want such bookmarks to be created
;;  too often or too close together.  You probably do not care about
;;  the names of the bookmarks created, and you do not want to be
;;  interrupted to name them.  You probably want automatic bookmarking
;;  to be per-buffer, but you might sometimes want to turn it on or
;;  off for all buffers.  You might want more than one automatic
;;  bookmark on a given line, but probably not.  Finally, you might or
;;  might not want automatic bookmarks to be temporary (current
;;  session only) or highlighted.
;;
;;  Mode `bmkp-auto-idle-bookmark-mode' is a local minor mode, which
;;  means that it is buffer-specific.  The command of the same name
;;  turns the mode on and off.  When the mode is on, the minor-mode
;;  indicator ("lighter") `Auto-Bmk' is shown in the mode line for the
;;  buffer.  You can customize this indicator (removing it, if you
;;  like), using option `bmkp-auto-idle-bookmark-mode-lighter'.
;;
;;  Command `bmkp-global-auto-idle-bookmark-mode' turns on the mode in
;;  all buffers, that is, it is global, not local.  Regardless of
;;  whether you use the mode locally or globally, a bookmark is
;;  created automatically only in the current buffer.  That is, a
;;  buffer must be current (selected) for an automatic bookmark to be
;;  created there - it is not enough that the mode be enabled in the
;;  buffer.
;;
;;  Option `bmkp-auto-idle-bookmark-mode-set-function' defines the
;;  bookmark-setting function.  By default, its value is
;;  `bmkp-set-autonamed-bookmark-at-line', which sets an autonamed
;;  bookmark at (the beginning of) the current line.  If you want
;;  bookmarks to be created automatically then you typically want them
;;  to be autonamed, both because the name is unimportant and because
;;  setting an autonamed bookmark requires no interaction on your
;;  part.  But you can use any setting function you like as the option
;;  value.  (You can always rename an autonamed bookmark later, if you
;;  want to keep it and give it a meaningful name.)
;;
;;  Option `bmkp-auto-idle-bookmark-min-distance' is the minimum
;;  number of characters between automatic bookmark positions.  If the
;;  cursor is currently closer to some existing automatically created
;;  bookmark, then no automatic bookmark is set at point.  If you set
;;  this to `nil' then there is no limit on how close the bookmarks
;;  can be.  (But there is only one autonamed bookmark at any given
;;  position.)
;;
;;  If you want the automatically created bookmarks to be temporary
;;  (not saved to your bookmark file), then customize option
;;  `bmkp-autotemp-bookmark-predicates' so that it includes the kind
;;  of bookmarks that are set by
;;  `bmkp-auto-idle-bookmark-mode-set-function'.  For example, if
;;  automatic bookmarking sets autonamed bookmarks, then
;;  `bmkp-autotemp-bookmark-predicates' should include
;;  `bmkp-autonamed-bookmark-p' or
;;  `bmkp-autonamed-this-buffer-bookmark-p' (it includes both of these
;;  by default).  Remember that you can toggle whether a given
;;  bookmark is temporary or savable, using `M-X' in the bookmark-list
;;  display (buffer `*Bookmark List*').
;;
;;  If you want the bookmarks to be automatically highlighted, then
;;  customize option `bmkp-auto-light-when-set' to highlight bookmarks
;;  of the appropriate kind.  For example, to highlight autonamed
;;  bookmarks set it to `autonamed-bookmark'.
;;
;;  NOTE: If you use Emacs 20, then by default
;;  `bmkp-auto-idle-bookmark-mode' is global rather than local.  The
;;  doc string tells you how to make it local instead.  If you use
;;  Emacs 21, then `bmkp-auto-idle-bookmark-mode' is local but there
;;  is no global mode, `bmkp-global-auto-idle-bookmark-mode'.  This is
;;  because Emacs 21 does not support `define-globalized-minor-mode'.
 
;;(@* "Highlighting Bookmark Locations")
;;  ** Highlighting Bookmark Locations **
;;
;;  You can highlight the location (destination) of a bookmark.  For
;;  this feature you need library `bookmark+-lit.el' in addition to
;;  the other Bookmark+ libraries.
;;
;;  You might never want to highlight a bookmark, or you might want to
;;  highlight most or even all bookmarks, or your use of highlighting
;;  might fall somewhere between.  It depends on what kind of
;;  bookmarks you have and how you use them.  Bookmark+ lets you
;;  choose.  By default, no bookmarks are highlighted.
 
;;(@* "Defining How to Highlight")
;;  ** Defining How to Highlight **
;;
;;  By default, autonamed bookmarks are highlighted differently from
;;  non-autonamed bookmarks.  Bookmark highlighting uses a style and a
;;  face.  The available styles are these:
;;
;;  * Region              - Highlight the region, if a region bookmark
;;  * Line                - Highlight line of the bookmark position
;;  * Position            - Highlight character at bookmark position
;;  * Line Beginning      - Highlight first character on line
;;  * Left Fringe         - Highlight only the left fringe
;;  * Left Fringe + Line  - Highlight the left fringe and the line
;;  * Right Fringe        - Highlight only the right fringe
;;  * Right Fringe + Line - Highlight the right fringe and the line
;;
;;  You can customize the default styles and faces to use for
;;  autonamed and non-autonamed bookmarks.  You can also customize the
;;  fringe bitmaps to use.
;;
;;  * `bmkp-light-autonamed'                  (face)
;;  * `bmkp-light-non-autonamed'              (face)
;;  * `bmkp-light-autonamed-region'           (face)
;;  * `bmkp-light-non-autonamed-region'       (face)
;;  * `bmkp-light-style-autonamed'            (option)
;;  * `bmkp-light-style-non-autonamed'        (option)
;;  * `bmkp-light-style-autonamed-region'     (option)
;;  * `bmkp-light-style-non-autonamed-region' (option)
;;  * `bmkp-light-left-fringe-bitmap'         (option)
;;  * `bmkp-light-right-fringe-bitmap'        (option)
;;
;;  Note: A region, position, or line highlight acts more or less like
;;  an Emacs marker: it moves with the surrounding text.  As you edit
;;  the text in the buffer, the highlighted location can thus become
;;  out of sync with the recorded position.  This is normal.  When you
;;  jump to the bookmark, its highlight is automatically repositioned
;;  to the recorded location, possibly adjusted according to the the
;;  surrounding context.
;;
;;  In addition to the default highlighting, which you can customize,
;;  you can set the highlighting for individual bookmarks and
;;  particular sets of bookmarks (overriding their default
;;  highlighting).  These individual settings are saved as part of the
;;  bookmarks themselves.
;;
;;  In the bookmark list display (buffer `*Bookmark List*'):
;;
;;  * `H +'    - Set the highlighting for this line's bookmark
;;  * `H > +'  - Set the highlighting for the marked bookmarks
;;
;;  Globally, you can use `M-x bmkp-set-lighting-for-bookmark' to set
;;  the highlighting for a given bookmark.
;;
;;  Each of these commands prompts you (with completion) for the style
;;  and face to set, as well as for a condition that controls whether
;;  to highlight.  Each of these is optional - just hit `RET' (empty
;;  input) at its prompt to skip setting it.
;;
;;  The condition is an Emacs-Lisp sexp that is evaluated whenever an
;;  attempt is made to highlight the bookmark.  Any resulting value
;;  except `:no-light' highlights the bookmark.  The sexp can refer to
;;  the variables `this-bookmark' and `this-bookmark-name', whose
;;  values are the bookmark to be highlighted and its name,
;;  respectively.
;;
;;  So, for example, if you wanted to be prompted each time before
;;  highlighting a certain bookmark you might set its highlighting
;;  condition to a sexp such as this:
;;
;;  (or (y-or-n-p (format "Highlight `%s' " this-bookmark-name))
;;      :no-light)
;;
;;  If you hit `n' at the prompt then `:no-light' is returned and the
;;  bookmark is not highlighted.
;;
;;  In the bookmark-list display, a pink-background, one-character
;;  highlight is used next to each bookmark that has a highlight
;;  override wrt the default.  You can see what that override setting
;;  is by using `C-u C-h RET' - look for the `lighting' entry in the
;;  bookmark definition.
;;
;;
;;(@* "Highlighting On Demand")
;;  *** Highlighting On Demand ***
;;
;;  You can highlight or unhighlight a bookmark or a set of bookmarks
;;  on demand.
;;
;;  In the bookmark list (buffer `*Bookmark List*'):
;;
;;  * `H H',   `H U'   - Highlight, unhighlight this line's bookmark
;;
;;  * `H > H', `H > U' - Highlight, unhighlight the marked bookmarks
;;
;;  Globally:
;;
;;  * `C-x p C-u'          - Unhighlight a highlighted bookmark at
;;                           point or on the same line (in that order)
;;
;;  * `C-x p h', `C-x p u' - Highlight, unhighlight a bookmark in the
;;                           current buffer (with completion).
;;
;;  * `C-x p H', `C-x p U' - Highlight, unhighlight bookmarks:
;;
;;                           With plain `C-u': all bookmarks
;;
;;                           With `C-u C-u': navigation-list bookmarks
;;
;;                           Otherwise, bookmarks in current buffer:
;;                            No prefix arg:  all bookmarks
;;                            Prefix arg > 0: autonamed bookmarks
;;                                       < 0: non-autonamed bookmarks
;;
;;  The default bookmark for `C-x p u' is the same bookmark that is
;;  unhighlighted by `C-x p C-u': a (highlighted) bookmark at point
;;  (preferably) or on the same line.  The latter key binding just
;;  saves you having to hit `RET' to pick the default.
;;
;;  When you use `C-x p h', you can use a prefix argument to override
;;  both the default highlighting and any highlighting that is
;;  recorded for the bookmark itself.  You are prompted for the style
;;  or face to use:
;;
;;  * Negative arg:     prompted for style
;;  * Non-negative arg: prompted for face
;;  * Plain `C-u':      prompted for style and face
;;
;;
;;(@* "Highlighting Automatically")
;;  *** Highlighting Automatically ***
;;
;;  You can also highlight automatically, whenever you set (create) a
;;  bookmark or jump to one.  This is controlled by these options:
;;
;;  * `bmkp-auto-light-when-set'
;;  * `bmkp-auto-light-when-jump'
;;
;;  You can choose any of these values for either option:
;;
;;  * Autonamed bookmark
;;  * Non-autonamed bookmark
;;  * Any bookmark
;;  * Autonamed bookmarks in buffer
;;  * Non-autonamed bookmarks in buffer
;;  * All bookmarks in buffer
;;  * None (no automatic highlighting) - the default
;;
;;  The first three values highlight only the bookmark being set or
;;  jumped to.
;;
;;  Be aware that, depending on the setting, highlighting can take a
;;  while.
 
;;(@* "Using Highlighted Bookmarks")
;;  ** Using Highlighted Bookmarks **
;;
;;  Once you have highlighted bookmarks, what can you do with them?
;;  Obviously, the highlighting can help you distinguish and find
;;  bookmarks visually.  But highlighting also serves as yet another
;;  way to define sets: the highlighted vs unhighlighted bookmarks.
;;
;;  Any command that operates on a set of bookmarks can be applied to
;;  one or the other of these two sets.  Bookmark+ defines only a few
;;  such operations, but you can easily define others.
;;
;;  In addition to such specific commands, you can also apply general
;;  operations to the highlighted or unhighlighted bookmarks, using
;;  the bookmark-list display (`*Bookmark List*').  `H S' shows only
;;  the bookmarks that are currently highlighted, and `H M' marks
;;  them.  You can then perform any of the available bookmark-list
;;  operations on them.
;;
;;  Globally, you can use these keys:
;;
;;  * `C-x p ='                    - List the bookmarks that are
;;                                   highlighted at point.  With a
;;                                   prefix arg, show the full data.
;;
;;  * `C-x j h', `C-x 4 j h'       - Jump to a highlighted bookmark.
;;                                   Only highlighted bookmarks are
;;                                   completion candidates.
;;
;;  * `C-x p C-down', `C-x p C-up' - Cycle to the next and previous
;;                                   highlighted bookmark.
 
;;(@* "Bookmark Links")
;;  ** Bookmark Links **
;;
;;  You can use command `bmkp-insert-bookmark-link' to create links in
;;  any Emacs text that jump to particular bookmarks when you follow
;;  them (by hitting `RET' or clicking `mouse-2').  If you hit `?' or
;;  double-click `mouse-1' on such a bookmark link then the bookmark
;;  is described, showing the same information as `C-x p ?'
;;  (`bmkp-describe-bookmark').
;;
;;  You are prompted for the bookmark to link.  If the region is
;;  active and nonempty then the link is put on its text.  Otherwise,
;;  you are prompted for the link text, which is inserted.  The
;;  default link text is the bookmark name in this case.
;;
;;  The bookmark linked can be of any type.
;;
;;  This simple feature lets you easily create "launching pads" for
;;  different sets of bookmarks: buffers or files that consist of
;;  bookmark links and any other text you like.  This gives you yet
;;  another way to organize bookmarks (and so also the files,
;;  directories, etc. that they target).
;;
;;  If you also use library `font-lock+.el' then the links appear with
;;  face `link', even in a font-locked buffer.  (Library
;;  `font-lock+.el' just provides this feature of allowing
;;  non-font-lock highlighting in a font-locked buffer.  See
;;  http://lists.gnu.org/archive/html/emacs-devel/2014-08/msg00540.html.)
;;
;;  The links you create this way are not persistent, but you can of
;;  course re-create them using Lisp.
;;
;;
;;(@* "Org Mode Links that Jump To Bookmarks")
;;  *** Org Mode Links that Jump To Bookmarks ***
;;
;;  You can also easily define Org-mode links that jump to bookmarks.
;;  These links are persistent.  Again, the bookmark linked can be of
;;  any type.
;;
;;  You can use the standard Org command `org-store-link' (`C-c l') in
;;  buffer `*Bookmark List*' to store a link to the bookmark at point.
;;  (This is also item `Store Org Link' in the mouse-3 popup menu.)
;;
;;  Outside buffer `*Bookmark List*' you can use command
;;  `bmkp-store-org-link' to store a link to any bookmark.  You are
;;  prompted for the bookmark name.  You can even enter the name of a
;;  bookmark that does not yet exist.  (This is also item `Store Org
;;  Link To...' on menu `Bookmarks'.)
;;
;;  If you use a numeric prefix arg with either command then the
;;  bookmark link stored will be for jumping to the bookmark in the
;;  same window.  Without a numeric prefix arg, the link will use
;;  another window.  (Org mode defines other behaviors for non-numeric
;;  prefix args, such as `C-u C-u'.)
;;
;;  As usual, to insert a bookmark link, you use command
;;  `org-insert-link'.  Enter the name of the target bookmark at the
;;  prompt.  In Org mode you can use the usual Org key bindings to
;;  follow the link.  In any mode you can use standard Org command
;;  `org-open-at-point-global' (not bound to a key by default).
 
;;(@* "Use Bookmark+ with Icicles")
;;  ** Use Bookmark+ with Icicles **
;;
;;  `Icicles' (http://www.emacswiki.org/Icicles) enhances your use of
;;  Bookmark+ in several ways.
;;
;;  When jumping to a bookmark, you can narrow the completion
;;  candidates to bookmarks of a particular type (e.g. Info, using
;;  `C-M-i'; remote, using `C-M-@'; region, using `C-M-r').  You can
;;  narrow again (and again), to another bookmark type, to get the
;;  intersection (e.g. remote Info bookmarks that define a region).
;;
;;  You can also narrow against different bookmark-name patterns
;;  (e.g. regexps) - so-called "progressive completion".  And take the
;;  complement (e.g., bookmarks whose names do not match
;;  `foo.*2010.*bar').  (This is not special to bookmarks; it is
;;  standard `Icicles' practice.)
;;
;;  In Icicle mode, several of the Bookmark+ keys are remapped to
;;  corresponding `Icicles' multi-commands.  A bookmark jump key thus
;;  becomes a bookmarks browser.  For example, `C-x j d' browses among
;;  any number of Dired bookmarks.
;;
;;  A single key can set a bookmark or visit bookmarks.  This key is
;;  whatever command `bmkp-bookmark-set-confirm-overwrite' would
;;  normally be bound to - e.g. `C-x r m'.  A prefix arg controls what
;;  it does.  If negative (`M--'), jump to (browse) bookmarks.
;;  Otherwise, set a bookmark using
;;  `bmkp-bookmark-set-confirm-overwrite', as follows:
;;
;;  * No prefix arg: Prompt for the bookmark name.  The candidates are
;;    bookmarks in the current buffer (or all bookmarks if there are
;;    none in the current buffer).
;;
;;  * (Non-negative) numeric prefix arg: No prompt.  Use the buffer
;;    name plus the text of the region (if active) or the current line
;;    as the bookmark name.  Quickest way to set a bookmark.
;;
;;  * Plain `C-u': Prompt for name, no bookmark overwrite.
;;
;;  During completion of a bookmark name, many features of the
;;  bookmark-list display (see (@> "The Bookmark List Display")) are
;;  available on the fly.  Buffer `*Completions*' acts like a dynamic
;;  version of `*Bookmark List*':
;;
;;  * Candidates are highlighted in the `*Completions*' window
;;    according to their bookmark type.
;;
;;  * Candidates are `Icicles' multi-completions with up to three
;;    parts:
;;
;;     a. the bookmark name
;;     b. the bookmark file or buffer name
;;     c. any tags
;;
;;    You can match any or all of the parts.  For example, you can
;;    match bookmarks that have tags by typing this regexp:
;;
;;    C-M-j . * C-M-j S-TAB
;;
;;    Each `C-M-j' inserts `^G\n', which is `icicle-list-join-string',
;;    the string used to join the parts.  This regexp says, "match the
;;    completion candidates that have all three parts (two join
;;    strings)", hence some tags.
;;
;;    You can turn off the use of multi-completion candidates for
;;    subsequent commands, so only bookmark names are used, by hitting
;;    `M-m' in the minibuffer.  You can think of this as similar to
;;    using `M-t' in `*Bookmark List*' to toggle showing file names.
;;    You can make not showing files and tags the default behavior by
;;    customizing `icicle-show-multi-completion-flag'.
;;
;;  * You can sort completion candidates using the Bookmark+ sort
;;    orders.  Use `C-,' to cycle among sort orders.
;;
;;  * You can use `Icicles' candidate-help keys (`C-M-RET',
;;    `C-M-down', etc.) to get detailed information about the current
;;    bookmark candidate.  `C-u C-M-RET' shows the complete, internal
;;    info defining the bookmark.  And without doing anything, summary
;;    info about the current candidate is available in the mode line
;;    of buffer `*Completions*'.
;;
;;  * You can use `Icicles' candidate-action keys (`C-RET',
;;    `C-mouse-2', `C-down', etc.) to visit any number of bookmarks.
;;    For example, holding down `C-down' cycles among the current
;;    bookmark candidates, opening each in turn.
;;
;;  * You can use `S-delete' to delete the bookmark named by the
;;    current candidate.  You can delete any number of bookmarks this
;;    way, during a single invocation of a bookmark command.
;;
;;  * You can define `Icicles' sets of bookmarks, persistent or not,
;;    and act on their members in various ways.
;;
;;  During file-name completion, you can do any of the following on
;;  the fly:
;;
;;  * Jump to one or more file bookmarks, using `C-x m'.
;;
;;  * Create one or more autofile bookmarks, using `C-x a a'.
;;
;;  * Add tags to one or more files (autofile bookmarks), using `C-x a
;;    +'.
;;
;;  * Remove tags from one or more files (autofile bookmarks), using
;;    `C-x a -'.
;;
;;  There are 25 Icicles commands for searching bookmark destinations!
;;  The most general is `icicle-search-bookmark'.  Others let you
;;  search specific kinds of bookmarks, or bookmarks having various
;;  combinations of tags.
;;
;;  During Icicles search (of anything, not just a bookmark
;;  destination), you can save sets of completion candidates, which
;;  means sets of search hits, as bookmarks.  And Icicles lets you use
;;  set operations (complement, union, intersection, difference etc.)
;;  on the current set of search hits.
;;
;;  When you "jump" to an Icicles search-hits bookmark, its recorded
;;  search hits are restored to Icicles search as completion
;;  candidates, either replacing the current candidates or adding to
;;  them.
;;
;;  You can thus save and later return to different sets of search
;;  results using different bookmarks.  You can "jump" to an Icicles
;;  search-hits bookmark during any Icicles search, whether you search
;;  a file, a buffer, multiple files, or multiple buffers.
 
;;(@* "Bookmark Compatibility with Vanilla Emacs (`bookmark.el')")
;;  ** Bookmark Compatibility with Vanilla Emacs (`bookmark.el') **
;;
;;  Bookmark+ is generally compatible with GNU Emacs versions 20 and
;;  later.  You can use bookmarks with Bookmark+ regardless of whether
;;  they were created using Bookmark+ or vanilla Emacs (i.e., library
;;  `bookmark.el').
;;
;;  But for best results, if you have bookmarks that you created using
;;  Bookmark+ then use Bookmark+, not vanilla Emacs, to access them.
;;  This section provides details.
;;
;;  Set user option `bmkp-propertize-bookmark-names-flag', depending
;;  on your usage scenario (the default is `t' for Emacs 21 and later,
;;  `nil' for Emacs 20):
;;
;;  1. Set it to `nil' if you will often be going back and forth
;;     between using Bookmark+ and using vanilla Emacs.  (Do this also
;;     if you use Emacs 20.)
;;
;;  2. Set it to non-`nil' if you instead always use only Bookmark+
;;     (with Emacs 21 or later), or you use vanilla Emacs only to jump
;;     to bookmarks but never to update or create bookmarks.
;;
;;  #1 is VERY IMPORTANT.  You can lose data if you do not respect it.
;;
;;  The reason for rule #1 is this: When the option is non-`nil'
;;  Bookmark+ writes bookmarks to your bookmark file in a format that
;;  can be read and used by vanilla Emacs (21 and later) but which
;;  vanilla Emacs then saves as unreadable.  If the option value is
;;  `nil' there is no such problem.
;;
;;  #2 is not a requirement.  It is just a good idea, to be able to
;;  take better advantage of Bookmark+.  If you set the option to
;;  `nil' then you cannot use multiple bookmarks that have the same
;;  name.  Vanilla Emacs does not make good use of such critters, but
;;  Bookmark+ does.  Having multiple bookmarks with the same name is
;;  particularly useful for autofiles.  It means you can have
;;  different autofiles in different directories but with the same
;;  name. See (@> "Autofile Bookmarks").
;;
;;  Here is what happens when `bmkp-propertize-bookmark-names-flag' is
;;  non-nil:
;;
;;  Besides its name, which is what you see and use most of the time,
;;  a bookmark contains other information such as the target location,
;;  textual context hints, and last access time.  Non-`nil'
;;  `bmkp-propertize-bookmark-names-flag' has no effect on vanilla
;;  Emacs, but it causes Bookmark+ to put the full bookmark
;;  information on the bookmark name as a text property.
;;
;;  The name thus encapsulates all of the information contained in the
;;  full bookmark of which it is part.  Knowing the name is then
;;  enough to know everything about the bookmark.  Part of the
;;  bookmark (its name) refers to the whole of it.  In Lisp this
;;  self-reference is implemented using circular structures.
;;
;;  When Bookmark+ saves such circular structures to your bookmark
;;  file, if the option is non-`nil' then it takes care to do so in
;;  such a way that they can be read in again when your bookmark file
;;  is loaded.  In Lisp terms, it binds `print-circle' to non-`nil'
;;  when it writes your bookmarks.  If the option value is `nil' then
;;  the circularity (self-reference) is removed before your bookmarks
;;  are saved.  Either way, the file is readable.
;;
;;  Vanilla Emacs (21 and later) has no problem reading your bookmark
;;  file if it contains such circular structures.  But if you then use
;;  it to save the file again, the Lisp code it writes has invalid
;;  Lisp `read' syntax (because it does not remove the circularity but
;;  it also does not bind `print-circle' to non-`nil').
;;
;;  If that happens, the result is a bookmark file that is UNREADABLE.
;;  It cannot be loaded into either vanilla Emacs or Bookmark+.  If
;;  you do not have an uncorrupted backup version of the file to
;;  revert to, then you will need to edit it by hand to clean it up.
;;
;;  So do not let that happen to you!  For best results use only
;;  Bookmark+ to access bookmarks created using Bookmark+.
;;
;;  If you must use vanilla Emacs with your bookmarks, then make sure
;;  they are not saved by Bookmark+ with the option non-`nil': Using
;;  Bookmark+, set the option to `nil' and then save the file.
;;
;;  That is:
;;
;;  1. `M-x set-variable bmkp-propertize-bookmark-names-flag nil',
;;     to stop using propertized bookmark names.
;;  2. `C-x p e' or `C-x r l', to display the bookmark list.
;;  3. `g', to refresh the display.
;;  4. `S', to save the bookmark list.
;;  5. `M-x bmkp-save-menu-list-state', to save the display state.
;;
;;  Then you can use your bookmark file with vanilla Emacs (but
;;  without the possibility of having multiple bookmarks with the same
;;  name).
;;
;;  Note that when the option value is non-`nil', propertized bookmark
;;  names are saved not only to your bookmark file but also to any
;;  full snapshots you create of the bookmark-list display state using
;;  command `bmkp-bmenu-define-full-snapshot-command' (`C-c C-C', aka
;;  `C-c C-S-c').  See (@> "State-Restoring Commands and Bookmarks").
 
;;(@* "New Bookmark Structure")
;;  ** New Bookmark Structure **
;;
;;  The bookmark data structure, variable `bookmark-alist', has been
;;  enhanced to support new bookmark types.  For a description of this
;;  enhanced structure, use `C-h v bookmark-alist'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
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
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

;; You need not load this file.  It contains only documentation.

(provide 'bookmark+-doc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-doc.el ends here

