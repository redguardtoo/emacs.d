;;; mic-paren.el --- advanced highlighting of matching parentheses

;;; Copyright (C) 2008, 2012, 2013 Thien-Thi Nguyen
;;; Copyright (C) 1997 Mikael Sjödin (mic@docs.uu.se)

;; Version: 3.11
;; Package-Version: 20140714.719
;; Released: 2013-09-20
;; Author: Mikael Sjödin (mic@docs.uu.se)
;;         Klaus Berndl  <berndl@sdm.de>
;;         Jonathan Kotta <jpkotta@gmail.com>
;; Maintainer: ttn
;; Keywords: languages, faces, parenthesis, matching
;;
;; This program contains additional code by:
;; - Vinicius Jose Latorre <vinicius@cpqd.br>
;; - Steven L Baur <steve@xemacs.org>
;; - Klaus Berndl  <berndl@sdm.de>
;; - ttn
;;
;; mic-paren.el is free software
;;
;; This file is *NOT* (yet?) part of GNU Emacs.
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
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; ----------------------------------------------------------------------
;; Short Description:
;;
;; Load this file, activate it and Emacs will display highlighting on
;; whatever parenthesis (and paired delimiter if you like this) matches
;; the one before or after point.  This is an extension to the paren.el
;; file distributed with Emacs.  The default behaviour is similar to
;; paren.el but more sophisticated.  Normally you can try all default
;; settings to enjoy mic-paren.
;;
;; Some examples to try in your ~/.emacs:
;;
;;  (add-hook 'LaTeX-mode-hook
;;            (function (lambda ()
;;                        (paren-toggle-matching-quoted-paren 1)
;;                        (paren-toggle-matching-paired-delimiter 1))))
;;
;;  (add-hook 'c-mode-common-hook
;;            (function (lambda ()
;;                         (paren-toggle-open-paren-context 1))))
;;
;; If you use CUA mode, these might be useful, too:
;;
;;  (put 'paren-forward-sexp 'CUA 'move)
;;  (put 'paren-backward-sexp 'CUA 'move)
;;
;; ----------------------------------------------------------------------
;; Installation:
;;
;; o Place this file in a directory in your `load-path' and byte-compile
;;   it.  If there are warnings, please report them to ttn.
;; o Put the following in your .emacs file:
;;      (require 'mic-paren) ; loading
;;      (paren-activate)     ; activating
;;      ;;; set here any of the customizable variables of mic-paren:
;;      ;;; ...
;; o Restart your Emacs; mic-paren is now installed and activated!
;; o To list the possible customizations type `C-h f paren-activate' or
;;   go to the customization group `mic-paren-matching'.
;;
;; ----------------------------------------------------------------------
;; Long Description:
;;
;; mic-paren.el is an extension and replacement to the packages paren.el
;; and stig-paren.el for Emacs.  When mic-paren is active Emacs normal
;; parenthesis matching is deactivated.  Instead parenthesis matching will
;; be performed as soon as the cursor is positioned at a parenthesis.  The
;; matching parenthesis (or the entire structured expression between the
;; parentheses) is highlighted until the cursor is moved away from the
;; parenthesis.  Features include:
;; o Both forward and backward parenthesis matching (simultaneously if
;;   cursor is between two expressions).
;; o Indication of mismatched parentheses.
;; o Recognition of "escaped" (also often called "quoted") parentheses.
;; o Recognition of SML-style "sexp-ish" comment syntax.
;;   NB: This support is preliminary; there are still problems
;;       when the parens in the comment span multiple lines, etc.
;; o Option to match "escaped" parens too, especially in (La)TeX-mode
;;   (e.g., matches expressions like "\(foo bar\)" properly).
;; o Offers two functions as replacement for `forward-sexp' and
;;   `backward-sexp' which handle properly quoted parens (s.a.).  These
;;   new functions can automatically be bounded to the original binding
;;   of the standard `forward-sexp' and `backward-sexp' functions.
;; o Option to activate matching of paired delimiter (i.e., characters with
;;   syntax '$').  This is useful for writing in LaTeX-mode for example.
;; o Option to select in which situations (always, never, if match, if
;;   mismatch) the entire expression should be highlighted or only the
;;   matching parenthesis.
;; o Message describing the match when the matching parenthesis is off-screen
;;   (vertical and/or horizontal).  Message contains either the linenumber or
;;   the number of lines between the two matching parens.  Option to select in
;;   which cases this message should be displayed.
;; o Optional delayed highlighting (useful on slow systems),
;; o Functions to activate/deactivate mic-paren.el are provided.
;; o Numerous options to control the behaviour and appearance of
;;   mic-paren.el.
;;
;; mic-paren.el was originally developed and tested under Emacs 19.28 -
;; 20.3.  Since then, support for Emacs 19 and 20 has bit-rotted (not
;; dropped completely, but not tested against changes, either), and
;; will probably be removed without warning in a future version.  This
;; version was developed and tested under Emacs 23.0.60 (wip).  XEmacs
;; compatibility has been provided by Steven L Baur <steve@xemacs.org>.
;; Jan Dubois (jaduboi@ibm.net) provided help to get mic-paren to work in
;; OS/2.
;;
;; This file (and other wonderful stuff) can be obtained from
;; the Emacs Wiki: <http://www.emacswiki.org/>
;;
;; ----------------------------------------------------------------------
;; Available customizable options:
;; - `paren-priority'
;; - `paren-overlay-priority'
;; - `paren-sexp-mode'
;; - `paren-highlight-at-point'
;; - `paren-highlight-offscreen'
;; - `paren-display-message'
;; - `paren-message-linefeed-display'
;; - `paren-message-no-match'
;; - `paren-message-show-linenumber'
;; - `paren-message-truncate-lines'
;; - `paren-max-message-length'
;; - `paren-ding-unmatched'
;; - `paren-delay'
;; - `paren-dont-touch-blink'
;; - `paren-match-face'
;; - `paren-mismatch-face'
;; - `paren-no-match-paren'
;; - `paren-bind-modified-sexp-functions'
;; Available customizable faces:
;; - `paren-face-match'
;; - `paren-face-mismatch'
;; - `paren-face-no-match'
;; Available commands:
;; - `paren-activate'
;; - `paren-deactivate'
;; - `paren-toggle-matching-paired-delimiter'
;; - `paren-toggle-matching-quoted-paren'
;; - `paren-toggle-open-paren-context'
;; - `paren-forward-sexp'
;; - `paren-backward-sexp'
;; ----------------------------------------------------------------------
;;
;; IMPORTANT NOTES (important for people who have customized mic-paren
;;                  from within elisp):
;; - In version >= 3.3 the prefix "mic-" has been removed from the
;;   command-names `mic-paren-forward-sexp' and `mic-paren-backward-sexp'.
;;   Now all user-functions and -options begin with the prefix "paren-"
;;   because this package should be a replacement of the other
;;   paren-packages like paren.el and stig-paren.el!
;; - In version >= 3.2 the prefix "mic-" has been removed from the
;;   command-names `mic-paren-toggle-matching-quoted-paren' and
;;   `mic-paren-toggle-matching-paired-delimiter'.
;; - In versions >= 3.1 mic-paren is NOT auto-activated after loading.
;; - In versions >= 3.0 the variable `paren-face' has been renamed to
;;   `paren-match-face'.
;;
;; ----------------------------------------------------------------------
;; Versions:
;; v3.11   + Added support for recognizing SML-style comments as a sexp.
;;           Thanks to Leo Liu, Stefan Monnier.
;;
;; v3.10   + Added message-length clamping (var `paren-max-message-length').
;;           Thanks to Jonathan Kotta.
;;
;; v3.9    + Fixed XEmacs bug in `define-mic-paren-nolog-message'.
;;           Thanks to Sivaram Neelakantan.
;;
;; v3.8    + Maintainership (crassly) grabbed by ttn.
;;         + License now GPLv3+.
;;         + Byte-compiler warnings eliminated; if you see one, tell me!
;;         + Dropped funcs: mic-char-bytes, mic-char-before.
;;         + Docstrings, messages, comments revamped.
;;
;; v3.7    + Removed the message "You should be in LaTeX-mode!".
;;         + Fixed a bug in `paren-toggle-matching-quoted-paren'.
;;         + Fixed some misspellings in the comments and docs.
;;
;; v3.6    + Fixed a very small bug in `mic-paren-horizontal-pos-visible-p'.
;;         + The informational messages like "Matches ... [+28]" which are
;;           displayed if the matching paren is offscreen, do not longer
;;           wasting the log.
;;
;; v3.5    + No mic-paren-messages are displayed if we are in isearch-mode.
;;         + Matching quoted parens is switched on if entering a minibuffer.
;;           This is useful for easier inserting regexps, e.g., with
;;           `query-replace-regexp'.  Now \(...\) will be highlighted
;;           in the minibuffer.
;;         + New option `paren-message-show-linenumber': You can determine
;;           the computation of the offscreen-message-linenumber.  Either the
;;           number of lines between the two matching parens or the absolute
;;           linenumber.  (Thank you for the idea and a first implementation
;;           to Eli Barzilay <eli@barzilay.org>.)
;;         + New option `paren-message-truncate-lines': If mic-paren messages
;;           should be truncated or not (has only an effect in GNU Emacs 21).
;;           (Thank you for the idea and a first implementation to Eli
;;           Barzilay <eli@barzilay.org>.)
;;
;; v3.4    + Corrected some bugs in the backward-compatibility for older
;;           Emacsen.  Thanks to Tetsuo Tsukamoto <czkmt@remus.dti.ne.jp>.
;;
;; v3.3    + Now the priority of the paren-overlays can be customized
;;           (option `paren-overlay-priority').  For a description of the
;;           priority of an overlay see in the emacs-lisp-manual the node
;;           "Overlays".  This option is mainly useful for experienced
;;           users which use many packages using overlays to perform their
;;           tasks.
;;         + Now you can determine what line-context will be displayed if
;;           the matching open paren is offscreen.  In functional
;;           programming languages like lisp it is useful to display the
;;           following line in the echo-area if the opening matching paren
;;           has no preceding text in the same line.
;;           But in procedural languages like C++ or Java it is convenient
;;           to display the first previous non empty line in this case
;;           instead of the following line.  Look at the new variable
;;           `paren-open-paren-context-backward' and the related toggling
;;           function `paren-toggle-open-paren-context' for a detailed
;;           description of this new feature.
;;         + In addition to the previous described new feature you can
;;           specify how a linefeed in the message (e.g., if the matching
;;           paren is offscreen) is displayed.  This is mainly because the
;;           standard echo-area display of a linefeed (^J) is bad to read.
;;           Look at the option `paren-message-linefeed-display'.
;;         + Solved a little bug in the compatibility-code for Emacsen
;;           not supporting current customize-feature.
;;         + Removed the prefix "mic-" from the commands
;;           `mic-paren-forward-sexp' and `mic-paren-backward-sexp'.
;;           For an explanation look at comments for version v3.2.
;;
;; v3.2    + The prefix "mic-" has been removed from the commands
;;           `mic-paren-toggle-matching-quoted-paren' and
;;           `mic-paren-toggle-matching-paired-delimiter'.  This is for
;;           consistency.  Now all user-variables, -faces and -commands
;;           begin with the prefix "paren-" and all internal functions
;;           and variables begin with the prefix "mic-paren-".
;;         + Now you can exactly specify in which situations the whole
;;           sexp should be highlighted (option `paren-sexp-mode'):
;;           Always, never, if match or if mismatch.  Tested with Gnus
;;           Emacs >= 20.3.1 and XEmacs >= 21.1.
;;
;; v3.1    + From this version on mic-paren is not autoloaded.  To
;;           activate it you must call `paren-activate' (either in your
;;           .emacs or manually with M-x).  Therefore the variable
;;           `paren-dont-activate-on-load' ise obsolet and has been
;;           removed.
;;         + Now mic-paren works also in older Emacsen without the
;;           custom-feature.  If the actual custom-library is provided
;;           mic-paren use them and is full customizable otherwise normal
;;           defvars are used for the options.
;;         + Fix of a bug displaying a message if the matching paren is
;;           horizontal out of view.
;;         + All new features are now tested with XEmacs >= 21.1.6.
;;
;; v3.0    + Checking if matching paren is horizontally offscreen (in
;;           case of horizontal scrolling).  In that case the message is
;;           displayed in the echo-area (anlogue to vertical offscreen).
;;           In case of horizontal offscreen closing parenthesis the
;;           displayed message is probably wider than the frame/window.
;;           So you can only read the whole message if you are using a
;;           package like mscroll.el (scrolling long messages) in GNU
;;           Emacs.
;;         + Now full customizable, means all user-options and -faces now
;;           can be set with the custom-feature of Emacs.  On the other
;;           hand, this means this version of mic-paren only works with an
;;           Emacs which provides the custom-package!
;;         + In case of the matching paren is offscreen now the displayed
;;           message contains the linenumber of the matching paren too.
;;         This version is only tested with Gnu Emacs >= 20.4 and not with
;;         any XEmacs!
;;         Implemented by Klaus Berndl <berndl@sdm.de>.
;;
;; v2.3    No additional feature but replacing `char-bytes' and
;;         `char-before' with `mic-char-bytes' and `mic-char-before' to
;;         prevent a clash in the global-namespace.  Now the new
;;         features of v2.1 and v2.2 are also tested with XEmacs!
;;
;; v2.2    Adding the new feature for matching paired delimiter.  Not
;;         tested with XEmacs.  Implemented by Klaus Berndl <berndl@sdm.de>
;;
;; v2.1    Adding the new feature for matching escaped parens too.  Not
;;         tested with XEmacs.  Implemented by Klaus Berndl <berndl@sdm.de>.
;;
;; v2.0    Support for MULE and Emacs 20 multibyte characters added.
;;         Inspired by the suggestion and code of Saito Takaaki
;;         <takaaki@is.s.u-tokyo.ac.jp>.
;;
;; v1.9    Avoids multiple messages/dings when point has not moved.  Thus,
;;         mic-paren no longer overwrites messages in minibuffer.  Inspired by
;;         the suggestion and code of Eli Barzilay <eli@barzilay.org>.
;;
;; v1.3.1  Some spelling corrected (from Vinicius Jose Latorre
;;         <vinicius@cpqd.br> and Steven L Baur <steve@xemacs.org>).
;;
;; v1.3    Added code from Vinicius Jose Latorre <vinicius@cpqd.br> to
;;         highlight unmatched parentheses (useful in minibuffer).
;;
;; v1.2.1  Fixed stuff to work with OS/2 emx-emacs:
;;          - checks if `x-display-colour-p' is bound before calling it;
;;          - changed how X/Lucid Emacs is detected.
;;         Added automatic load of the timer-feature (plus variable to
;;         disable the loading).

;;; Code:

(defvar mic-paren-version "3.11"
  "Version of mic-paren.")

(eval-when-compile (require 'cl))

;;; ======================================================================
;; Compatibility stuff
;; BLOB to make custom stuff work even without customize
(eval-and-compile
  (condition-case ()
      (require 'custom)
    (error nil))
  (unless (fboundp 'defgroup)
    (defmacro defgroup (&rest rest) nil))
  (unless (fboundp 'defcustom)
    (defmacro defcustom (sym val str &rest rest)
      `(defvar ,sym ,val ,str)))
  (unless (fboundp 'defface)
    (defmacro defface (sym val str &rest rest)
      `(defvar ,sym (make-face ',sym) ,str))))

;;; ======================================================================
;;; here begin the user options

(defgroup mic-paren-matching nil
  "Enable advanced (un)matching of parens and expressions."
  :prefix "paren-"
  :group 'paren-matching)

(defcustom paren-priority 'both
  "*Control behavior in a \"abutted close-open\" situation.
This occurs when point is between a closing and an opening
parenthesis, such as: (A B)(C D)
                           ^
                         point
close -- highlight the parenthesis matching the close-parenthesis
         before the point (highlight opening paren before A).
open  -- highlight the parenthesis matching the open-parenthesis after
         the point (highlight closing paren after D).
both  -- highlight both parenthesis matching the parenthesis beside
         the point (highlight opening before A and closing after D)."
  :type '(choice (const :tag "Match close" close)
                 (const :tag "Match open" open)
                 (const :tag "Match both" both))
  :group 'mic-paren-matching)

(defcustom paren-overlay-priority 999
  "*Non-negative integer to specify paren overlay priority.
For details, see info node `(elisp) Overlays'.
Normally you don't want to change the default value!"
  :set (function
        (lambda (symbol value)
          (set symbol (if (< value 0) (* -1 value) value))))
  :initialize 'custom-initialize-default
  :type 'integer
  :group 'mic-paren-matching)

(defcustom paren-sexp-mode nil
  "*Control in which situations the whole sexp should be highlighted.
This means the whole s-expression between the matching parentheses is
highlighted instead of only the matching/mismatching parenthesis.

t        -- Always highlight the whole s-expression.
nil      -- Never highlight the whole s-expression.
match    -- Highlight the whole s-expression only if the parens match.
mismatch -- Highlight the whole s-expression only if the parens don't match."
  :type '(choice (const :tag "Never sexp-mode" nil)
                 (const :tag "Always sexp-mode" t)
                 (const :tag "If match" match)
                 (const :tag "If mismatch" mismatch))
  :group 'mic-paren-matching)

(defcustom paren-highlight-at-point t
  "*Non-nil highlights both parens when point is after the close-paren.
If nil, only the open parenthesis is highlighted."
  :type '(choice (const :tag "Highlight both" t)
                 (const :tag "Highlight open" nil))
  :group 'mic-paren-matching)

(defcustom paren-highlight-offscreen nil
  "*Non-nil enables highlighting text not visible in the current buffer.

This is useful if you regularly display the current buffer in
multiple windows or frames (e.g., if you use Follow mode, by
andersl@csd.uu.se).  Note: this option may slow down your Emacs.

This variable is ignored (treated as non-nil) if you set
`paren-sexp-mode' to non-nil."
  :type 'boolean
  :group 'mic-paren-matching)

(defcustom paren-display-message 'only
  "*Display message if matching parenthesis is off-screen.
Possible settings are:
always -- message is always displayed regardless if offscreen or not
only   -- message is only displayed when matching is offscreen
never  -- never a message is displayed."
  :type '(choice (const :tag "Display always" always)
                 (const :tag "Display if offscreen" only)
                 (const :tag "No Message display" never))
  :group 'mic-paren-matching)

(defcustom paren-message-linefeed-display " RET "
  "*String for displaying a linefeed in the matching paren context message.
There are three predefined values:
- Displays linefeeds with \" RET \" in the message.
- Displays linefeeds with a SPACE in the message.
- Displays linefeeds in the standard-form, means with \"^J\".
But you can also specify any user-defined string for it.

For further explanations about message displaying look at
`paren-display-message'."
  :type '(choice (const :tag "Display with \"RET\"" :value " RET ")
                 (const :tag "Display with a SPACE" :value " ")
                 (const :tag "Standard" :value "^J")
                 (string :tag "User defined"))
  :group 'mic-paren-matching)

(defcustom paren-message-show-linenumber 'sexp
  "*Determine the computation of the offscreen-message-linenumber.

If the matching paren is offscreen, then maybe a message with the
context of the matching paren and it's linenumber is displayed
\(depends on the setting in `paren-display-message').  Here the
computation of the linenumber can be determined:

sexp -- Display the number of lines between the matching parens.  Then the
        number of lines is displayed as negative number if the matching paren
        is somewhere above.  Otherwise the number has a positive sign.

absolute -- Display the absolute linenumber of the machting paren computed
            from the beginning of the buffer."
  :type '(choice (const :tag "Count accros sexp" sexp)
                 (const :tag "Absolute number" absolute))
  :group 'mic-paren-matching)

(defcustom paren-message-no-match t
  "*Display message if no matching parenthesis is found."
  :type '(choice (const :tag "Display message" t)
                 (const :tag "No message" nil))
  :group 'mic-paren-matching)

(defcustom paren-message-truncate-lines t
  "*Non nil means truncate lines for all messages mic-paren can display.
This option has only an effect with GNU Emacs 21.x!"
  :type 'boolean
  :group 'mic-paren-matching)

(defcustom paren-max-message-length 0
  "*If positive, the max length `mic-paren-nolog-message' should output.
The length is reduced by removing the middle section of the message.
A value of zero means do not modify the message."
  :type 'integer
  :group 'mic-paren-matching)

(defcustom paren-ding-unmatched nil
  "*Non-nil means make noise in unmatched situations.
An unmatched situation occurs if the cursor is at an unmatched
parenthesis or no matching parenthesis is found.
Even if nil, typing an unmatched parenthesis produces a ding."
  :type 'boolean
  :group 'mic-paren-matching)

(defcustom paren-delay nil
  "*This variable controls when highlighting is done.
The variable has different meaning in different versions of Emacs.

In Emacs 19.29 and below:
  This variable is ignored.

In Emacs 19.30:
  A value of nil will make highlighting happen immediately \(this may slow
  down your Emacs if running on a slow system).  Any non-nil value will
  delay highlighting for the time specified by post-command-idle-delay.

In Emacs 19.31 and above:
  A value of nil will make highlighting happen immediately \(this may slow
  down your Emacs if running on a slow system).  If not nil, the value
  should be a number \(possible a floating point number if your Emacs
  support floating point numbers).  The number is the delay in seconds
  before mic-paren performs highlighting.

If you change this variable when mic-paren is active you have to
re-activate \(with M-x paren-activate) mic-paren for the change to take
effect."
  :type '(choice (number :tag "Delay time")
                 (const :tag "No delay" nil))
  :group 'mic-paren-matching)

(defcustom paren-dont-touch-blink nil
  "*Non-nil means not to change the value of `blink-matching-paren'.
This takes effect when mic-paren is activated or deactivated.  If nil
mic-paren turns of blinking when activated and turns on blinking when
deactivated."
  :type 'boolean
  :group 'mic-paren-matching)

(defcustom paren-dont-load-timer (not (string-match "XEmacs\\|Lucid"
                                                    emacs-version))
  "*Non-nil inhibits loading `timer'.

\(I have no idea why Emacs user ever want to set this to non-nil but I hate
packages which loads/activates stuff I don't want to use so I provide this
way to prevent the loading if someone doesn't want timers to be loaded.)"
  :type 'boolean
  :group 'mic-paren-matching)

(defcustom paren-bind-modified-sexp-functions t
  "*Automatic binding of the new sexp-functions to the old bindings.
If non nil mic-paren checks at load-time the keybindings for the functions
`forward-sexp' and `backward-sexp' and binds the modified sexp-functions
`paren-forward-sexp' and `paren-backward-sexp' to exactly these
bindings if and only if matching quoted/escaped parens is turned on by
`paren-toggle-matching-quoted-paren'.  These new bindings are done only
in a buffer-local keymap, therefore if you activate the quoted matching
only in some modes from within a hook only in these buffers the new
bindings are active and in all other not.

If you deactivate the quoted matching feature by
`paren-toggle-matching-quoted-paren' then `forward-sexp' and
`backward-sexp' will be bound again to their original key-bindings!"
  :type 'boolean
  :group 'mic-paren-matching)

;;; ------------------------------
;;; Faces
;;; ------------------------------

(defface paren-face-match
  '((((class color)) (:background "turquoise"))
    (t (:background "gray")))
  "Mic-paren mode face used for a matching paren."
  :group 'faces
  :group 'mic-paren-matching)

(defface paren-face-mismatch
  '((((class color)) (:foreground "white" :background "purple"))
    (t (:reverse-video t)))
  "Mic-paren mode face used for a mismatching paren."
  :group 'faces
  :group 'mic-paren-matching)

(defface paren-face-no-match
  '((((class color)) (:foreground "black" :background "yellow"))
    (t (:reverse-video t)))
  "Mic-paren mode face used for an unmatched paren."
  :group 'faces
  :group 'mic-paren-matching)

(defcustom paren-match-face 'paren-face-match
  "*Face to use for showing the matching parenthesis."
  :type 'face
  :group 'mic-paren-matching)

(defcustom paren-mismatch-face 'paren-face-mismatch
  "*Face to use when highlighting a mismatched parenthesis."
  :type 'face
  :group 'mic-paren-matching)

(defcustom paren-no-match-face 'paren-face-no-match
  "*Face to use when highlighting an unmatched parenthesis."
  :type 'face
  :group 'mic-paren-matching)

;;; End of User Options
;;; ======================================================================

;;; Below there are only variables and options which either should be not
;;; set directly but with toggle-functions or pure internal variables.

(defvar paren-match-quoted-paren nil
  "*Non-nil enables matching properly quoted (or escaped) parens.
E.g., \"\\\(x-3y + z = 7\\\)\"\) in a TeX file.  GNU Emacs can not match
quoted parens, so we must temporally deactivate the quoting until emacs
has done its sexp-parsing.  Therefore emacs itself does not \(can not!\)
take into consideration if either both matched parens are quoted or none.
But nevertheless we do this!  Only symmetric balanced parens are matched;
either both matching parens must be quoted or none, otherwise they we will
be highlighted as mismatched.

This package offers also two slightly modified versions of sexp traversal
functions: `paren-forward-sexp' and `paren-backward-sexp'.  These versions
can also jump to escaped/quoted parens.

If this variable is not nil and `paren-bind-modified-sexp-functions' is
set to non nil, then `paren-toggle-matching-quoted-paren' will also toggle
the original binding of `forward-sexp' and `backward-sexp' between the
original functions and the modified equivalents.

Do NOT set this variable directly but use
`paren-toggle-matching-quoted-paren' to activate/deactivate/toggle this
feature!  The best method is to do this in a mode hook, e.g.:
\(add-hook \'LaTeX-mode-hook
          \(function \(lambda \(\)
                      \(paren-toggle-matching-quoted-paren 1\)\)\)\)")

(make-variable-buffer-local 'paren-match-quoted-paren)

(defvar paren-match-paired-delimiter nil
  "*Non-nil enables matching of characters with syntax \"$\".
E.g., in LaTeX \"$...$\" is equivalent to \"\\(...\\)\".
Unlike to parens quoted/escaped paired delimiter will never match.

Do NOT set this variable directly but use
`paren-toggle-matching-paired-delimiter' to activate/deactivate/toggle
this feature!  The best method is to do this in a mode hook, e.g.:
\(add-hook \'LaTeX-mode-hook
          \(function \(lambda \(\)
                      \(paren-toggle-matching-paired-delimiter 1\)\)\)\)")

(make-variable-buffer-local 'paren-match-paired-delimiter)

(defvar paren-open-paren-context-backward nil
  "*Controls which context of the matching open paren will be displayed.
This takes effect if the matching open paren is offscreen or
`paren-display-message' is `always' (see `paren-display-message')
and the matching open paren has no previous text in the same line.
Possible values:
nil -- Contents of the **next** not empty and not whitespace-line will be
  displayed.  This value is useful for example in functional programming
  languages like (emacs)lisp.
not-nil -- Contents of the first **previous** not empty and not only
  whitespace-line will be displayed.  This value is useful for example in
  procedural programming languages like C, C++, Java etc.

Lets take a look at a short example:
In languages like C++ we often have situations like
  if \(i > VALUE\)
  \{
      // some code
  \}
With a value non nil the displayed opening-brace context would be
\"if \(i > VALUE\)^J\{\" but with nil it would be \"\{^J // some code\"
which would be in C++ lesser useful as the non nil version.
\(The ^J stands for a newline in the buffer\).

Do NOT set this variable directly but use `paren-toggle-open-paren-context'
to change the value of this option!  The best method is to do this in a
mode hook, e.g.:
\(add-hook \'c-common-mode-hook
           \(function \(lambda \(\)
                         \(paren-toggle-open-paren-context 1\)\)\)\)")

(make-variable-buffer-local 'paren-open-paren-context-backward)

(defconst mic-paren-original-keybinding-of-sexp-functions
  (list (car (where-is-internal 'forward-sexp))
        (car (where-is-internal 'backward-sexp))))

;;; Compatibility.
;;; Try to make mic-paren work in different Emacs flavours.

;; XEmacs compatibility (mainly by Steven L Baur <steve@xemacs.org>).
(eval-and-compile
  (if (string-match "\\(Lucid\\|XEmacs\\)" emacs-version)
      (progn
        (fset 'mic-make-overlay 'make-extent)
        (fset 'mic-delete-overlay 'delete-extent)
        (fset 'mic-overlay-put 'set-extent-property)
        (fset 'mic-cancel-timer 'delete-itimer)
        (fset 'mic-run-with-idle-timer 'start-itimer))
    (fset 'mic-make-overlay 'make-overlay)
    (fset 'mic-delete-overlay 'delete-overlay)
    (fset 'mic-overlay-put 'overlay-put)
    (fset 'mic-cancel-timer 'cancel-timer)
    (fset 'mic-run-with-idle-timer 'run-with-idle-timer)))

(defun paren-clamp-string-maybe (str)
  "Remove the middle of STR if it exceeds `paren-max-message-length'.
However, if STR is `nil' or `paren-max-message-length' is zero,
simply return STR."
  (if (or (not str) (zerop paren-max-message-length))
      str
    (let ((len (string-width str)))
      (if (<= len paren-max-message-length)
          str
        (let* ((sep "[...]")
               (cut (ash (- paren-max-message-length
                            (string-width sep))
                         -1)))
          (concat (substring str 0 cut)
                  sep
                  (substring str (- len cut))))))))

(eval-when-compile
  (defmacro define-mic-paren-nolog-message (yes no)
    `(defun mic-paren-nolog-message (&rest args)
       "Work like `message' but without logging.
See variable `paren-max-message-length'."
       (let ((msg (paren-clamp-string-maybe
                   (cond ((or (null args)
                              (null (car args)))
                          nil)
                         ((null (cdr args))
                          (car args))
                         (t
                          (apply 'format args))))))
         (if msg ,yes ,no)
         msg))))

(eval-and-compile
  (if (and (fboundp 'display-message)
           (fboundp 'clear-message))
      ;; Some GNU Emacs versions need the `eval' so as to avoid saying:
      ;; > the following functions are not known to be defined:
      ;; >         display-message, clear-message
      (eval '(define-mic-paren-nolog-message
               (display-message 'no-log msg)
               (clear-message 'no-log)))
    (define-mic-paren-nolog-message
      (let (message-log-max) (message "%s" msg))
      (message nil))))

;;; ======================================================================
;;; Pure Internal variables

(defvar mic-paren-overlays (vector (mic-make-overlay 1 1)
                                   (mic-make-overlay 1 1)
                                   (mic-make-overlay 1 1))
  "Vector of of the form [BACKW POINT FOREW].

BACKW: Overlay for the open-paren which matches the close-paren
       before point.  When in sexp-mode this is the overlay for
       the expression before point.

POINT: Overlay for the close-paren before point.
       This is not used when is sexp-mode.

FOREW: Overlay for the close-paren which matches the open-paren
       after point.  When in sexp-mode this is the overlay for
       the expression after point.")

(defvar mic-paren-idle-timer nil
  "Idle-timer.
Used only in Emacs 19.31 and above (and if paren-delay is nil).")

(defvar mic-paren-previous-location [nil nil nil]
  "Where point was the last time mic-paren performed some action.
This is is a vector of the form [POINT BUFFER WINDOW].")

;;; ======================================================================
;;; User Functions

;;;###autoload
(defun paren-activate ()
  "Activate mic-paren parenthesis highlighting.
Note: This also deactivates the paren.el
and stig-paren.el packages if they are active!

The following options are available via the customize-feature:
  `paren-priority'
  `paren-overlay-priority'
  `paren-sexp-mode'
  `paren-highlight-at-point'
  `paren-highlight-offscreen'
  `paren-display-message'
  `paren-message-linefeed-display'
  `paren-message-no-match'
  `paren-message-show-linenumber'
  `paren-message-truncate-lines'
  `paren-ding-unmatched'
  `paren-delay'
  `paren-dont-touch-blink'
  `paren-match-face'
  `paren-mismatch-face'
  `paren-no-match-face'
  `paren-bind-modified-sexp-functions'

The following options are settable via toggling functions \(look at the
documentation of these options for the names of these functions\):
  `paren-match-quoted-paren'
  `paren-match-paired-delimiter'
  `paren-open-paren-context-backward'"
  (interactive)
  ;; Deactivate mic-paren.el (to remove redundant hooks).
  (paren-deactivate)
  ;; Deactivate paren.el if loaded.
  (when (boundp 'post-command-idle-hook)
    (remove-hook 'post-command-idle-hook 'show-paren-command-hook))
  (remove-hook 'post-command-hook 'show-paren-command-hook)
  (and (boundp 'show-paren-overlay)
       show-paren-overlay
       (mic-delete-overlay show-paren-overlay))
  (and (boundp 'show-paren-overlay-1)
       show-paren-overlay-1
       (mic-delete-overlay show-paren-overlay-1))
  ;; Deactivate stig-paren.el if loaded.
  (when (boundp 'post-command-idle-hook)
    (remove-hook 'post-command-idle-hook 'stig-paren-command-hook))
  (remove-hook 'post-command-hook 'stig-paren-command-hook)
  (remove-hook 'post-command-hook 'stig-paren-safe-command-hook)
  (remove-hook 'pre-command-hook 'stig-paren-delete-overlay)
  ;; Deactivate Emacs standard parenthesis blinking.
  (or paren-dont-touch-blink
      (setq blink-matching-paren nil))

  (cond(
        ;; If timers are available use them
        ;; (Emacs 19.31 and above).
        (featurep 'timer)
        (if (numberp paren-delay)
            (setq mic-paren-idle-timer
                  (mic-run-with-idle-timer paren-delay t
                                           'mic-paren-command-idle-hook))
          (add-hook 'post-command-hook 'mic-paren-command-hook)))
       ;; If the idle hook exists assume it is functioning and use it
       ;; (Emacs 19.30).
       ((and (boundp 'post-command-idle-hook)
             (boundp 'post-command-idle-delay))
        (if paren-delay
            (add-hook 'post-command-idle-hook 'mic-paren-command-idle-hook)
          (add-hook 'post-command-hook 'mic-paren-command-hook)))
       ;; Check if we (at least) have `post-comand-hook', and use it
       ;; (Emacs 19.29 and below).
       ((boundp 'post-command-hook)
        (add-hook 'post-command-hook 'mic-paren-command-hook))
       ;; Not possible to install mic-paren hooks
       (t (error "Cannot activate mic-paren in this Emacs version")))
  ;; We want matching quoted parens in the minibuffer to ease inserting
  ;; paren-expressions in a regexp.
  (add-hook 'minibuffer-setup-hook
            'mic-paren-minibuffer-setup-hook)
  (add-hook 'minibuffer-exit-hook
            'mic-paren-minibuffer-exit-hook))

;;;###autoload
(defun paren-deactivate ()
  "Deactivate mic-paren parenthesis highlighting."
  (interactive)
  ;; Deactivate (don't bother to check where/if mic-paren is acivte, just
  ;; delete all possible hooks and timers).
  (when (boundp 'post-command-idle-hook)
    (remove-hook 'post-command-idle-hook 'mic-paren-command-idle-hook))
  (when mic-paren-idle-timer
    (mic-cancel-timer mic-paren-idle-timer))
  (remove-hook 'post-command-hook 'mic-paren-command-hook)
  (remove-hook 'minibuffer-setup-hook
               'mic-paren-minibuffer-setup-hook)
  (remove-hook 'minibuffer-exit-hook
               'mic-paren-minibuffer-exit-hook)
  ;; Remove any old highlight.
  (mic-delete-overlay (aref mic-paren-overlays 0))
  (mic-delete-overlay (aref mic-paren-overlays 1))
  (mic-delete-overlay (aref mic-paren-overlays 2))

  ;; Reactivate Emacs standard parenthesis blinking.
  (or paren-dont-touch-blink
      (setq blink-matching-paren t)))

;;;###autoload
(defun paren-toggle-matching-paired-delimiter (arg &optional no-message)
  "Toggle matching paired delimiter.
Force on with positive ARG.  Use this in mode hooks to activate or
deactivate paired delimiter matching.  If optional second argument
NO-MESSAGE is non-nil then don't display a message about the
current activation state of the paired-delimiter-matching feature."
  (interactive "P")
  (setq paren-match-paired-delimiter (if (numberp arg)
                                         (> arg 0)
                                       (not paren-match-paired-delimiter)))
  (unless no-message
    (message "Matching paired delimiter is %s"
             (if paren-match-paired-delimiter
                 "ON"
               "OFF"))))

;;;###autoload
(defun paren-toggle-matching-quoted-paren (arg &optional no-message)
  "Toggle matching quoted parens.
Force on with positive ARG.  Use this in mode hooks to activate or
deactivate quoted paren matching.  If optional second argument
NO-MESSAGE is non-nil then don't display a message about the
current activation state of the quoted-paren-matching feature."
  (interactive "P")
  (setq paren-match-quoted-paren (if (numberp arg)
                                     (> arg 0)
                                   (not paren-match-quoted-paren)))
  ;; If matching quoted parens is active now bind the original binding
  ;; of forward-sexp and backward-sexp to the modified versions
  ;; `paren-forward-sexp' and `paren-backward-sexp'.  If not, bind
  ;; it back to the original `forward-sexp' and `backward-sexp'.
  (let ((f (car mic-paren-original-keybinding-of-sexp-functions))
        (b (cadr mic-paren-original-keybinding-of-sexp-functions))
        (funs (if paren-match-quoted-paren
                  '(paren-forward-sexp . paren-backward-sexp)
                '(forward-sexp . backward-sexp))))
    (when (and paren-bind-modified-sexp-functions b f)
      (local-set-key f (car funs))
      (local-set-key b (cdr funs))))
  (unless no-message
    (message "Matching quoted parens is %s"
             (if paren-match-quoted-paren
                 "ON"
               "OFF"))))

;;;###autoload
(defun paren-toggle-open-paren-context (arg)
  "Toggle whether or not to determine context of the matching open-paren.
Force backward context with positive ARG.  Use this in mode-hooks.
See `paren-open-paren-context-backward'."
  (interactive "P")
  (setq paren-open-paren-context-backward
        (if (numberp arg)
            (> arg 0)
          (not paren-open-paren-context-backward))))

;;;###autoload
(defun paren-forward-sexp (&optional arg)
  "Act like `forward-sexp' but also handle quoted parens.
See `paren-match-quoted-paren'."
  (interactive "p")
  (or arg (setq arg 1))
  (let* ((uncharquote-diff (if (< arg 0) 2 1))
         (match-check-diff (if (< arg 0) 1 2))
         (charquote (mic-paren-uncharquote (- (point) uncharquote-diff)))
         match-pos mismatch)
    ;; We must encapsulate this in condition-case so we regain control
    ;; after error and we can undo our unquoting if any done before!
    (condition-case ()
        (setq match-pos (scan-sexps (point) arg))
      (error nil))
    (mic-paren-recharquote charquote)
    (if (not match-pos)
        (buffer-end arg)
      (setq mismatch (mic-paren-fcq-mismatch (- match-pos match-check-diff)
                                             charquote))
      (if mismatch
          (forward-sexp arg)
        (goto-char match-pos)))))

;;;###autoload
(defun paren-backward-sexp (&optional arg)
  "Act like `backward-sexp' but also match quoted parens.
See `paren-match-quoted-paren'."
  (interactive "p")
  (or arg (setq arg 1))
  (paren-forward-sexp (- arg)))

;;; ======================================================================
;;; Internal functions

(defun mic-paren-command-idle-hook ()
  (condition-case paren-error
      (mic-paren-highlight)
    (error
     (unless (window-minibuffer-p (selected-window))
       (message "mic-paren caught error (please report): %s"
                paren-error)))))

(defun mic-paren-command-hook ()
  (or executing-kbd-macro
      ;; NB: This might cause trouble since the function is unreliable.
      (input-pending-p)
      (mic-paren-command-idle-hook)))

(defun mic-paren-minibuffer-setup-hook ()
  (paren-toggle-matching-quoted-paren 1 t))

(defun mic-paren-minibuffer-exit-hook ()
  (paren-toggle-matching-quoted-paren -1 t))

(defun mic-paren-fcq-mismatch (pos charquote)
  (not (zerop (logxor (if (mic-paren-is-following-char-quoted pos) 1 0)
                      (if charquote 1 0)))))

(defun mic-paren-highlight ()
  "Do everything: highlighting, dinging, messages, cleaning-up.
This is the main function of mic-paren."
  ;; Remove any old highlighting.
  (mic-delete-overlay (aref mic-paren-overlays 0))
  (mic-delete-overlay (aref mic-paren-overlays 1))
  (mic-delete-overlay (aref mic-paren-overlays 2))

  (let ((loc mic-paren-previous-location)
        charquote two opos matched-paren mismatch face visible)

    (flet ((highlight-p
            (pos prio which)
            (let ((fcq (mic-paren-is-following-char-quoted pos))
                  (right-prio (eq prio paren-priority))
                  (get-c-0 (if which 'preceding-char 'following-char))
                  (get-c-1 (if which 'following-char 'preceding-char)))
              (or (and (eq (char-syntax (funcall get-c-0))
                           (if which ?\) ?\())
                       (not (and (eq (char-syntax (funcall get-c-1))
                                     (if which ?\( ?\)))
                                 right-prio))
                       (or paren-match-quoted-paren
                           (not fcq)))
                  (and paren-match-paired-delimiter
                       (eq (char-syntax (funcall get-c-0)) ?\$)
                       (not (and (eq (char-syntax (funcall get-c-1)) ?\$)
                                 right-prio))
                       (not fcq)))))

           (comment-style
            ()
            (or (get major-mode 'mic-paren-comment-style)
                (put major-mode 'mic-paren-comment-style
                     ;; Tested (lightly) w/ SML, Modula-2, Pascal.
                     (flet ((sub (str pos) (condition-case ()
                                               (aref str (if (> 0 pos)
                                                             (+ (length str)
                                                                pos)
                                                           pos))
                                             (error 0))))
                       (if (string= "()" (string (sub comment-start 0)
                                                 (sub comment-end -1)))
                           'sexp
                         'normal)))))

           (sexp-ish-comment-edge
            (p mult)
            (and (eq 'sexp (comment-style))
                 (if (> 0 mult)
                     (prog1 (nth 8 (syntax-ppss (1- p)))
                       (forward-char 1))
                   ;; hmmm
                   (save-match-data
                     (looking-at (regexp-quote comment-start))))))

           (find-other-paren
            (forwardp)
            (let ((mult (if forwardp 1 -1)))
              ;; Find the position of the other paren.
              (save-excursion
                (save-restriction
                  (when blink-matching-paren-distance
                    (let ((lim (+ (point) (* blink-matching-paren-distance
                                             mult))))
                      (narrow-to-region (if forwardp
                                            (point-min)
                                          (max lim (point-min)))
                                        (if forwardp
                                            (min lim (point-max))
                                          (point-max)))))
                  (condition-case ()
                      (setq opos (let ((p (point)))
                                   (if (not (sexp-ish-comment-edge p mult))
                                       (scan-sexps p mult)
                                     (forward-comment mult)
                                     (point))))
                    (error nil))))
              ;; We must call matching-paren because `scan-sexps' doesn't
              ;; care about the kind of paren (e.g., matches '( and '}).
              ;; However, `matching-paren' only returns the character
              ;; displaying the matching paren in buffer's syntax-table
              ;; (regardless of the buffer's current contents!).  Below we
              ;; compare the results of `scan-sexps' and `matching-paren'
              ;; and if different we display a mismatch.
              (let ((c (funcall (if forwardp
                                    'following-char
                                  'preceding-char))))
                (setq matched-paren (matching-paren c))
                ;; matching-paren can only handle chars with syntax ) or (.
                (when (eq (char-syntax c) ?\$)
                  (setq matched-paren c)))
              ;; If we have changed the syntax of the escape or quote-char
              ;; we must undo this and we can do this first now.
              (mic-paren-recharquote charquote)
              opos))

           (nov
            (place b e face)
            (let ((ov (mic-make-overlay b e)))
              (mic-overlay-put ov 'face face)
              (mic-overlay-put ov 'priority paren-overlay-priority)
              (aset mic-paren-overlays
                    (cdr (assq place '((backw . 0)
                                       (point . 1)
                                       (forew . 2))))
                    ov)))

           (new-location-p
            ()
            (not (and (eq (point)           (aref loc 0))
                      (eq (current-buffer)  (aref loc 1))
                      (eq (selected-window) (aref loc 2)))))

           (ding-maybe
            (ok)
            (and ok paren-ding-unmatched
                 (new-location-p)
                 (ding)))

           (sorry
            (place b e)
            ;; Highlight unmatched paren.
            (nov place b e paren-no-match-face)
            ;; Print no-match message.
            (and paren-message-no-match
                 (not (window-minibuffer-p (selected-window)))
                 (not isearch-mode)
                 (new-location-p)
                 (mic-paren-nolog-message "No %sing parenthesis found"
                                          (if (eq 'backw place)
                                              "open"
                                            "clos")))
            (ding-maybe paren-message-no-match))

           (set-mismatch/face/visible
            (c-at ofs)
            (setq mismatch (or (not matched-paren)
                               (/= matched-paren (funcall c-at opos))
                               (mic-paren-fcq-mismatch (+ opos ofs) charquote))
                  face (if mismatch
                           paren-mismatch-face
                         paren-match-face)
                  visible (when (pos-visible-in-window-p opos)
                            (save-excursion
                              (goto-char opos)
                              (let ((hrel (- (current-column)
                                             (window-hscroll))))
                                (and (<             -1 hrel)
                                     (> (window-width) hrel)))))))

           (sexp-mode-p
            ()
            (case paren-sexp-mode
              (match (not mismatch))
              (mismatch mismatch)
              ((nil t) paren-sexp-mode)))

           (finish
            (get-message)
            ;; Print messages if match is offscreen.
            (and (not (eq paren-display-message 'never))
                 (or (not visible) (eq paren-display-message 'always))
                 (not (window-minibuffer-p (selected-window)))
                 (not isearch-mode)
                 (new-location-p)
                 (let ((message-truncate-lines paren-message-truncate-lines))
                   (mic-paren-nolog-message
                    "%s %s"
                    (if mismatch "MISMATCH:" "Matches")
                    (funcall get-message opos))))
            ;; Ding if mismatch.
            (ding-maybe mismatch)))

      ;; Handle backward highlighting.
      (when (highlight-p (- (point) 2) 'open t)
        (setq charquote (mic-paren-uncharquote (- (point) 2)))
        (if (not (find-other-paren nil))
            (sorry 'backw (point) (1- (point)))
          (set-mismatch/face/visible 'char-after -1)
          (when (or visible paren-highlight-offscreen paren-sexp-mode)
            (let ((sexp-mismatch (sexp-mode-p)))
              (nov 'backw opos (if sexp-mismatch
                                   (point)
                                 (1+ opos))
                   face)
              (when (and (not sexp-mismatch)
                         paren-highlight-at-point)
                (nov 'point (1- (point)) (point) face))))
          (finish 'mic-paren-get-matching-open-text)))

      ;; Handle forward highlighting.
      (when (highlight-p (1- (point)) 'close nil)
        (setq charquote (mic-paren-uncharquote (1- (point))))
        (if (not (find-other-paren t))
            (sorry 'forew (point) (1+ (point)))
          (set-mismatch/face/visible 'char-before -2)
          (when (or visible paren-highlight-offscreen paren-sexp-mode)
            (nov 'forew (if (sexp-mode-p)
                            (point)
                          (1- opos))
                 opos face))
          (finish 'mic-paren-get-matching-close-text))))

    ;; Store the point's position.
    (unless (window-minibuffer-p (selected-window))
      (aset loc 0 (point))
      (aset loc 1 (current-buffer))
      (aset loc 2 (selected-window)))))

(defun mic-paren-get-matching-open-text (open)
  "Return a string with the context around OPEN-paren.
If there's stuff on this line preceding the paren, then
display text from beginning of line to paren.

If, however, the paren is at the beginning of a line (means only
whitespace before the paren), then skip whitespace forward and
display text from paren to end of the next line containing
non-space text.  But if `paren-open-paren-context-backward' is
non-nil, then skip whitespaces backward and display text from
beginning of previous line to paren."
  (let* ((loc (if (eq paren-message-show-linenumber 'sexp)
                  (point) (point-min)))
         (str (save-excursion
                (goto-char open)
                (if (save-excursion
                      (skip-chars-backward " \t")
                      (not (bolp)))
                    (progn
                      (beginning-of-line)
                      (format "%s... [%s%d-]"
                              (buffer-substring (point) (1+ open))
                              (if (eq paren-message-show-linenumber 'sexp)
                                  "-" "")
                              (count-lines loc open)))
                  (let (paren-context-string)
                    (if (not paren-open-paren-context-backward)
                        (progn
                          (forward-char 1)
                          (skip-chars-forward "\n \t")
                          (end-of-line)
                          (setq paren-context-string
                                (buffer-substring open (point))))
                      (skip-chars-backward "\n \t")
                      (beginning-of-line)
                      (setq paren-context-string
                            (buffer-substring (point) (1+ open))))
                    (format "%s [%s%d]"
                            paren-context-string
                            (if (eq paren-message-show-linenumber 'sexp)
                                "-" "")
                            (count-lines loc open)))))))
    (while (string-match "[\n]" str)
      (setq str (replace-match paren-message-linefeed-display nil t str)))
    str))

(defun mic-paren-get-matching-close-text (close)
  "Return a string with the context around CLOSE-paren.
The whole line up until the close-paren with \"...\"
appended if there is more text after the close-paren."
  (let* ((loc (if (eq paren-message-show-linenumber 'sexp)
                  (point) (point-min)))
         (str (save-excursion
                (goto-char close)
                (forward-char -1)
                (skip-chars-backward "\n \t")
                (beginning-of-line)
                (format "%s%s [%s%d]"
                        (buffer-substring (point) close)
                        (progn
                          (goto-char close)
                          (if (looking-at "[ \t]*$")
                              ""
                            "..."))
                        (if (eq paren-message-show-linenumber 'sexp)
                            "+" "")
                        (count-lines loc close)))))
    (while (string-match "[\n]" str)
      (setq str (replace-match paren-message-linefeed-display nil t str)))
    str))

(defun mic-paren-is-following-char-quoted (pos)
  "Return t if character at POS escapes or quotes the following char."
  (let ((n 0))
    (while (and (<= (point-min) pos)
                (memq (char-syntax (char-after pos)) '(?\\ ?/)))
      (setq n (1+ n)
            pos (1- pos)))
    (not (zerop (% n 2)))))

(defun mic-paren-uncharquote (pos)
  "Modify syntax of character at POS, maybe.
If the syntax of character C at POS is escape or quote and if the
character is not escaped or quoted itself then modify its syntax to
punctuation and return the list (C SYNTAX-STRING-OF-C); otherwise nil."
  (when (and (<= (point-min) pos)
             paren-match-quoted-paren
             (mic-paren-is-following-char-quoted pos))
    (let ((c (char-after pos)))
      (modify-syntax-entry c ".")
      (list c (char-to-string (char-syntax c))))))

(defun mic-paren-recharquote (charquote)
  "Modify syntax entry according to CHARQUOTE.
If CHARQUOTE is nil, do nothing.  Otherwise, it
should be a list of the form (CHAR SYNTAX-STRING)."
  (when charquote
    (apply 'modify-syntax-entry charquote)))

;;; ======================================================================
;;; Initialization when loading

;;; Try to load the timer feature if it's not already loaded.
(or paren-dont-load-timer
    (featurep 'timer)
    (condition-case ()
        (require 'timer)
      (error nil)))

(provide 'mic-paren)
(provide 'paren)

;;; Local variables:
;;; coding: utf-8
;;; End:
;;; mic-paren.el ends here
