SLIME is the ``Superior Lisp Interaction Mode for Emacs.''

SLIME extends Emacs with support for interactive programming in
Common Lisp. The features are centered around slime-mode, an Emacs
minor-mode that complements the standard lisp-mode. While lisp-mode
supports editing Lisp source files, slime-mode adds support for
interacting with a running Common Lisp process for compilation,
debugging, documentation lookup, and so on.

The slime-mode programming environment follows the example of
Emacs's native Emacs Lisp environment. We have also included good
ideas from similar systems (such as ILISP) and some new ideas of
our own.

SLIME is constructed from two parts: a user-interface written in
Emacs Lisp, and a supporting server program written in Common
Lisp. The two sides are connected together with a socket and
communicate using an RPC-like protocol.

The Lisp server is primarily written in portable Common Lisp. The
required implementation-specific functionality is specified by a
well-defined interface and implemented separately for each Lisp
implementation. This makes SLIME readily portable.
