In this repository there is a colletion of my personal [[http://github.com/capitaomorte/yasnippet][yasnippet]]
snippets for many different Emacs modes.


# How to use

1. install yasnippet
3. add to your .emacs the following
   - (add-to-list 'yas/root-directory "$DIRECTORY_WHERE_YOU_CLONED")
   - (yas/initialize)
4. M-x yas/reload-all to activate them

# Contributing

This repository has now become the default snippets repository (as a submodule) in yasnippet.
So if you have any useful snippets for any language or framework please feel free to contribute.

To study the current snippets I suggest to use M-x yas/describe-tables
which will gave a table representation of all the snippets available in the current mode.


# Guidelines

Snippets need to be generic enough to be useful for everyone, and not contain anything specific to your own system.
