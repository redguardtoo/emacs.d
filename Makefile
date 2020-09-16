SHELL = /bin/sh
EMACS ?= emacs
PROFILER =

.PHONY: test clean githooks

# Delete byte-compiled files etc.
clean:
	rm -f *~
	rm -f \#*\#
	rm -f *.elc

githooks:
	cd `git rev-parse --show-toplevel`/.git/hooks && ln -s ../../githooks/pre-commit pre-commit && cd -

# Run tests.
test: clean
	$(EMACS) -Q -nw --batch -l init.el

