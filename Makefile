SHELL = /bin/sh
EMACS ?= emacs
PROFILER =

.PHONY: test clean githooks

# Delete byte-compiled files etc.
clean:
	@rm -f *~
	@rm -f \#*\#
	@rm -f *.elc

githooks:
	cd `git rev-parse --show-toplevel`/.git/hooks && ln -s ../../githooks/pre-commit pre-commit && cd -

spellcheck:
	@$(EMACS) -batch -Q -L site-lisp/wucuo -l site-lisp/wucuo/wucuo.el -l tools/spellcheck.el

# Run tests.
test: clean spellcheck
	@$(EMACS) -Q -nw --debug-init --batch --eval "(setq my-disable-idle-timer t)" -l init.el -l tests/emacs.d-test.el

