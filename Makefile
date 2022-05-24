SHELL = /bin/sh
EMACS ?= emacs
PROFILER =
RM = @rm -rf
EMACS_BATCH_OPTS = --batch -Q

.PHONY: test clean githooks spellcheck

# Delete byte-compiled files etc.
clean:
	$(RM) *~
	$(RM) \#*\#
	$(RM) *.elc
	$(RM) lisp/*.elc

githooks:
	cd `git rev-parse --show-toplevel`/.git/hooks && ln -s ../../githooks/pre-commit pre-commit && cd -

# Delete byte-compiled files etc.
spellcheck:
	@$(EMACS) $(EMACS_BATCH_OPTS) -L site-lisp/wucuo -l site-lisp/wucuo/wucuo.el -l tools/spellcheck.el

# Run tests.
test: clean spellcheck
	@$(EMACS) $(EMACS_BATCH_OPTS) --debug-init --eval "(setq my-disable-idle-timer t)" -l init.el -l tests/emacs.d-test.el
