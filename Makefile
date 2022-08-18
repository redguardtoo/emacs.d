SHELL = /bin/sh
EMACS ?= emacs
PROFILER =
RM = @rm -rf
EMACS_BATCH_OPTS = --batch -Q --debug-init --eval "(setq my-disable-idle-timer t)"

.PHONY: test clean githooks spellcheck compile install

# Delete byte-compiled files etc.
clean:
	$(RM) *~
	$(RM) \#*\#
	$(RM) *.elc
	$(RM) lisp/*.elc

githooks:
	cd `git rev-parse --show-toplevel`/.git/hooks && ln -s ../../githooks/pre-commit pre-commit && cd -

install: clean
	@$(EMACS) $(EMACS_BATCH_OPTS) -l init.el

# Delete byte-compiled files etc.
spellcheck:
	@$(EMACS) $(EMACS_BATCH_OPTS) -L site-lisp/wucuo -l site-lisp/wucuo/wucuo.el -l tools/spellcheck.el

compile: install
	@$(EMACS) $(EMACS_BATCH_OPTS) -l init.el -l tests/my-byte-compile.el 2>&1 | grep -Ev "init-(hydra|evil).el:.*Warning: docstring wider than 80 characters|an obsolete" | grep -E "[0-9]: ([Ee]rror|[Ww]arning):" && exit 1 || exit 0

# Run tests.
test: compile spellcheck
	@$(EMACS) $(EMACS_BATCH_OPTS) -l init.el -l tests/emacs.d-test.el
