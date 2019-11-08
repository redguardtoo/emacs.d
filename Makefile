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
	$(EMACS) -nw --batch --eval '(let* ((user-emacs-directory default-directory) (user-init-file (expand-file-name "init.el")) (load-path (delq default-directory load-path))) (load-file user-init-file))'

