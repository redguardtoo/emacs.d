##
## Makefile for Proof General.
## 
## Author:  David Aspinall <David.Aspinall@ed.ac.uk>
##
##  make		- do "compile" targets
##  make compile	- make .elc's 
##  make scripts	- edit paths to bash/perl/PGHOME in scripts
##  make install	- install into system directories
##  make clean		- return to clean source
##
## Edit the EMACS setting below or call with an explicit one, like this:
##
##     make EMACS=emacs-23.0.60
## or
##     make EMACS=/Applications/Emacs.app/Contents/MacOS/Emacs
##
## Makefile,v 12.3 2012/03/05 18:52:34 tews Exp
## 
###########################################################################

# Set this according to your version of Emacs.
# NB: this is also used to set default install path names below.
EMACS=$(shell if [ -z "`which emacs`" ]; then echo "Emacs executable not found"; exit 1; else echo emacs; fi)
# EMACS=/Applications/Emacs\ 23.4.app/Contents/MacOS/Emacs

# We default to /usr rather than /usr/local because installs of
# desktop and doc files under /usr/local are unlikely to work with
# rest of the system.  If that's no good for you, edit the paths
# individually before the install section.
# NB: DEST_PREFIX is used for final destination prefix, in case we're
# packaging into a build prefix rather than live root (e.g. in rpmbuild).
# NBB: DESTDIR provides for staged installs, for instance when building 
# Debian packages, see http://www.gnu.org/prep/standards/html_node/DESTDIR.html
PREFIX=$(DESTDIR)/usr
DEST_PREFIX=$(DESTDIR)/usr

PWD=$(shell pwd)

PROVERS=acl2 ccc coq hol98 isar lego hol-light phox pgshell pgocaml pghaskell
OTHER_ELISP=generic lib contrib/mmm
ELISP_DIRS=${PROVERS} ${OTHER_ELISP}
ELISP_EXTRAS=isar/interface isar/isartags
EXTRA_DIRS = images

DOC_FILES=AUTHORS BUGS COMPATIBILITY CHANGES COPYING INSTALL README REGISTER doc/*.pdf
DOC_EXAMPLES=acl2/*.acl2 hol98/*.sml isar/*.thy lclam/*.lcm lego/*.l pgshell/*.pgsh phox/*.phx plastic/*.lf twelf/*.elf
DOC_SUBDIRS=${DOC_EXAMPLES} */README* */CHANGES */BUGS 

BATCHEMACS=${EMACS} --batch --no-site-file -q 

# Scripts to edit paths to shells
BASH_SCRIPTS = isar/interface bin/proofgeneral
PERL_SCRIPTS = lego/legotags coq/coqtags isar/isartags
# Scripts to edit path to PG
PG_SCRIPTS = bin/proofgeneral

# Scripts to install to bin directory
BIN_SCRIPTS = bin/proofgeneral lego/legotags coq/coqtags isar/isartags

# Setting load path might be better in Elisp, but seems tricky to do
# only during compilation.  Another idea: put a function in proof-site
# to output the compile-time load path and ELISP_DIRS so these are set
# just in that one place.
BYTECOMP = $(BATCHEMACS) -eval '(setq load-path (append (mapcar (lambda (d) (concat "${PWD}/" (symbol-name d))) (quote (${ELISP_DIRS}))) load-path))' -eval '(progn (require (quote bytecomp)) (require (quote mouse)) (require (quote tool-bar)) (require (quote fontset)) (setq byte-compile-warnings (remove (quote cl-functions) (remove (quote noruntime) byte-compile-warning-types))) (setq byte-compile-error-on-warn t))' -f batch-byte-compile
EL=$(shell for f in $(ELISP_DIRS); do ls $$f/*.el; done)
ELC=$(EL:.el=.elc)

.SUFFIXES:	.el .elc

default: all

FORCE:

## 
## compile : byte compile all lisp files
##
## Compiling can show up errors in the code, but be wary of fixing obsoletion
## or argument call warnings unless they're valid for all supported Emacsen.
##
compile: $(EL) 
	@echo "****************************************************************"
	@echo " Byte compiling... "
	@echo "****************************************************************"
	$(MAKE) elc
	@echo "****************************************************************"
	@echo " Finished."
	@echo "****************************************************************"


##
## Make an individual .elc.  Building separately means we need to be
## careful to add proper requires in source files and prevent
## evaluating/optimising top-level forms too early.  Using a separate
## emacs process for each file is slower but avoids any chance of
## accidently polluting the compilation environment, it also should
## work with make -j n.
##
.el.elc:
	$(BYTECOMP) $*.el

elc:	$(ELC)


##
## Default targets
##

all:	compile


##
## Remove generated targets
##
clean:	cleanpgscripts
	rm -f $(ELC) *~ */*~ .\#* */.\#* */.autotest.log */.profile.log
	(cd doc; $(MAKE) clean)

distclean: clean

##
## Install files 
##
DESKTOP_PREFIX=${PREFIX}

# Set Elisp directories according to paths used in Red Hat RPMs
# (which may or may not be official Emacs policy).  We generate
# a pg-init.el file which loads the appropriate proof-site.el.
ELISPP=share/${EMACS}/site-lisp/ProofGeneral
ELISP_START=${PREFIX}/share/${EMACS}/site-lisp/site-start.d

ELISP=${PREFIX}/${ELISPP}
DEST_ELISP=${DEST_PREFIX}/${ELISPP}

BINDIR=${PREFIX}/bin
DESKTOP=${PREFIX}/share
DOCDIR=${PREFIX}/share/doc/ProofGeneral
MANDIR=${PREFIX}/share/man/man1
INFODIR=${PREFIX}/share/info

install: install-desktop install-elisp install-bin install-init

install-desktop:
	mkdir -p ${DESKTOP}/icons/hicolor/16x16
	cp etc/desktop/icons/16x16/proofgeneral.png ${DESKTOP}/icons/hicolor/16x16
	mkdir -p ${DESKTOP}/icons/hicolor/32x32
	cp etc/desktop/icons/32x32/proofgeneral.png ${DESKTOP}/icons/hicolor/32x32
	mkdir -p ${DESKTOP}/icons/hicolor/48x48
	cp etc/desktop/icons/48x48/proofgeneral.png ${DESKTOP}/icons/hicolor/48x48
	mkdir -p ${DESKTOP}/pixmaps
	cp etc/desktop/icons/48x48/proofgeneral.png ${DESKTOP}/pixmaps
	mkdir -p ${DESKTOP}/applications
	cp etc/desktop/proofgeneral.desktop ${DESKTOP}/applications
	mkdir -p ${DESKTOP}/mime-info
	cp etc/desktop/mime-info/proofgeneral.mime ${DESKTOP}/mime-info
	cp etc/desktop/mime-info/proofgeneral.keys ${DESKTOP}/mime-info
# backwards compatibility with old linuxes
	mkdir -p ${DESKTOP}/application-registry
	cp etc/desktop/application-registry/proofgeneral.applications ${DESKTOP}/application-registry

# NB: .el files are not strictly necessary, but we package/install them
# for the time being to help with debugging, or for users to recompile.
install-elisp: install-el install-elc

# NB: "elisp" directory actually includes the extra subdirs in EXTRA_DIRS,
# i.e. images.  FIXME: we could put these elsewhere, but
# then we would need to adjust paths in proof-site.el.
# FIMXE 3: Michaël Cadilhac pointed out that 'cp -p' when used with
# sudo to install will give users ownership instead of root. 
# Should use install program or fix ownerships afterwards here.
install-el:
	mkdir -p ${ELISP}
	for f in ${ELISP_DIRS} ${EXTRA_DIRS}; do mkdir -p ${ELISP}/$$f; done
	for f in ${ELISP_DIRS}; do cp -pf $$f/*.el ${ELISP}/$$f; done
	for f in ${EXTRA_DIRS}; do cp -prf $$f/* ${ELISP}/$$f; done
	for f in ${ELISP_EXTRAS}; do cp -pf $$f ${ELISP}/$$f; done

install-elc: compile
	mkdir -p ${ELISP}
	for f in ${ELISP_DIRS} ${EXTRA_DIRS}; do mkdir -p ${ELISP}/$$f; done
	for f in ${ELISP_DIRS}; do cp -pf $$f/*.elc ${ELISP}/$$f; done
	for f in ${ELISP_EXTRAS}; do cp -pf $$f ${ELISP}/$$f; done

install-init:
	mkdir -p ${ELISP_START}
	echo ';;; pg-init.el --- setup for Proof General' > ${ELISP_START}/pg-init.el
	echo "(setq load-path (append load-path '(\"${DEST_ELISP}/generic\")))" >> ${ELISP_START}/pg-init.el
	echo "(require 'proof-site)" >> ${ELISP_START}/pg-init.el

install-bin: scripts
	mkdir -p ${BINDIR}
	cp -pf ${BIN_SCRIPTS} ${BINDIR}

install-doc: doc.info doc.pdf
	mkdir -p ${MANDIR}
	cp -pf doc/proofgeneral.1 ${MANDIR}
	mkdir -p ${INFODIR}
	cp -pf doc/*.info ${INFODIR}
	/sbin/install-info ${INFODIR}/ProofGeneral.info* ${INFODIR}/dir
	/sbin/install-info ${INFODIR}/PG-adapting.info* ${INFODIR}/dir
	mkdir -p ${DOCDIR}
	for f in ${DOC_FILES}; do cp -pf $$f ${DOCDIR}; done
	for f in ${DOC_EXAMPLES}; do mkdir -p ${DOCDIR}/`dirname $$f`; cp -pf $$f ${DOCDIR}/$$f; done

doc: FORCE
	(cd doc; $(MAKE) EMACS=$(EMACS) $*)

doc.%: FORCE
	(cd doc; $(MAKE) EMACS=$(EMACS) $*)

##
## scripts: try to patch bash and perl scripts with correct paths
##
scripts: bashscripts perlscripts pgscripts

bashscripts:
	@(bash="`which bash`"; \
	 if [ -z "$$bash" ]; then \
	   echo "Could not find bash - bash paths not checked" >&2; \
	   exit 0; \
	 fi; \
	 for i in $(BASH_SCRIPTS); do \
	   sed "s|^#.*!.*/bin/bash.*$$|#!$$bash|" < $$i > .tmp \
	   && cat .tmp > $$i; \
	 done; \
	 rm -f .tmp)

perlscripts:
	@(perl="`which perl`"; \
	 if [ -z "$$perl" ]; then \
	   echo "Could not find perl - perl paths not checked" >&2; \
	   exit 0; \
	 fi; \
	 for i in $(PERL_SCRIPTS); do \
	   sed "s|^#.*!.*/bin/perl.*$$|#!$$perl|" < $$i > .tmp \
	   && cat .tmp > $$i; \
	 done; \
	 rm -f .tmp)

# FIXME: this next edit is really for install case, shouldn't be made
# just when user types 'make'
pgscripts:
	@(for i in $(PG_SCRIPTS); do \
	   sed "s|PGHOMEDEFAULT=.*$$|PGHOMEDEFAULT=${DEST_ELISP}|" < $$i > .tmp \
	   && cat .tmp > $$i; \
	 done; \
	 rm -f .tmp)

# Set PGHOME path in scripts back to default location.
cleanpgscripts:
	@(for i in $(PG_SCRIPTS); do \
	   sed "s|PGHOMEDEFAULT=.*$$|PGHOMEDEFAULT=\$$HOME/ProofGeneral|" < $$i > .tmp \
	   && cat .tmp > $$i; \
	 done; \
	 rm -f .tmp)

##
## Include developer's makefile if it exists here.
##

-include Makefile.devel
