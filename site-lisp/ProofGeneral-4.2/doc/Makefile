##
## Makefile for Proof General doc directory.
##
## Author:  David Aspinall <da@inf.ed.ac.uk>
##
## Maintainer:  Proof General maintainer <da+proofgen@inf.ed.ac.uk>
##
## Makefile,v 12.0 2011/10/13 10:54:47 da Exp
## 
###########################################################################
##
## Use:
##	make info,pdf,html    - build respective docs from texi source.
##	make doc              - make default kinds of doc (, info).
##
###########################################################################

default:
	$(MAKE) doc

%:
	$(MAKE) -f Makefile.doc DOCNAME=PG-adapting MAKE="$(MAKE) -f Makefile.doc" $@
	$(MAKE) -f Makefile.doc DOCNAME=ProofGeneral MAKE="$(MAKE) -f Makefile.doc" $@ 

##
## man page for proofgeneral script
##
# man: proofgeneral.1
#
proofgeneral.1: ../bin/proofgeneral
	help2man --output=$@  ../bin/proofgeneral
