# The Makefile is for the following PolyP-version
export polyp_version = 2.$(shell date +%y%m%d)

default: ghc

help: 
	@echo Makefile for PolyP by Patrik Jansson
	@echo Usage: 
	@echo "  gmake X    where X is ghc, hbc or hugs"
	@echo "    makes the sources and compiles them with compiler X"
	@echo "  gmake check.X"
	@echo "    runs some regression tests."

# Choose the desired version of Haskell ...
export HASKELLVERSION = 98
# ... and of the compiler
export ghc  = ghc
export hbc  = hbc
export hugs = runhugs

POLYPDIR   = $(shell pwd)

INSTALLBINDIR = $(HOME)/bin

# Use some version of the PolyP compiler in the bin directory
#   with polyp (somewhere on the path) as a fall-back option
export PolyP := $(firstword $(wildcard ${POLYPDIR}/bin/*polyp) polyp)

# For a quick test of PolyP - use hugs to avoid compilation

# Make PolyP using hugs, ghc or hbc
hugs ghc hbc: bin/chase
# Make the source
	-mkdir $@src
	$(MAKE) -C src $@src "hc=$($@)" 
# compile[1] the source
	$(MAKE) -C $@src "hc=$($@)"
	@echo Read the files src/$@.USAGE and USAGE for details on how to run PolyP
# compile (with the new polyp) the standard library PolyLib
	$(MAKE) -C polylib all
# "install"
	-ln -s $(POLYPDIR)/bin/$@polyp $(INSTALLBINDIR)/$@polyp
	-ln -s $(INSTALLBINDIR)/$@polyp $(INSTALLBINDIR)/polyp
	-ln -s $(POLYPDIR)/bin/chase $(INSTALLBINDIR)/chase

# [1] For hbc and ghc the source is really compiled, but as hugs is an
# interpreter, its makefile only provides a name for the call to
# runhugs hugssrc/Main.lhs

# Run some regression tests
#   -s makes the testcompilations silent (unless there is an error)
check: boilerplate.mk
	$(MAKE) -e -s -C examples check
	$(MAKE) -e -s -C test check

check.% : %  boilerplate.mk
	$(MAKE) -e -s -C examples check PolyP=../bin/$*polyp
	$(MAKE) -e -s -C test check PolyP=../bin/$*polyp

# compile with all three compilers and check the results
checkdist: check.ghc check.hbc check.hugs

POLYLIBDIR = $(POLYPDIR)/polylib
PERL       = $(shell which perl)

bin/chase: src/chase.in
	mkdir -p bin
	echo '#!'$(PERL) > bin/chase
	echo '$$POLYLIBDIR='\'$(POLYLIBDIR)\'\; >>bin/chase
	cat src/chase.in >> bin/chase
	chmod +x bin/chase

boilerplate.mk:
	echo POLYPDIR=$(POLYPDIR) > boilerplate.mk

oldhugs:
# Make the source for older (before ~1998) versions of hugs
	-mkdir hugssrc
	$(MAKE) -C src $@src 

clean:
	rm -f *~
	rm -f \#*\#
	$(MAKE) -C src clean
	rm -f polylib/*~
	rm -f docs/*~
	-$(MAKE) -C examples clean
	$(MAKE) -C polylib clean
	$(MAKE) -C book clean
	rm -fr polyp$(polyp_version) polyp$(polyp_version).tar.gz

veryclean:	clean
	$(MAKE) -C src veryclean
	rm -fr hugssrc
	rm -fr hbcsrc
	rm -fr ghcsrc
	$(MAKE) -C examples veryclean
	$(MAKE) -C book veryclean

distclean:	veryclean
	rm -f  bin/hugspolyp bin/ghcpolyp bin/hbcpolyp bin/polyp bin/chase


# Distribution
polyp$(polyp_version):
	-rm -r $@
	cvs export -D now -d $@  p

polyp$(polyp_version).tar.gz: polyp$(polyp_version)
	-rm -r $@
	gtar -zcf $@ $<

WWWDIR = $(HOME)/pub/www/poly

www: polyp$(polyp_version).tar.gz
	cp polyp$(polyp_version).tar.gz $(WWWDIR)
	cd $(WWWDIR); $(MAKE) -e polyp$(polyp_version)
	rm -rf polyp$(polyp_version).tar.gz polyp$(polyp_version)
# `-e' `--environment-overrides'
#     Give variables taken from the environment precedence over
#     variables from makefiles. Used here to export $(polyp_version)

packpolylib:
	gtar -zcf polylib.tar.gz polylib examples 

local:	polyp$(polyp_version)
	$(MAKE) -C polyp$(polyp_version) ghc
	$(MAKE) -C polyp$(polyp_version) check.ghc
	cp polyp$(polyp_version)/bin/ghcpolyp $(HOME)/bin/polyp
	@echo Skicka brev lokalt och meddela detta

fromwww:
	lynx -source 'http://www.cs.chalmers.se/~patrikj/poly/polyp.tar.gz'\
           > polyp.tar.gz
	gunzip < polyp.tar.gz | tar xf -
	cd polyp$(polyp_version); $(MAKE) check.ghc

WEBSITE = http://www.cs.chalmers.se/~patrikj/poly/polyp/
WEBDIR  = $(HOME)/pub/www/poly/polyp

README:	index.html
	mv $(WEBDIR)/index.html qqq
	cp index.html $(WEBDIR)
	lynx -dump $(WEBSITE) >README
	mv qqq $(WEBDIR)/index.html

# These targets are not real files
.PHONY: help install hugs ghc hbc clean distclean packpolylib \
	www fromwww local 

# for some reason, checkhbc, checkghc, chechhugs should not be in that list
