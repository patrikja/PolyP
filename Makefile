# The Makefile is for the following PolyP-version
version=0.9

help: 
	@echo Makefile for PolyP by Patrik Jansson
	@echo Usage: 
	@echo "  gmake X    where X is ghc, hbc or hugs"
	@echo "    makes the sources and compiles them with compiler X"
	@echo "  gmake check.X"
	@echo "    runs some regression tests."


# These variables can be used to specify the desired version of the compiler
ghc  = ghc
hbc  = hbc
hugs = runhugs

# For a quick test of PolyP - use hugs to avoid compilation

# Make PolyP using hugs, ghc or hbc
hugs ghc hbc:
# Make the source
	-mkdir $@src
	$(MAKE) -C src $@src 
# compile[1] the source
	$(MAKE) -C $@src hc=$($@)
	@echo Read the files src/$@.USAGE and USAGE for details on how to run PolyP

# [1] For hbc and ghc the source is really compiled, but as hugs is an
# interpreter, its makefile only provides a name for the call to
# runhugs hugssrc/Main.lhs

# Run some regression tests
check:
	$(MAKE) -C examples check

check.% : %
	$(MAKE) -C examples check PolyP=../bin/$*polyp

# compile with all three compilers and check the results
checkdist: check.ghc check.hbc check.hugs


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
	$(MAKE) -C book clean

veryclean:	clean
	$(MAKE) -C src veryclean
	rm -fr hugssrc
	rm -fr hbcsrc
	rm -fr ghcsrc
	$(MAKE) -C examples veryclean
	$(MAKE) -C book veryclean

distclean:	veryclean
	rm -fr  bin/hugspolyp bin/ghcpolyp bin/hbcpolyp bin/polyp
	rm -r   CVS */CVS

packpolylib:
	tar cf polylib.tar polylib examples 
	gzip polylib.tar

# outdated
dist:
	$(MAKE) -C src dist
	-rm -r ../polyp$(version)
	mkdir ../polyp$(version)
	cp -r * ../polyp$(version)
	$(MAKE) -C ../polyp$(version) distclean
	-rm ../polyp$(version).tar
# change directory to store the correct path in the .tar-file
	cd ..; tar cf polyp$(version).tar polyp$(version)
	gzip ../polyp$(version).tar

disthugs:
	-rm -r ../polyphugs$(version)
	mkdir ../polyphugs$(version)
	cp -r * ../polyphugs$(version)
	$(MAKE) -C ../polyphugs$(version) distclean
	$(MAKE) -C ../polyphugs$(version)/src hugssrc
	cd ..; tar cf polyphugs$(version).tar polyphugs$(version); 
	gzip ../polyphugs$(version).tar
	cd ../polyphugs$(version); tar -zcf hugssrc.tar.gz hugssrc


# These targets are not real files
.PHONY: help install hugs ghc hbc clean distclean packpolylib dist disthugs

# for some reason, checkhbc, checkghc, chechhugs should not be in that list
