PolyP := $(firstword $(wildcard ../bin/*polyp) polyp)
#PolyP = polyp
PERL = perl

targets = testSum.hs testCrush.hs testFlatten.hs testPropagate.hs	\
          testThread.hs testZip.hs testConstructorName.hs testEqOrd.hs 	\
          testEqual.hs testSubstructures.hs testShow.hs testBaseM.hs

CHASE = $(PERL) ../bin/chase -i ../polylib

default: $(targets)

# Files in this directory:
# README
# contents.txt
# Makefile

# testConstructorName.phs
# testCrush.phs
# testEqOrd.phs
# testEqual.phs
# testFlatten.phs
# testPropagate.phs
# testShow.phs
# testSubstructures.phs
# testSum.phs
# testThread.phs     typeThread.hs
# testZip.phs	

# Show.phs
# Substructures.phs
# stub.phs


all: $(targets)

.SUFFIXES: 
.SUFFIXES: .phs .hs .check

# using the perl-script chase for import-chasing this rule translates
# its input file using polyp, prepends possible extra type
# information, and runs it under hugs if it PolyP worked. Otherwise it
# renames the file (to indicate failure) and shows the output to help
# find the error.

test%.hs : test%.phs
	$(CHASE) $< >tmp.phs
	-(   $(PolyP) tmp.phs >tmp.hs \
          && cat $(wildcard type$*.hs) tmp.hs >$@ \
          && hugs $@) \
         || (mv $@ tmp.hs; more tmp.hs)

# make check should only print lines starting with --!!!

check:: $(targets:.hs=.check) $(wildcard ../polylib/*.phs)

check:: 
	rm *.check

test%.check : test%.phs
	@echo "--!!! Checking $*"
	@$(CHASE) $< >tmp.phs
	@-($(PolyP) tmp.phs | cat $(wildcard type$*.hs) - >test$*.hs \
          && runhugs test$*.hs > test$*.check) || echo >test$*.check
	@diff test$*.check test$*.out

genfiles = $(targets) $(targets:.hs=.check) tmp.phs tmp.hs Separate.hs

print:
	cat ../polylib/Base.phs    ../polylib/Sum.phs       ../polylib/Crush.phs	\
	    ../polylib/Flatten.phs ../polylib/Propagate.phs ../polylib/Thread.phs	\
	    ../polylib/Zip.phs     ../polylib/ConstructorName.phs			\
            ../polylib/EqOrd.phs   ../polylib/Equal.phs					\
	    ../polylib/BaseM.phs   Show.phs > All.phs ; \
	enscript -2Gr All.phs 

clean:
	rm -f *~

veryclean: clean
	rm -f $(genfiles)

.PHONY:	all print clean veryclean

