###################
## Simple tests of the PolyP compiler (requires GNU make)
# If the PolyP installation works as it should 
#     make check 
# should be silent (that is, not print anything)

###################
## Compiler selection
# Use some version of the compiler in the ../bin directory
#   with polyp as a fall-back option
PolyP := $(firstword $(wildcard ../bin/*polyp) polyp)
#PolyP = polyp
PERL = perl
#CHASE = $(PERL) ../bin/chase
CHASE = chase
runhugs = runhugs

DIFF = diff
## For older hugs systems (pre 1998)
#DIFF = diff -w
# The -w argument to diff is to ignore white space differences
# caused by the change of printing of hugs in 1998. "(1, 2)" -> "(1,2)"
# The .out files contain the (correct) output (without the extra space)

###################
# The target Haskell files of the tests to be performed
targets = testSum.hs testCrush.hs testFlatten.hs testPropagate.hs	\
          testThread.hs testZip.hs testConstructorName.hs testEqOrd.hs 	\
          testEqual.hs testSubstructures.hs testShow.hs testBaseM.hs \
          Separate.hs

default: check
 
all: $(targets)

check:: $(targets:.hs=.check) $(wildcard ../polylib/*.phs)

check:: veryclean

# Make the testcompilations silent
MAKEFLAGS += -s

include ../test/polyp.mk

print:
	cat ../polylib/Base.phs    ../polylib/Sum.phs       ../polylib/Crush.phs \
	    ../polylib/Flatten.phs ../polylib/Propagate.phs ../polylib/Thread.phs\
	    ../polylib/Zip.phs     ../polylib/ConstructorName.phs		 \
            ../polylib/EqOrd.phs   ../polylib/Equal.phs				 \
	    ../polylib/BaseM.phs   Show.phs > All.phs ; \
	enscript -2Gr All.phs 

.PHONY:	all print

# The rest is old stuff
##################
# using CHASE for import-chasing this rule translates its input file
# using PolyP, prepends possible extra type information, and runs it
# under hugs if it PolyP worked. Otherwise it renames the file (to
# indicate failure) and shows the output to help find the error.

#test%.hs : test%.phs
#	$(CHASE) $< >tmp.phs
#	-(   $(PolyP) tmp.phs >tmp.hs \
#          && cat $(wildcard type$*.hs) tmp.hs >$@ \
#          && hugs $@) \
#         || (mv $@ tmp.hs; more tmp.hs)
#test%.check : test%.phs
#	@echo "--!!! Checking $*"
#	@$(CHASE) $< >tmp.phs
#	@-($(PolyP) tmp.phs | cat $(wildcard type$*.hs) - >test$*.hs \
#          && ${runhugs} test$*.hs > test$*.check) || echo >test$*.check
#	@${DIFF} test$*.check test$*.out
