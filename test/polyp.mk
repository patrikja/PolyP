# PolyPFLAGS = extra flags to PolyP
#   example: PolyPFLAGS = -p ArrTypes.hs -r start
# HUGSFLAGS = extra flags to hugs and runhugs

# Extension names: .phs -- input polyp modules
#                  .Phs2 -- one big import-chased polyp file
#                  .Hs2  -- output from polyp (may need som expl. types)
#                  .hs  -- final Haskell code produced

################################################################
runhugs = runhugs

-include ../boilerplate.mk

PolyP = $(POLYPDIR)/bin/ghcpolyp $(POLYPFLAGS)
#PolyP = polyp
# CHASE = perl $(POLYPDIR)/bin/chase
CHASE = $(POLYPDIR)/bin/chase
#CHASE = chase

%.run: %.hs
	$(runhugs) $(HUGSFLAGS) $<

#type%.hs :
#	echo import MyPolyPrel > $@

#%.hs: %.Hs2 type%.hs
#	cat $(dir $*)type$(notdir $*).hs $< > $@

#%.Hs2: %.Phs2
#	$(PolyP) $(PolyPFLAGS) ${PolyPREQUESTS} $< > $@ 

#%.Phs2: %.phs
#	$(CHASE) $(CHASEFLAGS) $< > $@

%.hs : %.phs
	$(PolyP) $< > $@

%.phs: %.lphs
	lhs2TeX -code -lcodeOnly=True $< | cut -c3- > $@

%.out2: %.hs
	$(runhugs) $(HUGSFLAGS) -P:$(POLYPDIR)/lib:$(POLYPDIR)/polylib $< > $@

%.out2: %.lhs
	$(runhugs) $(HUGSFLAGS) $< > $@

%.check: %.out2
	diff $*.out2 $*.out > $*.check

clean::
	rm -f $(targets:.hs=.check)

veryclean:: clean
	rm -f $(targets) $(targets:.hs=.phi) $(targets:.hs=.Hs2) $(targets:.hs=.Phs2) $(targets:.hs=.out2) $(patsubst %.hs,type%.hs,$(targets))

