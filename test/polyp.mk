# PolyPFLAGS = extra flags to PolyP
#   example: PolyPFLAGS = -p ArrTypes.hs -r start

# Extension names: .phs -- input polyp modules
#                  .Phs2 -- one big import-chased polyp file
#                  .Hs2  -- output from polyp (may need som expl. types)
#                  .hs  -- final Haskell code produced

################################################################
runhugs = runhugs

PolyPDIR = ${HOME}
# PolyP = $(PolyPDIR)/bin/polyp
PolyP = polyp
# CHASE = perl $(PolyPDIR)/bin/chase
# CHASE = $(PolyPDIR)/bin/chase
CHASE = chase

%.run: %.hs
	$(runhugs) $<

%.hs: %.Hs2
	cat $(wildcard type$*.hs) $< > $@

%.Hs2: %.Phs2
	$(PolyP) $(PolyPFLAGS) ${PolyPREQUESTS} $< > $@ 

%.Phs2: %.phs
	$(CHASE) $(CHASEFLAGS) $< > $@

%.out2: %.hs
	$(runhugs) $< > $@

%.check: %.out2
	diff $*.out2 $*.out > $*.check

clean::
	rm -f $(targets:.hs=.check)

veryclean:: clean
	rm -f $(targets) $(targets:.hs=.Hs2) $(targets:.hs=.Phs2) $(targets:.hs=.out2) 
