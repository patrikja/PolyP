# PolyPFLAGS = extra flags to PolyP
#   example: PolyPFLAGS = -p ArrTypes.hs -r start

# Extension names: .phs -- input polyp modules
#                  .Phs -- one big import-chased polyp file
#                  .Hs  -- output from polyp (may need som expl. types)
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

%.hs: %.Hs
	cat $(wildcard type$*.hs) $< > $@

%.Hs: %.Phs
	$(PolyP) $(PolyPFLAGS) $< > $@ 

%.Phs: %.phs
	$(CHASE) $(CHASEFLAGS) $< > $@

%.check: %.hs %.out
	$(runhugs) $< | diff - $*.out

clean:
	rm -f $(targets:.hs=.Hs) $(targets:.hs=.Phs)

veryclean: clean
	rm -f $(targets)
