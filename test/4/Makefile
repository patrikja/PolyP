runhugs = runhugs
PolyP = polyp
CHASE = perl ../../bin/chase -i ../../polylib/

check:	simpledataconversion.hs
	$(runhugs) simpledataconversion.hs | diff - simpledataconversion.out

run:	simpledataconversion.hs
	$(runhugs) simpledataconversion.hs  

simpledataconversion.hs: simpledataconversion.Phs
	$(PolyP) simpledataconversion.Phs > simpledataconversion.hs   

simpledataconversion.Phs: simpledataconversion.phs
	$(CHASE) simpledataconversion.phs > simpledataconversion.Phs

clean:
	rm -f simpledataconversion.Phs

veryclean: clean
	rm -f simpledataconversion.hs
