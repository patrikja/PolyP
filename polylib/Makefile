
polyp = ../bin/ghcpolyp
chase = ../bin/chase
split = ../bin/splitHeader

# POLYPFLAGS =

%.hs : %.phs
	$(polyp) $(POLYPFLAGS) $< > $@

all: $(hs_files)

clean :
	rm -f $(hs_files) $(phi_files)

modules = BaseM Base Compare ConstructorName CrushFuns Crush Equal EqualVariants Flatten Fold Propagate Show Substructures Sum ThreadFuns Thread Zip ZipVariants EP

hsfiles = $(patsubst %,PolyLib/%.hs,$(modules))
phifiles = $(patsubst %,PolyLib/%.phi,$(modules))

all : $(hsfiles)

clean :
	rm -f $(hsfiles) $(phifiles)

PolyLib/BaseM.hs         : PolyLib/Base.hs
PolyLib/CrushFuns.hs     : PolyLib/Crush.hs PolyLib/Base.hs
PolyLib/Crush.hs         : PolyLib/Base.hs
PolyLib/EqualVariants.hs : PolyLib/Flatten.hs PolyLib/Zip.hs
PolyLib/Flatten.hs       : PolyLib/Base.hs
PolyLib/Fold.hs          : PolyLib/Base.hs
PolyLib/Propagate.hs     : PolyLib/Base.hs
PolyLib/Show.hs          : PolyLib/Base.hs PolyLib/ConstructorName.hs
PolyLib/Substructures.hs : PolyLib/Base.hs PolyLib/Flatten.hs
PolyLib/Sum.hs           : PolyLib/Base.hs
PolyLib/ThreadFuns.hs    : PolyLib/Base.hs PolyLib/BaseM.hs PolyLib/Thread.hs
PolyLib/Zip.hs           : PolyLib/Base.hs PolyLib/Propagate.hs
PolyLib/ZipVariants.hs   : PolyLib/Zip.hs  PolyLib/Flatten.hs


# lphs_files = $(wildcard *.lphs)
# phs_files = $(wildcard *.phs)
# hs_files = $(phs_files:.phs=.hs)
# phi_files = $(phs_files:.phs=.phi)
#	$(chase) $(CHASEFLAGS) $< > /tmp/$(<:.phs=.full)
#	$(split) $@ /tmp/$(<:.phs=.body) /tmp/$(<:.phs=.full)
#	echo import MyPolyPrel >> $@
#	$(polyp) $(POLYPFLAGS) /tmp/$(<:.phs=.body) >> $@

# %.phs: %.lphs
# 	lhs2TeX --code -lcodeOnly=True $< | cut -c3- > $@


