
%.phs: %.lphs
	lhs2TeX --code -lcodeOnly=True $< | cut -c3- > $@

polyp = ../bin/ghcpolyp
chase = ../bin/chase
split = ../bin/splitHeader

# POLYPFLAGS =

%.hs : %.phs
	$(polyp) $(POLYPFLAGS) $< > $@

phs_files = $(wildcard *.phs)
hs_files = $(phs_files:.phs=.hs)
phi_files = $(phs_files:.phs=.phi)

all : $(hs_files)

clean :
	rm -f $(hs_files) $(phi_files)

BaseM.hs : Base.hs
Crush.hs : Base.hs
CrushFuns.hs : Crush.hs Base.hs
EqualVariants.hs : Flatten.hs Zip.hs
Flatten.hs : Base.hs
Propagate.hs : Base.hs
Sum.hs : Base.hs
Thread.hs : Base.hs BaseM.hs
ThreadFuns.hs : Thread.hs
Zip.hs : Base.hs Propagate.hs
ZipVariants.hs : Zip.hs Flatten.hs
Show.hs : Base.hs ConstructorName.hs

#	$(chase) $(CHASEFLAGS) $< > /tmp/$(<:.phs=.full)
#	$(split) $@ /tmp/$(<:.phs=.body) /tmp/$(<:.phs=.full)
#	echo import MyPolyPrel >> $@
#	$(polyp) $(POLYPFLAGS) /tmp/$(<:.phs=.body) >> $@


