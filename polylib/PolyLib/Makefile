
%.hs : %.phs
	(cd ..; polyp PolyLib/$< > PolyLib/$@)

modules = BaseM Base Compare ConstructorName CrushFuns Crush Equal EqualVariants Flatten Fold Propagate Show Substructures Sum ThreadFuns Thread Zip ZipVariants EP

all : $(modules:=.hs)

clean :
	rm -f $(modules:=.hs) $(modules:=.phi)

BaseM.hs : Base.hs
CrushFuns.hs : Crush.hs Base.hs
Crush.hs : Base.hs
EqualVariants.hs : Flatten.hs Zip.hs
Flatten.hs : Base.hs
Fold.hs : Base.hs
Propagate.hs : Base.hs
Show.hs : Base.hs ConstructorName.hs
Substructures.hs : Base.hs Flatten.hs
Sum.hs : Base.hs
ThreadFuns.hs : Base.hs BaseM.hs Thread.hs
Zip.hs : Base.hs Propagate.hs
ZipVariants.hs : Zip.hs Flatten.hs

