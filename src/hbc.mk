# This is really a GNUmakefile, i.e. it requires GNU make extensions

prog = ../bin/hbcpolyp
#hs_flags += -O
hc = hbc

SUFFIXES= .hi .hs .lhs .o

default: $(prog)

%.hi:	%.o
	@
#echo tillverkar .hi fran .o

%.o:	%.hs
	$(hc) -c $(hs_flags) $<

%.o:	%.lhs
	$(hc) -c $(hs_flags) $<

o_files= Main.o DependencyAnalysis.o Env.o Grammar.o LabelType.o	\
         MonadLibrary.o Parser.o PolyInstance.o PrettyPrinter.o		\
         StateFix.o TypeBasis.o TypeGraph.o UnifyTypes.o Folding.o	\
         GraphLibrary.o MyPrelude.o InferType.o StartTBasis.o		\
         ParseLibrary.o Functorize.o PrettyPrintExtra.o			\
         PrettyPrintLibrary.o NonStdTrace.o InferKind.o
         
lhs_files = $(o_files:.o=.lhs)
hi_files  = $(o_files:.o=.hi)

clean::	
	rm -f *~
	rm -f $(o_files)
	rm -f $(prog)

veryclean::	clean
	rm -f $(hi_files)


$(prog):	$(o_files)
	$(hc) $(hs_flags) $(hs_link_flags) $^ -o $(prog) 

depends: hbcdepends.mk

# use hbcmake to recreate the dependencies in hbcdepends.mk
hbcdepends.mk: $(lhs_files)
	hbcmake -g Main.lhs > hbcdepends.mk

include hbcdepends.mk
