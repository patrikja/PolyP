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
         PrettyPrintLibrary.o StateArrayFix.o NonStdTrace.o		\
         InferKind.o

hi_files= Main.hi DependencyAnalysis.hi Env.hi Grammar.hi LabelType.hi	\
          MonadLibrary.hi Parser.hi PolyInstance.hi PrettyPrinter.hi	\
          StateFix.hi TypeBasis.hi TypeGraph.hi UnifyTypes.hi		\
          Folding.hi GraphLibrary.hi MyPrelude.hi InferType.hi		\
          StartTBasis.hi ParseLibrary.hi Functorize.hi			\
          PrettyPrintExtra.hi PrettyPrintLibrary.hi StateArrayFix.hi	\
          NonStdTrace.hi InferKind.hi

clean::	
	rm -f *~
	rm -f $(o_files)
	rm -f $(prog)

veryclean::
	rm -f $(hi_files)


$(prog):	$(o_files)
	$(hc) $(hs_flags) $(hs_link_flags) $^ -o $(prog) 

NonStdTrace.o: NonStdTrace.lhs

StateFix.o: StateFix.lhs

PrettyPrintLibrary.o: PrettyPrintLibrary.lhs

StateArrayFix.o: StateArrayFix.lhs

MyPrelude.o: MyPrelude.lhs NonStdTrace.hi

PrettyPrintExtra.o: PrettyPrintExtra.lhs PrettyPrintLibrary.hi

Grammar.o: Grammar.lhs MyPrelude.hi

MonadLibrary.o: MonadLibrary.lhs StateFix.hi MyPrelude.hi

GraphLibrary.o: GraphLibrary.lhs MyPrelude.hi StateFix.hi StateArrayFix.hi

Env.o: Env.lhs MyPrelude.hi MonadLibrary.hi

Folding.o: Folding.lhs Grammar.hi MyPrelude.hi MonadLibrary.hi

PrettyPrinter.o: PrettyPrinter.lhs MonadLibrary.hi PrettyPrintExtra.hi Grammar.hi

ParseLibrary.o: ParseLibrary.lhs MonadLibrary.hi

TypeGraph.o: TypeGraph.lhs StateFix.hi MyPrelude.hi Grammar.hi	\
             PrettyPrintExtra.hi PrettyPrintLibrary.hi 		\
             MonadLibrary.hi Env.hi Folding.hi

Parser.o: Parser.lhs MyPrelude.hi MonadLibrary.hi 	\
          ParseLibrary.hi Grammar.hi

TypeBasis.o: TypeBasis.lhs Grammar.hi Folding.hi 	\
             StateFix.hi MyPrelude.hi 			\
             MonadLibrary.hi Env.hi TypeGraph.hi

UnifyTypes.o: UnifyTypes.lhs MyPrelude.hi TypeGraph.hi 		\
              StateFix.hi MonadLibrary.hi Env.hi 		\
              PrettyPrintExtra.hi PrettyPrinter.hi Grammar.hi

InferKind.o: InferKind.lhs Grammar.hi TypeGraph.hi TypeBasis.hi 	\
             PrettyPrinter.hi UnifyTypes.hi MonadLibrary.hi

StartTBasis.o: StartTBasis.lhs Parser.hi ParseLibrary.hi 	\
               MyPrelude.hi Grammar.hi MonadLibrary.hi 		\
               Env.hi TypeBasis.hi

DependencyAnalysis.o: DependencyAnalysis.lhs Env.hi 			\
                      Folding.hi Grammar.hi GraphLibrary.hi 		\
                      MyPrelude.hi PrettyPrinter.hi TypeBasis.hi

Functorize.o: Functorize.lhs Env.hi Grammar.hi MyPrelude.hi 	\
              Parser.hi StartTBasis.hi

InferType.o: InferType.lhs InferKind.hi UnifyTypes.hi TypeGraph.hi 	\
             TypeBasis.hi StartTBasis.hi Env.hi MyPrelude.hi 		\
             MonadLibrary.hi Grammar.hi Folding.hi 			\
             StateFix.hi ParseLibrary.hi Parser.hi PrettyPrinter.hi

PolyInstance.o: PolyInstance.lhs Env.hi Grammar.hi Folding.hi 		\
                Functorize.hi MonadLibrary.hi MyPrelude.hi 		\
                Parser.hi PrettyPrinter.hi StartTBasis.hi TypeBasis.hi
	$(hc) -c $(hs_flags) -H12000000 $<

LabelType.o: LabelType.lhs Env.hi Folding.hi Grammar.hi InferType.hi 	\
             MonadLibrary.hi MyPrelude.hi StartTBasis.hi StateFix.hi 	\
             TypeBasis.hi TypeGraph.hi UnifyTypes.hi

Main.o: Main.lhs DependencyAnalysis.hi Env.hi Grammar.hi 			\
        LabelType.hi MonadLibrary.hi Parser.hi PolyInstance.hi 			\
        PrettyPrinter.hi StateFix.hi TypeBasis.hi TypeGraph.hi UnifyTypes.hi
