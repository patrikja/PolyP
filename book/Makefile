.PHONY: all print clean veryclean

.SUFFIXES:

all:	book.ps

book.ps:	book.dvi
	dvips -f <book.dvi >book.ps

print: book.dvi
	dvips -f <book.dvi | mpage -2r | lpr

book.dvi: book.toc
	latex book.tex

srcfiles = ../src/MyPrelude.lhs			\
	   ../src/MonadLibrary.lhs		\
	   ../src/ParseLibrary.lhs		\
	   ../src/Grammar.lhs			\
	   ../src/Parser.lhs			\
	   ../src/Folding.lhs			\
	   ../src/Functorize.lhs		\
	   ../src/PrettyPrintLibrary.lhs	\
	   ../src/PrettyPrintExtra.lhs		\
	   ../src/PrettyPrinter.lhs		\
	   ../src/Env.lhs			\
	   ../src/TypeGraph.lhs			\
	   ../src/TypeBasis.lhs			\
	   ../src/UnifyTypes.lhs		\
	   ../src/InferKind.lhs			\
	   ../src/StartTBasis.lhs		\
	   ../src/InferType.lhs			\
	   ../src/LabelType.lhs			\
	   ../src/PolyInstance.lhs		\
	   ../src/GraphLibrary.lhs		\
	   ../src/DependencyAnalysis.lhs	\
	   ../src/Main.lhs


book.toc: book.tex introduction.tex progress.tex $(srcfiles)
	latex book.tex


clean:
	rm -f *~
	rm -f book.aux
	rm -f book.log
	rm -f book.toc

veryclean:	clean
	rm -f book.dvi
	rm -f book.ps


