PrettyPrintLibrary.o: PrettyPrintLibrary.lhs
NonStdTrace.o: NonStdTrace.lhs
StateFix.o: StateFix.lhs
MyPrelude.o: MyPrelude.lhs NonStdTrace.hi
PrettyPrintExtra.o: PrettyPrintExtra.lhs PrettyPrintLibrary.hi
Grammar.o: Grammar.lhs MyPrelude.hi
MonadLibrary.o: MonadLibrary.lhs StateFix.hi MyPrelude.hi
GraphLibrary.o: GraphLibrary.lhs MyPrelude.hi StateFix.hi
PrettyPrinter.o: PrettyPrinter.lhs PrettyPrintExtra.hi Grammar.hi
Env.o: Env.lhs MyPrelude.hi MonadLibrary.hi
Folding.o: Folding.lhs Grammar.hi MyPrelude.hi MonadLibrary.hi
ParseLibrary.o: ParseLibrary.lhs MonadLibrary.hi
TypeGraph.o: TypeGraph.lhs MyPrelude.hi Grammar.hi PrettyPrinter.hi MonadLibrary.hi Env.hi Folding.hi
Parser.o: Parser.lhs MyPrelude.hi MonadLibrary.hi ParseLibrary.hi Grammar.hi
TypeBasis.o: TypeBasis.lhs Grammar.hi Folding.hi MyPrelude.hi MonadLibrary.hi Env.hi TypeGraph.hi
TypeError.o: TypeError.lhs TypeGraph.hi MonadLibrary.hi PrettyPrinter.hi Grammar.hi
UnifyTypes.o: UnifyTypes.lhs TypeGraph.hi TypeError.hi MonadLibrary.hi Env.hi Grammar.hi MyPrelude.hi
StartTBasis.o: StartTBasis.lhs Parser.hi ParseLibrary.hi MyPrelude.hi Grammar.hi MonadLibrary.hi Env.hi TypeBasis.hi
DependencyAnalysis.o: DependencyAnalysis.lhs Env.hi Folding.hi Grammar.hi GraphLibrary.hi MyPrelude.hi PrettyPrinter.hi TypeBasis.hi
InferKind.o: InferKind.lhs Grammar.hi TypeGraph.hi TypeBasis.hi PrettyPrinter.hi UnifyTypes.hi MonadLibrary.hi
Functorize.o: Functorize.lhs Env.hi Grammar.hi MyPrelude.hi Parser.hi StartTBasis.hi
InferType.o: InferType.lhs InferKind.hi UnifyTypes.hi TypeGraph.hi TypeBasis.hi StartTBasis.hi Env.hi MyPrelude.hi MonadLibrary.hi StateFix.hi Grammar.hi Folding.hi ParseLibrary.hi Parser.hi PrettyPrinter.hi
PolyInstance.o: PolyInstance.lhs Env.hi Grammar.hi Folding.hi Functorize.hi MonadLibrary.hi MyPrelude.hi Parser.hi PrettyPrinter.hi StartTBasis.hi TypeBasis.hi
LabelType.o: LabelType.lhs Env.hi Folding.hi Grammar.hi InferType.hi MonadLibrary.hi MyPrelude.hi StartTBasis.hi StateFix.hi TypeBasis.hi TypeGraph.hi UnifyTypes.hi
Main.o: Main.lhs DependencyAnalysis.hi Env.hi Grammar.hi LabelType.hi MonadLibrary.hi Parser.hi PolyInstance.hi PrettyPrinter.hi StateFix.hi TypeBasis.hi TypeGraph.hi UnifyTypes.hi
