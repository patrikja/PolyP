\chapter{Putting it all together}
\begin{verbatim}

> module Main(main) where
#ifdef __DEBUG__
> import BuiltinInstances
> import Chase
> import CommandLine
> import DependencyAnalysis
> import Env
> import Flags
> import Folding
> import FunctorNames
> import Functorise
> import Grammar
> import GraphLibrary
> import InferKind
> import InferType
> import LabelType
> import MonadLibrary
> import MyPrelude
> import NonStdTrace
> import ParseLibrary
> import Parser
> import PolyInstance
> import PrettyPrintExtra
> import PrettyPrintLibrary
> import PrettyPrinter
> import StartTBasis
> import StateFix
> import TypeBasis
> import TypeError
> import TypeGraph
> import UnifyTypes
> import System(getProgName)
> import List(intersperse)
#else
> import DependencyAnalysis(dependencyProgram)
> import Grammar(Eqn'(..),Eqn,PrgEqns,PrgTEqns,getHeadOfEqn)
> import List(intersperse)
> import LabelType(labelProgram)
> import MonadLibrary(handleError, LErr, showLErr, mapLErr)
> import MyPrelude(putErrStr,putErrStrLn,fatalError,fMap,stopNow,flushErr)
> import Parser(parse,pModule)
> import PolyInstance(instantiateProgram)
> import PrettyPrinter(Pretty(..),($$),(<>),text,pshow,Doc)
> import Env(assocsEnv)
> import StateFix -- [(runST [,RunST])] in hugs, ghc, hbc
> import System(getProgName)
> import qualified IO(stderr)
> import TypeBasis(TBasis,getFuncEnv)
> import Flags(Flags(..),flags)
#endif

\end{verbatim}
\section{The main compilation function}
\begin{verbatim}

#ifdef __DEBUG__

> comp :: PrgName -> IO ()
> comp f = putStr =<< compile f

> compile :: PrgName -> IO PrgText
> compile fpath = fmap compile' $ readFile fpath

> compile' :: PrgText -> PrgText
> compile' = showLErr
>          . mapLErr ( showEqns
>                    . instantiateProgram 
>                    )
>          . labelProgram 
>          . dependencyProgram 
>          . parseProgram

#endif

\end{verbatim}
\section{Verbose mode}
In verbose mode every stage of the program generation presents a summary:
\begin{itemize}
\item The parser reports the names of the successfully parsed equations.
\item The dependency analysis presents the topologically sorted list
  of mutually recursive groups of equations.
\item The type inference reports the types of all (top level) equations.
\item The code generation presents the generated code.
\end{itemize}
\begin{verbatim}

> report :: IO ()
> report = (putErrStrLn "{-" >>  -- Resync the emacs haskell mode: -}
>           handleArgs)   >>=  
>           report' 

> handleArgs :: IO String
> handleArgs = if version flags 
>	       then showVersion >> stopNow
>	       else if help flags 
>	       then showUsage
>	       else if null (fileargs flags) 
>	       then putStr "Filename: " >> getLine
>	       else if length (fileargs flags) > 1 
>	       then fatalError "too many file arguments"
>	       else foldr (>>) (return (head (fileargs flags)))
>		    (map checkExists (preludeFileNames flags))


> checkExists :: String -> IO ()
> checkExists fN = (readFile fN >> return ()) `catch` \_ -> 
>                  putErrStr ("-- Main: Failed to open file `"++fN++"'.\n") >>
>                  flushErr

> report' :: PrgName -> IO ()
> report' n = readFile n >>= report''

> report'' :: PrgText -> IO ()
> report'' p = r1 >> r2 >> r3 >> putErrStrLn "-}" >> r4 >> flush
>   where r4 = putStr sp >> putErrStr (handleError id (fMap (\_->"") err))
>         (sp,err) = mapLErr showEqns ip
>         ip = mapLErr instantiateProgram lp
>         r3 = typeReport lp
>         lp = labelProgram pqs 
>         r2 = dependencyReport pqs 
>         pqs= dependencyProgram qs 
>         r1 = parserReport qs
>         qs = parseProgram p
>	  flush = putErrStrLn "" >> flushErr

> showVersion :: IO ()
> showVersion = putStrLn versionText

> versionText :: String
> versionText = "PolyP version " ++ __POLYP_VERSION__ ++ 
>		" (built "++ __DATE__ ++
>                  " with " ++ __POLYP_COMPILER__ ++ ")"

> showUsage :: IO a
> showUsage = getProgName >>= usage

> usage :: PrgName -> IO a
> usage name = error ("Usage: "++name++usageText) 

> usageText :: String
> usageText = " [-p preltypes.hs] file.phs [>file.hs]"

\end{verbatim}
\subsection{Parser report}
\begin{verbatim}

> parserReport' :: [Eqn] -> [String]
> parserReport' = map getHeadOfEqn

> parserReport :: [Eqn] -> IO ()
> parserReport = putErrStrLn . ("Parsed entities:\n"++) . 
>                concat . intersperse ", " . parserReport' 

\end{verbatim}

\subsection{Dependency report}
The program doesn't handle mutual recursive datatypes.
\begin{verbatim}

> dependencyReport' :: PrgEqns -> [[String]]
> dependencyReport' (datas,eqnss) = map (:[]) (getnames datas) ++ 
>                                   map getnames eqnss
>   where getnames = map getHeadOfEqn

> dependencyReport :: PrgEqns -> IO ()
> dependencyReport = putErrStrLn . ("Dependency ordered entities:\n("++)  
>                  . concat . (++[")"]) . intersperse "),(" 
>                  . map (concat . intersperse "," ) 
>                  . dependencyReport'

\end{verbatim}
\subsection{Type report}
\begin{verbatim}

> typeReport' :: LErr (TBasis,PrgTEqns) -> LErr Doc
> typeReport' ((tb,(ds,qss)),err) = 
>    (reportFuncEnv tb  $$ reportEqs qss, err)
>   where reportFuncEnv = stack . map reportFunc . assocsEnv . getFuncEnv
>         reportFunc (d,(_,f)) = text ("FunctorOf "++d++" = ") <> pretty f
>         --reportDatas = text . concat . intersperse "," . map getHeadOfEqn  
>         reportEqs = stack . map (stack' . map (pretty . getEqnType))
>         getEqnType (Polytypic n t _ _)      = ExplType [n] t
>         getEqnType (VarBind n (Just t) _ _) = ExplType [n] t
>         getEqnType (VarBind n _ _ _) = error ("getEqnType: untyped eqn: "++n)
>	  getEqnType _ = error "Main.typeReport': impossible: not a binding"
>         stack  [] = text ""
>         stack  ds = foldr1 ($$) ds
>         stack' [] = text "Error: typeReport: Empty binding group."
>         stack' ds = foldr1 ($$) ds                               

> typeReport :: LErr (TBasis,PrgTEqns) -> IO ()
> typeReport = putErrStrLn . ("After typing:\n"++) . showLErr . 
>              typeReport'

\end{verbatim} 
This printing could be made lazier, leading to better error
localisation, if the prettyprinter was replaced by a function that
prints the name first and only then looks at the data.

\section{Parsing and dependency analysis}
These are still preliminary versions. 
\begin{verbatim}

> type PrgName = String
> type PrgText = String

> parseProgram :: PrgText -> [Eqn]
> parseProgram = handleError err . parse pModule
>   where
>     err = error . ("Main.parseProgram: "++)

#ifdef __DEBUG__
> prettify :: PrgText -> PrgText
> prettify = concat . map pshow . parseProgram

> parseanddep :: PrgText -> PrgEqns
> parseanddep = dependencyProgram . parseProgram

> prettyordered :: PrgText -> PrgText
> prettyordered pgm = concatMap (unlines . map pshow) (datas:eqnss)
>   where (datas,eqnss) = parseanddep pgm

> labelling :: PrgText -> PrgText
> labelling = (\((b,p),e) -> showEqns (concat (fst p:snd p)) ++ showTBasis (b,e))
>           . labelProgram 
>           . dependencyProgram 
>           . parseProgram

\end{verbatim}
\section{Type inference}
\begin{verbatim}  

> showTBasis :: LErr TBasis -> String
> showTBasis (~((tenv,kenv),fenv),err) = concat (
>    ("Kinds:\n":map showpair (assocsEnv kenv) ) ++
>    ("Types:\n":map showpair (assocsEnv tenv) ) ++ [errtext] )
>   where showpair (name,t) = ' ':name ++ " :: " ++ pshow t
>         errtext = handleError id (fMap (\_->"") err)

#endif

> showEqns :: Pretty a => [a] -> String
> showEqns = concat . map pshow

\end{verbatim}
\section{Code generation}
{\tt instantiateProgram} generates the necessary polytypic instances
as a list of equations. To make this a complete program we need a
prelude.
\subsection{The prelude}
Two possible approaches:
\begin{itemize}
\item A small built-in prelude. Can be pre-compiled and therefore
  quick to handle.
\item A user-specified file. It must be read and type checked just
  like the normal file and --- if it contains polytypic definitions
  --- instances must be emitted. These new instances could either go
  to a renamed version of the specified prelude or directly to the
  output file. 
\end{itemize}
\section{main}
\begin{verbatim}
 
> main :: IO ()
> main = report 

main = seq IO.stderr report 

The "seq stderr" was a try to work around a ghc-bug:
  "The problem is caused by overzealous locking in our I/O library"
(GHC 4.06 Mini-FAQ, http://haskell.org/ghc/faq_406.html)

It does not seem to work.


#ifdef __DEBUG__
> testunify = do t <- getType
>                t'<- getType
>                let (t2,t2') = testunify' (t,t')
>                putStr (pshow t2)
>                putStr (pshow t2')

> testunify' (t,t') = unDone $ __RUNST__ m'
>   where m'= convertSTErr m
>         m = mliftErr (kindIntoHeap t) >>= \ht-> 
>             mliftErr (kindIntoHeap t')>>= \ht'->
>             unify ht ht'              >>
>             mliftErr (typesOutOfHeap allGeneric [ht,ht']) >>= \[x,y] ->
>             return (x,y)

> getType :: IO Type
> getType = getLine <@ parse pType1 <@ unDone

> testlabel :: IO ()
> testlabel = mloopit (fmap labelling . readFile)

> testpretord :: IO ()
> testpretord = mloopit (fmap prettyordered . readFile)

> testpretty :: IO ()
> testpretty = mloopit (fmap prettify . readFile)

> testall :: IO ()
> testall = comp @@ const getLine @@ putStr $ "Filename: "


> mloopit :: (String -> IO String) -> IO ()
> mloopit f = do putStr "\n>"
>                s <- getLine
>                s' <- f s
>                putStr s'
>                mloopit f

> loopit :: (String -> String) -> IO ()
> loopit f = do putStr "\n>"
>               s <- getLine
>               putStr (f s)
>               loopit f
#endif

\end{verbatim}
