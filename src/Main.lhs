\chapter{Putting it all together}
\begin{verbatim}

> module Main(main) where
> import DependencyAnalysis(dependencyProgram)
> import Grammar(Eqn'(..),Eqn,PrgEqns,PrgTEqns,getNameOfEqn)
> import List(intersperse)
> import LabelType(labelProgram)
> import MonadLibrary(handleError, LErr, showLErr, mapLErr)
> import MyPrelude(putErrStr,putErrStrLn,fatalError,fMap,stopNow)
> import Parser(parse,pModule)
> import PolyInstance(instantiateProgram)
> import PrettyPrinter(Pretty(..),($$),text,pshow)
> import StateFix -- [(runST [,RunST])] in hugs, ghc, hbc
> import System(getProgName)
> import TypeBasis(TBasis)
> import Flags(Flags(..),flags)

\end{verbatim}
\section{The main compilation function}
\begin{verbatim}

#ifdef __DEBUG__
> comp :: PrgName -> IO ()
> comp = putStr @@ compile 

> compile :: PrgName -> IO PrgText
> compile fpath = readFile fpath <@ compile'

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
>                  putErrStr ("-- Main: Failed to open file `"++fN++"'.\n")

> report' :: PrgName -> IO ()
> report' n = readFile n >>= report''

> report'' :: PrgText -> IO ()
> report'' p = r1 >> r2 >> r3 >> putErrStrLn "-}" >> r4 >> putErrStrLn ""
>   where r4 = putStr sp >> putErrStr (handleError id (fMap (\_->"") err))
>         (sp,err) = mapLErr showEqns ip
>         ip = mapLErr instantiateProgram lp
>         r3 = typeReport lp
>         lp = labelProgram pqs 
>         r2 = dependencyReport pqs 
>         pqs= dependencyProgram qs 
>         r1 = parserReport qs
>         qs = parseProgram p

> showVersion :: IO ()
> showVersion = putStrLn versionText

> versionText :: String
> versionText = "PolyP version " ++ __POLYP_VERSION__

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
> parserReport' = map getNameOfEqn

> parserReport :: [Eqn] -> IO ()
> parserReport = putErrStrLn . ("Parsed functions:\n"++) . 
>                concat . intersperse "," . parserReport' 

\end{verbatim}

\subsection{Dependency report}
The program doesn't handle mutual recursive datatypes.
\begin{verbatim}

> dependencyReport' :: PrgEqns -> [[String]]
> dependencyReport' (datas,eqnss) = map (:[]) (getnames datas) ++ 
>                                   map getnames eqnss
>   where getnames = map getNameOfEqn

> dependencyReport :: PrgEqns -> IO ()
> dependencyReport = putErrStrLn . ("Dependency ordered functions:\n("++)  
>                  . concat . (++[")"]) . intersperse "),(" 
>                  . map (concat . intersperse "," ) 
>                  . dependencyReport'

\end{verbatim}
\subsection{Type report}
\begin{verbatim}

> typeReport' :: LErr (TBasis,PrgTEqns) -> LErr [[Eqn]]
> typeReport' ((_,(_,qss)),err) = (map (map getEqnType) qss , err)
>   where getEqnType (Polytypic n t _ _)      = ExplType [n] t
>         getEqnType (VarBind n (Just t) _ _) = ExplType [n] t
>         getEqnType (VarBind n _ _ _) = error ("getEqnType: untyped eqn: "++n)
>	  getEqnType _ = error "Main.typeReport': impossible: not a binding"

> typeReport :: LErr (TBasis,PrgTEqns) -> IO ()
> typeReport = putErrStrLn . ("Typed functions:\n"++) . showLErr . 
>              mapLErr (stack . map (stack . map pretty)) . 
>              typeReport'
>   where stack [] = text "Empty type group - probably an error."
>         stack ds = foldr1 ($$) ds

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
> showTBasis (~(tenv,kenv),err) = concat (
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
> main =  report

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
>             mliftErr (typesOutOfHeap [] (ht,ht'))

> getType :: IO Type
> getType = getLine <@ parse pType1 <@ unDone

> testlabel :: IO ()
> testlabel = mloopit (map labelling . readFile)

> testpretord :: IO ()
> testpretord = mloopit (map prettyordered . readFile)

> testpretty :: IO ()
> testpretty = mloopit (map prettify . readFile)

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
