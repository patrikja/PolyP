\chapter{Putting it all together}
\begin{verbatim}

> module Main(main) where
> import DependencyAnalysis(dependencyProgram)
> import Env(assocsEnv)
> import Grammar(Eqn'(..),Eqn,Type,PrgEqns,PrgTEqns,getNameOfEqn)
> import List(intersperse)
> import LabelType(labelProgram)
> import MonadLibrary(Error(..), handleError, unDone, 
>                     LErr, showLErr, mapLErr, 
>                     convertSTErr,mliftErr,(<@),(@@))
> import Parser(parse,pModule,pType1)
> import PolyInstance(instantiateProgram)
> import PrettyPrinter(Pretty(..),($$),text)
> import StateFix -- [(runST [,RunST])] in hugs, ghc, hbc
> import System(getArgs,getProgName)
> import TypeBasis(TBasis)
> import TypeGraph(kindIntoHeap,typesOutOfHeap)
> import UnifyTypes(unify)

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
In verbose mode every stage of the program generation presents s summary:
\begin{itemize}
\item The parser reports the names of the successfully parsed equations.
\item The dependency analysis presents the topologically sorted list
  of mutually reqursive groups of equations.
\item The type inference reports the types of all (top level) equations.
\item The code generation presents the generated code.
\end{itemize}
\begin{verbatim}

> report :: IO ()
> report = (putStrLn "{-" >>  -- Resync the emacs haskell mode: -}
>           getArgs       >>=  
>           handleArgs)   >>=  
>           report' 

> includeFlag :: String
> includeFlag = "-p"

> handleArgs :: [String] -> IO String
> handleArgs [] = putStr "Filename: " >> getLine
> handleArgs (('-':c:str):rest) | c `elem` "?h" = showUsage
> handleArgs (fl:fileName:rest) | fl == includeFlag = print fileName >> handleArgs rest
> handleArgs (file:rest)= return file


> report' :: PrgName -> IO ()
> report' n = readFile n >>= report''

> report'' :: PrgText -> IO ()
> report'' p = r1 >> r2 >> r3 >> putStrLn "-}" >> r4 >> putStrLn ""
>   where r4 = putStr (sp ++ handleError (\_->"") id err)
>         (sp,err) = mapLErr showEqns ip
>         ip = mapLErr instantiateProgram lp
>         r3 = typeReport lp
>         lp = labelProgram pqs 
>         r2 = dependencyReport pqs 
>         pqs= dependencyProgram qs 
>         r1 = parserReport qs
>         qs = parseProgram p

> showUsage :: IO a
> showUsage = getProgName >>= usage

> usage :: PrgName -> IO a
> usage name = error ("Usage: "++name++usageText) 

> usageText :: String
> usageText = " file.phs [>file.hs]"

> type FileName = String

\end{verbatim}
\subsection{Parser report}
\begin{verbatim}

> parserReport' :: [Eqn] -> [String]
> parserReport' = map getNameOfEqn

> parserReport :: [Eqn] -> IO ()
> parserReport = putStrLn . ("Parsed functions:\n"++) . 
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
> dependencyReport = putStrLn . ("Dependency ordered functions:\n("++)  
>                  . concat . (++[")"]) . intersperse "),(" 
>                  . map (concat . intersperse "," ) 
>                  . dependencyReport'

\end{verbatim}
\subsection{Type report}
\begin{verbatim}

> typeReport' :: LErr (TBasis,PrgTEqns) -> LErr [[Eqn]]
> typeReport' ((tb,(ds,qss)),err) = (map (map getEqnType) qss , err)
>   where getEqnType (Polytypic n t _ _)      = ExplType [n] t
>         getEqnType (VarBind n (Just t) _ _) = ExplType [n] t
>         getEqnType (VarBind n _ _ _) = error ("getEqnType: untyped eqn: "++n)
>	  getEqnType _ = error "Main: typeReport': impossible: not a binding"

> typeReport :: LErr (TBasis,PrgTEqns) -> IO ()
> typeReport = putStrLn . ("Typed functions:\n"++) . showLErr . 
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
> parseProgram = handleError id err . parse pModule
>   where
>     err = error . ("Parser: "++)

#ifdef __DEBUG__
> prettify :: PrgText -> PrgText
> prettify = concat . map (show.pretty) . parseProgram

> parseanddep :: PrgText -> PrgEqns
> parseanddep = dependencyProgram . parseProgram

> prettyordered :: PrgText -> PrgText
> prettyordered pgm = concatMap (unlines . map (show.pretty)) (datas:eqnss)
>   where (datas,eqnss) = parseanddep pgm

> labelling :: PrgText -> PrgText
> labelling = (\((b,p),e) -> showEqns (concat (fst p:snd p)) ++ showTBasis (b,e))
>           . labelProgram 
>           . dependencyProgram 
>           . parseProgram
#endif

\end{verbatim}
\section{Type inference}
\begin{verbatim}  

> showTBasis :: LErr TBasis -> String
> showTBasis (~(tenv,kenv),err) = concat (
>    ("Kinds:\n":map showpair (assocsEnv kenv) ) ++
>    ("Types:\n":map showpair (assocsEnv tenv) ) ++ [errtext] )
>   where showpair (name,t) = ' ':name ++ " :: " ++ show (pretty t)
>         errtext = handleError (\_->"") id err

> showEqns :: Pretty a => [a] -> String
> showEqns = concat . map (show.pretty)

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
>                putStr (show (pretty t2))
>                putStr (show (pretty t2'))

#ifdef __HBC__
> testunify' (t,t') = unDone $ runST $ RunST m'
>   where m'= convertSTErr m
#else /* not __HBC__ */
> testunify' (t,t') = unDone $ runST         m' 
>   where m'= convertSTErr m
#endif /* __HBC__ */
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
