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
> import IO
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
> import System
> import List
#else
> import DependencyAnalysis(dependencyProgram)
> import Grammar(Module'(..),Module,ImpExp(..),Import,Export,Eqn'(..),Eqn,PrgEqns,PrgTEqns,TEqn,ConID,QType,Qualified(..),Qualifier,Type,VarID,getHeadOfEqn)
> import List(intersperse,nubBy,isPrefixOf,nub,nubBy,deleteBy,(\\))
> import IO(hPutStrLn)
> import LabelType(labelProgram)
> import MonadLibrary(handleError, LErr, showLErr, mapLErr)
> import MyPrelude(errorfile,putErrStr,putErrStrLn,fatalError,fMap,stopNow,flushErr,mapSnd)
> import Parser(parse,pModule)
> import PolyInstance(instantiateProgram)
> import PrettyPrinter(Pretty(..),($$),(<>),text,pshow,Doc)
> import Env(assocsEnv)
> import StateFix -- [(runST [,RunST])] in hugs, ghc, hbc
> import System(getProgName,exitWith,ExitCode(..))
> import qualified IO(stderr)
> import TypeBasis(TBasis,TypeEnv,getTypeEnv,getFuncEnv)
> import Flags(Flags(..),flags)
> import StartTBasis (setImportFileNames)
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
>          . moduleEqns
>          . parseProgram
>   where moduleEqns (Module _ _ _ qs) = qs

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

> report :: IO ExitCode
> report = (putErrStrLn "{-" >>  -- Resync the emacs haskell mode: -}
>           handleArgs)   >>=  
>           report'

> handleArgs :: IO String
> handleArgs = if version flags 
>         then showVersion >> stopNow
>         else if help flags 
>         then showUsage
>         else if null (fileargs flags) 
>         then putStr "Filename: " >> getLine
>         else if length (fileargs flags) > 1 
>         then fatalError "too many file arguments"
>         else foldr (>>) (return (head (fileargs flags)))
>         (map checkExists (preludeFileNames flags))


> checkExists :: String -> IO ()
> checkExists fN = (readFile fN >> return ()) `catch` \_ -> 
>                  putErrStr ("-- Main: Failed to open file `"++fN++"'.\n") >>
>                  flushErr

> report' :: PrgName -> IO ExitCode
> report' n = readFile n >>= report'' n

> report'' :: PrgName -> PrgText -> IO ExitCode
> report'' n p = r0 >> r1 >> r2 >> r3 >> putErrStrLn "-}" >> r4 >> r5 >> flush >> return ec
>   where r4 = putStr sp >> putErrStr (handleError id (fMap (\_->"") err))
>         r5 = writeFile (hiFile n) hi >> putErrStr (handleError id (fMap (\_ -> "") err2))
>         (hi,err2) = mapLErr (showInterface $ fst lp) im
>	  exitCode err = handleError (const $ ExitFailure 1) (fMap (const ExitSuccess) err)
>	  ec = case (exitCode err, exitCode err2) of
>		(ExitSuccess, ExitSuccess)  -> ExitSuccess
>		_			    -> ExitFailure 1
>         (sp,err) = mapLErr pshow im
>         im = mapLErr (addClasses $ getTypeEnv $ fst $ fst lp) im0
>         --im0 = mapLErr (Module name exps (("PolyPrelude",[]):imps)) ip
>         im0 = mapLErr (Module name exps imps) ip
>         ip = mapLErr instantiateProgram lp
>         r3 = typeReport lp
>         lp = labelProgram pqs
>         r2 = dependencyReport pqs
>         pqs= dependencyProgram qs
>         r1 = parserReport qs
>         r0 = setImportFileNames $ map ((++".phi") . dot2slash . fst) imps
>         Module name exps imps qs = m
>         m  = parseProgram p
>         flush = putErrStrLn "" >> flushErr
>         getExps (Module _ exps _ _) = exps
>	  dot2slash = map s
>	    where s '.' = '/'
>		  s c = c

> showVersion :: IO ()
> showVersion = putStrLn versionText

> versionText :: String
> versionText = "PolyP version " ++ __POLYP_VERSION__ ++ 
>     " (built "++ __DATE__ ++
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
> dependencyReport' (datas,_,eqnss) = map (:[]) (getnames datas) ++ 
>                                     map getnames eqnss
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
> typeReport' ((tb,(ds,ixs,qss)),err) = 
>    (reportFuncEnv tb  $$ reportIxs ixs $$ reportEqs qss, err)
>   where reportFuncEnv = stack . map reportFunc . assocsEnv . getFuncEnv
>         reportFunc (d,(_,f)) = text ("FunctorOf "++d++" = ") <> pretty f
>         --reportDatas = text . concat . intersperse "," . map getHeadOfEqn  
>	  reportIxs = stack . map pretty
>         reportEqs = stack . map (stack' . map (pretty . getEqnType))
>         getEqnType (Polytypic n t _ _)      = ExplType [n] t
>         getEqnType (VarBind n (Just t) _ _) = ExplType [n] t
>         getEqnType (VarBind n _ _ _) = error ("getEqnType: untyped eqn: "++n)
>         getEqnType _ = error "Main.typeReport': impossible: not a binding"
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

> parseProgram :: PrgText -> Module --[Eqn]
> parseProgram = handleError err . parse pModule
>   where
>     err = error . ("Main.parseProgram: "++)

#ifdef __DEBUG__
> prettify :: PrgText -> PrgText
> prettify = pshow . parseProgram

> parseanddep :: PrgText -> PrgEqns
> parseanddep = dependencyProgram . moduleEqns . parseProgram
>   where moduleEqns (Module _ _ _ eqns) = eqns

> prettyordered :: PrgText -> PrgText
> prettyordered pgm = concatMap (unlines . map pshow) (datas:infixdecls:eqnss)
>   where (datas,infixdecls,eqnss) = parseanddep pgm

> labelling :: PrgText -> PrgText
> labelling = (\((b,(d,x,q)),e) -> showEqns (concat (d:x:q)) ++ showTBasis (b,e))
>           . labelProgram 
>           . dependencyProgram
>	    . moduleEqns
>           . parseProgram
>   where moduleEqns (Module _ _ _ eqns) = eqns

\end{verbatim}
\section{Type inference}
\begin{verbatim}  

> showTBasis :: LErr TBasis -> String
> showTBasis (~(((tenv,xenv),kenv),fenv),err) = concat (
>    ("Kinds:\n":map showpair (assocsEnv kenv) ) ++
>    ("Fixities:\n":map showpair (assocsEnv xenv) ) ++
>    ("Types:\n":map showpair (assocsEnv tenv) ) ++ [errtext] )
>   where showpair (name,t) = ' ':name ++ " :: " ++ pshow t
>         errtext = handleError id (fMap (\_->"") err)

#endif

> showEqns :: Pretty a => [a] -> String
> showEqns = concat . map pshow

> definedFunctions :: [TEqn] -> [(VarID,QType)]
> definedFunctions eqns = concatMap def eqns
>     where
>        def (ExplType vs t)          = zip vs $ repeat t 
>        def (VarBind n (Just t) _ _) = [(n,t)]
>        def (Class _ ctx eqns)       = map (addCtx ctx) $ definedFunctions eqns
>        def _                        = []
>        addCtx c (n,cs :=> t)        = (n, (c:cs) :=> t)

> getPClasses :: [Eqn] -> [ConID]
> getPClasses = nub . concatMap pcls
>   where
>       pcls (ExplType (n:_) (c:=>_))       = pClasses c
>       pcls (VarBind n (Just (c:=>_)) _ _) = pClasses c
>       pcls _                              = []

> pClasses :: [Qualifier Type] -> [ConID]
> pClasses = filter (isPrefixOf "P_") . map fst

> externalFunctions :: TypeEnv -> [(VarID,QType)] -> [(VarID,QType)]
> externalFunctions allfuns internal = foldr (deleteBy fstEq) allfuns internal
>   where fstEq (x,_) (y,_) = x == y

> addClasses :: TypeEnv -> Module -> Module
> addClasses tenv (Module name exps imps eqns) = Module name exps' imps' eqns
>   where expcls  = getPClasses eqns
>         exps' | null exps = []
>               | otherwise = exps ++ map Plain expcls
>         ext     = externalFunctions tenv $ definedFunctions eqns
>         cenv    = concatMap (\(n,c:=>_) -> zip (repeat n) (pClasses c)) ext
>         imps0   = map (mapSnd (map unPlain . filter isPlain)) imps
>         impEnv  = nubb $ map (mapSnd findClasses) imps0
>         findClasses   = nub . concatMap (lUp cenv)
>         lUp cenv n    = nub $ map snd $ filter ((==n) . fst) cenv
>         imps'         = zipWith (\(i,is) cs -> (i,is ++ map Plain cs)) imps (map snd impEnv)
>         nubb ((i,cs):is) = (i,cs) : nubb (map (mapSnd (\\cs)) is)
>         nubb []          = []
>         unPlain (Plain s) = s
>         isPlain (Plain _) = True
>         isPlain _         = False

> showInterface :: (TBasis, PrgTEqns) -> Module -> String
> showInterface ((((tenv,_),_),_), (datadefs,infixdecls,_)) (Module _ exps _ eqns) =
>     "-- Functions\n" ++
>     concatMap pshow (concatMap toExplType allFuns) ++
>     "-- Datatypes\n" ++
>     concatMap pshow datadefs
>   where
>     allFuns = nubBy (\x y -> fst x == fst y) $ defs ++ tenv
>     toExplType (f,t)
>        | f `elem` explist   = [ExplType [f] t]
>        | otherwise          = []
>     defs = definedFunctions eqns
>     explist
>        | null exps  = map fst defs
>        | otherwise  = map name exps
>     name (Plain n)  = n
>     name (Mod m)    = m
>     name (Subs n _) = n

> hiFile :: PrgName -> PrgName
> hiFile ('.':s)
>  | '.' `notElem` s = ".phi"
> hiFile (c:s)       = c:hiFile s
> hiFile []          = ".phi"

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
> main = report >>= exitWith

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
