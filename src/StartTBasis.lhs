\chapter{PolyPs prelude}
\begin{verbatim}

> module StartTBasis(startTBasis,preludeFuns,
>                    innType,outType,charType,intType,floatType,
>                    eitherType,fcnameType,boolType,strType,
>                    sumtypename,leftname,rightname,
>                    preludedatadefs,sumdatadef) where
> import Parser(pType0,pType1,pTypeFile)
> import ParseLibrary(parse)
> import MyPrelude(mapSnd,splitUp,maytrace,variablename,putErrStr)
> import Grammar(Eqn,Eqn'(..),Qualified(..),Type(..),VarID,
>                (-=>),QType,Kind,qualify,deQualify,isDataDef,
>                tupleConstructor,listConstructor,functionConstructor)
> import MonadLibrary(Error,unDone,(<@),(<@-),unLErr)
> import Env(newEnv,extendsEnv)
> import TypeBasis(TBasis)
> import InferKind(inferDataDefs)
> import NonStdTrace(unsafePerformIO)
> import System(getEnv,getArgs)

\end{verbatim}
We could need three versions of the prelude:
\begin{itemize}
\item One as PolyP code. (For readability.)
\item One with commands to build the internal (this is what we have).
\item One precalculated internal. (Calcultated from from second and
  pasted into the file for efficiency.)
\end{itemize}
For the PolyP version - see \verb|../lib/PolyPrel.hs|.

\begin{verbatim}

> typeass = polypass ++ haskellass
> polypass = [("inn",innType),("out",outType),
>             ("fconstructorName",fcnameType)]

> preludeFuns :: [VarID]
> preludeFuns = map fst haskellass

\end{verbatim}

Idea: A prelude (haskell) file (specified on the command line) is used
to initialize the type information. Only data type declarations and
explicit type declarations are recorded - the rest is ignored.

First try: only explicit type declarations are accepted.
Second try: added data-declarations also.

\begin{verbatim}

> preludeAssocs :: [(String,QType)]
> preludeAssocs = concatMap convExplType explTypes

> preludeEqns, dataDefs, explTypes :: [Eqn]
> [dataDefs, explTypes] = splitUp [isDataDef] preludeEqns

> preludeEqns = unDone . parse pTypeFile . unsafePerformIO $ prelfileIO

> convExplType :: Eqn -> [(VarID,QType)]
> convExplType (ExplType ns t) = ns <@ (\n->(n,t))
> convExplType _ = error "StartTBasis.convExplType: impossible: not ExplType"

> getEnvDef :: String -> String -> IO String
> getEnvDef e d = getEnv e `catch` \ _ -> return d

> preludeFileName :: String

#ifdef __POLYPPRELUDE__
> preludeFileName = __POLYPPRELUDE__
#else
> preludeFileName = "PolyPrel.hs"
#endif

> prelfileIO :: IO String
> prelfileIO = do 
>    preludename  <- getEnvDef "POLYPPRELUDE" preludeFileName
>    includenames <- getArgs <@ preludeFileNames
>    mapM (readFileDef "") (preludename : includenames) <@ concat


> readFileDef :: String -> FilePath -> IO String
> readFileDef d n = (readFile n >>= \s -> 
>                    putErrStr readOk <@- s) `catch` \_ -> 
>                   putErrStr readFailed >> (return d)
>   where readOk     = "{- Prelude file '" ++ n ++ "' read OK. -}\n"
>         readFailed = "{- ERROR: Prelude file '" ++ n ++ "' not found. -}\n"

> includeFlag :: String
> includeFlag = "-p"

> preludeFileNames :: [String] -> [String]
> preludeFileNames []       = []
> preludeFileNames (fl:name:rest) 
>    | fl == includeFlag    = name:preludeFileNames rest
> preludeFileNames (_:rest) = preludeFileNames rest

> haskellass :: [(String,QType)]
> haskellass = haskellConstructorAssoc ++ preludeAssocs

> maxTupleSize :: Int
> maxTupleSize = 7

> haskellConstructorAssoc :: [(String,QType)]
> haskellConstructorAssoc = 
>       map (mapSnd (unDone . parse pType0))
>              [(listConstructor,"[a]"),(":","a->[a]->[a]")]
>    ++ map (\n-> (tupleConstructor n, tupleType n)) (0:[2..maxTupleSize])

> tupleType :: Int -> QType
> tupleType 1 = error "StartTBasis.tupleType: There are no 1-tuples"
> tupleType n = qualify $ foldr1 (-=>) (tyvars ++ [tuple])
>   where tuple = foldl1 (:@@:) (TCon (tupleConstructor n):tyvars)
>         tyvars = map (TVar . variablename) [0..n-1]

> tupleKind :: Int -> Kind
> tupleKind 1 = error "StartTBasis.tupleKind: There are no 1-tuples"
> tupleKind n = foldr1 (-=>) (replicate (n+1) starKind)

\end{verbatim}
The operator \verb|@@| is not in the Haskell prelude, but it is in
Gofer's {\tt cc.prelude}.
\begin{verbatim}

> startTBasis :: TBasis
> startTBasis = unLErr $ inferDataDefs 
>                          (extendsEnv typeass newEnv,
>                           extendsEnv kindass newEnv ) 
>                          dataDefs
>   where 
>     s2s     = starKind -=> starKind
>     s2s2s   = starKind -=> s2s
>     kindass = kindhaskellass ++ kindpolypass
>
>     kindhaskellass = 
>               [(functionConstructor, s2s2s),
>                (listConstructor,     s2s)]
>            ++ map (\n-> (tupleConstructor n, tupleKind n))
>                   (0:[2..maxTupleSize])
>            ++ map (\x->(x,starKind)) 
>                ["Char","Double","Float","Int","Integer",
>                 "IOError","Void","Ordering"]
>            ++ [("IO",s2s)]
>

>     kindpolypass = [("Mu", s2s2s -=> s2s),("FunctorOf", s2s -=> s2s2s)]

> starKind :: Kind
> starKind = TCon "*" 


> pT = unDone . parse pType1

> eitherTextType = "(a -> b) -> (c -> b) -> Either a c -> b"

> innType = regular :=> fada -=> da
> outType = regular :=> da -=> fada
> eitherType= [] :=> pT eitherTextType
> intType = [] :=> TCon "Int"
> floatType=[] :=> TCon "Float"
> charType= [] :=> TCon "Char"
> boolType= [] :=> TCon "Bool"
> strType = [] :=> TCon listConstructor :@@: TCon "Char"
> fcnameType= bifun :=> fab -=> deQualify strType
> fab     = TVar "f" :@@: TVar "a" :@@: TVar "b"
> da      = TVar "d" :@@: TVar "a"
> fada    = fofd :@@: TVar "a" :@@: da
> regular = [("Poly",[fofd])]
> bifun   = [("Poly",[TVar "f"])]
> fofd    = TCon "FunctorOf" :@@: TVar "d"

> (sumtypename,[leftname,rightname]) = ("Either",["Left","Right"])
> sumdatadef = DataDef sumtypename ["a","b"] 
>                      [(leftname,[TVar "a"]),(rightname,[TVar "b"])] []

> preludedatadefs = 
>   [DataDef "[]" ["a"] 
>            [("[]",[]), (":",[TVar "a",TCon listConstructor :@@: TVar "a"])] 
>            [] -- deriving
>   ]
>   ++ dataDefs

\end{verbatim}
The \texttt{preludedatadefs} are used in \texttt{PolyInstance} to
translate datatypes to functors.
%

%
There is no type synonym handling in the main part of PolyP, but the
type synonym \texttt{String} is translated to \texttt{[Char]} by the
parser.

