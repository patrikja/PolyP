\chapter{PolyPs prelude}
\begin{verbatim}

> module StartTBasis(startTBasis,preludeFuns,
>                    innType,outType,charType,intType,floatType,
>                    eitherType,fcnameType,dnameType,boolType,strType,
>                    sumtypename,leftname,rightname,
>                    preludedatadefs,sumdatadef,setImportFileNames) where
> import Parser(pType0,pType1,pTypeFile)
> import ParseLibrary(parse)
> import MyPrelude(mapSnd,splitUp,variablename,putErrStr)
> import Grammar(Eqn,Eqn'(..),Qualified(..),Type(..),VarID,Func,ConID,
>                (-=>),QType,Kind,qualify,deQualify,isDataDef,isExplType,
>                tupleConstructor,listConstructor,functionConstructor,
>                getNameOfDataDef)
> import MonadLibrary(unDone,(<@),(<@-),unLErr)
> import TypeBasis(TBasis,extendTypeTBasis,extendKindTBasis,emptyTBasis)
> import InferKind(inferDataDefs)
> import NonStdTrace(unsafePerformIO)
> import Flags(Flags(..),flags)
#if __GLASGOW_HASKELL__ > 600
> import Data.IORef
#else
> import IOExts
#endif

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

> typeass :: [(VarID,QType)]
> typeass = polypass ++ haskellass
> polypass :: [(VarID,QType)] 
> polypass = [("inn",innType),("out",outType),
>             ("constructorName",fcnameType),
>             ("constructorFixity",fcfixType),
>             ("datatypeName",dnameType)]

> preludeFuns :: [VarID]
> preludeFuns = map fst haskellass

\end{verbatim}

Idea: A prelude (haskell) file (specified on the command line) is used
to initialize the type information. Only data type declarations and
explicit type declarations are recorded - the rest is ignored.

First try: only explicit type declarations are accepted.
Second try: added data-declarations also.

\begin{verbatim}

> importFileNames :: [String]
> importFileNames = unsafePerformIO $ readIORef importFileNames'

> importFileNames' :: IORef [String]
> importFileNames' = unsafePerformIO $ newIORef []

> setImportFileNames :: [String] -> IO ()
> setImportFileNames xs = writeIORef importFileNames' xs

> preludeAssocs :: [(String,QType)]
> preludeAssocs = concatMap convExplType explTypes

> dataDefs, explTypes, preludeEqns :: [Eqn]
> [dataDefs, explTypes, _] = splitUp [isDataDef,isExplType] preludeEqns

> convExplType :: Eqn -> [(VarID,QType)]
> convExplType (ExplType ns t) = ns <@ (\n->(n,t))
> convExplType _ = error "StartTBasis.convExplType: impossible: not ExplType"

> preludeEqns = unDone . parse pTypeFile . unsafePerformIO $ prelfileIO

> prelfileIO :: IO String
> prelfileIO = mapM (readFileDef "") (preludeFileNames flags ++ importFileNames) <@ unlines

> readFileDef :: String -> FilePath -> IO String
> readFileDef d n = (((readFile n >>= \s -> 
>                     putErrStr (readOk n)<@- s) `catch` \_ ->
>                     readFile altFile >>= \s ->
>                     putErrStr (readOk altFile) <@- s) `catch` \_ ->
>                     readFile altFile2 >>= \s ->
>                     putErrStr (readOk altFile2) <@- s) `catch` \_ ->
>                     putErrStr readFailed >> (return d)
>   where readOk n   = "{- Interface file '" ++ n ++ "' read OK. -}\n"
>         readFailed = "{- ERROR: Interface file '" ++ n ++ 
>                      "' not found: neither as '" ++ n ++
>                      "', '" ++ altFile ++ 
>                      "' nor '" ++ altFile2 ++ 
>                      "'. -}\n"
>         altFile    = polypDir flags ++ "/lib/" ++ n
>         altFile2   = polypDir flags ++ "/polylib/" ++ n

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
>                          (extendTypeTBasis typeass . 
>                           extendKindTBasis kindass $
>                           emptyTBasis)
>                          preludedatadefs 
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

> pT :: String -> Type
> pT = unDone . parse pType1

> eitherTextType, sumtypename, leftname, rightname :: String
> eitherTextType = "(a -> b) -> (c -> b) -> Either a c -> b"

> innType, outType, eitherType, 
>   intType, floatType, charType, boolType, strType, fixType,
>   fcnameType, fcfixType :: QType

> innType = regular :=> fada -=> da
> outType = regular :=> da -=> fada
> eitherType= [] :=> pT eitherTextType
> --intType = [] :=> TCon "Int"
> intType = [("Num",[TVar "a"])] :=> TVar "a"
> floatType=[] :=> TCon "Float"
> charType= [] :=> TCon "Char"
> boolType= [] :=> TCon "Bool"
> strType = [] :=> TCon listConstructor :@@: TCon "Char"
> fixType = [] :=> TCon "Fixity"
> fcnameType= regular :=> da  -=> deQualify strType
> fcfixType = regular :=> da -=> deQualify fixType
> dnameType = regular :=> da  -=> deQualify strType

> fab, da, fada, fofd :: Type
> fab     = TVar "f" :@@: TVar "a" :@@: TVar "b"
> da      = TVar "d" :@@: TVar "a"
> fada    = fofd :@@: TVar "a" :@@: da

> regular, bifun :: [(String,[Type])]
> regular = [("Poly",[fofd])]
> bifun   = [("Poly",[TVar "f"])]
> fofd    = TCon "FunctorOf" :@@: TVar "d"

> sumdatadef :: Eqn' a

> preludedatadefs :: [Eqn]
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

