\chapter{PolyPs prelude}
\begin{verbatim}

> module StartTBasis(startTBasis,preludeFuns,
>                    innType,outType,charType,intType,floatType,
>                    eitherType,fcnameType,boolType,strType,
>                    sumtypename,leftname,rightname,
>                    preludedatadefs,sumdatadef) where
> import Parser(pType0,pType1,pExplicitTypes)
> import ParseLibrary(parse)
> import MyPrelude(mapSnd,trace)
> import Grammar(Eqn'(..),Qualified(..),Type(..),VarID,(-=>),QType,
>                deQualify,
>                tupleConstructor,listConstructor,functionConstructor)
> import MonadLibrary(Error,unDone,(<@))
> import Env(newEnv,extendsEnv)
> import TypeBasis(TBasis)
> import NonStdTrace(unsafePerformIO)
> import System(getEnv,getArgs)

\end{verbatim}
We will need three versions of the prelude:
\begin{itemize}
\item One as PolyP code. (For readability.)
\item One with commands to build the internal (this is what we have).
\item One precalculated internal. (Calcultated from from second and
  pasted into the file for efficiency.)
\end{itemize}
For the PolyP version - see \verb|../comments.txt|.

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

First try: only explicit type declarations are accepted - the rest is
ignored.

\begin{verbatim}

> preludeAssocs :: [(String,QType)]
> preludeAssocs = unDone . parse pExplicitTypes . unsafePerformIO $ prelfileIO

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
> readFileDef d n = readFile n `catch` \_ -> return d

> includeFlag :: String
> includeFlag = "-p"

> preludeFileNames :: [String] -> [String]
> preludeFileNames []       = []
> preludeFileNames (fl:name:rest) 
>    | fl == includeFlag    = name:preludeFileNames rest
> preludeFileNames (_:rest) = preludeFileNames rest


> haskellass :: [(String,QType)]
> haskellass = haskellConstructorAssoc ++ preludeAssocs

> haskellConstructorAssoc :: [(String,QType)]
> haskellConstructorAssoc = map (mapSnd (unDone . parse pType0))
>              [(listConstructor,"[a]"),(":","a->[a]->[a]"),
>               (leftname ,"a->"++sumtypename++" a b"),
>               (rightname,"b->"++sumtypename++" a b"),
>               ("True","Bool"),("False","Bool"),
>               ("Nothing","Maybe a"),("Just","a->Maybe a"),
>               ("LT","Ordering"),("EQ","Ordering"),("GT","Ordering"),
>               (tupleConstructor 0,"()"),
>               (tupleConstructor 2,"a->b->(a,b)"),
>               (tupleConstructor 3,"a->b->c->(a,b,c)")
>               ]

\end{verbatim}
The operator \verb|@@| is not in the Haskell prelude, but it is in
Gofer's {\tt cc.prelude}.
\begin{verbatim}

> startTBasis :: TBasis
> startTBasis = (extendsEnv typeass newEnv,
>                extendsEnv kindass newEnv )
>   where 
>     a2a2a  = pT "a->a->a"
>     s2s = star -=> star
>     s2s2s = star -=> s2s
>     kindass = kindhaskellass ++ kindpolypass
>
>     kindhaskellass = 
>               [(functionConstructor, s2s2s),
>                (listConstructor,     s2s),
>                (tupleConstructor 0,  star),
>                (tupleConstructor 2,  s2s2s),
>                (tupleConstructor 3,  star -=> s2s2s)] 
>            ++ map (\x->(x,star)) 
>                ["Char","Double","Float","Int","Integer",
>                 "IOError","Void","Ordering"]
>            ++ [("Maybe",s2s),
>                ("IO",s2s),
>                (sumtypename,s2s2s)]
>

>     kindpolypass = [("Mu", s2s2s -=> s2s),("FunctorOf", s2s -=> s2s2s)]
>     star = TCon "*" 

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
>   ,DataDef "Maybe" ["a"] 
>            [("Nothing",[]), ("Just",[TVar "a"])]
>            [] -- deriving (Eq, Ord, Read, Show)
>   ]


\end{verbatim}
Missing things:
\begin{itemize}
\item \texttt{String} (there are no type synonyms in PolyP)
\end{itemize}