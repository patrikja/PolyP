\chapter{PolyPs prelude}
\begin{verbatim}

> module StartTBasis(startTBasis,preludeFuns,
>                    innType,outType,charType,intType,floatType,
>                    eitherType,fcnameType,boolType,strType,
>                    sumtypename,leftname,rightname,
>                    preludedatadefs,sumdatadef) where
> import Parser(pType0,pType1)
> import ParseLibrary(parse)
> import MyPrelude(mapSnd,trace)
> import Grammar(Eqn'(..),Qualified(..),Type(..),VarID)
> import MonadLibrary(Error,unDone)
> import Env(newEnv,extendsEnv)
> import TypeBasis(TBasis)

> infixr 9 -=>

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

These should be read from a file.

> haskellass = map (mapSnd (unDone . parse pType0))
>              [("[]","[a]"),(":","a->[a]->[a]"),
>               (leftname ,"a->"++sumtypename++" a b"),
>               (rightname,"b->"++sumtypename++" a b"),
>               ("True","Bool"),("False","Bool"),
>               ("Nothing","Maybe a"),("Just","a->Maybe a"),
>               ("LT","Ordering"),("EQ","Ordering"),("GT","Ordering"),
>               ("()","()"),
>               ("(,)","a->b->(a,b)"),
>               ("(,,)","a->b->c->(a,b,c)"),

>               (".","(b->c)->(a->b)->(a->c)"),
>               ("+","Num a => a->a->a"),
>               ("-","Num a => a->a->a"),
>               ("*","Num a => a->a->a"),
>               ("<=","Ord a => a->a->Bool"),
>               ("==","Eq a => a->a->Bool"),
>               ("&&","Bool->Bool->Bool"),
>               ("||","Bool->Bool->Bool"),
>               ("$","(a->b)->a->b"),
>               ("and","[Bool]->Bool"),
>               ("all","(a -> Bool) -> [a] -> Bool"),
>               ("any","(a -> Bool) -> [a] -> Bool"),
>               ("compare","Ord a => a -> a -> Ordering"),
>               ("or" ,"[Bool]->Bool"),
>               ("foldr","(a -> b -> b) -> b -> [a] -> b"),
>               ("negate","Num a => a->a"),
>               ("uncurry","(a -> b -> c) -> (a,b) -> c"),
>               ("error","[Char] -> a"),
>               ("undefined","a"),
>               ("print","Show a => a -> IO ()"),
>               ("length","[a] -> Int"),
>--               ("",""),
>               ("concat","[[a]]->[a]"),
>               ("maybe","a -> (b -> a) -> Maybe b -> a"),
>               ("const","a->b->a"),
>               ("either",eitherTextType),
>               ("id","a->a"),
>               ("map","(a->b)->[a]->[b]"),
>               ("++","[a]->[a]->[a]"),
>               ("fst","(a,b)->a"),("snd","(a,b)->b"),
>               ("head","[a]->a"),("tail","[a]->[a]"),
>               ("zip","[a] -> [b] -> [(a,b)]"),
>--               ("@@","Monad m => (b->m c) -> (a->m b) -> (a->m c)"),
>               ("return","Monad m => a -> m a"),
>               (">>=","Monad m => m a -> (a -> m b) -> m b")
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
>               [("->", s2s2s),
>                ("[]",s2s),
>                ("()",star),
>                ("(,)",s2s2s),
>                ("(,,)",s2s2s)] 
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
> strType = [] :=> TCon "[]" :@@: TCon "Char"
> fcnameType= bifun :=> fab -=> (TCon "[]" :@@: TCon "Char")
> fab     = TVar "f" :@@: TVar "a" :@@: TVar "b"
> da      = TVar "d" :@@: TVar "a"
> fada    = fofd :@@: TVar "a" :@@: da
> regular = [("Poly",[fofd])]
> bifun   = [("Poly",[TVar "f"])]
> fofd    = TCon "FunctorOf" :@@: TVar "d"
> a -=> b = TCon "->" :@@: a :@@: b

> (sumtypename,[leftname,rightname]) = ("Either",["Left","Right"])
> sumdatadef = DataDef sumtypename ["a","b"] 
>                      [(leftname,[TVar "a"]),(rightname,[TVar "b"])] []

> preludedatadefs = 
>   [DataDef "[]" ["a"] 
>            [("[]",[]), (":",[TVar "a",TCon "[]" :@@: TVar "a"])] 
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