\chapter{Predefined instances}
\begin{verbatim}

> module BuiltinInstances(inn_def,out_def,either_def,fcname_def,dname_def,
>                         makeUncurry,parseUncurry,isUncurry,
>                         Req,eqReq) where
> import Env(lookupEnv)
> import Functorise(Struct)
> import Grammar(Eqn'(..),Expr'(..),Expr,Type(..),Qualified(..),Literal(..),
>                Eqn,Func,QType, ConID,VarID,spineWalkType,
>                tupleConstructor,listConstructor,isTupleCon,(-=>),qualify)
> import Folding(cataType)
> import MonadLibrary(Error(..),ErrorMonad(..),map0,map1,map2,accumseq)
> import MyPrelude(mapFst,mapSnd,pair,variablename,fMap)
> import StartTBasis(innType,outType,fcnameType,dnameType,
>		     leftname,rightname,eitherType)
> import PrettyPrinter(pshow)

\end{verbatim}
\section{Predefined instances}
For every functor we need {\tt out}, {\tt inn} and {\tt constructorName}.

Then {\tt either} needs {\tt Either} and {\tt uncurryn} needs {\tt ()}
and {\tt (,)}. (Easiest solved by including them in the prelude.)

These definitons produce lists of requests of other functions to be
defined (uncurry0,1,2 ...).
\subsection{Generating {\tt inn}}
{\tt innD = uncurryk1 C1 `either` uncurryk2 C2 `either` ... `either` uncurrykn Cn}

The definition requires {\tt either} and {\tt uncurryi} for some {\tt i}.
{\tt geninnD = uncurryk1 e1 `either` uncurryk2 e2 `either` ... `either` uncurrykn en}

A very similar function can be used to handle the {\tt \{ Ci -> ei
  \}} notation $\Rightarrow$ 

Generalize: Take as input a [(constructor replacement, arity)] = cres,
find the type in question from the result type of the first Ci (or
rather take that as an input), get the {\tt ces}. For all elem's in
{\tt ces}: Look up the constructor {\tt cres} - if its there take,
otherwise leave the elem from {\tt ces}.

The {\tt inn} function is recovered by supplying an empty list as {\tt
  cres}!

\begin{verbatim}

> inn_def :: VarID -> Struct -> (QType,([Req],[Eqn]))
> inn_def v s = geninn_def v [] s

> type CEList = [(ConID, Expr)]

> geninn_def :: VarID -> CEList -> Struct -> (QType,([Req],[Eqn]))
> geninn_def n cres (_,ss) = (innType,
>                             (reqs,[VarBind n (Just innType) [] 
>                                      (eitherfs (map constrs' ss))]))
>   where 
>     noPoly = qualify undefined
>     reqs   = map (`pair` noPoly) needed 
>     needed = (if length ss > 1 then ("either":) else id) 
>              (map (uncurryn.snd) ss)
>     constrs (c,n')  = funcurry n' c
>     constrs' = constrs 
>              . mapFst (\c->maybe (Con c) id (lookupEnv c cres))

> {-
> firstLow :: String -> String
> firstLow (c:cs) = toLower c:cs
> firstLow [] = error "BuiltinInstances.firstLow: impossible: empty string"
> -}

> eitherfs :: [Expr' t] -> Expr' t
> eitherfs = foldr1 eitherf
> eitherf :: Expr' t -> Expr' t -> Expr' t
> eitherf f g = Var "either" :@: f :@: g

\end{verbatim} 

\subsection{Generating {\tt out}} 
{\em insert parts of the licensiate thesis here.}
\begin{verbatim}

out_name x = case x of 
               C1 a11 .. a1k1  -> Left (a11,(...,a1k1)...)
               C2 a21 .. a2k2  -> Right (Left (a21,(...,a2k2)...))
               ...
               Cn an1 .. ankn  -> Right (.. (Right (Left (an1 ... )))..)

> out_def :: VarID -> Struct -> (QType,([Req],[Eqn]))
> out_def n (_,ss) = (outType,
>                     ([],[VarBind n (Just outType) [x] 
>                            (Case x (calts ss))]))
>   where 
>     x = Var "x"
>     calt (nam,num) = (apply nam vars,nestpairs vars)
>       where vars = map (Var . variablename) [0..num-1]
>     calts []  = error "BuiltinInstances.out_def: impossible: empty case"
>     calts [p] = [calt p]
>     calts (p:ps) = (mapSnd inl alt) : map (mapSnd inr) alts
>       where alt  = calt p
>             alts = calts ps
>     inl = (Con leftname :@:)
>     inr = (Con rightname :@:)
>     apply c vs = foldl1 (:@:) (Con c:vs)
>     nestpairs [p] = p
>     nestpairs (p:ps) = tup2 :@: p :@: nestpairs ps
>     nestpairs [] = Con (tupleConstructor 0)
>     tup2 = Con (tupleConstructor 2)

> either_def :: ([Req],[Eqn])
> either_def = ([],[--unDone (parse pEqn eithertext)
>                 VarBind "either" (Just eitherType) [f,g,x] eithercase])
>    where eithercase = Case x [(left a,f :@: a),(right b,g :@: b)]
>          [a,b,f,g,x] = map (Var.(:"")) "abfgx"
>          left  = (Con leftname :@:)
>          right = (Con rightname :@:)

\end{verbatim}
\subsection{Generating {\tt fconstructorName}}
\begin{verbatim}

datatypeName :: Regular d => d a -> String
datatypeName _ = D

fconstructorname :: Bifunctor f => f a b -> String
fconstructorname = (\_->C1) `either` ((\_->C2) `either` ... (\_->Cn))...)

> fcname_def :: VarID -> Struct -> (QType,([Req],[Eqn]))
> fcname_def n (_,ss) = (fcnameType,
>                        (reqs,
>                         [VarBind n Nothing []
>                            (eitherfs (map (constf . fst) ss))]))
>   where 
>     noPoly = [] :=> undefined
>     reqs   = map (`pair` noPoly) needed 
>     needed = if length ss > 1 then ["either"] else []

> constf :: ConID -> Expr' t
> constf = (Lambda WildCard) . Literal . StrLit

> dname_def :: VarID -> ConID -> (QType,([Req],[Eqn]))
> dname_def n d = (dnameType, (noReqs, [VarBind n Nothing [] (constf d)]))
>   where 
>     noReqs = []

\end{verbatim}
\subsection{Generating {\tt uncurry}}
It is important that the matching is done lazily.

unc0 :: a -> () -> a
unc1 :: (a->b) -> (a) -> b
unc2 :: (a->b->c) -> (a,b) -> c

uncn :: (a0->a1->...->an) -> (a0,(a1,...,an-1)...) -> an
{\tt uncurryn = uncurry . (uncurryn-1 .) }

\begin{verbatim}

> makeUncurry :: VarID -> Int -> ([Req], [Eqn])
> makeUncurry name m = case m of 
>      0 -> ([] ,[]) -- uncurry0 = const
>      1 -> ([] ,[]) -- uncurry1 = id
>      2 -> ([] ,[]) -- uncurry2 = uncurry
>      n -> ([req (n-1)],
>            unc n [f,p] ((funcurry (n-1) (f :@: p1)) :@: p2 ))
>    where [f,p]      = map Var ["f","p"]
>          [p1,p2]    = map ((:@:p).Var) ["fst","snd"]
>	   unc :: Int -> [Expr] -> Expr -> [Eqn]
>          unc n ps e = [VarBind name (Just (tunc n)) ps e]
>          tpairf a b = TCon (tupleConstructor 2) :@@: a :@@: b
>          req k      = (uncurryn k,tunc k)
>          tunc n     = qualify (func n -=> righttuple n -=> var n)
>          func n     = foldr (-=>) (var n) (map var [0..n-1])
>          righttuple 0= TCon (tupleConstructor 0)
>          righttuple 1= var 0
>          righttuple n= foldr1 tpairf (map var [0..n-1])
>	   var :: Int -> Type
>          var n = TVar ("a"++show n)

> funcurry :: Int -> Expr' a -> Expr' a
> funcurry 0 e = Var "const" :@: e
> funcurry 1 e = e
> funcurry 2 e = Var uncurryName :@: e
> funcurry n e = Var (uncurryn n) :@: e

> uncurryn :: Int -> String
> uncurryn n = uncurryName++show n

> uncurryName :: String
> uncurryName = "uncurry"
> uncurryNameLength :: Int
> uncurryNameLength = length uncurryName
> isUncurry :: String -> Bool
> isUncurry = not . null . parseUncurry
> parseUncurry :: String -> [Int]
> parseUncurry name | length name > uncurryNameLength && 
>                     maybeUncurry == uncurryName = [n]
>		    | otherwise = []
>   where (maybeUncurry,rest) = splitAt uncurryNameLength name
>	  n :: Int
>         n = read rest


\end{verbatim}





\section{Requests}
An element of the type Req is a request for a traversal of the named
definition with the given type.
\begin{verbatim}

> type Req = (VarID,TypeInfo)
> type TypeInfo = QType

\end{verbatim}
Two requests are the same if they are for the same identifier with the
same functors as arguments.
\begin{verbatim}

> eqReq :: Eq a => (a,QType) -> (a,QType) -> Bool
> eqReq (x,ps:=>_) (y,qs:=>_) = x==y && funs ps == funs qs
>   where funs preds = [ f | ("Poly",f:_) <- preds ]

\end{verbatim}

