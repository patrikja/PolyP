\chapter{Functors and predefined instances}
\begin{verbatim}

> module Functorize(inn_def,out_def,either_def,fcname_def,
>                   Struct,makeFunctorStruct,Req,eqReq,codeFunctors) where
> -- import Char(isDigit)
> import Env(lookupEnv)
> import Grammar(Eqn'(..),Expr'(..),Expr,Type(..),Qualified(..),Literal(..),
>                Eqn,Func,QType, ConID,VarID,spineWalkType,
>                tupleConstructor,listConstructor,isTupleCon)
> import Folding(cataType)
> import MonadLibrary(Error(..),ErrorMonad(..),map0,map1,map2,accumseq)
> import MyPrelude(mapFst,mapSnd,pair,variablename,fMap)
> import StartTBasis(innType,outType,fcnameType,leftname,rightname,eitherType)
> import PrettyPrinter(pshow)

\end{verbatim}
\section{Extracting functors from {\tt data}-definitions} 
For every regular datatype we need the functor that represents its
recursive structure: {\tt D} == {\tt Mu fD}.

Preliminary version: Works for exactly one type parameter and not with
any structure on the right hand side.

The type {\tt Struct} represents the top level structure of the
datatype definition: 
\begin{verbatim}

> {-
> makeFunctor :: Eqn -> Func
> makeFunctor = snd . makeFunctorStruct

> mapPList :: (a->b) -> PList a -> PList b
> mapPList f (a,as) = (f a,map f as)
> -}

> type PList a = (a,[a])
> type Struct = PList (ConID,Int)

\end{verbatim}

*** Triples and beyond should probably be translated to nested pairs
in inn, out, or forbidden below.

\begin{verbatim}

> makeFunctorStruct :: Eqn -> (Struct,Func)
> makeFunctorStruct (DataDef def [_] alts _)
>   = ( ((def,1),map (mapSnd length) alts) , convAlts def alts)
> makeFunctorStruct _ = error "Functorize.makeFunctorStruct: impossible: not a DataDef"

> convAlts :: ConID -> [(ConID, [Type])] -> Func
> convAlts def alts = foldr1 plus (map (convProd def . snd) alts)
>   where x `plus` y = TCon "+" :@@: x :@@: y

> convProd :: ConID -> [Type] -> Func
> convProd _   [] = TCon "Empty" 
> convProd def ts = foldr1 prodFunctor (map (convType def) ts)

> prodFunctor :: Func -> Func -> Func
> prodFunctor f g = TCon "*" :@@: f :@@: g

> convType :: ConID -> Type -> Func
> convType _   (TVar _) = TCon "Par" -- indexed if multiple params
> convType _   t | isConstantType t = TCon "Const" :@@: t
> convType def (TCon con :@@: TVar _)
>   | con == def = TCon "Rec"
> convType def t | isTupleCon tup   = convProd def ts
>      where (TCon tup:ts) = spineWalkType t
> convType def (TCon con :@@: t)    = 
>    TCon "@" :@@: TCon con :@@: convType def t
> convType def _ = error ("Functorize.convType: Can't calculate FunctorOf "++ def ++" as the type is not regular enough.")

> isConstantType :: Type -> Bool
> isConstantType = null . typeVars

> typeVars :: Type -> [VarID]
> typeVars = cataType ((:[]),const [],(++))

\end{verbatim}
Far too many bad functors get through this a the moment.

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
  \}} notation $\Rightarrow$ Generalize: Take as input a [(constructor
replacement, arity)] = cres, find the type in question from the result
type of the first Ci (or rather take that as an input), get the {\tt
  ces}. For all elem's in {\tt ces}: Look up the constructor {\tt
  cres} - if its there take, otherwise leave the elem from {\tt ces}.

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
>     noPoly = [] :=> undefined
>     reqs   = map (`pair` noPoly) needed 
>     needed = (if length ss > 1 then ("either":) else id) 
>              (map (uncurryn.snd) ss)
>     constrs (c,n')  = funcurry n' :@: c
>     constrs' = constrs 
>              . mapFst (\c->maybe (Con c) id (lookupEnv c cres))

 funcurry = Var . uncurryn -- hbc takes it but Hugs doesn't !

> funcurry :: Int -> Expr' a
> funcurry n = Var (uncurryn n)
> uncurryn :: Int -> String
> uncurryn n = "uncurry"++show n

> {-
> firstLow :: String -> String
> firstLow (c:cs) = toLower c:cs
> firstLow [] = error "Functorize.firstLow: impossible: empty string"
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
>     calts []  = error "Functorize.out_def: impossible: empty case"
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
>     constf :: ConID -> Expr' t
>     constf = (Lambda WildCard) . Literal . StrLit

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

% ----------------------------------------------------------------
\section{Functor names}
To identify a functor in a concise way, we use a coding of functors as
strings of characters. 
%
We use prefix format and translate the operators as follows: 
%
The structures {\tt f+g}, {\tt f*g} and {\tt d@g} are coded by the
first letters in Sum, Product and Application followed by the coded
versions of their children. 
%
The base cases {\tt Empty}, {\tt Par}, {\tt Rec} and {\tt Const t} are
coded by their first letter but in lower case.  
%
(This will have to be improved in the {\tt Const t} case when t is not
just a type variable.  We simply need a pair of functions {\tt
  codeType} and {\tt decodeType}.)  
%
There is one special case: {\tt FunctorOf []} is coded as {\tt F0}
instead of {\tt F[]} to make it a legal Haskell identifier(-suffix).
\begin{verbatim}

> codeFunctors :: [Func] -> Error String
> codeFunctors = fMap concat . accumseq . map (fMap ('_':) . codeFunctor)

> codeFunctor :: Func -> Error String
> codeFunctor f = fMap ($ "") (s f)
>   where 
>     s :: Func -> Error (String -> String)
>     s (TCon "Const" :@@: c)   = map1 (('c':).) (codeType c)
>     s (g :@@: t)     = map2 (.) (s g) (s t)
>     s (TCon "Empty") = map0 ('e':)
>     s (TCon "Par")   = map0 ('p':)    
>     s (TCon "Rec")   = map0 ('r':)    
>     s (TCon "Mu")    = map0 ('m':)
>     s (TCon "FunctorOf")= map0 ('f':)
>     s (TCon "+")     = map0 ('S':)
>     s (TCon "*")     = map0 ('P':)
>     s (TCon "@")     = map0 ('A':)
>     s (TCon d)       = map0 ((codeTyCon d)++)
>     s t@(TVar _)     = failEM ("Functorize.codeFunctor: uninstantiated functor variable " ++
>                               pshow t ++ " found as part of " ++ pshow f )

> codeType :: Type -> Error (String -> String)
> codeType _ = Done id

> {- 
> decodeType :: String -> (String, Func)
> decodeType xs = (xs,TCon "Const" :@@: TVar "t")

> decodeFunctor :: String -> Func
> decodeFunctor s = snd (p s)
>   where
>     p ('e':xs)  = (xs,TCon "Empty")
>     p ('p':xs)  = (xs,TCon "Par")
>     p ('r':xs)  = (xs,TCon "Rec")
>     p ('m':xs)  = (xs,TCon "Mu")
>     p ('f':xs)  = (xs,TCon "FunctorOf")
>     p ('c':xs)  = decodeType xs
>     p ('S':xs)  = mapSnd plus (popp xs)
>     p ('P':xs)  = mapSnd prod (popp xs)
>     p ('A':xs)  = mapSnd appl (popp xs)
>     p ( c :xs) | isDigit c = mapSnd TCon (decodeTyCon (c:xs))
>                | otherwise = error "Functorize.decodeFunctor: bad functor encoding"
>     p ""        = error "Functorize.decodeFunctor: functor ended prematurely"
>     popp = p `op` p
>     plus (t,t') = TCon "+" :@@: t :@@: t'
>     prod (t,t') = TCon "*" :@@: t :@@: t'
>     appl (t,t') = TCon "@" :@@: t :@@: t'
>     op w w' xs = (zs,(y,z))
>       where (ys,y) = w  xs
>             (zs,z) = w' ys

> decodeTyCon :: String -> (ConID,String)
> decodeTyCon s | n > 0  = splitAt n text
>               | n == 0 = (listConstructor,text)
>               | True   = error "Functorize.decodeTyCon: impossible: negative length"
>    where (num,text) = span isDigit s
>          n :: Int
>          n = if length num == 0 || (read num :: Float) > fromInt (maxBound :: Int)
>              then error ("decodeTyCon: Bad number: '"++ num ++"'")
>              else read num

\end{verbatim}
Just a test expression --- not used.
\begin{verbatim}

> testfunctors :: [Func]
> testfunctors = map decodeFunctor [fList,fTree,fRoseTree,
>                                   fVarTree,fVNumber,fBoolAlg]
>      where fList     = "SePpr"
>            fTree     = "SpPrr"
>            fRoseTree = "PpA"++fList++"r"
>            fVarTree  = "Sc"++fTree
>            fVNumber  = "SeSrSPrrPrr"
>            fBoolAlg  = "Se"++fVNumber
> -}

> codeTyCon :: ConID -> String
> codeTyCon c | c == listConstructor = "0"
>             | otherwise            = show (length c) ++ c

\end{verbatim}
