> module FunctorNames(codeFunctors) where
> import MonadLibrary(Error(..),ErrorMonad(..),map0,map1,map2,accumseq)
> import MyPrelude(fMap)
> import Grammar(Type(..),Func,ConID,VarID,listConstructor)
> import PrettyPrinter(pshow)

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
>     s (TCon d)       = map0 ((codeTCon d)++)
>     s t@(TVar _)     = failEM ("FunctorNames.codeFunctor: uninstantiated functor variable " ++
>                               pshow t ++ " found as part of " ++ pshow f )

> codeType :: Type -> Error (String -> String)
> codeType (f :@@: t) = map2 (.) (codeType f) (codeType t)
> codeType (TCon d)  = map0 ((codeTCon d)++)
> codeType (TVar v)  = map0 ((codeTVar v)++)



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
>     p ( c :xs) | isDigit c = mapSnd TCon (decodeTCon (c:xs))
>                | otherwise = error "FunctorNames.decodeFunctor: bad functor encoding"
>     p ""        = error "FunctorNames.decodeFunctor: functor ended prematurely"
>     popp = p `op` p
>     plus (t,t') = TCon "+" :@@: t :@@: t'
>     prod (t,t') = TCon "*" :@@: t :@@: t'
>     appl (t,t') = TCon "@" :@@: t :@@: t'
>     op w w' xs = (zs,(y,z))
>       where (ys,y) = w  xs
>             (zs,z) = w' ys

> decodeTCon :: String -> (ConID,String)
> decodeTCon s | n > 0  = splitAt n text
>               | n == 0 = (listConstructor,text)
>               | True   = error "FunctorNames.decodeTCon: impossible: negative length"
>    where (num,text) = span isDigit s
>          n :: Int
>          n = if length num == 0 || (read num :: Float) > fromInt (maxBound :: Int)
>              then error ("decodeTCon: Bad number: '"++ num ++"'")
>              else read num

> decodeTVar :: String -> (VarID,String)
> decodeTVar s = splitAt n text
>    where (num,text) = span isDigit s
>          n :: Int
>          n = if length num == 0 || (read num :: Float) > fromInt (maxBound :: Int)
>              then error ("decodeTVar: Bad number: '"++ num ++"'")
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

> codeTCon :: ConID -> String
> codeTCon c | c == listConstructor = "0"
>             | otherwise            = show (length c) ++ c

> codeTVar :: VarID -> String
> codeTVar v = show (length v) ++ v

\end{verbatim}
