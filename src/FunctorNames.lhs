> module FunctorNames(codeFunctors) where
> import MonadLibrary(Error(..),ErrorMonad(..),map0,map1,map2,accumseq)
> import MyPrelude(fMap)
> import Grammar(Type(..),Func,ConID,VarID,
>                listConstructor,functionConstructor,isTupleCon)
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
>     s (TCon ">")     = map0 ('F':)
>     s (TCon "@")     = map0 ('A':)
>     s (TCon d)       = map0 ((codeTCon d)++)
>     s t@(TVar _)     = failEM ("FunctorNames.codeFunctor: uninstantiated functor variable " ++
>                               pshow t ++ " found as part of " ++ pshow f )

> codeType :: Type -> Error (String -> String)
> codeType (f :@@: t) = map1 (('a':).) (map2 (.) (codeType f) (codeType t))
> codeType (TCon d)   = map0 (('C':).((codeTCon d)++))
> codeType (TVar v)   = map0 (('V':).((codeTVar v)++))

> {- 
> decodeType :: String -> (String, Func)
> decodeType s = p s
>   where p "" = error "FunctorNames.decodeType: type encoding ended prematurely"
>         p ('a':xs) = mapSnd (uncurry (:@@:)) ((p >*> p) xs)
>         p ('C':xs) = decodeTCon xs
>         p ('V':xs) = decodeTVar xs

> decodeFunctor :: String -> Func
> decodeFunctor s = snd (p s)
>   where
>     p ('e':xs)  = (xs,TCon "Empty")
>     p ('p':xs)  = (xs,TCon "Par")
>     p ('r':xs)  = (xs,TCon "Rec")
>     p ('m':xs)  = (xs,TCon "Mu")
>     p ('f':xs)  = (xs,TCon "FunctorOf")
>     p ('c':xs)  = mapSnd (TCon "Const" :@@:) (decodeType xs)
>     p ('S':xs)  = mapSnd plus (popp xs)
>     p ('P':xs)  = mapSnd prod (popp xs)
>     p ('F':xs)  = mapSnd fun  (popp xs)
>     p ('A':xs)  = mapSnd appl (popp xs)
>     p ( c :xs) | isDigit c = mapSnd TCon (decodeTCon (c:xs))
>                | otherwise = error "FunctorNames.decodeFunctor: bad functor encoding"
>     p ""        = error "FunctorNames.decodeFunctor: functor encoding ended prematurely"
>     plus (t,t') = TCon "+" :@@: t :@@: t'
>     prod (t,t') = TCon "*" :@@: t :@@: t'
>     fun  (t,t') = TCon ">" :@@: t :@@: t'
>     appl (t,t') = TCon "@" :@@: t :@@: t'
>     pthenp = p >*> p

> -- Operator for sequencing simple parsers
> (>*>) :: SimpleParser a -> SimpleParser b -> SimpleParser (a,b)
> (>*>) w w' xs = (zs,(y,z))
>   where (ys,y) = w  xs
>         (zs,z) = w' ys

> decodeTCon :: String -> (ConID,String)
> decodeTCon s | n > 0  = splitAt n text
>               | n == 0 = (listConstructor,text)
>               | True   = error "FunctorNames.decodeTCon: impossible: negative length"
>    where (num,text) = span isDigit s
>          n :: Int
>          n = if length num == 0 || (read num :: Float) > fromIntegral (maxBound :: Int)
>              then error ("decodeTCon: Bad number: '"++ num ++"'")
>              else read num

> decodeTVar :: String -> (VarID,String)
> decodeTVar s = splitAt n text
>    where (num,text) = span isDigit s
>          n :: Int
>          n = if length num == 0 || (read num :: Float) > fromIntegral (maxBound :: Int)
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
> codeTCon c | c == listConstructor     = codeString ""
>            | c == functionConstructor = codeString "_"
>            | isTupleCon c = codeString ('_':show tuplesize)
>            | otherwise    = codeString c
>   where tuplesize :: Int
>         tuplesize = let n = length c - 1 in if n==1 then 0 else n

> codeTVar :: VarID -> String
> codeTVar = codeString

> codeString :: String -> String
> codeString s = show (length s) ++ s

\end{verbatim}
