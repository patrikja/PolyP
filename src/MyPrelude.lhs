\chapter{Prelude-like functions}
\begin{verbatim}

> module MyPrelude(module MyPrelude,trace) where

> import NonStdTrace(trace)
> import List(nubBy)

\end{verbatim}
\section{Compatibility issues}

In Haskell 98 what was earlier \texttt{map} has been split into two 
values: one class member \texttt{fmap} and one list map \texttt{map}.
To achieve backward compatibility we define \texttt{fmap} even for 
earlier Haskell versions.

#ifndef __Haskell98__

> fmap :: Functor f => (a->b) -> f a -> f b
> fmap = map

#endif

\section{Some list utilities}

\begin{verbatim}

> flatMap :: (a -> [b]) -> [a] -> [b]
> without :: Eq a => [a] -> [a] -> [a]
> withoutBy:: (a -> a -> Bool) -> [a] -> [a] -> [a]
> splitUp :: [a -> Bool] -> [a] -> [[a]]

 nubBy   :: (a->a->Bool) -> [a] -> [a]  -- remove duplicates from list

> unique  :: Eq a => [a] -> [a]
> combineUniqueBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]

\end{verbatim}
Given an equality function and two lists qs and xs where the first
list contains no duplicates, {\tt combineUniqueBy} gives a sublist ys
of xs such that qs++ys contains no duplicates.

The function {\tt flatMap} maps a function (returning a list
instead of just one element) over a list and concatenates the 
resulting lists afterwards.

The function {\tt without} removes all occurrences of elements in the
second list from the first list; 
e.g. {\tt [1,2,3,3,4] `without` [1,3] = [2,4]}

The function {\tt splitUp} splits up a list according to a list of 
predicates. The resulting list of lists has a length that is one
more than the list of predicates. The last list is used to store
all elements that don't satisfy any of the predicates;
e.g. {\tt splitUp [(>3), (<2)] [1..5] = [[4,5], [1], [2,3]]}.

\subsection{Maybe}
The {\tt Maybe} data type is used whenever a function is not certain
to return a value (for example in environment lookups). \verb|Maybe|
is a functor and a monad with zero and plus.  In Haskell 1.3 this type
and most operations are already in the prelude.
\begin{verbatim}
 data Maybe a = Nothing  | Just a deriving Show
 maybe :: b -> (a -> b) -> Maybe a -> b 

> unJust :: Maybe a -> a

\end{verbatim}
\subsection{Debugging}
For debugging \verb|trace| can be very useful - it prints its first
string argument as a side effect when it is reduced. It is the identity
function on its second argument. \verb|debug| shows it's argument and
returns it.

In H1.3 (hbc) we include the trace function from the module NonStdTrace.
\begin{verbatim}

> debug :: Show a => a -> a

#ifdef __DEBUG__
> maytrace = trace  -- debug info on
#else
> maytrace _ = id -- debug info off
#endif

\end{verbatim}
\subsection{Pairs}
\begin{verbatim}

> mapFst :: (a -> b) -> (a, c) -> (b, c)
> mapSnd :: (a -> b) -> (c, a) -> (c, b)
> pair   :: a -> b -> (a,b)
> swap   :: (a, b) -> (b, a)

\end{verbatim}
\subsection{Misc.}
\begin{verbatim}

> variablename :: Int -> String

\end{verbatim}
\section{Implementation}
\begin{verbatim}

> flatMap f = concat . map f

> xs `without` ys = filter (\x -> not (elem x ys)) xs
> withoutBy eq xs ys = filter (\x -> not (myelem x ys)) xs
>     where myelem = any . eq

 nubBy eq = nub
   where nub []     = []
         nub (x:xs) = x : nub (filter (not.(eq x)) xs)

> splitUp preds []     = replicate (length preds + 1) []
> splitUp preds (x:xs) = let lists = splitUp preds xs 
>                        in try x preds lists
>   where try y []       [lastList]   = [(y:lastList)]
>         try y (pr:prs) (list:lists) 
>           | pr y      = (y:list) : lists
>           | otherwise = list:(try y prs lists)
>         try _ _  []      = error "MyPrelude.lhs: splitUp: impossible: too few lists"
>         try _ [] (_:_:_) = error "MyPrelude.lhs: splitUp: impossible: too many lists"

> debug x = trace (show x) x

> mapFst f (a,b) = (f a,b)
> mapSnd f (a,b) = (a,f b)

> pair x y = (x,y)
> swap (x,y) = (y,x)

> variablename n | n<26 = [num2chr n]
>   where num2chr n = toEnum (fromEnum 'a' + n )
> variablename n = variablename (n `div` 26 - 1) ++ 
>                  variablename (n `mod` 26) 

> unJust (Just x) = x
> unJust Nothing  = error "unJust!"

> unique xs = unique' xs [] 
> unique' [] = id
> unique' (x:xs) = (x:).(unique' [y|y<-xs,y/=x])

> combineUniqueBy eq = cu
>   where cu qs [] = []
>         cu qs (x:xs) | x `elemByeq` qs = cu qs xs
>                      | otherwise   = x:cu (x:qs) xs
>         elemByeq = any . eq

\end{verbatim}
