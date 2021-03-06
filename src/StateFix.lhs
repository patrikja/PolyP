\section{Mutable variables}

This module serves as a glue between the rest of the PolyP
implementation and the varying implementations of the ST-monad.  As
the ST-monad is a Haskell extension, the interface has not yet
settled.

The differences are of two kinds:
\begin{itemize}
\item Different names of the new functions (easy to fix):\\
  The names used in the rest of PolyP are those that were earlier used
  in hugs and still are used in hbc [980428].
  
\item Different ways of extending the type system to deal with
  \texttt{runST} (harder to fix):\\
  In hugs, \texttt{runST} is a keyword and not a function, which means
  that it can not be renamed and it can not even be mentioned in the
  import or export lists. In hbc, a special constructor \texttt{RunST}
  is used in concert with (the normal function) \texttt{runST}. And in
  ghc \texttt{runST} is a normal function. (Provided the flag
  \texttt{-fglasgow-exts} is used when compiling.)
\end{itemize}

\begin{verbatim}

#if defined(__HUGS__) || defined(__GLASGOW_HASKELL__)
> module StateFix(MutVar,newVar,readVar,writeVar,(===),
>                 module ST,
>                 MutArr,newArr,readArr,writeArr) where
#if __GLASGOW_HASKELL__ > 600
> import Control.Monad.ST as ST
> import Data.STRef       as ST
> import Data.Array.ST
#else
> import ST -- (ST,STRef,runST,newSTRef,readSTRef,writeSTRef)
#endif
#endif
#ifdef __HBC__
> module StateFix(module State,module MutArray,MutVar,(===),
>                 MutArr,newArr,readArr,writeArr) where
> import State
#endif

In Haskell 98 the class Ix is in a separate module instead of in the
  prelude.  (The change was discovered when moving from ghc-4.02 to
  ghc-4.03 thus the prelude in ghc-4.02 is wrong.)

#if defined(__Haskell98__)
> import Ix(Ix)
#endif



#ifdef __OLD_HUGS__
> import STArray
#else
# if defined(__HUGS__) || defined(__GLASGOW_HASKELL__)
> type MutArr s a b = STArray s a b
> type MutVar s a = STRef s a

> newVar   ::               a -> ST s (MutVar s a)
> readVar  :: MutVar a b ->      ST a b
> writeVar :: MutVar a b -> b -> ST a ()

> newVar  = newSTRef     
> readVar = readSTRef
> writeVar= writeSTRef
# endif 
# ifdef __HBC__
> import MutArray
> type MutArr s a b = MutArray s a b
> type MutVar s a   = MutableVar s a
# endif
#endif

\end{verbatim}
Due to problems with combining overloading with the \verb|ST s|-monad
(in particular the construct \verb|runST|) we will use a special
symbol (the triple equality sign symbol, \verb|===|) for pointer
equality. 
\begin{verbatim}

> (===) :: MutVar s a -> MutVar s a -> Bool
#ifdef __HBC__
> (===) = sameVar -- Pointer equality
#else 
> (===) = (==)    -- Pointer equality
#endif 

#ifndef __Haskell98__
# if (defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 401) || defined(__OLD_HUGS__)
> instance Functor (ST s) where
>   map f m = m >>= \ x -> return (f x)
# endif 
#endif

\end{verbatim}
\section{Mutable arrays}
\begin{verbatim}

#ifndef __OLD_HUGS__
> newArr       :: Ix a => (a,a) -> b -> ST s (MutArr s a b)
> readArr      :: Ix a => MutArr s a b -> a -> ST s b
> writeArr     :: Ix a => MutArr s a b -> a -> b -> ST s ()
# if defined(__HUGS__) || defined(__GLASGOW_HASKELL__)
#  if __GLASGOW_HASKELL__ > 600 
> newArr   = newArray
> readArr  = readArray
> writeArr = writeArray
#  else
> newArr   = newSTArray
> readArr  = readSTArray
> writeArr = writeSTArray
#  endif
# endif
# ifdef __HBC__
> newArr   = newMutArray
> readArr  = readMutArray
> writeArr = writeMutArray
# endif 
#endif 

\end{verbatim}
