\section{Mutable variables}
\begin{verbatim}

#if defined(__HUGS__) || defined(__GLASGOW_HASKELL__)
> module StateFix(module ST,MutVar, newVar, readVar, writeVar, (===),(>>=!)) where

# ifdef __HUGS__
> import ST
# else
> import ST(ST,STRef,runST,newSTRef,readSTRef,writeSTRef)
# endif
#endif

#ifdef __HBC__
> module StateFix(module State,MutVar,(===)) where
> import State
#endif /* __HBC__ */

#ifdef __HBC__
> type MutVar s a = MutableVar s a

#else /* not __HBC__ */

#ifdef __OLD_HUGS__
> instance Functor (ST s) where
>   map f mx = mx >>= \x -> return (f x)
#else
> type MutVar s a = STRef s a

newVar :: a -> ST s (STRef s a)

> newVar  = newSTRef     
> readVar = readSTRef
> writeVar= writeSTRef

In earlier versions of Hugs, the three lines above were not needed.
#endif /* __OLD_HUGS__ */
#endif /* __HBC__ */

\end{verbatim}
Due to problems with combining overloading with the \verb|ST s|-monad
(in particular the construct \verb|runST|) we will use a special
symbol (the triple equality sign symbol, \verb|===|) for pointer
equality. 
\begin{verbatim}

> (===) :: MutVar s a -> MutVar s a -> Bool
#ifndef __HBC__
> (===) = (==) -- Pointer equality

> (>>=!) :: Monad m => m a -> (a -> m b) -> m b
> (>>=!) = (>>=) 
#else /* __HBC__ */
> (===) = sameVar -- Pointer equality
#endif /* __HBC__ */

#ifdef __GLASGOW_HASKELL__
> instance Functor (ST s) where
>   map f m = m >>= \ x -> return (f x)

#endif /* __GLASGOW_HASKELL__ */
\end{verbatim}
