\begin{verbatim}

#ifndef __GLASGOW_HASKELL__
> module StateArrayFix(ST,MutArr,newArr,readArr,writeArr) where
#else /* __GLASGOW_HASKELL__ */
> module StateArrayFix(module ST,MutArr,newArr,readArr,writeArr) where
#endif /* __GLASGOW_HASKELL__ */

#ifndef __HBC__

#ifdef __HUGS__
> import ST -- (ST)
#else
> import ST --(ST,runST)
#endif

#else /* __HBC__ */
> import State(ST)
> import MutArray
#endif /* __HBC__ */

#if defined(__HUGS__) || defined(__GLASGOW_HASKELL__)
# ifdef __OLD_HUGS__
> import STArray
# else
> type MutArr s a b = STArray s a b
# endif
#endif
#ifdef __HBC__
> type MutArr s a b = MutArray s a b
#endif /* __HBC__ */

#if defined(__HUGS__) || defined(__GLASGOW_HASKELL__)
# ifndef __OLD_HUGS__
> newArr       :: Ix a => (a,a) -> b -> ST s (MutArr s a b)
> readArr      :: Ix a => MutArr s a b -> a -> ST s b
> writeArr     :: Ix a => MutArr s a b -> a -> b -> ST s ()
> newArr   = newSTArray
> readArr  = readSTArray
> writeArr = writeSTArray
# endif
#endif
#ifdef __HBC__
> newArr       :: Ix a => (a,a) -> b -> ST s (MutArr s a b)
> readArr      :: Ix a => MutArr s a b -> a -> ST s b
> writeArr     :: Ix a => MutArr s a b -> a -> b -> ST s ()
> newArr   = newMutArray
> readArr  = readMutArray
> writeArr = writeMutArray
#endif /* __HBC__ */

\end{verbatim}
