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

#ifndef __HBC__
> type MutArr s a b = STArray s a b
#else /* __HBC__ */
> type MutArr s a b = MutArray s a b
#endif /* __HBC__ */

> newArr       :: Ix a => (a,a) -> b -> ST s (MutArr s a b)
> readArr      :: Ix a => MutArr s a b -> a -> ST s b
> writeArr     :: Ix a => MutArr s a b -> a -> b -> ST s ()
#ifndef __HBC__
> newArr   = newSTArray
> readArr  = readSTArray
> writeArr = writeSTArray
#else /* __HBC__ */
> newArr   = newMutArray
> readArr  = readMutArray
> writeArr = writeMutArray
#endif /* __HBC__ */

\end{verbatim}
