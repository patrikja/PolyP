\chapter{Monad library}
\begin{verbatim}

> module MonadLibrary where
> import StateFix(ST,  (>>=!)) -- Hugs import ST
> import MyPrelude(pair,mapFst)

> infixl 9 <@
> infixl 9 <@-
> infixr 9 @@
> infixr 9 <*>
> infixr 1 <<

\end{verbatim}
\section{Monad based utilities}
\begin{verbatim}

> x <@ f = map f x
> x <@- e = map (\_->e) x

> join      :: Monad m => m (m a) -> m a
> join x     = x >>= id

> (@@) :: Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
> (@@) f g x        = g x >>= f

The original LHS: {\tt (f @@ g) x} proves not to be allowed by
Haskell 1.4. (Though it should be, in my opinion.)

> mfoldl           :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
> mfoldl f a []     = return a
> mfoldl f a (x:xs) = f a x >>= (\fax -> mfoldl f fax xs)

> mfoldr           :: Monad m => (a -> b -> m b) -> b -> [a] -> m b
> mfoldr f a []     = return a
> mfoldr f a (x:xs) = mfoldr f a xs >>= (\y -> f x y)

> mapl             :: Monad m => (a -> m b) -> ([a] -> m [b])
> mapl f []         = return [] 
> mapl f (x:xs)     = f x >>= \y -> mapl f xs >>= \ys -> return (y:ys) 

> mapr             :: Monad m => (a -> m b) -> ([a] -> m [b])
> mapr f []         = return []
> mapr f (x:xs)     = mapr f xs >>= \ys -> f x >>= \y-> return (y:ys) 

> mIf :: Monad m => m Bool -> m a -> m a -> m a
> mIf mb t f = mb >>= \b-> if b then t else f

> mguard :: MonadZero m => (a -> Bool) -> a -> m a
> mguard p x | p x = return x
>            | True= zero

\end{verbatim}
\section{IO and ST monads}
Hugs:
\begin{verbatim}
instance Functor (ST a) where
  map f sta = sta `thenST` \a -> return (f a)
\end{verbatim}
\section{Error monad}
\begin{verbatim}

> class Monad m => ErrorMonad m where
>   failEM :: String -> m a

> data Error a = Done a
>              | Err String
>              deriving Show

> instance Functor Error where
>   map f (Done x) = Done (f x)
>   map f (Err s)  = Err s

> instance Monad Error where
>     return         = Done
>     Done x  >>= f  = f x
>     Err msg >>= f  = Err msg

> instance ErrorMonad Error where
>   failEM = Err

> unDone (Done x) = x
> unDone (Err s) = error s

> type LErr a = (a,Error ())
> showLErr (x,err) = show x ++ handleError (\_->"") id err
> mapLErr = mapFst
> handleError f e = h
>   where h (Done x)   = f x
>         h (Err mess) = e mess

> instance ErrorMonad [] where
>   failEM msg = []

\end{verbatim}
\section{IOErr monad}
\begin{verbatim}

> newtype IOErr a = IOErr (IO (Error a)) 
>   {- in mapIOE, returnIOE, bindIOE, failIOE,
>         liftIOtoIOErr, dropIOErrtoIO, dropError -}
> 
> mapIOE :: (a -> b) -> (IOErr a) -> (IOErr b)
> mapIOE f (IOErr xs) = IOErr (xs <@ map f)
> 
> instance Functor IOErr where   
>   map = mapIOE
> 
> returnIOE :: a -> IOErr a 
> returnIOE x = IOErr (return (Done x))
> 
> bindIOE :: IOErr a -> (a -> IOErr b) -> IOErr b
> (IOErr xs) `bindIOE` f 
>   = IOErr (xs >>= \x ->
>            case x of
>              Done a  -> unIOErr (f a)
>              Err msg -> return (Err msg))
>     where unIOErr (IOErr x) = x
> 
> instance Monad IOErr where
>   return = returnIOE
>   (>>=)   = bindIOE
> 
> failIOE :: String -> IOErr a
> failIOE msg = IOErr (return (Err msg))
> 
> instance ErrorMonad IOErr where
>   failEM = failIOE
> 
> liftIOtoIOErr :: IO a -> IOErr a
> liftIOtoIOErr = IOErr . map Done
> 
> dropIOErrtoIO :: IOErr a -> IO a
> dropIOErrtoIO (IOErr m)
>     = m >>= \x -> 
>       case x of 
>         Done a  -> return a
>         Err msg -> putStrLn msg  >>
>                    error "drop!" --return undefined
> 
> dropError :: IOErr a -> IO b -> (a -> IO b) -> IO b
> dropError (IOErr m) failure success
>   = m >>= \x -> 
>     case x of 
>       Done a  -> success a
>       Err msg -> putStrLn msg >> failure

\end{verbatim}
\section{STErr monad}
\begin{verbatim}
 
> newtype STErr s a = STErr (ST s (Error a))
>  {- in mapSTE,returnSTE,bindSTE,failSTE,liftSTtoSTErr,
>        dropSTErrtoST,dropErrorST,convertSTErr -}
> 
> mapSTE :: (a -> b) -> (STErr s a) -> (STErr s b)
> mapSTE f (STErr xs) = STErr (xs <@ map f)
> 
> instance Functor (STErr s) where   
>   map = mapSTE
> 
> returnSTE :: a -> STErr s a 
> returnSTE x = STErr (return (Done x))
> 
> bindSTE :: STErr s a -> (a -> STErr s b) -> STErr s b
> (STErr xs) `bindSTE` f 
>   = STErr (xs >>=! \x ->  -- could be >>= also (>>=! slightly stricter)
>            case x of
>              Done a  -> unSTErr (f a)
>              Err msg -> return (Err msg))
>     where unSTErr (STErr x) = x
> 
> 
> instance Monad (STErr s) where
>   return = returnSTE
>   (>>=)  = bindSTE
> 
> failSTE :: String -> STErr s a
> failSTE msg = STErr (return (Err msg))
> 
> instance ErrorMonad (STErr s) where
>   failEM = failSTE
> 
> liftSTtoSTErr :: ST s a -> STErr s a
> liftSTtoSTErr = STErr . map Done
> 
> dropSTErrtoST :: STErr s a -> ST s a
> dropSTErrtoST (STErr m)
>     = m >>= \x -> 
>       case x of 
>         Done a  -> return a
>         Err msg -> error ("dropSTErrtoST: "++msg)
> 
> 
> dropErrorST :: STErr s a -> (String -> ST s b) -> (a -> ST s b) -> ST s b
> dropErrorST (STErr m) failure success
>   = m >>= \x -> 
>     case x of 
>       Done a  -> success a
>       Err msg -> failure msg
> 
> convertSTErr :: STErr s a -> ST s (Error a)
> convertSTErr (STErr x) = x

\end{verbatim}
\section{State monad}
\begin{verbatim}

> data State s a = ST (s -> (a,s))
> 
> instance Functor (State s) where
>   map f (ST st) = ST (\s -> let (x,s') = st s in (f x, s'))
> 
> instance Monad (State s) where
>   return x      = ST (\s -> (x,s))
>   ST m >>= f = ST (\s -> let (x,s') = m s
>                              ST f'  = f x
>                          in  f' s')
> 
> updateST f = ST (\s -> (s, f s))
> fetchST = updateST id
> 
> executeST :: s -> State s a -> a
> executeST s (ST m) = a where (a,_) = m s

\end{verbatim}
\section{STM monad}
\begin{verbatim}

> data StateM m s a = STM (s -> m (a,s)) 
> 
> instance Functor m => Functor (StateM m s) where
>   map f (STM xs) = STM (\s -> map (\(x,s') -> (f x, s'))
>                                   (xs s)
>                        )
> 
> instance Monad m => Monad (StateM m s) where
>   return x        = STM (\s -> return (x,s))
>   STM xs >>= f = STM (\s -> xs s >>= \(x, s') ->
>                                let STM f' = f x
>                                in f' s'
>                         )  
> instance MonadZero m => MonadZero (StateM m s) where
>   zero = STM (\s -> zero)
> 
> instance MonadPlus m => MonadPlus (StateM m s) where
>   (STM stm) ++ (STM stm') = STM (\s -> stm s ++ stm' s)
> 
> instance ErrorMonad m => ErrorMonad (StateM m s) where
>   failEM msg = STM (\s -> failEM msg)
> 
> updateSTM f = STM (\s -> return (s, f s))
> 
> fetchSTM :: Monad m => StateM m a a
> fetchSTM = updateSTM id
> 
> executeSTM :: Monad m => s -> StateM m s a -> m a
> executeSTM s (STM m) = m s >>=  \ ~(x,_) -> return x

\end{verbatim}
\section{Conversions between monads}
\begin{verbatim}

> mliftErr = liftSTtoSTErr
> 
> mliftSTM m = STM (\s -> map (`pair` s) m)

> mliftOut :: Functor m => m a -> OutputT b m a
> mliftOut ma = OT (map return ma)

\end{verbatim}
\section{Operations on all monads}
\begin{verbatim}

> foreach :: Monad m => [a] -> (a -> m b) -> m [b]
> foreach = flip mapl
> 
> loop :: Monad m => [a -> m a] -> a -> m a
> loop []     x = return x
> loop (f:fs) x = f x >>= \y -> 
>                 loop fs y

> (<*>) :: Monad m => m a -> m b -> m (a,b)
> (<*>) = liftop pair

> (<:*>) :: Monad m => m a -> m [a] -> m [a] 
> (<:*>) = liftop (:)

> (<<) :: Monad m => m a -> m b -> m a
> (<<) = liftop const

\end{verbatim}
\subsection{More monad utilities}
Some other functions used in the following. \verb|liftop| does for an
operator what \verb|map| (on a monad) does for a function. 
\begin{verbatim}

> liftop :: Monad m   => (a -> b -> c)  ->  m a -> m b -> m c
> map2   :: Monad m   => (a -> b -> c)  ->  m a -> m b -> m c
> map1   :: Functor m => (a -> b)       ->  m a -> m b 
> map0   :: Monad m   => a              ->  m a

\end{verbatim}
The order of the \verb|bind|s is important. (Swap them and the parser
will be a nice left recursive black hole;-)
\begin{verbatim}

> liftop f mp mq=mp >>= \p-> mq >>= \q-> return (f p q)
> map2 = liftop
> map1 = map
> map0 = return

\end{verbatim}
\section{Writer and output monads}
\begin{verbatim}

> data Writer a b = Writer ([a]->[a]) b
> instance Functor (Writer a) where
>   map f (Writer s x) = Writer s (f x)
> instance Monad (Writer a) where
>   return = Writer id
>   (Writer s a) >>= f = Writer (s.t) b
>               where Writer t b = f a

> write :: a -> Writer a ()
> write x = Writer (x:) ()

> data OutputT a m b = OT (m (Writer a b))

> unOT :: (OutputT a m b) -> m (Writer a b)
> unOT (OT m) = m

> instance Functor m => Functor (OutputT a m) where
>   map f (OT mx) = OT (map (map f) mx)

> instance (Functor m ,Monad m) => Monad (OutputT a m) where
>   return x   = OT (return (return x))
>   (OT m) >>= f = OT ((map join . join . map f') m)
>        where f' = swap . map (unOT . f)
>              swap (Writer s ma) = map (Writer s) ma

> output :: Monad m => a -> OutputT a m ()
> output x = OT (return (write x))

> runOutput' :: Functor m => OutputT a m b -> m ([a] -> [a],b)
> runOutput' (OT m) = map (\(Writer s a) -> (s,a)) m

> runOutput :: Functor m => [a] -> OutputT a m b -> m ([a],b)
> runOutput l o = map (\(s,x)->(s l,x)) (runOutput' o)

\end{verbatim}

