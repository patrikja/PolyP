\chapter{Monad library}
\begin{verbatim}

> module MonadLibrary(module StateFix,
>                     State     ,updateST ,fetchST ,executeST ,
>                     StateM(..),updateSTM,fetchSTM,executeSTM,mliftSTM,
>                     (<@),(<@-),(<*>),(<:*>),(<<),(@@),(<|),(+++),mIf,
>                     applyM,applyM2,
>                     Error(..),unDone,noErrorFilter,errorToList,
>                     LErr,unLErr,mapLErr,showLErr,handleError,
>                     STErr,mliftErr,convertSTErr,ErrorMonad(failEM),
>		      changeError,
>                     OutputT,output,runOutput,mliftOut,
>                     mapl,foreach,liftop,map0,map1,map2,mfoldl,mfoldr,
>		      mZero,mplus,
>		      accumseq,accumseq_,mguard) where
> import StateFix
> import MyPrelude(pair,mapFst,fMap)

#ifdef __Haskell98__
> import Monad(MonadPlus(..),join)
#else
> import Monad(join)
#endif
#ifdef __Haskell98__
#define MONADZERONAME MonadPlus
#define MONADPLUSOP `mplus`
#else
#define MONADZERONAME MonadZero
#define MONADPLUSOP ++
#endif

> infixl 9 <@
> infixl 9 <@-
> infixr 9 @@
> infixr 9 <*>
> infixl 7 <|
> infixr 5 +++
> infixr 1 <<

> mZero :: MONADZERONAME m => m a
#ifdef __Haskell98__
> mZero = mzero
#else
> mZero = zero
> mplus :: MonadPlus m => m a -> m a -> m a
> mplus = (++)
#endif

> mguard :: MONADZERONAME m => Bool -> m ()
> mguard b = if b then return () else mZero

> (+++) :: MonadPlus m => m a -> m a -> m a
> (+++) = mplus

\end{verbatim}
\section{Monad based utilities}

Function \texttt{accumseq} is called \texttt{sequence} in Haskell 98
but earlier \textt{accumulate}.

\begin{verbatim}

> accumseq :: Monad m => [m a] -> m [a]
> accumseq = mapM id
> accumseq_ :: Monad m => [m a] -> m ()
> accumseq_ = foldr (>>) (return ())

> (<@) :: Functor f => f a -> (a -> b) -> f b
> x <@ f  = fMap f x
> (<@-) :: Functor f => f a -> b -> f b
> x <@- e = fMap (\_->e) x

join      :: Monad m => m (m a) -> m a
join x     = x >>= id

#ifdef __Haskell98__
Removed from the prelude:

> applyM :: Monad m => (a -> m b) -> m a -> m b
> applyM = flip (>>=)

#endif

> applyM2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
> applyM2 f ma mb = ma >>= \a -> mb >>= \b -> f a b
> --applyM2 f ma mb = ma >>= (mb >>=) . f

> (@@) :: Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
> (@@) f g x        = g x >>= f

The original LHS: {\tt (f @@ g) x} proves not to be allowed by
Haskell 1.4. (Though it should be, in my opinion.) It is OK in Haskell 98.

> mfoldl           :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
> mfoldl _ a []     = return a
> mfoldl f a (x:xs) = f a x >>= (\fax -> mfoldl f fax xs)

> mfoldr           :: Monad m => (a -> b -> m b) -> b -> [a] -> m b
> mfoldr _ a []     = return a
> mfoldr f a (x:xs) = mfoldr f a xs >>= (\y -> f x y)

> mapl             :: Monad m => (a -> m b) -> ([a] -> m [b])
> mapl _ []         = return [] 
> mapl f (x:xs)     = f x >>= \y -> mapl f xs >>= \ys -> return (y:ys) 

> mapr             :: Monad m => (a -> m b) -> ([a] -> m [b])
> mapr _ []         = return []
> mapr f (x:xs)     = mapr f xs >>= \ys -> f x >>= \y-> return (y:ys) 

> mIf :: Monad m => m Bool -> m a -> m a -> m a
> mIf mb t f = mb >>= \b-> if b then t else f

> (<|) :: MONADZERONAME m => m a -> (a -> Bool) -> m a
> m <| p = m >>= \x -> if p x then return x else mZero

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
>              deriving (Show, Eq)


> instance Functor Error where
>   __FMAPNAME__ f (Done x) = Done (f x)
>   __FMAPNAME__ _ (Err s)  = Err s

> instance Monad Error where
>     return         = Done
>     Done x  >>= f  = f x
>     Err msg >>= _  = Err msg

> instance ErrorMonad Error where
>   failEM = Err

> unDone :: Error a -> a
> unDone (Done x) = x
> unDone (Err s) = error s

> type LErr a = (a,Error ())

> showLErr :: Show a => LErr a -> String
> showLErr (x,err) = show x ++ handleError id (fMap (\_->"") err)

> mapLErr :: (a->b) -> LErr a -> LErr b
> mapLErr = mapFst

> unLErr :: LErr a -> a
> unLErr = handleLErr (error.("MonadLibrary.handleLErr:"++))

> handleLErr :: (String -> a) -> LErr a -> a
> handleLErr _   (x,Done ()) = x
> handleLErr def (_,Err msg) = def msg

> handleError :: (String -> a) -> Error a -> a
> handleError d = h
>   where h (Done x)   = x
>         h (Err mess) = d mess

> errorToList :: Error a -> [a]
> errorToList (Err msg) = []
> errorToList (Done x)  = [x]

> noErrorFilter :: [Error a] -> [a]
> noErrorFilter = concatMap errorToList

> instance ErrorMonad [] where
>   failEM _ = []

\end{verbatim}
\section{IOErr monad}
\begin{verbatim}

> newtype IOErr a = IOErr (IO (Error a)) 
>   {- in mapIOE, returnIOE, bindIOE, failIOE,
>         liftIOtoIOErr, dropIOErrtoIO, dropError -}
> 
> mapIOE :: (a -> b) -> (IOErr a) -> (IOErr b)
> mapIOE f (IOErr xs) = IOErr (xs <@ fMap f)
> 
> instance Functor IOErr where   
>   __FMAPNAME__ = mapIOE
> 
> returnIOE :: a -> IOErr a 
> returnIOE x = IOErr (return (Done x))
> 
> bindIOE :: IOErr a -> (a -> IOErr b) -> IOErr b
> (IOErr xs) `bindIOE` f 
>   = IOErr (xs >>= \x ->
>            case x of
>              Done a  -> unIOErr (f a)
>              Err msg -> return (Err msg)
>           )
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
> {-
> liftIOtoIOErr :: IO a -> IOErr a
> liftIOtoIOErr = IOErr . fMap Done
> 
> dropIOErrtoIO :: IOErr a -> IO a
> dropIOErrtoIO (IOErr m)
>     = m >>= \x -> 
>       case x of 
>         Done a  -> return a
>         Err msg -> putErrStrLn msg  >>
>                    error "drop!" --return undefined
> 
> dropError :: IOErr a -> IO b -> (a -> IO b) -> IO b
> dropError (IOErr m) failure success
>   = m >>= \x -> 
>     case x of 
>       Done a  -> success a
>       Err msg -> putErrStrLn msg >> failure
> -}

\end{verbatim}
\section{STErr monad}
\begin{verbatim}
 
> newtype STErr s a = STErr (ST s (Error a))
>  {- in mapSTE,returnSTE,bindSTE,failSTE,liftSTtoSTErr,
>        dropSTErrtoST,dropErrorST,convertSTErr -}
> 
> mapSTE :: (a -> b) -> (STErr s a) -> (STErr s b)
> mapSTE f (STErr xs) = STErr (xs <@ fMap f)
> 
> instance Functor (STErr s) where   
>   __FMAPNAME__ = mapSTE
> 
> returnSTE :: a -> STErr s a 
> returnSTE x = STErr (return (Done x))
> 
> bindSTE :: STErr s a -> (a -> STErr s b) -> STErr s b
> (STErr xs) `bindSTE` f 
>   = STErr (xs >>= \x ->
>            case x of
>              Done a  -> convertSTErr (f a)
>              Err msg -> return (Err msg)
>           )
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
> changeError :: (String -> String) -> STErr s a -> STErr s a
> changeError f (STErr m) = STErr $ m >>= \e-> case e of
>				Done x -> return (Done x)
>				Err msg-> return (Err (f msg))
> 
> liftSTtoSTErr :: ST s a -> STErr s a
> liftSTtoSTErr = STErr . fMap Done
> 
> mzeroSTErr = STErr (return (Err "mzero:"))
>
> instance MONADZERONAME (STErr s) where
#ifdef __Haskell98__
>   mzero  = mzeroSTErr
#else
>   zero = mzeroSTErr
#endif

#ifndef __Haskell98__
> instance MonadPlus (STErr s) where
#endif
>   a MONADPLUSOP b = STErr $ 
>     convertSTErr a >>= \x -> case x of
>   	Done y -> return (Done y)
>   	Err _  -> convertSTErr b

> {- 
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
> -}
> 
> convertSTErr :: STErr s a -> ST s (Error a)
> convertSTErr (STErr x) = x

\end{verbatim}
\section{State monad}
\begin{verbatim}

> data State s a = ST (s -> (a,s))
> 
> instance Functor (State s) where
>   __FMAPNAME__ f (ST st) = 
>     ST (\s -> let {(x,s') = st s} in (f x, s'))
> 
> instance Monad (State s) where
>   return x   = ST (\s -> (x,s))
>   ST m >>= f = ST (\s -> let (x,s') = m s
>                              ST f'  = f x
>                          in  f' s')
> 
> updateST :: (s->s) -> State s s
> updateST f = ST (\s -> (s, f s))
> fetchST :: State s s
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
>   __FMAPNAME__ f (STM xs) = 
>     STM (\s -> fMap (\(x,s') -> (f x, s')) 
>                     (xs s)                                
>         )                                 
> instance Monad m => Monad (StateM m s) where
>   return x        = STM (\s -> return (x,s))
>   STM xs >>= f = STM (\s -> xs s >>= \(x, s') ->
>                                let STM f' = f x
>                                in f' s'
>                         )  
>
> mZeroSTM :: MONADZERONAME m => StateM m s a
> mZeroSTM = STM (\_ -> mZero)
>
#ifdef __Haskell98__
> instance MonadPlus m => MonadPlus (StateM m s) where
>   mzero = mZeroSTM
>   mplus (STM stm) (STM stm') = STM (\s -> stm s +++ stm' s)
#else
> instance MonadZero m => MonadZero (StateM m s) where
>   zero = mZeroSTM
> 
> instance MonadPlus m => MonadPlus (StateM m s) where
>   (STM stm) ++ (STM stm') = STM (\s -> stm s ++ stm' s)
#endif
> 
> instance ErrorMonad m => ErrorMonad (StateM m s) where
>   failEM msg = STM (\_ -> failEM msg)
> 
> updateSTM :: Monad m => (s->s) -> StateM m s s
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

> mliftErr :: ST s a -> STErr s a
> mliftErr = liftSTtoSTErr
> 
> mliftSTM :: Functor f => f a -> StateM f s a
> mliftSTM m = STM (\s -> fMap (`pair` s) m)

> mliftOut :: Functor m => m a -> OutputT b m a
> mliftOut ma = OT (fMap return ma)

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
> map1 = fMap
> map0 = return

\end{verbatim}
\section{Writer and output monads}
\begin{verbatim}

> data Writer a b = Writer ([a]->[a]) b
> instance Functor (Writer a) where
>   __FMAPNAME__ f (Writer s x) = Writer s (f x)
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
>   __FMAPNAME__ f (OT mx) = OT (fMap (fMap f) mx)

> instance (Functor m ,Monad m) => Monad (OutputT a m) where
>   return x     = OT (return (return x))
>   (OT m) >>= f = OT ((fMap join . join . fMap f') m)
>        where f' = swap . fMap (unOT . f)
>              swap (Writer s ma) = fMap (Writer s) ma

> output :: Monad m => a -> OutputT a m ()
> output x = OT (return (write x))

> runOutput' :: Functor m => OutputT a m b -> m ([a] -> [a],b)
> runOutput' (OT m) = fMap (\(Writer s a) -> (s,a)) m

> runOutput :: Functor m => [a] -> OutputT a m b -> m ([a],b)
> runOutput l o = fMap (\(s,x)->(s l,x)) (runOutput' o)

\end{verbatim}

