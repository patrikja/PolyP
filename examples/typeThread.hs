fthread_Prr    :: Monad m => (m a,m b) -> m (a,b)
fthread_Ppr    :: Monad m => (m a,m b) -> m (a,b)
fthread_e      :: Monad m => () -> m ()
fthread_f0     :: Monad m => Either () (m a,m b) -> m (Either () (a,b))
thread_f0      :: Monad m => [m a] -> m [a]
sumthread      :: Monad m => Either (m a) (m b) -> m (Either a b)
fthread_f4Tree :: Monad m => Either (m a) (m b,m c) -> m (Either a (b,c))
thread_f4Tree  :: Monad m => Tree (m a) -> m (Tree a)
