fthread :: (Bifunctor f,Monad m) => f (m a) (m b) -> m (f a b)
fthread = undefined

