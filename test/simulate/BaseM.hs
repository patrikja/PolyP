fthread :: (Bifunctor f,Monad m) => f (m a) (m b) -> m (f a b)
fthread = undefined

fmap2M :: (Bifunctor f,Monad m) => (a->m c) -> (b->m d) -> f a b -> m (f c d)
fmap2M fM gM = fthread . fmap2 fM gM

cataM :: (Regular d,Monad m) => (FunctorOf d a b -> m b) -> d a -> m b
cataM iM = iM @@ fmap2M idM (cataM iM) @@ outM

anaM :: (Regular d,Monad m) => (b -> m (FunctorOf d a b)) -> b -> m (d a)
anaM oM = innM @@ fmap2M idM (anaM oM) @@ oM

ana :: Regular d => (b -> FunctorOf d a b) -> b -> d a
ana f = inn . fmap2 id (ana f) . f

innM :: (Regular d, Monad m) =>  FunctorOf d a (d a) -> m (d a)
innM = return . inn
outM :: (Regular d, Monad m) =>  d a -> m (FunctorOf d a (d a))
outM = return . out
idM :: Monad m => a -> m a
idM = return

