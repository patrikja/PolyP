module BaseM(pmapM,fmap2M,cataM,anaM,hyloM,paraM,innM,outM,idM,(@@),mapm) where
import PolyPTypes

pmapM :: (Regular d, Monad m) => (a -> m b) -> d a -> m (d b)
pmapM fM   = mapm inn . fmap2M fM  (pmapM fM)   . out

fmap2M :: (Bifunctor f,Monad m) => (a->m c) -> (b->m d) -> f a b -> m (f c d)
fmap2M fM gM x = error "fmap2M: only useful for type checking"

cataM :: (Regular d,Monad m) => (FunctorOf d a b -> m b) -> d a -> m b
cataM iM = iM @@ fmap2M idM (cataM iM) @@ outM

anaM :: (Regular d,Monad m) => (b -> m (FunctorOf d a b)) -> b -> m (d a)
anaM oM = innM @@ fmap2M idM (anaM oM) @@ oM

hyloM :: (Bifunctor f,Monad m) => (f a b -> m b)-> (c -> m (f a c)) -> c -> m b
hyloM iM oM = iM      @@ fmap2M idM (hyloM iM oM) @@ oM

paraM :: (Regular d, Monad m) => (d a -> FunctorOf d a b -> m b) -> d a -> m b
paraM iM x = iM x =<< fmap2M idM (paraM iM) (out x)

innM :: (Regular d, Monad m) =>  FunctorOf d a (d a) -> m (d a)
innM = return . inn
outM :: (Regular d, Monad m) =>  d a -> m (FunctorOf d a (d a))
outM = return . out
idM :: Monad m => a -> m a
idM = return

mapm :: Monad m => (a->b) -> m a -> m b
mapm f mx = mx >>= \x -> return (f x)
(@@) :: Monad m => (b->m c) -> (a->m b) -> (a->m c)
f @@ g = \y -> g y >>= f
