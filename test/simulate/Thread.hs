module Thread(thread,pmapM,fthread,fmap2M) where
import PolyPTypes
import Base(cata,inn,pmap)
import BaseM(pmapM,fmap2M)

thread :: (Regular d, Monad m) => d (m a) -> m (d a)
thread  =  cata (liftM inn . fthread)

fthread :: (Bifunctor f,Monad m) => f (m a) (m b) -> m (f a b)
fthread x = error "fthread: only useful for type checking"

sumthread  :: Monad m => Either (m a) (m b) -> m (Either a b)
sumthread  =  liftM Left `either` liftM Right

prodthread :: Monad m => (m a,m b) -> m (a,b)
prodthread (mx,my) = mx >>= \x-> my >>= \y-> return (x,y)

liftM :: Monad m => (a->b) -> m a -> m b
liftM f mx = mx >>= \x -> return (f x)
