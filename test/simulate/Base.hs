module Base(fmap2,pmap,cata,ana,hylo,para,(-*-),(-+-),module PolyPTypes) where 
import PolyPTypes

class Bifunctor f where
  fmap2 :: (a->c) -> (b->d) -> f a b -> f c d

pmap :: Regular d => (a -> b) -> d a -> d b
pmap f   = inn . fmap2 f  (pmap f)   . out

instance Regular d => Bifunctor (FunctorOf d) where
  fmap2 f g x = undefined

cata :: Regular d => (FunctorOf d a b -> b) -> (d a -> b)
ana  :: Regular d => (b -> FunctorOf d a b) -> (b -> d a)
hylo :: Bifunctor f => (f a b -> b) -> (c -> f a c) -> c -> b
cata i   = i   . fmap2 id (cata i  ) . out
ana    o = inn . fmap2 id (ana    o) . o
hylo i o = i   . fmap2 id (hylo i o) . o

para :: Regular d => (d a -> FunctorOf d a b -> b) -> d a -> b
para i x = i x (fmap2 id (para i) (out x))

---------------------------------------------------------------
-- Help functions
(-*-) :: (a -> c) -> (b -> d) -> (a,b) -> (c,d)
(-+-) :: (a -> c) -> (b -> d) -> Either a b -> Either c d

f -*- g = \p -> (f (fst p), g (snd p))
f -+- g = either (Left . f) (Right . g)

