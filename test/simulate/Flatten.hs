module Flatten(flatten,fflatten,fl_par,fl_rec,fl_all,singleton,nil) where
import Base(pmap,fmap2)
import PolyPTypes

flatten :: Regular d => d a -> [a]
flatten  =  fflatten . fmap2 singleton flatten . out

fflatten :: f [a] [a] -> [a]
fflatten x = error "fflatten: only useful for type checking" x

fl_par :: Bifunctor f => f a b -> [a]
fl_rec :: Bifunctor f => f a b -> [b]
fl_all :: Bifunctor f => f a a -> [a]
fl_par = fflatten . fmap2 singleton nil
fl_rec = fflatten . fmap2 nil       singleton
fl_all = fflatten . fmap2 singleton singleton

singleton :: a -> [a]
singleton    x =  [x]
nil :: a -> [b]
nil    _ =  []



