module Crush(crush,fcrush) where 
import Base(cata,pmap)
import PolyPTypes

crush :: Regular d => (a->a->a) -> a -> d a -> a
crush op e =  cata (fcrush op e)


fcrush :: Bifunctor f => (a->a->a) -> a -> f a a -> a
fcrush op zero x = onlyUsefulForTypeChecking "fcrush"
