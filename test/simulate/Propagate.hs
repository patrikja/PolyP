module Propagate(propagate,fprop,sumprop,prodprop,mapMaybe) where
import Base(cata,inn,pmap)
import PolyPTypes

propagate  :: Regular d => d (Maybe a) -> Maybe (d a)
propagate  =  cata (mapMaybe inn . fprop)


fprop :: Bifunctor f => f (Maybe a) (Maybe b) -> Maybe (f a b)
fprop x = onlyUsefulForTypeChecking "fprop"

sumprop  :: Either (Maybe a) (Maybe b) -> Maybe (Either a b)
sumprop  =  mapMaybe Left `either` mapMaybe Right

prodprop :: (Maybe a,Maybe b) -> Maybe (a,b)
prodprop p = case p of
               (Just x,Just y) ->  Just (x,y)
               _               ->  Nothing

---------------------------------------------------------------
--  Maybe functions

mapMaybe :: (a->b) -> Maybe a -> Maybe b
mapMaybe f = maybe Nothing (Just . f)

