module Equal(pequal,fequal,peq) where
import PolyPTypes

pequal :: Regular d => (a->b->Bool) -> d a -> d b -> Bool
pequal eq x y = fequal eq (pequal eq) (out x) (out y)

peq :: (Regular d, Eq a) => d a -> d a -> Bool
peq = pequal (==)

fequal :: Bifunctor f => (a->b->Bool) -> (c->d->Bool) -> 
                         f a c -> f b d -> Bool
fequal p r x y = onlyUsefulForTypeChecking "fequal" p r x y 

sumequal :: (a->b->Bool) -> (c->d->Bool) -> 
            Either a c -> Either b d -> Bool
sumequal f g a b = case (a,b) of
		   (Left  x, Left  v)  ->  f x v
		   (Right y, Right w)  ->  g y w
		   _                   ->  False

prodequal :: (a->b->Bool) -> (c->d->Bool) -> 
             (a,c)->(b,d) -> Bool
prodequal f g p q = f (fst p) (fst q) && 
                    g (snd p) (snd q)
--prodequal f g (x,y) (v,w) = f x v && g y w

