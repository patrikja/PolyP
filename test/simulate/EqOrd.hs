module EqOrd(pequal,peq,peq',pord) where
import Base(fmap2)
import ConstructorName(constructor2Int)
import Flatten(flatten,fl_all)
import Zip(pzip,fzip,pzipWith')
import PolyPTypes

pequal :: Regular d => (a->b->Bool) -> d a -> d b -> Bool
pequal op l r = pzipWith' (and . fl_all)
		          (\_ -> False) 
		          (uncurry op)
		          (l,r)        
-- fequal o1 o2 l r = 

peq :: (Regular d, Eq a) => d a -> d a -> Bool
peq l r = pzipWith' (and . fl_all)
		    (\_ -> False) 
		    (uncurry (==))
		    (l,r)        

peq' :: (Regular d, Eq a) => d a -> d a -> Bool
peq' x y = maybe False 
                 (all (uncurry (==)) . flatten) 
                 (pzip (x,y))

-- pord not officially released yet
pord :: (Regular d, Ord a) => (d a,d a) -> Ordering
pord (x,y) = maybe (compare (constructor2Int x) (constructor2Int y))
                   (foldr ordop EQ
                   .fl_all
                   .fmap2 (uncurry compare) pord
                   )
                   (fzip (out x, out y))

ordop :: Ordering -> Ordering -> Ordering
ordop x y = case x of 
              EQ -> y
              _  -> x