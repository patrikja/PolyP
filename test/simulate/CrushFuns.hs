module CrushFuns(psum,prod,conc,pand,por,size,flatten,pall,pany,pelem) where
import Crush(crush)
import Base(pmap)
import PolyPTypes

psum :: Regular d => d Int -> Int
prod :: Regular d => d Int -> Int
comp :: Regular d => d (a->a) -> (a->a)
conc :: Regular d => d [a] -> [a]
pand :: Regular d => d Bool -> Bool
por  :: Regular d => d Bool -> Bool
psum = crush (+)  0
prod = crush (*)  1
comp = crush (.)  id
conc = crush (++) []
pand = crush (&&) True
por  = crush (||) False

size    :: Regular d => d a -> Int
flatten :: Regular d => d a -> [a]
pall    :: Regular d => (a -> Bool) -> d a -> Bool
pany    :: Regular d => (a -> Bool) -> d a -> Bool
pelem   :: (Regular d,Eq a) => a -> d a -> Bool
size    = psum . pmap (\_->1)
flatten = conc . pmap (\x->[x])
pall p  = pand . pmap p
pany p  = por  . pmap p
pelem x = pany (\y->x==y)

flatten' :: Regular d => d a -> [a]
flatten'= (\f -> f []) . comp . pmap (:)
