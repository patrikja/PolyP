module Sum(psum,fsum,size) where 
import Base(cata,pmap)
import PolyPTypes

psum :: Regular d => d Int -> Int
psum = cata fsum

fsum :: Bifunctor f => f Int Int -> Int
fsum x = onlyUsefulForTypeChecking "fsum"

size :: Regular d => d a -> Int
size = psum . pmap (\_->1)
