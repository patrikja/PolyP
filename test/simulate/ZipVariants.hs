module ZipVariants(pzipWith'',pzip'',pzip') where
import Zip(pzipWith,pzipWith')
import Flatten(fl_all)
import PolyPTypes

pzipWith'' :: Regular d => ((a, b) -> c) -> (d a, d b) -> Maybe (d c)
pzipWith'' op = pzipWith (return . op)

pzip'' :: Regular d => (d a,d b) -> Maybe (d (a,b))
pzip'' = pzipWith'' id

pzip' :: Regular d => (d a, d b) -> (d (a,b), Bool)
pzip' p = ( pzipWith'    inn     (const undefined)    id      p
          , pzipWith' (and.fl_all) (const False) (const True) p
          )

