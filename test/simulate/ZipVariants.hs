module ZipVariants(pzipWith'',pzip'',pzip') where
import Zip(pzipWith,pzipWith',resultM)
import Flatten(fl_all)
import PolyPTypes

pzipWith'' :: Regular d => ((a, b) -> c) -> (d a, d b) -> Maybe (d c)
pzipWith'' op = pzipWith (resultM.op)

pzip'' :: Regular d => (d a,d b) -> Maybe (d (a,b))
pzip'' = pzipWith'' id

pzip' :: Regular d => (d a, d b) -> (d (a,b), Bool)
pzip' p = ( pzipWith'    inn     (const undefined)    id      p
          , pzipWith' (and.fl_all) (const False) (const True) p
          )

-- incomplete definition
-- fzipWith op1 op2 p = fmap2 fzip p
--   Maybe (f i j) <- Maybe (f (a,b) (c,d)) <- (f a c, f b d) 

--pzipWith' ins fail op (x,y)  =
--  maybe (fail (x,y)) (ins . fmap2 op (pzipWith' ins fail op)) 
--        (fzip (out x, out y))
