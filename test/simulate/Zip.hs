module Zip(pzip,fzip,pzipWith,pzipWith',fzipWith,(@@),resultM) where
import Base(pmap,fmap2,(-+-),(-*-))
import Propagate(fprop,sumprop,prodprop,propagate,mapMaybe)
import PolyPTypes
-- Maybe could be replaced by any MonadZero

pzip :: Regular d => (d a,d b) -> Maybe (d (a,b))
pzip  =  ( (resultM . inn) @@ (fprop.fmap2 resultM pzip) @@ fzip )
      .  (out -*- out)

punzip :: Regular d => d (a,b) -> (d a,d b)
punzip x = (pmap fst x, pmap snd x)

pzipWith' :: Regular d => (FunctorOf d c e -> e) -> 
                          ((d a,d b)->e) -> 
                          ((a,b)->c) -> (d a,d b) -> e
pzipWith' ins fail op (x,y)  =
  maybe (fail (x,y)) (ins . fmap2 op (pzipWith' ins fail op)) 
        (fzip (out x, out y))

{-
pzipWith' ins fail op (x,y) =  
  maybe (fail (x,y)) ins (fzipWith op (pzipWith' ins fail op) (out x, out y))
-}

pzipWith :: Regular d => ((a, b) -> Maybe c) -> (d a, d b) -> Maybe (d c)
pzipWith  = pzipWith' (mapMaybe inn.fprop) (const zeroM)

funzip :: Bifunctor f => f (a,c) (b,d) -> (f a b,f c d)
funzip x = (fmap2 fst fst x, fmap2 snd snd x)

-- Note: a different kind of typing compared to pzipWith
fzipWith :: Bifunctor f => ((a,a')->c) -> ((b,b')->d) -> 
	    (f a b, f a' b') -> Maybe (f c d)
fzipWith f g = mapMaybe (fmap2 f g) . fzip 

fzip :: Bifunctor f => (f a b,f c d) -> Maybe (f (a,c) (b,d))
fzip p = onlyUsefulForTypeChecking "fzip"

sumzip :: (Either a b,Either c d)-> Maybe (Either (a,c) (b,d))
sumzip p = case p of
	     (Left s ,Left t ) -> resultM (Left (s,t))
	     (Right s,Right t) -> resultM (Right (s,t))
	     _                 -> zeroM

prodzip :: ((a,b),(c,d)) -> Maybe ((a,c),(b,d))
prodzip ((x,y),(s,t))  =  resultM ((x,s),(y,t))

-- This requires an inexpressible type of fzip, but works due to a PolyP bug
constzip :: Eq t => (t,t) -> Maybe t
constzip (x,y) = if x==y then resultM x else zeroM

-- this is the intended meaning: one for each instance of Eq
--constzipInt :: (Int,Int) -> Maybe Int
--constzipInt (x,y) = if x==y then resultM x else zeroM

{-
  Maybe monad functions
-}
zeroM :: Maybe a
zeroM = Nothing

resultM  :: a -> Maybe a
resultM x  =  Just x

bindM    :: Maybe a -> (a -> Maybe b) -> Maybe b
bindM x f  =  maybe Nothing f x

(@@)     :: (a -> Maybe b) -> (c -> Maybe a) -> c -> Maybe b
g @@ f = \a-> f a `bindM` g
