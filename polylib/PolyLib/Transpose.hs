
module PolyLib.Transpose where

import PolyLib.Prelude
import PolyLib.Base
import PolyLib.BaseM
import PolyLib.Zip

import Control.Monad.State

-- Simplified version -----------------------------------------------------

--transpose :: .. => d (e a) -> e (d a)
transpose x = pmap (combine s) $ listTranspose c
    where (s,c) = separate x

separate :: (FunctorOf f d, P_fmap2M f) => d a -> (d (), [a])
separate x    = runState  (pmapM push x) []

combine  :: (FunctorOf f d, P_fmap2M f) => d () -> [a] -> d a
combine  x as = evalState (pmapM pop x)  as

push a = do    as <- get
	       put (as++[a])  -- or use a:as here and pmapMreversed above
	       return ()

pop () = do    a:as <- get
	       put as
	       return a

listTranspose :: (FunctorOf f d, P_fzip f, P_fprop f, P_fmap2 f)
		=> [d a] -> d [a]
listTranspose []     = error "Cannot transpose empty list"
listTranspose [x]    = pmap (:[]) x
listTranspose (x:xs) = pzipWith_ (:) x (listTranspose xs)

--

pzipWith_ f x y = case pzipWith f' (x,y) of
		    Just z  -> z
		    _	    -> error "Zipped structures doesn't match"
    where f' (x,y) = Just $ f x y

--

{-
-- Version with error handling
combine :: (FunctorOf f d, P_fmap2M f) => d () -> [a] -> Maybe (d a)
combine x as = evalStateT (pmapM (const pop) x) as
    where
	pop = do    s <- get
		    case s of
			a:as	-> do	put as
					return a
			_	-> lift Nothing

runError :: (Monad m) => ErrorT e m a -> m (Maybe a)
runError = liftM (either (const Nothing) Just) . runErrorT

listTranspose :: (FunctorOf f d, P_fzip f, P_fprop f, P_fmap2 f)
		=> [d a] -> Maybe (d [a])
listTranspose [] = Nothing
listTranspose [x] = Just $ pmap singleton x
listTranspose (x:xs) =
	do  y <- listTranspose xs
	    pzipWith mcons (x, y)
    where
	mcons (a,as) = Just (a:as)

--transpose :: .. => d (e a) -> Maybe (e (d a))
transpose dea = do  ela <- listTranspose $ flatten dea
		    pmapM (combine s) ela
    where
	s = pmap (const ()) dea
-}

