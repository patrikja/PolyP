-- Fake definitions of the basic polytypic combinators in Haskell
--   Useful for typechecking (fragments of) polytypic programs with hugs.
module PolyPTypes(Regular,inn,out,FunctorOf,Mu) where 
-- fake definitions of FunctorOf and Mu with the correct kinds
-- FunctorOf :: (*->*) -> (*->*->*)
data FunctorOf d a b = FunctorOf (d a)
-- Mu :: (*->*->*) -> (*->*)
data Mu f a = In f (Mu f a)
-- (Note that the relation between FunctorOf and Mu is lost

class Regular d where
  inn :: FunctorOf d a (d a) -> d a
  out :: d a -> FunctorOf d a (d a)
  inn = error "inn: Only useful for typechecking"
  out = error "out: Only useful for typechecking"

instance Regular []
instance Regular Maybe

