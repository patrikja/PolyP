
module PolyPrelude where

---
--		FunctorOf class
---

class FunctorOf f d | d -> f where
	inn :: f a (d a) -> d a
	out :: d a -> f a (d a)
	datatypeName :: d a -> String
	constructorName :: d a -> String

---
--		Default FunctorOf instances
---

instance FunctorOf (SumF EmptyF (ProdF ParF RecF)) [] where
	inn (InL EmptyF) = []
	inn (InR ((ParF a) :*: (RecF b))) = a : b
	out [] = InL EmptyF
	out (a : b) = InR ((ParF a) :*: (RecF b))
	datatypeName = const "[]"
	constructorName [] = "[]"
	constructorName (_:_) = ":"
 
instance FunctorOf (SumF EmptyF ParF) Maybe where
  inn (InL EmptyF) = Nothing
  inn (InR (ParF a)) = Just a
  out Nothing = InL EmptyF
  out (Just a) = InR (ParF a)
  datatypeName = const "Maybe"
  constructorName Nothing = "Nothing"
  constructorName (Just _) = "Just"
  
---
--		Structure types
---

data SumF f g a b		= InL (f a b)
							| InR (g a b)			deriving Show
data ProdF f g a b	= f a b :*: g a b		deriving Show
data EmptyF a b		= EmptyF					deriving Show
data ParF a b			= ParF a					deriving Show
data RecF a b			= RecF b					deriving Show
data CompF d g a b	= CompF (d (g a b))	deriving Show
data ConstF t a b		= ConstF t				deriving Show

unSumF (InL x) = Left x
unSumF (InR y) = Right y
unProdF (x :*: y) = (x,y)
unParF (ParF x) = x
unRecF (RecF x) = x
unConstF (ConstF x) = x
unCompF (CompF x) = x

(f -*- g) (x :*: y) = f x :*: g y
f -+- g = foldSum (InL . f) (InR . g)

(f -**- g) (x:*:y) = (f x, g y)
f -++- g = (Left . f) `foldSum` (Right . g)

foldProd f (x :*: y) = f x y

foldSum f g e = case e of
	InL x	-> f x
	InR y	-> g y

---
--		Polytypic map
---

gmap :: (FunctorOf f d, Bifunctor f) => (a -> b) -> d a -> d b
gmap f = inn . bimap f (gmap f) . out

class Bifunctor f where
	bimap :: (a -> b) -> (c -> d) -> f a c -> f b d

instance (Bifunctor f, Bifunctor g) => Bifunctor (SumF f g) where
	bimap f g (InL l)			= InL $ bimap f g l
	bimap f g (InR r)			= InR $ bimap f g r

instance (Bifunctor f, Bifunctor g) => Bifunctor (ProdF f g) where
	bimap f g (x :*: y)	= bimap f g x :*: bimap f g y

instance Bifunctor EmptyF where
	bimap _ _ EmptyF			= EmptyF

instance Bifunctor ParF where
	bimap f _ (ParF a)		= ParF $ f a

instance Bifunctor RecF where
	bimap _ g (RecF b)		= RecF $ g b

instance (FunctorOf f d, Bifunctor f, Bifunctor g) => Bifunctor (CompF d g) where
	bimap f g (CompF d)		= CompF $ gmap (bimap f g) d

instance Bifunctor (ConstF t) where
	bimap _ _ (ConstF c)		= ConstF c

---
--		Stuff
---

---
--		EP
---

data EP a b = EP {to :: a -> b, from :: b -> a}

funEP :: EP a b -> EP c d -> EP (a -> c) (b -> d)
funEP ab cd = EP { to = \f -> to cd . f . from ab, from = \g -> from cd . g . to ab }

idEP :: EP a a
idEP = EP id id

sumEP = EP (either InL InR) unSumF
prodEP = EP (uncurry (:*:)) unProdF
emptyEP = EP (const EmptyF) (const ())
parEP = EP ParF unParF
recEP = EP RecF unRecF
compEP = EP CompF unCompF
constEP = EP ConstF unConstF

