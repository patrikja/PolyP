{-# OPTIONS -fglasgow-exts #-}

module PolyLib.Prelude where

---
--    Structure types
---

class FunctorOf f d | d -> f where
    inn                 :: f a (d a) -> d a
    out                 :: d a -> f a (d a)

    datatypeName        :: d a -> String
    constructorName     :: d a -> String
    constructorFixity   :: d a -> Fixity
    -- Defaults
    constructorFixity _ = defaultFixity

data Fixity = Fixity    { associativity :: Associativity
                        , precedence    :: Int
                        }
    deriving (Eq, Show)

defaultFixity = Fixity LeftAssoc 9

data Associativity = NonAssoc | LeftAssoc | RightAssoc
    deriving (Eq, Show)

---
--  Default FunctorOf instances
---

$(deriveFunctorOf $ reifyDecl [])
$(deriveFunctorOf $ reifyDecl Maybe)

---
--              Structure types
---

data    SumF  f g a b = InL (f a b)
                      | InR (g a b)
data    ProdF f g a b = f a b :*: g a b
data    EmptyF    a b = EmptyF
newtype FunF  f g a b = FunF   {unFunF   :: f a b -> g a b}
newtype ParF      a b = ParF   {unParF   :: a}
newtype RecF      a b = RecF   {unRecF   :: b}
newtype CompF d g a b = CompF  {unCompF  :: d (g a b)}
newtype ConstF t  a b = ConstF {unConstF :: t}

infixr 5 :*:

unSumF (InL x)      = Left x
unSumF (InR y)      = Right y
unProdF (x :*: y)   = (x,y)

(f -*- g) (x :*: y) = f x :*: g y
f -+- g = foldSum (InL . f) (InR . g)
(f ->- g) (FunF x) = FunF $ g . x . f

(f -**- g) (x:*:y) = (f x, g y)
f -++- g = (Left . f) `foldSum` (Right . g)
(f ->>- g) (FunF x) = g . x . f

foldProd f (x :*: y) = f x y

foldSum f g e = case e of
    InL x   -> f x
    InR y   -> g y

first (x :*: y)	    = x
second (x :*: y)    = y

---
--  Polytypic map
---

gmap :: (FunctorOf f d, Bifunctor f) => (a -> b) -> d a -> d b
gmap f = inn . bimap f (gmap f) . out

class Bifunctor f where
  bimap :: (a -> b) -> (c -> d) -> f a c -> f b d

instance (Bifunctor f, Bifunctor g) => Bifunctor (SumF f g) where
    bimap f g (InL l)       = InL $ bimap f g l
    bimap f g (InR r)       = InR $ bimap f g r

instance (Bifunctor f, Bifunctor g) => Bifunctor (ProdF f g) where
    bimap f g (x :*: y)     = bimap f g x :*: bimap f g y

instance Bifunctor EmptyF where
    bimap _ _ EmptyF        = EmptyF

instance Bifunctor ParF where
    bimap f _ (ParF a)      = ParF $ f a

instance Bifunctor RecF where
    bimap _ g (RecF b)      = RecF $ g b

instance (FunctorOf f d, Bifunctor f, Bifunctor g) => Bifunctor (CompF d g) where
    bimap f g (CompF d)     = CompF $ gmap (bimap f g) d

instance Bifunctor (ConstF t) where
    bimap _ _ (ConstF c)    = ConstF c

---
--  to and from
---

class PatternFunctor f p r t | f p r -> t where
    to	    :: t -> f p r
    from    :: f p r -> t

instance PatternFunctor ParF p r p where
    to	    = ParF
    from    = unParF

instance PatternFunctor RecF p r r where
    to	    = RecF
    from    = unRecF

instance (FunctorOf f d, Bifunctor f, PatternFunctor g p r t)
	=> PatternFunctor (CompF d g) p r (d t) where
    to	    = CompF . gmap to
    from    = gmap from . unCompF

instance PatternFunctor (ConstF t) p r t where
    to	    = ConstF
    from    = unConstF

instance (PatternFunctor f p r t, PatternFunctor g p r u)
	=> PatternFunctor (FunF f g) p r (t -> u) where
    to	    = FunF . (to.) . (.from)
    from    = (from.) . (.to) . unFunF

