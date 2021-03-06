{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

module PolyPrelude where

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

instance FunctorOf (SumF EmptyF (ProdF ParF RecF)) [] where
    inn (InL EmptyF)                    = []
    inn (InR ((ParF a) :*: (RecF b)))   = a : b
    out []                              = InL EmptyF
    out (a : b)                         = InR ((ParF a) :*: (RecF b))

    datatypeName                        = const "[]"
    constructorName []                  = "[]"
    constructorName (_:_)               = ":"
    constructorFixity []                = defaultFixity
    constructorFixity (_:_)             = Fixity RightAssoc 5
 
instance FunctorOf (SumF EmptyF ParF) Maybe where
    inn (InL EmptyF)            = Nothing
    inn (InR (ParF a))          = Just a
    out Nothing                 = InL EmptyF
    out (Just a)                = InR (ParF a)
    datatypeName                = const "Maybe"
    constructorName Nothing     = "Nothing"
    constructorName (Just _)    = "Just"
  
---
--              Structure types
---

data    SumF  f g a b = InL (f a b)
                      | InR (g a b)
data    ProdF f g a b = f a b :*: g a b
data    EmptyF    a b = EmptyF                         deriving Show
newtype FunF  f g a b = FunF   {unFunF   :: f a b -> g a b}
newtype ParF      a b = ParF   {unParF   :: a}
newtype RecF      a b = RecF   {unRecF   :: b}
newtype CompF d g a b = CompF  {unCompF  :: d (g a b)}
newtype ConstF t  a b = ConstF {unConstF :: t}

instance (Show (f a b), Show (g a b)) => Show (SumF f g a b) where
    showsPrec p (InL x) = showParen (p>9) $ showString "InL " . showsPrec 10 x
    showsPrec p (InR y) = showParen (p>9) $ showString "InR " . showsPrec 10 y

instance (Show (f a b), Show (g a b)) => Show (ProdF f g a b) where
    showsPrec p (x :*: y) = showParen (p>5) $ showsPrec 6 x . showString " :*: " . showsPrec 5 y

instance Show a => Show (ParF a b) where
    showsPrec p (ParF x) = showParen (p>9) $ showString "ParF " . showsPrec 10 x

instance Show b => Show (RecF a b) where
    showsPrec p (RecF x) = showParen (p>9) $ showString "RecF " . showsPrec 10 x

instance Show (d (g a b)) => Show (CompF d g a b) where
    showsPrec p (CompF x) = showParen (p>9) $ showString "CompF " . showsPrec 10 x

instance Show t => Show (ConstF t a b) where
    showsPrec p (ConstF x) = showParen (p>9) $ showString "ConstF " . showsPrec 10 x

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

toPar           = ParF
toRec           = RecF
toConst         = ConstF
toComp toG      = CompF . gmap toG
toFun fromG toH = FunF . (toH.) . (.fromG)

fromPar         = unParF
fromRec         = unRecF
fromConst       = unConstF
fromComp fromG  = gmap fromG . unCompF
fromFun toG fromH   = (fromH.) . (.toG) . unFunF

