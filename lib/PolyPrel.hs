-- Prelude functions
(!!)    :: [a] -> Int -> a
($)     :: (a->b)->a->b
(&&)    :: Bool->Bool->Bool
(*)     :: Num a => a->a->a
(/)     :: Num a => a->a->a
(+)     :: Num a => a->a->a
(++)    :: [a]->[a]->[a]
(-)     :: Num a => a->a->a
(.)     :: (b->c)->(a->b)->(a->c)
(/=)    :: Eq a => a->a->Bool
(/=)    :: Eq a => a->a->Bool
(<)     :: Ord a => a->a->Bool
(<=)    :: Ord a => a->a->Bool
(=<<)   :: Monad m => (a -> m b) -> m a -> m b
(==)    :: Eq a => a->a->Bool
(>)     :: Ord a => a->a->Bool
(>=)    :: Ord a => a->a->Bool
(>>)    :: Monad m => m a -> m b -> m b
(>>=)   :: Monad m => m a -> (a -> m b) -> m b
(||)    :: Bool->Bool->Bool
all     :: (a -> Bool) -> [a] -> Bool
and     :: [Bool]->Bool
any     :: (a -> Bool) -> [a] -> Bool
asTypeOf:: a->a->a
compare :: Ord a => a -> a -> Ordering
concat  :: [[a]]->[a]
const   :: a->b->a
div     :: Integral a => a -> a -> a
drop    :: Int->[a]->[a]
either  :: (a->c) -> (b->c) -> Either a b -> c
error   :: [Char] -> a
filter  :: (a->Bool)->[a]->[a]
flip    :: (a -> b -> c) -> b -> a -> c
foldr   :: (a -> b -> b) -> b -> [a] -> b
fst     :: (a,b)->a
getLine :: IO String
head    :: [a]->a
id      :: a->a
isSpace :: Char->Bool
length  :: [a]->Int
lines   :: String -> [String]
log     :: Floating a => a -> a
lookup  :: Eq a => a -> [(a,b)] -> Maybe b
map     :: (a->b)->[a]->[b]
max     :: Ord a => a -> a -> a
maximum :: Ord a => [a] -> a
min     :: Ord a => a -> a -> a
minimum :: Ord a => [a] -> a
maybe   :: a -> (b -> a) -> Maybe b -> a
negate  :: Num a => a->a
not     :: Bool->Bool
null	:: [a] -> Bool
or      :: [Bool]->Bool
print   :: Show a => a -> IO ()
putStr  :: String -> IO ()
putStrLn:: String -> IO ()
read    :: Read a => String -> a
return  :: Monad m => a -> m a
show    :: Show a => a -> String
snd     :: (a,b)->b
splitAt :: Int -> [a] -> ([a],[a])
tail    :: [a]->[a]
take    :: Int->[a]->[a]
takeWhile:: (a -> Bool) -> [a] -> [a]
uncurry :: (a -> b -> c) -> (a,b) -> c
undefined :: a
unlines :: [String] -> String
unwords :: [String]->String
words   :: String->[String]
zip     :: [a] -> [b] -> [(a,b)]
unParF  :: ParF a b -> a
unRecF  :: RecF a b -> b
unCompF :: CompF d g a b -> d (g a b)
unConstF:: ConstF t a b -> t
-- Prelude data types
data Bool        =  False | True
data Either a b  =  Left a | Right b
data Maybe a     =  Nothing | Just a
data Ordering    =  LT | EQ | GT
-- data (->) a b
-- data [a] = [] | a : [a]
-- data (), (,), (,,)
-- data Char, Double, Float, Int, Integer, IOError, Void
-- data IO a
data SumF f g a b  = InL (f a b) | InR (g a b)
data ProdF f g a b = f a b :*: g a b
data EmptyF a b    = EmptyF
data ParF a b      = ParF a
data RecF a b      = RecF b
data CompF d g a b = CompF (d (g a b))
data ConstF t a b  = ConstF t
