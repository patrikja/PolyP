-- Prelude functions
(!!)    :: [a] -> Int -> a
($)     :: (a->b)->a->b	       
(&&)    :: Bool->Bool->Bool      
(*)     :: Num a => a->a->a      
(+)     :: Num a => a->a->a      
(++)    :: [a]->[a]->[a]
(-)     :: Num a => a->a->a      
(.)     :: (b->c)->(a->b)->(a->c)
(/=)    :: Eq a => a->a->Bool    
(<)     :: Ord a => a->a->Bool   
(<=)    :: Ord a => a->a->Bool   
(==)    :: Eq a => a->a->Bool    
(>)     :: Ord a => a->a->Bool   
(>=)    :: Ord a => a->a->Bool   
(>>)    :: Monad m => m a -> m b -> m b
(>>=)   :: Monad m => m a -> (a -> m b) -> m b
(||)    :: Bool->Bool->Bool      
all     :: (a -> Bool) -> [a] -> Bool
and     :: [Bool]->Bool          
any     :: (a -> Bool) -> [a] -> Bool
applyM  :: Monad m => (a -> m b) -> m a -> m b
asTypeOf:: a->a->a
compare :: Ord a => a -> a -> Ordering
concat  :: [[a]]->[a]
const   :: a->b->a
either  :: (a->c) -> (b->c) -> Either a b -> c
error   :: [Char] -> a
filter  :: (a->Bool)->[a]->[a]
flip    :: (a -> b -> c) -> b -> a -> c
foldr   :: (a -> b -> b) -> b -> [a] -> b
fst     :: (a,b)->a
head    :: [a]->a
id      :: a->a
isSpace :: Char->Bool
length  :: [a]->Int
map     :: (a->b)->[a]->[b]
maybe   :: a -> (b -> a) -> Maybe b -> a
negate  :: Num a => a->a
not     :: Bool->Bool	       
or      :: [Bool]->Bool
print   :: Show a => a -> IO ()
return  :: Monad m => a -> m a
show    :: Show a => a -> String
snd     :: (a,b)->b
tail    :: [a]->[a]
take    :: Int->[a]->[a]
uncurry :: (a -> b -> c) -> (a,b) -> c
undefined :: a
unwords :: [String]->String
words   :: String->[String]
zip     :: [a] -> [b] -> [(a,b)]
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
