-- Prelude functions
(.)     :: (b->c)->(a->b)->(a->c)
(+)     :: Num a => a->a->a      
(-)     :: Num a => a->a->a      
(*)     :: Num a => a->a->a      
(<=)    :: Ord a => a->a->Bool   
(>=)    :: Ord a => a->a->Bool   
(>)     :: Ord a => a->a->Bool   
(<)     :: Ord a => a->a->Bool   
(==)    :: Eq a => a->a->Bool    
(/=)    :: Eq a => a->a->Bool    
(&&)    :: Bool->Bool->Bool      
(||)    :: Bool->Bool->Bool      
($)     :: (a->b)->a->b	       
not     :: Bool->Bool	       
and     :: [Bool]->Bool          
all     :: (a -> Bool) -> [a] -> Bool
any     :: (a -> Bool) -> [a] -> Bool
compare :: Ord a => a -> a -> Ordering
or      :: [Bool]->Bool
foldr   :: (a -> b -> b) -> b -> [a] -> b
negate  :: Num a => a->a
uncurry :: (a -> b -> c) -> (a,b) -> c
error   :: [Char] -> a
undefined :: a
print   :: Show a => a -> IO ()
length  :: [a]->Int
concat  :: [[a]]->[a]
maybe   :: a -> (b -> a) -> Maybe b -> a
const   :: a->b->a
either  :: (a->c) -> (b->c) -> Either a b -> c
id      :: a->a
flip    :: (a -> b -> c) -> b -> a -> c
map     :: (a->b)->[a]->[b]
(++)    :: [a]->[a]->[a]
fst     :: (a,b)->a
snd     :: (a,b)->b
head    :: [a]->a
tail    :: [a]->[a]
take    :: Int->[a]->[a]
filter  :: (a->Bool)->[a]->[a]
asTypeOf:: a->a->a
(!!)    :: [a] -> Int -> a
show    :: Show a => a -> String
isSpace :: Char->Bool
words   :: String->[String]
unwords :: [String]->String
zip     :: [a] -> [b] -> [(a,b)]
return  :: Monad m => a -> m a
(>>=)   :: Monad m => m a -> (a -> m b) -> m b
(>>)    :: Monad m => m a -> m b -> m b
applyM  :: Monad m => (a -> m b) -> m a -> m b
