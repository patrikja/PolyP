module ConstructorName where
import PolyPTypes

constructorName :: Regular d => d a -> String
constructorName = fconstructorName . out

fconstructorName :: Bifunctor f => f a b -> String -- is built in
fconstructorName = onlyUsefulForTypeChecking "fconstructorName"

constructorNames :: Regular d => d a -> [String]
constructorNames = fconstructorNames . out

fconstructorNames :: Bifunctor f => f a b -> [String]
fconstructorNames x =
  map fconstructorName (fconstructors `asTypeOf` [x])

constructors  :: Regular d => [d a]
constructors  =  map inn fconstructors

fconstructors :: [f a b]
fconstructors = onlyUsefulForTypeChecking "fconstructors"

constructor2Int :: Regular d => d a -> Int
constructor2Int = fconstructor2Int . out

fconstructor2Int :: f a b -> Int
fconstructor2Int x = onlyUsefulForTypeChecking "fconstructor2Int"

plus1 :: Int -> Int
plus1 x = 1 + x

int2constructor :: Regular d => Int -> d a
int2constructor n = constructors !! n

int2fconstructor :: Bifunctor f => Int -> f a b
int2fconstructor n = fconstructors !! n
