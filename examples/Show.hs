-- dummy module to satisfy hugs
module Show where
pshow :: (a->[Char]) -> d a -> [Char]
pshow = error ""

ppretty :: d a -> Expr a
ppretty = error ""

x +++ y = [] ++ x ++ y  -- trick to get the restricted type

data Expr a = Constr [Char] [Expr a] | Par a
        deriving Show

joinExpr :: Expr (Expr a) -> Expr a
joinExpr e = case e of
   (Par x) -> x
   (Constr c l) -> Constr c (map joinExpr l)


singleton x = [x]


astypeof :: a -> a -> a
astypeof = const

