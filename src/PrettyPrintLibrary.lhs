=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Pretty printing combinators.

> module PrettyPrintLibrary(Doc,(<>),($$),text,sep,nest,layout) where

> infixr $$
> infixr <>

> data Doc = Nest Int [Alt]
> data Alt = Text Int SS | Above Int SS Doc
> type SS  = String -> String

> text   :: String -> Doc			-- literal text
> nest   :: Int -> Doc -> Doc		-- indention
> ($$)   :: Doc -> Doc -> Doc		-- vertical composition
> (<>)   :: Doc -> Doc -> Doc		-- horizontal composition
> sep    :: [Doc] -> Doc			-- "intelligent" composition
> layout :: Int -> Int -> Doc -> String   -- layout a document

> text xs = Nest 0 [Text (length xs) (xs ++)]

> nest n = \(Nest m as) -> Nest (m+n) as

> (Nest n as) $$ d
>    = Nest n (map f as)
>      where
>         f (Text m s)     = Above m s (nest (-n) d)
>         f (Above m s d') = Above m s (d' $$ nest (-n) d)


> (Nest n as) <> (Nest m bs)
>    = Nest n (concat (map f as))
>      where
>         f (Text k s)    = map g bs
>                           where
>                              g (Text l t)    = Text (k+l) (s.t)
>                              g (Above l t d) = Above (k+l) (s.t) (nest k d)
>         f (Above k s d) = [Above k s (d <> (Nest m bs))]

> sep []  = text ""
> sep [d] = d
> sep ds  = fitunion (foldr1 (\x y -> x <> text " " <> y) ds) (foldr1 ($$) ds)

> layout w r d = nestbest 0 w r d


=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Auxilliary functions


> fitunion :: Doc -> Doc -> Doc
> nice     :: Int -> Int -> Alt -> Bool
> choose   :: Int -> Int -> Alt -> Alt -> Alt
> nestbest :: Int -> Int -> Int -> Doc -> String

> fitunion (Nest n (Text m s : _)) (Nest _ as) = Nest n (Text m s:as)
> fitunion _ d  = d

> nice w r (Text n s)    = n <= min r w
> nice w r (Above n s d) = n <= min r w

> choose w r d d' = if nice w r d then d else d'

> nestbest n w r (Nest m as) =
>    case foldr1 (choose (w-m) r) as of
>       Text _ s    -> indnt (n+m) s ""
>       Above _ s d -> indnt (n+m) s (nestbest (n+m) (w-m) r d)

> indnt n s c | n >= 8 = '\t' : indnt (n-8) s c
> indnt n s c | n >= 1 = ' '  : indnt (n-1) s c
> indnt 0 s c          = s ('\n': c)

indnt is only defined for n>=0

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

