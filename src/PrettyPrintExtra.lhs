\chapter{More pretty printing combinators} 
\begin{verbatim}

> module PrettyPrintExtra(module PrettyPrintLibrary,
>                         module PrettyPrintExtra) where
> import PrettyPrintLibrary

> class Pretty a where
>    pretty :: a -> Doc

> instance Pretty Doc where
>   pretty = id

> showDoc :: Doc -> String
> showDoc = layout 100 100 
> instance Show Doc where
>   showsPrec _ x = \s -> showDoc x ++ s

\end{verbatim}
\section{Combinators}
\begin{verbatim}

> ppHorizontalList :: Pretty a => [a] -> Doc
> ppHorizontalList 
>   = foldr (<>) (text "") . map pretty

> ppVerticalList :: Pretty a => [a] -> Doc
> ppVerticalList [] = text ""
> ppVerticalList xs
>   = foldr1 ($$) $ map pretty xs

> ppSepby :: (Pretty a,Pretty b) => [a] -> b -> Doc
> ppSepby [] _ = text ""
> ppSepby (x:xs) separator
>   = ppHorizontalList ( pretty x : map ppsep xs)
>   where ppsep y = pretty separator <> pretty y

> ppPackedList :: Pretty a => String -> [a] -> 
>                             String -> String -> Doc
> ppPackedList left xs right separator
>   = ppPack left (xs `ppSepby` text separator) right

> ppPack :: Pretty a => String -> a -> String -> Doc
> ppPack left x right = text left <> pretty x <> text right

> ppParentheses, ppBrackets, ppBraces :: Pretty a => a -> Doc
> ppParentheses x = ppPack "(" x ")" 
> ppBrackets    x = ppPack "[" x "]"
> ppBraces      x = ppPack "{" x "}"

> ppTuple,ppList,ppCommaList :: Pretty a => [a] -> Doc
> --ppTuple xs = ppPackedList "(" xs ")" ", "
> ppList  xs = ppPackedList "[" xs "]" ", "
> ppCommaList xs = xs `ppSepby` text ","

> ppApp :: [Doc] -> Doc
> ppApp xs = foldr1 (\x y -> x <> (text " ") <> y) xs

> ppTuple xs = text "(" <> 
>              sep (map (<>(text ",")) (init ds) ++ 
>                   [(last ds)<>text ")"]) 
>   where ds = map pretty xs

> infixr <+>
> x <+> y = x <> text " " <> y

\end{verbatim}
