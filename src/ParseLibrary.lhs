\chapter{Monadic parsing combinators} 
Converted from Gofer to Hugs to Haskell 1.3 to 1.4: This means that some
comments are now obsolete.
\begin{verbatim}

> module ParseLibrary where
> --      (optional, digit, ...)
> import MonadLibrary((<@),(<@-),(<<),(<:*>),(<*>),(<|),mguard,(+++),
>                     StateM(..),fetchSTM,updateSTM,
>                     Error(..),ErrorMonad(..))
> import MyPrelude(fMap)
> import Char(isSpace,isAlpha,isDigit)
#ifdef __HBC__
> import Monad() -- hbc does not import instance declarations correctly
#endif

> infixl 1 `chainr`, `chainl`

\end{verbatim}

Based on ``Monadic parsing combinators'' a DRAFT by Graham Hutton, 8th
May, 1995

\section{Parsers as monads}

The standard type of non-deterministic parsers,
\begin{verbatim}

  type Parser a = String -> [(String,a)]

\end{verbatim}
is an instance of the parameterised state monad, in which the
base monad is list, the state is a string:
\begin{verbatim}

  type Parser a = StateM [] String a

\end{verbatim}
In fact, since we want access to line and column numbers for the
purpose of error reporting (and for handling the offside rule),
we will use a more refined type of parsers:

\begin{verbatim}

> type Pos = ( Int     -- current line number
>            , Int     -- current column number
>            , Int     -- current offside line
>            , Int )   -- current offside column
>
> type Parser a = StateM [] (String,Pos) a

> item :: Parser Char
> item = STM (\(s,(l,c,ol,oc)) -> case s of
>             []     -> []
>             (x:xs) -> -- trace (x:"") $ 
>                       if l > ol && c < oc then []
>                       else [(x,(xs,(l',c',ol,oc)))]
>                       where (l',c') = case x of
>                                         '\t' -> (l,((c `div` 8)+1)*8)
>                                         '\n' -> (l+1,0)
>                                         _    -> (l,c+1)
>            )

\end{verbatim}
A parser that consumes single characters satisfying a given predicate.
\begin{verbatim}

> sat :: (Char -> Bool) -> Parser Char
> sat p  = item <| p

> digit :: Parser Char
> digit = sat isDigit

\end{verbatim}
Parsers for specific characters and strings are defined by:
\begin{verbatim}

> lit :: Char -> Parser Char
> lit x = sat (==x)
>
> string :: String -> Parser String
> string   []   = return []
> string (x:xs) = lit x <:*> string xs

\end{verbatim}
\section{Combinators for repetition}
A number of parsing combinators that deal with repetition can
be generalised to an arbitrary monad with a zero and a plus:
\begin{verbatim}
  many   :: MonadPlus m => m a -> m [a]
  some   :: MonadPlus m => m a -> m [a]
  sepby  :: MonadPlus m => m a -> m b -> m [a]
  chainr :: MonadPlus m => m a -> m (a -> a -> a) -> m a
  chainl :: MonadPlus m => m a -> m (a -> a -> a) -> m a
\end{verbatim}  
But we will use specialized versions for efficiency.
\begin{verbatim}

> many   :: Parser a -> Parser [a]
> some   :: Parser a -> Parser [a]
> sepby  :: Parser a -> Parser b -> Parser [a]
> chainr :: Parser a -> Parser (a -> a -> a) -> Parser a
> chainl :: Parser a -> Parser (a -> a -> a) -> Parser a

> many p = (p <:*> (many p)) `opt` []
> some p = p <:*> (many p)
>
> p `sepby`  op = p >>= \x ->
>                 (op >> (p `sepby` op) <@ (x:)) `opt` [x]
>
>
> p `chainr` op = p >>= \x ->
>                  (op             >>= \f-> 
>                  (p `chainr` op) >>= \y-> 
>                   return (f x y))              `opt` x
> 
> p `chainl` op = p >>= chainl'
>                 where
>                    chainl' x = (op >>= \f ->
>                                 p  >>= \y ->
>                                 chainl' (f x y)) `opt` x

> opt :: Parser a -> a -> Parser a
> (STM p) `opt` v = STM (\s -> case p s of
>                                 []    -> [(v,s)]
>                                 (x:_) -> [x]
>                       )

> optional :: Parser a -> Parser (Maybe a)
> optional p = (p <@ Just) `opt` Nothing

> cut :: Parser a -> Parser a
> cut (STM p) = STM (take 1 . p)

\end{verbatim}
\section{White-space and comments}
As mentioned earlier, white-space must be treated specially
during parsing, in the sense that it is never offside.  This
can be achieved by the simple trick of setting the offside
column to 0 before parsing white-space, and restoring the
original column position afterwards. Comments can be handled
in the spaces parser. A comment can either be a simple comment
or a nested comment.
\begin{verbatim}

> spaces :: Parser ()
> spaces = fetch_off >>= \(l,c) -> 
>          set_off (l,0) >> 
>          many (sat isSpace +++ comment +++ ncomment) >>
>          set_off (l,c) >>
>          return ()
>     where comment  = string "--" >>  
>                      many (sat (/='\n')) >>  
>                      return ' '
>
>           ncomment = string "{-" >> skipcomment ' ' >> return ' '
>           skipcomment x = item >>= \y->
>                            case [x,y] of
>                              "{-" -> skipcomment ' ' >>
>                                      skipcomment ' ' >> return ()
>                              "-}" -> return ()
>                              _    -> skipcomment y  

\end{verbatim}
The functions \verb|fetch_off| and \verb|set_off| are defined using fetch
and update; we also define \verb|fetch_pos| and \verb|set_pos|:
\begin{verbatim}

> fetch_off :: Parser (Int,Int)
> fetch_pos :: Parser (Int,Int)
>
> fetch_off = fetchSTM >>= \(_,(_,_,ol,oc)) -> return (ol,oc)
> fetch_pos = fetchSTM >>= \(_,(l,c,_ ,_ )) -> return ( l, c)
>
> set_off :: (Int,Int) -> Parser ()
> set_pos :: (Int,Int) -> Parser ()
>
> set_off (ol,oc) = updateSTM (\ (s,(l,c,_,_))   -> (s,(l,c,ol,oc))) <@- ()
> set_pos (l,c)   = updateSTM (\ (s,(_,_,ol,oc)) -> (s,(l,c,ol,oc))) <@- ()

\end{verbatim}
It is convenient to define a combinator that strips white-space
and comments after applying a given parser:
\begin{verbatim}

> strip :: Parser a -> Parser a 
> strip p = p << spaces

\end{verbatim}
Using strip we define a number of useful parsers:
\begin{verbatim}

> symbol :: String -> Parser String
> symbol xs = strip (string xs)
>
> word :: Parser String
> word = strip (some (sat isAlpha))
>
> number :: Parser Int
> number = strip (fMap str2int (some (sat isDigit)))
>          where f x y = 10*x + (fromEnum y - fromEnum '0')
>                str2int = foldl f 0

\end{verbatim}
\section{Handling offside-rules}
The Gofer-style offside rule can be implemented as follows:
first set the offside position to one character beyond the
position of the first significant character, then apply the
given parser repeatedly until the column position is strictly
less than the original column number (each time setting the
line number to the current line number), and then restore the
offside position to its original setting.
\begin{verbatim}

> some_offside :: Parser a -> Parser [a]
> some_offside p = 
>    fetch_off <*> fetch_pos >>= \((ol,oc),(l,c)) -> 
>    (set_off (l,c+1) >> (p `sepby` offside_op c)) << set_off (ol,oc)          

> offside_op :: Int -> Parser ()
> offside_op oc = fetch_pos       >>= \(l,c) -> 
>                 mguard (oc == c) >> 
>                 set_off (l,c+1)

\end{verbatim}
\section{Error handling}
Sometimes you know that a certain string is expected. It is nice to
report an error if this string isn't matched. This is what the
mustbe combinator does.
\begin{verbatim}

> err      :: String -> Parser a
> err xs    = fetch_pos >>= (\(l,_)-> failEM ("(line " ++ show l
>                         ++ ") Syntax error (expected \"" ++ xs ++ "\")"))

> mustbe   :: String -> Parser String
> mustbe xs = cut (symbol xs +++ err xs)

\end{verbatim}
\section{Applying parsers}
The function parse applies a parser to a given string, and returns
the first result value if the parser succeeds, and gives a simple
error message otherwise.  The strip combinator is used to remove
white-space and comments after parsing tokens; the parse function
is a convenient place to do the same before the first token.
\begin{verbatim}

> parse :: Parser a -> String -> Error a
> parse p ys = let (STM p') = cut (spaces >> p)
>              in case p' (ys,(0,0,0,0)) of
>                    []                   -> Err "can't parse input string"
>                    [(v,([],_))]         -> Done v
>                    [(_,(xs,(l,_,_,_)))] -> Err ("(line " ++ show l ++
>                                               ") Syntax error (unexpected `"
>                                               ++ take 20 xs ++ "'...)")
>                    _                    -> error "ParseLibrary.parse: impossible: cut gives list length > 1"

\end{verbatim}
