\chapter{The parser}

The basic idea for all these parsers is that they should {\em end} by
eating white space (and comments) and assume that the first character
they receive be non-space.

\end{itemize}

\begin{verbatim}

#ifdef __DEBUG__
> module Parser (parse,pModule,pType0,pType1,pTypeFile) where
#else
> module Parser (parse,pModule,pType0,pType1,pTypeFile) where
#endif

#ifdef __DEBUG__

> import Char
> import MyPrelude
> import MonadLibrary
> import ParseLibrary
> import Grammar
> import PrettyPrinter
> import qualified Maybe

#else

> import Char(isUpper,isLower,isAlpha,isDigit)
> import MyPrelude(mapSnd,fMap)
> import MonadLibrary((<:*>),(<*>),(<@),(<@-),(<<),(<|),liftop,
>                     mapl,ErrorMonad(failEM),mZero,(+++))
> import ParseLibrary(Parser,item,lit,sat,digit,opt,optional,
>                     some_offside,mustbe,symbol,sepby,string,
>                     chainl,chainr,number,
>                     many,some,strip, parse)
> import Grammar(Expr'(..),Eqn'(..),Type(..),Qualified(..),Literal(..),ImpExp(..),
>                Import,Export,Associativity(..),
>                Expr,Eqn,Func,QType,Qualifier,VarID,ConID,Module'(..),Module,
>                qualify,noType,spineWalk,spineWalkType,(-=>),
>                tupleConstructor,listConstructor,isTupleCon,
>                functionConstructor)
> import qualified Maybe(catMaybes)

#endif
#ifdef __HBC__
> import Monad() -- hbc does not import instance declarations correctly
#endif

\end{verbatim}
The parser is not in good shape and uses far too many reductions
right now. (Plus it's UGLY!)

\section{Module}
The module parser accepts but ignores the module head, exports and imports.

\begin{verbatim}

> pModule :: Parser Module --[Eqn]
> pModule = pModule'

> pModule' :: Parser Module --[Eqn]
> pModule' = pModuleHead >>= \(name, exps) ->
>            pImpDecls >>= \imps ->
>            pEqns >>= \eqns ->
>		return $ Module name exps imps eqns

> pModuleHead :: Parser (ConID, [Export])
> pModuleHead = (   (symbol "module" >> pConID)
>                <*> pExports << mustbe "where") `opt` ("Main",[])

> pExports :: Parser [Export]
> pExports = pParenTuple pExport `opt` []
> pExport :: Parser Export
> pExport =  pImport
>        +++ (symbol "module" >> pConID <@ Mod)

> pImpDecls :: Parser [(ConID,[Import])] 
> pImpDecls = some_offside pImpDecl `opt` []
> pImpDecl :: Parser (ConID,[Import])
> pImpDecl =   (symbol "import" >> may (symbol "qualified") >> pConID)  
>         <*> (may (symbol "as" >> pConID) >> pImpSpec)

> pImpSpec :: Parser [Import]
> pImpSpec = (pImpTuple+++ ((symbol "hiding") >> pImpTuple)
>            ) `opt` []

> pImpTuple :: Parser [Import]
> pImpTuple = pParenTuple pImport

> pImport :: Parser Import
> pImport =  (pVarID <@ Plain)
>        +++ ((pConID <*> pParenthesized 
>                          (   symbol ".." <@- []
>                          +++ pCommaList (pConID+++pVarID)
>                          )
>             ) <@ uncurry Subs)
>        +++ ((pParenthesized infixcon) <@ Plain)
>        +++ ((pParenthesized infixop) <@ Plain)
>        +++ (pConID <@ Plain)

> pParenTuple :: Parser a -> Parser [a]
> pParenTuple p = pParenthesized (pCommaList p `opt` [])

> may :: Parser a -> Parser a
> may p = p `opt` undefined

\end{verbatim}
%
\section{Equations}
Definitions have no {\tt where} part.
\begin{verbatim}

> pEqns :: Parser [Eqn]
> pEqns = some_offside pEqn

> pEqn :: Parser Eqn
> pEqn = pDataDef+++ pPolytypic+++ pVarBind+++ pExplType+++ pInfix

> pInfix :: Parser Eqn
> pInfix = do	ass <- symbol "infix" <@- NonAssoc
>			+++ symbol "infixl" <@- LeftAssoc
>			+++ symbol "infixr" <@- RightAssoc
>		f <- opt number 9
>		ops <- pCommaList (infixop +++ pBackQuoted (pConID +++ pVarID))
>		return $ InfixDecl ass f ops

> pVarBind :: Parser Eqn
> pVarBind = (pLeft << mustbe "=") >>= \(name,pats)->
>             pExpr <@ VarBind name noType pats

> pLeft :: Parser (String,[Expr])
> pLeft = pExpr >>= \expr -> 
>         let (f:ps) = spineWalk expr 
>         in case f of
>              Con n -> return (n,ps) 
>              Var n -> return (n,ps)
>              _     -> mZero 

\end{verbatim}
Only variables and constructors are allowed as the head of a left hand
side. 
\begin{verbatim}

> pDataDef :: Parser Eqn
> pDataDef 
>   = (symbol "data" +++ symbol "newtype") >> pConID >>= \tyCon -> 
>     many pVarID             >>= \vars  -> 
>     mustbe "=" >> 
>        (pDataDefAlt `sepby` symbol "|") >>= \alts -> 
>     (pDeriving `opt` []) <@
>     DataDef tyCon vars alts

> pDataDefAlt :: Parser (ConID,[Type])
> pDataDefAlt
>   = (pType2 >>= \a-> infixcon >>= \c-> pType2 >>= \b-> return (c,[a,b]))
>     +++ (pConID <*> many pType3)

> pDeriving :: Parser [ConID]
> pDeriving 
>   = symbol "deriving" >> 
>     (   pConID <@ (:[]) 
>     +++ pParenthesized (pCommaList pConID `opt` []))


> pExplType :: Parser Eqn
> pExplType = liftop ExplType 
>                    (pCommaList (pVarID+++ pParenthesized infixop))
>                    (symbol "::" >> pType0)

> pPolytypic :: Parser Eqn
> pPolytypic
>   = symbol "polytypic" >> pVarID    >>= \name -> 
>     mustbe "::"        >> pType0    >>= \tp   -> 
>     mustbe "="         >> pPolyBody >>= \(fvar,alts) ->
>     return (Polytypic name tp fvar alts)

Work in progress

> pClass :: Parser Eqn
> pClass = do
>               symbol "class"
>               let ctx = ("Foo", [TVar "t"])
>               return $ Class [] ctx []

\end{verbatim}
Some simple hungry expressions should be allowed before the case
expression. It should be distriduted into all the case alternatives.
Currently this is done for Lambda expressions only.
\begin{verbatim}

> pPolyBody :: Parser (QType,[(QType,Expr)])
> pPolyBody = 
>     (many pLambdaLeft <@ cmp << mustbe "case") >>= \lam->
>     (pVarID <@ mktype        << mustbe "of"  ) >>= \fvar -> 
>     some_offside pPolytypicAlt >>= \alts -> 
>     return (fvar,map (mapSnd lam) alts)
>  where mktype c = []:=>TVar c
>        cmp = foldr (.) id

> pPolytypicAlt :: Parser (QType,Expr)
> pPolytypicAlt
>   = (pFunc << symbol "->") >>= \tp   -> 
>     pExpr                  >>= \expr -> 
>     return ([]:=>tp, expr)

> pFunc :: Parser Func
> pFunc = constrdef <@ mkConApp
>    where mkConApp = foldl1 (:@@:)

> constrdef :: Parser [Type]
> constrdef =  pTypeVar <@ (:[]) 
>          +++ ((pConID <@ TCon) <:*> (many pType3))
>          +++ (pType3       >>= \a -> 
>               infixfunccon >>= \c -> 
>               pType3       >>= \b -> 
>               return (c:a:b:[]))

> infixfunccon :: Parser Func
> infixfunccon  = strip (sat (`elem` "+*@>") <@ (TCon.(:[])))

> infixcon :: Parser ConID
> infixcon = strip (lit ':' <:*> many (sat isOpChar)) 
>               <| (`notElem` specialops)

\end{verbatim}
\section{Expressions}
Parse an expression; if it is explicitly typed, return the typed
expression, otherwise return just the expession.

\begin{tabular}{rcl}
  expr & ::= & opexpr [ '::' type0 ] \\
opexpr & ::= & pfxexpr | opexpr1 | ... \\
pfxexpr& ::= & ['-'] appexpr \\
appexpr& ::= & atom .... atom \\
atom   & ::= & exprvar | exprcon | lambda | literal | \\
       &     & wildcard | case | letrec | exprparen \\
\end{tabular}

This implementation is {\em very} inefficient.
\begin{verbatim}

> pExpr,opexpr,pfxexpr,nappexpr,appexpr,pAtomic :: Parser Expr
> pExpr  
>   = opexpr  >>= \e -> 
>     (symbol "::" >> pType0 <@ Typed e)
>        `opt` e

> opexpr    = pfxexpr
>            `chainl` ops 9 
>            `chainr` ops 8 
>            `chainr` ops 7
>            `chainl` ops 6 
>            `chainl` ops 5 
>            `chainr` ops 4 
>            `chainr` ops 3 
>            `chainr` ops 2 
>            `chainr` ops 1 
>            `chainr` ops 0
>            where ops n = (pOps!!n) <@ \op-> (:@:) . (:@:) op 

 
> {-
> isConstructor :: ConID -> Bool
> isConstructor (x:_) = isUpper x || x == ':'
> isConstructor []    = error "Parser.isConstructor: impossible: empty constructor"
> -}

> pfxexpr   = nappexpr+++ appexpr
 
> nappexpr  = symbol "-" >> fMap ((Var "negate") :@:) appexpr 
 
> appexpr   = pAtomic `chainl` return (:@:)

> isOpChar :: Char -> Bool
> isOpChar a    = a `elem` ":!#$%&*+./<=>?@\\^|-" 
> pOps :: [Parser (Expr' a)]
> pOps = [ var "$"                                       -- 0 
>        , var "||"                                      -- 1
>        , var "&&"                                      -- 2
>        , pBackQuoted ((var "elem")+++ (var "notElem")) -- 3
>       +++ (var "==")
>       +++ (var "/=")
>       +++ (var "<" )
>       +++ (var "<=")
>       +++ (var ">")
>       +++ (var ">=")
>        , (var "++")                                    -- 4
>       +++ (con ":")                                    
>       +++ (var "\\\\")                                 
>        , (var "+")                                     -- 5
>       +++ (var "-")
>        , (var "/")                                     -- 6
>       +++ (var "*")
>       +++ pBackQuoted ((var "div")+++ 
>                    (var "rem")+++ (var "mod"))
>        , var "^"                                       -- 7
>        , var "."                                       -- 8
>        , var "!!"                                      -- 9
>       +++ (pBackQuoted pVarID <@ Var)
>       +++ (infixcon' <@ Con+++ infixop' <@ Var)
>        ]
>  where con s = symbol s <@ Con
>        var s = symbol s <@ Var

> infixop'  :: Parser String
> infixop'  = infixop  <| (`notElem` preludeops)
                          
> infixcon'  :: Parser String
> infixcon' = infixcon <| (`notElem` preludecons)

> -- infix operators, including infix constructors but not `op`s
> infixop :: Parser String
> infixop = strip (some (sat isOpChar)) 
>               <| (`notElem` specialops)

> specialops :: [String]
> specialops = [ "..", "::", "=", "\\", "|", 
>                "<-", "->", "@", "~", "=>" ]

> preludeops :: [String]
> preludeops = [ "$" , "||" , "&&" , "elem" , "notElem" , "==" , "/=",
>                "<" , "<=", ">", ">=", "++", ":", "\\\\", "+" , "-",
>                "/", "*", "div", "rem", "^", ".", "!!"
>              ]

> preludecons :: [String]
> preludecons = [":"]

\end{verbatim}
Operator sections are not yet handled but they could be introduced
into pExprTuple.

The element of the unit type - \verb|()| - is represented by
\verb|()|.
\begin{verbatim}

> pExprTuple :: Parser Expr
> pExprTuple = fMap Var infixop+++ pTuple pExpr mktuple
>   where
>     mktuple xs = foldl (:@:) (Con (tupleConstructor n)) xs
>       where n = length xs

> pAtomic = pCase
>       +++ pIf
>       +++ pLetrec
>       +++ pExprVar
>       +++ pExprCon
>       +++ pLambda
>       +++ pLiteral
>       +++ pWildCard
>       +++ pParenthesized pExprTuple
> 
> pExprVar, pExprCon :: Parser (Expr' a)
> pExprVar = fMap Var pVarID
> pExprCon = fMap Con $
>                  pConID
>              +++ pTupleCon   -- () (,) (,,) ...

\end{verbatim}
Lambda expressions are currently only allowing one argument. The
choice that it should be \verb|pAtomic| is not final. There should be
a parser specifically for patterns: \verb|pPat|. 
\begin{verbatim}
 
> pLambdaLeft :: Parser (Expr -> Expr)
> pLambdaLeft = ( (symbol "\\" >> args) << mustbe "->") <@ mkLambda
>   where args = some pAtomic
>         mkLambda = cmp . map Lambda
>         cmp = foldr (.) id

> pLambda :: Parser Expr
> pLambda = liftop ($) pLambdaLeft pExpr

> pWildCard :: Parser Expr
> pWildCard = symbol "_"  <@- WildCard

\end{verbatim}
Guards in lambda- or case- expressions are not parsed.
In \verb|(1)| \verb|pExpr| is too general.
\begin{verbatim}
 
> pCase :: Parser Expr
> pCase = liftop Case 
>                (symbol "case" >> pExpr)
>                (mustbe "of" >> some_offside pAlt)
>   where pAlt = pExpr <*> (symbol "->" >> pExpr)

> pIf :: Parser Expr
> pIf = ( (symbol "if"   >> pExpr) <*>
>         (mustbe "then" >> pExpr) <*>
>         (mustbe "else" >> pExpr) )
>       <@ if2case

> if2case :: (Expr,(Expr,Expr)) -> Expr
> if2case (b,(t,f)) = Case b [(Con "True",t),(WildCard,f)] 

> pLetrec :: Parser Expr
> pLetrec = liftop Letrec 
>             (symbol "let" >> pEqns <@ (:[]))
>             (mustbe "in"  >> pExpr)

> pTuple :: Parser a -> ([a] -> a) -> Parser a
> pTuple p tpl = (pCommaList p `opt` []) <@ f
>   where
>     f []  = tpl [] 
>     f [x] = x      
>     f xs  = tpl xs 

\end{verbatim}

When parsing tuples, a "one-tuple" is treated as just a parenthesized
expression.

\subsection{Literals}
\begin{verbatim}

> pLiteral :: Parser Expr
> pLiteral  = ( ( pNumber+++
>                 (pCharLit <@ CharLit)+++   
>                 (pBoolLit <@ BoolLit)+++ 
>                 (pStrLit  <@ StrLit ) ) <@ Literal )+++
>             pListLit 


> pRawNumber :: Parser (String,Maybe String)
> pRawNumber = strip (some digit <*> optional (lit '.' >> some digit))

> pNumber :: Parser Literal
> pNumber = pRawNumber <@ cookNum

> cookNum :: (String, Maybe String) -> Literal
> cookNum (fore, Just aft) = FloatLit (read (fore++'.':aft))
> cookNum (fore, Nothing ) = IntLit   (read fore)

> pListLit :: Parser Expr
> pListLit = pBracketed (pCommaList pExpr `opt` []) <@ list2expr

> pStrLit :: Parser String
> pStrLit = pDoubleQuoted (many (sat (/='"')))

> list2expr :: [Expr] -> Expr
> list2expr = foldr (\e1 e2 -> Con ":" :@: e1 :@: e2) (Con listConstructor)

> pCharLit :: Parser Char
> pCharLit = (lit '\'' >> pChar) << mustbe "'"

> pBoolLit :: Parser Bool
> pBoolLit = (symbol "True" <@- True)+++ (symbol "False" <@- False)

> pChar  :: Parser Char
> pChar =   (lit '\\' >> lit '\'') -- an escaped '
>        +++ item

\end{verbatim}

These string and character literal parsers do not allow special
characters.  This could be solved using {\tt reads :: Read a => String
-> [(a,String)]} if it can be transformed into a Parser.

\section{Types}
The list type constructor \verb|[]| is represented by \verb|TCon "[]"|
and a 3-tuple is represented by \verb|TCon "(,,)"|. A 1-tuple is just
a parenthesized expression.

To parse a qualified type ({\tt pType0}) we use the fact that the
context looks like a type followed by an arrow ``\verb|=>|''. This
means that if we can transform the abstract syntax of types to that of
a context, we can start parsing a type and --- if it is followed by an
arrow --- transform it to a context and parse the rest.

Qualified types are parsed by \texttt{pType0}, unqualified types by
\texttt{pType1} which is a chain of \texttt{pType2}s with arrows in
between. A \texttt{pType2} is an application of \texttt{pType3}s

\begin{verbatim}

> type2context :: Type -> Parser [Qualifier Type]
> type2context = check . map spineWalkType . untuple 
>   where check      = handle . mapl out
>         handle     = maybe (failEM msg) return
>         out (TCon "Regular":d:[]) = Just ("Poly",[TCon "FunctorOf" :@@: d])
>         out (TCon "Bifunctor":f:[]) = Just ("Poly",[f])
>         out (TCon t:ts) = Just (t,ts)
>         out _      = Nothing
>         msg = "Can't parse type context"
>         untuple t = case spineWalkType t of 
>                       (TCon tup:ts) | isTupleCon tup -> ts
>                       _                              -> [t]

> pType0 :: Parser QType
> pType0 = pType1 >>= \t->
>          (symbol "=>" >> 
>           liftop (:=>) (type2context t) pType1) `opt` qualify t 

liftop (:=>) pContext pType1

> pType1 :: Parser Type
> pType1 = pType2 `chainr` (symbol "->" <@- (-=>)) 
>                 `chainl` (infixfunccon <@ \op f g-> op :@@: f :@@: g)
 
> pType2 :: Parser Type
> pType2 = pType3 `chainl` return (:@@:)
 
> pType3 :: Parser Type
> pType3 = pTypeVar
>      +++ pTypeCon
>      +++ pBracketed pTypeList
>      +++ pParenthesized pTypeTuple
 
***Hack addition to allow _parsing_ of existential types. (No type checking.)

> pTypeVar :: Parser Type
> pTypeVar = fMap TVar (pVarID+++ sat (=='?') <:*> pVarID)

From the Haskell report:
  gtycon -> qtycon
          | () (unit type)
          | [] (list constructor)
          | (->) (function constructor)
          | (,{,}) (tupling constructors)

> pTypeCon :: Parser Type
> pTypeCon = fMap (expandTypeSynonyms . TCon) $
>              pConID 
>          +++ symbol listConstructor 
>          +++ symbol "(->)" <@- functionConstructor
>          +++ pTupleCon

> expandTypeSynonyms :: Type -> Type
> expandTypeSynonyms (TCon "String") = 
>   TCon listConstructor :@@: TCon "Char"
> expandTypeSynonyms c               = c

*** Hack to allow String as a predefined type synonym for [Char]

> pTupleCon :: Parser ConID
> pTupleCon = pParenthesized (many (lit ',')) <@ (tupleConstructor . tupNum)
>   where tupNum "" = 0
>         tupNum s  = length s + 1

> pTypeList :: Parser Type
> pTypeList = pType1 <@ ((TCon listConstructor):@@:) 
 
> pTypeTuple :: Parser Type
> pTypeTuple = pTuple pType1 f
>   where
>     f xs = foldl (:@@:) (TCon (tupleConstructor n)) xs
>       where n = length xs

\end{verbatim}
\section{Variable and constructor names}
\begin{verbatim}

> pConID :: Parser ConID
> pConID = strip (sat isUpper <:*> many (sat isVarChar))

> pVarID :: Parser VarID
> pVarID = strip (sat isLower <:*> many (sat isVarChar)) 
>              <| (`notElem` keywords)
 
> isVarChar :: Char -> Bool
> isVarChar c = isAlpha c || isDigit c || c `elem` "_'"
 
> keywords :: [VarID]
> keywords = [ "case", "of", "let", "in", "if", "then", "else",
>              "data", "polytypic", "deriving", "where", "class",
>                                       "instance"]

\end{verbatim}
***
Reserved identifiers in Haskell 1.3: {\tt case | class | data |
  default | deriving | do | else | if | import | in | infix | infixl |
  infixr | instance | let | module | newtype | of | then | type |
  where }
\section{Extra combinators}
Function \texttt{pPack'} does not allow space after leading symbol.
\begin{verbatim}

> pPack :: String -> Parser a -> String -> Parser a
> pPack  a p  b  = (symbol a >> p ) << mustbe b
> pPack' :: String -> Parser a -> String -> Parser a
> pPack' a p' b  = (string a >> p') << mustbe b
 
> pDoubleQuoted :: Parser a -> Parser a
> pDoubleQuoted  p' = pPack' "\"" p' "\"" 
> pBackQuoted :: Parser a -> Parser a
> pBackQuoted    p' = pPack' "`"  p' "`"

> pBracketed :: Parser a -> Parser a
> pBracketed     p = pPack "[" p "]"
> pParenthesized :: Parser a -> Parser a
> pParenthesized p = pPack "(" p ")"

> pCommaList :: Parser a -> Parser [a]
> pCommaList p = p `sepby` symbol ","

\end{verbatim}

\subsection{Searching for explicit types and \texttt{data} declarations}

The idea is to scan a Haskell file for type and data declarations but
ignoring any other definitions. We use the hack "pAnyLine" to parse
any line that does not look like a type or a data, but this can be
fooled by various Haskell constructs like x::a on a single line in a
where, or perhaps by nested comments. The alternative would be to use
the full parser, but this would force the file to conform to the
limited syntax of PolyP's Haskell. (And it would be inefficient, but
this is only a secondary issue.)

\begin{verbatim}

> pMaybeExplType :: Parser (Maybe Eqn)
> pMaybeExplType = (pDataDef+++ pExplType) <@ Just 
>               +++ pAnyLine

> pAnyLine :: Parser (Maybe Eqn)
> pAnyLine = many (sat (/='\n')) >> sat (=='\n')
>              <@- Nothing

> pTypeFile :: Parser [Eqn]
> pTypeFile = pModuleHead >>  -- throw away the head
>             pImpDecls >>    -- and the imports
>             some_offside pMaybeExplType `opt` [] 
>               <@ Maybe.catMaybes

\end{verbatim}
