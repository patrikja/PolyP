\chapter{The parser}

The basic idea for all these parsers is that they should {\em end} by
eating white space (and comments) and assume that the first character
they receive be non-space.

\begin{verbatim}

> module Parser(parse,pModule,pType0,pType1) where

> import Char(isUpper,isLower,isAlphanum,isDigit)
> import MyPrelude(mapSnd)
> import MonadLibrary((<:*>),(<*>),(<@),(<@-),(<<),liftop,
>                     mapl,ErrorMonad(failEM))
> import ParseLibrary(Parser,item,lit,sat,digit,opt,optional,
>                     some_offside,mustbe,symbol,sepby,
>                     chainl,chainr,spaces,number,
>                     many,some,strip, parse)
> import Grammar(Expr'(..),Eqn'(..),Type(..),Qualified(..),Literal(..),
>                Expr,Eqn,Func,QType,Qualifier,VarID,ConID,
>                qualify,noType,spineWalk,spineWalkType,(-=>),
>                tupleConstructor,listConstructor,isTupleCon,
>		 functionConstructor)

\end{verbatim}
The parser is not in good shape and uses far too many reductions
right now. (Plus it's UGLY!)

\section{Module}
The module parser accepts but ignores the module head, exports and imports.
%
\begin{verbatim}

> pModule :: Parser [Eqn]
> pModule = pModule'

> pModule' = (pModuleHead `opt` ("Main",["main"])) >> 
>            pImpDecls >> 
>            pEqns

> pModuleHead =  (symbol "module" >> pConID)
>             <*> pExports << mustbe "where"

> pExports = pParenTuple pExport `opt` []
> pExport =  pImport
>         ++ (symbol "module" >> pConID)

> pImpDecls = some_offside pImpDecl `opt` []
> pImpDecl =   (symbol "import" >> may (symbol "qualified") >> pConID)  
>         <*> (may (symbol "as" >> pConID) >> pImpSpec)

> pImpSpec = (pImpTuple ++ ((symbol "hiding") >> pImpTuple)
>            ) `opt` []

> pImpTuple = pParenTuple pImport

> pImport =   pVarID 
>         ++ (pConID << 
>                  (pParenthesized 
>                     (   symbol ".." <@- []
>                      ++ pCommaList (pConID++pVarID)
>                     )
>                  ) `opt` []
>            )

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
> pEqn = pDataDef ++ pPolytypic ++ pVarBind ++ pExplType
 
> pVarBind :: Parser Eqn
> pVarBind = (pLeft << mustbe "=") >>= \(name,pats)->
>             pExpr <@ VarBind name noType pats

> pLeft :: Parser (String,[Expr])
> pLeft = pExpr >>= \expr -> 
>         let (f:ps) = spineWalk expr 
>         in case f of
>              Con n -> return (n,ps) 
>              Var n -> return (n,ps)
>              _     -> zero 

\end{verbatim}
Only variables and constructors are allowed as the head of a left hand
side. 
\begin{verbatim}

> pDataDef :: Parser Eqn
> pDataDef 
>   = symbol "data" >> pConID >>= \tyCon -> 
>     many pVarID             >>= \vars  -> 
>     mustbe "=" >> 
>        (pDataDefAlt `sepby` symbol "|") >>= \alts -> 
>     (pDeriving `opt` []) <@
>     DataDef tyCon vars alts

> pDataDefAlt :: Parser (ConID,[Type])
> pDataDefAlt
>   = pConID <*> many pType3 

> pDeriving :: Parser [ConID]
> pDeriving 
>   = symbol "deriving" >> 
>     (   pConID <@ (:[]) 
>      ++ pParenthesized (pCommaList pConID `opt` []))


> pExplType :: Parser Eqn
> pExplType = liftop ExplType 
>                    (pCommaList (pVarID ++ pParenthesized infixop))
>                    (symbol "::" >> pType0)

> pPolytypic :: Parser Eqn
> pPolytypic
>   = symbol "polytypic" >> pVarID    >>= \name -> 
>     mustbe "::"        >> pType0    >>= \tp   -> 
>     mustbe "="         >> pPolyBody >>= \(fvar,alts) ->
>     return (Polytypic name tp fvar alts)

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
>           ++ ((pConID <@ TCon) <:*> (many pType3))
>           ++ (pType3       >>= \a -> 
>               infixfunccon >>= \c -> 
>               pType3       >>= \b -> 
>               return (c:a:b:[]))

> infixfunccon :: Parser Func
> infixfunccon  = strip (sat (`elem` "+*@") <@ (TCon.(:[])))

> infixcon :: Parser ConID
> infixcon = strip (lit ':' <:*> many (sat isOpChar)) >>= \ys -> 
>                   if ys `elem` specialops then zero
>                   else return ys

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

 
> isConstructor :: ConID -> Bool
> isConstructor (x:_) = isUpper x || x == ':'
> isConstructor []    = error "Parser: isConstructor: impossible: empty constructor"

> pfxexpr   = nappexpr ++ appexpr
 
> nappexpr  = symbol "-" >> map ((Var "negate") :@:) appexpr 
 
> appexpr   = pAtomic`chainl` return (:@:)

> isOpChar a    = a `elem` ":!#$%&*+./<=>?@\\^|-" 
> pOps = [ var "$" 
>        , var "||" 
>        , var "&&"
>        , pBackQuoted ((var "elem") ++ (var "notElem"))
>        ++ (var "==")
>        ++ (var "/=")
>        ++ (var "<" )
>        ++ (var "<=")
>        ++ (var ">")
>        ++ (var ">=")
>        , (var "++")
>        ++ (con ":")
>        ++ (var "\\\\")
>        , (var "+")
>        ++ (var "-")
>        , (var "/")
>        ++ (var "*")
>        ++ pBackQuoted ((var "div") ++ 
>                    (var "rem") ++ (var "mod"))
>        , var "^"
>        , var "."
>        , var "!!"
>        ++ (pBackQuoted pVarID <@ Var)
>        ++ (infixcon <@ Con ++ infixop <@ Var)]
>  where con s = symbol s <@ Con
>        var s = symbol s <@ Var

> infixop = strip (some (sat isOpChar)) >>= \xs -> 
>           if xs `elem` specialops then zero
>           else return xs
> specialops :: [String]
> specialops = [ "..", "::", "=", "\\", "|", 
>                "<-", "->", "@", "~", "=>" ]

\end{verbatim}
Operator sections are not yet handled but they could be introduced
into pExprTuple.

The element of the unit type - \verb|()| - is represented by
\verb|()|.
\begin{verbatim}

> pExprTuple = map Var infixop ++ pTuple pExpr mktuple
>   where
>     mktuple xs = foldl (:@:) (Con (tupleConstructor n)) xs
>       where n = length xs

> pAtomic = pCase
>        ++ pIf
>        ++ pLetrec
>        ++ pExprVar
>        ++ pExprCon
>        ++ pLambda
>        ++ pLiteral
>        ++ pWildCard
>        ++ pParenthesized pExprTuple
> 
> pExprVar = map Var pVarID
> pExprCon = map Con $
>                  pConID
>               ++ pTupleCon   -- () (,) (,,) ...

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
\subsection{Literals}
\begin{verbatim}

> pLiteral :: Parser Expr
> pLiteral  = ( ( pNumber ++
>                 (pCharLit <@ CharLit) ++   
>                 (pBoolLit <@ BoolLit) ++ 
>                 (pStrLit  <@ StrLit ) ) <@ Literal ) ++
>             pListLit 


> pRawNumber :: Parser (String,Maybe String)
> pRawNumber = strip (some digit <*> optional (lit '.' >> some digit))

> pNumber :: Parser Literal
> pNumber = pRawNumber <@ cookNum

> cookNum :: (String, Maybe String) -> Literal
> cookNum (fore, Just aft) = FloatLit (read (fore++'.':aft))
> cookNum (fore, Nothing ) = IntLit (read fore)

> pListLit :: Parser Expr
> pListLit = pBracketed (pCommaList pExpr `opt` []) <@ list2expr

> pStrLit :: Parser String
> pStrLit = pPack "\"" (many (sat (/='"'))) "\"" 

> list2expr :: [Expr] -> Expr
> list2expr = foldr (\e1 e2 -> Con ":" :@: e1 :@: e2) (Con listConstructor)

> pCharLit :: Parser Char
> pCharLit = (lit '\'' >> pChar) << mustbe "'"

> pBoolLit :: Parser Bool
> pBoolLit = (symbol "True" <@- True) ++ (symbol "False" <@- False)

> pChar  :: Parser Char
> pChar =   (lit '\\' >> lit '\'') -- an escaped '
>         ++ item

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

\begin{verbatim}

> type2context :: Type -> Parser [Qualifier Type]
> type2context = check . map spineWalkType . untuple 
>   where check      = handle . mapl out
>         handle     = maybe (failEM msg) return
>         out (TCon t:ts) = Just (t,ts)
>         out _      = Nothing
>         msg = "Can't parse type context"
>         untuple t = case spineWalkType t of 
>                       (TCon tup:ts) | isTupleCon tup -> ts
>                       _                              -> [t]

> pType0 = pType1 >>= \t->
>          (symbol "=>" >> 
>           liftop (:=>) (type2context t) pType1) `opt` qualify t 

liftop (:=>) pContext pType1

> pType1 = pType2 `chainr` (symbol "->" <@- (-=>))
 
> pType2 = pType3 `chainl` return (:@@:)
 
> pType3 = pTypeVar
>       ++ pTypeCon
>       ++ pBracketed pTypeList
>       ++ pParenthesized pTypeTuple
 
***Hack addition to allow _parsing_ of existential types. (No type checking.)

> pTypeVar = map TVar (pVarID ++ sat (=='?') <:*> pVarID)

From the Haskell report:
  gtycon -> qtycon
	  | () (unit type)
	  | [] (list constructor)
	  | (->) (function constructor)
	  | (,{,}) (tupling constructors)

> pTypeCon = map TCon $
>              pConID
>           ++ symbol listConstructor 
>           ++ symbol "(->)" <@- functionConstructor
>           ++ pTupleCon

> pTupleCon :: Parser ConID
> pTupleCon = pParenthesized (many (lit ',')) <@ (tupleConstructor . tupNum)
>   where tupNum "" = 0
>         tupNum s  = length s + 1

> pTypeList = pType1 <@ ((TCon listConstructor):@@:) 
 
> pTypeTuple = pTuple pType1 f
>   where
>     f xs = foldl (:@@:) (TCon (tupleConstructor n)) xs
>       where n = length xs

\end{verbatim}
\section{Variable and constructor names}
\begin{verbatim}

> pConID = strip (sat isUpper <:*> many (sat isVarChar))

> pVarID = strip (sat isLower <:*> many (sat isVarChar)) >>= \ys -> 
>                   if ys `elem` keywords then zero
>                   else return ys
 
> isVarChar c = isAlphanum c || c `elem` "_'"
 
> keywords = [ "case", "of", "let", "in", "if", "then", "else",
>              "data", "polytypic", "deriving"]

\end{verbatim}
Reserved identifiers in Haskell 1.3: {\tt case | class | data |
  default | deriving | do | else | if | import | in | infix | infixl |
  infixr | instance | let | module | newtype | of | then | type |
  where }
\section{Extra combinators}
\begin{verbatim}

> pPack a p b  = (symbol a >> p) << mustbe b
 
> pBracketed     p = pPack "[" p "]"
> pParenthesized p = pPack "(" p ")"
> pBackQuoted    p = pPack "`" p "`"

> pCommaList p = p `sepby` symbol ","

\end{verbatim}
