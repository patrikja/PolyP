\chapter{Pretty printer}
\begin{verbatim}

> module PrettyPrinter(module PrettyPrinter,module PrettyPrintExtra,
>                      module Grammar) where
> import Char(isAlpha)
> import PrettyPrintExtra(Pretty(..),ppVerticalList,ppCommaList,
>                         ppTuple,ppParentheses,ppApp,ppPackedList,showDoc,
>                         (<>),($$),nest,text,Doc,sep)
> import Grammar

\end{verbatim}
\section{Instances}

We want instances for Pretty to be able to Show all program
objects. Unfortunately the following is not legal:
\begin{verbatim}
instance Pretty a => Show a where
  showsPrec _ = (++) . showDoc . pretty
\end{verbatim}
The normal Haskell way around is to order the classes, and give a
default instance, but we cannot change the class Show to have Pretty
as a superclass as Show is in the Haskell prelude. Another way around
is to give a number if instance declarations like 
\begin{verbatim}
instance Pretty a => Show (Eqn' a) where ...
\end{verbatim}
A third way is to abandon show and use pshow = showDoc . pretty instead.
\begin{verbatim}

> pshow :: Pretty a => a -> String
> pshow = showDoc . pretty

> instance Pretty a => Pretty (Eqn' a) where
>   pretty = prEqn

> instance Pretty a => Show   (Eqn' a) where
>   showsPrec _ = (++) . showDoc . pretty

> instance Pretty a => Pretty (Expr' a) where
>   pretty = prExpr

> instance Pretty Char where
>   pretty c = text [c]
> instance Pretty Literal where
>   pretty = prLit

> instance Pretty a => Pretty [a] where
>   pretty = sep . map pretty

> instance Pretty Type where 
>   pretty = prType

> instance Show Type where
>   showsPrec _ = (++) . showDoc . pretty

> instance (Typelike t, Pretty t) => Pretty (Qualified t) where
>   pretty = prQualified

> instance (Typelike t, Pretty t) => Show   (Qualified t) where
>   showsPrec _ = (++) . showDoc . pretty

> class Typelike t where
>   checkFOf         :: t -> Maybe t
>   isSimpleTypelike :: t -> Bool

> instance Typelike Type where
>   checkFOf (TCon "FunctorOf" :@@: d) = Just d
>   checkFOf _                         = Nothing
>   isSimpleTypelike = isSimpleType

\end{verbatim}
The class \texttt{Typelike} is only used to get past the Haskell 1.4
restriction that forbids instances for \texttt{Qualified Type}.

\section{Equations}
\begin{verbatim}

> prEqn :: Pretty a => Eqn' a -> Doc
> prEqn (VarBind name mt pats body) 
>   =  maybe id (prTypeFirst name) mt $
>      prApp (Var name : pats)
>   <> text " = " 
>   <> prExpr body

> prEqn (DataDef tyCon vars (alt:alts) ds)
>   =  text "data "
>   <> ( sep ( ppApp (map text (tyCon : vars))
>            : prAlt '=' alt
>            : map (prAlt '|') alts
>            ++ [prDeriving ds])
>      )

> prEqn (Polytypic name tp functorVar alts) 
>   =  (text ("polytypic " ++ name ++ " :: ") <> pretty tp )
>   $$ (text "  = case " <> pretty functorVar <> text " of " )
>   $$ nest 6 (sep (map showAlt alts))
>   where
>     showAlt (f, rhs) = pretty f <> text " -> " <> prExpr rhs

> prEqn (Class preds def eqns)
>   = (text "class " <> prQ preds (context2type def) <> text " where")
>   $$ nest 2 (ppVerticalList eqns)

> prEqn (Instance preds def eqns)
>   = (text "instance " <> prQ preds (context2type def) <> text " where")
>   $$ nest 2 (ppVerticalList eqns)

> prEqn (ExplType vars tp)
>   = sep [ppCommaList (map text' vars) <> text " ::", nest 2 (pretty tp)]
>   where text' s | isOperatorName s = text ('(':s++")")
>                 | otherwise        = text s


> prEqn _ = error "PrettyPrinter.prEqn: not implemented"

> prTypeFirst :: Pretty t => VarID -> t -> Doc -> Doc
> prTypeFirst name t d = 
>       prEqn (ExplType [name] t)
>    $$ d

\end{verbatim}
The type is printed as a sanity check, and to avoid that the 
output Haskell code violates the monomorphism restriction.

\subsection{Substructures}
\begin{verbatim}

> prDeriving :: [ConID] -> Doc
> prDeriving [] = text ""
> prDeriving cs = text "deriving " <> ppTuple (map text cs)

> prPreds :: Pretty t => [Qualifier t] -> Doc
> prPreds [prd] = prPred prd
> prPreds preds = ppTuple (map prPred preds)

> prPred :: Pretty t => Qualifier t -> Doc
> prPred (cls, args) = text cls 
>                     <> text " " 
>                     <> (foldr1 (<>) (map ((<> (text " "))
>                                          . pretty
>                                          ) args))

> prAlt :: (Typelike t, Pretty t) => Char -> (ConID,[t]) -> Doc
> prAlt sepchar (constr, types)
>   =  text (sepchar : " ")
>   <> if isOperatorName constr 
>      then pretty (types!!0) <> text (" "++constr++" ") <> pretty (types!!1)
>      else text constr
>        <> if null types                                         
>   	    then text ""                                          
>   	    else ppPackedList " " (map prT types) "" " "

\end{verbatim}
\section{Expressions}
\begin{verbatim}

> prId :: Expr' t -> String -> Doc

> prId e n | isOperator e = ppParentheses (text n)
>          | otherwise    = text n

> prExpr :: Pretty a => Expr' a -> Doc
> prExpr e@(Var name) = prId e name
> prExpr e@(Con name) = prId e name

> prExpr e@(Lambda _ _) 
>     = sep [text "\\" <> ppApp (map prPat ps) <> text " ->" , nest 2 (prExpr body)]
>   where (ps,body) = lambdaWalk e

> prExpr (Literal lit) = pretty lit

> prExpr x@(_ :@: _) = prApp (spineWalk x) 

> prExpr (Case expr alts) 
>   =  (text "case " <> prExpr expr <> text " of")
>   $$ nest 2 (ppVerticalList (map prBranch alts))
>   where 
>     prBranch (pat, rhs) = sep [prPat pat <> text " ->", nest 2 (prExpr rhs)]

> prExpr WildCard = text "_"

> prExpr (Letrec eqnss expr)
>   = sep [ text "let " <> ppVerticalList (map ppVerticalList eqnss)
>         , text "in " <> prExpr expr
>         ]

> prExpr (Typed e t) 
>   = sep [prPat e <> text " ::", nest 2 (pretty t)]

> prApp :: Pretty t => [Expr' t] -> Doc
> prApp (fun:args)
>   | tupletest fun == n = ppTuple args
>   | isOperator fun     = prOperator fun args
>   | otherwise          = sep (prP fun : map (nest 2 . prP) args)
>   where
>     n = length args
> prApp [] = error "PrettyPrinter.prApp: impossible: nothing to apply"

> lambdaWalk :: Expr' t -> ([Pat' t],Expr' t)
> lambdaWalk (Lambda p e) = (p:ps,e')
>   where (ps,e') = lambdaWalk e
> lambdaWalk e = ([],e)

\end{verbatim}
\section{Patterns}
\begin{verbatim}

> prPat :: Pretty a => Pat' a -> Doc
> prPat = prP

\end{verbatim}
\section{Types}
\begin{verbatim}

> prQualified :: (Typelike t, Pretty t) => Qualified t -> Doc
> prQualified (cs:=>t) = prQ cs t
> 
> prQ :: (Typelike t, Pretty t) => [Qualifier t] -> t -> Doc
> prQ []  t = pretty t
> prQ [c] t = sep [prContext c   <> text " =>", nest 2 (pretty t)]
> prQ cs  t = sep [prContexts cs <> text " =>", nest 2 (pretty t)]

> prContexts :: (Typelike t, Pretty t) => [(String, [t])] -> Doc
> prContexts cs = ppTuple (map prContext cs)

> prContext :: (Typelike t, Pretty t) => (String, [t]) -> Doc
> prContext ("Poly",[f]) = case checkFOf f of
>                            Just d  -> prContext' ("Regular",[d])
>                            Nothing -> prContext' ("Bifunctor",[f])
> prContext p            = prContext' p

> prContext' :: (Typelike t, Pretty t) => (String, [t]) -> Doc
> prContext' (c,ts) =  
>   sep (text c : map (nest 2 . prT) ts)

> prType :: Type -> Doc
> prType (TVar v)                = text v
> prType (TCon c)                = text c
> prType (TCon c :@@: t) | c == listConstructor 
>                                = text "[" <> prType t <> text "]"
> prType x@(_ :@@: _) 
>   | tupletypetest fun == n     = ppTuple args
>   | isFunctionType fun && n==2 = prArrow (head args) (head (tail args))
>   | isTypeOp fun               = prTypeOp fun args
>   | otherwise                  = sep (prT fun : map (nest 2.prT) args)
>   where
>     (fun:args) = spineWalkType x
>     n = length args

> prT :: (Typelike t,Pretty t) => t -> Doc
> prT x = (if isSimpleTypelike x then id else ppParentheses) (pretty x)

> prArrow :: Type -> Type -> Doc
> prArrow r d = sep [ppleft r (prType r) <> text " ->", prType d] 
>   where
>     ppleft (c :@@: _ :@@: _) 
>        | isFunctionType c    = ppParentheses 
>     ppleft   _               = id

\end{verbatim}
\section{Literals}
\begin{verbatim}

> prLit :: Grammar.Literal -> Doc
> prLit (IntLit  n) = text (show n)
> prLit (FloatLit f)= text (show f)
> prLit (BoolLit b) = text (show b)
> prLit (CharLit c) = text (show c)
> prLit (StrLit s)  = text (show s)

\end{verbatim}
\section{Auxiliary functions}
\begin{verbatim}

> prP :: Pretty a => Expr' a -> Doc
> prP x = (if isSimple x then prExpr else ppParentheses) x

> prOperator :: Pretty a => Expr' a -> [Expr' a] -> Doc
> prOperator fun args 
>   | n >= 2 = let (a:b:cs) = map prP args 
>                  doc = sep [a <> text " " <> prOp fun,b]
>              in if null cs then doc
>                 else sep (text "(" <> doc <> text ") " : map (nest 2) cs)
>   | otherwise = sep (pretty fun : map (nest 2 . prP) args)
>   where
>     n = length args
>     prOp (Con op) = text op
>     prOp (Var op) = text op
>     prOp _        = error "PrettyPrinter.prOp: not an operator"

> prTypeOp :: Type -> [Type] -> Doc
> prTypeOp fun args 
>   | n >= 2 = let (a:b:cs) = args 
>              in sep (map prT (a:fun:b:cs))
>   | otherwise = sep (ppParentheses fun : map prT args)
>   where 
>     n = length args
    

> isSimple :: Expr' a -> Bool
> isSimple (Var _)      = True
> isSimple (Con _)      = True
> isSimple (Literal _)  = True
> isSimple WildCard     = True
> isSimple x | tupletest fun == length args
>                       = True
>   where (fun:args) = spineWalk x
> isSimple _            = False

> isSimpleType :: Type -> Bool
> isSimpleType (TVar _) = True
> isSimpleType (TCon _) = True
> isSimpleType (TCon c :@@: _) | c == listConstructor   
>                       = True
> isSimpleType t        = tupletypetest fun == length args
>   where (fun:args) = spineWalkType t

\end{verbatim}
Variables, constructors, tuple types and list types are considered simple 
and thus do not need to be parenthesized when used as type arguments.

\begin{verbatim}

> isOperator :: Expr' a -> Bool
> isOperator (Var x) = isOperatorName x
> isOperator (Con x) = isOperatorName x
> isOperator _       = False

> isTypeOp :: Type -> Bool
> isTypeOp (TVar x) = isOperatorName x
> isTypeOp (TCon x) = isOperatorName x
> isTypeOp _        = False

> isOperatorName :: String -> Bool
> isOperatorName ('(':_) = False 
> isOperatorName ('[':_) = False 
> isOperatorName (c  :_) = not (isAlpha c) 
> isOperatorName ""      = error "PrettyPrinter.isOperatorName: empty name"

\end{verbatim}
Gives the size of the tuple or -1 if no tuple. Assumes that the tuple
constructors are () (,) (,,) (,,,) ...
\begin{verbatim}

> tupletest :: Expr' a -> Int
> tupletest (Con ('(':xs)) = f (length xs)
>   where f 1 = 0
>         f n = n
> tupletest _ = -1

> tupletypetest :: Type -> Int
> tupletypetest (TCon ('(':xs)) =  f (length xs)
>   where f 1 = 0
>         f n = n
> tupletypetest _ = -1

\end{verbatim}
\section{Dependencies}
{\tt
\begin{tabular}{lll}
function& uses recursively & other uses\\
prEqn & prEqn, prExpr, prApp      & prPred, prPreds, prAlt, pretty(type)\\
prExpr& prExpr, prEqn, prApp, prP & pretty(type,Literal)\\
prApp & prP, prOperator           & tupletest, isOperator\\
prP   & prExpr                    & isSimple\\
prOperator&prExpr, prP            & \\
\end{tabular}
\\
\begin{tabular}{lll}
prType & prType, prT, prArrow, prTypeOp & isFunctionType,tupletypetest,isTypeOp\\
prT    & prType & isSimpleType\\
prArrow& prType & \\
prTypeOp & prT & \\
\end{tabular}
}

\section{To be done}

\begin{itemize}
\item Improve printing of datatype declarations: replace
  \texttt{ppParentheses} with \texttt{prT} in \texttt{prAlt}.
%
  This requires changes to a series of types as they will need a
  \texttt{Typelike t} context.
\end{itemize}
