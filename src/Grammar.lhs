\chapter{PolyP's Grammar}
\begin{verbatim}

> module Grammar where
> import MyPrelude(mapSnd)

> infixl 9 :@:
> infixl 9 :@@:
> infixr 9 -=>
> infix  4 :=>

\end{verbatim}
\section{Equations}
There are seven kinds of equations:
\begin{itemize}
\item Variable bindings (\verb|VarBind|) can appear both at top-level
  and in a \verb|let|-construct. They bind a variable to a body (which
  is an expression).
\item Polytypic variable bindings.
\item Data type definitions (\verb|DataDef|) can only appear at
  top-level. A data definition defines a new type and a set of
  functions (constructors) that build values of this new type.
\item Explicitly typed variables.
\item Type synonym declarations.
\item Class declarations.
\item Instance declarations.
\end{itemize}
(Currently, the three last constructs are not parsed, nor handled in
the type inference algorithm)

Modules

> data Module' t
>     = Module ConID [Export] [(ConID, [Import])] [Eqn' t]
>
> type Module = Module' QType

> data ImpExp = Plain ConID
>             | Mod ConID
>             | Subs ConID [ConID]
> type Export = ImpExp
> type Import = ImpExp

> data Associativity = NonAssoc | LeftAssoc | RightAssoc
>   deriving (Eq)

The datatype \verb|Eqn'| is mutually recursive with the type for
expressions as the expressions in the variable bindings can contain
let-expressions which in turn contains equations. The type parameter
\verb|t| is used in \verb|Expr'| to denote the type of types as there
will be a need for different representation for types later. The {\tt
  Maybe} in {\tt VarBind} is used for a possible explicit type.
(Dependency analysis will combine {\tt ExplType} with the
corresponding {\tt VarBind}s.
\begin{verbatim}

> data Eqn' t
>    = VarBind VarID (Maybe t) [Pat' t] (Expr' t)
>    | Polytypic VarID t t [(t, Expr' t)]
>    | DataDef ConID [VarID] [(ConID, [Type])]   [ConID]
>    | ExplType [VarID] t
>    | InfixDecl Associativity Int [VarID]

>    | TypeSyn ConID [VarID] Type
>    | Class    [Context] Context [Eqn' t] 
>    | Instance [Context] Context [Eqn' t]

>    deriving (Eq)

> type Func = Type

\end{verbatim}
(It is not completely clear yet if \verb|t| should be used in more
places.)

A future enhancement would be to extend the \verb|VarBind| to
\verb|PatBind| that just takes a pattern and an expression thus
allowing definitions like {\tt (a,b) = f 3} where f is a function
returning a pair.

Only VarBind and ExplType are allowed in letrecs.
\section{Expressions, patterns, types and kinds}
Expressions are similar to patterns and types are similar to kinds in
many ways.  So we use one data type for each pair. An advantage is
that a lot of code can be shared (e.g. \verb|fold|). A problem with
this approach is that the pairs are not completely the same. Patterns
can use everything but $\lambda$-abstractions, \verb|case| and
\verb|letrec| expressions.  Finally, expressions can't use the
\verb|WildCard| constructor (maybe in expressions \verb|WildCard|
could denote \verb|undefined|).  (Patterns are combinations of
variables, constants, applications, literals and wildcards. )
\begin{verbatim}

> data Expr' t
>    = Var VarID 
>    | Con ConID 
>    | (Expr' t) :@: (Expr' t)
>    | Lambda (Pat' t) (Expr' t)
>    | Literal Literal
>    | WildCard
>    | Case (Expr' t) [(Pat' t, Expr' t)]
>    | Letrec [[Eqn' t]] (Expr' t)
>    | Typed (Expr' t) t

>    deriving (Eq)

> type Pat' t = Expr' t

> data Type
>    = TVar VarID
>    | TCon ConID
>    | Type :@@: Type    
>    deriving (Eq,Ord)

> type Kind = Type

\end{verbatim}
Normally (that is, everywhere except during type inference)
expressions, patterns and equations use the type \verb|QType| to
represent the types. A program consists of a list of datatype
definitions followed by a list (ordered by dependencies) of blocks of
mutually recursive definitions.
\begin{verbatim}

> type Expr    = Expr' QType
> type Pat     = Pat'  QType
> type Eqn     = Eqn'  QType
> type PrgEqns = ([Eqn],[Eqn],[[Eqn]])

> data Qualified t = [Qualifier t] :=> t 
>                    deriving (Eq)
> deQualify :: Qualified t -> t
> qualify :: t -> Qualified t 

> noType :: Maybe QType
> noType = Nothing

> instance Functor Qualified where
>   __FMAPNAME__ f (qs:=>t) = map (mapSnd (map f)) qs :=> f t

> context2type :: Context -> Type
> type Qualifier t = (ConID,[t])
> type Context = Qualifier Type

> type QType = Qualified Type

\end{verbatim}
Expressions labelled with types can be expressed with elements of
\verb|TExpr| where every second level is the \verb|Typed| constructor.
\begin{verbatim}

> type TExpr   = Expr' QType
> type TEqn    = Eqn'  QType
> type PrgTEqns = ([Eqn],[Eqn],[[TEqn]])

\end{verbatim}
\section{Literals}
Integers, floats, characters, booleans and strings supported so far.
\begin{verbatim}

> data Literal
>    = IntLit Int
>    | FloatLit Float
>    | BoolLit Bool
>    | CharLit Char
>    | StrLit String
>    deriving (Eq)

\end{verbatim}
\section{Miscellaneous types}
A later optimisation would be to parametrise the type of expressions
with the type of identifiers --- strings are not very efficient. As
soon as parsing has finished the strings could be replaced by integers
and a lookup table. A type parameter could be added to Expr' and Eqn'
and new maps ... written over that structure.
\begin{verbatim}

> type VarID = String
> type ConID = String

\end{verbatim}
\section{Access- and check-functions}
Function \verb|spineWalk|(-\verb|Type|) converts an expression (a
type) to a non-empty list containing the head of the application and
all arguments.
\begin{verbatim}

> spineWalk :: Expr' a -> [Expr' a]
> spineWalk e = sW e []
>   where sW (x :@: y) = sW x . (y:)
>         sW  x        = (x:)

> spineWalkType :: Type -> [Type]
> spineWalkType t = sW t []
>   where sW (x :@@: y) = sW x . (y:)
>         sW  x        = (x:)

> isVarBind :: Eqn' t -> Bool
> isVarBind (VarBind _ _ _ _) = True
> isVarBind _             = False

> isDataDef :: Eqn' t -> Bool
> isDataDef (DataDef _ _ _ _) = True
> isDataDef _               = False

> isInfixDecl :: Eqn' t -> Bool
> isInfixDecl (InfixDecl _ _ _) = True
> isInfixDecl _			= False

> isExplType :: Eqn' t -> Bool
> isExplType (ExplType _ _) = True
> isExplType _              = False

> isPolytypic :: Eqn' t -> Bool
> isPolytypic (Polytypic _ _ _ _) = True
> isPolytypic _                   = False

> changeNameOfBind :: (String -> String) -> Eqn' t -> Eqn' t
> changeNameOfBind f (VarBind n t ps e) = VarBind (f n) t ps e
> changeNameOfBind f (Polytypic n t fun cs) = Polytypic (f n) t fun cs
> changeNameOfBind _ _ = error "Grammar.changeNameOfBind: neither VarBind nor Polytypic"


> getHeadOfEqn :: Eqn -> String
> getHeadOfEqn (VarBind   name _ _ _) = name
> getHeadOfEqn (Polytypic name _ _ _) = "polytypic "++name
> getHeadOfEqn (DataDef   name _ _ _) = "data "++name
> getHeadOfEqn (ExplType  names _)    = "{-Typed: "++head names++
>                                       if length names>1 then "..." else ""++
>                                       "-}"
> getHeadOfEqn _                      = "{-Other-}"


> getNameOfBind :: Eqn' t -> String
> getNameOfBind (VarBind name _ _ _)     = name
> getNameOfBind (Polytypic name _ _ _) = name
> getNameOfBind _ = error "Grammar.getNameOfBind: wrong argument"

> getNameOfVarBind :: Eqn' t -> String
> getNameOfVarBind (VarBind name _ _ _)  = name
> getNameOfVarBind _ =error "Grammar.getNameOfVarBind: wrong argument"

> getNameOfDataDef :: Eqn' t -> String
> getNameOfDataDef (DataDef name _ _ _) = name
> getNameOfDataDef _ =error "Grammar.getNameOfDataDef: wrong argument"

> deQualify (_:=>t) = t
> qualify t = []:=>t

> functionConstructor :: ConID
> functionConstructor = "->"

> isFunctionType :: Type -> Bool
> isFunctionType (TCon c) =  c == functionConstructor
> isFunctionType _        =  False

> (-=>) :: Type -> Type -> Type 
> a -=> b = TCon functionConstructor :@@: a :@@: b

> listConstructor :: String
> listConstructor = "[]"

> tupleConstructor :: Int -> ConID
> tupleConstructor n = ( ('(':replicate (max (n-1) 0) ',')++")")

> isTupleCon :: ConID -> Bool
> isTupleCon (c:_) = c=='('
> isTupleCon []     = error "Grammar.isTupleCon: impossible: empty constructor"

> context2type (c,ts) = foldl (:@@:) (TCon c) ts

\end{verbatim}
