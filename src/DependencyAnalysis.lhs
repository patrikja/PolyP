\chapter{Dependency analysis}
\begin{verbatim}

> module DependencyAnalysis where
> import Array(array,(!))
> import Env(lookupEnv,newEnv,extendsEnv)
> import Folding(cataEqn,freeVarsEqn)
> import Grammar(Eqn,Eqn'(..),Expr'(..),PrgEqns,getNameOfBind,
>                isDataDef,isExplType,isInfixDecl)
> import GraphLibrary(Graph,Tree(..),scc')
> import MyPrelude(splitUp)
> import PrettyPrinter(pshow,prQualified,QType,Eqn)
> import TypeBasis(TypeEnv)

\end{verbatim}
\section{What is dependency analysis?}
{\em Dependency analysis}\/ is needed in the process of type
checking. Without it every equation must be assumed to be
mutually recursive with every other equation. This leads
to more restricted types than the best possible. 
That is because (in my type checker, which doesn't support 
{\em polymorphic recursion}\/) recursive calls to the variable
being defined must all have the same type. So, without
dependency analysis the expression
\begin{verbatim}
  let map f xs = .... -- usual definition
      id x     = x 
      dummy    = map id
  in  map
\end{verbatim}
would be assigned the type: \verb|(a -> a) -> [a] -> [a]|.
However, if the expression were to be transformed to
\begin{verbatim}
  let map f xs = ....
  in  let id x = x
      in  let dummy = map id
          in  map
\end{verbatim}
the problem would not occur. For \verb|map|, \verb|id|
and \verb|dummy| are not assumed to be mutually recursive
when they are not in the same \verb|let|. This rearranging
of definitions is the task of dependency analysis (or
better: dependency transformation). 

In this implementation the transformation is not so 'physical' as
pictured above. Instead, as you can see in the grammar, \verb|Letrec|
takes a list of a lists of equations. The dependency transformation
splits the equations up in lists (of mutually recursive equations) and
then performs a topological sort on these blocks.

The dependency transformation takes the following steps:
\begin{enumerate}
\item Number the variables bound by the equations.  The first variable
  has number zero.
\item Find free variables of the equations' bodies.
\item Transform those variables to numbers as far as they refer to the
  variables that are currently being defined.
\item Transform all this information into a form the strongly
  connected component algorithm (John Launchbury) likes.
\item Feed the information to this algorithm; this algorithm actually
  also does a topological sort of the strongly connected components.
\item Transform the groups of numbers you now have back to the
  corresponding equations.
\end{enumerate}
These tasks are divided over two functions; \verb|makeGraph| takes a
set of equations and performs step 1-4 and \verb|dependencyEqn| takes
care of the last two steps.
\begin{verbatim}

> makeGraph      :: [Eqn] -> Graph
> dependencyEqns :: [Eqn] -> [[Eqn]]

\end{verbatim}
Finally, there are two auxiliary functions that make it possible to do
dependency analysis on a complete program: \verb|dependencyEqn|
performs the transformation on all the \verb|letrec|s in an equation
and \verb|dependencyProgram| does this for every equation and for the
program as a whole.
\begin{verbatim}

> dependencyEqn :: Eqn -> Eqn
> dependencyProgram :: [Eqn] -> PrgEqns

\end{verbatim}
\section{Implementation}
\begin{verbatim}

> makeGraph eqns 
>   = array (0, length eqns - 1)
>           (zip [0..] (map numberedFreeVars eqns) )
>   where
>     numberedFreeVars =  -- lookup corresponding numbers and
>         findNumbers . freeVarsEqn -- find free variables
>                                   -- (refs to other functions)
>     env = extendsEnv -- names paired with numbers
>               (zip (map getNameOfBind eqns) [0..])  newEnv
>
>     findNumbers [] = []
>     findNumbers (x:xs) = case lookupEnv x env of
>                           Nothing ->   findNumbers xs
>                           Just i  -> i:findNumbers xs

> dependencyEqns = dependencyEqns' . handleExplTypes
 
> dependencyEqns' :: [Eqn] -> [[Eqn]]
> dependencyEqns' eqns = map (map (eqnarr !)) groups
>   where
>     eqnarr = array (0, length eqns -1) (zip [0..] eqns)
>     groups = ( map flatten  -- flatten rose trees
>              . scc'         -- perform scc + topsort
>              . makeGraph)    -- construct graph
>                eqns

> flatten :: Tree a -> [a]
> flatten (Node x xs) = x : concatMap flatten xs

> dependencyEqn
>   = cataEqn ( (Var, Con, (:@:), Lambda, Literal, 
>                 WildCard, Case, letrec, Typed)
>             , (VarBind, DataDef, Polytypic, ExplType, InfixDecl)
>             )
>   where letrec [qs] body = Letrec (dependencyEqns qs) body
>         letrec _ _ = error "DependencyAnalysis.dependencyEqn: impossible: input list not of length 1"

> dependencyProgram eqns = (dataDefs,infixDecls,bindss)
>   where [dataDefs, infixDecls, binds] = splitUp [isDataDef, isInfixDecl] eqns
>         bindss = (dependencyEqns . map dependencyEqn ) binds

\end{verbatim}
\section{Inserting explicit types in the correct positions}
For every list of equations (including local let bindings) the
following is done: The list of equations is split up into three
categories: normal declarations, polytypic declarations and explicitly
typed identifiers.  The explicitly typed declarations are converted to
a type environment which is then used to insert explicit types into
the normal bindings.  If a polytypic identifier is given an explicit
type it must me identical to the type in the declaration. 

At this point variable bindings still have their arguments on the LHS
so the explicit type can not simply be placed on the rhs.
\begin{verbatim}

> handleExplTypes :: [Eqn] -> [Eqn]
> handleExplTypes eqns = map handle binds
>   where [ets,binds] = splitUp [isExplType] eqns
>         env = ets2TyEnv ets
>         handle q = mayInsType (lookupEnv (getNameOfBind q) env) q


> ets2TyEnv :: [Eqn] -> TypeEnv 
> ets2TyEnv ets = extendsEnv (concat (map get ets)) newEnv
>   where get (ExplType vs t) = zip vs (repeat t)
>         get _ = error "DependencyAnalysis.ets2TyEnv: impossible: only ExplType allowed."

> mayInsType :: Maybe QType -> Eqn -> Eqn
> mayInsType t (VarBind v _ ps e) = VarBind v t ps e
> mayInsType t q@(Polytypic p t' _ _) = case t of 
>         Nothing              -> q
>         Just t'' | t''==t'   -> q
>                  | otherwise -> error ("mayInsType: "++err t' t'')
>   where err :: QType -> QType -> String
>         err ty1 ty2 = "Polytypic declaration "++p++
>                       " with two different types:\n"++
>                       show (prQualified ty1) ++ " and " ++ 
>                       show (prQualified ty2)
> mayInsType _ q = error ("mayInsType: Unexpected equation:\n"++pshow q)

\end{verbatim}
