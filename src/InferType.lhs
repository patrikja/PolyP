\chapter{Type inference}
\begin{verbatim}

> module InferType(tevalAndSubst,qTypeEval,checkTypedInstance) where
> import UnifyTypes(checkInstance)
> import TypeGraph(HpType,NodePtr,HpNode(..),HpQType,NonGenerics,
>                  mkFOfd,(==>),checkCon,
>                  typeIntoHeap,qtypeIntoHeap,qtypeOutOfHeap,allGeneric,
>                  spineWalkHpType,getChild, showNodePtr)
> import TypeBasis(Basis,FuncEnv,getTBasis,getFuncEnv,instantiate)
> import Env(Env,newEnv,rangeEnv,lookupEnv,extendsEnv)
> import MyPrelude(fMap, trace,debug)
> import MonadLibrary(STErr,mliftErr,unDone,(@@),mplus,
>                     mapl,(<@),(<@-),accumseq,accumseq_)
> import StateFix -- (ST [,runST [,RunST]]) in hugs, ghc, hbc
> import Grammar(Eqn'(..),Expr'(..),
>		 Qualified(..),Qualifier,QType,
>                VarID,ConID,Type(TVar))
> import ParseLibrary(parse)
> import Parser(pType1)
> import PrettyPrinter()
> import Monad(foldM)

\end{verbatim}
\section{Contents}
The functions \texttt{tevalAndSubst}, \texttt{qTypeEval} and
  \texttt{checkTypedInstance} are all implemented in terms of
  \texttt{hpQTypeEval}.

%*** This should be generalised.
The functor variable in the polytypic case is assumed to be the first
in the context list.

\begin{verbatim}

> tevalAndSubst :: Basis s -> 
>                  HpQType s -> HpQType s -> -- type, functor
>                  ST s (HpQType s)          -- evaluated type
> tevalAndSubst basis hpty' (_:=>hpfi) = 
>   instantiate allGeneric hpty' >>= \hpty->
>   let pf = pickFunctorVariable hpty
>	funcenv = getFuncEnv (getTBasis basis)
>   in 
>     pf ==> hpfi                  >> -- substitution by destructive update
>     hpQTypeEval funcenv hpty     >> -- type evaluation  
>     return hpty

> pickFunctorVariable :: HpQType s -> HpType s
> pickFunctorVariable (("Poly",[pf]):_:=>_) = pf
> pickFunctorVariable _ = error $ "InferType.pickFunctorVariable:" ++
>              " The functor variable was not first in the context."

\end{verbatim}
\begin{verbatim}

> qTypeEval :: FuncEnv -> QType -> QType
> qTypeEval funcenv qt = __RUNST__ mqt
>   where mqt :: ST s QType
>         mqt = qtypeIntoHeap qt      >>= 
>		hpQTypeEval funcenv   >>= 
>		qtypeOutOfHeap allGeneric

typeEval :: Type -> Type
typeEval t = __RUNST__ m
  where m :: ST s Type
        m = typeIntoHeap t >>= \hpt ->
            hpTypeEval hpt >>
            typeOutOfHeap [] hpt
               
> checkTypedInstance :: Basis s -> NonGenerics s -> 
>                       HpQType s -> HpQType s -> STErr s ()
> checkTypedInstance basis ngs small big 
>   = checkInstance ngs small big 
>   `mplus`
>     (mliftErr (hpQTypeEval (getFuncEnv (getTBasis basis)) small) >>= \small' ->
>     checkInstance ngs small' big)



> hpQTypeEval :: FuncEnv -> HpQType s -> ST s (HpQType s)
> hpQTypeEval funcenv (l :=> t) = 
>   (fMap concat (mapl tevalC l)) >>= \l' ->
>   hpTypeEval funcenv t >> -- side effect on t
>   return (l':=>t)

> tevalC :: Qualifier (HpType s) -> ST s [Qualifier (HpType s)]
> tevalC ("Poly", fun : _ ) = fMap (map poly) (funEval fun)
>    where poly :: HpType s -> Qualifier (HpType s)
>          poly f = ("Poly", [f])
> tevalC c                  = return [ c ]

\end{verbatim}


The type evaluation trasforms the context as sketched below:

\begin{verbatim}
hpQTypeEval ({f|->g+h} Poly f => f a b -> b) = 
hpQTypeEval (Poly (g+h) => (g+h) a b -> b) = 
(Poly g,Poly h) => Either (g a b) (h a b) -> b

hpQTypeEval ({f|->Par} Poly f => f a b -> b) = 
hpQTypeEval (Poly Par => (Par) a b -> b) = 
() => a -> b
\end{verbatim}
The context transformation/simplification is implemented by funEval.

\begin{verbatim}

> funEval :: HpType s -> ST s [HpType s] -- functors
> funEval = funEval' @@ spineWalkHpType 

\end{verbatim}

If the functors were syntactic objects as they are parsed this
definition would do it.

\begin{verbatim}
 funEval (g+h)     = funEval g ++ funEval h
 funEval (g*h)     = funEval g ++ funEval h
 funEval (d@g)     = [FunctorOf d] ++ funEval g
 funEval (Par)     = []
 funEval (Rec)     = []
 funEval (Const t) = []
 funEval (f)       = [f]  -- functor variable
\end{verbatim}

In practice we have to work a little harder: not only are the functors
encoded in the type for types, but also this type is encoded using
pointers. We can encode the varying part of the above function sketch
in a table:

\begin{verbatim}

> funEvalEnv :: Env String [HpType s -> ST s [HpType s]]
> funEvalEnv = extendsEnv 
>   [("+",[funEval, funEval])
>   ,("*",[funEval, funEval])
>   ,("@",[dataEval,funEval])
>   ,("Par",[])
>   ,("Rec",[])
>   ,("Empty",[])
>   ,("Const",[consttypeEval])
>   ,("FunctorOf",[fMap (:[]) . mkFOfd])
>   ] newEnv

\end{verbatim}

\begin{verbatim}
spineWalkHpType gives (f:args)
HpCon c -> -- a functor constructor encountered
  lookupEnv c funEvalEnv gives funs
  if not found => error
  make sure the argument list has same length as args
  zipWith ($) funs args
  sequence and concatenate the results
f@(HpVar v) -> -- a functor variable
  make sure it has no arguments (it could be m g, but that is no Bifunctor)
  return [f]  
(HpApp _ _) -> impossible ...
\end{verbatim}


\begin{verbatim}

> funEval' :: [(NodePtr s,HpNode s)] -> ST s [NodePtr s]
> funEval' [] = error "InferType.funEval': impossible: nothing to apply"
> funEval' ((pf,f):pnargs) = case f of
>     HpVar _   -> def
>     HpCon c   -> maybe (errNoBifun c) (funEvalArgs c args) (lookupEnv c funEvalEnv)
>     HpApp _ _ -> error "InferType.funEval': impossible: HpApp found after spine removal"
>   where args = map (getChild . snd) pnargs
>         def | null args  = return [pf]
>             | otherwise  = error "InferType.funEval': Expected functor variable, found application."
>         errNoBifun c = error ("InferType.funEval': found "++c++
>                               " when expecting a Bifunctor constructor.")

> funEvalArgs :: String -> [HpType s] -> [HpType s -> ST s [HpType s]] -> ST s [HpType s]
> funEvalArgs c args argfuns 
>   | numfuns == numargs 
>      = fMap concat (accumseq (zipWith ($) argfuns args))
>   | otherwise
>      = error ("InferType.funEval': Bifunctor constructor "++ c ++
>               "expects "++show numfuns ++" arguments, found instead "++
>                           show numargs ++" arguments.")
>       where 
>         numfuns = length argfuns
>         numargs = length args

\end{verbatim}

If d is not a fixed datatype D: 
  build FunctorOf d
  return it in a singleton list
otherwise
  remove it

\begin{verbatim}

> dataEval :: HpType s -> ST s [HpType s]
> dataEval d = checkCon d >>= 
>              maybe (fMap (:[]) (mkFOfd d))
>                    (return . const [])

> consttypeEval :: HpType s -> ST s [HpType s]
> consttypeEval _ = return []

\end{verbatim}

\subsection{Type evaluation in the heap}
For all the cases: 
\begin{itemize}
\item Get a fresh copy $t_i$ of the type $t$ with handle $h_i$ to the
  functor $f$ inside the heap type.
\item Transform the functor case into the heap giving $f_i$.
\item Perform the substitution by unifying the handle with $f_i$.
\item Apply hpteval to the type $t_i$. (It will also need to know about
  $f_i$ to know which transformation rule to apply and $h_i$ so that only
  the correct occurrences of the matching rule will be used.)
\item Check that the inferred type is an instance of this type.
\end{itemize}
New idea: Treat \verb|+| ... as type synonyms! In this way the
unification algorithm will have to be extended, but teval completely
disappears.

\section{Specific polytypic help functions.}
Static checks:
\begin{itemize}
\item Const x: x must be type variable
\end{itemize}
\subsection{Type evaluation}
Type expressions containing type synonyms are evaluated to expressions
without synonyms just like the evaluation of expressions to normal
form in a simple functional language. The language has variables,
constructors and applications.

The evaluation is done by side-effecting the pointer structure.

\begin{verbatim}

> hpTypeEval  :: FuncEnv -> NodePtr s -> ST s ()
> hpTypeEval' :: FuncEnv -> [(NodePtr s,HpNode s)] -> ST s [NodePtr s]

> hpTypeEval funcenv = hpteval 
>   where hpteval = (accumseq_ . fMap hpteval) @@ 
>		    hpTypeEval' funcenv        @@ 
>		    spineWalkHpType 

> hpTypeEval' funcenv [] = error "InferType.hpTypeEval': impossible: nothing to apply"
> hpTypeEval' funcenv pargs = case f of
>     HpVar _   -> def
>     HpCon c | isFuncorOf c -> evalFunctorOf funcenv children
>	      | otherwise    -> maybe def eval (lookupEnv c typeSynEnv)
>     HpApp _ _ -> error "InferType.hpTypeEval': impossible: HpApp found after spine removal"
>   where f:args   = map snd pargs
>         nargs    = length args
>         children = map getChild args
>         def      = return children
>         eval (arity,syn) | arity > nargs = def -- partial application
>                          | otherwise     = applySynonym syn children >>= again
>         again ptr = 
>           root ==> ptr >>
>           spineWalkHpType root >>= \pargs2->
>           hpTypeEval' funcenv (pargs2++rest)
>         (root,_):rest = drop nargs pargs
>
>         again2 ptr = 
>           root2 ==> ptr >>
>           spineWalkHpType root >>= \pargs2->
>           hpTypeEval' funcenv (pargs2++ rest2)
>         (root2,_):rest2 = drop 1 pargs

>         --evalFunctorOf :: FuncEnv -> [NodePtr s] -> ST s [NodePtr s]
>         evalFunctorOf funcenv [] = error "InferType.evalFunctorOf: FunctorOf without any argument"
>         evalFunctorOf funcenv (d:args) = checkCon d >>= maybe def fOf
>         evalFunctorOf funcenv _ = def
>
>         -- fOf :: ConID -> ST s [NodePtr s]
>	  fOf d = maybe def (again2 @@ (typeIntoHeap . debug . snd)) $ 
>		  lookupEnv d funcenv


> isFuncorOf :: ConID -> Bool
> isFuncorOf = ("FunctorOf"==)

\end{verbatim}
These should be precalculated (maybe moved to another module).
Function \verb|teval| 'evaluates' type expressions by repeatadly
applying the following rewrite rules: \\
\begin{tabular}{lll}
  (f + g) a b     & $\rightarrow$ & Either (f a b) (g a b) \\
  (f * g) a b     & $\rightarrow$ & (f a b,g a b) \\
  (d @ g) a b     & $\rightarrow$ & d (g a b)     \\
  Par a b         & $\rightarrow$ & a             \\
  Rec a b         & $\rightarrow$ & b             \\
  Const t a b     & $\rightarrow$ & t             \\
  Empty a b       & $\rightarrow$ & ()            \\
\end{tabular} \\
\begin{verbatim}

> typeSynEnv :: Env VarID (Int,QType)
> typeSynEnv = extendsEnv [typeSyn "+" "fgab" "Either (f a b) (g a b)",
>                          typeSyn "*" "fgab" "(f a b, g a b)",
>                          typeSyn "@" "dgab" "d (g a b)",
>                          typeSyn "Par" "ab" "a",
>                          typeSyn "Rec" "ab" "b",
>                          typeSyn "Const" "tab" "t",
>                          typeSyn "Empty" "ab" "()"
>                         ] newEnv

\end{verbatim}
We represent type synonyms by their arity, and a qualified type where
the context is used to name the variables and the type is the body. In
this way the normal \texttt{qtypeIntoHeap} will give us pointers into
the body that we can use for substitution.

Problem: The program loops if not all synonyms are present. 
\begin{verbatim}

> typeSyn :: name -> String -> String -> (name,(Int,QType))
> typeSyn n cs rhs = (n, (length cs, ps :=> unDone (parse pType1 rhs)))
>   where ps = map (\c->("",[TVar [c]])) cs
> splitTypeSyn :: Qualified t -> ([t],t)
> splitTypeSyn (ps:=>rhs) = (map f ps,rhs)
>   where f (_,[pv]) = pv
>         f _ = error "InferType.splitTypeSyn: not a type variable"

> applySynonym :: QType -> [HpType s] -> ST s (HpType s)
> applySynonym syn args = 
>     qtypeIntoHeap syn <@ splitTypeSyn  >>= \(vars,rhs)->
>     accumseq (zipWith (==>) vars args) <@- rhs

\end{verbatim}
\section{Groups}
To infer the types of a list of blocks of (mutually recursive)
equations we start with a type environment with primitive functions
and type constructors and extend this incrementally with the types
from each group.

We would like to:
\begin{itemize}
\item Get the result from the first few groups even if the type
  inference fails later
\item Get this result lazily (the types of the declarations in the
  first group should be available immediately after they have been
  inferred)
\end{itemize}
Idea:
\begin{itemize}
\item Assume that there is a list of succesive approximations to the
  final \verb|TBasis|. (\verb|tbasiss|)
\item Apply \verb|inferGroup| to each group and the corresponding
  basis. (Giving \verb|errtenvs|)
\item Filter out only the successful inferences. (Giving \verb|tenvs|)
\item Calculate the original list from the starting type basis and
  this list.
\item Now the result is essentially the last element in the list of
  approximations, but to preserve laziness it is calculated
  separately. (Function \verb|last| waits until the whole list is
  produced before giving any result.)
\end{itemize}

To infer the types in a group of mutually recursive definitions we
need to:
\begin{itemize}
\item Assume new non-generic type variables for the variable
  bindings. (Store in the heap.)
\item Store the explicitly given types for the polytypic definitions
  in \verb|TBasis|.
\item Infer the types of the variable bindings.
\item Make their type variables generic.
\item Check the types of the polytypic definitions.
\item Get the types of the variable bindings out of the heap and
  return them. 
\end{itemize}
The fact that the variable bindings are temporarily given non-generic
types means that we don't allow polymorphic recursion. The explicitly
given types in the polytypic declarations are treated as containg only
generic variables (just like any other explicit type).

The idea is that the types should be stored in \verb|TBasis| in such a
way that they can be lazily pulled out of it one group at a time.

\section{Expressions}
The fact that an expression $e$ has type $\tau$ in a type environment
$\Gamma$ in often written $\Gamma \vdash e : \tau$. To imitate that
way of writing we will denote the function that infers the most
general type of an expression by the infix operator \verb"|-" of type:
\begin{verbatim}

#if 0
> (|-) :: Basis s -> Expr -> STErr s (HpQType s)
#endif

\end{verbatim}
The result type is the inferred type or an error message embedded in
the \verb|STErr|-monad.

The algorithm is split up into different cases corresponding to the
alternatives in the abstract syntax of expressions. 

\section{Patterns}
To infer the type of a pattern we invent non-generic type variables
for the free variables occuring in the pattern and then infer the type
as for expressions. As the new variables will be needed in some
corresponding right hand side the extended basis is returned along with
the inferred type.

Takes basis to basis' and then pattern to type.

\section{Blocks of equations (sorted after dependencies)}
To infer the types in a program, we simply infer the types of the
blocks in the order they arrive (thus assuming that they are
topologically sorted with respect to dependecies), threading the
updated basis through the calculation.

\section{List of (mutually recursive) equations}
To infer the types of a mutually recursive group of value- and
polytypic-definitions we first extend the environment with the
(explicitly given) types of the polytypic definitions and some fresh
type variables for the value definitions. Thus equipped we move on to
inferring and checking the types of the definitions with the new type
variables temporarily non-generic. (We don't allow polymorphic
recursion.)  (We assume here that the explicitly given types have the
right kind.)

After transforming the pattern bindings to value bindings we proceed
to inferring the types of the value bindings and the polydefs. The
value bindings are checked in an environment where all their type
variables are non-generic, but before the polytypic definitions are
checked the variables are again made generic.  (If this is the right
way requires further thinking.)

To check a polytypic definition we first infer the types of the case 
alternatives one by one.
We also calculate the types the alternatives {\em should} have by
substituting the different functor alternatives for the functor in the
given type and evaluating the resulting type using teval.
Finally we check that the inferred types are more general than the
calculated types.


polytypic checking of x :: ty = case f of {fi -> ei}
\begin{itemize}
 \item ty is a type (i.e. has kind *)
 \item f occurs in ty
 \item f,fi are functors (i.e. have kind *->*->*)
 \item (1): tyEnv' is tyEnv extended with x :: ty
 \item (2): ei are typable with types ti in tyEnv'
 \item (3): taui = teval {f |-> fi} ty
 \item (4): ti >= taui
\end{itemize}

