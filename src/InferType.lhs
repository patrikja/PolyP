\chapter{Type inference}
\begin{verbatim}

> module InferType where
> import InferKind(inferDataDefs)
> import UnifyTypes(unify,checkInstance)
> import TypeGraph(HpType,HpKind,NodePtr,HpNode(..),HpQType,NonGenerics,
>                  mkFun,mkCon,mkVar,mkFOfd,mkQFun,
>                  (==>),fetchNode,checkCon,
>                  qtypeIntoHeap,qtypeOutOfHeap,allGeneric,
>                  spineWalkHpType,getChild, (##))
> import TypeBasis(Basis,TBasis,
>                  tBasis2Basis,extendTypeTBasis,extendTypeAfterTBasis,
>                  getNonGenerics,makeNonGeneric,lookupType,ramTypeToRom,
>                  extendTypeEnv,ramKindToRom,getKindEnv,instantiate,
>                  extendKindEnv,extendKindTBasis,inventTypes)
> import StartTBasis(startTBasis,charType,intType,floatType,boolType,strType)
> import Env(Env,newEnv,lookupEnv,extendsEnv)
> import MyPrelude(pair,splitUp)
> import MonadLibrary(STErr,mliftErr,convertSTErr,Error(..),unDone,(@@),
>                     foreach,mapl,(<@),(<@-),LErr,map2)
> import StateFix-- (ST [,runST [,RunST]]) in hugs, ghc, hbc
> import Grammar -- (Qualified,Type(..),PrgEqns)
> import Folding(freeVarsPat,cataType)
> import ParseLibrary(parse)
> import Parser(pType1)
> import PrettyPrinter(Pretty(..))
> import Monad(foldM)

\end{verbatim}
\section{Programs}
\begin{verbatim}

> inferProgram :: PrgEqns -> LErr TBasis
> inferProgram (dataDefs, bindss) = 
>   let p@(basis,err) = inferDataDefs startTBasis dataDefs
>   in case err of 
>        Err msg -> p
>        _       -> inferGroups bindss basis

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
\begin{verbatim}

> inferGroups :: [[Eqn]] -> TBasis -> LErr TBasis
> inferGroups eqnss starttbasis = (finaltbasis,err)
>  where 
>   tbasiss :: [TBasis]
>   errtenvs= zipWith inferGroup eqnss tbasiss
>   tenvs   = map unDone (takeWhile ok errtenvs)
>   tbasiss = scanl (flip extendTypeTBasis) starttbasis tenvs
>   finaltbasis = extendTypeAfterTBasis (concat tenvs) 
>                                       starttbasis
>   err = last errtenvs <@- ()
>   ok (Done _) = True
>   ok _        = False

\end{verbatim}
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
\begin{verbatim}

> inferGroup :: [Eqn] -> TBasis -> Error [(VarID,QType)]
#ifdef __HBC__
> inferGroup eqns tbasis = runST $ RunST (convertSTErr (mInferGroup eqns tbasis))
#else /* not __HBC__ */
> inferGroup eqns tbasis = runST         (convertSTErr (mInferGroup eqns tbasis))
#endif /* __HBC__ */

> mInferGroup :: [Eqn] -> TBasis -> STErr s [(String,QType)]
> mInferGroup eqns tbasis = inferBlock basis eqns   >>= \basis' ->
>                           mliftErr (ramTypeToRom basis')
>   where basis = tBasis2Basis tbasis

\end{verbatim}
\section{Expressions}
The fact that an expression $e$ has type $\tau$ in a type environment
$\Gamma$ in often written $\Gamma \vdash e : \tau$. To imitate that
way of writing we will denote the function that infers the most
general type of an expression by the infix operator \verb"|-" of type:
\begin{verbatim}

> (|-) :: Basis s -> Expr -> STErr s (HpQType s)

\end{verbatim}
The result type is the inferred type or an error message embedded in
the \verb|STErr|-monad.

The algorithm is split up into different cases corresponding to the
alternatives in the abstract syntax of expressions. 

\begin{verbatim}

> basis |- (Var name) = name `lookupType` basis
> basis |- (Con name) = name `lookupType` basis
> basis |- (f :@: x)  =
>     basis |- x               >>= \(ps:=>tX)-> 
>     basis |- f               >>= \(qs:=>tF)-> 
>     mliftErr mkVar           >>= \tApp -> 
>     mliftErr (mkFun tX tApp) >>= \tF'  -> 
>     unify tF tF'             >> 
>     mliftErr (ps ## qs)      >>= \pqs ->
>     return (pqs :=> tApp)

> basis |- (Lambda pat expr)
>   = inferPat basis pat >>= \(tPat, basis')-> 
>     basis' |- expr     >>= \tExpr-> 
>     mliftErr (mkQFun tPat tExpr)

> basis |- (Literal lit) = inferLiteral basis lit
> basis |- WildCard      = mliftErr (mkVar <@ qualify)

> basis |- (Case expr alts)
>   = basis |- expr            >>= \(ps:=>tExpr) -> 
>     mliftErr mkVar           >>= \tA -> 
>     foreach alts (infAlt (tExpr,tA)) >>= \qss ->
>     mliftErr (foldM (##) [] (ps:qss))  >>= \pqs->
>     return (pqs :=> tA)
>  where -- infAlt :: (HpType s,HpType s) -> (Expr,Expr) -> 
>        --           STErr s [Qualifier (HpType s)]
>        infAlt (l,r) (lhs,rhs) = 
>           inferPat basis lhs >>= \((qs:=>tLhs), basis') -> 
>           basis' |- rhs      >>= \(rs:=>tRhs) -> 
>           unify l tLhs       >> 
>           unify tRhs r       >>
>           mliftErr (qs ## rs)

> basis |- (Letrec eqnss expr)
>   = inferBlocks basis eqnss >>= \basis' -> 
>     basis' |- expr

> basis |- (Typed expr uType)
>   = mliftErr (qtypeIntoHeap uType)   >>= \uHpQType -> 
>     basis |- expr                   >>= \tExpr   -> 
>     checkInstance ngs uHpQType tExpr >>= \_ ->
>     return tExpr
>   where ngs = getNonGenerics basis

\end{verbatim}
\section{Literals}
Just selects the type of the literal. 
\begin{verbatim}

> inferLiteral :: Basis s -> Literal -> STErr s (HpQType s)
> inferLiteral basis (IntLit _)  = mliftErr (qtypeIntoHeap intType)
> inferLiteral basis (FloatLit _)= mliftErr (qtypeIntoHeap floatType)
> inferLiteral basis (BoolLit _) = mliftErr (qtypeIntoHeap boolType)
> inferLiteral basis (CharLit _) = mliftErr (qtypeIntoHeap charType)
> inferLiteral basis (StrLit _)  = mliftErr (qtypeIntoHeap strType)

\end{verbatim}
\section{Patterns}
To infer the type of a pattern we invent non-generic type variables
for the free variables occuring in the pattern and then infer the type
as for expressions. As the new variables will be needed in some
corresponding right hand side the extended basis is returned along with
the inferred type.

Takes basis to basis' and then pattern to type.
\begin{verbatim}

> inferPat :: Basis s -> Pat -> STErr s (HpQType s, Basis s)
> inferPat basis pat
>   = inventTypes vars >>= \tVars -> 
>     let basis' = ( makeNonGeneric tVars
>                  . extendTypeEnv (zip vars (map qualify tVars)) 
>                  ) basis
>     in (basis' |- pat) <@ (`pair` basis')
>   where vars = freeVarsPat pat

\end{verbatim}

\section{Blocks of equations (sorted after dependencies)}
To infer the types in a program, we simply infer the types of the
blocks in the order they arrive (thus assuming that they are
topologically sorted with respect to dependecies), threading the
updated basis through the calculation.
\begin{verbatim}

> inferBlocks :: Basis s -> [[Eqn]] -> STErr s (Basis s)
> inferBlocks basis [] = return basis
> inferBlocks basis (block:blocks) 
>   = basis  `inferBlock`  block  >>= \basis' -> 
>     basis' `inferBlocks` blocks

\end{verbatim}
\section{List of (mutually recursive) equations}
To infer the types of a mutually recursive group of value- and
polytypic-definitions we first extend the environment with the
(explicitly given) types of the polytypic definitions and some fresh
type variables for the value definitions. Thus equipped we move on to
inferring and checking the types of the definitions with the new type
variables temporarily non-generic. (We don't allow polymorphic
recursion.)  (We assume here that the explicitly given types have the
right kind.)
\begin{verbatim}

> inferBlock :: Basis s -> [Eqn] -> STErr s (Basis s)
> inferBlock basis eqns = m
>   where
>     [peqns,veqns] = splitUp [isPolytypic] eqns
>     typeVar veqn = mkVar <@ (pair (getNameOfVarBind veqn) . qualify)
>     typePoly (Polytypic v (ps:=>t) f cs) = 
>                 qtypeIntoHeap (poly f ps :=> t) <@ pair v
>     typePoly _ = error "InferType.inferBlock: impossible: not Polytypic"
>     poly :: QType -> [Context]-> [Context]
>     poly f ps = ("Poly",[deQualify f]):ps
>     m = mliftErr (foreach veqns typeVar ) >>= \vals ->
>         mliftErr (foreach peqns typePoly) >>= \polys -> 
>         let extbasis = extendTypeEnv (vals++polys) basis
>             tmpbasis = makeNonGeneric tVars extbasis
>             tVars    = map (deQualify.snd) vals

\end{verbatim}
After transforming the pattern bindings to value bindings we proceed
to inferring the types of the value bindings and the polydefs. The
value bindings are checked in an environment where all their type
variables are non-generic, but before the polytypic definitions are
checked the variables are again made generic.  (If this is the right
way requires further thinking.)
\begin{verbatim}

>             veqnt = zip veqns tVars
>         in foreach veqnt (checkVal tmpbasis)  >>= \ts ->
>            foreach peqns (checkPoly extbasis) >>
>            let finalbasis = extendTypeEnv (vals'++polys) basis
>                vals' = zipWith (\(n,_) t -> (n,t)) vals ts
>            in return finalbasis

\end{verbatim}
Maybe this definition should be in a static analysis phase.

The last component, inv, puts back the patterns in their original
position.
\begin{verbatim}

> patBindToVarBind :: Eqn' t -> (Expr' t,Expr' t -> Eqn' t)
> patBindToVarBind q@(VarBind v t pats rhs) = (expr',inv t)
>   where expr'= maybe id (flip Typed) t (foldr Lambda rhs pats)
>         inv' 0 e = ([],e)
>         inv' n (Lambda p e) = (p:ps,e')
>              where (ps,e') = inv' (n-1) e
>         inv' n _ = error "InferType.patBindToVarBind: impossible: wrong no of Lambdas"
>         inv Nothing = uncurry (VarBind v Nothing) . (inv' (length pats))
>         inv (Just _)= invfun
>         invfun (Typed e ty) =
>                       (uncurry (VarBind v (Just ty)) (inv' (length pats) e))
>         invfun _ = error ("patBindToVarBind: untyped Typed expression found:"++v)
> patBindToVarBind _ = error "InferType.patBindToVarBind: impossible: not a VarBind"

> checkVal :: Basis s -> (Eqn,HpType s) -> STErr s (HpQType s)
> checkVal basis (eqn,tLhs) = 
>    basis |- e >>= \t@(ps:=>tRhs) -> 
>    unify tLhs tRhs <@- t
>  where (e,_) = patBindToVarBind eqn

\end{verbatim}
To check a polytypic definition we first infer the types of the case 
alternatives one by one.
\begin{verbatim}

> checkPoly :: Basis s -> Eqn -> STErr s ()
> checkPoly basis (Polytypic _ ty f cases) =
>    let (funs,es) = unzip cases  
>    in mapl (basis |-) es >>= \ti -> 

\end{verbatim}
We also calculate the types the alternatives {\em should} have by
substituting the different functor alternatives for the functor in the
given type and evaluating the resulting type using teval.

\begin{verbatim}

>       mliftErr (qtypeIntoHeap ty        >>= \hpty->
>                 mapl qtypeIntoHeap funs >>= \funs'->
>                 mapl (tevalAndSubst hpty) funs') >>= \taui -> 

\end{verbatim}
Finally we check that the inferred types are more general than the
calculated types.
\begin{verbatim}

>          mapl (moreGeneral ngs) (zip ti taui) >>
>          return ()
>  where
>    ngs = getNonGenerics basis
>    moreGeneral ngs' (t,tau) = checkInstance ngs' tau t
> checkPoly _ _ = error "InferType.checkPoly: impossible: not Polytypic"

\end{verbatim}

The functor variable in the polytypic case is assumed to be the first
in the context list.

\begin{verbatim}

> tevalAndSubst :: HpQType s -> HpQType s -> -- type, functor
>                  ST s (HpQType s)          -- evaluated type
> tevalAndSubst hpty' (_:=>hpfi) = 
>   instantiate allGeneric hpty' >>= \hpty@((_,pf:_):_:=>pt) ->
>   pf ==> hpfi                  >> -- substitution by destructive update
>   hpQTypeEval hpty             >> -- type evaluation  
>   return hpty

\end{verbatim}

The type evaluation should also evaluate the context as sketched
below.  The idea is that 
\begin{verbatim}
hpQTypeEval ({f|->g+h} Poly f => f a b -> b) = 
hpQTypeEval (Poly (g+h) => (g+h) a b -> b) = 
(Poly g,Poly h) => Either (g a b) (h a b) -> b

hpQTypeEval ({f|->Par} Poly f => f a b -> b) = 
hpQTypeEval (Poly Par => (Par) a b -> b) = 
() => a -> b
\end{verbatim}

\begin{verbatim}

> qTypeEval :: QType -> QType
> qTypeEval qt = 
#ifdef __HBC__
>    runST $ RunST mqt
#else /* not __HBC__ */
>    runST         mqt
#endif /* __HBC__ */
>   where mqt :: ST s QType
>         mqt = qtypeIntoHeap qt >>= hpQTypeEval >>= qtypeOutOfHeap allGeneric

typeEval :: Type -> Type
typeEval t = runST m
  where m :: ST s Type
        m = typeIntoHeap t >>= \hpt ->
            hpTypeEval hpt >>
            typeOutOfHeap [] hpt
               

> hpQTypeEval :: HpQType s -> ST s (HpQType s)
> hpQTypeEval (l :=> t) = (map concat (mapl tevalC l)) >>= \l' ->
>                         hpTypeEval t >> -- side effect on t
>                         return (l':=>t)

> tevalC :: Qualifier (HpType s) -> ST s [Qualifier (HpType s)]
> tevalC ("Poly", fun : _ ) = map (map poly) (funEval fun)
>    where poly :: HpType s -> Qualifier (HpType s)
>          poly f = ("Poly", [f])
> tevalC c                  = return [ c ]

> funEval :: HpType s -> ST s [HpType s] -- functors
> funEval = funEval' @@ spineWalkHpType 

> checkTypedInstance :: NonGenerics s -> HpQType s -> HpQType s -> STErr s ()
> checkTypedInstance ngs small big 
>   = mliftErr (hpQTypeEval small) >>= \small' ->
>     checkInstance ngs small' big

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
>   ,("FunctorOf",[map (:[]) . mkFOfd])
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
>      = map concat (accumulate (zipWith ($) argfuns args))
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
>              maybe (map (:[]) (mkFOfd d))
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

> hpTypeEval :: NodePtr s -> ST s ()
> hpTypeEval' :: [(NodePtr s,HpNode s)] -> ST s [NodePtr s]

> hpTypeEval = (sequence . map hpTypeEval) @@ hpTypeEval' @@ spineWalkHpType 

> hpTypeEval' [] = error "InferType.hpTypeEval': impossible: nothing to apply"
> hpTypeEval' pargs = case f of
>     HpVar _   -> def
>     HpCon c   -> maybe def eval (lookupEnv c typeSynEnv)
>     HpApp _ _ -> error "InferType.hpTypeEval': impossible: HpApp found after spine removal"
>   where f:args = map snd pargs
>         nargs = length args
>         children = map getChild args
>         def = return children
>         eval (arity,syn) | arity > nargs = def -- partial application
>                          | otherwise     = applySynonym syn children >>= again
>         again ptr = 
>           root ==> ptr >>
>           spineWalkHpType root >>= \pargs2->
>           hpTypeEval' (pargs2++rest)
>         (root,_):rest = drop nargs pargs

\end{verbatim}
These should be precalculated (maybe moved to another module).
Function \verb|teval| 'evaluates' type expressions by the following
rewrite rules: \\
\begin{tabular}{lll}
  Rec a b           & $\rightarrow$ & b             \\
  Par a b           & $\rightarrow$ & a             \\
  (f :+: g) a b     & $\rightarrow$ & f a b + g a b \\
  (f :*: g) a b     & $\rightarrow$ & (f a b,g a b) \\
  ((Mu f) :@: g) a b& $\rightarrow$ & Mu f (g a b)  \\
  Const x a b       & $\rightarrow$ & x             \\
\end{tabular} \\
\begin{verbatim}

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
this way the normal qtypeIntoHeap will give us pointers into the body
that we can use for substitution.

Problem: The program loops if not all synonyms are present. 
\begin{verbatim}

> typeSyn n cs rhs = (n, (length cs, ps :=> unDone (parse pType1 rhs)))
>   where ps = map (\c->("",[TVar [c]])) cs
> splitTypeSyn (ps:=>rhs) = (map f ps,rhs)
>   where f (_,[pv]) = pv
>         f _ = error "InferType.splitTypeSyn: not a type variable"

> applySynonym syn args = 
>     qtypeIntoHeap syn <@ splitTypeSyn  >>= \(vars,rhs)->
>     sequence (zipWith (==>) vars args) <@- rhs

\end{verbatim}

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

