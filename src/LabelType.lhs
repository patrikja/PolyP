\chapter{Type labelling} 
\begin{verbatim}

> module LabelType(labelProgram) where
> import List(nub)
> import Folding(freeVarsPat,mapEqn)
> import Grammar(Literal(..), VarID, Eqn'(..), Expr'(..), Type(..), Eqn, 
>                TEqn, PrgEqns, PrgTEqns, QType, Qualified((:=>)),
>                deQualify,qualify,isPolytypic,getNameOfVarBind)
> import InferKind(inferDataDefs)
> import InferType(checkTypedInstance,tevalAndSubst)
> import MonadLibrary(STErr, (<@),(<@-), mliftErr, unDone, LErr, mapLErr,
>                     convertSTErr, Error(..), mapl, foreach,changeError)
> import MyPrelude(pair,mapSnd,splitUp,fMap,  maytrace)
> import StartTBasis(startTBasis)
> import StartTBasis(charType,intType,floatType,boolType,strType)
> import StateFix -- (ST [,runST [,RunST]]) in hugs, ghc, hbc
> import TypeBasis(Basis,TBasis,
>                  tBasis2Basis,extendTypeAfterTBasis,
>                  extendTypeEnv,extendTypeTBasis,
>                  getNonGenerics,getRamTypes,instantiate,inventTypes,
>                  lookupType,makeNonGeneric)
> import TypeGraph(HpQType,HpType, HpTExpr, HpTEqn, 
>                  mkVar, mkFun, (+#+), mkQFun,
>                  eqnIntoHeap, blockOutOfHeap,allGeneric,
>                  qtypeIntoHeap)
> import UnifyTypes(unify, checkInstance)
> import Monad(foldM)

> infix 9 |->

\end{verbatim}
This is an extension of the normal type inference algorithm that gives
both the updated type basis and an explicitly typed version of the
program. The translation is done in such a way that all type variables
in one equation get names that shows the sharing.
\section{Content description}
The function to be called from outside is {\tt labelProgram}. It
checks the datatype definitions and calls {\tt labelTopBlocks} on the
equations.

{\tt labelTopBlocks} takes as arguments a type basis (containing
information about types and kinds defined earlier) and a list of
blocks of equations. The result is the type basis extended with the
types of the defined values (the kind information is only read, not
changed or extended) and blocks - now with explicit types everywhere.

Every block is a minimal group of mutually recursive definitions and
the list of blocks is ordered by the dependencies between the blocks -
the later blocks may refer to the earlier, but not vice versa.

A block of equations is typed with {\tt labelBlock} but as the type
labelling is done inside the {\tt ST}-monad using mutable variables we
have a function {\tt labelTopBlock} that runs the {\tt ST}-monad and
converts the resulting types (and typed equations) back to the normal
abstract syntax for types (and typed expressions). In the translation
of the typed equations the type variables are assumed to scope over
the whole equation.

The normal value bindings are typed using {\tt labelVal} and the
polytypic definitions using {\tt labelPoly} and both these functions
use \verb!|->! to label expressions with types. 

\section{Programs}

After the data declarations have been kind-checked, a mapping from
type names to functors should be added to the \texttt{TBasis}.  
% 
This mapping is needed during type inference, when simplifying type
expressions containing \texttt{FunctorOf}.

\begin{verbatim}

> labelProgram :: PrgEqns -> LErr (TBasis,PrgTEqns)
> labelProgram (dataDefs, bindss) = 
>         case inferDataDefs startTBasis dataDefs of
>           (_,Err msg) -> ((startTBasis,(dataDefs,[])),Err msg)
>           (tbasis, _) ->
>               mapLErr (mapSnd (pair dataDefs))  
>                       (labelTopBlocks bindss tbasis)

\end{verbatim}
\section{Blocks of equations}
There are two functions to label blocks of definitions with types -
one is used recursively for every \verb|letrec| in the language and
the other is used on the top level.
\begin{verbatim}

> labelTopBlocks :: [[Eqn]] -> TBasis -> LErr (TBasis,[[TEqn]])
> labelTopBlocks blocks starttbasis = ((finaltbasis,blocks'),err)
>   where
>      tbasiss :: [TBasis]
>      errresults = zipWith labelTopBlock blocks tbasiss
>      (blocks',tenvs) = unzip (map unDone (takeWhile ok errresults)) 
>                               -- stops before the error 
>      tbasiss  = scanl (flip extendTypeTBasis) starttbasis tenvs
>      finaltbasis = extendTypeAfterTBasis (concat tenvs) 
>                                          starttbasis
>      err = case errresults of
>         []   -> Done ()
>         _    -> last errresults <@- ()
>      ok (Done _) = True
>      ok _        = False

> labelBlocks :: Basis s -> [[HpTEqn s]] -> STErr s ([[HpTEqn s]],Basis s)
> labelBlocks basis [] = return ([],basis)
> labelBlocks basis (block:blocks) 
>   = labelBlock  basis  block  >>= \(block',basis') -> 
>     labelBlocks basis' blocks >>= \(blocks',basis'') -> 
>     return (block':blocks',basis'')

\end{verbatim}
\section{Expressions}
Operator \verb"|->" labels an expression with the inferred
(heap-)types. The algorithm is very similar to the normal type
inference.
\begin{verbatim}

> mkTyped :: HpTExpr s ->   HpQType s -> (HpTExpr s,HpQType s)
> mkTyped e hpt = (Typed e hpt,hpt)

> (|->) :: Basis s -> HpTExpr s -> STErr s (HpTExpr s,HpQType s)

> basis |-> e@(Var name) 
>   = (name `lookupType` basis) <@ mkTyped e

> basis |-> e@(Con name)
>   = (name `lookupType` basis) <@ mkTyped e

> basis |-> (f :@: x)
>   = basis |-> f          >>= \(f',ps:=>tF) -> 
>     basis |-> x          >>= \(x',qs:=>tX) -> 
>     lift mkVar           >>= \tApp -> 
>     lift (mkFun tX tApp) >>= \tF'  -> 
>     unify tF tF'         >>
>     lift (ps +#+ qs)      >>= \pqs ->
>     return (pqs :=> tApp) <@ 
>     pair (f' :@: x')

> basis |-> (Lambda pat expr)
>   = basis `labelPat` pat >>= \((pat',tPat), basis') -> 
>     basis' |-> expr      >>= \(expr',tExpr) -> 
>     lift (mkQFun tPat tExpr) <@ 
>     pair (Lambda pat' expr')

> basis |-> e@(Literal lit)
>   = inferLiteral basis lit <@ pair e

> _     |-> e@WildCard
>   = lift (mkVar <@ qualify <@ pair e)

> basis |-> (Case expr alts)
>   = basis |-> expr >>= \(expr',ps:=>tExpr) -> 
>     lift mkVar     >>= \tA -> 
>     foreach alts (inferCaseAlt basis (tExpr,tA)) <@ unzip
>              >>= \(alts',qss) -> 
>     lift (foldM (+#+) [] (ps:qss))  >>= \pqs->
>     return (pqs :=> tA) <@ 
>     pair (Case expr' alts')
>  where 
>    inferCaseAlt basis' (l,a) (lhs, rhs) = 
>       basis' `labelPat` lhs >>= \((lhs',qs:=>tLhs), basis'') -> 
>       basis'' |-> rhs       >>= \(rhs',rs:=>tRhs) -> 
>       unify l tLhs          >>
>       unify a tRhs          >>
>       lift (qs +#+ rs)  <@
>       pair (lhs',rhs')

\end{verbatim}
Maybe the similarity with $\lambda$-expressions could be exploited:
unify the type lhs -> rhs with l -> a. (That would make the two
unifications one, less efficient but more beautiful.) The same idea
could perhaps be used in the parser.
\begin{verbatim}

> basis |-> (Letrec eqnss expr)
>   = basis `labelBlocks` eqnss >>= \(eqnss',basis') -> 
>     basis' |-> expr           >>= \(expr',tExpr) -> 
>     return tExpr              <@
>     pair (Letrec eqnss' expr')

\end{verbatim}
Infer the type of the expression, and check that it is more general
than the supplied type. Label with the (less general) explicit type.
When comparing generality the inferred type (tExpr) is instantiated so
that if the check succeeds tExpr should be equal to the explicitly
supplied type hpType.

%***BUG: The contexts are not compared => bad contexts are allowed.
%***BUG: line 3 below: checkInstance allGeneric hpType tExpr 
This should not be allGeneric but ngs, or something like that, but it
interferes with explicitly typed equations. This means that the
present trick for handling explicitly typed equations by translation
to explicitly typed expressions should be changed, and a special rule
for type checking equations should be used.

\begin{verbatim}

> basis |-> (Typed expr hpType)
>   = basis |-> expr        >>= \(expr',tExpr) -> 
>     checkTypedInstance basis allGeneric hpType tExpr >>
>     return hpType <@ 
>     mkTyped expr' 
>   -- where ngs = getNonGenerics basis

\end{verbatim}


\section{Patterns}
When checking a pattern we extend the nevironment with new types for
the variables in the pattern and check the pattern as an expression in
this environment. It is important that {\tt extendTypeEnv} puts these
new bindings in front of old bindings, possibly hiding some of them,
as these new bindings are more local. The extend environment is
returned for use in the right hand side of the construct that used the
pattern.

It is important that the new variables hide the old ones to get the
scope rules right.
\begin{verbatim}

> labelPat :: Basis s -> HpTExpr s -> 
>             STErr s ((HpTExpr s,HpQType s), Basis s)
> basis `labelPat` pat
>   = inventTypes vars >>= \tVars -> 
>     let basis' = ( makeNonGeneric tVars
>                  . extendTypeEnv (zip vars (map qualify tVars)) 
>                  ) basis
>     in (basis' |-> pat) <@ (`pair` basis')
>   where vars = freeVarsPat pat

\end{verbatim}

\section{List of (mutually recursive) equations}
To infer the types of a mutually recursive group of value- and
polytypic- definitions we first extend the environment with the
(explicitly given) types of the polytypic definitions and some fresh
type variables for the value definitions. Thus equipped we go on to
infer and check the types of the definitions with the new type
variables temporarily non-generic. (We don't allow polymorphic
recursion.)  

We have to be careful to translate the type variables in the type for
an identifier in the basis together with the corresponding equation.

(should check that explicitly given types have the right kind.)
(needs cleaning up)
\begin{verbatim}

> labelTopBlock :: [Eqn] -> TBasis -> Error ([TEqn],[(VarID,QType)])
> labelTopBlock eqns tbasis = fMap simplify (__RUNST__ (convertSTErr m))
>   where basis = tBasis2Basis tbasis
>         m :: STErr s ([TEqn],[(VarID,QType)])
>         m = (lift (foreach eqns' eqnIntoHeap) >>=  
>             labelBlock basis) >>= \(hpeqns,basis') ->
>             lift 
>              (blockOutOfHeap (zip hpeqns (getRamTypes basis')) 
>                   <@ (maytrace "labelTopBlock finished\n" $ unzip))

>         insertPoly (Polytypic v (ps:=>t) f cs) = 
>                     Polytypic v (poly f ps:=>t) f cs 
>         insertPoly q = q

>         poly f ps = ("Poly",[deQualify f]):ps
>         eqns' = map insertPoly eqns


\end{verbatim}
The order is important: hpeqns must be in the same order as {\tt
  getRamTypes basis'}.
\begin{verbatim}
             
>         simplify :: ([TEqn],[(VarID,QType)]) -> ([TEqn],[(VarID,QType)])
>         simplify (eqs,ps) = (map (mapEqn simp) eqs, map (mapSnd simp2) ps)
>         simp :: QType -> QType
>         simp (qs:=>t) = (nub qs :=> t)
>         simp2 (qs:=>t)= ((nub . remconst) qs) :=> t
>         remconst = filter (not.constant) 
>         constant ("Poly",TCon "FunctorOf" :@@: TCon _ : _) = True
>         constant _ = False

\end{verbatim}
To label a block of mutually recursive definitions we first assume new
types for the value bindings and the explicitly given types for the
polytypic bindings and then call \verb|labelVal| and \verb|labelPoly|
respectively to do the labelling. 

Each polytypic declaration gets the context {\tt Poly f} added to mark
the functor as polytypic in the labelling algorithm.

After inferring the types of the variable bindings, the collected
contexts are added to the types and the inference is redone. This is
repeated until the context stops changing but never more than n+1
times where n is the number of equations in the binding group. This is
needed to ensure the correctness of the contexts. (This is not as
inefficient as it may seem; as most functions are not mutually
recursive, n is mostly 1.)
\begin{verbatim}

> prepBasis :: Basis s -> ([HpTEqn s],[HpTEqn s]) -> 
>              ST s (Basis s, [(VarID,HpQType s)])
> prepBasis basis (peqns,veqns) = 
>     foreach veqns typeVar  <@
>     pair (extendTypeEnv (map typePoly peqns) basis)
>  where typeVar veqn = mkVar <@ (pair (getNameOfVarBind veqn) . qualify)
>        typePoly (Polytypic v hpt _ _) = (v,hpt)
>        typePoly _                     = error "LabelType.prepBasis: Impossible!"

> splitEqns :: [Eqn' (Qualified t)] -> 
>              ([Eqn' (Qualified t)],[Eqn' (Qualified t)])
> splitEqns eqns = (peqns,veqns)
>   where [peqns,veqns] = splitUp [isPolytypic] eqns

> type BlockData s = ([(VarID,HpQType s)],([HpTEqn s],[HpTEqn s]))

\end{verbatim}
\begin{itemize}
\item Extend the environment with the types for the polytypic bindings.
\item Label the value bindings:
  \begin{itemize}
  \item Make the type variables nongeneric
  \item Label each equations
  \end{itemize}
\item Label the polytypic definitions.
\item Return a list with the types of the value bindings and the
  labelled equations.
\end{itemize}
\begin{verbatim}

> labelBlock' :: Basis s -> BlockData s -> STErr s (BlockData s)
> labelBlock' polybasis (vals,(peqns,veqns))  = 
>   let extbasis = extendTypeEnv vals polybasis
>       ts = map (deQualify.snd) vals
>       veqnt = zip veqns ts
>       ngsbasis = makeNonGeneric ts extbasis
>   in foreach veqnt (labelVal ngsbasis) 
>                     <@ unzip >>= \(veqns',ts') ->
>      foreach peqns (labelPoly extbasis) >>= \peqns' ->
>      let vals' = zipWith (\(n,_) t -> (n,t)) vals ts'
>      in return (maytrace "labelBlock' finished\n" $
>                 vals',(peqns',veqns')) 

\end{verbatim}
To label a block of equations with types we
\begin{itemize}
\item Split the equation list into a polytypic part and a value
  definition part.
\item Assume initial types for the definitions.
\item Label the equations until the context is stable.
\item Return the last set of labelled equations.
\end{itemize}
\begin{verbatim}

> labelBlock :: Basis s -> [HpTEqn s] -> STErr s ([HpTEqn s],Basis s)
> labelBlock basis eqns
>   = lift (prepBasis basis pq)        >>= \(polybasis,vals)->
>     rep n (labelit polybasis pq) (vals,undefined) >>= \(vals',pq') ->
>     let finalbasis = extendTypeEnv vals' polybasis
>     in return (maytrace "labelBlock finished\n" $
>                conc pq',finalbasis)
>  where conc (pqs,vqs) = vqs ++ pqs
>        pq = splitEqns eqns
>        n = length eqns + 1
>        rep 0 _ x = return x
>        rep m f x = f x >>= rep (m-1) f
>        labelit base peve (vals',_) = labelBlock' base (vals',peve)

\end{verbatim}
While labelling a value binding we transform patterns on the left to
lambda expressions on the right to be able to use the normal type
labelling rules.
\begin{verbatim}

> labelVal :: Basis s -> (HpTEqn s,HpType s) -> 
>                STErr s (HpTEqn s,HpQType s)
> labelVal basis (eqn,tLhs) = changeError addPosition $
>     basis |-> e >>= \(e',t@(_:=>tRhs)) -> 
>     unify tLhs tRhs <@-
>     (insType t (inv e'),t)
>  where (e,inv) = patBindToVarBind eqn
>        insType t (VarBind v Nothing ps e') = VarBind v (Just t) ps e'
>        insType _ q = q
>        addPosition s = getNameOfVarBind eqn++": error in type checking:\n"++s

\end{verbatim}

To improve the error messages from the unification algorithm, we
prepend a line to the error message to indicate the location of the
error. To do this we use the function \texttt{changeError :: (String
-> String) -> STErr s a -> STErr s a}.

\subsection{labelPoly in the heap}
To check a polytypic definition we first infer the types of the case 
alternatives one by one.
\begin{verbatim}

> labelPoly :: Basis s -> HpTEqn s -> STErr s (HpTEqn s)
> labelPoly basis (Polytypic n hpty' _ cases) =
>    changeError (\e->n++": error in type checking:\n"++e) $ 
>    let (funs',es) = maytrace "labelPoly starts\n"
>                                                               $ unzip cases
>    in mapl (basis |->) es  <@ unzip >>= \(es',ti)->

\end{verbatim}
We also calculate the types the alternatives {\em should} have by
substituting the different functor alternatives for the functor in the
given type and evaluating the resulting type using teval.

The complicated match for hpty and hpf assumes that the Poly context
associated with the functor in the functor case is the first context
in the list. 

*** BUG (probably) related to moreGeneral: it should unify and affect
    the type variables that end up in the type label.

\begin{verbatim}

>       lift (instantiate allGeneric hpty') >>= \hpty@(((_,hpf:_):_):=>_)-> 
>       lift (mapl (maytrace "instantiating\n" $ instantiate allGeneric) funs') >>= \funs->
>       lift (mapl (tevalAndSubst basis hpty) 
>                  (maytrace "teval\n" funs)) >>= \taui ->

\end{verbatim}
Finally we check that the inferred types are more general than the
calculated types.
\begin{verbatim}

>       mapl (moreGeneral (maytrace "moreGeneral\n" ngs)
>                            ) (zip ti taui) >>
>       return (maytrace "labelPoly finished\n" $
>          Polytypic n hpty (qualify hpf) (zip funs es'))
>  where
>    ngs = getNonGenerics basis
>    moreGeneral ngs' (t,tau) = checkInstance ngs' tau t

> labelPoly _     _ = error "LabelType.labelPoly: not a polytypic definition"

\end{verbatim}

\section{Literals}
Just selects the type of the literal. 
\begin{verbatim}

> inferLiteral :: Basis s -> Literal -> STErr s (HpQType s)
> inferLiteral _ (IntLit _)  = mliftErr (qtypeIntoHeap intType)
> inferLiteral _ (FloatLit _)= mliftErr (qtypeIntoHeap floatType)
> inferLiteral _ (BoolLit _) = mliftErr (qtypeIntoHeap boolType)
> inferLiteral _ (CharLit _) = mliftErr (qtypeIntoHeap charType)
> inferLiteral _ (StrLit _)  = mliftErr (qtypeIntoHeap strType)

\end{verbatim}


%**
Maybe this definition should be in a static analysis phase.

Function \texttt{patBindToVarBind} transforms a pattern binding to a
lambda expression so that the type checker does not need to know about
pattern bindings. To restore the original shape of the expression a
function (inv) from expressions to equations is returned.

\begin{verbatim}

> patBindToVarBind :: Eqn' t -> (Expr' t,Expr' t -> Eqn' t)
> patBindToVarBind (VarBind v t pats rhs) = (expr',inv t)
>   where expr'= maybe id (flip Typed) t (foldr Lambda rhs pats)
>         inv' 0 e = ([],e)
>         inv' n (Lambda p e) = (p:ps,e')
>              where (ps,e') = inv' (n-1) e
>         inv' _ _ = error "InferType.patBindToVarBind: impossible: wrong no of Lambdas"
>         inv Nothing = uncurry (VarBind v Nothing) . (inv' (length pats))
>         inv (Just _)= invfun
>         invfun (Typed e ty) =
>                       (uncurry (VarBind v (Just ty)) (inv' (length pats) e))
>         invfun _ = error ("patBindToVarBind: untyped Typed expression found:"++v)
> patBindToVarBind _ = error "InferType.patBindToVarBind: impossible: not a VarBind"

\end{verbatim}

A shorthand notation:
\begin{verbatim}

> lift :: ST a b -> STErr a b
> lift = mliftErr 

\end{verbatim}
\section{Future work}
This module almost implements the squiggly arrow from Mark Jones'
Ph.D. thesis that type checks and inserts dictionary values. It should
ideally be an extension of that. 

Currently a polytypic expression {\tt e} is transformed to {\tt e ::
  Poly f => t} which is later (in polyInstance) transformed to an
instance for the specific f it is used on in the end. The context part
of the type is used as evidence. Instead the expression should be
transformed to one using dictionaries.



