\chapter{Unification}
\begin{verbatim}

> module UnifyTypes(unify,checkInstance,  unifyVar) where
> import TypeGraph(HpType,fetchNode,occursInType,
>                  typeIntoHeap, flattenNgs,
>                  flattenHpType,mkCon,mkApp,
>                  HpNode(..),HpQType,NonGenerics,(==>))
> import TypeError
> import MonadLibrary(STErr,mliftErr,ErrorMonad(failEM),(<@),mIf,liftop,
>                     ST,(===),readVar)
> import Env(newEnv,lookupEnv,extendsEnv)
> import Grammar(Type(..),Qualified(..),qualify,deQualify)

#ifdef __DEBUG_UNIFY__
> import MyPrelude(swap,maytrace)
#else
> import MyPrelude(swap)
#ifndef __OLD_HUGS__
> maytrace _ = id
#endif
#endif

> lifE = mliftErr   -- local short name

\end{verbatim}
\section{Simple unification}
The function \verb|unify| unifies two types. Variables are made to
point to the corresponding part of the other type. Constructors are
checked for equality and application nodes unify their children.  The
occurs-check (in \verb|unifyVar|) prevents cyclic types to being
constructed.

If a non-generic type variable is to be unified with a type t, all of
t's variables have to be made non-generic too. This is automatically
handled by the representation of the non-generic variables; it is a
list of pointers into the types that are unified, with the
interpretation that all variables reachable from that list are
non-generic. This means that this list is automatically kept up to
date without being explicitly used in \verb|unify|. (A useful `side
effect'!)

(The error messages are currently not very enlightning.)
\begin{verbatim}

> unify a b = maytrace "<" 
>               (punify a b >> maytrace ">" (return ()))

#ifdef FALSE
> unifyold :: HpType s -> HpType s -> STErr s ()
> unifyold a b 
>   = lifE (fetchNode a) >>= \(a', nodeA) -> 
>     lifE (fetchNode b) >>= \(b', nodeB) -> 
>     if a' === b' -- equal pointers => identical types
>     then ok 
>     else case (nodeA, nodeB) of
>            (HpVar _, _      ) -> unifyVar a' b'
>            (_      , HpVar _) -> unifyVar b' a'
>            (HpApp af ax, HpApp bf bx) ->
>               lifE (a' ==> b') >> 
> -- otimization: will never re-unify them
>               unify af bf        >>
>               unify ax bx 
>            (HpCon conA, HpCon conB) | conA==conB -> ok
>            _ -> failWith "Constructor mismatch" a' b'
>     where ok = return () 
#endif /* FALSE */

> unifyVar :: HpType s -> HpType s -> STErr s ()
> unifyVar a b= -- mayshowargs a b >>
>               if a === b then error "unifyVar: equal pointers"
>               else
>                 mIf (a `occursIn` b) 
>                  (failEM "unifyVar: Cyclic types not allowed")
>                  (lifE (a ==> b))
>   where   t1 `occursIn` t2 = lifE (t1 `occursInType` t2)

\end{verbatim}
This unification algorithm should be extended with a shell that takes
two qualified types, unifies the type parts and merges the predicates.
(In the impl. of Gofer every type variable points to its predicates?).
Example: {\tt unify (Show a => a) (Read b => b)} gives {\tt (Show
  a,Read a) => a}.

\section{Type ordering}
Function \verb|checkInstance ngs a b| tries to instantiate \verb|b|
(with non-generic variables in the list \verb|ngs|) to \verb|a|. It is
a 'one-way' unification algorithm that only allows non-generic
variables to be instantiated to non-generic types. (As \verb|a| is
assumed not to contain any non-generic variables this means
monotypes.)

Should also check that the predicates are related.

Using {\tt allngs} below is an optimization in that the list of
variables is calculated only once, but for correctness this requires
that the list will not change during execution of {\tt
isInstance}. Unfortunately this is not necessarily true as the
algorithm changes the types pointer structure using {\tt (==>)}.

\begin{verbatim}

> checkInstance :: NonGenerics s -> HpQType s -> HpQType s -> 
>                    STErr s ()
> checkInstance ngs (_:=>a) (_:=>b) =
>      lifE (flattenNgs ngs >>= \allngs ->
>            isInstance allngs a b) >>= 
>      mayreportTError ngs a

\end{verbatim}
This function answers the equivalent questions:
\begin{itemize}
\item Is a an instance of b
\item Is b more general than a
\item Can a and b be unified with the substitution only affecting
  variables in b.
\end{itemize}
The algorithm implements the following (successful) cases:
\begin{itemize}
\item t <= forall b . b
\item t <= b, if t is a monotype
\item f1 e1 <= f2 e2, if f1 <= f2 and e1 <= e2
\item c <= c 
\end{itemize}
\begin{verbatim}

> isInstance :: NonGenerics s -> HpType s -> HpType s -> 
>                ST s (TError (HpType s))
> isInstance ngs a' b' 
>   = fetchNode a' >>= \(a, nodeA) -> 
>     fetchNode b' >>= \(b, nodeB) -> 
>     if a === b
>     then ok
>     else case (nodeA, nodeB) of
>            (_, HpVar v) ->
>                 if isGen v
>                 then  b `instantiateWith` a
>                 else
>                   mIf (isMonoType a)
>                      (b `instantiateWith` a)
>                      (err nongeneric a b)
>            (HpVar _, _) ->
>              err toogeneral a b
>            (HpApp af ax, HpApp bf bx) ->
>              (b ==> a)            >>
>              (isInstance ngs af bf >>= \inst -> 
>               case inst of
>                 TOk -> isInstance ngs ax bx
>                 _   -> return inst 
>              )
>            (HpCon conA, HpCon conB) | conA==conB -> ok
>            _ -> 
>              err mismatch a b
>   where t1 `instantiateWith` t2 =  (t1 ==> t2) <@ const TOk
>         isGen v = not (any (===v) ngs)
>         ok = return TOk
>         err msg t1 t2 = return (TBad msg t1 t2)
>         nongeneric = "A nongeneric type variable can only "
>                         ++ "be instantiated to a monotype."
>         toogeneral = "The type is too general."
>         mismatch   = "The types don't match."

\end{verbatim}

A non-generic type variable may only be instantiated to a type without
generic typevariables. In all cases where \verb|checkInstance| is used
the specified type has only generic type variables so the checking
that a type is non-generic is reduced to checking that it has no
variables at all. (Otherwise we would need to have access to the list
of all non-generic variables and we could then simply check that all
variables in the type are in this list.)

\begin{verbatim}

> isMonoType :: HpType s -> ST s Bool
> isMonoType ht = flattenHpType ht <@ allNonGeneric
>   where allNonGeneric :: [HpType s] -> Bool
>         allNonGeneric = null

\end{verbatim}

\section{Polytypic unification}
{\em The following text is older than the algorithm}
To type check the use of a polytypic function on a concrete value we
have to be able to unify {\tt Mu}-types with normal datatypes. As an
example consider the application of {\tt size :: Mu f a -> Int} to the
value {\tt Leaf x :: Tree a}. The unification algorithm will be called
with the pair {\tt (Mu f a -> Int, Tree a -> b)} which it will take
apart until it gets to the pair {\tt (Mu f,Tree)}. Here is where the
polytypic unification comes in: {\tt Tree} is replaced by {\tt Mu
  (FunctorOf Tree)} and the unfication continued.

This calls for a way to handle the unification of values containing
{\tt FunctorOf D}:
\begin{itemize}
\item ({\tt FunctorOf D}, {\tt FunctorOf D'}) - if D==D' then ok else fail
\item ({\tt Mu (FunctorOf D)}, {\tt D'}) - if D==D' the ok else fail
\item ({\tt FunctorOf D}, {\tt f+g}) - first unify ({\tt functorOf D},
  {\tt f+g)}, then overwrite {\tt f+g} with {\tt FunctorOf D}
\end{itemize}

This means that we need a modified unification algorithm taking these
new cases into account. This algorithm can then be used when either of
the types to be unified is polytypic.

\subsection{Implementation}
We need a function {\tt functorOf} that takes the name of a datatype
to the functor that represents its structure.

New rules in unify:
\begin{itemize}
\item (Mu x, D): overwrite D with Mu (FunctorOf D).  This together
  with the normal rules takes care of the two first cases above.
\item (FunctorOf D, t) where t is generated by Empty, Const, Par, Rec,
  +, *, @ and type (functor) variables: unify and overwrite t.
\end{itemize}
\subsection{How to recognize these cases}
(We need a mapping from type names to their datatypes (and functors).)
{\em Rewrite, clean up, describe.}
\begin{verbatim}

> punify :: HpType s -> HpType s -> STErr s ()

> punify = punify' punifyfuns
> punify' funs a b
>   = lifE (fetchNode a) >>= \(a, nodeA) -> 
>     lifE (fetchNode b) >>= \(b, nodeB) -> 
>     if a === b -- equal pointers => identical types
>     then ok 
>     else unify1 (nodeA,nodeB) a b 
>  where 
>    unify1 p a b = case maytrace "u1 " p of
>      (HpVar _, _      ) -> unifyVar a b
>      (_      , HpVar _) -> unifyVar b a
>      (HpCon conA, HpCon conB) | conA==conB -> ok
>                               | otherwise  -> failWith (conA++"/="++conB) a b
>      p                  -> unify2 p a b

\end{verbatim}
At this point we know that we have (App,Con), (Con,App) or (App,App).
Unlike the normal unification we now have to look more closely at the
cases before deciding what to do. We want to detect {\tt FunctorOf D}
matched against something and {\tt Mu f} matched against a
constructor. 
\begin{verbatim}

>    unify2 p a b = case maytrace "u2 " p of
>      (HpApp f x, t) -> unify3 p a b f x t
>      (t, HpApp f x) -> unify3 (swap p) b a f x t 
>      _              -> error "UnifyTypes: unify2: impossible: no application"
>    unify3 p a b f x t = 
>         lifE (maytrace "u3 " (checkCon f)) >>= 
>         maybe continue (\c-> case c of
>           "Mu"        -> unifyMu p a b f x t
>           "FunctorOf" -> unifyFun p a b x t
>           _           -> continue
>          )
>      where continue = unify4 p a b
>    unify4 p a b = case maytrace "u4 " p of
>      (HpApp f x,HpApp g y) -> 
>         lifE (a ==> b) >> punify f g >> punify x y 
>      _ -> failWith "constructor/=application" a b 

>    unifyMu p a b f x (HpCon d) = 
>        (maytrace "uMu " (lifE (makeMuFD f d))) >>= \mufd ->

        lifE (writeVar b mufd) >> -- leads to trouble

>        unify4 (fst p,mufd) a b
>    unifyMu p a b _ _ _ = unify4 p a b

>    makeMuFD pMu d = 
>      mkCon d       >>= \pd->
>      mkFOf         >>= \pFOf->
>      mkApp pFOf pd >>= \pFOfd->
>      return (HpApp pMu pFOfd)

>    mkFOf = mkCon "FunctorOf"

\end{verbatim}
If the right hand side (rhs) is also {\tt FunctorOf d} we just compare
the arguments, otherwise we look up the functor corresponding to the
datatype and try to unify this functor with the rhs.
\begin{verbatim}

>    unifyFun p a b x (HpApp g y) = 
>        lifE (checkCon g) >>= 
>        maybe cont 
>          (\gc-> case gc of
>            "FunctorOf" -> punify x y
>            _           -> cont
>          )
>    
>      where 
>        cont =
>          lifE (checkCon (maytrace "uF " x)) >>= maybe err (\d->
>          maybe (failWith "functor not found" a b) 
>                writeFunctor 
>                  (lookupEnv d funs))
>        writeFunctor f = 
>          lifE (typeIntoHeap (qualify f) <@ deQualify) >>= \fp->
>          maytrace "wFun " (punify b fp)

              >>
              lifE (writeVar b (fst p))

>        err = error "unifyFun: FunctorOf <not datatype>"

>    unifyFun p a b x n = mayshowargs a b >> 
>                         failEM ("unifyFun: "++baderr)
>    baderr = "Application expected (this should not happen!)"

Fix the bug due to assymmetry

a=CFunctorOf@Var=FunctorOf a
,b=C(,)=(,)

unifyFun: Application expected (this should not happen!)

>    ok = return () 

> punifyfuns = extendsEnv l newEnv
>      where l = error "punify: Needs functor environment (to be implemented)"

> checkCon pc = fetchNode pc >>= \(_,n) -> case n of
>                  (HpCon c) -> return (Just (maytrace ("["++c++"]") c))
>                  _         -> return Nothing

\end{verbatim}


