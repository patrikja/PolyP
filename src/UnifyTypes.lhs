\chapter{Unification}
\begin{verbatim}

> module UnifyTypes(unify,checkInstance,  unifyVar) where
> import TypeGraph(HpType,fetchNode,occursInType,
>                  typeIntoHeap, flattenNgs,
>                  flattenHpType,mkFOfd,(==>),
>                  HpNode(..),HpQType,NonGenerics,isGenericApproximation)
>                  
> import TypeError
> import MonadLibrary(STErr,mliftErr,ErrorMonad(failEM),
>                     (<@),(<@-),mIf,applyM,applyM2,
>                     ST,(===))
> import Env(Env,newEnv,lookupEnv,extendsEnv)
> import Grammar(Qualified(..),Func)
> import MyPrelude(pair)

#ifdef __DEBUG_UNIFY__
> import MyPrelude(maytrace)
#else
#ifndef __OLD_HUGS__
> maytrace :: String -> a -> a
> maytrace _ = id
#endif
#endif

> lifE :: ST s a -> STErr s a
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

If an error occurs in the unification process, the \texttt{STErr}
monad contains an error message stating the local problem. Here on the
top level this should be extended with a message stating the types
that failed to unify. The error reporting function
\texttt{mayreportTypeError} is defined in \texttt{TypeError.lhs}.

\begin{verbatim}

> unify :: HpType s -> HpType s -> STErr s ()
> unify a b = maytrace "<" 
>               (punify a b >> 
>             maytrace ">" 
>               (return ()))

> unifyVar :: HpType s -> HpType s -> STErr s (ErrMsg (HpType s))
> unifyVar a b= -- mayshowargs a b >>
>               if a === b 
>               then maytrace "unifyVar: equal pointers" ok <@- noErrMsg
>               else
>                 mIf (a `occursIn` b) 
>                  (failHere a b ECyclicType)
>                  (lifE (a ==> b) <@- noErrMsg)
>   where   t1 `occursIn` t2 = lifE (t1 `occursInType` t2)

\end{verbatim}
This unification algorithm should be extended with a shell that takes
two qualified types, unifies the type parts and merges the predicates.
(In the impl. of Gofer every type variable points to its predicates?).
Example: {\tt unify (Show a => a) (Read b => b)} gives {\tt (Show
  a,Read a) => a}.

There are two problems with dealing with contexts correctly: context
simplification and a canonical ordering of contexts. The current
implementation of type variables can not be ordered and must therefore
be changed. One simple idea would be to pair the pointers up with
unique integers and use these as an order.

\section{Type ordering}
Function \verb|checkInstance ngs a b| tries to instantiate \verb|b|
(with non-generic variables in the list \verb|ngs|) to \verb|a|. It is
a 'one-way' unification algorithm that only allows non-generic
variables to be instantiated to non-generic types. (As \verb|a| is
assumed not to contain any non-generic variables this means
monotypes.)

Should also check that the predicates are related, and handle
polytypic types.

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
>      mayreportTError ngs a b

\end{verbatim}
This function answers the equivalent questions:
\begin{itemize}
\item Is a an instance of b
\item Is b more general than a
\item Can a and b be unified with a substitution only affecting
  variables in b.
\end{itemize}
The algorithm implements the following (successful) cases:
\begin{itemize}
\item \texttt{t <= forall b . b}
\item \texttt{t <= b}, if t is a monotype
\item \texttt{f1 e1 <= f2 e2}, if \texttt{f1 <= f2} and \texttt{e1 <= e2}
\item \texttt{c <= c} 
\end{itemize}
\begin{verbatim}

> isInstance :: NonGenerics s -> HpType s -> HpType s -> 
>                ST s (TError (HpType s))
> isInstance ngs a' b' =
>     {- mayshowargs' ngs a' b' >> -} 
>     fetchNode a' >>= \(a, nodeA) -> 
>     fetchNode b' >>= \(b, nodeB) -> 
>     if a === b
>     then ok
>     else case (nodeA, nodeB) of
>            (_, HpVar v) ->
>                 if isGen v
>                 then  b `mayinstantiateWith` a
>                 else
>                   mIf (isMonoType a)
>                      (b `instantiateWith` a)
>                      (err nongeneric a b)
>            (HpVar _, _) ->
>              err toogeneral a b
>            (HpApp af ax, HpApp bf bx) ->
>              --(b ==> a)            >>
>              isInstance ngs af bf >>= 
>              continueIfNoError (isInstance ngs ax bx)
>            (HpCon conA, HpCon conB) | conA==conB -> ok
>            _ -> 
>              err mismatch a b
>   where t1 `mayinstantiateWith` t2 =  
>           mIf (t1 `occursInType` t2)
>               (err "Cyclic types not allowed" t1 t2)
>               (t1 `instantiateWith` t2)
>         t1 `instantiateWith` t2 = (t1 ==> t2) >> 
>                                   ok
>         isGen v = isGenericApproximation v ngs
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
(We need a mapping from type names to their datatypes (and functors).)
{\em Rewrite, clean up, describe.}

First we need to distinguish between the five different cases we can
run into.

\begin{verbatim}

> data HpTy s = V (HpType s)            -- variable
>             | C String                -- constructor
>             | A (HpType s) (HpType s) -- application
>             | Mu (HpType s)           -- Mu f
>             | FOf (HpType s)          -- FunctorOf d

> constrNum :: HpTy s -> Int
> constrNum (V _  ) = 0
> constrNum (C _  ) = 1
> constrNum (A _ _) = 2
> constrNum (Mu _ ) = 3
> constrNum (FOf _) = 4

> instance Eq (HpTy s) where
>   a == b = (constrNum a) == (constrNum b)

> instance Ord (HpTy s) where
>   compare a b = compare (constrNum a) (constrNum b)

> analyzeTop :: HpType s -> ST s (HpType s, HpTy s)
> analyzeTop t
>   = fetchNode t >>= \(a, nodeA) ->
>     case nodeA of
>       HpVar _   -> return (a, V a)
>       HpCon c   -> return (a, C c) -- should not be Mu or FunctorOf
>       HpApp f x -> analyzeApp f x <@ pair a

> analyzeApp :: HpType s -> HpType s -> ST s (HpTy s)
> analyzeApp f' x' 
>   = fetchNode f' <@ \(_, nodeF) ->
>     case nodeF of
>       HpCon c | c == "Mu"        -> Mu   x'
>               | c == "FunctorOf" -> FOf  x'
>       _                          -> A f' x'

\end{verbatim}

To unify two terms we first (in \texttt{punify}) analyze the top level
structures by transforming the terms from \texttt{HpType s} to
\texttt{HpTy s}. As each of the terms can have five different top
level constructors, we have 25 cases to handle. To reduce the
complexity we use (in \texttt{punify1}) the symmetry of unification to
reduce this to 15 cases by ordering the constructors.

The unification should actually need a few more arguments: 
\begin{itemize}
\item The functor environment to be able to simplify and check types
  containing things like \texttt{FunctorOf Tree}.
\item The non-generic variabels (so that \texttt{handleTypeError} can
  print the types with genericity taken inte account)
\item The kind environment (so that we can do kinded unification
  correctly)
\end{itemize}
As all of these are in the \texttt{TypeBasis.Basis} so it would
suffice to pass this along. Probably all uses of unification does have
a the basis accessible, so the change should not be too big.

External usages of unify: (000127)
\begin{itemize}
\item InferKind: this uses unify for kind unification which much
  simpler that the full polytypic unification. If unify is extended
  with a context there will have to be a residual (simple) kindunify
  for this case.
\item LabelType: in the type inference at (:@:), Case and labelVal -
  in all cases the environment is immediately available.
\item Main: only in the debugging code, here we could use the empty
  environment (TypeBasis.emptyBasis)
\item 
\end{itemize}

Internal usages of punify
\begin{itemize}
\item unify: puniy
\item punify: punify'
\item punify': punify1
\item punify1: punify2
\item punify2: unifyVar, punify', punifyMu, punifyFOf 
\item punifyMu: punify'
\item punifyFOf: punifyFOf'
\item punifyFOf': *** here the punifyfuns argument is needed
\end{itemize}
All these usages need an extra argument (the basis or a suitable
subset).


All functions except punify use the result type \texttt{STErr s
(ErrMsg (HpType s))} which is used as if it were \texttt{STErr2 s ()},
where \texttt{STErr2} has better error reporting than
\texttt{STErr}. This is an ugly solution and should be replaced with a
better error reporting monad.

\begin{verbatim}

> punify :: HpType s -> HpType s -> STErr s ()
> punify a b = 
>   punify' a b >>=
>   handleTypeError a b

> punify' :: HpType s -> HpType s -> STErr s (ErrMsg (HpType s))
> punify' a b
>   = applyM2 punify1 (lifE (analyzeTop a)) (lifE (analyzeTop b))

> punify1 :: (HpType s, HpTy s) -> (HpType s, HpTy s) -> STErr s (ErrMsg (HpType s))
> punify1 p q | fst p === fst q  = ok <@- noErrMsg -- identical types
>             | snd p <=  snd q  = punify2 p q
>             | otherwise        = punify2 q p

> -- We require snd p <= snd q for all calls punify2 p q
> punify2 :: (HpType s, HpTy s) -> (HpType s, HpTy s) -> STErr s (ErrMsg (HpType s))

The first five cases are dealt with by the variable rule
\texttt{unifyVar}: it checks for circularity (occur check), performs
the substitution.

> punify2 (a,V _ )  (b, _   ) = unifyVar a b

The four remaining diagonal cases are handled as usual - by unifying
the children pairwise.

> punify2 (a,C cA ) (b,C cB)  | cA==cB    = ok <@- noErrMsg
>                             | otherwise = failHere a b EDifferentConstructors
> punify2 (a,A f x) (b,A g y) = -- [1]  lifE (a ==> b) >> 
>                               punify' f g >>=
>                               continueIfNoErr (punify' x y)
> punify2 (a,Mu f ) (b,Mu g ) = -- [1]  lifE (a ==> b) >> 
>                               punify' f g 
> punify2 (a,FOf d) (b,FOf e) = -- [1]  lifE (a ==> b) >> 
>                               punify' d e
> -- alternatively we could unify fOf d with fOf e ?

Now there is the classical mismatch case, and a new error case due to
kind mismatch as \texttt{Mu f :: *->*} and \texttt{FOf d :: *->*->*}.

> punify2 (a,C cA)  (b,A _ _) = failHere a b (EUnifyConstApp cA)
> punify2 (a,Mu _)  (b,FOf _) = failHere a b EUnifyKind

Finally we have the four interesting new cases when the functor
constructors are matched against other types.

> punify2 (a,C _  ) (b,Mu f ) = punifyMu a f
> punify2 (a,A _ _) (b,Mu _ ) = failHere a b ENoMuApp
> punify2 (a,C _  ) (b,FOf d) = punifyFOf d a b
> punify2 (a,A _ _) (b,FOf d) = punifyFOf d a b

As an extra precaution a base case checks for missed cases or
violations of the invariant that the arguments to \texttt{punify2}
should be ordered.

> punify2 (_, a   ) (_, b   ) | a <= b    = internalError "Unify missed case"
>                             | otherwise = impossible "unorderd HpTy in punify2"

Take care of D ~ Mu f by calling Mu (FOf D) ~ Mu f, or rather FOf D ~ f

> punifyMu :: HpType s -> HpType s -> STErr s (ErrMsg (HpType s))
> punifyMu d f = applyM (punify' f) (lifE $ mkFOfd d)

Take care of FOf d ~ f by calling fOf d ~ f. Requires that d is a
datatype constructor.

> punifyFOf :: HpType s -> HpType s -> HpType s -> 
>              STErr s (ErrMsg (HpType s))
> punifyFOf d' f' b =
>    do (_,d) <- lifE (analyzeTop d')
>       fOrErr <- punifyFOf' d f' b
>       either (punify' f') return fOrErr

> -- **** punifyfuns should be a parameter
> punifyFOf' :: HpTy s -> HpType s -> HpType s -> STErr s (Either (HpType s) (ErrMsg (HpType s)))
> punifyFOf' (C d)   a b = failHere a b (ENoFunctorEnv d) <@ Right

                           case lookupEnv d punifyfuns of 
                            Nothing   -> failHere a b (ENoFunctorFor d) <@ Right
                            Just fOfd -> (lifE $ typeIntoHeap fOfd)     <@ Left

> punifyFOf' (Mu f') a b = return f' <@ Left
> punifyFOf' (FOf _) a b = failHere a b (EFOfnonDT "FunctorOf (FunctorOf _) not allowed") <@ Right
> punifyFOf' (A _ _) a b = failHere a b (EFOfnonDT "FunctorOf (type application) not allowed") <@ Right
> punifyFOf' (V _)   a b = failHere a b (EFOfnonDT "FunctorOf (variable) not implemented") <@ Right

> failHere :: HpType s -> HpType s -> LocalErrMsg -> STErr s (ErrMsg (HpType s))
> failHere a b lerr = return (ErrMsg (Just (lerr,a,b)))

> ok :: Monad m => m ()
> ok = return ()

(internalError "Unify.ok: This value should not have been used.")

 punifyfuns :: Env String Func
 punifyfuns = extendsEnv l newEnv
      where l = error "UnifyTypes.punify: Needs functor environment (to be implemented)"

\end{verbatim}
\subsection{Future improvements to the unification algorithm}
Maybe the types should be stratified into two sorts, functors, and
types with a special appication constructor for applying
(syntactically) a functor to one or more types.

In matching \texttt{FOf d} with \texttt{FOf d'} one could consider
unifying \texttt{fOf d} with \texttt{fOf d'} but this probably messes
up the type system as we lose information (about \texttt{d},
\texttt{d'}).

In matching \texttt{Mu f} with \texttt{Mu f'} we should have a dual
situation - we could try to find the types \texttt{d}, \texttt{d'}
that these came from and only succeed if we can unify \texttt{d} with
\texttt{d'} (as they are constructors, that means checking for
equality: \texttt{d} = \texttt{d'}).

If partially applied datatypes are to be allowed as being regular, the
\texttt{punifyMu} and \texttt{punifyFOf} cases have to be updated to
allow an application and not only a constructor.

In the diagonal cases, the overwriting \texttt{a ==> b} that takes
place before the subunification(s) is intended to speed up the
unification if exactly the same pair of types need to be unified again
in the same call to (the top level) \texttt{punify}. It is not clear
if this means a speedup in practice as there is a tradeoff between the
extra work added by this equality test, and the reduced work during
unification. In types with lots of sharing it should pay off.


990703: Simple test: Work done by hugs when run on exaples/Separate.phs
With    ==> (3484618 reductions, 6346771 cells, 34 garbage collections)
Without ==> (3462077 reductions, 6313207 cells, 34 garbage collections)

Thus we can probably remove the overwriting and gain speed.

(Originally the unification algorithm was written to deal with
possibly infinite types, and in that case the overwriting was essential for
termination. Currently it is only an optimization and can be removed
without invalidating the algorithm.) The overwriting might make the
type error messages look strange if a mismatch is encountered further
down in a type, while the print out of the top level types will show
two identical structures.

An important observation about the use of \texttt{FOf} is that
currently \texttt{FOf d} does not unify with \texttt{g+h} while
\texttt{FOf List} does unify with \texttt{g+h}. This means that the
order the different subunifications are done in a type matters! (In
the above example, the variable \texttt{d} might later be unified with
\texttt{List}.) This is bad news and means that we really ought to
implement semantic unification correctly instead. It is possible that
a solution is to delay the handling of unification reqests involving
\texttt{FOf} (and \texttt{Mu}) until after the rest of the type has
been dealt with. 

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
