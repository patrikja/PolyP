\chapter{Kind inference}
\begin{verbatim}

> module InferKind where

> import Grammar(Type(..))
> import TypeGraph(HpKind,HpNode(..),fetchNode,mkVar,mkCon,mkFun,kindOutOfHeap)
> import TypeBasis(KindBasis,lookupKind)
> import PrettyPrinter(Pretty(..))
> import UnifyTypes(unify)
> import MonadLibrary(STErr,mliftErr,ErrorMonad(failEM))

> infix 9 |*

\end{verbatim}
The kind inference is used to check that the type constructors are
used correctly in explicitly given types. (Including datatype
definitions.)  Every expression must have kind $\ast$ so
\verb|assureType| infers the kind and (effectively) unifies it with
$\ast$.  This could have been done by a call to \verb|unify| but to get
the correct error message it is done by pattern matching on the kind
directly.
\begin{verbatim}

> assureType :: KindBasis s -> Type -> STErr s ()
> assureType basis tp
>   = basis |* tp                 >>= \hpKind -> 
>     mliftErr (fetchNode hpKind) >>= \(k, node) -> 
>     case node of
>       HpCon "*" -> return ()
>       HpVar _  -> return ()
>       _       -> mliftErr (kindOutOfHeap k) >>= \kind->
>                  failEM ("Kind error: Expected * but found: "
>                          ++ show (pretty kind))

 assureType basis tp
   = basis |* tp                 >>= \hpKind -> 
     mliftErr (mkCon "*")        >>= \star   ->
     unify star hpKind 
\end{verbatim}
The actual kind inference algorithm.
\begin{verbatim}

> (|*) :: KindBasis s -> Type -> STErr s (HpKind s)

> basis |* (TVar name) = name `lookupKind` basis
> basis |* (TCon name) = name `lookupKind` basis 
> basis |* (f :@@: x)
>   = basis |* x               >>= \kX   -> 
>     basis |* f               >>= \kF   -> 
>     mliftErr mkVar           >>= \kApp -> 
>     mliftErr (mkFun kX kApp) >>= \kF'  -> 
>     unify kF kF'             >>
>     return kApp

\end{verbatim}
(It seems to be slightly more efficient to infer the kind of \verb|x|
before \verb|f|.)

